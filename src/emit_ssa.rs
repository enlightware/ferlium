use std::collections::HashMap;

use ustr::Ustr;

use crate::hir::function::{ResolvedArgPassing, ResolvedValueArgPassing};
use crate::module::{
    ExtraParameterId, ResolvedLocalClone, ResolvedLocalDrop, ResolvedTakeLocalValueMode,
};
use crate::{
    CompilerSession, Location, Modules, containers,
    format::FormatWith,
    hir::{
        self, CallArgument, Case, ENode, ENodeArena, Elaborated, GetDictionary, LoopId,
        value::LiteralValue,
    },
    module::{
        self, FunctionId, ImportFunctionSlotId, LocalDeclId, LocalFunctionId, Module, ModuleEnv,
        ModuleId, TraitDictionary, TraitImpl, TraitImplId, id::Id,
    },
    ssa::{self, BlockIdentity, Program, value::FunctionReference},
    types::r#type::{FnArgType, Type},
};

/// Emits the textual representation of the low-level (aka SSA) ferlium IR of `module`.
///
/// Intended for testing & debugging.
pub fn emit_ssa(module: &Module, others: &Modules, session: &CompilerSession) -> String {
    let mut a: Vec<String> = vec![];
    for n in module.own_symbols() {
        a.push(format!("{:?}", n));
        if let Some(f) = module.get_local_function_id(n) {
            a.push(Emitter::emit_ssa_fn(f, module, others, session));
        }
    }
    a.join("\n")
}

/// Returns the qualified name of `f`.
fn function_name(f: LocalFunctionId, module: &Module, others: &Modules) -> Ustr {
    let e = ModuleEnv::new(module, others);
    let qualified_module = others.get_name(module.module_id()).unwrap();
    let function = e.current.get_function_name_by_id(f).unwrap();
    format!("{}::{}", qualified_module, function).into()
}

/// Returns the `ModuleId` and `LocalFunctionId` corresponding to an `ImportFunctionSlotId`.
fn imported_function(
    f: ImportFunctionSlotId,
    module: &Module,
    session: &CompilerSession,
) -> (LocalFunctionId, ModuleId) {
    let sl = module.get_import_fn_slot(f).unwrap();
    let mi = sl.module;
    let m = session.expect_fresh_module(mi);
    let fi = match &sl.target {
        module::ImportFunctionTarget::NamedFunction(name) => {
            m.get_local_function_id(*name).unwrap()
        }
        module::ImportFunctionTarget::TraitImplMethod { key, index } => {
            m.get_impl_data_by_trait_key(key).unwrap().methods[index.as_index()]
        }
    };
    (fi, mi)
}

/// How `arg` is conveyed into a callee, following `doc/hir-to-ssa.md` §4.
///
/// A mutable argument is an `&mut` / inferred-inout by-reference parameter. Other arguments are
/// by-value here; the non-`TrivialCopy` shared-reference case arrives with aggregates.
fn argument_passing(arg: &FnArgType) -> ssa::ArgumentPassing {
    if arg.mut_ty.is_mutable() {
        ssa::ArgumentPassing::MutableReference
    } else {
        ssa::ArgumentPassing::Value
    }
}

/// The SSA blocks involved in the lowering of a case in a match expression.
struct CaseBlocks {
    /// The head blocks for the conditions.
    heads: Vec<BlockIdentity>,

    /// The body blocks for the conditions.
    bodies: Vec<BlockIdentity>,

    /// The default case block.
    default: BlockIdentity,

    /// The tail block of the case.
    tail: BlockIdentity,
}

/// A constructor of SSA IR.
struct Emitter<'a> {
    /// The module being lowered.
    module: &'a Module,

    /// The other modules.
    others: &'a Modules,

    /// The context in which the emitter inserts new IR.
    context: InsertionContext,

    /// The HIR node arena.
    hir_arena: &'a ENodeArena,

    /// The current compiler session.
    session: &'a CompilerSession,
}

impl<'a> Emitter<'a> {
    /// Generates the IR of `source`, which has the given `identity`.
    fn emit_ssa_fn(
        identity: LocalFunctionId,
        module: &'a Module,
        others: &'a Modules,
        session: &'a CompilerSession,
    ) -> String {
        // TODO: This is the program into which IR is being inserted. Eventually that should become
        // an argument of the function, as this data structure should persist.
        let mut program = Program::new();

        let f = module.get_function_by_id(identity).unwrap();
        match f.code.as_ref().as_script() {
            Some(syntax) => {
                let name = module.get_function_name_by_id(identity).unwrap();
                let mut lowered = ssa::Function::new(name);

                // The function signature is laid out as `[extra dictionary/evidence params..., runtime
                // args...]`. Extra parameters occupy the leading slots `[0, extra_count)` and the visible
                // runtime arguments, which are the leading `LocalDecl`s, occupy `[extra_count, ..)`.
                let env = ModuleEnv::new(module, others);
                let extra = f.definition.ty_scheme.extra_parameters(env);
                let extra_count = extra.requirements.len();

                let mut extra_parameters: HashMap<ExtraParameterId, ssa::Value> = HashMap::new();
                for j in 0..extra_count {
                    extra_parameters
                        .insert(ExtraParameterId::from_index(j), ssa::Value::Parameter(j));
                }

                // Record the function signature in slot order: the extra (dictionary/evidence)
                // parameters first, then the visible runtime arguments (the leading `LocalDecl`s).
                for req in &extra.requirements {
                    lowered.add_parameter(req.to_dict_type_in_env(&env), ssa::ParameterKind::Extra);
                }

                // Classify and bind the argument locals per the slot rule (`doc/hir-to-ssa.md` §4). A
                // by-value (`TrivialCopy`) argument is its register directly; a by-reference argument's
                // register is the incoming pointer, so the local is bound to that place.
                let mut locals: HashMap<LocalDeclId, LocalBinding> = HashMap::new();
                for i in 0..f.definition.arg_names.len() {
                    let passing = argument_passing(&f.definition.ty_scheme.ty.args[i]);
                    lowered.add_parameter(f.locals[i].ty, ssa::ParameterKind::Argument(passing));
                    let param = ssa::Value::Parameter(extra_count + i);
                    let binding = match passing {
                        ssa::ArgumentPassing::Value => LocalBinding::Value(param),
                        ssa::ArgumentPassing::MutableReference
                        | ssa::ArgumentPassing::SharedReference => LocalBinding::Place(param),
                    };
                    locals.insert(LocalDeclId::from_index(i), binding);
                }

                // Create the function's entry.
                let entry = lowered.add_block().id();
                let code = &module.hir_arena[syntax.entry_node_id];
                let span = code.span;

                // Instantiate an emitter to generate the function's contents.
                let mut emitter = Emitter {
                    module,
                    others,
                    context: InsertionContext {
                        function: lowered,
                        source: identity,
                        point: InsertionPoint::End(entry),
                        span,
                        locals,
                        extra_parameters,
                        loop_results: HashMap::new(),
                    },
                    hir_arena: &module.hir_arena,
                    session,
                };

                // Allocate frame storage for every `Owned` local and bind it to its `alloca` place.
                emitter.allocate_owned_locals();

                // The body of the function evaluates to the return value.
                let v = emitter.lower_as_rvalue(code);
                emitter.insert(ssa::Instruction::ret(emitter.context.span, v));

                // Save the definition of the lowered function into the SSA program.
                let lowered = emitter.context.function;
                let g = program.set_definition(lowered);
                let env = ModuleEnv::new(module, others);
                format!("{}", g.format_with(&env))
            }

            None => panic!(),
        }
    }

    /// Returns a reference to the function identified by `f`.
    fn demand_function(&mut self, f: LocalFunctionId, module_identity: ModuleId) -> ssa::Value {
        let module = self.session.expect_fresh_module(module_identity);
        ssa::Value::Function(FunctionReference {
            identity: f,
            name: function_name(f, module, self.others),
            module: module_identity,
        })
    }

    /// Allocates frame storage for every [`LocalStorage::Owned`] local of the lowered function and
    /// binds it to its `alloca` place.
    ///
    /// Arguments are `NonOwning` and keep their by-value parameter binding. Non-owning, non-argument
    /// locals (aliases) are bound lazily when first stored, in a later phase.
    fn allocate_owned_locals(&mut self) {
        let f = self.module.get_function_by_id(self.context.source).unwrap();
        let owned: Vec<(LocalDeclId, Type)> = f
            .locals
            .iter()
            .enumerate()
            .filter(|(_, l)| l.owns_storage())
            .map(|(i, l)| (LocalDeclId::from_index(i), l.ty))
            .collect();
        for (id, ty) in owned {
            let place = self
                .insert(ssa::Instruction::alloca(self.context.span, ty))
                .unwrap();
            self.context.locals.insert(id, LocalBinding::Place(place));
        }
    }

    /// Returns the place (a pointer SSA value) backing the local `id`.
    ///
    /// - Requires: `id` is bound to a place (an `Owned` `alloca` or a by-reference parameter).
    fn place_of_local(&self, id: LocalDeclId) -> ssa::Value {
        match self.context.locals.get(&id) {
            Some(LocalBinding::Place(p)) => p.clone(),
            Some(LocalBinding::Value(_)) => {
                panic!("local {:?} is bound by value and has no place", id)
            }
            None => panic!("local {:?} is not bound in the current frame", id),
        }
    }

    /// Generates the IR for `node` used as a place, returning a pointer SSA value.
    ///
    /// Mirrors the interpreter's `try_eval_node_as_place`.
    fn lower_as_place(&mut self, node: &ENode) -> ssa::Value {
        use hir::NodeKind as K;
        match &node.kind {
            K::LoadLocal(n) => self.place_of_local(n.id),
            _ => todo!(
                "lower_as_place is unimplemented for node kind {:?}",
                node.kind
            ),
        }
    }

    /// Lowers `arg` to its call operand per the resolved passing mode.
    ///
    /// A `MutableRef` (`&mut` / inout) argument is lowered as a place: a pointer the callee mutates
    /// through. A `TrivialCopy` value is lowered as an rvalue. A `SharedRef` is also lowered as an
    /// rvalue for now: under the iteration-1 value model a shared borrow is the value register
    /// itself; true shared-borrow places and temporary materialization arrive with aggregates.
    /// - See: `doc/hir-to-ssa.md` §6
    fn lower_argument(&mut self, arg: &CallArgument<Elaborated>) -> ssa::Value {
        match arg.passing {
            ResolvedArgPassing::MutableRef => self.lower_as_place(&self.hir_arena[arg.value]),
            ResolvedArgPassing::Value(
                ResolvedValueArgPassing::TrivialCopy(_) | ResolvedValueArgPassing::SharedRef { .. },
            ) => self.lower_as_rvalue(&self.hir_arena[arg.value]),
        }
    }

    /// Returns the blocks created for `n`.
    fn create_case_blocks(&mut self, n: &Box<Case<Elaborated>>) -> CaseBlocks {
        let mut heads: Vec<BlockIdentity> = vec![];
        let mut bodies: Vec<BlockIdentity> = vec![];
        for _ in n.alternatives.iter() {
            heads.push(self.context.function.add_block().id());
            bodies.push(self.context.function.add_block().id());
        }
        let default: BlockIdentity = self.context.function.add_block().id();
        let tail: BlockIdentity = self.context.function.add_block().id();
        CaseBlocks {
            heads,
            bodies,
            default,
            tail,
        }
    }

    /// Returns a copy of the dictionary value held by `t`.
    fn dictionary_value(&mut self, t: &GetDictionary) -> (TraitDictionary, ModuleId) {
        match t.dictionary {
            TraitImplId::Local(id) => (
                self.dictionary_value_from_trait(self.module.get_impl_data(id)),
                self.module.module_id(),
            ),
            TraitImplId::Import(id) => {
                let slot = self.module.get_import_impl_slot(id).unwrap();
                let other_module = self.others.get(slot.module).unwrap().module().unwrap();
                (
                    self.dictionary_value_from_trait(
                        other_module.get_impl_data_by_trait_key(&slot.key),
                    ),
                    other_module.module_id(),
                )
            }
        }
    }

    /// Returns a copy of the dictionary value of `t`.
    fn dictionary_value_from_trait(&self, t: Option<&TraitImpl>) -> TraitDictionary {
        t.unwrap().dictionary_value.clone()
    }

    /// Returns the SSA Dictionary lowered from `n`.
    fn lower(&mut self, n: &GetDictionary) -> ssa::Value {
        let (d, m) = self.dictionary_value(n);
        ssa::Value::Dictionary(
            d.methods()
                .iter()
                .map(|x| self.demand_function(*x, m))
                .collect(),
        )
    }

    /// Generates the IR for `node`, which occurs as rvalue.
    fn lower_as_rvalue(&mut self, node: &ENode) -> ssa::Value {
        use hir::NodeKind as K;
        match &node.kind {
            K::Block(n) => {
                let arena = self.hir_arena;
                n.body
                    .iter()
                    .map(|s| self.lower_as_rvalue(&arena[*s]))
                    .last()
                    .unwrap_or(ssa::Value::Unit)

                // todo emit cleanup
            }

            K::Case(n) => {
                let blocks = self.create_case_blocks(n);

                // We lower the scrutinee before the case blocks so that its value can be used in all conditions.
                let scrutinee = self.lower_as_rvalue(&self.hir_arena[n.value]);

                // Create a temporary allocation to store the result of the match.
                let temporary = self
                    .insert(ssa::Instruction::alloca(node.span, node.ty))
                    .unwrap();
                self.insert(ssa::Instruction::br(node.span, blocks.heads[0]));

                // Lower the alternatives.
                for (i, (c, a)) in n.alternatives.iter().enumerate() {
                    // Load the next alternative's condition if there's one. Otherwise, we've reached the
                    // default case.
                    let next = if i < n.alternatives.len() - 1 {
                        blocks.heads[i + 1]
                    } else {
                        blocks.default
                    };

                    // Transfer control flow to the head of the match.
                    self.context.point = InsertionPoint::End(blocks.heads[i]);

                    // Lower the pattern
                    let x0 = self.lower_as_primitive(c).unwrap();
                    // Compare the condition with the scrutinee and, depending on the result, branch to
                    // either the body of the current alternative or the next head.
                    let v = self
                        .insert(ssa::Instruction::compare_eq(
                            node.span,
                            scrutinee.clone(),
                            x0,
                        ))
                        .unwrap();
                    self.insert(ssa::Instruction::condbr(
                        node.span,
                        v,
                        blocks.bodies[i],
                        next,
                    ));

                    // Lower the body of the alternative.
                    self.context.point = InsertionPoint::End(blocks.bodies[i]);
                    let x1 = self.lower_as_rvalue(&self.hir_arena[*a]);

                    // Store the result of the expression.
                    self.insert(ssa::Instruction::store(node.span, x1, temporary.clone()));
                    self.insert(ssa::Instruction::br(node.span, blocks.tail));
                }

                // Default case.
                self.context.point = InsertionPoint::End(blocks.default);
                let v = self.lower_as_rvalue(&self.hir_arena[n.default]);
                self.insert(ssa::Instruction::store(node.span, v, temporary.clone()));
                self.insert(ssa::Instruction::br(node.span, blocks.tail));

                // Tail.
                self.context.point = InsertionPoint::End(blocks.tail);
                self.insert(ssa::Instruction::load(node.span, temporary))
                    .unwrap()
            }

            K::Immediate(n) => {
                if let Some(result) = self.lower_as_primitive(n) {
                    result
                } else {
                    let s = self.show(node.ty);
                    panic!(
                        "lowering is unimplemented for node of kind '{:?}' of type {:?}",
                        n, s
                    )
                }
            }

            K::Assign(n) => {
                // Drop the previous destination value first if required. `Skip` and an uninitialized
                // (`None`) destination need no semantic drop; `Static`/`Dictionary` drops are Phase 4.
                match n.drop {
                    None | Some(ResolvedLocalDrop::Skip) => {}
                    Some(ResolvedLocalDrop::Static(_)) | Some(ResolvedLocalDrop::Dictionary(_)) => {
                        todo!("Assign drop via Value::drop is not lowered yet")
                    }
                }
                let value = self.lower_as_rvalue(&self.hir_arena[n.value]);
                let place = self.lower_as_place(&self.hir_arena[n.place]);
                self.insert(ssa::Instruction::store(node.span, value, place));
                ssa::Value::Unit
            }

            K::LoadLocal(n) => {
                // A by-value binding yields its value directly; a place binding (an `Owned` alloca or a
                // by-reference parameter) is loaded.
                match self.context.locals.get(&n.id) {
                    Some(LocalBinding::Value(v)) => v.clone(),
                    Some(LocalBinding::Place(p)) => {
                        let p = p.clone();
                        self.insert(ssa::Instruction::load(node.span, p)).unwrap()
                    }
                    None => panic!("local {:?} is not bound in the current frame", n.id),
                }
            }

            K::StoreLocal(n) => {
                // Initialize the local's storage. The local's `clone` dispatch decides how the value is
                // produced: `None`/`TrivialCopy` stores the loaded value directly; `Static`/`Dictionary`
                // perform `Value::clone` into the target (Phase 4).
                let clone = self
                    .module
                    .get_function_by_id(self.context.source)
                    .unwrap()
                    .locals[n.id.as_index()]
                .clone;
                match clone {
                    None | Some(ResolvedLocalClone::TrivialCopy(_)) => {
                        let value = self.lower_as_rvalue(&self.hir_arena[n.value]);
                        let place = self.place_of_local(n.id);
                        self.insert(ssa::Instruction::store(node.span, value, place));
                    }
                    Some(ResolvedLocalClone::Static(_))
                    | Some(ResolvedLocalClone::Dictionary(_)) => {
                        todo!("StoreLocal initialization via Value::clone is not lowered yet")
                    }
                }
                ssa::Value::Unit
            }

            K::CloneValue(n) => {
                let source = self.lower_as_rvalue(&self.hir_arena[n.source]);
                match n.clone {
                    // A trivial copy of an already-loaded value is the same SSA value: copying the
                    // representation of a register is a no-op at this logical level. A later ABI pass may
                    // materialize an explicit storage copy where one is physically required.
                    ResolvedLocalClone::TrivialCopy(_) => source,
                    // `Value::clone(source, &mut target)` dispatch is introduced in Phase 4.
                    ResolvedLocalClone::Static(_) | ResolvedLocalClone::Dictionary(_) => {
                        todo!("CloneValue via Value::clone (Static/Dictionary) is not lowered yet")
                    }
                }
            }

            K::TakeLocalValue(n) => {
                match n.mode {
                    ResolvedTakeLocalValueMode::MoveOwned => {
                        // Move the owned value out: load the place and skip its lexical drop (cleanup is
                        // handled in Phase 9). A by-value binding yields its value directly.
                        match self.context.locals.get(&n.id) {
                            Some(LocalBinding::Place(p)) => {
                                let p = p.clone();
                                self.insert(ssa::Instruction::load(node.span, p)).unwrap()
                            }
                            Some(LocalBinding::Value(v)) => v.clone(),
                            None => panic!("local {:?} is not bound in the current frame", n.id),
                        }
                    }
                    ResolvedTakeLocalValueMode::CloneBorrowed(_) => {
                        todo!("TakeLocalValue CloneBorrowed is not lowered yet")
                    }
                }
            }

            K::StaticApply(n) => {
                let (fi, mi) = match n.function {
                    FunctionId::Local(i) => (i, self.module.module_id()),
                    FunctionId::Import(i) => imported_function(i, self.module, self.session),
                };
                let f = self.demand_function(fi, mi);
                let mut arguments: Vec<ssa::Value> = vec![];
                for x in &n.extra_arguments {
                    arguments.push(self.lower_as_rvalue(&self.hir_arena[*x]));
                }
                for arg in &n.arguments {
                    arguments.push(self.lower_argument(arg));
                }

                assert_eq!(node.ty, n.ty.ret);
                self.insert(ssa::Instruction::call(node.span, f, arguments, n.ty.ret))
                    .unwrap()
            }

            K::GetDictionary(d) => self.lower(d),

            K::Apply(n) => {
                let f = self.lower_as_rvalue(&self.hir_arena[n.function]);
                let a: Vec<ssa::Value> = n
                    .arguments
                    .iter()
                    .map(|arg| self.lower_argument(arg))
                    .collect();

                self.insert(ssa::Instruction::call(
                    node.span,
                    f,
                    a,
                    self.hir_arena[n.function].ty,
                ))
                .unwrap()
            }

            K::Project(n) => {
                let m = &self.hir_arena[n.value];

                let v = self.lower_as_rvalue(m);

                self.insert(ssa::Instruction::project(
                    node.span,
                    v,
                    n.index.as_index(),
                    node.ty,
                ))
                .unwrap()
            }

            K::Loop(n) => {
                // Create a temporary allocation to store the result of the match.
                let result = self
                    .insert(ssa::Instruction::alloca(node.span, node.ty))
                    .unwrap();
                self.context.loop_results.insert(n.label, result.clone());

                self.lower_as_rvalue(&self.hir_arena[n.body]);

                // TODO: result is the alloca pointer. lower_as_rvalue must return the value, so this needs a load result like Case does (emit_ssa.rs:374). Additionally there is no loop head/back-edge/exit block emitted, and Break/Continue are unhandled (they fall through to todo!), so Loop is effectively non-functional. §5 marks Loop/Break/Continue as ✅; either complete them or this should be a clearly-scoped TODO.

                result
            }

            K::ExtractTag(_n) => {
                // TODO: N should be a variant, which will be lowered to either a `ssa::Value::Tuple` or to a new `ssa::Value::Variant`
                // So we should either extract the tag with a fixed index for the tuple, or accessing a custom property of the variant.
                todo!("Lowering for ExtractTag is unimplemented");
            }

            K::Variant(_) => {
                // TODO: Implemented this either by lowering it to a `ssa::Value::Tuple`, a `ssa::Value::Variant`
                todo!("Lowering for Variant is unimplemented");
            }

            K::LoadDictionary(n) => {
                // A required dictionary/evidence resolves to its incoming extra parameter.
                self.context.extra_parameters[&n.extra_parameter].clone()
            }

            K::CallDictionaryMethod(n) => {
                // Look up the method function value by projecting it out of the dictionary, then call it.
                let dict = self.lower_as_rvalue(&self.hir_arena[n.dictionary]);
                let method_ty = Type::function_type(n.ty.clone());
                let method = self
                    .insert(ssa::Instruction::project(
                        node.span,
                        dict,
                        n.entry_index.as_index(),
                        method_ty,
                    ))
                    .unwrap();
                let mut a: Vec<ssa::Value> = vec![];
                for arg in &n.arguments {
                    a.push(self.lower_argument(arg));
                }
                self.insert(ssa::Instruction::call(node.span, method, a, n.ty.ret))
                    .unwrap()
            }

            // Runtime guards have no SSA representation yet; they lower to nothing.
            K::CheckCallDepth | K::CheckFuel => ssa::Value::Unit,

            _ => {
                todo!(
                    "lowering is unimplemented for node of kind '{:?}'",
                    node.kind
                );
            }
        }
    }

    /// Returns the lowered representation of the given native value.
    fn lower_as_primitive(&mut self, native: &LiteralValue) -> Option<ssa::Value> {
        use ssa::value::Integer as Int;

        if native.as_primitive_ty::<()>().is_some() {
            Some(ssa::Value::Unit)
        } else if let Some(n) = native.as_primitive_ty::<isize>() {
            Some(ssa::Value::Integer(containers::b(Int::from_isize(*n))))
        } else if let Some(n) = native.as_primitive_ty::<u32>() {
            Some(ssa::Value::Integer(containers::b(Int::from_u32(*n))))
        } else if let Some(n) = native.as_primitive_ty::<i32>() {
            Some(ssa::Value::Integer(containers::b(Int::from_i32(*n))))
        } else if let Some(n) = native.as_primitive_ty::<bool>() {
            Some(ssa::Value::Boolean(*n))
        } else {
            None
        }
    }

    /// Inserts `s` at the current insertion point and returns the register assigned by
    /// that instruction, if any.
    fn insert(&mut self, s: ssa::Instruction) -> Option<ssa::Value> {
        let i = match &self.context.point {
            InsertionPoint::End(b) => self.context.function.block_mut(*b).append(s),
        };
        self.context.function.definition(i)
    }

    /// Returns a textual representation of `x`.
    fn show<T: FormatWith<ModuleEnv<'a>>>(&self, x: T) -> String {
        let e = ModuleEnv::new(self.module, self.others);
        format!("{}", x.format_with(&e))
    }
}

/// How a source-level local is bound in the SSA frame.
///
/// Mirrors the interpreter's `ValOrMut`: a by-value parameter is held directly in an SSA
/// register, while an owning `alloca` or a by-reference parameter is a pointer to storage.
#[derive(Clone)]
enum LocalBinding {
    /// An owned value held directly in an SSA register (a by-value `TrivialCopy` parameter).
    Value(ssa::Value),

    /// A pointer to storage: an owning `alloca` or a by-reference parameter.
    Place(ssa::Value),
}

/// The context in which instructions are inserted.
struct InsertionContext {
    /// The function in which new instructions are inserted.
    function: ssa::Function,

    /// The function we are lowering from.
    source: LocalFunctionId,

    /// Where new instructions are inserted in `function`.
    point: InsertionPoint,

    /// The source region with which inserted instructions are associated.
    span: Location,

    /// The SSA bindings of the function's locals, including explicit arguments and any
    /// variables declared within the function.
    locals: HashMap<LocalDeclId, LocalBinding>,

    /// The SSA values bound to extra parameters of the function.
    extra_parameters: HashMap<ExtraParameterId, ssa::Value>,

    /// The SSA register (an `alloca` result) holding the result of each active loop,
    /// keyed by the loop's `LoopId`. A `break` stores its value into this register and
    /// the loop's exit block loads it.
    loop_results: HashMap<LoopId, ssa::Value>,
}

/// Where an instruction should be inserted in a basic block.
enum InsertionPoint {
    /// The end of a basic block.
    End(BlockIdentity),
}
