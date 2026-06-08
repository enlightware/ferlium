use std::collections::HashMap;

use ustr::Ustr;

use crate::module::{
    ExtraParameterId, ResolvedLocalClone, ResolvedLocalDrop, ResolvedTakeLocalValueMode,
};
use crate::{
    containers, format::FormatWith, hir::{
        self, value::LiteralValue, CallArgument, Case, ENode, ENodeArena, Elaborated, GetDictionary,
        LoopId,
    }, module::{
        self, id::Id, FunctionId, ImportFunctionSlotId, LocalDeclId, LocalFunctionId, Module,
        ModuleEnv, ModuleId, TraitDictionary, TraitImpl, TraitImplId,
    },
    ssa::{self, value::FunctionReference, BlockIdentity, Program},
    types::r#type::Type,
    CompilerSession,
    Location,
    Modules,
};

/// Emits the textual representation of the low-level (aka SSA) ferlium IR of `module`.
///
/// Intended for testing & debugging.
pub fn emit_ssa(module: &Module, others: &Modules, session: &CompilerSession) -> String {
    module
        .own_symbols()
        .filter_map(|n| module.get_local_function_id(n))
        .map(|f| Emitter::emit_ssa_fn(f, module, others, session))
        .collect::<Vec<_>>()
        .join("\n")
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
    /// Generates the IR of `source`.
    fn emit_ssa_fn(
        source: LocalFunctionId,
        module: &'a Module,
        others: &'a Modules,
        session: &'a CompilerSession,
    ) -> String {
        // TODO: This is the program into which IR is being inserted. Eventually that should become
        // an argument of the function, as this data structure should persist.
        let mut program = Program::new();

        let f = module.get_function_by_id(source).unwrap();
        let syntax = f
            .code
            .as_ref()
            .as_script()
            .expect("function should be a script");

        let name = module.get_function_name_by_id(source).unwrap();
        let mut lowered = ssa::Function::new(name);

        // The function signature is laid out as `[extra dictionary/evidence params..., runtime
        // args...]`. Extra parameters occupy the leading slots `[0, extra_count)` and the visible
        // runtime arguments, which are the leading `LocalDecl`s, occupy `[extra_count, ..)`.
        let env = ModuleEnv::new(module, others);
        let extra = f.definition.ty_scheme.extra_parameters(env);
        let extra_count = extra.requirements.len();

        let mut extra_parameters: HashMap<ExtraParameterId, ssa::Value> = HashMap::new();
        for j in 0..extra_count {
            extra_parameters.insert(ExtraParameterId::from_index(j), ssa::Value::Parameter(j));
        }

        // Record the function signature in slot order: the extra (dictionary/evidence)
        // parameters first, then the visible runtime arguments (the leading `LocalDecl`s).
        for req in &extra.requirements {
            lowered.add_parameter(req.to_dict_type_in_env(&env), ssa::ParameterTag::Dictionary);
        }

        // Bind the argument locals. Every parameter is passed by pointer (the resolved passing is
        // recorded in the signature only as the obligation a later backend may relax to direct
        // passing per `doc/abi.md`), so each argument local is the place its incoming pointer
        // denotes.
        let mut locals: HashMap<LocalDeclId, ssa::Value> = HashMap::new();
        for i in 0..f.definition.arg_names.len() {
            let resolved = syntax.param_passing[i];
            lowered.add_parameter(f.locals[i].ty, ssa::ParameterTag::Parameter(resolved));
            let param = ssa::Value::Parameter(extra_count + i);
            locals.insert(LocalDeclId::from_index(i), param);
        }

        // Append the return out-pointer as the last parameter. It is present unconditionally, even
        // when the return type is `()`: the function writes its result through this pointer and then
        // returns with no operand.
        let return_type = f.definition.ty_scheme.ty.ret;
        let return_destination =
            ssa::Value::Parameter(lowered.add_parameter(return_type, ssa::ParameterTag::Return));

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
                source,
                point: InsertionPoint::End(entry),
                span,
                locals,
                extra_parameters,
                loop_results: HashMap::new(),
                return_destination,
            },
            hir_arena: &module.hir_arena,
            session,
        };

        // Allocate frame storage for every `Owned` local and bind it to its `alloca` place.
        emitter.allocate_owned_locals();

        // The body of the function stores its result into the return out-pointer and then returns.
        let ret_dest = emitter.context.return_destination.clone();
        emitter.lower_into(code, Some(ret_dest));
        emitter.insert(ssa::Instruction::ret(emitter.context.span));

        // Save the definition of the lowered function into the SSA program.
        let lowered = emitter.context.function;
        let g = program.define(lowered);
        let env = ModuleEnv::new(module, others);

        format!("{}", g.format_with(&env))
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
            self.context.locals.insert(id, place);
        }
    }

    /// Returns the place (a pointer SSA value) backing the local `l`.
    ///
    /// Every local is bound to a place: an incoming by-pointer parameter or an `Owned` `alloca`.
    fn place_of_local(&self, l: LocalDeclId) -> ssa::Value {
        self.context
            .locals
            .get(&l)
            .expect("local must be bound in the current frame")
            .clone()
    }

    /// Lowers `node` as a place, returning a pointer SSA value to the storage holding its value.
    ///
    /// Place-denoting nodes (a local, a projection) return their storage directly. Any other node
    /// is materialized into a fresh owned temporary (`alloca` + store its value) whose pointer is
    /// returned. Cleanup of a materialized temporary is not emitted yet.
    ///
    /// Mirrors the interpreter's `try_eval_node_as_place`.
    fn lower_as_place(&mut self, node: &ENode) -> ssa::Value {
        use hir::NodeKind as K;
        match &node.kind {
            K::LoadLocal(n) => self.place_of_local(n.id),
            // A required dictionary/evidence is its incoming extra parameter, itself a place.
            K::LoadDictionary(n) => self.context.extra_parameters[&n.extra_parameter].clone(),
            K::Project(n) => {
                let base = self.lower_as_place(&self.hir_arena[n.value]);
                self.insert(ssa::Instruction::project(
                    node.span,
                    base,
                    n.index.as_index(),
                    node.ty,
                ))
                .unwrap()
            }
            // A value-producing node is materialized into a temporary place.
            _ => {
                let temp = self
                    .insert(ssa::Instruction::alloca(node.span, node.ty))
                    .unwrap();
                self.lower_into(node, Some(temp.clone()));
                temp
            }
        }
    }

    /// Lowers `node` as a register value (a loaded scalar / value held directly in an SSA register).
    ///
    /// A primitive immediate is produced directly; any other node is lowered as a place and the
    /// value is `load`ed from it.
    fn lower_as_register(&mut self, node: &ENode) -> ssa::Value {
        use hir::NodeKind as K;
        if let K::Immediate(n) = &node.kind
            && let Some(prim) = self.lower_as_primitive(n)
        {
            return prim;
        }
        let place = self.lower_as_place(node);
        self.insert(ssa::Instruction::load(node.span, place))
            .unwrap()
    }

    /// Lowers `arg` to its call operand: a pointer to the argument's storage. Every argument is
    /// passed by pointer; the resolved passing mode is recorded only in the callee's signature.
    fn lower_argument(&mut self, arg: &CallArgument<Elaborated>) -> ssa::Value {
        self.lower_as_place(&self.hir_arena[arg.value])
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

    /// Stores the register `value` into `dest` if a destination is present; a `None` `dest`
    /// discards the value.
    fn store_into(&mut self, span: Location, value: ssa::Value, dest: Option<ssa::Value>) {
        if let Some(dest) = dest {
            self.insert(ssa::Instruction::store(span, value, dest));
        }
    }

    /// Returns the out-pointer to pass to a call producing `node`'s value, given the caller's
    /// destination. Every call receives an out-pointer unconditionally, even `()`-typed ones: the
    /// caller's destination is used, or a fresh throwaway temporary when the result is discarded.
    fn call_out_ptr(&mut self, node: &ENode, dest: Option<ssa::Value>) -> ssa::Value {
        if let Some(dest) = dest {
            dest
        } else {
            self.insert(ssa::Instruction::alloca(node.span, node.ty))
                .unwrap()
        }
    }

    /// Lowers `node` in destination-passing style: the value produced by `node` is stored into the
    /// storage pointed to by `dest`. A `None` `dest` denotes a discarded result (effects only); a
    /// `()`-typed node also has nothing to store.
    fn lower_into(&mut self, node: &ENode, dest: Option<ssa::Value>) {
        use hir::NodeKind as K;
        match &node.kind {
            K::Block(n) => {
                // Lower each statement for its effects; the block's value is its tail node, which is
                // lowered into the destination.
                if let Some((tail, init)) = n.body.split_last() {
                    for s in init {
                        self.lower_into(&self.hir_arena[*s], None);
                    }
                    self.lower_into(&self.hir_arena[*tail], dest);
                }
                // todo emit cleanup
            }

            K::Case(n) => {
                // TODO make this work for non-primitive types, using the Value dictionary's `eq` or a statically resolved conformance.

                let blocks = self.create_case_blocks(n);

                // We lower the scrutinee before the case blocks so that its value can be used in all conditions.
                let scrutinee = self.lower_as_register(&self.hir_arena[n.value]);

                self.insert(ssa::Instruction::br(node.span, blocks.heads[0]));

                // Lower the alternatives. Each alternative stores its value directly into `dest`.
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

                    let alternative_pattern = self.lower_as_primitive(c).unwrap();

                    // Compare the condition with the scrutinee and, depending on the result, branch to
                    // either the body of the current alternative or the next head.
                    let v = self
                        .insert(ssa::Instruction::compare_eq(
                            node.span,
                            scrutinee.clone(),
                            alternative_pattern,
                        ))
                        .unwrap();
                    self.insert(ssa::Instruction::condbr(
                        node.span,
                        v,
                        blocks.bodies[i],
                        next,
                    ));

                    // Lower the body of the alternative into the destination.
                    self.context.point = InsertionPoint::End(blocks.bodies[i]);
                    self.lower_into(&self.hir_arena[*a], dest.clone());
                    self.insert(ssa::Instruction::br(node.span, blocks.tail));
                }

                // Default case.
                self.context.point = InsertionPoint::End(blocks.default);
                self.lower_into(&self.hir_arena[n.default], dest.clone());
                self.insert(ssa::Instruction::br(node.span, blocks.tail));

                // Tail. The value has already been stored into `dest`.
                self.context.point = InsertionPoint::End(blocks.tail);
            }

            K::Immediate(n) => {
                if n.as_primitive_ty::<()>().is_some() {
                    // Storing void would be redundant.
                } else if let Some(value) = self.lower_as_primitive(n) {
                    self.store_into(node.span, value, dest);
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
                // (`None`) destination need no semantic drop; `Static`/`Dictionary` drops are deferred.
                match n.drop {
                    None | Some(ResolvedLocalDrop::Skip) => {}
                    Some(ResolvedLocalDrop::Static(_)) | Some(ResolvedLocalDrop::Dictionary(_)) => {
                        todo!("Assign drop via Value::drop is not lowered yet")
                    }
                }
                let place = self.lower_as_place(&self.hir_arena[n.place]);
                self.lower_into(&self.hir_arena[n.value], Some(place));
                // `Assign` is `()`-typed: nothing to store into `dest`.
            }

            K::LoadLocal(n) => {
                // A bare load in value position is a trivial-copy read (non-trivial reads are wrapped
                // in `CloneValue`/`TakeLocalValue` by HIR): load the local's place and store it.
                if dest.is_some() {
                    let p = self.place_of_local(n.id);
                    let v = self.insert(ssa::Instruction::load(node.span, p)).unwrap();
                    self.store_into(node.span, v, dest);
                }
            }

            K::StoreLocal(n) => {
                // Initialize the local's storage. The local's `clone` dispatch decides how the value is
                // produced: `None`/`TrivialCopy` stores the produced value directly; `Static`/`Dictionary`
                // perform `Value::clone` into the target (deferred).

                let clone = self
                    .module
                    .get_function_by_id(self.context.source)
                    .unwrap()
                    .locals[n.id.as_index()]
                .clone;
                match clone {
                    None | Some(ResolvedLocalClone::TrivialCopy(_)) => {
                        let place = self.place_of_local(n.id);
                        self.lower_into(&self.hir_arena[n.value], Some(place));
                    }
                    Some(ResolvedLocalClone::Static(_))
                    | Some(ResolvedLocalClone::Dictionary(_)) => {
                        todo!("StoreLocal initialization via Value::clone is not lowered yet")
                    }
                }
                // `StoreLocal` is `()`-typed: nothing to store into `dest`.
            }

            K::CloneValue(n) => {
                match n.clone {
                    // A trivial copy: load the source place and store it into the destination. A later
                    // ABI pass may relax this to direct passing where physically possible.
                    ResolvedLocalClone::TrivialCopy(_) => {
                        self.lower_into(&self.hir_arena[n.source], dest);
                    }
                    // `Value::clone(source, &mut target)` dispatch is deferred.
                    ResolvedLocalClone::Static(_) | ResolvedLocalClone::Dictionary(_) => {
                        todo!("CloneValue via Value::clone (Static/Dictionary) is not lowered yet")
                    }
                }
            }

            K::TakeLocalValue(n) => match n.mode {
                ResolvedTakeLocalValueMode::MoveOwned => {
                    // Move the owned value out: load the place and store it into the destination,
                    // skipping the local's lexical drop (cleanup is deferred).
                    if dest.is_some() {
                        let p = self.place_of_local(n.id);
                        let v = self.insert(ssa::Instruction::load(node.span, p)).unwrap();
                        self.store_into(node.span, v, dest);
                    }
                }
                ResolvedTakeLocalValueMode::CloneBorrowed(_) => {
                    todo!("TakeLocalValue CloneBorrowed is not lowered yet")
                }
            },

            K::StaticApply(n) => {
                let (fi, mi) = match n.function {
                    FunctionId::Local(i) => (i, self.module.module_id()),
                    FunctionId::Import(i) => imported_function(i, self.module, self.session),
                };
                let f = self.demand_function(fi, mi);
                let mut arguments: Vec<ssa::Value> = vec![];
                for x in &n.extra_arguments {
                    arguments.push(self.lower_as_place(&self.hir_arena[*x]));
                }
                for arg in &n.arguments {
                    arguments.push(self.lower_argument(arg));
                }

                assert_eq!(node.ty, n.ty.ret);
                arguments.push(self.call_out_ptr(node, dest));
                self.insert(ssa::Instruction::call(node.span, f, arguments, n.ty.ret));
            }

            K::GetDictionary(d) => {
                let dict = self.lower(d);
                self.store_into(node.span, dict, dest);
            }

            K::Apply(n) => {
                let f = self.lower_as_register(&self.hir_arena[n.function]);
                let mut arguments: Vec<ssa::Value> = n
                    .arguments
                    .iter()
                    .map(|arg| self.lower_argument(arg))
                    .collect();
                arguments.push(self.call_out_ptr(node, dest));
                self.insert(ssa::Instruction::call(node.span, f, arguments, n.ty.ret));
            }

            K::Project(_) => {
                // A projection is a place: load the field place and store it into the destination
                // (trivial copy; non-trivial reads are wrapped in `CloneValue` by HIR).
                if dest.is_some() {
                    let fp = self.lower_as_place(node);
                    let v = self.insert(ssa::Instruction::load(node.span, fp)).unwrap();
                    self.store_into(node.span, v, dest);
                }
            }

            K::Loop(n) => {
                // The loop's result is written into `dest` (or a throwaway temporary when discarded).
                let result = match &dest {
                    Some(dest) => dest.clone(),
                    None => self
                        .insert(ssa::Instruction::alloca(node.span, node.ty))
                        .unwrap(),
                };
                self.context.loop_results.insert(n.label, result);

                self.lower_into(&self.hir_arena[n.body], None);

                // TODO: no loop head/back-edge/exit block is emitted and Break/Continue are unhandled
                // (they fall through to todo!), so Loop is effectively non-functional.
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
                // A required dictionary/evidence resolves to its incoming extra parameter, which is a
                // place. Copy it into the destination if one is requested.
                if dest.is_some() {
                    let p = self.context.extra_parameters[&n.extra_parameter].clone();
                    let v = self.insert(ssa::Instruction::load(node.span, p)).unwrap();
                    self.store_into(node.span, v, dest);
                }
            }

            K::CallDictionaryMethod(n) => {
                // Project the method's storage out of the dictionary place, load the function
                // reference, then call it.
                let dict = self.lower_as_place(&self.hir_arena[n.dictionary]);
                let method_ty = Type::function_type(n.ty.clone());
                let method_place = self
                    .insert(ssa::Instruction::project(
                        node.span,
                        dict,
                        n.entry_index.as_index(),
                        method_ty,
                    ))
                    .unwrap();
                let method = self
                    .insert(ssa::Instruction::load(node.span, method_place))
                    .unwrap();

                let mut arguments: Vec<ssa::Value> =
                    n.arguments.iter().map(|a| self.lower_argument(a)).collect();
                arguments.push(self.call_out_ptr(node, dest));
                self.insert(ssa::Instruction::call(
                    node.span, method, arguments, n.ty.ret,
                ));
            }

            // Runtime guards have no SSA representation yet; they lower to nothing.
            K::CheckCallDepth | K::CheckFuel => {}

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

    /// Inserts `s` at the current insertion point, and returns its result register, if any.
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

    /// The SSA places (pointer values) backing the function's locals, including explicit arguments
    /// (each passed by pointer) and any variables declared within the function.
    locals: HashMap<LocalDeclId, ssa::Value>,

    /// The SSA values bound to extra parameters of the function.
    extra_parameters: HashMap<ExtraParameterId, ssa::Value>,

    /// The SSA place (an `alloca` result or the return out-pointer) into which each active loop
    /// writes its result via `break`, keyed by the loop's `LoopId`.
    loop_results: HashMap<LoopId, ssa::Value>,

    /// The return out-pointer (the last parameter) into which the function writes its result.
    return_destination: ssa::Value,
}

/// Where an instruction should be inserted in a basic block.
enum InsertionPoint {
    /// The end of a basic block.
    End(BlockIdentity),
}
