use std::collections::HashMap;

use ordered_float::NotNan;
use ustr::Ustr;

use crate::module::{
    ExtraParameterId, ResolvedLocalClone, ResolvedLocalDrop, ResolvedTakeLocalValueMode,
};
use crate::ssa::Instruction;
use crate::ssa::value::ShownType;
use crate::types::r#type::{FnReturnConvention, FnType};
use crate::{
    CompilerSession, Location, Modules, containers,
    format::FormatWith,
    hir::{
        self, CallArgument, Case, ENode, ENodeArena, Elaborated, GetDictionary, LoopId,
        dictionary::DictionaryReq, value::LiteralValue,
    },
    module::{
        self, FunctionId, ImportFunctionSlotId, LocalDeclId, LocalFunctionId, Module, ModuleEnv,
        ModuleId, TraitDictionary, TraitImpl, TraitImplId, id::Id,
    },
    ssa::{self, BlockIdentity, value::FunctionReference},
    std::{
        STD_MODULE_ID,
        core_traits_names::VALUE_TRAIT_NAME,
        math::Float,
        value::{VALUE_CLONE_METHOD_INDEX, is_function_surface_only_value_type},
    },
    types::r#type::Type,
    types::type_like::TypeLike,
};

/// Emits the textual representation of the low-level (aka SSA) ferlium IR of `module`.
///
/// Every lowerable local function of `module` is emitted, including the (anonymous) member
/// functions of its subscripts. Bodiless (native) functions and inline-only `YieldedOnce`
/// subscript members — which have no standalone SSA form and are consumed at their `WithYielded`
/// site — are skipped.
///
/// Intended for testing & debugging.
pub fn emit_ssa(module: &Module, others: &Modules, session: &CompilerSession) -> String {
    let mut functions: Vec<(Ustr, LocalFunctionId)> = (0..module.function_count())
        .map(LocalFunctionId::from_index)
        .filter_map(|id| {
            let f = module.get_function_by_id(id)?;
            // Only script functions have a body to lower.
            f.code.as_ref().as_script()?;
            // A `YieldedOnce` member is inline-only: emitted at its `WithYielded` site, never here.
            if f.definition.return_convention() == FnReturnConvention::YieldedOnce {
                return None;
            }
            // A subscript member resolves to its subscript's name; truly anonymous functions are skipped.
            let name = module.get_function_name_by_id(id)?;
            Some((name, id))
        })
        .collect();
    functions.sort_by_key(|(name, id)| (*name, id.as_index()));
    functions
        .into_iter()
        .map(|(_, f)| Emitter::emit_ssa_fn(f, module, others, session))
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
        &module::function::ImportFunctionTarget::SubscriptMember { name, mut_member } => {
            // Resolve the subscript bundle, then select the ref or mut member's function.
            let subscript = m.get_subscript(name).expect("imported subscript not found");
            let member = if mut_member {
                &subscript.mut_member
            } else {
                &subscript.ref_member
            };
            member
                .as_ref()
                .expect("imported subscript member must exist")
                .function
        }
    };
    (fi, mi)
}

/// A standard-library intrinsic operating on trusted `Uninit<T>` storage.
///
/// These intrinsics have no script body; the SSA emitter lowers them inline as memory operations
/// (`Uninit<T>` has the same layout as `T`, so the conversions are reinterpretations).
#[derive(Clone, Copy)]
enum UninitIntrinsic {
    /// `uninit() -> Uninit<T>`: produces uninitialized storage.
    Uninit,
    /// `write_init(target: &mut Uninit<T>, value: T)`: moves `value` into `target`.
    WriteInit,
    /// `assume_init(value: Uninit<T>) -> T`: moves the initialized value out of its storage.
    AssumeInit,
    /// `assume_init_mut(target: &mut Uninit<T>) -> &mut T`: reinterprets storage as initialized.
    AssumeInitMut,
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

/// Builds the SSA IR of the function `source` of `module` and returns the lowered function.
///
/// This is the shared entry point used both by the textual SSA dump (`emit_ssa`) and by backends
/// (such as the WASM emitter) that consume the lowered `ssa::Function` directly.
pub fn build_ssa_function(
    source: LocalFunctionId,
    module: &Module,
    others: &Modules,
    session: &CompilerSession,
) -> ssa::Function {
    Emitter::build_ssa_fn(source, module, others, session)
}

impl<'a> Emitter<'a> {
    /// Generates the textual IR of `source`.
    fn emit_ssa_fn(
        source: LocalFunctionId,
        module: &'a Module,
        others: &'a Modules,
        session: &'a CompilerSession,
    ) -> String {
        let lowered = Self::build_ssa_fn(source, module, others, session);
        let env = ModuleEnv::new(module, others);
        format!("{}", lowered.format_with(&env))
    }

    /// Builds and returns the lowered SSA representation of `source`.
    fn build_ssa_fn(
        source: LocalFunctionId,
        module: &'a Module,
        others: &'a Modules,
        session: &'a CompilerSession,
    ) -> ssa::Function {
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

        // Record which incoming dictionary parameter witnesses the `Value` layout of each generic
        // type, so that allocations of generic storage can carry their run-time layout witness.
        let value_trait_id = env.expect_std_trait_id(VALUE_TRAIT_NAME);
        let mut value_witnesses: Vec<(Type, ssa::Value)> = vec![];
        for (j, req) in extra.requirements.iter().enumerate() {
            if let DictionaryReq::TraitImpl {
                trait_id,
                input_tys,
                ..
            } = req
                && *trait_id == value_trait_id
                && let [ty] = input_tys[..]
            {
                value_witnesses.push((ty, ssa::Value::Parameter(j)));
            }
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
            let resolved = f.parameter_passing[i];
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
                value_witnesses,
                loop_results: HashMap::new(),
                return_destination,
                returns_place: f.definition.returns_place(),
            },
            hir_arena: &module.hir_arena,
            session,
        };

        // Allocate frame storage for every `Owned` local and bind it to its `alloca` place.
        emitter.allocate_owned_locals();

        // Lower the body, dispatching on the function's return convention.
        match f.definition.return_convention() {
            // A value-returning function stores its result into the return out-pointer.
            FnReturnConvention::Value => {
                let ret_dest = emitter.context.return_destination.clone();
                emitter.lower_value_into(code, Some(ret_dest));
            }
            // An addressor function returns a caller-rooted place. Its body is `never`-typed and
            // ends in `return <place-expr>` (enforced at `FunctionDefinition::returns_place`
            // validation); the embedded `Return` stores the place pointer into the return
            // out-pointer. Driving with no destination avoids a spurious value store.
            FnReturnConvention::AddressorPlace => {
                emitter.lower_value_into(code, None);
            }
            // A `YieldedOnce` member has no standalone SSA semantics: it is consumed inline at its
            // `WithYielded` site. It must never be emitted as a callable.
            FnReturnConvention::YieldedOnce => panic!(
                "a YieldedOnce subscript member is inline-only and must never be emitted standalone; \
                 it is consumed structurally at its WithYielded site"
            ),
        }

        // Append the trailing `ret`.
        if !emitter.current_block_is_terminated() {
            emitter.insert(Instruction::ret(emitter.context.span));
        }

        emitter.context.function
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

    /// Lowers an indirect `Value::clone(source, target)` call dispatched through the dictionary
    /// extra parameter `dictionary`.
    ///
    /// `source` is the place of the value to clone, and `target` is the (uninitialized) destination
    /// place the clone initializes. `cloned_ty` is the cloned value's type `T`, used to resolve the
    /// dictionary's `clone` slot. The clone method returns `()`, so a throwaway unit return
    /// out-pointer is appended to the call per the ABI.
    fn lower_value_clone_via_dictionary(
        &mut self,
        span: Location,
        dictionary: ExtraParameterId,
        cloned_ty: Type,
        source: ssa::Value,
        target: ssa::Value,
    ) {
        // The dictionary parameter is itself a place (a pointer to the dictionary tuple).
        let dictionary_place = self.context.extra_parameters[&dictionary].clone();
        let (entry_index, method_ty) = self.value_clone_method(cloned_ty);
        let method_place = self
            .insert(Instruction::project(
                span,
                dictionary_place,
                entry_index,
                method_ty,
            ))
            .unwrap();
        let method = self.insert(Instruction::load(span, method_place)).unwrap();
        self.insert(Instruction::call(span, method, [source, target]));
    }

    /// Returns the runtime dictionary entry index and function type of the `Value::clone` method
    /// for `cloning`.
    fn value_clone_method(&self, cloning: Type) -> (usize, Type) {
        let env = ModuleEnv::new(self.module, self.others);
        let value_trait_id = env.expect_std_trait_id(VALUE_TRAIT_NAME);
        let trait_def = env.trait_def(value_trait_id);
        let dict_ty = trait_def.get_dictionary_type_for_tys(&[cloning], &[], &[]);
        let entry_index = trait_def
            .dictionary_method_index(VALUE_CLONE_METHOD_INDEX)
            .as_index();
        let dict_ty_data = dict_ty.data();
        let method_ty = dict_ty_data
            .as_tuple()
            .expect("Value dictionary should be a tuple type")[entry_index];
        (entry_index, method_ty)
    }

    /// Recognizes a call to a trusted `Uninit<T>` standard-library intrinsic, which the emitter
    /// lowers inline as a memory operation rather than as an opaque (bodyless) call.
    fn uninit_intrinsic(&self, function: FunctionId) -> Option<UninitIntrinsic> {
        let (fi, mi) = match function {
            FunctionId::Local(i) => (i, self.module.module_id()),
            FunctionId::Import(i) => imported_function(i, self.module, self.session),
        };
        if mi != STD_MODULE_ID {
            return None;
        }
        let module = self.session.expect_fresh_module(mi);
        let name = module.get_function_name_by_id(fi)?;
        match name.as_str() {
            "uninit" => Some(UninitIntrinsic::Uninit),
            "write_init" => Some(UninitIntrinsic::WriteInit),
            "assume_init" => Some(UninitIntrinsic::AssumeInit),
            "assume_init_mut" => Some(UninitIntrinsic::AssumeInitMut),
            _ => None,
        }
    }

    /// Lowers a trusted `Uninit<T>` intrinsic call in destination-passing (value) position.
    fn lower_uninit_intrinsic_into(
        &mut self,
        node: &ENode,
        n: &hir::StaticApplication<Elaborated>,
        intrinsic: UninitIntrinsic,
        destination: Option<ssa::Value>,
    ) {
        match intrinsic {
            // `uninit()` yields uninitialized storage: leave `destination` uninitialized.
            UninitIntrinsic::Uninit => {}
            // `write_init(target, value)` moves `value` into `target`'s storage. It is `()`-typed,
            // so nothing is stored into `destination`.
            UninitIntrinsic::WriteInit => {
                let target = self.lower_as_place(&self.hir_arena[n.arguments[0].value]);
                self.lower_value_into(&self.hir_arena[n.arguments[1].value], Some(target));
            }
            // `assume_init(value)` reinterprets the storage as initialized and moves the value out;
            // the value lives in the argument's place, so copy it into `destination`.
            UninitIntrinsic::AssumeInit => {
                if destination.is_some() {
                    self.assert_statically_sized(node.ty);
                    let place = self.lower_as_place(&self.hir_arena[n.arguments[0].value]);
                    let v = self.insert(Instruction::load(node.span, place)).unwrap();
                    self.store_into_if_needed(node.span, v, destination);
                }
            }
            // `assume_init_mut` is place-returning; lower it through the place path.
            UninitIntrinsic::AssumeInitMut => self.lower_place_call_into(node, destination),
        }
    }

    /// Allocates frame storage for every [`LocalStorage::Owned`] local of the lowered function and
    /// binds it to its `alloca` place.
    ///
    /// Arguments are `NonOwning` and keep their by-value parameter binding. Non-owning, non-argument
    /// locals (aliases) are bound to their initializer's place when their `StoreLocal` is lowered.
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
            let place = self.alloca_storage(self.context.span, ty);
            self.context.locals.insert(id, place);
        }
    }

    /// Returns the `Value` dictionary parameter (a place) witnessing the run-time layout of `ty`, if any.
    fn value_dictionary(&self, ty: Type) -> Option<ssa::Value> {
        self.context
            .value_witnesses
            .iter()
            .find(|(t, _)| *t == ty)
            .map(|(_, w)| w.clone())
    }

    /// Inserts an allocation of storage for an instance of `ty` and returns its address.
    ///
    /// Statically sized storage is allocated directly; storage of a generic type carries the
    /// `Value` dictionary witnessing its run-time layout as operand.
    fn alloca_storage(&mut self, span: Location, ty: Type) -> ssa::Value {
        if ty.is_constant() || is_function_surface_only_value_type(ty) {
            // Note: is_function_surface_only_value_type indicates it's a function, which always
            // has the same, known layout. No dictionary is required.
            self.insert(Instruction::alloca(span, ty)).unwrap()
        } else {
            let witness = self.value_dictionary(ty).unwrap_or_else(|| {
                panic!(
                    "no Value dictionary witnesses the layout of generic storage of type {}",
                    self.show(ty)
                )
            });
            self.insert(Instruction::alloca_dynamic(span, ty, witness))
                .unwrap()
        }
    }

    /// Asserts that `ty` has a statically known layout, so that a value of that type may be moved
    /// with direct `load`/`store` instructions.
    ///
    /// Generic values have no static layout: they must be allocated with `alloca_dynamic` and
    /// moved through their `Value` dictionary witness (`Value::clone`/`Value::drop`), never with
    /// direct `load`/`store`.
    fn assert_statically_sized(&self, ty: Type) {
        assert!(
            ty.is_constant() || is_function_surface_only_value_type(ty),
            "attempted direct load/store of a generic value of type {}; generic values must be moved through their Value dictionary witness",
            self.show(ty)
        );
    }

    /// Returns the declaration for `l` within the currently-lowered function.
    fn local_declaration(&self, l: LocalDeclId) -> &module::ELocalDecl {
        &self
            .module
            .get_function_by_id(self.context.source)
            .unwrap()
            .locals[l.as_index()]
    }

    /// Returns the place (a pointer SSA value) backing the local `l`.
    ///
    /// Every local is bound to a place: an incoming by-pointer parameter or an `Owned` `alloca`
    /// or a non-owned alias.
    fn place_of_local(&self, l: LocalDeclId) -> ssa::Value {
        self.context
            .locals
            .get(&l)
            .expect("local must be bound in the current frame")
            .clone()
    }

    /// Lowers `node` as a place.
    ///
    /// If possible, lowers directly as a place, otherwise lowers a value into stack storage,
    /// returning its address.
    fn lower_as_place(&mut self, node: &ENode) -> ssa::Value {
        // let ty = node.ty;
        // let place = self
        //     .insert(Instruction::alloca_place(self.context.span, ty))
        //     .unwrap();
        // self.lower_as_place_into(node, &place);

        // self.insert(Instruction::load(node.span, place)).unwrap()

        use hir::NodeKind as K;
        match &node.kind {
            K::LoadLocal(n) => self.place_of_local(n.id),

            K::LoadDictionary(n) => {
                // A dictionary parameter is already a place.
                self.context.extra_parameters[&n.extra_parameter].clone()
            }

            K::Project(n) => {
                let dictionary = &self.hir_arena[n.value];
                let base = self.lower_as_place(dictionary);

                self.insert(Instruction::project(
                    node.span,
                    base,
                    n.index.as_index(),
                    node.ty,
                ))
                .unwrap()
            }

            K::Apply(n) => {
                let result_storage = self.allocate_result(node, &n.ty);
                let f = self.lower_as_register(&self.hir_arena[n.function]);
                let mut arguments: Vec<ssa::Value> = n
                    .arguments
                    .iter()
                    .map(|arg| self.lower_argument(arg))
                    .collect();
                arguments.push(result_storage.clone());

                self.insert(Instruction::call(node.span, f, arguments));

                if n.ty.returns_place() {
                    self.insert(Instruction::load(node.span, result_storage))
                        .unwrap()
                } else {
                    result_storage
                }
            }

            K::StaticApply(n) => {
                if let Some(intrinsic) = self.uninit_intrinsic(n.function) {
                    return match intrinsic {
                        // `assume_init`/`assume_init_mut` reinterpret the argument's storage as
                        // initialized: the result place is the argument's place (an identity).
                        UninitIntrinsic::AssumeInit | UninitIntrinsic::AssumeInitMut => {
                            self.lower_as_place(&self.hir_arena[n.arguments[0].value])
                        }
                        // `uninit`/`write_init` produce a value: materialize it into a temporary.
                        UninitIntrinsic::Uninit | UninitIntrinsic::WriteInit => {
                            let storage = self.alloca_storage(node.span, node.ty);
                            self.lower_uninit_intrinsic_into(
                                node,
                                n,
                                intrinsic,
                                Some(storage.clone()),
                            );
                            storage
                        }
                    };
                }
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
                    arguments.push(self.lower_as_place(&self.hir_arena[arg.value]));
                }

                let result_storage = self.allocate_result(node, &n.ty);
                arguments.push(result_storage.clone());

                self.insert(Instruction::call(node.span, f, arguments));

                if n.ty.returns_place() {
                    self.insert(Instruction::load(node.span, result_storage))
                        .unwrap()
                } else {
                    result_storage
                }
            }

            K::CallDictionaryMethod(n) => {
                // A place-returning method dispatched through a dictionary: project+load the
                // method, call it with a place out-pointer, then load the returned place.
                let (method, mut arguments) = self.lower_dictionary_method_target(node, n);
                let result_storage = self.allocate_result(node, &n.ty);
                arguments.push(result_storage.clone());
                self.insert(Instruction::call(node.span, method, arguments));
                if n.ty.returns_place() {
                    self.insert(Instruction::load(node.span, result_storage))
                        .unwrap()
                } else {
                    result_storage
                }
            }

            K::WithPlace(n) => {
                // An addressor subscript site: bind the accessor's place, then the body (a
                // `LoadLocal` of the binding, possibly projected) is itself a place.
                self.bind_local_for_with_place(n);
                self.lower_as_place(&self.hir_arena[n.body])
            }

            K::WithYielded(_) => {
                panic!("WithYielded should be just lowered as an inlining.")
            }

            // A value-producing node is materialized into a temporary place.
            _ => {
                let storage = self.alloca_storage(node.span, node.ty);
                self.lower_value_into(node, Some(storage.clone()));
                storage
            }
        }
    }

    /// Lowers the addressor `place` of a [`hir::WithPlace`] and binds its non-owning `binding`
    /// local to that place, so the driver `body` can read it through `LoadLocal(binding)`.
    ///
    /// Mirrors the interpreter's `eval_with_place`: the binding aliases existing caller-rooted
    /// storage, so no store is emitted (the same shape as a non-owning `StoreLocal` alias).
    fn bind_local_for_with_place(&mut self, n: &hir::WithPlace<Elaborated>) {
        let place = self.lower_as_place(&self.hir_arena[n.place]);
        self.context.locals.insert(n.binding, place);
    }

    /// Lowers `node` as a register value (a loaded scalar / value held directly in an SSA register).
    ///
    /// A primitive immediate is produced directly; any other node is lowered as a place, and the
    /// value is `load`ed from it.
    fn lower_as_register(&mut self, node: &ENode) -> ssa::Value {
        use hir::NodeKind as K;
        if let K::Immediate(n) = &node.kind
            && let Some(prim) = self.lower_as_primitive(n)
        {
            return prim;
        }
        self.assert_statically_sized(node.ty);
        let place = self.lower_as_place(node);
        self.insert(Instruction::load(node.span, place)).unwrap()
    }

    /// Lowers `arg` to its call operand: a pointer to the argument's storage.
    ///
    /// Note: All arguments are passed indirectly in SSA IR.
    fn lower_argument(&mut self, arg: &CallArgument<Elaborated>) -> ssa::Value {
        self.lower_as_place(&self.hir_arena[arg.value])
    }

    /// Returns the blocks created for `n`.
    fn create_case_blocks(&mut self, n: &Case<Elaborated>) -> CaseBlocks {
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
    fn lower_dictionary(&mut self, n: &GetDictionary) -> ssa::Value {
        let (d, m) = self.dictionary_value(n);
        let mut entries: Vec<ssa::Value> = d
            .methods()
            .iter()
            .map(|x| self.demand_function(*x, m))
            .collect();
        for value in d.associated_const_values() {
            let value = self
                .lower_as_primitive(value)
                .expect("dictionary associated const must be a primitive value");
            entries.push(value);
        }
        ssa::Value::Dictionary(entries)
    }

    /// Stores the register `value` into `dest` if a destination is present; a `None` `dest`
    /// discards the value.
    fn store_into_if_needed(
        &mut self,
        span: Location,
        value: ssa::Value,
        destination: Option<ssa::Value>,
    ) {
        if let Some(d) = destination {
            self.insert(Instruction::store(span, value, d));
        }
    }

    /// Inserts a `store` instruction to store `v` at `destination`.
    fn store(&mut self, span: Location, v: ssa::Value, destination: ssa::Value) {
        self.insert(Instruction::store(span, v, destination));
    }

    /// Projects the method function reference out of `n`'s dictionary place, loads it, and lowers
    /// the call's runtime arguments to their place operands. Returns `(method, arguments)` ready
    /// to be completed with a result out-pointer and emitted as a `call`.
    fn lower_dictionary_method_target(
        &mut self,
        node: &ENode,
        n: &hir::CallDictionaryMethod<Elaborated>,
    ) -> (ssa::Value, Vec<ssa::Value>) {
        let dictionary = self.lower_as_place(&self.hir_arena[n.dictionary]);
        let method_ty = Type::function_type(n.ty.clone());
        let method_place = self
            .insert(Instruction::project(
                node.span,
                dictionary,
                n.entry_index.as_index(),
                method_ty,
            ))
            .unwrap();
        let method = self
            .insert(Instruction::load(node.span, method_place))
            .unwrap();
        let arguments = n.arguments.iter().map(|a| self.lower_argument(a)).collect();
        (method, arguments)
    }

    /// Inserts an allocation of `f`'s result storage and returns its address.
    ///
    /// For void return types, no static allocation is inserted; we use the special value UnitPlace.
    fn allocate_result(&mut self, node: &ENode, f: &FnType) -> ssa::Value {
        if f.ret == Type::unit() {
            ssa::value::Value::UnitPlace
        } else {
            match f.return_convention {
                FnReturnConvention::Value => self.alloca_storage(node.span, node.ty),
                FnReturnConvention::AddressorPlace => self
                    .insert(Instruction::alloca_place(node.span, node.ty))
                    .unwrap(),
                FnReturnConvention::YieldedOnce => todo!("YieldedOnce return convention"),
            }
        }
    }

    /// Lowers a place-returning call in value position: the call's place result is resolved and
    /// its value is copied into the destination (trivial copy; non-trivial reads are wrapped in
    /// `CloneValue` by HIR). A `None` destination lowers the call for its effects only.
    fn lower_place_call_into(&mut self, node: &ENode, destination: Option<ssa::Value>) {
        let place = self.lower_as_place(node);
        if let Some(dest) = destination {
            self.assert_statically_sized(node.ty);
            let v = self.insert(Instruction::load(node.span, place)).unwrap();
            self.store(node.span, v, dest);
        }
    }

    /// Lowers `node` in destination-passing style: the value produced by `node` is stored into the
    /// storage pointed to by `dest`. A `None` `dest` denotes a discarded result (effects only); a
    /// `()`-typed node also has nothing to store.
    fn lower_value_into(&mut self, node: &ENode, destination: Option<ssa::Value>) {
        use hir::NodeKind as K;
        match &node.kind {
            K::Block(n) => {
                // Lower each statement for its effects; the block's value is its tail node, which is
                // lowered into the destination.
                if let Some((tail, init)) = n.body.split_last() {
                    for s in init {
                        self.lower_value_into(&self.hir_arena[*s], None);
                    }
                    self.lower_value_into(&self.hir_arena[*tail], destination);
                }
                // todo emit cleanup
            }

            K::Case(n) => {
                // TODO make this work for non-primitive types, using the Value dictionary's `eq` or a statically resolved conformance.

                let blocks = self.create_case_blocks(n);

                // We lower the scrutinee before the case blocks so that its value can be used in all conditions.
                let scrutinee = self.lower_as_register(&self.hir_arena[n.value]);

                self.insert(Instruction::br(node.span, blocks.heads[0]));

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
                        .insert(Instruction::compare_eq(
                            node.span,
                            scrutinee.clone(),
                            alternative_pattern,
                        ))
                        .unwrap();
                    self.insert(Instruction::condbr(node.span, v, blocks.bodies[i], next));

                    // Lower the body of the alternative into the destination.
                    self.context.point = InsertionPoint::End(blocks.bodies[i]);
                    self.lower_value_into(&self.hir_arena[*a], destination.clone());
                    self.insert(Instruction::br(node.span, blocks.tail));
                }

                // Default case.
                self.context.point = InsertionPoint::End(blocks.default);
                self.lower_value_into(&self.hir_arena[n.default], destination.clone());
                self.insert(Instruction::br(node.span, blocks.tail));

                // Tail. The value has already been stored into `dest`.
                self.context.point = InsertionPoint::End(blocks.tail);
            }

            K::Immediate(n) => {
                if n.as_primitive_ty::<()>().is_some() {
                    // Storing void would be redundant.
                } else if let Some(value) = self.lower_as_primitive(n) {
                    self.store_into_if_needed(node.span, value, destination);
                } else {
                    let s = self.show(node.ty);
                    panic!(
                        "lowering is unimplemented for node of kind '{:?}' of type {:?}",
                        node.kind, s
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
                self.lower_value_into(&self.hir_arena[n.value], Some(place));
                // `Assign` is `()`-typed: nothing to store into `dest`.
            }

            K::LoadLocal(n) => {
                // A bare load in value position is a trivial-copy read (non-trivial reads are wrapped
                // in `CloneValue`/`TakeLocalValue` by HIR): load the local's place and store it.
                if destination.is_some() {
                    self.assert_statically_sized(node.ty);
                    let p = self.place_of_local(n.id);
                    let v = self.insert(Instruction::load(node.span, p)).unwrap();
                    self.store_into_if_needed(node.span, v, destination);
                }
            }

            K::StoreLocal(n) => {
                // Initialize the local's storage. A non-owning local is an alias: bind it to the
                // place of its initializer (no store). Otherwise the local's `clone` dispatch
                // decides how the value is produced: `None`/`TrivialCopy` stores the produced
                // value directly; `Static`/`Dictionary` perform `Value::clone` into the target
                // (deferred).
                if !self.local_declaration(n.id).owns_storage() {
                    let aliasee = self.lower_as_place(&self.hir_arena[n.value]);
                    self.context.locals.insert(n.id, aliasee);
                    return;
                }
                let clone = self.local_declaration(n.id).clone;
                match clone {
                    None | Some(ResolvedLocalClone::TrivialCopy) => {
                        let place = self.place_of_local(n.id);
                        self.lower_value_into(&self.hir_arena[n.value], Some(place));
                    }
                    Some(ResolvedLocalClone::Static(f)) => {
                        // Clone the source place into the local's (uninitialized) owned storage
                        // through the statically known clone function `f`.
                        let (fi, mi) = match f {
                            FunctionId::Local(i) => (i, self.module.module_id()),
                            FunctionId::Import(i) => {
                                imported_function(i, self.module, self.session)
                            }
                        };
                        let f = self.demand_function(fi, mi);

                        let target = self.place_of_local(n.id);
                        let source = self.lower_as_place(&self.hir_arena[n.value]);

                        self.insert(Instruction::call(node.span, f, [source, target]));
                    }
                    Some(ResolvedLocalClone::Dictionary(dictionary)) => {
                        // Clone the source place into the local's (uninitialized) owned storage
                        // through the `Value::clone` method loaded from the dictionary parameter.
                        let cloned_ty = self.local_declaration(n.id).ty;
                        let target = self.place_of_local(n.id);
                        let source = self.lower_as_place(&self.hir_arena[n.value]);
                        self.lower_value_clone_via_dictionary(
                            node.span, dictionary, cloned_ty, source, target,
                        );
                    }
                }
                // `StoreLocal` is `()`-typed: nothing to store into `dest`.
            }

            K::CloneValue(n) => {
                match n.clone {
                    // A trivial copy: load the source place and store it into the destination. A later
                    // ABI pass may relax this to direct passing where physically possible.
                    ResolvedLocalClone::TrivialCopy => {
                        self.lower_value_into(&self.hir_arena[n.source], destination);
                    }
                    ResolvedLocalClone::Static(f) => {
                        // Clone the source place into the local's (uninitialized) owned storage
                        // through the statically known clone function `f`.
                        let (fi, mi) = match f {
                            FunctionId::Local(i) => (i, self.module.module_id()),
                            FunctionId::Import(i) => {
                                imported_function(i, self.module, self.session)
                            }
                        };
                        let f = self.demand_function(fi, mi);

                        let source = self.lower_as_place(&self.hir_arena[n.source]);

                        self.insert(Instruction::call(
                            node.span,
                            f,
                            [source, destination.unwrap()],
                        ));
                    }
                    ResolvedLocalClone::Dictionary(dictionary) => {
                        // Materialize an owned snapshot by cloning the source place into a fresh
                        // target through the `Value::clone` method loaded from the dictionary
                        // parameter. A `None` destination still needs target storage to clone into.
                        let target =
                            destination.unwrap_or_else(|| self.alloca_storage(node.span, node.ty));
                        let source = self.lower_as_place(&self.hir_arena[n.source]);
                        self.lower_value_clone_via_dictionary(
                            node.span, dictionary, node.ty, source, target,
                        );
                    }
                }
            }

            K::TakeLocalValue(n) => match n.mode {
                ResolvedTakeLocalValueMode::MoveOwned => {
                    // Move the owned value out: load the place and store it into the destination,
                    // skipping the local's lexical drop (cleanup is deferred).
                    if destination.is_some() {
                        self.assert_statically_sized(node.ty);
                        let p = self.place_of_local(n.id);
                        let v = self.insert(Instruction::load(node.span, p)).unwrap();
                        self.store_into_if_needed(node.span, v, destination);
                    }
                }
                ResolvedTakeLocalValueMode::CloneBorrowed(_) => {
                    todo!("TakeLocalValue CloneBorrowed is not lowered yet")
                }
            },

            K::StaticApply(n) => {
                if let Some(intrinsic) = self.uninit_intrinsic(n.function) {
                    return self.lower_uninit_intrinsic_into(node, n, intrinsic, destination);
                }
                if n.ty.returns_place() {
                    return self.lower_place_call_into(node, destination);
                }
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
                arguments.push(destination.unwrap_or_else(|| self.allocate_result(node, &n.ty)));
                self.insert(Instruction::call(node.span, f, arguments));
            }

            K::GetDictionary(d) => {
                let dict = self.lower_dictionary(d);
                self.store_into_if_needed(node.span, dict, destination);
            }

            K::Apply(n) => {
                if n.ty.returns_place() {
                    return self.lower_place_call_into(node, destination);
                }
                let f = self.lower_as_register(&self.hir_arena[n.function]);
                let mut arguments: Vec<ssa::Value> = n
                    .arguments
                    .iter()
                    .map(|arg| self.lower_argument(arg))
                    .collect();
                arguments.push(destination.unwrap_or_else(|| self.allocate_result(node, &n.ty)));
                self.insert(Instruction::call(node.span, f, arguments));
            }

            K::Project(_) => {
                // A projection is a place: load the field place and store it into the destination
                // (trivial copy; non-trivial reads are wrapped in `CloneValue` by HIR).
                if destination.is_some() {
                    self.assert_statically_sized(node.ty);
                    let fp = self.lower_as_place(node);
                    let v = self.insert(Instruction::load(node.span, fp)).unwrap();
                    self.store_into_if_needed(node.span, v, destination);
                }
            }

            K::Loop(n) => {
                // The loop's result is written into `dest` (or a throwaway temporary when discarded).
                let result = match &destination {
                    Some(dest) => dest.clone(),
                    None => self.alloca_storage(node.span, node.ty),
                };
                self.context.loop_results.insert(n.label, result);

                self.lower_value_into(&self.hir_arena[n.body], None);

                // TODO: no loop head/back-edge/exit block is emitted and Break/Continue are unhandled
                // (they fall through to todo!), so Loop is effectively non-functional.
            }

            K::ExtractTag(_n) => {
                // TODO: N should be a variant, which will be lowered to either a `ssa::Value::Tuple` or to a new `ssa::Value::Variant`
                // So we should either extract the tag with a fixed index for the tuple, or accessing a custom property of the variant.
                todo!("Lowering for ExtractTag is unimplemented");
            }

            K::Variant(_) => {
                // TODO: Implemented this either by lowering it to a `ssa::Value::Tuple`, or a `ssa::Value::Variant`
                todo!("Lowering for Variant is unimplemented");
            }

            K::LoadDictionary(n) => {
                // A required dictionary/evidence resolves to its incoming extra parameter, which is a
                // place. Copy it into the destination if one is requested.
                if destination.is_some() {
                    let p = self.context.extra_parameters[&n.extra_parameter].clone();
                    let v = self.insert(Instruction::load(node.span, p)).unwrap();
                    self.store_into_if_needed(node.span, v, destination);
                }
            }

            K::CallDictionaryMethod(n) => {
                // A place-returning method is resolved as a place and copied into the destination,
                // like any other place-returning call.
                if n.ty.returns_place() {
                    return self.lower_place_call_into(node, destination);
                }
                // Project the method out of the dictionary, load it, then call it into the
                // destination (or a throwaway result for a discarded call).
                let (method, mut arguments) = self.lower_dictionary_method_target(node, n);
                arguments.push(destination.unwrap_or_else(|| self.allocate_result(node, &n.ty)));
                self.insert(Instruction::call(node.span, method, arguments));
            }

            // Runtime guards have no SSA representation yet; they lower to nothing.
            K::CheckCallDepth | K::CheckFuel => {}

            K::Tuple(ns) => {
                let d = destination.expect("ignored tuple construction not yet implemented");
                let mut values = vec![];

                for (i, n) in ns.iter().enumerate() {
                    let node = &self.hir_arena[*n];
                    let f = self
                        .insert(Instruction::project(
                            node.span,
                            d.clone(),
                            i,
                            node.ty.clone(),
                        ))
                        .unwrap();

                    values.push(self.lower_value_into(&node, Some(f)));
                }
            }

            K::Record(ns) => {
                let d = destination.expect("ignored record construction not yet implemented");
                let mut values = vec![];

                for (i, n) in ns.iter().enumerate() {
                    let node = &self.hir_arena[*n];
                    let f = self
                        .insert(Instruction::project(
                            node.span,
                            d.clone(),
                            i,
                            node.ty.clone(),
                        ))
                        .unwrap();

                    values.push(self.lower_value_into(&node, Some(f)));
                }
            }

            K::Uninit => self.store(
                node.span,
                ssa::Value::Uninit(ShownType {
                    ty: node.ty.clone(),
                    name: self.show(node.ty),
                }),
                destination.expect("discarded uninit construction is not yet implemented"),
            ),

            K::WithPlace(n) => {
                // An addressor subscript site: bind the accessor's place, then lower the body
                // (which reads the binding) into the destination.
                self.bind_local_for_with_place(n);
                self.lower_value_into(&self.hir_arena[n.body], destination);
            }

            K::WithYielded(_) => {
                panic!("WithYielded should be just lowered as an inlining.")
            }

            K::Return(n) => {
                // `return <expr>` writes into the function's return out-pointer and terminates,
                // ignoring the ambient `destination`. Mirrors the interpreter's `eval_return`:
                // a place-returning function returns the `*T` place pointer; otherwise the value.
                let operand = &self.hir_arena[*n];
                let dest = self.context.return_destination.clone();
                if self.context.returns_place {
                    let place = self.lower_as_place(operand);
                    self.store(node.span, place, dest);
                } else {
                    self.lower_value_into(operand, Some(dest));
                }
                self.insert(Instruction::ret(node.span));
            }

            K::Yield(_) => {
                // `Yield` is consumed structurally by its `WithYielded` driver (Stage 4) and must
                // never be reached through generic lowering.
                panic!("Yield reached outside its WithYielded accessor");
            }

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
        } else if let Some(x) = native.as_primitive_ty::<Float>() {
            // A `Float` is always finite and never NaN, so it converts to a `NotNan` infallibly.
            Some(ssa::Value::Float(
                NotNan::new(x.into_inner()).expect("a Float is never NaN"),
            ))
        } else if let Some(s) = native.as_primitive_ty::<crate::std::string::String>() {
            Some(ssa::Value::String(s.clone()))
        } else {
            native
                .as_primitive_ty::<bool>()
                .map(|n| ssa::Value::Boolean(*n))
        }
    }

    /// Inserts `s` at the current insertion point, and returns its result register, if any.
    fn insert(&mut self, s: Instruction) -> Option<ssa::Value> {
        let i = match &self.context.point {
            InsertionPoint::End(b) => self.context.function.block_mut(*b).append(s),
        };
        self.context.function.definition(i)
    }

    /// Returns whether the current insertion block already ends in a terminator (e.g. a `ret`
    /// emitted by an explicit `return`), so callers can avoid inserting after a terminator.
    fn current_block_is_terminated(&self) -> bool {
        match &self.context.point {
            InsertionPoint::End(b) => self.context.function.block(*b).is_terminated(),
        }
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

    /// The `Value` dictionary parameters witnessing the run-time layout of generic types, used to
    /// allocate storage whose size is known only at run time.
    value_witnesses: Vec<(Type, ssa::Value)>,

    /// The SSA place (an `alloca` result or the return out-pointer) into which each active loop
    /// writes its result via `break`, keyed by the loop's `LoopId`.
    loop_results: HashMap<LoopId, ssa::Value>,

    /// The return out-pointer (the last parameter) into which the function writes its result.
    return_destination: ssa::Value,

    /// Whether the lowered function itself returns a place (`FnReturnConvention::AddressorPlace`).
    /// When set, `return <expr>` lowers `<expr>` as a place and stores that pointer into the
    /// `**T` return out-pointer (mirrors the interpreter's `EvalCtx::returns_place`).
    returns_place: bool,
}

/// Where an instruction should be inserted in a basic block.
enum InsertionPoint {
    /// The end of a basic block.
    End(BlockIdentity),
}
