// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
//! Specializing a generic MIR body at one call site's instantiation.
//!
//! A generic function is compiled once, its type parameters left as quantified variables and its
//! trait constraints turned into hidden dictionary parameters. Specializing it has two halves —
//! substituting the types and binding the dictionaries — and **they must be applied together**. A
//! body with only its dictionaries bound says `int` in its evidence and `A` in its types; that is
//! latent while nothing acts on it, but the moment folding uses the now-resolved `dict_entry` it
//! evaluates a call at the concrete instantiation and has nowhere type-correct to put the result.
//!
//! This module currently implements the first half. Nothing consumes its output yet: a body that
//! has had one half applied and not the other may exist behind tests, never in the round loop.
//!
//! Substitution composes down the call graph without anything reasoning about nesting, because a
//! call's recorded instantiation is written in the *containing* function's type environment.
//! Substituting `forwarding<U>` at `U := int` rewrites its inner call's recorded `[U]` into
//! `[int]`, so a call that was generic becomes concrete. See `doc/generic-instantiation.md`.
//!
//! Exercised only by its own tests until the specialization pass consumes it; remove the allow
//! below then, as `const_eval.rs` did when folding started calling it.
#![allow(dead_code)]

use crate::{
    mir::{
        Function, Instantiation, Operation, OperationKind, edit::FunctionEdit,
        terminator::TerminatorKind,
    },
    module::ModuleEnv,
    types::{
        type_like::TypeLike, type_mapper::BitmapInstantiationMapper, type_mapper::TypeMapper,
        type_scheme::TypeScheme,
    },
};

/// Rewrites every type `func` carries by `instantiation`, which is positional against `scheme`'s
/// quantifiers — the declared scheme of the very function being substituted.
///
/// The result is verified by [`FunctionEdit::finish`], which is what makes this half independently
/// checkable: the verifier already requires that instantiating a callee's declared signature by a
/// call's recorded arguments reproduces that call's own type, so a type this misses shows up as a
/// mismatch at the first call site that names it.
pub(crate) fn substitute_types<Ty: TypeLike>(
    func: &Function,
    scheme: &TypeScheme<Ty>,
    instantiation: &Instantiation,
    env: ModuleEnv<'_>,
) -> Function {
    let subst = instantiation.substitution(scheme);
    // Bitmap rather than simple: one mapper is reused across every type in the body, which is what
    // makes its `affects_type` constant-time construction cost pay for itself.
    map_types(func, &mut BitmapInstantiationMapper::new(&subst), env)
}

/// Rewrites every type `func` carries through `mapper`.
///
/// Separate from [`substitute_types`] so that a caller can supply a mapper of its own: the tests
/// enumerate a body's per-operation types by running this same traversal with a recording mapper.
/// They deliberately do *not* do that for the signature and the constant pool, which they read
/// directly — a check sharing the traversal it checks cannot see what the traversal skips.
fn map_types(func: &Function, mapper: &mut impl TypeMapper, env: ModuleEnv<'_>) -> Function {
    let mut edit = FunctionEdit::new(func.clone());

    for parameter in edit.parameters_mut() {
        parameter.ty = parameter.ty.map(mapper);
    }
    for constant in edit.constants_mut() {
        constant.ty = constant.ty.map(mapper);
    }
    for block in edit.blocks().collect::<Vec<_>>() {
        let block = edit.block_mut(block);
        for operation in &mut block.operations {
            substitute_in_operation(operation, mapper);
        }
        if let TerminatorKind::Invoke { operation, .. } = &mut block.terminator.kind {
            substitute_in_operation(operation, mapper);
        }
    }

    edit.finish(env)
}

/// Rewrites the types one operation carries.
///
/// Exhaustive by construction: the `match` names every kind, so an operation that gains a type
/// field fails to compile here rather than silently keeping the generic one.
fn substitute_in_operation(operation: &mut Operation, mapper: &mut impl TypeMapper) {
    match &mut operation.kind {
        OperationKind::Alloca { ty }
        | OperationKind::Subfield { ty }
        | OperationKind::DictEntry { ty, .. }
        | OperationKind::SubscriptMember { ty, .. }
        | OperationKind::BuildSubscript { ty }
        | OperationKind::Variant { ty, .. }
        | OperationKind::BuildClosure { ty, .. }
        | OperationKind::CloneClosureEnv { ty } => *ty = ty.map(mapper),
        OperationKind::AllocaPlace { pointing_to } => *pointing_to = pointing_to.map(mapper),
        OperationKind::Call { ty, instantiation } => {
            **ty = ty.map(mapper);
            // The instantiation this body's own calls record. Easy to miss because it is not a
            // type field, and the one that makes specialization cascade: an inner call recording
            // the container's quantifiers becomes concrete exactly when the container does.
            if let Some(instantiation) = instantiation {
                substitute_in_instantiation(instantiation, mapper);
            }
        }
        OperationKind::Project { yielded, ty } => {
            *yielded = yielded.map(mapper);
            **ty = ty.map(mapper);
        }
        OperationKind::EndProject
        | OperationKind::CompareEqual
        | OperationKind::Load
        | OperationKind::ExtractTag
        | OperationKind::Store
        | OperationKind::Clear
        | OperationKind::Memcpy
        | OperationKind::Move
        | OperationKind::StackSave
        | OperationKind::StackRestore
        | OperationKind::CheckCallDepth
        | OperationKind::CheckFuel
        | OperationKind::Drop
        | OperationKind::DropClosureEnv => {}
    }
}

/// Rewrites a recorded instantiation, which is a list of types and effects like any other.
fn substitute_in_instantiation(instantiation: &mut Instantiation, mapper: &mut impl TypeMapper) {
    for ty in &mut instantiation.ty_args {
        *ty = ty.map(mapper);
    }
    for eff in &mut instantiation.eff_args {
        *eff = mapper.map_effect_type(eff);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        CompilerSession, ExecutionTarget, MirOptimization,
        mir::{Value, terminator::TerminatorKind},
        module::{ModuleId, Path},
        types::{
            effects::EffType,
            mutability::MutType,
            r#type::{Type, TypeVar},
        },
    };
    use ustr::ustr;

    /// A generic callee, its declared scheme, and how one concrete call site instantiated it —
    /// everything substitution consumes, harvested from real lowering rather than hand-built.
    struct Site {
        callee: Function,
        scheme: crate::types::type_scheme::TypeScheme<crate::types::r#type::FnType>,
        instantiation: Instantiation,
    }

    fn compile(session: &mut CompilerSession, src: &str) -> ModuleId {
        session
            .compile_for(ExecutionTarget::Mir, src, "test", Path::single_str("test"))
            .expect("test source must compile")
            .module_id
    }

    fn body<'a>(session: &'a CompilerSession, module: ModuleId, name: &str) -> &'a Function {
        let id = session
            .expect_fresh_module(module)
            .get_local_function_id(ustr(name))
            .unwrap_or_else(|| panic!("no function named {name}"));
        session
            .mir_artifacts_for(module, MirOptimization::Disabled)
            .expect("MIR must be prepared")
            .get(id)
            .expect("function must have a MIR body")
    }

    /// Finds the call to `callee_name` inside `caller_name` and collects what it instantiated.
    fn site(
        session: &CompilerSession,
        module: ModuleId,
        caller_name: &str,
        callee_name: &str,
    ) -> Site {
        let caller = body(session, module, caller_name);
        let wanted = session
            .expect_fresh_module(module)
            .get_local_function_id(ustr(callee_name))
            .unwrap_or_else(|| panic!("no function named {callee_name}"));
        for block_id in caller.blocks() {
            let block = caller.block(block_id);
            let operations = block
                .operations()
                .iter()
                .chain(match &block.terminator().kind {
                    TerminatorKind::Invoke { operation, .. } => Some(operation),
                    _ => None,
                });
            for operation in operations {
                let OperationKind::Call { instantiation, .. } = &operation.kind else {
                    continue;
                };
                let Value::Function(callee) = &operation.operands[0] else {
                    continue;
                };
                if callee.module != module || callee.function != wanted {
                    continue;
                }
                let instantiation = instantiation
                    .as_ref()
                    .unwrap_or_else(|| {
                        panic!("the call to {callee_name} must record its instantiation")
                    })
                    .as_ref()
                    .clone();
                let scheme = session
                    .expect_fresh_module(module)
                    .get_function_by_id(wanted)
                    .expect("the callee is a function of this module")
                    .definition
                    .ty_scheme
                    .clone();
                return Site {
                    callee: body(session, module, callee_name).clone(),
                    scheme,
                    instantiation,
                };
            }
        }
        panic!("{caller_name} contains no call to {callee_name}");
    }

    /// Records every type and effect the traversal visits, returning each unchanged.
    #[derive(Default)]
    struct Collector {
        types: Vec<Type>,
        effects: Vec<EffType>,
    }

    impl TypeMapper for Collector {
        fn map_type(&mut self, ty: Type) -> Type {
            self.types.push(ty);
            ty
        }
        fn map_mut_type(&mut self, mut_ty: MutType) -> MutType {
            mut_ty
        }
        fn map_effect_type(&mut self, eff_ty: &EffType) -> EffType {
            self.effects.push(eff_ty.clone());
            eff_ty.clone()
        }
    }

    /// The type variables still free anywhere in `func`.
    ///
    /// The signature and the constant pool are read from the function's own API, *not* through the
    /// traversal: sharing the traversal with what it checks is circular, and a version that skipped
    /// parameter types passed this test until they were read directly. What stays traversal-shared
    /// is the per-operation metadata, where the exhaustive `match` in
    /// [`substitute_in_operation`] gives coverage at compile time instead.
    fn free_ty_vars(func: &Function, env: ModuleEnv<'_>) -> Vec<TypeVar> {
        let mut collector = Collector::default();
        map_types(func, &mut collector, env);
        func.parameters()
            .iter()
            .map(|parameter| parameter.ty)
            .chain(func.constants().iter().map(|constant| constant.ty))
            .chain(collector.types.iter().copied())
            .flat_map(|ty| ty.inner_ty_vars())
            .collect()
    }

    /// Substituting a generic body by a concrete call site's instantiation leaves no type variable
    /// anywhere in it — and the result verifies, which is what makes evidence and types agree.
    #[test]
    fn substituting_a_generic_callee_makes_its_body_concrete() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            "fn twice_it(x) { x + x }\n\
             fn use_it() -> int { twice_it(3) }",
        );
        let site = site(&session, module, "use_it", "twice_it");
        assert!(
            !free_ty_vars(&site.callee, session.module_env()).is_empty(),
            "twice_it must be generic before substitution, or this test proves nothing"
        );

        let specialized = substitute_types(
            &site.callee,
            &site.scheme,
            &site.instantiation,
            session.module_env(),
        );

        assert!(
            free_ty_vars(&specialized, session.module_env()).is_empty(),
            "no type variable may survive substitution at a concrete call site"
        );
    }

    /// Substitution composes: a generic caller records its *own* quantifier on its inner call, so
    /// specializing the caller makes that inner call concrete without anything reasoning about
    /// nesting. This is the cascade the whole design rests on.
    #[test]
    fn substitution_makes_a_forwarded_inner_call_concrete() {
        let mut session = CompilerSession::new();
        let module = compile(
            &mut session,
            "fn twice_it(x) { x + x }\n\
             fn forwarding(y) { twice_it(y) }\n\
             fn use_it() -> int { forwarding(3) }",
        );
        let inner = site(&session, module, "forwarding", "twice_it");
        assert!(
            inner.instantiation.ty_args.iter().any(Type::is_variable),
            "the forwarding call must record a variable, or this test proves nothing"
        );

        let outer = site(&session, module, "use_it", "forwarding");
        let specialized = substitute_types(
            &outer.callee,
            &outer.scheme,
            &outer.instantiation,
            session.module_env(),
        );

        let mut inner_calls = 0;
        for block_id in specialized.blocks() {
            for operation in specialized.block(block_id).operations() {
                if let OperationKind::Call {
                    instantiation: Some(instantiation),
                    ..
                } = &operation.kind
                {
                    inner_calls += 1;
                    assert!(
                        instantiation.ty_args.iter().all(Type::is_constant),
                        "an inner call's recorded instantiation must be substituted too"
                    );
                }
            }
        }
        assert!(
            inner_calls > 0,
            "the specialized body must still contain the forwarded call"
        );
    }
}
