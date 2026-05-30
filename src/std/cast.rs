// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use crate::{
    Location,
    compiler::error::InternalCompilationError,
    hir,
    hir::function::FunctionDefinition,
    module::{
        LocalDeclId, Module, PendingLocalClone, ResolvedLocalClone, TraitId, TraitImplId, id::Id,
    },
    std::{core_traits_names::VALUE_TRAIT_NAME, value::VALUE_CLONE_METHOD_INDEX},
    types::effects::{EffType, PrimitiveEffect},
    types::r#trait::{Deriver, Trait},
    types::trait_solver::TraitSolver,
    types::r#type::{FnType, Type},
    types::type_like::TypeLike,
};
use ustr::ustr;

use FunctionDefinition as Def;

#[derive(Debug, Clone)]
struct SelfCastDeriver;
impl Deriver for SelfCastDeriver {
    fn derive_impl(
        &self,
        trait_id: TraitId,
        input_types: &[Type],
        span: Location,
        arena: &mut hir::NodeArena,
        solver: &mut TraitSolver,
    ) -> Result<Option<TraitImplId>, InternalCompilationError> {
        use hir::hir_syn::*;
        let from_ty = input_types[0];
        let to_ty = input_types[1];
        if from_ty != to_ty {
            return Ok(None);
        }
        if !from_ty.is_constant() {
            return Ok(None);
        }

        // Identity implementation: clone from borrowed argument storage into
        // the returned value.
        let locals = vec![local("value", from_ty)];
        let id = LocalDeclId::from_index(0);
        let source_id = arena.alloc(hir::Node::new(
            load_local(id),
            from_ty,
            EffType::empty(),
            span,
        ));
        let clone = solver.solve_impl_method(
            solver.std_trait_id(VALUE_TRAIT_NAME),
            &[from_ty],
            VALUE_CLONE_METHOD_INDEX,
            span,
            arena,
        )?;
        let code_id = arena.alloc(hir::Node::new(
            hir::NodeKind::CloneValue(hir::CloneValue {
                source: source_id,
                clone: PendingLocalClone::Resolved(ResolvedLocalClone::Static(clone)),
            }),
            from_ty,
            EffType::empty(),
            span,
        ));
        let local_impl_id =
            solver.add_concrete_impl_from_code(code_id, locals, trait_id, input_types, []);
        Ok(Some(TraitImplId::Local(local_impl_id)))

        // TODO: optimize away the cast entirely in the compiler
        // TODO: add same-code optimization passes in module building to reduce duplications generated here
    }
}

pub fn cast_trait() -> Trait {
    let var0_ty = Type::variable_id(0);
    let var1_ty = Type::variable_id(1);
    let unary_fn_ty = FnType::new_by_val(
        [var0_ty],
        var1_ty,
        EffType::single_primitive(PrimitiveEffect::Fallible),
    );
    Trait::new(
        "Cast",
        "Conversion of a value from one type to another.",
        ["From", "To"],
        [],
        [(
            "cast",
            Def::new_infer_quantifiers(
                unary_fn_ty,
                ["value"],
                "Casts `value` to the type of `To`.",
            ),
        )],
    )
    .with_deriver(SelfCastDeriver)
}

pub fn add_to_module(to: &mut Module) {
    // Traits
    let id = to.add_trait(cast_trait());
    debug_assert_eq!(to.get_trait_id(ustr("Cast")).unwrap().index, id);
}
