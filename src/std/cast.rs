// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use std::sync::LazyLock;

use crate::{
    Location,
    compiler::error::InternalCompilationError,
    hir,
    hir::function::FunctionDefinition,
    module::{LocalDeclId, Module, TraitImplId, id::Id},
    std::STD_MODULE_ID,
    types::effects::EffType,
    types::r#trait::{Deriver, TraitRef},
    types::trait_solver::TraitSolver,
    types::r#type::{FnType, Type},
};

use FunctionDefinition as Def;

#[derive(Debug, Clone)]
struct SelfCastDeriver;
impl Deriver for SelfCastDeriver {
    fn derive_impl(
        &self,
        trait_ref: &TraitRef,
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

        // No-op implementation
        let locals = vec![local("self", from_ty)];
        let id = LocalDeclId::from_index(0);
        let code_id = arena.alloc(hir::Node::new(load(0, id), from_ty, EffType::empty(), span));
        let local_impl_id =
            solver.add_concrete_impl_from_code(code_id, locals, trait_ref, input_types, []);
        Ok(Some(TraitImplId::Local(local_impl_id)))

        // TODO: optimize away the cast entirely in the compiler
        // TODO: add same-code optimization passes in module building to reduce duplications generated here
    }
}

pub static CAST_TRAIT: LazyLock<TraitRef> = LazyLock::new(|| {
    let var0_ty = Type::variable_id(0);
    let var1_ty = Type::variable_id(1);
    let unary_fn_ty = FnType::new_by_val([var0_ty], var1_ty, EffType::empty());
    let cast_trait = TraitRef::new(
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
    );
    cast_trait.with_module_id_and_deriver(STD_MODULE_ID, SelfCastDeriver)
});

pub fn add_to_module(to: &mut Module) {
    // Traits
    to.add_trait(CAST_TRAIT.clone());
}
