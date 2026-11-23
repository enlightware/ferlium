// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

use super::{tables::Revision, unify::UnifiedTypeInference};
use crate::{
    FxHashMap,
    compiler::error::InternalCompilationError,
    format::FormatWith,
    hir::{self, FnInstData, dictionary::DictionaryReq},
    module::{LocalDecl, LocalStorage, ModuleEnv, PendingModuleFunction},
    types::{
        effects::{EffType, EffectVar, EffectsInstSubst},
        mutability::{MutType, MutVar},
        r#type::{
            CallImplType, FnType, SubscriptType, Type, TypeInstSubst, TypeKind, TypeLimitExceeded,
            TypeVar,
        },
        type_scheme::PubTypeConstraint,
        type_substitution::{
            TypeSubstituer, substitute_fn_type, substitute_fn_type_in_place,
            substitute_subscript_type_in_place, substitute_type, substitute_type_fields_in_place,
            substitute_types, substitute_types_in_place,
        },
    },
};

/// Instantiation substitution that maps type and effect variables to actual types and effects.
pub type InstSubst = (TypeInstSubst, EffectsInstSubst);

type Result<T> = std::result::Result<T, InternalCompilationError>;

/// A type that substitution would make too large, as an error without a span yet.
fn too_large(error: TypeLimitExceeded) -> InternalCompilationError {
    InternalCompilationError::type_limit_exceeded(error)
}

impl UnifiedTypeInference {
    fn constraint_normalization_revision(&self) -> (Revision, Revision, Revision, Revision) {
        (
            self.ty_unification_table.revision(),
            self.mut_unification_table.revision(),
            self.effects.substitution_revision(),
            self.remaining_ty_constraints.revision(),
        )
    }

    /// Substitute and deduplicate only when equalities, effect substitution or
    /// the constraint vector changed. Revisions are invalidation tokens, not
    /// evidence of semantic progress for defaulting.
    pub fn normalize_remaining_constraints(&mut self) -> Result<()> {
        if self.constraints_normalized_at == Some(self.constraint_normalization_revision()) {
            self.selection_stats.skipped_constraint_normalizations += 1;
            return Ok(());
        }
        self.selection_stats.performed_constraint_normalizations += 1;
        let mut constraints = self.remaining_ty_constraints.take();
        let result = self.substitute_in_constraints_in_place(&mut constraints);
        if result.is_ok() {
            self.deduplicate_constraints_in_place(&mut constraints);
        }
        self.remaining_ty_constraints.replace(constraints);
        result?;
        self.constraints_normalized_at = Some(self.constraint_normalization_revision());
        Ok(())
    }

    /// Borrow the remaining constraints. Call `normalize_remaining_constraints`
    /// first if you need them fully substituted.
    pub fn remaining_constraints(&self) -> &[PubTypeConstraint] {
        &self.remaining_ty_constraints
    }

    pub(crate) fn replace_remaining_constraints(&mut self, constraints: Vec<PubTypeConstraint>) {
        self.remaining_ty_constraints.replace(constraints);
    }

    /// Extract the remaining constraints from self.
    pub fn take_constraints(&mut self) -> Vec<PubTypeConstraint> {
        let mut constraints = self.remaining_ty_constraints.take();
        for constraint in &mut constraints {
            constraint.set_origin(Default::default());
        }
        constraints
    }

    pub(super) fn normalize_type(&mut self, ty: Type) -> Result<Type> {
        substitute_type(ty, &mut NormalizeTypes(self)).map_err(too_large)
    }

    pub(super) fn normalize_types(&mut self, tys: &[Type]) -> Result<Vec<Type>> {
        substitute_types(tys, &mut NormalizeTypes(self)).map_err(too_large)
    }

    pub(super) fn normalize_types_in_place(&mut self, tys: &mut [Type]) -> Result<()> {
        substitute_types_in_place(tys, &mut NormalizeTypes(self)).map_err(too_large)
    }

    pub(super) fn normalize_mut_type(&mut self, mut_ty: MutType) -> MutType {
        NormalizeTypes(self).substitute_mut_type(mut_ty)
    }

    pub fn substitute_in_pending_module_function(
        &mut self,
        descr: &mut PendingModuleFunction,
    ) -> Result<()> {
        let span = descr.code.arena[descr.code.entry_node_id].span;
        descr
            .evidence_plan
            .substitute(self)
            .map_err(|error| error.locate_limit(span))?;
        self.substitute_in_fn_type_in_place(&mut descr.definition.ty_scheme.ty)
            .map_err(|error| error.locate_limit(span))?;
        self.substitute_in_constraints_in_place(&mut descr.definition.ty_scheme.constraints)?;
        self.substitute_in_node(&mut descr.code.arena, descr.code.entry_node_id)?;
        if let Some(yield_node_id) = descr.code.yield_node_id {
            self.substitute_in_node(&mut descr.code.arena, yield_node_id)?;
        }
        self.substitute_in_local_decls_in_place(&mut descr.locals)
            .map_err(|error| error.locate_limit(span))
    }

    pub fn substitute_in_type(&mut self, ty: Type) -> Result<Type> {
        substitute_type(ty, &mut SubstituteTypes::new(self)).map_err(too_large)
    }

    pub fn substitute_in_types(&mut self, tys: &[Type]) -> Result<Vec<Type>> {
        substitute_types(tys, &mut SubstituteTypes::new(self)).map_err(too_large)
    }

    pub fn substitute_in_types_in_place(&mut self, tys: &mut [Type]) -> Result<()> {
        substitute_types_in_place(tys, &mut SubstituteTypes::new(self)).map_err(too_large)
    }

    pub fn substitute_in_fn_type(&mut self, fn_ty: &FnType) -> Result<FnType> {
        substitute_fn_type(fn_ty, &mut SubstituteTypes::new(self)).map_err(too_large)
    }

    pub fn substitute_in_fn_type_in_place(&mut self, fn_ty: &mut FnType) -> Result<()> {
        substitute_fn_type_in_place(fn_ty, &mut SubstituteTypes::new(self)).map_err(too_large)
    }

    pub fn substitute_in_subscript_type_in_place(
        &mut self,
        subscript_ty: &mut SubscriptType,
    ) -> Result<()> {
        substitute_subscript_type_in_place(subscript_ty, &mut SubstituteTypes::new(self))
            .map_err(too_large)
    }

    pub fn substitute_in_call_impl_type_in_place(
        &mut self,
        call_ty: &mut CallImplType,
    ) -> Result<()> {
        self.substitute_in_fn_type_in_place(&mut call_ty.fn_ty)
    }

    pub fn substitute_in_mut_type(&mut self, mut_ty: MutType) -> MutType {
        SubstituteTypes::new(self).substitute_mut_type(mut_ty)
    }

    pub fn substitute_in_effect_type(&mut self, eff_ty: &EffType) -> EffType {
        SubstituteTypes::new(self).substitute_effect_type(eff_ty)
    }

    pub fn substitute_in_effect_types(&mut self, eff_tys: &[EffType]) -> Vec<EffType> {
        eff_tys
            .iter()
            .map(|eff| self.substitute_in_effect_type(eff))
            .collect()
    }

    pub fn substitute_in_effect_types_in_place(&mut self, eff_tys: &mut [EffType]) {
        for eff in eff_tys {
            *eff = SubstituteTypes::new(self).substitute_effect_type(eff);
        }
    }

    pub(crate) fn substitute_in_local_decls_in_place(
        &mut self,
        locals: &mut [LocalDecl],
    ) -> Result<()> {
        substitute_type_fields_in_place(
            locals,
            |local| &mut local.ty,
            &mut SubstituteTypes::new(self),
        )
        .map_err(too_large)?;
        for local in locals {
            local.mut_ty = self.substitute_in_mut_type(local.mut_ty);
            if let LocalStorage::Deferred(deferred) = &mut local.storage {
                deferred.initializer_mut_ty =
                    self.substitute_in_mut_type(deferred.initializer_mut_ty);
                deferred.binding_mut_ty = self.substitute_in_mut_type(deferred.binding_mut_ty);
            }
        }
        Ok(())
    }

    pub fn lookup_type_var(&mut self, var: TypeVar) -> Type {
        match self.ty_unification_table.probe_value(var) {
            Some(ty) => ty,
            _ => Type::variable(self.ty_unification_table.find(var)),
        }
    }

    fn substitute_type_lookup(&mut self, ty: Type) -> Type {
        let ty_data = ty.data();
        let var = match &*ty_data {
            TypeKind::Variable(var) => *var,
            _ => return ty,
        };
        drop(ty_data);
        self.lookup_type_var(var)
    }

    fn substitute_mut_lookup(&mut self, mut_ty: MutType, accept_var: bool) -> MutType {
        match mut_ty {
            MutType::Resolved(_) => mut_ty,
            MutType::Variable(var) => {
                let root = self.mut_unification_table.find(var);
                match self.mut_unification_table.probe_value(root) {
                    Some(val) => MutType::resolved(val),
                    _ => {
                        if accept_var {
                            MutType::variable(root)
                        } else {
                            panic!("Unresolved mutability variable")
                        }
                    }
                }
            }
        }
    }

    /// Sharper `affects_type` predicate shared by `SubstituteTypes` and
    /// `NormalizeTypes`: returns `true` iff substituting `ty` against the
    /// current unification tables would change anything. A free variable can
    /// only induce a change if it has either been bound to a value or
    /// unified with a different root variable.
    fn substitution_affects_type(&mut self, ty: Type) -> bool {
        let summary = ty.summary();
        if summary.free_ty_vars.is_empty()
            && summary.free_mut_vars.is_empty()
            && summary.free_eff_vars.is_empty()
        {
            return false;
        }
        for var in summary.free_ty_vars.iter() {
            if self.ty_unification_table.probe_value(var).is_some()
                || self.ty_unification_table.find(var) != var
            {
                return true;
            }
        }
        for var in summary.free_mut_vars.iter() {
            if self.mut_unification_table.probe_value(var).is_some()
                || self.mut_unification_table.find(var) != var
            {
                return true;
            }
        }
        for var in summary.free_eff_vars.iter() {
            if self.effects.effect_var_affects_substitution(var) {
                return true;
            }
        }
        false
    }

    pub fn substitute_in_node(
        &mut self,
        arena: &mut hir::NodeArena,
        node_id: hir::NodeId,
    ) -> Result<()> {
        let children = arena[node_id].kind.child_node_ids();
        for child in children {
            self.substitute_in_node(arena, child)?;
        }
        let span = arena[node_id].span;
        self.substitute_in_node_types(arena, node_id)
            .map_err(|error| error.locate_limit(span))
    }

    fn substitute_in_node_types(
        &mut self,
        arena: &mut hir::NodeArena,
        node_id: hir::NodeId,
    ) -> Result<()> {
        let node = &mut arena[node_id];
        node.ty = self.substitute_in_type(node.ty)?;
        node.effects = SubstituteTypes::new(self).substitute_effect_type(&node.effects);
        use hir::NodeKind::*;
        match &mut arena[node_id].kind {
            PendingAssignment(plan) => {
                if let hir::PendingAssignment::DivergingInputs { argument_types, .. } = &mut **plan
                {
                    for arg in argument_types {
                        arg.ty = self.substitute_in_type(arg.ty)?;
                        arg.mut_ty = self.substitute_in_mut_type(arg.mut_ty);
                    }
                }
            }
            SubscriptApply(app) => {
                self.substitute_in_call_impl_type_in_place(&mut app.ty)?;
            }
            FunctionApply(app) => {
                self.substitute_in_call_impl_type_in_place(&mut app.ty)?;
            }
            StaticApply(app) => {
                self.substitute_in_call_impl_type_in_place(&mut app.ty)?;
                self.substitute_in_fn_inst_data(&mut app.inst_data)?;
            }
            TraitMethodApply(app) => {
                self.substitute_in_call_impl_type_in_place(&mut app.ty)?;
                self.substitute_in_types_in_place(&mut app.input_tys)?;
                self.substitute_in_types_in_place(&mut app.output_tys)?;
                self.substitute_in_effect_types_in_place(&mut app.output_effs);
                self.substitute_in_fn_inst_data(&mut app.inst_data)?;
            }
            GetFunction(get_fn) => {
                self.substitute_in_fn_inst_data(&mut get_fn.inst_data)?;
            }
            GetSubscript(get_subscript) => {
                self.substitute_in_fn_inst_data(&mut get_subscript.inst_data)?;
            }
            GetTraitMethod(get_method) => {
                self.substitute_in_types_in_place(&mut get_method.input_tys)?;
                self.substitute_in_types_in_place(&mut get_method.output_tys)?;
                self.substitute_in_effect_types_in_place(&mut get_method.output_effs);
                self.substitute_in_fn_inst_data(&mut get_method.inst_data)?;
            }
            GetTraitAssociatedConst(get_const) => {
                self.substitute_in_types_in_place(&mut get_const.input_tys)?;
                self.substitute_in_types_in_place(&mut get_const.output_tys)?;
                self.substitute_in_effect_types_in_place(&mut get_const.output_effs);
            }
            GetVariantPayloadStorage(get_storage) => {
                get_storage.variant_ty = self.substitute_in_type(get_storage.variant_ty)?;
                get_storage.payload_ty = self.substitute_in_type(get_storage.payload_ty)?;
            }
            GetTraitDictionary(get_dict) => {
                self.substitute_in_types_in_place(&mut get_dict.input_tys)?;
                self.substitute_in_types_in_place(&mut get_dict.output_tys)?;
                self.substitute_in_effect_types_in_place(&mut get_dict.output_effs);
            }
            _ => {}
        }
        Ok(())
    }

    fn substitute_in_fn_inst_data(&mut self, inst_data: &mut FnInstData) -> Result<()> {
        for dict in &mut inst_data.dicts_req {
            match dict {
                DictionaryReq::ProjectionSubscript { subscript_ty, .. } => {
                    self.substitute_in_subscript_type_in_place(subscript_ty)?;
                }
                DictionaryReq::VariantPayloadIndirection {
                    variant_ty,
                    payload_ty,
                    ..
                } => {
                    *variant_ty = self.substitute_in_type(*variant_ty)?;
                    *payload_ty = self.substitute_in_type(*payload_ty)?;
                }
                DictionaryReq::TraitImpl {
                    input_tys,
                    output_tys,
                    output_effs,
                    ..
                } => {
                    self.substitute_in_types_in_place(input_tys)?;
                    self.substitute_in_types_in_place(output_tys)?;
                    self.substitute_in_effect_types_in_place(output_effs);
                }
            }
        }
        // The arguments hold the fresh variables allocated when the callee's scheme was
        // instantiated; this is where they become the types unification solved them to.
        self.substitute_in_types_in_place(&mut inst_data.ty_args)?;
        self.substitute_in_effect_types_in_place(&mut inst_data.eff_args);
        Ok(())
    }

    pub fn substitute_in_constraint(
        &mut self,
        constraint: &PubTypeConstraint,
    ) -> Result<PubTypeConstraint> {
        let mut constraint = constraint.clone();
        self.substitute_in_constraint_in_place(&mut constraint)?;
        Ok(constraint)
    }

    fn substitute_in_constraint_in_place(
        &mut self,
        constraint: &mut PubTypeConstraint,
    ) -> Result<()> {
        let span = constraint.use_site();
        self.substitute_in_constraint_types(constraint)
            .map_err(|error| error.locate_limit(span))
    }

    fn substitute_in_constraint_types(&mut self, constraint: &mut PubTypeConstraint) -> Result<()> {
        use PubTypeConstraint::*;
        match constraint {
            TupleAtIndexIs {
                tuple_ty,
                element_ty,
                ..
            } => {
                *tuple_ty = self.substitute_in_type(*tuple_ty)?;
                *element_ty = self.substitute_in_type(*element_ty)?;
            }
            ProjectionSubscriptIs { subscript_ty, .. } => {
                self.substitute_in_subscript_type_in_place(subscript_ty)?;
            }
            TypeHasVariant {
                variant_ty,
                payload_ty,
                ..
            }
            | VariantPayloadLayout {
                variant_ty,
                payload_ty,
                ..
            }
            | VariantPayloadStorage {
                variant_ty,
                payload_ty,
                ..
            } => {
                *variant_ty = self.substitute_in_type(*variant_ty)?;
                *payload_ty = self.substitute_in_type(*payload_ty)?;
            }
            HaveTrait {
                input_tys,
                output_tys,
                output_effs,
                ..
            } => {
                self.substitute_in_types_in_place(input_tys)?;
                self.substitute_in_types_in_place(output_tys)?;
                self.substitute_in_effect_types_in_place(output_effs);
            }
        }
        Ok(())
    }

    pub(crate) fn substitute_in_constraints(
        &mut self,
        constraints: &[PubTypeConstraint],
    ) -> Result<Vec<PubTypeConstraint>> {
        let mut constraints = constraints.to_vec();
        self.substitute_in_constraints_in_place(&mut constraints)?;
        Ok(constraints)
    }

    pub(super) fn substitute_in_constraints_in_place(
        &mut self,
        constraints: &mut [PubTypeConstraint],
    ) -> Result<()> {
        for constraint in constraints {
            self.substitute_in_constraint_in_place(constraint)?;
        }
        Ok(())
    }

    pub fn log_debug_constraints(&self, module_env: ModuleEnv) {
        if !log::log_enabled!(log::Level::Trace) {
            return;
        }
        if self.remaining_ty_constraints.is_empty() {
            log::trace!("No type constraints after unification.");
        } else {
            log::trace!("Type constraints after unification:");
            if !self.remaining_ty_constraints.is_empty() {
                for constraint in self.remaining_ty_constraints.iter() {
                    log::trace!("  {}", constraint.format_with(&module_env));
                }
            }
        }
    }

    pub fn log_debug_substitution_tables(&mut self, module_env: ModuleEnv) {
        if !log::log_enabled!(log::Level::Trace) {
            return;
        }
        log::trace!("Type substitution table:");
        for i in 0..self.ty_unification_table.len() {
            let var = TypeVar::new(i as u32);
            let value = self.ty_unification_table.probe_value(var);
            match value {
                Some(value) => log::trace!("  {var} → {}", value.format_with(&module_env)),
                None => log::trace!("  {var} → {} (unbound)", {
                    self.ty_unification_table.find(var)
                }),
            }
        }
        log::trace!("Mutability substitution table:");
        for i in 0..self.mut_unification_table.len() {
            let var = MutVar::new(i as u32);
            let value = self.mut_unification_table.probe_value(var);
            match value {
                Some(value) => log::trace!("  {var} → {value}"),
                None => log::trace!("  {var} → {} (unbound)", {
                    self.mut_unification_table.find(var)
                }),
            }
        }
        self.effects.log_debug_constraints();
    }
}

struct SubstituteTypes<'a> {
    ty_inf: &'a mut UnifiedTypeInference,
    effect_cache: FxHashMap<EffectVar, EffType>,
}

impl<'a> SubstituteTypes<'a> {
    fn new(ty_inf: &'a mut UnifiedTypeInference) -> Self {
        Self {
            ty_inf,
            effect_cache: FxHashMap::default(),
        }
    }
}

impl SubstituteTypes<'_> {
    fn substitute_effect_var(&mut self, var: EffectVar) -> EffType {
        if let Some(cached) = self.effect_cache.get(&var) {
            return cached.clone();
        }
        let effects = self.ty_inf.effects.substitute_var(var);
        self.effect_cache.insert(var, effects.clone());
        effects
    }
}

impl TypeSubstituer for SubstituteTypes<'_> {
    fn substitute_type(&mut self, ty: Type) -> Type {
        self.ty_inf.substitute_type_lookup(ty)
    }

    fn substitute_mut_type(&mut self, mut_ty: MutType) -> MutType {
        self.ty_inf.substitute_mut_lookup(mut_ty, false)
    }

    fn affects_type(&mut self, ty: Type) -> bool {
        self.ty_inf.substitution_affects_type(ty)
    }

    /// Substitute the effect type by flattening the effect variables.
    fn substitute_effect_type(&mut self, eff_ty: &EffType) -> EffType {
        if !eff_ty.has_variables() {
            return eff_ty.clone();
        }
        let mut effects = EffType::multiple_primitive(&eff_ty.inner_non_vars());
        for var in eff_ty.inner_vars() {
            effects.extend(&self.substitute_effect_var(var));
        }
        effects
    }
}

/// Normalization phase
struct NormalizeTypes<'a>(&'a mut UnifiedTypeInference);
impl TypeSubstituer for NormalizeTypes<'_> {
    fn substitute_type(&mut self, ty: Type) -> Type {
        self.0.substitute_type_lookup(ty)
    }

    fn substitute_mut_type(&mut self, mut_ty: MutType) -> MutType {
        self.0.substitute_mut_lookup(mut_ty, true)
    }

    fn substitute_effect_type(&mut self, eff_ty: &EffType) -> EffType {
        eff_ty.clone()
    }

    fn affects_type(&mut self, ty: Type) -> bool {
        self.0.substitution_affects_type(ty)
    }
}

#[cfg(test)]
mod tests {
    use super::UnifiedTypeInference;
    use crate::{
        compiler::error::{CompilationErrorImpl, CompilerLimitKind},
        parser::location::Location,
        types::{
            effects::{EffType, Effect, PrimitiveEffect},
            r#type::{TYPE_HEIGHT_LIMIT, Type},
        },
    };

    /// `α0 := (α1,)`, `α1 := (α2,)`, …: each binding is shallow when it is made, but substitution
    /// builds a type as high as the chain. It stops at the limit, on the stack that the limit
    /// bounds, rather than when the type is interned.
    #[test]
    fn substitution_limits_the_height_of_delayed_bindings() {
        let n = 4 * TYPE_HEIGHT_LIMIT;
        let mut inference = UnifiedTypeInference::new_with_ty_vars(n + 1);
        let span = Location::new_synthesized();
        for i in 0..n {
            let wrapped = Type::tuple(vec![Type::variable_id(i + 1)]);
            inference
                .unify_same_type(Type::variable_id(i), span, wrapped, span)
                .unwrap();
        }
        let error = inference
            .substitute_in_type(Type::variable_id(0))
            .unwrap_err();
        let CompilationErrorImpl::CompilerLimitExceeded(limit) = &*error else {
            panic!("expected a compiler limit, got {error:?}");
        };
        assert_eq!(limit.kind, CompilerLimitKind::TypeHeight);
        // Within the limit, the chain substitutes.
        let deepest = Type::variable_id(n - TYPE_HEIGHT_LIMIT + 1);
        let substituted = inference.substitute_in_type(deepest).unwrap();
        assert_eq!(substituted.metrics().0, TYPE_HEIGHT_LIMIT);
        // A failed substitution leaves the types it substitutes in place as they were.
        let original = [deepest, Type::variable_id(0)];
        let mut tys = original;
        inference
            .substitute_in_types_in_place(&mut tys)
            .unwrap_err();
        assert_eq!(tys, original);
    }

    #[test]
    fn constraint_normalization_observes_effect_publication() {
        use crate::{
            module::{LocalTraitId, ModuleId, TraitId},
            types::type_scheme::PubTypeConstraint,
        };
        let mut inference = UnifiedTypeInference::default();
        let span = Location::new_synthesized();
        let effect = EffType::single_variable(inference.fresh_effect_var());
        let ceiling = EffType::single_primitive(PrimitiveEffect::Read);
        inference
            .add_effect_inclusion(&effect, span, &ceiling, span)
            .unwrap();
        let constraint = |output| {
            PubTypeConstraint::new_have_trait(
                TraitId::new(ModuleId::new(0), LocalTraitId::new(0)),
                vec![],
                vec![],
                vec![output],
                span,
            )
        };
        inference
            .remaining_ty_constraints
            .push(constraint(effect.clone()));
        inference.normalize_remaining_constraints().unwrap();
        assert_eq!(inference.remaining_constraints(), &[constraint(effect)]);
        inference.effects.finalize().unwrap();
        inference.normalize_remaining_constraints().unwrap();
        assert_eq!(inference.remaining_constraints(), &[constraint(ceiling)]);
    }

    #[test]
    fn constraint_normalization_revisions_cover_inputs_and_substitutions() {
        use crate::{
            module::{LocalTraitId, ModuleId, TraitId},
            std::{logic::bool_type, math::int_type},
            types::{
                mutability::{MutType, MutVal},
                r#type::{FnArgType, FnType, Type},
                type_scheme::PubTypeConstraint,
            },
        };
        let mut inference = UnifiedTypeInference::new_with_ty_vars(2);
        let span = Location::new_synthesized();
        let effect = EffType::single_variable(inference.fresh_effect_var());
        let mut_var = inference.mut_unification_table.new_key(None);
        let callable = Type::function_type(FnType::new(
            vec![FnArgType {
                ty: Type::variable_id(0),
                mut_ty: MutType::variable(mut_var),
            }],
            Type::variable_id(1),
            effect.clone(),
        ));
        // Public constraints are normalized only after mutability is resolved.
        inference
            .mut_unification_table
            .unify_var_value(mut_var, Some(MutVal::constant()))
            .unwrap();
        let constraint = |ty| {
            PubTypeConstraint::new_have_trait(
                TraitId::new(ModuleId::new(0), LocalTraitId::new(0)),
                vec![ty],
                vec![],
                vec![],
                span,
            )
        };
        inference
            .remaining_ty_constraints
            .push(constraint(callable));
        inference.normalize_remaining_constraints().unwrap();
        let first = inference.constraints_normalized_at;
        inference.fresh_type_var(); // allocation cannot affect an existing term
        inference.fresh_effect_var();
        inference.fresh_rigid_effect_var();
        inference.lookup_type_var(crate::types::r#type::TypeVar::new(0));
        inference.normalize_remaining_constraints().unwrap();
        assert_eq!(inference.constraints_normalized_at, first);

        inference
            .unify_same_type(Type::variable_id(0), span, int_type(), span)
            .unwrap();
        inference.normalize_remaining_constraints().unwrap();
        assert_ne!(inference.constraints_normalized_at, first);
        let expected = inference.substitute_in_type(callable).unwrap();
        assert_eq!(inference.remaining_constraints(), &[constraint(expected)]);

        let before_effect = inference.constraints_normalized_at;
        inference
            .unify_same_effect(&effect, span, &EffType::empty(), span)
            .unwrap();
        inference.normalize_remaining_constraints().unwrap();
        assert_ne!(inference.constraints_normalized_at, before_effect);
        let expected = inference.substitute_in_type(callable).unwrap();
        assert_eq!(inference.remaining_constraints(), &[constraint(expected)]);

        // Replacing with the same length must invalidate, even without a binding.
        inference.remaining_ty_constraints[0] = constraint(Type::variable_id(0));
        inference.normalize_remaining_constraints().unwrap();
        assert_eq!(inference.remaining_constraints(), &[constraint(int_type())]);
        inference
            .remaining_ty_constraints
            .push(constraint(int_type()));
        inference.normalize_remaining_constraints().unwrap();
        assert_eq!(inference.remaining_constraints().len(), 1);

        // A failed speculative branch must not reuse its normalization stamp.
        let snapshot = inference.snapshot();
        inference
            .unify_same_type(Type::variable_id(1), span, bool_type(), span)
            .unwrap();
        inference.normalize_remaining_constraints().unwrap();
        let speculative = inference.constraints_normalized_at;
        inference.rollback_to(snapshot);
        inference.normalize_remaining_constraints().unwrap();
        assert_ne!(inference.constraints_normalized_at, speculative);
        assert_eq!(
            inference.normalize_type(Type::variable_id(1)).unwrap(),
            Type::variable_id(1)
        );
    }

    /// A rollback restores the constraints that a speculation rewrote, not only their number:
    /// two that a temporary binding makes equal, and that normalization merges, are both back.
    #[test]
    fn rollback_restores_constraints_that_normalization_merged() {
        use crate::{
            module::{LocalTraitId, ModuleId, TraitId},
            types::{r#type::Type, type_scheme::PubTypeConstraint},
        };
        let mut inference = UnifiedTypeInference::new_with_ty_vars(2);
        let span = Location::new_synthesized();
        let constraint = |ty| {
            PubTypeConstraint::new_have_trait(
                TraitId::new(ModuleId::new(0), LocalTraitId::new(0)),
                vec![ty],
                vec![],
                vec![],
                span,
            )
        };
        let originals = vec![
            constraint(Type::variable_id(0)),
            constraint(Type::variable_id(1)),
        ];
        inference.replace_remaining_constraints(originals.clone());
        let snapshot = inference.snapshot();
        inference
            .unify_same_type(Type::variable_id(0), span, Type::variable_id(1), span)
            .unwrap();
        inference.normalize_remaining_constraints().unwrap();
        assert_eq!(inference.remaining_constraints().len(), 1);
        inference.rollback_to(snapshot);
        assert_eq!(inference.remaining_constraints(), &originals[..]);
    }

    #[test]
    fn recursive_effect_substitution_reaches_a_fixed_point() {
        let mut unified = UnifiedTypeInference::default();
        let var = unified.fresh_effect_var();
        let span = Location::new_synthesized();
        let recursive_effect =
            EffType::single_primitive(PrimitiveEffect::Read).union(&EffType::single_variable(var));

        unified
            .unify_same_effect(
                &EffType::single_variable(var),
                span,
                &recursive_effect,
                span,
            )
            .unwrap();

        let mut substituted = EffType::single_variable(var);
        for _ in 0..8 {
            substituted = unified.substitute_in_effect_type(&substituted);
            assert!(substituted.contains(Effect::Primitive(PrimitiveEffect::Read)));
            assert!(substituted.contains(Effect::Variable(var)));
        }
        assert_eq!(substituted, recursive_effect);
    }

    #[test]
    fn recursive_effect_substitution_canonicalizes_alias_cycles() {
        let mut unified = UnifiedTypeInference::default();
        let first = unified.fresh_effect_var();
        let second = unified.fresh_effect_var();
        let span = Location::new_synthesized();

        unified
            .unify_same_effect(
                &EffType::single_variable(first),
                span,
                &EffType::single_primitive(PrimitiveEffect::Read)
                    .union(&EffType::single_variable(second)),
                span,
            )
            .unwrap();
        unified
            .unify_same_effect(
                &EffType::single_variable(second),
                span,
                &EffType::single_variable(first),
                span,
            )
            .unwrap();

        let substituted = unified.substitute_in_effect_type(&EffType::single_variable(first));
        assert!(substituted.contains(Effect::Primitive(PrimitiveEffect::Read)));
        assert_eq!(substituted.inner_vars().len(), 1);
        assert_eq!(
            substituted,
            unified.substitute_in_effect_type(&EffType::single_variable(second))
        );
    }
}
