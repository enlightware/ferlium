use std::mem;

use crate::{
    FxHashMap, FxHashSet,
    format::FormatWith,
    hir::dictionary::DictionaryReq,
    hir::{self, FnInstData},
    module::{LocalDecl, LocalStorage, ModuleEnv},
    types::{
        effects::{EffType, Effect, EffectVar, EffectsInstSubst},
        mutability::{MutType, MutVar},
        r#type::{FnType, Type, TypeInstSubst, TypeKind, TypeVar},
        type_scheme::PubTypeConstraint,
        type_substitution::{
            TypeSubstituer, substitute_fn_type, substitute_fn_type_in_place, substitute_type,
            substitute_type_fields_in_place, substitute_types, substitute_types_in_place,
        },
    },
};

use super::unify::UnifiedTypeInference;

/// Instantiation substitution that maps type and effect variables to actual types and effects.
pub type InstSubst = (TypeInstSubst, EffectsInstSubst);

impl UnifiedTypeInference {
    /// Substitute the remaining constraints using the current unification tables,
    /// storing the normalized constraints back into self.
    pub fn normalize_remaining_constraints(&mut self) {
        let mut constraints = mem::take(&mut self.remaining_ty_constraints);
        self.substitute_in_constraints_in_place(&mut constraints);
        self.remaining_ty_constraints = constraints;
    }

    /// Borrow the remaining constraints. Call `normalize_remaining_constraints`
    /// first if you need them fully substituted.
    pub fn remaining_constraints(&self) -> &[PubTypeConstraint] {
        &self.remaining_ty_constraints
    }

    /// Extract the remaining constraints from self.
    pub fn take_constraints(&mut self) -> Vec<PubTypeConstraint> {
        mem::take(&mut self.remaining_ty_constraints)
    }

    pub(super) fn normalize_type(&mut self, ty: Type) -> Type {
        substitute_type(ty, &mut NormalizeTypes(self))
    }

    pub(super) fn normalize_types(&mut self, tys: &[Type]) -> Vec<Type> {
        substitute_types(tys, &mut NormalizeTypes(self))
    }

    pub(super) fn normalize_types_in_place(&mut self, tys: &mut [Type]) {
        substitute_types_in_place(tys, &mut NormalizeTypes(self));
    }

    pub(super) fn normalize_mut_type(&mut self, mut_ty: MutType) -> MutType {
        NormalizeTypes(self).substitute_mut_type(mut_ty)
    }

    pub fn substitute_in_pending_module_function(
        &mut self,
        descr: &mut crate::module::PendingModuleFunction,
    ) {
        self.substitute_in_fn_type_in_place(&mut descr.definition.ty_scheme.ty);
        self.substitute_in_constraints_in_place(&mut descr.definition.ty_scheme.constraints);
        self.substitute_in_node(&mut descr.code.arena, descr.code.entry_node_id);
        self.substitute_in_local_decls_in_place(&mut descr.locals);
    }

    pub fn substitute_in_type(&mut self, ty: Type) -> Type {
        substitute_type(ty, &mut SubstituteTypes::new(self))
    }

    pub fn substitute_in_types(&mut self, tys: &[Type]) -> Vec<Type> {
        substitute_types(tys, &mut SubstituteTypes::new(self))
    }

    pub fn substitute_in_types_in_place(&mut self, tys: &mut [Type]) {
        substitute_types_in_place(tys, &mut SubstituteTypes::new(self));
    }

    pub fn substitute_in_fn_type(&mut self, fn_ty: &FnType) -> FnType {
        substitute_fn_type(fn_ty, &mut SubstituteTypes::new(self))
    }

    pub fn substitute_in_fn_type_in_place(&mut self, fn_ty: &mut FnType) {
        substitute_fn_type_in_place(fn_ty, &mut SubstituteTypes::new(self));
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

    pub(crate) fn substitute_in_local_decls_in_place(&mut self, locals: &mut [LocalDecl]) {
        substitute_type_fields_in_place(
            locals,
            |local| &mut local.ty,
            &mut SubstituteTypes::new(self),
        );
        for local in locals {
            local.mut_ty = self.substitute_in_mut_type(local.mut_ty);
            if let LocalStorage::Deferred(deferred) = &mut local.storage {
                deferred.initializer_mut_ty =
                    self.substitute_in_mut_type(deferred.initializer_mut_ty);
            }
        }
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

    pub fn substitute_in_node(&mut self, arena: &mut hir::NodeArena, node_id: hir::NodeId) {
        let children = arena[node_id].kind.child_node_ids();
        for child in children {
            self.substitute_in_node(arena, child);
        }
        let node = &mut arena[node_id];
        node.ty = self.substitute_in_type(node.ty);
        node.effects = SubstituteTypes::new(self).substitute_effect_type(&node.effects);
        use hir::NodeKind::*;
        match &mut arena[node_id].kind {
            Apply(app) => {
                self.substitute_in_fn_type_in_place(&mut app.ty);
            }
            StaticApply(app) => {
                self.substitute_in_fn_type_in_place(&mut app.ty);
                self.substitute_in_fn_inst_data(&mut app.inst_data);
            }
            TraitMethodApply(app) => {
                self.substitute_in_fn_type_in_place(&mut app.ty);
                self.substitute_in_types_in_place(&mut app.input_tys);
                self.substitute_in_fn_inst_data(&mut app.inst_data);
            }
            GetFunction(get_fn) => {
                self.substitute_in_fn_inst_data(&mut get_fn.inst_data);
            }
            GetTraitMethod(get_method) => {
                self.substitute_in_types_in_place(&mut get_method.input_tys);
                self.substitute_in_types_in_place(&mut get_method.output_tys);
                self.substitute_in_effect_types_in_place(&mut get_method.output_effs);
                self.substitute_in_fn_inst_data(&mut get_method.inst_data);
            }
            GetTraitAssociatedConst(get_const) => {
                self.substitute_in_types_in_place(&mut get_const.input_tys);
                self.substitute_in_types_in_place(&mut get_const.output_tys);
                self.substitute_in_effect_types_in_place(&mut get_const.output_effs);
            }
            GetTraitDictionary(get_dict) => {
                self.substitute_in_types_in_place(&mut get_dict.input_tys);
                self.substitute_in_types_in_place(&mut get_dict.output_tys);
                self.substitute_in_effect_types_in_place(&mut get_dict.output_effs);
            }
            _ => {}
        }
    }

    fn substitute_in_fn_inst_data(&mut self, inst_data: &mut FnInstData) {
        for dict in &mut inst_data.dicts_req {
            match dict {
                DictionaryReq::FieldIndex { ty, .. } => {
                    *ty = self.substitute_in_type(*ty);
                }
                DictionaryReq::TraitImpl {
                    input_tys,
                    output_tys,
                    output_effs,
                    ..
                } => {
                    self.substitute_in_types_in_place(input_tys);
                    self.substitute_in_types_in_place(output_tys);
                    self.substitute_in_effect_types_in_place(output_effs);
                }
            }
        }
    }

    pub fn substitute_in_constraint(
        &mut self,
        constraint: &PubTypeConstraint,
    ) -> PubTypeConstraint {
        let mut constraint = constraint.clone();
        self.substitute_in_constraint_in_place(&mut constraint);
        constraint
    }

    fn substitute_in_constraint_in_place(&mut self, constraint: &mut PubTypeConstraint) {
        use PubTypeConstraint::*;
        match constraint {
            TupleAtIndexIs {
                tuple_ty,
                element_ty,
                ..
            } => {
                *tuple_ty = self.substitute_in_type(*tuple_ty);
                *element_ty = self.substitute_in_type(*element_ty);
            }
            RecordFieldIs {
                record_ty,
                element_ty,
                ..
            } => {
                *record_ty = self.substitute_in_type(*record_ty);
                *element_ty = self.substitute_in_type(*element_ty);
            }
            TypeHasVariant {
                variant_ty,
                payload_ty,
                ..
            } => {
                *variant_ty = self.substitute_in_type(*variant_ty);
                *payload_ty = self.substitute_in_type(*payload_ty);
            }
            HaveTrait {
                input_tys,
                output_tys,
                output_effs,
                ..
            } => {
                self.substitute_in_types_in_place(input_tys);
                self.substitute_in_types_in_place(output_tys);
                self.substitute_in_effect_types_in_place(output_effs);
            }
        }
    }

    pub(super) fn substitute_in_constraints(
        &mut self,
        constraints: &[PubTypeConstraint],
    ) -> Vec<PubTypeConstraint> {
        let mut constraints = constraints.to_vec();
        self.substitute_in_constraints_in_place(&mut constraints);
        constraints
    }

    pub(super) fn substitute_in_constraints_in_place(
        &mut self,
        constraints: &mut [PubTypeConstraint],
    ) {
        for constraint in constraints {
            self.substitute_in_constraint_in_place(constraint);
        }
    }

    pub fn log_debug_constraints(&self, module_env: ModuleEnv) {
        if self.remaining_ty_constraints.is_empty() {
            log::debug!("No type constraints after unification.");
        } else {
            log::debug!("Type constraints after unification:");
            if !self.remaining_ty_constraints.is_empty() {
                for constraint in &self.remaining_ty_constraints {
                    log::debug!("  {}", constraint.format_with(&module_env));
                }
            }
        }
    }

    pub fn log_debug_substitution_tables(&mut self, module_env: ModuleEnv) {
        log::debug!("Type substitution table:");
        for i in 0..self.ty_unification_table.len() {
            let var = TypeVar::new(i as u32);
            let value = self.ty_unification_table.probe_value(var);
            match value {
                Some(value) => log::debug!("  {var} → {}", value.format_with(&module_env)),
                None => log::debug!("  {var} → {} (unbound)", {
                    self.ty_unification_table.find(var)
                }),
            }
        }
        log::debug!("Mutability substitution table:");
        for i in 0..self.mut_unification_table.len() {
            let var = MutVar::new(i as u32);
            let value = self.mut_unification_table.probe_value(var);
            match value {
                Some(value) => log::debug!("  {var} → {value}"),
                None => log::debug!("  {var} → {} (unbound)", {
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
    fn substitute_effect_type_inner(
        &mut self,
        eff_ty: &EffType,
        visiting: &mut FxHashSet<EffectVar>,
    ) -> EffType {
        use Effect::*;

        if eff_ty.is_empty() || !eff_ty.has_variables() {
            return eff_ty.clone();
        }

        if let Some(Variable(var)) = eff_ty.as_single() {
            return self.substitute_effect_var(var, visiting);
        }

        let mut effects = EffType::multiple_primitive(&eff_ty.inner_non_vars());
        for var in eff_ty.inner_vars() {
            effects.extend(&self.substitute_effect_var(var, visiting));
        }
        effects
    }

    fn substitute_effect_var(
        &mut self,
        var: EffectVar,
        visiting: &mut FxHashSet<EffectVar>,
    ) -> EffType {
        use Effect::*;

        let root = self.ty_inf.effects.effect_var_root(var);
        if let Some(cached) = self.effect_cache.get(&root) {
            return cached.clone();
        }
        if !visiting.insert(root) {
            return EffType::single_variable(root);
        }

        let mut effects = match self.ty_inf.effects.effect_var_value(root) {
            Some(value) => self.substitute_effect_type_inner(&value, visiting),
            None => EffType::single_variable(root),
        };

        // When an effect variable has accumulated concrete lower bounds, keep
        // the canonical variable in the substituted effect so later callers can
        // still add more bounds to the same polymorphic effect.
        if !effects.is_only_vars() {
            effects.insert(Variable(root));
        }

        visiting.remove(&root);
        self.effect_cache.insert(root, effects.clone());
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
        self.substitute_effect_type_inner(eff_ty, &mut FxHashSet::default())
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
    use crate::{
        parser::location::Location,
        types::effects::{EffType, Effect, PrimitiveEffect},
    };

    use super::UnifiedTypeInference;

    #[test]
    fn recursive_effect_substitution_reaches_a_fixed_point() {
        let mut unified = UnifiedTypeInference::default();
        let var = unified.fresh_effect_var();
        let span = Location::new_synthesized();
        let recursive_effect =
            EffType::single_primitive(PrimitiveEffect::Read).union(&EffType::single_variable(var));

        unified
            .unify_same_effect(
                EffType::single_variable(var),
                span,
                recursive_effect.clone(),
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
                EffType::single_variable(first),
                span,
                EffType::single_primitive(PrimitiveEffect::Read)
                    .union(&EffType::single_variable(second)),
                span,
            )
            .unwrap();
        unified
            .unify_same_effect(
                EffType::single_variable(second),
                span,
                EffType::single_variable(first),
                span,
            )
            .unwrap();

        let substituted = unified.substitute_in_effect_type(&EffType::single_variable(first));
        let root = unified.effects.effect_var_root(first);
        assert!(substituted.contains(Effect::Primitive(PrimitiveEffect::Read)));
        assert!(substituted.contains(Effect::Variable(root)));
    }
}
