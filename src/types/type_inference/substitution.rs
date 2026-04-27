use std::{cell::RefCell, mem};

use crate::{
    FxHashSet,
    format::FormatWith,
    hir::dictionary_passing::DictionaryReq,
    hir::{self, FnInstData},
    module::{ModuleEnv, ModuleFunction},
    types::{
        effects::{EffType, Effect, EffectVar, EffectsSubstitution},
        mutability::{MutType, MutVar},
        r#type::{FnType, Type, TypeKind, TypeSubstitution, TypeVar},
        type_scheme::PubTypeConstraint,
        type_substitution::{
            TypeSubstituer, substitute_fn_type, substitute_type, substitute_types,
        },
    },
};

use super::unify::UnifiedTypeInference;

pub type InstSubstitution = (TypeSubstitution, EffectsSubstitution);

impl UnifiedTypeInference {
    /// Substitute the remaining constraints using the current unification tables,
    /// storing the normalized constraints back into self.
    pub fn normalize_remaining_constraints(&mut self) {
        let constraints = mem::take(&mut self.remaining_ty_constraints);
        self.remaining_ty_constraints = self.substitute_in_constraints(&constraints);
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

    pub(super) fn normalize_mut_type(&mut self, mut_ty: MutType) -> MutType {
        NormalizeTypes(self).substitute_mut_type(mut_ty)
    }

    pub fn substitute_in_module_function(
        &mut self,
        descr: &mut ModuleFunction,
        arena: &mut crate::hir::NodeArena,
    ) {
        descr.definition.ty_scheme.ty = self.substitute_in_fn_type(&descr.definition.ty_scheme.ty);
        descr.definition.ty_scheme.constraints =
            self.substitute_in_constraints(&descr.definition.ty_scheme.constraints);
        if let Some(root) = descr.get_code_entry() {
            self.substitute_in_node(arena, root);
        }
        for local in &mut descr.locals {
            local.ty = self.substitute_in_type(local.ty);
            local.mut_ty = self.substitute_in_mut_type(local.mut_ty);
        }
    }

    pub fn substitute_in_type(&mut self, ty: Type) -> Type {
        substitute_type(ty, &mut SubstituteTypes(self))
    }

    pub fn substitute_in_types(&mut self, tys: &[Type]) -> Vec<Type> {
        substitute_types(tys, &mut SubstituteTypes(self))
    }

    pub fn substitute_in_fn_type(&mut self, fn_ty: &FnType) -> FnType {
        substitute_fn_type(fn_ty, &mut SubstituteTypes(self))
    }

    pub fn substitute_in_mut_type(&mut self, mut_ty: MutType) -> MutType {
        SubstituteTypes(self).substitute_mut_type(mut_ty)
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

    fn resolve_effect_var(&mut self, var: EffectVar) -> EffType {
        match self.effect_unification_table.probe_value(var) {
            Some(effects) => SubstituteTypes(self).substitute_effect_type(&effects),
            None => EffType::single_variable(self.effect_unification_table.find(var)),
        }
    }

    pub fn substitute_in_node(&mut self, arena: &mut hir::NodeArena, id: hir::NodeId) {
        let children = arena[id].kind.child_node_ids();
        for child in children {
            self.substitute_in_node(arena, child);
        }
        let node = &mut arena[id];
        node.ty = self.substitute_in_type(node.ty);
        node.effects = SubstituteTypes(self).substitute_effect_type(&node.effects);
        use hir::NodeKind::*;
        match &mut arena[id].kind {
            StaticApply(app) => {
                app.ty = self.substitute_in_fn_type(&app.ty);
                self.substitute_in_fn_inst_data(&mut app.inst_data);
            }
            TraitFnApply(app) => {
                app.ty = self.substitute_in_fn_type(&app.ty);
                app.input_tys = self.substitute_in_types(&app.input_tys);
                self.substitute_in_fn_inst_data(&mut app.inst_data);
            }
            GetFunction(get_fn) => {
                self.substitute_in_fn_inst_data(&mut get_fn.inst_data);
            }
            GetTraitFunction(get_fn) => {
                get_fn.input_tys = self.substitute_in_types(&get_fn.input_tys);
                get_fn.output_tys = self.substitute_in_types(&get_fn.output_tys);
                self.substitute_in_fn_inst_data(&mut get_fn.inst_data);
            }
            _ => {}
        }
    }

    fn substitute_in_fn_inst_data(&mut self, inst_data: &mut FnInstData) {
        use DictionaryReq::*;
        inst_data.dicts_req = inst_data
            .dicts_req
            .iter()
            .map(|dict| match dict {
                FieldIndex { ty, field } => FieldIndex {
                    ty: self.substitute_in_type(*ty),
                    field: *field,
                },
                TraitImpl {
                    trait_ref,
                    input_tys,
                    output_tys,
                } => TraitImpl {
                    trait_ref: trait_ref.clone(),
                    input_tys: self.substitute_in_types(input_tys),
                    output_tys: self.substitute_in_types(output_tys),
                },
            })
            .collect();
    }

    pub fn substitute_in_constraint(
        &mut self,
        constraint: &PubTypeConstraint,
    ) -> PubTypeConstraint {
        use PubTypeConstraint::*;
        match constraint {
            TupleAtIndexIs {
                tuple_ty,
                tuple_span,
                index,
                index_span,
                element_ty,
            } => {
                let tuple_ty = self.substitute_in_type(*tuple_ty);
                let element_ty = self.substitute_in_type(*element_ty);
                TupleAtIndexIs {
                    tuple_ty,
                    tuple_span: tuple_span.clone(),
                    index: *index,
                    index_span: index_span.clone(),
                    element_ty,
                }
            }
            RecordFieldIs {
                record_ty,
                record_span,
                field,
                field_span,
                element_ty,
            } => {
                let record_ty = self.substitute_in_type(*record_ty);
                let element_ty = self.substitute_in_type(*element_ty);
                RecordFieldIs {
                    record_ty,
                    record_span: record_span.clone(),
                    field: *field,
                    field_span: field_span.clone(),
                    element_ty,
                }
            }
            TypeHasVariant {
                variant_ty,
                variant_span,
                tag,
                payload_ty,
                payload_span,
            } => {
                let variant_ty = self.substitute_in_type(*variant_ty);
                let payload_ty = self.substitute_in_type(*payload_ty);
                TypeHasVariant {
                    variant_ty,
                    variant_span: variant_span.clone(),
                    tag: *tag,
                    payload_ty,
                    payload_span: payload_span.clone(),
                }
            }
            HaveTrait {
                trait_ref,
                input_tys,
                output_tys,
                span,
            } => {
                let input_tys = self.substitute_in_types(input_tys);
                let output_tys = self.substitute_in_types(output_tys);
                HaveTrait {
                    trait_ref: trait_ref.clone(),
                    input_tys,
                    output_tys,
                    span: span.clone(),
                }
            }
        }
    }

    pub(super) fn substitute_in_constraints(
        &mut self,
        constraints: &[PubTypeConstraint],
    ) -> Vec<PubTypeConstraint> {
        constraints
            .iter()
            .map(|c| self.substitute_in_constraint(c))
            .collect()
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
        self.log_debug_effect_constraints();
    }

    fn log_debug_effect_constraints(&mut self) {
        log::debug!("Effect substitution table:");
        for i in 0..self.effect_unification_table.len() {
            let var = EffectVar::new(i as u32);
            let value = self.effect_unification_table.probe_value(var);
            match value {
                Some(value) => log::debug!("  {var} → {value}"),
                None => log::debug!("  {var} → {} (unbound)", {
                    self.effect_unification_table.find(var)
                }),
            }
        }
        if !self.effect_constraints_inv.is_empty() {
            log::debug!("Inverted effect constraints:");
            for dep in &self.effect_constraints_inv {
                log::debug!("  {} → {}", dep.source, dep.target);
            }
        }
    }
}

struct SubstituteTypes<'a>(&'a mut UnifiedTypeInference);
impl TypeSubstituer for SubstituteTypes<'_> {
    fn substitute_type(&mut self, ty: Type) -> Type {
        self.0.substitute_type_lookup(ty)
    }

    fn substitute_mut_type(&mut self, mut_ty: MutType) -> MutType {
        self.0.substitute_mut_lookup(mut_ty, false)
    }

    /// Substitute the effect type by flattening the effect variables.
    fn substitute_effect_type(&mut self, eff_ty: &EffType) -> EffType {
        use Effect::*;

        // Thread-local hash-map for cycle detection
        thread_local! {
            static VAR_VISITED: RefCell<FxHashSet<EffectVar>> = RefCell::new(FxHashSet::default());
        }

        EffType::from_iter(eff_ty.iter().flat_map(|eff| {
            EffType::into_iter(match eff {
                Primitive(effect) => EffType::single_primitive(*effect),
                Variable(var) => {
                    let cycle_detected = VAR_VISITED.with(|visited| {
                        let mut visited = visited.borrow_mut();
                        if visited.contains(var) {
                            true // Cycle detected
                        } else {
                            visited.insert(*var);
                            false
                        }
                    });

                    if cycle_detected {
                        return EffType::empty().into_iter();
                    }

                    let mut effects = self.0.resolve_effect_var(*var);

                    // add back the variable itself if not only variables
                    if !effects.is_only_vars() {
                        effects = effects.union(&EffType::single_variable(*var));
                    }

                    VAR_VISITED.with(|visited| {
                        visited.borrow_mut().remove(var);
                    });

                    effects
                }
            } as EffType)
        }))
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
}
