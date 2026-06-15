// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
use std::fmt::{self, Debug};

use crate::{FxHashMap, FxHashSet, define_id_type};

use dyn_clone::DynClone;
use itertools::Itertools;
use ustr::Ustr;
use ustr::ustr;

use crate::{
    Location,
    compiler::error::{
        InternalCompilationError, InvalidTraitDefinitionKind, UnsupportedTraitDefinitionKind,
    },
    format::{FormatWith, write_with_separator_and_format_fn},
    hir::function::FunctionDefinition,
    module::{ModuleEnv, TraitId, TraitImplId, id::Id},
    types::effects::{EffType, EffectVar, EffectsInstSubst},
    types::trait_solver::TraitSolver,
    types::r#type::{Type, TypeInstSubst, TypeVar},
    types::type_inference::substitution::InstSubst,
    types::type_like::TypeLike,
    types::type_mapper::BitmapInstantiationMapper,
    types::type_scheme::PubTypeConstraint,
    types::type_scheme_display::{
        TypeConstraintRenderStyle, format_pub_type_constraint_with_style,
    },
    types::type_visitor::TyVarsCollector,
};

/// Help deriving implementations of traits.
pub trait Deriver: Debug + DynClone + Sync + Send {
    /// Derive an implementation of a trait for the given input types, if possible.
    fn derive_impl(
        &self,
        trait_id: TraitId,
        input_types: &[Type],
        span: Location,
        arena: &mut crate::hir::NodeArena,
        solver: &mut TraitSolver,
    ) -> Result<Option<TraitImplId>, InternalCompilationError>;
}

dyn_clone::clone_trait_object!(Deriver);

/// A trait method argument span, storing the spans of the argument name and its type.
pub type TraitMethodArgSpan = (Location, Location);

define_id_type!(
    /// Index into a trait's method list.
    TraitMethodIndex
);

define_id_type!(
    /// Index into a trait's associated const list.
    TraitAssociatedConstIndex
);

define_id_type!(
    /// Index into a runtime trait dictionary tuple.
    TraitDictionaryEntryIndex
);

/// If the trait method is from code, this struct contains the spans of the method.
#[derive(Debug, Clone)]
pub struct TraitMethodSpans {
    pub name: Location,
    pub args: Vec<TraitMethodArgSpan>,
    pub ret_ty: Option<Location>,
    pub span: Location,
}

/// If the trait is from code, this struct contains the spans of the trait definition.
#[derive(Debug, Clone)]
pub struct TraitSpans {
    pub name: Location,
    pub input_type_names: Vec<Location>,
    pub output_type_names: Vec<Location>,
    pub output_effect_names: Vec<Location>,
    pub parent_constraints: Vec<Location>,
    pub constraints: Vec<Location>,
    pub methods: Vec<TraitMethodSpans>,
    pub span: Location,
}

/// An associated const declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TraitAssociatedConst {
    pub name: Ustr,
    pub ty: Type,
    pub doc: Option<String>,
}

impl TraitAssociatedConst {
    pub fn new(name: &str, ty: Type, doc: &str) -> Self {
        Self {
            name: ustr(name),
            ty,
            doc: (!doc.is_empty()).then(|| doc.to_string()),
        }
    }
}

/// A trait, equivalent to a multi-parameter type class in Haskell, with output types.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TraitImplPolicy {
    UserImplementable,
    NativeOnly,
}

#[derive(Debug, Clone)]
pub struct Trait {
    /// Name of the trait, for debugging purposes.
    pub name: Ustr,
    /// Optional documentation for the trait.
    pub doc: Option<String>,
    /// Number of input types, by convention, the first type variables correspond to input types.
    pub input_type_names: Vec<Ustr>,
    /// Name of the output types.
    /// By convention, the type variables just after input types correspond to output types.
    pub output_type_names: Vec<Ustr>,
    /// Name of the output effects, determined by the input types like output types.
    /// By convention, the first effect variables correspond to output effects.
    pub output_effect_names: Vec<Ustr>,
    /// Trait constraints required to implement this trait.
    pub parent_constraints: Vec<PubTypeConstraint>,
    /// The constraints on the trait, for example related to the associated types.
    pub constraints: Vec<PubTypeConstraint>,
    /// The methods provided by the trait.
    pub methods: Vec<(Ustr, FunctionDefinition)>,
    /// Compiler-defined associated consts provided by implementations.
    pub associated_consts: Vec<TraitAssociatedConst>,
    /// The trait derivers
    pub derivers: Vec<Box<dyn Deriver>>,
    /// Whether Ferlium source code is allowed to implement this trait.
    pub impl_policy: TraitImplPolicy,
    /// If the trait is from code, this contains the source spans of the definition.
    pub spans: Option<TraitSpans>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TraitValidationError {
    Invalid {
        trait_name: Ustr,
        kind: InvalidTraitDefinitionKind,
    },
    Unsupported {
        trait_name: Ustr,
        kind: UnsupportedTraitDefinitionKind,
    },
}

impl TraitValidationError {
    pub fn message(&self) -> String {
        match self {
            Self::Invalid { trait_name, kind } => kind.message(*trait_name),
            Self::Unsupported { trait_name, kind } => kind.message(*trait_name),
        }
    }
}

impl Trait {
    pub fn from_trait_data(trait_data: Trait) -> Result<Self, TraitValidationError> {
        if trait_data.input_type_names.is_empty() {
            return Err(TraitValidationError::Invalid {
                trait_name: trait_data.name,
                kind: InvalidTraitDefinitionKind::MissingInputTypes,
            });
        }
        trait_data.try_validate()?;
        Ok(trait_data)
    }

    pub fn new<'a>(
        name: &str,
        doc: &str,
        input_type_names: impl Into<Vec<&'a str>>,
        output_type_names: impl Into<Vec<&'a str>>,
        methods: impl Into<Vec<(&'a str, FunctionDefinition)>>,
    ) -> Self {
        let input_type_names = input_type_names.into();
        assert!(
            !input_type_names.is_empty(),
            "A trait must have at least one input type."
        );
        let methods = methods
            .into()
            .into_iter()
            .map(|(name, def)| (ustr(name), def))
            .collect();
        let trait_data = Trait {
            name: ustr(name),
            doc: Some(doc.to_string()),
            input_type_names: input_type_names.into_iter().map(ustr).collect(),
            output_type_names: output_type_names.into().into_iter().map(ustr).collect(),
            output_effect_names: Vec::new(),
            parent_constraints: Vec::new(),
            constraints: Vec::new(),
            methods,
            associated_consts: Vec::new(),
            derivers: Vec::new(),
            impl_policy: TraitImplPolicy::UserImplementable,
            spans: None,
        };
        Self::from_trait_data(trait_data).unwrap()
    }

    /// Add output effect slots to this trait, re-validating the methods against them.
    pub fn with_output_effects<'a>(mut self, output_effect_names: impl Into<Vec<&'a str>>) -> Self {
        self.output_effect_names = output_effect_names.into().into_iter().map(ustr).collect();
        self.validate();
        self
    }

    pub fn new_with_self_input_type<'a>(
        name: &str,
        doc: &str,
        output_type_names: impl Into<Vec<&'a str>>,
        methods: impl Into<Vec<(&'a str, FunctionDefinition)>>,
    ) -> Self {
        Self::new(name, doc, ["Self"], output_type_names, methods)
    }

    pub fn new_with_constraints<'a>(
        name: &str,
        doc: &str,
        input_type_names: impl Into<Vec<&'a str>>,
        output_type_names: impl Into<Vec<&'a str>>,
        constraints: impl Into<Vec<PubTypeConstraint>>,
        methods: impl Into<Vec<(&'a str, FunctionDefinition)>>,
    ) -> Self {
        let input_type_names = input_type_names.into();
        assert!(
            !input_type_names.is_empty(),
            "A trait must have at least one input type."
        );
        let methods = methods
            .into()
            .into_iter()
            .map(|(name, def)| (ustr(name), def))
            .collect();
        let trait_data = Trait {
            name: ustr(name),
            doc: Some(doc.to_string()),
            input_type_names: input_type_names.into_iter().map(ustr).collect(),
            output_type_names: output_type_names.into().into_iter().map(ustr).collect(),
            output_effect_names: Vec::new(),
            parent_constraints: Vec::new(),
            constraints: constraints.into(),
            methods,
            associated_consts: Vec::new(),
            derivers: Vec::new(),
            impl_policy: TraitImplPolicy::UserImplementable,
            spans: None,
        };
        Self::from_trait_data(trait_data).unwrap()
    }

    pub fn with_associated_consts(
        mut self,
        associated_consts: impl Into<Vec<TraitAssociatedConst>>,
    ) -> Self {
        self.associated_consts = associated_consts.into();
        self.validate();
        self
    }

    pub fn with_native_impl_only(mut self) -> Self {
        self.impl_policy = TraitImplPolicy::NativeOnly;
        self
    }

    pub fn with_deriver(mut self, deriver: impl Deriver + 'static) -> Self {
        self.derivers.push(Box::new(deriver));
        self
    }

    pub fn with_derivers(mut self, derivers: Vec<Box<dyn Deriver + 'static>>) -> Self {
        self.derivers = derivers;
        self
    }

    /// Return the number of input types in this trait.
    pub fn input_type_count(&self) -> u32 {
        self.input_type_names.len() as u32
    }
    /// Return the number of output types in this trait.
    pub fn output_type_count(&self) -> u32 {
        self.output_type_names.len() as u32
    }

    /// Return the number of type variables in this trait.
    pub fn type_var_count(&self) -> u32 {
        self.input_type_count() + self.output_type_count()
    }

    /// Return the number of output effects in this trait.
    pub fn output_effect_count(&self) -> u32 {
        self.output_effect_names.len() as u32
    }

    /// Return impl output effects, defaulting omitted slots to empty effects.
    /// Panics if a non-empty list of the wrong length is given.
    pub fn impl_output_effs_or_pure_defaults(&self, output_effs: Vec<EffType>) -> Vec<EffType> {
        if output_effs.is_empty() {
            vec![EffType::empty(); self.output_effect_count() as usize]
        } else {
            assert_eq!(
                output_effs.len(),
                self.output_effect_count() as usize,
                "Mismatched output effect count when implementing trait {}.",
                self.name,
            );
            output_effs
        }
    }

    /// Return the number of methods in this trait.
    pub fn method_count(&self) -> usize {
        self.methods.len()
    }

    /// Return the number of associated consts in this trait.
    pub fn associated_const_count(&self) -> usize {
        self.associated_consts.len()
    }

    /// Return the number of runtime dictionary entries for this trait.
    pub fn runtime_dictionary_entry_count(&self) -> usize {
        self.method_count() + self.associated_const_count()
    }

    /// Return whether this trait needs a runtime dictionary.
    pub fn has_runtime_dictionary_entries(&self) -> bool {
        self.runtime_dictionary_entry_count() > 0
    }

    /// Return the runtime dictionary index for a method.
    pub fn dictionary_method_index(
        &self,
        method_index: TraitMethodIndex,
    ) -> TraitDictionaryEntryIndex {
        assert!(method_index.as_index() < self.method_count());
        TraitDictionaryEntryIndex::from_index(method_index.as_index())
    }

    /// Return the runtime dictionary index for an associated const.
    pub fn dictionary_associated_const_index(
        &self,
        associated_const_index: TraitAssociatedConstIndex,
    ) -> TraitDictionaryEntryIndex {
        assert!(associated_const_index.as_index() < self.associated_const_count());
        TraitDictionaryEntryIndex::from_index(
            self.method_count() + associated_const_index.as_index(),
        )
    }

    /// Return the index of the associated const with the given name, if it exists.
    pub fn associated_const_index(&self, name: Ustr) -> Option<TraitAssociatedConstIndex> {
        self.associated_consts
            .iter()
            .position(|associated_const| associated_const.name == name)
            .map(TraitAssociatedConstIndex::from_index)
    }

    /// Return the index of the method with the given name, if it exists.
    pub fn method_index(&self, name: Ustr) -> Option<TraitMethodIndex> {
        self.methods
            .iter()
            .position(|(fn_name, _)| *fn_name == name)
            .map(TraitMethodIndex::from_index)
    }

    /// Return the method at the given trait method index.
    pub fn method(&self, index: TraitMethodIndex) -> &(Ustr, FunctionDefinition) {
        &self.methods[index.as_index()]
    }

    /// Return the associated const at the given trait associated const index.
    pub fn associated_const(&self, index: TraitAssociatedConstIndex) -> &TraitAssociatedConst {
        &self.associated_consts[index.as_index()]
    }

    /// Return the qualified method name for the given method index, e.g., "TraitName<…>::method_name"
    /// using the interned indices of the provided types.
    pub fn qualified_method_name(&self, index: TraitMethodIndex, input_tys: &[Type]) -> String {
        let mut s = format!("{}<", self.name);
        for (i, ty) in input_tys.iter().enumerate() {
            if i > 0 {
                s.push_str(", ");
            }
            if let Some(world) = ty.world() {
                s.push_str(format!("{}-", world).as_str());
            }
            s.push_str(format!("{}", ty.index()).as_str());
        }
        s.push_str(&format!(">::{}", self.method(index).0));
        s
    }

    /// Validate the trait, ensuring that its method signatures adhere to the limitations of the current implementation.
    pub fn validate(&self) {
        self.try_validate()
            .unwrap_or_else(|error| panic!("{}", error.message()));
    }

    /// Validate the trait and return a descriptive error instead of panicking.
    pub fn try_validate(&self) -> Result<(), TraitValidationError> {
        // Make sure that parent constraints only refer to the input or the output type variables.
        let trait_type_count = self.type_var_count();
        for constraint in &self.parent_constraints {
            for ty_var in constraint.inner_ty_vars() {
                if ty_var.name() >= trait_type_count {
                    return Err(TraitValidationError::Invalid {
                        trait_name: self.name,
                        kind: InvalidTraitDefinitionKind::InvalidConstraintTypeVar { ty_var },
                    });
                }
            }
        }

        // Make sure that constraints only refer to the input or the output type variables.
        for constraint in &self.constraints {
            for ty_var in constraint.inner_ty_vars() {
                if ty_var.name() >= trait_type_count {
                    return Err(TraitValidationError::Invalid {
                        trait_name: self.name,
                        kind: InvalidTraitDefinitionKind::InvalidConstraintTypeVar { ty_var },
                    });
                }
            }
        }

        // Make sure that associated const types only refer to the input or output type variables.
        for associated_const in &self.associated_consts {
            for ty_var in associated_const.ty.inner_ty_vars() {
                if ty_var.name() >= trait_type_count {
                    return Err(TraitValidationError::Invalid {
                        trait_name: self.name,
                        kind: InvalidTraitDefinitionKind::InvalidConstraintTypeVar { ty_var },
                    });
                }
            }
        }

        // Collect the effect variables that methods are allowed to mention:
        // the trait's output effect slots plus the effect variables bound as
        // outputs of the trait's constraints.
        let mut allowed_effect_vars: FxHashSet<EffectVar> = (0..self.output_effect_count())
            .map(EffectVar::new)
            .collect();
        for constraint in &self.constraints {
            if let Some((_, _, _, output_effs, _)) = constraint.as_have_trait() {
                for eff in output_effs {
                    eff.fill_with_inner_effect_vars(&mut allowed_effect_vars);
                }
            }
        }

        // Make sure that all method definitions are valid and refer to the correct type variables.
        for (name, method) in &self.methods {
            for quantifier in &method.ty_scheme.ty_quantifiers {
                if quantifier.name() >= trait_type_count {
                    return Err(TraitValidationError::Unsupported {
                        trait_name: self.name,
                        kind: UnsupportedTraitDefinitionKind::GenericMethod {
                            method_name: *name,
                            quantifier: *quantifier,
                        },
                    });
                }
            }
            let foreign_effect_vars: Vec<_> = method
                .ty_scheme
                .eff_quantifiers
                .iter()
                .filter(|eff_var| !allowed_effect_vars.contains(eff_var))
                .copied()
                .sorted()
                .collect();
            if !foreign_effect_vars.is_empty() {
                return Err(TraitValidationError::Unsupported {
                    trait_name: self.name,
                    kind: UnsupportedTraitDefinitionKind::GenericEffect {
                        method_name: *name,
                        effect_vars: foreign_effect_vars,
                    },
                });
            }
            if !method.ty_scheme.constraints.is_empty() {
                return Err(TraitValidationError::Unsupported {
                    trait_name: self.name,
                    kind: UnsupportedTraitDefinitionKind::GenericConstraints {
                        method_name: *name,
                        constraint_count: method.ty_scheme.constraints.len(),
                    },
                });
            }
            for input_ty_var in 0..self.input_type_count() {
                let ty_var = TypeVar::new(input_ty_var);
                if !method.ty_scheme.ty_quantifiers.contains(&ty_var) {
                    return Err(TraitValidationError::Invalid {
                        trait_name: self.name,
                        kind: InvalidTraitDefinitionKind::MissingInputTypeVarInMethod {
                            method_name: *name,
                            ty_var,
                        },
                    });
                }
            }
            // Make sure that all constraints have their input type variables reachable from
            // the method type, in a single pass.
            // The single pass is important because in TraitImpls::get_impl()
            // we assume that we can get all output type variables in a single pass over the constraints.
            let mut quantifiers: FxHashSet<_> =
                method.ty_scheme.ty_quantifiers.iter().copied().collect();
            for (i, constraint) in self.constraints.iter().enumerate() {
                let (_, input_tys, output_tys, _, _) = constraint
                    .as_have_trait()
                    .expect("Only HaveTrait constraints are supported in traits.");
                if !input_tys
                    .iter()
                    .flat_map(TypeLike::inner_ty_vars)
                    .all(|ty_var| quantifiers.contains(&ty_var))
                {
                    return Err(TraitValidationError::Invalid {
                        trait_name: self.name,
                        kind: InvalidTraitDefinitionKind::UnreachableConstraintInputTypeVar {
                            method_name: *name,
                            constraint_index: i,
                        },
                    });
                }
                let mut additional_ty_vars = FxHashSet::default();
                let mut collector = TyVarsCollector(&mut additional_ty_vars);
                output_tys.iter().for_each(|ty| ty.visit(&mut collector));
                quantifiers.extend(additional_ty_vars);
            }
        }
        Ok(())
    }

    /// Instantiate all method definitions of this trait for the given input and output types and output effects.
    pub fn instantiate_for_tys(
        &self,
        input_tys: &[Type],
        output_tys: &[Type],
        output_effs: &[EffType],
    ) -> Vec<FunctionDefinition> {
        let inst_subst = self.param_subst_for(input_tys, output_tys, output_effs);
        let mut mapper = BitmapInstantiationMapper::new(&inst_subst);
        self.methods
            .iter()
            .map(|(_, def)| FunctionDefinition {
                ty_scheme: def.ty_scheme.map_simplified(&mut mapper),
                generic_params: def.generic_params.clone(),
                arg_names: def.arg_names.clone(),
                doc: def.doc.clone(),
                attributes: def.attributes.clone(),
            })
            .collect::<Vec<_>>()
    }

    /// Instantiate all associated const types of this trait for the given input and output types.
    pub fn instantiate_associated_const_tys_for_tys(
        &self,
        input_tys: &[Type],
        output_tys: &[Type],
        output_effs: &[EffType],
    ) -> Vec<Type> {
        let inst_subst = self.param_subst_for(input_tys, output_tys, output_effs);
        let mut mapper = BitmapInstantiationMapper::new(&inst_subst);
        self.associated_consts
            .iter()
            .map(|associated_const| associated_const.ty.map(&mut mapper))
            .collect()
    }

    /// Get the type of the dictionary for this trait for the given input and output types.
    /// Only the types are substituted, the constraints are not considered.
    pub fn get_dictionary_type_for_tys(
        &self,
        input_tys: &[Type],
        output_tys: &[Type],
        output_effs: &[EffType],
    ) -> Type {
        let inst_subst = self.param_subst_for(input_tys, output_tys, output_effs);
        let mut mapper = BitmapInstantiationMapper::new(&inst_subst);
        let method_tys = self
            .methods
            .iter()
            .map(|(_, def)| Type::function_type(def.ty_scheme.ty.map(&mut mapper)))
            .collect::<Vec<_>>();
        let associated_const_tys = self
            .associated_consts
            .iter()
            .map(|associated_const| associated_const.ty.map(&mut mapper))
            .collect::<Vec<_>>();
        Type::tuple(
            method_tys
                .into_iter()
                .chain(associated_const_tys)
                .collect::<Vec<_>>(),
        )
    }

    /// Build the type-variable substitution for this trait applied to the given input and output types.
    pub fn type_param_subst_for_tys(
        &self,
        input_tys: &[Type],
        output_tys: &[Type],
    ) -> TypeInstSubst {
        debug_assert_eq!(input_tys.len(), self.input_type_count() as usize);
        debug_assert_eq!(output_tys.len(), self.output_type_count() as usize);
        input_tys
            .iter()
            .chain(output_tys.iter())
            .enumerate()
            .map(|(i, ty)| (TypeVar::new(i as u32), *ty))
            .collect::<FxHashMap<_, _>>()
    }

    /// Build the effect-variable substitution for this trait applied to the given output effects.
    pub fn effect_param_subst_for_effs(&self, output_effs: &[EffType]) -> EffectsInstSubst {
        debug_assert_eq!(output_effs.len(), self.output_effect_count() as usize);
        output_effs
            .iter()
            .enumerate()
            .map(|(i, eff)| (EffectVar::new(i as u32), eff.clone()))
            .collect::<FxHashMap<_, _>>()
    }

    /// Build the full instantiation substitution for this trait applied to the
    /// given input/output types and output effects.
    pub fn param_subst_for(
        &self,
        input_tys: &[Type],
        output_tys: &[Type],
        output_effs: &[EffType],
    ) -> InstSubst {
        (
            self.type_param_subst_for_tys(input_tys, output_tys),
            self.effect_param_subst_for_effs(output_effs),
        )
    }
}

impl FormatWith<ModuleEnv<'_>> for Trait {
    fn fmt_with(&self, f: &mut fmt::Formatter, env: &ModuleEnv) -> fmt::Result {
        if let Some(doc) = &self.doc {
            for line in doc.split("\n") {
                writeln!(f, "/// {line}")?;
            }
        }
        write!(f, "trait {} <", self.name)?;
        let input_ty_count = self.input_type_count();
        write_with_separator_and_format_fn(
            0..input_ty_count,
            ", ",
            |index, f| {
                write!(
                    f,
                    "{} = {}",
                    self.input_type_names[index as usize],
                    TypeVar::new(index)
                )
            },
            f,
        )?;
        if self.output_type_count() > 0 {
            write!(f, " ↦ ")?;
            write_with_separator_and_format_fn(
                0..self.output_type_count(),
                ", ",
                |index, f| {
                    write!(
                        f,
                        "{} = {}",
                        self.output_type_names[index as usize],
                        TypeVar::new(input_ty_count + index)
                    )
                },
                f,
            )?;
        }
        if self.output_effect_count() > 0 {
            write!(f, " ! ")?;
            write_with_separator_and_format_fn(
                0..self.output_effect_count(),
                ", ",
                |index, f| {
                    write!(
                        f,
                        "{} = {}",
                        self.output_effect_names[index as usize],
                        EffectVar::new(index)
                    )
                },
                f,
            )?;
        }
        if !self.parent_constraints.is_empty() {
            write!(f, ">: ")?;
            write_with_separator_and_format_fn(
                &self.parent_constraints,
                ", ",
                |constraint, f| {
                    format_pub_type_constraint_with_style(
                        constraint,
                        f,
                        env,
                        TypeConstraintRenderStyle::ParentList,
                    )
                },
                f,
            )?;
        } else {
            write!(f, ">")?;
        }
        if self.constraints.is_empty() {
            writeln!(f, " {{")?;
        } else {
            write!(f, "\nwhere")?;
            for constraint in &self.constraints {
                write!(f, "\n    ")?;
                constraint.fmt_with(f, env)?;
            }
            writeln!(f, "\n{{")?;
        }
        let mut first = true;
        for (name, def) in &self.methods {
            if first {
                first = false;
            } else {
                writeln!(f)?;
            }
            def.fmt_with_name_and_module_env(f, *name, "    ", env)?;
            write!(f, ";")?;
        }
        writeln!(f, "\n}}")?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        types::{
            effects::EffType,
            r#type::{FnType, Type},
        },
        ustr,
    };

    use super::*;

    #[test]
    fn construct_multi_parameter_trait() {
        let fn_ty = FnType::new_by_val(
            [
                Type::variable_id(0),
                Type::variable_id(1),
                Type::variable_id(2),
            ],
            Type::variable_id(3),
            EffType::empty(),
        );
        let trait_def = Trait::new(
            "Add",
            "Addition.",
            ["Lhs", "Rhs", "Output"],
            ["Result"],
            [(
                "add",
                FunctionDefinition::new_infer_quantifiers(
                    fn_ty,
                    ["lhs", "rhs", "output"],
                    "Add values.",
                ),
            )],
        );

        assert_eq!(trait_def.name, ustr("Add"));
        assert_eq!(trait_def.input_type_count(), 3);
        assert_eq!(trait_def.output_type_count(), 1);
        assert_eq!(
            trait_def.method_index(ustr("add")),
            Some(TraitMethodIndex(0))
        );
    }

    #[test]
    fn construct_trait_with_output_effect() {
        let fn_ty = FnType::new_by_val(
            [Type::variable_id(0)],
            Type::variable_id(1),
            EffType::single_variable_id(0),
        );
        let trait_def = Trait::new(
            "EffProject",
            "Projection with a trait-determined effect.",
            ["Self"],
            ["Output"],
            [(
                "project",
                FunctionDefinition::new_infer_quantifiers(fn_ty, ["value"], "Project a value."),
            )],
        )
        .with_output_effects(["E"]);

        assert_eq!(trait_def.output_effect_count(), 1);
        assert_eq!(trait_def.output_effect_names, vec![ustr("E")]);

        // Instantiating the trait substitutes the effect slot in the method signature.
        let read = EffType::single_primitive(crate::types::effects::PrimitiveEffect::Read);
        let defs = trait_def.instantiate_for_tys(
            &[Type::unit()],
            &[Type::unit()],
            std::slice::from_ref(&read),
        );
        assert_eq!(defs[0].ty_scheme.ty.effects, read);

        // An empty effect list pads to all-empty effects, a wrong length panics.
        assert_eq!(
            trait_def.impl_output_effs_or_pure_defaults(vec![]),
            vec![EffType::empty()]
        );
    }
}

impl Trait {
    pub fn validate_impl_size(&self, input_tys: &[Type], output_tys: &[Type], method_count: usize) {
        self.validate_impl_shape(input_tys, output_tys, &[], 0, method_count)
    }

    pub fn validate_impl_shape(
        &self,
        input_tys: &[Type],
        output_tys: &[Type],
        output_effs: &[EffType],
        associated_const_count: usize,
        method_count: usize,
    ) {
        assert_eq!(
            self.input_type_count(),
            input_tys.len() as u32,
            "Mismatched input type count when implementing trait {}.",
            self.name,
        );
        assert_eq!(
            self.output_type_count(),
            output_tys.len() as u32,
            "Mismatched output type count when implementing trait {}.",
            self.name,
        );
        assert_eq!(
            self.output_effect_count(),
            output_effs.len() as u32,
            "Mismatched output effect count when implementing trait {}.",
            self.name,
        );
        assert_eq!(
            self.associated_consts.len(),
            associated_const_count,
            "Mismatched associated const count when implementing trait {}.",
            self.name,
        );
        assert_eq!(
            self.methods.len(),
            method_count,
            "Mismatched method count when implementing trait {}.",
            self.name,
        );
    }

    /// Span of the trait definition, or synthesized if not available.
    pub fn trait_span(&self) -> Location {
        self.spans
            .as_ref()
            .map_or_else(Location::new_synthesized, |spans| spans.span)
    }
}
