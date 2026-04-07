// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use rustc_hash::FxHashSet;

use crate::{
    FxHashMap, Location,
    effects::EffectsSubstitution,
    r#type::{NamedType, Type, TypeKind},
    type_like::TypeLike,
    type_scheme::PubTypeConstraint,
};

struct NamedTypeConstraintCollector {
    use_site: Location,
    seen_tys: FxHashSet<Type>,
    seen_constraints: FxHashSet<PubTypeConstraint>,
    constraints: Vec<PubTypeConstraint>,
}

impl NamedTypeConstraintCollector {
    fn new(use_site: Location) -> Self {
        Self {
            use_site,
            seen_tys: FxHashSet::default(),
            seen_constraints: FxHashSet::default(),
            constraints: Vec::new(),
        }
    }

    fn collect_type(&mut self, ty: Type) {
        if !self.seen_tys.insert(ty) {
            return;
        }

        let ty_data = ty.data().clone();
        match ty_data {
            TypeKind::Native(native_ty) => {
                for arg in native_ty.arguments {
                    self.collect_type(arg);
                }
            }
            TypeKind::Variant(types) => {
                for (_, payload_ty) in types {
                    self.collect_type(payload_ty);
                }
            }
            TypeKind::Tuple(types) => {
                for item_ty in types {
                    self.collect_type(item_ty);
                }
            }
            TypeKind::Record(fields) => {
                for (_, field_ty) in fields {
                    self.collect_type(field_ty);
                }
            }
            TypeKind::Function(fn_ty) => {
                for arg in fn_ty.args {
                    self.collect_type(arg.ty);
                }
                self.collect_type(fn_ty.ret);
            }
            TypeKind::Named(named_ty) => self.collect_named_type(&named_ty),
            TypeKind::Variable(_) | TypeKind::Never => {}
        }
    }

    fn collect_named_type(&mut self, named: &NamedType) {
        let ty_subst = named
            .def
            .shape
            .ty_quantifiers
            .iter()
            .copied()
            .zip(named.params.iter().copied())
            .collect::<FxHashMap<_, _>>();
        let subst = (ty_subst, EffectsSubstitution::default());
        for constraint in &named.def.shape.constraints {
            let mut constraint = constraint.instantiate(&subst);
            constraint.instantiate_location(self.use_site);
            if self.seen_constraints.insert(constraint.clone()) {
                self.constraints.push(constraint);
            }
        }
        for &param in &named.params {
            self.collect_type(param);
        }
    }

    fn finish(self) -> Vec<PubTypeConstraint> {
        self.constraints
    }
}

pub(crate) fn named_type_constraints_in_types(
    tys: impl IntoIterator<Item = Type>,
    use_site: Location,
) -> Vec<PubTypeConstraint> {
    let mut collector = NamedTypeConstraintCollector::new(use_site);
    for ty in tys {
        collector.collect_type(ty);
    }
    collector.finish()
}
