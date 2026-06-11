// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//

use crate::{
    FxHashSet,
    types::{
        effects::EffType,
        mutability::MutType,
        r#type::{Type, TypeKind, TypeVar},
        type_like::TypeLike,
        type_substitution::{TypeSubstituer, substitute_type},
    },
};

/// The rule that an invalid recursive type equation failed to satisfy.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum RecursiveEquationError {
    /// An occurrence of the variable is not guarded by a variant payload.
    UnguardedCycle,
    /// Every variant payload on the cycle refers back to the variable.
    NoTerminatingPayload,
}

/// Validate and intern the recursive type equation `var = ty`, where `ty` is a
/// fully normalized type containing `var`.
///
/// The equation is accepted under the same rules as declared recursive types:
/// every occurrence of `var` must be guarded by a variant payload, and at least
/// one variant payload on the cycle must not refer back to `var`.
pub(crate) fn try_intern_recursive_equation(
    var: TypeVar,
    ty: Type,
) -> Result<Type, RecursiveEquationError> {
    let mut validation = Validation {
        var,
        visited: FxHashSet::default(),
        has_terminating_payload: false,
    };
    if !validation.validate(ty, false) {
        return Err(RecursiveEquationError::UnguardedCycle);
    }
    if !validation.has_terminating_payload {
        return Err(RecursiveEquationError::NoTerminatingPayload);
    }
    Ok(substitute_type(ty, &mut TieEquation { var, root: ty }))
}

/// Checks the declared-recursive-type rules on the `var`-containing region of the
/// type graph: occurrences of `var` must sit below a variant payload, and at least
/// one variant payload of the region must be free of `var` so the type terminates.
///
/// These rules mirror `validate_type_cycle` in `desugar/module.rs`, which enforces
/// them on the AST for declared recursive types; keep the two in sync.
struct Validation {
    var: TypeVar,
    /// Composite types already visited at a given guardedness; bounds the
    /// traversal when the region crosses existing recursive worlds.
    visited: FxHashSet<(Type, bool)>,
    has_terminating_payload: bool,
}

impl Validation {
    fn validate(&mut self, ty: Type, guarded: bool) -> bool {
        if !ty.contains_any_type_var(self.var) {
            return true;
        }
        let kind = { ty.data().clone() };
        if let TypeKind::Variable(_) = kind {
            // The summary check above ensures this variable is `var` itself.
            return guarded;
        }
        // A subtree validated unguarded also validates guarded, hence the
        // `(ty, false)` check subsumes both keys.
        if self.visited.contains(&(ty, false)) || !self.visited.insert((ty, guarded)) {
            return true;
        }
        use TypeKind::*;
        match kind {
            Variable(_) => unreachable!(),
            Native(native) => native
                .arguments
                .iter()
                .all(|arg| self.validate(*arg, guarded)),
            Variant(items) => items.iter().all(|(_, payload)| {
                if payload.contains_any_type_var(self.var) {
                    self.validate(*payload, true)
                } else {
                    self.has_terminating_payload = true;
                    true
                }
            }),
            Tuple(items) => items.iter().all(|item| self.validate(*item, guarded)),
            Record(fields) => fields
                .iter()
                .all(|(_, field)| self.validate(*field, guarded)),
            Function(fn_ty) => {
                fn_ty
                    .args
                    .iter()
                    .all(|arg| self.validate(arg.ty, guarded))
                    && self.validate(fn_ty.ret, guarded)
            }
            Named(named) => named
                .params
                .iter()
                .all(|param| self.validate(*param, guarded)),
            Never => true,
        }
    }
}

/// Rewrites occurrences of `var` to the equation root type. The substitution
/// driver visits the root first, so its shared `seen` map resolves the rewritten
/// occurrences to a local reference to the root, tying the recursive knot, and
/// its final `store_types` interns the region as a recursive SCC.
struct TieEquation {
    var: TypeVar,
    root: Type,
}

impl TypeSubstituer for TieEquation {
    fn substitute_type(&mut self, ty: Type) -> Type {
        if ty == Type::variable(self.var) {
            self.root
        } else {
            ty
        }
    }

    fn substitute_mut_type(&mut self, mut_ty: MutType) -> MutType {
        mut_ty
    }

    fn substitute_effect_type(&mut self, eff_ty: &EffType) -> EffType {
        eff_ty.clone()
    }

    fn affects_type(&mut self, ty: Type) -> bool {
        ty.contains_any_type_var(self.var)
    }
}

#[cfg(test)]
mod tests {
    use ustr::ustr;

    use crate::std::math::int_type as int;

    use super::*;

    #[test]
    fn guarded_variant_cycle_is_interned() {
        // v = Leaf(int) | Node((v, v))
        let var = TypeVar::new(1000);
        let ty = Type::variant(vec![
            (ustr("Leaf"), int()),
            (
                ustr("Node"),
                Type::tuple(vec![Type::variable(var), Type::variable(var)]),
            ),
        ]);
        let rec_ty = try_intern_recursive_equation(var, ty).unwrap();
        assert!(rec_ty.is_global_recursive());
        assert!(!rec_ty.contains_any_type_var(var));

        // The same equation built from the unfolded form interns to the same type.
        let unfolded = Type::variant(vec![
            (ustr("Leaf"), int()),
            (ustr("Node"), Type::tuple(vec![rec_ty, rec_ty])),
        ]);
        assert_eq!(unfolded, rec_ty);
    }

    #[test]
    fn non_variant_root_with_guarded_cycle_is_interned() {
        // v = (int, Leaf(int) | Node(v)): the root is a tuple, the cycle is
        // guarded by the Node payload and terminated by the Leaf payload.
        let var = TypeVar::new(1005);
        let ty = Type::tuple(vec![
            int(),
            Type::variant(vec![
                (ustr("Leaf"), int()),
                (ustr("Node"), Type::variable(var)),
            ]),
        ]);
        let rec_ty = try_intern_recursive_equation(var, ty).unwrap();
        assert!(rec_ty.is_global_recursive());
        assert!(!rec_ty.contains_any_type_var(var));
    }

    #[test]
    fn unguarded_cycle_is_rejected() {
        // v = (int, v)
        let var = TypeVar::new(1001);
        let ty = Type::tuple(vec![int(), Type::variable(var)]);
        assert_eq!(
            try_intern_recursive_equation(var, ty),
            Err(RecursiveEquationError::UnguardedCycle)
        );
    }

    #[test]
    fn sum_cycle_without_terminating_payload_is_rejected() {
        // v = A(v) | B(v)
        let var = TypeVar::new(1002);
        let ty = Type::variant(vec![
            (ustr("A"), Type::variable(var)),
            (ustr("B"), Type::variable(var)),
        ]);
        assert_eq!(
            try_intern_recursive_equation(var, ty),
            Err(RecursiveEquationError::NoTerminatingPayload)
        );
    }

    #[test]
    fn cycle_through_existing_recursive_world_is_interned() {
        // w = Nil | Cons((v, w)), then v = End(int) | Wrap(w): the second
        // equation's region crosses the world interned for the first one.
        let var_v = TypeVar::new(1003);
        let list_of_v = {
            let var_w = TypeVar::new(1004);
            let ty = Type::variant(vec![
                (ustr("Nil"), Type::unit()),
                (
                    ustr("Cons"),
                    Type::tuple(vec![Type::variable(var_v), Type::variable(var_w)]),
                ),
            ]);
            try_intern_recursive_equation(var_w, ty).unwrap()
        };
        assert!(list_of_v.contains_any_type_var(var_v));

        let ty = Type::variant(vec![(ustr("End"), int()), (ustr("Wrap"), list_of_v)]);
        let rec_ty = try_intern_recursive_equation(var_v, ty).unwrap();
        assert!(rec_ty.is_global_recursive());
        assert!(!rec_ty.contains_any_type_var(var_v));
    }
}
