// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

//! Binary bounds of regular type graphs, including symbolic graphs whose
//! constructor decisions are already known. This module does not select
//! inference solutions: a computed join remains only a lower bound.
//!
//! Product states contain two input nodes and a polarity. Construction is
//! iterative, including failure propagation: an unrepresentable join can be
//! discovered after a recursive backedge has already been visited. Failed joins
//! invalidate enclosing joins and collapse enclosing meets to Never.

use std::mem;

use crate::{
    FxHashMap,
    parser::location::Location,
    types::{
        effects::EffType,
        mutability::MutType,
        r#type::{
            FnArgType, SubscriptMemberType, SubscriptResultConvention, Type, TypeKind, store_types,
        },
        type_like::TypeLike,
    },
};

use super::unify::UnifiedTypeInference;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) enum BoundOperation {
    Join,
    Meet,
}

impl BoundOperation {
    fn dual(self) -> Self {
        match self {
            Self::Join => Self::Meet,
            Self::Meet => Self::Join,
        }
    }

    fn effects(self, left: &EffType, right: &EffType) -> EffType {
        match self {
            Self::Join => left.union(right),
            Self::Meet => left.intersection(right),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct UnresolvedBound;

type EffectMeet<'a> = Option<&'a mut dyn FnMut(&EffType, &EffType) -> EffType>;

/// `None` means the join is unrepresentable. Binary meet always has a result.
/// Reject unknowns even in identical inputs: equality does not make them ground.
pub(super) fn ground_bound(
    left: Type,
    right: Type,
    operation: BoundOperation,
) -> Result<Option<Type>, UnresolvedBound> {
    if !left.is_constant() || !right.is_constant() {
        return Err(UnresolvedBound);
    }
    known_bound(left, right, operation)
}

/// A symbolic product is usable only when every constructor decision is known.
/// Identical symbolic leaves and bottom identities are exact for every
/// instantiation. An undecidable equality or meet blocks the whole operation;
/// it must not be mistaken for a failed join and collapse an enclosing meet.
pub(super) fn known_bound(
    left: Type,
    right: Type,
    operation: BoundOperation,
) -> Result<Option<Type>, UnresolvedBound> {
    symbolic_bound(left, right, operation, None)
}

pub(super) fn symbolic_bound(
    left: Type,
    right: Type,
    operation: BoundOperation,
    effect_meet: EffectMeet<'_>,
) -> Result<Option<Type>, UnresolvedBound> {
    let mut product = Product {
        effect_meet,
        ..Product::default()
    };
    let root = product.request(left, right, operation);
    if root.world().is_some() {
        return Ok(Some(root));
    }
    let mut index = 0;
    while index < product.states.len() {
        let (left, right, operation) = product.states[index];
        product.kinds[index] = product.expand(left, right, operation);
        index += 1;
    }
    if product.unresolved {
        return Err(UnresolvedBound);
    }

    // Only failure of a join propagates: a failed meet has the valid result
    // Never. A queue visits each reverse edge at most once.
    let mut parents = vec![Vec::new(); product.states.len()];
    let mut failed = vec![false; product.states.len()];
    let mut queue = Vec::new();
    for (index, kind) in product.kinds.iter().enumerate() {
        if let Some(kind) = kind {
            kind.for_each_inner_type(|child| {
                if child.world().is_none() {
                    parents[child.index() as usize].push(index);
                }
            });
        } else {
            failed[index] = true;
            if product.states[index].2 == BoundOperation::Join {
                queue.push(index);
            }
        }
    }
    while let Some(child) = queue.pop() {
        for &parent in &parents[child] {
            if !failed[parent] {
                failed[parent] = true;
                if product.states[parent].2 == BoundOperation::Join {
                    queue.push(parent);
                }
            }
        }
    }
    let root_index = root.index() as usize;
    if failed[root_index] && operation == BoundOperation::Join {
        return Ok(None);
    }
    let kinds: Vec<_> = product
        .kinds
        .into_iter()
        .enumerate()
        .map(|(index, kind)| {
            if failed[index] {
                TypeKind::Never
            } else {
                kind.expect("successful product state has a constructor")
            }
        })
        .collect();
    // A collapsed meet disconnects its former children. Do not publish those
    // abandoned product states into the session's permanent type universe.
    let reachable = reachable_product(root, kinds);
    log::trace!(
        "type product: {} pair states, {} reachable nodes",
        product.states.len(),
        reachable.len()
    );
    Ok(Some(store_types(&reachable)[0]))
}

/// Compact the finished graph, preserving global children and recursive edges.
/// Discovery assigns the root index zero before following any backedge.
fn reachable_product(root: Type, mut kinds: Vec<TypeKind>) -> Vec<TypeKind> {
    let root = root.index() as usize;
    let mut remapping = vec![None; kinds.len()];
    let mut reachable = vec![root];
    remapping[root] = Some(Type::new_local(0));
    let mut cursor = 0;
    while cursor < reachable.len() {
        kinds[reachable[cursor]].for_each_inner_type(|child| {
            if child.world().is_none() {
                let child = child.index() as usize;
                if remapping[child].is_none() {
                    remapping[child] = Some(Type::new_local(reachable.len() as u32));
                    reachable.push(child);
                }
            }
        });
        cursor += 1;
    }
    reachable
        .into_iter()
        .map(|index| {
            let mut kind = mem::replace(&mut kinds[index], TypeKind::Never);
            kind.for_each_inner_type_mut(|child| {
                if child.world().is_none() {
                    *child =
                        remapping[child.index() as usize].expect("reachable child has a new index");
                }
            });
            kind
        })
        .collect()
}

#[derive(Default)]
struct Product<'a> {
    effect_meet: EffectMeet<'a>,
    unresolved: bool,
    indices: FxHashMap<(Type, Type, BoundOperation), Type>,
    states: Vec<(Type, Type, BoundOperation)>,
    kinds: Vec<Option<TypeKind>>,
}

impl Product<'_> {
    fn request(&mut self, left: Type, right: Type, operation: BoundOperation) -> Type {
        if left == right {
            return left;
        }
        if left == Type::never() || right == Type::never() {
            return match operation {
                BoundOperation::Join if left == Type::never() => right,
                BoundOperation::Join => left,
                BoundOperation::Meet => Type::never(),
            };
        }
        let key = (left, right, operation);
        if let Some(&ty) = self.indices.get(&key) {
            return ty;
        }
        let ty = Type::new_local(self.states.len() as u32);
        self.indices.insert(key, ty);
        self.states.push(key);
        self.kinds.push(None);
        ty
    }

    fn args(
        &mut self,
        left: &mut [FnArgType],
        right: &[FnArgType],
        operation: BoundOperation,
    ) -> Option<()> {
        if left.len() != right.len() {
            return None;
        }
        for (left, right) in left.iter_mut().zip(right) {
            if left.mut_ty.is_variable() || right.mut_ty.is_variable() {
                self.unresolved = true;
                return None;
            }
            let left_mut = left.mut_ty == MutType::mutable();
            let right_mut = right.mut_ty == MutType::mutable();
            match operation {
                BoundOperation::Join if left_mut || right_mut => {
                    if left.ty != right.ty && (!left.ty.is_constant() || !right.ty.is_constant()) {
                        self.unresolved = true;
                        return None;
                    }
                    // A writable implementation fixes both the read and write
                    // type. Every read-only contributor must accept that type.
                    let fixed = if left_mut { left.ty } else { right.ty };
                    let compatible = if left_mut && right_mut {
                        left.ty == right.ty
                    } else {
                        ground_subtype(fixed, if left_mut { right.ty } else { left.ty })
                    };
                    if !compatible {
                        return None;
                    }
                    left.ty = fixed;
                    left.mut_ty = MutType::mutable();
                }
                BoundOperation::Meet if left_mut && right_mut && left.ty == right.ty => {}
                _ => {
                    left.ty = self.request(left.ty, right.ty, operation.dual());
                    left.mut_ty = MutType::constant();
                }
            }
        }
        Some(())
    }

    fn effect_bound(
        &mut self,
        left: &EffType,
        right: &EffType,
        operation: BoundOperation,
    ) -> Option<EffType> {
        if operation == BoundOperation::Meet
            && left != right
            && (left.has_variables() || right.has_variables())
        {
            if let Some(meet) = &mut self.effect_meet {
                Some(meet(left, right))
            } else {
                self.unresolved = true;
                None
            }
        } else {
            Some(operation.effects(left, right))
        }
    }

    fn member_bound(
        &mut self,
        left: &Option<SubscriptMemberType>,
        right: &Option<SubscriptMemberType>,
        operation: BoundOperation,
    ) -> Option<Option<SubscriptMemberType>> {
        let mut result = member_bound(left, right, operation);
        if let (Some(left), Some(right), Some(result)) = (left, right, &mut result) {
            result.effects = self.effect_bound(&left.effects, &right.effects, operation)?;
        }
        Some(result)
    }

    fn expand(&mut self, left: Type, right: Type, operation: BoundOperation) -> Option<TypeKind> {
        use TypeKind::*;
        let ground = left.is_constant() && right.is_constant();
        let mut left = left.data().clone();
        let right = right.data().clone();
        match (&mut left, &right) {
            (Variable(_), _) | (_, Variable(_)) => {
                self.unresolved = true;
                return None;
            }
            (Native(left), Native(right))
                if left.bare_ty == right.bare_ty
                    && left.arguments.len() == right.arguments.len() =>
            {
                for (left, right) in left.arguments.iter_mut().zip(&right.arguments) {
                    *left = self.request(*left, *right, operation);
                }
            }
            (Tuple(left), Tuple(right)) if left.len() == right.len() => {
                for (left, right) in left.iter_mut().zip(right) {
                    *left = self.request(*left, *right, operation);
                }
            }
            (Record(left), Record(right)) | (Variant(left), Variant(right))
                if left.len() == right.len()
                    && left
                        .iter()
                        .zip(right)
                        .all(|(left, right)| left.0 == right.0) =>
            {
                for (left, right) in left.iter_mut().zip(right) {
                    left.1 = self.request(left.1, right.1, operation);
                }
            }
            (Function(left), Function(right)) => {
                self.args(&mut left.args, &right.args, operation)?;
                left.ret = self.request(left.ret, right.ret, operation);
                left.effects = self.effect_bound(&left.effects, &right.effects, operation)?;
            }
            (Subscript(left), Subscript(right)) => {
                self.args(&mut left.args, &right.args, operation)?;
                let same_result = left.ret == right.ret;
                left.ret = match operation {
                    BoundOperation::Meet
                        if left.mut_member.is_some() || right.mut_member.is_some() =>
                    {
                        // A lower bound must retain every required mutable
                        // member, whose result storage type is fixed exactly.
                        let fixed = if left.mut_member.is_some() {
                            left.ret
                        } else {
                            right.ret
                        };
                        if !same_result && (!left.ret.is_constant() || !right.ret.is_constant()) {
                            self.unresolved = true;
                            return None;
                        }
                        let compatible = if left.mut_member.is_some() && right.mut_member.is_some()
                        {
                            same_result
                        } else {
                            ground_subtype(
                                fixed,
                                if left.mut_member.is_some() {
                                    right.ret
                                } else {
                                    left.ret
                                },
                            )
                        };
                        if !compatible {
                            return None;
                        }
                        fixed
                    }
                    _ => self.request(left.ret, right.ret, operation),
                };
                left.ref_member =
                    self.member_bound(&left.ref_member, &right.ref_member, operation)?;
                left.mut_member = if operation == BoundOperation::Join && !same_result {
                    // Differently typed storage cannot share a writable view.
                    None
                } else {
                    self.member_bound(&left.mut_member, &right.mut_member, operation)?
                };
            }
            // Nominal parameters (including effects) are invariant. Equal
            // ground types were handled by request before constructing a state.
            (Named(left), Named(right)) if left.def == right.def => {
                if !ground {
                    self.unresolved = true;
                }
                return None;
            }
            _ => return None,
        }
        Some(left)
    }
}

fn ground_subtype(left: Type, right: Type) -> bool {
    let span = Location::new_synthesized();
    UnifiedTypeInference::default()
        .unify_sub_type(left, span, right, span)
        .is_ok()
}

fn member_bound(
    left: &Option<SubscriptMemberType>,
    right: &Option<SubscriptMemberType>,
    operation: BoundOperation,
) -> Option<SubscriptMemberType> {
    use BoundOperation::*;
    use SubscriptResultConvention::*;
    match (left, right) {
        (Some(left), Some(right)) => Some(SubscriptMemberType {
            effects: operation.effects(&left.effects, &right.effects),
            result_convention: match operation {
                Join if left.result_convention == AddressorPlace
                    && right.result_convention == AddressorPlace =>
                {
                    AddressorPlace
                }
                Join => YieldedOnce,
                Meet if left.result_convention == YieldedOnce
                    && right.result_convention == YieldedOnce =>
                {
                    YieldedOnce
                }
                Meet => AddressorPlace,
            },
        }),
        (left, right) => match operation {
            Join => None,
            Meet => left.as_ref().or(right.as_ref()).cloned(),
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        containers::b,
        std::{logic::bool_type, math::int_type},
        types::{
            effects::{EffectVar, PrimitiveEffect, effect, no_effects},
            r#type::{FnType, SubscriptType, TypeVar},
        },
    };
    use ustr::ustr;

    fn bound(left: Type, right: Type, operation: BoundOperation) -> Option<Type> {
        ground_bound(left, right, operation).unwrap()
    }

    #[test]
    fn ground_bounds_callable_read_write_model() {
        // Independent finite interpretation of read/write contracts. The three
        // callback behaviors are divergence, returning int, and returning bool;
        // primitive int/bool values occupy separate bits. This universe is
        // closed under representable binary joins and meets of argument types.
        let arguments = [
            (Type::never(), 0_u8),
            (int_type(), 1),
            (bool_type(), 2),
            (Type::nullary_function_by_val(Type::never()), 4),
            (Type::nullary_function_by_val(int_type()), 12),
            (Type::nullary_function_by_val(bool_type()), 20),
        ];
        let results = [(Type::never(), 0_u8), (int_type(), 1), (bool_type(), 2)];
        let effects = [
            no_effects(),
            effect(PrimitiveEffect::Read),
            effect(PrimitiveEffect::Fallible),
            effect(PrimitiveEffect::Read).union(&effect(PrimitiveEffect::Fallible)),
        ];
        let mut universe = vec![(Type::never(), None)];
        for (arg, read) in arguments {
            for mutable in [false, true] {
                for (ret, result) in results {
                    for (eff, effects) in effects.iter().enumerate() {
                        let ty = Type::function_type(FnType::new(
                            vec![FnArgType::new(
                                arg,
                                if mutable {
                                    MutType::mutable()
                                } else {
                                    MutType::constant()
                                },
                            )],
                            ret,
                            effects.clone(),
                        ));
                        universe.push((ty, Some((read, mutable, result, eff))));
                    }
                }
            }
        }
        let subset = |left, right| left & right == left;
        let relation: Vec<Vec<_>> = universe
            .iter()
            .map(|(_, left)| {
                universe
                    .iter()
                    .map(|(_, right)| match (left, right) {
                        (None, _) => true,
                        (_, None) => false,
                        (Some((lr, lm, lv, le)), Some((rr, rm, rv, re))) => {
                            (!lm || *rm)
                                && subset(*rr, *lr)
                                && (!lm || subset(*lr, *rr))
                                && subset(*lv, *rv)
                                && le & re == *le
                        }
                    })
                    .collect()
            })
            .collect();
        let indices: FxHashMap<_, _> = universe
            .iter()
            .enumerate()
            .map(|(i, (ty, _))| (*ty, i))
            .collect();
        for (a, (left, _)) in universe.iter().enumerate() {
            for (b, (right, _)) in universe.iter().enumerate() {
                assert_eq!(ground_subtype(*left, *right), relation[a][b]);
                for operation in [BoundOperation::Join, BoundOperation::Meet] {
                    let candidates: Vec<_> = (0..universe.len())
                        .filter(|&c| match operation {
                            BoundOperation::Join => relation[a][c] && relation[b][c],
                            BoundOperation::Meet => relation[c][a] && relation[c][b],
                        })
                        .collect();
                    let result = bound(*left, *right, operation);
                    match result {
                        Some(result) => {
                            let r = indices[&result];
                            assert!(
                                candidates.contains(&r),
                                "invalid {operation:?}: {left:?}, {right:?}"
                            );
                            assert!(
                                candidates.iter().all(|&c| match operation {
                                    BoundOperation::Join => relation[r][c],
                                    BoundOperation::Meet => relation[c][r],
                                }),
                                "non-extremal {operation:?}: {left:?}, {right:?}"
                            );
                        }
                        None => assert!(
                            candidates.is_empty(),
                            "missing {operation:?}: {left:?}, {right:?}"
                        ),
                    }
                    assert_eq!(result, bound(*right, *left, operation));
                }
            }
        }
    }

    fn recursive(payloads: &[Type]) -> Type {
        let mut graph = Vec::new();
        for (index, &payload) in payloads.iter().enumerate() {
            graph.push(TypeKind::Variant(vec![
                (ustr("End"), Type::unit()),
                (ustr("Step"), Type::new_local((2 * index + 1) as u32)),
            ]));
            graph.push(TypeKind::Tuple(vec![
                Type::new_local((2 * ((index + 1) % payloads.len())) as u32),
                payload,
            ]));
        }
        store_types(&graph)[0]
    }

    #[test]
    fn ground_bounds_recursive_products_preserve_distinct_states() {
        let bottom = recursive(&[Type::never()]);
        let alternating = recursive(&[int_type(), bool_type()]);
        assert_eq!(
            bound(bottom, alternating, BoundOperation::Join),
            Some(alternating)
        );
        assert_eq!(
            bound(bottom, alternating, BoundOperation::Meet),
            Some(bottom)
        );
        let left = recursive(&[int_type(), Type::never()]);
        let right = recursive(&[Type::never(), bool_type()]);
        assert_eq!(bound(left, right, BoundOperation::Join), Some(alternating));
        assert_eq!(bound(left, right, BoundOperation::Meet), Some(bottom));
        for operation in [BoundOperation::Join, BoundOperation::Meet] {
            assert_eq!(bound(left, right, operation), bound(right, left, operation));
            assert_eq!(bound(left, left, operation), Some(left));
            let unfolded = recursive(&[int_type(), Type::never(), int_type(), Type::never()]);
            assert_eq!(
                bound(unfolded, right, operation),
                bound(left, right, operation)
            );
        }
    }

    #[test_log::test]
    fn ground_bounds_coprime_recursive_stress() {
        // Coprime periods force a multiplicative product, with no unfolding
        // cutoff. The independent stream model also fixes the result period.
        let mut a = vec![Type::never(); 17];
        let mut b = vec![Type::never(); 19];
        a[0] = int_type();
        b[1] = int_type();
        let expected: Vec<_> = (0..17 * 19)
            .map(|i| {
                if a[i % 17] == int_type() || b[i % 19] == int_type() {
                    int_type()
                } else {
                    Type::never()
                }
            })
            .collect();
        let (left, right, expected) = (recursive(&a), recursive(&b), recursive(&expected));
        for (left, right) in [(left, right), (right, left)] {
            assert_eq!(bound(left, right, BoundOperation::Join), Some(expected));
        }
    }

    #[test]
    fn ground_bounds_recursive_failures_propagate_through_backedges() {
        let left = recursive(&[int_type()]);
        let right = recursive(&[int_type(), bool_type()]);
        assert_eq!(bound(left, right, BoundOperation::Join), None);
        // A failed argument join collapses the enclosing function meet, but a
        // covariant tuple's Never child must not collapse its enclosing tuple.
        let left_fn = Type::function_by_val([left], int_type());
        let right_fn = Type::function_by_val([right], int_type());
        assert_eq!(
            bound(left_fn, right_fn, BoundOperation::Meet),
            Some(Type::never())
        );
        assert_eq!(
            bound(
                TypeKind::Tuple(vec![left_fn]).store(),
                TypeKind::Tuple(vec![right_fn]).store(),
                BoundOperation::Meet
            ),
            Some(TypeKind::Tuple(vec![Type::never()]).store()),
        );
    }

    #[test]
    fn ground_bounds_publication_prunes_abandoned_states_and_remaps_cycles() {
        // A collapsed meet is represented by node 3. Its old subtree (0, 1)
        // has become unreachable. Root 2 and the 2 <-> 4 cycle must be remapped
        // without changing the already interned global child.
        let graph = vec![
            TypeKind::Tuple(vec![Type::new_local(1)]),
            TypeKind::Tuple(vec![Type::new_local(0), bool_type()]),
            TypeKind::Tuple(vec![Type::new_local(3), Type::new_local(4), int_type()]),
            TypeKind::Never,
            TypeKind::Variant(vec![
                (ustr("End"), Type::unit()),
                (ustr("Next"), Type::new_local(2)),
            ]),
        ];
        let retained = reachable_product(Type::new_local(2), graph);
        assert_eq!(
            retained,
            vec![
                TypeKind::Tuple(vec![Type::new_local(1), Type::new_local(2), int_type()]),
                TypeKind::Never,
                TypeKind::Variant(vec![
                    (ustr("End"), Type::unit()),
                    (ustr("Next"), Type::new_local(0))
                ]),
            ]
        );
        assert_eq!(
            reachable_product(
                Type::new_local(1),
                vec![TypeKind::Tuple(vec![bool_type()]), TypeKind::Never]
            ),
            vec![TypeKind::Never]
        );
    }

    #[test]
    fn ground_bounds_contravariant_cycles_can_collapse_inside_a_product() {
        let recursive_callback = |ret| {
            store_types(&[
                TypeKind::Variant(vec![
                    (ustr("End"), Type::unit()),
                    (ustr("Step"), Type::new_local(1)),
                ]),
                TypeKind::Function(b(FnType::new(
                    vec![FnArgType::new_by_val(Type::new_local(0))],
                    ret,
                    no_effects(),
                ))),
            ])[0]
        };
        let left = recursive_callback(int_type());
        let right = recursive_callback(bool_type());
        assert_eq!(bound(left, right, BoundOperation::Join), None);
        let expected = Type::variant(vec![
            (ustr("End"), Type::unit()),
            (ustr("Step"), Type::never()),
        ]);
        assert_eq!(bound(left, right, BoundOperation::Meet), Some(expected));
        assert!(ground_subtype(expected, left));
        assert!(ground_subtype(expected, right));
    }

    #[test]
    fn ground_bounds_periodic_graphs_match_sequence_model() {
        // Model the infinite payload sequences, independently of graph pairing
        // and interning. A common period is enough to compare every position.
        // Three positions include coprime periods, repetition and phase shifts.
        let mut sequences = Vec::new();
        let atoms = [Type::never(), int_type(), bool_type()];
        for length in 1..=3 {
            for mut code in 0..3_usize.pow(length) {
                let mut sequence = Vec::new();
                for _ in 0..length {
                    sequence.push(atoms[code % 3]);
                    code /= 3;
                }
                sequences.push((recursive(&sequence), sequence));
            }
        }
        for (left, a) in &sequences {
            for (right, b) in &sequences {
                let period = a.len() * b.len();
                for op in [BoundOperation::Join, BoundOperation::Meet] {
                    let expected: Option<Vec<_>> = (0..period)
                        .map(|i| {
                            let a = a[i % a.len()];
                            let b = b[i % b.len()];
                            if a == b {
                                Some(a)
                            } else {
                                match op {
                                    BoundOperation::Meet => Some(Type::never()),
                                    BoundOperation::Join if a == Type::never() => Some(b),
                                    BoundOperation::Join if b == Type::never() => Some(a),
                                    BoundOperation::Join => None,
                                }
                            }
                        })
                        .collect();
                    let expected = expected.map(|sequence| recursive(&sequence));
                    assert_eq!(bound(*left, *right, op), expected, "{op:?}: {a:?}, {b:?}");
                }
            }
        }
    }

    #[test]
    fn ground_bounds_nominal_parameters_are_invariant() {
        use crate::std::array::array_type;
        let left = array_type(Type::nullary_function_by_val(Type::never()));
        let right = array_type(Type::nullary_function_by_val(int_type()));
        assert_eq!(bound(left, right, BoundOperation::Join), None);
        assert_eq!(
            bound(left, right, BoundOperation::Meet),
            Some(Type::never())
        );
        assert_eq!(bound(left, left, BoundOperation::Join), Some(left));
    }

    #[test]
    fn ground_bounds_subscripts_match_independent_read_write_model() {
        use SubscriptResultConvention::*;
        // The same independent value/behavior sets as the callable model. A
        // result contract allows reads from this set; a mutable member also
        // allows writing every member of the set, requiring reverse inclusion.
        let results = [
            (Type::never(), 0_u8),
            (int_type(), 1),
            (bool_type(), 2),
            (Type::nullary_function_by_val(Type::never()), 4),
            (Type::nullary_function_by_val(int_type()), 12),
            (Type::nullary_function_by_val(bool_type()), 20),
        ];
        // Member contracts independently record effect bits and whether the
        // result remains valid beyond a scoped yield (caller-rooted addressor).
        let members = [
            None,
            Some((0_u8, false)),
            Some((0, true)),
            Some((1, false)),
            Some((1, true)),
        ];
        let to_member = |member: Option<(u8, bool)>| {
            member.map(|(effects, addressor)| {
                SubscriptMemberType::new(
                    if effects == 0 {
                        no_effects()
                    } else {
                        effect(PrimitiveEffect::Fallible)
                    },
                    if addressor {
                        AddressorPlace
                    } else {
                        YieldedOnce
                    },
                )
            })
        };
        let mut universe = vec![(Type::never(), None)];
        for (ret, values) in results {
            for read in members {
                for write in members {
                    let ty = Type::subscript_type(SubscriptType::new(
                        vec![FnArgType::new_by_val(int_type())],
                        ret,
                        to_member(read),
                        to_member(write),
                    ));
                    universe.push((ty, Some((values, read, write))));
                }
            }
        }
        let permits =
            |actual: Option<(u8, bool)>, expected: Option<(u8, bool)>| match (actual, expected) {
                (_, None) => true,
                (None, _) => false,
                (Some((ae, aa)), Some((ee, ea))) => ae & ee == ae && (!ea || aa),
            };
        let relation: Vec<Vec<_>> = universe
            .iter()
            .map(|(_, actual)| {
                universe
                    .iter()
                    .map(|(_, expected)| match (actual, expected) {
                        (None, _) => true,
                        (_, None) => false,
                        (Some((av, ar, aw)), Some((ev, er, ew))) => {
                            av & ev == *av
                                && (ew.is_none() || ev & av == *ev)
                                && permits(*ar, *er)
                                && permits(*aw, *ew)
                        }
                    })
                    .collect()
            })
            .collect();
        let indices: FxHashMap<_, _> = universe
            .iter()
            .enumerate()
            .map(|(i, (ty, _))| (*ty, i))
            .collect();
        for (a, &(left, _)) in universe.iter().enumerate() {
            for (b, &(right, _)) in universe.iter().enumerate() {
                // Compare the production comparator to the model as well: it
                // must not serve as its own oracle for writable result safety.
                assert_eq!(
                    ground_subtype(left, right),
                    relation[a][b],
                    "{left:?} <: {right:?}"
                );
                for op in [BoundOperation::Join, BoundOperation::Meet] {
                    let candidates: Vec<_> = (0..universe.len())
                        .filter(|&c| match op {
                            BoundOperation::Join => relation[a][c] && relation[b][c],
                            BoundOperation::Meet => relation[c][a] && relation[c][b],
                        })
                        .collect();
                    let result = bound(left, right, op);
                    if let Some(result) = result {
                        let r = indices[&result];
                        assert!(
                            candidates.contains(&r),
                            "invalid {op:?}: {left:?}, {right:?}"
                        );
                        assert!(
                            candidates.iter().all(|&c| match op {
                                BoundOperation::Join => relation[r][c],
                                BoundOperation::Meet => relation[c][r],
                            }),
                            "non-extremal {op:?}: {left:?}, {right:?}"
                        );
                    } else {
                        assert!(candidates.is_empty(), "missing {op:?}: {left:?}, {right:?}");
                    }
                    assert_eq!(result, bound(right, left, op));
                }
                for c in 0..universe.len() {
                    assert!(!relation[a][b] || !relation[b][c] || relation[a][c]);
                }
            }
        }
    }

    #[test]
    fn ground_bounds_reject_unknowns_before_identity_shortcut() {
        for ty in [
            Type::variable(TypeVar::new(0)),
            Type::function_by_val_with_effects(
                [],
                int_type(),
                EffType::single_variable(EffectVar::new(0)),
            ),
        ] {
            assert_eq!(
                ground_bound(ty, ty, BoundOperation::Join),
                Err(UnresolvedBound)
            );
        }
    }

    #[test]
    fn ground_bounds_unresolved_argument_join_can_change_enclosing_meet_shape() {
        // A proposed symbolic meet of (a -> int) and (b -> int) cannot
        // unconditionally be (c -> int), a <: c, b <: c. Once a = int and
        // b = bool, c has no solution, but the original meet is Never.
        // Ground selection must precede emitting those leaf obligations, or
        // selection needs a transaction that can discard them on collapse.
        let a = Type::variable(TypeVar::new(0));
        let b = Type::variable(TypeVar::new(1));
        let callback = |arg| Type::function_by_val([arg], int_type());
        assert_eq!(
            ground_bound(callback(a), callback(b), BoundOperation::Meet),
            Err(UnresolvedBound)
        );
        assert_eq!(bound(int_type(), bool_type(), BoundOperation::Join), None);
        assert_eq!(
            bound(
                callback(int_type()),
                callback(bool_type()),
                BoundOperation::Meet
            ),
            Some(Type::never())
        );
        // The surrounding callable join is nevertheless representable. Losing
        // that fallback would reject a concrete P1-A case at the next depth.
        let outer = |arg| Type::function_by_val([arg], int_type());
        let result = bound(
            outer(callback(int_type())),
            outer(callback(bool_type())),
            BoundOperation::Join,
        )
        .unwrap();
        assert_eq!(result, outer(Type::never()));
        assert!(ground_subtype(outer(callback(int_type())), result));
        assert!(ground_subtype(outer(callback(bool_type())), result));
    }
}
