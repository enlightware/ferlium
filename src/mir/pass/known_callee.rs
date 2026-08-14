// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
//! The std functions whose value semantics the optimizer is allowed to reason about symbolically.
//!
//! Ferlium keeps numeric arithmetic, comparison and array indexing as ordinary calls into std; MIR
//! has no arithmetic operations of its own. Constant folding copes with that by *running* a call
//! ([`const_eval`](crate::mir::const_eval)), which needs every argument known. Symbolic consumers
//! need the opposite: the meaning of a call whose arguments are **not** all known, so that `i + 1`
//! relates to `i`, `x * 1.0` becomes `x`, and `i < len` refines a branch. This table is where that
//! meaning is attached to a callee, and it is the only place in the optimizer that hard-codes std
//! identities.
//!
//! **Identity, not shape.** A callee qualifies by being the very function std declares — resolved
//! once through the trait tables and the module's function names — never by matching a name, a
//! signature or a body. A user function called `add` is a different `FunctionId` and gets no
//! semantics from here.
//!
//! **Identity does not grant general purity.** Every entry names what a call computes; whether a
//! call may be moved, merged or removed remains a question for its inferred effects, which a
//! consumer must check for itself. The explicit `total and speculatable` classification below is a
//! second, stronger contract used for dead calls; it is never inferred from purity, since a pure
//! script function may diverge. A consumer may also use an entry's narrower std contract — range
//! reasoning knows that computing either array addressor does not mutate its receiver — but that
//! does not make arbitrary known calls pure or suppress their declared effects.
//!
//! **A specialization resolves to its original.** Optimization preserves semantics, so a
//! specialized copy of a known callee is still that callee. Every entry below is additionally
//! *instantiation-independent* — array length and indexing have the same meaning at every element
//! type, and the arithmetic entries are concrete already — which is why canonicalizing to the
//! original needs no accompanying type check. An entry whose meaning depended on the instantiation
//! could not be admitted without one, and none is.
//!
//! Consumers currently include partial call simplification, dead-call elimination and integer
//! range reasoning.
#![allow(dead_code)]

use rustc_hash::FxHashMap;
use ustr::ustr;

use crate::{
    Modules,
    module::{
        FunctionId, LocalFunctionId, Module, ProjectionIndex, TypeDefId, id::Id,
        trait_impl::ConcreteTraitImplKey,
    },
    std::{
        STD_MODULE_ID,
        core_traits_names::{ITERATOR_TRAIT_NAME, NUM_TRAIT_NAME, ORD_TRAIT_NAME},
        math::{float_type, int_type},
    },
    types::{
        effects::EffType,
        r#type::{CallImplType, Type, TypeKind},
    },
};

/// The definition a named type refers to, if it is one.
fn named_def(ty: Type) -> Option<TypeDefId> {
    let guard = ty.data();
    match &*guard {
        TypeKind::Named(named) => Some(named.def),
        _ => None,
    }
}

/// What a call to a known std function computes.
///
/// Each variant is a statement about the returned value in terms of the arguments, in argument
/// order. Wrapping behaviour is the runtime's: Ferlium's `int` is a wrapping two's-complement
/// integer, so `IntAdd` is exact modulo that and a consumer reasoning about magnitudes must account
/// for it rather than assume mathematical integers.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum KnownCallee {
    /// `Num<int>::add(left, right)` — `left + right`.
    IntAdd,
    /// `Num<int>::sub(left, right)` — `left - right`.
    IntSub,
    /// `Num<int>::mul(left, right)` — `left * right`.
    IntMul,
    /// `Num<int>::neg(value)` — `-value`.
    IntNeg,
    /// `Ord<int>::cmp(left, right)` — `Less`, `Equal` or `Greater`.
    ///
    /// This is the whole of integer comparison in MIR: a source-level `<` lowers to this call plus
    /// an `extract_tag` and a `comp_eq` against one tag.
    IntCmp,
    /// `Num<float>::add(left, right)` — finite, saturating `left + right`.
    FloatAdd,
    /// `Num<float>::sub(left, right)` — finite, saturating `left - right`.
    FloatSub,
    /// `Num<float>::mul(left, right)` — finite, saturating `left * right`.
    FloatMul,
    /// `Num<float>::neg(value)` — `-value`.
    FloatNeg,
    /// `Ord<float>::cmp(left, right)` — `Less`, `Equal` or `Greater`.
    ///
    /// Ferlium floats are finite and ordered, rather than IEEE values admitting NaN and infinity.
    FloatCmp,
    /// `array_len(array)` — the array's element count, which is its `len` field.
    ArrayLen,
    /// `array_resolve_index(index, len)` — `index` when `0 <= index < len`, `len + index` when
    /// `-len <= index < 0`, and a panic otherwise.
    ///
    /// The panic is why this is fallible, and removing it once the index is proved in range is the
    /// point of proving it.
    ArrayResolveIndex,
    /// The mutable member of `array_index(array, index)` — projects the element selected by a
    /// signed index, or panics when that index is out of range.
    ArrayIndex,
    /// The mutable member of `array_offset_unchecked(array, offset)` — projects the element at an
    /// offset whose `0 <= offset < len(array)` precondition the caller has established.
    ArrayOffsetUnchecked,
    /// `array_wrap_index(capacity, index)` — `index - capacity` when `index >= capacity`, and
    /// `index` otherwise.
    ///
    /// The circular-buffer step. Proving an index in range says nothing about this: it wraps a
    /// *physical* slot, and dropping it needs its own proof that `start + offset < capacity`.
    ArrayWrapIndex,
    /// `Iterator<RangeIterator>::next(iterator)` — advances `iterator.next` by one step towards
    /// `iterator.range.end` and yields the value before the step, or `None` at the end.
    ///
    /// Ascending when `range.end >= range.start` and descending otherwise, and the bound is
    /// exclusive. This is where a `for i in a..b` loop's induction variable lives, which is why it
    /// must be understood rather than waited on to be inlined.
    RangeNext,
    /// `Iterator<RangeInclusiveIterator>::next(iterator)` — as [`RangeNext`](Self::RangeNext), with
    /// an inclusive bound.
    RangeInclusiveNext,
}

impl KnownCallee {
    /// Whether this exact std callable is total, deterministic and safe to execute speculatively.
    ///
    /// This is deliberately stronger than an empty effect row. A pure script function may diverge,
    /// so purity alone never permits dead-call removal or motion out of a zero-trip loop. These
    /// entries name concrete native numeric operations whose implementations always terminate and
    /// do not fail for values inhabiting their Ferlium types.
    pub(crate) fn is_total_and_speculatable(self) -> bool {
        matches!(
            self,
            Self::IntAdd
                | Self::IntSub
                | Self::IntMul
                | Self::IntNeg
                | Self::IntCmp
                | Self::FloatAdd
                | Self::FloatSub
                | Self::FloatMul
                | Self::FloatNeg
                | Self::FloatCmp
        )
    }
}

/// The fields of a std type the optimizer reads positionally.
///
/// Resolved rather than assumed: MIR names a field by index, and the index is **not** the
/// declaration order — records are laid out by name, so `Range { start, end }` is `end` at 0 and
/// `start` at 1. Writing the numbers down by hand would work until someone renamed a field.
#[derive(Clone, Copy, Debug)]
pub(crate) struct RangeLayout {
    /// The iterator's cursor.
    pub(crate) next: ProjectionIndex,
    /// The iterator's range.
    pub(crate) range: ProjectionIndex,
    /// The range's inclusive lower bound.
    pub(crate) start: ProjectionIndex,
    /// The range's upper bound, exclusive for `Range` and inclusive for `RangeInclusive`.
    pub(crate) end: ProjectionIndex,
}

/// The std field positions the optimizer reads.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Layouts {
    /// `array`'s element count, which is the only array field with a semantic the optimizer uses:
    /// it is never negative, and no MIR operation says so.
    pub(crate) array_len: ProjectionIndex,
    pub(crate) range: RangeLayout,
    pub(crate) range_inclusive: RangeLayout,
}

/// The known std callees, keyed by identity.
///
/// Built once against a session's std module. Nothing here depends on the module being optimized,
/// so one table serves every module of a session.
pub(crate) struct KnownCallees {
    by_id: FxHashMap<FunctionId, KnownCallee>,
    int_add: FunctionId,
    int_add_ty: CallImplType,
    array_offset_unchecked: FunctionId,
    array_offset_unchecked_effects: EffType,
    layouts: Layouts,
    /// The type definitions a place has to be an instance of for a field position above to mean
    /// anything.
    array: TypeDefId,
    range_iterator: TypeDefId,
    range_inclusive_iterator: TypeDefId,
}

impl KnownCallees {
    /// Resolves every known callee against the registered std module.
    ///
    /// Panics if one is missing: these are std's own items, so an absent entry means std was
    /// renamed out from under the optimizer, and the alternative is range reasoning that silently
    /// stops firing.
    pub(crate) fn new(modules: &Modules) -> Self {
        let std_module = modules
            .get(STD_MODULE_ID)
            .and_then(|entry| entry.module())
            .expect("the std module is registered before any module is optimized");
        let resolver = Resolver {
            modules,
            std_module,
        };
        let range_iterator = resolver.named_type("RangeIterator");
        let range_inclusive_iterator = resolver.named_type("RangeInclusiveIterator");
        let int_add = resolver.method(NUM_TRAIT_NAME, int_type(), "add");
        let array_index = resolver.subscript_mut_member("array_index");
        let array_offset_unchecked = resolver.subscript_mut_member("array_offset_unchecked");
        resolver.assert_retargetable(array_index, array_offset_unchecked);
        let entries = [
            (int_add, KnownCallee::IntAdd),
            (
                resolver.method(NUM_TRAIT_NAME, int_type(), "sub"),
                KnownCallee::IntSub,
            ),
            (
                resolver.method(NUM_TRAIT_NAME, int_type(), "mul"),
                KnownCallee::IntMul,
            ),
            (
                resolver.method(NUM_TRAIT_NAME, int_type(), "neg"),
                KnownCallee::IntNeg,
            ),
            (
                resolver.method(ORD_TRAIT_NAME, int_type(), "cmp"),
                KnownCallee::IntCmp,
            ),
            (
                resolver.method(NUM_TRAIT_NAME, float_type(), "add"),
                KnownCallee::FloatAdd,
            ),
            (
                resolver.method(NUM_TRAIT_NAME, float_type(), "sub"),
                KnownCallee::FloatSub,
            ),
            (
                resolver.method(NUM_TRAIT_NAME, float_type(), "mul"),
                KnownCallee::FloatMul,
            ),
            (
                resolver.method(NUM_TRAIT_NAME, float_type(), "neg"),
                KnownCallee::FloatNeg,
            ),
            (
                resolver.method(ORD_TRAIT_NAME, float_type(), "cmp"),
                KnownCallee::FloatCmp,
            ),
            (resolver.function("array_len"), KnownCallee::ArrayLen),
            (
                resolver.function("array_resolve_index"),
                KnownCallee::ArrayResolveIndex,
            ),
            (array_index, KnownCallee::ArrayIndex),
            (array_offset_unchecked, KnownCallee::ArrayOffsetUnchecked),
            (
                resolver.function("array_wrap_index"),
                KnownCallee::ArrayWrapIndex,
            ),
            (
                resolver.method(ITERATOR_TRAIT_NAME, range_iterator, "next"),
                KnownCallee::RangeNext,
            ),
            (
                resolver.method(ITERATOR_TRAIT_NAME, range_inclusive_iterator, "next"),
                KnownCallee::RangeInclusiveNext,
            ),
        ];
        Self {
            by_id: entries.into_iter().collect(),
            int_add,
            int_add_ty: resolver.call_impl_type(int_add),
            array_offset_unchecked,
            array_offset_unchecked_effects: resolver.effects(array_offset_unchecked),
            layouts: Layouts {
                array_len: resolver.field("array", "len"),
                range: resolver.range_layout("RangeIterator", "Range"),
                range_inclusive: resolver.range_layout("RangeInclusiveIterator", "RangeInclusive"),
            },
            array: resolver.type_def("array"),
            range_iterator: resolver.type_def("RangeIterator"),
            range_inclusive_iterator: resolver.type_def("RangeInclusiveIterator"),
        }
    }

    pub(crate) fn layouts(&self) -> &Layouts {
        &self.layouts
    }

    /// The concrete integer addition used to materialize an affine offset proved by the range
    /// analysis. Keeping its complete call type here makes the rewrite use the same ordinary std
    /// operation whose wrapping semantics [`KnownCallee::IntAdd`] describes.
    pub(crate) fn int_add(&self) -> (FunctionId, &CallImplType) {
        (self.int_add, &self.int_add_ty)
    }

    /// The unchecked array accessor and the effects its call-site type must carry.
    pub(crate) fn array_offset_unchecked(&self) -> (FunctionId, &EffType) {
        (
            self.array_offset_unchecked,
            &self.array_offset_unchecked_effects,
        )
    }

    /// Whether `ty` is the std array type, at any element type.
    pub(crate) fn is_array(&self, ty: Type) -> bool {
        named_def(ty) == Some(self.array)
    }

    /// The range iterator `ty` is, if it is one.
    pub(crate) fn range_iterator(&self, ty: Type) -> Option<(KnownCallee, RangeLayout)> {
        let def = named_def(ty)?;
        if def == self.range_iterator {
            Some((KnownCallee::RangeNext, self.layouts.range))
        } else if def == self.range_inclusive_iterator {
            Some((
                KnownCallee::RangeInclusiveNext,
                self.layouts.range_inclusive,
            ))
        } else {
            None
        }
    }

    /// What `callee` computes, if the optimizer knows.
    ///
    /// `original_of` canonicalizes a specialization to the function it was specialized from — pass
    /// [`Specializations::original`](super::monomorphize::Specializations::original) inside the
    /// driver — so that a call already rewritten to a specialized copy resolves to the same answer
    /// as the call it replaced.
    pub(crate) fn resolve(
        &self,
        callee: FunctionId,
        original_of: impl Fn(FunctionId) -> Option<FunctionId>,
    ) -> Option<KnownCallee> {
        let original = original_of(callee).unwrap_or(callee);
        self.by_id.get(&original).copied()
    }
}

/// The std module and the lookups that reach into it, so that the table above reads as a list.
struct Resolver<'a> {
    modules: &'a Modules,
    std_module: &'a Module,
}

impl Resolver<'_> {
    /// A std function by the name it is declared under.
    fn function(&self, name: &str) -> FunctionId {
        let name = ustr(name);
        let local = self
            .std_module
            .get_local_function_id(name)
            .unwrap_or_else(|| panic!("std declares no function `{name}`"));
        FunctionId::new(STD_MODULE_ID, local)
    }

    /// The shared mutable member implementation of a std addressor subscript.
    fn subscript_mut_member(&self, name: &str) -> FunctionId {
        let name = ustr(name);
        let member = self
            .std_module
            .get_subscript(name)
            .unwrap_or_else(|| panic!("std declares no subscript `{name}`"))
            .mut_member
            .as_ref()
            .unwrap_or_else(|| panic!("std subscript `{name}` has no mutable member"));
        FunctionId::new(STD_MODULE_ID, member.function)
    }

    /// The declared effects of a resolved std callable.
    fn effects(&self, function: FunctionId) -> EffType {
        self.std_module
            .get_function_by_id(function.function)
            .expect("a resolved std function has a definition")
            .definition
            .ty_scheme
            .ty
            .effects
            .clone()
    }

    /// The selected callable type recorded on a direct MIR call.
    fn call_impl_type(&self, function: FunctionId) -> CallImplType {
        let definition = &self
            .std_module
            .get_function_by_id(function.function)
            .expect("a resolved std function has a definition")
            .definition;
        CallImplType::new(
            definition.ty_scheme.ty.clone(),
            definition.result_convention,
        )
    }

    /// Checks the ABI assumption used when bounds elimination retargets one call to another.
    ///
    /// The effect row is deliberately the one difference: removing the proved panic makes the
    /// replacement infallible. Quantifiers and constraints must stay positional because the call's
    /// recorded generic instantiation is preserved unchanged.
    fn assert_retargetable(&self, checked: FunctionId, unchecked: FunctionId) {
        let checked = self
            .std_module
            .get_function_by_id(checked.function)
            .expect("a resolved std function has a definition");
        let unchecked = self
            .std_module
            .get_function_by_id(unchecked.function)
            .expect("a resolved std function has a definition");
        let mut expected = checked.definition.ty_scheme.clone();
        expected.ty.effects = unchecked.definition.ty_scheme.ty.effects.clone();
        assert_eq!(
            expected, unchecked.definition.ty_scheme,
            "checked and unchecked array addressors must differ only in effects"
        );
        assert_eq!(
            checked.definition.result_convention, unchecked.definition.result_convention,
            "checked and unchecked array addressors must use one result convention"
        );
        assert_eq!(
            checked.parameter_passing, unchecked.parameter_passing,
            "checked and unchecked array addressors must pass visible arguments identically"
        );
    }

    /// The definition of a std type, named the way source names it.
    fn type_def(&self, name: &str) -> TypeDefId {
        let name = ustr(name);
        self.std_module
            .get_type_def_id(name)
            .unwrap_or_else(|| panic!("std declares no type `{name}`"))
    }

    /// The position of a field in a std product type.
    fn field(&self, type_name: &str, field: &str) -> ProjectionIndex {
        let def = self.std_module.type_def(self.type_def(type_name));
        // The parameters only have to be well-formed: a field's *position* does not depend on what
        // the type is instantiated at.
        let shape = def.instantiated_shape(&vec![int_type(); def.param_count()]);
        let guard = shape.data();
        let TypeKind::Record(fields) = &*guard else {
            panic!("std type `{type_name}` is not a record");
        };
        let position = fields
            .iter()
            .position(|(name, _)| name.as_str() == field)
            .unwrap_or_else(|| panic!("std type `{type_name}` has no field `{field}`"));
        ProjectionIndex::from_index(position)
    }

    /// The field positions of an iterator and the range it walks.
    fn range_layout(&self, iterator: &str, range: &str) -> RangeLayout {
        RangeLayout {
            next: self.field(iterator, "next"),
            range: self.field(iterator, "range"),
            start: self.field(range, "start"),
            end: self.field(range, "end"),
        }
    }

    /// A std type with no type arguments, named the way source names it.
    fn named_type(&self, name: &str) -> Type {
        Type::named(self.type_def(name), [])
    }

    /// The method of std's concrete implementation of `trait_name` for `input_ty`.
    fn method(&self, trait_name: &str, input_ty: Type, method: &str) -> FunctionId {
        let trait_id = Module::expect_std_trait_id(self.modules, trait_name);
        let index = self
            .std_module
            .trait_def(trait_id)
            .methods
            .iter()
            .position(|(name, _)| name == &ustr(method))
            .unwrap_or_else(|| panic!("trait `{trait_name}` declares no method `{method}`"));
        let key = ConcreteTraitImplKey::new(trait_id, vec![input_ty]);
        let impl_id = *self
            .std_module
            .get_concrete_impl_by_key(&key)
            .unwrap_or_else(|| panic!("std does not implement `{trait_name}` for this type"));
        let local: LocalFunctionId = self
            .std_module
            .get_impl_data(impl_id)
            .expect("an impl id from the table has data")
            .methods[index];
        FunctionId::new(STD_MODULE_ID, local)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CompilerSession, module::Path, module::id::Id};

    fn known_callees(session: &CompilerSession) -> KnownCallees {
        KnownCallees::new(session.raw_modules())
    }

    /// Every entry must resolve to a function of its own. Two lookups landing on one id would
    /// silently drop an entry and give the survivor the other's semantics, and the table is built
    /// from a list of literals that nothing else checks.
    #[test]
    fn each_known_callee_has_its_own_identity() {
        let session = CompilerSession::new();
        assert_eq!(
            known_callees(&session).by_id.len(),
            17,
            "two known callees resolved to the same function id"
        );
    }

    /// The identities must be the ones a compiled call actually names, which nothing but a
    /// compiled call can confirm — a hand-built id would only restate the lookup.
    #[test]
    fn a_compiled_integer_addition_names_the_known_callee() {
        let mut session = CompilerSession::new();
        let module = session.emit_mir("known", "fn add_them(a: int, b: int) -> int { a + b }");
        let table = known_callees(&session);
        let expected = table
            .by_id
            .iter()
            .find(|(_, known)| **known == KnownCallee::IntAdd)
            .map(|(id, _)| *id)
            .expect("the table holds integer addition");
        let name = session
            .std_module()
            .get_function_name_by_id(expected.function)
            .expect("the resolved function is named");
        assert!(
            module.contains(name.as_str()),
            "`a + b` must call `{name}`, the function the table resolved:\n{module}"
        );
    }

    /// A specialized copy of a known callee is still that callee, which is the whole reason
    /// `resolve` canonicalizes before looking up.
    #[test]
    fn resolution_sees_through_specialization() {
        let session = CompilerSession::new();
        let table = known_callees(&session);
        let (&known, &semantics) = table.by_id.iter().next().expect("the table is not empty");
        // A specialization's id is a slot past the declared table, which is exactly what this is.
        let specialized = FunctionId::new(
            STD_MODULE_ID,
            LocalFunctionId::from_index(session.std_module().function_count()),
        );
        assert_eq!(
            table.resolve(specialized, |_| None),
            None,
            "an unresolved id must stay unknown"
        );
        assert_eq!(
            table.resolve(specialized, |_| Some(known)),
            Some(semantics),
            "canonicalizing to a known original must yield that original's semantics"
        );
    }

    /// Field positions must come from the type, never from the declaration. Records are laid out
    /// by name, so the two disagree for every std type read here — a hand-written table would have
    /// been wrong on the day it was written.
    #[test]
    fn field_positions_are_resolved_rather_than_assumed() {
        let session = CompilerSession::new();
        let table = known_callees(&session);
        let range = table.layouts().range;
        assert_ne!(
            (range.start.as_index(), range.end.as_index()),
            (0, 1),
            "`Range {{ start, end }}` is laid out by name, so `end` comes first"
        );
        assert_ne!(range.start, range.end);
        assert_ne!(range.next, range.range);
        assert!(
            table.layouts().array_len.as_index() < 4,
            "`array` has four fields, so `len` is one of them"
        );
    }

    /// A function std does not declare must resolve to nothing, so that a user function named like
    /// a std one gains no semantics.
    #[test]
    fn a_user_function_is_not_known() {
        let mut session = CompilerSession::new();
        session.emit_mir("known", "fn array_len(a: int) -> int { a }");
        let table = known_callees(&session);
        let (module_id, module) = session
            .modules()
            .get_by_path(&Path::single_str("known"))
            .expect("the module was just compiled");
        let local = module
            .get_local_function_id(ustr("array_len"))
            .expect("the user function was declared");
        assert_eq!(
            table.resolve(FunctionId::new(module_id, local), |_| None),
            None,
            "a user function sharing a std name must not be treated as the std one"
        );
    }
}
