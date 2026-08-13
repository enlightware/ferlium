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
//! Ferlium keeps integer arithmetic, integer comparison and array indexing as ordinary calls into
//! std; MIR has no arithmetic operations of its own. Constant folding copes with that by *running*
//! a call ([`const_eval`](crate::mir::const_eval)), which needs every argument known. Range
//! reasoning needs the opposite: the meaning of a call whose arguments are **not** known, so that
//! `i + 1` relates to `i` and `i < len` refines a branch. This table is where that meaning is
//! attached to a callee, and it is the only place in the optimizer that hard-codes std identities.
//!
//! **Identity, not shape.** A callee qualifies by being the very function std declares — resolved
//! once through the trait tables and the module's function names — never by matching a name, a
//! signature or a body. A user function called `add` is a different `FunctionId` and gets no
//! semantics from here.
//!
//! **Purity is not asserted here.** Every entry names what a call *computes*; whether a call may be
//! moved, merged or removed remains a question for its inferred effects, which a consumer must
//! check for itself. Nothing in this table overrides them.
//!
//! **A specialization resolves to its original.** Optimization preserves semantics, so a
//! specialized copy of a known callee is still that callee. Every entry below is additionally
//! *instantiation-independent* — `array_len` reads the same field at every element type, and the
//! rest are concrete already — which is why canonicalizing to the original needs no accompanying
//! type check. An entry whose meaning depended on the instantiation could not be admitted without
//! one, and none is.
//!
//! The consumers are the range-reasoning passes; the items here are exercised by the tests below
//! until those land.
#![allow(dead_code)]

use rustc_hash::FxHashMap;
use ustr::ustr;

use crate::{
    Modules,
    module::{FunctionId, LocalFunctionId, Module, trait_impl::ConcreteTraitImplKey},
    std::{
        STD_MODULE_ID,
        core_traits_names::{ITERATOR_TRAIT_NAME, NUM_TRAIT_NAME, ORD_TRAIT_NAME},
        math::int_type,
    },
    types::r#type::Type,
};

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
    /// `array_len(array)` — the array's element count, which is its `len` field.
    ArrayLen,
    /// `array_resolve_index(index, len)` — `index` when `0 <= index < len`, `len + index` when
    /// `-len <= index < 0`, and a panic otherwise.
    ///
    /// The panic is why this is fallible, and removing it once the index is proved in range is the
    /// point of proving it.
    ArrayResolveIndex,
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

/// The known std callees, keyed by identity.
///
/// Built once against a session's std module. Nothing here depends on the module being optimized,
/// so one table serves every module of a session.
pub(crate) struct KnownCallees {
    by_id: FxHashMap<FunctionId, KnownCallee>,
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
        let entries = [
            (
                resolver.method(NUM_TRAIT_NAME, int_type(), "add"),
                KnownCallee::IntAdd,
            ),
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
            (resolver.function("array_len"), KnownCallee::ArrayLen),
            (
                resolver.function("array_resolve_index"),
                KnownCallee::ArrayResolveIndex,
            ),
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

    /// A std type with no type arguments, named the way source names it.
    fn named_type(&self, name: &str) -> Type {
        let name = ustr(name);
        let def = self
            .std_module
            .get_type_def_id(name)
            .unwrap_or_else(|| panic!("std declares no type `{name}`"));
        Type::named(def, [])
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
            10,
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
