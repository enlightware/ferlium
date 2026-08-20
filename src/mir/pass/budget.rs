// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
//! Every budget the optimization passes obey, in one place.
//!
//! These bound compiler work, not program behaviour: exhausting one costs an optimization, never a
//! result. They are deliberately generous and stable, because a user who annotates a hot path to
//! make it foldable should not lose the speedup when an unrelated edit pushes the function across a
//! threshold. Changing one of these is a user-visible change, and the fold report cites the
//! inlining budgets by name so a user can see which one they hit.
//!
//! **Every budget here is spent within one unit of work, and none is session-wide.** Most are per
//! function; the branch-forwarding pair is narrower still, bounding one rewrite candidate inside a
//! function; and [`specialization_limit`] is per module, because a specialization is shared between
//! every call site that asks for it. A session-wide budget would make whether a function is
//! optimized depend on how much work unrelated functions consumed first, which is exactly the
//! fragility above. Module-wide generation limits use either a floor or a linearly scaled allowance
//! over the stable input population, whichever is larger; the floor is not added to the scaled
//! allowance, and generated output never enlarges its own budget. Compile time therefore stays
//! linear in input size with a predictable constant. The compile-time evaluation budgets —
//! fuel, call depth, environment cells — live with the engine that spends them, in
//! [`crate::mir::const_eval`].

/// How many fold/inline rounds a single function may go through.
///
/// Folding and inlining feed each other — inlining a generic callee lets folding resolve its
/// `dict_entry`s, which turns indirect calls direct, which offers new inlining candidates — so one
/// pass of each is not enough. In practice the chain is short; this bounds the outer loop of the
/// driver, and is the last of the three bounds that make optimization terminate (the other two
/// being the monotone lattice and the inlining growth budget).
pub const MAX_ROUNDS: usize = 4;

/// The largest callee, in operations, that inlining will copy into a caller.
///
/// Generous rather than tuned: the point of inlining here is to hand folding a body whose arguments
/// are known, and the callees that pays off for are small — accessors, arithmetic helpers, trait
/// method bodies. A cap that a routine edit can cross would make the speedup fragile, which is the
/// stability requirement that a user who annotates a hot path must not lose the optimization to
/// an unrelated edit.
pub const INLINE_CALLEE_OPERATIONS: usize = 32;

/// How much inlining may grow one function, in operations, beyond the size it had *before*
/// optimization started.
///
/// Bounds the whole of optimization rather than each site or each round: a function full of small
/// calls would otherwise inline all of them, and measuring against the current size would let each
/// round grant the budget afresh. Together with the callee cap this is what bounds code growth, and
/// it is public because a budget change is a user-visible change — the optimization report cites
/// these by name.
pub const INLINE_FUNCTION_GROWTH: usize = 128;

/// Largest owned string result one compile-time evaluation may embed as a constructive recipe.
///
/// A string is not stored in the constant pool: reification interns its immutable text as a
/// `StaticStr` and emits a run-time `string_from_static` construction. Bounding the text still
/// matters because interning makes it process-lifetime compiler data and because generated MIR
/// should not hide an arbitrarily large result behind one folded call.
pub const REIFIED_STRING_BYTES: usize = 64 * 1024;

/// How many blocks one boolean-branch forwarding may walk back through to find the stores reaching
/// a join.
///
/// A short-circuit `or`/`and` puts its arms one or more store-free forwarding blocks above the
/// join, so the search cannot stop at the immediate predecessors. It stays small because the region
/// it crosses is the lowering of one source-level boolean expression, not a general slice.
pub const FORWARD_BOOLEAN_BLOCKS: usize = 16;

/// How many edge-cleanup operations that forwarding may replay onto one arm.
///
/// Every block the rewrite removes from a path carries its `stack_restore`s onto each arm that used
/// to run them, so a long path duplicates code into several arms. This bounds that growth.
pub const FORWARD_BOOLEAN_REPLAYED_OPERATIONS: usize = 8;

/// Minimum number of specialized bodies one module's optimization may create.
///
/// Specialization cascades by design: monomorphizing a caller makes the dictionaries it forwards
/// constant, which brings its own generic calls into reach, which may specialize further. The cache
/// bounds the *breadth* — one body per distinct instantiation rather than per call site — but not
/// the depth, so [`specialization_limit`] bounds the total.
///
/// Per module rather than per function, unlike the inlining budgets, because a specialization is
/// shared between every call site that asks for it: charging it to whichever function happened to
/// ask first would make the cost depend on optimization order. The floor is deliberately generous
/// for a small entry module which instantiates a deep generic graph imported from dependencies.
pub const MIN_SPECIALIZATIONS: usize = 512;

/// Additional specialization allowance per declared script body.
pub const SPECIALIZATIONS_PER_BODY: usize = 4;

/// How many specialized bodies one module's optimization may create.
///
/// Based only on declared MIR bodies, before optimization creates any output. This keeps generated
/// code linear in stable input size rather than allowing a cascade to fund itself.
pub const fn specialization_limit(declared_bodies: usize) -> usize {
    let scaled = declared_bodies.saturating_mul(SPECIALIZATIONS_PER_BODY);
    if scaled > MIN_SPECIALIZATIONS {
        scaled
    } else {
        MIN_SPECIALIZATIONS
    }
}

/// Minimum number of ownership-taking ABI variants the final whole-module pass may add.
///
/// Variants are cached by `(callee, owned argument set)` and created only for masks observed at
/// profitable call sites. The floor preserves small modules with a wide imported API.
pub const MIN_OWNED_ARGUMENT_VARIANTS: usize = 256;

/// Additional owned-ABI variant allowance per stable source body.
pub const OWNED_ARGUMENT_VARIANTS_PER_BODY: usize = 2;

/// How many ownership-taking ABI variants the final whole-module pass may add.
///
/// The source population is fixed before generation begins. Variants accumulated while the pass
/// runs are deliberately absent, preventing a combinatorial family from funding itself.
pub const fn owned_argument_variant_limit(source_bodies: usize) -> usize {
    let scaled = source_bodies.saturating_mul(OWNED_ARGUMENT_VARIANTS_PER_BODY);
    if scaled > MIN_OWNED_ARGUMENT_VARIANTS {
        scaled
    } else {
        MIN_OWNED_ARGUMENT_VARIANTS
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn module_generation_budgets_have_a_floor_and_scale_linearly() {
        assert_eq!(specialization_limit(0), MIN_SPECIALIZATIONS);
        assert_eq!(specialization_limit(128), MIN_SPECIALIZATIONS);
        assert_eq!(specialization_limit(129), 516);

        assert_eq!(owned_argument_variant_limit(0), MIN_OWNED_ARGUMENT_VARIANTS);
        assert_eq!(
            owned_argument_variant_limit(128),
            MIN_OWNED_ARGUMENT_VARIANTS
        );
        assert_eq!(owned_argument_variant_limit(129), 258);
    }

    #[test]
    fn module_generation_budgets_do_not_overflow() {
        assert_eq!(specialization_limit(usize::MAX), usize::MAX);
        assert_eq!(owned_argument_variant_limit(usize::MAX), usize::MAX);
    }
}
