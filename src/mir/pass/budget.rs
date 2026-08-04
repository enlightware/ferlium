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
//! threshold. Changing one of these is a user-visible change; the fold report cites them by name so
//! a user can see which one they hit.
//!
//! **Every budget here is per function.** There is deliberately no module- or session-wide budget:
//! a global one would make whether a function is optimized depend on how much work unrelated
//! functions consumed first, which is exactly the fragility above. Compile time therefore stays
//! linear in function count with a predictable constant. The compile-time evaluation budgets — fuel,
//! call depth, environment cells — live with the engine that spends them, in
//! [`crate::mir::const_eval`].
//!
//! See `doc/plans/partial-evaluation.md`.

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
/// stability requirement in `doc/plans/partial-evaluation.md`.
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
