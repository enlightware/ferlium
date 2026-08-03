// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
//! Rewriting support for canonical MIR functions.
//!
//! A canonical [`Function`](crate::mir::Function) is immutable, so a pass produces a new function
//! rather than editing one in place: it decomposes the input and reassembles it through
//! [`FunctionBuilder`](crate::mir::builder::FunctionBuilder), which reasserts every canonical
//! invariant (and, in debug and test builds, runs the full MIR verifier) at
//! [`finish`](crate::mir::builder::FunctionBuilder::finish).
//!
//! Only the identity rewrite exists today. It is the substrate the partial-evaluation passes build
//! on, and on its own it is the check that MIR is rewritable at all: every function the emitter
//! produces must survive a decompose/reassemble round trip unchanged. See
//! `doc/plans/partial-evaluation.md`.

mod rebuild;

pub(crate) use rebuild::rebuild_function;
