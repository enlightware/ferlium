// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
//! Where an addressor's returned place is rooted.
//!
//! `AddressorPlace` promises the place a subscript hands back is *caller-rooted* — that it outlives
//! the call — but not **which** of the caller's objects it points into. So nothing can reason that a
//! write through `array_index(a, i)`'s result is a write into `a`, nor, which is what a
//! common-subexpression elimination needs, that such a write cannot move `a`'s other elements.
//!
//! The missing fact is one number: the parameter the result is rooted in. It is **derived, not
//! declared** — a returned place traces back through `subfield`, `load` and nested addressor calls
//! to exactly one root, and if that root is not a parameter the accessor was already broken, since
//! its own frame ends at the return. Being derived, it can be recomputed and checked rather than
//! trusted.
//!
//! Natives are the exception and the only place the fact is asserted: `buffer_slot` computes its
//! address in Rust, so it declares [`CallableDefinition::result_rooted_in`] instead. That is the one
//! surface where this can be wrong.
//!
//! Exercised only by its own tests until common-subexpression elimination consumes it; remove the
//! allow below then.
#![allow(dead_code)]

use rustc_hash::FxHashMap;

use crate::{
    mir::{self, Function, OperationKind, ParameterKind, terminator::TerminatorKind},
    module::{FunctionId, LocalFunctionId, ModuleEnv, ModuleId, id::Id},
    types::r#type::CallResultConvention,
};

use super::call_graph::CallGraph;

/// Which of a function's parameters its returned place points into.
///
/// Only meaningful for a function returning through `AddressorPlace`; anything else has no place to
/// be rooted anywhere.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum ResultProvenance {
    /// The result points into the pointee of this **visible argument**.
    ///
    /// An argument index rather than a MIR parameter index, because MIR counts hidden evidence
    /// first and a native declares this in argument terms. Keeping one vocabulary is what lets a
    /// derived answer and a declared one be compared, stored and read across a module boundary
    /// without a translation nobody remembers to apply.
    Argument(u32),
    /// Not derivable. Always sound to assume, and what every consumer must fall back to.
    Unknown,
}

/// One module's result provenances, indexed like its function table.
#[derive(Clone, Default)]
pub(crate) struct Provenances {
    of: Vec<ResultProvenance>,
}

impl Provenances {
    /// Derives the provenance of every function in `bodies`, callees before callers.
    ///
    /// A component of more than one function is a recursive group, and its members are iterated to
    /// a fixpoint from `Unknown` — the *conservative* start, so that a cycle which never resolves
    /// stays `Unknown` rather than inventing a root for itself.
    /// `external` answers for a callee in another module, whose summary was computed when *that*
    /// module's artifacts were built — dependencies are always built first, so the answer is there.
    pub(crate) fn of_module(
        bodies: &[Option<Function>],
        module: ModuleId,
        env: ModuleEnv<'_>,
        external: &dyn Fn(FunctionId) -> ResultProvenance,
    ) -> Self {
        let graph = CallGraph::of_module(bodies, module);
        let mut of = vec![ResultProvenance::Unknown; bodies.len()];

        for component in graph.components_callees_first() {
            // A single function cannot depend on itself here: a self-call would have put it in a
            // component of its own size, so one pass settles it.
            let mut changed = true;
            while changed {
                changed = false;
                for &id in &component {
                    let derived = match &bodies[id.as_index()] {
                        Some(body) => derive(body, module, &of, external, env),
                        // No body: a native, which declares the fact instead.
                        None => declared(id, env),
                    };
                    if derived != of[id.as_index()] {
                        of[id.as_index()] = derived;
                        changed = true;
                    }
                }
                if component.len() == 1 {
                    break;
                }
            }
        }
        Self { of }
    }

    pub(crate) fn get(&self, id: LocalFunctionId) -> ResultProvenance {
        self.of
            .get(id.as_index())
            .copied()
            .unwrap_or(ResultProvenance::Unknown)
    }
}

/// What a native declares about where its result points.
fn declared(id: LocalFunctionId, env: ModuleEnv<'_>) -> ResultProvenance {
    match env
        .current
        .get_function_by_id(id)
        .and_then(|function| function.definition.result_rooted_in)
    {
        Some(index) => ResultProvenance::Argument(index),
        None => ResultProvenance::Unknown,
    }
}

/// Where `body` roots the place it stores into its `@ret` parameter.
///
/// `known` supplies the provenance of callees already summarized; a callee in another module, or
/// one not yet settled inside a recursive group, reads as `Unknown` and makes this `Unknown` too.
fn derive(
    body: &Function,
    module: ModuleId,
    known: &[ResultProvenance],
    external: &dyn Fn(FunctionId) -> ResultProvenance,
    env: ModuleEnv<'_>,
) -> ResultProvenance {
    let parameters = body.parameters();
    if !parameters
        .last()
        .is_some_and(|parameter| matches!(parameter.kind, ParameterKind::Return))
    {
        return ResultProvenance::Unknown;
    }
    let ret = mir::ParameterId::from_index(parameters.len() - 1);

    // MIR parameter index -> visible argument index. Hidden evidence comes first and is not an
    // argument, so a root landing on one has no argument to name and stays unknown.
    let argument_of = |id: mir::ParameterId| -> Option<u32> {
        let index = id.as_index();
        matches!(parameters.get(index)?.kind, ParameterKind::Parameter(_)).then(|| {
            parameters[..index]
                .iter()
                .filter(|parameter| matches!(parameter.kind, ParameterKind::Parameter(_)))
                .count() as u32
        })
    };

    // Which parameter each register's place points into, filled in as the body is walked. A
    // register absent from the map is one the trace could not follow, which is `Unknown`.
    let mut roots: FxHashMap<mir::ValueId, u32> = FxHashMap::default();
    let mut result: Option<ResultProvenance> = None;

    for block_id in body.blocks() {
        let block = body.block(block_id);
        let operations = block
            .operations()
            .iter()
            .chain(match &block.terminator().kind {
                TerminatorKind::Invoke { operation, .. } => Some(operation),
                _ => None,
            });
        for operation in operations {
            let root_of = |operand: &mir::Value, roots: &FxHashMap<mir::ValueId, u32>| match operand
            {
                mir::Value::Parameter(id) => argument_of(*id),
                mir::Value::Register(id) => roots.get(id).copied(),
                _ => None,
            };
            match &operation.kind {
                // A field's address is rooted wherever its base is.
                OperationKind::Subfield { .. } => {
                    if let (Some(id), Some(root)) = (
                        operation.result_id(),
                        root_of(&operation.operands[0], &roots),
                    ) {
                        roots.insert(id, root);
                    }
                }
                // Dereferencing a slot yields whatever a call wrote into it.
                OperationKind::Load => {
                    if let (Some(id), Some(root)) = (
                        operation.result_id(),
                        root_of(&operation.operands[0], &roots),
                    ) {
                        roots.insert(id, root);
                    }
                }
                // A nested addressor writes a place into the ret-out operand this call passes, and
                // that place is rooted wherever *this* call's corresponding argument is.
                OperationKind::Call { ty, .. } => {
                    if ty.result_convention != CallResultConvention::ADDRESSOR_PLACE {
                        continue;
                    }
                    let mir::Value::Function(callee) = &operation.operands[0] else {
                        continue;
                    };
                    // A callee in this module is being summarized alongside this one; one in
                    // another module was summarized when that module's artifacts were built.
                    let callee_provenance = if callee.module == module {
                        known[callee.function.as_index()]
                    } else {
                        external(*callee)
                    };
                    let ResultProvenance::Argument(index) = callee_provenance else {
                        continue;
                    };
                    // Operands are `[callee, hidden evidence…, visible arguments…, ret-out]`, so a
                    // visible argument index has to skip the callee and whatever evidence precedes
                    // the arguments. The evidence count is what the operand list has left over.
                    let visible = ty.fn_ty.args.len();
                    let Some(hidden) = operation.operands.len().checked_sub(visible + 2) else {
                        continue;
                    };
                    let Some(argument) = operation.operands.get(1 + hidden + index as usize) else {
                        continue;
                    };
                    let Some(root) = root_of(argument, &roots) else {
                        continue;
                    };
                    let Some(out) = operation.operands.last() else {
                        continue;
                    };
                    if let mir::Value::Register(id) = out {
                        roots.insert(*id, root);
                    }
                }
                // The return: whatever is stored into `@ret` is the answer.
                OperationKind::Store => {
                    if operation.operands[1] != mir::Value::Parameter(ret) {
                        continue;
                    }
                    let stored = match root_of(&operation.operands[0], &roots) {
                        Some(root) => ResultProvenance::Argument(root),
                        None => ResultProvenance::Unknown,
                    };
                    // Two stores that disagree leave the caller unable to say which, so neither
                    // answer is usable.
                    result = Some(match result {
                        None => stored,
                        Some(previous) if previous == stored => stored,
                        Some(_) => ResultProvenance::Unknown,
                    });
                }
                _ => {}
            }
        }
    }
    let _ = env;
    result.unwrap_or(ResultProvenance::Unknown)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CompilerSession, ExecutionTarget, MirOptimization, module::Path};
    use ustr::ustr;

    /// Provenance over a compiled module, plus a lookup from source name to local id.
    fn provenance_of(src: &str) -> (Provenances, impl Fn(&str) -> LocalFunctionId) {
        let mut session = CompilerSession::new();
        let module_id = session
            .compile_for(
                ExecutionTarget::Mir,
                src,
                "test",
                Path::single_str("provenance"),
            )
            .expect("the test source must compile")
            .module_id;
        let provenances = {
            let modules = session.raw_modules();
            let module = session.expect_fresh_module(module_id);
            let artifacts = session
                .mir_artifacts_for(module_id, MirOptimization::Disabled)
                .expect("raw MIR must be prepared");
            Provenances::of_module(
                artifacts.bodies(),
                module_id,
                ModuleEnv::new(module, modules),
                &|_| ResultProvenance::Unknown,
            )
        };
        // Generated members carry a `#subscript:` hash, so a prefix match is what names them.
        let lookup = move |name: &str| {
            let module = session.expect_fresh_module(module_id);
            module
                .get_local_function_id(ustr(name))
                .or_else(|| {
                    module.def_table.iter().find_map(|(def, defined)| {
                        defined
                            .filter(|defined| defined.starts_with(name))
                            .and_then(|_| def.kind.as_function().copied())
                    })
                })
                .unwrap_or_else(|| panic!("no function named {name}"))
        };
        (provenances, lookup)
    }

    /// The base case: the accessor hands back a field of its receiver.
    #[test]
    fn an_addressor_is_rooted_in_its_receiver() {
        let (provenances, id) = provenance_of(
            "struct Pair { a: int, b: int }\n\
             subscript first(p: &mut Pair, i: int) -> int { ref mut { return p.a } }",
        );
        assert_eq!(
            provenances.get(id("first::ref_mut")),
            ResultProvenance::Argument(0),
            "the place is a field of parameter 0"
        );
    }

    /// The case the whole analysis exists for, and the one that needs the call graph: over the
    /// standard library, `array_index::ref_mut` roots in its array — but only by way of
    /// `buffer_slot`, a native whose address computation is in Rust and which therefore *declares*
    /// its own root. One derived link on top of one declared one.
    #[test]
    fn a_nested_addressor_inherits_the_root_through_the_callee() {
        let session = CompilerSession::new();
        let (std_id, _) = session
            .modules()
            .get_by_path(&Path::single_str("std"))
            .expect("the standard library is always registered");
        crate::compiler::ensure_mir_artifacts(session.raw_modules(), std_id);
        let modules = session.raw_modules();
        let module = session.expect_fresh_module(std_id);
        let artifacts = session
            .mir_artifacts_for(std_id, MirOptimization::Disabled)
            .expect("std raw MIR must be prepared");
        let provenances = Provenances::of_module(
            artifacts.bodies(),
            std_id,
            ModuleEnv::new(module, modules),
            &|_| ResultProvenance::Unknown,
        );

        let named = |name: &str| {
            module
                .def_table
                .iter()
                .find_map(|(def, defined)| {
                    defined
                        .filter(|defined| defined.starts_with(name))
                        .and_then(|_| def.kind.as_function().copied())
                })
                .unwrap_or_else(|| panic!("std has no `{name}`"))
        };
        assert_eq!(
            provenances.get(named("buffer_slot::ref_mut")),
            ResultProvenance::Argument(0),
            "the native declares its root"
        );
        assert_eq!(
            provenances.get(named("array_index::ref_mut")),
            ResultProvenance::Argument(0),
            "and the accessor above it derives the same root through it"
        );
    }

    /// What storing the summaries buys: a user accessor wrapping `std`'s array indexing roots in
    /// its own array, which needs `std`'s answer read back rather than recomputed. Asked through
    /// `MirArtifacts`, the way a consumer will ask.
    #[test]
    fn an_accessor_over_a_dependency_inherits_its_root() {
        let mut session = CompilerSession::new();
        let module_id = session
            .compile_for(
                ExecutionTarget::Mir,
                "subscript first(a: &mut [int]) -> int { ref mut { return a[0] } }",
                "test",
                Path::single_str("provenance"),
            )
            .expect("the test source must compile")
            .module_id;
        let module = session.expect_fresh_module(module_id);
        let id = module
            .def_table
            .iter()
            .find_map(|(def, defined)| {
                defined
                    .filter(|defined| defined.starts_with("first::ref_mut"))
                    .and_then(|_| def.kind.as_function().copied())
            })
            .expect("the module defines `first`");
        let artifacts = session
            .mir_artifacts_for(module_id, MirOptimization::Disabled)
            .expect("raw MIR must be prepared");
        assert_eq!(
            artifacts.result_provenance(id),
            ResultProvenance::Argument(0),
            "the root must come through std's `array_index`, whose summary is stored"
        );
    }

    /// A function that returns a value rather than a place has nowhere to be rooted.
    #[test]
    fn a_value_returning_function_has_no_provenance() {
        let (provenances, id) = provenance_of("fn double(x: int) -> int { x + x }");
        assert_eq!(provenances.get(id("double")), ResultProvenance::Unknown);
    }
}
