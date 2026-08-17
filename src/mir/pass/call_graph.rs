// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
//! The call graph of one module, and the order an interprocedural pass walks it in.
//!
//! Every pass before this one is strictly intra-function. A summary like "which parameter is this
//! addressor's result rooted in" cannot be: `array_index` answers it only once `buffer_slot` has,
//! and a recursive group answers it only about itself. That needs the call graph condensed into
//! strongly connected components and walked callees-first, which is what this provides.
//!
//! **One module.** Module compilation is independent and cannot touch another module, so the graph
//! never spans one: a callee in a dependency is not a node here, and its summary is read from that
//! module's artifacts. Safe for the same reason cross-module specialization is — a dependency's
//! revision is immutable, so its bodies cannot change underneath.
//!
//! Exercised only by its own tests until the provenance summary consumes it; remove the allow below
//! then, as `const_eval.rs` did when folding started calling it.
#![allow(dead_code)]

use crate::{
    graph::{self, Node},
    mir::{self, Function, terminator::TerminatorKind},
    module::{LocalFunctionId, ModuleId, id::Id},
};

/// One function's outgoing edges, as indices into [`CallGraph::nodes`].
///
/// `u32` like every other index in the compiler — `LocalFunctionId` and friends are `NonMaxU32`, and
/// `graph::Node` only asks its index to be `TryInto<usize>`. The solver widens on the way into a
/// slice; the edge list has no reason to be stored double-width.
struct CallNode {
    callees: Vec<u32>,
}

impl Node for CallNode {
    type Index = u32;

    fn neighbors(&self) -> impl Iterator<Item = u32> {
        self.callees.iter().copied()
    }
}

/// Which functions of a module call which, over one artifact stage.
///
/// Indices are positions in the slice the graph was built from, which is a module's function table:
/// index *i* is [`LocalFunctionId::from_index(i)`], in [`CallGraph::module`]. The public API speaks
/// `LocalFunctionId`; the bare index inside does not leave this file. A function the stage has no body for — a native,
/// or a slot the table left empty — is a node with no outgoing edges rather than an absent one, so
/// the indices keep lining up.
pub(crate) struct CallGraph {
    module: ModuleId,
    nodes: Vec<CallNode>,
}

impl CallGraph {
    /// Builds the graph of `functions`, keeping only edges that stay inside `module`.
    ///
    /// **An edge for every function-valued operand, not only a call's callee.** `clone` and `drop`
    /// name functions at different operand positions, so scanning for the value rather than the
    /// position cannot miss one as those kinds grow. It over-approximates — a function merely
    /// *mentioned* gets an edge — and that is the safe direction here: a spurious edge can only
    /// merge more functions into one component, which makes a summary more conservative, never
    /// less.
    ///
    /// `build_closure` stores its target in the operation kind rather than an operand and therefore
    /// contributes no edge here. Constructing a closure does not invoke that target; a consumer
    /// concerned with a later indirect call must reject that call independently.
    ///
    /// A call with no statically known callee contributes no edge, which is why this graph alone
    /// cannot answer reachability. A consumer needing that has to add its own conservatism.
    pub(crate) fn of_module(functions: &[Option<Function>], module: ModuleId) -> Self {
        let nodes = functions
            .iter()
            .map(|function| CallNode {
                callees: match function {
                    Some(function) => callees_within(function, module),
                    None => Vec::new(),
                },
            })
            .collect();
        Self { module, nodes }
    }

    /// The module these indices address.
    ///
    /// Carried once here rather than on every edge, which is why an edge is a bare index: the
    /// module is invariant across the whole graph, and repeating it per edge would be both larger
    /// and no safer. What it is *not* is optional — a local index means nothing without it, and a
    /// consumer building a [`FunctionId`] must take it from here.
    pub(crate) fn module(&self) -> ModuleId {
        self.module
    }

    pub(crate) fn len(&self) -> usize {
        self.nodes.len()
    }

    /// The functions `id` calls within this module.
    pub(crate) fn callees(
        &self,
        id: LocalFunctionId,
    ) -> impl Iterator<Item = LocalFunctionId> + '_ {
        self.nodes[id.as_index()]
            .callees
            .iter()
            .map(|&index| LocalFunctionId::from_index(index as usize))
    }

    /// The module's functions grouped into strongly connected components, **callees first**.
    ///
    /// The order a bottom-up summary is computed in: when a component is reached, every component
    /// it calls has already been summarized, so only the calls *within* it are still unknown. A
    /// component of more than one function is a recursive group, and a summary over it has to
    /// iterate to a fixpoint — being handed the group rather than its members one at a time is the
    /// point of condensing.
    pub(crate) fn components_callees_first(&self) -> Vec<Vec<LocalFunctionId>> {
        let sccs = graph::find_strongly_connected_components(&self.nodes);
        let mut sorted = graph::topological_sort_sccs(&self.nodes, &sccs);
        // `topological_sort_sccs` puts callers first, which is the order for propagating *down*
        // from callers. A summary flows the other way.
        sorted.reverse();
        sorted
            .into_iter()
            .map(|component| {
                component
                    .into_iter()
                    .map(|index| LocalFunctionId::from_index(index as usize))
                    .collect()
            })
            .collect()
    }
}

/// Every function of `module` that `function` names, as graph indices.
fn callees_within(function: &Function, module: ModuleId) -> Vec<u32> {
    let mut callees = Vec::new();
    let mut record = |operand: &mir::Value| {
        if let mir::Value::Function(callee) = operand
            && callee.module == module
        {
            let index = callee.function.as_index() as u32;
            if !callees.contains(&index) {
                callees.push(index);
            }
        }
    };
    for block in function.blocks() {
        let block = function.block(block);
        let operations = block
            .operations()
            .iter()
            .chain(match &block.terminator().kind {
                TerminatorKind::Invoke { operation, .. } => Some(operation),
                _ => None,
            });
        for operation in operations {
            for operand in operation.operands.iter() {
                record(operand);
            }
        }
    }
    callees
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CompilerSession, ExecutionTarget, MirOptimization, module::Path};
    use ustr::ustr;

    /// The module's raw MIR as a graph, plus a lookup from source name to local id.
    fn graph_of(src: &str) -> (CallGraph, impl Fn(&str) -> LocalFunctionId) {
        let mut session = CompilerSession::new();
        let module_id = session
            .compile_for(
                ExecutionTarget::Mir,
                src,
                "test",
                Path::single_str("call_graph"),
            )
            .expect("the test source must compile")
            .module_id;
        let graph = {
            let artifacts = session
                .mir_artifacts_for(module_id, MirOptimization::Disabled)
                .expect("raw MIR must be prepared");
            CallGraph::of_module(artifacts.bodies(), module_id)
        };
        let lookup = move |name: &str| {
            session
                .expect_fresh_module(module_id)
                .get_local_function_id(ustr(name))
                .unwrap_or_else(|| panic!("no function named {name}"))
        };
        (graph, lookup)
    }

    #[test]
    fn a_call_becomes_an_edge() {
        let (graph, id) =
            graph_of("fn leaf(x: int) -> int { x }\nfn root(x: int) -> int { leaf(x) }");
        let callees: Vec<_> = graph.callees(id("root")).collect();
        assert!(
            callees.contains(&id("leaf")),
            "root must have an edge to leaf, got {callees:?}"
        );
    }

    /// Callees first is the whole reason this order exists: a summary of `root` needs `leaf`'s.
    #[test]
    fn components_put_callees_before_callers() {
        let (graph, id) =
            graph_of("fn leaf(x: int) -> int { x }\nfn root(x: int) -> int { leaf(x) }");
        let order = graph.components_callees_first();
        let position = |wanted: LocalFunctionId| {
            order
                .iter()
                .position(|component| component.contains(&wanted))
                .expect("every function is in a component")
        };
        assert!(
            position(id("leaf")) < position(id("root")),
            "leaf must be summarized before root"
        );
    }

    /// A recursive group arrives as one component, which is what a fixpoint is run over. A
    /// single-function order could not express it.
    #[test]
    fn mutually_recursive_functions_share_a_component() {
        let (graph, id) = graph_of(
            "fn is_even(n: int) -> bool { if n == 0 { true } else { is_odd(n - 1) } }\n\
             fn is_odd(n: int) -> bool { if n == 0 { false } else { is_even(n - 1) } }",
        );
        let order = graph.components_callees_first();
        let component = order
            .iter()
            .find(|component| component.contains(&id("is_even")))
            .expect("is_even is in a component");
        assert!(
            component.contains(&id("is_odd")),
            "mutual recursion must condense into one component, got {component:?}"
        );
    }

    /// Every function is in exactly one component, including ones with no body — otherwise indices
    /// stop lining up with the function table.
    #[test]
    fn every_function_appears_exactly_once() {
        let (graph, _) = graph_of("fn a(x: int) -> int { x }\nfn b(x: int) -> int { a(x) }");
        let total: usize = graph.components_callees_first().iter().map(Vec::len).sum();
        assert_eq!(total, graph.len());
    }
}
