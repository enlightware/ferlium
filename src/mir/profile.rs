// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.

//! Dynamic, unweighted execution counts for the MIR reference interpreter.
//!
//! A profile records facts — how often each MIR instruction executed — rather than pretending the
//! boxed interpreter supplies a cost model for a future backend. [`MirInstructionCostClass`] gives
//! the report a deliberately rough order: it puts semantic and size-dependent work first so the
//! expensive-looking residue is easy to find, but no weights are attached and the classes must not
//! be summed into a score.
//!
//! An `invoke` contributes two independently useful events: its embedded operation and the
//! `invoke` control transfer. Accordingly, `total()` is a compact event checksum, not a static MIR
//! instruction count or a cost.

use std::{collections::BTreeMap, fmt};

use rustc_hash::FxHashMap;

use crate::{
    mir::{
        Operation, OperationKind, Value,
        interpreter::FunctionKey,
        operation::OperationKindDiscriminant,
        terminator::{TerminatorKind, TerminatorKindDiscriminant},
    },
    types::r#type::Type,
};

/// A rough, backend-oriented ordering of MIR work, from least bounded to cheapest-looking.
///
/// This is an ordinal presentation aid, not a claim that every instruction in one class costs more
/// than every instruction in the next. A small `memcpy` can be cheaper than a call, while a large
/// one can dominate it; a native call can do arbitrary work. Exact counts and their type/callee
/// context remain the evidence.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MirInstructionCostClass {
    Semantic,
    SizeDependent,
    Storage,
    Addressing,
    Scalar,
    Scaffolding,
}

impl MirInstructionCostClass {
    pub const ALL: [Self; 6] = [
        Self::Semantic,
        Self::SizeDependent,
        Self::Storage,
        Self::Addressing,
        Self::Scalar,
        Self::Scaffolding,
    ];

    pub const fn label(self) -> &'static str {
        match self {
            Self::Semantic => "semantic / callee-dependent",
            Self::SizeDependent => "size-dependent",
            Self::Storage => "fixed storage",
            Self::Addressing => "address / evidence",
            Self::Scalar => "scalar / control",
            Self::Scaffolding => "runtime scaffolding",
        }
    }
}

/// Stable aggregation key for an executed MIR operation or terminator.
///
/// `strum::EnumDiscriminants` generates the operation and terminator tags from the IR enums. Calls
/// are the one deliberate refinement: their operand distinguishes direct from indirect dispatch,
/// which the `OperationKind::Call` discriminant alone cannot express.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MirInstructionKind {
    DirectCall,
    IndirectCall,
    Operation(OperationKindDiscriminant),
    Terminator(TerminatorKindDiscriminant),
}

impl MirInstructionKind {
    pub fn label(self) -> String {
        match self {
            Self::DirectCall => "call_direct".to_owned(),
            Self::IndirectCall => "call_indirect".to_owned(),
            Self::Operation(kind) => kind.to_string(),
            Self::Terminator(kind) => kind.to_string(),
        }
    }

    pub const fn cost_class(self) -> MirInstructionCostClass {
        use MirInstructionCostClass as Cost;
        use OperationKindDiscriminant as Op;
        use TerminatorKindDiscriminant as Term;

        match self {
            Self::DirectCall | Self::IndirectCall => Cost::Semantic,
            Self::Operation(
                Op::Project
                | Op::EndProject
                | Op::Clone
                | Op::Drop
                | Op::CloneClosureEnv
                | Op::DropClosureEnv,
            ) => Cost::Semantic,
            Self::Operation(Op::Memcpy | Op::Move | Op::BuildClosure | Op::Variant) => {
                Cost::SizeDependent
            }
            Self::Operation(Op::Alloca | Op::AllocaPlace | Op::Load | Op::Store | Op::Clear) => {
                Cost::Storage
            }
            Self::Operation(
                Op::Subfield | Op::DictEntry | Op::SubscriptMember | Op::BuildSubscript,
            ) => Cost::Addressing,
            Self::Operation(Op::CompareEqual | Op::ExtractTag) => Cost::Scalar,
            Self::Operation(
                Op::StackSave | Op::StackRestore | Op::CheckCallDepth | Op::CheckFuel,
            ) => Cost::Scaffolding,
            // `invoke` is conceptually both a fallible semantic operation and its success/error
            // control transfer. The embedded operation is recorded separately in its own class,
            // so this terminator event represents only the control-transfer half.
            Self::Terminator(
                Term::Goto
                | Term::CondBr
                | Term::Invoke
                | Term::Yield
                | Term::Return
                | Term::PropagateError
                | Term::FailureDuringCleanup,
            ) => Cost::Scalar,
            // Calls are refined into DirectCall or IndirectCall when recorded.
            Self::Operation(Op::Call) => Cost::Semantic,
        }
    }
}

/// Counts indexed by [`MirInstructionKind`].
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MirInstructionCounts(BTreeMap<MirInstructionKind, u64>);

impl MirInstructionCounts {
    pub fn get(&self, kind: MirInstructionKind) -> u64 {
        self.0.get(&kind).copied().unwrap_or(0)
    }

    pub fn total(&self) -> u64 {
        self.0.values().sum()
    }

    pub fn nonzero(&self) -> impl Iterator<Item = (MirInstructionKind, u64)> + '_ {
        self.0.iter().map(|(kind, count)| (*kind, *count))
    }

    fn increment(&mut self, kind: MirInstructionKind) {
        *self.0.entry(kind).or_default() += 1;
    }

    /// Adds another set of counts without attaching weights to either one.
    pub fn merge(&mut self, other: &Self) {
        for (kind, count) in &other.0 {
            *self.0.entry(*kind).or_default() += count;
        }
    }
}

/// Dynamic execution facts gathered by one MIR interpreter run.
#[derive(Clone, Debug, Default)]
pub struct MirExecutionProfile {
    total: MirInstructionCounts,
    by_function: FxHashMap<FunctionKey, MirInstructionCounts>,
    by_type: FxHashMap<(MirInstructionKind, Type), u64>,
}

impl MirExecutionProfile {
    pub fn total(&self) -> &MirInstructionCounts {
        &self.total
    }

    pub fn functions(&self) -> impl Iterator<Item = (FunctionKey, &MirInstructionCounts)> + '_ {
        self.by_function.iter().map(|(key, counts)| (*key, counts))
    }

    /// Counts for operations whose MIR kind carries a concrete type.
    pub fn types(&self) -> impl Iterator<Item = (MirInstructionKind, Type, u64)> + '_ {
        self.by_type
            .iter()
            .map(|((kind, ty), count)| (*kind, *ty, *count))
    }

    pub(crate) fn record_operation(&mut self, function: FunctionKey, operation: &Operation) {
        let discriminant = OperationKindDiscriminant::from(&operation.kind);
        let kind = if discriminant == OperationKindDiscriminant::Call {
            if matches!(operation.operands.first(), Some(Value::Function(_))) {
                MirInstructionKind::DirectCall
            } else {
                MirInstructionKind::IndirectCall
            }
        } else {
            MirInstructionKind::Operation(discriminant)
        };
        self.record(function, kind);

        let ty = match &operation.kind {
            OperationKind::Alloca { ty }
            | OperationKind::Subfield { ty }
            | OperationKind::DictEntry { ty, .. }
            | OperationKind::SubscriptMember { ty, .. }
            | OperationKind::BuildSubscript { ty }
            | OperationKind::Variant { ty, .. }
            | OperationKind::Clone { ty }
            | OperationKind::Drop { ty }
            | OperationKind::BuildClosure { ty, .. }
            | OperationKind::CloneClosureEnv { ty } => Some(*ty),
            OperationKind::AllocaPlace { pointing_to } => Some(*pointing_to),
            _ => None,
        };
        if let Some(ty) = ty {
            *self.by_type.entry((kind, ty)).or_default() += 1;
        }
    }

    pub(crate) fn record_terminator(&mut self, function: FunctionKey, terminator: &TerminatorKind) {
        self.record(
            function,
            MirInstructionKind::Terminator(TerminatorKindDiscriminant::from(terminator)),
        );
    }

    fn record(&mut self, function: FunctionKey, kind: MirInstructionKind) {
        self.total.increment(kind);
        self.by_function
            .entry(function)
            .or_default()
            .increment(kind);
    }
}

impl fmt::Display for MirExecutionProfile {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for class in MirInstructionCostClass::ALL {
            let rows = self
                .total
                .nonzero()
                .filter(|(kind, _)| kind.cost_class() == class)
                .collect::<Vec<_>>();
            if rows.is_empty() {
                continue;
            }
            writeln!(f, "{}:", class.label())?;
            for (kind, count) in rows {
                writeln!(f, "  {:<24} {count:>12}", kind.label())?;
            }
        }
        writeln!(f, "  {:<24} {:>12}", "TOTAL", self.total.total())
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        CompilerSession, ExecutionTarget, MirOptimization, Path, hir::value::Value,
        mir::operation::OperationKindDiscriminant as Op,
        mir::terminator::TerminatorKindDiscriminant as Term,
    };

    use super::{MirInstructionCostClass as Cost, MirInstructionKind as Kind};

    #[test]
    fn instruction_discriminants_are_grouped_by_ordinal_cost() {
        assert_eq!(Kind::Operation(Op::Clone).cost_class(), Cost::Semantic);
        assert_eq!(
            Kind::Operation(Op::Memcpy).cost_class(),
            Cost::SizeDependent
        );
        assert_eq!(Kind::Operation(Op::Store).cost_class(), Cost::Storage);
        assert_eq!(
            Kind::Operation(Op::DictEntry).cost_class(),
            Cost::Addressing
        );
        assert_eq!(Kind::Operation(Op::CompareEqual).cost_class(), Cost::Scalar);
        assert_eq!(Kind::Terminator(Term::Invoke).cost_class(), Cost::Scalar);
        assert_eq!(
            Kind::Operation(Op::StackRestore).cost_class(),
            Cost::Scaffolding
        );
    }

    #[test]
    fn interpreter_profile_counts_operations_terminators_and_functions() {
        let mut session = CompilerSession::new();
        session.set_mir_optimization(MirOptimization::Disabled);
        let module_id = session
            .compile_for(
                ExecutionTarget::Mir,
                "fn twice(x: int) -> int { x + x } fn main(x: int) -> int { let mut y = x; y = twice(y); y }",
                "profile",
                Path::single_str("profile"),
            )
            .unwrap()
            .module_id;
        let entry = session
            .expect_fresh_module(module_id)
            .get_local_function_id(crate::ustr("main"))
            .unwrap();
        let (result, profile) = session
            .run_mir_entry_profiled(module_id, entry, vec![Value::native(21isize)])
            .unwrap();
        assert_eq!(result.into_primitive_ty::<isize>().unwrap(), 42);

        assert!(profile.total().get(Kind::DirectCall) >= 2);
        assert!(
            profile
                .total()
                .nonzero()
                .any(|(kind, _)| matches!(kind, Kind::Operation(_)))
        );
        assert!(
            profile
                .total()
                .nonzero()
                .any(|(kind, _)| matches!(kind, Kind::Terminator(_)))
        );
        assert!(profile.total().total() > 0);
        let attributed: u64 = profile.functions().map(|(_, counts)| counts.total()).sum();
        assert_eq!(attributed, profile.total().total());
    }
}
