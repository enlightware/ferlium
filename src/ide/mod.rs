// Copyright 2026 Enlightware GmbH
// SPDX-License-Identifier: Apache-2.0

mod annotations;
mod compiler;
mod diagnostics;
mod execution;
mod position_index_lookup;
mod signatures;

pub use annotations::AnnotationData;
pub use compiler::Compiler;
pub use diagnostics::{CompilationReport, ErrorData};
pub use execution::{ExecutionErrorData, ExecutionResult, IrText, TextSourceMapEntry};
pub use position_index_lookup::PositionEncoding;
pub use signatures::FunctionSignature;
