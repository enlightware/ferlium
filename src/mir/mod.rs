pub(crate) mod builder;
pub(crate) mod const_eval;
pub(crate) mod edit;
pub mod function;
pub mod interpreter;
pub mod operation;
pub mod terminator;
pub mod value;
#[cfg(any(debug_assertions, test))]
pub(crate) mod verify;

pub use function::{BasicBlock, BlockId, Function, Parameter, ParameterKind};
pub use operation::{Operation, OperationKind, OperationResult};
pub use value::{ParameterId, Value, ValueId};
