pub mod function;
pub mod instruction;
pub mod interpreter;
pub mod value;
#[cfg(any(debug_assertions, test))]
pub(crate) mod verify;

pub use function::{BlockId, Function, Parameter, ParameterTag};
pub use instruction::{Instruction, InstructionId, InstructionKind, InstructionResult};
pub use value::{ParameterId, Value};
