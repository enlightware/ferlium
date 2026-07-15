pub mod function;
pub mod instruction;
pub mod interpreter;
pub mod value;

pub use function::{BlockId, Function, Parameter, ParameterTag};
pub use instruction::{Instruction, InstructionId, InstructionKind, InstructionResult};
pub use value::{ParameterId, Value};
