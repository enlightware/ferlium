pub mod function;
pub mod instruction;
pub mod interpreter;
pub mod value;

pub use function::{BlockIdentity, Function, Parameter, ParameterTag};
pub use instruction::{Instruction, InstructionIdentity, InstructionKind, InstructionResult};
pub use value::{ParameterId, Value};
