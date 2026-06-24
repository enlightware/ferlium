pub mod function;
pub mod instruction;
pub mod interpreter;
pub mod value;

pub use function::{BlockIdentity, Function, Parameter, ParameterTag};
pub use instruction::{Instruction, InstructionIdentity, InstructionResult, InstructionView};
pub use value::Value;
