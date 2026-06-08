pub mod function;
pub mod instruction;
pub mod program;
pub mod value;

pub use function::{BlockIdentity, Function, Parameter, ParameterTag};
pub use instruction::{Instruction, InstructionIdentity, InstructionResult};
pub use program::Program;
pub use value::Value;
