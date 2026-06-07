pub mod function;
pub mod instruction;
pub mod program;
pub mod value;

pub use function::{ArgumentPassing, BlockIdentity, Function, Parameter, ParameterKind};
pub use instruction::{Instruction, InstructionIdentity, InstructionResult};
pub use program::Program;
pub use value::Value;
