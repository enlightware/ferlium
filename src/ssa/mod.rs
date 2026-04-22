pub mod function;
pub mod instruction;
pub mod value;

pub use function::{BlockIdentity, Function};
pub use instruction::{Instruction, InstructionIdentity, InstructionResult};
pub use value::Value;
