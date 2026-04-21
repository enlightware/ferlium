pub mod function;
pub mod instruction;
pub mod unit;
pub mod value;

pub use function::{BlockIdentity, Function};
pub use instruction::{Instruction, InstructionIdentity, InstructionResult};
pub use unit::Unit;
pub use value::Value;
