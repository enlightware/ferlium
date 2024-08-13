// Note: disabled for now until we have a borrow checker
// use crate::{module::Module, value::Value};

// use ustr::ustr;

// pub fn swap(a: &mut Value, b: &mut Value) {
//     std::mem::swap(a, b);
// }

// pub fn add_to_module(to: &mut Module) {
//     to.functions.insert(
//         ustr("swap"),
//         BinaryNativeFnMMP::description_gen0_gen0(swap),
//     );
// }
