use crate::{
    module::{Module, Modules, Use},
    r#type::Type,
};

use ustr::ustr;

pub mod array;
pub mod flow;
pub mod io;
pub mod iterator;
pub mod logic;
pub mod math;
pub mod mem;
pub mod option;
pub mod range;
pub mod string;

pub fn std_module() -> Module {
    let mut module = Module::default();
    module.types.set(ustr("()"), Type::unit());
    flow::add_to_module(&mut module);
    // mem::add_to_module(&mut module);
    logic::add_to_module(&mut module);
    math::add_to_module(&mut module);
    range::add_to_module(&mut module);
    array::add_to_module(&mut module);
    io::add_to_module(&mut module);
    string::add_to_module(&mut module);
    // option::add_option_functions(&mut module);
    module
}

pub fn new_std_module_env() -> Modules {
    let mut modules: Modules = Default::default();
    modules.insert(ustr("std"), std_module());
    modules
}

pub fn new_module_with_prelude() -> Module {
    let mut new_module = Module::default();
    new_module.uses.push(Use::All(ustr("std")));
    new_module
}
