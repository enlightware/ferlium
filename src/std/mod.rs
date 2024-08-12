use crate::module::{Module, Modules, Use};

use ustr::ustr;

pub mod array;
pub mod iterator;
pub mod logic;
pub mod math;
pub mod option;
pub mod range;

pub fn std_module() -> Module {
    let mut module = Module::default();
    logic::add_to_module(&mut module);
    math::add_to_module(&mut module);
    range::add_to_module(&mut module);
    array::add_to_module(&mut module);
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
