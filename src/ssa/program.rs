use std::collections::HashMap;
use ustr::Ustr;

use crate::{ssa};

/// A Ferlium program expressed in SSA form.
pub struct Program {

  /// The functions in the program.
  functions: HashMap<Ustr, ssa::Function>,

}

impl Program {

  /// Creates an empty program.
  pub fn new() -> Self {
    Program { functions: HashMap::new() }
  }

  /// Adds the declaration of a function having the given `name` iff such a function has not been
  /// declared in `self` yet.
  pub fn declare(&mut self, name: Ustr) -> &mut ssa::Function {
    self.functions.entry(name).or_insert(ssa::Function::new(name))
  }

  /// Adds the definition of `f` this this program.
  ///
  /// `f` is declared if it was not already. Otherwise, the definition of the existing function is
  /// set to that of `f`.
  pub fn set_definition(&mut self, f: ssa::Function) -> &ssa::Function {
    let g = self.declare(f.name);
    *g = f;
    g
  }

}
