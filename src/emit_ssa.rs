use std::mem;

use crate::{
  Location, Modules, containers,
  format::FormatWith,
  hir::{self, Case, NodeArena, value::Value},
  module::{FunctionId, LocalFunctionId, Module, ModuleEnv, TraitImpl, TraitImplId},
  ssa::{self, BlockIdentity, Program},
};

/// Emit the low-level (aka SSA) ferlium IR of `module`.
/// Returns a string for debugging purpose.
pub fn emit_ssa(module: &Module, others: &Modules) -> String {
  let mut a: Vec<String> = [].to_vec();
  for n in module.own_symbols() {
    a.push(format!("{:?}", n));
    if let Some(f) = module.get_local_function_id(n) {
      a.push(Emitter::emit_ssa_fn(f, module, others));
    }
  }
  a.join("\n")
}

/// The SSA blocks involved in the lowering of a case in a match expression.
struct CaseBlocks {
  /// The conditions head blocks
  heads: Vec<BlockIdentity>,

  /// The conditions bodies blocks
  bodies: Vec<BlockIdentity>,

  /// The default case block
  default: BlockIdentity,

  /// The tail of the case
  tail: BlockIdentity,
}

/// A constructor of SSA IR.
struct Emitter<'a> {

  /// The module being lowered.
  module: &'a Module,

  /// The other modules.
  others: &'a Modules,

  /// The program into which IR is being emitted.
  program: &'a mut Program,

  /// The context in which the emitter inserts new IR.
  context: InsertionContext,

  /// The HIR node arena.
  hir_arena: &'a NodeArena,

}

impl<'a> Emitter<'a> {

  /// Generates the IR of `source`, which has the given `identity`.
  fn emit_ssa_fn(identity: LocalFunctionId, module: &'a Module, others: &'a Modules) -> String {
    // TODO: This is the program into which IR is being inserted. Eventually that should become
    // an argument of the function, as this data structure should persist.
    let mut program = Program::new();

    let f = module.get_function_by_id(identity).unwrap();
    match f.code.as_ref().as_script() {
      Some(syntax) => {
        // Create the function.
        // TODO: Use better identities.

        let name = module.get_function_name_by_id(identity).unwrap();
        let mut lowered = ssa::Function::new(name);

        let t = f.definition.ty_scheme.extra_parameters();

        // Each parameter introduces a new binding in the environment.
        let environment = (0..(t.requirements.len() + f.definition.arg_names.len()))
          .map(|i| ssa::Value::Parameter(i))
          .collect::<Vec<ssa::Value>>();

        // Create the function's entry.
        let entry = lowered.add_block().id();

        let code = &module.ir_arena[syntax.entry_node_id];

        // Instantiate an emitter to generate the function's contents.
        let mut emitter = Emitter {
          module,
          others,
          program: &mut program,
          context: InsertionContext {
            function: lowered,
            point: InsertionPoint::End(entry),
            span: code.span,
            environment,
          },
          hir_arena: &module.ir_arena,
        };

        // The body of the function evaluates to the return value.
        let v = emitter.lower_as_rvalue(code);
        emitter.insert(ssa::Instruction::ret(emitter.context.span, v));

        // Save the definition of the lowered function into the SSA program.
        lowered = emitter.context.function;
        let g = program.set_definition(lowered);
        format!("{}", *g)
      }

      None => panic!(),
    }
  }

  /// Returns a reference to the function identified by `f`.
  fn demand_function(&mut self, f: FunctionId, current_module: &'a Module) -> ssa::Value {
    let e = ModuleEnv::new(current_module, self.others);
    let s = format!("{}", f.format_with(&e));
    ssa::Value::Function(s.into())
  }

  /// Generates the IR for `node`, which occurs as a statement.
  fn lower_as_statement(&mut self, node: &hir::Node) {
    // use ir::NodeKind as K;
    match &node.kind {
      _ => {
        // QUESTION: Should we explicitly drop values?
        self.lower_as_rvalue(node);
      }
    }
  }

  /// Returns the blocks created for `n`.
  fn create_case_blocks(&mut self, n: &Box<Case>) -> CaseBlocks {
    let mut heads: Vec<BlockIdentity> = vec![];
    let mut bodies: Vec<BlockIdentity> = vec![];
    for _ in n.alternatives.iter() {
      heads.push(self.context.function.add_block().id());
      bodies.push(self.context.function.add_block().id());
    }
    let default: ssa::BlockIdentity = self.context.function.add_block().id();
    let tail: ssa::BlockIdentity = self.context.function.add_block().id();
    CaseBlocks { heads, bodies, default: default, tail:tail }
  }

  /// Returns a copy of the dictionnary value holded by `t`.
  fn dictionnary_value(&mut self, t: &hir::GetDictionary) -> hir::value::Value {
    match t.dictionary {
      TraitImplId::Local(id) => {
        self.dictionnary_value_from_trait(self.module.get_impl_data(id))
      },
      TraitImplId::Import(id) => {
        let slot = self.module.get_import_impl_slot(id).unwrap();
        let other_module = self.others.get(slot.module).unwrap().module().unwrap();
        self.dictionnary_value_from_trait(other_module.get_impl_data_by_trait_key(&slot.key))
      }
    }
  }

  /// Returns a copy of the dictionnary value of `t`.
  fn dictionnary_value_from_trait(&mut self, t: Option<&TraitImpl>) -> hir::value::Value {
    t.unwrap().dictionary_value.clone()
  }

  /// Converts a HIR `Tuple` into a SSA `Dictionnary`.
  fn to_ssa_dictionnary(&mut self, v: Value) -> ssa::Value {
    let mut r: Vec<ssa::Value> = vec![];
    let hir::value::Value::Tuple(t) = v else {
      panic!("the value must be a tuple to be converted into a dictionnary");
    };
    for tv in t.iter() {
      let hir::value::Value::Function(f) = tv else {
        panic!("");
      };
      let i = f.as_ref().function;
      let n = if f.as_ref().module == self.module.module_id() {
        let f = FunctionId::Local(i);
        self.demand_function(f, self.module)
      } else {
        let oe = self.others.get(f.as_ref().module).unwrap();
        let om = oe.module().unwrap();
        let f = FunctionId::Local(i);
        self.demand_function(f, om)
      };
      r.push(n);
    };
    ssa::Value::Dictionary(r)
  }

  /// Generates the IR for `node`, which occurs as rvalue.
  fn lower_as_rvalue(&mut self, node: &hir::Node) -> ssa::Value {
    use hir::NodeKind as K;
    match &node.kind {
      K::Block(n) => {
        let (last, prefix) = n.split_last().unwrap();
        for s in prefix.iter() {
          self.lower_as_statement(&self.hir_arena[*s]);
        }
        self.lower_as_rvalue(&self.hir_arena[*last])
      }

      K::Case(n) => {
        let blocks = self.create_case_blocks(n);

        let end: usize = self.context.environment.len();

        // We lower the scrutinee before the case blocks so that its value can be used in all conditions.
        let scrutinee = self.lower_as_rvalue(&self.hir_arena[n.value]);

        // Create a temporary allocation to store the result of the match.
        let temporary = self
          .insert(ssa::Instruction::alloca(node.span, node.ty))
          .unwrap();
        self.insert(ssa::Instruction::br(node.span, blocks.heads[0]));

        // Lower the alternatives.
        for (i, (c, a)) in n.alternatives.iter().enumerate() {
          // Load the next alternative's condition if there's one. Otherwise, we've reached the
          // default case.
          let next = if i < &n.alternatives.len() - 1 {
            blocks.heads[i + 1]
          } else {
            blocks.default
          };

          // Transfer control flow to the head of the match.
          self.context.point = InsertionPoint::End(blocks.heads[i]);

          // Lower the pattern
          let x0 = self.lower_as_primitive(&c.clone().into_value()).unwrap();
          // Compare the condition with the scrutinee and, depending on the result, branch to
          // either the body of the current alternative or the next head.
          let v = self
            .insert(ssa::Instruction::compare_eq(node.span, scrutinee.clone(), x0))
            .unwrap();
          self.insert(ssa::Instruction::condbr(node.span, v, blocks.bodies[i], next));

          // Lower the body of the alternative.
          self.context.point = InsertionPoint::End(blocks.bodies[i]);
          let x1 = self.lower_as_rvalue(&self.hir_arena[*a]);

          // Store the result of the expression.
          self.insert(ssa::Instruction::store(node.span, x1, temporary.clone()));
          self.insert(ssa::Instruction::br(node.span, blocks.tail));
          self.context.environment.truncate(end);
        }

        // Default case.
        self.context.point = InsertionPoint::End(blocks.default);
        let v = self.lower_as_rvalue(&self.hir_arena[n.default]);
        self.insert(ssa::Instruction::store(node.span, v, temporary.clone()));
        self.insert(ssa::Instruction::br(node.span, blocks.tail));
        self.context.environment.truncate(end);

        // Tail.
        self.context.point = InsertionPoint::End(blocks.tail);
        self
          .insert(ssa::Instruction::load(node.span, temporary))
          .unwrap()
      }

      K::Immediate(n) => {
        if let Some(result) = self.lower_as_primitive(&n.value) {
          result
        } else {
          let s = self.show(node.ty);
          panic!("lowering is unimplemented for node of kind '{:?}' of type {:?}",
            n.value, s)
        }
      }

      K::EnvLoad(n) => {
        // The following assumes we can simply copy any value referred to by a load.
        self.context.environment[n.index as usize].clone()
      }

      K::EnvStore(n) => {
        let rhs = self.lower_as_rvalue(&self.hir_arena[n.value]);
        self.context.environment.push(rhs);
        ssa::Value::Unit
      }

      K::StaticApply(n) => {
        let f = self.demand_function(n.function, self.module);
        let mut a: Vec<ssa::Value> = vec![];
        for x in &n.arguments {
          a.push(self.lower_as_rvalue(&self.hir_arena[*x]));
        }

        assert!(node.ty == n.ty.ret);
        self
          .insert(ssa::Instruction::call(node.span, f, a, n.ty.ret))
          .unwrap()
      }

      K::GetDictionary(n) => {
        let v = self.dictionnary_value(n);
        self.to_ssa_dictionnary(v)
      }

      K::Apply(n) => {
        let f = self.lower_as_rvalue(&self.hir_arena[n.function]);
        let a: Vec<ssa::Value> = n.arguments.iter()
          .map(|a| self.lower_as_rvalue(&self.hir_arena[*a]))
          .collect();

        self.insert(ssa::Instruction::call(
          node.span, f, a, self.hir_arena[n.function].ty,
        ))
        .unwrap()
      }

      K::Project(n, i) => {
        let m = &self.hir_arena[*n];

        let v = self.lower_as_rvalue(m);

        self
          .insert(ssa::Instruction::project(node.span, v, *i, node.ty))
          .unwrap()
      }

      K::Loop(n) => {
        match &self.hir_arena[*n].kind {
          K::Block(b) => {
            let (head, body, tail) = (
              self.context.function.add_block().id(),
              self.context.function.add_block().id(),
              self.context.function.add_block().id(),
            );

            self.context.point = InsertionPoint::End(head);

            // Compute the next iterator element.
            self.lower_as_rvalue(&self.hir_arena[b[0]]);

            match &self.hir_arena[b[1]].kind {
              K::Case(n) => {
                // Lower in the loop's condition.
                let scrutinee = self.lower_as_rvalue(&self.hir_arena[n.value]);

                assert_eq!(n.alternatives.len(), 1 as usize);

                let c0 = self.lower_as_primitive(&n.alternatives[0].0.clone().into_value()).unwrap();

                // Jump to the loop's body if the condition holds or to its tail otherwise.
                let v = self
                  .insert(ssa::Instruction::compare_eq(node.span, scrutinee.clone(), c0,))
                  .unwrap();
                self.insert(ssa::Instruction::condbr(node.span, v, body, tail));

                self.context.point = InsertionPoint::End(body);
                // We lower the loop body
                self.lower_as_rvalue(&self.hir_arena[n.alternatives[0].1]);

                self.insert(ssa::Instruction::br(node.span, head));
                self.context.point = InsertionPoint::End(tail);
                ssa::Value::Unit
              }
              _ => {
                panic!("unreachable : First node of loop block was not a case")
              }
            }
          }
          _ => {
            panic!("unreachable : First node of loop was not a block")
          }
        }
      }

      K::ExtractTag(n) => {
        // TODO: N should be a variant, which will be lowered to either a `ssa::Value::Tuple` or to a new `ssa::Value::Variant`
        // So we should either extract the tag with a fixed index for the tuple, or accessing a custom property of the variant.
        todo!("Lowering for ExtractTag is unimplemented");
      }

      K::Variant(t, n) => {
        // TODO: Implemented this either by lowering it to a `ssa::Value::Tuple`, a `ssa::Value::Variant`
        todo!("Lowering for Variant is unimplemented");
      }

      _ => {
        println!(
          "lowering is unimplemented for node of kind '{:?}'",
          node.kind
        );
        todo!()
      }
    }
  }

  /// Returns the lowered representation of the given native value.
  fn lower_as_primitive(&mut self, native: &hir::value::Value) -> Option<ssa::Value> {
    use ssa::value::Integer as Int;

    if native.as_primitive_ty::<()>() != None {
      Some(ssa::Value::Unit)
    } else if let Some(n) = native.as_primitive_ty::<isize>() {
      Some(ssa::Value::Integer(containers::b(Int::from_isize(*n))))
    } else if let Some(n) = native.as_primitive_ty::<u32>() {
      Some(ssa::Value::Integer(containers::b(Int::from_u32(*n))))
    } else if let Some(n) = native.as_primitive_ty::<i32>() {
      Some(ssa::Value::Integer(containers::b(Int::from_i32(*n))))
    } else if let Some(n) = native.as_primitive_ty::<bool>() {
      Some(ssa::Value::Boolean(*n))
    } else {
      None
    }
  }

  /// Inserts `s` at the current insertion point and returns the result the register assigned by
  /// that instruction, if any.
  fn insert(&mut self, s: ssa::Instruction) -> Option<ssa::Value> {
    let i = match &self.context.point {
      InsertionPoint::End(b) => self.context.function.block_mut(*b).append(s),
    };
    self.context.function.definition(i)
  }

  /// Returns a textual representation of `x`.
  fn show<T: FormatWith<ModuleEnv<'a>>>(&self, x: T) -> String {
    let e = ModuleEnv::new(self.module, self.others);
    format!("{}", x.format_with(&e))
  }

}

/// The context in which instructions are inserted.
struct InsertionContext {

  /// The function in which new instructions are inserted.
  function: ssa::Function,

  /// Where new instructions are inserted in `function`.
  point: InsertionPoint,

  /// The region in the source code to which inserted instructions are associated.
  span: Location,

  environment: Vec<ssa::Value>,

}

/// Where an instruction should be inserted in a basic block.
enum InsertionPoint {

  /// The end of a basic block.
  End(ssa::BlockIdentity),

}
