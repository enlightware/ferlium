use crate::{
  Location, Modules, containers,
  format::FormatWith,
  ir::{self, Case, NodeArena},
  module::{FunctionId, LocalFunctionId, Module, ModuleEnv, TraitImplId},
  ssa::{self, BlockIdentity},
  value::{self, Value},
};

/// Emit the low-level (aka SSA) ferlium IR of `module`.
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

/// The SSA blocks composing a Case HIR node.
struct CaseBlocks {
  /// The conditions head blocks
  heads: Vec<BlockIdentity>,

  /// The conditions bodies blocks
  bodies: Vec<BlockIdentity>,

  /// The default case block
  default: BlockIdentity,

  /// The tail of the case
  tail: BlockIdentity
}

/// A constructor of SSA IR.
struct Emitter<'a> {
  /// The module being lowered.
  module: &'a Module,

  /// The other modules.
  others: &'a Modules,

  /// The context in which the emitter inserts new IR.
  context: InsertionContext,

  /// The HIR node arena.
  hir_arena: &'a NodeArena,
}

impl<'a> Emitter<'a> {
  /// Generates the IR of `source`, which has the given `identity`.
  fn emit_ssa_fn(identity: LocalFunctionId, module: &'a Module, others: &'a Modules) -> String {
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
        let mut emitter = Self {
          module,
          others,
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

        format!("{}", emitter.context.function)
      }

      None => panic!(),
    }
  }

  /// Returns a reference to the function identified by `f`.
  fn demand_function(&mut self, f: FunctionId) -> ssa::Value {
    let e = ModuleEnv::new(self.module, self.others);
    let s = format!("{}", f.format_with(&e));
    ssa::Value::Function(s.into())
  }

  /// Generates the IR for `node`, which occurs as a statement.
  fn lower_as_statement(&mut self, node: &ir::Node) {
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

  /// Generates the IR for `node`, which occurs as rvalue.
  fn lower_as_rvalue(&mut self, node: &ir::Node) -> ssa::Value {
    use ir::NodeKind as K;
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

        // We want to lower the scrutinee before the case blocks. This allows us to use the lowered scrutinee value in all conditions blocks
        let scrutinee = self.lower_as_rvalue(&self.hir_arena[n.value]);

        // Create a temporary allocation to store the result of the match.
        let temporary = self
          .insert(ssa::Instruction::alloca(node.span, node.ty))
          .unwrap();
        self.insert(ssa::Instruction::br(node.span, blocks.heads[0]));

        // Lower the alternatives.
        for (i, (c, a)) in n.alternatives.iter().enumerate() {
          // Load the next alternative's condition. If there aren't any left, we've reached the base case.
          let next = if i < &n.alternatives.len() - 1 {
            blocks.heads[i + 1]
          } else {
            blocks.default
          };

          // Transfer control flow to the head of the loop.
          self.context.point = InsertionPoint::End(blocks.heads[i]);

          // Lower the condition value
          // TODO: We may want to check if the types of the lowered condition and the scrutinee are the same
          let x0 = self.lower_as_primitive(c).unwrap();
          // We compare and branch either on the current condition body, or to the next condition head
          let v = self
            .insert(ssa::Instruction::compare_eq(
              node.span, scrutinee.clone(), x0))
            .unwrap();
          self.insert(ssa::Instruction::condbr(node.span, v, blocks.bodies[i], next));

          // Lower the condition.
          self.context.point = InsertionPoint::End(blocks.bodies[i]);
          let x1 = self.lower_as_rvalue(&self.hir_arena[*a]);

          // Store the result of the expression.
          self.insert(ssa::Instruction::store(node.span, x1, temporary.clone()));
          self.insert(ssa::Instruction::br(node.span, blocks.tail));
          self.context.environment.truncate(end);
        }

        // Default case
        self.context.point = InsertionPoint::End(blocks.default);
        let v = self.lower_as_rvalue(&self.hir_arena[n.default]);
        self.insert(ssa::Instruction::store(node.span, v, temporary.clone()));
        self.insert(ssa::Instruction::br(node.span, blocks.tail));
        self.context.environment.truncate(end);

        // Tail
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
        // TODO: Is the casting from u32 to usize acceptable ?
        self.context.environment[n.index as usize].clone()
      }

      K::EnvStore(n) => {
        let rhs = self.lower_as_rvalue(&self.hir_arena[n.value]);
        self.context.environment.push(rhs);
        ssa::Value::Unit
      }

      K::StaticApply(n) => {
        let f = self.demand_function(n.function);
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
        let v = match n.dictionary {
          TraitImplId::Local(id) => self
            .module
            .get_impl_data(id)
            .unwrap()
            .dictionary_value
            .clone(),
          TraitImplId::Import(id) => {
            let slot = self.module.get_import_impl_slot(id).unwrap();
            let other_module = self.others.get(slot.module).unwrap().module().unwrap();
            other_module
              .get_impl_data_by_trait_key(&slot.key)
              .unwrap()
              .dictionary_value
              .clone()
          }
        };
        let mut r: Vec<ssa::Value> = vec![];
        match v {
          Value::Tuple(n) => {
            for f in n.iter() {
              match f {
                Value::Function(v) => {
                  let i = v.as_ref().function;
                  let m = v.as_ref().module;
                  let n = if m == self.module.module_id() {
                    let f = FunctionId::Local(i);
                    let e = ModuleEnv::new(self.module, self.others);
                    format!("{}", f.format_with(&e))
                  } else {
                    let oe = self.others.get(m).unwrap();
                    let om = oe.module().unwrap();
                    let f = FunctionId::Local(i);
                    let e = ModuleEnv::new(om, self.others);
                    format!("{}", f.format_with(&e))
                  };
                  r.push(ssa::Value::Function(n.into()));
                }
                _ => {
                  panic!("unreachable: all node in dictionnary tuple should be functions");
                }
              }
            }
          }
          _ => {
            panic!("unreachable: dictionnary value should be a tuple");
          }
        }
        ssa::Value::Dictionary(r)
      }

      K::Apply(n) => {
        let f = self.lower_as_rvalue(&self.hir_arena[n.function]);
        let a: Vec<ssa::Value> = n
          .arguments
          .iter()
          .map(|a| self.lower_as_rvalue(&self.hir_arena[*a]))
          .collect();

        self
          .insert(ssa::Instruction::call(
            node.span, f, a, self.hir_arena[n.function].ty,
          ))
          .unwrap()
      }

      K::Project(n, i) => {
        let m = &self.hir_arena[*n];

        let v = self.lower_as_rvalue(m);

        // TODO: For now, the index is passed as a usize directly, and just printed in the instruction.
        // We may want to lower it as a primitive to have the type information directly wrapped in here
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

            // Writing the loop head
            self.context.point = InsertionPoint::End(head);

            // We store the next iterator element on the memory
            self.lower_as_rvalue(&self.hir_arena[b[0]]);

            match &self.hir_arena[b[1]].kind {
              K::Case(n) => {
                // We lower in the loop head. This is the instruction we need to run to evaluate the condition each iteration in the loop
                let scrutinee = self.lower_as_rvalue(&self.hir_arena[n.value]);

                // We assumes that we have a single alternative
                assert_eq!(&n.alternatives.len(), &(1 as usize));

                // We lower the condition of the first alternative (=> The loop condition to check)
                let c0 = self.lower_as_primitive(&n.alternatives[0].0).unwrap();

                // We compare to branch -> either to loop head again || to loop tail
                let v = self
                  .insert(ssa::Instruction::compare_eq(
                    node.span,
                    scrutinee.clone(),
                    c0,
                  ))
                  .unwrap();
                self.insert(ssa::Instruction::condbr(node.span, v, body, tail));

                // We target the loop body block now
                self.context.point = InsertionPoint::End(body);
                // We lower the loop content
                self.lower_as_rvalue(&self.hir_arena[n.alternatives[0].1]);
                // We branch unconditionaly to the head again
                self.insert(ssa::Instruction::br(node.span, head));

                // We lower the tail, this is the loop end
                self.context.point = InsertionPoint::End(tail);
                // Loop evaluation = Unit
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
        let m = &self.hir_arena[*n];

        let s = self.lower_as_rvalue(m);

        // Do we want to fix the index here ? Or what ?
        self
          .insert(ssa::Instruction::project(node.span, s, 1, node.ty))
          .unwrap()
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
  fn lower_as_primitive(&mut self, native: &value::Value) -> Option<ssa::Value> {
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

  // /// Returns the result of `action` on `self` with the insertion context attached to `span`.
  // fn at<T>(&mut self, mut span: Location, action: impl FnOnce(&mut Self) -> T) -> T {
  //   mem::swap(&mut self.context.span, &mut span);
  //   let result = action(self);
  //   mem::swap(&mut self.context.span, &mut span);
  //   result
  // }

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
