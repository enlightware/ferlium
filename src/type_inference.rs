use std::collections::HashMap;

use ena::unify::{EqUnifyValue, InPlaceUnificationTable, UnifyKey};

use crate::{
    ast::{Expr, ExprKind, NodeId},
    r#type::{Type, TypeVar},
};

impl UnifyKey for TypeVar {
    type Value = Option<Type>;

    fn index(&self) -> u32 {
        self.0
    }

    fn from_index(u: u32) -> Self {
        Self(u)
    }

    fn tag() -> &'static str {
        "TypeVar"
    }
}

impl EqUnifyValue for Type {}

/// A constraint on types.
enum Constraint {
    TypeEqual(Type, Type),
}

/// A typing environment, including the known types and the unification table.
#[derive(Default)]
pub struct TypingEnv {
    unification_table: InPlaceUnificationTable<TypeVar>,
    types: HashMap<NodeId, Type>,
}

impl TypingEnv {
    pub fn fresh_type_var(&mut self) -> TypeVar {
        self.unification_table.new_key(None)
    }

    fn infer(&mut self, expr: &Expr) -> (Vec<Constraint>, Type) {
        use ExprKind::*;
        match &expr.kind {
            Literal(_) => todo!(),
            Variable(_) => todo!(),
            LetVar(_, _, _) => todo!(),
            Abstract(_, _) => todo!(),
            Apply(_, _) => todo!(),
            StaticApply(_, _) => todo!(),
            Block(_) => todo!(),
            Assign(_, _) => todo!(),
            Tuple(_) => todo!(),
            Project(_, _) => todo!(),
            Array(_) => todo!(),
            Index(_, _) => todo!(),
            Match(_, _, _) => todo!(),
            Error(_) => todo!(),
        }
        todo!("Implement type inference")
    }

    fn check(&mut self, expr: &Expr, ty: Type) -> Vec<Constraint> {
        todo!("Implement type checking")
    }
}
