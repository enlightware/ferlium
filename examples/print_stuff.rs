use std::{cell::RefCell, rc::Rc};

use painturscript::{
    function::{BinaryNativeFn, FunctionRef},
    ir::{Application, EvalCtx, Node, StaticApplication},
    r#type::{bare_native_type, store_types, NativeType, Type, TypeKind, TypeOfNativeValue},
    value::Value,
};
use smallvec::smallvec;
use ustr::ustr;

fn main() {
    // basic types
    let int = Type::primitive::<isize>();
    let u32 = Type::primitive::<u32>();
    let float = Type::primitive::<f32>();
    let string = Type::primitive::<String>();
    let empty_tuple = Type::tuple(vec![]);
    let gen0 = Type::variable_id(0);

    // test type printing
    println!("Some types:\n");
    let st = Type::record(vec![
        (ustr("ty"), gen0),
        (ustr("name"), string),
        (ustr("age"), int),
    ]);
    println!("{}", st);

    let variant = Type::variant(vec![(ustr("i"), int), (ustr("s"), string)]);
    println!("{}", variant);
    let variant = Type::variant(vec![
        (ustr("i"), int),
        (ustr("f"), float),
        (ustr("u32"), u32),
    ]);
    println!("{}", variant);

    // ADT recursive list
    let adt_list_element = TypeKind::Tuple(vec![gen0, Type::new_local(1)]);
    let adt_list = TypeKind::Variant(vec![
        (ustr("Nil"), empty_tuple),
        (ustr("Cons"), Type::new_local(0)),
    ]);
    // add them to the universe as a batch
    let adt_list = store_types(&[adt_list_element, adt_list])[1];
    println!("{}", adt_list);

    // native list
    #[derive(Debug, Clone, PartialEq, Eq)]
    struct List(Vec<Value>);
    impl TypeOfNativeValue for List {
        fn type_of_value(&self) -> NativeType {
            NativeType::new(
                bare_native_type::<Self>(),
                match self.0.first() {
                    Some(value) => vec![value.ty()],
                    None => vec![Type::variable_id(0)],
                }
            )
        }
    }
    let list = Type::native::<List>(vec![gen0]);
    let list_int = Type::native::<List>(vec![int]);
    println!("{}", list);
    println!("{}", list_int);

    // functions
    let functions = [
        Rc::new(RefCell::new(BinaryNativeFn::description(
            std::ops::Add::add as fn(isize, isize) -> isize,
        ))),
        Rc::new(RefCell::new(BinaryNativeFn::description(
            std::ops::Sub::sub as fn(isize, isize) -> isize,
        ))),
    ];
    let add_fn_ty = functions[0].borrow().ty();
    println!("{}", add_fn_ty);
    let add_fn = FunctionRef::new_strong(&functions[0]);
    let sub_fn = FunctionRef::new_strong(&functions[1]);
    let add_value = Value::Function(add_fn.clone());

    // some interesting functions and types
    let option = Type::variant(vec![(ustr("None"), empty_tuple), (ustr("Some"), gen0)]);
    println!("Option: {}", option);
    let iterator_gen0 = Type::function(&[], Type::tuple(vec![option, Type::new_local(0)]));
    println!("Iterator: {}", iterator_gen0);

    // test printing values
    println!("\nSome values:\n");
    let v_int = Value::Native(Box::new(11_isize));
    println!("{}", v_int);
    let v_list_int = Value::Native(Box::new(List(vec![
        Value::native(11_isize),
        Value::native(22_isize),
    ])));
    println!("{}", v_list_int);
    println!("{}", add_value);

    // test ir execution
    println!("\nSome IR and its execution:\n");
    let ir = Node::BlockExpr(Box::new(smallvec![
        Node::EnvStore(Box::new(Node::Literal(Value::native(11_isize)))),
        Node::Apply(Box::new(Application {
            function: Node::Literal(Value::Function(add_fn)),
            arguments: vec![
                Node::StaticApply(Box::new(StaticApplication {
                    function: sub_fn,
                    arguments: vec![Node::EnvLoad(0), Node::Literal(Value::native(5_isize))],
                })),
                Node::Literal(Value::native(3_isize)),
            ],
        })),
    ]));
    println!("{:?}", ir);
    ir.eval_and_print(&mut EvalCtx::new());
}
