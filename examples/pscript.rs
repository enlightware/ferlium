use std::rc::Rc;

use painturscript::{
    function::{BinaryNativeFn, FunctionKey},
    ir::{Application, Context, Node, StaticApplication},
    r#type::{store_types, Type, TypeData},
    value::Value,
};
use smallvec::smallvec;
use ustr::ustr;

fn main() {
    // basic types
    let int = Type::primitive::<i32>();
    let u32 = Type::primitive::<u32>();
    let float = Type::primitive::<f32>();
    let string = Type::primitive::<String>();
    let empty_tuple = Type::tuple(vec![]);
    let gen0 = Type::generic_variable(0);

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
    let adt_list_element = TypeData::Tuple(vec![gen0, Type::new_local(1)]);
    let adt_list = TypeData::Variant(vec![
        (ustr("Nil"), empty_tuple),
        (ustr("Cons"), Type::new_local(0)),
    ]);
    // add them to the universe as a batch
    let adt_list = store_types(&[adt_list_element, adt_list])[1];
    println!("{}", adt_list);

    // native list
    #[derive(Debug, Clone, PartialEq, Eq)]
    struct List(Vec<Value>);
    let list = Type::generic_native::<List>(smallvec![gen0]);
    let list_int = Type::generic_native::<List>(smallvec![int]);
    println!("{}", list);
    println!("{}", list_int);

    // functions
    let functions = [
        Rc::new(BinaryNativeFn::description(
            std::ops::Add::add as fn(i32, i32) -> i32,
        )),
        Rc::new(BinaryNativeFn::description(
            std::ops::Sub::sub as fn(i32, i32) -> i32,
        )),
    ];
    let add_fn_ty = functions[0].ty();
    println!("{}", add_fn_ty);
    let add_fn = FunctionKey::new(&functions[0]);
    let sub_fn = FunctionKey::new(&functions[1]);
    let add_value = Value::Function(add_fn.clone());

    // some interesting functions and types
    let option = Type::variant(vec![(ustr("None"), empty_tuple), (ustr("Some"), gen0)]);
    println!("Option: {}", option);
    let iterator_gen0 = Type::function(&[], Type::tuple(vec![option, Type::new_local(0)]));
    println!("Iterator: {}", iterator_gen0);

    // test printing values
    println!("\nSome values:\n");
    let v_int = Value::Primitive(Box::new(11_i32));
    println!("{}", v_int);
    let v_list_int = Value::Primitive(Box::new(List(vec![
        Value::primitive(11_i32),
        Value::primitive(22_i32),
    ])));
    println!("{}", v_list_int);
    println!("{}", add_value);

    // test ir execution
    println!("\nSome IR and its execution:\n");
    let ir = Node::BlockExpr(Box::new(smallvec![
        Node::EnvStore(Box::new(Node::Literal(Value::primitive(11_i32)))),
        Node::Apply(Box::new(Application {
            function: Node::Literal(Value::Function(add_fn)),
            arguments: vec![
                Node::StaticApply(Box::new(StaticApplication {
                    function: sub_fn,
                    arguments: vec![Node::EnvLoad(0), Node::Literal(Value::primitive(5_i32))],
                })),
                Node::Literal(Value::primitive(3_i32)),
            ],
        })),
    ]));
    println!("{:?}", ir);
    ir.eval_and_print(&mut Context::new());
}
