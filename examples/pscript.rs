use std::{cell::RefCell, rc::Rc};

use painturscript::{
    function::{binary_native_function, FunctionKey},
    ir::{Application, Context, Node, StaticApplication},
    r#type::{native_type, Type},
    value::{GenericNativeValue, Value},
};
use smallvec::smallvec;
use ustr::ustr;

fn main() {
    // basic types
    let int = native_type::<i32>();
    let u32 = native_type::<u32>();
    let float = native_type::<f32>();
    let string = native_type::<String>();
    let empty_tuple = Type::tuple(vec![]);

    // test type printing
    println!("Some types:\n");
    let st = Type::Record(vec![
        (ustr("ty"), Type::GenericVariable(0)),
        (ustr("name"), Type::Primitive(string.clone())),
        (ustr("age"), Type::Primitive(int.clone())),
    ]);
    println!("{}{}", st.format_generics(), st);

    let un = Type::Union(vec![Type::Primitive(int.clone()), Type::Primitive(string)]);
    println!("{}{}", un.format_generics(), un);
    let un = Type::Union(vec![
        Type::Primitive(int.clone()),
        Type::Primitive(float),
        Type::Primitive(u32),
    ]);
    println!("{}{}", un.format_generics(), un);

    // ADT recursive list
    let adt_list = Rc::new((
        ustr("AdtList"),
        RefCell::new(Type::union(vec![empty_tuple.clone()])),
    ));
    let adt_list_ref = Type::named(&adt_list);
    adt_list
        .1
        .borrow_mut()
        .as_union_mut()
        .unwrap()
        .push(Type::tuple(vec![
            Type::generic_variable(0),
            adt_list_ref.clone(),
        ]));
    println!(
        "{}{} = {}",
        adt_list_ref.format_generics(),
        adt_list_ref,
        adt_list.1.borrow()
    );

    // native list
    #[derive(Debug, Clone, PartialEq, Eq)]
    struct List(Vec<Value>);

    let list = Type::generic_native::<List>(smallvec![Type::GenericVariable(0)]);
    let list_int = Type::generic_native::<List>(smallvec![Type::Primitive(int.clone())]);
    println!("{}{}", list.format_generics(), list);
    println!("{}{}", list_int.format_generics(), list_int);

    // functions
    let functions = [
        Rc::new(binary_native_function(
            std::ops::Add::add as fn(i32, i32) -> i32,
        )),
        Rc::new(binary_native_function(
            std::ops::Sub::sub as fn(i32, i32) -> i32,
        ))
    ];
    let add_fn = FunctionKey::new(&functions[0]);
    let sub_fn = FunctionKey::new(&functions[1]);
    let add_value = Value::Function(add_fn.clone());

    // test printing values
    println!("\nSome values:\n");
    let v_int = Value::Primitive(Box::new(11_i32));
    println!("{}", v_int);
    let v_list_int = Value::GenericNative(Box::new(GenericNativeValue {
        native: Box::new(List(vec![
            Value::primitive(11_i32),
            Value::primitive(22_i32),
        ])),
        arguments: smallvec![Type::Primitive(int.clone())],
    }));
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
