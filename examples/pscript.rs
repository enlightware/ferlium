use painturscript::{
    function::binary_native_function,
    ir::{Application, Context, Functions, Node, StaticApplication},
    r#type::{native_type, Type},
    value::{GenericNativeValue, Value},
};
use ustr::ustr;
use smallvec::smallvec;

fn main() {
    // basic types
    let int = native_type::<i32>();
    let u32 = native_type::<u32>();
    let float = native_type::<f32>();
    let string = native_type::<String>();

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

    #[derive(Debug, Clone, PartialEq, Eq)]
    struct List(Vec<Value>);

    let list = Type::generic_native::<List>(smallvec![Type::GenericVariable(0)]);
    let list_int = Type::generic_native::<List>(smallvec![Type::Primitive(int.clone())]);
    println!("{}{}", list.format_generics(), list);
    println!("{}{}", list_int.format_generics(), list_int);

    // test printing values
    println!("\nSome values:\n");
    let v_int = Value::Primitive(Box::new(11_i32));
    println!("{}", v_int);
    let v_list_int = Value::GenericNative(Box::new(GenericNativeValue {
        native: Box::new(List(vec![Value::primitive(11_i32), Value::primitive(22_i32)])),
        arguments: smallvec![Type::Primitive(int.clone())],
    }));
    println!("{}", v_list_int);

    // test ir execution
    println!("\nSome IR and its execution:\n");
    // 1. add some native functions
    let mut functions = Functions::default();
    let add_fn = functions.insert(binary_native_function(
        std::ops::Add::add as fn(i32, i32) -> i32,
    ));
    let sub_fn = functions.insert(binary_native_function(
        std::ops::Sub::sub as fn(i32, i32) -> i32,
    ));
    let mut ctx = Context::new(&functions);
    // 2. define some code
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
    // 3. execute this code
    ir.eval_and_print(&mut ctx);
}
