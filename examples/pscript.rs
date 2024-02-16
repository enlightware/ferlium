use painturscript::{
    ir::{Context, Node},
    r#type::{native_type, Type},
};

fn main() {
    // basic types
    let int = native_type::<i32>();
    let u32 = native_type::<u32>();
    let float = native_type::<f32>();
    let string = native_type::<String>();

    // test type printing
    let st = Type::Record(vec![
        ("ty".to_string(), Type::GenericArg(0)),
        ("name".to_string(), Type::Primitive(string.clone())),
        ("age".to_string(), Type::Primitive(int.clone())),
    ]);
    println!("{}{}", st.format_generics(), st);

    let un = Type::Union(vec![Type::Primitive(int.clone()), Type::Primitive(string)]);
    println!("{}{}", un.format_generics(), un);
    let un = Type::Union(vec![
        Type::Primitive(int),
        Type::Primitive(float),
        Type::Primitive(u32),
    ]);
    println!("{}{}", un.format_generics(), un);

    // test ir execution
    let ir = Node::BlockExpr(vec![
        Node::EnvStore(Box::new(Node::Literal(Box::new(11_i32)))),
        Node::NativeFunctionCall {
            function: Box::new(std::ops::Add::add as fn(i32, i32) -> i32),
            arguments: vec![
                Node::NativeFunctionCall {
                    function: Box::new(std::ops::Sub::sub as fn(i32, i32) -> i32),
                    arguments: vec![Node::EnvLoad(0), Node::Literal(Box::new(5_i32))],
                },
                Node::Literal(Box::new(3_i32)),
            ],
        },
    ]);
    println!("{:?}", ir);
    let mut ctx = Context::default();
    ir.eval_and_print(&mut ctx);
}
