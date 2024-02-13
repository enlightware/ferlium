use painturscript::{
    ir::Node,
    r#type::{native_type, Type},
};

fn main() {
    // basic types
    let int = native_type::<i32>();
    let string = native_type::<String>();

    // test type printing
    let st = Type::Struct(vec![
        ("ty".to_string(), Type::GenericRef(0)),
        ("name".to_string(), Type::Primitive(string.clone())),
        ("age".to_string(), Type::Primitive(int.clone())),
    ]);
    println!("{}{}", st.format_generics(), st);

    let un = Type::Union(vec![Type::Primitive(int), Type::Primitive(string)]);
    println!("{}{}", un.format_generics(), un);

    // test ir execution
    let ir = Node::NativeFunctionCall {
        function: Box::new(std::ops::Add::add as fn(i32, i32) -> i32),
        arguments: vec![
            Node::NativeFunctionCall {
                function: Box::new(std::ops::Sub::sub as fn(i32, i32) -> i32),
                arguments: vec![
                    Node::Literal(Box::new(11_i32)),
                    Node::Literal(Box::new(5_i32)),
                ],
            },
            Node::Literal(Box::new(3_i32)),
        ],
    };
    println!("{:?}", ir);
    ir.eval_and_print();
}
