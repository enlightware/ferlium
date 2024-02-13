use crate::value::BinaryNativeFunction;

impl BinaryNativeFunction for fn(i32, i32) -> i32 {
    type A = i32;
    type B = i32;
    type O = i32;
}
