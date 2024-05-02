use lrpar::Span;

pub type LocatedError = (String, Span);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RuntimeError {
    DivisionByZero,
    RemainderByZero,
    ArrayAccessOutOfBounds { index: isize, len: usize },
    // TODO: add executation duration limit exhausted
    // TODO: add stack overflow
}
