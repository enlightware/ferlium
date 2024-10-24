use ustr::Ustr;

/// A `Span` records what portion of the user's input something (e.g. a lexeme or production)
/// references (i.e. the `Span` doesn't hold a reference / copy of the actual input).
/// It also contains which module the input was in, if not the current one.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct Span {
    start: usize,
    end: usize,
    module: Option<Ustr>,
}

impl Span {
    /// Create a new span starting at byte `start` and ending at byte `end`.
    pub fn new(start: usize, end: usize, module: Option<Ustr>) -> Self {
        if end < start {
            panic!("Span starts ({}) after it ends ({})!", start, end);
        }
        Span { start, end, module }
    }

    /// Create a new span starting at byte `start` and ending at byte `end`.
    /// Panics if `end` is less than `start`.
    pub fn new_local(start: usize, end: usize) -> Self {
        Self::new(start, end, None)
    }

    /// Create a new span starting at byte `start` and ending at byte `end` in the given module.
    /// Panics if `end` is less than `start`.
    pub fn new_in_module(start: usize, end: usize, module: Ustr) -> Self {
        Self::new(start, end, Some(module))
    }

    /// Byte offset of the start of the span.
    pub fn start(&self) -> usize {
        self.start
    }

    /// Byte offset of the end of the span.
    pub fn end(&self) -> usize {
        self.end
    }

    /// Length in bytes of the span.
    pub fn len(&self) -> usize {
        self.end - self.start
    }

    /// Returns `true` if this `Span` covers 0 bytes, or `false` otherwise.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the module this span is in, if any.
    pub fn module(&self) -> Option<Ustr> {
        self.module
    }

    /// Sets the module this span is in.
    pub fn set_module(&mut self, module: Option<Ustr>) {
        self.module = module;
    }
}
