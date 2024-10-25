use ustr::Ustr;

/// A range of bytes in the user's input.
/// It only contains the start and end byte offsets, not the actual input string.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub fn new(start: usize, end: usize) -> Self {
        if end < start {
            panic!("Span starts ({}) after it ends ({})!", start, end);
        }
        Span { start, end }
    }

    pub fn start(&self) -> usize {
        self.start
    }

    pub fn end(&self) -> usize {
        self.end
    }

    pub fn len(&self) -> usize {
        self.end - self.start
    }
}

/// An external location is a span in a different module.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct ExternalLocation {
    module_name: Ustr,
    span: Span,
}

impl ExternalLocation {
    pub fn module_name(&self) -> Ustr {
        self.module_name
    }

    pub fn span(&self) -> Span {
        self.span
    }
}

/// A location in the user's input.
/// If it originated outside the current module, the module field tracks that original location,
/// and span tracks the location within the current module where it was brought into scope.
/// (the function instantiation point).
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct Location {
    span: Span,
    module: Option<ExternalLocation>,
}

impl Location {
    /// Create a new location starting at byte `start` and ending at byte `end`.
    pub fn new(start: usize, end: usize, module: Option<ExternalLocation>) -> Self {
        Location {
            span: Span::new(start, end),
            module,
        }
    }

    /// Create a new location starting at byte `start` and ending at byte `end`, in the current module.
    /// Panics if `end` is less than `start`.
    pub fn new_local(start: usize, end: usize) -> Self {
        Self::new(start, end, None)
    }

    /// Byte offset of the start of the span.
    pub fn start(&self) -> usize {
        self.span.start
    }

    /// Byte offset of the end of the span.
    pub fn end(&self) -> usize {
        self.span.end
    }

    /// Length in bytes of the span.
    pub fn len(&self) -> usize {
        self.span.end - self.span.start
    }

    /// Returns `true` if this location's span covers 0 bytes, or `false` otherwise.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the span of this location.
    pub fn span(&self) -> Span {
        self.span
    }

    /// Returns the module this location comes from, if any.
    pub fn module(&self) -> Option<ExternalLocation> {
        self.module
    }

    /// If module is not None, this location is in a different module, make it
    /// an imported location.
    pub fn instantiate(&mut self, module: Option<Ustr>, span: Span) {
        let name = match module {
            Some(name) => name,
            None => return,
        };
        if self.module.is_none() {
            // if the location was previously local, make it external
            self.module = Some(ExternalLocation {
                module_name: name,
                span: self.span, // The original span
            });
        }
        // Note: if the location was already external, just overwrite the instantiation point
        self.span = span; // The span of the instantiation point in the current module
    }
}
