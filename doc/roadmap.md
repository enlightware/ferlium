# Roadmap

### Language features

- Type classes / traits
- As casting
- Tuple and record deconstruction on assignation
- Private module members
- Recursive types, with inference
- Co-routine/async
- Generalised match following Maranget 2008
- Complex type instantiation
- User-defined closures
- Object-oriented style function calls
- Early return and breaks
- Short circuiting logical operators
- Unit testing with mock function generation through annotations
- Compiler plugin for compile-time code validation (somehow similar to Rust's procedural macro system)

### Language features under consideration

- Recursive modules

### Library and test features

- Array from iterator (note: functional iterators require closures or type classes)

### Compiler features

- Add context to IsNotSubtype error and write some more useful error messages when match exhaustiveness fails
- Advanced optimisations: generic partial evaluation (constant propagation)
- IR as control-flow graph
- Just in time compilation

### IDE features

- Show location of execution error
