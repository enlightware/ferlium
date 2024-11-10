# Roadmap

### Language features

- Type classes
- Private module members
- Tuple deconstruction on assignation
- Recursive modules
- Recursive types inference
- Co-routine/async
- Recursive types
- Generalised match following Maranget 2008
- User-defined closures
- Object-oriented style function calls
- Early return and breaks
- Short circuiting logical operators
- Unit testing with mock function generation through annotations

### Library and test features

- Array from iterator (note: functional iterators require closures or type classes)

### Compiler features

- Basic optimisations: replace constructors of literals with constructed literals
- Add context to IsNotSubtype error and write some more useful error messages when match exhaustiveness fails
- Advanced optimisations: generic partial evaluation (constant propagation)
- Just in time compilation

### IDE features

- Show location of execution error

### Next tasks


### Open questions

- Should integer overflow be caught?