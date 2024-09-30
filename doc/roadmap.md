# Roadmap

### Language features

- Split compilation of modules by analysing the dependency graph
- Recursive modules
- Type classes
- Recursive types inference
- Co-routine/async
- Recursive types
- Generalised match following Maranget 2008
- User-defined closures
- Object-oriented style function calls
- Early return and breaks

### Library and test features

- Array from iterator (note: functional iterators require closures or type classes)

### Compiler features

- Better parsing error messages
- Basic optimisations
- Just in time compilation
- Partial evaluation

### IDE features

- Show location of execution error

### Next tasks

- Switch grammar to lalrpop
- Add {} block expression
- Fix grammar with equal in lambdas

### Open questions

- Should integer overflow be caught?