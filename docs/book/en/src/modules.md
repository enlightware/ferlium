# Modules and Program Structure

So far the book has shown Ferlium code as single, self-contained snippets.
Real programs are usually larger than that, and Ferlium organises them with **modules**.
A module is the unit of compilation: a named collection of source definitions (functions and types) that the compiler treats as one piece, with its own scope.
Code in one module can refer to items in another using a path like `module::name`.

This chapter explains how modules look from the language side, how the standard library fits in as a module of its own, and the part you may not be used to: in Ferlium, **the host application decides what modules exist**, not the language.

## Referencing items across modules

Suppose a host has loaded a module called `geometry` containing:

```ferlium
fn area(r: float) -> float {
    3.14 * r * r
}
```

From another module, you can call it through its path:

```ferlium,ignore
geometry::area(2.0)
```

The `::` separator joins module names and item names.
Paths can have any depth — a host may organise its API as `physics::collision::detect(...)` or `engine::input::mouse_position()`.

## `use` declarations

Repeating long paths becomes noisy.
A `use` declaration brings a name from another module into the current scope:

```ferlium,ignore
use geometry::area;

area(2.0)
```

You can import several names at once:

```ferlium,ignore
use geometry::{area, perimeter};

area(2.0) + perimeter(2.0)
```

Or import everything a module exposes with the wildcard form:

```ferlium,ignore
use geometry::*;

area(2.0)
```

Grouped imports can also be nested:

```ferlium,ignore
use shapes::{
    circle::{area, perimeter},
    square::side,
};
```

If two `use` declarations bring in the same name, or if a `use` collides with a local definition, the compiler reports an error rather than silently shadowing.

## The standard library is a module

You have already been using a module without knowing it.
Functions like `map`, `filter`, `array_len`, and `idiv` come from `std`, which Ferlium pre-imports into every module with an implicit wildcard `use std::*;`.
You can still write the long form when it helps clarity:

```ferlium
std::array_len([1, 2, 3])
```

is exactly the same as:

```ferlium
array_len([1, 2, 3])
```

## The host decides how modules are organised

This is a key difference from Rust, Python, or JavaScript: **Ferlium itself does not look at the file system**.
A Ferlium script cannot declare a new module with something like `mod foo { ... }`, and there is no `import "./helpers.fer"`.
Modules are created by the application that embeds Ferlium, and that application chooses the layout.

Common layouts you will encounter:

- **The playground.** All the code you type lives in a single module. Cross-module syntax still works for calling into `std`, but you do not see other modules unless the playground exposes them.
- **The REPL.** Each entry you type is compiled as its own module. Later entries can refer to earlier ones by name.
- **An embedding application.** The host might give every user-authored script its own module while exposing host-provided modules for the API — for example, a game engine could expose `engine`, `audio`, and `input`, and put each gameplay script the user writes into its own module that uses them.

The same Ferlium code can therefore live in very different module layouts depending on where it runs.
What stays the same is the language-level syntax for paths and `use` declarations.

## Why this design

Putting module organisation in the host's hands has two practical benefits:

- The host can shape **trust boundaries**: it decides which modules exist, what they contain, and which scripts may reference which.
The language has no ambient I/O, so the host's choice of exposed modules is also the script's entire surface area for interacting with the outside world.
- The host can manage **incremental recompilation**: when a module is changed, every module that depends on it is automatically marked stale and recompiled in dependency order.
This makes IDE-style workflows — including the playground itself — feel instant even on large projects.

## What modules are not (today)

To set expectations:

- A module is the unit of compilation. The dependency graph between modules must be acyclic: if `a` calls into `b`, then `b` cannot call back into `a`.
- There is no in-script module declaration syntax (`mod foo { ... }` is not part of the language).
- There is no file-based module discovery from script source (no `import "./helpers.fer"`).
- There is no separate package distribution format; modules are whatever the host gives you.
- A module name cannot itself be brought into scope as a value (you can `use geometry::area;` but not `use geometry;` to then write `geometry::area(...)` — that form is currently not supported).

These are language-level limits today, not host-level ones: a host can still expose any module layout it wants.

## What comes next

The next section of the book covers Ferlium's standard library — `std` is the first module you have been using all along, and you can now read paths like `std::array_len` fluently.
