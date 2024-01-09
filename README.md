# HVM-Lang

HVM-Lang is a lambda-calculus based language and serves as an Intermediate Representation for HVM-Core, offering a higher level syntax for writing programs based on the [Interaction-Calculus](https://github.com/VictorTaelin/Interaction-Calculus#interaction-calculus).

## Installation

With the nightly version of rust installed, clone the repository:
```bash
git clone https://github.com/HigherOrderCO/hvm-lang.git

cd hvm-lang
```

Install using cargo:
```bash
cargo install --path .
```

## Usage

First things first, let's write a basic program that adds the numbers 3 and 2.

```hs
main = (+ 3 2)
```

HVM-Lang searches for the `main | Main` definitions as entrypoint of the program.

To run a program, use the `run` argument:
```bash
hvml run <file>
```

It will show the number 5.
Adding the `--stats` option displays some runtime stats like time and rewrites.

To limit the runtime memory, use the `--mem <size> option.` The default is 1GB:
```bash
hvml --mem 65536 run <file>
```
You can specify the memory size in bytes (default), kilobytes (k), megabytes (m), or gigabytes (g), e.g., `--mem 200m.`

To compile a program use the `compile` argument:
```bash
hvml compile <file>
```
This will output the compiled file to stdout.

## Syntax


HVM-Lang files consists of a series of definitions, which bind a name to a term. Terms can be lambdas, applications, or other terms.

Here's a lambda where the body is the variable `x`:
```rs
id = λx x
```

Lambdas can also be defined using `@`. 
To discard the variable and not bind it to any name, use `*`:
```hs
True  = @t @* t
False = λ* λf f
```

Applications are enclosed by `(` `)`.
```rs
(λx x λx x λx x)
```
This term is the same as:
```rs
(((λx x) (λx x)) (λx x))
```
Parentheses around lambdas are optional. Lambdas have a high precedence

```rust
(λx a b) == ((λx a) b) != (λx (a b))
```

`*` can also be used to define an eraser term.  
It compiles to an `inet` node with only one port that deletes anything that’s plugged into it.
```rs
era = *
```

A let term binds some value to the next term, in this case `(* result 2)`:
```rs
let result = (+ 1 2); (* result 2)
```

It is possible to define tuples:
```rs
tup = (2, 2)
```

And destructuring tuples with `let`:
```rs
let (x, y) = tup; (+ x y)
```

### Advanced features

Advanced features are described in other files:

- Duplications and superpositions: [Dups and sups](docs/dups-and-sups.md)
- Data types: [Defining data types](docs/defining-data-types.md)
- Native numbers and operations: [Native numbers](docs/native-numbers.md)
- Scopeless lambdas: [Using scopeless lambdas](docs/using-scopeless-lambdas.md)
- Tagged lambdas and applications: [Automatic vectorization with tagged lambdas](docs/automatic-vectorization-with-tagged-lambdas.md)
- Lazy definitions: [Making recursive definitions lazy](docs/lazy-definitions.md)

## Further reading

- [Compilation and readback](docs/compilation-and-readback.md)
- [Old HVM wiki learning material](https://github.com/HigherOrderCO/HVM/wiki/HVM-Wiki). It is outdated, but it can still teach you some of the basics.