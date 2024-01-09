# Compilation and readback

How are terms compiled to interaction net nodes?

HVM-Core has a bunch of useful nodes to write IC programs.
Every node contains one `main` port `0` and two `auxiliary` ports, `1` and `2`.

There are 6 kinds of nodes, Eraser, Constructor, Reference, Number, Operation and Match.

A lambda `λx x` compiles into a Constructor node.
An application `((λx x) (λx x))` also compiles into a Constructor node.

```
  0 - Points to the lambda occurrence      0 - Points to the function
  |                                        |
  λ Lambda                                 @ Application
 / \                                      / \
1   2 - Points to the lambda body        1   2 - Points to the application occurrence
|                                        |
Points to the lambda variable            Points to the argument
```

When reading back, if we visit a Constructor via port 0 then we know it's a lambda, and if we visit it via port 2 it's an application.

- The `Number` node uses the label to store it's number.
- An `Op2` node uses the label to store it's operation.
- And a `Constructor` node can have a label too! This is used for `dup` and [lambda tags](docs/automatic-vectorization-with-tagged-lambdas.md.

A duplication `dup a b = x` compiles into a Constructor node too, but with a different label.
A superposition `{a b}` compiles to a Constructor node too. The difference here comes from context too.

Additionally, nodes have labels. We use the label to store data in the node's memory, which can be used for various purposes.

```
  0 - Points to the sup occurence          0 - Points to the duplicated value
  |                                        |
  # Superposition                          # Duplication
 / \                                      / \
1   2 - Points to the second value       1   2 - Points to the second binding
|                                        |
Points to the first value                Points to the first binding
```

Check out [HVM-Core](https://github.com/HigherOrderCO/hvm-core/tree/main#language), one of the Higher Order Company's projects, to know more about this.
