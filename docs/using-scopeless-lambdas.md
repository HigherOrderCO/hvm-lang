# Using scopeless lambdas

Scopeless lambdas are very powerful lambdas that are a side-effect of HVM's internal representation for lambda terms.

Scopeless lambdas are lambdas that have no scope. The variables bound by them can be used outside the lambda's body. They can be created by prefixing a dollar symbol (`$`) to a lambda's variable name.

```rs
λ$x $x // The identity function as a scopeless lambda
```

Of course, using scopeless lambdas as a replacement for regular lambdas is kind of pointless. Their real power comes from being able to use the bound variable outside the body:

```rs
main = (((λ$x 1) 2), $x)
// ---- x gets replaced by 2 and application gets replaced by 1
// Outputs (1, 2)
```

Take some time to think about the program above. It is valid, despite `$x` being used outside the body.

## Duplicating scopeless lambdas

We have seen that the variable bound to a scopeless lambda gets set when the lambda is called. But, what happens if we never call `λ$x 1`? What will `$x` get set to then? Here is a program that does that:

```rs
main = // TODO bug in hvm-lang
	let _ = λ$x 1 // Discard and erase the scopeless lambda
	(2, $x)
```
Output:
```rs
(2, *)
```

The program outputs `2` as the first item of the tuple, as expected. But the second item is `*`! What is `*`?

`*` (called ERA or eraser) is a special term HVM uses when a value was erased. This is what happened to `$x`. We erased `λ$x 1` when we discarded it, which led to `$x` being erased.

What happens if we call `λ$x 1` with two different values instead? 

Try to answer this with your knowledge of HVM. Will it throw a runtime error? Will it return something unexpected?

```rs
main =
	let f = λ$x 1 // Assign the lambda to a variable
	((f 2), ((f 3), $x)) // Return a tuple of (f 2) and another tuple.
```
Output:
```
(1, (1, {#0 3 2}))
```

What? This is even more confusing. The first two values are `1`, as expected. But what about the last term?

The last term in the tuple is a **superposition** of two values. A [superposition](docs/dups-and-sups.md) is the "other side" of a duplication. It is created here because we implicitly duplicated `f` when we used it twice, and duplicating lambdas creates superpositions.

## Usage

Now that we know how scopeless lambdas work, we can make programs using them. An example of a function that is usually thought as "primitive", but can be implemented using scopeless lambdas is **call/cc**. 

Callcc is a function that takes a function that takes a parameter `k`. When `k` is called with an argument, `callcc` returns it.

TODO: Code
