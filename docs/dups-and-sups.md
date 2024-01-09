# Dups and sups

Term duplication is done automatically when a variable is used more than once. But it's possible to manually duplicate a term using `dup`:
```rs
// the number 2 in church encoding using dup.
ch2 = λf λx dup f1 f2 = f; (f1 (f2 x))

// the number 3 in church encoding using dup.
ch3 = λf λx dup f0 f1 = f; dup f2 f3 = f0; (f1 (f2 (f3 x)))
```

A `sup` is a superposition of two values, it is defined using curly brackets with two terms inside. A superposition is the opposite of a duplication.
```rs
sup = {3 7}
```

Sups can be used anywhere a value is expected, if anything interacts with the superposition, the result is the superposition of that interaction on both the possible values:

```rs
mul = λa λb (* a b)
result     = (mul 2 5)         // returns 10
result_sup = (mul 2 {5 7})     // returns {10 14}
multi_sup  = (mul {2 3} {5 7}) // returns {{10 14} {15 21}}
```

To access both values of a superposition, `dups` with labels are needed.  
A `dup` generally just duplicates the term it points to:

```rs
// each dup variable now has a copy of the {1 2} superposition
dup x1 x2 = {1 2}
```

Both `dups` and `sups` support labels, that is, a field starting with `#` to identify their counterpart:
```rs
// here, x1 now contains the value of 1, and x2 the value of 2
dup #i x1 x2 = {#i 1 2}
```

Due to how dups are compiled, dup tags between two interacting terms should not contain the same label. For example, an application of the church numeral 2 with itself won't reduce as expected:

```rs
c2 = λf λx dup f1 f2 = f; (f1 (f2 x))
main = (c2 c2)
```

To avoid label collision, HVM-Lang automatically generates new dup labels for each dup in the code. But with cases like the example above, when the interacting dups comes from the same place, the result is an invalid reduction.

This is not *incorrect* behavior or *undefined* behaviour. It is incorrect only if we treat HVM as a λ-calculus reduction engine, which isn't true. However, there are some cases where HVM diverges from λ-calculus, and this is one of them.

To fix the problem, its necessary to re-create the term so that a new label is assigned, or manually assign one:
```rs
c2  = λf λx dup        f1 f2 = f; (f1 (f2 x))
c2_ = λf λx dup #label f1 f2 = f; (f1 (f2 x))
main = (c2 c2_)
```
