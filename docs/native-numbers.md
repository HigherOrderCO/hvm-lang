# Native numbers

HVM is more than a pure functional programming language. HVM also supports native unsigned 60-bits integers to improve performance.

```rs
two = 2
```

Native integers should be used instead of Scott-encoded natural numbers when performance is needed.

Numbers can also be written in binary or hexadecimal form. Underscores can be optionally used as digit separators to make large numbers more readable.

```rs
decimal =     1194684
binary =      0b100_100_011_101_010_111_100
hexadecimal = 0x123_abc
```

There is also support for native operations. They are written in reverse polish notation and take 2 arguments each.

```rs
some_val = (+ (+ 7 4) (* 2 3))
```
The current operations include `+, -, *, /, %, ==, !=, <, >, <=, >=, &, |, ^, ~, <<, >>`.

HVM-lang also includes a `match` syntax for native numbers. The `0` case is chosen when `n` is 0, and the `+` case is chosen when `n` is greater than 0. The previous number, by default, bound to `n-1`.
```rs
Number.to_church = λn λf λx 
  match n {
    0: x
    +: (f (Number.to_church n-1 f x))
  }
// Alternative syntax
Number.to_church = λn λf λx 
  match n {
    0: x
    +p: (f (Number.to_church p f x))
  }
```

Using everything we learned, we can write a program that calculates the n-th Fibonacci number using native numbers

```rs
fibonacci = λn // n is the argument
  match n {
    // If the number is 0, then return 0
    0: 0
    // If the number is greater than 0, bind the predecessor to `a`
    +a:
    match a {
      // If the predecessor is 0, then return 1
      0: 1
      // Otherwise, bind n-2 to `b` and return the sum of (fib n-1) and (fib n-2)
      +b: (+ (fibonacci a) (fibonacci b))
    }
  }

main = (fibonacci 15)
```
