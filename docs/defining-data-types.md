# Defining data types

It is possible to define complex data types using the `data` keyword.

```rs
// A Boolean is either True or False
data Bool = True | False
```

If a constructor has any arguments, parentheses are necessary around it:
```rs
// An option either contains some value, or None
data Option = (Some val) | None
```

If the data type has a single constructor, it can be destructured using `let`:
```rs
// A Box is a wrapper around a valuee.
data Boxed = (Box val)

let (Box value) = boxed; value
```

For more complex types, there are two pattern syntaxes for matching on data types.  

One of them binds implicitly the matched variable name plus `.` and the field names on each constructor:

```rs
Option.map = λoption λf
  match option {
    Some: (Some (f option.val))
    None: None
  }
```

And another one which deconstructs the matched variable with explicit bindings:

```rs
Option.map = λoption λf
  match option {
    (Some value): (Some (f value))
    (None): None
  }
```

Rules can also have patterns.
They work like match expressions with explicit bindings:

```rs
(Option.map (Some value) f) = (Some (f value))
(Option.map None f) = None
```

However, they also allow matching on multiple values at once, which is something that regular `match` can't do:

```rs
data Boolean = True | False

(Option.is_both_some (Some lft_val) (Some rgt_val)) = True
(Option.is_both_some lft rgt) = False
```

In conclusion, the `data` keyword is very useful as it allows you easily create data types and deconstruct them.