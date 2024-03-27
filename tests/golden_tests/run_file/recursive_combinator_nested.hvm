// Tests that `({Foo @* a} 9)` is correctly extracted as a combinator, otherwise the file would hang when running
Foo = @a switch a {
  0: (#a {Foo @* a} 9);
  _: a-1
}

main = (Foo 0)
