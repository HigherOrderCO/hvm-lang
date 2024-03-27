sum_pred = @a @b switch a {
  0: switch b {
    0: 0
    _: b-1
  };
  _: switch b {
    0: a-1
    _: (+ a-1 b-1)
  }
}

main = (sum_pred 8 5)
