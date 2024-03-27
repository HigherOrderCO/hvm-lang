zero_succ = @x switch x {
  0: 0
  _: x-1
}

succ_zero = @x switch x {
  _: x-1
  0: 0
}

zero = @x switch x {
  0: 0
}

succ = @x switch x {
  _: x-1
}

succ_zero_succ = @x switch x {
  _: x-1
  0: 0
  _: (+ x-1 1)
}

zero_succ_zero = @x switch x {
  0: 0
  _: x-1
  0: 1
}

zero_zero_succ = @x switch x {
  0: 0
  0: 1
  _: x-1
}

zero_succ_succ = @x switch x {
  0: 0
  _: x-1
  _: (+ x-1 1)
}

main = 0