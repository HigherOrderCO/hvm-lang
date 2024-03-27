lambda_out = @x @$y switch x {
  0: $y
  _: x-1
}

lambda_in = @x (switch x {
  0: @x x
  _: @$y x-1
} $y)

main = *