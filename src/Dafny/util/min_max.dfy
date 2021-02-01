module MinMax {
  function method min(x: int, y: int): int
  {
    if x < y then x else y
  }

  function method max(x: int, y: int): int
  {
    if x < y then y else x
  }
}
