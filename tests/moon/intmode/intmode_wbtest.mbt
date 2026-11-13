test "int mode" {
  assert_eq(fact(5), 120)
  assert_eq(sub3(10), 7)
  assert_eq(sub3(2), 0)
  assert_eq(collatz(27, 0), 111)
  assert_eq(ediv(7, 2), 3)
  assert_eq(ediv(-7, 2), -4)
  assert_eq(emod(-7, 2), 1)
  assert_eq(ediv(7, 0), 0)
  assert_eq(powTwo(10), 1024)
}
