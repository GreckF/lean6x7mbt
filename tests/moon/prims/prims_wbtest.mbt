// Runtime tests for the code extracted from tests/Prims.lean.

test "arrays" {
  let a = [1N, 2N, 3N]
  assert_eq(arrSum(a), 6N)
  let b = arrPush(a, 4N)
  assert_eq(b.length(), 4)
  assert_eq(a.length(), 3) // persistence: the original is untouched
  assert_eq(arrGet(b, 3N), 4N)
  assert_eq(arrGetD(b, 10N), 0N)
  assert_eq(arrSize(b), 4N)
  assert_eq(arrMap(a), [2N, 3N, 4N])
  assert_eq(mkArr, [1N, 2N, 3N])
  let c = arrSet(a, 1N, 20N)
  assert_eq(c, [1N, 20N, 3N])
  assert_eq(a, [1N, 2N, 3N])
}

test "strings, chars, fixed width" {
  assert_eq(str1("hi"), "hi!")
  assert_eq(strLen("hello"), 5N)
  assert_eq(chr(97N), 'a')
  assert_eq(u64(3UL, 4UL), 13UL)
  assert_eq(u64(18446744073709551615UL, 2UL), 18446744073709551615UL * 2UL + 1UL)
  assert_eq(u8(100), (100 + 200).to_byte())
  assert_eq(nToStr(12345N), "12345")
}

test "floats" {
  assert_eq(flt(2.0), 5.0)
}
