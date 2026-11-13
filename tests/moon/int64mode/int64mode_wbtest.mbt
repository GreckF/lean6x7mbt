// Runtime tests for the code extracted from tests/Int64Mode.lean.

test "int64 mode" {
  assert_eq(u8m(300L), b'\x2d')
  assert_eq(u32m(4294967301L), 6U)
  assert_eq(u64m(5L), 6UL)
  assert_eq(un(b'\x02', 3U, 4UL), 9L)
  assert_eq(arrm([1L, 2L, 3L], 1L), 20L)
  assert_eq(natOps(13L, 5L), 8L + 2L + 3L + 169L)
  assert_eq(natOps(5L, 13L), 0L + 0L + 5L + 25L)
  assert_eq(natOps(7L, 0L), 7L + 0L + 7L + 49L)
}
