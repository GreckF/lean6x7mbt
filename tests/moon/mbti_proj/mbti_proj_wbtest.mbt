// Runtime checks of tests/MbtiProj.lean (project mode: the generated moon.pkg imports the
// external package extlib).  Expected values computed by hand from tests/moon/extlib/extlib.mbt.

test "project mode with an external package" {
  assert_eq(projSucc(1N), 2N) // succ n = n + 1
  assert_eq(projCounter(10N), 12N) // Counter::new(10).bump(2).get()
  let l = projMapped(@lean_core.List::Cons(1N, @lean_core.List::Nil))
  match l {
    @lean_core.List::Cons(h, _) => assert_eq(h, 3N) // add3(1, 1, 1)
    @lean_core.List::Nil => fail("empty")
  }
  assert_eq(projDepth, 1N) // a single node
}
