// Runtime tests for the code extracted from tests/Monads.lean
// (recursive monad-polymorphic functions are specialized to Id/Option/Except/StateM).

fn[A] lst(xs : Array[A]) -> List[A] {
  let mut l : List[A] = List::Nil
  for k = xs.length() - 1; k >= 0; k = k - 1 {
    l = List::Cons(xs[k], l)
  }
  l
}

fn[A] arr(l : List[A]) -> Array[A] {
  let out = []
  fn go(l : List[A]) {
    match l {
      List::Nil => ()
      List::Cons(x, t) => {
        out.push(x)
        go(t)
      }
    }
  }
  go(l)
  out
}

fn bs(xs : Array[Int]) -> List[BigInt] {
  lst(xs.map(fn(i) { BigInt::from_int(i) }))
}

test "for loops in Id" {
  assert_eq(loopSum(5N), 10N)
  assert_eq(loopSum(0N), 0N)
  assert_eq(sumListLoop(bs([1, 2, 3, 4])), 10N)
  assert_eq(evensBelow(10N), 5N)
}

test "mapM in Option" {
  match mapOpt(bs([1, 2, 3])) {
    Some(l) => assert_eq(arr(l).map(fn(b) { b.to_int() }), [0, 1, 2])
    None => fail("expected some")
  }
  assert_true(mapOpt(bs([1, 0, 3])) is None)
}

test "StateM" {
  assert_eq(runCounter(7N), 7N)
  assert_eq(runCounter(0N), 0N)
}

test "Except loop" {
  assert_eq(checkAll(bs([1, 2, 3])), Ok(6N))
  assert_eq(checkAll(bs([1, 0, 3])), Err("zero found"))
}
