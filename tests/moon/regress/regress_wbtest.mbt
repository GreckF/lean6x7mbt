// Runtime tests for the code extracted from tests/Regress.lean.
// Expected values are what Lean's `#eval` prints.

fn[A] la(l : List[A]) -> Array[A] {
  let out : Array[A] = []
  let mut cur = l
  while true {
    match cur {
      List::Nil => break
      List::Cons(h, t) => {
        out.push(h)
        cur = t
      }
    }
  }
  out
}

test "no duplicated work" {
  assert_eq(t_depth(T_::Node(T_::Node(T_::Leaf, T_::Leaf), T_::Leaf)), 2N)
  // 2^60 calls if `max` evaluates its arguments twice
  let mut t = T_::Leaf
  for i = 0; i < 60; i = i + 1 {
    t = T_::Node(t, T_::Leaf)
  }
  assert_eq(t_depth(t), 60N)
  assert_eq(mx(3N, 9N), 6N)
  assert_eq([mdisc(5N), mdisc(0N), mdisc(2N)], [3N, 1N, 5N])
  assert_eq(sq(fn(x) { x + 1N }, 3N), 20N)
}

test "templates without placeholders" {
  assert_eq(mk0(3N), [3N])
}

test "strings" {
  assert_eq(la(strOps("ab", 'z')), [
    "abz", "42", "[2]", "-5", "true", "abab", "z", "[1, 2]", "(some 3)", "z", "ab, ab",
  ])
  assert_eq(la(strB("ab", "a")), [false, true, false])
  assert_eq(la(strB("", "")), [true, false, true])
}

test "chars" {
  assert_eq(la(chUp('a')), ['A', 'a'])
  assert_eq(la(chUp('Q')), ['Q', 'q'])
  assert_eq(la(chUp('1')), ['1', '1'])
  assert_eq(la(chB('x')), [false, true, true, false, false])
  assert_eq(la(chB('7')), [true, false, false, true, false])
  assert_eq(la(chB(' ')), [false, false, false, true, true])
}

test "array loop" {
  assert_eq(arrLoop([1N, 2N, 3N, 5N, 7N]), 4N)
}
