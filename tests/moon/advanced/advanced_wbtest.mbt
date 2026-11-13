// Runtime tests for the code extracted from tests/Advanced.lean.

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

fn ints(l : List[BigInt]) -> Array[Int] {
  arr(l).map(fn(b) { b.to_int() })
}

test "monads" {
  assert_eq(addOpt(Some(1N), Some(2N)), Some(3N))
  assert_eq(addOpt(Some(1N), None), None)
  match divAll(bs([10, 20]), 5N) {
    Ok(l) => assert_eq(ints(l), [2, 4])
    Err(_) => fail("unexpected error")
  }
  match divAll(bs([10, 20]), 0N) {
    Ok(_) => fail("expected error")
    Err(e) => assert_eq(e, "zero")
  }
}

test "deriving and structures" {
  assert_true(sameColor(Color::Red, Color::Red))
  assert_false(sameColor(Color::Red, Color::Blue))
  assert_true(sameColor(color_next(Color::Blue), Color::Red))
  assert_true(sameColor(defColor, Color::Red))
  let c = config_bump({ name: "a", size: 1N, flag: true })
  assert_eq(c.size, 2N)
  assert_eq(c.name, "a")
}

test "expressions" {
  let e = Expr::Add(Expr::Num(0N), Expr::Mul(Expr::Num(1N), Expr::Neg(Expr::Num(7N))))
  assert_eq(expr_eval(e), -7N)
  let s = expr_simp(e)
  assert_eq(expr_eval(s), -7N)
  match s {
    Expr::Neg(Expr::Num(n)) => assert_eq(n, 7N)
    _ => fail("not simplified")
  }
}

test "lists and patterns" {
  let ps = pairs(bs([1, 2, 3, 4, 5]))
  assert_eq(arr(ps).map(fn(p) { (p.0.to_int(), p.1.to_int()) }), [(1, 2), (3, 4)])
  assert_eq(firstOr(bs([]), 9N), 9N)
  assert_eq(firstOr(bs([4, 5]), 9N), 4N)
  assert_eq(lastOf(bs([4, 5, 6])), Some(6N))
  assert_eq(lastOf(bs([])), None)
  assert_eq(lengthOf(bs([1, 2, 3])), 3N)
  assert_eq(ints(rev(bs([1, 2, 3]))), [3, 2, 1])
  assert_eq(ints(filterEven(bs([1, 2, 3, 4]))), [2, 4])
}

test "bignums and classes" {
  assert_eq(bigMul(2N), 246913578024691357802469135780N)
  assert_eq(rectArea({ w: 3N, h: 4N }), 12N)
  assert_eq(squares(lst([{ s: 2N }, { s: 3N }])), 13N)
}
