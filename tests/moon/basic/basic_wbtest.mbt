// Runtime tests for the code extracted from tests/Basic.lean.

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

test "arithmetic" {
  assert_eq(fact(5N), 120N)
  assert_eq(fact(25N), 15511210043330985984000000N)
  assert_eq(gcd_(12N, 18N), 6N)
  assert_eq(collatz(27N, 0N), 111N)
  assert_eq(addN(2N, 3N), 5N)
  assert_eq(twice(fn(x) { x * 3N }, 2N), 18N)
  assert_eq(sumTo(10N), 55N)
  assert_eq(intAbs(-5N), 5N)
  assert_eq(intMix(7N, -3N), -21N - 2N)
}

test "booleans and literals" {
  assert_true(isFive(5N))
  assert_false(isFive(6N))
  assert_true(isEven(10N))
  assert_false(isEven(7N))
  assert_true(isOdd(7N))
}

test "lists" {
  assert_eq(sumList(bs([1, 2, 3, 4])), 10N)
  assert_eq(ints(useMap(bs([1, 2, 3]))), [2, 4, 6])
  assert_eq(sumSafe(bs([5, 6, 7])), 18N)
  let z = zip3(bs([1, 2, 3]), lst(["a", "b"]))
  assert_eq(arr(z).map(fn(p) { p.1 }), ["a", "b"])
  assert_eq(ints(compose(fn(l : List[BigInt]) { l }, fn(l : List[BigInt]) { l }, bs([1]))), [1])
}

test "trees" {
  let mut t : Tree[BigInt] = Tree::Leaf
  for x in [5, 2, 8, 1, 9, 3] {
    t = tree_insert(t, BigInt::from_int(x))
  }
  assert_eq(tree_size(t), 6N)
  assert_eq(ints(tree_toList(t)), [1, 2, 3, 5, 8, 9])
}

test "structures and options" {
  let p = p_swap({ x: 1N, y: true })
  assert_eq(p.x, 2N)
  assert_false(p.y)
  let q = addPoints({ x: 1N, y: 2N }, { x: 10N, y: 20N })
  assert_eq(q.x, 11N)
  assert_eq(q.y, 22N)
  assert_eq(mapOpt(fn(x : Int) { x + 1 }, Some(1)), Some(2))
  assert_eq(mapOpt(fn(x : Int) { x + 1 }, None), None)
  assert_eq(useSubtype(4N), 5N)
  assert_eq(fin3({ val: 2N }), 2N)
}

test "strings and results" {
  assert_eq(classify(0N), "zero")
  assert_eq(classify(5N), "small")
  assert_eq(classify(50N), "large")
  assert_eq(safeDiv(7N, 2N), Ok(3N))
  assert_eq(safeDiv(7N, 0N), Err("div by zero"))
}
