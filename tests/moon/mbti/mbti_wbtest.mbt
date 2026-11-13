// Runtime checks of tests/Mbti.lean (functions calling the hand-written MoonBit library
// tests/moon/extlib through `import_mbti`).  The expected values are computed by hand from the
// MoonBit implementation in extlib.mbt (Lean cannot evaluate the imported axioms).

fn[A] to_arr(l : List[A]) -> Array[A] {
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

fn[A] list_of(a : Array[A]) -> List[A] {
  let mut l : List[A] = List::Nil
  for k = a.length() - 1; k >= 0; k = k - 1 {
    l = List::Cons(a[k], l)
  }
  l
}

test "numbers" {
  assert_eq(succTwice(5N), 7N) // succ n = n + 1
  assert_eq(addAll(1N, 2N, 3N), 6N) // add3 = a + b + c
  assert_eq(addOne(10N)(20N), 31N) // add3(1, 10, 20)
  assert_eq(to_arr(mapSucc(list_of([1N, 2N, 3N]))), [2N, 3N, 4N])
  assert_eq(to_arr(mapAdd(list_of([1N, 2N]))), [4N, 5N]) // add3(1, 2, x)
  assert_eq(sumSucc(list_of([1N, 2N, 3N])), 9N) // 2 + 3 + 4
  assert_eq(loopAdd(4N), 10N) // s <- s + i + 1 for i = 0..3: 1, 3, 6, 10
  assert_eq(useMax(5N), 105N) // max_items = 100N
  assert_eq(theAnswer, 42N) // unit_fn() = 42N
  assert_eq(labelledOnly(7N), 7N) // labelled(x=7), y defaults to 0N
}

test "strings, chars, floats, fixed width" {
  assert_eq(greet("hi"), "hi!!") // shout s = s + "!"
  assert_eq(hello, "hello, world") // greeting = "hello"
  assert_true(bothVowels('a', 'e'))
  assert_false(bothVowels('a', 'b'))
  assert_eq(quarter(8.0), 2.0) // halve x = x / 2.0
  assert_eq(lowByteOf(300U).to_int(), 44) // 300 % 256
  assert_eq(bigTwice(3UL), 12UL) // big_u64 n = n * 2
}

test "closures" {
  assert_eq(incTwice(5N), 7N)
  assert_eq(addTwice(1N), 61N) // f x = 10 + 20 + x; f(f(1)) = 61
  assert_eq(succTwiceHO(3N), 5N)
  assert_eq(adder5(1N), 6N) // make_adder(5)(1)
  assert_eq(to_arr(adders(list_of([1N, 2N]))), [101N, 102N])
  // add_curried_pair(f, x) = f(x, x): the curried Lean closure is adapted to a 2-argument closure
  assert_eq(pairSum(fn(a) { fn(b) { a * b } }, 6N), 36N)
  assert_eq(pairSumAdd(4N), 8N)
  assert_eq(pairSumPartial(5N), 1010N) // add3(1000, 5, 5)
  assert_eq(thunk(10N), 11N) // run_thunk(f) = f() + 1
}

test "containers" {
  assert_eq(arrSum([1N, 2N, 3N]), 6N)
  assert_eq(rangeSum(4N), 6N) // 0 + 1 + 2 + 3
  assert_eq(firstEvenOr([1N, 3N, 4N, 6N], 9N), 4N)
  assert_eq(firstEvenOr([1N, 3N], 9N), 9N)
  assert_eq(digitOr("2", 9N), 2N)
  assert_eq(digitOr("x", 9N), 9N)
  assert_eq(digitErr("x"), "not a digit: x")
  assert_eq(digitErr("1"), "")
  assert_eq(swapped(1N, "a"), ("a", 1N))
  assert_eq(incOpt(Some(1N)), Some(2N))
  assert_eq(incOpt(None), None)
  assert_eq(twiceStr("a"), ("a", "a"))
  assert_eq(orDefault(Some(3N)), 3N)
  assert_eq(orDefault(None), 7N)
}

test "opaque types" {
  assert_eq(counterDemo(1N), 16N) // 1 + 5 + 10
  assert_eq(to_arr(counters(list_of([1N, 2N]))), [1N, 2N])
  assert_eq(boxDemo(9N), 9N)
  assert_eq(boxStr("z"), "z")
}

test "enums and structs" {
  assert_eq(areaOf(@extlib.Shape::Circle(2.0)), 12.0) // 3 * r * r
  assert_eq(areaOf(@extlib.Shape::Rect(2.0, 3.0)), 6.0)
  assert_eq(areaOf(@extlib.Shape::Dot), 1.0)
  assert_eq(to_arr(areas), [12.0, 6.0, 1.0])
  assert_eq(shapeName(@extlib.Shape::Rect(2.0, 2.0)), "square")
  assert_eq(shapeName(@extlib.Shape::Rect(2.0, 3.0)), "rect")
  assert_eq(shapeName(@extlib.Shape::Circle(1.0)), "circle")
  assert_eq(shapeName(@extlib.Shape::Dot), "dot")
  assert_eq(treeSum(sampleTree), 10N) // 1 + 2 + 3 + 4
  assert_eq(sampleSize, 4N)
  assert_eq(sampleDepth, 3N) // 2 -> (3 -> 4)
  assert_eq(pointNorm(3N, -4N), 7N) // |3| + |-4|
  let p = @extlib.Point::{ x: 1N, y: 2N }
  assert_eq(pointSum(p), 3N)
  let q = pointSwap(p)
  assert_eq((q.x, q.y), (2N, 1N))
  assert_eq(pointMatch(@extlib.Point::{ x: 3N, y: 4N }), 12N)
  assert_eq((pointLit.x, pointLit.y), (3N, -4N))
}
