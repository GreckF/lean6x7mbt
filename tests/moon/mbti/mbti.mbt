// Extracted from Lean by lean6x7mbt.

// Helpers

fn lean_float_of_scientific(m : BigInt, neg : Bool, e : BigInt) -> Double {
  let mut x = BigInt::to_int64(m).to_double()
  let mut k = BigInt::to_int(e)
  while k > 0 {
    if neg { x = x / 10.0 } else { x = x * 10.0 }
    k = k - 1
  }
  x
}

pub(all) enum List[A] {
  Nil
  Cons(A, List[A])
}

pub(all) enum ForInStep[A] {
  Done(A)
  Yield(A)
}

pub(all) struct Std_Legacy_Range {
  start : BigInt
  stop : BigInt
  step : BigInt
}

pub fn succTwice(n : BigInt) -> BigInt {
  @extlib.succ(@extlib.succ(n))
}

pub fn addAll(a : BigInt, b : BigInt, c : BigInt) -> BigInt {
  @extlib.add3(a, b, c)
}

pub let addOne : (BigInt) -> (BigInt) -> BigInt = fn(a : BigInt) { fn(a_1 : BigInt) { @extlib.add3(1N, a, a_1) } }

pub fn mapSucc(xs : List[BigInt]) -> List[BigInt] {
  list_map(fn(a : BigInt) { @extlib.succ(a) }, xs)
}

pub fn mapAdd(xs : List[BigInt]) -> List[BigInt] {
  list_map(fn(a : BigInt) { @extlib.add3(1N, 2N, a) }, xs)
}

pub fn sumSucc(xs : List[BigInt]) -> BigInt {
  let acc = 0N
  let acc_1 = list_forIn__loop_spec1(xs, fn(a : BigInt) {
    fn(r : BigInt) {
      let acc_1 = r
      let acc_2 = acc_1 + @extlib.succ(a)
      ForInStep::Yield(acc_2)
    }
  }, xs, acc)
  acc_1
}

pub fn loopAdd(n : BigInt) -> BigInt {
  let s = 0N
  let s_1 = {
    let range = Std_Legacy_Range::{ start: 0N, stop: n, step: 1N }
    std_Legacy_Range_forIn__loop_spec2(range, fn(a : BigInt) {
      fn(r : BigInt) {
        let s_1 = r
        let s_2 = @extlib.add3(s_1, a, 1N)
        ForInStep::Yield(s_2)
      }
    }, s, range.start)
  }
  s_1
}

pub fn greet(s : String) -> String {
  @extlib.shout(@extlib.shout(s))
}

pub fn bothVowels(a : Char, b : Char) -> Bool {
  @extlib.is_vowel(a) && @extlib.is_vowel(b)
}

pub fn quarter(x : Double) -> Double {
  @extlib.halve(@extlib.halve(x))
}

pub fn lowByteOf(n : UInt) -> Byte {
  @extlib.low_byte(n)
}

pub fn bigTwice(x : UInt64) -> UInt64 {
  @extlib.big_u64(@extlib.big_u64(x))
}

pub fn useMax(n : BigInt) -> BigInt {
  n + @extlib.max_items
}

pub let hello : String = @extlib.greeting + ", world"

pub let theAnswer : BigInt = @extlib.unit_fn()

pub fn labelledOnly(n : BigInt) -> BigInt {
  @extlib.labelled(x=n)
}

pub fn incTwice(x : BigInt) -> BigInt {
  @extlib.apply_twice((fn(y : BigInt) { y + 1N }), x)
}

pub fn addTwice(x : BigInt) -> BigInt {
  @extlib.apply_twice((fn(a : BigInt) { @extlib.add3(10N, 20N, a) }), x)
}

pub fn succTwiceHO(x : BigInt) -> BigInt {
  @extlib.apply_twice((fn(a : BigInt) { @extlib.succ(a) }), x)
}

pub fn adder5(x : BigInt) -> BigInt {
  @extlib.make_adder(5N)(x)
}

pub fn adders(xs : List[BigInt]) -> List[BigInt] {
  list_map(fn(a : BigInt) { @extlib.make_adder(100N)(a) }, xs)
}

pub fn pairSum(f : (BigInt) -> (BigInt) -> BigInt, x : BigInt) -> BigInt {
  @extlib.add_curried_pair(fn(lean_p0_0, lean_p0_1) { (f)(lean_p0_0)(lean_p0_1) }, x)
}

pub fn pairSumAdd(x : BigInt) -> BigInt {
  @extlib.add_curried_pair(fn(lean_p0_0, lean_p0_1) { ((fn(a : BigInt) { fn(b : BigInt) { a + b } }))(lean_p0_0)(lean_p0_1) }, x)
}

pub fn pairSumPartial(x : BigInt) -> BigInt {
  @extlib.add_curried_pair(fn(lean_p0_0, lean_p0_1) { ((fn(a : BigInt) { fn(a_1 : BigInt) { @extlib.add3(1000N, a, a_1) } }))(lean_p0_0)(lean_p0_1) }, x)
}

pub fn thunk(n : BigInt) -> BigInt {
  @extlib.run_thunk(fn() { ((fn(_ : Unit) { n }))(()) })
}

pub fn arrSum(a : Array[BigInt]) -> BigInt {
  @extlib.sum_array(a)
}

pub fn rangeSum(n : BigInt) -> BigInt {
  @extlib.sum_array(@extlib.range_array(n))
}

pub fn firstEvenOr(a : Array[BigInt], d : BigInt) -> BigInt {
  match @extlib.first_even(a) {
    None => d
    Some(val) => val
  }
}

pub fn digitOr(s : String, d : BigInt) -> BigInt {
  match @extlib.parse_digit(s) {
    Err(_) => d
    Ok(a) => a
  }
}

pub fn digitErr(s : String) -> String {
  match @extlib.parse_digit(s) {
    Err(a) => a
    Ok(_) => ""
  }
}

pub fn swapped(n : BigInt, s : String) -> (String, BigInt) {
  @extlib.swap_pair((n, s))
}

pub fn incOpt(o : Option[BigInt]) -> Option[BigInt] {
  @extlib.map_option(o, (fn(x : BigInt) { x + 1N }))
}

pub fn twiceStr(s : String) -> (String, String) {
  @extlib.twice(s)
}

pub fn orDefault(o : Option[BigInt]) -> BigInt {
  @extlib.option_or(o, 7N)
}

pub fn counterDemo(n : BigInt) -> BigInt {
  @extlib.Counter::get(@extlib.Counter::bump(@extlib.Counter::bump(@extlib.Counter::new(n), 5N), 10N))
}

pub fn counters(xs : List[BigInt]) -> List[BigInt] {
  list_map(fn(a : @extlib.Counter) { @extlib.Counter::get(a) }, list_map(fn(a : BigInt) { @extlib.Counter::new(a) }, xs))
}

pub fn boxDemo(n : BigInt) -> BigInt {
  @extlib.Box::get(@extlib.Box::new(n))
}

pub fn boxStr(s : String) -> String {
  @extlib.Box::get(@extlib.Box::new(s))
}

pub fn areaOf(s : @extlib.Shape) -> Double {
  @extlib.Shape::area(s)
}

pub let areas : List[Double] = list_map(fn(a : @extlib.Shape) { @extlib.Shape::area(a) }, List::Cons(@extlib.Shape::Circle(lean_float_of_scientific(20N, true, 1N)), List::Cons(@extlib.Shape::Rect(lean_float_of_scientific(20N, true, 1N), lean_float_of_scientific(30N, true, 1N)), List::Cons(@extlib.Shape::Dot, List::Nil))))

pub fn shapeName(s : @extlib.Shape) -> String {
  match s {
    @extlib.Shape::Circle(_) => "circle"
    @extlib.Shape::Rect(a, a_1) => if a == a_1 { "square" } else { "rect" }
    @extlib.Shape::Dot => "dot"
  }
}

pub let sampleTree : @extlib.Tree[BigInt] = @extlib.Tree::Node(@extlib.Tree::Node(@extlib.Tree::Leaf, 1N, @extlib.Tree::Leaf), 2N, @extlib.Tree::Node(@extlib.Tree::Leaf, 3N, @extlib.Tree::Node(@extlib.Tree::Leaf, 4N, @extlib.Tree::Leaf)))

pub fn treeSum(x : @extlib.Tree[BigInt]) -> BigInt {
  match x {
    @extlib.Tree::Leaf => 0N
    @extlib.Tree::Node(a, a_1, a_2) => (treeSum(a) + a_1) + treeSum(a_2)
  }
}

pub let sampleSize : BigInt = @extlib.tree_size(sampleTree)

pub let sampleDepth : BigInt = @extlib.Tree::depth(sampleTree)

pub fn pointNorm(a : BigInt, b : BigInt) -> BigInt {
  @extlib.Point::norm1(@extlib.Point::{ x: a, y: b })
}

pub fn pointSum(p : @extlib.Point) -> BigInt {
  p.x + p.y
}

pub fn pointSwap(p : @extlib.Point) -> @extlib.Point {
  @extlib.Point::{ x: p.y, y: p.x }
}

pub fn pointMatch(p : @extlib.Point) -> BigInt {
  match p {
    { x: x, y: y } => x * y
  }
}

pub let pointLit : @extlib.Point = @extlib.Point::{ x: 3N, y: (-4N) }

pub fn[A, B] list_map(f : (A) -> B, x : List[A]) -> List[B] {
  match x {
    List::Nil => List::Nil
    List::Cons(head, tail) => List::Cons(f(head), list_map(f, tail))
  }
}

pub fn[A, B] list_forIn__loop_spec1(as_ : List[A], f : (A) -> (B) -> ForInStep[B], x : List[A], x_1 : B) -> B {
  match x {
    List::Nil => x_1
    List::Cons(head, tail) => match f(head)(x_1) {
      ForInStep::Done(a) => a
      ForInStep::Yield(a) => list_forIn__loop_spec1(as_, f, tail, a)
    }
  }
}

pub fn[A] std_Legacy_Range_forIn__loop_spec2(range : Std_Legacy_Range, f : (BigInt) -> (A) -> ForInStep[A], b : A, i : BigInt) -> A {
  if i < range.stop {
    match f(i)(b) {
      ForInStep::Done(a) => a
      ForInStep::Yield(a) => std_Legacy_Range_forIn__loop_spec2(range, f, a, i + range.step)
    }
  } else {
    b
  }
}

pub let unit_unit : Unit = ()
