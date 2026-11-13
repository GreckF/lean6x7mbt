// A hand-written "existing MoonBit library", used to test `import_mbti`
// (tests/Mbti.lean).  The interface is tests/moon/extlib/pkg.generated.mbti.

///| An opaque type: its representation is private.
pub struct Counter {
  priv value : Int
}

///| Constructor of the opaque type.
pub fn Counter::new(start : BigInt) -> Counter {
  { value: start.to_int() }
}

///| Observer of the opaque type.
pub fn Counter::get(self : Counter) -> BigInt {
  BigInt::from_int(self.value)
}

///| Another function of the opaque type.
pub fn Counter::bump(self : Counter, by : BigInt) -> Counter {
  { value: self.value + by.to_int() }
}

///| A fully public enum.
pub(all) enum Shape {
  Circle(Double)
  Rect(Double, Double)
  Dot
}

///| A fully public struct.
pub(all) struct Point {
  x : BigInt
  y : BigInt
}

///| A generic fully public enum.
pub(all) enum Tree[A] {
  Leaf
  Node(Tree[A], A, Tree[A])
}

pub fn Shape::area(self : Shape) -> Double {
  match self {
    Circle(r) => 3.0 * r * r
    Rect(w, h) => w * h
    Dot => 1.0
  }
}

pub fn Point::norm1(self : Point) -> BigInt {
  let ax = if self.x < 0N { -self.x } else { self.x }
  let ay = if self.y < 0N { -self.y } else { self.y }
  ax + ay
}

pub fn[A] tree_size(t : Tree[A]) -> BigInt {
  match t {
    Leaf => 0N
    Node(l, _, r) => tree_size(l) + 1N + tree_size(r)
  }
}

///| Mathematical successor.
pub fn succ(n : BigInt) -> BigInt {
  n + 1N
}

pub fn add3(a : BigInt, b : BigInt, c : BigInt) -> BigInt {
  a + b + c
}

pub fn shout(s : String) -> String {
  s + "!"
}

pub fn is_vowel(c : Char) -> Bool {
  c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u'
}

pub fn halve(x : Double) -> Double {
  x / 2.0
}

pub fn low_byte(n : UInt) -> Byte {
  (n % 256).to_byte()
}

pub fn big_u64(n : UInt64) -> UInt64 {
  n * 2UL
}

pub fn sum_array(a : Array[BigInt]) -> BigInt {
  let mut s = 0N
  for x in a {
    s = s + x
  }
  s
}

pub fn range_array(n : BigInt) -> Array[BigInt] {
  let out : Array[BigInt] = []
  let mut i = 0N
  while i < n {
    out.push(i)
    i = i + 1N
  }
  out
}

pub fn first_even(a : Array[BigInt]) -> BigInt? {
  for x in a {
    if x % 2N == 0N {
      return Some(x)
    }
  }
  None
}

pub fn parse_digit(s : String) -> Result[BigInt, String] {
  match s {
    "0" => Ok(0N)
    "1" => Ok(1N)
    "2" => Ok(2N)
    _ => Err("not a digit: " + s)
  }
}

pub fn swap_pair(p : (BigInt, String)) -> (String, BigInt) {
  (p.1, p.0)
}

pub fn apply_twice(f : (BigInt) -> BigInt, x : BigInt) -> BigInt {
  f(f(x))
}

pub fn make_adder(n : BigInt) -> (BigInt) -> BigInt {
  fn(x) { x + n }
}

pub fn[A, B] map_option(o : A?, f : (A) -> B) -> B? {
  match o {
    Some(x) => Some(f(x))
    None => None
  }
}

pub fn[A] twice(x : A) -> (A, A) {
  (x, x)
}

pub fn[A] option_or(o : A?, d : A) -> A {
  match o {
    Some(x) => x
    None => d
  }
}

pub fn unit_fn() -> BigInt {
  42N
}

pub let max_items : BigInt = 100N

pub let greeting : String = "hello"

// ---- items that import_mbti must skip with a warning ----

pub fn risky(n : BigInt) -> BigInt raise Failure {
  if n < 0N {
    fail("negative")
  }
  n
}

pub fn small_int(n : Int) -> Int {
  n + 1
}

pub fn add_curried_pair(f : (BigInt, BigInt) -> BigInt, x : BigInt) -> BigInt {
  f(x, x)
}

pub fn triple(a : BigInt) -> (BigInt, BigInt, BigInt) {
  (a, a, a)
}

pub fn labelled(x~ : BigInt, y? : BigInt = 0N) -> BigInt {
  x + y
}

pub trait Describe {
  describe(Self) -> String
}

pub impl Describe for Point with describe(self) {
  "(" + self.x.to_string() + ", " + self.y.to_string() + ")"
}

pub fn[T : Describe] describe_all(xs : Array[T]) -> String {
  let mut s = ""
  for x in xs {
    s = s + x.describe()
  }
  s
}

pub async fn later(n : BigInt) -> BigInt {
  n
}

pub suberror Oops {
  Oops(String)
}

pub const LIMIT : Int = 10

pub type Index = Int

pub fn first_byte(b : Bytes) -> Byte {
  b[0]
}

// ---- more items ----

///| A generic opaque type.
pub struct Box[A] {
  priv v : A
}

pub fn[A] Box::new(a : A) -> Box[A] {
  { v: a }
}

pub fn[A] Box::get(self : Box[A]) -> A {
  self.v
}

pub fn[A] Tree::depth(self : Tree[A]) -> BigInt {
  match self {
    Leaf => 0N
    Node(l, _, r) => {
      let a = l.depth()
      let b = r.depth()
      1N + (if a > b { a } else { b })
    }
  }
}

pub fn make_binop() -> (BigInt, BigInt) -> BigInt {
  fn(a, b) { a * b }
}

pub fn run_thunk(f : () -> BigInt) -> BigInt {
  f() + 1N
}
