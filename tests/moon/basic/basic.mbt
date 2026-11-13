// Extracted from Lean by lean6x7mbt.

// Helpers

fn lean_nat_div(a : BigInt, b : BigInt) -> BigInt {
  if b == 0 { 0 } else { a / b }
}

fn lean_nat_mod(a : BigInt, b : BigInt) -> BigInt {
  if b == 0 { a } else { a % b }
}

fn lean_int_ediv(a : BigInt, b : BigInt) -> BigInt {
  if b == 0 {
    0
  } else {
    let q = a / b
    let r = a % b
    if r < 0 { if b > 0 { q - 1 } else { q + 1 } } else { q }
  }
}

pub(all) enum Tree[A] {
  Leaf
  Node(Tree[A], A, Tree[A])
}

pub(all) enum List[A] {
  Nil
  Cons(A, List[A])
}

pub(all) struct P_ {
  x : BigInt
  y : Bool
}

pub(all) struct Add_[A] {
  add : (A) -> (A) -> A
}

pub(all) struct OfNat[A] {
  ofNat : A
}

pub(all) struct Point {
  x : BigInt
  y : BigInt
}

pub(all) struct Fin {
  val : BigInt
}

pub(all) struct Subtype[A] {
  val : A
}

pub fn fact(x : BigInt) -> BigInt {
  if x == 0N {
    1N
  } else {
    let n = x - 1N
    (n + 1N) * fact(n)
  }
}

pub fn[A] tree_size(x : Tree[A]) -> BigInt {
  match x {
    Tree::Leaf => 0N
    Tree::Node(a, _, a_2) => (tree_size(a) + 1N) + tree_size(a_2)
  }
}

pub fn tree_insert(t : Tree[BigInt], k : BigInt) -> Tree[BigInt] {
  match t {
    Tree::Leaf => Tree::Node(Tree::Leaf, k, Tree::Leaf)
    Tree::Node(a, a_1, a_2) => if k < a_1 {
      Tree::Node(tree_insert(a, k), a_1, a_2)
    } else {
      Tree::Node(a, a_1, tree_insert(a_2, k))
    }
  }
}

pub fn[A] tree_toList(x : Tree[A]) -> List[A] {
  match x {
    Tree::Leaf => List::Nil
    Tree::Node(a, a_1, a_2) => list_append(list_append(tree_toList(a), List::Cons(a_1, List::Nil)), tree_toList(a_2))
  }
}

pub fn[A, B] mapOpt(f : (A) -> B, x : Option[A]) -> Option[B] {
  match x {
    None => None
    Some(val) => Some(f(val))
  }
}

pub fn p_swap(p : P_) -> P_ {
  P_::{ x: p.x + 1N, y: !p.y }
}

pub fn sumList(x : List[BigInt]) -> BigInt {
  match x {
    List::Nil => 0N
    List::Cons(head, tail) => head + sumList(tail)
  }
}

pub fn[A, B] zip3(x : List[A], x_1 : List[B]) -> List[(A, B)] {
  let alt = fn(_ : List[A]) { fn(_ : List[B]) { List::Nil } }
  match x {
    List::Cons(head, tail) => match x_1 {
      List::Cons(head_1, tail_1) => List::Cons((head, head_1), zip3(tail, tail_1))
      _ => alt(List::Cons(head, tail))(x_1)
    }
    _ => alt(x)(x_1)
  }
}

pub fn gcd_(a : BigInt, b : BigInt) -> BigInt {
  if b == 0N { a } else { gcd_(b, lean_nat_mod(a, b)) }
}

pub fn collatz(n : BigInt, steps : BigInt) -> BigInt {
  if n <= 1N {
    steps
  } else if ({
    let a = lean_nat_mod(n, 2N)
    a == 0N
  }) {
    collatz(lean_nat_div(n, 2N), steps + 1N)
  } else {
    collatz((3N * n) + 1N, steps + 1N)
  }
}

pub fn isFive(x : BigInt) -> Bool {
  if x == 5N { true } else { false }
}

pub fn isEven(x : BigInt) -> Bool {
  if x == 0N {
    true
  } else {
    let n = x - 1N
    isOdd(n)
  }
}

pub fn isOdd(x : BigInt) -> Bool {
  if x == 0N {
    false
  } else {
    let n = x - 1N
    isEven(n)
  }
}

pub fn[A, B, C] compose(g : (B) -> C, f : (A) -> B, x : A) -> C {
  g(f(x))
}

pub fn twice(f : (BigInt) -> BigInt, x : BigInt) -> BigInt {
  f(f(x))
}

pub fn addN(n : BigInt, x : BigInt) -> BigInt {
  x + n
}

pub fn useMap(xs : List[BigInt]) -> List[BigInt] {
  list_map(fn(x : BigInt) { x * 2N }, xs)
}

pub fn sumTo(n : BigInt) -> BigInt {
  sumTo_go(n, 0N)
}

pub fn[A] sumAll(inst : Add_[A], inst_1 : OfNat[A], xs : List[A]) -> A {
  list_foldl(fn(x1 : A) { fn(x2 : A) { (inst.add)(x1)(x2) } }, inst_1.ofNat, xs)
}

pub fn intAbs(i : BigInt) -> BigInt {
  if i < 0N { -i } else { i }
}

pub fn intMix(a : BigInt, b : BigInt) -> BigInt {
  (a * b) - lean_int_ediv((a + b), 2N)
}

pub fn addPoints(a : Point, b : Point) -> Point {
  Point::{ x: a.x + b.x, y: a.y + b.y }
}

pub fn classify(n : BigInt) -> String {
  if n == 0N { "zero" } else if n < 10N { "small" } else { "large" }
}

pub fn safeDiv(a : BigInt, b : BigInt) -> Result[BigInt, String] {
  if b == 0N { Err("div by zero") } else { Ok(lean_nat_div(a, b)) }
}

pub fn sumSafe(xs : List[BigInt]) -> BigInt {
  list_foldl(fn(acc : BigInt) { fn(x : BigInt) { acc + x } }, 0N, xs)
}

pub fn fin3(i : Fin) -> BigInt {
  i.val
}

pub fn useSubtype(n : BigInt) -> BigInt {
  exampleSigma(n).val
}

pub fn[A] list_append(x : List[A], x_1 : List[A]) -> List[A] {
  match x {
    List::Nil => x_1
    List::Cons(head, tail) => List::Cons(head, list_append(tail, x_1))
  }
}

pub fn[A, B] list_map(f : (A) -> B, x : List[A]) -> List[B] {
  match x {
    List::Nil => List::Nil
    List::Cons(head, tail) => List::Cons(f(head), list_map(f, tail))
  }
}

pub fn sumTo_go(k : BigInt, acc : BigInt) -> BigInt {
  if k == 0N {
    acc
  } else {
    let n = k - 1N
    sumTo_go(n, (acc + n) + 1N)
  }
}

pub fn[A, B] list_foldl(f : (A) -> (B) -> A, x : A, x_1 : List[B]) -> A {
  match x_1 {
    List::Nil => x
    List::Cons(head, tail) => list_foldl(f, f(x)(head), tail)
  }
}

pub fn exampleSigma(n : BigInt) -> Subtype[BigInt] {
  Subtype::{ val: n + 1N }
}
