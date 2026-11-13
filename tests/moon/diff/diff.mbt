// Extracted from Lean by lean6x7mbt.

// Helpers

fn lean_nat_sub(a : BigInt, b : BigInt) -> BigInt {
  if a > b { a - b } else { 0 }
}

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

fn lean_int_emod(a : BigInt, b : BigInt) -> BigInt {
  if b == 0 {
    a
  } else {
    let r = a % b
    if r < 0 { if b > 0 { r + b } else { r - b } } else { r }
  }
}

fn lean_int_natabs(a : BigInt) -> BigInt {
  if a < 0 { -a } else { a }
}

fn[A] lean_array_of_list(l : List[A]) -> Array[A] {
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

fn lean_char_of_nat(n : BigInt) -> Char {
  if n < 55296 || (n > 57343 && n < 1114112) {
    BigInt::to_int(n).unsafe_to_char()
  } else {
    '\u{0}'
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

pub(all) struct Pt {
  x : BigInt
  y : BigInt
  tag : String
}

pub(all) enum Shape {
  Circle(BigInt)
  Rect(BigInt, BigInt)
  Empty
}

pub(all) struct BEq[A] {
  beq : (A) -> (A) -> Bool
}

pub(all) struct NatCast[A] {
  natCast : (BigInt) -> A
}

pub fn arith(a : BigInt, b : BigInt) -> BigInt {
  lean_nat_sub(((a * b) + lean_nat_div(a, (b + 1N))), lean_nat_mod(b, 3N)) + (lean_nat_sub(a, b) * 2N)
}

pub fn intArith(a : BigInt, b : BigInt) -> BigInt {
  (((a * b) - lean_int_ediv((a + b), 2N)) + lean_int_emod(a, 3N)) - nat_cast(instNatCastInt)(lean_int_natabs(b))
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

pub fn[A] tree_size(x : Tree[A]) -> BigInt {
  match x {
    Tree::Leaf => 0N
    Tree::Node(a, _, a_2) => (tree_size(a) + 1N) + tree_size(a_2)
  }
}

pub fn[A] tree_toList(x : Tree[A]) -> List[A] {
  match x {
    Tree::Leaf => List::Nil
    Tree::Node(a, a_1, a_2) => list_append(list_append(tree_toList(a), List::Cons(a_1, List::Nil)), tree_toList(a_2))
  }
}

pub fn fromList(xs : List[BigInt]) -> Tree[BigInt] {
  list_foldl(fn(t : Tree[BigInt]) { fn(k : BigInt) { tree_insert(t, k) } }, Tree::Leaf, xs)
}

pub let t0 : Tree[BigInt] = fromList(List::Cons(5N, List::Cons(2N, List::Cons(8N, List::Cons(1N, List::Nil)))))

pub fn pt_shift(p : Pt, d : BigInt) -> Pt {
  Pt::{ x: p.x + d, y: p.y + 1N, tag: p.tag + "!" }
}

pub fn shape_area(x : Shape) -> BigInt {
  match x {
    Shape::Circle(r) => (3N * r) * r
    Shape::Rect(w, h) => w * h
    Shape::Empty => 0N
  }
}

pub fn shape_grow(s : Shape, k : BigInt) -> Shape {
  match s {
    Shape::Circle(r) => Shape::Circle(r + k)
    Shape::Rect(w, h) => Shape::Rect(w + k, h * k)
    Shape::Empty => Shape::Empty
  }
}

pub fn evens(n : BigInt) -> List[BigInt] {
  list_filter(fn(x : BigInt) {
    let a = lean_nat_mod(x, 2N)
    a == 0N
  }, list_range(n))
}

pub fn firstBig(xs : List[BigInt]) -> Option[BigInt] {
  list_find_(fn(x : BigInt) { 10N < x }, xs)
}

pub fn divmod(a : BigInt, b : BigInt) -> (BigInt, BigInt) {
  (lean_nat_div(a, b), lean_nat_mod(a, b))
}

pub fn sq(xs : Array[BigInt]) -> Array[BigInt] {
  xs.map((fn(x : BigInt) { x * x }))
}

pub fn shout(s : String) -> String {
  (s + "!") + s
}

pub fn nextChar(c : Char) -> Char {
  lean_char_of_nat((BigInt::from_int(c.to_int()) + 1N))
}

pub fn pairs(xs : List[BigInt]) -> List[(BigInt, String)] {
  list_map(fn(x : BigInt) { (x, x.to_string()) }, xs)
}

pub fn safeDiv(a : BigInt, b : BigInt) -> Result[BigInt, String] {
  if b == 0N { Err("div by zero") } else { Ok(lean_nat_div(a, b)) }
}

pub fn isPrime(n : BigInt) -> Bool {
  (2N <= n) && list_all(list_range(lean_nat_sub(n, 2N)), fn(i : BigInt) {
    !({
      let a = lean_nat_mod(n, (i + 2N))
      a == 0N
    })
  })
}

pub fn isEven(x : BigInt) -> Bool {
  if x == 0N {
    true
  } else {
    let n = x - 1N
    isOdd(n)
  }
}

pub fn[A] instBEqTree_beq(inst : BEq[A], x : Tree[A], x_1 : Tree[A]) -> Bool {
  let alt = fn(_ : Tree[A]) { fn(_ : Tree[A]) { false } }
  match x {
    Tree::Leaf => match x_1 {
      Tree::Leaf => true
      _ => alt(Tree::Leaf)(x_1)
    }
    Tree::Node(a, a_1, a_2) => match x_1 {
      Tree::Node(a_3, a_4, a_5) => instBEqTree_beq(inst, a, a_3) && ((inst.beq)(a_1)(a_4) && instBEqTree_beq(inst, a_2, a_5))
      _ => alt(Tree::Node(a, a_1, a_2))(x_1)
    }
  }
}

pub fn[A] instBEqOfDecidableEq(inst : (A) -> (A) -> Bool) -> BEq[A] {
  BEq::{ beq: fn(a : A) { fn(b : A) { inst(a)(b) } } }
}

pub fn[A] list_beq(inst : BEq[A], x : List[A], x_1 : List[A]) -> Bool {
  let alt = fn(_ : List[A]) { fn(_ : List[A]) { false } }
  match x {
    List::Nil => match x_1 {
      List::Nil => true
      List::Cons(head, tail) => alt(List::Nil)(List::Cons(head, tail))
    }
    List::Cons(head, tail) => match x_1 {
      List::Nil => alt(List::Cons(head, tail))(List::Nil)
      List::Cons(head_1, tail_1) => (inst.beq)(head)(head_1) && list_beq(inst, tail, tail_1)
    }
  }
}

pub fn instBEqPt_beq(x : Pt, x_1 : Pt) -> Bool {
  let x_2 = x.x
  let y = x.y
  let tag = x.tag
  let x_3 = x_1.x
  let y_1 = x_1.y
  let tag_1 = x_1.tag
  (x_2 == x_3) && ((y == y_1) && (tag == tag_1))
}

pub fn instBEqShape_beq(x : Shape, x_1 : Shape) -> Bool {
  let alt = fn(_ : Shape) { fn(_ : Shape) { false } }
  match x {
    Shape::Circle(r) => match x_1 {
      Shape::Circle(r_1) => r == r_1
      _ => alt(Shape::Circle(r))(x_1)
    }
    Shape::Rect(w, h) => match x_1 {
      Shape::Rect(w_1, h_1) => (w == w_1) && (h == h_1)
      _ => alt(Shape::Rect(w, h))(x_1)
    }
    Shape::Empty => match x_1 {
      Shape::Empty => true
      _ => alt(Shape::Empty)(x_1)
    }
  }
}

pub fn[A] option_instBEq_beq(inst : BEq[A], x : Option[A], x_1 : Option[A]) -> Bool {
  let alt = fn(_ : Option[A]) { fn(_ : Option[A]) { false } }
  match x {
    None => match x_1 {
      None => true
      Some(val) => alt(None)(Some(val))
    }
    Some(val) => match x_1 {
      None => alt(Some(val))(None)
      Some(val_1) => (inst.beq)(val)(val_1)
    }
  }
}

pub fn[A] array_isEqvAux(xs : Array[A], ys : Array[A], p : (A) -> (A) -> Bool, x : BigInt) -> Bool {
  if x == 0N {
    true
  } else {
    let n = x - 1N
    p(xs[BigInt::to_int(n)])(ys[BigInt::to_int(n)]) && array_isEqvAux(xs, ys, p, n)
  }
}

pub fn[A, B] instBEqProd(inst : BEq[A], inst_1 : BEq[B]) -> BEq[(A, B)] {
  BEq::{ beq: fn(x : (A, B)) {
    fn(x_1 : (A, B)) {
      match x {
        (fst, snd) => match x_1 {
          (fst_1, snd_1) => (inst.beq)(fst)(fst_1) && (inst_1.beq)(snd)(snd_1)
        }
      }
    }
  } }
}

pub fn[A, B] instBEqExcept_tests_beq(inst : BEq[A], inst_1 : BEq[B], x : Result[B, A], x_1 : Result[B, A]) -> Bool {
  let alt = fn(_ : Result[B, A]) { fn(_ : Result[B, A]) { false } }
  match x {
    Err(a) => match x_1 {
      Err(a_1) => (inst.beq)(a)(a_1)
      Ok(_) => alt(Err(a))(x_1)
    }
    Ok(a) => match x_1 {
      Err(_) => alt(Ok(a))(x_1)
      Ok(a_1) => (inst_1.beq)(a)(a_1)
    }
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

pub fn[A] nat_cast(inst : NatCast[A]) -> (BigInt) -> A {
  inst.natCast
}

pub let instNatCastInt : NatCast[BigInt] = NatCast::{ natCast: fn(n : BigInt) { n } }

pub fn[A] list_append(x : List[A], x_1 : List[A]) -> List[A] {
  match x {
    List::Nil => x_1
    List::Cons(head, tail) => List::Cons(head, list_append(tail, x_1))
  }
}

pub fn[A, B] list_foldl(f : (A) -> (B) -> A, x : A, x_1 : List[B]) -> A {
  match x_1 {
    List::Nil => x
    List::Cons(head, tail) => list_foldl(f, f(x)(head), tail)
  }
}

pub fn[A] list_filter(p : (A) -> Bool, x : List[A]) -> List[A] {
  match x {
    List::Nil => List::Nil
    List::Cons(head, tail) => {
      let s = p(head)
      if s {
        List::Cons(head, list_filter(p, tail))
      } else {
        list_filter(p, tail)
      }
    }
  }
}

pub fn list_range(n : BigInt) -> List[BigInt] {
  list_range_loop(n, List::Nil)
}

pub fn[A] list_find_(p : (A) -> Bool, x : List[A]) -> Option[A] {
  match x {
    List::Nil => None
    List::Cons(head, tail) => {
      let s = p(head)
      if s { Some(head) } else { list_find_(p, tail) }
    }
  }
}

pub fn[A, B] list_map(f : (A) -> B, x : List[A]) -> List[B] {
  match x {
    List::Nil => List::Nil
    List::Cons(head, tail) => List::Cons(f(head), list_map(f, tail))
  }
}

pub fn[A] list_all(x : List[A], x_1 : (A) -> Bool) -> Bool {
  match x {
    List::Nil => true
    List::Cons(head, tail) => x_1(head) && list_all(tail, x_1)
  }
}

pub fn list_range_loop(x : BigInt, x_1 : List[BigInt]) -> List[BigInt] {
  if x == 0N {
    x_1
  } else {
    let n = x - 1N
    list_range_loop(n, List::Cons(n, x_1))
  }
}
