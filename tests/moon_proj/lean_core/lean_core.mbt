// Extracted from Lean by lean6x7mbt (package `lean_core`).

// Helpers

pub fn lean_nat_sub(a : BigInt, b : BigInt) -> BigInt {
  if a > b { a - b } else { 0 }
}

pub fn lean_nat_div(a : BigInt, b : BigInt) -> BigInt {
  if b == 0 { 0 } else { a / b }
}

pub fn[A] lean_array_of_list(l : List[A]) -> Array[A] {
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

pub fn[A] lean_array_push(a : Array[A], x : A) -> Array[A] {
  let r = a.copy()
  r.push(x)
  r
}

pub fn[A, B] lean_array_foldl(f : (B) -> (A) -> B, init : B, a : Array[A], start : BigInt, stop : BigInt) -> B {
  let mut acc = init
  let hi = if stop < BigInt::from_int(a.length()) { BigInt::to_int(stop) } else { a.length() }
  let mut i = BigInt::to_int(start)
  while i < hi {
    acc = f(acc)(a[i])
    i = i + 1
  }
  acc
}

pub(all) enum List[A] {
  Nil
  Cons(A, List[A])
}

pub(all) struct Std_Legacy_Range {
  start : BigInt
  stop : BigInt
  step : BigInt
}

pub(all) enum ForInStep[A] {
  Done(A)
  Yield(A)
}

pub(all) struct BEq[A] {
  beq : (A) -> (A) -> Bool
}

pub(all) struct MProd[A, B] {
  fst : A
  snd : B
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

pub fn[A, B] list_map(f : (A) -> B, x : List[A]) -> List[B] {
  match x {
    List::Nil => List::Nil
    List::Cons(head, tail) => List::Cons(f(head), list_map(f, tail))
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

pub fn[A, B] list_foldl(f : (A) -> (B) -> A, x : A, x_1 : List[B]) -> A {
  match x_1 {
    List::Nil => x
    List::Cons(head, tail) => list_foldl(f, f(x)(head), tail)
  }
}

pub let unit_unit : Unit = ()
