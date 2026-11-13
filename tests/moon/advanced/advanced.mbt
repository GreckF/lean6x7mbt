// Extracted from Lean by lean6x7mbt.

// Helpers

fn lean_nat_div(a : BigInt, b : BigInt) -> BigInt {
  if b == 0 { 0 } else { a / b }
}

fn lean_nat_mod(a : BigInt, b : BigInt) -> BigInt {
  if b == 0 { a } else { a % b }
}

pub(all) enum List[A] {
  Nil
  Cons(A, List[A])
}

pub(all) enum Color {
  Red
  Green
  Blue
}

pub(all) struct Config {
  name : String
  size : BigInt
  flag : Bool
}

pub(all) enum Expr {
  Num(BigInt)
  Add(Expr, Expr)
  Mul(Expr, Expr)
  Neg(Expr)
}

pub(all) struct Rect {
  w : BigInt
  h : BigInt
}

pub(all) struct Square {
  s : BigInt
}

pub(all) struct Shape[A] {
  area : (A) -> BigInt
  name : (A) -> String
}

pub fn addOpt(a : Option[BigInt], b : Option[BigInt]) -> Option[BigInt] {
  match a {
    None => None
    Some(val) => match b {
      None => None
      Some(val_1) => Some((val + val_1))
    }
  }
}

pub fn divAll(xs : List[BigInt], d : BigInt) -> Result[List[BigInt], String] {
  match xs {
    List::Nil => Ok(List::Nil)
    List::Cons(head, tail) => {
      let do_jp = fn(_ : Unit) {
        match divAll(tail, d) {
          Err(a) => Err(a)
          Ok(a) => Ok(List::Cons(lean_nat_div(head, d), a))
        }
      }
      if d == 0N {
        match Err("zero") {
          Err(a) => Err(a)
          Ok(a) => do_jp(a)
        }
      } else {
        match Ok(()) {
          Err(a) => Err(a)
          Ok(a) => do_jp(a)
        }
      }
    }
  }
}

pub fn color_next(x : Color) -> Color {
  match x {
    Color::Red => Color::Green
    Color::Green => Color::Blue
    Color::Blue => Color::Red
  }
}

pub fn sameColor(a : Color, b : Color) -> Bool {
  instBEqColor_beq(a, b)
}

pub let defColor : Color = instInhabitedColor_default

pub fn config_bump(c : Config) -> Config {
  Config::{ name: c.name, size: c.size + 1N, flag: c.flag }
}

pub fn expr_eval(x : Expr) -> BigInt {
  match x {
    Expr::Num(a) => a
    Expr::Add(a, a_1) => expr_eval(a) + expr_eval(a_1)
    Expr::Mul(a, a_1) => expr_eval(a) * expr_eval(a_1)
    Expr::Neg(a) => -expr_eval(a)
  }
}

pub fn expr_simp(x : Expr) -> Expr {
  let alt = fn(e : Expr) { expr_simp(e) }
  let alt_1 = fn(e : Expr) { expr_simp(e) }
  let alt_2 = fn(a : Expr) { fn(b : Expr) { Expr::Add(expr_simp(a), expr_simp(b)) } }
  let alt_3 = fn(a : Expr) { fn(b : Expr) { Expr::Mul(expr_simp(a), expr_simp(b)) } }
  match x {
    Expr::Add(a, a_1) => match a {
      Expr::Num(a_2) => if a_2 == 0N {
        expr_simp(a_1)
      } else {
        match a_1 {
          Expr::Num(a_3) => if a_3 == 0N {
            alt(Expr::Num(a_2))
          } else {
            alt_2(Expr::Num(a_2))(Expr::Num(a_3))
          }
          _ => alt_2(Expr::Num(a_2))(a_1)
        }
      }
      _ => match a_1 {
        Expr::Num(a_2) => if a_2 == 0N { alt(a) } else { alt_2(a)(Expr::Num(a_2)) }
        _ => alt_2(a)(a_1)
      }
    }
    Expr::Mul(a, a_1) => match a {
      Expr::Num(a_2) => if a_2 == 1N {
        expr_simp(a_1)
      } else {
        match a_1 {
          Expr::Num(a_3) => if a_3 == 1N {
            alt_1(Expr::Num(a_2))
          } else {
            alt_3(Expr::Num(a_2))(Expr::Num(a_3))
          }
          _ => alt_3(Expr::Num(a_2))(a_1)
        }
      }
      _ => match a_1 {
        Expr::Num(a_2) => if a_2 == 1N { alt_1(a) } else { alt_3(a)(Expr::Num(a_2)) }
        _ => alt_3(a)(a_1)
      }
    }
    Expr::Neg(a) => Expr::Neg(expr_simp(a))
    _ => x
  }
}

pub fn pairs(xs : List[BigInt]) -> List[(BigInt, BigInt)] {
  let alt = fn(_ : List[BigInt]) { List::Nil }
  match xs {
    List::Cons(head, tail) => match tail {
      List::Cons(head_1, tail_1) => List::Cons((head, head_1), pairs(tail_1))
      _ => alt(List::Cons(head, tail))
    }
    _ => alt(xs)
  }
}

pub fn bigMul(n : BigInt) -> BigInt {
  n * big
}

pub fn rectArea(r : Rect) -> BigInt {
  r.w * r.h
}

pub fn squares(xs : List[Square]) -> BigInt {
  totalArea(instShapeSquare, xs)
}

pub fn firstOr(xs : List[BigInt], d : BigInt) -> BigInt {
  match list_head_(xs) {
    None => d
    Some(val) => val
  }
}

pub fn lastOf(xs : List[BigInt]) -> Option[BigInt] {
  list_getLast_(xs)
}

pub fn lengthOf(xs : List[BigInt]) -> BigInt {
  list_length(xs)
}

pub fn rev(xs : List[BigInt]) -> List[BigInt] {
  list_reverse(xs)
}

pub fn filterEven(xs : List[BigInt]) -> List[BigInt] {
  list_filter(fn(x : BigInt) {
    let a = lean_nat_mod(x, 2N)
    a == 0N
  }, xs)
}

pub fn instBEqColor_beq(x : Color, y : Color) -> Bool {
  let a = color_ctorIdx(x)
  let b = color_ctorIdx(y)
  a == b
}

pub let instInhabitedColor_default : Color = Color::Red

pub let big : BigInt = 123456789012345678901234567890N

pub fn[A] totalArea(inst : Shape[A], xs : List[A]) -> BigInt {
  list_foldl(fn(acc : BigInt) { fn(x : A) { acc + (inst.area)(x) } }, 0N, xs)
}

pub let instShapeSquare : Shape[Square] = Shape::{ area: fn(s : Square) { s.s * s.s }, name: fn(_ : Square) { "square" } }

pub fn[A] list_head_(x : List[A]) -> Option[A] {
  match x {
    List::Nil => None
    List::Cons(head, _) => Some(head)
  }
}

pub fn[A] list_getLast_(x : List[A]) -> Option[A] {
  match x {
    List::Nil => None
    List::Cons(head, tail) => Some(list_getLast(List::Cons(head, tail)))
  }
}

pub fn[A] list_length(x : List[A]) -> BigInt {
  match x {
    List::Nil => 0N
    List::Cons(_, tail) => list_length(tail) + 1N
  }
}

pub fn[A] list_reverse(as_ : List[A]) -> List[A] {
  list_reverseAux(as_, List::Nil)
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

pub fn color_ctorIdx(x : Color) -> BigInt {
  match x {
    Color::Red => 0N
    Color::Green => 1N
    Color::Blue => 2N
  }
}

pub fn[A, B] list_foldl(f : (A) -> (B) -> A, x : A, x_1 : List[B]) -> A {
  match x_1 {
    List::Nil => x
    List::Cons(head, tail) => list_foldl(f, f(x)(head), tail)
  }
}

pub fn[A] list_getLast(x : List[A]) -> A {
  match x {
    List::Nil => abort("unreachable (absurd)")
    List::Cons(head, tail) => match tail {
      List::Nil => head
      List::Cons(head_1, tail_1) => list_getLast(List::Cons(head_1, tail_1))
    }
  }
}

pub fn[A] list_reverseAux(x : List[A], x_1 : List[A]) -> List[A] {
  match x {
    List::Nil => x_1
    List::Cons(head, tail) => list_reverseAux(tail, List::Cons(head, x_1))
  }
}
