// Extracted from Lean by lean6x7mbt.

// Helpers

fn lean_nat_sub(a : BigInt, b : BigInt) -> BigInt {
  if a > b { a - b } else { 0 }
}

fn lean_nat_mod(a : BigInt, b : BigInt) -> BigInt {
  if b == 0 { a } else { a % b }
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

pub(all) enum List[A] {
  Nil
  Cons(A, List[A])
}

pub fn loopSum(n : BigInt) -> BigInt {
  let s = 0N
  let s_1 = {
    let range = Std_Legacy_Range::{ start: 0N, stop: n, step: 1N }
    std_Legacy_Range_forIn__loop_spec1(range, fn(a : BigInt) {
      fn(r : BigInt) {
        let s_1 = r
        let s_2 = s_1 + a
        ForInStep::Yield(s_2)
      }
    }, s, range.start)
  }
  s_1
}

pub fn sumListLoop(xs : List[BigInt]) -> BigInt {
  let s = 0N
  let s_1 = list_forIn__loop_spec2(xs, fn(a : BigInt) {
    fn(r : BigInt) {
      let s_1 = r
      let s_2 = s_1 + a
      ForInStep::Yield(s_2)
    }
  }, xs, s)
  s_1
}

pub fn mapOpt(xs : List[BigInt]) -> Option[List[BigInt]] {
  list_mapM_loop_spec3(fn(x : BigInt) { if 0N < x { Some(lean_nat_sub(x, 1N)) } else { None } }, xs, List::Nil)
}

pub fn runCounter(n : BigInt) -> BigInt {
  counter(n)(0N).1
}

pub fn checkAll(xs : List[BigInt]) -> Result[BigInt, String] {
  let total = 0N
  match list_forIn__loop_spec4(xs, fn(a : BigInt) {
    fn(r : BigInt) {
      let total_1 = r
      let do_jp = fn(total_2 : BigInt) {
        fn(_ : Unit) {
          let total_3 = total_2 + a
          match Ok(()) {
            Err(a_1) => Err(a_1)
            Ok(_) => Ok(ForInStep::Yield(total_3))
          }
        }
      }
      if a == 0N {
        match Err("zero found") {
          Err(a_1) => Err(a_1)
          Ok(a_1) => do_jp(total_1)(a_1)
        }
      } else {
        match Ok(()) {
          Err(a_1) => Err(a_1)
          Ok(a_1) => do_jp(total_1)(a_1)
        }
      }
    }
  }, xs, total) {
    Err(a) => Err(a)
    Ok(a) => {
      let total_1 = a
      Ok(total_1)
    }
  }
}

pub fn evensBelow(n : BigInt) -> BigInt {
  let c = 0N
  let c_1 = {
    let range = Std_Legacy_Range::{ start: 0N, stop: n, step: 1N }
    std_Legacy_Range_forIn__loop_spec1(range, fn(a : BigInt) {
      fn(r : BigInt) {
        let c_1 = r
        if ({
          let a_1 = lean_nat_mod(a, 2N)
          a_1 == 0N
        }) {
          let c_2 = c_1 + 1N
          ForInStep::Yield(c_2)
        } else {
          ForInStep::Yield(c_1)
        }
      }
    }, c, range.start)
  }
  c_1
}

pub fn[A] std_Legacy_Range_forIn__loop_spec1(range : Std_Legacy_Range, f : (BigInt) -> (A) -> ForInStep[A], b : A, i : BigInt) -> A {
  if i < range.stop {
    match f(i)(b) {
      ForInStep::Done(a) => a
      ForInStep::Yield(a) => std_Legacy_Range_forIn__loop_spec1(range, f, a, i + range.step)
    }
  } else {
    b
  }
}

pub fn[A, B] list_forIn__loop_spec2(as_ : List[A], f : (A) -> (B) -> ForInStep[B], x : List[A], x_1 : B) -> B {
  match x {
    List::Nil => x_1
    List::Cons(head, tail) => match f(head)(x_1) {
      ForInStep::Done(a) => a
      ForInStep::Yield(a) => list_forIn__loop_spec2(as_, f, tail, a)
    }
  }
}

pub fn[A, B] list_mapM_loop_spec3(f : (A) -> Option[B], x : List[A], x_1 : List[B]) -> Option[List[B]] {
  match x {
    List::Nil => Some(list_reverse(x_1))
    List::Cons(head, tail) => match f(head) {
      None => None
      Some(val) => list_mapM_loop_spec3(f, tail, List::Cons(val, x_1))
    }
  }
}

pub fn counter(n : BigInt) -> (BigInt) -> (Unit, BigInt) {
  fn(s : BigInt) {
    match ({
      let range = Std_Legacy_Range::{ start: 0N, stop: n, step: 1N }
      (fn(a : BigInt) {
        std_Legacy_Range_forIn__loop_spec5(range, fn(_ : BigInt) {
          fn(_ : Unit) {
            fn(s_1 : BigInt) {
              match ((), (s_1 + 1N)) {
                (_, snd) => (ForInStep::Yield(()), snd)
              }
            }
          }
        }, (), range.start, a)
      })(s)
    }) {
      (_, snd) => ((), snd)
    }
  }
}

pub fn[A, B] list_forIn__loop_spec4(as_ : List[A], f : (A) -> (B) -> Result[ForInStep[B], String], x : List[A], x_1 : B) -> Result[B, String] {
  match x {
    List::Nil => Ok(x_1)
    List::Cons(head, tail) => match f(head)(x_1) {
      Err(a) => Err(a)
      Ok(a) => match a {
        ForInStep::Done(a_1) => Ok(a_1)
        ForInStep::Yield(a_1) => list_forIn__loop_spec4(as_, f, tail, a_1)
      }
    }
  }
}

pub fn[A] list_reverse(as_ : List[A]) -> List[A] {
  list_reverseAux(as_, List::Nil)
}

pub fn[A] std_Legacy_Range_forIn__loop_spec5(range : Std_Legacy_Range, f : (BigInt) -> (A) -> (BigInt) -> (ForInStep[A], BigInt), b : A, i : BigInt, a : BigInt) -> (A, BigInt) {
  (if i < range.stop {
    fn(s : BigInt) {
      match f(i)(b)(s) {
        (fst, snd) => match fst {
          ForInStep::Done(a_1) => (a_1, snd)
          ForInStep::Yield(a_1) => (fn(a_2 : BigInt) { std_Legacy_Range_forIn__loop_spec5(range, f, a_1, i + range.step, a_2) })(snd)
        }
      }
    }
  } else {
    fn(s : BigInt) { (b, s) }
  })(a)
}

pub fn[A] list_reverseAux(x : List[A], x_1 : List[A]) -> List[A] {
  match x {
    List::Nil => x_1
    List::Cons(head, tail) => list_reverseAux(tail, List::Cons(head, x_1))
  }
}
