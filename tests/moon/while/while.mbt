// Extracted from Lean by lean6x7mbt.

// Helpers

fn lean_nat_mod(a : BigInt, b : BigInt) -> BigInt {
  if b == 0 { a } else { a % b }
}

pub(all) struct MProd[A, B] {
  fst : A
  snd : B
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

pub(all) enum List[A] {
  Nil
  Cons(A, List[A])
}

pub fn whileLoop(n : BigInt) -> BigInt {
  let i = 0N
  let s = 0N
  let s_1 = lean6x7mbt_loopForIn_spec1(fn(_ : Unit) {
    fn(r : MProd[BigInt, BigInt]) {
      let i_1 = r.fst
      let s_1 = r.snd
      if i_1 < n {
        let s_2 = s_1 + i_1
        let i_2 = i_1 + 1N
        ForInStep::Yield(MProd::{ fst: i_2, snd: s_2 })
      } else {
        ForInStep::Done(MProd::{ fst: i_1, snd: s_1 })
      }
    }
  }, MProd::{ fst: i, snd: s })
  let snd = s_1.snd
  snd
}

pub fn whileBreak(n : BigInt) -> BigInt {
  let i = 0N
  let s = 0N
  let s_1 = lean6x7mbt_loopForIn_spec1(fn(_ : Unit) {
    fn(r : MProd[BigInt, BigInt]) {
      let i_1 = r.fst
      let s_1 = r.snd
      if i_1 < n {
        let i_2 = i_1 + 1N
        let do_jp = fn(s_2 : BigInt) {
          fn(_ : Unit) {
            let s_3 = s_2 + i_2
            if 20N < s_3 {
              ForInStep::Done(MProd::{ fst: i_2, snd: s_3 })
            } else {
              ForInStep::Yield(MProd::{ fst: i_2, snd: s_3 })
            }
          }
        }
        if ({
          let a = lean_nat_mod(i_2, 2N)
          a == 0N
        }) {
          ForInStep::Yield(MProd::{ fst: i_2, snd: s_1 })
        } else {
          do_jp(s_1)(())
        }
      } else {
        ForInStep::Done(MProd::{ fst: i_1, snd: s_1 })
      }
    }
  }, MProd::{ fst: i, snd: s })
  let snd = s_1.snd
  snd
}

pub fn whileReturn(n : BigInt) -> BigInt {
  let i = 0N
  let r = lean6x7mbt_loopForIn_spec1(fn(_ : Unit) {
    fn(r : MProd[Option[BigInt], BigInt]) {
      let r_1 = r.snd
      let i_1 = r_1
      if i_1 < 1000N {
        let do_jp = fn(i_2 : BigInt) {
          fn(_ : Unit) {
            let i_3 = i_2 + 1N
            ForInStep::Yield(MProd::{ fst: None, snd: i_3 })
          }
        }
        if n < (i_1 * i_1) {
          ForInStep::Done(MProd::{ fst: Some(i_1), snd: i_1 })
        } else {
          do_jp(i_1)(())
        }
      } else {
        ForInStep::Done(MProd::{ fst: None, snd: i_1 })
      }
    }
  }, MProd::{ fst: None, snd: i })
  let i_1 = r.snd
  let do_jp = fn(_ : Unit) { 9999N }
  match r.fst {
    None => do_jp(())
    Some(val) => val
  }
}

pub fn whileFor(n : BigInt) -> BigInt {
  let i = 0N
  let s = 0N
  let s_1 = lean6x7mbt_loopForIn_spec1(fn(_ : Unit) {
    fn(r : MProd[BigInt, BigInt]) {
      let i_1 = r.fst
      let s_1 = r.snd
      if i_1 < n {
        let s_2 = {
          let range = Std_Legacy_Range::{ start: 0N, stop: i_1, step: 1N }
          std_Legacy_Range_forIn__loop_spec2(range, fn(a : BigInt) {
            fn(r_1 : BigInt) {
              let s_2 = r_1
              let s_3 = s_2 + a
              ForInStep::Yield(s_3)
            }
          }, s_1, range.start)
        }
        let i_2 = i_1 + 1N
        ForInStep::Yield(MProd::{ fst: i_2, snd: s_2 })
      } else {
        ForInStep::Done(MProd::{ fst: i_1, snd: s_1 })
      }
    }
  }, MProd::{ fst: i, snd: s })
  let snd = s_1.snd
  snd
}

pub fn whileWhile(n : BigInt) -> BigInt {
  let i = 0N
  let c = 0N
  let s = lean6x7mbt_loopForIn_spec1(fn(_ : Unit) {
    fn(r : MProd[BigInt, BigInt]) {
      let c_1 = r.fst
      let i_1 = r.snd
      if i_1 < n {
        let j = 0N
        let s = lean6x7mbt_loopForIn_spec1(fn(_ : Unit) {
          fn(r_1 : MProd[BigInt, BigInt]) {
            let c_2 = r_1.fst
            let j_1 = r_1.snd
            if j_1 < i_1 {
              let c_3 = c_2 + 1N
              let j_2 = j_1 + 1N
              ForInStep::Yield(MProd::{ fst: c_3, snd: j_2 })
            } else {
              ForInStep::Done(MProd::{ fst: c_2, snd: j_1 })
            }
          }
        }, MProd::{ fst: c_1, snd: j })
        let fst = s.fst
        let i_2 = i_1 + 1N
        ForInStep::Yield(MProd::{ fst: fst, snd: i_2 })
      } else {
        ForInStep::Done(MProd::{ fst: c_1, snd: i_1 })
      }
    }
  }, MProd::{ fst: c, snd: i })
  let fst = s.fst
  fst
}

pub fn whileExcept(n : BigInt) -> Result[BigInt, String] {
  let i = 0N
  let s = 0N
  match lean6x7mbt_loopForIn_spec3(fn(_ : Unit) {
    fn(r : MProd[BigInt, BigInt]) {
      let i_1 = r.fst
      let s_1 = r.snd
      if i_1 < 10N {
        let do_jp = fn(i_2 : BigInt) {
          fn(s_2 : BigInt) {
            fn(_ : Unit) {
              let s_3 = s_2 + i_2
              let i_3 = i_2 + 1N
              match Ok(()) {
                Err(a) => Err(a)
                Ok(_) => Ok(ForInStep::Yield(MProd::{ fst: i_3, snd: s_3 }))
              }
            }
          }
        }
        if i_1 == n {
          match Err(("hit " + i_1.to_string())) {
            Err(a) => Err(a)
            Ok(a) => do_jp(i_1)(s_1)(a)
          }
        } else {
          match Ok(()) {
            Err(a) => Err(a)
            Ok(a) => do_jp(i_1)(s_1)(a)
          }
        }
      } else {
        Ok(ForInStep::Done(MProd::{ fst: i_1, snd: s_1 }))
      }
    }
  }, MProd::{ fst: i, snd: s }) {
    Err(a) => Err(a)
    Ok(a) => {
      let snd = a.snd
      Ok(snd)
    }
  }
}

pub fn runWhileState(n : BigInt) -> BigInt {
  whileState(n)(100N).1
}

pub fn whileNever(n : BigInt) -> BigInt {
  let s = 7N
  let s_1 = lean6x7mbt_loopForIn_spec1(fn(_ : Unit) {
    fn(r : BigInt) {
      let s_1 = r
      if n < 0N {
        let s_2 = s_1 + 1N
        ForInStep::Yield(s_2)
      } else {
        ForInStep::Done(s_1)
      }
    }
  }, s)
  s_1
}

pub fn deepExcept(n : BigInt) -> Result[BigInt, String] {
  let i = 0N
  match lean6x7mbt_loopForIn_spec3(fn(_ : Unit) {
    fn(r : BigInt) {
      let i_1 = r
      if i_1 < n {
        let do_jp = fn(i_2 : BigInt) {
          fn(_ : Unit) {
            let i_3 = i_2 + 1N
            match Ok(()) {
              Err(a) => Err(a)
              Ok(_) => Ok(ForInStep::Yield(i_3))
            }
          }
        }
        if ({
          let b = n + 1N
          i_1 == b
        }) {
          match Err("unreachable") {
            Err(a) => Err(a)
            Ok(a) => do_jp(i_1)(a)
          }
        } else {
          match Ok(()) {
            Err(a) => Err(a)
            Ok(a) => do_jp(i_1)(a)
          }
        }
      } else {
        Ok(ForInStep::Done(i_1))
      }
    }
  }, i) {
    Err(a) => Err(a)
    Ok(a) => {
      let i_1 = a
      Ok(i_1)
    }
  }
}

pub fn deepFor(n : BigInt) -> Result[BigInt, String] {
  let s = 0N
  match ({
    let range = Std_Legacy_Range::{ start: 0N, stop: n, step: 1N }
    std_Legacy_Range_forIn__loop_spec4(range, fn(a : BigInt) {
      fn(r : BigInt) {
        let s_1 = r
        let do_jp = fn(s_2 : BigInt) {
          fn(_ : Unit) {
            let s_3 = s_2 + a
            match Ok(()) {
              Err(a_1) => Err(a_1)
              Ok(_) => Ok(ForInStep::Yield(s_3))
            }
          }
        }
        if ({
          let b = n + 1N
          a == b
        }) {
          match Err("unreachable") {
            Err(a_1) => Err(a_1)
            Ok(a_1) => do_jp(s_1)(a_1)
          }
        } else {
          match Ok(()) {
            Err(a_1) => Err(a_1)
            Ok(a_1) => do_jp(s_1)(a_1)
          }
        }
      }
    }, s, range.start)
  }) {
    Err(a) => Err(a)
    Ok(a) => {
      let s_1 = a
      Ok(s_1)
    }
  }
}

pub fn deepList(n : BigInt) -> Result[BigInt, String] {
  let s = 0N
  match ({
    let as_ = list_range(n)
    list_forIn__loop_spec5(as_, fn(a : BigInt) {
      fn(r : BigInt) {
        let s_1 = r
        let do_jp = fn(s_2 : BigInt) {
          fn(_ : Unit) {
            let s_3 = s_2 + a
            match Ok(()) {
              Err(a_1) => Err(a_1)
              Ok(_) => Ok(ForInStep::Yield(s_3))
            }
          }
        }
        if a == n {
          match Err("unreachable") {
            Err(a_1) => Err(a_1)
            Ok(a_1) => do_jp(s_1)(a_1)
          }
        } else {
          match Ok(()) {
            Err(a_1) => Err(a_1)
            Ok(a_1) => do_jp(s_1)(a_1)
          }
        }
      }
    }, as_, s)
  }) {
    Err(a) => Err(a)
    Ok(a) => {
      let s_1 = a
      Ok(s_1)
    }
  }
}

pub fn deepState(n : BigInt) -> BigInt {
  ({
    let i = 0N
    fn(s : BigInt) {
      match lean6x7mbt_loopForIn_spec6(fn(_ : Unit) {
        fn(r : BigInt) {
          let i_1 = r
          if i_1 < n {
            fn(s_1 : BigInt) {
              match ((), (s_1 + 2N)) {
                (_, snd) => ({
                  let i_2 = i_1 + 1N
                  fn(s_2 : BigInt) {
                    match ((), s_2) {
                      (_, snd_1) => (ForInStep::Yield(i_2), snd_1)
                    }
                  }
                })(snd)
              }
            }
          } else {
            fn(s_1 : BigInt) { (ForInStep::Done(i_1), s_1) }
          }
        }
      }, i, s) {
        (fst, snd) => ({
          let i_1 = fst
          fn(s_1 : BigInt) { ((), s_1) }
        })(snd)
      }
    }
  })(1N).1
}

pub fn deepStateExcept(n : BigInt) -> Result[(BigInt, BigInt), String] {
  ({
    let i = 0N
    fn(s : BigInt) {
      match lean6x7mbt_loopForIn_spec7(fn(_ : Unit) {
        fn(r : BigInt) {
          let i_1 = r
          if i_1 < n {
            fn(s_1 : BigInt) {
              match Ok((s_1, s_1)) {
                Err(a) => Err(a)
                Ok(a) => match a {
                  (fst, snd) => ({
                    let do_jp = fn(i_2 : BigInt) {
                      fn(_ : Unit) {
                        fn(_ : BigInt) {
                          match Ok(((), (fst + 3N))) {
                            Err(a_1) => Err(a_1)
                            Ok(a_1) => match a_1 {
                              (_, snd_1) => ({
                                let i_3 = i_2 + 1N
                                fn(s_3 : BigInt) {
                                  match Ok(((), s_3)) {
                                    Err(a_2) => Err(a_2)
                                    Ok(a_2) => match a_2 {
                                      (_, snd_2) => Ok((ForInStep::Yield(i_3), snd_2))
                                    }
                                  }
                                }
                              })(snd_1)
                            }
                          }
                        }
                      }
                    }
                    if (3N * n) < fst {
                      fn(s_2 : BigInt) {
                        match (match Err("unreachable") {
                          Err(a_1) => Err(a_1)
                          Ok(a_1) => Ok((a_1, s_2))
                        }) {
                          Err(a_1) => Err(a_1)
                          Ok(a_1) => match a_1 {
                            (fst_1, snd_1) => do_jp(i_1)(fst_1)(snd_1)
                          }
                        }
                      }
                    } else {
                      fn(s_2 : BigInt) {
                        match Ok(((), s_2)) {
                          Err(a_1) => Err(a_1)
                          Ok(a_1) => match a_1 {
                            (fst_1, snd_1) => do_jp(i_1)(fst_1)(snd_1)
                          }
                        }
                      }
                    }
                  })(snd)
                }
              }
            }
          } else {
            fn(s_1 : BigInt) { Ok((ForInStep::Done(i_1), s_1)) }
          }
        }
      }, i, s) {
        Err(a) => Err(a)
        Ok(a) => match a {
          (fst, snd) => ({
            let i_1 = fst
            fn(s_1 : BigInt) { Ok((i_1, s_1)) }
          })(snd)
        }
      }
    }
  })(0N)
}

pub fn[A] lean6x7mbt_loopForIn_spec1(f : (Unit) -> (A) -> ForInStep[A], b : A) -> A {
  match f(unit_unit)(b) {
    ForInStep::Done(a) => a
    ForInStep::Yield(a) => lean6x7mbt_loopForIn_spec1(f, a)
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

pub fn[A] lean6x7mbt_loopForIn_spec3(f : (Unit) -> (A) -> Result[ForInStep[A], String], b : A) -> Result[A, String] {
  match f(unit_unit)(b) {
    Err(a) => Err(a)
    Ok(a) => match a {
      ForInStep::Done(a_1) => Ok(a_1)
      ForInStep::Yield(a_1) => lean6x7mbt_loopForIn_spec3(f, a_1)
    }
  }
}

pub fn whileState(n : BigInt) -> (BigInt) -> (Unit, BigInt) {
  let i = 0N
  fn(s : BigInt) {
    match lean6x7mbt_loopForIn_spec6(fn(_ : Unit) {
      fn(r : BigInt) {
        let i_1 = r
        if i_1 < n {
          fn(s_1 : BigInt) {
            match ((), (s_1 + i_1)) {
              (_, snd) => ({
                let i_2 = i_1 + 1N
                fn(s_2 : BigInt) {
                  match ((), s_2) {
                    (_, snd_1) => (ForInStep::Yield(i_2), snd_1)
                  }
                }
              })(snd)
            }
          }
        } else {
          fn(s_1 : BigInt) { (ForInStep::Done(i_1), s_1) }
        }
      }
    }, i, s) {
      (fst, snd) => ({
        let i_1 = fst
        fn(s_1 : BigInt) { ((), s_1) }
      })(snd)
    }
  }
}

pub fn[A] std_Legacy_Range_forIn__loop_spec4(range : Std_Legacy_Range, f : (BigInt) -> (A) -> Result[ForInStep[A], String], b : A, i : BigInt) -> Result[A, String] {
  if i < range.stop {
    match f(i)(b) {
      Err(a) => Err(a)
      Ok(a) => match a {
        ForInStep::Done(a_1) => Ok(a_1)
        ForInStep::Yield(a_1) => std_Legacy_Range_forIn__loop_spec4(range, f, a_1, i + range.step)
      }
    }
  } else {
    Ok(b)
  }
}

pub fn list_range(n : BigInt) -> List[BigInt] {
  list_range_loop(n, List::Nil)
}

pub fn[A, B] list_forIn__loop_spec5(as_ : List[A], f : (A) -> (B) -> Result[ForInStep[B], String], x : List[A], x_1 : B) -> Result[B, String] {
  match x {
    List::Nil => Ok(x_1)
    List::Cons(head, tail) => match f(head)(x_1) {
      Err(a) => Err(a)
      Ok(a) => match a {
        ForInStep::Done(a_1) => Ok(a_1)
        ForInStep::Yield(a_1) => list_forIn__loop_spec5(as_, f, tail, a_1)
      }
    }
  }
}

pub fn[A] lean6x7mbt_loopForIn_spec6(f : (Unit) -> (A) -> (BigInt) -> (ForInStep[A], BigInt), b : A, a : BigInt) -> (A, BigInt) {
  match f(unit_unit)(b)(a) {
    (fst, snd) => match fst {
      ForInStep::Done(a_1) => (a_1, snd)
      ForInStep::Yield(a_1) => lean6x7mbt_loopForIn_spec6(f, a_1, snd)
    }
  }
}

pub fn[A] lean6x7mbt_loopForIn_spec7(f : (Unit) -> (A) -> (BigInt) -> Result[(ForInStep[A], BigInt), String], b : A, a : BigInt) -> Result[(A, BigInt), String] {
  match f(unit_unit)(b)(a) {
    Err(a_1) => Err(a_1)
    Ok(a_1) => match a_1 {
      (fst, snd) => match fst {
        ForInStep::Done(a_2) => Ok((a_2, snd))
        ForInStep::Yield(a_2) => lean6x7mbt_loopForIn_spec7(f, a_2, snd)
      }
    }
  }
}

pub let unit_unit : Unit = ()

pub fn list_range_loop(x : BigInt, x_1 : List[BigInt]) -> List[BigInt] {
  if x == 0N {
    x_1
  } else {
    let n = x - 1N
    list_range_loop(n, List::Cons(n, x_1))
  }
}
