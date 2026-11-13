// Extracted from Lean by lean6x7mbt (package `proj_main`).

pub fn chain(a : BigInt, b : BigInt, c : BigInt) -> Result[BigInt, String] {
  match @proj_b.projB_safeDiv(a, b) {
    Err(a_1) => Err(a_1)
    Ok(a_1) => match @proj_b.projB_safeDiv(a_1, c) {
      Err(a_2) => Err(a_2)
      Ok(a_2) => Ok((a_1 + a_2))
    }
  }
}

pub fn mainLoop(n : BigInt) -> BigInt {
  let s = 0N
  let s_1 = {
    let range = @lean_core.Std_Legacy_Range::{ start: 0N, stop: n, step: 1N }
    std_Legacy_Range_forIn__loop_spec1(range, fn(a : BigInt) {
      fn(r : BigInt) {
        let s_1 = r
        let s_2 = s_1 + @proj_b.projB_countDown(a)
        @lean_core.ForInStep::Yield(s_2)
      }
    }, s, range.start)
  }
  s_1 + @proj_a.projA_sumTo(n)
}

pub let areaOfAll : BigInt = @proj_b.projB_totalArea(@proj_a.projA_instHasAreaShape, @proj_b.projB_shapes) + @proj_b.projB_totalArea(@proj_a.projA_instHasAreaShape, @lean_core.List::Cons(@proj_a.ProjA_Shape::Circle(1N), @lean_core.List::Nil))

pub fn[A] std_Legacy_Range_forIn__loop_spec1(range : @lean_core.Std_Legacy_Range, f : (BigInt) -> (A) -> @lean_core.ForInStep[A], b : A, i : BigInt) -> A {
  if i < range.stop {
    match f(i)(b) {
      @lean_core.ForInStep::Done(a) => a
      @lean_core.ForInStep::Yield(a) => std_Legacy_Range_forIn__loop_spec1(range, f, a, i + range.step)
    }
  } else {
    b
  }
}
