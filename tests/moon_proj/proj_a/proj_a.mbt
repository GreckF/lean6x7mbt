// Extracted from Lean by lean6x7mbt (package `proj_a`).

pub(all) enum ProjA_Shape {
  Circle(BigInt)
  Rect(BigInt, BigInt)
  Unit
}

pub(all) struct ProjA_Pt[A] {
  x : A
  y : BigInt
}

pub(all) struct ProjA_HasArea[A] {
  area : (A) -> BigInt
}

pub fn projA_instBEqShape_beq(x : ProjA_Shape, x_1 : ProjA_Shape) -> Bool {
  let alt = fn(_ : ProjA_Shape) { fn(_ : ProjA_Shape) { false } }
  match x {
    ProjA_Shape::Circle(r) => match x_1 {
      ProjA_Shape::Circle(r_1) => r == r_1
      _ => alt(ProjA_Shape::Circle(r))(x_1)
    }
    ProjA_Shape::Rect(w, h) => match x_1 {
      ProjA_Shape::Rect(w_1, h_1) => (w == w_1) && (h == h_1)
      _ => alt(ProjA_Shape::Rect(w, h))(x_1)
    }
    ProjA_Shape::Unit => match x_1 {
      ProjA_Shape::Unit => true
      _ => alt(ProjA_Shape::Unit)(x_1)
    }
  }
}

pub fn[A] projA_instBEqPt_beq(inst : @lean_core.BEq[A], x : ProjA_Pt[A], x_1 : ProjA_Pt[A]) -> Bool {
  let x_2 = x.x
  let y = x.y
  let x_3 = x_1.x
  let y_1 = x_1.y
  (inst.beq)(x_2)(x_3) && (y == y_1)
}

pub fn[A] projA_mkPt(a : A, n : BigInt) -> ProjA_Pt[A] {
  ProjA_Pt::{ x: a, y: n }
}

pub fn projA_arrSum(a : Array[BigInt]) -> BigInt {
  @lean_core.lean_array_foldl((fn(x1 : BigInt) { fn(x2 : BigInt) { x1 + x2 } }), 0N, a, 0N, BigInt::from_int(a.length()))
}

pub fn projA_minus3(a : BigInt) -> BigInt {
  @lean_core.lean_nat_sub(a, 3N)
}

pub let projA_instHasAreaShape : ProjA_HasArea[ProjA_Shape] = ProjA_HasArea::{ area: fn(a : ProjA_Shape) { projA_Shape_area(a) } }

pub fn projA_sumTo(n : BigInt) -> BigInt {
  let s = 0N
  let s_1 = {
    let range = @lean_core.Std_Legacy_Range::{ start: 0N, stop: n, step: 1N }
    std_Legacy_Range_forIn__loop_spec3(range, fn(a : BigInt) {
      fn(r : BigInt) {
        let s_1 = r
        let s_2 = s_1 + a
        @lean_core.ForInStep::Yield(s_2)
      }
    }, s, range.start)
  }
  s_1
}

pub fn projA_Shape_area(x : ProjA_Shape) -> BigInt {
  match x {
    ProjA_Shape::Circle(r) => (3N * r) * r
    ProjA_Shape::Rect(w, h) => w * h
    ProjA_Shape::Unit => 1N
  }
}

pub fn[A] std_Legacy_Range_forIn__loop_spec3(range : @lean_core.Std_Legacy_Range, f : (BigInt) -> (A) -> @lean_core.ForInStep[A], b : A, i : BigInt) -> A {
  if i < range.stop {
    match f(i)(b) {
      @lean_core.ForInStep::Done(a) => a
      @lean_core.ForInStep::Yield(a) => std_Legacy_Range_forIn__loop_spec3(range, f, a, i + range.step)
    }
  } else {
    b
  }
}
