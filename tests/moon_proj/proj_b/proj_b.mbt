// Extracted from Lean by lean6x7mbt (package `proj_b`).

pub fn projB_grow(s : @proj_a.ProjA_Shape) -> @proj_a.ProjA_Shape {
  match s {
    @proj_a.ProjA_Shape::Circle(r) => @proj_a.ProjA_Shape::Circle(r + 1N)
    @proj_a.ProjA_Shape::Rect(w, h) => @proj_a.ProjA_Shape::Rect(w + 1N, h + 1N)
    @proj_a.ProjA_Shape::Unit => @proj_a.ProjA_Shape::Rect(1N, 1N)
  }
}

pub fn projB_movePt(p : @proj_a.ProjA_Pt[BigInt]) -> @proj_a.ProjA_Pt[BigInt] {
  @proj_a.ProjA_Pt::{ x: p.x + p.y, y: @proj_a.projA_minus3(p.y) }
}

pub fn projB_describe(x : @proj_a.ProjA_Shape) -> BigInt {
  match x {
    @proj_a.ProjA_Shape::Circle(r) => r
    @proj_a.ProjA_Shape::Rect(w, _) => w
    @proj_a.ProjA_Shape::Unit => 0N
  }
}

pub let projB_shapes : @lean_core.List[@proj_a.ProjA_Shape] = @lean_core.List::Cons(@proj_a.ProjA_Shape::Circle(2N), @lean_core.List::Cons(@proj_a.ProjA_Shape::Rect(3N, 4N), @lean_core.List::Cons(@proj_a.ProjA_Shape::Unit, @lean_core.List::Nil)))

pub fn projB_ptSum(p : @proj_a.ProjA_Pt[BigInt]) -> BigInt {
  p.x + p.y
}

pub fn projB_pushDoubles(xs : @lean_core.List[BigInt]) -> Array[BigInt] {
  let a = @lean_core.lean_array_of_list(@lean_core.List::Nil)
  let a_1 = list_forIn__loop_spec2(xs, fn(a_1 : BigInt) {
    fn(r : Array[BigInt]) {
      let a_2 = r
      let a_3 = @lean_core.lean_array_push(a_2, (a_1 * 2N))
      @lean_core.ForInStep::Yield(a_3)
    }
  }, xs, a)
  a_1
}

pub fn projB_safeDiv(a : BigInt, b : BigInt) -> Result[BigInt, String] {
  if b == 0N { Err("div by zero") } else { Ok(@lean_core.lean_nat_div(a, b)) }
}

pub fn[A] projB_totalArea(inst : @proj_a.ProjA_HasArea[A], xs : @lean_core.List[A]) -> BigInt {
  @lean_core.list_foldl(fn(x1 : BigInt) { fn(x2 : BigInt) { x1 + x2 } }, 0N, @lean_core.list_map(inst.area, xs))
}

pub fn projB_countDown(n : BigInt) -> BigInt {
  let k = n
  let c = 0N
  let s = lean6x7mbt_loopForIn_spec4(fn(_ : Unit) {
    fn(r : @lean_core.MProd[BigInt, BigInt]) {
      let c_1 = r.fst
      let k_1 = r.snd
      if 0N < k_1 {
        let k_2 = @proj_a.projA_minus3(k_1)
        let c_2 = c_1 + 1N
        @lean_core.ForInStep::Yield(@lean_core.MProd::{ fst: c_2, snd: k_2 })
      } else {
        @lean_core.ForInStep::Done(@lean_core.MProd::{ fst: c_1, snd: k_1 })
      }
    }
  }, @lean_core.MProd::{ fst: c, snd: k })
  let fst = s.fst
  fst
}

pub fn[A, B] list_forIn__loop_spec2(as_ : @lean_core.List[A], f : (A) -> (B) -> @lean_core.ForInStep[B], x : @lean_core.List[A], x_1 : B) -> B {
  match x {
    @lean_core.List::Nil => x_1
    @lean_core.List::Cons(head, tail) => match f(head)(x_1) {
      @lean_core.ForInStep::Done(a) => a
      @lean_core.ForInStep::Yield(a) => list_forIn__loop_spec2(as_, f, tail, a)
    }
  }
}

pub fn[A] lean6x7mbt_loopForIn_spec4(f : (Unit) -> (A) -> @lean_core.ForInStep[A], b : A) -> A {
  match f(@lean_core.unit_unit)(b) {
    @lean_core.ForInStep::Done(a) => a
    @lean_core.ForInStep::Yield(a) => lean6x7mbt_loopForIn_spec4(f, a)
  }
}
