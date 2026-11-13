// Extracted from Lean by lean6x7mbt.

// Helpers

fn lean_nat_sub(a : Int, b : Int) -> Int {
  if a > b { a - b } else { 0 }
}

fn lean_nat_div(a : Int, b : Int) -> Int {
  if b == 0 { 0 } else { a / b }
}

fn lean_int_ediv(a : Int, b : Int) -> Int {
  if b == 0 {
    0
  } else {
    let q = a / b
    let r = a % b
    if r < 0 { if b > 0 { q - 1 } else { q + 1 } } else { q }
  }
}

fn lean_int_emod(a : Int, b : Int) -> Int {
  if b == 0 {
    a
  } else {
    let r = a % b
    if r < 0 { if b > 0 { r + b } else { r - b } } else { r }
  }
}

pub(all) enum List[A] {
  Nil
  Cons(A, List[A])
}

pub fn sumSq(n : Int) -> Int {
  list_foldl(fn(acc : Int) { fn(k : Int) { acc + (k * k) } }, 0, list_range(n + 1))
}

pub fn mix(a : Int, b : Int) -> Int {
  ((a * b) - lean_int_ediv((a + b), 2)) + lean_int_emod(a, 3)
}

pub fn natSub(a : Int, b : Int) -> Int {
  lean_nat_sub(a, b) + lean_nat_div(a, (b + 1))
}

pub fn fib(x : Int) -> Int {
  if x == 0 {
    0
  } else {
    let n = x - 1
    if n == 0 {
      1
    } else {
      let n_1 = n - 1
      fib(n_1) + fib(n_1 + 1)
    }
  }
}

pub fn clamp(lo : Int, hi : Int, x : Int) -> Int {
  if x < lo { lo } else if hi < x { hi } else { x }
}

pub fn[A, B] list_foldl(f : (A) -> (B) -> A, x : A, x_1 : List[B]) -> A {
  match x_1 {
    List::Nil => x
    List::Cons(head, tail) => list_foldl(f, f(x)(head), tail)
  }
}

pub fn list_range(n : Int) -> List[Int] {
  list_range_loop(n, List::Nil)
}

pub fn list_range_loop(x : Int, x_1 : List[Int]) -> List[Int] {
  if x == 0 {
    x_1
  } else {
    let n = x - 1
    list_range_loop(n, List::Cons(n, x_1))
  }
}
