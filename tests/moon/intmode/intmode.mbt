// Extracted from Lean by lean6x7mbt.

// Helpers

fn lean_nat_sub(a : Int, b : Int) -> Int {
  if a > b { a - b } else { 0 }
}

fn lean_nat_div(a : Int, b : Int) -> Int {
  if b == 0 { 0 } else { a / b }
}

fn lean_nat_mod(a : Int, b : Int) -> Int {
  if b == 0 { a } else { a % b }
}

fn lean_nat_pow(a : Int, b : Int) -> Int {
  let mut result : Int = 1
  let mut base = a
  let mut e = b
  while e > 0 {
    if e % 2 == 1 { result = result * base }
    base = base * base
    e = e / 2
  }
  result
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

pub fn fact(x : Int) -> Int {
  if x == 0 {
    1
  } else {
    let n = x - 1
    (n + 1) * fact(n)
  }
}

pub fn sub3(n : Int) -> Int {
  lean_nat_sub(n, 3)
}

pub fn collatz(n : Int, steps : Int) -> Int {
  if n <= 1 {
    steps
  } else if ({
    let a = lean_nat_mod(n, 2)
    a == 0
  }) {
    collatz(lean_nat_div(n, 2), steps + 1)
  } else {
    collatz((3 * n) + 1, steps + 1)
  }
}

pub fn ediv(a : Int, b : Int) -> Int {
  lean_int_ediv(a, b)
}

pub fn emod(a : Int, b : Int) -> Int {
  lean_int_emod(a, b)
}

pub fn powTwo(n : Int) -> Int {
  lean_nat_pow(2, n)
}
