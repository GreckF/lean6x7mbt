// Extracted from Lean by lean6x7mbt.

// Helpers

fn lean_nat_sub(a : Int64, b : Int64) -> Int64 {
  if a > b { a - b } else { 0 }
}

fn lean_nat_div(a : Int64, b : Int64) -> Int64 {
  if b == 0 { 0 } else { a / b }
}

fn lean_nat_mod(a : Int64, b : Int64) -> Int64 {
  if b == 0 { a } else { a % b }
}

fn lean_nat_pow(a : Int64, b : Int64) -> Int64 {
  let mut result : Int64 = 1
  let mut base = a
  let mut e = b
  while e > 0 {
    if e % 2 == 1 { result = result * base }
    base = base * base
    e = e / 2
  }
  result
}

fn[A] lean_array_get_d(a : Array[A], i : Int64, d : A) -> A {
  if i < Int::to_int64(a.length()) { a[Int64::to_int(i)] } else { d }
}

fn[A] lean_array_get_bang(a : Array[A], i : Int64) -> A {
  if i < Int::to_int64(a.length()) { a[Int64::to_int(i)] } else { abort("index out of bounds") }
}

fn[A] lean_array_set(a : Array[A], i : Int64, x : A) -> Array[A] {
  let r = a.copy()
  if i < Int::to_int64(r.length()) {
    r[Int64::to_int(i)] = x
  }
  r
}

fn[A, B] lean_array_foldl(f : (B) -> (A) -> B, init : B, a : Array[A], start : Int64, stop : Int64) -> B {
  let mut acc = init
  let hi = if stop < Int::to_int64(a.length()) { Int64::to_int(stop) } else { a.length() }
  let mut i = Int64::to_int(start)
  while i < hi {
    acc = f(acc)(a[i])
    i = i + 1
  }
  acc
}

fn lean_uint8_of_nat(n : Int64) -> Byte {
  Int64::to_int(n % 256).to_byte()
}

fn lean_int64_to_uint(x : Int64) -> UInt {
  x.to_int().reinterpret_as_uint()
}

pub fn u8m(n : Int64) -> Byte {
  nat_toUInt8(n) + lean_uint8_of_nat(1L)
}

pub fn u32m(n : Int64) -> UInt {
  nat_toUInt32(n) + lean_int64_to_uint(1L)
}

pub fn u64m(n : Int64) -> UInt64 {
  nat_toUInt64(n) + 1L.to_uint64()
}

pub fn un(a : Byte, b : UInt, c : UInt64) -> Int64 {
  (Int::to_int64(a.to_int()) + UInt::to_int64(b)) + UInt64::to_int64(c)
}

pub fn arrm(a : Array[Int64], i : Int64) -> Int64 {
  ((lean_array_get_bang(a, i) + lean_array_get_d(a, i, 3L)) + Int::to_int64(a.length())) + lean_array_foldl((fn(x1 : Int64) { fn(x2 : Int64) { x1 + x2 } }), 0L, lean_array_set(a, i, 9L), 0L, Int::to_int64(lean_array_set(a, i, 9L).length()))
}

pub fn natOps(a : Int64, b : Int64) -> Int64 {
  ((lean_nat_sub(a, b) + lean_nat_div(a, b)) + lean_nat_mod(a, b)) + lean_nat_pow(a, 2L)
}

pub let nat_toUInt8 : (Int64) -> Byte = fn(n : Int64) { lean_uint8_of_nat(n) }

pub let nat_toUInt32 : (Int64) -> UInt = fn(n : Int64) { lean_int64_to_uint(n) }

pub let nat_toUInt64 : (Int64) -> UInt64 = fn(n : Int64) { n.to_uint64() }
