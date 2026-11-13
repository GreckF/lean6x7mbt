// Extracted from Lean by lean6x7mbt.

// Helpers

fn[A] lean_array_of_list(l : List[A]) -> Array[A] {
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

fn[A] lean_array_push(a : Array[A], x : A) -> Array[A] {
  let r = a.copy()
  r.push(x)
  r
}

fn[A] lean_array_get_d(a : Array[A], i : BigInt, d : A) -> A {
  if i < BigInt::from_int(a.length()) { a[BigInt::to_int(i)] } else { d }
}

fn[A] lean_array_get_bang(a : Array[A], i : BigInt) -> A {
  if i < BigInt::from_int(a.length()) { a[BigInt::to_int(i)] } else { abort("index out of bounds") }
}

fn[A] lean_array_set(a : Array[A], i : BigInt, x : A) -> Array[A] {
  let r = a.copy()
  if i < BigInt::from_int(r.length()) {
    r[BigInt::to_int(i)] = x
  }
  r
}

fn[A, B] lean_array_foldl(f : (B) -> (A) -> B, init : B, a : Array[A], start : BigInt, stop : BigInt) -> B {
  let mut acc = init
  let hi = if stop < BigInt::from_int(a.length()) { BigInt::to_int(stop) } else { a.length() }
  let mut i = BigInt::to_int(start)
  while i < hi {
    acc = f(acc)(a[i])
    i = i + 1
  }
  acc
}

fn lean_char_of_nat(n : BigInt) -> Char {
  if n < 55296 || (n > 57343 && n < 1114112) {
    BigInt::to_int(n).unsafe_to_char()
  } else {
    '\u{0}'
  }
}

fn lean_uint8_of_nat(n : BigInt) -> Byte {
  BigInt::to_int(n % 256).to_byte()
}

fn lean_float_of_scientific(m : BigInt, neg : Bool, e : BigInt) -> Double {
  let mut x = BigInt::to_int64(m).to_double()
  let mut k = BigInt::to_int(e)
  while k > 0 {
    if neg { x = x / 10.0 } else { x = x * 10.0 }
    k = k - 1
  }
  x
}

pub(all) enum List[A] {
  Nil
  Cons(A, List[A])
}

pub fn arrSum(a : Array[BigInt]) -> BigInt {
  lean_array_foldl((fn(x1 : BigInt) { fn(x2 : BigInt) { x1 + x2 } }), 0N, a, 0N, BigInt::from_int(a.length()))
}

pub fn arrPush(a : Array[BigInt], x : BigInt) -> Array[BigInt] {
  lean_array_push(a, x)
}

pub fn arrGet(a : Array[BigInt], i : BigInt) -> BigInt {
  lean_array_get_bang(a, i)
}

pub fn arrGetD(a : Array[BigInt], i : BigInt) -> BigInt {
  lean_array_get_d(a, i, 0N)
}

pub fn arrSize(a : Array[BigInt]) -> BigInt {
  BigInt::from_int(a.length())
}

pub fn arrMap(a : Array[BigInt]) -> Array[BigInt] {
  a.map((fn(x : BigInt) { x + 1N }))
}

pub let mkArr : Array[BigInt] = lean_array_of_list(List::Cons(1N, List::Cons(2N, List::Cons(3N, List::Nil))))

pub fn arrSet(a : Array[BigInt], i : BigInt, x : BigInt) -> Array[BigInt] {
  lean_array_set(a, i, x)
}

pub fn str1(s : String) -> String {
  s + "!"
}

pub fn strLen(s : String) -> BigInt {
  BigInt::from_int(s.length())
}

pub fn chr(n : BigInt) -> Char {
  lean_char_of_nat(n)
}

pub fn u64(a : UInt64, b : UInt64) -> UInt64 {
  (a * b) + 1N.to_uint64()
}

pub fn u8(a : Byte) -> Byte {
  a + lean_uint8_of_nat(200N)
}

pub fn flt(x : Double) -> Double {
  x * lean_float_of_scientific(25N, true, 1N)
}

pub fn nToStr(n : BigInt) -> String {
  n.to_string()
}
