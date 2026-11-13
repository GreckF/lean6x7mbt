// Extracted from Lean by lean6x7mbt.

// Helpers

fn lean_nat_sub(a : BigInt, b : BigInt) -> BigInt {
  if a > b { a - b } else { 0 }
}

fn[A] lean_array_push(a : Array[A], x : A) -> Array[A] {
  let r = a.copy()
  r.push(x)
  r
}

fn lean_string_any(s : String, p : (Char) -> Bool) -> Bool {
  for c in s {
    if p(c) {
      return true
    }
  }
  false
}

fn lean_char_of_nat(n : BigInt) -> Char {
  if n < 55296 || (n > 57343 && n < 1114112) {
    BigInt::to_int(n).unsafe_to_char()
  } else {
    '\u{0}'
  }
}

pub(all) enum T_ {
  Leaf
  Node(T_, T_)
}

pub(all) enum List[A] {
  Nil
  Cons(A, List[A])
}

pub(all) enum ForInStep[A] {
  Done(A)
  Yield(A)
}

pub(all) struct ToString[A] {
  toString : (A) -> String
}

pub fn t_depth(x : T_) -> BigInt {
  match x {
    T_::Leaf => 0N
    T_::Node(l, r) => 1N + ({
      let x_1 = t_depth(l)
      let y = t_depth(r)
      if x_1 <= y { y } else { x_1 }
    })
  }
}

pub fn mx(a : BigInt, b : BigInt) -> BigInt {
  let x = a + 1N
  let y = {
    let y = a * 2N
    if b <= y { b } else { y }
  }
  if x <= y { y } else { x }
}

pub fn mdisc(y : BigInt) -> BigInt {
  let x = y * y
  if x == 0N { 1N } else if x == 25N { 3N } else { x + 1N }
}

pub fn sq(f : (BigInt) -> BigInt, n : BigInt) -> BigInt {
  let x = f(n)
  (x * x) + x
}

pub fn mk0(n : BigInt) -> Array[BigInt] {
  lean_array_push([], n)
}

pub fn strOps(s : String, c : Char) -> List[String] {
  List::Cons(s + c.to_string(), List::Cons(42N.to_string(), List::Cons(("[" + BigInt::from_int(s.length()).to_string()) + "]", List::Cons({
    let s_1 = -5N
    if s_1 >= 0N {
      let a = s_1
      a.to_string()
    } else {
      let a = -s_1 - 1N
      "-" + (a + 1N).to_string()
    }
  }, List::Cons(if true { "true" } else { "false" }, List::Cons(s + s, List::Cons("" + c.to_string(), List::Cons(list_toString(instToStringNat, List::Cons(1N, List::Cons(2N, List::Nil))), List::Cons(match Some(3N) {
    None => "none"
    Some(val) => ("(some " + addParenHeuristic(val.to_string())) + ")"
  }, List::Cons("" + c.to_string(), List::Cons(string_intercalate(", ", List::Cons(s, List::Cons(s, List::Nil))), List::Nil)))))))))))
}

pub fn strB(s : String, t : String) -> List[Bool] {
  List::Cons(s == t, List::Cons(!(s == t), List::Cons(s == "", List::Nil)))
}

pub fn chUp(c : Char) -> List[Char] {
  List::Cons(if (lean_char_of_nat(97N).to_uint() <= c.to_uint()) && (c.to_uint() <= lean_char_of_nat(122N).to_uint()) {
    (c.to_uint() + (lean_char_of_nat(65N).to_uint() - lean_char_of_nat(97N).to_uint())).reinterpret_as_int().unsafe_to_char()
  } else {
    c
  }, List::Cons(if (lean_char_of_nat(65N).to_uint() <= c.to_uint()) && (c.to_uint() <= lean_char_of_nat(90N).to_uint()) {
    (c.to_uint() + (lean_char_of_nat(97N).to_uint() - lean_char_of_nat(65N).to_uint())).reinterpret_as_int().unsafe_to_char()
  } else {
    c
  }, List::Nil))
}

pub fn chB(c : Char) -> List[Bool] {
  List::Cons((lean_char_of_nat(48N).to_uint() <= c.to_uint()) && (c.to_uint() <= lean_char_of_nat(57N).to_uint()), List::Cons(((lean_char_of_nat(65N).to_uint() <= c.to_uint()) && (c.to_uint() <= lean_char_of_nat(90N).to_uint())) || ((lean_char_of_nat(97N).to_uint() <= c.to_uint()) && (c.to_uint() <= lean_char_of_nat(122N).to_uint())), List::Cons({
    let b = lean_char_of_nat(120N)
    c == b
  }, List::Cons(char_instDecidableLt(c, lean_char_of_nat(109N)), List::Cons((((c == lean_char_of_nat(32N)) || (c == lean_char_of_nat(9N))) || (c == lean_char_of_nat(13N))) || (c == lean_char_of_nat(10N)), List::Nil)))))
}

pub fn arrLoop(a : Array[BigInt]) -> BigInt {
  let s = 0N
  let s_1 = array_forIn__loop_spec1(a, fn(a_1 : BigInt) {
    fn(r : BigInt) {
      let s_1 = r
      let do_jp = fn(s_2 : BigInt) {
        fn(_ : Unit) {
          let do_jp = fn(s_3 : BigInt) {
            fn(_ : Unit) {
              let s_4 = s_3 + a_1
              ForInStep::Yield(s_4)
            }
          }
          if a_1 == 2N { ForInStep::Yield(s_2) } else { do_jp(s_2)(()) }
        }
      }
      if a_1 == 5N { ForInStep::Done(s_1) } else { do_jp(s_1)(()) }
    }
  }, BigInt::from_int(a.length()), s)
  s_1
}

pub fn[A] list_toString(inst : ToString[A], x : List[A]) -> String {
  match x {
    List::Nil => "[]"
    List::Cons(head, tail) => match tail {
      List::Nil => ("[" + (inst.toString)(head)) + "]"
      _ => list_foldl(fn(l : String) { fn(r : A) { (l + ", ") + (inst.toString)(r) } }, "[" + (inst.toString)(head), tail) + lean_char_of_nat(93N).to_string()
    }
  }
}

pub let instToStringNat : ToString[BigInt] = ToString::{ toString: fn(n : BigInt) { n.to_string() } }

pub fn addParenHeuristic(s : String) -> String {
  if ((s.has_prefix("(") || s.has_prefix("[")) || s.has_prefix("{")) || s.has_prefix("#[") {
    s
  } else if !lean_string_any(s, (fn(c : Char) { (((c == lean_char_of_nat(32N)) || (c == lean_char_of_nat(9N))) || (c == lean_char_of_nat(13N))) || (c == lean_char_of_nat(10N)) })) {
    s
  } else {
    ("(" + s) + ")"
  }
}

pub fn string_intercalate(s : String, x : List[String]) -> String {
  match x {
    List::Nil => ""
    List::Cons(head, tail) => string_intercalate_go(head, s, tail)
  }
}

pub fn char_instDecidableLt(a : Char, b : Char) -> Bool {
  a.to_uint() < b.to_uint()
}

pub fn[A, B] array_forIn__loop_spec1(as_ : Array[A], f : (A) -> (B) -> ForInStep[B], i : BigInt, b : B) -> B {
  if i == 0N {
    b
  } else {
    let n = i - 1N
    match f(as_[BigInt::to_int(lean_nat_sub(lean_nat_sub(BigInt::from_int(as_.length()), 1N), n))])(b) {
      ForInStep::Done(a) => a
      ForInStep::Yield(a) => array_forIn__loop_spec1(as_, f, n, a)
    }
  }
}

pub fn[A, B] list_foldl(f : (A) -> (B) -> A, x : A, x_1 : List[B]) -> A {
  match x_1 {
    List::Nil => x
    List::Cons(head, tail) => list_foldl(f, f(x)(head), tail)
  }
}

pub fn string_intercalate_go(acc : String, s : String, x : List[String]) -> String {
  match x {
    List::Nil => acc
    List::Cons(head, tail) => string_intercalate_go((acc + s) + head, s, tail)
  }
}
