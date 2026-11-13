import Lean6x7mbt.Table

/-!
# Default mappings of Lean core types and functions to MoonBit

Import this module (done by `import Lean6x7mbt`) to get `Nat`, `Int`, `Bool`,
`Option`, products, `Except`, ... mapped to their MoonBit counterparts.  All
entries can be overridden by later `extract_constant`/`extract_inductive`
commands.

`@Nat`/`@Int` follow `set_option lean6x7mbt.nat`.
-/

namespace Lean6x7mbt

/-! ## Bool, Decidable, Unit -/

extract_inductive Bool => "Bool" ["false", "true"]
extract_inductive Decidable => "Bool" ["false", "true"]
extract_inductive PUnit => "Unit" ["()"]

extract_constant Bool.not => "!$0"
extract_constant Bool.and => "($0 && $1)"
extract_constant Bool.or => "($0 || $1)"
extract_constant Bool.xor => "($0 != $1)"
extract_constant Bool.decEq => "($0 == $1)"
extract_constant instDecidableEqBool => "($0 == $1)"
extract_constant instDecidableAnd => "($0 && $1)"
extract_constant instDecidableOr => "($0 || $1)"
extract_constant instDecidableNot => "!$0"
extract_constant instDecidableTrue => "true"
extract_constant instDecidableFalse => "false"

/-! ## Nat and Int -/

extract_inductive Nat => "@Nat" ["@zero", "($0 + @one)"]
extract_inductive Int => "@Int" ["$0", "(-$0 - @one)"]

extract_helper lean_nat_sub => "fn lean_nat_sub(a : @Nat, b : @Nat) -> @Nat {\n  if a > b { a - b } else { 0 }\n}"
extract_helper lean_nat_div => "fn lean_nat_div(a : @Nat, b : @Nat) -> @Nat {\n  if b == 0 { 0 } else { a / b }\n}"
extract_helper lean_nat_mod => "fn lean_nat_mod(a : @Nat, b : @Nat) -> @Nat {\n  if b == 0 { a } else { a % b }\n}"
extract_helper lean_nat_pow => "fn lean_nat_pow(a : @Nat, b : @Nat) -> @Nat {\n  let mut result : @Nat = 1\n  let mut base = a\n  let mut e = b\n  while e > 0 {\n    if e % 2 == 1 { result = result * base }\n    base = base * base\n    e = e / 2\n  }\n  result\n}"
extract_helper lean_int_ediv => "fn lean_int_ediv(a : @Int, b : @Int) -> @Int {\n  if b == 0 {\n    0\n  } else {\n    let q = a / b\n    let r = a % b\n    if r < 0 { if b > 0 { q - 1 } else { q + 1 } } else { q }\n  }\n}"
extract_helper lean_int_emod => "fn lean_int_emod(a : @Int, b : @Int) -> @Int {\n  if b == 0 {\n    a\n  } else {\n    let r = a % b\n    if r < 0 { if b > 0 { r + b } else { r - b } } else { r }\n  }\n}"
extract_helper lean_int_natabs => "fn lean_int_natabs(a : @Int) -> @Nat {\n  if a < 0 { -a } else { a }\n}"
extract_helper lean_int_tonat => "fn lean_int_tonat(a : @Int) -> @Nat {\n  if a < 0 { 0 } else { a }\n}"

extract_constant Nat.add => "($0 + $1)"
extract_constant Nat.sub => "lean_nat_sub($0, $1)"
extract_constant Nat.mul => "($0 * $1)"
extract_constant Nat.div => "lean_nat_div($0, $1)"
extract_constant Nat.mod => "lean_nat_mod($0, $1)"
extract_constant Nat.pow => "lean_nat_pow($0, $1)"
extract_constant Nat.beq => "($0 == $1)"
extract_constant Nat.ble => "($0 <= $1)"
extract_constant Nat.blt => "($0 < $1)"
extract_constant Nat.decEq => "($0 == $1)"
extract_constant instDecidableEqNat => "($0 == $1)"
extract_constant Nat.decLt => "($0 < $1)"
extract_constant Nat.decLe => "($0 <= $1)"

extract_constant Int.add => "($0 + $1)"
extract_constant Int.sub => "($0 - $1)"
extract_constant Int.mul => "($0 * $1)"
extract_constant Int.neg => "(-$0)"
extract_constant Int.ediv => "lean_int_ediv($0, $1)"
extract_constant Int.emod => "lean_int_emod($0, $1)"
extract_constant Int.natAbs => "lean_int_natabs($0)"
extract_constant Int.toNat => "lean_int_tonat($0)"
extract_constant Int.decEq => "($0 == $1)"
extract_constant Nat.repr => "$0.to_string()"
extract_constant Int.repr => "$0.to_string()"
extract_constant Int.instDecidableEq => "($0 == $1)"
extract_constant Int.decLt => "($0 < $1)"
extract_constant Int.decLe => "($0 <= $1)"

/-! ## Option, products, sums -/

extract_inductive Option => "Option[$0]" ["None", "Some($0)"]
extract_inductive Prod => "($0, $1)" ["($0, $1)"]
extract_constant Prod.fst => "$0.0"
extract_constant Prod.snd => "$0.1"
extract_inductive Except => "Result[$1, $0]" ["Err($0)", "Ok($0)"]

/-! ## Strings -/

extract_inductive String => "String" ["abort(\"String.mk\")"]
extract_constant String.append => "($0 + $1)"
extract_constant String.decEq => "($0 == $1)"
extract_constant instDecidableEqString => "($0 == $1)"

/-! ## Conversions between Nat/Int and MoonBit's `Int` -/

extract_helper lean_id_int => "fn lean_id_int(x : Int) -> Int {\n  x\n}"
extract_helper lean_id_int64 => "fn lean_id_int64(x : Int64) -> Int64 {\n  x\n}"

/-! ## Arrays

A Lean `Array` is MoonBit's `Array`.  Lean arrays are persistent, so every
update copies; this is correct but O(n). -/

extract_inductive Array => "Array[$0]" ["lean_array_of_list($0)"]

extract_helper lean_array_of_list => "fn[A] lean_array_of_list(l : List[A]) -> Array[A] {\n  let out : Array[A] = []\n  let mut cur = l\n  while true {\n    match cur {\n      List::Nil => break\n      List::Cons(h, t) => {\n        out.push(h)\n        cur = t\n      }\n    }\n  }\n  out\n}"
extract_helper lean_array_to_list => "fn[A] lean_array_to_list(a : Array[A]) -> List[A] {\n  let mut l : List[A] = List::Nil\n  for k = a.length() - 1; k >= 0; k = k - 1 {\n    l = List::Cons(a[k], l)\n  }\n  l\n}"
extract_helper lean_array_push => "fn[A] lean_array_push(a : Array[A], x : A) -> Array[A] {\n  let r = a.copy()\n  r.push(x)\n  r\n}"
extract_helper lean_array_append => "fn[A] lean_array_append(a : Array[A], b : Array[A]) -> Array[A] {\n  let r = a.copy()\n  for x in b {\n    r.push(x)\n  }\n  r\n}"
extract_helper lean_array_get_d => "fn[A] lean_array_get_d(a : Array[A], i : @Nat, d : A) -> A {\n  if i < @ofInt(a.length()) { a[@toInt(i)] } else { d }\n}"
extract_helper lean_array_get_bang => "fn[A] lean_array_get_bang(a : Array[A], i : @Nat) -> A {\n  if i < @ofInt(a.length()) { a[@toInt(i)] } else { abort(\"index out of bounds\") }\n}"
extract_helper lean_array_set => "fn[A] lean_array_set(a : Array[A], i : @Nat, x : A) -> Array[A] {\n  let r = a.copy()\n  if i < @ofInt(r.length()) {\n    r[@toInt(i)] = x\n  }\n  r\n}"
extract_helper lean_array_foldl => "fn[A, B] lean_array_foldl(f : (B) -> (A) -> B, init : B, a : Array[A], start : @Nat, stop : @Nat) -> B {\n  let mut acc = init\n  let hi = if stop < @ofInt(a.length()) { @toInt(stop) } else { a.length() }\n  let mut i = @toInt(start)\n  while i < hi {\n    acc = f(acc)(a[i])\n    i = i + 1\n  }\n  acc\n}"

extract_constant Array.toList => "lean_array_to_list($0)"
extract_constant List.toArray => "lean_array_of_list($0)"
extract_constant Array.empty => "[]"
extract_constant Array.mkEmpty => "[]"
extract_constant Array.emptyWithCapacity => "[]"
extract_constant Array.push => "lean_array_push($0, $1)"
extract_constant Array.append => "lean_array_append($0, $1)"
extract_constant Array.size => "@ofInt($0.length())"
extract_constant Array.getD => "lean_array_get_d($0, $1, $2)"
extract_constant Array.get!Internal => "lean_array_get_bang($0, $1)"
extract_constant Array.getInternal => "$0[@toInt($1)]"
extract_constant Array.set! => "lean_array_set($0, $1, $2)"
extract_constant Array.setIfInBounds => "lean_array_set($0, $1, $2)"
extract_constant Array.map => "$1.map($0)"
extract_constant Array.foldl => "lean_array_foldl($0, $1, $2, $3, $4)"

/-! ## Strings and characters (UTF-16 in MoonBit, so `length` counts code units) -/

extract_constant String.length => "@ofInt($0.length())"
extract_constant String.push => "($0 + $1.to_string())"
extract_constant String.isEmpty => "($0 == \"\")"

-- `Char.mk v _` (as in `Char.toUpper`): the template is only valid as an expression
-- `String.Internal.*` are `@[extern] opaque`: they have no Lean definition to extract
extract_constant String.Internal.append => "($0 + $1)"
extract_constant String.Internal.length => "@ofInt($0.length())"
extract_constant String.Internal.isEmpty => "($0 == \"\")"
extract_constant String.Internal.isPrefixOf => "$1.has_prefix($0)"
extract_constant String.Internal.contains => "$0.contains_char($1)"
extract_helper lean_string_any => "fn lean_string_any(s : String, p : (Char) -> Bool) -> Bool {\n  for c in s {\n    if p(c) {\n      return true\n    }\n  }\n  false\n}"
extract_constant String.Internal.any => "lean_string_any($0, $1)"
extract_helper lean_string_pushn => "fn lean_string_pushn(s : String, c : Char, n : @Nat) -> String {\n  let mut r = s\n  let mut k = n\n  while k > 0 {\n    r = r + c.to_string()\n    k = k - 1\n  }\n  r\n}"
extract_constant String.Internal.pushn => "lean_string_pushn($0, $1, $2)"
extract_helper lean_string_intercalate => "fn lean_string_intercalate(sep : String, l : List[String]) -> String {\n  let mut r = \"\"\n  let mut first = true\n  let mut cur = l\n  while true {\n    match cur {\n      List::Nil => break\n      List::Cons(h, t) => {\n        if first { r = h } else { r = r + sep + h }\n        first = false\n        cur = t\n      }\n    }\n  }\n  r\n}"
extract_constant String.Internal.intercalate => "lean_string_intercalate($0, $1)"

extract_inductive Char => "Char" ["$0.reinterpret_as_int().unsafe_to_char()"]
extract_constant Char.val => "$0.to_uint()"
extract_helper lean_char_of_nat => "fn lean_char_of_nat(n : @Nat) -> Char {\n  if n < 55296 || (n > 57343 && n < 1114112) {\n    @toInt(n).unsafe_to_char()\n  } else {\n    '\\u{0}'\n  }\n}"
extract_constant Char.ofNat => "lean_char_of_nat($0)"
extract_constant Char.toNat => "@ofInt($0.to_int())"
extract_constant instDecidableEqChar => "($0 == $1)"

/-! ## Fixed-width integers -/

extract_inductive UInt8 => "Byte" ["abort(\"UInt8.mk\")"]
extract_inductive UInt16 => "UInt16" ["abort(\"UInt16.mk\")"]
extract_inductive UInt32 => "UInt" ["abort(\"UInt32.mk\")"]
extract_inductive UInt64 => "UInt64" ["abort(\"UInt64.mk\")"]
extract_inductive USize => "UInt64" ["abort(\"USize.mk\")"]

extract_helper lean_uint8_of_nat => "fn lean_uint8_of_nat(n : @Nat) -> Byte {
  @toInt(n % 256).to_byte()
}"
extract_constant UInt8.ofNat => "lean_uint8_of_nat($0)"
extract_constant UInt8.toNat => "@ofInt($0.to_int())"
extract_constant UInt8.add => "($0 + $1)"
extract_constant UInt8.sub => "($0 - $1)"
extract_constant UInt8.mul => "($0 * $1)"
extract_constant UInt8.decEq => "($0 == $1)"
extract_constant UInt8.decLt => "($0 < $1)"
extract_constant UInt8.decLe => "($0 <= $1)"

extract_helper lean_int64_to_uint => "fn lean_int64_to_uint(x : Int64) -> UInt {
  x.to_int().reinterpret_as_uint()
}"
extract_constant UInt32.ofNat => "@toU32($0)"
extract_constant UInt32.toNat => "@ofU32($0)"
extract_constant UInt32.add => "($0 + $1)"
extract_constant UInt32.sub => "($0 - $1)"
extract_constant UInt32.mul => "($0 * $1)"
extract_constant UInt32.decEq => "($0 == $1)"
extract_constant UInt32.decLt => "($0 < $1)"
extract_constant UInt32.decLe => "($0 <= $1)"

extract_constant UInt64.ofNat => "$0.to_uint64()"
extract_constant UInt64.toNat => "@ofU64($0)"
extract_constant UInt64.add => "($0 + $1)"
extract_constant UInt64.sub => "($0 - $1)"
extract_constant UInt64.mul => "($0 * $1)"
extract_constant UInt64.decEq => "($0 == $1)"
extract_constant UInt64.decLt => "($0 < $1)"
extract_constant UInt64.decLe => "($0 <= $1)"

/-! ## Floats -/

extract_inductive Float => "Double" ["abort(\"Float.mk\")"]
extract_helper lean_float_of_scientific => "fn lean_float_of_scientific(m : @Nat, neg : Bool, e : @Nat) -> Double {\n  let mut x = @toInt64(m).to_double()\n  let mut k = @toInt(e)\n  while k > 0 {\n    if neg { x = x / 10.0 } else { x = x * 10.0 }\n    k = k - 1\n  }\n  x\n}"
extract_constant Float.ofScientific => "lean_float_of_scientific($0, $1, $2)"
extract_constant Float.add => "($0 + $1)"
extract_constant Float.sub => "($0 - $1)"
extract_constant Float.mul => "($0 * $1)"
extract_constant Float.div => "($0 / $1)"
extract_constant Float.neg => "(-$0)"
extract_constant Float.decLt => "($0 < $1)"
extract_constant Float.decLe => "($0 <= $1)"
extract_constant Float.beq => "($0 == $1)"

/-! ## Panics -/

extract_constant panicCore => "abort($0)"

end Lean6x7mbt
