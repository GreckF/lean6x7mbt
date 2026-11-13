import Lean6x7mbt

/-!
`import_mbti` test: `tests/moon/extlib` is a hand-written MoonBit library; its interface
(`pkg.generated.mbti`, written by `moon info`) is imported as axioms in namespace `Ext`, used from
ordinary Lean code and extracted to `tests/moon/mbti` (whose `moon.pkg` imports `extlib`).
-/

/--
warning: import_mbti: skipped `pub const LIMIT : Int32 = 10`: MoonBit `Int32` has no Lean counterpart when `lean6x7mbt.nat` is "bigint" (Lean `Nat`/`Int` extract to `BigInt`)
---
warning: import_mbti: skipped `pub fn[T : Describe] describe_all(Array[T]) -> String`: type parameter `T` with trait bound `Describe`
---
warning: import_mbti: skipped `pub fn first_byte(Bytes) -> Byte`: unknown type `Bytes`
---
warning: import_mbti: skipped `pub async fn later(@bigint.BigInt) -> @bigint.BigInt`: async function
---
warning: import_mbti: skipped `pub fn make_binop() -> (@bigint.BigInt, @bigint.BigInt) -> @bigint.BigInt`: closure with 2 parameters (Lean function values are single-argument closures)
---
warning: import_mbti: skipped `pub fn risky(@bigint.BigInt) -> @bigint.BigInt raise Failure`: function that may raise (`raise`)
---
warning: import_mbti: skipped `pub fn small_int(Int32) -> Int32`: MoonBit `Int32` has no Lean counterpart when `lean6x7mbt.nat` is "bigint" (Lean `Nat`/`Int` extract to `BigInt`)
---
warning: import_mbti: skipped `pub fn triple(@bigint.BigInt) -> (@bigint.BigInt, @bigint.BigInt, @bigint.BigInt)`: 3-tuple (only pairs correspond to Lean's `Prod`)
---
warning: import_mbti: skipped `pub suberror Oops {`: error type (`suberror`)
---
warning: import_mbti: skipped `pub impl Describe for Point`: trait implementation (`impl`)
---
warning: import_mbti: skipped `pub type Index = Int32`: type alias (aliases are already expanded in signatures)
---
warning: import_mbti: skipped `pub trait Describe {`: trait
---
info: import_mbti: package lean6x7mbt/tests/extlib as Ext: imported 32 function(s)/value(s) and 5 type(s), skipped 12 item(s)
-/
#guard_msgs in
import_mbti "tests/moon/extlib/pkg.generated.mbti" as Ext

open Ext

/-! ## Functions on numbers, strings, characters, floats -/

def succTwice (n : Int) : Int := succ (succ n)
def addAll (a b c : Int) : Int := add3 a b c
def addOne : Int → Int → Int := add3 1                 -- partial application of an axiom
def mapSucc (xs : List Int) : List Int := xs.map succ  -- axiom as a higher-order argument
def mapAdd (xs : List Int) : List Int := xs.map (add3 1 2)
def sumSucc (xs : List Int) : Int := Id.run do         -- called in a loop
  let mut acc : Int := 0
  for x in xs do
    acc := acc + succ x
  return acc
def loopAdd (n : Nat) : Int := Id.run do
  let mut s : Int := 0
  for i in [0:n] do
    s := add3 s (Int.ofNat i) 1
  return s
def greet (s : String) : String := shout (shout s)
def bothVowels (a b : Char) : Bool := is_vowel a && is_vowel b
def quarter (x : Float) : Float := halve (halve x)
def lowByteOf (n : UInt32) : UInt8 := low_byte n
def bigTwice (x : UInt64) : UInt64 := big_u64 (big_u64 x)
def useMax (n : Int) : Int := n + max_items
def hello : String := greeting ++ ", world"
def theAnswer : Int := unit_fn ()
def labelledOnly (n : Int) : Int := labelled n

/-! ## Closures -/

def incTwice (x : Int) : Int := apply_twice (fun y => y + 1) x
def addTwice (x : Int) : Int := apply_twice (add3 10 20) x
def succTwiceHO (x : Int) : Int := apply_twice succ x
def adder5 (x : Int) : Int := make_adder 5 x                 -- result closure applied at once
def adders (xs : List Int) : List Int := xs.map (make_adder 100)
def pairSum (f : Int → Int → Int) (x : Int) : Int := add_curried_pair f x   -- 2-argument closure adapter
def pairSumAdd (x : Int) : Int := add_curried_pair (fun a b => a + b) x
def pairSumPartial (x : Int) : Int := add_curried_pair (add3 1000) x
def thunk (n : Int) : Int := run_thunk (fun _ => n)

/-! ## Containers -/

def arrSum (a : Array Int) : Int := sum_array a
def rangeSum (n : Int) : Int := sum_array (range_array n)
def firstEvenOr (a : Array Int) (d : Int) : Int := (first_even a).getD d
def digitOr (s : String) (d : Int) : Int :=
  match parse_digit s with
  | .ok n => n
  | .error _ => d
def digitErr (s : String) : String :=
  match parse_digit s with
  | .ok _ => ""
  | .error e => e
def swapped (n : Int) (s : String) : String × Int := swap_pair (n, s)
def incOpt (o : Option Int) : Option Int := map_option o (fun x => x + 1)
def twiceStr (s : String) : String × String := twice s
def orDefault (o : Option Int) : Int := option_or o 7

/-! ## Opaque types -/

def counterDemo (n : Int) : Int := ((Counter.new n).bump 5).bump 10 |>.get
def counters (xs : List Int) : List Int := (xs.map Counter.new).map Counter.get
def boxDemo (n : Int) : Int := (Box.new n).get
def boxStr (s : String) : String := Box.get (Box.new s)

/-! ## Enums and structs -/

def areaOf (s : Shape) : Float := s.area
def areas : List Float := [Shape.Circle 2.0, Shape.Rect 2.0 3.0, Shape.Dot].map Shape.area
def shapeName (s : Shape) : String :=
  match s with
  | .Circle _ => "circle"
  | .Rect w h => if w == h then "square" else "rect"
  | .Dot => "dot"
def sampleTree : Tree Int := .Node (.Node .Leaf 1 .Leaf) 2 (.Node .Leaf 3 (.Node .Leaf 4 .Leaf))
def treeSum : Tree Int → Int
  | .Leaf => 0
  | .Node l x r => treeSum l + x + treeSum r
def sampleSize : Int := tree_size sampleTree
def sampleDepth : Int := sampleTree.depth
def pointNorm (a b : Int) : Int := (Point.mk a b).norm1
def pointSum (p : Point) : Int := p.x + p.y
def pointSwap (p : Point) : Point := { p with x := p.y, y := p.x }
def pointMatch (p : Point) : Int :=
  match p with
  | ⟨a, b⟩ => a * b
def pointLit : Point := { x := 3, y := -4 }

extract_moonbit "tests/moon/mbti/mbti.mbt"
  succTwice addAll addOne mapSucc mapAdd sumSucc loopAdd greet bothVowels quarter lowByteOf bigTwice
  useMax hello theAnswer labelledOnly
  incTwice addTwice succTwiceHO adder5 adders pairSum pairSumAdd pairSumPartial thunk
  arrSum rangeSum firstEvenOr digitOr digitErr swapped incOpt twiceStr orDefault
  counterDemo counters boxDemo boxStr
  areaOf areas shapeName sampleTree treeSum sampleSize sampleDepth pointNorm pointSum pointSwap pointMatch pointLit

/-! ## Other options -/

-- `unqualified`: the caller lives in the MoonBit package of the library (no `@extlib.` prefix)
#guard_msgs (drop warning) in
import_mbti "tests/moon/extlib/pkg.generated.mbti" as ExtU (unqualified)

def unq (n : Int) : Int := ExtU.succ (ExtU.Counter.get (ExtU.Counter.new n))

/--
info: // Extracted from Lean by lean6x7mbt.

pub fn unq(n : BigInt) -> BigInt {
  succ(Counter::get(Counter::new(n)))
}
-/
#guard_msgs in
extract_moonbit unq

-- the package alias can be chosen (it must match the `moon.pkg` of the generated code)
#guard_msgs (drop warning) in
import_mbti "tests/moon/extlib/pkg.generated.mbti" as ExtA (alias := "lib")

def aliased (s : String) : String := ExtA.shout s

/--
info: // Extracted from Lean by lean6x7mbt.

pub fn aliased(s : String) -> String {
  @lib.shout(s)
}
-/
#guard_msgs in
extract_moonbit aliased

-- in `int` mode MoonBit's `Int` is the counterpart of Lean's `Int`; `BigInt` has none
set_option lean6x7mbt.nat "int" in
#guard_msgs (drop warning) in
import_mbti "tests/moon/extlib/pkg.generated.mbti" as ExtI

#check @ExtI.small_int

-- imported functions cannot be evaluated by Lean: `with_tests` says so
/--
error: this test term cannot be evaluated by Lean: it uses `Ext.succ`, a function imported from MoonBit (`import_mbti`) that has no Lean implementation; check such code in a hand-written `*_wbtest.mbt` instead
-/
#guard_msgs in
extract_moonbit with_tests [succ 1 == 2]
