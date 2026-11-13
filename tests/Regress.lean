import Lean6x7mbt

/-! Regression tests for bugs found while auditing the extractor. -/

-- 1. Inlining must not duplicate work: `max (f x) (g y)` evaluated `f x` twice,
--    which made `T.depth` exponential.
inductive T where
  | leaf
  | node (l r : T)

def T.depth : T → Nat
  | .leaf => 0
  | .node l r => 1 + max l.depth r.depth

def mx (a b : Nat) : Nat := max (a + 1) (min b (a * 2))

-- a non-trivial discriminant inspected several times is bound once
def mdisc (y : Int) : Int :=
  match y * y with
  | 0 => 1
  | 25 => 3
  | x => x + 1

def sq (f : Nat → Nat) (n : Nat) : Nat := (fun x => x * x + x) (f n)

-- 2. A template without placeholders still consumes the arguments (`[](n)`).
def mk0 (n : Nat) : Array Nat := (Array.mkEmpty n).push n

-- 3. `@[extern] opaque` constants (`String.Internal.*`) were extracted from
--    their inhabitation witness: `toString (-5 : Int)` gave `""`.
def strOps (s : String) (c : Char) : List String :=
  [s.push c, toString 42, s!"[{s.length}]", toString (-5 : Int), toString true, s ++ s,
   toString c, toString [1, 2], toString (some 3), String.singleton c, ", ".intercalate [s, s]]

def strB (s t : String) : List Bool := [s == t, s != t, s.isEmpty]

-- 4. Projections of mapped types (`c.val`) and `Char.mk` (`Char.toUpper`).
def chUp (c : Char) : List Char := [c.toUpper, c.toLower]
def chB (c : Char) : List Bool := [c.isDigit, c.isAlpha, c == 'x', c < 'm', c.isWhitespace]

-- 5. `for x in arr` reads the array directly (`Array.getInternal`).
def arrLoop (a : Array Nat) : Nat := Id.run do
  let mut s := 0
  for x in a do
    if x == 5 then break
    if x == 2 then continue
    s := s + x
  return s

extract_moonbit "tests/moon/regress/regress.mbt"
  T.depth mx mdisc sq mk0 strOps strB chUp chB arrLoop

/-! Constants without a definition must be reported, never silently extracted. -/

@[extern "my_ext"] opaque myExt : Nat → Nat
def useExt (n : Nat) : Nat := myExt n + 1

/--
error: extraction failed (1 item could not be extracted):

no extraction for `myExt`: it has no definition (axiom, `opaque` or `extern` constant)
  via useExt → myExt

missing mappings (add them, e.g.):
  extract_constant myExt => "..."
-/
#guard_msgs in
extract_moonbit useExt

def strBytes (s : String) : Nat := s.toByteArray.size

/--
error: extraction failed (1 item could not be extracted):

projection `String.toByteArray` of the mapped type `String` has no extraction
  via strBytes → String.toByteArray

missing mappings (add them, e.g.):
  extract_constant String.toByteArray => "..."
-/
#guard_msgs in
extract_moonbit strBytes

/-! All problems of one extraction are reported together, with the dependency chain
(here `useBoth → helper → myExt2` goes through an intermediate function). -/

@[extern "my_ext2"] opaque myExt2 : Nat → Nat
def helper (n : Nat) : Nat := myExt2 n * 2
def useBoth (n : Nat) : Nat := helper n + myExt n

/--
error: extraction failed (2 items could not be extracted):

no extraction for `myExt`: it has no definition (axiom, `opaque` or `extern` constant)
  via useBoth → myExt

no extraction for `myExt2`: it has no definition (axiom, `opaque` or `extern` constant)
  via useBoth → helper → myExt2

missing mappings (add them, e.g.):
  extract_constant myExt => "..."
  extract_constant myExt2 => "..."
-/
#guard_msgs in
extract_moonbit useBoth
