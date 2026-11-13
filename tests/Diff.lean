import Lean6x7mbt

/-! Differential tests: the expected values are not written by hand.  Every term of
`with_tests [..]` is evaluated by Lean and the generated `tests/moon/diff/diff_gen_wbtest.mbt`
asserts that the extracted MoonBit code agrees. -/

open Lean (ToExpr)

-- arithmetic
def arith (a b : Nat) : Nat := a * b + a / (b + 1) - b % 3 + (a - b) * 2
def intArith (a b : Int) : Int := a * b - (a + b) / 2 + a % 3 - Int.natAbs b

-- well-founded recursion and `partial`
def gcd' (a b : Nat) : Nat :=
  if h : b = 0 then a else gcd' b (a % b)
termination_by b
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

partial def collatz (n steps : Nat) : Nat :=
  if n ≤ 1 then steps
  else if n % 2 == 0 then collatz (n / 2) (steps + 1)
  else collatz (3 * n + 1) (steps + 1)

-- user inductive types as results
inductive Tree (α : Type) where
  | leaf : Tree α
  | node : Tree α → α → Tree α → Tree α
  deriving ToExpr, BEq

def Tree.insert (t : Tree Nat) (k : Nat) : Tree Nat :=
  match t with
  | .leaf => .node .leaf k .leaf
  | .node l x r => if k < x then .node (l.insert k) x r else .node l x (r.insert k)

def Tree.size {α} : Tree α → Nat
  | .leaf => 0
  | .node l _ r => l.size + 1 + r.size

def Tree.toList {α} : Tree α → List α
  | .leaf => []
  | .node l x r => l.toList ++ [x] ++ r.toList

def fromList (xs : List Nat) : Tree Nat := xs.foldl Tree.insert .leaf

def t0 : Tree Nat := fromList [5, 2, 8, 1]

structure Pt where
  x : Int
  y : Nat
  tag : String
  deriving ToExpr, BEq

def Pt.shift (p : Pt) (d : Int) : Pt := { p with x := p.x + d, y := p.y + 1, tag := p.tag ++ "!" }

inductive Shape where
  | circle (r : Nat)
  | rect (w h : Nat)
  | empty
  deriving ToExpr, BEq

def Shape.area : Shape → Nat
  | .circle r => 3 * r * r
  | .rect w h => w * h
  | .empty => 0

def Shape.grow (s : Shape) (k : Nat) : Shape :=
  match s with
  | .circle r => .circle (r + k)
  | .rect w h => .rect (w + k) (h * k)
  | .empty => .empty

-- List / Option / Prod / Array / String / Char
def evens (n : Nat) : List Nat := (List.range n).filter (· % 2 == 0)
def firstBig (xs : List Nat) : Option Nat := xs.find? (· > 10)
def divmod (a b : Nat) : Nat × Nat := (a / b, a % b)
def sq (xs : Array Nat) : Array Nat := xs.map fun x => x * x
def shout (s : String) : String := s ++ "!" ++ s
def nextChar (c : Char) : Char := Char.ofNat (c.toNat + 1)
def pairs (xs : List Nat) : List (Nat × String) := xs.map fun x => (x, toString x)

-- Except
def safeDiv (a b : Nat) : Except String Nat :=
  if b = 0 then .error "div by zero" else .ok (a / b)

deriving instance ToExpr, BEq for Except

-- Bool predicates
def isPrime (n : Nat) : Bool :=
  n ≥ 2 && (List.range (n - 2)).all fun i => n % (i + 2) != 0

mutual
def isEven : Nat → Bool
  | 0 => true
  | n+1 => isOdd n
def isOdd : Nat → Bool
  | 0 => false
  | n+1 => isEven n
end

extract_moonbit "tests/moon/diff/diff.mbt"
  arith intArith gcd' collatz Tree.insert Tree.size Tree.toList fromList t0 Pt.shift Shape.area
  Shape.grow evens firstBig divmod sq shout nextChar pairs safeDiv isPrime isEven
with_tests [
  arith 7 3, arith 2 9, arith 100 0,
  intArith 7 (-3), intArith (-7) 3, intArith (-20) (-6),
  gcd' 48 18, gcd' 17 5, gcd' 0 9,
  collatz 27 0, collatz 1 0,
  Tree.insert t0 4, fromList [3, 1, 2], t0,
  Tree.size t0, Tree.toList (Tree.insert t0 7),
  Pt.shift ⟨1, 2, "p"⟩ (-5),
  Shape.grow (.rect 2 3) 4, Shape.grow (.circle 1) 2, Shape.area (.rect 6 7), Shape.grow .empty 1,
  evens 10, firstBig [1, 5, 12, 30], firstBig [1, 2], divmod 17 5, divmod 3 0,
  sq #[1, 2, 3], shout "ab\"c\n", nextChar 'a', pairs [1, 20],
  safeDiv 7 2, safeDiv 1 0,
  isPrime 97, isPrime 91, isPrime 1, isEven 10, isOdd 10, gcd' 12 18 == 6
]
