import Lean6x7mbt

-- do-notation in concrete monads
def addOpt (a b : Option Nat) : Option Nat := do
  let x ← a
  let y ← b
  pure (x + y)

def divAll (xs : List Nat) (d : Nat) : Except String (List Nat) :=
  match xs with
  | [] => .ok []
  | x :: rest => do
    if d = 0 then throw "zero"
    let r ← divAll rest d
    pure (x / d :: r)

-- deriving
inductive Color where
  | red | green | blue
  deriving DecidableEq, BEq, Inhabited

def Color.next : Color → Color
  | .red => .green
  | .green => .blue
  | .blue => .red

def sameColor (a b : Color) : Bool := a == b
def defColor : Color := default

structure Config where
  name : String
  size : Nat
  flag : Bool
  deriving BEq

def Config.bump (c : Config) : Config := { c with size := c.size + 1 }

-- nested patterns
inductive Expr where
  | num : Int → Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | neg : Expr → Expr

def Expr.eval : Expr → Int
  | .num n => n
  | .add a b => a.eval + b.eval
  | .mul a b => a.eval * b.eval
  | .neg a => - a.eval

def Expr.simp : Expr → Expr
  | .add (.num 0) e => e.simp
  | .add e (.num 0) => e.simp
  | .mul (.num 1) e => e.simp
  | .mul e (.num 1) => e.simp
  | .add a b => .add a.simp b.simp
  | .mul a b => .mul a.simp b.simp
  | .neg e => .neg e.simp
  | e => e

def pairs (xs : List Nat) : List (Nat × Nat) :=
  match xs with
  | a :: b :: rest => (a, b) :: pairs rest
  | _ => []

def big : Nat := 123456789012345678901234567890
def bigMul (n : Nat) : Nat := n * big

-- polymorphic with user type class
class Shape (α : Type) where
  area : α → Nat
  name : α → String

structure Rect where
  w : Nat
  h : Nat

structure Square where
  s : Nat

instance : Shape Rect := ⟨fun r => r.w * r.h, fun _ => "rect"⟩
instance : Shape Square := ⟨fun s => s.s * s.s, fun _ => "square"⟩

def totalArea {α} [Shape α] (xs : List α) : Nat :=
  xs.foldl (fun acc x => acc + Shape.area x) 0

def rectArea (r : Rect) : Nat := Shape.area r
def squares (xs : List Square) : Nat := totalArea xs

-- Option helpers from core
def firstOr (xs : List Nat) (d : Nat) : Nat := xs.head?.getD d
def lastOf (xs : List Nat) : Option Nat := xs.getLast?
def lengthOf (xs : List Nat) : Nat := xs.length
def rev (xs : List Nat) : List Nat := xs.reverse
def filterEven (xs : List Nat) : List Nat := xs.filter (fun x => x % 2 == 0)

extract_moonbit "tests/moon/advanced/advanced.mbt"
  addOpt divAll Color.next sameColor defColor Config.bump Expr.eval Expr.simp pairs bigMul
  rectArea squares firstOr lastOf lengthOf rev filterEven
