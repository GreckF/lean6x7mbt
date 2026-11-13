import Lean.ToExpr

/-! Lower module of the multi-package test (`tests/proj/ProjMain.lean`). -/

open Lean (ToExpr)

namespace ProjA

inductive Shape where
  | circle (r : Nat)
  | rect (w h : Nat)
  | unit
  deriving ToExpr, BEq

structure Pt (α : Type) where
  x : α
  y : Nat
  deriving ToExpr, BEq

class HasArea (α : Type) where
  area : α → Nat

def Shape.area : Shape → Nat
  | .circle r => 3 * r * r
  | .rect w h => w * h
  | .unit => 1

instance : HasArea Shape := ⟨Shape.area⟩

def minus3 (a : Nat) : Nat := a - 3

def sumTo (n : Nat) : Nat := Id.run do
  let mut s := 0
  for i in [0:n] do
    s := s + i
  return s

def arrSum (a : Array Nat) : Nat := a.foldl (· + ·) 0

def mkPt {α : Type} (a : α) (n : Nat) : Pt α := { x := a, y := n }

end ProjA
