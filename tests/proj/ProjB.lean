import ProjA

/-! Middle module: uses the types, functions and instances of `ProjA`. -/

open ProjA

namespace ProjB

def totalArea {α : Type} [HasArea α] (xs : List α) : Nat :=
  (xs.map HasArea.area).foldl (· + ·) 0

def shapes : List Shape := [.circle 2, .rect 3 4, .unit]

def describe : Shape → Nat
  | .circle r => r
  | .rect w _ => w
  | .unit => 0

def grow (s : Shape) : Shape :=
  match s with
  | .circle r => .circle (r + 1)
  | .rect w h => .rect (w + 1) (h + 1)
  | .unit => .rect 1 1

def movePt (p : Pt Nat) : Pt Nat := { x := p.x + p.y, y := minus3 p.y }

def ptSum (p : Pt Nat) : Nat := p.x + p.y

def countDown (n : Nat) : Nat := Id.run do
  let mut k := n
  let mut c := 0
  while k > 0 do
    k := minus3 k
    c := c + 1
  return c

def safeDiv (a b : Nat) : Except String Nat :=
  if b == 0 then throw "div by zero" else pure (a / b)

def pushDoubles (xs : List Nat) : Array Nat := Id.run do
  let mut a := #[]
  for x in xs do
    a := a.push (x * 2)
  return a

end ProjB
