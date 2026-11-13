import Lean6x7mbt

def loopSum (n : Nat) : Nat := Id.run do
  let mut s := 0
  for i in [0:n] do
    s := s + i
  return s

def sumListLoop (xs : List Nat) : Nat := Id.run do
  let mut s := 0
  for x in xs do
    s := s + x
  return s

def mapOpt (xs : List Nat) : Option (List Nat) :=
  xs.mapM (fun x => if x > 0 then some (x - 1) else none)

def counter (n : Nat) : StateM Nat Unit := do
  for _ in [0:n] do
    modify (· + 1)

def runCounter (n : Nat) : Nat := (counter n |>.run 0).2

def checkAll (xs : List Nat) : Except String Nat := do
  let mut total := 0
  for x in xs do
    if x == 0 then throw "zero found"
    total := total + x
  return total

def evensBelow (n : Nat) : Nat := Id.run do
  let mut c := 0
  for i in [0:n] do
    if i % 2 == 0 then
      c := c + 1
  return c

extract_moonbit "tests/moon/monads/monads.mbt"
  loopSum sumListLoop mapOpt runCounter checkAll evensBelow
