import Lean6x7mbt

def whileLoop (n : Nat) : Nat := Id.run do
  let mut i := 0
  let mut s := 0
  while i < n do
    s := s + i
    i := i + 1
  return s

-- sum of odd numbers below n, stopping once the running sum exceeds 20
def whileBreak (n : Nat) : Nat := Id.run do
  let mut i := 0
  let mut s := 0
  while i < n do
    i := i + 1
    if i % 2 == 0 then continue
    s := s + i
    if s > 20 then break
  return s

-- first i with i * i > n, returned from inside the loop
def whileReturn (n : Nat) : Nat := Id.run do
  let mut i := 0
  while i < 1000 do
    if i * i > n then return i
    i := i + 1
  return 9999

-- while containing a for
def whileFor (n : Nat) : Nat := Id.run do
  let mut i := 0
  let mut s := 0
  while i < n do
    for j in [0:i] do
      s := s + j
    i := i + 1
  return s

-- while containing a while
def whileWhile (n : Nat) : Nat := Id.run do
  let mut i := 0
  let mut c := 0
  while i < n do
    let mut j := 0
    while j < i do
      c := c + 1
      j := j + 1
    i := i + 1
  return c

def whileExcept (n : Nat) : Except String Nat := do
  let mut i := 0
  let mut s := 0
  while i < 10 do
    if i == n then throw s!"hit {i}"
    s := s + i
    i := i + 1
  return s

def whileState (n : Nat) : StateM Nat Unit := do
  let mut i := 0
  while i < n do
    modify (· + i)
    i := i + 1

def runWhileState (n : Nat) : Nat := (whileState n |>.run 100).2

def whileNever (n : Nat) : Nat := Id.run do
  let mut s := 7
  while n < 0 do
    s := s + 1
  return s

/-! Deep loops in `Except`/`StateM`: the recursive call of the loop must be a
tail call (`bind` is inlined, the state is a parameter of the specialized
copy).  These overflowed the stack at about 10000 iterations. -/

def deepExcept (n : Nat) : Except String Nat := do
  let mut i := 0
  while i < n do
    if i == n + 1 then throw "unreachable"
    i := i + 1
  return i

def deepFor (n : Nat) : Except String Nat := do
  let mut s := 0
  for i in [0:n] do
    if i == n + 1 then throw "unreachable"
    s := s + i
  return s

def deepList (n : Nat) : Except String Nat := do
  let mut s := 0
  for x in List.range n do
    if x == n then throw "unreachable"
    s := s + x
  return s

def deepState (n : Nat) : Nat := ((do
  let mut i := 0
  while i < n do
    modify (· + 2)
    i := i + 1 : StateM Nat Unit).run 1).2

def deepStateExcept (n : Nat) : Except String (Nat × Nat) := ((do
  let mut i := 0
  while i < n do
    let s ← get
    if s > 3 * n then throw "unreachable"
    set (s + 3)
    i := i + 1
  return i : StateT Nat (Except String) Nat).run 0)

extract_moonbit "tests/moon/while/while.mbt"
  whileLoop whileBreak whileReturn whileFor whileWhile whileExcept runWhileState whileNever
  deepExcept deepFor deepList deepState deepStateExcept
