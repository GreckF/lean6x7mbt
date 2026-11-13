import Lean6x7mbt

-- Nat and Int become MoonBit `Int` (wraps on overflow) with this option.
set_option lean6x7mbt.nat "int"

def fact : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * fact n

def sub3 (n : Nat) : Nat := n - 3

def collatz (n steps : Nat) : Nat :=
  if n ≤ 1 then steps
  else if n % 2 == 0 then collatz (n / 2) (steps + 1)
  else collatz (3 * n + 1) (steps + 1)
decreasing_by all_goals sorry

def ediv (a b : Int) : Int := a / b
def emod (a b : Int) : Int := a % b

def powTwo (n : Nat) : Nat := 2 ^ n

extract_moonbit "tests/moon/intmode/intmode.mbt" fact sub3 collatz ediv emod powTwo
