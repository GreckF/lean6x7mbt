import Lean6x7mbt

/-! Differential tests in `int` mode (Nat/Int are MoonBit `Int`); values stay small. -/

set_option lean6x7mbt.nat "int"

def sumSq (n : Nat) : Nat := (List.range (n + 1)).foldl (fun acc k => acc + k * k) 0
def mix (a b : Int) : Int := a * b - (a + b) / 2 + a % 3
def natSub (a b : Nat) : Nat := a - b + a / (b + 1)

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

def clamp (lo hi x : Int) : Int := if x < lo then lo else if x > hi then hi else x

extract_moonbit "tests/moon/diffint/diffint.mbt" sumSq mix natSub fib clamp
with_tests [
  sumSq 10, mix 7 (-3), mix (-9) 4, natSub 3 5, natSub 9 2, fib 15,
  clamp 0 10 (-4), clamp 0 10 99, clamp 0 10 5, fib 10 == 55
]
