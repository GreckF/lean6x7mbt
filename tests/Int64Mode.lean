import Lean6x7mbt

-- Nat and Int become MoonBit `Int64` (wraps on overflow).
set_option lean6x7mbt.nat "int64"

def u8m (n : Nat) : UInt8 := n.toUInt8 + 1
def u32m (n : Nat) : UInt32 := n.toUInt32 + 1
def u64m (n : Nat) : UInt64 := n.toUInt64 + 1
def un (a : UInt8) (b : UInt32) (c : UInt64) : Nat := a.toNat + b.toNat + c.toNat
-- arrays without any `List` in the program (the `List` helpers must not be emitted)
def arrm (a : Array Nat) (i : Nat) : Nat :=
  a[i]! + a.getD i 3 + a.size + (a.set! i 9).foldl (· + ·) 0
def natOps (a b : Nat) : Nat := (a - b) + a / b + a % b + a ^ 2

extract_moonbit "tests/moon/int64mode/int64mode.mbt" u8m u32m u64m un arrm natOps
