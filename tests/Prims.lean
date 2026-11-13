import Lean6x7mbt

def arrSum (a : Array Nat) : Nat := a.foldl (· + ·) 0
def arrPush (a : Array Nat) (x : Nat) : Array Nat := a.push x
def arrGet (a : Array Nat) (i : Nat) : Nat := a[i]!
def arrGetD (a : Array Nat) (i : Nat) : Nat := a.getD i 0
def arrSize (a : Array Nat) : Nat := a.size
def arrMap (a : Array Nat) : Array Nat := a.map (· + 1)
def mkArr : Array Nat := #[1, 2, 3]
def arrSet (a : Array Nat) (i x : Nat) : Array Nat := a.set! i x
def str1 (s : String) : String := s ++ "!"
def strLen (s : String) : Nat := s.length
def chr (n : Nat) : Char := Char.ofNat n
def u64 (a b : UInt64) : UInt64 := a * b + 1
def u8 (a : UInt8) : UInt8 := a + 200
def flt (x : Float) : Float := x * 2.5
def nToStr (n : Nat) : String := toString n

extract_moonbit "tests/moon/prims/prims.mbt"
  arrSum arrPush arrGet arrGetD arrSize arrMap mkArr arrSet str1 strLen chr u64 u8 flt nToStr
