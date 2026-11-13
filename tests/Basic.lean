import Lean6x7mbt

def fact : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * fact n

inductive Tree (α : Type) where
  | leaf : Tree α
  | node : Tree α → α → Tree α → Tree α

def Tree.size {α} : Tree α → Nat
  | .leaf => 0
  | .node l _ r => l.size + 1 + r.size

def Tree.insert (t : Tree Nat) (k : Nat) : Tree Nat :=
  match t with
  | .leaf => .node .leaf k .leaf
  | .node l x r => if k < x then .node (l.insert k) x r else .node l x (r.insert k)

def Tree.toList {α} : Tree α → List α
  | .leaf => []
  | .node l x r => l.toList ++ [x] ++ r.toList

def mapOpt {α β} (f : α → β) : Option α → Option β
  | none => none
  | some a => some (f a)

structure P where
  x : Nat
  y : Bool

def P.swap (p : P) : P := ⟨p.x + 1, !p.y⟩

def sumList : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumList xs

def zip3 : List α → List β → List (α × β)
  | a::as, b::bs => (a,b) :: zip3 as bs
  | _, _ => []

def gcd' (a b : Nat) : Nat :=
  if h : b = 0 then a else gcd' b (a % b)
termination_by b
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

partial def collatz (n steps : Nat) : Nat :=
  if n ≤ 1 then steps
  else if n % 2 == 0 then collatz (n / 2) (steps + 1)
  else collatz (3 * n + 1) (steps + 1)

def isFive : Nat → Bool
  | 5 => true
  | _ => false

mutual
def isEven : Nat → Bool
  | 0 => true
  | n+1 => isOdd n
def isOdd : Nat → Bool
  | 0 => false
  | n+1 => isEven n
end

def compose {α β γ} (g : β → γ) (f : α → β) : α → γ := fun x => g (f x)

def twice (f : Nat → Nat) (x : Nat) : Nat := f (f x)

def addN (n : Nat) : Nat → Nat := fun x => x + n

def useMap (xs : List Nat) : List Nat := xs.map (· * 2)

def sumTo (n : Nat) : Nat :=
  let rec go (k acc : Nat) : Nat :=
    match k with
    | 0 => acc
    | k+1 => go k (acc + k + 1)
  go n 0

def sumAll {α} [Add α] [OfNat α 0] (xs : List α) : α :=
  xs.foldl (· + ·) 0

def intAbs (i : Int) : Int := if i < 0 then -i else i

def intMix (a b : Int) : Int := a * b - (a + b) / 2

structure Point where
  x : Int
  y : Int

instance : Add Point := ⟨fun a b => ⟨a.x + b.x, a.y + b.y⟩⟩

def addPoints (a b : Point) : Point := a + b

def classify (n : Nat) : String :=
  if n = 0 then "zero" else if n < 10 then "small" else "large"

def safeDiv (a b : Nat) : Except String Nat :=
  if b = 0 then .error "div by zero" else .ok (a / b)

def sumSafe (xs : List Nat) : Nat := xs.foldl (fun acc x => acc + x) 0

def fin3 (i : Fin 3) : Nat := i.val

def exampleSigma (n : Nat) : { m : Nat // m > 0 } := ⟨n + 1, Nat.succ_pos n⟩

def useSubtype (n : Nat) : Nat := (exampleSigma n).val

extract_moonbit "tests/moon/basic/basic.mbt"
  fact Tree.size Tree.insert Tree.toList mapOpt P.swap sumList zip3 gcd' collatz isFive isEven isOdd
  compose twice addN useMap sumTo sumAll intAbs intMix addPoints classify safeDiv sumSafe fin3
  useSubtype
