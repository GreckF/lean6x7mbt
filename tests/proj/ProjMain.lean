import Lean6x7mbt
import ProjB

/-! Multi-package extraction: `ProjA`, `ProjB` and this module become separate MoonBit
packages (`proj_a`, `proj_b`, `proj_main`), the core library goes to `lean_core`. -/

open ProjA ProjB

def chain (a b c : Nat) : Except String Nat := do
  let x ← safeDiv a b
  let y ← safeDiv x c
  return x + y

def mainLoop (n : Nat) : Nat := Id.run do
  let mut s := 0
  for i in [0:n] do
    s := s + countDown i
  return s + (sumTo n)

def areaOfAll : Nat := totalArea shapes + totalArea [Shape.circle 1]

set_option lean6x7mbt.module "lean6x7mbt/tests_proj" in
set_option lean6x7mbt.main_package "proj_main" in
extract_moonbit_project "tests/moon_proj" chain mainLoop areaOfAll grow movePt
  with_tests [
    (chain 100 5 2).toOption,
    (chain 1 0 2).toOption,
    mainLoop 12,
    areaOfAll,
    grow (Shape.circle 4),
    grow Shape.unit,
    shapes.map describe,
    movePt (mkPt 5 10),
    ptSum (movePt (mkPt 5 10)),
    pushDoubles [1, 2, 3],
    arrSum #[1, 2, 3, 4],
    minus3 2,
    minus3 10,
    (safeDiv 7 0).toOption,
    totalArea shapes,
    sumTo 10,
    countDown 20
  ]
