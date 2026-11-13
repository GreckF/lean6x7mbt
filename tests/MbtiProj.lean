import Lean6x7mbt

/-!
`import_mbti` with `extract_moonbit_project`: the generated package `mbti_proj` imports the external package
`lean6x7mbt/tests/extlib` (declared by the `package` line of its `.mbti`) with the alias used by the templates.
The output goes into the `tests/moon` module (its `moon.mod` is kept), next to `extlib`.
-/

#guard_msgs (drop warning, drop info) in
import_mbti "tests/moon/extlib/pkg.generated.mbti" as Ext

def projSucc (n : Int) : Int := Ext.succ n
def projCounter (n : Int) : Int := ((Ext.Counter.new n).bump 2).get
def projMapped (xs : List Int) : List Int := xs.map (Ext.add3 1 1)
def projTree : Ext.Tree Int := .Node .Leaf 5 .Leaf
def projDepth : Int := projTree.depth

set_option lean6x7mbt.main_package "mbti_proj" in
extract_moonbit_project "tests/moon" projSucc projCounter projMapped projDepth
