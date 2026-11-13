// Extracted from Lean by lean6x7mbt (package `mbti_proj`).

pub fn projSucc(n : BigInt) -> BigInt {
  @extlib.succ(n)
}

pub fn projCounter(n : BigInt) -> BigInt {
  @extlib.Counter::get(@extlib.Counter::bump(@extlib.Counter::new(n), 2N))
}

pub fn projMapped(xs : @lean_core.List[BigInt]) -> @lean_core.List[BigInt] {
  @lean_core.list_map(fn(a : BigInt) { @extlib.add3(1N, 1N, a) }, xs)
}

pub let projDepth : BigInt = @extlib.Tree::depth(projTree)

pub let projTree : @extlib.Tree[BigInt] = @extlib.Tree::Node(@extlib.Tree::Leaf, 5N, @extlib.Tree::Leaf)
