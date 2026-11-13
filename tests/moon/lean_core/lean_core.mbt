// Extracted from Lean by lean6x7mbt (package `lean_core`).

pub(all) enum List[A] {
  Nil
  Cons(A, List[A])
}

pub fn[A, B] list_map(f : (A) -> B, x : List[A]) -> List[B] {
  match x {
    List::Nil => List::Nil
    List::Cons(head, tail) => List::Cons(f(head), list_map(f, tail))
  }
}
