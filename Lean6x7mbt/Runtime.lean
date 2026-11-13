/-!
Public stand-ins for core definitions whose bodies are private or opaque, so
they can be extracted. `Translate.lean` rewrites calls to the originals into
calls to these.
-/

/-- Public equivalent of the private `partial` loop behind `Lean.Loop.forIn`
(`while` / `repeat`). -/
partial def Lean6x7mbt.loopForIn {β : Type u} {m : Type u → Type v} [Monad m]
    (f : Unit → β → m (ForInStep β)) (b : β) : m β := do
  match ← f () b with
  | .done b => pure b
  | .yield b => Lean6x7mbt.loopForIn f b
