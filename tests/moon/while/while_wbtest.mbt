// Runtime tests for `while` loops (Lean.Loop.forIn -> specialized lean6x7mbt_loopForIn_specN).
// Expected values come from Lean's #eval.

test "basic while in Id" {
  assert_eq(whileLoop(0N), 0N)
  assert_eq(whileLoop(1N), 0N)
  assert_eq(whileLoop(5N), 10N)
  assert_eq(whileLoop(10N), 45N)
}

test "while with break/continue" {
  assert_eq(whileBreak(0N), 0N)
  assert_eq(whileBreak(3N), 4N)
  assert_eq(whileBreak(6N), 9N)
  assert_eq(whileBreak(100N), 25N)
}

test "while with early return" {
  assert_eq(whileReturn(0N), 1N)
  assert_eq(whileReturn(10N), 4N)
  assert_eq(whileReturn(99N), 10N)
  assert_eq(whileReturn(2000000N), 9999N)
}

test "while containing for" {
  assert_eq(whileFor(0N), 0N)
  assert_eq(whileFor(1N), 0N)
  assert_eq(whileFor(5N), 10N)
  assert_eq(whileFor(6N), 20N)
}

test "while containing while" {
  assert_eq(whileWhile(0N), 0N)
  assert_eq(whileWhile(1N), 0N)
  assert_eq(whileWhile(5N), 10N)
  assert_eq(whileWhile(6N), 15N)
}

test "while in Except" {
  assert_eq(whileExcept(0N), Err("hit 0"))
  assert_eq(whileExcept(3N), Err("hit 3"))
  assert_eq(whileExcept(10N), Ok(45N))
  assert_eq(whileExcept(20N), Ok(45N))
}

test "while in StateM" {
  assert_eq(runWhileState(0N), 100N)
  assert_eq(runWhileState(1N), 100N)
  assert_eq(runWhileState(5N), 110N)
}

test "while that never runs" {
  assert_eq(whileNever(0N), 7N)
  assert_eq(whileNever(4N), 7N)
}

test "deep loops do not overflow the stack" {
  assert_eq(deepExcept(200000N), Ok(200000N))
  assert_eq(deepFor(200000N), Ok(19999900000N))
  assert_eq(deepList(200000N), Ok(19999900000N))
  assert_eq(deepState(200000N), 400001N)
  assert_eq(deepStateExcept(200000N), Ok((200000N, 600000N)))
}
