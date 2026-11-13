#!/usr/bin/env bash
# Build the extractor, extract every tests/*.lean into tests/moon/<pkg>/ and run `moon test`.
# Usage: tests/run.sh [moon target]   (default: wasm-gc)
set -uo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
cd "$ROOT"
lake build || exit 1
fail=0
for f in tests/*.lean; do
  echo "== extracting $f"
  out=$(lake env lean "$f" 2>&1)
  st=$?
  echo "$out" | grep -v "linter\|unused\|^$\|sorry" || true
  # an extraction error (or a failed `#guard_msgs`) must fail the run
  if [ $st -ne 0 ]; then
    echo "!! $f failed"
    fail=1
  fi
done
cd tests/moon
echo "== moon test"
moon test --target "${1:-wasm-gc}" 2>&1 | grep -v "^Warning\|^ *[╭│╰─]\|^ *[0-9]* │\|^$"
[ "${PIPESTATUS[0]}" -eq 0 ] || fail=1
cd "$ROOT"
# multi-package extraction: tests/proj/*.lean -> tests/moon_proj/ (one MoonBit package per Lean module)
echo "== extracting tests/proj/ProjMain.lean (project mode)"
if lake build ProjTest 2>&1 | grep -v "linter\|unused\|^$\|sorry" ; [ "${PIPESTATUS[0]}" -ne 0 ]; then
  echo "!! lake build ProjTest failed"
  fail=1
fi
out=$(lake env lean tests/proj/ProjMain.lean 2>&1)
st=$?
echo "$out" | grep -v "linter\|unused\|^$\|sorry" || true
if [ $st -ne 0 ]; then
  echo "!! tests/proj/ProjMain.lean failed"
  fail=1
fi
cd tests/moon_proj
echo "== moon test (tests/moon_proj)"
moon test --target "${1:-wasm-gc}" 2>&1 | grep -v "^Warning\|^ *[╭│╰─]\|^ *[0-9]* │\|^$"
[ "${PIPESTATUS[0]}" -eq 0 ] || fail=1
exit $fail
