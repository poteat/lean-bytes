import BytesTest.Basic
import BytesTest.Random

/-! Top-level test driver. Runs the basic (hand-derived) test suite and the
randomized FFI-equivalence suite in sequence; either exits the process
non-zero on its own failures, so reaching the end of `main` means both
suites passed. -/

def main : IO Unit := do
  BytesTest.Basic.main
  IO.println ""
  BytesTest.Random.main
