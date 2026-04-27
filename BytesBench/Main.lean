import Bytes

/-! Microbenchmarks comparing `Bytes.*` (C extern) against pure-Lean
reimplementations on a large `ByteArray`. Each row reports the wall-clock
mean per call and the C-vs-Lean speedup. -/

namespace BytesBench

/-! ## Pure-Lean reference implementations

Same bodies as the `@[extern]` decls in `Bytes.lean` but without the tag, so
calls compile to the Lean implementation rather than routing through C. -/

namespace Ref

@[inline] def loadU8 (data : ByteArray) (off : Nat) : UInt8 :=
  data.get! off

@[inline] def loadU64LE (data : ByteArray) (off : Nat) : UInt64 :=
  let b0 := (data.get! off).toUInt64
  let b1 := (data.get! (off + 1)).toUInt64
  let b2 := (data.get! (off + 2)).toUInt64
  let b3 := (data.get! (off + 3)).toUInt64
  let b4 := (data.get! (off + 4)).toUInt64
  let b5 := (data.get! (off + 5)).toUInt64
  let b6 := (data.get! (off + 6)).toUInt64
  let b7 := (data.get! (off + 7)).toUInt64
  b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24) |||
    (b4 <<< 32) ||| (b5 <<< 40) ||| (b6 <<< 48) ||| (b7 <<< 56)

@[inline] def storeU64LE (data : ByteArray) (off : Nat) (val : UInt64) : ByteArray :=
  if off + 8 ≤ data.size then
    let b0 := val.toUInt8
    let b1 := (val >>> 8).toUInt8
    let b2 := (val >>> 16).toUInt8
    let b3 := (val >>> 24).toUInt8
    let b4 := (val >>> 32).toUInt8
    let b5 := (val >>> 40).toUInt8
    let b6 := (val >>> 48).toUInt8
    let b7 := (val >>> 56).toUInt8
    (((((((data.set! off b0).set! (off + 1) b1).set! (off + 2) b2).set! (off + 3) b3
      ).set! (off + 4) b4).set! (off + 5) b5).set! (off + 6) b6).set! (off + 7) b7
  else data

@[inline] def copy (src : ByteArray) (srcOff : Nat) (dst : ByteArray)
    (dstOff : Nat) (len : Nat) : ByteArray :=
  if srcOff + len > src.size || dstOff + len > dst.size then dst
  else Nat.fold len (fun i _ d => d.set! (dstOff + i) (src.get! (srcOff + i))) dst

@[inline] def fill (data : ByteArray) (off : Nat) (len : Nat) (val : UInt8) : ByteArray :=
  if off + len > data.size then data
  else Nat.fold len (fun i _ d => d.set! (off + i) val) data

@[inline] def equal (a : ByteArray) (aOff : Nat) (b : ByteArray)
    (bOff : Nat) (len : Nat) : Bool :=
  if aOff + len > a.size || bOff + len > b.size then false
  else Nat.fold len (fun i _ acc => acc && (a.get! (aOff + i) == b.get! (bOff + i))) true

end Ref

/-! ## Timing harness -/

/-- Run `body` and return its wall-clock time in nanoseconds. -/
private def timeNs (body : IO Unit) : IO Nat := do
  let t0 ← IO.monoNanosNow
  body
  let t1 ← IO.monoNanosNow
  return t1 - t0

private structure Row where
  label    : String
  cNsPer   : Float    -- nanoseconds per call (C path)
  refNsPer : Float    -- nanoseconds per call (Lean path)

private def fmt (f : Float) (decimals : Nat := 2) : String :=
  let pow : Nat := Nat.fold decimals (fun _ _ acc => acc * 10) 1
  let scaled := (f * pow.toFloat).toUInt64.toNat
  let i := scaled / pow
  let frac := scaled % pow
  let pad := decimals - (toString frac).length
  let zeros := String.ofList (List.replicate pad '0')
  s!"{i}.{zeros}{frac}"

private def pad (s : String) (n : Nat) : String :=
  s ++ String.ofList (List.replicate (n - min s.length n) ' ')

private def fmtNs (ns : Float) : String :=
  if ns < 1_000 then s!"{fmt ns 1} ns"
  else if ns < 1_000_000 then s!"{fmt (ns / 1_000.0) 2} µs"
  else s!"{fmt (ns / 1_000_000.0) 2} ms"

private def Row.print (r : Row) : IO Unit := do
  let speedup := r.refNsPer / r.cNsPer
  IO.println s!"  {pad r.label 12} C: {pad (fmtNs r.cNsPer) 10}  Lean: {pad (fmtNs r.refNsPer) 10}  speedup: {fmt speedup 2}x"

/-! ## Benchmarks -/

/-- 1 MiB working set; large enough to dwarf cache effects, small enough to repeat. -/
private def bufSize : Nat := 1 <<< 20

/-- Per-byte loops repeat this many times to smooth jitter. -/
private def innerIters : Nat := 16

/-- Bulk-op benchmarks repeat this many calls. -/
private def bulkIters : Nat := 64

private def mkBuf : ByteArray :=
  ⟨Array.ofFn (n := bufSize) fun i => (i.val % 251).toUInt8⟩

private def benchLoadU8 (buf : ByteArray) : IO Row := do
  let totalOps := innerIters * bufSize
  let cNs ← timeNs do
    let mut acc : UInt8 := 0
    for _ in [:innerIters] do
      for off in [:bufSize] do acc := acc ^^^ Bytes.loadU8 buf off
    if acc == 0xFF then IO.println ""  -- sink
  let refNs ← timeNs do
    let mut acc : UInt8 := 0
    for _ in [:innerIters] do
      for off in [:bufSize] do acc := acc ^^^ Ref.loadU8 buf off
    if acc == 0xFF then IO.println ""
  return { label := "loadU8", cNsPer := cNs.toFloat / totalOps.toFloat,
           refNsPer := refNs.toFloat / totalOps.toFloat }

private def benchLoadU64LE (buf : ByteArray) : IO Row := do
  let n := bufSize - 8
  let totalOps := innerIters * n
  let cNs ← timeNs do
    let mut acc : UInt64 := 0
    for _ in [:innerIters] do
      for off in [:n] do acc := acc ^^^ Bytes.loadU64LE buf off
    if acc == 0xDEADBEEF then IO.println ""
  let refNs ← timeNs do
    let mut acc : UInt64 := 0
    for _ in [:innerIters] do
      for off in [:n] do acc := acc ^^^ Ref.loadU64LE buf off
    if acc == 0xDEADBEEF then IO.println ""
  return { label := "loadU64LE", cNsPer := cNs.toFloat / totalOps.toFloat,
           refNsPer := refNs.toFloat / totalOps.toFloat }

private def benchStoreU64LE (buf : ByteArray) : IO Row := do
  let n := (bufSize / 8) - 1
  let totalOps := innerIters * n
  let cNs ← timeNs do
    let mut b := buf
    for _ in [:innerIters] do
      for i in [:n] do b := Bytes.storeU64LE b (i * 8) 0xDEADBEEFCAFEBABE
    if b.size == 0 then IO.println ""
  let refNs ← timeNs do
    let mut b := buf
    for _ in [:innerIters] do
      for i in [:n] do b := Ref.storeU64LE b (i * 8) 0xDEADBEEFCAFEBABE
    if b.size == 0 then IO.println ""
  return { label := "storeU64LE", cNsPer := cNs.toFloat / totalOps.toFloat,
           refNsPer := refNs.toFloat / totalOps.toFloat }

private def benchCopy (src : ByteArray) (dst : ByteArray) : IO Row := do
  let cNs ← timeNs do
    let mut d := dst
    for _ in [:bulkIters] do d := Bytes.copy src 0 d 0 bufSize
    if d.size == 0 then IO.println ""
  let refNs ← timeNs do
    let mut d := dst
    for _ in [:bulkIters] do d := Ref.copy src 0 d 0 bufSize
    if d.size == 0 then IO.println ""
  return { label := s!"copy {bufSize >>> 20}MiB", cNsPer := cNs.toFloat / bulkIters.toFloat,
           refNsPer := refNs.toFloat / bulkIters.toFloat }

private def benchFill (buf : ByteArray) : IO Row := do
  let cNs ← timeNs do
    let mut b := buf
    for _ in [:bulkIters] do b := Bytes.fill b 0 bufSize 0xFF
    if b.size == 0 then IO.println ""
  let refNs ← timeNs do
    let mut b := buf
    for _ in [:bulkIters] do b := Ref.fill b 0 bufSize 0xFF
    if b.size == 0 then IO.println ""
  return { label := s!"fill {bufSize >>> 20}MiB", cNsPer := cNs.toFloat / bulkIters.toFloat,
           refNsPer := refNs.toFloat / bulkIters.toFloat }

private def benchEqual (buf : ByteArray) (buf2 : ByteArray) : IO Row := do
  -- Compare distinct buffers with identical contents. Passing the same
  -- Lean object twice would let clang's alias analysis fold the inlined
  -- `__builtin_memcmp(p, p, n)` to constant 0, eliding the work.
  let cNs ← timeNs do
    let mut acc := true
    for _ in [:bulkIters] do acc := acc && Bytes.equal buf 0 buf2 0 bufSize
    if !acc then IO.println ""
  let refNs ← timeNs do
    let mut acc := true
    for _ in [:bulkIters] do acc := acc && Ref.equal buf 0 buf2 0 bufSize
    if !acc then IO.println ""
  return { label := s!"equal {bufSize >>> 20}MiB", cNsPer := cNs.toFloat / bulkIters.toFloat,
           refNsPer := refNs.toFloat / bulkIters.toFloat }

def main : IO Unit := do
  IO.println s!"bytes-bench — C extern vs pure-Lean reference"
  IO.println s!"  buffer: {bufSize >>> 20} MiB   per-byte iters: {innerIters}   bulk iters: {bulkIters}"
  IO.println ""
  let buf := mkBuf
  let dst : ByteArray := ⟨Array.ofFn (n := bufSize) fun _ => (0 : UInt8)⟩
  -- Distinct ByteArray with identical contents — needed by `benchEqual`
  -- so the inlined `memcmp` actually runs end-to-end.
  let buf2 : ByteArray := Bytes.copy buf 0 dst 0 bufSize
  let _ := buf.size  -- warm
  let _ := dst.size
  let _ := buf2.size
  let rLoadU8     ← benchLoadU8 buf
  let rLoadU64LE  ← benchLoadU64LE buf
  let rStoreU64LE ← benchStoreU64LE buf
  let rCopy       ← benchCopy buf dst
  let rFill       ← benchFill buf
  let rEqual      ← benchEqual buf buf2
  IO.println "Results (mean per call):"
  rLoadU8.print
  rLoadU64LE.print
  rStoreU64LE.print
  rCopy.print
  rFill.print
  rEqual.print

end BytesBench

def main : IO Unit := BytesBench.main
