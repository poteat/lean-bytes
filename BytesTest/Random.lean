import Bytes
import BytesTest.Spec

/-! Randomized FFI-equivalence tests. For every public `Bytes.*` primitive,
generate a stream of random inputs from a seeded PRNG and compare the C
extern result against `BytesTest.Spec.*` (the same body without `@[extern]`).
Catches divergences the hand-derived `Basic` test cannot hit (boundary
offsets, specific bit patterns, OOB edge cases). -/

namespace BytesTest.Random

/-! ## PRNG (splitmix64) -/

abbrev Rng := IO.Ref UInt64

private def mkRng (seed : UInt64) : IO Rng := IO.mkRef seed

private def Rng.nextU64 (r : Rng) : IO UInt64 := do
  -- splitmix64 — small state, decent statistical quality, deterministic.
  let z₀ := (← r.get) + 0x9E3779B97F4A7C15
  r.set z₀
  let z₁ := (z₀ ^^^ (z₀ >>> 30)) * 0xBF58476D1CE4E5B9
  let z₂ := (z₁ ^^^ (z₁ >>> 27)) * 0x94D049BB133111EB
  return z₂ ^^^ (z₂ >>> 31)

private def Rng.nextU8  (r : Rng) : IO UInt8  := do return (← r.nextU64).toUInt8
private def Rng.nextU16 (r : Rng) : IO UInt16 := do return (← r.nextU64).toUInt16
private def Rng.nextU32 (r : Rng) : IO UInt32 := do return (← r.nextU64).toUInt32

private def Rng.nextNat (r : Rng) (bound : Nat) : IO Nat := do
  return (← r.nextU64).toNat % bound

/-! ## Generators -/

private def randomByteArray (r : Rng) (size : Nat) : IO ByteArray := do
  let mut arr := ByteArray.empty
  for _ in [:size] do arr := arr.push (← r.nextU8)
  return arr

/-! ## Test driver -/

private structure Stats where
  passed : Nat := 0
  failed : Nat := 0

private def report (s : IO.Ref Stats) (label : String) (ok : Bool)
    (detail : Unit → String) : IO Unit := do
  if ok then s.modify fun st => { st with passed := st.passed + 1 }
  else
    s.modify fun st => { st with failed := st.failed + 1 }
    IO.eprintln s!"  FAIL {label}: {detail ()}"

/- Iteration count per primitive. Small enough to run under a second; large
   enough that boundary offsets get hit many times by uniform sampling. -/
private def iters : Nat := 1000

/- Buffer sizes we draw inputs from. Small/odd/even/aligned mix. -/
private def sizes : List Nat := [1, 7, 16, 17, 32, 64, 65, 128]

def main : IO Unit := do
  let r ← mkRng 0xDEADBEEFCAFEF00D
  let s ← IO.mkRef ({} : Stats)
  IO.println "bytes-random — randomized FFI equivalence (seed 0xDEADBEEFCAFEF00D)"

  /- Loads: gen buffer, gen offset (may be OOB), compare. -/
  for _ in [:iters] do
    let size := sizes[(← r.nextNat sizes.length)]!
    let buf ← randomByteArray r size
    let off ← r.nextNat (size + 8)
    let g := Bytes.loadU8 buf off
    let e := Spec.loadU8 buf off
    report s "loadU8" (g == e) fun _ => s!"size={size} off={off} got={g} exp={e}"
  for _ in [:iters] do
    let size := sizes[(← r.nextNat sizes.length)]!
    let buf ← randomByteArray r size
    let off ← r.nextNat (size + 8)
    let g := Bytes.loadU16LE buf off
    let e := Spec.loadU16LE buf off
    report s "loadU16LE" (g == e) fun _ => s!"size={size} off={off} got={g} exp={e}"
  for _ in [:iters] do
    let size := sizes[(← r.nextNat sizes.length)]!
    let buf ← randomByteArray r size
    let off ← r.nextNat (size + 8)
    let g := Bytes.loadU16BE buf off
    let e := Spec.loadU16BE buf off
    report s "loadU16BE" (g == e) fun _ => s!"size={size} off={off} got={g} exp={e}"
  for _ in [:iters] do
    let size := sizes[(← r.nextNat sizes.length)]!
    let buf ← randomByteArray r size
    let off ← r.nextNat (size + 8)
    let g := Bytes.loadU32LE buf off
    let e := Spec.loadU32LE buf off
    report s "loadU32LE" (g == e) fun _ => s!"size={size} off={off} got={g} exp={e}"
  for _ in [:iters] do
    let size := sizes[(← r.nextNat sizes.length)]!
    let buf ← randomByteArray r size
    let off ← r.nextNat (size + 8)
    let g := Bytes.loadU32BE buf off
    let e := Spec.loadU32BE buf off
    report s "loadU32BE" (g == e) fun _ => s!"size={size} off={off} got={g} exp={e}"
  for _ in [:iters] do
    let size := sizes[(← r.nextNat sizes.length)]!
    let buf ← randomByteArray r size
    let off ← r.nextNat (size + 8)
    let g := Bytes.loadU64LE buf off
    let e := Spec.loadU64LE buf off
    report s "loadU64LE" (g == e) fun _ => s!"size={size} off={off} got={g} exp={e}"
  for _ in [:iters] do
    let size := sizes[(← r.nextNat sizes.length)]!
    let buf ← randomByteArray r size
    let off ← r.nextNat (size + 8)
    let g := Bytes.loadU64BE buf off
    let e := Spec.loadU64BE buf off
    report s "loadU64BE" (g == e) fun _ => s!"size={size} off={off} got={g} exp={e}"

  /- Stores: gen buffer, gen off+val, compare resulting arrays. -/
  for _ in [:iters] do
    let size := sizes[(← r.nextNat sizes.length)]!
    let buf ← randomByteArray r size
    let off ← r.nextNat (size + 8)
    let val ← r.nextU8
    let g := Bytes.storeU8 buf off val
    let e := Spec.storeU8 buf off val
    report s "storeU8" (g == e) fun _ => s!"size={size} off={off} val={val}"
  for _ in [:iters] do
    let size := sizes[(← r.nextNat sizes.length)]!
    let buf ← randomByteArray r size
    let off ← r.nextNat (size + 8)
    let val ← r.nextU16
    let g := Bytes.storeU16LE buf off val
    let e := Spec.storeU16LE buf off val
    report s "storeU16LE" (g == e) fun _ => s!"size={size} off={off} val={val}"
  for _ in [:iters] do
    let size := sizes[(← r.nextNat sizes.length)]!
    let buf ← randomByteArray r size
    let off ← r.nextNat (size + 8)
    let val ← r.nextU16
    let g := Bytes.storeU16BE buf off val
    let e := Spec.storeU16BE buf off val
    report s "storeU16BE" (g == e) fun _ => s!"size={size} off={off} val={val}"
  for _ in [:iters] do
    let size := sizes[(← r.nextNat sizes.length)]!
    let buf ← randomByteArray r size
    let off ← r.nextNat (size + 8)
    let val ← r.nextU32
    let g := Bytes.storeU32LE buf off val
    let e := Spec.storeU32LE buf off val
    report s "storeU32LE" (g == e) fun _ => s!"size={size} off={off} val={val}"
  for _ in [:iters] do
    let size := sizes[(← r.nextNat sizes.length)]!
    let buf ← randomByteArray r size
    let off ← r.nextNat (size + 8)
    let val ← r.nextU32
    let g := Bytes.storeU32BE buf off val
    let e := Spec.storeU32BE buf off val
    report s "storeU32BE" (g == e) fun _ => s!"size={size} off={off} val={val}"
  for _ in [:iters] do
    let size := sizes[(← r.nextNat sizes.length)]!
    let buf ← randomByteArray r size
    let off ← r.nextNat (size + 8)
    let val ← r.nextU64
    let g := Bytes.storeU64LE buf off val
    let e := Spec.storeU64LE buf off val
    report s "storeU64LE" (g == e) fun _ => s!"size={size} off={off} val={val}"
  for _ in [:iters] do
    let size := sizes[(← r.nextNat sizes.length)]!
    let buf ← randomByteArray r size
    let off ← r.nextNat (size + 8)
    let val ← r.nextU64
    let g := Bytes.storeU64BE buf off val
    let e := Spec.storeU64BE buf off val
    report s "storeU64BE" (g == e) fun _ => s!"size={size} off={off} val={val}"

  /- Bulk: copy/fill/equal/compare. Both ranges may be OOB. -/
  for _ in [:iters] do
    let srcSize := sizes[(← r.nextNat sizes.length)]!
    let dstSize := sizes[(← r.nextNat sizes.length)]!
    let src ← randomByteArray r srcSize
    let dst ← randomByteArray r dstSize
    let srcOff ← r.nextNat (srcSize + 4)
    let dstOff ← r.nextNat (dstSize + 4)
    let len ← r.nextNat (max srcSize dstSize + 4)
    let g := Bytes.copy src srcOff dst dstOff len
    let e := Spec.copy src srcOff dst dstOff len
    report s "copy" (g == e) fun _ =>
      s!"srcSize={srcSize} dstSize={dstSize} srcOff={srcOff} dstOff={dstOff} len={len}"
  for _ in [:iters] do
    let size := sizes[(← r.nextNat sizes.length)]!
    let buf ← randomByteArray r size
    let off ← r.nextNat (size + 4)
    let len ← r.nextNat (size + 4)
    let val ← r.nextU8
    let g := Bytes.fill buf off len val
    let e := Spec.fill buf off len val
    report s "fill" (g == e) fun _ => s!"size={size} off={off} len={len} val={val}"
  for _ in [:iters] do
    let aSize := sizes[(← r.nextNat sizes.length)]!
    let bSize := sizes[(← r.nextNat sizes.length)]!
    let a ← randomByteArray r aSize
    let b ← randomByteArray r bSize
    let aOff ← r.nextNat (aSize + 4)
    let bOff ← r.nextNat (bSize + 4)
    let len ← r.nextNat (max aSize bSize + 4)
    let g := Bytes.equal a aOff b bOff len
    let e := Spec.equal a aOff b bOff len
    report s "equal" (g == e) fun _ =>
      s!"aSize={aSize} bSize={bSize} aOff={aOff} bOff={bOff} len={len}"
  for _ in [:iters] do
    let aSize := sizes[(← r.nextNat sizes.length)]!
    let bSize := sizes[(← r.nextNat sizes.length)]!
    let a ← randomByteArray r aSize
    let b ← randomByteArray r bSize
    let aOff ← r.nextNat (aSize + 4)
    let bOff ← r.nextNat (bSize + 4)
    let len ← r.nextNat (max aSize bSize + 4)
    let g := Bytes.compare a aOff b bOff len
    let e := Spec.compare a aOff b bOff len
    report s "compare" (g == e) fun _ =>
      s!"aSize={aSize} bSize={bSize} aOff={aOff} bOff={bOff} len={len}"

  let final ← s.get
  IO.println s!"\n  passed: {final.passed}    failed: {final.failed}"
  if final.failed > 0 then IO.Process.exit 1

end BytesTest.Random
