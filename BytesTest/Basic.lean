import Bytes

/-! Basic test for `Bytes.*` extern primitives. Each call invokes the C
function; the expected value is hand-derived against a fixed test buffer.
Any mismatch indicates a Lean-↔-C semantic divergence. -/

namespace BytesTest.Basic

private structure Stats where
  passed : Nat := 0
  failed : Nat := 0

private def checkBy (stats : IO.Ref Stats) (label : String) (got expected : String)
    (ok : Bool) : IO Unit := do
  if ok then
    stats.modify fun s => { s with passed := s.passed + 1 }
  else
    stats.modify fun s => { s with failed := s.failed + 1 }
    IO.eprintln s!"  FAIL {label}: got {got}, expected {expected}"

private def check {α : Type} [BEq α] [ToString α] (stats : IO.Ref Stats)
    (label : String) (got expected : α) : IO Unit :=
  checkBy stats label (toString got) (toString expected) (got == expected)

private def checkOrd (stats : IO.Ref Stats) (label : String)
    (got expected : Ordering) : IO Unit :=
  let toStr : Ordering → String
    | .lt => "lt" | .eq => "eq" | .gt => "gt"
  checkBy stats label (toStr got) (toStr expected) (got == expected)

def main : IO Unit := do
  let s ← IO.mkRef ({} : Stats)
  -- Direct calls keep `check` polymorphic; let-binding `check stats` would
  -- monomorphise α to whatever the first call uses.
  let check {α : Type} [BEq α] [ToString α] := @check α _ _ s
  let checkOrd := checkOrd s
  IO.println "bytes-basic — Lean spec vs C extern coverage"

  -- Test buffer: bytes 0x01, 0x02, 0x03, ..., 0x10
  let buf : ByteArray := ⟨Array.ofFn (n := 16) fun i => (i.val + 1).toUInt8⟩
  let zero : ByteArray := ⟨Array.ofFn (n := 16) fun _ => (0 : UInt8)⟩

  /- Loads -/
  check "loadU8 @0"        (Bytes.loadU8 buf 0)   (0x01 : UInt8)
  check "loadU8 @15"       (Bytes.loadU8 buf 15)  (0x10 : UInt8)
  check "loadU8 OOB"       (Bytes.loadU8 buf 100) (0x00 : UInt8)

  check "loadU16LE @0"     (Bytes.loadU16LE buf 0)  (0x0201 : UInt16)
  check "loadU16BE @0"     (Bytes.loadU16BE buf 0)  (0x0102 : UInt16)
  check "loadU16LE @14"    (Bytes.loadU16LE buf 14) (0x100F : UInt16)
  check "loadU16LE OOB"    (Bytes.loadU16LE buf 15) (0x0010 : UInt16)

  check "loadU32LE @0"     (Bytes.loadU32LE buf 0)  (0x04030201 : UInt32)
  check "loadU32BE @0"     (Bytes.loadU32BE buf 0)  (0x01020304 : UInt32)
  check "loadU32LE @12"    (Bytes.loadU32LE buf 12) (0x100F0E0D : UInt32)
  check "loadU32LE OOB"    (Bytes.loadU32LE buf 14) (0x00100F : UInt32)

  check "loadU64LE @0"     (Bytes.loadU64LE buf 0)  (0x0807060504030201 : UInt64)
  check "loadU64BE @0"     (Bytes.loadU64BE buf 0)  (0x0102030405060708 : UInt64)
  check "loadU64LE @8"     (Bytes.loadU64LE buf 8)  (0x100F0E0D0C0B0A09 : UInt64)
  check "loadU64LE OOB"    (Bytes.loadU64LE buf 12) (0x00000000100F0E0D : UInt64)

  /- Stores: write into a zeroed buffer, inspect bytes -/
  let b1 := Bytes.storeU8 zero 5 0xAB
  check "storeU8 @5"       (b1.get! 5) (0xAB : UInt8)
  check "storeU8 @4 (0)"   (b1.get! 4) (0x00 : UInt8)
  check "storeU8 @6 (0)"   (b1.get! 6) (0x00 : UInt8)

  let b2 := Bytes.storeU16LE zero 0 0xCAFE
  check "storeU16LE byte0" (b2.get! 0) (0xFE : UInt8)
  check "storeU16LE byte1" (b2.get! 1) (0xCA : UInt8)

  let b3 := Bytes.storeU16BE zero 0 0xCAFE
  check "storeU16BE byte0" (b3.get! 0) (0xCA : UInt8)
  check "storeU16BE byte1" (b3.get! 1) (0xFE : UInt8)

  let b4 := Bytes.storeU32LE zero 0 0xDEADBEEF
  check "storeU32LE byte0" (b4.get! 0) (0xEF : UInt8)
  check "storeU32LE byte1" (b4.get! 1) (0xBE : UInt8)
  check "storeU32LE byte2" (b4.get! 2) (0xAD : UInt8)
  check "storeU32LE byte3" (b4.get! 3) (0xDE : UInt8)

  let b5 := Bytes.storeU32BE zero 0 0xDEADBEEF
  check "storeU32BE byte0" (b5.get! 0) (0xDE : UInt8)
  check "storeU32BE byte3" (b5.get! 3) (0xEF : UInt8)

  let b6 := Bytes.storeU64LE zero 0 0x123456789ABCDEF0
  check "storeU64LE byte0" (b6.get! 0) (0xF0 : UInt8)
  check "storeU64LE byte7" (b6.get! 7) (0x12 : UInt8)

  let b7 := Bytes.storeU64BE zero 0 0x123456789ABCDEF0
  check "storeU64BE byte0" (b7.get! 0) (0x12 : UInt8)
  check "storeU64BE byte7" (b7.get! 7) (0xF0 : UInt8)

  /- Round-trips: store then load should return the original value -/
  check "store/load U16LE rt" (Bytes.loadU16LE b2 0) (0xCAFE : UInt16)
  check "store/load U16BE rt" (Bytes.loadU16BE b3 0) (0xCAFE : UInt16)
  check "store/load U32LE rt" (Bytes.loadU32LE b4 0) (0xDEADBEEF : UInt32)
  check "store/load U32BE rt" (Bytes.loadU32BE b5 0) (0xDEADBEEF : UInt32)
  check "store/load U64LE rt" (Bytes.loadU64LE b6 0) (0x123456789ABCDEF0 : UInt64)
  check "store/load U64BE rt" (Bytes.loadU64BE b7 0) (0x123456789ABCDEF0 : UInt64)

  /- OOB stores are no-ops -/
  let b8 := Bytes.storeU64LE zero 12 0x123456789ABCDEF0
  check "storeU64LE OOB @0" (b8.get! 0)  (0x00 : UInt8)
  check "storeU64LE OOB @12" (b8.get! 12) (0x00 : UInt8)
  check "storeU64LE OOB @15" (b8.get! 15) (0x00 : UInt8)

  /- Bulk: copy 8 bytes from buf[0..8] into a fresh dst[4..12] -/
  let dst : ByteArray := ⟨Array.ofFn (n := 16) fun _ => (0 : UInt8)⟩
  let copied := Bytes.copy buf 0 dst 4 8
  check "copy untouched @0"  (copied.get! 0)  (0x00 : UInt8)
  check "copy first @4"      (copied.get! 4)  (0x01 : UInt8)
  check "copy last @11"      (copied.get! 11) (0x08 : UInt8)
  check "copy untouched @12" (copied.get! 12) (0x00 : UInt8)

  let copyOOB := Bytes.copy buf 0 dst 10 8 -- would write past end → noop
  check "copy OOB noop"      (copyOOB.get! 4) (0x00 : UInt8)

  /- Bulk: fill -/
  let filled := Bytes.fill zero 4 8 0xFF
  check "fill untouched @0"  (filled.get! 0)  (0x00 : UInt8)
  check "fill @4"            (filled.get! 4)  (0xFF : UInt8)
  check "fill @11"           (filled.get! 11) (0xFF : UInt8)
  check "fill untouched @12" (filled.get! 12) (0x00 : UInt8)

  /- Bulk: equal -/
  check "equal self full"    (Bytes.equal buf 0 buf 0 16) true
  check "equal self partial" (Bytes.equal buf 4 buf 4 4)  true
  check "equal different"    (Bytes.equal buf 0 buf 4 4)  false
  check "equal zero-len"     (Bytes.equal buf 0 buf 8 0)  true
  check "equal OOB"          (Bytes.equal buf 0 buf 0 99) false

  /- Bulk: compare -/
  checkOrd "compare self"    (Bytes.compare buf 0 buf 0 16) .eq
  checkOrd "compare lt"      (Bytes.compare buf 0 buf 4 4)  .lt
  checkOrd "compare gt"      (Bytes.compare buf 4 buf 0 4)  .gt
  checkOrd "compare zero"    (Bytes.compare buf 0 buf 8 0)  .eq

  let final ← s.get
  IO.println s!"\n  passed: {final.passed}    failed: {final.failed}"
  if final.failed > 0 then IO.Process.exit 1

end BytesTest.Basic
