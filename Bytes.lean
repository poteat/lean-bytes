/-! # Bytes — fast unaligned reads, writes, and bulk ops on `ByteArray`

The functions in this module are declared `@[extern]` and route to
small C functions in `c/bytes_ffi.c` at runtime. The Lean bodies remain
the spec for kernel reduction and proofs: any in-bounds offset must
produce the same result either way.

## Out-of-bounds semantics

The whole module avoids panics; OOB is handled as a documented default:

* **Loads** are *partial*: each byte beyond `data.size` reads as `0`,
  inheriting the `ByteArray.get!` runtime behaviour. So a `loadU64LE`
  whose last few bytes lie past the end returns the in-bounds prefix
  with the missing high bytes zeroed.
* **Stores** are *atomic*: if any byte of the requested write would
  fall outside `data.size`, the call is a no-op and `data` is returned
  unchanged. No partial writes.
* **Bulk ops** (`copy`, `fill`) are atomic in the same sense; `equal`
  returns `false` when ranges don't fit, `compare` returns `.eq` (a
  safe but information-losing default — callers that care must
  bounds-check).
-/

namespace Bytes

/-! ## Reads

Each `loadU{N}{LE,BE}` returns a `UInt{N}` of the natural width. To
zero-extend to a wider type, use `.toUInt64` etc. at the call site. -/

/-- Read one byte from `data` at byte `off`. Returns `0` if OOB. -/
@[extern "lean_bytes_load_u8"]
def loadU8 (data : @& ByteArray) (off : @& Nat) : UInt8 :=
  data.get! off

/-- Read a little-endian 16-bit word at byte `off`. -/
@[extern "lean_bytes_load_u16_le"]
def loadU16LE (data : @& ByteArray) (off : @& Nat) : UInt16 :=
  let b0 := (data.get! off).toUInt16
  let b1 := (data.get! (off + 1)).toUInt16
  b0 ||| (b1 <<< 8)

/-- Read a big-endian 16-bit word at byte `off`. -/
@[extern "lean_bytes_load_u16_be"]
def loadU16BE (data : @& ByteArray) (off : @& Nat) : UInt16 :=
  let b0 := (data.get! off).toUInt16
  let b1 := (data.get! (off + 1)).toUInt16
  (b0 <<< 8) ||| b1

/-- Read a little-endian 32-bit word at byte `off`. -/
@[extern "lean_bytes_load_u32_le"]
def loadU32LE (data : @& ByteArray) (off : @& Nat) : UInt32 :=
  let b0 := (data.get! off).toUInt32
  let b1 := (data.get! (off + 1)).toUInt32
  let b2 := (data.get! (off + 2)).toUInt32
  let b3 := (data.get! (off + 3)).toUInt32
  b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)

/-- Read a big-endian 32-bit word at byte `off`. -/
@[extern "lean_bytes_load_u32_be"]
def loadU32BE (data : @& ByteArray) (off : @& Nat) : UInt32 :=
  let b0 := (data.get! off).toUInt32
  let b1 := (data.get! (off + 1)).toUInt32
  let b2 := (data.get! (off + 2)).toUInt32
  let b3 := (data.get! (off + 3)).toUInt32
  (b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8) ||| b3

/-- Read a little-endian 64-bit word at byte `off`. -/
@[extern "lean_bytes_load_u64_le"]
def loadU64LE (data : @& ByteArray) (off : @& Nat) : UInt64 :=
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

/-- Read a big-endian 64-bit word at byte `off`. -/
@[extern "lean_bytes_load_u64_be"]
def loadU64BE (data : @& ByteArray) (off : @& Nat) : UInt64 :=
  let b0 := (data.get! off).toUInt64
  let b1 := (data.get! (off + 1)).toUInt64
  let b2 := (data.get! (off + 2)).toUInt64
  let b3 := (data.get! (off + 3)).toUInt64
  let b4 := (data.get! (off + 4)).toUInt64
  let b5 := (data.get! (off + 5)).toUInt64
  let b6 := (data.get! (off + 6)).toUInt64
  let b7 := (data.get! (off + 7)).toUInt64
  (b0 <<< 56) ||| (b1 <<< 48) ||| (b2 <<< 40) ||| (b3 <<< 32) |||
    (b4 <<< 24) ||| (b5 <<< 16) ||| (b6 <<< 8) ||| b7

/-! ## Writes

Stores take `data` by value, return the modified ByteArray, and
preserve linearity at runtime: when the C function is given an exclusive
reference it mutates in place; otherwise it copies once and mutates
the copy. Atomic OOB semantics — any out-of-bounds byte makes the
whole call a no-op. -/

/-- Write one byte at `off`. No-op if OOB. -/
@[extern "lean_bytes_store_u8"]
def storeU8 (data : ByteArray) (off : @& Nat) (val : UInt8) : ByteArray :=
  if off < data.size then data.set! off val else data

/-- Write a little-endian 16-bit word at `off`. No-op if `off+2 > data.size`. -/
@[extern "lean_bytes_store_u16_le"]
def storeU16LE (data : ByteArray) (off : @& Nat) (val : UInt16) : ByteArray :=
  if off + 2 ≤ data.size then
    let b0 := val.toUInt8
    let b1 := (val >>> 8).toUInt8
    (data.set! off b0).set! (off + 1) b1
  else data

/-- Write a big-endian 16-bit word at `off`. No-op if `off+2 > data.size`. -/
@[extern "lean_bytes_store_u16_be"]
def storeU16BE (data : ByteArray) (off : @& Nat) (val : UInt16) : ByteArray :=
  if off + 2 ≤ data.size then
    let b0 := (val >>> 8).toUInt8
    let b1 := val.toUInt8
    (data.set! off b0).set! (off + 1) b1
  else data

/-- Write a little-endian 32-bit word at `off`. No-op if `off+4 > data.size`. -/
@[extern "lean_bytes_store_u32_le"]
def storeU32LE (data : ByteArray) (off : @& Nat) (val : UInt32) : ByteArray :=
  if off + 4 ≤ data.size then
    let b0 := val.toUInt8
    let b1 := (val >>> 8).toUInt8
    let b2 := (val >>> 16).toUInt8
    let b3 := (val >>> 24).toUInt8
    (((data.set! off b0).set! (off + 1) b1).set! (off + 2) b2).set! (off + 3) b3
  else data

/-- Write a big-endian 32-bit word at `off`. No-op if `off+4 > data.size`. -/
@[extern "lean_bytes_store_u32_be"]
def storeU32BE (data : ByteArray) (off : @& Nat) (val : UInt32) : ByteArray :=
  if off + 4 ≤ data.size then
    let b0 := (val >>> 24).toUInt8
    let b1 := (val >>> 16).toUInt8
    let b2 := (val >>> 8).toUInt8
    let b3 := val.toUInt8
    (((data.set! off b0).set! (off + 1) b1).set! (off + 2) b2).set! (off + 3) b3
  else data

/-- Write a little-endian 64-bit word at `off`. No-op if `off+8 > data.size`. -/
@[extern "lean_bytes_store_u64_le"]
def storeU64LE (data : ByteArray) (off : @& Nat) (val : UInt64) : ByteArray :=
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

/-- Write a big-endian 64-bit word at `off`. No-op if `off+8 > data.size`. -/
@[extern "lean_bytes_store_u64_be"]
def storeU64BE (data : ByteArray) (off : @& Nat) (val : UInt64) : ByteArray :=
  if off + 8 ≤ data.size then
    let b0 := (val >>> 56).toUInt8
    let b1 := (val >>> 48).toUInt8
    let b2 := (val >>> 40).toUInt8
    let b3 := (val >>> 32).toUInt8
    let b4 := (val >>> 24).toUInt8
    let b5 := (val >>> 16).toUInt8
    let b6 := (val >>> 8).toUInt8
    let b7 := val.toUInt8
    (((((((data.set! off b0).set! (off + 1) b1).set! (off + 2) b2).set! (off + 3) b3
      ).set! (off + 4) b4).set! (off + 5) b5).set! (off + 6) b6).set! (off + 7) b7
  else data

/-! ## Bulk operations

Backed by `memmove`, `memset`, `memcmp` on the C side. All four are
atomic w.r.t. OOB: if the requested range exceeds either array's
size, `copy`/`fill` no-op, `equal` returns `false`, `compare` returns
`.eq`. -/

/-- Copy `len` bytes from `src` starting at `srcOff` into `dst`
starting at `dstOff`. Aliasing is handled (uses `memmove` semantics
on the C side). No-op if either range is OOB. -/
@[extern "lean_bytes_copy"]
def copy (src : @& ByteArray) (srcOff : @& Nat)
         (dst : ByteArray) (dstOff : @& Nat) (len : @& Nat) : ByteArray :=
  if srcOff + len > src.size || dstOff + len > dst.size then dst
  else Nat.fold len (fun i _ d => d.set! (dstOff + i) (src.get! (srcOff + i))) dst

/-- Fill `len` bytes of `data` starting at `off` with `val`. No-op if `off+len > data.size`. -/
@[extern "lean_bytes_fill"]
def fill (data : ByteArray) (off : @& Nat) (len : @& Nat) (val : UInt8) : ByteArray :=
  if off + len > data.size then data
  else Nat.fold len (fun i _ d => d.set! (off + i) val) data

/-- Byte-equal: `true` iff `a[aOff..aOff+len] = b[bOff..bOff+len]`.
Returns `false` if either range is OOB. The Lean spec walks the full
range with an `&&` accumulator (no early exit); the C runtime uses
`memcmp`. Same observable result. -/
@[extern "lean_bytes_equal"]
def equal (a : @& ByteArray) (aOff : @& Nat)
          (b : @& ByteArray) (bOff : @& Nat) (len : @& Nat) : Bool :=
  if aOff + len > a.size || bOff + len > b.size then false
  else Nat.fold len (fun i _ acc => acc && (a.get! (aOff + i) == b.get! (bOff + i))) true

/-- Lexicographic byte compare of two ranges. Returns `.eq` as the safe
default if either range is OOB — callers that care must bounds-check.
The spec walks the full range, keeping the first non-`.eq` decision; C
side uses `memcmp` and exits early. Same observable result. -/
@[extern "lean_bytes_compare"]
def compare (a : @& ByteArray) (aOff : @& Nat)
            (b : @& ByteArray) (bOff : @& Nat) (len : @& Nat) : Ordering :=
  if aOff + len > a.size || bOff + len > b.size then .eq
  else Nat.fold len
    (fun i _ acc => match acc with
      | .eq => Ord.compare (a.get! (aOff + i)) (b.get! (bOff + i))
      | _ => acc)
    .eq

end Bytes
