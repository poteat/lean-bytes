import Bytes

/-! Pure-Lean reimplementations of every `Bytes.*` primitive. Bodies are
identical to the spec sides of the `@[extern]` declarations in `Bytes.lean`,
but without the `@[extern]` tag — so calls compile to the Lean implementation
rather than routing through `c/bytes_ffi.c`. Used as the oracle in
randomized FFI-equivalence tests. -/

namespace BytesTest.Spec

def loadU8 (data : ByteArray) (off : Nat) : UInt8 :=
  data.get! off

def loadU16LE (data : ByteArray) (off : Nat) : UInt16 :=
  let b0 := (data.get! off).toUInt16
  let b1 := (data.get! (off + 1)).toUInt16
  b0 ||| (b1 <<< 8)

def loadU16BE (data : ByteArray) (off : Nat) : UInt16 :=
  let b0 := (data.get! off).toUInt16
  let b1 := (data.get! (off + 1)).toUInt16
  (b0 <<< 8) ||| b1

def loadU32LE (data : ByteArray) (off : Nat) : UInt32 :=
  let b0 := (data.get! off).toUInt32
  let b1 := (data.get! (off + 1)).toUInt32
  let b2 := (data.get! (off + 2)).toUInt32
  let b3 := (data.get! (off + 3)).toUInt32
  b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)

def loadU32BE (data : ByteArray) (off : Nat) : UInt32 :=
  let b0 := (data.get! off).toUInt32
  let b1 := (data.get! (off + 1)).toUInt32
  let b2 := (data.get! (off + 2)).toUInt32
  let b3 := (data.get! (off + 3)).toUInt32
  (b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8) ||| b3

def loadU64LE (data : ByteArray) (off : Nat) : UInt64 :=
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

def loadU64BE (data : ByteArray) (off : Nat) : UInt64 :=
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

def storeU8 (data : ByteArray) (off : Nat) (val : UInt8) : ByteArray :=
  if off < data.size then data.set! off val else data

def storeU16LE (data : ByteArray) (off : Nat) (val : UInt16) : ByteArray :=
  if off + 2 ≤ data.size then
    let b0 := val.toUInt8
    let b1 := (val >>> 8).toUInt8
    (data.set! off b0).set! (off + 1) b1
  else data

def storeU16BE (data : ByteArray) (off : Nat) (val : UInt16) : ByteArray :=
  if off + 2 ≤ data.size then
    let b0 := (val >>> 8).toUInt8
    let b1 := val.toUInt8
    (data.set! off b0).set! (off + 1) b1
  else data

def storeU32LE (data : ByteArray) (off : Nat) (val : UInt32) : ByteArray :=
  if off + 4 ≤ data.size then
    let b0 := val.toUInt8
    let b1 := (val >>> 8).toUInt8
    let b2 := (val >>> 16).toUInt8
    let b3 := (val >>> 24).toUInt8
    (((data.set! off b0).set! (off + 1) b1).set! (off + 2) b2).set! (off + 3) b3
  else data

def storeU32BE (data : ByteArray) (off : Nat) (val : UInt32) : ByteArray :=
  if off + 4 ≤ data.size then
    let b0 := (val >>> 24).toUInt8
    let b1 := (val >>> 16).toUInt8
    let b2 := (val >>> 8).toUInt8
    let b3 := val.toUInt8
    (((data.set! off b0).set! (off + 1) b1).set! (off + 2) b2).set! (off + 3) b3
  else data

def storeU64LE (data : ByteArray) (off : Nat) (val : UInt64) : ByteArray :=
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

def storeU64BE (data : ByteArray) (off : Nat) (val : UInt64) : ByteArray :=
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

def copy (src : ByteArray) (srcOff : Nat) (dst : ByteArray)
    (dstOff : Nat) (len : Nat) : ByteArray :=
  if srcOff + len > src.size || dstOff + len > dst.size then dst
  else Nat.fold len (fun i _ d => d.set! (dstOff + i) (src.get! (srcOff + i))) dst

def fill (data : ByteArray) (off : Nat) (len : Nat) (val : UInt8) : ByteArray :=
  if off + len > data.size then data
  else Nat.fold len (fun i _ d => d.set! (off + i) val) data

def equal (a : ByteArray) (aOff : Nat) (b : ByteArray) (bOff : Nat) (len : Nat) : Bool :=
  if aOff + len > a.size || bOff + len > b.size then false
  else Nat.fold len (fun i _ acc => acc && (a.get! (aOff + i) == b.get! (bOff + i))) true

def compare (a : ByteArray) (aOff : Nat) (b : ByteArray)
    (bOff : Nat) (len : Nat) : Ordering :=
  if aOff + len > a.size || bOff + len > b.size then .eq
  else Nat.fold len
    (fun i _ acc => match acc with
      | .eq => Ord.compare (a.get! (aOff + i)) (b.get! (bOff + i))
      | _ => acc)
    .eq

end BytesTest.Spec
