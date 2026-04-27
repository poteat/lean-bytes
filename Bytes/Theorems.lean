import Bytes
import Std.Tactic.BVDecide

/-! # Theorems about `Bytes.*` primitives

The runtime side of every primitive is its C function in `bytes_ffi.c`,
but the Lean body is the *spec*: each `@[extern]`-tagged declaration
has a definitional unfolding that the kernel can reduce. The theorems
below establish the basic algebraic laws over those specs:

* **Tier 1** — size preservation, OOB-noop, and store/load roundtrip
  for every width × endianness.
* **Tier 2** — pointwise characterizations of `copy`/`fill` and
  reflection lemmas for `equal`/`compare`.
* **Tier 3** — endianness symmetry: `loadUNBE = (loadUNLE).byteSwap`
  and the corresponding store laws.

Together these let you reason about Lean code that uses the
primitives without having to unfold the cascaded `set!`s by hand.

This file is **opt-in**: `import Bytes` gets only the runtime API;
`import Bytes.Theorems` brings the theorems in too.

## Axiom footprint

In addition to the three standard axioms (`propext`, `Quot.sound`,
`Classical.choice`), the bit-shuffling roundtrip and endianness
theorems use `bv_decide`, which emits per-call
`_native.bv_decide.ax_*` axioms backed by an externally-verified LRAT
proof certificate. These are the standard cost of mechanised
bit-vector reasoning and are accepted upstream. -/

/-! ## Helpers on `ByteArray`

Stdlib's `ByteArray.set!` lacks the standard bang-version simp lemmas
(stdlib's set/get lemmas are stated for `Array.setIfInBounds`/
`getElem`). The three lemmas below bridge them to `ByteArray.set!`
and `ByteArray.get!`. They are local helpers — sound and reusable,
but not the headline API. -/

namespace ByteArray

@[simp] theorem data_set! (a : ByteArray) (i : Nat) (b : UInt8) :
    (a.set! i b).data = a.data.set! i b := by rcases a; rfl

theorem get!_eq_data (a : ByteArray) (i : Nat) : a.get! i = a.data[i]! := by
  rcases a; rfl

@[simp] theorem size_set! (a : ByteArray) (i : Nat) (b : UInt8) :
    (a.set! i b).size = a.size := by
  rcases a with ⟨bs⟩
  show (bs.set! i b).size = bs.size
  simp

theorem get!_set!_self (a : ByteArray) (i : Nat) (b : UInt8) (h : i < a.size) :
    (a.set! i b).get! i = b := by
  rw [get!_eq_data, data_set!, Array.set!_eq_setIfInBounds]
  have h' : i < a.data.size := h
  rw [getElem!_pos _ i (by simpa using h')]
  exact Array.getElem_setIfInBounds_self _

theorem get!_set!_ne (a : ByteArray) (i j : Nat) (b : UInt8) (h : i ≠ j) :
    (a.set! i b).get! j = a.get! j := by
  rw [get!_eq_data, get!_eq_data, data_set!, Array.set!_eq_setIfInBounds]
  by_cases hj : j < a.data.size
  · rw [getElem!_pos _ j (by simpa using hj), getElem!_pos _ j hj]
    exact Array.getElem_setIfInBounds_ne hj h
  · rw [getElem!_neg _ j (by simpa using hj), getElem!_neg _ j hj]

end ByteArray

namespace Bytes

/-! ## Tier 1 — size preservation

Stores never resize their argument. Trivial via the helper above plus
the fact that the `if`-branches return `data.set!`-cascades or `data`
itself. -/

@[simp] theorem storeU8_size (data : ByteArray) (off : Nat) (val : UInt8) :
    (storeU8 data off val).size = data.size := by
  unfold storeU8; split <;> simp

@[simp] theorem storeU16LE_size (data : ByteArray) (off : Nat) (val : UInt16) :
    (storeU16LE data off val).size = data.size := by
  unfold storeU16LE; split <;> simp

@[simp] theorem storeU16BE_size (data : ByteArray) (off : Nat) (val : UInt16) :
    (storeU16BE data off val).size = data.size := by
  unfold storeU16BE; split <;> simp

@[simp] theorem storeU32LE_size (data : ByteArray) (off : Nat) (val : UInt32) :
    (storeU32LE data off val).size = data.size := by
  unfold storeU32LE; split <;> simp

@[simp] theorem storeU32BE_size (data : ByteArray) (off : Nat) (val : UInt32) :
    (storeU32BE data off val).size = data.size := by
  unfold storeU32BE; split <;> simp

@[simp] theorem storeU64LE_size (data : ByteArray) (off : Nat) (val : UInt64) :
    (storeU64LE data off val).size = data.size := by
  unfold storeU64LE; split <;> simp

@[simp] theorem storeU64BE_size (data : ByteArray) (off : Nat) (val : UInt64) :
    (storeU64BE data off val).size = data.size := by
  unfold storeU64BE; split <;> simp

/-! ## Tier 1 — OOB no-op

When the requested write would fall (partly) outside the buffer, the
store returns `data` unchanged. -/

theorem storeU8_oob (data : ByteArray) {off : Nat} (val : UInt8)
    (h : off ≥ data.size) : storeU8 data off val = data := by
  unfold storeU8; rw [if_neg (Nat.not_lt.mpr h)]

theorem storeU16LE_oob (data : ByteArray) {off : Nat} (val : UInt16)
    (h : off + 2 > data.size) : storeU16LE data off val = data := by
  unfold storeU16LE; rw [if_neg (Nat.not_le.mpr h)]

theorem storeU16BE_oob (data : ByteArray) {off : Nat} (val : UInt16)
    (h : off + 2 > data.size) : storeU16BE data off val = data := by
  unfold storeU16BE; rw [if_neg (Nat.not_le.mpr h)]

theorem storeU32LE_oob (data : ByteArray) {off : Nat} (val : UInt32)
    (h : off + 4 > data.size) : storeU32LE data off val = data := by
  unfold storeU32LE; rw [if_neg (Nat.not_le.mpr h)]

theorem storeU32BE_oob (data : ByteArray) {off : Nat} (val : UInt32)
    (h : off + 4 > data.size) : storeU32BE data off val = data := by
  unfold storeU32BE; rw [if_neg (Nat.not_le.mpr h)]

theorem storeU64LE_oob (data : ByteArray) {off : Nat} (val : UInt64)
    (h : off + 8 > data.size) : storeU64LE data off val = data := by
  unfold storeU64LE; rw [if_neg (Nat.not_le.mpr h)]

theorem storeU64BE_oob (data : ByteArray) {off : Nat} (val : UInt64)
    (h : off + 8 > data.size) : storeU64BE data off val = data := by
  unfold storeU64BE; rw [if_neg (Nat.not_le.mpr h)]

/-! ## Tier 1 — store/load roundtrip

Writing a value with `storeUNXX` and immediately reading it back with
`loadUNXX` returns the original value, provided the write fits in the
buffer. The single-byte case is direct; the multi-byte cases reduce
to a chain of `get!_set!_self`/`get!_set!_ne` and a final bit-vector
identity (`bv_decide`). -/

theorem loadU8_storeU8_eq (data : ByteArray) (off : Nat) (val : UInt8)
    (h : off < data.size) :
    loadU8 (storeU8 data off val) off = val := by
  unfold loadU8 storeU8
  rw [if_pos h]
  exact ByteArray.get!_set!_self _ _ _ h

theorem loadU16LE_storeU16LE_eq (data : ByteArray) (off : Nat) (val : UInt16)
    (h : off + 2 ≤ data.size) :
    loadU16LE (storeU16LE data off val) off = val := by
  unfold loadU16LE storeU16LE
  rw [if_pos h]
  have h0 : off < data.size := by omega
  have h1' : off + 1 < (data.set! off val.toUInt8).size := by
    rw [ByteArray.size_set!]; omega
  rw [ByteArray.get!_set!_ne _ _ _ _ (by omega : (off + 1 : Nat) ≠ off),
      ByteArray.get!_set!_self _ _ _ h0,
      ByteArray.get!_set!_self _ _ _ h1']
  bv_decide

theorem loadU16BE_storeU16BE_eq (data : ByteArray) (off : Nat) (val : UInt16)
    (h : off + 2 ≤ data.size) :
    loadU16BE (storeU16BE data off val) off = val := by
  unfold loadU16BE storeU16BE
  rw [if_pos h]
  have h0 : off < data.size := by omega
  have h1' : off + 1 < (data.set! off (val >>> 8).toUInt8).size := by
    rw [ByteArray.size_set!]; omega
  rw [ByteArray.get!_set!_ne _ _ _ _ (by omega : (off + 1 : Nat) ≠ off),
      ByteArray.get!_set!_self _ _ _ h0,
      ByteArray.get!_set!_self _ _ _ h1']
  bv_decide

theorem loadU32LE_storeU32LE_eq (data : ByteArray) (off : Nat) (val : UInt32)
    (h : off + 4 ≤ data.size) :
    loadU32LE (storeU32LE data off val) off = val := by
  unfold loadU32LE storeU32LE
  rw [if_pos h]
  -- Read at off+3 (outermost set!): direct _self
  rw [ByteArray.get!_set!_self _ (off + 3) _ (by simp; omega)]
  -- Read at off+2: peel set!(off+3), then _self
  rw [ByteArray.get!_set!_ne _ (off + 3) (off + 2) _ (by omega),
      ByteArray.get!_set!_self _ (off + 2) _ (by simp; omega)]
  -- Read at off+1: peel set!(off+3), set!(off+2), then _self
  rw [ByteArray.get!_set!_ne _ (off + 3) (off + 1) _ (by omega),
      ByteArray.get!_set!_ne _ (off + 2) (off + 1) _ (by omega),
      ByteArray.get!_set!_self _ (off + 1) _ (by simp; omega)]
  -- Read at off: peel set!(off+3), set!(off+2), set!(off+1), then _self
  rw [ByteArray.get!_set!_ne _ (off + 3) off _ (by omega),
      ByteArray.get!_set!_ne _ (off + 2) off _ (by omega),
      ByteArray.get!_set!_ne _ (off + 1) off _ (by omega),
      ByteArray.get!_set!_self _ off _ (by omega)]
  bv_decide

theorem loadU32BE_storeU32BE_eq (data : ByteArray) (off : Nat) (val : UInt32)
    (h : off + 4 ≤ data.size) :
    loadU32BE (storeU32BE data off val) off = val := by
  unfold loadU32BE storeU32BE
  rw [if_pos h]
  rw [ByteArray.get!_set!_self _ (off + 3) _ (by simp; omega)]
  rw [ByteArray.get!_set!_ne _ (off + 3) (off + 2) _ (by omega),
      ByteArray.get!_set!_self _ (off + 2) _ (by simp; omega)]
  rw [ByteArray.get!_set!_ne _ (off + 3) (off + 1) _ (by omega),
      ByteArray.get!_set!_ne _ (off + 2) (off + 1) _ (by omega),
      ByteArray.get!_set!_self _ (off + 1) _ (by simp; omega)]
  rw [ByteArray.get!_set!_ne _ (off + 3) off _ (by omega),
      ByteArray.get!_set!_ne _ (off + 2) off _ (by omega),
      ByteArray.get!_set!_ne _ (off + 1) off _ (by omega),
      ByteArray.get!_set!_self _ off _ (by omega)]
  bv_decide

theorem loadU64LE_storeU64LE_eq (data : ByteArray) (off : Nat) (val : UInt64)
    (h : off + 8 ≤ data.size) :
    loadU64LE (storeU64LE data off val) off = val := by
  unfold loadU64LE storeU64LE
  rw [if_pos h]
  rw [ByteArray.get!_set!_self _ (off + 7) _ (by simp; omega)]
  rw [ByteArray.get!_set!_ne _ (off + 7) (off + 6) _ (by omega),
      ByteArray.get!_set!_self _ (off + 6) _ (by simp; omega)]
  rw [ByteArray.get!_set!_ne _ (off + 7) (off + 5) _ (by omega),
      ByteArray.get!_set!_ne _ (off + 6) (off + 5) _ (by omega),
      ByteArray.get!_set!_self _ (off + 5) _ (by simp; omega)]
  rw [ByteArray.get!_set!_ne _ (off + 7) (off + 4) _ (by omega),
      ByteArray.get!_set!_ne _ (off + 6) (off + 4) _ (by omega),
      ByteArray.get!_set!_ne _ (off + 5) (off + 4) _ (by omega),
      ByteArray.get!_set!_self _ (off + 4) _ (by simp; omega)]
  rw [ByteArray.get!_set!_ne _ (off + 7) (off + 3) _ (by omega),
      ByteArray.get!_set!_ne _ (off + 6) (off + 3) _ (by omega),
      ByteArray.get!_set!_ne _ (off + 5) (off + 3) _ (by omega),
      ByteArray.get!_set!_ne _ (off + 4) (off + 3) _ (by omega),
      ByteArray.get!_set!_self _ (off + 3) _ (by simp; omega)]
  rw [ByteArray.get!_set!_ne _ (off + 7) (off + 2) _ (by omega),
      ByteArray.get!_set!_ne _ (off + 6) (off + 2) _ (by omega),
      ByteArray.get!_set!_ne _ (off + 5) (off + 2) _ (by omega),
      ByteArray.get!_set!_ne _ (off + 4) (off + 2) _ (by omega),
      ByteArray.get!_set!_ne _ (off + 3) (off + 2) _ (by omega),
      ByteArray.get!_set!_self _ (off + 2) _ (by simp; omega)]
  rw [ByteArray.get!_set!_ne _ (off + 7) (off + 1) _ (by omega),
      ByteArray.get!_set!_ne _ (off + 6) (off + 1) _ (by omega),
      ByteArray.get!_set!_ne _ (off + 5) (off + 1) _ (by omega),
      ByteArray.get!_set!_ne _ (off + 4) (off + 1) _ (by omega),
      ByteArray.get!_set!_ne _ (off + 3) (off + 1) _ (by omega),
      ByteArray.get!_set!_ne _ (off + 2) (off + 1) _ (by omega),
      ByteArray.get!_set!_self _ (off + 1) _ (by simp; omega)]
  rw [ByteArray.get!_set!_ne _ (off + 7) off _ (by omega),
      ByteArray.get!_set!_ne _ (off + 6) off _ (by omega),
      ByteArray.get!_set!_ne _ (off + 5) off _ (by omega),
      ByteArray.get!_set!_ne _ (off + 4) off _ (by omega),
      ByteArray.get!_set!_ne _ (off + 3) off _ (by omega),
      ByteArray.get!_set!_ne _ (off + 2) off _ (by omega),
      ByteArray.get!_set!_ne _ (off + 1) off _ (by omega),
      ByteArray.get!_set!_self _ off _ (by omega)]
  bv_decide

theorem loadU64BE_storeU64BE_eq (data : ByteArray) (off : Nat) (val : UInt64)
    (h : off + 8 ≤ data.size) :
    loadU64BE (storeU64BE data off val) off = val := by
  unfold loadU64BE storeU64BE
  rw [if_pos h]
  rw [ByteArray.get!_set!_self _ (off + 7) _ (by simp; omega)]
  rw [ByteArray.get!_set!_ne _ (off + 7) (off + 6) _ (by omega),
      ByteArray.get!_set!_self _ (off + 6) _ (by simp; omega)]
  rw [ByteArray.get!_set!_ne _ (off + 7) (off + 5) _ (by omega),
      ByteArray.get!_set!_ne _ (off + 6) (off + 5) _ (by omega),
      ByteArray.get!_set!_self _ (off + 5) _ (by simp; omega)]
  rw [ByteArray.get!_set!_ne _ (off + 7) (off + 4) _ (by omega),
      ByteArray.get!_set!_ne _ (off + 6) (off + 4) _ (by omega),
      ByteArray.get!_set!_ne _ (off + 5) (off + 4) _ (by omega),
      ByteArray.get!_set!_self _ (off + 4) _ (by simp; omega)]
  rw [ByteArray.get!_set!_ne _ (off + 7) (off + 3) _ (by omega),
      ByteArray.get!_set!_ne _ (off + 6) (off + 3) _ (by omega),
      ByteArray.get!_set!_ne _ (off + 5) (off + 3) _ (by omega),
      ByteArray.get!_set!_ne _ (off + 4) (off + 3) _ (by omega),
      ByteArray.get!_set!_self _ (off + 3) _ (by simp; omega)]
  rw [ByteArray.get!_set!_ne _ (off + 7) (off + 2) _ (by omega),
      ByteArray.get!_set!_ne _ (off + 6) (off + 2) _ (by omega),
      ByteArray.get!_set!_ne _ (off + 5) (off + 2) _ (by omega),
      ByteArray.get!_set!_ne _ (off + 4) (off + 2) _ (by omega),
      ByteArray.get!_set!_ne _ (off + 3) (off + 2) _ (by omega),
      ByteArray.get!_set!_self _ (off + 2) _ (by simp; omega)]
  rw [ByteArray.get!_set!_ne _ (off + 7) (off + 1) _ (by omega),
      ByteArray.get!_set!_ne _ (off + 6) (off + 1) _ (by omega),
      ByteArray.get!_set!_ne _ (off + 5) (off + 1) _ (by omega),
      ByteArray.get!_set!_ne _ (off + 4) (off + 1) _ (by omega),
      ByteArray.get!_set!_ne _ (off + 3) (off + 1) _ (by omega),
      ByteArray.get!_set!_ne _ (off + 2) (off + 1) _ (by omega),
      ByteArray.get!_set!_self _ (off + 1) _ (by simp; omega)]
  rw [ByteArray.get!_set!_ne _ (off + 7) off _ (by omega),
      ByteArray.get!_set!_ne _ (off + 6) off _ (by omega),
      ByteArray.get!_set!_ne _ (off + 5) off _ (by omega),
      ByteArray.get!_set!_ne _ (off + 4) off _ (by omega),
      ByteArray.get!_set!_ne _ (off + 3) off _ (by omega),
      ByteArray.get!_set!_ne _ (off + 2) off _ (by omega),
      ByteArray.get!_set!_ne _ (off + 1) off _ (by omega),
      ByteArray.get!_set!_self _ off _ (by omega)]
  bv_decide

/-! ## Tier 2 — bulk op invariant helper

`Nat.fold n f init` is the spec primitive used by `copy`, `fill`,
`equal`, and `compare`. Most of the bulk-op lemmas reduce to "this
property is preserved by every step", so we prove that pattern once. -/

private theorem foldInvariant {α : Type u} (P : α → Prop) :
    ∀ {n : Nat} (init : α) (f : (i : Nat) → i < n → α → α),
      P init → (∀ i h a, P a → P (f i h a)) → P (Nat.fold n f init) := by
  intro n
  induction n with
  | zero => intros init f h0 _; rw [Nat.fold_zero]; exact h0
  | succ k ih =>
      intros init f h0 hf
      rw [Nat.fold_succ]
      exact hf k _ _ (ih init (fun i h => f i (Nat.lt_succ_of_lt h)) h0
        (fun i h a hPa => hf _ _ _ hPa))

/-! ## Tier 2 — `copy` and `fill` size preservation -/

@[simp] theorem copy_size (src : ByteArray) (srcOff : Nat) (dst : ByteArray)
    (dstOff len : Nat) :
    (copy src srcOff dst dstOff len).size = dst.size := by
  unfold copy
  split
  · rfl
  · refine foldInvariant (fun d => d.size = dst.size) dst _ rfl ?_
    intros _ _ d h; rw [ByteArray.size_set!]; exact h

@[simp] theorem fill_size (data : ByteArray) (off len : Nat) (val : UInt8) :
    (fill data off len val).size = data.size := by
  unfold fill
  split
  · rfl
  · refine foldInvariant (fun d => d.size = data.size) data _ rfl ?_
    intros _ _ d h; rw [ByteArray.size_set!]; exact h

/-! ## Tier 2 — `copy`/`fill`/`equal`/`compare` OOB no-op -/

theorem copy_oob_src (src : ByteArray) {srcOff : Nat} (dst : ByteArray)
    (dstOff len : Nat) (h : srcOff + len > src.size) :
    copy src srcOff dst dstOff len = dst := by
  unfold copy; rw [if_pos (by simp [h])]

theorem copy_oob_dst (src : ByteArray) (srcOff : Nat) (dst : ByteArray)
    {dstOff len : Nat} (h : dstOff + len > dst.size) :
    copy src srcOff dst dstOff len = dst := by
  unfold copy; rw [if_pos (by simp [h])]

theorem fill_oob (data : ByteArray) {off len : Nat} (val : UInt8)
    (h : off + len > data.size) : fill data off len val = data := by
  unfold fill; rw [if_pos h]

theorem equal_oob_a (a : ByteArray) {aOff : Nat} (b : ByteArray) (bOff len : Nat)
    (h : aOff + len > a.size) : equal a aOff b bOff len = false := by
  unfold equal; rw [if_pos (by simp [h])]

theorem equal_oob_b (a : ByteArray) (aOff : Nat) (b : ByteArray) {bOff len : Nat}
    (h : bOff + len > b.size) : equal a aOff b bOff len = false := by
  unfold equal; rw [if_pos (by simp [h])]

theorem compare_oob_a (a : ByteArray) {aOff : Nat} (b : ByteArray) (bOff len : Nat)
    (h : aOff + len > a.size) : compare a aOff b bOff len = .eq := by
  unfold compare; rw [if_pos (by simp [h])]

theorem compare_oob_b (a : ByteArray) (aOff : Nat) (b : ByteArray) {bOff len : Nat}
    (h : bOff + len > b.size) : compare a aOff b bOff len = .eq := by
  unfold compare; rw [if_pos (by simp [h])]

/-! ## Tier 2 — `equal`/`compare` reflexivity

`equal a off a off len` is `true` and `compare a off a off len` is
`.eq`, provided the range fits. The fold accumulator is invariant: at
every step both sides agree. -/

theorem equal_self (a : ByteArray) (off len : Nat) (h : off + len ≤ a.size) :
    equal a off a off len = true := by
  unfold equal
  rw [if_neg (by simp; omega)]
  refine foldInvariant (fun b => b = true) true _ rfl ?_
  intros _ _ acc hAcc; subst hAcc; simp

theorem compare_self (a : ByteArray) (off len : Nat) (h : off + len ≤ a.size) :
    compare a off a off len = Ordering.eq := by
  unfold compare
  rw [if_neg (by simp; omega)]
  refine foldInvariant (fun o => o = Ordering.eq) Ordering.eq _ rfl ?_
  intros i _ acc hAcc
  subst hAcc
  show (Ord.compare (a.get! (off + i)) (a.get! (off + i))) = Ordering.eq
  show compareOfLessAndEq (a.get! (off + i)) (a.get! (off + i)) = Ordering.eq
  unfold compareOfLessAndEq
  simp

/-! ## Tier 2 — `copy` / `fill` pointwise characterizations

Both `copy` and `fill` reduce to a `Nat.fold` of `set!` calls at
distinct offsets, so we can characterize the result byte-by-byte:
inside the written window the value is what was written, outside it
the buffer is untouched. The two private fold helpers below capture
the inductive content; the headline `_get_in_range` / `_get_out_range`
theorems specialize to `fill` and `copy`. -/

private theorem fold_set!_size (data : ByteArray) (n : Nat) (g : Nat → UInt8) (off : Nat) :
    (Nat.fold n (fun i _ d => d.set! (off + i) (g i)) data).size = data.size := by
  induction n with
  | zero => rw [Nat.fold_zero]
  | succ m ih =>
      rw [Nat.fold_succ, ByteArray.size_set!]
      exact ih

private theorem fold_set!_get_in (data : ByteArray) (off : Nat) (g : Nat → UInt8)
    (n : Nat) (hsz : off + n ≤ data.size) (k : Nat) (hk : k < n) :
    (Nat.fold n (fun i _ d => d.set! (off + i) (g i)) data).get! (off + k) = g k := by
  induction n with
  | zero => omega
  | succ m ih =>
      rw [Nat.fold_succ]
      by_cases hkm : k = m
      · rw [hkm]
        apply ByteArray.get!_set!_self
        have := fold_set!_size data m g off
        omega
      · rw [ByteArray.get!_set!_ne _ (off + m) (off + k) _ (by omega)]
        exact ih (by omega) (by omega)

private theorem fold_set!_get_out (data : ByteArray) (off : Nat) (g : Nat → UInt8) (n : Nat)
    (j : Nat) (hj : j < off ∨ j ≥ off + n) :
    (Nat.fold n (fun i _ d => d.set! (off + i) (g i)) data).get! j = data.get! j := by
  induction n with
  | zero => rw [Nat.fold_zero]
  | succ m ih =>
      rw [Nat.fold_succ]
      rw [ByteArray.get!_set!_ne _ (off + m) j _ (by omega)]
      exact ih (by omega)

theorem fill_get_in_range (data : ByteArray) (off len : Nat) (val : UInt8)
    (h : off + len ≤ data.size) (k : Nat) (hk : k < len) :
    (fill data off len val).get! (off + k) = val := by
  unfold fill
  rw [if_neg (by omega)]
  exact fold_set!_get_in data off (fun _ => val) len h k hk

theorem fill_get_out_range (data : ByteArray) (off len : Nat) (val : UInt8)
    (j : Nat) (hj : j < off ∨ j ≥ off + len) :
    (fill data off len val).get! j = data.get! j := by
  unfold fill
  split
  · rfl
  · exact fold_set!_get_out data off (fun _ => val) len j hj

theorem copy_get_in_range (src : ByteArray) (srcOff : Nat) (dst : ByteArray)
    (dstOff len : Nat) (hsrc : srcOff + len ≤ src.size) (hdst : dstOff + len ≤ dst.size)
    (k : Nat) (hk : k < len) :
    (copy src srcOff dst dstOff len).get! (dstOff + k) = src.get! (srcOff + k) := by
  unfold copy
  rw [if_neg (by simp; omega)]
  exact fold_set!_get_in dst dstOff (fun i => src.get! (srcOff + i)) len hdst k hk

theorem copy_get_out_range (src : ByteArray) (srcOff : Nat) (dst : ByteArray)
    (dstOff len j : Nat) (hj : j < dstOff ∨ j ≥ dstOff + len) :
    (copy src srcOff dst dstOff len).get! j = dst.get! j := by
  unfold copy
  split
  · rfl
  · exact fold_set!_get_out dst dstOff (fun i => src.get! (srcOff + i)) len j hj

/-! ## Tier 3 — endianness symmetry

`loadUNBE` reads the same bytes as `loadUNLE` but with the bytes
reversed. We package that observation as `loadUNBE = byteSwapN
(loadUNLE)` (and dually for stores). The byte-swap helpers below are
proof-side conveniences; the runtime never calls them. -/

/-- 16-bit byte swap: high byte ↔ low byte. -/
def byteSwap16 (x : UInt16) : UInt16 := (x <<< 8) ||| (x >>> 8)

/-- 32-bit byte swap: reverses the four bytes. -/
def byteSwap32 (x : UInt32) : UInt32 :=
  ((x &&& 0x000000FF) <<< 24) ||| ((x &&& 0x0000FF00) <<< 8) |||
  ((x &&& 0x00FF0000) >>> 8)  ||| ((x &&& 0xFF000000) >>> 24)

/-- 64-bit byte swap: reverses the eight bytes. -/
def byteSwap64 (x : UInt64) : UInt64 :=
  ((x &&& 0x00000000000000FF) <<< 56) ||| ((x &&& 0x000000000000FF00) <<< 40) |||
  ((x &&& 0x0000000000FF0000) <<< 24) ||| ((x &&& 0x00000000FF000000) <<< 8) |||
  ((x &&& 0x000000FF00000000) >>> 8)  ||| ((x &&& 0x0000FF0000000000) >>> 24) |||
  ((x &&& 0x00FF000000000000) >>> 40) ||| ((x &&& 0xFF00000000000000) >>> 56)

theorem loadU16BE_eq_byteSwap_loadU16LE (data : ByteArray) (off : Nat) :
    loadU16BE data off = byteSwap16 (loadU16LE data off) := by
  unfold loadU16BE loadU16LE byteSwap16
  bv_decide

theorem loadU32BE_eq_byteSwap_loadU32LE (data : ByteArray) (off : Nat) :
    loadU32BE data off = byteSwap32 (loadU32LE data off) := by
  unfold loadU32BE loadU32LE byteSwap32
  bv_decide

theorem loadU64BE_eq_byteSwap_loadU64LE (data : ByteArray) (off : Nat) :
    loadU64BE data off = byteSwap64 (loadU64LE data off) := by
  unfold loadU64BE loadU64LE byteSwap64
  bv_decide

theorem storeU16BE_eq_storeU16LE_byteSwap (data : ByteArray) (off : Nat) (val : UInt16) :
    storeU16BE data off val = storeU16LE data off (byteSwap16 val) := by
  have hb0 : (val >>> 8).toUInt8 = (byteSwap16 val).toUInt8 := by
    unfold byteSwap16; bv_decide
  have hb1 : val.toUInt8 = (byteSwap16 val >>> 8).toUInt8 := by
    unfold byteSwap16; bv_decide
  unfold storeU16BE storeU16LE
  rw [hb0, hb1]

theorem storeU32BE_eq_storeU32LE_byteSwap (data : ByteArray) (off : Nat) (val : UInt32) :
    storeU32BE data off val = storeU32LE data off (byteSwap32 val) := by
  have hb0 : (val >>> 24).toUInt8 = (byteSwap32 val).toUInt8 := by
    unfold byteSwap32; bv_decide
  have hb1 : (val >>> 16).toUInt8 = (byteSwap32 val >>> 8).toUInt8 := by
    unfold byteSwap32; bv_decide
  have hb2 : (val >>> 8).toUInt8 = (byteSwap32 val >>> 16).toUInt8 := by
    unfold byteSwap32; bv_decide
  have hb3 : val.toUInt8 = (byteSwap32 val >>> 24).toUInt8 := by
    unfold byteSwap32; bv_decide
  unfold storeU32BE storeU32LE
  rw [hb0, hb1, hb2, hb3]

theorem storeU64BE_eq_storeU64LE_byteSwap (data : ByteArray) (off : Nat) (val : UInt64) :
    storeU64BE data off val = storeU64LE data off (byteSwap64 val) := by
  have hb0 : (val >>> 56).toUInt8 = (byteSwap64 val).toUInt8 := by
    unfold byteSwap64; bv_decide
  have hb1 : (val >>> 48).toUInt8 = (byteSwap64 val >>> 8).toUInt8 := by
    unfold byteSwap64; bv_decide
  have hb2 : (val >>> 40).toUInt8 = (byteSwap64 val >>> 16).toUInt8 := by
    unfold byteSwap64; bv_decide
  have hb3 : (val >>> 32).toUInt8 = (byteSwap64 val >>> 24).toUInt8 := by
    unfold byteSwap64; bv_decide
  have hb4 : (val >>> 24).toUInt8 = (byteSwap64 val >>> 32).toUInt8 := by
    unfold byteSwap64; bv_decide
  have hb5 : (val >>> 16).toUInt8 = (byteSwap64 val >>> 40).toUInt8 := by
    unfold byteSwap64; bv_decide
  have hb6 : (val >>> 8).toUInt8 = (byteSwap64 val >>> 48).toUInt8 := by
    unfold byteSwap64; bv_decide
  have hb7 : val.toUInt8 = (byteSwap64 val >>> 56).toUInt8 := by
    unfold byteSwap64; bv_decide
  unfold storeU64BE storeU64LE
  rw [hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7]

end Bytes
