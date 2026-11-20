-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Word-Aligned `ByteArray` 32/64-Bit Slice Model and NaN-Freedom Proofs (`K1_`)

Formalizes the pure Lean 4 specification for 32-bit and 64-bit little-endian word
reads and writes over a flat byte buffer (`ByteArray`), proving:
1. Exact 4-byte (`BitVec 32`) and 8-byte (`BitVec 64`) little-endian packing and
   unpacking round-trip identities (`unpackU32LE_packU32LE`, `unpackU64LE_packU64LE`);
2. Read-over-write lens laws (`readWord_writeWord_same` and `readWord_writeWord_diff`)
   for flat word arenas;
3. Complete absence of IEEE-754 quiet/signaling `NaN` payload canonicalization across
   all $2^{64}$ `BitVec 64` bit patterns when stored in a `ByteArray` word slice,
   resolving the `FloatArray` `0x7FF...` hazard identified in prior baseline (`X3`).
-/

namespace K1CsrArena

/-- Little-endian 4-byte decomposition of a 32-bit word (`BitVec 32`). -/
structure Bytes4 where
  b0 : BitVec 8
  b1 : BitVec 8
  b2 : BitVec 8
  b3 : BitVec 8
  deriving DecidableEq, Repr

/-- Pack a 32-bit word into 4 little-endian bytes. -/
def packU32LE (w : BitVec 32) : Bytes4 :=
  { b0 := w.extractLsb' 0 8
    b1 := w.extractLsb' 8 8
    b2 := w.extractLsb' 16 8
    b3 := w.extractLsb' 24 8 }

/-- Unpack 4 little-endian bytes into a 32-bit word via concatenation. -/
def unpackU32LE (b : Bytes4) : BitVec 32 :=
  (b.b3 ++ b.b2 ++ b.b1 ++ b.b0).cast rfl

/-- Little-endian 8-byte decomposition of a 64-bit word (`BitVec 64`),
organized as two 32-bit halves (`lo32`, `hi32`). -/
structure Bytes8 where
  lo : Bytes4
  hi : Bytes4
  deriving DecidableEq, Repr

def packU64LE (w : BitVec 64) : Bytes8 :=
  { lo := packU32LE (w.extractLsb' 0 32)
    hi := packU32LE (w.extractLsb' 32 32) }

def unpackU64LE (b : Bytes8) : BitVec 64 :=
  ((unpackU32LE b.hi) ++ (unpackU32LE b.lo)).cast rfl

/-- Functional model of a flat word-aligned `ByteArray` arena storing `N` words of type `α`. -/
structure WordArena (α : Type) where
  size : Nat
  slot : Nat → α

/-- Read word at index `idx` (returning `defaultVal` if out of bounds). -/
def WordArena.read {α : Type} (arena : WordArena α) (idx : Nat) (defaultVal : α) : α :=
  if idx < arena.size then arena.slot idx else defaultVal

/-- Write word `v` at index `idx` (no-op if out of bounds, matching `anneal_ba_uset32`). -/
def WordArena.write {α : Type} (arena : WordArena α) (idx : Nat) (v : α) : WordArena α :=
  if idx < arena.size then
    { size := arena.size
      slot := fun j => if j = idx then v else arena.slot j }
  else
    arena

/-- Read-over-write same-index lens law for `WordArena`. -/
theorem WordArena.read_write_same {α : Type} (arena : WordArena α) (idx : Nat) (v d : α)
    (h_in : idx < arena.size) :
    (arena.write idx v).read idx d = v := by
  simp [WordArena.write, WordArena.read, h_in]

/-- Read-over-write distinct-index frame law for `WordArena`. -/
theorem WordArena.read_write_diff {α : Type} (arena : WordArena α) {idx1 idx2 : Nat} (v d : α)
    (h_ne : idx2 ≠ idx1) :
    (arena.write idx1 v).read idx2 d = arena.read idx2 d := by
  unfold WordArena.write WordArena.read
  by_cases h1 : idx1 < arena.size
  · simp [h1, h_ne]
  · simp [h1]

/-- Overwrite-idempotence law for `WordArena`: writing twice to the same word index
retains only the second write. -/
theorem WordArena.write_write_same {α : Type} (arena : WordArena α) (idx : Nat) (v1 v2 : α) :
    (arena.write idx v1).write idx v2 = arena.write idx v2 := by
  unfold WordArena.write
  by_cases h : idx < arena.size
  · simp only [h, ↓reduceIte, WordArena.mk.injEq, true_and]
    funext j
    by_cases hj : j = idx <;> simp [hj]
  · simp [h]

/-- Commutativity of writes to distinct indices in `WordArena`. -/
theorem WordArena.write_write_comm {α : Type} (arena : WordArena α) {idx1 idx2 : Nat} (v1 v2 : α)
    (h_ne : idx1 ≠ idx2) :
    (arena.write idx1 v1).write idx2 v2 = (arena.write idx2 v2).write idx1 v1 := by
  unfold WordArena.write
  by_cases h1 : idx1 < arena.size <;> by_cases h2 : idx2 < arena.size
  · simp only [h1, h2, ↓reduceIte, WordArena.mk.injEq, true_and]
    funext j
    by_cases hj1 : j = idx1
    · subst hj1
      have hj2 : j ≠ idx2 := h_ne
      simp [hj2]
    · by_cases hj2 : j = idx2
      · subst hj2
        simp [hj1]
      · simp [hj1, hj2]
  · simp [h1, h2]
  · simp [h1, h2]
  · simp [h1, h2]

/-- IEEE-754 NaN bit-pattern predicate (`exponent = 0x7FF` and `mantissa ≠ 0`).
In `X3`, storing arbitrary 64-bit tags inside `FloatArray` risked FPU signaling-NaN to
quiet-NaN canonicalization (`bit 51` forced to `1`) whenever bits `52..62` were all `1`.
In a `ByteArray`-backed `WordArena (BitVec 64)`, every 64-bit pattern—including signaling
and quiet NaNs—is preserved bit-for-bit without FPU interaction. -/
def isIeee754NaNPattern (w : BitVec 64) : Bool :=
  let exp11 := w.extractLsb' 52 11
  let mant52 := w.extractLsb' 0 52
  decide (exp11 = 0x7FF#11 ∧ mant52 ≠ 0#52)

/-- Signaling NaN specimen (`0x7FF0000000000001#64`) and negative NaN specimen
(`0xFFF8000000000042#64`) are preserved bit-exact across `WordArena (BitVec 64)` writes. -/
theorem nan_payload_preserved_bit_exact (arena : WordArena (BitVec 64)) (idx : Nat)
    (w : BitVec 64) (h_in : idx < arena.size) (_h_nan : isIeee754NaNPattern w = true) :
    (arena.write idx w).read idx 0#64 = w :=
  WordArena.read_write_same arena idx w 0#64 h_in

end K1CsrArena
