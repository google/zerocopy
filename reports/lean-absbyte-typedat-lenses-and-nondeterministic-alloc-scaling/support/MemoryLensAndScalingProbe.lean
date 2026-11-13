-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Mechanized Probe: `TypedAt` + `HasUniqueWritePerm` Lenses, Tree Borrows, and Provenance-Directed Addressing

Standalone, kernel-checked Lean 4 module (verified on both Lean `v4.28.0-rc1`
commit `3b0f2862196c6a8af9eb0025ee650252694013dd` and Lean `v4.34.1` commit
`5045d0056413266e57c625dcd7c365b10e377c52`) establishing:

1. **Relational Memory and Borrow-Tree Lenses**: Mechanized prototype and kernel
   scaling benchmark of `TypedAt` + `HasUniqueWritePerm` / `HasSharedReadPerm`
   (`FootprintAt`) over `List AbsByte` and 5-state `BorrowTree`, including
   `LayoutCodec` (`UInt32`, `UInt64`, `ThinPtr`, `pairCodec`), `TransmuteAs`,
   two-stage protector release, and the four foundational relational lens
   theorems:
   - `read_write_same`
   - `read_write_disjoint`
   - `footprintAt_preserve_local_write` (plus `footprintAt_preserve_disjoint_write`)
   - `footprintAt_preserve_foreign_read`
   together with up to 30 sequential symbolic struct/reference mutations over
   universally quantified `∀ x y z : UInt32`.
2. **Provenance-Directed Nondeterministic Allocation Scaling**: Eliminating
   $O(N^2)$ address-disjointness (`omega`) obligations under nondeterministic
   `baseAddr` (`StepResult.choice` over `ValidFreshBaseAddr`) via
   provenance-directed intra-allocation offset cancellation
   (`resolveOffset_offsetPtr_rootPtr`), constructive nonemptiness
   (`validFreshBaseAddr_nonempty`), the $O(1)$ weakest-precondition step theorem
   (`wp_forceAllocation_choice`), and an $N = 10$ nondeterministic stack
   allocation benchmark (`wp_ten_nondet_stack_allocs`) with zero pairwise
   `baseAddr_i ≠ baseAddr_j` obligations.
-/

namespace MemoryLensAndScalingProbe

/-! ## Section 1: Abstract Bytes (`AbsByte`), Provenance, and Contiguous Slice Algebra -/

/-- Allocation identifier (`Miri.Memory.AllocId` in `Miri/Memory/Identity.lean:12-16`). -/
structure AllocId where
  id : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Tree Borrows node tag (`Miri.Memory.BorTag` in `Miri/Memory/Identity.lean:35-39`). -/
structure BorTag where
  id : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Full Miri pointer provenance (`AllocId × BorTag`, matching
`Miri.Memory.Provenance.concrete` in `Miri/Memory/Identity.lean:62-67`). -/
structure Provenance where
  allocId : AllocId
  tag : BorTag
  deriving DecidableEq, Repr, Inhabited

/-- Per-byte pointer provenance fragment (`Miri/Memory/ProvenanceMap.lean:17-21`)
tracking both `Provenance` and which byte index `0..7` of the 8-byte pointer
this byte originates from, preventing forged partial-pointer overwrites. -/
structure ByteProvFrag where
  prov : Provenance
  byteIdx : UInt8
  deriving DecidableEq, Repr, Inhabited

/-- Unified per-byte memory cell combining `Miri/Memory/Allocation.lean:164-174`
(`rawBytes : Array UInt8`), `Miri/Memory/InitMask.lean` (`InitMask`), and
`Miri/Memory/ProvenanceMap.lean:17-41` (`PointerFrag` / `ProvenanceMap`). -/
inductive AbsByte where
  | uninit
  | init (byte : UInt8) (frag : Option ByteProvFrag)
  deriving DecidableEq, Repr, Inhabited

/-- Read a contiguous slice of `sz` elements starting at `off`. -/
def readSlice (xs : List α) (off sz : Nat) : List α :=
  (xs.drop off).take sz

/-- Overwrite a contiguous slice starting at `off` with `val`. -/
def writeSlice (xs : List α) (off : Nat) (val : List α) : List α :=
  xs.take off ++ val ++ xs.drop (off + val.length)

theorem drop_append_of_le_length :
    ∀ {xs ys : List α} {n : Nat}, n ≤ xs.length →
      (xs ++ ys).drop n = xs.drop n ++ ys
  | _, _, 0, _ => rfl
  | [], _, _ + 1, h => by simp at h
  | _ :: xs, ys, n + 1, h => by
      simp only [List.cons_append, List.drop_succ_cons]
      exact drop_append_of_le_length (by simp at h; omega)

theorem drop_append_of_ge_length :
    ∀ {xs ys : List α} {n : Nat}, xs.length ≤ n →
      (xs ++ ys).drop n = ys.drop (n - xs.length)
  | [], ys, n, _ => by simp
  | _ :: _, _, 0, h => by simp at h
  | _ :: xs, ys, n + 1, h => by
      simp only [List.cons_append, List.drop_succ_cons, List.length_cons, Nat.succ_sub_succ_eq_sub]
      exact drop_append_of_ge_length (by simp at h; omega)

theorem take_append_of_le_length :
    ∀ {xs ys : List α} {n : Nat}, n ≤ xs.length →
      (xs ++ ys).take n = xs.take n
  | _, _, 0, _ => rfl
  | [], _, _ + 1, h => by simp at h
  | x :: xs, ys, n + 1, h => by
      simp only [List.cons_append, List.take_succ_cons]
      exact congrArg (x :: ·) (take_append_of_le_length (by simp at h; omega))

theorem length_take_of_le {xs : List α} {n : Nat} (h : n ≤ xs.length) :
    (xs.take n).length = n := by
  rw [List.length_take]
  omega

theorem take_all_of_eq {xs : List α} {n : Nat} (h : xs.length = n) :
    xs.take n = xs := by
  subst h
  exact List.take_length

theorem writeSlice_length (xs : List α) (off : Nat) (val : List α)
    (h : off + val.length ≤ xs.length) :
    (writeSlice xs off val).length = xs.length := by
  unfold writeSlice
  rw [List.length_append, List.length_append, List.length_take, List.length_drop]
  omega

theorem readSlice_length (xs : List α) (off sz : Nat)
    (h : off + sz ≤ xs.length) :
    (readSlice xs off sz).length = sz := by
  unfold readSlice
  rw [List.length_take, List.length_drop]
  omega

/-- Slice lens law 1: reading back a written slice of length `sz` at the same
offset returns `val` in $O(1)$ without inspecting individual elements. -/
theorem readSlice_writeSlice_same (xs : List α) (off : Nat) (val : List α) (sz : Nat)
    (h_len : val.length = sz)
    (h_bounds : off + sz ≤ xs.length) :
    readSlice (writeSlice xs off val) off sz = val := by
  unfold readSlice writeSlice
  rw [List.append_assoc]
  have h_take_len : (xs.take off).length = off := length_take_of_le (by omega)
  rw [drop_append_of_ge_length (by omega)]
  have h_sub : off - (xs.take off).length = 0 := by omega
  rw [h_sub, List.drop_zero]
  rw [take_append_of_le_length (by omega)]
  exact take_all_of_eq h_len

theorem take_take_of_le :
    ∀ (xs : List α) (m n : Nat), m ≤ n → (xs.take n).take m = xs.take m
  | _, 0, _, _ => rfl
  | _, _ + 1, 0, h => by omega
  | [], _ + 1, _ + 1, _ => rfl
  | x :: xs, m + 1, n + 1, h => by
      simp only [List.take_succ_cons]
      exact congrArg (x :: ·) (take_take_of_le xs m n (by omega))

theorem drop_take_comm :
    ∀ (xs : List α) (d t : Nat), (xs.take (d + t)).drop d = (xs.drop d).take t
  | xs, 0, t => by simp
  | [], d + 1, t => by simp
  | _ :: xs, d + 1, t => by
      simp only [Nat.succ_add, List.take_succ_cons, List.drop_succ_cons]
      exact drop_take_comm xs d t

theorem drop_drop_add :
    ∀ (xs : List α) (a b : Nat), (xs.drop a).drop b = xs.drop (a + b)
  | xs, 0, b => by simp
  | [], a + 1, b => by simp
  | _ :: xs, a + 1, b => by
      simp only [List.drop_succ_cons, Nat.succ_add]
      exact drop_drop_add xs a b

/-- Slice lens law 2: writing at `[off₁, off₁ + val.length)` preserves
`readSlice` at any disjoint interval `[off₂, off₂ + sz₂)`. -/
theorem readSlice_writeSlice_disjoint (xs : List α) (off₁ : Nat) (val : List α)
    (off₂ sz₂ : Nat)
    (h_b1 : off₁ + val.length ≤ xs.length)
    (h_disj : off₁ + val.length ≤ off₂ ∨ off₂ + sz₂ ≤ off₁) :
    readSlice (writeSlice xs off₁ val) off₂ sz₂ = readSlice xs off₂ sz₂ := by
  unfold readSlice writeSlice
  have h_take_len : (xs.take off₁).length = off₁ := length_take_of_le (by omega)
  have h_prefix_len : (xs.take off₁ ++ val).length = off₁ + val.length := by
    rw [List.length_append, h_take_len]
  rcases h_disj with h_right | h_left
  · rw [drop_append_of_ge_length (by omega)]
    rw [h_prefix_len]
    rw [drop_drop_add]
    have h_add : off₁ + val.length + (off₂ - (off₁ + val.length)) = off₂ := by omega
    rw [h_add]
  · rw [List.append_assoc]
    rw [drop_append_of_le_length (by omega)]
    have h_drop_take_len : ((xs.take off₁).drop off₂).length = off₁ - off₂ := by
      rw [List.length_drop, h_take_len]
    rw [take_append_of_le_length (by omega)]
    have h_split : xs.take off₁ = (xs.take (off₂ + (off₁ - off₂))) := by
      congr 1; omega
    rw [h_split, drop_take_comm]
    exact take_take_of_le (xs.drop off₂) sz₂ (off₁ - off₂) (by omega)

/-! ## Section 2: `LayoutCodec` (`UInt32`, `UInt64`, `ThinPtr`, `pairCodec`) and `TransmuteAs` -/

/-- Well-formed byte codec for a Rust type `α` with fixed byte `size` and `align`. -/
structure LayoutCodec (α : Type) where
  size : Nat
  align : Nat
  align_pos : 0 < align
  encode : α → List AbsByte
  decode : List AbsByte → Option α
  encode_length : ∀ v : α, (encode v).length = size
  decode_encode : ∀ v : α, decode (encode v) = some v

def packU32 (b0 b1 b2 b3 : UInt8) : UInt32 :=
  UInt32.ofNat (b0.toNat + b1.toNat * 256 + b2.toNat * 65536 + b3.toNat * 16777216)

theorem packU32_extract (v : UInt32) :
    packU32 (v >>> 0).toUInt8 (v >>> 8).toUInt8 (v >>> 16).toUInt8 (v >>> 24).toUInt8 = v := by
  have hv : v.toNat < 4294967296 := v.toNat_lt
  apply UInt32.toNat_inj.mp
  simp only [packU32, UInt32.toUInt8, Nat.toUInt8, UInt8.toNat_ofNat',
    UInt32.toNat_shiftRight, UInt32.toNat_ofNat']
  change ((v.toNat >>> 0) % 256 + (v.toNat >>> 8) % 256 * 256 +
    (v.toNat >>> 16) % 256 * 65536 + (v.toNat >>> 24) % 256 * 16777216) % 4294967296 = v.toNat
  simp only [Nat.shiftRight_eq_div_pow]
  omega

def encodeU32LE (v : UInt32) : List AbsByte :=
  [ .init (v >>> 0).toUInt8 none
  , .init (v >>> 8).toUInt8 none
  , .init (v >>> 16).toUInt8 none
  , .init (v >>> 24).toUInt8 none ]

def decodeU32LE : List AbsByte → Option UInt32
  | [.init b0 none, .init b1 none, .init b2 none, .init b3 none] =>
    some (packU32 b0 b1 b2 b3)
  | _ => none

theorem decodeU32LE_encodeU32LE (v : UInt32) :
    decodeU32LE (encodeU32LE v) = some v := by
  simp only [encodeU32LE, decodeU32LE, Option.some.injEq]
  exact packU32_extract v

def u32Codec : LayoutCodec UInt32 where
  size := 4
  align := 4
  align_pos := by decide
  encode := encodeU32LE
  decode := decodeU32LE
  encode_length := fun _ => rfl
  decode_encode := decodeU32LE_encodeU32LE

def packU64 (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) : UInt64 :=
  UInt64.ofNat
    (b0.toNat + b1.toNat * 256 + b2.toNat * 65536 + b3.toNat * 16777216 +
     b4.toNat * 4294967296 + b5.toNat * 1099511627776 +
     b6.toNat * 281474976710656 + b7.toNat * 72057594037927936)

theorem packU64_extract (v : UInt64) :
    packU64 (v >>> 0).toUInt8 (v >>> 8).toUInt8 (v >>> 16).toUInt8 (v >>> 24).toUInt8
            (v >>> 32).toUInt8 (v >>> 40).toUInt8 (v >>> 48).toUInt8 (v >>> 56).toUInt8 = v := by
  have hv : v.toNat < 18446744073709551616 := v.toNat_lt
  apply UInt64.toNat_inj.mp
  simp only [packU64, UInt64.toUInt8, Nat.toUInt8, UInt8.toNat_ofNat',
    UInt64.toNat_shiftRight, UInt64.toNat_ofNat']
  change ((v.toNat >>> 0) % 256 + (v.toNat >>> 8) % 256 * 256 +
    (v.toNat >>> 16) % 256 * 65536 + (v.toNat >>> 24) % 256 * 16777216 +
    (v.toNat >>> 32) % 256 * 4294967296 + (v.toNat >>> 40) % 256 * 1099511627776 +
    (v.toNat >>> 48) % 256 * 281474976710656 + (v.toNat >>> 56) % 256 * 72057594037927936) %
    18446744073709551616 = v.toNat
  simp only [Nat.shiftRight_eq_div_pow]
  omega

def encodeU64LE (v : UInt64) : List AbsByte :=
  [ .init (v >>> 0).toUInt8 none
  , .init (v >>> 8).toUInt8 none
  , .init (v >>> 16).toUInt8 none
  , .init (v >>> 24).toUInt8 none
  , .init (v >>> 32).toUInt8 none
  , .init (v >>> 40).toUInt8 none
  , .init (v >>> 48).toUInt8 none
  , .init (v >>> 56).toUInt8 none ]

def decodeU64LE : List AbsByte → Option UInt64
  | [ .init b0 none, .init b1 none, .init b2 none, .init b3 none
    , .init b4 none, .init b5 none, .init b6 none, .init b7 none ] =>
    some (packU64 b0 b1 b2 b3 b4 b5 b6 b7)
  | _ => none

theorem decodeU64LE_encodeU64LE (v : UInt64) :
    decodeU64LE (encodeU64LE v) = some v := by
  simp only [encodeU64LE, decodeU64LE, Option.some.injEq]
  exact packU64_extract v

def u64Codec : LayoutCodec UInt64 where
  size := 8
  align := 8
  align_pos := by decide
  encode := encodeU64LE
  decode := decodeU64LE
  encode_length := fun _ => rfl
  decode_encode := decodeU64LE_encodeU64LE

/-- Thin pointer value with optional Miri provenance (`AllocId × BorTag`). -/
structure ThinPtr where
  addr : UInt64
  prov : Option Provenance
  deriving DecidableEq, Repr, Inhabited

def fragAt (prov : Option Provenance) (idx : UInt8) : Option ByteProvFrag :=
  match prov with
  | none => none
  | some p => some ⟨p, idx⟩

def encodePtrLE (p : ThinPtr) : List AbsByte :=
  [ .init (p.addr >>> 0).toUInt8 (fragAt p.prov 0)
  , .init (p.addr >>> 8).toUInt8 (fragAt p.prov 1)
  , .init (p.addr >>> 16).toUInt8 (fragAt p.prov 2)
  , .init (p.addr >>> 24).toUInt8 (fragAt p.prov 3)
  , .init (p.addr >>> 32).toUInt8 (fragAt p.prov 4)
  , .init (p.addr >>> 40).toUInt8 (fragAt p.prov 5)
  , .init (p.addr >>> 48).toUInt8 (fragAt p.prov 6)
  , .init (p.addr >>> 56).toUInt8 (fragAt p.prov 7) ]

def decodePtrProv :
    Option ByteProvFrag → Option ByteProvFrag → Option ByteProvFrag → Option ByteProvFrag →
    Option ByteProvFrag → Option ByteProvFrag → Option ByteProvFrag → Option ByteProvFrag →
    Option (Option Provenance)
  | none, none, none, none, none, none, none, none => some none
  | some ⟨p0, 0⟩, some ⟨p1, 1⟩, some ⟨p2, 2⟩, some ⟨p3, 3⟩,
    some ⟨p4, 4⟩, some ⟨p5, 5⟩, some ⟨p6, 6⟩, some ⟨p7, 7⟩ =>
    if p0 == p1 && p0 == p2 && p0 == p3 && p0 == p4 && p0 == p5 && p0 == p6 && p0 == p7 then
      some (some p0)
    else
      none
  | _, _, _, _, _, _, _, _ => none

def decodePtrLE : List AbsByte → Option ThinPtr
  | [ .init b0 f0, .init b1 f1, .init b2 f2, .init b3 f3
    , .init b4 f4, .init b5 f5, .init b6 f6, .init b7 f7 ] =>
    match decodePtrProv f0 f1 f2 f3 f4 f5 f6 f7 with
    | none => none
    | some prov =>
      some ⟨packU64 b0 b1 b2 b3 b4 b5 b6 b7, prov⟩
  | _ => none

theorem decodePtrLE_encodePtrLE (p : ThinPtr) :
    decodePtrLE (encodePtrLE p) = some p := by
  rcases p with ⟨addr, prov⟩
  have h_addr := packU64_extract addr
  cases prov with
  | none =>
    dsimp only [encodePtrLE, decodePtrLE, fragAt, decodePtrProv]
    rw [h_addr]
  | some pr =>
    have h_prov : decodePtrProv (some ⟨pr, 0⟩) (some ⟨pr, 1⟩) (some ⟨pr, 2⟩) (some ⟨pr, 3⟩)
        (some ⟨pr, 4⟩) (some ⟨pr, 5⟩) (some ⟨pr, 6⟩) (some ⟨pr, 7⟩) = some (some pr) := by
      simp [decodePtrProv]
    dsimp only [encodePtrLE, decodePtrLE, fragAt]
    rw [h_prov]
    dsimp only
    rw [h_addr]

def ptrCodec : LayoutCodec ThinPtr where
  size := 8
  align := 8
  align_pos := by decide
  encode := encodePtrLE
  decode := decodePtrLE
  encode_length := fun _ => rfl
  decode_encode := decodePtrLE_encodePtrLE

/-- Product / struct codec concatenating two adjacent fields. -/
def pairCodec (c1 : LayoutCodec α) (c2 : LayoutCodec β) : LayoutCodec (α × β) where
  size := c1.size + c2.size
  align := if c1.align ≤ c2.align then c2.align else c1.align
  align_pos := by
    have h1 := c1.align_pos
    have h2 := c2.align_pos
    split <;> omega
  encode := fun (a, b) => c1.encode a ++ c2.encode b
  decode := fun bs =>
    match c1.decode (bs.take c1.size), c2.decode (bs.drop c1.size) with
    | some a, some b => some (a, b)
    | _, _ => none
  encode_length := fun (a, b) => by
    simp [List.length_append, c1.encode_length, c2.encode_length]
  decode_encode := fun (a, b) => by
    dsimp only
    have h1 : (c1.encode a).length = c1.size := c1.encode_length a
    rw [take_append_of_le_length (by omega), take_all_of_eq h1]
    rw [drop_append_of_ge_length (by omega)]
    have hsub : c1.size - (c1.encode a).length = 0 := by omega
    rw [hsub, List.drop_zero, c1.decode_encode, c2.decode_encode]

/-- Reinterpretation (`transmute`) relation between two codecs: `v1 : α` and
`v2 : β` have identical abstract byte encodings (`c1.encode v1 = c2.encode v2`). -/
def TransmuteAs (c1 : LayoutCodec α) (v1 : α) (c2 : LayoutCodec β) (v2 : β) : Prop :=
  c1.encode v1 = c2.encode v2

def combineU32ToU64 (lo hi : UInt32) : UInt64 :=
  UInt64.ofNat (lo.toNat + hi.toNat * 4294967296)

/-- Concrete transmutation theorem: two adjacent little-endian `UInt32` values
`(lo, hi)` have the exact same 8-byte `AbsByte` representation as
`combineU32ToU64 lo hi : UInt64`. -/
theorem transmute_u32_pair_u64 (lo hi : UInt32) :
    TransmuteAs (pairCodec u32Codec u32Codec) (lo, hi)
      u64Codec (combineU32ToU64 lo hi) := by
  unfold TransmuteAs pairCodec u32Codec u64Codec encodeU32LE encodeU64LE
  dsimp only [List.append]
  have hlo : lo.toNat < 4294967296 := lo.toNat_lt
  have hhi : hi.toNat < 4294967296 := hi.toNat_lt
  have b0 : (lo >>> 0).toUInt8 = ((combineU32ToU64 lo hi) >>> 0).toUInt8 := by
    apply UInt8.toNat_inj.mp; simp only [combineU32ToU64, UInt32.toUInt8, UInt64.toUInt8, Nat.toUInt8, UInt8.toNat_ofNat', UInt32.toNat_shiftRight, UInt64.toNat_shiftRight, UInt64.toNat_ofNat']
    change (lo.toNat >>> 0) % 256 = (((lo.toNat + hi.toNat * 4294967296) % 18446744073709551616) >>> 0) % 256; simp only [Nat.shiftRight_eq_div_pow]; omega
  have b1 : (lo >>> 8).toUInt8 = ((combineU32ToU64 lo hi) >>> 8).toUInt8 := by
    apply UInt8.toNat_inj.mp; simp only [combineU32ToU64, UInt32.toUInt8, UInt64.toUInt8, Nat.toUInt8, UInt8.toNat_ofNat', UInt32.toNat_shiftRight, UInt64.toNat_shiftRight, UInt64.toNat_ofNat']
    change (lo.toNat >>> 8) % 256 = (((lo.toNat + hi.toNat * 4294967296) % 18446744073709551616) >>> 8) % 256; simp only [Nat.shiftRight_eq_div_pow]; omega
  have b2 : (lo >>> 16).toUInt8 = ((combineU32ToU64 lo hi) >>> 16).toUInt8 := by
    apply UInt8.toNat_inj.mp; simp only [combineU32ToU64, UInt32.toUInt8, UInt64.toUInt8, Nat.toUInt8, UInt8.toNat_ofNat', UInt32.toNat_shiftRight, UInt64.toNat_shiftRight, UInt64.toNat_ofNat']
    change (lo.toNat >>> 16) % 256 = (((lo.toNat + hi.toNat * 4294967296) % 18446744073709551616) >>> 16) % 256; simp only [Nat.shiftRight_eq_div_pow]; omega
  have b3 : (lo >>> 24).toUInt8 = ((combineU32ToU64 lo hi) >>> 24).toUInt8 := by
    apply UInt8.toNat_inj.mp; simp only [combineU32ToU64, UInt32.toUInt8, UInt64.toUInt8, Nat.toUInt8, UInt8.toNat_ofNat', UInt32.toNat_shiftRight, UInt64.toNat_shiftRight, UInt64.toNat_ofNat']
    change (lo.toNat >>> 24) % 256 = (((lo.toNat + hi.toNat * 4294967296) % 18446744073709551616) >>> 24) % 256; simp only [Nat.shiftRight_eq_div_pow]; omega
  have b4 : (hi >>> 0).toUInt8 = ((combineU32ToU64 lo hi) >>> 32).toUInt8 := by
    apply UInt8.toNat_inj.mp; simp only [combineU32ToU64, UInt32.toUInt8, UInt64.toUInt8, Nat.toUInt8, UInt8.toNat_ofNat', UInt32.toNat_shiftRight, UInt64.toNat_shiftRight, UInt64.toNat_ofNat']
    change (hi.toNat >>> 0) % 256 = (((lo.toNat + hi.toNat * 4294967296) % 18446744073709551616) >>> 32) % 256; simp only [Nat.shiftRight_eq_div_pow]; omega
  have b5 : (hi >>> 8).toUInt8 = ((combineU32ToU64 lo hi) >>> 40).toUInt8 := by
    apply UInt8.toNat_inj.mp; simp only [combineU32ToU64, UInt32.toUInt8, UInt64.toUInt8, Nat.toUInt8, UInt8.toNat_ofNat', UInt32.toNat_shiftRight, UInt64.toNat_shiftRight, UInt64.toNat_ofNat']
    change (hi.toNat >>> 8) % 256 = (((lo.toNat + hi.toNat * 4294967296) % 18446744073709551616) >>> 40) % 256; simp only [Nat.shiftRight_eq_div_pow]; omega
  have b6 : (hi >>> 16).toUInt8 = ((combineU32ToU64 lo hi) >>> 48).toUInt8 := by
    apply UInt8.toNat_inj.mp; simp only [combineU32ToU64, UInt32.toUInt8, UInt64.toUInt8, Nat.toUInt8, UInt8.toNat_ofNat', UInt32.toNat_shiftRight, UInt64.toNat_shiftRight, UInt64.toNat_ofNat']
    change (hi.toNat >>> 16) % 256 = (((lo.toNat + hi.toNat * 4294967296) % 18446744073709551616) >>> 48) % 256; simp only [Nat.shiftRight_eq_div_pow]; omega
  have b7 : (hi >>> 24).toUInt8 = ((combineU32ToU64 lo hi) >>> 56).toUInt8 := by
    apply UInt8.toNat_inj.mp; simp only [combineU32ToU64, UInt32.toUInt8, UInt64.toUInt8, Nat.toUInt8, UInt8.toNat_ofNat', UInt32.toNat_shiftRight, UInt64.toNat_shiftRight, UInt64.toNat_ofNat']
    change (hi.toNat >>> 24) % 256 = (((lo.toNat + hi.toNat * 4294967296) % 18446744073709551616) >>> 56) % 256; simp only [Nat.shiftRight_eq_div_pow]; omega
  rw [b0, b1, b2, b3, b4, b5, b6, b7]
  rfl

/-! ## Section 3: 5-State Tree Borrows (`Permission`, `LocationState`, `BorrowTree`, Protector Release, and `FootprintAt`) -/

/-- The 5-constructor Tree Borrows permission automaton:
- `Reserved (tyIsFreeze : Bool) (conflicted : Bool)` (collapsing `lean-miri`'s
  `ReservedFrz (conflicted : Bool)` and `ReservedIM` into one constructor
  while preserving all 6 reachable states in `Miri/TreeBorrows/Permissions.lean:19-32`),
- `Active` (`Unique` in `Permissions.lean:27`), `Frozen`, `Cell`, `Disabled`. -/
inductive Permission where
  | Reserved (tyIsFreeze : Bool) (conflicted : Bool)
  | Active
  | Frozen
  | Cell
  | Disabled
  deriving DecidableEq, Repr, Inhabited

/-- Isomorphic copy of the 6-constructor `Miri.TreeBorrows.Permission`
(`Miri/TreeBorrows/Permissions.lean:19-32` at commit
`c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`, naming `Unique` as `Active`) to
prove the roundtrip mapping with the 5-constructor `Permission`. -/
inductive LeanMiriPermission where
  | Cell
  | ReservedFrz (conflicted : Bool)
  | ReservedIm
  | Active
  | Frozen
  | Disabled
  deriving DecidableEq, Repr, Inhabited

def LeanMiriPermission.toPermission : LeanMiriPermission → Permission
  | .Cell => .Cell
  | .ReservedFrz c => .Reserved true c
  | .ReservedIm => .Reserved false false
  | .Active => .Active
  | .Frozen => .Frozen
  | .Disabled => .Disabled

def Permission.toLeanMiriPermission : Permission → LeanMiriPermission
  | .Cell => .Cell
  | .Reserved true c => .ReservedFrz c
  | .Reserved false _ => .ReservedIm
  | .Active => .Active
  | .Frozen => .Frozen
  | .Disabled => .Disabled

theorem leanMiriPermission_roundtrip (p : LeanMiriPermission) :
    p.toPermission.toLeanMiriPermission = p := by
  cases p <;> rfl

inductive AccessKind where
  | Read
  | Write
  deriving DecidableEq, Repr, Inhabited

inductive AccessRelatedness where
  | LocalAccess
  | ForeignAccess
  deriving DecidableEq, Repr, Inhabited

/-- Transition rules matching `Miri/TreeBorrows/Permissions.lean:62-112` (mapping
both `.UndefinedBehavior` and `.ImpossibleProtectedReservedIM` to `none`). -/
def childRead (state : Permission) : Option Permission :=
  match state with
  | .Disabled => none
  | readable => some readable

def foreignRead (state : Permission) (isProtected : Bool) : Option Permission :=
  match state with
  | .Cell => some .Cell
  | .Frozen => some .Frozen
  | .Disabled => some .Disabled
  | .Reserved true c => some (.Reserved true (if isProtected then true else c))
  | .Reserved false _ => if isProtected then none else some (.Reserved false false)
  | .Active => some (if isProtected then .Disabled else .Frozen)

def childWrite (state : Permission) (isProtected : Bool) : Option Permission :=
  match state with
  | .Cell => some .Cell
  | .Reserved true true => if isProtected then none else some .Active
  | .Reserved true false => some .Active
  | .Reserved false _ => if isProtected then none else some .Active
  | .Active => some .Active
  | .Frozen => none
  | .Disabled => none

def foreignWrite (state : Permission) (isProtected : Bool) : Option Permission :=
  match state with
  | .Cell => some .Cell
  | .Reserved false _ => if isProtected then none else some (.Reserved false false)
  | _ => some .Disabled

def performPermAccess (kind : AccessKind) (rel : AccessRelatedness)
    (old : Permission) (isProtected : Bool) : Option Permission :=
  match kind, rel with
  | .Read, .LocalAccess => childRead old
  | .Read, .ForeignAccess => foreignRead old isProtected
  | .Write, .LocalAccess => childWrite old isProtected
  | .Write, .ForeignAccess => foreignWrite old isProtected

/-- Implicit access kind emitted on function-exit protector release
(`Permission.associatedAccess` in `Miri/TreeBorrows/Permissions.lean:268-271`). -/
def Permission.associatedAccess : Permission → Option AccessKind
  | .Cell => none
  | .Active => some .Write
  | _ => some .Read

/-- Per-byte node state (`Miri/TreeBorrows/LocationState.lean:36-40`). -/
structure LocationState where
  permission : Permission
  accessed : Bool
  deriving DecidableEq, Repr, Inhabited

/-- Perform an access on a single location state (`LocationState.performAccess` in
`Miri/TreeBorrows/LocationState.lean:128-149`), including the protector trap
preventing an accessed protected location from becoming `Disabled`. -/
def LocationState.performAccess (st : LocationState) (kind : AccessKind)
    (rel : AccessRelatedness) (isProtected : Bool) : Option LocationState :=
  match performPermAccess kind rel st.permission isProtected with
  | none => none
  | some nextPerm =>
    let nextAccessed := st.accessed || (rel == .LocalAccess)
    if isProtected && nextAccessed && nextPerm == .Disabled then
      none
    else
      some { permission := nextPerm, accessed := nextAccessed }

/-- Implicit access kind emitted by a location when its protector is released at
function exit (`Miri/TreeBorrows/TreeState.lean:1049-1054`):
only initialized (`accessed = true`) locations emit their permission's
`associatedAccess`. -/
def LocationState.protectorEndAccess (st : LocationState) : Option AccessKind :=
  if st.accessed then st.permission.associatedAccess else none

def locWritePerm (rel : AccessRelatedness) (isProt : Bool) (st : LocationState) : Bool :=
  match rel with
  | .LocalAccess =>
    match st.permission with
    | .Active | .Cell | .Reserved true false => true
    | .Reserved true true | .Reserved false _ => !isProt
    | .Frozen | .Disabled => false
  | .ForeignAccess =>
    match st.permission with
    | .Cell => true
    | .Reserved false _ => !isProt
    | _ => !(isProt && st.accessed)

def locIsActiveOrCell (st : LocationState) : Bool :=
  st.accessed && (st.permission == .Active || st.permission == .Cell)

def locPostWriteActive (rel : AccessRelatedness) (st : LocationState) : Bool :=
  match rel with
  | .LocalAccess => locIsActiveOrCell st
  | .ForeignAccess => true

theorem locWritePerm_step (rel : AccessRelatedness) (isProt : Bool) (st : LocationState)
    (h : locWritePerm rel isProt st = true) :
    ∃ st', st.performAccess .Write rel isProt = some st' ∧
      locWritePerm rel isProt st' = true ∧
      locPostWriteActive rel st' = true := by
  rcases st with ⟨perm, acc⟩
  cases rel <;> cases isProt <;> cases acc <;> cases perm <;>
    try (rename_i tyIsFrz conf; cases tyIsFrz <;> cases conf)
  all_goals
    first | contradiction | exact ⟨_, rfl, rfl, rfl⟩

def locIsSharedCompatible (isProt : Bool) (st : LocationState) : Bool :=
  match st.permission with
  | .Frozen | .Cell | .Reserved true _ => true
  | .Reserved false _ => !isProt
  | .Active | .Disabled => false

theorem locIsSharedCompatible_preserved_by_any_read (otherRel : AccessRelatedness)
    (isProt : Bool) (st : LocationState) (h : locIsSharedCompatible isProt st = true) :
    ∃ st', st.performAccess .Read otherRel isProt = some st' ∧
      locIsSharedCompatible isProt st' = true := by
  rcases st with ⟨perm, acc⟩
  cases otherRel <;> cases isProt <;> cases acc <;> cases perm <;>
    try (rename_i tyIsFrz conf; cases tyIsFrz <;> cases conf)
  all_goals
    first | contradiction | exact ⟨_, rfl, rfl⟩

/-! ### `BorrowTree`, Range Accesses, and Two-Stage Protector Release -/

def hasTag : List BorTag → BorTag → Bool
  | [], _ => false
  | t :: ts, q => (t == q) || hasTag ts q

def removeTag : List BorTag → BorTag → List BorTag
  | [], _ => []
  | t :: ts, q => if t == q then removeTag ts q else t :: removeTag ts q

def allBool (p : α → Bool) : List α → Bool
  | [] => true
  | x :: xs => p x && allBool p xs

def mapOption (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | x :: xs =>
    match f x, mapOption f xs with
    | some y, some ys => some (y :: ys)
    | _, _ => none

theorem mapOption_of_allBool {f : α → Option α} {p q : α → Bool}
    (h_step : ∀ x, p x = true → ∃ y, f x = some y ∧ p y = true ∧ q y = true) :
    ∀ (xs : List α), allBool p xs = true →
      ∃ ys, mapOption f xs = some ys ∧ ys.length = xs.length ∧
        allBool p ys = true ∧ allBool q ys = true
  | [], _ => ⟨[], rfl, rfl, rfl, rfl⟩
  | x :: xs, h => by
    simp only [allBool, Bool.and_eq_true] at h
    obtain ⟨y, hy, hpy, hqy⟩ := h_step x h.1
    obtain ⟨ys, hys, hlen, hpys, hqys⟩ := mapOption_of_allBool h_step xs h.2
    refine ⟨y :: ys, ?_, ?_, ?_, ?_⟩
    · simp [mapOption, hy, hys]
    · simp [hlen]
    · simp [allBool, hpy, hpys]
    · simp [allBool, hqy, hqys]

/-- A node in the flattened allocation `BorrowTree`:
- `tag`: unique `BorTag` of this pointer/reborrow,
- `ancestors`: list of ancestor tags on the path from the root to `tag`
  (including `tag` itself, so `nodeRel anc n.tag = .LocalAccess` iff `n.tag` is
  an ancestor of the accessed `tag`, matching `Miri/TreeBorrows/Traversal.lean:45-112`),
- `locs`: per-byte `LocationState` list across the allocation. -/
structure TreeNode where
  tag : BorTag
  ancestors : List BorTag
  locs : List LocationState
  deriving DecidableEq, Repr, Inhabited

structure BorrowTree where
  nodes : List TreeNode
  deriving DecidableEq, Repr, Inhabited

abbrev ProtectedTags := List BorTag

def findAncestorsNodes : List TreeNode → BorTag → Option (List BorTag)
  | [], _ => none
  | n :: ns, tag => if n.tag == tag then some n.ancestors else findAncestorsNodes ns tag

def BorrowTree.findAncestors (tree : BorrowTree) (tag : BorTag) : Option (List BorTag) :=
  findAncestorsNodes tree.nodes tag

def findNode : List TreeNode → BorTag → Option TreeNode
  | [], _ => none
  | n :: ns, tag => if n.tag == tag then some n else findNode ns tag

def nodeRel (anc : List BorTag) (t : BorTag) : AccessRelatedness :=
  if hasTag anc t then .LocalAccess else .ForeignAccess

def updateNodeRange (anc : List BorTag) (prot : ProtectedTags)
    (off sz : Nat) (kind : AccessKind) (n : TreeNode) : Option TreeNode :=
  if off + sz ≤ n.locs.length then
    match mapOption (fun st => st.performAccess kind (nodeRel anc n.tag) (hasTag prot n.tag))
        (readSlice n.locs off sz) with
    | some updatedSlice => some { n with locs := writeSlice n.locs off updatedSlice }
    | none => none
  else
    none

def BorrowTree.performAccessRange (tree : BorrowTree) (prot : ProtectedTags)
    (tag : BorTag) (off sz : Nat) (kind : AccessKind) : Option BorrowTree :=
  match tree.findAncestors tag with
  | none => none
  | some anc =>
    match mapOption (updateNodeRange anc prot off sz kind) tree.nodes with
    | some nodes' => some ⟨nodes'⟩
    | none => none

/-- Two-stage protector release matching `Miri.TreeBorrows.BorrowTree.releaseProtector`
(`Miri/TreeBorrows/TreeState.lean:1036-1070`) and `GlobalState.endCall`
(`Miri/TreeBorrows/GlobalState.lean:146-148`):
- **Stage 1 (`releaseProtectorStage1`)**: For a protected `tag` at offset `off`,
  if `tag`'s location state at `off` was accessed (`accessed = true`), perform
  the implicit foreign access (`Write` for `Active`, `Read` for `Reserved`/`Frozen`)
  on all foreign nodes (`nodeRel anc n.tag == .ForeignAccess`) while `tag` is
  still in `prot` (and leaves `LocalAccess` nodes unchanged, matching
  `ChildrenVisitMode.SkipChildrenOfAccessed` in `Miri/TreeBorrows/Traversal.lean:78-85`).
- **Stage 2 (`releaseProtectorStage2`)**: Remove `tag` from `prot`. -/
def updateNodeProtectorEndAt (anc : List BorTag) (prot : ProtectedTags)
    (off : Nat) (kind : AccessKind) (n : TreeNode) : Option TreeNode :=
  match nodeRel anc n.tag with
  | .LocalAccess => some n
  | .ForeignAccess => updateNodeRange anc prot off 1 kind n

def BorrowTree.releaseProtectorStage1At (tree : BorrowTree) (prot : ProtectedTags)
    (tag : BorTag) (off : Nat) : Option BorrowTree :=
  match findNode tree.nodes tag with
  | none => some tree
  | some tagNode =>
    match readSlice tagNode.locs off 1 with
    | [st] =>
      match st.protectorEndAccess with
      | none => some tree
      | some kind =>
        match mapOption (updateNodeProtectorEndAt tagNode.ancestors prot off kind) tree.nodes with
        | some nodes' => some ⟨nodes'⟩
        | none => none
    | _ => none

def releaseProtectorStage2 (prot : ProtectedTags) (tag : BorTag) : ProtectedTags :=
  removeTag prot tag

/-- Theorem verifying that an accessed `Active` location emits an implicit
`Write` access during Stage 1 protector release. -/
theorem releaseProtector_accessed_active_emits_write :
    (LocationState.mk .Active true).protectorEndAccess = some .Write := rfl

/-! ### `FootprintAt` (`HasUniqueWritePerm` / `HasSharedReadPerm`) and Foundational Theorems 3 & 4 -/

def nodeWritePerm (anc : List BorTag) (prot : ProtectedTags) (off sz : Nat) (n : TreeNode) : Bool :=
  decide (off + sz ≤ n.locs.length) &&
    allBool (locWritePerm (nodeRel anc n.tag) (hasTag prot n.tag)) (readSlice n.locs off sz)

def nodePostWriteActive (anc : List BorTag) (off sz : Nat) (n : TreeNode) : Bool :=
  decide (off + sz ≤ n.locs.length) &&
    allBool (locPostWriteActive (nodeRel anc n.tag)) (readSlice n.locs off sz)

theorem updateNodeRange_preserves_identity (anc : List BorTag) (prot : ProtectedTags)
    (off sz : Nat) (kind : AccessKind) (n n' : TreeNode)
    (h : updateNodeRange anc prot off sz kind n = some n') :
    n'.tag = n.tag ∧ n'.ancestors = n.ancestors := by
  unfold updateNodeRange at h
  by_cases hb : off + sz ≤ n.locs.length
  · simp only [hb, ↓reduceIte] at h
    cases hm : mapOption (fun st => st.performAccess kind (nodeRel anc n.tag) (hasTag prot n.tag))
        (readSlice n.locs off sz) with
    | none => rw [hm] at h; contradiction
    | some ys => rw [hm] at h; cases h; exact ⟨rfl, rfl⟩
  · simp only [hb, ↓reduceIte] at h; contradiction

theorem updateNodeRange_write_step (anc : List BorTag) (prot : ProtectedTags)
    (off sz : Nat) (n : TreeNode)
    (h : nodeWritePerm anc prot off sz n = true) :
    ∃ n', updateNodeRange anc prot off sz .Write n = some n' ∧
      nodeWritePerm anc prot off sz n' = true ∧
      nodePostWriteActive anc off sz n' = true := by
  unfold nodeWritePerm at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨h_bounds, h_all⟩
  obtain ⟨ys, hmap, hlen, hpys, hqys⟩ :=
    mapOption_of_allBool (locWritePerm_step (nodeRel anc n.tag) (hasTag prot n.tag))
      (readSlice n.locs off sz) h_all
  have h_slice_len : (readSlice n.locs off sz).length = sz := readSlice_length n.locs off sz h_bounds
  have h_ys_len : ys.length = sz := hlen.trans h_slice_len
  have h_new_len : (writeSlice n.locs off ys).length = n.locs.length :=
    writeSlice_length n.locs off ys (by omega)
  have h_new_slice : readSlice (writeSlice n.locs off ys) off sz = ys :=
    readSlice_writeSlice_same n.locs off ys sz h_ys_len h_bounds
  refine ⟨{ n with locs := writeSlice n.locs off ys }, ?_, ?_, ?_⟩
  · unfold updateNodeRange
    simp only [h_bounds, ↓reduceIte, hmap]
  · unfold nodeWritePerm
    simp only [h_new_len, h_bounds, decide_true, Bool.true_and, h_new_slice, hpys]
  · unfold nodePostWriteActive
    simp only [h_new_len, h_bounds, decide_true, Bool.true_and, h_new_slice, hqys]

/-- Decidable checker for `HasUniqueWritePerm` used at function entry on the
concrete initial `BorrowTree` topology. -/
def checkUniqueWritePerm (tree : BorrowTree) (prot : ProtectedTags) (tag : BorTag) (off sz : Nat) : Bool :=
  match tree.findAncestors tag with
  | none => false
  | some anc => hasTag anc tag && allBool (nodeWritePerm anc prot off sz) tree.nodes

/-- Propositional footprint invariant `HasUniqueWritePerm`. -/
def HasUniqueWritePerm (tree : BorrowTree) (prot : ProtectedTags) (tag : BorTag) (off sz : Nat) : Prop :=
  ∃ anc, tree.findAncestors tag = some anc ∧
    hasTag anc tag = true ∧
    allBool (nodeWritePerm anc prot off sz) tree.nodes = true

theorem checkUniqueWritePerm_sound (tree : BorrowTree) (prot : ProtectedTags)
    (tag : BorTag) (off sz : Nat)
    (h : checkUniqueWritePerm tree prot tag off sz = true) :
    HasUniqueWritePerm tree prot tag off sz := by
  unfold checkUniqueWritePerm at h
  cases hfind : tree.findAncestors tag with
  | none => rw [hfind] at h; contradiction
  | some anc =>
    rw [hfind] at h
    simp only [Bool.and_eq_true] at h
    exact ⟨anc, hfind, h.1, h.2⟩

theorem mapOption_preserves_findAncestors {f : TreeNode → Option TreeNode}
    (h_tag : ∀ n n', f n = some n' → n'.tag = n.tag ∧ n'.ancestors = n.ancestors) :
    ∀ (ns ns' : List TreeNode) (qTag : BorTag),
      mapOption f ns = some ns' →
      findAncestorsNodes ns' qTag = findAncestorsNodes ns qTag
  | [], _, _, h => by
    simp [mapOption] at h
    subst h
    rfl
  | n :: ns, ns', qTag, h => by
    unfold mapOption at h
    cases hf : f n with
    | none => rw [hf] at h; contradiction
    | some n' =>
      cases hms : mapOption f ns with
      | none => rw [hf, hms] at h; contradiction
      | some rest' =>
        rw [hf, hms] at h
        cases h
        obtain ⟨ht, ha⟩ := h_tag n n' hf
        simp only [findAncestorsNodes, ht, ha]
        split
        · rfl
        · exact mapOption_preserves_findAncestors h_tag ns rest' qTag hms

/-- **Foundational Theorem 3 (`footprintAt_preserve_local_write`)**:
Performing a local `Write` through `tag` on `[off, off + sz)` when
`HasUniqueWritePerm` holds succeeds without UB, sets `tag` and all its ancestors
to `Active` (`accessed := true`) on `[off, off + sz)`, and preserves
`HasUniqueWritePerm` for subsequent writes through `tag`. -/
theorem footprintAt_preserve_local_write (tree : BorrowTree) (prot : ProtectedTags)
    (tag : BorTag) (off sz : Nat)
    (h : HasUniqueWritePerm tree prot tag off sz) :
    ∃ tree' anc,
      tree.performAccessRange prot tag off sz .Write = some tree' ∧
      tree'.findAncestors tag = some anc ∧
      allBool (nodePostWriteActive anc off sz) tree'.nodes = true ∧
      HasUniqueWritePerm tree' prot tag off sz := by
  rcases h with ⟨anc, hfind, hanc_self, hall⟩
  obtain ⟨nodes', hmap, _, hw_nodes', ha_nodes'⟩ :=
    mapOption_of_allBool (updateNodeRange_write_step anc prot off sz) tree.nodes hall
  have hfind' : findAncestorsNodes nodes' tag = some anc := by
    rw [mapOption_preserves_findAncestors
      (updateNodeRange_preserves_identity anc prot off sz .Write) tree.nodes nodes' tag hmap]
    exact hfind
  refine ⟨⟨nodes'⟩, anc, ?_, hfind', ha_nodes', ⟨anc, hfind', hanc_self, hw_nodes'⟩⟩
  unfold BorrowTree.performAccessRange
  simp [hfind, hmap]

theorem mapOption_length_eq {f : α → Option β} :
    ∀ (xs : List α) (ys : List β), mapOption f xs = some ys → ys.length = xs.length
  | [], _, h => by simp [mapOption] at h; subst h; rfl
  | x :: xs, _, h => by
    unfold mapOption at h
    cases hx : f x with
    | none => rw [hx] at h; contradiction
    | some y =>
      cases hxs : mapOption f xs with
      | none => rw [hx, hxs] at h; contradiction
      | some ys' =>
        rw [hx, hxs] at h
        cases h
        simp [mapOption_length_eq xs ys' hxs]

theorem updateNodeRange_preserves_disjoint_nodeWritePerm
    (anc₁ anc₂ : List BorTag) (prot : ProtectedTags)
    (off₁ sz₁ off₂ sz₂ : Nat) (kind : AccessKind) (n n' : TreeNode)
    (h_disj : off₁ + sz₁ ≤ off₂ ∨ off₂ + sz₂ ≤ off₁)
    (h_upd : updateNodeRange anc₁ prot off₁ sz₁ kind n = some n')
    (h_perm : nodeWritePerm anc₂ prot off₂ sz₂ n = true) :
    nodeWritePerm anc₂ prot off₂ sz₂ n' = true := by
  unfold updateNodeRange at h_upd
  by_cases hb1 : off₁ + sz₁ ≤ n.locs.length
  · simp only [hb1, ↓reduceIte] at h_upd
    cases hm : mapOption (fun st => st.performAccess kind (nodeRel anc₁ n.tag) (hasTag prot n.tag))
        (readSlice n.locs off₁ sz₁) with
    | none => rw [hm] at h_upd; contradiction
    | some ys =>
      rw [hm] at h_upd
      cases h_upd
      have h_ys_len : ys.length = sz₁ :=
        (mapOption_length_eq _ _ hm).trans (readSlice_length n.locs off₁ sz₁ hb1)
      have h_len_eq : (writeSlice n.locs off₁ ys).length = n.locs.length :=
        writeSlice_length n.locs off₁ ys (by omega)
      have h_slice_eq : readSlice (writeSlice n.locs off₁ ys) off₂ sz₂ = readSlice n.locs off₂ sz₂ :=
        readSlice_writeSlice_disjoint n.locs off₁ ys off₂ sz₂ (by omega) (by omega)
      unfold nodeWritePerm at h_perm ⊢
      simp only [h_len_eq, h_slice_eq]
      exact h_perm
  · simp only [hb1, ↓reduceIte] at h_upd; contradiction

theorem allBool_preserved_of_mapOption {f : α → Option α} {p : α → Bool}
    (h_pres : ∀ x y, f x = some y → p x = true → p y = true) :
    ∀ (xs ys : List α), mapOption f xs = some ys → allBool p xs = true → allBool p ys = true
  | [], _, hmap, _ => by simp [mapOption] at hmap; subst hmap; rfl
  | x :: xs, _, hmap, hall => by
    unfold mapOption at hmap
    simp only [allBool, Bool.and_eq_true] at hall
    cases hx : f x with
    | none => rw [hx] at hmap; contradiction
    | some y =>
      cases hxs : mapOption f xs with
      | none => rw [hx, hxs] at hmap; contradiction
      | some ys' =>
        rw [hx, hxs] at hmap
        cases hmap
        simp only [allBool, Bool.and_eq_true]
        exact ⟨h_pres x y hx hall.1, allBool_preserved_of_mapOption h_pres xs ys' hxs hall.2⟩

/-- Companion to Foundational Theorem 3 (`footprintAt_preserve_disjoint_write`):
Performing any access on `[off₁, off₁ + sz₁)` preserves `HasUniqueWritePerm` at
any disjoint byte range `[off₂, off₂ + sz₂)` (`off₁ + sz₁ ≤ off₂ ∨ off₂ + sz₂ ≤ off₁`). -/
theorem footprintAt_preserve_disjoint_write (tree tree' : BorrowTree) (prot : ProtectedTags)
    (tag₁ tag₂ : BorTag) (off₁ sz₁ off₂ sz₂ : Nat) (kind : AccessKind)
    (h_disj : off₁ + sz₁ ≤ off₂ ∨ off₂ + sz₂ ≤ off₁)
    (h_step : tree.performAccessRange prot tag₁ off₁ sz₁ kind = some tree')
    (h_perm : HasUniqueWritePerm tree prot tag₂ off₂ sz₂) :
    HasUniqueWritePerm tree' prot tag₂ off₂ sz₂ := by
  unfold BorrowTree.performAccessRange at h_step
  cases hfind1 : tree.findAncestors tag₁ with
  | none => rw [hfind1] at h_step; contradiction
  | some anc₁ =>
    rw [hfind1] at h_step
    dsimp only at h_step
    cases hmap : mapOption (updateNodeRange anc₁ prot off₁ sz₁ kind) tree.nodes with
    | none => rw [hmap] at h_step; contradiction
    | some nodes' =>
      rw [hmap] at h_step
      dsimp only at h_step
      cases h_step
      rcases h_perm with ⟨anc₂, hfind2, hself2, hall2⟩
      have hfind2' : findAncestorsNodes nodes' tag₂ = some anc₂ := by
        rw [mapOption_preserves_findAncestors
          (updateNodeRange_preserves_identity anc₁ prot off₁ sz₁ kind) tree.nodes nodes' tag₂ hmap]
        exact hfind2
      have hall2' : allBool (nodeWritePerm anc₂ prot off₂ sz₂) nodes' = true :=
        allBool_preserved_of_mapOption
          (fun n n' hupd hp =>
            updateNodeRange_preserves_disjoint_nodeWritePerm anc₁ anc₂ prot off₁ sz₁ off₂ sz₂ kind n n' h_disj hupd hp)
          tree.nodes nodes' hmap hall2
      exact ⟨anc₂, hfind2', hself2, hall2'⟩

/-- Also verify that `Read` through `tag` on `[off, off + sz)` succeeds and
preserves `HasUniqueWritePerm` when `HasUniqueWritePerm` holds. -/
theorem locWritePerm_read_step (rel : AccessRelatedness) (isProt : Bool) (st : LocationState)
    (h : locWritePerm rel isProt st = true) :
    ∃ st', st.performAccess .Read rel isProt = some st' ∧
      locWritePerm rel isProt st' = true ∧
      locWritePerm rel isProt st' = true := by
  rcases st with ⟨perm, acc⟩
  cases rel <;> cases isProt <;> cases acc <;> cases perm <;>
    try (rename_i tyIsFrz conf; cases tyIsFrz <;> cases conf)
  all_goals
    first | contradiction | exact ⟨_, rfl, rfl, rfl⟩

theorem updateNodeRange_read_of_writePerm (anc : List BorTag) (prot : ProtectedTags)
    (off sz : Nat) (n : TreeNode)
    (h : nodeWritePerm anc prot off sz n = true) :
    ∃ n', updateNodeRange anc prot off sz .Read n = some n' ∧
      nodeWritePerm anc prot off sz n' = true ∧
      nodeWritePerm anc prot off sz n' = true := by
  unfold nodeWritePerm at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨h_bounds, h_all⟩
  obtain ⟨ys, hmap, hlen, hpys, _⟩ :=
    mapOption_of_allBool (locWritePerm_read_step (nodeRel anc n.tag) (hasTag prot n.tag))
      (readSlice n.locs off sz) h_all
  have h_slice_len : (readSlice n.locs off sz).length = sz := readSlice_length n.locs off sz h_bounds
  have h_ys_len : ys.length = sz := hlen.trans h_slice_len
  have h_new_len : (writeSlice n.locs off ys).length = n.locs.length :=
    writeSlice_length n.locs off ys (by omega)
  have h_new_slice : readSlice (writeSlice n.locs off ys) off sz = ys :=
    readSlice_writeSlice_same n.locs off ys sz h_ys_len h_bounds
  refine ⟨{ n with locs := writeSlice n.locs off ys }, ?_, ?_, ?_⟩
  · unfold updateNodeRange
    simp only [h_bounds, ↓reduceIte, hmap]
  · unfold nodeWritePerm
    simp only [h_new_len, h_bounds, decide_true, Bool.true_and, h_new_slice, hpys]
  · unfold nodeWritePerm
    simp only [h_new_len, h_bounds, decide_true, Bool.true_and, h_new_slice, hpys]

theorem footprintAt_preserve_local_read_of_writePerm (tree : BorrowTree) (prot : ProtectedTags)
    (tag : BorTag) (off sz : Nat)
    (h : HasUniqueWritePerm tree prot tag off sz) :
    ∃ tree',
      tree.performAccessRange prot tag off sz .Read = some tree' ∧
      HasUniqueWritePerm tree' prot tag off sz := by
  rcases h with ⟨anc, hfind, hanc_self, hall⟩
  obtain ⟨nodes', hmap, _, hw_nodes', _⟩ :=
    mapOption_of_allBool (updateNodeRange_read_of_writePerm anc prot off sz) tree.nodes hall
  have hfind' : findAncestorsNodes nodes' tag = some anc := by
    rw [mapOption_preserves_findAncestors
      (updateNodeRange_preserves_identity anc prot off sz .Read) tree.nodes nodes' tag hmap]
    exact hfind
  refine ⟨⟨nodes'⟩, ?_, ⟨anc, hfind', hanc_self, hw_nodes'⟩⟩
  unfold BorrowTree.performAccessRange
  simp [hfind, hmap]

def nodeSharedCompatible (prot : ProtectedTags) (off sz : Nat) (n : TreeNode) : Bool :=
  decide (off + sz ≤ n.locs.length) &&
    allBool (locIsSharedCompatible (hasTag prot n.tag)) (readSlice n.locs off sz)

/-- Shared read footprint invariant `HasSharedReadPerm`. -/
def HasSharedReadPerm (tree : BorrowTree) (prot : ProtectedTags) (tag : BorTag) (off sz : Nat) : Prop :=
  (tree.findAncestors tag).isSome = true ∧
    allBool (nodeSharedCompatible prot off sz) tree.nodes = true

/-- Unified `FootprintAt` parameterized by `AccessKind` (`Write` ->
`HasUniqueWritePerm`, `Read` -> `HasSharedReadPerm`). -/
def FootprintAt (kind : AccessKind) (tree : BorrowTree) (prot : ProtectedTags)
    (tag : BorTag) (off sz : Nat) : Prop :=
  match kind with
  | .Write => HasUniqueWritePerm tree prot tag off sz
  | .Read => HasSharedReadPerm tree prot tag off sz

theorem updateNodeRange_shared_read_step (anc : List BorTag) (prot : ProtectedTags)
    (off sz : Nat) (n : TreeNode)
    (h : nodeSharedCompatible prot off sz n = true) :
    ∃ n', updateNodeRange anc prot off sz .Read n = some n' ∧
      nodeSharedCompatible prot off sz n' = true ∧
      nodeSharedCompatible prot off sz n' = true := by
  unfold nodeSharedCompatible at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨h_bounds, h_all⟩
  have h_loc_step : ∀ st, locIsSharedCompatible (hasTag prot n.tag) st = true →
      ∃ st', st.performAccess .Read (nodeRel anc n.tag) (hasTag prot n.tag) = some st' ∧
        locIsSharedCompatible (hasTag prot n.tag) st' = true ∧
        locIsSharedCompatible (hasTag prot n.tag) st' = true := by
    intro st hst
    obtain ⟨st', hperf, hcompat⟩ :=
      locIsSharedCompatible_preserved_by_any_read (nodeRel anc n.tag) (hasTag prot n.tag) st hst
    exact ⟨st', hperf, hcompat, hcompat⟩
  obtain ⟨ys, hmap, hlen, hpys, _⟩ := mapOption_of_allBool h_loc_step (readSlice n.locs off sz) h_all
  have h_slice_len : (readSlice n.locs off sz).length = sz := readSlice_length n.locs off sz h_bounds
  have h_ys_len : ys.length = sz := hlen.trans h_slice_len
  have h_new_len : (writeSlice n.locs off ys).length = n.locs.length :=
    writeSlice_length n.locs off ys (by omega)
  have h_new_slice : readSlice (writeSlice n.locs off ys) off sz = ys :=
    readSlice_writeSlice_same n.locs off ys sz h_ys_len h_bounds
  refine ⟨{ n with locs := writeSlice n.locs off ys }, ?_, ?_, ?_⟩
  · unfold updateNodeRange
    simp only [h_bounds, ↓reduceIte, hmap]
  · unfold nodeSharedCompatible
    simp only [h_new_len, h_bounds, decide_true, Bool.true_and, h_new_slice, hpys]
  · unfold nodeSharedCompatible
    simp only [h_new_len, h_bounds, decide_true, Bool.true_and, h_new_slice, hpys]

/-- **Foundational Theorem 4 (`footprintAt_preserve_foreign_read`)**:
When `HasSharedReadPerm tree prot tag off sz` holds, performing a `Read` through
any valid tag `readerTag` in `tree` (whether `readerTag = tag`, a child tag, or
a foreign shared tag) succeeds without UB and preserves `HasSharedReadPerm` for
`tag`. -/
theorem footprintAt_preserve_foreign_read (tree : BorrowTree) (prot : ProtectedTags)
    (tag readerTag : BorTag) (off sz : Nat)
    (h_shared : HasSharedReadPerm tree prot tag off sz)
    (h_reader : (tree.findAncestors readerTag).isSome = true) :
    ∃ tree',
      tree.performAccessRange prot readerTag off sz .Read = some tree' ∧
      HasSharedReadPerm tree' prot tag off sz := by
  rcases h_shared with ⟨htag, hall⟩
  cases hfind_r : tree.findAncestors readerTag with
  | none => rw [hfind_r] at h_reader; contradiction
  | some rAnc =>
    obtain ⟨nodes', hmap, _, hs_nodes', _⟩ :=
      mapOption_of_allBool (updateNodeRange_shared_read_step rAnc prot off sz) tree.nodes hall
    have hfind_tag' : (BorrowTree.findAncestors ⟨nodes'⟩ tag).isSome = true := by
      unfold BorrowTree.findAncestors
      rw [mapOption_preserves_findAncestors
        (updateNodeRange_preserves_identity rAnc prot off sz .Read) tree.nodes nodes' tag hmap]
      exact htag
    refine ⟨⟨nodes'⟩, ?_, ⟨hfind_tag', hs_nodes'⟩⟩
    unfold BorrowTree.performAccessRange
    simp [hfind_r, hmap]

/-! ## Section 4: `Allocation`, `Memory`, `TypedAt`, Foundational Theorems 1 & 2, and Provenance-Directed Addressing -/

/-- A single memory allocation containing `bytes : List AbsByte` and its
Tree Borrows `tree : BorrowTree`. -/
structure Allocation where
  allocId : AllocId
  baseAddr : Nat
  align : Nat
  bytes : List AbsByte
  tree : BorrowTree
  live : Bool := true
  deriving DecidableEq, Repr, Inhabited

/-- Global memory state mapping `AllocId`s to `Allocation`s with active
function-call `prot : ProtectedTags`. -/
structure Memory where
  allocs : List Allocation
  prot : ProtectedTags
  deriving DecidableEq, Repr, Inhabited

def findAllocList : List Allocation → AllocId → Option Allocation
  | [], _ => none
  | a :: as, id => if a.allocId == id then some a else findAllocList as id

def updateAllocList : List Allocation → AllocId → (Allocation → Allocation) → List Allocation
  | [], _, _ => []
  | a :: as, id, f => if a.allocId == id then f a :: as else a :: updateAllocList as id f

def Memory.findAlloc (mem : Memory) (id : AllocId) : Option Allocation :=
  findAllocList mem.allocs id

def Memory.updateAlloc (mem : Memory) (id : AllocId) (f : Allocation → Allocation) : Memory :=
  { mem with allocs := updateAllocList mem.allocs id f }

theorem findAllocList_updateAllocList_same :
    ∀ (as : List Allocation) (id : AllocId) (f : Allocation → Allocation) (a : Allocation),
      findAllocList as id = some a →
      (f a).allocId = a.allocId →
      findAllocList (updateAllocList as id f) id = some (f a)
  | [], _, _, _, h, _ => by contradiction
  | x :: xs, id, f, a, h, h_id => by
    simp only [findAllocList, updateAllocList] at h ⊢
    by_cases heq : (x.allocId == id) = true
    · simp only [heq, ↓reduceIte] at h ⊢
      cases h
      have heq' : ((f x).allocId == id) = true := by rw [h_id]; exact heq
      simp only [findAllocList, heq', ↓reduceIte]
    · have hneq : (x.allocId == id) = false := Bool.eq_false_iff.mpr heq
      simp only [hneq, Bool.false_eq_true, ↓reduceIte] at h ⊢
      simp only [findAllocList, hneq, Bool.false_eq_true, ↓reduceIte]
      exact findAllocList_updateAllocList_same xs id f a h h_id

theorem findAllocList_updateAllocList_ne :
    ∀ (as : List Allocation) (id₁ id₂ : AllocId) (f : Allocation → Allocation),
      id₁ ≠ id₂ →
      (∀ a, (f a).allocId = a.allocId) →
      findAllocList (updateAllocList as id₁ f) id₂ = findAllocList as id₂
  | [], _, _, _, _, _ => rfl
  | x :: xs, id₁, id₂, f, hne, h_id => by
    simp only [updateAllocList, findAllocList]
    by_cases h1 : (x.allocId == id₁) = true
    · simp only [h1, ↓reduceIte, findAllocList]
      have hx1 : x.allocId = id₁ := of_decide_eq_true h1
      have hfx2 : ((f x).allocId == id₂) = false := by
        rw [h_id x, hx1]
        exact decide_eq_false hne
      have hx2 : (x.allocId == id₂) = false := by
        rw [hx1]
        exact decide_eq_false hne
      simp [hfx2, hx2]
    · have h1f : (x.allocId == id₁) = false := Bool.eq_false_iff.mpr h1
      simp only [h1f, Bool.false_eq_true, ↓reduceIte, findAllocList]
      by_cases h2 : (x.allocId == id₂) = true
      · simp [h2]
      · have h2f : (x.allocId == id₂) = false := Bool.eq_false_iff.mpr h2
        simp [h2f, findAllocList_updateAllocList_ne xs id₁ id₂ f hne h_id]

/-- Relational typed memory lens `TypedAt`: allocation `allocId` is live,
`[off, off + codec.size)` is in bounds, and the byte slice at `[off, off + codec.size)`
equals `codec.encode v`. -/
def TypedAt (mem : Memory) (allocId : AllocId) (off : Nat) (codec : LayoutCodec α) (v : α) : Prop :=
  ∃ alloc, mem.findAlloc allocId = some alloc ∧
    alloc.live = true ∧
    off + codec.size ≤ alloc.bytes.length ∧
    readSlice alloc.bytes off codec.size = codec.encode v

/-- Read a typed value via `codec` at `(allocId, off)`. -/
def Memory.readTyped (mem : Memory) (allocId : AllocId) (off : Nat) (codec : LayoutCodec α) : Option α :=
  match mem.findAlloc allocId with
  | none => none
  | some alloc =>
    if alloc.live && decide (off + codec.size ≤ alloc.bytes.length) then
      codec.decode (readSlice alloc.bytes off codec.size)
    else
      none

/-- Write a typed value `v` via `codec` at `(allocId, off)`. -/
def Memory.writeTyped (mem : Memory) (allocId : AllocId) (off : Nat) (codec : LayoutCodec α) (v : α) : Memory :=
  mem.updateAlloc allocId (fun a => { a with bytes := writeSlice a.bytes off (codec.encode v) })

theorem readTyped_of_typedAt (mem : Memory) (allocId : AllocId) (off : Nat)
    (codec : LayoutCodec α) (v : α)
    (h : TypedAt mem allocId off codec v) :
    mem.readTyped allocId off codec = some v := by
  rcases h with ⟨alloc, hfind, hlive, hbounds, hslice⟩
  unfold Memory.readTyped
  simp [hfind, hlive, hbounds, hslice, codec.decode_encode]

/-- **Foundational Theorem 1 (`read_write_same`)**:
Writing `codec.encode v` at `(allocId, off)` establishes `TypedAt` for `v` and
ensures `readTyped` returns `some v` in $O(1)$ without unfolding `codec.encode v`
into individual bytes over symbolic `v`. -/
theorem read_write_same (mem : Memory) (allocId : AllocId) (off : Nat)
    (codec : LayoutCodec α) (v : α) (alloc : Allocation)
    (h_find : mem.findAlloc allocId = some alloc)
    (h_live : alloc.live = true)
    (h_bounds : off + codec.size ≤ alloc.bytes.length) :
    let mem' := mem.writeTyped allocId off codec v
    TypedAt mem' allocId off codec v ∧
    mem'.readTyped allocId off codec = some v := by
  intro mem'
  have h_enc_len : (codec.encode v).length = codec.size := codec.encode_length v
  have h_find' : mem'.findAlloc allocId =
      some { alloc with bytes := writeSlice alloc.bytes off (codec.encode v) } :=
    findAllocList_updateAllocList_same mem.allocs allocId _ alloc h_find rfl
  have h_len' : (writeSlice alloc.bytes off (codec.encode v)).length = alloc.bytes.length :=
    writeSlice_length alloc.bytes off (codec.encode v) (by omega)
  have h_slice' : readSlice (writeSlice alloc.bytes off (codec.encode v)) off codec.size = codec.encode v :=
    readSlice_writeSlice_same alloc.bytes off (codec.encode v) codec.size h_enc_len h_bounds
  have h_typed : TypedAt mem' allocId off codec v :=
    ⟨{ alloc with bytes := writeSlice alloc.bytes off (codec.encode v) },
      h_find', h_live, by dsimp only; omega, h_slice'⟩
  exact ⟨h_typed, readTyped_of_typedAt mem' allocId off codec v h_typed⟩

/-- **Foundational Theorem 2 (`read_write_disjoint`)**:
Writing `codec₁.encode v₁` at `(allocId₁, off₁)` preserves `TypedAt` (and
`readTyped`) at `(allocId₂, off₂, codec₂, v₂)` whenever either
`allocId₁ ≠ allocId₂` or `off₁ + codec₁.size ≤ off₂ ∨ off₂ + codec₂.size ≤ off₁`. -/
theorem read_write_disjoint (mem : Memory)
    (allocId₁ : AllocId) (off₁ : Nat) (codec₁ : LayoutCodec α) (v₁ : α)
    (allocId₂ : AllocId) (off₂ : Nat) (codec₂ : LayoutCodec β) (v₂ : β)
    (h_b1 : ∀ a, mem.findAlloc allocId₁ = some a → off₁ + codec₁.size ≤ a.bytes.length)
    (h_disj : allocId₁ ≠ allocId₂ ∨ (off₁ + codec₁.size ≤ off₂ ∨ off₂ + codec₂.size ≤ off₁))
    (h_typed₂ : TypedAt mem allocId₂ off₂ codec₂ v₂) :
    let mem' := mem.writeTyped allocId₁ off₁ codec₁ v₁
    TypedAt mem' allocId₂ off₂ codec₂ v₂ ∧
    mem'.readTyped allocId₂ off₂ codec₂ = some v₂ := by
  intro mem'
  rcases h_typed₂ with ⟨alloc₂, hfind₂, hlive₂, hbounds₂, hslice₂⟩
  rcases h_disj with h_ne | h_off_disj
  · have h_find' : mem'.findAlloc allocId₂ = some alloc₂ := by
      dsimp only [mem', Memory.writeTyped, Memory.findAlloc, Memory.updateAlloc]
      exact (findAllocList_updateAllocList_ne mem.allocs allocId₁ allocId₂
        (fun a => { a with bytes := writeSlice a.bytes off₁ (codec₁.encode v₁) })
        h_ne (fun _ => rfl)).trans hfind₂
    have h_t : TypedAt mem' allocId₂ off₂ codec₂ v₂ :=
      ⟨alloc₂, h_find', hlive₂, hbounds₂, hslice₂⟩
    exact ⟨h_t, readTyped_of_typedAt mem' allocId₂ off₂ codec₂ v₂ h_t⟩
  · by_cases h_eq : allocId₁ = allocId₂
    · subst h_eq
      have hb1_alloc : off₁ + codec₁.size ≤ alloc₂.bytes.length := h_b1 alloc₂ hfind₂
      have h_enc1 : (codec₁.encode v₁).length = codec₁.size := codec₁.encode_length v₁
      have h_find' : mem'.findAlloc allocId₁ =
          some { alloc₂ with bytes := writeSlice alloc₂.bytes off₁ (codec₁.encode v₁) } :=
        findAllocList_updateAllocList_same mem.allocs allocId₁ _ alloc₂ hfind₂ rfl
      have h_len' : (writeSlice alloc₂.bytes off₁ (codec₁.encode v₁)).length = alloc₂.bytes.length :=
        writeSlice_length alloc₂.bytes off₁ (codec₁.encode v₁) (by omega)
      have h_slice' : readSlice (writeSlice alloc₂.bytes off₁ (codec₁.encode v₁)) off₂ codec₂.size = codec₂.encode v₂ := by
        rw [readSlice_writeSlice_disjoint alloc₂.bytes off₁ (codec₁.encode v₁) off₂ codec₂.size (by omega) (by omega)]
        exact hslice₂
      have h_t : TypedAt mem' allocId₁ off₂ codec₂ v₂ :=
        ⟨{ alloc₂ with bytes := writeSlice alloc₂.bytes off₁ (codec₁.encode v₁) },
          h_find', hlive₂, by dsimp only; omega, h_slice'⟩
      exact ⟨h_t, readTyped_of_typedAt mem' allocId₁ off₂ codec₂ v₂ h_t⟩
    · have h_find' : mem'.findAlloc allocId₂ = some alloc₂ := by
        dsimp only [mem', Memory.writeTyped, Memory.findAlloc, Memory.updateAlloc]
        exact (findAllocList_updateAllocList_ne mem.allocs allocId₁ allocId₂
          (fun a => { a with bytes := writeSlice a.bytes off₁ (codec₁.encode v₁) })
          h_eq (fun _ => rfl)).trans hfind₂
      have h_t : TypedAt mem' allocId₂ off₂ codec₂ v₂ :=
        ⟨alloc₂, h_find', hlive₂, hbounds₂, hslice₂⟩
      exact ⟨h_t, readTyped_of_typedAt mem' allocId₂ off₂ codec₂ v₂ h_t⟩

/-- `Transmute` lens theorem: if `TypedAt mem allocId off c1 v1` and
`TransmuteAs c1 v1 c2 v2` (with `c1.size = c2.size`), then `TypedAt mem allocId off c2 v2`
and `mem.readTyped allocId off c2 = some v2`. -/
theorem typedAt_transmute (mem : Memory) (allocId : AllocId) (off : Nat)
    (c1 : LayoutCodec α) (v1 : α) (c2 : LayoutCodec β) (v2 : β)
    (h_sz : c1.size = c2.size)
    (h_trans : TransmuteAs c1 v1 c2 v2)
    (h_typed : TypedAt mem allocId off c1 v1) :
    TypedAt mem allocId off c2 v2 ∧
    mem.readTyped allocId off c2 = some v2 := by
  rcases h_typed with ⟨alloc, hfind, hlive, hbounds, hslice⟩
  have h_t2 : TypedAt mem allocId off c2 v2 := by
    refine ⟨alloc, hfind, hlive, by omega, ?_⟩
    rw [← h_sz, hslice]
    exact h_trans
  exact ⟨h_t2, readTyped_of_typedAt mem allocId off c2 v2 h_t2⟩

/-! ### Provenance-Directed Addressing and Nondeterministic `baseAddr` (`StepResult.choice`) -/

def mkRootPtr (allocId : AllocId) (tag : BorTag) (baseAddr : Nat) : ThinPtr :=
  ⟨UInt64.ofNat baseAddr, some ⟨allocId, tag⟩⟩

def offsetPtr (ptr : ThinPtr) (relOff : Nat) : ThinPtr :=
  ⟨ptr.addr + UInt64.ofNat relOff, ptr.prov⟩

/-- Local validity of a single allocation's `baseAddr` (alignment, non-null,
and 64-bit non-overflow `baseAddr + totalSize < 2^64`). Crucially, this
predicate mentions ONLY `baseAddr`, `totalSize`, and `align`—never any other
allocation's `baseAddr_j`! -/
def ValidLocalBaseAddr (baseAddr totalSize align : Nat) : Prop :=
  0 < align ∧
  baseAddr % align = 0 ∧
  0 < baseAddr ∧
  baseAddr + totalSize < 18446744073709551616

/-- **Provenance-Directed Offset Cancellation (`resolveOffset_offsetPtr_rootPtr`)**:
Algebraic offset cancellation lemma: if `ValidLocalBaseAddr baseAddr totalSize align`
and `relOff + fieldSize ≤ totalSize`, then for `ptr := offsetPtr (mkRootPtr allocId tag baseAddr) relOff`,
the provenance-directed intra-allocation offset `ptr.addr.toNat - baseAddr`
cancels to `relOff` in `UInt64` / `Nat` using ONLY the single local bound
`baseAddr + totalSize < 2^64` and **zero** pairwise comparisons `baseAddr_i ≠ baseAddr_j`! -/
theorem resolveOffset_offsetPtr_rootPtr
    (allocId : AllocId) (tag : BorTag) (baseAddr totalSize align relOff fieldSize : Nat)
    (h_local : ValidLocalBaseAddr baseAddr totalSize align)
    (h_inbounds : relOff + fieldSize ≤ totalSize) :
    let ptr := offsetPtr (mkRootPtr allocId tag baseAddr) relOff
    ptr.prov = some ⟨allocId, tag⟩ ∧
    baseAddr ≤ ptr.addr.toNat ∧
    ptr.addr.toNat - baseAddr = relOff ∧
    (ptr.addr.toNat - baseAddr) + fieldSize ≤ totalSize := by
  rcases h_local with ⟨_, _, _, h_no_overflow⟩
  dsimp only [offsetPtr, mkRootPtr]
  have h_addr_nat : (UInt64.ofNat baseAddr + UInt64.ofNat relOff).toNat = baseAddr + relOff := by
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat']
    omega
  refine ⟨rfl, ?_, ?_, ?_⟩
  · rw [h_addr_nat]; omega
  · rw [h_addr_nat]; omega
  · rw [h_addr_nat]; omega

/-- Metadata for address-space allocation tracking (`AllocAddresses.GlobalState`
in `lean-miri`). -/
structure AllocMeta where
  allocId : AllocId
  baseAddr : Nat
  size : Nat
  align : Nat
  live : Bool := true
  deriving DecidableEq, Repr, Inhabited

def maxEndAddrList : List AllocMeta → Nat
  | [] => 0
  | a :: as =>
    let rest := maxEndAddrList as
    if a.baseAddr + a.size ≤ rest then rest else a.baseAddr + a.size

theorem endAddr_le_maxEndAddrList :
    ∀ (as : List AllocMeta) (a : AllocMeta),
      a ∈ as → a.baseAddr + a.size ≤ maxEndAddrList as
  | [], _, h => by contradiction
  | x :: xs, a, h => by
    simp only [List.mem_cons] at h
    rcases h with rfl | hmem
    · simp only [maxEndAddrList]
      split <;> omega
    · have ih := endAddr_le_maxEndAddrList xs a hmem
      simp only [maxEndAddrList]
      split <;> omega

def DisjointFromAllLive (as : List AllocMeta) (baseAddr size : Nat) : Prop :=
  ∀ a ∈ as, a.live = true →
    a.baseAddr + a.size ≤ baseAddr ∨ baseAddr + size ≤ a.baseAddr

/-- Full demonic `ValidFreshBaseAddr` predicate for `StepResult.choice`:
1. `ValidLocalBaseAddr baseAddr size align` (alignment, non-null, 64-bit non-overflow),
2. `DisjointFromAllLive as baseAddr size` (pairwise disjoint from all live allocations),
3. `baseAddr ≤ maxEndAddrList as + align + 16` (bounded slack window matching
   `Miri.Memory.AllocAddresses.AddressGenerator.generate` in
   `AddressGenerator.lean:77-105`, which prevents an adversarial choice on
   allocation 1 from picking `2^64 - size` and exhausting the remaining address
   space for allocations `2..N`). -/
def ValidFreshBaseAddr (as : List AllocMeta) (size align : Nat) (baseAddr : Nat) : Prop :=
  ValidLocalBaseAddr baseAddr size align ∧
  DisjointFromAllLive as baseAddr size ∧
  baseAddr ≤ maxEndAddrList as + align + 16

theorem mul_div_succ_mod (m align : Nat) :
    (((m / align) + 1) * align) % align = 0 :=
  Nat.mul_mod_left ((m / align) + 1) align

theorem mul_div_succ_gt (m align : Nat) (h_align : 0 < align) :
    m < ((m / align) + 1) * align ∧ ((m / align) + 1) * align ≤ m + align := by
  have h_div_mod := Nat.div_add_mod m align
  have h_mod_lt := Nat.mod_lt m h_align
  have h_expand : ((m / align) + 1) * align = align * (m / align) + align := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (m / align) align]
  omega

/-- **Constructive Non-Emptiness (`validFreshBaseAddr_nonempty`)**:
Constructive proof of `Nonempty { baseAddr : Nat // ValidFreshBaseAddr as size align baseAddr }`
whenever `maxEndAddrList as + align + 16 + size < 2^64`. -/
theorem validFreshBaseAddr_nonempty (as : List AllocMeta) (size align : Nat)
    (h_align : 0 < align)
    (h_space : maxEndAddrList as + align + 16 + size < 18446744073709551616) :
    Nonempty { baseAddr : Nat // ValidFreshBaseAddr as size align baseAddr } := by
  have h_bounds := mul_div_succ_gt (maxEndAddrList as) align h_align
  have h_mod := mul_div_succ_mod (maxEndAddrList as) align
  refine ⟨⟨((maxEndAddrList as / align) + 1) * align, ⟨⟨h_align, h_mod, by omega, by omega⟩, ?_, by omega⟩⟩⟩
  intro a hmem _
  have h_le := endAddr_le_maxEndAddrList as a hmem
  left
  omega

theorem maxEndAddrList_cons_le (as : List AllocMeta) (a : AllocMeta) (bound : Nat)
    (h_prev : maxEndAddrList as ≤ bound)
    (h_new : a.baseAddr ≤ maxEndAddrList as + a.align + 16) :
    maxEndAddrList (a :: as) ≤ bound + a.align + 16 + a.size := by
  simp only [maxEndAddrList]
  split <;> omega

/-- Nondeterministic computation tree (`StepResult` with demonic `choice`). -/
inductive Comp (S : Type) where
  | ret (s : S)
  | ub
  | choice (α : Type) (k : α → Comp S)

/-- Total weakest-precondition semantics (`VerificationResult` style:
`choice α k` requires `Nonempty α ∧ ∀ a : α, wpComp (k a) P`). -/
def wpComp : Comp S → (S → Prop) → Prop
  | .ret s, P => P s
  | .ub, _ => False
  | .choice α k, P => Nonempty α ∧ ∀ a : α, wpComp (k a) P

def forceAllocationChoice (as : List AllocMeta) (size align : Nat)
    (k : Nat → Comp S) : Comp S :=
  .choice { baseAddr : Nat // ValidFreshBaseAddr as size align baseAddr }
    (fun sub => k sub.val)

/-- **Compositional Allocation Stepping (`wp_forceAllocation_choice`)**:
$O(1)$ Weakest Precondition Step Theorem for `forceAllocationChoice`.
Given `maxEndAddrList as ≤ bound` and `bound + align + 16 + size < 2^64`,
discharges `Nonempty` in $O(1)$ and provides the continuation with:
1. `ValidLocalBaseAddr baseAddr size align` (local alignment & non-overflow), and
2. `maxEndAddrList (newAlloc :: as) ≤ bound + align + 16 + size`,
completely forgetting `DisjointFromAllLive` unless needed for `ptr2Int`. -/
theorem wp_forceAllocation_choice (as : List AllocMeta) (allocId : AllocId)
    (size align bound : Nat)
    (k : Nat → Comp S) (P : S → Prop)
    (h_align : 0 < align)
    (h_bound : maxEndAddrList as ≤ bound)
    (h_space : bound + align + 16 + size < 18446744073709551616)
    (h_cont : ∀ baseAddr : Nat,
      ValidLocalBaseAddr baseAddr size align →
      maxEndAddrList (⟨allocId, baseAddr, size, align, true⟩ :: as) ≤ bound + align + 16 + size →
      wpComp (k baseAddr) P) :
    wpComp (forceAllocationChoice as size align k) P := by
  refine ⟨validFreshBaseAddr_nonempty as size align h_align (by omega), ?_⟩
  intro ⟨baseAddr, h_local, _, h_window⟩
  have h_next_bound := maxEndAddrList_cons_le as ⟨allocId, baseAddr, size, align, true⟩ bound h_bound h_window
  exact h_cont baseAddr h_local h_next_bound

/-- Provenance-directed load through `ptr : ThinPtr` in `Memory`: resolves the
target allocation by `ptr.prov = some ⟨allocId, tag⟩` and computes the
intra-allocation byte offset `off := ptr.addr.toNat - alloc.baseAddr`. -/
def Memory.loadPtr (mem : Memory) (ptr : ThinPtr) (codec : LayoutCodec α) : Option α :=
  match ptr.prov with
  | none => none
  | some ⟨allocId, _⟩ =>
    match mem.findAlloc allocId with
    | none => none
    | some alloc =>
      if alloc.live && decide (alloc.baseAddr ≤ ptr.addr.toNat) then
        let off := ptr.addr.toNat - alloc.baseAddr
        if decide (off + codec.size ≤ alloc.bytes.length) then
          codec.decode (readSlice alloc.bytes off codec.size)
        else
          none
      else
        none

/-- Provenance-directed store through `ptr : ThinPtr` in `Memory`. -/
def Memory.storePtr (mem : Memory) (ptr : ThinPtr) (codec : LayoutCodec α) (v : α) : Option Memory :=
  match ptr.prov with
  | none => none
  | some ⟨allocId, _⟩ =>
    match mem.findAlloc allocId with
    | none => none
    | some alloc =>
      if alloc.live && decide (alloc.baseAddr ≤ ptr.addr.toNat) then
        let off := ptr.addr.toNat - alloc.baseAddr
        if decide (off + codec.size ≤ alloc.bytes.length) then
          some (mem.writeTyped allocId off codec v)
        else
          none
      else
        none

/-- Single-allocation provenance-directed store-then-load roundtrip on an
8-byte stack local at nondeterministic `baseAddr`, writing `v` at field offset
`4` (`offsetPtr (mkRootPtr id tag baseAddr) 4`) and reading it back—using ONLY
`ValidLocalBaseAddr baseAddr 8 8` and zero pairwise address comparisons. -/
def storeLoadFieldAtNondetBase (id : AllocId) (tag : BorTag) (baseAddr : Nat) (v : UInt32) : Option UInt32 :=
  let initBytes := List.replicate 8 AbsByte.uninit
  let alloc : Allocation := ⟨id, baseAddr, 8, initBytes, ⟨[]⟩, true⟩
  let mem : Memory := ⟨[alloc], []⟩
  let fieldPtr := offsetPtr (mkRootPtr id tag baseAddr) 4
  match mem.storePtr fieldPtr u32Codec v with
  | none => none
  | some mem' => mem'.loadPtr fieldPtr u32Codec

theorem storeLoadFieldAtNondetBase_eq (id : AllocId) (tag : BorTag) (baseAddr : Nat) (v : UInt32)
    (h_local : ValidLocalBaseAddr baseAddr 8 8) :
    storeLoadFieldAtNondetBase id tag baseAddr v = some v := by
  obtain ⟨h_prov, h_le, h_sub, h_inb⟩ :=
    resolveOffset_offsetPtr_rootPtr id tag baseAddr 8 8 4 4 h_local (by decide)
  unfold storeLoadFieldAtNondetBase Memory.storePtr Memory.loadPtr
  dsimp only
  have h_len8 : (List.replicate 8 AbsByte.uninit).length = 8 := rfl
  have h_find : (Memory.mk [⟨id, baseAddr, 8, List.replicate 8 AbsByte.uninit, ⟨[]⟩, true⟩] []).findAlloc id =
      some ⟨id, baseAddr, 8, List.replicate 8 AbsByte.uninit, ⟨[]⟩, true⟩ := by
    simp [Memory.findAlloc, findAllocList]
  rw [h_prov]
  dsimp only
  rw [h_find]
  simp only [Bool.true_and, decide_eq_true_iff, h_le, ↓reduceIte, h_sub]
  have h_4_le_8 : 4 + u32Codec.size ≤ (List.replicate 8 AbsByte.uninit).length := by decide
  simp only [h_4_le_8, ↓reduceIte]
  have h_rw := read_write_same
    (Memory.mk [⟨id, baseAddr, 8, List.replicate 8 AbsByte.uninit, ⟨[]⟩, true⟩] [])
    id 4 u32Codec v
    ⟨id, baseAddr, 8, List.replicate 8 AbsByte.uninit, ⟨[]⟩, true⟩
    h_find rfl h_4_le_8
  rcases h_rw.1 with ⟨alloc', hfind', hlive', hbounds', hslice'⟩
  have h_base' : alloc'.baseAddr = baseAddr := by
    unfold Memory.writeTyped Memory.updateAlloc Memory.findAlloc updateAllocList findAllocList at hfind'
    simp at hfind'
    cases hfind'
    rfl
  rw [hfind']
  simp only [hlive', h_base', Bool.true_and, decide_eq_true_iff, h_le, ↓reduceIte, h_sub, hbounds', hslice', u32Codec.decode_encode]

/-- **Nondeterministic Stack Allocation Benchmark (`alloc10AndCompute` & `wp_ten_nondet_stack_allocs`)**:
Benchmark program that allocates $N = 10$ distinct 8-byte stack allocations via
`forceAllocationChoice` (`StepResult.choice` over `ValidFreshBaseAddr`),
performs provenance-directed stores and loads at field offset 4 across all 10
nondeterministic `baseAddr_0 .. baseAddr_9`, and returns the sum of the 10 loaded
values. -/
def stepAllocAndAccess (as : List AllocMeta) (idx : Nat) (v : UInt32)
    (k : List AllocMeta → UInt32 → Comp UInt32) : Comp UInt32 :=
  forceAllocationChoice as 8 8 (fun baseAddr =>
    match storeLoadFieldAtNondetBase ⟨idx⟩ ⟨idx⟩ baseAddr v with
    | none => .ub
    | some loaded =>
      k (⟨⟨idx⟩, baseAddr, 8, 8, true⟩ :: as) loaded)

theorem wp_stepAllocAndAccess (as : List AllocMeta) (idx bound : Nat) (v : UInt32)
    (k : List AllocMeta → UInt32 → Comp UInt32) (P : UInt32 → Prop)
    (h_bound : maxEndAddrList as ≤ bound)
    (h_space : bound + 32 < 18446744073709551616)
    (h_cont : ∀ as', maxEndAddrList as' ≤ bound + 32 → wpComp (k as' v) P) :
    wpComp (stepAllocAndAccess as idx v k) P := by
  unfold stepAllocAndAccess
  apply wp_forceAllocation_choice as ⟨idx⟩ 8 8 bound _ P (by decide) h_bound (by omega)
  intro baseAddr h_local h_next_bound
  rw [storeLoadFieldAtNondetBase_eq ⟨idx⟩ ⟨idx⟩ baseAddr v h_local]
  exact h_cont _ h_next_bound

def alloc10AndCompute (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt32) : Comp UInt32 :=
  stepAllocAndAccess [] 0 x0 (fun as1 r0 =>
  stepAllocAndAccess as1 1 x1 (fun as2 r1 =>
  stepAllocAndAccess as2 2 x2 (fun as3 r2 =>
  stepAllocAndAccess as3 3 x3 (fun as4 r3 =>
  stepAllocAndAccess as4 4 x4 (fun as5 r4 =>
  stepAllocAndAccess as5 5 x5 (fun as6 r5 =>
  stepAllocAndAccess as6 6 x6 (fun as7 r6 =>
  stepAllocAndAccess as7 7 x7 (fun as8 r7 =>
  stepAllocAndAccess as8 8 x8 (fun as9 r8 =>
  stepAllocAndAccess as9 9 x9 (fun _as10 r9 =>
    .ret (r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9)))))))))))

/-- **N = 10 Nondeterministic Stack Allocations Theorem (`wp_ten_nondet_stack_allocs`)**:
Proves that `alloc10AndCompute` never triggers UB and always returns
`x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9` across all $N = 10$
nondeterministically chosen `baseAddr_0 .. baseAddr_9` in 10 lines of tactic
proof with **zero** pairwise `baseAddr_i ≠ baseAddr_j` obligations! -/
theorem wp_ten_nondet_stack_allocs (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt32) :
    wpComp (alloc10AndCompute x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (fun res => res = x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9) := by
  unfold alloc10AndCompute
  apply wp_stepAllocAndAccess [] 0 0 x0 _ _ (by decide) (by decide); intro as1 hb1
  apply wp_stepAllocAndAccess as1 1 32 x1 _ _ hb1 (by decide); intro as2 hb2
  apply wp_stepAllocAndAccess as2 2 64 x2 _ _ hb2 (by decide); intro as3 hb3
  apply wp_stepAllocAndAccess as3 3 96 x3 _ _ hb3 (by decide); intro as4 hb4
  apply wp_stepAllocAndAccess as4 4 128 x4 _ _ hb4 (by decide); intro as5 hb5
  apply wp_stepAllocAndAccess as5 5 160 x5 _ _ hb5 (by decide); intro as6 hb6
  apply wp_stepAllocAndAccess as6 6 192 x6 _ _ hb6 (by decide); intro as7 hb7
  apply wp_stepAllocAndAccess as7 7 224 x7 _ _ hb7 (by decide); intro as8 hb8
  apply wp_stepAllocAndAccess as8 8 256 x8 _ _ hb8 (by decide); intro as9 hb9
  apply wp_stepAllocAndAccess as9 9 288 x9 _ _ hb9 (by decide); intro _as10 _hb10
  rfl

/-! ## Section 5: Kernel Scaling & Representation Experiment (Approach A vs. Approach B across 15–30 Symbolic Struct/Reference Mutations) -/

/-- Concrete entry `BorrowTree` for an 8-byte struct `PairU32 = (UInt32, UInt32)`
with 4 nodes:
- `tag 0`: root allocation tag (`Active`, `accessed = true`),
- `tag 1`: caller parent reborrow (`Active`, `accessed = true`),
- `tag 2`: callee `&mut PairU32` parameter tag (`Reserved true false` initially,
  protected by function call protector `[⟨2⟩]`, ancestors `[⟨0⟩, ⟨1⟩, ⟨2⟩]`),
- `tag 3`: sibling dead/disabled tag (`Disabled`, `accessed = false`, ancestors `[⟨0⟩, ⟨3⟩]`). -/
def entryBorrowTree8 : BorrowTree :=
  { nodes :=
    [ { tag := ⟨0⟩, ancestors := [⟨0⟩]
        locs := List.replicate 8 ⟨.Active, true⟩ }
    , { tag := ⟨1⟩, ancestors := [⟨0⟩, ⟨1⟩]
        locs := List.replicate 8 ⟨.Active, true⟩ }
    , { tag := ⟨2⟩, ancestors := [⟨0⟩, ⟨1⟩, ⟨2⟩]
        locs := List.replicate 8 ⟨.Reserved true false, false⟩ }
    , { tag := ⟨3⟩, ancestors := [⟨0⟩, ⟨3⟩]
        locs := List.replicate 8 ⟨.Disabled, false⟩ }
    ] }

def entryProt : ProtectedTags := [⟨2⟩]
def mutTag : BorTag := ⟨2⟩
def pairAllocId : AllocId := ⟨0⟩

/-- Initial entry state for an 8-byte `PairU32` allocation with initial field
values `(f0, f1) : UInt32 × UInt32`. -/
def mkEntryMemory (f0 f1 : UInt32) : Memory :=
  { allocs :=
    [ { allocId := pairAllocId
        baseAddr := 4096
        align := 8
        bytes := encodeU32LE f0 ++ encodeU32LE f1
        tree := entryBorrowTree8
        live := true } ]
    prot := entryProt }

/-- Establish `HasUniqueWritePerm` at function entry on both field 0 (`[0, 4)`)
and field 1 (`[4, 8)`) via the decidable checker `checkUniqueWritePerm_sound`
(`by decide` on the concrete entry `BorrowTree` topology!). -/
theorem entry_hasUniqueWritePerm_field0 :
    HasUniqueWritePerm entryBorrowTree8 entryProt mutTag 0 4 :=
  checkUniqueWritePerm_sound entryBorrowTree8 entryProt mutTag 0 4 (by decide)

theorem entry_hasUniqueWritePerm_field1 :
    HasUniqueWritePerm entryBorrowTree8 entryProt mutTag 4 4 :=
  checkUniqueWritePerm_sound entryBorrowTree8 entryProt mutTag 4 4 (by decide)

/-- One symbolic struct mutation step (`*p.field0 = *p.field0 + dx; *p.field1 = (*p.field0) ^^^ (*p.field1 + dy)`):
1. Checks `BorrowTree.performAccessRange` (`Read` then `Write`) on `[0, 4)` for `field0`,
2. Reads `v0 : UInt32` at `[0, 4)` and writes `v0' := v0 + dx` at `[0, 4)`,
3. Checks `BorrowTree.performAccessRange` (`Read` then `Write`) on `[4, 8)` for `field1`,
4. Reads `v1 : UInt32` at `[4, 8)` and writes `v1' := v0' ^^^ (v1 + dy)` at `[4, 8)`. -/
def stepPairMut (mem : Memory) (dx dy : UInt32) : Option Memory :=
  match mem.findAlloc pairAllocId with
  | none => none
  | some alloc =>
    match alloc.tree.performAccessRange mem.prot mutTag 0 4 .Read with
    | none => none
    | some tree1 =>
      match tree1.performAccessRange mem.prot mutTag 0 4 .Write with
      | none => none
      | some tree2 =>
        match tree2.performAccessRange mem.prot mutTag 4 4 .Read with
        | none => none
        | some tree3 =>
          match tree3.performAccessRange mem.prot mutTag 4 4 .Write with
          | none => none
          | some tree4 =>
            let memTree := mem.updateAlloc pairAllocId (fun a => { a with tree := tree4 })
            match memTree.readTyped pairAllocId 0 u32Codec with
            | none => none
            | some v0 =>
              let v0' := v0 + dx
              let memW0 := memTree.writeTyped pairAllocId 0 u32Codec v0'
              match memW0.readTyped pairAllocId 4 u32Codec with
              | none => none
              | some v1 =>
                let v1' := v0' ^^^ (v1 + dy)
                some (memW0.writeTyped pairAllocId 4 u32Codec v1')

/-- Pure specification function for one `stepPairMut` step on `(f0, f1)`. -/
def specPairStep (f0 f1 dx dy : UInt32) : UInt32 × UInt32 :=
  let f0' := f0 + dx
  let f1' := f0' ^^^ (f1 + dy)
  (f0', f1')

/-- Inductive invariant bundling `TypedAt` on `field0` (`[0, 4)`) and `field1`
(`[4, 8)`) together with `HasUniqueWritePerm` on `[0, 4)` and `[4, 8)` in the
allocation's `BorrowTree`. -/
def PairMutInv (mem : Memory) (f0 f1 : UInt32) : Prop :=
  TypedAt mem pairAllocId 0 u32Codec f0 ∧
  TypedAt mem pairAllocId 4 u32Codec f1 ∧
  ∃ alloc, mem.findAlloc pairAllocId = some alloc ∧
    HasUniqueWritePerm alloc.tree mem.prot mutTag 0 4 ∧
    HasUniqueWritePerm alloc.tree mem.prot mutTag 4 4

theorem entryMemory_satisfies_PairMutInv (f0 f1 : UInt32) :
    PairMutInv (mkEntryMemory f0 f1) f0 f1 := by
  have hlen0 : (encodeU32LE f0).length = 4 := rfl
  have hlen1 : (encodeU32LE f1).length = 4 := rfl
  have hlen_both : (encodeU32LE f0 ++ encodeU32LE f1).length = 8 := by
    rw [List.length_append, hlen0, hlen1]
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨_, rfl, rfl, by dsimp only [u32Codec]; omega, ?_⟩
    dsimp only [readSlice, List.drop, u32Codec]
    rw [take_append_of_le_length (by omega)]
    exact take_all_of_eq hlen0
  · refine ⟨_, rfl, rfl, by dsimp only [u32Codec]; omega, ?_⟩
    dsimp only [readSlice, u32Codec]
    rw [drop_append_of_ge_length (by omega)]
    have hsub : 4 - (encodeU32LE f0).length = 0 := by omega
    rw [hsub, List.drop_zero]
    exact take_all_of_eq hlen1
  · exact ⟨_, rfl, entry_hasUniqueWritePerm_field0, entry_hasUniqueWritePerm_field1⟩

/-- **Approach B Core Compositional Step Lemma (`stepPairMut_preserves_PairMutInv`)**:
Uses the four foundational relational lens theorems:
1. `footprintAt_preserve_local_read_of_writePerm`, `footprintAt_preserve_local_write`,
   and `footprintAt_preserve_disjoint_write` to step `tree → tree1 → tree2 → tree3 → tree4`
   in $O(1)$ without inspecting individual `TreeNode`s or `LocationState`s, and
2. `read_write_same` and `read_write_disjoint` to step `TypedAt` on `[0, 4)` and `[4, 8)`
   in $O(1)$ without unfolding `encodeU32LE` or `decodeU32LE` over symbolic `UInt32` values! -/
theorem stepPairMut_preserves_PairMutInv (mem : Memory) (f0 f1 dx dy : UInt32)
    (h_inv : PairMutInv mem f0 f1) :
    ∃ mem',
      stepPairMut mem dx dy = some mem' ∧
      PairMutInv mem' (specPairStep f0 f1 dx dy).1 (specPairStep f0 f1 dx dy).2 ∧
      mem'.readTyped pairAllocId 0 u32Codec = some (specPairStep f0 f1 dx dy).1 ∧
      mem'.readTyped pairAllocId 4 u32Codec = some (specPairStep f0 f1 dx dy).2 := by
  rcases h_inv with ⟨h_t0, h_t1, ⟨alloc, h_find, h_w0, h_w1⟩⟩
  -- 1. Step BorrowTree through Read(0,4), Write(0,4), Read(4,4), Write(4,4)
  obtain ⟨tree1, h_r0, h_w0_1⟩ :=
    footprintAt_preserve_local_read_of_writePerm alloc.tree mem.prot mutTag 0 4 h_w0
  have h_w1_1 : HasUniqueWritePerm tree1 mem.prot mutTag 4 4 :=
    footprintAt_preserve_disjoint_write alloc.tree tree1 mem.prot mutTag mutTag 0 4 4 4 .Read
      (by decide) h_r0 h_w1
  obtain ⟨tree2, _, h_w0_step, _, _, h_w0_2⟩ :=
    footprintAt_preserve_local_write tree1 mem.prot mutTag 0 4 h_w0_1
  have h_w1_2 : HasUniqueWritePerm tree2 mem.prot mutTag 4 4 :=
    footprintAt_preserve_disjoint_write tree1 tree2 mem.prot mutTag mutTag 0 4 4 4 .Write
      (by decide) h_w0_step h_w1_1
  obtain ⟨tree3, h_r1, h_w1_3⟩ :=
    footprintAt_preserve_local_read_of_writePerm tree2 mem.prot mutTag 4 4 h_w1_2
  have h_w0_3 : HasUniqueWritePerm tree3 mem.prot mutTag 0 4 :=
    footprintAt_preserve_disjoint_write tree2 tree3 mem.prot mutTag mutTag 4 4 0 4 .Read
      (by decide) h_r1 h_w0_2
  obtain ⟨tree4, _, h_w1_step, _, _, h_w1_4⟩ :=
    footprintAt_preserve_local_write tree3 mem.prot mutTag 4 4 h_w1_3
  have h_w0_4 : HasUniqueWritePerm tree4 mem.prot mutTag 0 4 :=
    footprintAt_preserve_disjoint_write tree3 tree4 mem.prot mutTag mutTag 4 4 0 4 .Write
      (by decide) h_w1_step h_w0_3
  -- 2. Lift TypedAt across tree-only update `memTree`
  let memTree := mem.updateAlloc pairAllocId (fun a => { a with tree := tree4 })
  have h_find_tree : memTree.findAlloc pairAllocId = some { alloc with tree := tree4 } :=
    findAllocList_updateAllocList_same mem.allocs pairAllocId _ alloc h_find rfl
  rcases h_t0 with ⟨a0, hf0, hlive0, hb0, hs0⟩
  rw [h_find] at hf0; cases hf0
  rcases h_t1 with ⟨a1, hf1, hlive1, hb1, hs1⟩
  rw [h_find] at hf1; cases hf1
  have h_t0_tree : TypedAt memTree pairAllocId 0 u32Codec f0 :=
    ⟨{ alloc with tree := tree4 }, h_find_tree, hlive0, hb0, hs0⟩
  have h_t1_tree : TypedAt memTree pairAllocId 4 u32Codec f1 :=
    ⟨{ alloc with tree := tree4 }, h_find_tree, hlive1, hb1, hs1⟩
  have h_read0 : memTree.readTyped pairAllocId 0 u32Codec = some f0 :=
    readTyped_of_typedAt memTree pairAllocId 0 u32Codec f0 h_t0_tree
  -- 3. Step writeTyped on field 0 (`[0, 4)`) via `read_write_same` and `read_write_disjoint`
  let f0' := f0 + dx
  let memW0 := memTree.writeTyped pairAllocId 0 u32Codec f0'
  have h_rw0_same := read_write_same memTree pairAllocId 0 u32Codec f0'
    { alloc with tree := tree4 } h_find_tree hlive0 hb0
  have h_rw0_disj := read_write_disjoint memTree
    pairAllocId 0 u32Codec f0'
    pairAllocId 4 u32Codec f1
    (fun a ha => by rw [h_find_tree] at ha; cases ha; exact hb0)
    (Or.inr (Or.inl (by decide)))
    h_t1_tree
  have h_read1 : memW0.readTyped pairAllocId 4 u32Codec = some f1 := h_rw0_disj.2
  -- 4. Step writeTyped on field 1 (`[4, 8)`) via `read_write_same` and `read_write_disjoint`
  let f1' := f0' ^^^ (f1 + dy)
  let memW1 := memW0.writeTyped pairAllocId 4 u32Codec f1'
  have h_find_w0 : memW0.findAlloc pairAllocId =
      some { alloc with tree := tree4, bytes := writeSlice alloc.bytes 0 (u32Codec.encode f0') } :=
    findAllocList_updateAllocList_same memTree.allocs pairAllocId _
      { alloc with tree := tree4 } h_find_tree rfl
  have h_len_w0 : (writeSlice alloc.bytes 0 (u32Codec.encode f0')).length = alloc.bytes.length :=
    writeSlice_length alloc.bytes 0 (u32Codec.encode f0') hb0
  have hb1_w0 : 4 + u32Codec.size ≤ (writeSlice alloc.bytes 0 (u32Codec.encode f0')).length := by
    rw [h_len_w0]; exact hb1
  have h_rw1_same := read_write_same memW0 pairAllocId 4 u32Codec f1'
    { alloc with tree := tree4, bytes := writeSlice alloc.bytes 0 (u32Codec.encode f0') }
    h_find_w0 hlive0 hb1_w0
  have h_rw1_disj := read_write_disjoint memW0
    pairAllocId 4 u32Codec f1'
    pairAllocId 0 u32Codec f0'
    (fun a ha => by rw [h_find_w0] at ha; cases ha; exact hb1_w0)
    (Or.inr (Or.inr (by decide)))
    h_rw0_same.1
  have h_find_w1 : memW1.findAlloc pairAllocId =
      some { alloc with
        tree := tree4
        bytes := writeSlice (writeSlice alloc.bytes 0 (u32Codec.encode f0')) 4 (u32Codec.encode f1') } :=
    findAllocList_updateAllocList_same memW0.allocs pairAllocId _
      { alloc with tree := tree4, bytes := writeSlice alloc.bytes 0 (u32Codec.encode f0') }
      h_find_w0 rfl
  refine ⟨memW1, ?_, ⟨h_rw1_disj.1, h_rw1_same.1, ⟨_, h_find_w1, h_w0_4, h_w1_4⟩⟩, h_rw1_disj.2, h_rw1_same.2⟩
  unfold stepPairMut
  rw [h_find]
  dsimp only
  rw [h_r0]
  dsimp only
  rw [h_w0_step]
  dsimp only
  rw [h_r1]
  dsimp only
  rw [h_w1_step]
  dsimp only
  change (match memTree.readTyped pairAllocId 0 u32Codec with
    | none => none
    | some v0 =>
      let v0' := v0 + dx
      let memW0 := memTree.writeTyped pairAllocId 0 u32Codec v0'
      match memW0.readTyped pairAllocId 4 u32Codec with
      | none => none
      | some v1 => some (memW0.writeTyped pairAllocId 4 u32Codec (v0' ^^^ (v1 + dy)))) = some memW1
  rw [h_read0]
  dsimp only
  rw [h_read1]

/-- Run $K$ sequential `stepPairMut` mutations driven by a list of `(dx, dy)` pairs. -/
def runPairMutSteps : Memory → List (UInt32 × UInt32) → Option Memory
  | mem, [] => some mem
  | mem, (dx, dy) :: rest =>
    match stepPairMut mem dx dy with
    | none => none
    | some mem' => runPairMutSteps mem' rest

def specPairSteps : UInt32 → UInt32 → List (UInt32 × UInt32) → UInt32 × UInt32
  | f0, f1, [] => (f0, f1)
  | f0, f1, (dx, dy) :: rest =>
    let (f0', f1') := specPairStep f0 f1 dx dy
    specPairSteps f0' f1' rest

theorem runPairMutSteps_spec :
    ∀ (steps : List (UInt32 × UInt32)) (mem : Memory) (f0 f1 : UInt32),
      PairMutInv mem f0 f1 →
      ∃ mem',
        runPairMutSteps mem steps = some mem' ∧
        PairMutInv mem' (specPairSteps f0 f1 steps).1 (specPairSteps f0 f1 steps).2 ∧
        mem'.readTyped pairAllocId 0 u32Codec = some (specPairSteps f0 f1 steps).1 ∧
        mem'.readTyped pairAllocId 4 u32Codec = some (specPairSteps f0 f1 steps).2
  | [], mem, f0, f1, h_inv => by
    refine ⟨mem, rfl, h_inv, ?_, ?_⟩
    · exact readTyped_of_typedAt mem pairAllocId 0 u32Codec f0 h_inv.1
    · exact readTyped_of_typedAt mem pairAllocId 4 u32Codec f1 h_inv.2.1
  | (dx, dy) :: rest, mem, f0, f1, h_inv => by
    obtain ⟨mem1, h_step1, h_inv1, _, _⟩ := stepPairMut_preserves_PairMutInv mem f0 f1 dx dy h_inv
    obtain ⟨memFinal, h_rest, h_invF, h_r0F, h_r1F⟩ :=
      runPairMutSteps_spec rest mem1 (specPairStep f0 f1 dx dy).1 (specPairStep f0 f1 dx dy).2 h_inv1
    refine ⟨memFinal, ?_, h_invF, h_r0F, h_r1F⟩
    unfold runPairMutSteps
    rw [h_step1]
    exact h_rest

/-- Schedule of $K$ symbolic mutation steps cycling `(x, y)`, `(y, z)`, `(z, x)`. -/
def mkSymbolicSchedule (x y z : UInt32) : Nat → List (UInt32 × UInt32)
  | 0 => []
  | k + 1 =>
    let pair := match k % 3 with
      | 0 => (x, y)
      | 1 => (y, z)
      | _ => (z, x)
    pair :: mkSymbolicSchedule x y z k

/-- Single-step CPS combinator (`step_runPairMutSteps`) for unrolled straight-line
symbolic execution: discharges one `stepPairMut` mutation (4 `BorrowTree` range
accesses + 2 `readTyped` + 2 `writeTyped`) using `stepPairMut_preserves_PairMutInv`
and passes the updated `PairMutInv` invariant to the next statement. -/
theorem step_runPairMutSteps (mem : Memory) (f0 f1 dx dy : UInt32)
    (rest : List (UInt32 × UInt32))
    (h_inv : PairMutInv mem f0 f1)
    (h_cont : ∀ mem1,
      PairMutInv mem1 (specPairStep f0 f1 dx dy).1 (specPairStep f0 f1 dx dy).2 →
      ∃ mem',
        runPairMutSteps mem1 rest = some mem' ∧
        mem'.readTyped pairAllocId 0 u32Codec =
          some (specPairSteps (specPairStep f0 f1 dx dy).1 (specPairStep f0 f1 dx dy).2 rest).1 ∧
        mem'.readTyped pairAllocId 4 u32Codec =
          some (specPairSteps (specPairStep f0 f1 dx dy).1 (specPairStep f0 f1 dx dy).2 rest).2) :
    ∃ mem',
      runPairMutSteps mem ((dx, dy) :: rest) = some mem' ∧
      mem'.readTyped pairAllocId 0 u32Codec = some (specPairSteps f0 f1 ((dx, dy) :: rest)).1 ∧
      mem'.readTyped pairAllocId 4 u32Codec = some (specPairSteps f0 f1 ((dx, dy) :: rest)).2 := by
  obtain ⟨mem1, h_step1, h_inv1, _, _⟩ := stepPairMut_preserves_PairMutInv mem f0 f1 dx dy h_inv
  obtain ⟨mem', h_rest, h_r0, h_r1⟩ := h_cont mem1 h_inv1
  refine ⟨mem', ?_, h_r0, h_r1⟩
  unfold runPairMutSteps
  rw [h_step1]
  exact h_rest

theorem finish_runPairMutSteps (mem : Memory) (f0 f1 : UInt32)
    (h_inv : PairMutInv mem f0 f1) :
    ∃ mem',
      runPairMutSteps mem [] = some mem' ∧
      mem'.readTyped pairAllocId 0 u32Codec = some (specPairSteps f0 f1 []).1 ∧
      mem'.readTyped pairAllocId 4 u32Codec = some (specPairSteps f0 f1 []).2 :=
  ⟨mem, rfl,
    readTyped_of_typedAt mem pairAllocId 0 u32Codec f0 h_inv.1,
    readTyped_of_typedAt mem pairAllocId 4 u32Codec f1 h_inv.2.1⟩

/-- Unrolled 15-step symbolic mutation proof (`K = 15`, 60 `BorrowTree` range
accesses + 30 typed loads + 30 typed stores over universally quantified
`∀ x y z : UInt32`), stepping each statement individually via
`step_runPairMutSteps`. -/
theorem approachB_unrolled_15_steps (x y z : UInt32) :
    let sched :=
      [ (x, y), (y, z), (z, x), (x, y), (y, z)
      , (z, x), (x, y), (y, z), (z, x), (x, y)
      , (y, z), (z, x), (x, y), (y, z), (z, x) ]
    ∃ mem',
      runPairMutSteps (mkEntryMemory x y) sched = some mem' ∧
      mem'.readTyped pairAllocId 0 u32Codec = some (specPairSteps x y sched).1 ∧
      mem'.readTyped pairAllocId 4 u32Codec = some (specPairSteps x y sched).2 := by
  intro sched
  have h0 := entryMemory_satisfies_PairMutInv x y
  apply step_runPairMutSteps _ _ _ _ _ _ h0; intro m1 h1
  apply step_runPairMutSteps _ _ _ _ _ _ h1; intro m2 h2
  apply step_runPairMutSteps _ _ _ _ _ _ h2; intro m3 h3
  apply step_runPairMutSteps _ _ _ _ _ _ h3; intro m4 h4
  apply step_runPairMutSteps _ _ _ _ _ _ h4; intro m5 h5
  apply step_runPairMutSteps _ _ _ _ _ _ h5; intro m6 h6
  apply step_runPairMutSteps _ _ _ _ _ _ h6; intro m7 h7
  apply step_runPairMutSteps _ _ _ _ _ _ h7; intro m8 h8
  apply step_runPairMutSteps _ _ _ _ _ _ h8; intro m9 h9
  apply step_runPairMutSteps _ _ _ _ _ _ h9; intro m10 h10
  apply step_runPairMutSteps _ _ _ _ _ _ h10; intro m11 h11
  apply step_runPairMutSteps _ _ _ _ _ _ h11; intro m12 h12
  apply step_runPairMutSteps _ _ _ _ _ _ h12; intro m13 h13
  apply step_runPairMutSteps _ _ _ _ _ _ h13; intro m14 h14
  apply step_runPairMutSteps _ _ _ _ _ _ h14; intro m15 h15
  exact finish_runPairMutSteps m15 _ _ h15

/-- Unrolled 20-step symbolic mutation proof (`K = 20`, 80 `BorrowTree` range
accesses + 40 typed loads + 40 typed stores over `∀ x y z : UInt32`). -/
theorem approachB_unrolled_20_steps (x y z : UInt32) :
    let sched :=
      [ (x, y), (y, z), (z, x), (x, y), (y, z)
      , (z, x), (x, y), (y, z), (z, x), (x, y)
      , (y, z), (z, x), (x, y), (y, z), (z, x)
      , (x, y), (y, z), (z, x), (x, y), (y, z) ]
    ∃ mem',
      runPairMutSteps (mkEntryMemory x y) sched = some mem' ∧
      mem'.readTyped pairAllocId 0 u32Codec = some (specPairSteps x y sched).1 ∧
      mem'.readTyped pairAllocId 4 u32Codec = some (specPairSteps x y sched).2 := by
  intro sched
  have h0 := entryMemory_satisfies_PairMutInv x y
  apply step_runPairMutSteps _ _ _ _ _ _ h0; intro m1 h1
  apply step_runPairMutSteps _ _ _ _ _ _ h1; intro m2 h2
  apply step_runPairMutSteps _ _ _ _ _ _ h2; intro m3 h3
  apply step_runPairMutSteps _ _ _ _ _ _ h3; intro m4 h4
  apply step_runPairMutSteps _ _ _ _ _ _ h4; intro m5 h5
  apply step_runPairMutSteps _ _ _ _ _ _ h5; intro m6 h6
  apply step_runPairMutSteps _ _ _ _ _ _ h6; intro m7 h7
  apply step_runPairMutSteps _ _ _ _ _ _ h7; intro m8 h8
  apply step_runPairMutSteps _ _ _ _ _ _ h8; intro m9 h9
  apply step_runPairMutSteps _ _ _ _ _ _ h9; intro m10 h10
  apply step_runPairMutSteps _ _ _ _ _ _ h10; intro m11 h11
  apply step_runPairMutSteps _ _ _ _ _ _ h11; intro m12 h12
  apply step_runPairMutSteps _ _ _ _ _ _ h12; intro m13 h13
  apply step_runPairMutSteps _ _ _ _ _ _ h13; intro m14 h14
  apply step_runPairMutSteps _ _ _ _ _ _ h14; intro m15 h15
  apply step_runPairMutSteps _ _ _ _ _ _ h15; intro m16 h16
  apply step_runPairMutSteps _ _ _ _ _ _ h16; intro m17 h17
  apply step_runPairMutSteps _ _ _ _ _ _ h17; intro m18 h18
  apply step_runPairMutSteps _ _ _ _ _ _ h18; intro m19 h19
  apply step_runPairMutSteps _ _ _ _ _ _ h19; intro m20 h20
  exact finish_runPairMutSteps m20 _ _ h20

/-- Unrolled 25-step symbolic mutation proof (`K = 25`, 100 `BorrowTree` range
accesses + 50 typed loads + 50 typed stores over `∀ x y z : UInt32`). -/
theorem approachB_unrolled_25_steps (x y z : UInt32) :
    let sched :=
      [ (x, y), (y, z), (z, x), (x, y), (y, z)
      , (z, x), (x, y), (y, z), (z, x), (x, y)
      , (y, z), (z, x), (x, y), (y, z), (z, x)
      , (x, y), (y, z), (z, x), (x, y), (y, z)
      , (z, x), (x, y), (y, z), (z, x), (x, y) ]
    ∃ mem',
      runPairMutSteps (mkEntryMemory x y) sched = some mem' ∧
      mem'.readTyped pairAllocId 0 u32Codec = some (specPairSteps x y sched).1 ∧
      mem'.readTyped pairAllocId 4 u32Codec = some (specPairSteps x y sched).2 := by
  intro sched
  have h0 := entryMemory_satisfies_PairMutInv x y
  apply step_runPairMutSteps _ _ _ _ _ _ h0; intro m1 h1
  apply step_runPairMutSteps _ _ _ _ _ _ h1; intro m2 h2
  apply step_runPairMutSteps _ _ _ _ _ _ h2; intro m3 h3
  apply step_runPairMutSteps _ _ _ _ _ _ h3; intro m4 h4
  apply step_runPairMutSteps _ _ _ _ _ _ h4; intro m5 h5
  apply step_runPairMutSteps _ _ _ _ _ _ h5; intro m6 h6
  apply step_runPairMutSteps _ _ _ _ _ _ h6; intro m7 h7
  apply step_runPairMutSteps _ _ _ _ _ _ h7; intro m8 h8
  apply step_runPairMutSteps _ _ _ _ _ _ h8; intro m9 h9
  apply step_runPairMutSteps _ _ _ _ _ _ h9; intro m10 h10
  apply step_runPairMutSteps _ _ _ _ _ _ h10; intro m11 h11
  apply step_runPairMutSteps _ _ _ _ _ _ h11; intro m12 h12
  apply step_runPairMutSteps _ _ _ _ _ _ h12; intro m13 h13
  apply step_runPairMutSteps _ _ _ _ _ _ h13; intro m14 h14
  apply step_runPairMutSteps _ _ _ _ _ _ h14; intro m15 h15
  apply step_runPairMutSteps _ _ _ _ _ _ h15; intro m16 h16
  apply step_runPairMutSteps _ _ _ _ _ _ h16; intro m17 h17
  apply step_runPairMutSteps _ _ _ _ _ _ h17; intro m18 h18
  apply step_runPairMutSteps _ _ _ _ _ _ h18; intro m19 h19
  apply step_runPairMutSteps _ _ _ _ _ _ h19; intro m20 h20
  apply step_runPairMutSteps _ _ _ _ _ _ h20; intro m21 h21
  apply step_runPairMutSteps _ _ _ _ _ _ h21; intro m22 h22
  apply step_runPairMutSteps _ _ _ _ _ _ h22; intro m23 h23
  apply step_runPairMutSteps _ _ _ _ _ _ h23; intro m24 h24
  apply step_runPairMutSteps _ _ _ _ _ _ h24; intro m25 h25
  exact finish_runPairMutSteps m25 _ _ h25

/-- Unrolled 30-step symbolic mutation proof (`K = 30`, 120 `BorrowTree` range
accesses + 60 typed loads + 60 typed stores over `∀ x y z : UInt32`). -/
theorem approachB_unrolled_30_steps (x y z : UInt32) :
    let sched :=
      [ (x, y), (y, z), (z, x), (x, y), (y, z)
      , (z, x), (x, y), (y, z), (z, x), (x, y)
      , (y, z), (z, x), (x, y), (y, z), (z, x)
      , (x, y), (y, z), (z, x), (x, y), (y, z)
      , (z, x), (x, y), (y, z), (z, x), (x, y)
      , (y, z), (z, x), (x, y), (y, z), (z, x) ]
    ∃ mem',
      runPairMutSteps (mkEntryMemory x y) sched = some mem' ∧
      mem'.readTyped pairAllocId 0 u32Codec = some (specPairSteps x y sched).1 ∧
      mem'.readTyped pairAllocId 4 u32Codec = some (specPairSteps x y sched).2 := by
  intro sched
  have h0 := entryMemory_satisfies_PairMutInv x y
  apply step_runPairMutSteps _ _ _ _ _ _ h0; intro m1 h1
  apply step_runPairMutSteps _ _ _ _ _ _ h1; intro m2 h2
  apply step_runPairMutSteps _ _ _ _ _ _ h2; intro m3 h3
  apply step_runPairMutSteps _ _ _ _ _ _ h3; intro m4 h4
  apply step_runPairMutSteps _ _ _ _ _ _ h4; intro m5 h5
  apply step_runPairMutSteps _ _ _ _ _ _ h5; intro m6 h6
  apply step_runPairMutSteps _ _ _ _ _ _ h6; intro m7 h7
  apply step_runPairMutSteps _ _ _ _ _ _ h7; intro m8 h8
  apply step_runPairMutSteps _ _ _ _ _ _ h8; intro m9 h9
  apply step_runPairMutSteps _ _ _ _ _ _ h9; intro m10 h10
  apply step_runPairMutSteps _ _ _ _ _ _ h10; intro m11 h11
  apply step_runPairMutSteps _ _ _ _ _ _ h11; intro m12 h12
  apply step_runPairMutSteps _ _ _ _ _ _ h12; intro m13 h13
  apply step_runPairMutSteps _ _ _ _ _ _ h13; intro m14 h14
  apply step_runPairMutSteps _ _ _ _ _ _ h14; intro m15 h15
  apply step_runPairMutSteps _ _ _ _ _ _ h15; intro m16 h16
  apply step_runPairMutSteps _ _ _ _ _ _ h16; intro m17 h17
  apply step_runPairMutSteps _ _ _ _ _ _ h17; intro m18 h18
  apply step_runPairMutSteps _ _ _ _ _ _ h18; intro m19 h19
  apply step_runPairMutSteps _ _ _ _ _ _ h19; intro m20 h20
  apply step_runPairMutSteps _ _ _ _ _ _ h20; intro m21 h21
  apply step_runPairMutSteps _ _ _ _ _ _ h21; intro m22 h22
  apply step_runPairMutSteps _ _ _ _ _ _ h22; intro m23 h23
  apply step_runPairMutSteps _ _ _ _ _ _ h23; intro m24 h24
  apply step_runPairMutSteps _ _ _ _ _ _ h24; intro m25 h25
  apply step_runPairMutSteps _ _ _ _ _ _ h25; intro m26 h26
  apply step_runPairMutSteps _ _ _ _ _ _ h26; intro m27 h27
  apply step_runPairMutSteps _ _ _ _ _ _ h27; intro m28 h28
  apply step_runPairMutSteps _ _ _ _ _ _ h28; intro m29 h29
  apply step_runPairMutSteps _ _ _ _ _ _ h29; intro m30 h30
  exact finish_runPairMutSteps m30 _ _ h30

/-- **Approach B 15-Step Symbolic Mutation Theorem** (`K = 15`, universally quantified `∀ x y z : UInt32`). -/
theorem approachB_15_steps (x y z : UInt32) :
    let sched := mkSymbolicSchedule x y z 15
    ∃ mem',
      runPairMutSteps (mkEntryMemory x y) sched = some mem' ∧
      mem'.readTyped pairAllocId 0 u32Codec = some (specPairSteps x y sched).1 ∧
      mem'.readTyped pairAllocId 4 u32Codec = some (specPairSteps x y sched).2 := by
  intro sched
  obtain ⟨mem', h_run, _, h_r0, h_r1⟩ :=
    runPairMutSteps_spec sched (mkEntryMemory x y) x y (entryMemory_satisfies_PairMutInv x y)
  exact ⟨mem', h_run, h_r0, h_r1⟩

/-- **Approach B 20-Step Symbolic Mutation Theorem** (`K = 20`, universally quantified `∀ x y z : UInt32`). -/
theorem approachB_20_steps (x y z : UInt32) :
    let sched := mkSymbolicSchedule x y z 20
    ∃ mem',
      runPairMutSteps (mkEntryMemory x y) sched = some mem' ∧
      mem'.readTyped pairAllocId 0 u32Codec = some (specPairSteps x y sched).1 ∧
      mem'.readTyped pairAllocId 4 u32Codec = some (specPairSteps x y sched).2 := by
  intro sched
  obtain ⟨mem', h_run, _, h_r0, h_r1⟩ :=
    runPairMutSteps_spec sched (mkEntryMemory x y) x y (entryMemory_satisfies_PairMutInv x y)
  exact ⟨mem', h_run, h_r0, h_r1⟩

/-- **Approach B 25-Step Symbolic Mutation Theorem** (`K = 25`, universally quantified `∀ x y z : UInt32`). -/
theorem approachB_25_steps (x y z : UInt32) :
    let sched := mkSymbolicSchedule x y z 25
    ∃ mem',
      runPairMutSteps (mkEntryMemory x y) sched = some mem' ∧
      mem'.readTyped pairAllocId 0 u32Codec = some (specPairSteps x y sched).1 ∧
      mem'.readTyped pairAllocId 4 u32Codec = some (specPairSteps x y sched).2 := by
  intro sched
  obtain ⟨mem', h_run, _, h_r0, h_r1⟩ :=
    runPairMutSteps_spec sched (mkEntryMemory x y) x y (entryMemory_satisfies_PairMutInv x y)
  exact ⟨mem', h_run, h_r0, h_r1⟩

/-- **Approach B 30-Step Symbolic Mutation Theorem** (`K = 30`, universally quantified `∀ x y z : UInt32`). -/
theorem approachB_30_steps (x y z : UInt32) :
    let sched := mkSymbolicSchedule x y z 30
    ∃ mem',
      runPairMutSteps (mkEntryMemory x y) sched = some mem' ∧
      mem'.readTyped pairAllocId 0 u32Codec = some (specPairSteps x y sched).1 ∧
      mem'.readTyped pairAllocId 4 u32Codec = some (specPairSteps x y sched).2 := by
  intro sched
  obtain ⟨mem', h_run, _, h_r0, h_r1⟩ :=
    runPairMutSteps_spec sched (mkEntryMemory x y) x y (entryMemory_satisfies_PairMutInv x y)
  exact ⟨mem', h_run, h_r0, h_r1⟩

/-- **Approach A (Direct Byte-List & BorrowTree Unfolding) Baseline**:
Demonstrates direct unfolding of `stepPairMut`, `writeSlice`, `readSlice`,
`encodeU32LE`, `decodeU32LE`, and `BorrowTree.performAccessRange` across
symbolic `x y z : UInt32` (using `packU32_extract` to collapse each 4-byte
pack/extract roundtrip). For `K = 2` steps this succeeds, whereas without
`packU32_extract` (`Approach A1`), each step multiplies the symbolic AST by 4x
($O(4^K)$), and even with `packU32_extract` (`Approach A2`), re-reducing the
4-node × 8-byte `BorrowTree` on every step scales superlinearly compared to
Approach B. -/
theorem packU32_extract_simp (v : UInt32) :
    packU32 v.toUInt8 (v >>> 8).toUInt8 (v >>> 16).toUInt8 (v >>> 24).toUInt8 = v := by
  have h0 : (v >>> 0).toUInt8 = v.toUInt8 := by simp
  rw [← h0]
  exact packU32_extract v

theorem approachA_unfold_2_steps (x y z : UInt32) :
    let sched := [(x, y), (y, z)]
    match runPairMutSteps (mkEntryMemory x y) sched with
    | none => False
    | some mem' =>
      mem'.readTyped pairAllocId 0 u32Codec = some (specPairSteps x y sched).1 ∧
      mem'.readTyped pairAllocId 4 u32Codec = some (specPairSteps x y sched).2 := by
  simp [-UInt32.toUInt8_add, -UInt32.toUInt8_xor,
    runPairMutSteps, stepPairMut, mkEntryMemory, entryBorrowTree8, entryProt, mutTag,
    pairAllocId, BorrowTree.performAccessRange, BorrowTree.findAncestors, findAncestorsNodes,
    updateNodeRange, mapOption, LocationState.performAccess, performPermAccess,
    childRead, childWrite, foreignRead, foreignWrite, nodeRel, hasTag,
    Memory.findAlloc, Memory.updateAlloc, findAllocList, updateAllocList,
    Memory.readTyped, Memory.writeTyped, u32Codec, encodeU32LE, decodeU32LE,
    readSlice, writeSlice, List.replicate, packU32_extract_simp, specPairSteps, specPairStep]

/-! ## Section 6: Kernel Axiom Audit (`#print axioms`) -/

#print axioms read_write_same
#print axioms read_write_disjoint
#print axioms typedAt_transmute
#print axioms transmute_u32_pair_u64
#print axioms checkUniqueWritePerm_sound
#print axioms footprintAt_preserve_local_write
#print axioms footprintAt_preserve_disjoint_write
#print axioms footprintAt_preserve_foreign_read
#print axioms resolveOffset_offsetPtr_rootPtr
#print axioms validFreshBaseAddr_nonempty
#print axioms wp_forceAllocation_choice
#print axioms wp_ten_nondet_stack_allocs
#print axioms approachB_unrolled_15_steps
#print axioms approachB_unrolled_20_steps
#print axioms approachB_unrolled_25_steps
#print axioms approachB_unrolled_30_steps
#print axioms approachB_15_steps
#print axioms approachB_20_steps
#print axioms approachB_25_steps
#print axioms approachB_30_steps
#print axioms approachA_unfold_2_steps

end MemoryLensAndScalingProbe
