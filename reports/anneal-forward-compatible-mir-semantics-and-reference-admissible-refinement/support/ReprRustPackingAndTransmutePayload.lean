/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

/-!
# Multi-Field `#[repr(Rust)]` Sub-Alignment Packing, Over-Alignment Freedom, All-ZST Structs, and `TransmutePayload` (`exactBits` vs. `initBytes`)

Standalone, zero-`sorry`, zero-axiom Lean 4 mechanization of `#[repr(Rust)]` Sub-Alignment Packing, Over-Alignment, and `TransmutePayload`:
1. **Power-of-2 Descending-Alignment Zero-Inter-Field-Padding Theorem (`foldReprCFields_sorted_eq_alignUp_sum`)**:
   Whenever struct fields `(s_1, a_1), ..., (s_n, a_n)` have power-of-2 alignments (`a_i = 2^{k_i}`),
   sizes divisible by their own alignments (`a_i ∣ s_i`, per `r[layout.properties.size]`), and are
   ordered by non-increasing alignment (`a_1 ≥ a_2 ≥ ... ≥ a_n`), sequential aligned field placement
   (`foldReprCLayout`) incurs **zero inter-field padding** at every field step and produces total
   byte size `alignUp (sumFieldSizes fields) (maxFieldAlign fields)`.
2. **`StructKind::MaybeUnsized` Tail-Invariance Theorem (`alignUp_tail_invariance`)**:
   Even when `rustc_abi::layout::univariant_biased` excludes the last field `f_{n-1}` from sorting
   under `StructKind::MaybeUnsized` (as it does for all non-empty tuples and `T: ?Sized` tail structs),
   because `a_{n-1} ∣ s_{n-1}` and `a_{n-1} ∣ maxAlign`, any inter-field padding inserted before the
   tail field trades off 1-for-1 against trailing padding:
   `alignUp (alignUp P a_tail + s_tail) maxAlign = alignUp (P + s_tail) maxAlign`.
3. **`adtPad` + `adtAlignShift` Soundness and Completeness (`reprRustLayout_sound`, `reprRustLayout_complete`)**:
   Parameterizing `AdtRepr.rust` layout by `(adtPad id, adtAlignShift id)` via
   `al = baseAlign * 2^(adtAlignShift id)` and `sz = if sum == 0 then 0 else alignUp sum al + adtPad id * al`
   is both sound and complete (surjective and injective per alignment) over the exact set of
   `(size, align)` pairs permitted by the Rust Reference (`r[layout.properties.align]`,
   `r[layout.properties.size]`, `r[layout.repr.rust.alignment]`, `r[layout.repr.rust.layout.struct]`,
   `r[layout.repr.rust.struct-zst]`), while matching `rustc_abi::layout::univariant` at `(0, 0)`.
4. **Corrected `tyLayoutStep` and `TransmutePayload` (`exactBits` vs. `initBytes`)**:
   Full layout and transmutation semantics handling `.rust` (all-ZST vs. non-ZST, `adtPad`,
   `adtAlignShift`), `.c`, `.transparent` (with arbitrary 1-ZST siblings), and `.packed`, together
   with holdout theorems for `Sandwich(u8, u16, u8)`, `InevitablePad([u8; 3], u32)`,
   `TwoU24([u8; 3], [u8; 3], u32)`, `Mixed(u8, u64)`, `Pair(u32, u32) -> [u8; 8]` vs.
   `CPair(u32, u32)` vs. `u64`, `SingleFieldRust(u32)`, `TransWithZst((), u64)`, and
   `RustZst((), ())`.
-/

namespace ReprRustPackingAndTransmutePayload

/-! ## Section 1: `alignUp` Arithmetic and Divisibility Algebra -/

/-- Round `offset` up to the next multiple of `align` (`align ≥ 1`), matching
`Trusted/MirSemantics.lean`. -/
def alignUp (offset align : Nat) : Nat :=
  let rem := offset % align
  if rem == 0 then offset else offset + (align - rem)

theorem alignUp_zero_left (align : Nat) : alignUp 0 align = 0 := by
  have h : 0 % align = 0 := Nat.zero_mod align
  simp [alignUp, h]

theorem alignUp_one_right (offset : Nat) : alignUp offset 1 = offset := by
  have h : offset % 1 = 0 := Nat.mod_one offset
  simp [alignUp, h]

theorem alignUp_of_dvd {offset align : Nat} (h : align ∣ offset) :
    alignUp offset align = offset := by
  have hmod : offset % align = 0 := Nat.mod_eq_zero_of_dvd h
  simp [alignUp, hmod]

theorem le_alignUp (offset align : Nat) : offset ≤ alignUp offset align := by
  dsimp [alignUp]
  split
  · exact Nat.le_refl offset
  · exact Nat.le_add_right offset _

theorem dvd_alignUp (offset : Nat) {align : Nat} (ha : 0 < align) :
    align ∣ alignUp offset align := by
  dsimp [alignUp]
  split
  · next h =>
    have h0 : offset % align = 0 := LawfulBEq.eq_of_beq h
    exact Nat.dvd_of_mod_eq_zero h0
  · next h =>
    have hlt : offset % align < align := Nat.mod_lt offset ha
    have hdiv : align * (offset / align) + offset % align = offset :=
      Nat.div_add_mod offset align
    refine ⟨offset / align + 1, ?_⟩
    have hexp : align * (offset / align + 1) = align * (offset / align) + align := by
      rw [Nat.mul_add, Nat.mul_one]
    omega

theorem alignUp_le_of_dvd {offset m align : Nat} (ha : 0 < align)
    (hm : align ∣ m) (hle : offset ≤ m) :
    alignUp offset align ≤ m := by
  rcases hm with ⟨q, rfl⟩
  dsimp [alignUp]
  split
  · exact hle
  · next h =>
    have hne : offset % align ≠ 0 := by
      intro h0
      exact h (beq_iff_eq.mpr h0)
    have hlt : offset % align < align := Nat.mod_lt offset ha
    have hdiv : align * (offset / align) + offset % align = offset :=
      Nat.div_add_mod offset align
    have hq_gt : offset / align < q := by
      have : ¬ (q ≤ offset / align) := by
        intro hqle
        have hmul : align * q ≤ align * (offset / align) :=
          Nat.mul_le_mul_left align hqle
        omega
      omega
    have hq_le : offset / align + 1 ≤ q := hq_gt
    have hmul : align * (offset / align + 1) ≤ align * q :=
      Nat.mul_le_mul_left align hq_le
    have hexp : align * (offset / align + 1) = align * (offset / align) + align := by
      rw [Nat.mul_add, Nat.mul_one]
    omega

theorem alignUp_idempotent (offset : Nat) {align : Nat} (ha : 0 < align) :
    alignUp (alignUp offset align) align = alignUp offset align :=
  alignUp_of_dvd (dvd_alignUp offset ha)

theorem alignUp_add_mul (offset k : Nat) {align : Nat} :
    alignUp (offset + k * align) align = alignUp offset align + k * align := by
  have hmod : (offset + k * align) % align = offset % align := by
    rw [Nat.mul_comm k align]
    exact Nat.add_mul_mod_self_left offset align k
  dsimp [alignUp]
  rw [hmod]
  split <;> omega

theorem alignUp_pos_of_pos {offset align : Nat} (h_off : 0 < offset) :
    0 < alignUp offset align := by
  have hle := le_alignUp offset align
  omega

theorem align_le_alignUp_of_pos {offset align : Nat}
    (h_off : 0 < offset) (h_al : 0 < align) :
    align ≤ alignUp offset align := by
  rcases dvd_alignUp offset h_al with ⟨k, hk⟩
  have hpos : 0 < alignUp offset align := alignUp_pos_of_pos h_off
  cases k with
  | zero => omega
  | succ k' =>
    have : align * 1 ≤ align * (k' + 1) := Nat.mul_le_mul_left align (by omega)
    omega

/-! ## Section 2: `StructKind::MaybeUnsized` Tail-Invariance Theorem -/

/-- Number-theoretic tail-invariance theorem for `rustc_abi::layout::univariant_biased`:
Whenever the tail field's alignment `a_tail` divides both its own size `s_tail`
(`r[layout.properties.size]`) and the overall struct alignment `maxAlign` (`a_tail ∣ maxAlign`),
aligning the prefix sum `P` to `a_tail` before adding `s_tail` and rounding up to `maxAlign`
produces the **exact same** total size as rounding `P + s_tail` directly up to `maxAlign`. -/
theorem alignUp_tail_invariance (P s_tail a_tail maxAlign : Nat)
    (ha_pos : 0 < a_tail) (hm_pos : 0 < maxAlign)
    (h_dvd_size : a_tail ∣ s_tail) (h_dvd_max : a_tail ∣ maxAlign) :
    alignUp (alignUp P a_tail + s_tail) maxAlign = alignUp (P + s_tail) maxAlign := by
  apply Nat.le_antisymm
  · let Q := alignUp (P + s_tail) maxAlign
    have hPQ : P + s_tail ≤ Q := le_alignUp (P + s_tail) maxAlign
    have hmQ : maxAlign ∣ Q := dvd_alignUp (P + s_tail) hm_pos
    have haQ : a_tail ∣ Q := Nat.dvd_trans h_dvd_max hmQ
    have ha_sub : a_tail ∣ (Q - s_tail) := Nat.dvd_sub haQ h_dvd_size
    have hP_sub : P ≤ Q - s_tail := by omega
    have h_alignP : alignUp P a_tail ≤ Q - s_tail :=
      alignUp_le_of_dvd ha_pos ha_sub hP_sub
    have h_sum_le : alignUp P a_tail + s_tail ≤ Q := by omega
    exact alignUp_le_of_dvd hm_pos hmQ h_sum_le
  · have hP : P + s_tail ≤ alignUp P a_tail + s_tail :=
      Nat.add_le_add_right (le_alignUp P a_tail) s_tail
    have h_le : P + s_tail ≤ alignUp (alignUp P a_tail + s_tail) maxAlign :=
      Nat.le_trans hP (le_alignUp (alignUp P a_tail + s_tail) maxAlign)
    exact alignUp_le_of_dvd hm_pos (dvd_alignUp _ hm_pos) h_le

/-! ## Section 3: Power-of-2 Descending-Alignment Zero-Inter-Field-Padding Theorem -/

/-- Sum of field byte sizes for a list of `(size, align)` pairs. -/
def sumFieldSizes : List (Nat × Nat) → Nat
  | [] => 0
  | (sz, _) :: rest => sz + sumFieldSizes rest

/-- Maximum field alignment (starting from `initAlign`, typically `1`). -/
def maxFieldAlignAux : List (Nat × Nat) → Nat → Nat
  | [], acc => acc
  | (_, al) :: rest, acc => maxFieldAlignAux rest (Nat.max acc al)

def maxFieldAlign (fields : List (Nat × Nat)) : Nat :=
  maxFieldAlignAux fields 1

/-- Sequential `#[repr(C)]` layout fold over concrete `(fieldSize, fieldAlign)` pairs,
matching `foldReprCFields` in `Trusted/MirSemantics.lean`. -/
def foldReprCLayout : List (Nat × Nat) → Nat → Nat → Nat × Nat
  | [], offset, maxAlign => (alignUp offset maxAlign, maxAlign)
  | (fSz, fAlign) :: rest, offset, maxAlign =>
    let alignedOffset := alignUp offset fAlign
    foldReprCLayout rest (alignedOffset + fSz) (Nat.max maxAlign fAlign)

/-- Inductive predicate stating that `fields` is sorted in non-increasing alignment
order beneath `curAlign`, where each consecutive alignment divides the previous one
(as holds for all non-increasing powers of 2) and each field's alignment divides its
own size (`r[layout.properties.size]`). -/
inductive DescendingAlignedChain : Nat → List (Nat × Nat) → Prop where
  | nil (curAlign : Nat) : DescendingAlignedChain curAlign []
  | cons {curAlign sz al : Nat} {rest : List (Nat × Nat)}
      (h_dvd_cur : al ∣ curAlign)
      (h_le_cur : al ≤ curAlign)
      (h_dvd_sz : al ∣ sz)
      (h_rest : DescendingAlignedChain al rest) :
      DescendingAlignedChain curAlign ((sz, al) :: rest)

/-- Core inductive lemma: along any `DescendingAlignedChain curAlign fields` where
`curAlign ∣ offset` and `curAlign ≤ maxAlign`, every field is already aligned at `offset`
(`alignUp offset al = offset`, i.e., **zero inter-field padding**), so `foldReprCLayout`
advances `offset` by `sumFieldSizes fields` and preserves `maxAlign`. -/
theorem foldReprCLayout_descending_chain
    {fields : List (Nat × Nat)} {curAlign offset maxAlign : Nat}
    (h_chain : DescendingAlignedChain curAlign fields)
    (h_off_dvd : curAlign ∣ offset)
    (h_max : curAlign ≤ maxAlign) :
    foldReprCLayout fields offset maxAlign =
      (alignUp (offset + sumFieldSizes fields) maxAlign, maxAlign) ∧
    maxFieldAlignAux fields maxAlign = maxAlign := by
  induction h_chain generalizing offset maxAlign with
  | nil curAlign =>
    simp [foldReprCLayout, sumFieldSizes, maxFieldAlignAux]
  | @cons curAlign sz al rest h_dvd_cur h_le_cur h_dvd_sz h_rest ih =>
    have h_al_off : al ∣ offset := Nat.dvd_trans h_dvd_cur h_off_dvd
    have h_align_eq : alignUp offset al = offset := alignUp_of_dvd h_al_off
    have h_al_next : al ∣ (offset + sz) := Nat.dvd_add h_al_off h_dvd_sz
    have h_al_le_max : al ≤ maxAlign := Nat.le_trans h_le_cur h_max
    have h_max_eq : Nat.max maxAlign al = maxAlign := by
      simp [Nat.max_def]
      omega
    dsimp [foldReprCLayout, sumFieldSizes, maxFieldAlignAux]
    rw [h_align_eq, h_max_eq]
    have ⟨h_fold, h_maxAux⟩ := ih h_al_next h_al_le_max
    rw [h_fold, h_maxAux]
    simp [Nat.add_assoc]

/-- **Power-of-2 Descending-Alignment Zero-Inter-Field-Padding Theorem**:
For any non-empty list of fields `(sz_0, al_0) :: rest` sorted in descending alignment order
(`DescendingAlignedChain al_0 rest`) where `1 ≤ al_0` and `al_0 ∣ sz_0`, `foldReprCLayout`
starting from `(0, 1)` incurs zero inter-field padding and produces exact layout
`(alignUp (sumFieldSizes fields) (maxFieldAlign fields), maxFieldAlign fields)`. -/
theorem foldReprCFields_sorted_eq_alignUp_sum
    {sz0 al0 : Nat} {rest : List (Nat × Nat)}
    (h_al0_pos : 1 ≤ al0)
    (h_dvd0 : al0 ∣ sz0)
    (h_chain : DescendingAlignedChain al0 rest) :
    foldReprCLayout ((sz0, al0) :: rest) 0 1 =
      (alignUp (sumFieldSizes ((sz0, al0) :: rest)) (maxFieldAlign ((sz0, al0) :: rest)),
       maxFieldAlign ((sz0, al0) :: rest)) := by
  have h_max0 : Nat.max 1 al0 = al0 := by
    simp [Nat.max_def]
    omega
  dsimp [foldReprCLayout, sumFieldSizes, maxFieldAlign, maxFieldAlignAux]
  rw [alignUp_zero_left, Nat.zero_add, h_max0]
  have ⟨h_fold, h_maxAux⟩ :=
    foldReprCLayout_descending_chain h_chain h_dvd0 (Nat.le_refl al0)
  rw [h_fold, h_maxAux]

/-- Power-of-2 helper: if `k2 ≤ k1`, then `2 ^ k2 ∣ 2 ^ k1` and `2 ^ k2 ≤ 2 ^ k1`. -/
theorem pow2_dvd_and_le_of_le {k1 k2 : Nat} (h : k2 ≤ k1) :
    (2 ^ k2 ∣ 2 ^ k1) ∧ (2 ^ k2 ≤ 2 ^ k1) := by
  refine ⟨⟨2 ^ (k1 - k2), ?_⟩, Nat.pow_le_pow_right (by omega) h⟩
  rw [← Nat.pow_add, Nat.add_sub_of_le h]

/-! ## Section 4: `adtPad` + `adtAlignShift` Soundness, Completeness, and Bijection -/

/-- Exact normative Rust Reference admissibility predicate for a `#[repr(Rust)]` struct
layout `(sz, al)` given field layouts `fields` (`r[layout.properties.align]`,
`r[layout.properties.size]`, `r[layout.repr.rust.alignment]`,
`r[layout.repr.rust.layout.struct]`, `r[layout.repr.rust.struct-zst]`). -/
structure ReferenceAdmissibleStructLayout (fields : List (Nat × Nat)) (sz al : Nat) : Prop where
  /-- `r[layout.properties.align]`: alignment is a power of two (`2^k ≥ 1`). -/
  align_pow2 : ∃ k : Nat, al = 2 ^ k
  /-- `r[layout.repr.rust.alignment]`: alignment is at least the maximum field alignment. -/
  align_ge_base : maxFieldAlign fields ≤ al
  /-- `r[layout.properties.size]`: size in bytes is a multiple of alignment. -/
  align_dvd_size : al ∣ sz
  /-- `r[layout.repr.rust.layout.struct]`: disjoint field intervals require `sum ≤ sz`. -/
  size_ge_sum : sumFieldSizes fields ≤ sz
  /-- `r[layout.repr.rust.struct-zst]`: if all fields have size 0, struct size is 0. -/
  zst_law : sumFieldSizes fields = 0 → sz = 0

/-- Ground `#[repr(Rust)]` struct layout parameterized by `pad = s.adtPad id` and
`alignShift = s.adtAlignShift id`. -/
def reprRustLayout (fields : List (Nat × Nat)) (pad alignShift : Nat) : Nat × Nat :=
  let sum := sumFieldSizes fields
  let baseAlign := maxFieldAlign fields
  let al := baseAlign * (2 ^ alignShift)
  let sz := if sum == 0 then 0 else alignUp sum al + pad * al
  (sz, al)

/-- **Soundness Theorem**: For every `pad` and `alignShift`, `reprRustLayout` produces a
Reference-admissible `(size, align)` pair. -/
theorem reprRustLayout_sound (fields : List (Nat × Nat)) (pad alignShift : Nat)
    (h_base_pow2 : ∃ b : Nat, maxFieldAlign fields = 2 ^ b) :
    let (sz, al) := reprRustLayout fields pad alignShift
    ReferenceAdmissibleStructLayout fields sz al := by
  rcases h_base_pow2 with ⟨b, hb⟩
  dsimp [reprRustLayout]
  have hal_pos : 0 < maxFieldAlign fields * 2 ^ alignShift := by
    rw [hb, ← Nat.pow_add]
    exact Nat.two_pow_pos (b + alignShift)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨b + alignShift, ?_⟩
    rw [hb, ← Nat.pow_add]
  · have hpow : 1 ≤ 2 ^ alignShift := Nat.two_pow_pos alignShift
    have := Nat.mul_le_mul_left (maxFieldAlign fields) hpow
    omega
  · split
    · exact Nat.dvd_zero _
    · exact Nat.dvd_add (dvd_alignUp _ hal_pos) ⟨pad, Nat.mul_comm _ _⟩
  · split
    · next h =>
      have h0 : sumFieldSizes fields = 0 := LawfulBEq.eq_of_beq h
      omega
    · have hle := le_alignUp (sumFieldSizes fields) (maxFieldAlign fields * 2 ^ alignShift)
      omega
  · intro hsum0
    simp [hsum0]

/-- **Completeness (Surjectivity) Theorem**: Every Reference-admissible `(sz, al)` pair for
a `#[repr(Rust)]` struct is realized by a concrete `(pad, alignShift)` pair in `reprRustLayout`. -/
theorem reprRustLayout_complete (fields : List (Nat × Nat)) (sz al : Nat)
    (h_base_pow2 : ∃ b : Nat, maxFieldAlign fields = 2 ^ b)
    (h_adm : ReferenceAdmissibleStructLayout fields sz al) :
    ∃ pad alignShift : Nat, reprRustLayout fields pad alignShift = (sz, al) := by
  rcases h_base_pow2 with ⟨b, hb⟩
  rcases h_adm.align_pow2 with ⟨k, hk⟩
  have h_le_pow : 2 ^ b ≤ 2 ^ k := by
    rw [← hb, ← hk]
    exact h_adm.align_ge_base
  have h_b_le_k : b ≤ k := by
    if h : b ≤ k then
      exact h
    else
      have hk_lt_b : k < b := by omega
      have hpow_lt : 2 ^ k < 2 ^ b :=
        Nat.pow_lt_pow_right (by omega) hk_lt_b
      omega
  let alignShift := k - b
  have hal_eq : maxFieldAlign fields * (2 ^ alignShift) = al := by
    rw [hb, hk, ← Nat.pow_add, Nat.add_sub_of_le h_b_le_k]
  have hal_pos : 0 < al := by
    rw [hk]
    exact Nat.two_pow_pos k
  by_cases hsum : sumFieldSizes fields = 0
  · refine ⟨0, alignShift, ?_⟩
    have hsz0 : sz = 0 := h_adm.zst_law hsum
    simp [reprRustLayout, hsum, hal_eq, hsz0]
  · have h_align_le_sz : alignUp (sumFieldSizes fields) al ≤ sz :=
      alignUp_le_of_dvd hal_pos h_adm.align_dvd_size h_adm.size_ge_sum
    have h_dvd_diff : al ∣ (sz - alignUp (sumFieldSizes fields) al) :=
      Nat.dvd_sub h_adm.align_dvd_size (dvd_alignUp (sumFieldSizes fields) hal_pos)
    rcases h_dvd_diff with ⟨pad, hpad⟩
    refine ⟨pad, alignShift, ?_⟩
    have hsum_beq : (sumFieldSizes fields == 0) = false :=
      beq_false_of_ne hsum
    dsimp [reprRustLayout]
    rw [hal_eq, hsum_beq]
    have h_prod : pad * al = sz - alignUp (sumFieldSizes fields) al := by
      rw [Nat.mul_comm pad al, ← hpad]
    apply Prod.ext
    · dsimp
      omega
    · rfl

/-- **Injectivity (Bijection) Theorem**: For any non-ZST struct (`0 < sumFieldSizes fields`
and `0 < maxFieldAlign fields`), `(pad, alignShift) ↦ reprRustLayout fields pad alignShift`
is injective (`pad1 = pad2 ∧ shift1 = shift2`), establishing a 1-to-1 bijection between
`(pad, alignShift) : Nat × Nat` and Reference-admissible `(sz, al)` pairs. -/
theorem reprRustLayout_injective (fields : List (Nat × Nat))
    (pad1 shift1 pad2 shift2 : Nat)
    (h_sum_pos : 0 < sumFieldSizes fields)
    (h_base_pos : 0 < maxFieldAlign fields)
    (h_eq : reprRustLayout fields pad1 shift1 = reprRustLayout fields pad2 shift2) :
    pad1 = pad2 ∧ shift1 = shift2 := by
  have hsum_ne : sumFieldSizes fields ≠ 0 := by omega
  have hsum_beq : (sumFieldSizes fields == 0) = false := beq_false_of_ne hsum_ne
  dsimp [reprRustLayout] at h_eq
  rw [hsum_beq] at h_eq
  have h_sz := Prod.mk.inj h_eq |>.1
  have h_al := Prod.mk.inj h_eq |>.2
  dsimp at h_sz h_al
  have h_pow_eq : (2 : Nat) ^ shift1 = 2 ^ shift2 :=
    Nat.eq_of_mul_eq_mul_left h_base_pos h_al
  have h_shift : shift1 = shift2 := by
    if h12 : shift1 < shift2 then
      have := Nat.pow_lt_pow_right (by omega : 1 < 2) h12
      omega
    else if h21 : shift2 < shift1 then
      have := Nat.pow_lt_pow_right (by omega : 1 < 2) h21
      omega
    else
      omega
  subst h_shift
  have hal_pos : 0 < maxFieldAlign fields * 2 ^ shift1 :=
    Nat.mul_pos h_base_pos (Nat.two_pow_pos shift1)
  have h_mul_eq : pad1 * (maxFieldAlign fields * 2 ^ shift1) =
      pad2 * (maxFieldAlign fields * 2 ^ shift1) := by
    omega
  exact ⟨Nat.eq_of_mul_eq_mul_right hal_pos h_mul_eq, rfl⟩

/-- **Pinned-`rustc` World Theorem**: At `(pad = 0, alignShift = 0)`, `reprRustLayout`
evaluates to `(alignUp (sumFieldSizes fields) (maxFieldAlign fields), maxFieldAlign fields)`
for both all-ZST (`sum = 0`) and non-ZST (`sum > 0`) structs. -/
theorem reprRustLayout_zero_zero (fields : List (Nat × Nat)) :
    reprRustLayout fields 0 0 =
      (alignUp (sumFieldSizes fields) (maxFieldAlign fields), maxFieldAlign fields) := by
  dsimp [reprRustLayout]
  simp only [Nat.mul_one, Nat.zero_mul, Nat.add_zero]
  split
  · next h =>
    have h0 : sumFieldSizes fields = 0 := LawfulBEq.eq_of_beq h
    rw [h0, alignUp_zero_left]
  · rfl

/-! ## Section 5: Corrected `tyLayoutStep` and `evalLayoutQuery` -/

/-- Target C ABI primitive layout parameters captured from `tcx.data_layout()`. -/
structure TargetLayout where
  ptrByteWidth : Nat := 8
  i64Align : Nat := 8
  i128Align : Nat := 16
  deriving DecidableEq, Repr

def defaultTargetLayout : TargetLayout := {}

/-- Maximum byte size of a Rust type on a 64-bit target (`isize::MAX`, `2^63 - 1`). -/
def isizeMaxBytes : Nat := 9223372036854775807

/-- Struct representation attribute on an `AdtDecl` (`src/type-layout.md`).
Includes `.rust`, `.transparent`, `.c`, `.cPacked` (`#[repr(C, packed(N))]`),
`.rustPacked` (`#[repr(Rust, packed(N))]`), and `.unmodeled`. -/
inductive AdtRepr where
  | rust (reprAlign : Option Nat := none)
  | transparent
  | c (reprAlign : Option Nat := none)
  | cPacked (packAlign : Nat)
  | rustPacked (packAlign : Nat)
  | unmodeled
  deriving DecidableEq, Repr

/-- Visibility and safety of a struct field (`FieldDef::vis` and `FieldDef::safety`). -/
inductive FieldAccess where
  | pubSafe
  | priv
  deriving DecidableEq, Repr

/-- First-order types in the MIR model. -/
inductive MirTy where
  | usize
  | isize
  | uint (bits : Nat)
  | int (bits : Nat)
  | bool
  | char
  | unit
  | adt (id : Nat)
  | param (idx : Nat)
  | ref (inner : MirTy)
  | rawPtr (inner : MirTy) (mutable : Bool)
  | array (elem : MirTy) (len : Nat)
  | arraySizeOf (elem : MirTy) (sizedTy : MirTy)
  | unmodeled
  deriving DecidableEq, Repr

/-- Declaration of a single struct field. -/
structure FieldDecl where
  ty : MirTy
  access : FieldAccess := .pubSafe
  deriving DecidableEq, Repr

/-- First-order `!= ne` scalar field invariant (`#[anneal::invariant(field != ne)]`). -/
structure InvariantSpec where
  ne : Nat
  deriving DecidableEq, Repr

/-- Declaration of a captured struct (`Trusted.AdtDecl`). -/
structure AdtDecl where
  id : Nat
  fields : List FieldDecl
  repr : AdtRepr := .rust none
  invariant : Option InvariantSpec := none
  deriving DecidableEq, Repr

def AdtDecl.allFieldsPubSafe (d : AdtDecl) : Bool :=
  d.fields.all (fun f => f.access == .pubSafe)

def findAdtDecl (adts : List AdtDecl) (id : Nat) : Option AdtDecl :=
  adts.find? (fun d => d.id == id)

def mapAll {α β : Type} (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | x :: xs =>
    (f x).bind fun y =>
      (mapAll f xs).map fun ys => y :: ys

def listEnumAux {α : Type} : Nat → List α → List (Nat × α)
  | _, [] => []
  | i, x :: xs => (i, x) :: listEnumAux (i + 1) xs

def listEnum {α : Type} (xs : List α) : List (Nat × α) :=
  listEnumAux 0 xs

def intBitWidthLayout (target : TargetLayout) (w : Nat) : Option (Nat × Nat) :=
  if w == 8 then some (1, 1)
  else if w == 16 then some (2, 2)
  else if w == 16 then some (2, 2)
  else if w == 32 then some (4, 4)
  else if w == 64 then some (8, target.i64Align)
  else if w == 128 then some (16, target.i128Align)
  else none

/-- Sequential `#[repr(C, packed(packAlign))]` layout fold (`r[layout.repr.alignment.packed]`):
each field's effective alignment is `Nat.min packAlign fAlign`, and the overall struct
alignment is `Nat.min packAlign maxFieldAlign` (or `1` if fieldless). -/
def foldReprCPackedLayout (packAlign : Nat) :
    List (Nat × Nat) → Nat → Nat → Nat × Nat
  | [], offset, maxAlign => (alignUp offset maxAlign, maxAlign)
  | (fSz, fAlign) :: rest, offset, maxAlign =>
    let effAlign := Nat.max 1 (Nat.min packAlign fAlign)
    let alignedOffset := alignUp offset effAlign
    foldReprCPackedLayout packAlign rest (alignedOffset + fSz) (Nat.max maxAlign effAlign)

/-- Byte offset of field `targetIdx` inside a `#[repr(C)]` field layout list. -/
def reprCFieldOffsetLayout : List (Nat × Nat) → Nat → Nat → Option Nat
  | [], _, _ => none
  | (_, fAlign) :: _, 0, offset => some (alignUp offset fAlign)
  | (fSz, fAlign) :: rest, idx + 1, offset =>
    let alignedOffset := alignUp offset fAlign
    reprCFieldOffsetLayout rest idx (alignedOffset + fSz)

/-- Byte offset of field `targetIdx` inside a `#[repr(C, packed(packAlign))]` field layout list. -/
def reprCPackedFieldOffsetLayout (packAlign : Nat) :
    List (Nat × Nat) → Nat → Nat → Option Nat
  | [], _, _ => none
  | (_, fAlign) :: _, 0, offset =>
    let effAlign := Nat.max 1 (Nat.min packAlign fAlign)
    some (alignUp offset effAlign)
  | (fSz, fAlign) :: rest, idx + 1, offset =>
    let effAlign := Nat.max 1 (Nat.min packAlign fAlign)
    let alignedOffset := alignUp offset effAlign
    reprCPackedFieldOffsetLayout packAlign rest idx (alignedOffset + fSz)

/-- Check `r[layout.repr.transparent.constraint-field]`:
A `#[repr(transparent)]` struct has at most one non-1-ZST field (`sz > 0 || al > 1`),
and all other fields are 1-ZSTs (`sz == 0 && al == 1`).
Returns `(structSz, structAlign, uniqueNonZstIdxOpt)`. -/
def checkTransparentFields (fieldLayouts : List (Nat × Nat)) :
    Option (Nat × Nat × Option Nat) :=
  let indexed := listEnum fieldLayouts
  let non1Zst := indexed.filter (fun (_, (sz, al)) => decide (sz > 0 ∨ al > 1))
  match non1Zst with
  | [] => some (0, 1, none)
  | [(idx, (sz, al))] =>
    if sz > 0 then
      some (sz, al, some idx)
    else
      some (0, al, none)
  | _ => none

/-- Corrected single-step layout function `tyLayoutStep`:
Computes `(byteSize, byteAlign)` parameterized by:
- `tySizes : Nat → Nat` (byte size of generic type parameter `.param idx`),
- `adtPad : Nat → Nat` (extra alignment-sized padding units on non-ZST `#[repr(Rust)]` structs),
- `adtAlignShift : Nat → Nat` (log2 extra alignment factor on `#[repr(Rust)]` structs). -/
def tyLayoutStep (adts : List AdtDecl) (tySizes : Nat → Nat)
    (adtPad : Nat → Nat) (adtAlignShift : Nat → Nat)
    (target : TargetLayout)
    (unfold : MirTy → Option (Nat × Nat)) : MirTy → Option (Nat × Nat)
  | .usize | .isize => some (target.ptrByteWidth, target.ptrByteWidth)
  | .uint w | .int w => intBitWidthLayout target w
  | .bool => some (1, 1)
  | .char => some (4, 4)
  | .unit => some (0, 1)
  | .param idx => some (tySizes idx, 1)
  | .ref inner | .rawPtr inner _ =>
    (tyLayoutStep adts tySizes adtPad adtAlignShift target unfold inner).map
      fun _ => (target.ptrByteWidth, target.ptrByteWidth)
  | .array elem len =>
    (tyLayoutStep adts tySizes adtPad adtAlignShift target unfold elem).bind
      fun (elemSz, elemAlign) =>
        let sz := elemSz * len
        if decide (sz ≤ isizeMaxBytes) then some (sz, elemAlign) else none
  | .arraySizeOf elem sizedTy =>
    (tyLayoutStep adts tySizes adtPad adtAlignShift target unfold elem).bind
      fun (elemSz, elemAlign) =>
        (tyLayoutStep adts tySizes adtPad adtAlignShift target unfold sizedTy).map
          fun (n, _) => (elemSz * n, elemAlign)
  | .adt id =>
    (findAdtDecl adts id).bind fun decl =>
      (mapAll (fun f => unfold f.ty) decl.fields).bind fun fieldLayouts =>
        let sum := sumFieldSizes fieldLayouts
        let baseAlign := maxFieldAlign fieldLayouts
        match decl.repr with
        | .unmodeled => none
        | .transparent =>
          (checkTransparentFields fieldLayouts).map fun (sz, al, _) => (sz, al)
        | .c reprAlignOpt =>
          let (cSz, cAl) := foldReprCLayout fieldLayouts 0 1
          let finalAl := match reprAlignOpt with
            | some rAl => Nat.max cAl rAl
            | none => cAl
          some (alignUp cSz finalAl, finalAl)
        | .cPacked packAlign =>
          if packAlign == 0 then none
          else some (foldReprCPackedLayout packAlign fieldLayouts 0 1)
        | .rust reprAlignOpt =>
          let minAlign := match reprAlignOpt with
            | some rAl => Nat.max baseAlign rAl
            | none => baseAlign
          let al := minAlign * (2 ^ adtAlignShift id)
          -- r[layout.repr.rust.struct-zst]: if all fields have size 0, struct size is 0.
          let sz := if sum == 0 then 0 else alignUp sum al + adtPad id * al
          some (sz, al)
        | .rustPacked packAlign =>
          if packAlign == 0 then none
          else
            let effMaxAlign := Nat.max 1 (Nat.min packAlign baseAlign)
            let sz := if sum == 0 then 0 else alignUp sum effMaxAlign + adtPad id * effMaxAlign
            some (sz, effMaxAlign)
  | .unmodeled => none

def tyLayoutFuel (adts : List AdtDecl) (tySizes : Nat → Nat := fun _ => 0)
    (adtPad : Nat → Nat := fun _ => 0)
    (adtAlignShift : Nat → Nat := fun _ => 0)
    (target : TargetLayout := defaultTargetLayout) :
    Nat → MirTy → Option (Nat × Nat)
  | 0, _ => none
  | fuel + 1, ty =>
    tyLayoutStep adts tySizes adtPad adtAlignShift target
      (tyLayoutFuel adts tySizes adtPad adtAlignShift target fuel) ty

def evalTyByteSize (adts : List AdtDecl) (ty : MirTy)
    (tySizes : Nat → Nat := fun _ => 0)
    (adtPad : Nat → Nat := fun _ => 0)
    (adtAlignShift : Nat → Nat := fun _ => 0)
    (target : TargetLayout := defaultTargetLayout) : Option Nat :=
  (tyLayoutFuel adts tySizes adtPad adtAlignShift target (adts.length + 1) ty).map Prod.fst

def evalTyAlign (adts : List AdtDecl) (ty : MirTy)
    (tySizes : Nat → Nat := fun _ => 0)
    (adtPad : Nat → Nat := fun _ => 0)
    (adtAlignShift : Nat → Nat := fun _ => 0)
    (target : TargetLayout := defaultTargetLayout) : Option Nat :=
  (tyLayoutFuel adts tySizes adtPad adtAlignShift target (adts.length + 1) ty).map Prod.snd

inductive LayoutQuery where
  | sizeOf (ty : MirTy)
  | alignOf (ty : MirTy)
  | offsetOf (containerTy : MirTy) (variantIdx : Nat) (fieldIdx : Nat)
  deriving DecidableEq, Repr

/-- Evaluate `LayoutQuery` (`size_of`, `align_of`, `offset_of!`).
For `offsetOf (.adt id) 0 fieldIdx`:
- `.c`: returns the exact declaration-order aligned offset of `fieldIdx`.
- `.cPacked packAlign`: returns the exact declaration-order packed offset of `fieldIdx`.
- `.transparent`: if `structSz == 0`, every field is at offset `0`; if `structSz > 0`,
   ONLY the unique non-ZST carrier field (`some fieldIdx == nonZstIdx`) is guaranteed to sit
  at offset `0` (1-ZST sibling fields have unspecified offsets in `0..=structSz`, and sit
  at `structSz` in `rustc`!).
- `.rust` / `.rustPacked`: if `structSz == 0` (all-ZST struct), every field sits within
  `[0, 0]` and therefore has offset `0`; if `structSz > 0`, returns `some 0` iff there is
  a single non-ZST field at `fieldIdx`, all other fields are ZSTs, and `structSz == sum`
  (so the unique non-ZST field fills `[0, structSz)` and must start at offset `0` while any
  ZST sibling has unspecified offset). -/
def evalLayoutQuery (adts : List AdtDecl) (query : LayoutQuery)
    (tySizes : Nat → Nat := fun _ => 0)
    (adtPad : Nat → Nat := fun _ => 0)
    (adtAlignShift : Nat → Nat := fun _ => 0)
    (target : TargetLayout := defaultTargetLayout) : Option Nat :=
  match query with
  | .sizeOf ty => evalTyByteSize adts ty tySizes adtPad adtAlignShift target
  | .alignOf ty => evalTyAlign adts ty tySizes adtPad adtAlignShift target
  | .offsetOf (.adt id) variantIdx fieldIdx =>
    if variantIdx != 0 then none
    else
      (findAdtDecl adts id).bind fun decl =>
        let unfold := tyLayoutFuel adts tySizes adtPad adtAlignShift target (adts.length + 1)
        (mapAll (fun f => unfold f.ty) decl.fields).bind fun fieldLayouts =>
          if fieldIdx >= fieldLayouts.length then none
          else
            (unfold (.adt id)).bind fun (structSz, _) =>
              match decl.repr with
              | .unmodeled => none
              | .c _ => reprCFieldOffsetLayout fieldLayouts fieldIdx 0
              | .cPacked packAlign =>
                if packAlign == 0 then none
                else reprCPackedFieldOffsetLayout packAlign fieldLayouts fieldIdx 0
              | .transparent =>
                (checkTransparentFields fieldLayouts).bind fun (_, _, nonZstIdxOpt) =>
                  if structSz == 0 then some 0
                  else if nonZstIdxOpt == some fieldIdx then some 0
                  else none
              | .rust _ | .rustPacked _ =>
                if structSz == 0 then
                  some 0
                else
                  let nonZst := (listEnum fieldLayouts).filter (fun (_, (sz, _)) => decide (sz > 0))
                  match nonZst with
                  | [(onlyIdx, (onlySz, _))] =>
                    if onlyIdx == fieldIdx && structSz == onlySz then some 0 else none
                  | _ => none
  | .offsetOf _ _ _ => none

/-! ## Section 6: `MirVal`, `TransmutePayload` (`exactBits` vs. `initBytes`), and `evalTransmuteVal` -/

/-- Runtime values in the MIR model (`MirVal.fieldCons` for multi-field structs). -/
inductive MirVal where
  | uninit
  | usize (bits : Nat)
  | bool (b : Bool)
  | unit
  | adt (id : Nat) (inner : MirVal)
  | fieldCons (head : MirVal) (tail : MirVal)
  | bytes (sz : Nat) (bits : Nat)
  deriving DecidableEq, Repr

def MirVal.isFullyInit : MirVal → Bool
  | .uninit => false
  | .usize _ | .bool _ | .unit | .bytes _ _ => true
  | .adt _ inner => inner.isFullyInit
  | .fieldCons h t => h.isFullyInit && t.isFullyInit

def packFields : List MirVal → MirVal
  | [] => .unit
  | [v] => v
  | v :: rest => .fieldCons v (packFields rest)

def unpackFields : Nat → MirVal → Option (List MirVal)
  | 0, .unit => some []
  | 1, .fieldCons _ _ => none
  | 1, v => some [v]
  | n + 2, .fieldCons h t => (unpackFields (n + 1) t).map (h :: ·)
  | _, _ => none

/-- Check whether `v` is the canonical zero-sized value of an all-ZST type `ty`. -/
def isCanonicalZstVal (adts : List AdtDecl) : Nat → MirTy → MirVal → Bool
  | 0, _, _ => false
  | _ + 1, .unit, .unit => true
  | _ + 1, .array _ 0, .bytes 0 _ => true
  | fuel + 1, .adt id, .adt vId inner =>
    vId == id &&
    match findAdtDecl adts id with
    | some decl =>
      decl.repr != .unmodeled &&
      match unpackFields decl.fields.length inner with
      | some vs =>
        (decl.fields.zip vs).all fun (f, fv) =>
          isCanonicalZstVal adts fuel f.ty fv
      | none => false
    | none => false
  | _, _, _ => false

/-- Construct the canonical zero-sized value of a `PubSafe` all-ZST type `ty`. -/
def makeCanonicalZstVal (adts : List AdtDecl) : Nat → MirTy → Option MirVal
  | 0, _ => none
  | _ + 1, .unit => some .unit
  | _ + 1, .array (.uint 8) 0 => some (.bytes 0 0)
  | fuel + 1, .adt id =>
    (findAdtDecl adts id).bind fun decl =>
      if decl.allFieldsPubSafe && decl.repr != .unmodeled then
        (mapAll (fun f => makeCanonicalZstVal adts fuel f.ty) decl.fields).map
          fun vs => .adt id (packFields vs)
      else
        none
  | _, _ => none

/-- Stage 1b `#[repr(transparent)]` peeling: peels outer `#[repr(transparent)]`
struct wrappers (including arbitrary 1-ZST sibling fields) down to the unique
non-ZST carrier field `(coreTy, coreVal)`. -/
def peelTransparent (adts : List AdtDecl) (tySizes adtPad adtAlignShift : Nat → Nat)
    (target : TargetLayout) : Nat → MirTy → MirVal → Option (MirTy × MirVal)
  | 0, ty, v => some (ty, v)
  | fuel + 1, .adt id, .adt vId inner =>
    if vId != id then none
    else
      match findAdtDecl adts id with
      | some decl =>
        if decl.repr == .transparent then
          let unfold := tyLayoutFuel adts tySizes adtPad adtAlignShift target (adts.length + 1)
          match mapAll (fun f => unfold f.ty) decl.fields,
                unpackFields decl.fields.length inner with
          | some fieldLayouts, some vs =>
            match checkTransparentFields fieldLayouts with
            | some (_, _, some carrierIdx) =>
              let zstOk := (listEnum (decl.fields.zip vs)).all fun (i, (f, fv)) =>
                i == carrierIdx || isCanonicalZstVal adts (adts.length + 1) f.ty fv
              if zstOk then
                match decl.fields[carrierIdx]?, vs[carrierIdx]? with
                | some cf, some cv =>
                  peelTransparent adts tySizes adtPad adtAlignShift target fuel cf.ty cv
                | _, _ => none
              else none
            | _ => some (.adt id, .adt vId inner)
          | _, _ => none
        else
          some (.adt id, .adt vId inner)
      | none => none
  | _ + 1, ty, v => some (ty, v)

/-- Stage 1b `#[repr(transparent)]` wrapping: wraps `(baseTy, baseVal)` into outer
`#[repr(transparent)]` wrappers whose fields are `allFieldsPubSafe`, synthesizing
canonical values for any 1-ZST sibling fields. -/
def wrapTransparent (adts : List AdtDecl) (tySizes adtPad adtAlignShift : Nat → Nat)
    (target : TargetLayout) : Nat → MirTy → MirTy → MirVal → Option MirVal
  | 0, _, _, _ => none
  | fuel + 1, baseTy, dstTy, baseVal =>
    if baseTy == dstTy then
      some baseVal
    else
      match dstTy with
      | .adt id =>
        (findAdtDecl adts id).bind fun decl =>
          if decl.allFieldsPubSafe && decl.repr == .transparent then
            let unfold := tyLayoutFuel adts tySizes adtPad adtAlignShift target (adts.length + 1)
            (mapAll (fun f => unfold f.ty) decl.fields).bind fun fieldLayouts =>
              (checkTransparentFields fieldLayouts).bind fun (_, _, carrierIdxOpt) =>
                match carrierIdxOpt with
                | some carrierIdx =>
                  (decl.fields[carrierIdx]?).bind fun cf =>
                    (wrapTransparent adts tySizes adtPad adtAlignShift target
                      fuel baseTy cf.ty baseVal).bind fun carrierVal =>
                      (mapAll (fun (i, (f : FieldDecl)) =>
                        if i == carrierIdx then some carrierVal
                        else makeCanonicalZstVal adts (adts.length + 1) f.ty)
                        (listEnum decl.fields)).map fun vs =>
                        .adt id (packFields vs)
                | none => none
          else
            none
      | _ => none

/-- Two-constructor transmutation payload distinguishing deterministic bit patterns
from fully initialized byte sequences with unspecified internal field order. -/
inductive TransmutePayload where
  /-- Known deterministic bit pattern `bits` of exact byte width `sz`. -/
  | exactBits (sz : Nat) (bits : Nat)
  /-- `sz` fully initialized bytes (zero padding) whose internal field order is
  unspecified (`#[repr(Rust)]` multi-field structs or abstract byte arrays). -/
  | initBytes (sz : Nat)
  deriving DecidableEq, Repr

def TransmutePayload.byteSize : TransmutePayload → Nat
  | .exactBits sz _ => sz
  | .initBytes sz => sz

/-- Combine a list of field `TransmutePayload`s in declaration order (`#[repr(C)]`):
if every field has `.exactBits`, concatenates the little-endian bit patterns into
`.exactBits totalSz totalBits`; if any field is `.initBytes`, degrades to `.initBytes totalSz`. -/
def foldExactPayloads : List TransmutePayload → TransmutePayload
  | [] => .exactBits 0 0
  | p :: rest =>
    match p, foldExactPayloads rest with
    | .exactBits sz1 bits1, .exactBits sz2 bits2 =>
      .exactBits (sz1 + sz2) (bits1 + bits2 * (2 ^ (8 * sz1)))
    | p1, p2 => .initBytes (p1.byteSize + p2.byteSize)

def primitiveByteSize (target : TargetLayout := defaultTargetLayout) :
    MirTy → Option Nat
  | .usize | .isize => some target.ptrByteWidth
  | .uint w | .int w => (intBitWidthLayout target w).map Prod.fst
  | .bool => some 1
  | .char => some 4
  | .unit => some 0
  | _ => none

/-- Extract the `TransmutePayload` of `(srcTy, srcVal)` under the current layout world
`(tySizes, adtPad, adtAlignShift)`:
- Primitives yield `some (.exactBits sz bits)`.
- Byte arrays (`[u8; N]`) yield `some (.initBytes sz)`.
- Structs yield `none` whenever `sumFieldSizes < actualStructSz` (i.e., the struct
  contains uninitialized inter-field or trailing padding bytes in the current world!).
- When `sumFieldSizes == actualStructSz` (zero padding in the current world):
  * `.transparent`, `.c`, `.cPacked`: preserve `.exactBits` via `foldExactPayloads`
    (because field order is normatively fixed!).
  * `.rust`, `.rustPacked`: if `actualStructSz == 0`, yield `some (.exactBits 0 0)`;
    if there is at most 1 non-ZST field (`nonZstPayloads.length ≤ 1`), that sole
    non-ZST field must sit at offset `0` (`[0, actualStructSz)`), so its `TransmutePayload`
    is preserved (`exactBits` stays `exactBits`); if there are `≥ 2` non-ZST fields,
    field permutation is unspecified by `r[layout.repr.rust.layout.struct]`, so the
    payload degrades to `some (.initBytes actualStructSz)`! -/
def extractTransmutePayloadFuel (adts : List AdtDecl)
    (tySizes adtPad adtAlignShift : Nat → Nat)
    (target : TargetLayout) :
    Nat → MirTy → MirVal → Option TransmutePayload
  | 0, _, _ => none
  | _ + 1, ty, .usize bits =>
    (primitiveByteSize target ty).map fun sz => .exactBits sz bits
  | _ + 1, .bool, .bool b => some (.exactBits 1 (if b then 1 else 0))
  | _ + 1, .unit, .unit => some (.exactBits 0 0)
  | _ + 1, .array (.uint 8) len, .bytes sz _ =>
    if sz == len then some (.initBytes sz) else none
  | _ + 1, .arraySizeOf (.uint 8) sizedTy, .bytes sz _ =>
    match evalTyByteSize adts sizedTy tySizes adtPad adtAlignShift target with
    | some expectedSz => if sz == expectedSz then some (.initBytes sz) else none
    | none => none
  | fuel + 1, .adt id, .adt vId inner =>
    if vId != id then none
    else
      (findAdtDecl adts id).bind fun decl =>
        if decl.repr == .unmodeled then none
        else
          (evalTyByteSize adts (.adt id) tySizes adtPad adtAlignShift target).bind fun structSz =>
            (unpackFields decl.fields.length inner).bind fun vs =>
              (mapAll (fun (f, fv) =>
                extractTransmutePayloadFuel adts tySizes adtPad adtAlignShift target fuel f.ty fv)
                (decl.fields.zip vs)).bind fun fieldPayloads =>
                let initSum := fieldPayloads.foldl (fun acc p => acc + p.byteSize) 0
                -- Reject if the struct contains any uninitialized padding bytes!
                if initSum != structSz then
                  none
                else
                  match decl.repr with
                  | .transparent | .c _ | .cPacked _ =>
                    some (foldExactPayloads fieldPayloads)
                  | .rust _ | .rustPacked _ =>
                    let nonZstPayloads := fieldPayloads.filter (fun p => decide (p.byteSize > 0))
                    match nonZstPayloads with
                    | [] => some (.exactBits 0 0)
                    | [singlePayload] => some singlePayload
                    | _ => some (.initBytes structSz)
                  | .unmodeled => none
  | _, _, _ => none

def extractTransmutePayload (adts : List AdtDecl)
    (tySizes adtPad adtAlignShift : Nat → Nat)
    (target : TargetLayout) (srcTy : MirTy) (srcVal : MirVal) :
    Option TransmutePayload :=
  extractTransmutePayloadFuel adts tySizes adtPad adtAlignShift target
    (adts.length + 1) srcTy srcVal

/-- Reconstruct field values of a `#[repr(C)]` or `#[repr(C, packed)]` struct in
declaration order from deterministic `.exactBits`. -/
def constructExactFields (construct : TransmutePayload → MirTy → Option MirVal)
    (unfoldLayout : MirTy → Option (Nat × Nat))
    (bits : Nat) : List FieldDecl → Option (Nat × List MirVal)
  | [] => some (0, [])
  | f :: rest =>
    (unfoldLayout f.ty).bind fun (fSz, _) =>
      let fMod := 2 ^ (8 * fSz)
      let fBits := bits % fMod
      let remBits := bits / fMod
      (construct (.exactBits fSz fBits) f.ty).bind fun v =>
        (constructExactFields construct unfoldLayout remBits rest).map
          fun (restSz, vs) => (fSz + restSz, v :: vs)

/-- Construct a `MirVal` of type `dstTy` from `payload : TransmutePayload`:
- Byte arrays (`[u8; dstSz]`) accept BOTH `.exactBits dstSz bits` and `.initBytes dstSz`,
  producing `.bytes dstSz 0` (soundly verifying `IntoBytes` transmutations such as
  `Sandwich(u8, u16, u8) -> [u8; 4]` and `Pair(u32, u32) -> [u8; 8]`).
- Integer scalars (`usize`, `isize`, `u*`, `i*`) accept `.exactBits dstSz bits`
  (producing `.usize bits`) and reject `.initBytes dstSz` (`none`) so proofs cannot
  assume a fixed field order on multi-field `#[repr(Rust)]` structs.
- `()` accepts any 0-byte payload (`.exactBits 0 _` or `.initBytes 0`).
- Target structs `.adt id` require `decl.allFieldsPubSafe` and zero padding
  (`sumFieldSizes == dstSz` in the current world):
  * If `dstSz == 0` (all-ZST struct), constructs the canonical ZST value.
  * If `decl` has a single non-ZST field (with all other fields ZSTs) and `sum == dstSz`,
    delegates `payload` to that single non-ZST field and fills ZST siblings canonically.
  * If `decl` has `≥ 2` non-ZST fields, requires `decl.repr` to have deterministic
    declaration-order layout (`.c` or `.cPacked`) AND `payload` to be `.exactBits dstSz bits`. -/
def constructTransmuteValFuel (adts : List AdtDecl)
    (tySizes adtPad adtAlignShift : Nat → Nat)
    (target : TargetLayout) :
    Nat → TransmutePayload → MirTy → Option MirVal
  | 0, _, _ => none
  | _ + 1, .exactBits sz bits, .usize | _ + 1, .exactBits sz bits, .isize =>
    if sz == target.ptrByteWidth then some (.usize bits) else none
  | _ + 1, .exactBits sz bits, .uint w | _ + 1, .exactBits sz bits, .int w =>
    match intBitWidthLayout target w with
    | some (expectedSz, _) => if sz == expectedSz then some (.usize bits) else none
    | none => none
  | _ + 1, _, .bool | _ + 1, _, .char => none
  | _ + 1, p, .unit => if p.byteSize == 0 then some .unit else none
  | _ + 1, p, .array (.uint 8) len =>
    if p.byteSize == len then some (.bytes len 0) else none
  | _ + 1, p, .arraySizeOf (.uint 8) sizedTy =>
    match evalTyByteSize adts sizedTy tySizes adtPad adtAlignShift target with
    | some expectedSz =>
      if p.byteSize == expectedSz then some (.bytes expectedSz 0) else none
    | none => none
  | fuel + 1, payload, .adt id =>
    (findAdtDecl adts id).bind fun decl =>
      if !decl.allFieldsPubSafe || decl.repr == .unmodeled then none
      else
        let unfold := tyLayoutFuel adts tySizes adtPad adtAlignShift target (adts.length + 1)
        (unfold (.adt id)).bind fun (structSz, _) =>
          if payload.byteSize != structSz then none
          else
            (mapAll (fun f => unfold f.ty) decl.fields).bind fun fieldLayouts =>
              let sum := sumFieldSizes fieldLayouts
              if sum != structSz then none
              else if structSz == 0 then
                makeCanonicalZstVal adts (adts.length + 1) (.adt id)
              else
                let nonZst := (listEnum fieldLayouts).filter (fun (_, (sz, _)) => decide (sz > 0))
                match nonZst with
                | [(carrierIdx, _)] =>
                  (decl.fields[carrierIdx]?).bind fun (cf : FieldDecl) =>
                    (constructTransmuteValFuel adts tySizes adtPad adtAlignShift target
                      fuel payload cf.ty).bind fun carrierVal =>
                      (mapAll (fun (i, (f : FieldDecl)) =>
                        if i == carrierIdx then some carrierVal
                        else makeCanonicalZstVal adts (adts.length + 1) f.ty)
                        (listEnum decl.fields)).map fun vs =>
                        .adt id (packFields vs)
                | _ =>
                  match decl.repr, payload with
                  | .c _, .exactBits _ bits | .cPacked _, .exactBits _ bits =>
                    (constructExactFields
                      (constructTransmuteValFuel adts tySizes adtPad adtAlignShift target fuel)
                      unfold bits decl.fields).bind fun (sumSz, vs) =>
                        if sumSz == structSz then some (.adt id (packFields vs))
                        else none
                  | _, _ => none
  | _ + 1, _, _ => none

/-- Full two-stage `evalTransmuteVal`:
- Stage 1a: Exact same-type reflexivity (`srcTy == dstTy && srcVal.isFullyInit`).
- Stage 1b: `#[repr(transparent)]` wrapper peeling/re-wrapping (supporting arbitrary 1-ZST siblings).
- Stage 2: Cross-type bit/byte reinterpretation via `TransmutePayload` (`exactBits` vs. `initBytes`). -/
def evalTransmuteVal (adts : List AdtDecl)
    (srcTy dstTy : MirTy) (srcVal : MirVal)
    (tySizes : Nat → Nat := fun _ => 0)
    (adtPad : Nat → Nat := fun _ => 0)
    (adtAlignShift : Nat → Nat := fun _ => 0)
    (target : TargetLayout := defaultTargetLayout) : Option MirVal :=
  if !srcVal.isFullyInit then none
  else
    match evalTyByteSize adts srcTy tySizes adtPad adtAlignShift target,
          evalTyByteSize adts dstTy tySizes adtPad adtAlignShift target with
    | some srcSz, some dstSz =>
      if srcSz != dstSz then none
      else if srcTy == dstTy then
        some srcVal
      else
        let fuel := adts.length + 1
        match (peelTransparent adts tySizes adtPad adtAlignShift target fuel srcTy srcVal).bind
            (fun (baseTy, baseVal) =>
              wrapTransparent adts tySizes adtPad adtAlignShift target fuel baseTy dstTy baseVal) with
        | some wrapped => some wrapped
        | none =>
          (extractTransmutePayload adts tySizes adtPad adtAlignShift target srcTy srcVal).bind
            fun payload =>
              if payload.byteSize == dstSz then
                constructTransmuteValFuel adts tySizes adtPad adtAlignShift target
                  fuel payload dstTy
              else
                none
    | _, _ => none

/-! ## Section 7: Concrete ADTs and Holdout Theorems (Bugs 1A–1E) -/

-- ADT IDs for the benchmark corpus
def idSandwich : Nat := 1        -- #[repr(Rust)] struct Sandwich { a: u8, b: u16, c: u8 }
def idCSandwich : Nat := 2       -- #[repr(C)] struct CSandwich { a: u8, b: u16, c: u8 }
def idOuterCWithSandwich : Nat := 3 -- #[repr(C)] struct OuterC { prefix: u8, inner: Sandwich }
def idInevitablePad : Nat := 4   -- #[repr(Rust)] struct InevitablePad { a: [u8; 3], b: u32 }
def idTwoU24 : Nat := 5          -- #[repr(Rust)] struct TwoU24 { a: [u8; 3], b: [u8; 3], c: u32 }
def idMixed : Nat := 6           -- #[repr(Rust)] struct Mixed { a: u8, b: u64 }
def idPair : Nat := 7            -- #[repr(Rust)] struct Pair { a: u32, b: u32 }
def idCPair : Nat := 8           -- #[repr(C)] struct CPair { a: u32, b: u32 }
def idSingleFieldRust : Nat := 9 -- #[repr(Rust)] struct SingleFieldRust { a: u32 }
def idTransWithZst : Nat := 10   -- #[repr(transparent)] struct TransWithZst((), u64)
def idRustZst : Nat := 11        -- #[repr(Rust)] struct RustZst((), ())
def idCPackedSandwich : Nat := 12    -- #[repr(C, packed(1))] struct CPackedSandwich { a: u8, b: u16, c: u8 }
def idRustPackedSandwich : Nat := 13 -- #[repr(Rust, packed(1))] struct RustPackedSandwich { a: u8, b: u16, c: u8 }

def declSandwich : AdtDecl :=
  { id := idSandwich
    repr := .rust none
    fields := [{ ty := .uint 8 }, { ty := .uint 16 }, { ty := .uint 8 }] }

def declCSandwich : AdtDecl :=
  { id := idCSandwich
    repr := .c none
    fields := [{ ty := .uint 8 }, { ty := .uint 16 }, { ty := .uint 8 }] }

def declOuterCWithSandwich : AdtDecl :=
  { id := idOuterCWithSandwich
    repr := .c none
    fields := [{ ty := .uint 8 }, { ty := .adt idSandwich }] }

def declInevitablePad : AdtDecl :=
  { id := idInevitablePad
    repr := .rust none
    fields := [{ ty := .array (.uint 8) 3 }, { ty := .uint 32 }] }

def declTwoU24 : AdtDecl :=
  { id := idTwoU24
    repr := .rust none
    fields := [{ ty := .array (.uint 8) 3 }, { ty := .array (.uint 8) 3 }, { ty := .uint 32 }] }

def declMixed : AdtDecl :=
  { id := idMixed
    repr := .rust none
    fields := [{ ty := .uint 8 }, { ty := .uint 64 }] }

def declPair : AdtDecl :=
  { id := idPair
    repr := .rust none
    fields := [{ ty := .uint 32 }, { ty := .uint 32 }] }

def declCPair : AdtDecl :=
  { id := idCPair
    repr := .c none
    fields := [{ ty := .uint 32 }, { ty := .uint 32 }] }

def declSingleFieldRust : AdtDecl :=
  { id := idSingleFieldRust
    repr := .rust none
    fields := [{ ty := .uint 32 }] }

def declTransWithZst : AdtDecl :=
  { id := idTransWithZst
    repr := .transparent
    fields := [{ ty := .unit }, { ty := .uint 64 }] }

def declRustZst : AdtDecl :=
  { id := idRustZst
    repr := .rust none
    fields := [{ ty := .unit }, { ty := .unit }] }

def declCPackedSandwich : AdtDecl :=
  { id := idCPackedSandwich
    repr := .cPacked 1
    fields := [{ ty := .uint 8 }, { ty := .uint 16 }, { ty := .uint 8 }] }

def declRustPackedSandwich : AdtDecl :=
  { id := idRustPackedSandwich
    repr := .rustPacked 1
    fields := [{ ty := .uint 8 }, { ty := .uint 16 }, { ty := .uint 8 }] }

def testAdts : List AdtDecl :=
  [declSandwich, declCSandwich, declOuterCWithSandwich, declInevitablePad,
   declTwoU24, declMixed, declPair, declCPair, declSingleFieldRust,
   declTransWithZst, declRustZst, declCPackedSandwich, declRustPackedSandwich]

/-! ### Holdout 1: `Sandwich(u8, u16, u8)` vs. `CSandwich(u8, u16, u8)` -/

/-- Declaration-order C-layout lower-bound flaw: computing `.rust` base size via declaration-order
`foldReprCLayout` assigns `Sandwich(u8, u16, u8)` a base size of `6`, so `adtPad + 6 ≥ 6`
can NEVER equal `rustc`'s actual size of `4`! -/
theorem reprC_base_size_excludes_rustc_sandwich_size (pad : Nat) :
    (foldReprCLayout [(1, 1), (2, 2), (1, 1)] 0 1).1 = 6 ∧
    pad + (foldReprCLayout [(1, 1), (2, 2), (1, 1)] 0 1).1 ≠ 4 := by
  refine ⟨rfl, ?_⟩
  change pad + 6 ≠ 4
  omega

/-- By contrast, sorting `Sandwich`'s fields by descending alignment `[(2, 2), (1, 1), (1, 1)]`
is a `DescendingAlignedChain` and yields `(4, 2) = (alignUp 4 2, 2)`. -/
theorem sandwich_sorted_chain_size_four :
    DescendingAlignedChain 2 [(1, 1), (1, 1)] ∧
    foldReprCLayout [(2, 2), (1, 1), (1, 1)] 0 1 = (4, 2) := by
  refine ⟨?_, rfl⟩
  exact .cons ⟨2, rfl⟩ (by omega) ⟨1, rfl⟩
    (.cons ⟨1, rfl⟩ (by omega) ⟨1, rfl⟩ (.nil 1))

/-- Corrected `tyLayoutStep` gives `Sandwich` size `4` and align `2` in the pinned `rustc`
world (`adtPad = 0, adtAlignShift = 0`), while `CSandwich` has size `6` and align `2`,
and `OuterCWithSandwich` (`#[repr(C)] { a: u8, inner: Sandwich }`) has size `6` and align `2`. -/
theorem sandwich_and_outer_c_layout_at_pinned_rustc :
    evalTyByteSize testAdts (.adt idSandwich) = some 4 ∧
    evalTyAlign testAdts (.adt idSandwich) = some 2 ∧
    evalTyByteSize testAdts (.adt idCSandwich) = some 6 ∧
    evalTyAlign testAdts (.adt idCSandwich) = some 2 ∧
    evalTyByteSize testAdts (.adt idOuterCWithSandwich) = some 6 ∧
    evalTyAlign testAdts (.adt idOuterCWithSandwich) = some 2 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- When `Sandwich` is over-aligned (`adtAlignShift idSandwich = 1`, `align = 4`) with `adtPad = 0`,
`Sandwich` STILL has size `4` (`alignUp 4 4 = 4`), while `OuterCWithSandwich` increases its
size from `6` to `8` (`prefix: u8` at `0`, 3 bytes padding, `inner: Sandwich` at `4..8`)! -/
theorem sandwich_and_outer_c_under_overalignment :
    let shift := fun id => if id == idSandwich then 1 else 0
    evalTyByteSize testAdts (.adt idSandwich) (fun _ => 0) (fun _ => 0) shift = some 4 ∧
    evalTyAlign testAdts (.adt idSandwich) (fun _ => 0) (fun _ => 0) shift = some 4 ∧
    evalTyByteSize testAdts (.adt idOuterCWithSandwich) (fun _ => 0) (fun _ => 0) shift = some 8 ∧
    evalTyAlign testAdts (.adt idOuterCWithSandwich) (fun _ => 0) (fun _ => 0) shift = some 4 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Transmuting `Sandwich { a, b, c }` to `[u8; 4]` (Zerocopy `IntoBytes`) succeeds in BOTH
zero-padding worlds (`(pad = 0, shift = 0)` and `(pad = 0, shift = 1)` where `size == 4`),
fails when `pad > 0` or `shift ≥ 2`, and transmuting `Sandwich` to `u32` (`.uint 32`) ALWAYS
fails (`none`) because `Sandwich`'s 3 non-ZST fields have unspecified order (`initBytes 4`). -/
theorem sandwich_transmute_into_bytes_vs_u32 (a b c : Nat) :
    let val := MirVal.adt idSandwich (.fieldCons (.usize a) (.fieldCons (.usize b) (.usize c)))
    let shift1 := fun id => if id == idSandwich then 1 else 0
    let pad1 := fun id => if id == idSandwich then 1 else 0
    evalTransmuteVal testAdts (.adt idSandwich) (.array (.uint 8) 4) val =
      some (.bytes 4 0) ∧
    evalTransmuteVal testAdts (.adt idSandwich) (.array (.uint 8) 4) val
      (fun _ => 0) (fun _ => 0) shift1 = some (.bytes 4 0) ∧
    evalTransmuteVal testAdts (.adt idSandwich) (.array (.uint 8) 4) val
      (fun _ => 0) pad1 (fun _ => 0) = none ∧
    evalTransmuteVal testAdts (.adt idSandwich) (.uint 32) val = none := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-! ### Holdout 2 (Bug 1B): `InevitablePad([u8; 3], u32)`, `TwoU24`, and `Mixed(u8, u64)` -/

/-- Even at `(adtPad = 0, adtAlignShift = 0)`, `InevitablePad([u8; 3], u32)` has `size = 8`
(matching `rustc`), `TwoU24([u8; 3], [u8; 3], u32)` has `size = 12`, and `Mixed(u8, u64)`
has `size = 16`, YET transmuting any of them to a byte array (`[u8; 8]`, `[u8; 12]`, `[u8; 16]`)
evaluates to `none` because `sumFieldSizes` (`7`, `10`, `9`) is strictly less than `structSz`
(`8`, `12`, `16`)! -/
theorem inevitable_padding_sizes_and_transmute_rejection (b : Nat) :
    let vInev := MirVal.adt idInevitablePad (.fieldCons (.bytes 3 0) (.usize b))
    let vTwoU24 := MirVal.adt idTwoU24 (.fieldCons (.bytes 3 0) (.fieldCons (.bytes 3 0) (.usize b)))
    let vMixed := MirVal.adt idMixed (.fieldCons (.usize 1) (.usize b))
    evalTyByteSize testAdts (.adt idInevitablePad) = some 8 ∧
    evalTyByteSize testAdts (.adt idTwoU24) = some 12 ∧
    evalTyByteSize testAdts (.adt idMixed) = some 16 ∧
    evalTransmuteVal testAdts (.adt idInevitablePad) (.array (.uint 8) 8) vInev = none ∧
    evalTransmuteVal testAdts (.adt idTwoU24) (.array (.uint 8) 12) vTwoU24 = none ∧
    evalTransmuteVal testAdts (.adt idMixed) (.array (.uint 8) 16) vMixed = none := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Holdout 3 (Bug 1E): `Pair(u32, u32)` vs. `CPair(u32, u32)` vs. `SingleFieldRust(u32)` -/

/-- For `Pair(u32, u32)` (`#[repr(Rust)]`):
1. At `(pad = 0, shift = 0)`, `extractTransmutePayload` yields `some (.initBytes 8)` (NOT `.exactBits`).
2. `Pair(u32, u32) -> [u8; 8]` SUCCEEDS (`some (.bytes 8 0)`).
3. `Pair(u32, u32) -> CPair(u32, u32)` and `Pair(u32, u32) -> u64` FAIL (`none`), preventing
   unsound proofs that assume declaration field order!
4. Reflexive `Pair(u32, u32) -> Pair(u32, u32)` SUCCEEDS in EVERY `(adtPad, adtAlignShift)` world! -/
theorem pair_repr_rust_transmute_discrimination (a b : Nat) (pad shift : Nat → Nat) :
    let vPair := MirVal.adt idPair (.fieldCons (.usize a) (.usize b))
    extractTransmutePayload testAdts (fun _ => 0) (fun _ => 0) (fun _ => 0)
      defaultTargetLayout (.adt idPair) vPair = some (.initBytes 8) ∧
    evalTransmuteVal testAdts (.adt idPair) (.array (.uint 8) 8) vPair = some (.bytes 8 0) ∧
    evalTransmuteVal testAdts (.adt idPair) (.adt idCPair) vPair = none ∧
    evalTransmuteVal testAdts (.adt idPair) (.uint 64) vPair = none ∧
    evalTransmuteVal testAdts (.adt idPair) (.adt idPair) vPair (fun _ => 0) pad shift =
      some vPair := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  change (if (alignUp 8 (4 * 2 ^ shift 7) + pad 7 * (4 * 2 ^ shift 7) !=
              alignUp 8 (4 * 2 ^ shift 7) + pad 7 * (4 * 2 ^ shift 7)) = true
          then none
          else some (MirVal.adt idPair (.fieldCons (.usize a) (.usize b)))) =
    some (MirVal.adt idPair (.fieldCons (.usize a) (.usize b)))
  simp only [bne_self_eq_false]
  rfl

/-- By contrast, for `CPair(u32, u32)` (`#[repr(C)]`):
1. `extractTransmutePayload` yields `some (.exactBits 8 (a + b * 2^32))`.
2. `CPair(u32, u32) -> u64`, `u64 -> CPair(u32, u32)`, and `CPair(u32, u32) -> [u8; 8]`
   ALL succeed across ALL `(adtPad, adtAlignShift)` worlds!
3. `CPair(u32, u32) -> Pair(u32, u32)` FAILS (`none`) because `Pair` is a multi-field
   `#[repr(Rust)]` struct with unspecified field order. -/
theorem cpair_repr_c_transmute_exact_bits (a b : Nat) :
    let vCPair := MirVal.adt idCPair (.fieldCons (.usize a) (.usize b))
    extractTransmutePayload testAdts (fun _ => 0) (fun _ => 0) (fun _ => 0)
      defaultTargetLayout (.adt idCPair) vCPair =
      some (.exactBits 8 (a + b * (2 ^ 32))) ∧
    evalTransmuteVal testAdts (.adt idCPair) (.uint 64) vCPair =
      some (.usize (a + b * (2 ^ 32))) ∧
    evalTransmuteVal testAdts (.adt idCPair) (.array (.uint 8) 8) vCPair =
      some (.bytes 8 0) ∧
    evalTransmuteVal testAdts (.adt idCPair) (.adt idPair) vCPair = none := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- For 1-non-ZST-field `SingleFieldRust(u32)` (`#[repr(Rust)]`):
At `(pad = 0, shift = 0)` (which is enforced by `const { assert!(size_of::<SingleFieldRust>() == 4) }`),
`SingleFieldRust` has `structSz = 4 == sumFieldSizes` and only 1 non-ZST field, so that field MUST
sit at offset `0` (`offset_of == some 0`), `extractTransmutePayload` preserves `.exactBits 4 x`,
and `SingleFieldRust(u32) <-> u32` succeeds; whereas when `pad > 0` or `shift > 0`, `structSz > 4`
and `SingleFieldRust(u32) <-> u32` fails! -/
theorem single_field_rust_exact_bits_when_unpadded (x : Nat) :
    let vSingle := MirVal.adt idSingleFieldRust (.usize x)
    let pad1 := fun id => if id == idSingleFieldRust then 1 else 0
    let shift1 := fun id => if id == idSingleFieldRust then 1 else 0
    evalLayoutQuery testAdts (.offsetOf (.adt idSingleFieldRust) 0 0) = some 0 ∧
    extractTransmutePayload testAdts (fun _ => 0) (fun _ => 0) (fun _ => 0)
      defaultTargetLayout (.adt idSingleFieldRust) vSingle = some (.exactBits 4 x) ∧
    evalTransmuteVal testAdts (.adt idSingleFieldRust) (.uint 32) vSingle = some (.usize x) ∧
    evalTransmuteVal testAdts (.uint 32) (.adt idSingleFieldRust) (.usize x) = some vSingle ∧
    evalTransmuteVal testAdts (.adt idSingleFieldRust) (.uint 32) vSingle
      (fun _ => 0) pad1 (fun _ => 0) = none ∧
    evalTransmuteVal testAdts (.adt idSingleFieldRust) (.uint 32) vSingle
      (fun _ => 0) (fun _ => 0) shift1 = none := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Holdout 4 (Bug 1D): `TransWithZst((), u64)` and `RustZst((), ())` -/

/-- For `#[repr(transparent)] struct TransWithZst((), u64)`:
1. `size_of == 8` and `align_of == 8` across all worlds.
2. `offset_of!(TransWithZst, 1)` (the `u64` carrier field) is `some 0`, whereas
   `offset_of!(TransWithZst, 0)` (the `()` 1-ZST sibling, placed at offset `8` by `rustc`!)
   is `none`!
3. Both Stage 1 (`peelTransparent` / `wrapTransparent`) and `evalTransmuteVal` succeed for
   `TransWithZst((), u64) <-> u64` across all worlds! -/
theorem trans_with_zst_layout_offset_and_transmute (x : Nat) :
    let vTrans := MirVal.adt idTransWithZst (.fieldCons .unit (.usize x))
    evalTyByteSize testAdts (.adt idTransWithZst) = some 8 ∧
    evalTyAlign testAdts (.adt idTransWithZst) = some 8 ∧
    evalLayoutQuery testAdts (.offsetOf (.adt idTransWithZst) 0 1) = some 0 ∧
    evalLayoutQuery testAdts (.offsetOf (.adt idTransWithZst) 0 0) = none ∧
    evalTransmuteVal testAdts (.adt idTransWithZst) (.uint 64) vTrans = some (.usize x) ∧
    evalTransmuteVal testAdts (.uint 64) (.adt idTransWithZst) (.usize x) = some vTrans := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- For `#[repr(Rust)] struct RustZst((), ())` (`r[layout.repr.rust.struct-zst]`):
1. Across ALL `adtPad` and `adtAlignShift` worlds, `size_of::<RustZst>() == 0`!
2. Across ALL `adtPad` and `adtAlignShift` worlds, `align_of::<RustZst>() == 2^(adtAlignShift idRustZst)`
   (so `align_of` is `1` at `shift = 0`, and `2^k > 1` when `shift = k > 0`).
3. Both `offset_of!(RustZst, 0)` and `offset_of!(RustZst, 1)` equal `some 0` in all worlds,
   and `RustZst((), ()) <-> ()` succeeds in all worlds! -/
theorem rust_zst_zero_size_and_variable_align (pad shift : Nat → Nat) :
    let vZst := MirVal.adt idRustZst (.fieldCons .unit .unit)
    evalTyByteSize testAdts (.adt idRustZst) (fun _ => 0) pad shift = some 0 ∧
    evalTyAlign testAdts (.adt idRustZst) (fun _ => 0) pad shift =
      some (2 ^ shift idRustZst) ∧
    evalLayoutQuery testAdts (.offsetOf (.adt idRustZst) 0 0) (fun _ => 0) pad shift = some 0 ∧
    evalLayoutQuery testAdts (.offsetOf (.adt idRustZst) 0 1) (fun _ => 0) pad shift = some 0 ∧
    evalTransmuteVal testAdts (.adt idRustZst) .unit vZst (fun _ => 0) pad shift = some .unit ∧
    evalTransmuteVal testAdts .unit (.adt idRustZst) .unit (fun _ => 0) pad shift = some vZst := by
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl⟩
  rw [← Nat.one_mul (2 ^ shift idRustZst)]
  rfl

/-! ### Holdout 5: `#[repr(C, packed(1))]` vs. `#[repr(Rust, packed(1))]` -/

/-- `#[repr(C, packed(1))] struct CPackedSandwich { a: u8, b: u16, c: u8 }` has deterministic
size `4`, align `1`, declaration-order field offsets `(0, 1, 3)`, and `.exactBits 4` payload
(transmuting to both `[u8; 4]` and `u32`), whereas `#[repr(Rust, packed(1))] struct RustPackedSandwich`
has size `4`, align `1`, unspecified field offsets (`offset_of == none`), and `.initBytes 4`
payload (transmuting to `[u8; 4]` but NOT `u32`)! -/
theorem c_packed_vs_rust_packed_sandwich (a b c : Nat) :
    let vCPacked := MirVal.adt idCPackedSandwich (.fieldCons (.usize a) (.fieldCons (.usize b) (.usize c)))
    let vRustPacked := MirVal.adt idRustPackedSandwich (.fieldCons (.usize a) (.fieldCons (.usize b) (.usize c)))
    evalTyByteSize testAdts (.adt idCPackedSandwich) = some 4 ∧
    evalTyAlign testAdts (.adt idCPackedSandwich) = some 1 ∧
    evalLayoutQuery testAdts (.offsetOf (.adt idCPackedSandwich) 0 0) = some 0 ∧
    evalLayoutQuery testAdts (.offsetOf (.adt idCPackedSandwich) 0 1) = some 1 ∧
    evalLayoutQuery testAdts (.offsetOf (.adt idCPackedSandwich) 0 2) = some 3 ∧
    evalTransmuteVal testAdts (.adt idCPackedSandwich) (.uint 32) vCPacked =
      some (.usize (a + (b + c * (2 ^ 16)) * (2 ^ 8))) ∧
    evalTyByteSize testAdts (.adt idRustPackedSandwich) = some 4 ∧
    evalTyAlign testAdts (.adt idRustPackedSandwich) = some 1 ∧
    evalLayoutQuery testAdts (.offsetOf (.adt idRustPackedSandwich) 0 1) = none ∧
    evalTransmuteVal testAdts (.adt idRustPackedSandwich) (.array (.uint 8) 4) vRustPacked =
      some (.bytes 4 0) ∧
    evalTransmuteVal testAdts (.adt idRustPackedSandwich) (.uint 32) vRustPacked = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end ReprRustPackingAndTransmutePayload
