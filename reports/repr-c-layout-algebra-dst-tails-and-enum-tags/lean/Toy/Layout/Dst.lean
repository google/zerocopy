import Toy.Layout.Struct

namespace Toy.Layout

/-!
# Slice-Tailed `#[repr(C)]` Dynamically Sized Types (DSTs)

This module models flat `#[repr(C)]` structs with fixed sized prefix fields and a trailing
slice `[T]` (with element layout `elem : FieldLayout`), under an optional `packed(N)`
or `align(N)` modifier.

It formalizes:
1. Equivalence between instantiating `[T]` at length `n` (`headFields ++ [⟨n * size T, align T⟩]`)
   and the closed-form formula `dstSize d n = alignUp (dstTailOffset d + n * elem.size) (dstAlign d)`;
2. Exact unbounded-`Nat` characterization of `maxSliceElems d bufferLen` — the maximum
   fitting trailing element count `n` for prefix casts on flat `#[repr(C)]` DSTs, including
   the empty (`none`) regime;
3. Impossibility of a maximum element count for zero-sized trailing elements (`elem.size = 0`)
   over unbounded `Nat`, with a concrete positive control and a proved bounded-domain
   escape hatch (`zst_tail_bounded_max_exists`);
4. Exact characterization of universally zero trailing padding (`dstAlign ∣ dstTailOffset ∧ dstAlign ∣ elem.size`),
   concrete counterexamples showing both failure modes of naive prefix-cast division
   `(bufferLen - tailOffset) / elem.size`, and a proved agreement lemma when all four
   sufficient conditions hold.
-/

/-- Specification of a flat `#[repr(C)]` slice-tailed DST: fixed prefix `headFields`,
    alignment modifier `modifier`, and trailing slice `[T]` with element layout `elem`. -/
structure SliceDstSpec where
  modifier : ReprModifier
  headFields : List FieldLayout
  elem : FieldLayout
  deriving Repr, DecidableEq, BEq

/-- Concrete `#[repr(C)]` struct layout obtained by instantiating the trailing slice
    `[T]` to a fixed array `[T; n]` (`r[layout.array]`, `r[layout.slice]`). -/
def dstInstantiated (d : SliceDstSpec) (n : Nat) : StructLayout :=
  reprCStruct d.modifier (d.headFields ++ [⟨n * d.elem.size, d.elem.align⟩])

/-- Byte offset at which the trailing slice `[T]` begins (independent of `n`).
    Matches `TupleHeadLayout::tail_offset` in MiniRust (`spec/lang/types.md`). -/
def dstTailOffset (d : SliceDstSpec) : Nat :=
  let (_, headEnd) := placeFields d.modifier 0 d.headFields
  alignUp headEnd (effFieldAlign d.modifier d.elem.align)

/-- Overall alignment of the slice-tailed DST (independent of `n`). -/
def dstAlign (d : SliceDstSpec) : Nat :=
  structAlign d.modifier (d.headFields ++ [d.elem])

/-- Closed-form total byte size of the slice-tailed DST for `n` trailing elements:
    `alignUp (dstTailOffset d + n * d.elem.size) (dstAlign d)`. -/
def dstSize (d : SliceDstSpec) (n : Nat) : Nat :=
  alignUp (dstTailOffset d + n * d.elem.size) (dstAlign d)

/-- Number of trailing padding bytes appended after the `n`-element slice to round the
    object size up to `dstAlign d`. (Does not count inter-field padding inside `headFields`.) -/
def dstTrailingPadding (d : SliceDstSpec) (n : Nat) : Nat :=
  dstSize d n - (dstTailOffset d + n * d.elem.size)

theorem ex_dstSize_pos :
    let d : SliceDstSpec := ⟨.none, [⟨2, 2⟩, ⟨1, 1⟩], ⟨1, 1⟩⟩
    dstTailOffset d = 3 ∧ dstAlign d = 2 ∧ dstSize d 0 = 4 ∧ dstSize d 1 = 4 ∧ dstSize d 2 = 6 := by
  decide

theorem ex_dstSize_neg_unaligned :
    let d : SliceDstSpec := ⟨.none, [⟨2, 2⟩, ⟨1, 1⟩], ⟨1, 1⟩⟩
    dstSize d 0 ≠ 3 := by
  decide

/-- Witness computation for the largest trailing slice element count `n` such that
    `dstSize d n ≤ bufferLen`:
    * returns `none` if `d.elem.size = 0` (no maximum exists over `Nat` when `n = 0` fits)
      or if `roundDown bufferLen (dstAlign d) < dstTailOffset d` (equivalently
      `bufferLen < dstSize d 0`, so no `n` fits);
    * otherwise returns `some ((roundDown bufferLen (dstAlign d) - dstTailOffset d) / d.elem.size)`. -/
def maxSliceElems (d : SliceDstSpec) (bufferLen : Nat) : Option Nat :=
  if d.elem.size = 0 then none
  else
    let cap := roundDown bufferLen (dstAlign d)
    if cap < dstTailOffset d then none
    else some ((cap - dstTailOffset d) / d.elem.size)

theorem ex_maxSliceElems_pos_some :
    maxSliceElems ⟨.none, [⟨2, 2⟩, ⟨1, 1⟩], ⟨1, 1⟩⟩ 5 = some 1 := rfl

theorem ex_maxSliceElems_pos_none :
    maxSliceElems ⟨.none, [⟨2, 2⟩, ⟨1, 1⟩], ⟨1, 1⟩⟩ 3 = none := rfl

theorem ex_maxSliceElems_neg_naive :
    maxSliceElems ⟨.none, [⟨2, 2⟩, ⟨1, 1⟩], ⟨1, 1⟩⟩ 5 ≠ some 2 := by decide

/-- Specification predicate: `n` is the greatest natural number whose DST size fits in
    `bufferLen` (`dstSize d n ≤ bufferLen` and every fitting `k` satisfies `k ≤ n`). -/
def IsMaxFittingElems (d : SliceDstSpec) (bufferLen n : Nat) : Prop :=
  dstSize d n ≤ bufferLen ∧ ∀ k : Nat, dstSize d k ≤ bufferLen → k ≤ n

theorem ex_isMaxFittingElems_pos :
    IsMaxFittingElems ⟨.none, [⟨2, 2⟩, ⟨1, 1⟩], ⟨1, 1⟩⟩ 5 1 := by
  refine ⟨by decide, ?_⟩
  intro k hk
  have h1 : dstTailOffset ⟨.none, [⟨2, 2⟩, ⟨1, 1⟩], ⟨1, 1⟩⟩ = 3 := rfl
  have h2 : dstAlign ⟨.none, [⟨2, 2⟩, ⟨1, 1⟩], ⟨1, 1⟩⟩ = 2 := rfl
  dsimp only [dstSize] at hk
  rw [h1, h2] at hk
  simp [alignUp, paddingNeeded] at hk
  split at hk <;> omega

theorem ex_isMaxFittingElems_neg_not_max :
    ¬ IsMaxFittingElems ⟨.none, [⟨2, 2⟩, ⟨1, 1⟩], ⟨1, 1⟩⟩ 5 0 := by
  intro ⟨_, hmax⟩
  have h1 := hmax 1 (by decide)
  omega

theorem ex_isMaxFittingElems_neg_overflows_buf :
    ¬ IsMaxFittingElems ⟨.none, [⟨2, 2⟩, ⟨1, 1⟩], ⟨1, 1⟩⟩ 5 2 := by
  intro ⟨hle, _⟩
  have h6 : dstSize ⟨.none, [⟨2, 2⟩, ⟨1, 1⟩], ⟨1, 1⟩⟩ 2 = 6 := rfl
  rw [h6] at hle
  omega

/-! ## Result 5: DST Closed-Form Size, Max-Element Characterization, and Tightness -/

private theorem foldl_max_ge_init (m : ReprModifier) (fs : List FieldLayout) (init : Nat) :
    init ≤ fs.foldl (fun acc f => max acc (effFieldAlign m f.align)) init := by
  induction fs generalizing init with
  | nil => exact Nat.le_refl _
  | cons f fs ih =>
    simp only [List.foldl_cons]
    exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

private theorem dstAlign_pos (d : SliceDstSpec) : 0 < dstAlign d := by
  unfold dstAlign structAlign fieldsMaxAlign
  cases h : d.modifier with
  | none =>
    dsimp only
    have h1 := foldl_max_ge_init .none (d.headFields ++ [d.elem]) 1
    exact Nat.lt_of_lt_of_le (by decide : 0 < 1) h1
  | packed p =>
    dsimp only
    have h1 := foldl_max_ge_init (.packed p) (d.headFields ++ [d.elem]) 1
    exact Nat.lt_of_lt_of_le (by decide : 0 < 1) h1
  | aligned n =>
    dsimp only
    have h1 := foldl_max_ge_init (.aligned n) (d.headFields ++ [d.elem]) 1
    have h2 := Nat.le_max_left ((d.headFields ++ [d.elem]).foldl
      (fun acc f => max acc (effFieldAlign (.aligned n) f.align)) 1) n
    exact Nat.lt_of_lt_of_le (by decide : 0 < 1) (Nat.le_trans h1 h2)

private theorem placeFields_append_dst (m : ReprModifier) (c : Nat)
    (xs ys : List FieldLayout) :
    placeFields m c (xs ++ ys) =
      ((placeFields m c xs).1 ++ (placeFields m (placeFields m c xs).2 ys).1,
       (placeFields m (placeFields m c xs).2 ys).2) := by
  induction xs generalizing c with
  | nil =>
    simp [placeFields]
  | cons x xs ih =>
    simp only [List.cons_append]
    rw [placeFields_cons, placeFields_cons]
    dsimp only
    rw [ih]
    simp [List.cons_append]

private theorem fieldsMaxAlign_append_same_align (m : ReprModifier)
    (xs : List FieldLayout) (sz₁ sz₂ al : Nat) :
    fieldsMaxAlign m (xs ++ [⟨sz₁, al⟩]) = fieldsMaxAlign m (xs ++ [⟨sz₂, al⟩]) := by
  unfold fieldsMaxAlign
  simp [List.foldl_append]

private theorem dstSize_le_iff (d : SliceDstSpec) (k bufferLen : Nat) :
    dstSize d k ≤ bufferLen ↔
      dstTailOffset d + k * d.elem.size ≤ roundDown bufferLen (dstAlign d) := by
  unfold dstSize
  exact alignUp_le_iff_le_roundDown (dstAlign_pos d)

/-- Main Result 5a: Instantiating a `#[repr(C)]` slice-tailed DST at element count `n`
    always yields alignment `dstAlign d`, size `dstSize d n`, and field offsets equal to
    the head offsets followed by `dstTailOffset d`. -/
theorem dstInstantiated_eq_closed_form (d : SliceDstSpec) (n : Nat) :
    (dstInstantiated d n).align = dstAlign d ∧
    (dstInstantiated d n).size = dstSize d n ∧
    (dstInstantiated d n).offsets =
      (placeFields d.modifier 0 d.headFields).1 ++ [dstTailOffset d] := by
  have heta : (⟨d.elem.size, d.elem.align⟩ : FieldLayout) = d.elem := by
    cases d.elem
    rfl
  have hal : structAlign d.modifier (d.headFields ++ [⟨n * d.elem.size, d.elem.align⟩]) =
      dstAlign d := by
    unfold dstAlign structAlign
    have hf : fieldsMaxAlign d.modifier (d.headFields ++ [⟨n * d.elem.size, d.elem.align⟩]) =
        fieldsMaxAlign d.modifier (d.headFields ++ [d.elem]) := by
      have hf0 := fieldsMaxAlign_append_same_align d.modifier d.headFields
        (n * d.elem.size) d.elem.size d.elem.align
      rw [heta] at hf0
      exact hf0
    cases hmod : d.modifier <;> simp [hmod] at hf ⊢ <;> rw [hf]
  have hp := placeFields_append_dst d.modifier 0 d.headFields [⟨n * d.elem.size, d.elem.align⟩]
  rcases hhead : placeFields d.modifier 0 d.headFields with ⟨hOffs, hEnd⟩
  have htail_off : dstTailOffset d = alignUp hEnd (effFieldAlign d.modifier d.elem.align) := by
    unfold dstTailOffset
    rw [hhead]
  have htail_place :
      placeFields d.modifier hEnd [⟨n * d.elem.size, d.elem.align⟩] =
        ([dstTailOffset d], dstTailOffset d + n * d.elem.size) := by
    simp [placeFields, htail_off]
  rw [hhead] at hp
  dsimp only at hp
  rw [htail_place] at hp
  dsimp only at hp
  unfold dstInstantiated reprCStruct dstSize
  rw [hp, hal]
  exact ⟨rfl, rfl, rfl⟩

theorem nv_dstInstantiated_eq_closed_form :
    let d : SliceDstSpec := ⟨.none, [⟨4, 4⟩, ⟨1, 1⟩], ⟨2, 2⟩⟩
    (dstInstantiated d 3).align = dstAlign d ∧
    (dstInstantiated d 3).size = dstSize d 3 ∧
    (dstInstantiated d 3).offsets = [0, 4, 6] := by
  decide

/-- Main Result 5b: `maxSliceElems d bufferLen = some n` holds if and only if `n` is the
    largest element count with `dstSize d n ≤ bufferLen` (unconditional — holds even when
    `d.elem.size = 0`, where both sides are `False`). -/
theorem maxSliceElems_some_iff (d : SliceDstSpec) (bufferLen n : Nat) :
    maxSliceElems d bufferLen = some n ↔ IsMaxFittingElems d bufferLen n := by
  by_cases hz : d.elem.size = 0
  · unfold maxSliceElems
    simp only [hz, ↓reduceIte]
    constructor
    · rintro ⟨⟩
    · rintro ⟨hfit, hmax⟩
      have hnext : dstSize d (n + 1) ≤ bufferLen := by
        simpa [dstSize, hz] using hfit
      have hle := hmax (n + 1) hnext
      omega
  · have hpos : 0 < d.elem.size := Nat.pos_of_ne_zero hz
    unfold maxSliceElems
    simp only [hz, ↓reduceIte]
    by_cases hcap : roundDown bufferLen (dstAlign d) < dstTailOffset d
    · simp only [hcap, ↓reduceIte]
      constructor
      · rintro ⟨⟩
      · rintro ⟨hfit, _⟩
        rw [dstSize_le_iff] at hfit
        omega
    · simp only [hcap, ↓reduceIte, Option.some.injEq]
      let q := (roundDown bufferLen (dstAlign d) - dstTailOffset d) / d.elem.size
      have hfit_iff : ∀ k : Nat, dstSize d k ≤ bufferLen ↔ k ≤ q := by
        intro k
        rw [dstSize_le_iff]
        constructor
        · intro hk
          have hmul : k * d.elem.size ≤ roundDown bufferLen (dstAlign d) - dstTailOffset d := by
            omega
          exact (Nat.le_div_iff_mul_le hpos).mpr hmul
        · intro hk
          have hmul : k * d.elem.size ≤ roundDown bufferLen (dstAlign d) - dstTailOffset d :=
            (Nat.le_div_iff_mul_le hpos).mp hk
          omega
      constructor
      · rintro rfl
        exact ⟨(hfit_iff q).mpr (Nat.le_refl q), fun k hk => (hfit_iff k).mp hk⟩
      · rintro ⟨hfit_n, hmax_n⟩
        have hn_le : n ≤ q := (hfit_iff n).mp hfit_n
        have hq_le : q ≤ n := hmax_n q ((hfit_iff q).mpr (Nat.le_refl q))
        omega

theorem nv_maxSliceElems_some_iff :
    let d : SliceDstSpec := ⟨.none, [⟨2, 2⟩, ⟨1, 1⟩], ⟨1, 1⟩⟩
    maxSliceElems d 5 = some 1 ∧ IsMaxFittingElems d 5 1 :=
  ⟨rfl, ex_isMaxFittingElems_pos⟩

/-- Main Result 5c: Assuming `0 < d.elem.size`, `maxSliceElems d bufferLen = none` if and
    only if no element count `n` fits (`∀ n, bufferLen < dstSize d n`, equivalently
    `bufferLen < dstSize d 0`). -/
theorem maxSliceElems_none_iff_of_elem_size_pos (d : SliceDstSpec) (bufferLen : Nat)
    (h_elem : 0 < d.elem.size) :
    maxSliceElems d bufferLen = none ↔ ∀ n : Nat, bufferLen < dstSize d n := by
  have hz : d.elem.size ≠ 0 := Nat.ne_of_gt h_elem
  unfold maxSliceElems
  simp only [hz, ↓reduceIte]
  by_cases hcap : roundDown bufferLen (dstAlign d) < dstTailOffset d
  · simp only [hcap, ↓reduceIte, true_iff]
    intro n
    by_cases hle : dstSize d n ≤ bufferLen
    · rw [dstSize_le_iff] at hle
      omega
    · omega
  · simp only [hcap, ↓reduceIte]
    constructor
    · rintro ⟨⟩
    · intro hall
      have h0 : dstSize d 0 ≤ bufferLen := by
        rw [dstSize_le_iff]
        omega
      have hlt0 := hall 0
      omega

theorem nv_maxSliceElems_none_iff_of_elem_size_pos :
    let d : SliceDstSpec := ⟨.none, [⟨2, 2⟩, ⟨1, 1⟩], ⟨1, 1⟩⟩
    0 < d.elem.size ∧ maxSliceElems d 3 = none ∧ ∀ n : Nat, 3 < dstSize d n := by
  refine ⟨by decide, rfl, ?_⟩
  intro n
  have h1 : dstTailOffset ⟨.none, [⟨2, 2⟩, ⟨1, 1⟩], ⟨1, 1⟩⟩ = 3 := rfl
  have h2 : dstAlign ⟨.none, [⟨2, 2⟩, ⟨1, 1⟩], ⟨1, 1⟩⟩ = 2 := rfl
  dsimp only [dstSize]
  rw [h1, h2]
  simp [alignUp, paddingNeeded]
  split <;> omega

/-- Canonical counterexample dropping `h_elem` from `maxSliceElems_none_iff_of_elem_size_pos`:
    for a zero-sized tail element `[()]` (`d.elem.size = 0`) and `bufferLen = 0`,
    `maxSliceElems d 0 = none`, yet `dstSize d 0 = 0 ≤ 0` (so `∀ n, 0 < dstSize d n` is false). -/
theorem ce_maxSliceElems_none_drop_elem_pos :
    let d : SliceDstSpec := ⟨.none, [], ⟨0, 1⟩⟩
    let bufferLen := 0
    ¬ (maxSliceElems d bufferLen = none ↔ ∀ n : Nat, bufferLen < dstSize d n) := by
  dsimp only
  intro h
  have hall := h.mp rfl
  have h0 := hall 0
  have hz : dstSize ⟨.none, [], ⟨0, 1⟩⟩ 0 = 0 := rfl
  rw [hz] at h0
  omega

/-- Main Result 5d (impossibility over unbounded `Nat`, fully proved): When the trailing
    slice element is zero-sized (`d.elem.size = 0`), no `n : Nat` can satisfy
    `IsMaxFittingElems d bufferLen n` for any `bufferLen : Nat` (either no `n` fits, or
    every `n` fits so there is no largest natural number). -/
theorem zst_tail_no_max_fitting_elems (d : SliceDstSpec) (bufferLen : Nat)
    (h_zst : d.elem.size = 0) :
    ∀ n : Nat, ¬ IsMaxFittingElems d bufferLen n := by
  intro n ⟨hfit, hmax⟩
  have hnext : dstSize d (n + 1) ≤ bufferLen := by
    simpa [dstSize, h_zst] using hfit
  have hle := hmax (n + 1) hnext
  omega

theorem nv_zst_tail_no_max_fitting_elems :
    let d : SliceDstSpec := ⟨.none, [⟨4, 4⟩], ⟨0, 1⟩⟩
    d.elem.size = 0 := rfl

/-- Positive control for `zst_tail_no_max_fitting_elems` (also canonical counterexample
    dropping `h_zst`): changing `elem.size` from `0` to `1` (`[u8]` tail) yields a unique
    maximum fitting element count `n = 4` for `bufferLen = 8`. -/
theorem pc_zst_tail_no_max_fitting_elems :
    let d : SliceDstSpec := ⟨.none, [⟨4, 4⟩], ⟨1, 1⟩⟩
    IsMaxFittingElems d 8 4 ∧ ¬ (∀ n : Nat, ¬ IsMaxFittingElems d 8 n) := by
  dsimp only
  have hfit : IsMaxFittingElems ⟨.none, [⟨4, 4⟩], ⟨1, 1⟩⟩ 8 4 := by
    refine ⟨by decide, ?_⟩
    intro k hk
    have h1 : dstTailOffset ⟨.none, [⟨4, 4⟩], ⟨1, 1⟩⟩ = 4 := rfl
    have h2 : dstAlign ⟨.none, [⟨4, 4⟩], ⟨1, 1⟩⟩ = 4 := rfl
    dsimp only [dstSize] at hk
    rw [h1, h2] at hk
    simp [alignUp, paddingNeeded] at hk
    omega
  exact ⟨hfit, fun hall => hall 4 hfit⟩

/-- Bounded-domain escape hatch for `zst_tail_no_max_fitting_elems` (fully proved):
    over any bounded metadata domain `n ≤ B` (such as Rust's `usize::MAX`), when
    `d.elem.size = 0` and `n = 0` fits (`dstSize d 0 ≤ bufferLen`), the bound `B` itself
    is the unique greatest fitting count in `[0, B]`. -/
theorem zst_tail_bounded_max_exists (d : SliceDstSpec) (bufferLen B : Nat)
    (h_zst : d.elem.size = 0) (h_fit0 : dstSize d 0 ≤ bufferLen) :
    dstSize d B ≤ bufferLen ∧ ∀ k : Nat, k ≤ B → dstSize d k ≤ bufferLen → k ≤ B := by
  refine ⟨?_, fun _ hk _ => hk⟩
  simpa [dstSize, h_zst] using h_fit0

/-- Main Result 5e: A flat slice-tailed DST has zero trailing padding for every element
    count `n` if and only if `dstAlign d` divides both `dstTailOffset d` and `d.elem.size`.
    Corresponds to `zerocopy`'s internal `DstLayout::requires_dynamic_padding` predicate in
    the flat case; `zerocopy` documents its predicate as conservative and proves only the
    safety direction (`false` implies no dynamic padding), whereas this theorem gives both
    directions for flat `#[repr(C)]` slice DSTs. -/
theorem dst_no_trailing_padding_all_iff (d : SliceDstSpec) :
    (∀ n : Nat, dstTrailingPadding d n = 0) ↔
      (dstAlign d ∣ dstTailOffset d ∧ dstAlign d ∣ d.elem.size) := by
  have hA : 0 < dstAlign d := dstAlign_pos d
  have hpad_zero_iff : ∀ n : Nat,
      dstTrailingPadding d n = 0 ↔ dstAlign d ∣ (dstTailOffset d + n * d.elem.size) := by
    intro n
    unfold dstTrailingPadding dstSize
    have hx_le :
        dstTailOffset d + n * d.elem.size ≤
          alignUp (dstTailOffset d + n * d.elem.size) (dstAlign d) :=
      le_alignUp (dstTailOffset d + n * d.elem.size) (dstAlign d)
    constructor
    · intro hsub
      have heq :
          alignUp (dstTailOffset d + n * d.elem.size) (dstAlign d) =
            dstTailOffset d + n * d.elem.size := by omega
      rw [← heq]
      exact dvd_alignUp hA
    · intro hdvd
      have heq :
          alignUp (dstTailOffset d + n * d.elem.size) (dstAlign d) =
            dstTailOffset d + n * d.elem.size :=
        alignUp_eq_self_of_dvd hdvd
      omega
  constructor
  · intro hall
    have h0 : dstAlign d ∣ dstTailOffset d := by
      simpa using (hpad_zero_iff 0).mp (hall 0)
    have h1 : dstAlign d ∣ (dstTailOffset d + d.elem.size) := by
      simpa using (hpad_zero_iff 1).mp (hall 1)
    refine ⟨h0, ?_⟩
    rcases h0 with ⟨q0, hq0⟩
    rcases h1 with ⟨q1, hq1⟩
    refine ⟨q1 - q0, ?_⟩
    rw [Nat.mul_sub_left_distrib]
    omega
  · rintro ⟨hT, hS⟩ n
    rw [hpad_zero_iff]
    rcases hS with ⟨qS, hqS⟩
    have hnS : dstAlign d ∣ n * d.elem.size := by
      refine ⟨n * qS, ?_⟩
      rw [hqS]
      calc n * (dstAlign d * qS)
          = (n * dstAlign d) * qS := (Nat.mul_assoc _ _ _).symm
        _ = (dstAlign d * n) * qS := by rw [Nat.mul_comm n (dstAlign d)]
        _ = dstAlign d * (n * qS) := Nat.mul_assoc _ _ _
    exact Nat.dvd_add hT hnS

theorem nv_dst_no_trailing_padding_all_iff :
    let d : SliceDstSpec := ⟨.none, [⟨4, 4⟩], ⟨4, 4⟩⟩
    dstAlign d ∣ dstTailOffset d ∧ dstAlign d ∣ d.elem.size :=
  ⟨⟨1, rfl⟩, ⟨1, rfl⟩⟩

/-- Qualified agreement lemma (fully proved, supporting the non-claim of
    `ce_dst_trailing_padding_breaks_naive_prefix_cast`): when `dstAlign d` divides both
    `dstTailOffset d` and `d.elem.size`, `0 < d.elem.size`, and `dstTailOffset d ≤ bufferLen`,
    naive division `(bufferLen - dstTailOffset d) / d.elem.size` agrees with
    `maxSliceElems d bufferLen`. -/
theorem maxSliceElems_eq_naive_of_no_trailing_padding
    (d : SliceDstSpec) (bufferLen : Nat)
    (h_off : dstAlign d ∣ dstTailOffset d)
    (h_elem_dvd : dstAlign d ∣ d.elem.size)
    (h_elem_pos : 0 < d.elem.size)
    (h_buf : dstTailOffset d ≤ bufferLen) :
    maxSliceElems d bufferLen = some ((bufferLen - dstTailOffset d) / d.elem.size) := by
  have hA : 0 < dstAlign d := dstAlign_pos d
  rcases h_off with ⟨qT, hT⟩
  rcases h_elem_dvd with ⟨qS, hS⟩
  have hA_ne : dstAlign d ≠ 0 := by omega
  have hS_ne : d.elem.size ≠ 0 := by omega
  have hqS_pos : 0 < qS := by
    by_cases h0 : qS = 0
    · subst h0; simp at hS; omega
    · omega
  have hqT_le : qT ≤ bufferLen / dstAlign d := by
    rw [Nat.le_div_iff_mul_le hA, Nat.mul_comm]
    omega
  have hcap_eq : roundDown bufferLen (dstAlign d) = (bufferLen / dstAlign d) * dstAlign d := by
    simp [roundDown, hA_ne]
  have hT_le_cap : dstTailOffset d ≤ roundDown bufferLen (dstAlign d) := by
    rw [hcap_eq, hT, Nat.mul_comm (dstAlign d) qT]
    exact Nat.mul_le_mul_right (dstAlign d) hqT_le
  unfold maxSliceElems
  simp only [hS_ne, ↓reduceIte]
  have hnotlt : ¬ roundDown bufferLen (dstAlign d) < dstTailOffset d := by omega
  simp only [hnotlt, ↓reduceIte]
  congr 1
  have hrem_lt : (bufferLen / dstAlign d - qT) % qS < qS := Nat.mod_lt _ hqS_pos
  have hr_lt : bufferLen % dstAlign d < dstAlign d := Nat.mod_lt _ hA
  have hdiv_decomp :
      bufferLen / dstAlign d - qT =
        qS * ((bufferLen / dstAlign d - qT) / qS) + (bufferLen / dstAlign d - qT) % qS :=
    (Nat.div_add_mod _ _).symm
  have hbuf_eq : bufferLen = roundDown bufferLen (dstAlign d) + bufferLen % dstAlign d := by
    rw [hcap_eq, Nat.mul_comm]
    exact (Nat.div_add_mod bufferLen (dstAlign d)).symm
  have hcap_sub :
      roundDown bufferLen (dstAlign d) - dstTailOffset d =
        d.elem.size * ((bufferLen / dstAlign d - qT) / qS) +
        dstAlign d * ((bufferLen / dstAlign d - qT) % qS) := by
    rw [hcap_eq, hT, hS]
    calc (bufferLen / dstAlign d) * dstAlign d - dstAlign d * qT
        = dstAlign d * (bufferLen / dstAlign d) - dstAlign d * qT := by rw [Nat.mul_comm]
      _ = dstAlign d * (bufferLen / dstAlign d - qT) := (Nat.mul_sub_left_distrib _ _ _).symm
      _ = dstAlign d * (qS * ((bufferLen / dstAlign d - qT) / qS) + (bufferLen / dstAlign d - qT) % qS) :=
          congrArg (dstAlign d * ·) hdiv_decomp
      _ = dstAlign d * (qS * ((bufferLen / dstAlign d - qT) / qS)) +
          dstAlign d * ((bufferLen / dstAlign d - qT) % qS) := Nat.mul_add _ _ _
      _ = (dstAlign d * qS) * ((bufferLen / dstAlign d - qT) / qS) +
          dstAlign d * ((bufferLen / dstAlign d - qT) % qS) := by rw [Nat.mul_assoc]
  have hbuf_sub :
      bufferLen - dstTailOffset d =
        d.elem.size * ((bufferLen / dstAlign d - qT) / qS) +
        (dstAlign d * ((bufferLen / dstAlign d - qT) % qS) + bufferLen % dstAlign d) := by
    omega
  have hrem1_lt : dstAlign d * ((bufferLen / dstAlign d - qT) % qS) < d.elem.size := by
    rw [hS]
    exact Nat.mul_lt_mul_of_pos_left hrem_lt hA
  have hrem2_lt :
      dstAlign d * ((bufferLen / dstAlign d - qT) % qS) + bufferLen % dstAlign d < d.elem.size := by
    have hstep : dstAlign d * ((bufferLen / dstAlign d - qT) % qS) + dstAlign d ≤ dstAlign d * qS := by
      have h1 : dstAlign d * (((bufferLen / dstAlign d - qT) % qS) + 1) ≤ dstAlign d * qS :=
        Nat.mul_le_mul_left (dstAlign d) (by omega)
      simpa [Nat.mul_add] using h1
    omega
  rw [hcap_sub, hbuf_sub, Nat.mul_add_div h_elem_pos, Nat.mul_add_div h_elem_pos,
    Nat.div_eq_of_lt hrem1_lt, Nat.div_eq_of_lt hrem2_lt]

/-- Edge-case counterexample showing `0 < d.elem.size` cannot be dropped from
    `maxSliceElems_eq_naive_of_no_trailing_padding`: for `elem = ⟨0, 4⟩`, `dstAlign ∣ 0`
    holds, yet naive `(8 - 4) / 0 = 0` while `maxSliceElems` returns `none`. -/
theorem ce_naive_agrees_fails_zst :
    let d : SliceDstSpec := ⟨.none, [⟨4, 4⟩], ⟨0, 4⟩⟩
    dstAlign d ∣ dstTailOffset d ∧ dstAlign d ∣ d.elem.size ∧
    dstTailOffset d ≤ 8 ∧
    (8 - dstTailOffset d) / d.elem.size = 0 ∧
    maxSliceElems d 8 = none := by
  decide

/-- Edge-case counterexample showing `dstTailOffset d ≤ bufferLen` cannot be dropped from
    `maxSliceElems_eq_naive_of_no_trailing_padding`: with `Nat` truncating subtraction,
    `(2 - 4) / 4 = 0` claims `n = 0` fits even though `dstSize d 0 = 4 > 2` and
    `maxSliceElems d 2 = none`. -/
theorem ce_naive_agrees_fails_short_buffer :
    let d : SliceDstSpec := ⟨.none, [⟨4, 4⟩], ⟨4, 4⟩⟩
    dstAlign d ∣ dstTailOffset d ∧ dstAlign d ∣ d.elem.size ∧
    0 < d.elem.size ∧
    (2 - dstTailOffset d) / d.elem.size = 0 ∧
    maxSliceElems d 2 = none ∧
    2 < dstSize d 0 := by
  decide

/-- Main Result 5f (tightness counterexample, fully proved): When
    `¬ (dstAlign d ∣ dstTailOffset d ∧ dstAlign d ∣ d.elem.size)`, trailing padding can
    break naive prefix-cast division `(bufferLen - dstTailOffset d) / d.elem.size` and the
    naive tail-fit test `dstTailOffset d ≤ bufferLen`. Three witnesses separate the failure modes:
    1. `d1 = ⟨.none, [⟨4, 4⟩], ⟨1, 1⟩⟩` (`dstAlign ∣ dstTailOffset` holds, `¬ (dstAlign ∣ elem.size)`):
       `dstTrailingPadding d1 1 = 3`, and at `bufferLen = 5`, naive `(5 - 4) / 1 = 1`
       over-estimates (`dstSize d1 1 = 8 > 5`) while `maxSliceElems d1 5 = some 0` and
       `IsMaxFittingElems d1 5 0`.
    2. `d2 = ⟨.none, [⟨2, 2⟩, ⟨1, 1⟩], ⟨1, 1⟩⟩` (neither divisibility holds):
       at `bufferLen = 3`, `dstTailOffset d2 = 3 ≤ 3` holds yet `maxSliceElems d2 3 = none`
       and `∀ n, 3 < dstSize d2 n`.
    3. `d3 = ⟨.none, [⟨2, 2⟩, ⟨1, 1⟩], ⟨2, 1⟩⟩` (e.g. tail `[[u8; 2]]`: `dstAlign ∣ elem.size`
       holds while `¬ (dstAlign ∣ dstTailOffset)`): at `bufferLen = 5`, naive `(5 - 3) / 2 = 1`
       over-estimates (`dstSize d3 1 = 6 > 5`, `maxSliceElems d3 5 = some 0`), and at
       `bufferLen = 3`, `dstTailOffset d3 = 3 ≤ 3` yet `maxSliceElems d3 3 = none` and
       `∀ n, 3 < dstSize d3 n`. -/
theorem ce_dst_trailing_padding_breaks_naive_prefix_cast :
    let d1 : SliceDstSpec := ⟨.none, [⟨4, 4⟩], ⟨1, 1⟩⟩
    let d2 : SliceDstSpec := ⟨.none, [⟨2, 2⟩, ⟨1, 1⟩], ⟨1, 1⟩⟩
    let d3 : SliceDstSpec := ⟨.none, [⟨2, 2⟩, ⟨1, 1⟩], ⟨2, 1⟩⟩
    -- Instance 1: dstAlign ∣ dstTailOffset, ¬ (dstAlign ∣ elem.size)
    (dstAlign d1 ∣ dstTailOffset d1) ∧
    ¬ (dstAlign d1 ∣ d1.elem.size) ∧
    dstTrailingPadding d1 1 = 3 ∧
    (5 - dstTailOffset d1) / d1.elem.size = 1 ∧
    5 < dstSize d1 1 ∧
    maxSliceElems d1 5 = some 0 ∧
    IsMaxFittingElems d1 5 0 ∧
    -- Instance 2: ¬ (dstAlign ∣ dstTailOffset) ∧ ¬ (dstAlign ∣ elem.size)
    ¬ (dstAlign d2 ∣ dstTailOffset d2) ∧
    ¬ (dstAlign d2 ∣ d2.elem.size) ∧
    dstTailOffset d2 ≤ 3 ∧
    maxSliceElems d2 3 = none ∧
    (∀ n : Nat, 3 < dstSize d2 n) ∧
    -- Instance 3: dstAlign ∣ elem.size, ¬ (dstAlign ∣ dstTailOffset)
    (dstAlign d3 ∣ d3.elem.size) ∧
    ¬ (dstAlign d3 ∣ dstTailOffset d3) ∧
    (5 - dstTailOffset d3) / d3.elem.size = 1 ∧
    5 < dstSize d3 1 ∧
    maxSliceElems d3 5 = some 0 ∧
    IsMaxFittingElems d3 5 0 ∧
    dstTailOffset d3 ≤ 3 ∧
    maxSliceElems d3 3 = none ∧
    (∀ n : Nat, 3 < dstSize d3 n) := by
  refine ⟨⟨1, rfl⟩, by decide, rfl, rfl, by decide, rfl, ?_,
    by decide, by decide, by decide, rfl, ?_,
    ⟨1, rfl⟩, by decide, rfl, by decide, rfl, ?_, by decide, rfl, ?_⟩
  · refine ⟨by decide, ?_⟩
    intro k hk
    have h1 : dstTailOffset ⟨.none, [⟨4, 4⟩], ⟨1, 1⟩⟩ = 4 := rfl
    have h2 : dstAlign ⟨.none, [⟨4, 4⟩], ⟨1, 1⟩⟩ = 4 := rfl
    dsimp only [dstSize] at hk
    rw [h1, h2] at hk
    simp [alignUp, paddingNeeded] at hk
    split at hk <;> omega
  · intro n
    have h1 : dstTailOffset ⟨.none, [⟨2, 2⟩, ⟨1, 1⟩], ⟨1, 1⟩⟩ = 3 := rfl
    have h2 : dstAlign ⟨.none, [⟨2, 2⟩, ⟨1, 1⟩], ⟨1, 1⟩⟩ = 2 := rfl
    dsimp only [dstSize]
    rw [h1, h2]
    simp [alignUp, paddingNeeded]
    split <;> omega
  · refine ⟨by decide, ?_⟩
    intro k hk
    have h1 : dstTailOffset ⟨.none, [⟨2, 2⟩, ⟨1, 1⟩], ⟨2, 1⟩⟩ = 3 := rfl
    have h2 : dstAlign ⟨.none, [⟨2, 2⟩, ⟨1, 1⟩], ⟨2, 1⟩⟩ = 2 := rfl
    dsimp only [dstSize] at hk
    rw [h1, h2] at hk
    simp [alignUp, paddingNeeded] at hk
    omega
  · intro n
    have h1 : dstTailOffset ⟨.none, [⟨2, 2⟩, ⟨1, 1⟩], ⟨2, 1⟩⟩ = 3 := rfl
    have h2 : dstAlign ⟨.none, [⟨2, 2⟩, ⟨1, 1⟩], ⟨2, 1⟩⟩ = 2 := rfl
    dsimp only [dstSize]
    rw [h1, h2]
    simp [alignUp, paddingNeeded]
    omega

/-! ## Normal-Form Size and Capacity Identities

The following lemmas restate `dstSize` and `maxSliceElems` in terms of a normal form
`(size_base, size_align, size_phase)`, in which the size for `n` trailing elements is
`size_base + alignUp (size_phase + n * d.elem.size) size_align` and the prefix-cast element
capacity for `bufferLen` bytes is
`(roundDown (bufferLen - size_base) size_align - size_phase) / d.elem.size`
(with `none` when either subtraction would underflow). -/

/-- With `size_align := dstAlign d`, `size_phase := dstTailOffset d % dstAlign d`, and
    `size_base := dstTailOffset d - size_phase`, the normal-form size formula equals
    `dstSize d n` for every element count `n`. No hypotheses are needed. -/
theorem dstSize_eq_phase_normal_form (d : SliceDstSpec) (n : Nat) :
    dstSize d n =
      (dstTailOffset d - dstTailOffset d % dstAlign d) +
        alignUp (dstTailOffset d % dstAlign d + n * d.elem.size) (dstAlign d) := by
  unfold dstSize
  have hle := Nat.mod_le (dstTailOffset d) (dstAlign d)
  have hsplit : dstTailOffset d + n * d.elem.size =
      (dstTailOffset d - dstTailOffset d % dstAlign d) +
        (dstTailOffset d % dstAlign d + n * d.elem.size) := by omega
  rw [hsplit]
  exact alignUp_add_of_dvd_left (Nat.dvd_sub_mod (dstTailOffset d))

private theorem roundDown_sub_of_dvd {x c a : Nat} (ha : 0 < a) (hc : a ∣ c) :
    roundDown (x - c) a = roundDown x a - c := by
  rcases hc with ⟨q, rfl⟩
  have ha0 : a ≠ 0 := Nat.pos_iff_ne_zero.mp ha
  have hq : (x - a * q) / a = x / a - q := Nat.sub_mul_div x a q
  simp only [roundDown, ha0, ↓reduceIte]
  rw [hq, Nat.sub_mul, Nat.mul_comm q a]

/-- With the same normal-form parameters as `dstSize_eq_phase_normal_form` and a positive
    element size, `maxSliceElems d bufferLen` equals the normal-form prefix-cast capacity:
    `none` if `bufferLen < size_base` or `roundDown (bufferLen - size_base) size_align <
    size_phase`, and otherwise
    `some ((roundDown (bufferLen - size_base) size_align - size_phase) / d.elem.size)`. -/
theorem maxSliceElems_eq_phase_normal_form_capacity (d : SliceDstSpec) (bufferLen : Nat)
    (h_elem : 0 < d.elem.size) :
    maxSliceElems d bufferLen =
      if bufferLen < dstTailOffset d - dstTailOffset d % dstAlign d then none
      else if roundDown (bufferLen - (dstTailOffset d - dstTailOffset d % dstAlign d))
          (dstAlign d) < dstTailOffset d % dstAlign d then none
      else some ((roundDown (bufferLen - (dstTailOffset d - dstTailOffset d % dstAlign d))
          (dstAlign d) - dstTailOffset d % dstAlign d) / d.elem.size) := by
  have ha := dstAlign_pos d
  have hdvd : dstAlign d ∣ dstTailOffset d - dstTailOffset d % dstAlign d :=
    Nat.dvd_sub_mod (dstTailOffset d)
  have hmod := Nat.mod_le (dstTailOffset d) (dstAlign d)
  have hRle : roundDown bufferLen (dstAlign d) ≤ bufferLen := roundDown_le bufferLen ha
  have hne : d.elem.size ≠ 0 := Nat.pos_iff_ne_zero.mp h_elem
  unfold maxSliceElems
  simp only [hne, ↓reduceIte]
  by_cases hlt : bufferLen < dstTailOffset d - dstTailOffset d % dstAlign d
  · have hcap : roundDown bufferLen (dstAlign d) < dstTailOffset d := by omega
    simp only [hlt, hcap, ↓reduceIte]
  · have hge : dstTailOffset d - dstTailOffset d % dstAlign d ≤ bufferLen := by omega
    have hR : roundDown (bufferLen - (dstTailOffset d - dstTailOffset d % dstAlign d)) (dstAlign d) =
        roundDown bufferLen (dstAlign d) - (dstTailOffset d - dstTailOffset d % dstAlign d) :=
      roundDown_sub_of_dvd ha hdvd
    have hbaseR : dstTailOffset d - dstTailOffset d % dstAlign d ≤
        roundDown bufferLen (dstAlign d) := le_roundDown_of_dvd ha hge hdvd
    rw [hR]
    by_cases hcap : roundDown bufferLen (dstAlign d) < dstTailOffset d
    · have hcap' : roundDown bufferLen (dstAlign d) -
          (dstTailOffset d - dstTailOffset d % dstAlign d) < dstTailOffset d % dstAlign d := by
        omega
      simp only [hlt, hcap, hcap', ↓reduceIte]
    · have hcap' : ¬ (roundDown bufferLen (dstAlign d) -
          (dstTailOffset d - dstTailOffset d % dstAlign d) < dstTailOffset d % dstAlign d) := by
        omega
      have hsub : roundDown bufferLen (dstAlign d) -
          (dstTailOffset d - dstTailOffset d % dstAlign d) - dstTailOffset d % dstAlign d =
          roundDown bufferLen (dstAlign d) - dstTailOffset d := by omega
      simp only [hlt, hcap, hcap', hsub, ↓reduceIte]

/-- If `dstAlign d` and `d.elem.align` both divide `d.elem.size`, then `dstSize d n` equals
    the normal-form size formula with `size_align := d.elem.align`, `size_phase := 0`, and
    `size_base := alignUp (dstTailOffset d) (dstAlign d)`. -/
theorem dstSize_eq_unphased_normal_form_of_dvd (d : SliceDstSpec) (n : Nat)
    (h_align_dvd : dstAlign d ∣ d.elem.size) (h_elem_dvd : d.elem.align ∣ d.elem.size) :
    dstSize d n =
      alignUp (dstTailOffset d) (dstAlign d) + alignUp (0 + n * d.elem.size) d.elem.align := by
  unfold dstSize
  rw [Nat.zero_add, alignUp_eq_self_of_dvd (Nat.dvd_mul_left_of_dvd h_elem_dvd n),
    Nat.add_comm (dstTailOffset d),
    alignUp_add_of_dvd_left (Nat.dvd_mul_left_of_dvd h_align_dvd n), Nat.add_comm]

end Toy.Layout
