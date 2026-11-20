import ToyZc.Transmute

/-!
# Result group 6: `KnownLayout` for slice DSTs

A model of zerocopy's slice-DST layout description and of
`DstLayout::validate_cast_and_convert_metadata` (`zerocopy/src/layout.rs:1650-1797` at commit
`c55af491426ef53f35fb8c6e83f220fa07712e66`). The model uses unbounded natural numbers (no `usize`
overflow) and replaces zerocopy's bit-mask arithmetic by the arithmetic it implements for
power-of-two alignments: `round_down_to_next_multiple_of_alignment(n, a) = n & !(a - 1)`
(`zerocopy/src/util/mod.rs:237-255`) is modeled by `roundDown n a`, and the bitwise OR
`aligned_bytes | initial_padding` (`layout.rs:339`) by `+` (the source comment at `layout.rs:333-339`
states that the operands have disjoint bits).

* `vccm_sliceDst_returns_max_fitting_elems` (R6a): if the size-rounding alignment is positive, the
  phase is at most that alignment, the element size is positive, and the alignment check passes,
  then the model returns `Ok((elems, split_at))` with `elems` the largest element count whose object
  size fits in `bytes_len` (and `split_at` the prefix/suffix split for that size), and returns the
  size error exactly when no element count fits.
* `vccm_sliceDst_start_aligned_of_align_dvd` (R6d): if the layout's alignment divides the size base
  and the size-rounding alignment (so every object size is a multiple of it), then on success the
  object's start (`addr` for a prefix cast, `addr + split_at` for a suffix cast) is aligned.
* `normalizeDst_sizeForElems_eq_dstSize` (R6b): for a flat `repr(C)` slice DST, the normalized
  layout `normalizeDst d` has object size `dstSize d n` (the closed-form size of the `repr(C)`
  layout model in `ToyZc.Layout`).
* `vccm_normalizeDst_elems_eq_maxSliceElems_of_aligned` (R6c): for such a DST, when the alignment
  check passes, the element count returned by the model equals `maxSliceElems d bytes_len`.

The layout alignment `align` is a free parameter of `DstLayout` here (as `DstLayout.align` is a free
field in zerocopy); R6a and R6c do not relate it to `TrailingSliceLayout`. The coupling that makes
suffix casts start at an aligned address is the separate hypothesis pair of R6d.
`TrailingSliceLayout.offset` is carried for fidelity but is not read by the validation (nor by
zerocopy's `validate_cast_and_convert_metadata`).
-/

namespace Toy.Zc

/-- A slice DST's trailing-slice layout (`TrailingSliceLayout`, `layout.rs:153-207`): the offset of
the trailing slice, the element size, and the normalized size formula
`size_base + round_up(size_phase + elems * elem_size, size_align)`. -/
structure TrailingSliceLayout where
  offset : Nat
  elemSize : Nat
  sizeBase : Nat
  sizeAlign : Nat
  sizePhase : Nat
  deriving Repr, DecidableEq

/-- Sized or slice-DST size information (`SizeInfo`, `layout.rs:47-50`). -/
inductive SizeInfo where
  | sized (size : Nat)
  | sliceDst (t : TrailingSliceLayout)
  deriving Repr, DecidableEq

/-- A type layout (`DstLayout`, `layout.rs:34-42`; the `statically_shallow_unpadded` flag is
omitted). -/
structure DstLayout where
  align : Nat
  sizeInfo : SizeInfo
  deriving Repr, DecidableEq

/-- Prefix or suffix cast (`CastType`, `layout.rs:810-813`). -/
inductive CastType where
  | prefixCast
  | suffixCast
  deriving Repr, DecidableEq

/-- Outcome of the metadata validation: `Ok((elems, split_at))`, `Err(Alignment)`, `Err(Size)`, or a
panic (zero-sized trailing element, `layout.rs:1688-1691`). -/
inductive VccmResult where
  | ok (elems splitAt : Nat)
  | alignmentErr
  | sizeErr
  | panic
  deriving Repr, DecidableEq

/-- Object size for `n` trailing elements (`layout.rs:190-194`). -/
def TrailingSliceLayout.sizeForElems (t : TrailingSliceLayout) (n : Nat) : Nat :=
  t.sizeBase + alignUp (t.sizePhase + n * t.elemSize) t.sizeAlign

/-- Model of `TrailingSliceLayout::max_trailing_bytes` (`layout.rs:252-341`). -/
def TrailingSliceLayout.maxTrailingBytes (t : TrailingSliceLayout) (avail : Nat) : Option Nat :=
  let roundedPhase := if t.sizePhase = 0 then 0 else t.sizeAlign
  let minimumSize := t.sizeBase + roundedPhase
  if avail < minimumSize then none
  else
    let extra := avail - minimumSize
    let aligned := roundDown extra t.sizeAlign
    let initialPadding := roundedPhase - t.sizePhase
    some (aligned + initialPadding)

/-- The address offset whose alignment is checked (`layout.rs:1713-1716`). -/
def castOffset : CastType → Nat → Nat
  | .prefixCast, _ => 0
  | .suffixCast, bytesLen => bytesLen

/-- The split index for an object of size `size` (`layout.rs:1785-1794`). -/
def splitFor : CastType → Nat → Nat → Nat
  | .prefixCast, _, size => size
  | .suffixCast, bytesLen, size => bytesLen - size

/-- Whether the layout is a slice DST with a zero-sized element (the validation panics). -/
def DstLayout.zstElem (l : DstLayout) : Bool :=
  match l.sizeInfo with
  | .sliceDst t => t.elemSize == 0
  | .sized _ => false

/-- Model of `DstLayout::validate_cast_and_convert_metadata` (`layout.rs:1650-1797`). -/
def vccm (l : DstLayout) (addr bytesLen : Nat) (ct : CastType) : VccmResult :=
  if l.zstElem then .panic
  else if (addr + castOffset ct bytesLen) % l.align != 0 then .alignmentErr
  else
    match l.sizeInfo with
    | .sized size => if size > bytesLen then .sizeErr else .ok 0 (splitFor ct bytesLen size)
    | .sliceDst t =>
      match t.maxTrailingBytes bytesLen with
      | none => .sizeErr
      | some maxSlice =>
        let elems := maxSlice / t.elemSize
        let unused := maxSlice % t.elemSize
        let unusedAligned := roundDown unused t.sizeAlign
        let maxRounded := roundDown (bytesLen - t.sizeBase) t.sizeAlign
        let selfBytes := t.sizeBase + (maxRounded - unusedAligned)
        .ok elems (splitFor ct bytesLen selfBytes)

/-- `n` is the largest element count whose object size fits in `bytesLen`. -/
def TrailingSliceLayout.IsMaxFit (t : TrailingSliceLayout) (bytesLen n : Nat) : Prop :=
  t.sizeForElems n ≤ bytesLen ∧ ∀ k, t.sizeForElems k ≤ bytesLen → k ≤ n

/-- The trailing-slice layout of the flat `repr(C)` slice DST `d`: base `T - T % A` and phase
`T % A`, where `T = dstTailOffset d` and `A = dstAlign d`. -/
def normalizeDst (d : SliceDstSpec) : TrailingSliceLayout where
  offset := dstTailOffset d
  elemSize := d.elem.size
  sizeBase := dstTailOffset d - dstTailOffset d % dstAlign d
  sizeAlign := dstAlign d
  sizePhase := dstTailOffset d % dstAlign d

/-- The element count of a successful validation (`none` for any error or panic). -/
def VccmResult.elems? : VccmResult → Option Nat
  | .ok e _ => some e
  | _ => none

/-- A running example: `#[repr(C)] struct { a: u16, b: u8, t: [u8] }` (trailing offset 3,
alignment 2). -/
def exampleDst : SliceDstSpec := ⟨.none, [⟨2, 2⟩, ⟨1, 1⟩], ⟨1, 1⟩⟩

/-- A slice-DST layout with size-rounding alignment 4 and phase 3 (e.g. the flat DST
`#[repr(C)] struct { a: u32, b: [u16; 1], c: u8, t: [u8] }` would have trailing offset 7 and
alignment 4). -/
def exampleTsl : TrailingSliceLayout := ⟨7, 1, 4, 4, 3⟩

theorem ex_sizeForElems_pos : exampleTsl.sizeForElems 0 = 8 ∧ exampleTsl.sizeForElems 2 = 12 := by
  decide
theorem ex_sizeForElems_neg : exampleTsl.sizeForElems 1 ≠ 9 := by decide
theorem ex_maxTrailingBytes_pos : exampleTsl.maxTrailingBytes 11 = some 1 := rfl
theorem ex_maxTrailingBytes_neg : exampleTsl.maxTrailingBytes 7 = none := rfl
theorem ex_vccm_pos : vccm ⟨4, .sliceDst exampleTsl⟩ 0 14 .prefixCast = .ok 5 12 := by decide
theorem ex_vccm_neg_align : vccm ⟨4, .sliceDst exampleTsl⟩ 2 14 .prefixCast = .alignmentErr := by
  decide
theorem ex_vccm_neg_size : vccm ⟨4, .sliceDst exampleTsl⟩ 0 7 .prefixCast = .sizeErr := by decide
theorem ex_vccm_suffix : vccm ⟨4, .sliceDst exampleTsl⟩ 0 16 .suffixCast = .ok 9 0 := by decide
theorem ex_normalizeDst_pos : normalizeDst exampleDst = ⟨3, 1, 2, 2, 1⟩ := by decide
theorem ex_normalizeDst_neg : (normalizeDst exampleDst).sizePhase ≠ 0 := by decide
theorem ex_isMaxFit_pos : exampleTsl.IsMaxFit 13 5 := by
  refine ⟨by decide, fun k hk => ?_⟩
  have h : 4 + alignUp (3 + k * 1) 4 ≤ 13 := hk
  unfold alignUp paddingNeeded at h
  simp only [Nat.mul_one, show (4 : Nat) ≠ 0 by decide, ↓reduceIte] at h
  split at h <;> omega
theorem ex_isMaxFit_neg : ¬ exampleTsl.IsMaxFit 13 4 := fun h =>
  absurd (h.2 5 (by decide)) (by decide)
/-- The `.sized` arm of the validation: a sized type of size 4 and alignment 2 fits in 6 bytes
(suffix split at 2) but not in 3 bytes. -/
theorem ex_vccm_sized_pos : vccm ⟨2, .sized 4⟩ 0 6 .suffixCast = .ok 0 2 := by decide
theorem ex_vccm_sized_neg : vccm ⟨2, .sized 4⟩ 0 3 .prefixCast = .sizeErr := by decide

/-- The offset of a successful cast's object start relative to `addr`: `0` for a prefix cast,
`split_at` for a suffix cast. -/
def startOffset : CastType → Nat → Nat
  | .prefixCast, _ => 0
  | .suffixCast, splitAt => splitAt

theorem ex_startOffset_pos : startOffset .suffixCast 3 = 3 := rfl
theorem ex_startOffset_neg : startOffset .prefixCast 3 ≠ 3 := by decide

/-- `dstAlign d` is positive. -/
theorem dstAlign_pos (d : SliceDstSpec) : 0 < dstAlign d := by
  have hfold : ∀ (m : ReprModifier) (l : List FieldLayout) (acc : Nat),
      acc ≥ 1 → l.foldl (fun a f => max a (effFieldAlign m f.align)) acc ≥ 1 := by
    intro m l
    induction l with
    | nil => intro acc h; exact h
    | cons x xs ih =>
      intro acc h
      simp only [List.foldl_cons]
      exact ih _ (by omega)
  have h1 := hfold d.modifier (d.headFields ++ [d.elem]) 1 (by omega)
  unfold dstAlign structAlign fieldsMaxAlign
  cases hm : d.modifier with
  | none => rw [hm] at h1; simp only; omega
  | packed _ => rw [hm] at h1; simp only; omega
  | aligned _ => rw [hm] at h1; simp only; omega

/-- The normalized layout of a flat `repr(C)` slice DST, with layout alignment `dstAlign d`,
satisfies both divisibility hypotheses of R6d (fully proved). -/
theorem normalizeDst_align_dvd (d : SliceDstSpec) :
    dstAlign d ∣ (normalizeDst d).sizeBase ∧ dstAlign d ∣ (normalizeDst d).sizeAlign := by
  refine ⟨?_, Nat.dvd_refl _⟩
  show dstAlign d ∣ dstTailOffset d - dstTailOffset d % dstAlign d
  refine ⟨dstTailOffset d / dstAlign d, ?_⟩
  have := Nat.div_add_mod (dstTailOffset d) (dstAlign d)
  omega

/-- Auxiliary: `alignUp T A` in terms of `T % A`. -/
theorem alignUp_eq_sub_mod_add (T A : Nat) (hA : 0 < A) :
    alignUp T A = (T - T % A) + (if T % A = 0 then 0 else A) := by
  have hA0 : A ≠ 0 := Nat.ne_of_gt hA
  have hlt := Nat.mod_lt T hA
  have hle := Nat.mod_le T A
  unfold alignUp paddingNeeded
  simp only [hA0, ↓reduceIte]
  split <;> omega

/-! ## Main statements -/

/-- **R6a.** For a slice-DST layout with positive size-rounding alignment, phase at most that
alignment, and positive element size, if the alignment check passes then the modeled
`validate_cast_and_convert_metadata` returns `Ok((elems, split_at))` where `elems` is the largest
element count whose object size fits in `bytesLen` and `split_at` is the split for that object
size, and it returns `Err(Size)` exactly when no element count fits. (zerocopy's
`RoundingAlignAndPhase` guarantees the stronger `phase < align`; the statement holds at
`phase = align` as well.) -/
theorem vccm_sliceDst_returns_max_fitting_elems (align addr bytesLen : Nat) (ct : CastType)
    (t : TrailingSliceLayout) (hA : 0 < t.sizeAlign) (hP : t.sizePhase ≤ t.sizeAlign)
    (hE : 0 < t.elemSize) (hAl : (addr + castOffset ct bytesLen) % align = 0) :
    match vccm ⟨align, .sliceDst t⟩ addr bytesLen ct with
    | .ok elems splitAt =>
        t.IsMaxFit bytesLen elems ∧ splitAt = splitFor ct bytesLen (t.sizeForElems elems)
    | .sizeErr => ∀ n, bytesLen < t.sizeForElems n
    | _ => False := by
  have hE0 : (t.elemSize == 0) = false := beq_false_of_ne (Nat.ne_of_gt hE)
  have hAl0 : ((addr + castOffset ct bytesLen) % align != 0) = false := by
    simp [bne, hAl]
  unfold vccm DstLayout.zstElem
  dsimp only
  simp only [hE0, Bool.false_eq_true, ↓reduceIte, hAl0]
  let rp : Nat := if t.sizePhase = 0 then 0 else t.sizeAlign
  have hrp_eq : rp = (if t.sizePhase = 0 then 0 else t.sizeAlign) := rfl
  cases hmtb : t.maxTrailingBytes bytesLen with
  | none =>
    dsimp only
    unfold TrailingSliceLayout.maxTrailingBytes at hmtb
    dsimp only at hmtb
    have hrp_align : alignUp t.sizePhase t.sizeAlign = rp := by
      rw [hrp_eq]
      exact alignUp_phase_eq hA hP
    have hlt : bytesLen < t.sizeBase + rp := by
      by_cases h : bytesLen < t.sizeBase + (if t.sizePhase = 0 then 0 else t.sizeAlign)
      · simpa [← hrp_eq] using h
      · simp [h] at hmtb
    intro n
    have hmono : rp ≤ alignUp (t.sizePhase + n * t.elemSize) t.sizeAlign := by
      rw [← hrp_align]
      exact alignUp_le_of_dvd hA (dvd_alignUp hA)
        (Nat.le_trans (Nat.le_add_right _ _) (le_alignUp _ _))
    unfold TrailingSliceLayout.sizeForElems
    omega
  | some maxSlice =>
    dsimp only
    unfold TrailingSliceLayout.maxTrailingBytes at hmtb
    dsimp only at hmtb
    have hnot_lt_raw :
        ¬ bytesLen < t.sizeBase + (if t.sizePhase = 0 then 0 else t.sizeAlign) := by
      intro h
      simp [h] at hmtb
    simp only [hnot_lt_raw, ↓reduceIte, Option.some.injEq] at hmtb
    have hmin_le : t.sizeBase + rp ≤ bytesLen := by
      have := Nat.not_lt.mp hnot_lt_raw
      simpa [← hrp_eq] using this
    have hB_le : t.sizeBase ≤ bytesLen := by omega
    have hP_le_rp : t.sizePhase ≤ rp := by
      rw [hrp_eq]
      split
      · omega
      · exact hP
    have hrp_mul : ∃ c, rp = c * t.sizeAlign := by
      rw [hrp_eq]
      split
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
    rcases hrp_mul with ⟨c, hrp_c⟩
    let extra : Nat := bytesLen - (t.sizeBase + rp)
    let aligned : Nat := roundDown extra t.sizeAlign
    let maxRounded : Nat := roundDown (bytesLen - t.sizeBase) t.sizeAlign
    have hextra_add : bytesLen - t.sizeBase = extra + c * t.sizeAlign := by
      show bytesLen - t.sizeBase = bytesLen - (t.sizeBase + rp) + c * t.sizeAlign
      omega
    have hmaxRounded_eq : maxRounded = aligned + rp := by
      show roundDown (bytesLen - t.sizeBase) t.sizeAlign = roundDown extra t.sizeAlign + rp
      rw [hextra_add, roundDown_add_mul_self extra c t.sizeAlign hA, ← hrp_c]
    have hmaxSlice_eq : maxSlice = aligned + (rp - t.sizePhase) := by
      simpa [extra, aligned, ← hrp_eq] using hmtb.symm
    have hP_add_maxSlice : t.sizePhase + maxSlice = maxRounded := by
      omega
    have hfit_iff : ∀ k, t.sizeForElems k ≤ bytesLen ↔ k ≤ maxSlice / t.elemSize := by
      intro k
      unfold TrailingSliceLayout.sizeForElems
      constructor
      · intro hk
        have h1 : alignUp (t.sizePhase + k * t.elemSize) t.sizeAlign ≤ bytesLen - t.sizeBase := by
          omega
        have h2 : t.sizePhase + k * t.elemSize ≤ maxRounded :=
          (alignUp_le_iff_le_roundDown hA).mp h1
        have h3 : k * t.elemSize ≤ maxSlice := by omega
        exact (Nat.le_div_iff_mul_le hE).mpr h3
      · intro hk
        have h3 : k * t.elemSize ≤ maxSlice := (Nat.le_div_iff_mul_le hE).mp hk
        have h2 : t.sizePhase + k * t.elemSize ≤ maxRounded := by omega
        have h1 : alignUp (t.sizePhase + k * t.elemSize) t.sizeAlign ≤ bytesLen - t.sizeBase :=
          (alignUp_le_iff_le_roundDown hA).mpr h2
        omega
    refine ⟨⟨(hfit_iff (maxSlice / t.elemSize)).mpr (Nat.le_refl _), fun k hk => (hfit_iff k).mp hk⟩, ?_⟩
    have hdiv_elem : (maxSlice / t.elemSize) * t.elemSize + maxSlice % t.elemSize = maxSlice := by
      rw [Nat.mul_comm]
      exact Nat.div_add_mod maxSlice t.elemSize
    have hsum_mr : (t.sizePhase + (maxSlice / t.elemSize) * t.elemSize) + maxSlice % t.elemSize =
        maxRounded := by
      omega
    have hsub_eq : maxRounded - roundDown (maxSlice % t.elemSize) t.sizeAlign =
        alignUp (t.sizePhase + (maxSlice / t.elemSize) * t.elemSize) t.sizeAlign :=
      sub_roundDown_eq_alignUp hA (dvd_roundDown (bytesLen - t.sizeBase) t.sizeAlign) hsum_mr
    congr 1
    unfold TrailingSliceLayout.sizeForElems
    show t.sizeBase + (maxRounded - roundDown (maxSlice % t.elemSize) t.sizeAlign) =
      t.sizeBase + alignUp (t.sizePhase + maxSlice / t.elemSize * t.elemSize) t.sizeAlign
    rw [hsub_eq]

/-- **R6d.** Start alignment of a successful cast. If the layout's alignment `align` divides the
size base and the size-rounding alignment of the trailing-slice layout (the completed-layout
condition under which every object size is a multiple of `align`), then whenever the modeled
validation returns `Ok((elems, split_at))`, the object starts at an address that is a multiple of
`align`: `addr` for a prefix cast and `addr + split_at` for a suffix cast. No positivity, phase, or
element-size hypothesis is needed (the validation's own endpoint check supplies the rest). -/
theorem vccm_sliceDst_start_aligned_of_align_dvd (align addr bytesLen : Nat) (ct : CastType)
    (t : TrailingSliceLayout) (hdB : align ∣ t.sizeBase) (hdA : align ∣ t.sizeAlign)
    (elems splitAt : Nat) (hok : vccm ⟨align, .sliceDst t⟩ addr bytesLen ct = .ok elems splitAt) :
    (addr + startOffset ct splitAt) % align = 0 := by
  unfold vccm DstLayout.zstElem at hok
  dsimp only at hok
  split at hok
  · cases hok
  · split at hok
    · cases hok
    · rename_i hnot_zst hnot_misal
      have hAl : (addr + castOffset ct bytesLen) % align = 0 := by
        revert hnot_misal
        simp [bne]
      cases hmtb : t.maxTrailingBytes bytesLen with
      | none =>
        rw [hmtb] at hok
        cases hok
      | some maxSlice =>
        rw [hmtb] at hok
        dsimp only at hok
        cases hok
        cases ct with
        | prefixCast =>
          simpa [startOffset, castOffset] using hAl
        | suffixCast =>
          simp only [castOffset] at hAl
          simp only [startOffset, splitFor]
          by_cases ha0 : align = 0
          · subst ha0
            simp only [Nat.mod_zero] at hAl ⊢
            omega
          · have hmin : ¬ bytesLen < t.sizeBase + (if t.sizePhase = 0 then 0 else t.sizeAlign) := by
              unfold TrailingSliceLayout.maxTrailingBytes at hmtb
              dsimp only at hmtb
              intro hlt
              simp [hlt] at hmtb
            have hB_le : t.sizeBase ≤ bytesLen := by omega
            let unusedAligned : Nat := roundDown (maxSlice % t.elemSize) t.sizeAlign
            let maxRounded : Nat := roundDown (bytesLen - t.sizeBase) t.sizeAlign
            let selfBytes : Nat := t.sizeBase + (maxRounded - unusedAligned)
            have hmr_le : maxRounded ≤ bytesLen - t.sizeBase :=
              roundDown_le (bytesLen - t.sizeBase) t.sizeAlign
            have hself_le : selfBytes ≤ bytesLen := by
              show t.sizeBase + (maxRounded - unusedAligned) ≤ bytesLen
              omega
            have hdvd_mr : align ∣ maxRounded :=
              Nat.dvd_trans hdA (dvd_roundDown (bytesLen - t.sizeBase) t.sizeAlign)
            have hdvd_ua : align ∣ unusedAligned :=
              Nat.dvd_trans hdA (dvd_roundDown (maxSlice % t.elemSize) t.sizeAlign)
            have hdvd_self : align ∣ selfBytes :=
              Nat.dvd_add hdB (dvd_sub_of_dvd hdvd_mr hdvd_ua)
            have hdvd_end : align ∣ addr + bytesLen := Nat.dvd_of_mod_eq_zero hAl
            have hsum : (addr + (bytesLen - selfBytes)) + selfBytes = addr + bytesLen := by omega
            have hdvd_start : align ∣ addr + (bytesLen - selfBytes) := by
              rw [← hsum] at hdvd_end
              exact (Nat.dvd_add_iff_left hdvd_self).mpr hdvd_end
            exact Nat.mod_eq_zero_of_dvd hdvd_start

/-- **R6b.** The normalized trailing-slice layout of a flat `repr(C)` slice DST has object size
`dstSize d n` for every element count `n`. -/
theorem normalizeDst_sizeForElems_eq_dstSize (d : SliceDstSpec) (n : Nat) :
    (normalizeDst d).sizeForElems n = dstSize d n := by
  have hA := dstAlign_pos d
  unfold TrailingSliceLayout.sizeForElems dstSize normalizeDst
  simp only
  have hdm := Nat.div_add_mod (dstTailOffset d) (dstAlign d)
  have hb : dstTailOffset d - dstTailOffset d % dstAlign d = (dstTailOffset d / dstAlign d) * dstAlign d := by
    rw [Nat.mul_comm]; omega
  have h2 : dstTailOffset d + n * d.elem.size =
      (dstTailOffset d % dstAlign d + n * d.elem.size) + (dstTailOffset d / dstAlign d) * dstAlign d := by
    rw [← hb]; have := Nat.mod_le (dstTailOffset d) (dstAlign d); omega
  rw [h2, alignUp_add_mul _ _ _ hA, hb]
  omega

/-- **R6c.** For a flat `repr(C)` slice DST, if the alignment check passes, the element count
returned by the modeled validation on `normalizeDst d` (prefix or suffix cast) equals
`maxSliceElems d bytesLen` (the largest fitting count, or `none` if none fits). For a zero-sized
element both sides are `none` (the validation panics; `maxSliceElems` returns `none`), so no
element-size hypothesis is needed. The layout alignment `align` is arbitrary; only the element
count is compared. -/
theorem vccm_normalizeDst_elems_eq_maxSliceElems_of_aligned (d : SliceDstSpec)
    (align addr bytesLen : Nat) (ct : CastType)
    (hAl : (addr + castOffset ct bytesLen) % align = 0) :
    (vccm ⟨align, .sliceDst (normalizeDst d)⟩ addr bytesLen ct).elems? = maxSliceElems d bytesLen := by
  have hA := dstAlign_pos d
  have hA0 : dstAlign d ≠ 0 := Nat.ne_of_gt hA
  have hAl0 : ((addr + castOffset ct bytesLen) % align != 0) = false := by simp [bne, hAl]
  unfold vccm DstLayout.zstElem maxSliceElems
  simp only [normalizeDst]
  by_cases hs : d.elem.size = 0
  · simp [hs, VccmResult.elems?]
  · have hs' : (d.elem.size == 0) = false := beq_false_of_ne hs
    simp only [hs', hs, Bool.false_eq_true, ↓reduceIte, hAl0]
    -- abbreviations
    generalize hT : dstTailOffset d = T
    generalize hAA : dstAlign d = A at hA hA0
    have hlt := Nat.mod_lt T hA
    have hle := Nat.mod_le T A
    have hM := alignUp_eq_sub_mod_add T A hA
    unfold TrailingSliceLayout.maxTrailingBytes
    simp only
    by_cases hL : bytesLen < T - T % A + (if T % A = 0 then 0 else A)
    · have hcap : roundDown bytesLen A < T := by
        rcases Nat.lt_or_ge (roundDown bytesLen A) T with h | h
        · exact h
        · exfalso
          have := (alignUp_le_iff_le_roundDown hA).mpr h
          omega
      simp [hL, hcap, VccmResult.elems?]
    · have hcap : ¬ roundDown bytesLen A < T := by
        intro h
        apply Nat.lt_irrefl (roundDown bytesLen A)
        have h1 : alignUp T A ≤ bytesLen := by omega
        have := (alignUp_le_iff_le_roundDown hA).mp h1
        omega
      simp only [hL, hcap, ↓reduceIte, VccmResult.elems?, Option.some.injEq]
      congr 1
      -- maxSlice = cap - T
      have hMdvd : A ∣ alignUp T A := dvd_alignUp hA
      obtain ⟨c, hc⟩ := hMdvd
      have hML : alignUp T A ≤ bytesLen := by omega
      have hsplit : bytesLen = (bytesLen - alignUp T A) + c * A := by rw [Nat.mul_comm] at hc; omega
      have hrd : roundDown bytesLen A = roundDown (bytesLen - alignUp T A) A + c * A := by
        conv => lhs; rw [hsplit]
        exact roundDown_add_mul_self _ _ _ hA
      have hTM : T ≤ alignUp T A := le_alignUp T A
      rw [Nat.mul_comm] at hc
      rw [← hM]
      have hrp : (if T % A = 0 then 0 else A) - T % A = alignUp T A - T := by
        rw [hM]; split <;> omega
      rw [hrp]
      omega

/-! ## Non-vacuity -/

theorem nv_vccm_sliceDst :
    0 < exampleTsl.sizeAlign ∧ exampleTsl.sizePhase ≤ exampleTsl.sizeAlign ∧
    0 < exampleTsl.elemSize ∧ (0 + castOffset .prefixCast 14) % 4 = 0 ∧
    vccm ⟨4, .sliceDst exampleTsl⟩ 0 14 .prefixCast = .ok 5 12 := by
  decide

/-- Non-vacuity of R6d: the running example with layout alignment `dstAlign exampleDst = 2`, a
suffix cast of 9 bytes at address 1 (so `addr + bytes_len = 10` is aligned): both divisibility
hypotheses hold and the validation succeeds with `split_at = 1` (object start `2`). -/
theorem nv_vccm_start_aligned :
    2 ∣ (normalizeDst exampleDst).sizeBase ∧ 2 ∣ (normalizeDst exampleDst).sizeAlign ∧
    vccm ⟨2, .sliceDst (normalizeDst exampleDst)⟩ 1 9 .suffixCast = .ok 5 1 ∧
    (1 + startOffset .suffixCast 1) % 2 = 0 := by
  decide

theorem nv_normalizeDst : (normalizeDst exampleDst).sizeForElems 3 = dstSize exampleDst 3 := by
  decide

/-- **Tightness of `hAl` in R6c.** A misaligned address gives no element count, although
`maxSliceElems` finds one. -/
theorem ce_vccm_normalizeDst_drop_aligned :
    ¬ ((1 + castOffset .prefixCast 9) % 2 = 0) ∧
    (vccm ⟨2, .sliceDst (normalizeDst exampleDst)⟩ 1 9 .prefixCast).elems? ≠
      maxSliceElems exampleDst 9 := by
  decide

theorem nv_vccm_normalizeDst :
    (0 + castOffset .prefixCast 9) % 2 = 0 ∧
    (vccm ⟨2, .sliceDst (normalizeDst exampleDst)⟩ 0 9 .prefixCast).elems? = some 5 ∧
    maxSliceElems exampleDst 9 = some 5 := by
  decide

/-! ## Counterexamples (canonical form: the other hypotheses hold, the conclusion fails) -/

/-- **Tightness of `hP` in R6a.** A phase above the alignment (not produced by zerocopy's
`RoundingAlignAndPhase`, whose constructor asserts `phase < align`, `layout.rs:72-96`): the model
returns `Ok` although no element count fits. -/
theorem ce_vccm_drop_phase_lt :
    let t : TrailingSliceLayout := ⟨0, 1, 0, 1, 2⟩
    0 < t.sizeAlign ∧ ¬ (t.sizePhase ≤ t.sizeAlign) ∧ 0 < t.elemSize ∧
    (0 + castOffset .prefixCast 1) % 1 = 0 ∧
    vccm ⟨1, .sliceDst t⟩ 0 1 .prefixCast = .ok 0 1 ∧ ¬ t.IsMaxFit 1 0 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, fun h => absurd h.1 (by decide)⟩

/-- **Tightness of `hA` in R6a.** A zero rounding alignment (excluded by `NonZeroUsize`), with the
phase `0 ≤ 0`: the model returns `Ok` with count `0`, which is not the largest fitting count
(`5` elements fit). -/
theorem ce_vccm_drop_align_pos :
    let t : TrailingSliceLayout := ⟨0, 1, 0, 0, 0⟩
    ¬ (0 < t.sizeAlign) ∧ t.sizePhase ≤ t.sizeAlign ∧ 0 < t.elemSize ∧
    (0 + castOffset .prefixCast 5) % 1 = 0 ∧
    vccm ⟨1, .sliceDst t⟩ 0 5 .prefixCast = .ok 0 0 ∧ t.sizeForElems 5 ≤ 5 ∧
    ¬ t.IsMaxFit 5 0 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    fun h => absurd (h.2 5 (by decide)) (by decide)⟩

/-- **Tightness of `hE` in R6a.** A zero-sized trailing element: the validation panics. -/
theorem ce_vccm_drop_elem_pos :
    let t : TrailingSliceLayout := ⟨0, 0, 0, 1, 0⟩
    0 < t.sizeAlign ∧ t.sizePhase ≤ t.sizeAlign ∧ ¬ (0 < t.elemSize) ∧
    (0 + castOffset .prefixCast 5) % 1 = 0 ∧
    vccm ⟨1, .sliceDst t⟩ 0 5 .prefixCast = .panic := by
  decide

/-- **Tightness of `hAl` in R6a.** A misaligned prefix address yields the alignment error,
although element counts fit. -/
theorem ce_vccm_drop_aligned :
    0 < exampleTsl.sizeAlign ∧ exampleTsl.sizePhase ≤ exampleTsl.sizeAlign ∧
    0 < exampleTsl.elemSize ∧ ¬ ((1 + castOffset .prefixCast 14) % 4 = 0) ∧
    vccm ⟨4, .sliceDst exampleTsl⟩ 1 14 .prefixCast = .alignmentErr ∧
    exampleTsl.sizeForElems 0 ≤ 14 := by
  decide

/-- **Tightness of `hdB` in R6d.** Layout alignment 2, size base 1 (odd), size-rounding alignment 2:
a suffix cast of 4 bytes at address 0 passes the endpoint check and succeeds with `split_at = 1`,
so the object starts at the odd address 1. -/
theorem ce_vccm_start_drop_dvd_base :
    let t : TrailingSliceLayout := ⟨0, 1, 1, 2, 0⟩
    ¬ (2 ∣ t.sizeBase) ∧ 2 ∣ t.sizeAlign ∧
    vccm ⟨2, .sliceDst t⟩ 0 4 .suffixCast = .ok 2 1 ∧
    ¬ ((0 + startOffset .suffixCast 1) % 2 = 0) := by
  decide

/-- **Tightness of `hdA` in R6d.** Layout alignment 2, size base 0, size-rounding alignment 1: a
suffix cast of 3 bytes at address 1 passes the endpoint check (`1 + 3 = 4`) and succeeds with
`split_at = 0`, so the object starts at the odd address 1. -/
theorem ce_vccm_start_drop_dvd_align :
    let t : TrailingSliceLayout := ⟨0, 1, 0, 1, 0⟩
    2 ∣ t.sizeBase ∧ ¬ (2 ∣ t.sizeAlign) ∧
    vccm ⟨2, .sliceDst t⟩ 1 3 .suffixCast = .ok 3 0 ∧
    ¬ ((1 + startOffset .suffixCast 0) % 2 = 0) := by
  decide

/-- **Tightness of `hok` in R6d.** Without the success premise the conclusion is about an arbitrary
`split_at`: with the divisibility hypotheses holding, the validation's actual result differs from
`Ok((0, 1))`, and `1 + 1` is not a multiple of 4. -/
theorem ce_vccm_start_drop_ok :
    4 ∣ exampleTsl.sizeBase ∧ 4 ∣ exampleTsl.sizeAlign ∧
    vccm ⟨4, .sliceDst exampleTsl⟩ 1 15 .suffixCast ≠ .ok 0 1 ∧
    ¬ ((1 + startOffset .suffixCast 1) % 4 = 0) := by
  decide

/-- **Zero-sized elements in R6c.** The validation panics and `maxSliceElems` returns
`none`, so R6c holds, but no largest fitting count exists (every count fits). -/
theorem vccm_normalizeDst_zst_both_none :
    let d : SliceDstSpec := ⟨.none, [⟨4, 4⟩], ⟨0, 1⟩⟩
    vccm ⟨4, .sliceDst (normalizeDst d)⟩ 0 8 .prefixCast = .panic ∧ maxSliceElems d 8 = none ∧
    (∀ n, dstSize d n ≤ 8) := by
  refine ⟨by decide, by decide, fun n => ?_⟩
  simp [dstSize, dstTailOffset, dstAlign, placeFields, structAlign, fieldsMaxAlign,
    effFieldAlign, alignUp, paddingNeeded]

end Toy.Zc
