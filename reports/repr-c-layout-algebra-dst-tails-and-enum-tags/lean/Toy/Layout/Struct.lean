import Toy.Layout.Core

namespace Toy.Layout

/-!
# `#[repr(C)]` Struct Layout, Characterization, Modifiers, and Padding

This module formalizes the `#[repr(C)]` struct layout algorithm with `packed(N)` and
`align(N)` modifiers (Rust Reference `r[layout.repr.c.struct]` and
`r[layout.repr.alignment]`), together with:

1. Separate named structural invariants (`OffsetsLengthMatch`, `OffsetsAligned`,
   `OffsetsMonotone`, `FieldsDisjoint`, `OrderedNonOverlapping`, `FieldsInBounds`,
   `SizeMinimalAligned`), their exact derivation relationship, and mutual independence
   of the five core invariants via concrete variant algorithms;
2. A declarative characterization (`OffsetsGreedyMinimal`, `EndOffsetExact`,
   `AlignIsMaxEffective`, `SizeMinimalAligned`) uniquely determining `reprCStruct`;
3. Modifier laws (`packed(1)`, general `packed(N)` alignment upper bound, `packed(N)`
   no-op, `align(N)` offset invariance and rounding composition);
4. Shallow padding characterization (`AllBytesOccupied ↔ size = totalFieldSize`),
   homogeneous padding characterization (`∀ k, AllBytesOccupied ↔ SizeMultipleOfAlign`
   under `AlignPos`), and heterogeneous counterexamples.
-/

/-- Computed layout of a struct: byte offsets in declaration order, unpadded end
    cursor after the final field, total padded byte `size`, and overall `align`.
    Captures `MockLayout` in the Rust Reference (`r[layout.repr.c.struct.size-field-offset]`)
    and the arbitrary-fields `LayoutData` output of `rustc_abi::LayoutCalculator`. -/
structure StructLayout where
  offsets : List Nat
  endOffset : Nat
  size : Nat
  align : Nat
  deriving Repr, DecidableEq, BEq

/-- Sequentially places `fields` in declaration order starting at byte offset `cursor`,
    aligning each field to `effFieldAlign m f.align` and advancing by `f.size`.
    Returns `(offsets, endOffset)`. -/
def placeFields (m : ReprModifier) (cursor : Nat) : List FieldLayout → List Nat × Nat
  | [] => ([], cursor)
  | f :: fs =>
    let off := alignUp cursor (effFieldAlign m f.align)
    let (restOffs, endOff) := placeFields m (off + f.size) fs
    (off :: restOffs, endOff)

/-- Maximum effective alignment across `fields`, with base `1` for empty structs
    (`r[layout.repr.c.struct.align]`). -/
def fieldsMaxAlign (m : ReprModifier) (fields : List FieldLayout) : Nat :=
  fields.foldl (fun acc f => max acc (effFieldAlign m f.align)) 1

/-- Overall alignment of a `#[repr(C)]` struct with modifier `m`:
    `max (fieldsMaxAlign m fields) n` for `aligned n`, and `fieldsMaxAlign m fields`
    otherwise (`r[layout.repr.alignment.align]`, `r[layout.repr.alignment.packed]`). -/
def structAlign (m : ReprModifier) (fields : List FieldLayout) : Nat :=
  match m with
  | .aligned n => max (fieldsMaxAlign m fields) n
  | .none | .packed _ => fieldsMaxAlign m fields

/-- Compute the `#[repr(C)]` struct layout for `fields` under modifier `m`.
    Matches Rust Reference `r[layout.repr.c.struct]` and `r[layout.repr.alignment]`
    on targets with `aggregate_align = 1` (e.g. `x86_64-unknown-linux-gnu`), abstracting
    away finite `isize::MAX` size-overflow checks. -/
def reprCStruct (m : ReprModifier) (fields : List FieldLayout) : StructLayout :=
  let (offs, endOff) := placeFields m 0 fields
  let a := structAlign m fields
  { offsets := offs
    endOffset := endOff
    size := alignUp endOff a
    align := a }

theorem ex_reprCStruct_pos_three_ints :
    reprCStruct .none [⟨2, 2⟩, ⟨1, 1⟩, ⟨4, 4⟩] =
      { offsets := [0, 2, 4], endOffset := 8, size := 8, align := 4 } := rfl

theorem ex_reprCStruct_neg_no_padding_assumed :
    (reprCStruct .none [⟨1, 1⟩, ⟨4, 4⟩]).size ≠ 5 := by decide

/-- Sum of the declared byte sizes of all fields in `fields`. -/
def totalFieldSize : List FieldLayout → Nat
  | [] => 0
  | f :: fs => f.size + totalFieldSize fs

theorem ex_totalFieldSize_pos : totalFieldSize [⟨1, 1⟩, ⟨2, 2⟩, ⟨4, 4⟩] = 7 := rfl
theorem ex_totalFieldSize_neg : totalFieldSize [⟨1, 1⟩, ⟨2, 2⟩] ≠ 4 := by decide

/-! ## Separate Named Struct Layout Properties -/

/-- The layout reports exactly one offset per declared field. -/
def OffsetsLengthMatch (fields : List FieldLayout) (L : StructLayout) : Prop :=
  L.offsets.length = fields.length

theorem ex_offsetsLengthMatch_pos :
    OffsetsLengthMatch [⟨1, 1⟩, ⟨4, 4⟩] (reprCStruct .none [⟨1, 1⟩, ⟨4, 4⟩]) := rfl

theorem ex_offsetsLengthMatch_neg :
    ¬ OffsetsLengthMatch [⟨1, 1⟩, ⟨4, 4⟩]
        { offsets := [0], endOffset := 1, size := 1, align := 1 } := by
  simp [OffsetsLengthMatch]

/-- Every field's offset is a multiple of its effective alignment under `m`
    (`r[layout.repr.rust.layout]` item 1, adjusted by `r[layout.repr.alignment.packed-fields]`). -/
def OffsetsAligned (m : ReprModifier) (fields : List FieldLayout) (L : StructLayout) : Prop :=
  ∀ (i : Nat) (hf : i < fields.length) (ho : i < L.offsets.length),
    effFieldAlign m fields[i].align ∣ L.offsets[i]

theorem ex_offsetsAligned_pos :
    OffsetsAligned .none [⟨1, 1⟩, ⟨4, 4⟩] (reprCStruct .none [⟨1, 1⟩, ⟨4, 4⟩]) := by
  intro i hf ho
  match i with
  | 0 => exact ⟨0, rfl⟩
  | 1 => exact ⟨1, rfl⟩
  | _ + 2 => simp at hf; omega

theorem ex_offsetsAligned_neg :
    ¬ OffsetsAligned .none [⟨1, 1⟩, ⟨4, 4⟩]
        { offsets := [0, 1], endOffset := 5, size := 8, align := 4 } := by
  intro h
  have h1 := h 1 (by decide) (by decide)
  rcases h1 with ⟨q, hq⟩
  simp [effFieldAlign] at hq
  omega

/-- Field offsets are non-decreasing in declaration order (`#[repr(C)]` ordering guarantee,
    not guaranteed by `#[repr(Rust)]`). -/
def OffsetsMonotone (L : StructLayout) : Prop :=
  ∀ (i j : Nat) (hi : i < L.offsets.length) (hj : j < L.offsets.length),
    i ≤ j → L.offsets[i] ≤ L.offsets[j]

theorem ex_offsetsMonotone_pos :
    OffsetsMonotone { offsets := [0, 4], endOffset := 8, size := 8, align := 4 } := by
  intro i j hi hj hij
  match i, j with
  | 0, 0 => simp
  | 0, 1 => simp
  | 1, 1 => simp
  | 1, 0 => omega
  | _ + 2, _ => simp at hi; omega
  | _, _ + 2 => simp at hj; omega

theorem ex_offsetsMonotone_neg :
    ¬ OffsetsMonotone { offsets := [4, 0], endOffset := 5, size := 8, align := 4 } := by
  intro h
  have h01 := h 0 1 (by decide) (by decide) (by omega)
  simp at h01

/-- Distinct fields occupy non-overlapping byte intervals (order-independent, matching
    `r[layout.repr.rust.struct]`; zero-sized fields may share an offset with another field). -/
def FieldsDisjoint (fields : List FieldLayout) (L : StructLayout) : Prop :=
  ∀ (i j : Nat) (hi : i < fields.length) (hj : j < fields.length)
    (hoi : i < L.offsets.length) (hoj : j < L.offsets.length),
    i ≠ j →
      L.offsets[i] + fields[i].size ≤ L.offsets[j] ∨
      L.offsets[j] + fields[j].size ≤ L.offsets[i]

theorem ex_fieldsDisjoint_pos :
    FieldsDisjoint [⟨1, 1⟩, ⟨4, 4⟩]
      { offsets := [4, 0], endOffset := 5, size := 8, align := 4 } := by
  intro i j hi hj hoi hoj hne
  match i, j with
  | 0, 0 => exact absurd rfl hne
  | 1, 1 => exact absurd rfl hne
  | 0, 1 => right; simp
  | 1, 0 => left; simp
  | _ + 2, _ => simp at hi; omega
  | _, _ + 2 => simp at hj; omega

theorem ex_fieldsDisjoint_neg :
    ¬ FieldsDisjoint [⟨1, 1⟩, ⟨4, 4⟩]
        { offsets := [0, 0], endOffset := 4, size := 4, align := 4 } := by
  intro h
  have h01 := h 0 1 (by decide) (by decide) (by decide) (by decide) (by decide)
  simp at h01

/-- Earlier fields finish at or before later fields begin in declaration order.
    Together with `OffsetsLengthMatch`, this implies both `OffsetsMonotone` and
    `FieldsDisjoint` (proved in `orderedNonOverlapping_implies_monotone_and_disjoint`),
    and is strictly stronger when zero-sized fields follow non-zero-sized fields. -/
def OrderedNonOverlapping (fields : List FieldLayout) (L : StructLayout) : Prop :=
  ∀ (i j : Nat) (hi : i < fields.length) (hj : j < fields.length)
    (hoi : i < L.offsets.length) (hoj : j < L.offsets.length),
    i < j → L.offsets[i] + fields[i].size ≤ L.offsets[j]

theorem ex_orderedNonOverlapping_pos :
    OrderedNonOverlapping [⟨4, 4⟩, ⟨0, 1⟩] (reprCStruct .none [⟨4, 4⟩, ⟨0, 1⟩]) := by
  intro i j hi hj hoi hoj hlt
  match i, j with
  | 0, 1 => simp [reprCStruct, placeFields, effFieldAlign, alignUp, paddingNeeded]
  | 0, 0 | 1, 0 | 1, 1 => omega
  | _ + 2, _ => simp at hi; omega
  | _, _ + 2 => simp at hj; omega

theorem ex_orderedNonOverlapping_neg :
    ¬ OrderedNonOverlapping [⟨4, 4⟩, ⟨0, 1⟩]
        { offsets := [0, 0], endOffset := 4, size := 4, align := 4 } := by
  intro h
  have h01 := h 0 1 (by decide) (by decide) (by decide) (by decide) (by decide)
  simp at h01

/-- Derivation lemma: for any `StructLayout`, `OffsetsLengthMatch` and
    `OrderedNonOverlapping` together entail both `OffsetsMonotone` and `FieldsDisjoint`. -/
theorem orderedNonOverlapping_implies_monotone_and_disjoint
    (fields : List FieldLayout) (L : StructLayout)
    (h_len : OffsetsLengthMatch fields L)
    (h_ord : OrderedNonOverlapping fields L) :
    OffsetsMonotone L ∧ FieldsDisjoint fields L := by
  unfold OffsetsLengthMatch at h_len
  constructor
  · intro i j hi hj hij
    rcases Nat.lt_or_eq_of_le hij with hlt | rfl
    · have := h_ord i j (by omega) (by omega) hi hj hlt
      omega
    · exact Nat.le_refl _
  · intro i j hi hj hoi hoj hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl (h_ord i j hi hj hoi hoj hlt)
    · exact Or.inr (h_ord j i hj hi hoj hoi hgt)

/-- Negative control showing `OffsetsLengthMatch` cannot be dropped from
    `orderedNonOverlapping_implies_monotone_and_disjoint`: with `fields = []` and
    `offsets = [1, 0]`, `OrderedNonOverlapping` holds vacuously while `OffsetsMonotone` fails. -/
theorem orderedNonOverlapping_without_length_not_monotone :
    OrderedNonOverlapping [] { offsets := [1, 0], endOffset := 0, size := 0, align := 1 } ∧
    ¬ OffsetsMonotone { offsets := [1, 0], endOffset := 0, size := 0, align := 1 } := by
  refine ⟨fun i _ hi => absurd hi (by simp), ?_⟩
  intro h
  have h01 := h 0 1 (by decide) (by decide) (by decide)
  simp at h01

/-- Every field lies completely inside `[0, L.endOffset]`. Together with `SizeMinimalAligned`
    (which carries `L.endOffset ≤ L.size`), every field lies inside `[0, L.size]`. -/
def FieldsInBounds (fields : List FieldLayout) (L : StructLayout) : Prop :=
  ∀ (i : Nat) (hf : i < fields.length) (ho : i < L.offsets.length),
    L.offsets[i] + fields[i].size ≤ L.endOffset

theorem ex_fieldsInBounds_pos :
    FieldsInBounds [⟨1, 1⟩, ⟨4, 4⟩] (reprCStruct .none [⟨1, 1⟩, ⟨4, 4⟩]) := by
  intro i hf ho
  match i with
  | 0 | 1 => simp [reprCStruct, placeFields, structAlign, fieldsMaxAlign, effFieldAlign, alignUp, paddingNeeded]
  | _ + 2 => simp at hf; omega

theorem ex_fieldsInBounds_neg :
    ¬ FieldsInBounds [⟨1, 1⟩, ⟨4, 4⟩]
        { offsets := [0, 4], endOffset := 4, size := 4, align := 4 } := by
  intro h
  have h1 := h 1 (by decide) (by decide)
  simp at h1

/-- The struct's total `size` is the least multiple of `L.align` that is `≥ L.endOffset`
    (`r[layout.repr.c.struct.size-field-offset]`). -/
def SizeMinimalAligned (L : StructLayout) : Prop :=
  IsLeastMultipleGe L.size L.endOffset L.align

theorem ex_sizeMinimalAligned_pos :
    SizeMinimalAligned (reprCStruct .none [⟨4, 4⟩, ⟨1, 1⟩]) := by
  refine ⟨by decide, ⟨2, rfl⟩, ?_⟩
  rintro m hle ⟨q, rfl⟩
  simp [reprCStruct, placeFields, structAlign, fieldsMaxAlign, effFieldAlign, alignUp, paddingNeeded] at hle ⊢
  omega

theorem ex_sizeMinimalAligned_neg :
    ¬ SizeMinimalAligned { offsets := [0, 4], endOffset := 5, size := 5, align := 4 } := by
  intro ⟨_, ⟨q, hq⟩, _⟩
  simp at hq
  omega

/-! ### Declarative Characterization Predicates for `reprCStruct` -/

/-- Minimum-padding greedy field placement (`r[layout.repr.c.struct.size-field-offset]`
    and `r[layout.repr.alignment.packed-padding]`): the first field is placed at the least
    multiple of its effective alignment `≥ 0`, and each subsequent field `i + 1` is placed
    at the least multiple of its effective alignment `≥ L.offsets[i] + fields[i].size`. -/
def OffsetsGreedyMinimal (m : ReprModifier) (fields : List FieldLayout) (L : StructLayout) : Prop :=
  (∀ (hf : 0 < fields.length) (ho : 0 < L.offsets.length),
    IsLeastMultipleGe L.offsets[0] 0 (effFieldAlign m fields[0].align)) ∧
  ∀ (i : Nat) (hf : i + 1 < fields.length) (ho : i + 1 < L.offsets.length),
    IsLeastMultipleGe L.offsets[i + 1]
      (L.offsets[i]'(Nat.lt_of_succ_lt ho) + fields[i].size)
      (effFieldAlign m fields[i + 1].align)

theorem ex_offsetsGreedyMinimal_pos :
    OffsetsGreedyMinimal .none [⟨1, 1⟩, ⟨4, 4⟩] (reprCStruct .none [⟨1, 1⟩, ⟨4, 4⟩]) := by
  refine ⟨?_, ?_⟩
  · intro _ _
    refine ⟨by simp [reprCStruct, placeFields, effFieldAlign, alignUp, paddingNeeded],
      ⟨0, rfl⟩, fun _ _ _ => Nat.zero_le _⟩
  · intro i hf ho
    match i with
    | 0 =>
      refine ⟨by simp [reprCStruct, placeFields, effFieldAlign, alignUp, paddingNeeded],
        ⟨1, rfl⟩, ?_⟩
      rintro k hle ⟨q, rfl⟩
      simp [reprCStruct, placeFields, effFieldAlign, alignUp, paddingNeeded] at hle ⊢
      omega
    | _ + 1 => simp at hf; omega

theorem ex_offsetsGreedyMinimal_neg_extra_pad :
    ¬ OffsetsGreedyMinimal .none [⟨1, 1⟩, ⟨1, 1⟩]
        { offsets := [0, 2], endOffset := 3, size := 3, align := 1 } := by
  intro ⟨_, hstep⟩
  have h0 := hstep 0 (by decide) (by decide)
  have hmin := h0.2.2 1 (by decide) ⟨1, rfl⟩
  simp at hmin

/-- `L.endOffset` is the exact unpadded cursor after the last field (`0` if `fields = []`,
    and `lastOffset + lastField.size` otherwise). -/
def EndOffsetExact (fields : List FieldLayout) (L : StructLayout) : Prop :=
  match fields.getLast?, L.offsets.getLast? with
  | none, _ => L.endOffset = 0
  | some f, some o => L.endOffset = o + f.size
  | some _, none => False

theorem ex_endOffsetExact_pos :
    EndOffsetExact [⟨1, 1⟩, ⟨4, 4⟩] (reprCStruct .none [⟨1, 1⟩, ⟨4, 4⟩]) := rfl

theorem ex_endOffsetExact_neg :
    ¬ EndOffsetExact [⟨1, 1⟩]
        { offsets := [0], endOffset := 5, size := 5, align := 1 } := by
  simp [EndOffsetExact]

/-- `L.align` is the least natural number `≥ 1` that is at least every field's effective
    alignment and (when `m = .aligned n`) at least `n` (`r[layout.repr.c.struct.align]`,
    `r[layout.repr.alignment.align]`, `r[layout.repr.alignment.packed]`). -/
def AlignIsMaxEffective (m : ReprModifier) (fields : List FieldLayout) (L : StructLayout) : Prop :=
  1 ≤ L.align ∧
  (∀ f ∈ fields, effFieldAlign m f.align ≤ L.align) ∧
  (∀ n : Nat, m = .aligned n → n ≤ L.align) ∧
  ∀ k : Nat, 1 ≤ k →
    (∀ f ∈ fields, effFieldAlign m f.align ≤ k) →
    (∀ n : Nat, m = .aligned n → n ≤ k) →
    L.align ≤ k

theorem ex_alignIsMaxEffective_pos :
    AlignIsMaxEffective .none [⟨1, 1⟩, ⟨4, 4⟩] (reprCStruct .none [⟨1, 1⟩, ⟨4, 4⟩]) := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · intro f hf
    simp at hf
    rcases hf with rfl | rfl <;> decide
  · intro n hn; cases hn
  · intro k _ hfs _
    have h4 := hfs ⟨4, 4⟩ (by simp)
    simpa [reprCStruct, structAlign, fieldsMaxAlign, effFieldAlign] using h4

theorem ex_alignIsMaxEffective_neg_too_small :
    ¬ AlignIsMaxEffective .none [⟨4, 4⟩]
        { offsets := [0], endOffset := 4, size := 4, align := 1 } := by
  intro ⟨_, hfs, _, _⟩
  have h4 := hfs ⟨4, 4⟩ (by simp)
  simp [effFieldAlign] at h4

theorem ex_alignIsMaxEffective_neg_too_large :
    ¬ AlignIsMaxEffective .none [⟨4, 4⟩]
        { offsets := [0], endOffset := 4, size := 8, align := 8 } := by
  intro ⟨_, _, _, hmin⟩
  have hle := hmin 4 (by decide) (by intro f hf; simp at hf; subst hf; decide) (by intro n hn; cases hn)
  simp at hle

/-- Every byte index `b < L.size` is covered by at least one declared field's byte range
    `[offset_i, offset_i + size_i)`. Captures absence of shallow (leading, inter-field,
    and trailing) padding bytes; treats individual fields as opaque byte ranges. -/
def AllBytesOccupied (fields : List FieldLayout) (L : StructLayout) : Prop :=
  ∀ b : Nat, b < L.size →
    ∃ (i : Nat) (hf : i < fields.length) (ho : i < L.offsets.length),
      L.offsets[i] ≤ b ∧ b < L.offsets[i] + fields[i].size

theorem ex_allBytesOccupied_pos :
    AllBytesOccupied [⟨2, 2⟩, ⟨2, 2⟩] (reprCStruct .none [⟨2, 2⟩, ⟨2, 2⟩]) := by
  intro b hb
  change b < 4 at hb
  by_cases h : b < 2
  · refine ⟨0, by decide, by decide, ?_, ?_⟩ <;>
      simp [reprCStruct, placeFields, effFieldAlign, alignUp, paddingNeeded] <;> omega
  · refine ⟨1, by decide, by decide, ?_, ?_⟩ <;>
      simp [reprCStruct, placeFields, effFieldAlign, alignUp, paddingNeeded] <;> omega

theorem ex_allBytesOccupied_neg :
    ¬ AllBytesOccupied [⟨1, 1⟩, ⟨2, 2⟩] (reprCStruct .none [⟨1, 1⟩, ⟨2, 2⟩]) := by
  intro h
  rcases h 1 (by decide) with ⟨i, hf, ho, hlo, hhi⟩
  match i with
  | 0 => simp [reprCStruct, placeFields, effFieldAlign, alignUp, paddingNeeded] at hhi
  | 1 => simp [reprCStruct, placeFields, effFieldAlign, alignUp, paddingNeeded] at hlo
  | _ + 2 => simp at hf; omega

/-! ## Result 1: `#[repr(C)]` Struct Invariants, Characterization, and Independence -/

theorem foldl_max_ge_init_gen {α : Type} (g : α → Nat) (xs : List α) (init : Nat) :
    init ≤ xs.foldl (fun acc x => max acc (g x)) init := by
  induction xs generalizing init with
  | nil => exact Nat.le_refl init
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact Nat.le_trans (Nat.le_max_left init (g x)) (ih (max init (g x)))

theorem foldl_max_ge_mem_gen {α : Type} (g : α → Nat) (xs : List α) (init : Nat)
    {x : α} (hx : x ∈ xs) :
    g x ≤ xs.foldl (fun acc y => max acc (g y)) init := by
  induction xs generalizing init with
  | nil => cases hx
  | cons y ys ih =>
    simp only [List.foldl_cons]
    simp at hx
    rcases hx with rfl | hmem
    · exact Nat.le_trans (Nat.le_max_right init (g x)) (foldl_max_ge_init_gen g ys _)
    · exact ih (max init (g y)) hmem

theorem foldl_max_le_gen {α : Type} (g : α → Nat) (xs : List α) (init k : Nat)
    (hinit : init ≤ k) (hxs : ∀ x ∈ xs, g x ≤ k) :
    xs.foldl (fun acc x => max acc (g x)) init ≤ k := by
  induction xs generalizing init with
  | nil => exact hinit
  | cons x xs ih =>
    simp only [List.foldl_cons]
    have hx : g x ≤ k := hxs x (by simp)
    apply ih (max init (g x)) (by omega)
    intro y hy
    exact hxs y (by simp [hy])

theorem foldl_max_pow2_gen {α : Type} (g : α → Nat) (xs : List α) (init : Nat)
    (hinit : IsPowerOfTwo init) (hxs : ∀ x ∈ xs, IsPowerOfTwo (g x)) :
    IsPowerOfTwo (xs.foldl (fun acc x => max acc (g x)) init) := by
  induction xs generalizing init with
  | nil => exact hinit
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact ih (max init (g x))
      (isPowerOfTwo_max hinit (hxs x (by simp)))
      (fun y hy => hxs y (by simp [hy]))

theorem placeFields_cons (m : ReprModifier) (cursor : Nat) (f : FieldLayout) (fs : List FieldLayout) :
    placeFields m cursor (f :: fs) =
      (alignUp cursor (effFieldAlign m f.align) ::
        (placeFields m (alignUp cursor (effFieldAlign m f.align) + f.size) fs).1,
       (placeFields m (alignUp cursor (effFieldAlign m f.align) + f.size) fs).2) := by
  simp only [placeFields]

theorem reprCStruct_eq_parts (m : ReprModifier) (fields : List FieldLayout) :
    reprCStruct m fields =
      { offsets := (placeFields m 0 fields).1
        endOffset := (placeFields m 0 fields).2
        size := alignUp (placeFields m 0 fields).2 (structAlign m fields)
        align := structAlign m fields } := by
  unfold reprCStruct
  rcases placeFields m 0 fields with ⟨offs, endOff⟩
  rfl

theorem placeFields_length (m : ReprModifier) (c : Nat) (fs : List FieldLayout) :
    (placeFields m c fs).1.length = fs.length := by
  induction fs generalizing c with
  | nil => simp [placeFields]
  | cons f fs ih =>
    rw [placeFields_cons]
    simp [ih]

theorem cursor_le_placeFields_end (m : ReprModifier) (c : Nat) (fs : List FieldLayout) :
    c ≤ (placeFields m c fs).2 := by
  induction fs generalizing c with
  | nil => exact Nat.le_refl c
  | cons f fs ih =>
    rw [placeFields_cons]
    dsimp only
    have h1 := le_alignUp c (effFieldAlign m f.align)
    have h2 := ih (alignUp c (effFieldAlign m f.align) + f.size)
    omega

theorem cursor_le_placeFields_getElem (m : ReprModifier) (c : Nat) (fs : List FieldLayout)
    (i : Nat) (ho : i < (placeFields m c fs).1.length) :
    c ≤ (placeFields m c fs).1[i] := by
  induction fs generalizing c i with
  | nil => simp [placeFields] at ho
  | cons f fs ih =>
    revert ho
    rw [placeFields_cons]
    dsimp only
    intro ho
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero]
      exact le_alignUp c (effFieldAlign m f.align)
    | succ i =>
      simp only [List.getElem_cons_succ]
      have h1 := le_alignUp c (effFieldAlign m f.align)
      have h2 := ih (alignUp c (effFieldAlign m f.align) + f.size) i (by simp at ho; omega)
      omega

theorem placeFields_inBounds (m : ReprModifier) (c : Nat) (fs : List FieldLayout)
    (i : Nat) (hf : i < fs.length) (ho : i < (placeFields m c fs).1.length) :
    (placeFields m c fs).1[i] + fs[i].size ≤ (placeFields m c fs).2 := by
  induction fs generalizing c i with
  | nil => cases hf
  | cons f fs ih =>
    revert ho
    rw [placeFields_cons]
    dsimp only
    intro ho
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero]
      exact cursor_le_placeFields_end m (alignUp c (effFieldAlign m f.align) + f.size) fs
    | succ i =>
      simp only [List.getElem_cons_succ]
      exact ih (alignUp c (effFieldAlign m f.align) + f.size) i
        (by simp at hf; omega)
        (by simp at ho; omega)

theorem placeFields_orderedNonOverlapping (m : ReprModifier) (c : Nat) (fs : List FieldLayout)
    (i j : Nat) (hi : i < fs.length) (hj : j < fs.length)
    (hoi : i < (placeFields m c fs).1.length) (hoj : j < (placeFields m c fs).1.length)
    (hlt : i < j) :
    (placeFields m c fs).1[i] + fs[i].size ≤ (placeFields m c fs).1[j] := by
  induction fs generalizing c i j with
  | nil => cases hi
  | cons f fs ih =>
    revert hoi hoj
    rw [placeFields_cons]
    dsimp only
    intro hoi hoj
    cases i with
    | zero =>
      cases j with
      | zero => omega
      | succ j =>
        simp only [List.getElem_cons_zero, List.getElem_cons_succ]
        exact cursor_le_placeFields_getElem m
          (alignUp c (effFieldAlign m f.align) + f.size) fs j
          (by simp at hoj; omega)
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        simp only [List.getElem_cons_succ]
        exact ih (alignUp c (effFieldAlign m f.align) + f.size) i j
          (by simp at hi; omega)
          (by simp at hj; omega)
          (by simp at hoi; omega)
          (by simp at hoj; omega)
          (by omega)

theorem placeFields_aligned (m : ReprModifier) (c : Nat) (fs : List FieldLayout)
    (hfs : ∀ f ∈ fs, AlignPos f) (hm : ModifierPackPos m)
    (i : Nat) (hf : i < fs.length) (ho : i < (placeFields m c fs).1.length) :
    effFieldAlign m fs[i].align ∣ (placeFields m c fs).1[i] := by
  induction fs generalizing c i with
  | nil => cases hf
  | cons f fs ih =>
    revert ho
    rw [placeFields_cons]
    dsimp only
    intro ho
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero]
      exact dvd_alignUp (effFieldAlign_pos (hfs f (by simp)) hm)
    | succ i =>
      simp only [List.getElem_cons_succ]
      exact ih (alignUp c (effFieldAlign m f.align) + f.size)
        (fun g hg => hfs g (by simp [hg])) i
        (by simp at hf; omega)
        (by simp at ho; omega)

theorem placeFields_step (m : ReprModifier) (c : Nat) (fs : List FieldLayout)
    (i : Nat) (hf : i + 1 < fs.length) (ho : i + 1 < (placeFields m c fs).1.length) :
    (placeFields m c fs).1[i + 1] =
      alignUp ((placeFields m c fs).1[i]'(Nat.lt_of_succ_lt ho) + fs[i].size)
        (effFieldAlign m fs[i + 1].align) := by
  induction fs generalizing c i with
  | nil => simp at hf
  | cons f fs ih =>
    revert ho
    rw [placeFields_cons]
    dsimp only
    intro ho
    cases i with
    | zero =>
      cases fs with
      | nil => simp at hf
      | cons f2 fs2 =>
        simp [placeFields_cons]
    | succ i =>
      simp only [List.getElem_cons_succ]
      exact ih (alignUp c (effFieldAlign m f.align) + f.size) i
        (by simp at hf; omega)
        (by simp at ho; omega)

theorem placeFields_endOffsetExact (m : ReprModifier) (c : Nat) (fs : List FieldLayout) :
    match fs.getLast?, (placeFields m c fs).1.getLast? with
    | none, _ => (placeFields m c fs).2 = c
    | some f, some o => (placeFields m c fs).2 = o + f.size
    | some _, none => False := by
  induction fs generalizing c with
  | nil =>
    simp [placeFields]
  | cons f fs ih =>
    cases fs with
    | nil =>
      rw [placeFields_cons]
      simp [placeFields]
    | cons f2 fs2 =>
      rw [placeFields_cons]
      dsimp only
      let c1 := alignUp c (effFieldAlign m f.align) + f.size
      have hih := ih c1
      have hlen : 0 < (placeFields m c1 (f2 :: fs2)).1.length := by
        rw [placeFields_length]
        simp
      cases hlist : (placeFields m c1 (f2 :: fs2)).1 with
      | nil =>
        rw [hlist] at hlen
        simp at hlen
      | cons o2 rest2 =>
        have hlast_f : (f :: f2 :: fs2).getLast? = (f2 :: fs2).getLast? := rfl
        have hlast_o :
            (alignUp c (effFieldAlign m f.align) :: o2 :: rest2).getLast? =
              (o2 :: rest2).getLast? := rfl
        rw [hlast_f, hlast_o]
        rw [hlist] at hih
        exact hih

theorem placeFields_end_mono (m : ReprModifier) {c₁ c₂ : Nat} (fs : List FieldLayout)
    (hc : c₁ ≤ c₂) :
    (placeFields m c₁ fs).2 ≤ (placeFields m c₂ fs).2 := by
  induction fs generalizing c₁ c₂ with
  | nil => simpa [placeFields] using hc
  | cons f fs ih =>
    rw [placeFields_cons, placeFields_cons]
    dsimp only
    apply ih
    have hal := alignUp_mono (a := effFieldAlign m f.align) hc
    omega

theorem placeFields_shift_of_dvd (c d : Nat) (fs : List FieldLayout)
    (hdvd : ∀ f ∈ fs, f.align ∣ d) :
    placeFields .none (d + c) fs =
      ((placeFields .none c fs).1.map (· + d), d + (placeFields .none c fs).2) := by
  induction fs generalizing c with
  | nil =>
    simp [placeFields]
  | cons f fs ih =>
    rw [placeFields_cons, placeFields_cons]
    dsimp only [effFieldAlign]
    have hoff : alignUp (d + c) f.align = d + alignUp c f.align :=
      alignUp_add_of_dvd_left (hdvd f (by simp))
    rw [hoff, Nat.add_assoc d (alignUp c f.align) f.size,
      ih (alignUp c f.align + f.size) (fun g hg => hdvd g (by simp [hg]))]
    simp [Nat.add_comm d]

theorem structAlign_ge_one (m : ReprModifier) (fields : List FieldLayout) :
    1 ≤ structAlign m fields := by
  unfold structAlign fieldsMaxAlign
  have h1 := foldl_max_ge_init_gen (fun f => effFieldAlign m f.align) fields 1
  cases m with
  | none => exact h1
  | packed _ => exact h1
  | aligned n => exact Nat.le_trans h1 (Nat.le_max_left _ n)

theorem structAlign_ge_field (m : ReprModifier) (fields : List FieldLayout)
    {f : FieldLayout} (hf : f ∈ fields) :
    effFieldAlign m f.align ≤ structAlign m fields := by
  unfold structAlign fieldsMaxAlign
  have hmem := foldl_max_ge_mem_gen (fun g => effFieldAlign m g.align) fields 1 hf
  cases m with
  | none => exact hmem
  | packed _ => exact hmem
  | aligned n => exact Nat.le_trans hmem (Nat.le_max_left _ n)

theorem reprCStruct_alignIsMaxEffective (m : ReprModifier) (fields : List FieldLayout) :
    AlignIsMaxEffective m fields (reprCStruct m fields) := by
  rw [reprCStruct_eq_parts]
  refine ⟨structAlign_ge_one m fields, fun f hf => structAlign_ge_field m fields hf, ?_, ?_⟩
  · intro n hm
    subst hm
    simp [structAlign, Nat.le_max_right]
  · intro k hk1 hfk hnk
    unfold structAlign fieldsMaxAlign
    have hfold : fields.foldl (fun acc f => max acc (effFieldAlign m f.align)) 1 ≤ k :=
      foldl_max_le_gen (fun f => effFieldAlign m f.align) fields 1 k hk1 hfk
    cases m with
    | none => exact hfold
    | packed _ => exact hfold
    | aligned n =>
      have hn : n ≤ k := hnk n rfl
      dsimp only at hfold ⊢
      omega

theorem reprCStruct_sizeMinimalAligned (m : ReprModifier) (fields : List FieldLayout) :
    SizeMinimalAligned (reprCStruct m fields) := by
  rw [reprCStruct_eq_parts]
  unfold SizeMinimalAligned
  dsimp only
  have hpos : 0 < structAlign m fields :=
    Nat.lt_of_lt_of_le (by decide : 0 < 1) (structAlign_ge_one m fields)
  exact alignUp_isLeastMultipleGe hpos

private theorem list_eq_of_length_getElem {xs ys : List Nat}
    (hlen : xs.length = ys.length)
    (hget : ∀ (i : Nat) (hx : i < xs.length) (hy : i < ys.length), xs[i] = ys[i]) :
    xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      have h0 : x = y := hget 0 (by simp) (by simp)
      have hrest : xs = ys := ih (by simp at hlen; omega) (fun i hx hy =>
        hget (i + 1) (by simp; omega) (by simp; omega))
      rw [h0, hrest]

/-- Main Result 1a: `reprCStruct m fields` satisfies the five non-redundant structural
    soundness invariants under minimal alignment positivity hypotheses (`AlignPos` on fields
    and `ModifierPackPos m`). `OffsetsMonotone` and `FieldsDisjoint` follow immediately from
    `OffsetsLengthMatch` and `OrderedNonOverlapping` via
    `orderedNonOverlapping_implies_monotone_and_disjoint`.

    Note: these soundness invariants do not uniquely determine `reprCStruct` (layouts with
    extra inter-field padding or smaller `align` also satisfy them); see
    `reprCStruct_eq_iff_of_align_pos` for the exact characterization. -/
theorem reprCStruct_invariants_of_align_pos
    (m : ReprModifier) (fields : List FieldLayout)
    (h_fields : ∀ f ∈ fields, AlignPos f)
    (h_pack : ModifierPackPos m) :
    let L := reprCStruct m fields
    OffsetsLengthMatch fields L ∧
    OffsetsAligned m fields L ∧
    OrderedNonOverlapping fields L ∧
    FieldsInBounds fields L ∧
    SizeMinimalAligned L := by
  dsimp only
  have hparts := reprCStruct_eq_parts m fields
  refine ⟨?_, ?_, ?_, ?_, reprCStruct_sizeMinimalAligned m fields⟩
  · unfold OffsetsLengthMatch
    rw [hparts]
    exact placeFields_length m 0 fields
  · unfold OffsetsAligned
    rw [hparts]
    intro i hf ho
    exact placeFields_aligned m 0 fields h_fields h_pack i hf ho
  · unfold OrderedNonOverlapping
    rw [hparts]
    intro i j hi hj hoi hoj hlt
    exact placeFields_orderedNonOverlapping m 0 fields i j hi hj hoi hoj hlt
  · unfold FieldsInBounds
    rw [hparts]
    intro i hf ho
    exact placeFields_inBounds m 0 fields i hf ho

theorem nv_reprCStruct_invariants_of_align_pos :
    let m := ReprModifier.none
    let fields : List FieldLayout := [⟨1, 1⟩, ⟨4, 4⟩, ⟨2, 2⟩]
    (∀ f ∈ fields, AlignPos f) ∧ ModifierPackPos m := by
  refine ⟨?_, ex_modifierPackPos_pos_none⟩
  intro f hf
  simp [AlignPos] at hf ⊢
  rcases hf with rfl | rfl | rfl <;> decide

/-- Canonical counterexample dropping `h_fields` from `reprCStruct_invariants_of_align_pos`:
    `m = .none` satisfies `ModifierPackPos`, yet `[⟨1, 1⟩, ⟨1, 0⟩]` places the
    zero-aligned field at offset `1`, violating `OffsetsAligned` (`¬ (0 ∣ 1)`). -/
theorem ce_reprCStruct_invariants_drop_fields_align_pos :
    let m := ReprModifier.none
    let fields : List FieldLayout := [⟨1, 1⟩, ⟨1, 0⟩]
    let L := reprCStruct m fields
    ModifierPackPos m ∧
    ¬ (OffsetsLengthMatch fields L ∧
       OffsetsAligned m fields L ∧
       OrderedNonOverlapping fields L ∧
       FieldsInBounds fields L ∧
       SizeMinimalAligned L) := by
  refine ⟨ex_modifierPackPos_pos_none, ?_⟩
  intro ⟨_, h_al, _, _, _⟩
  have h1 := h_al 1 (by decide) (by decide)
  rcases h1 with ⟨q, hq⟩
  simp [reprCStruct, placeFields, effFieldAlign, alignUp, paddingNeeded] at hq

/-- Canonical counterexample dropping `h_pack` from `reprCStruct_invariants_of_align_pos`:
    all fields satisfy `AlignPos`, yet `m = .packed 0` reduces effective alignment to `0`
    and places the second field at offset `1`, violating `OffsetsAligned` (`¬ (0 ∣ 1)`). -/
theorem ce_reprCStruct_invariants_drop_pack_pos :
    let m := ReprModifier.packed 0
    let fields : List FieldLayout := [⟨1, 1⟩, ⟨1, 4⟩]
    let L := reprCStruct m fields
    (∀ f ∈ fields, AlignPos f) ∧
    ¬ (OffsetsLengthMatch fields L ∧
       OffsetsAligned m fields L ∧
       OrderedNonOverlapping fields L ∧
       FieldsInBounds fields L ∧
       SizeMinimalAligned L) := by
  refine ⟨?_, ?_⟩
  · intro f hf
    simp [AlignPos] at hf ⊢
    rcases hf with rfl | rfl <;> decide
  · intro ⟨_, h_al, _, _, _⟩
    have h1 := h_al 1 (by decide) (by decide)
    rcases h1 with ⟨q, hq⟩
    simp [reprCStruct, placeFields, effFieldAlign, alignUp, paddingNeeded] at hq

/-- Main Result 1b (exact characterization): Under positive field alignments and a positive
    packing bound (if packed), a `StructLayout` `L` equals `reprCStruct m fields` if and
    only if it satisfies the five declarative rules: matching offset count, greedy minimal
    aligned placement (`OffsetsGreedyMinimal`), exact unpadded end cursor (`EndOffsetExact`),
    maximum effective alignment (`AlignIsMaxEffective`), and minimal aligned size
    (`SizeMinimalAligned`). -/
theorem reprCStruct_eq_iff_of_align_pos
    (m : ReprModifier) (fields : List FieldLayout) (L : StructLayout)
    (h_fields : ∀ f ∈ fields, AlignPos f)
    (h_pack : ModifierPackPos m) :
    L = reprCStruct m fields ↔
      OffsetsLengthMatch fields L ∧
      OffsetsGreedyMinimal m fields L ∧
      EndOffsetExact fields L ∧
      AlignIsMaxEffective m fields L ∧
      SizeMinimalAligned L := by
  let R := reprCStruct m fields
  have hR_parts : R =
      { offsets := (placeFields m 0 fields).1
        endOffset := (placeFields m 0 fields).2
        size := alignUp (placeFields m 0 fields).2 (structAlign m fields)
        align := structAlign m fields } := reprCStruct_eq_parts m fields
  have hR_len : OffsetsLengthMatch fields R := by
    unfold OffsetsLengthMatch
    rw [hR_parts]
    exact placeFields_length m 0 fields
  have hR_greedy : OffsetsGreedyMinimal m fields R := by
    unfold OffsetsGreedyMinimal
    rw [hR_parts]
    dsimp only
    constructor
    · intro hf ho
      cases fields with
      | nil => simp at hf
      | cons f0 fs =>
        revert ho
        rw [placeFields_cons]
        dsimp only
        intro ho
        simp only [List.getElem_cons_zero]
        exact alignUp_isLeastMultipleGe (effFieldAlign_pos (h_fields f0 (by simp)) h_pack)
    · intro i hf ho
      rw [placeFields_step m 0 fields i hf ho]
      have hmem : fields[i + 1] ∈ fields := List.getElem_mem hf
      exact alignUp_isLeastMultipleGe (effFieldAlign_pos (h_fields _ hmem) h_pack)
  have hR_end : EndOffsetExact fields R := by
    unfold EndOffsetExact
    rw [hR_parts]
    dsimp only
    simpa using placeFields_endOffsetExact m 0 fields
  have hR_al : AlignIsMaxEffective m fields R := reprCStruct_alignIsMaxEffective m fields
  have hR_sz : SizeMinimalAligned R := reprCStruct_sizeMinimalAligned m fields
  constructor
  · rintro rfl
    exact ⟨hR_len, hR_greedy, hR_end, hR_al, hR_sz⟩
  · rintro ⟨hL_len, hL_greedy, hL_end, hL_al, hL_sz⟩
    have hoffs : L.offsets = R.offsets := by
      have hlen_eq : L.offsets.length = R.offsets.length := by
        unfold OffsetsLengthMatch at hL_len hR_len
        omega
      apply list_eq_of_length_getElem hlen_eq
      intro i hiL hiR
      have hif : i < fields.length := by
        unfold OffsetsLengthMatch at hL_len
        omega
      induction i with
      | zero =>
        exact isLeastMultipleGe_unique (hL_greedy.1 hif hiL) (hR_greedy.1 hif hiR)
      | succ i ih =>
        have hiL' : i < L.offsets.length := Nat.lt_of_succ_lt hiL
        have hiR' : i < R.offsets.length := Nat.lt_of_succ_lt hiR
        have hif' : i < fields.length := Nat.lt_of_succ_lt hif
        have hprev : L.offsets[i]'hiL' = R.offsets[i]'hiR' := ih hiL' hiR' hif'
        have hstepL := hL_greedy.2 i hif hiL
        rw [hprev] at hstepL
        exact isLeastMultipleGe_unique hstepL (hR_greedy.2 i hif hiR)
    have hend : L.endOffset = R.endOffset := by
      unfold EndOffsetExact at hL_end hR_end
      rw [hoffs] at hL_end
      cases hfl : fields.getLast? with
      | none =>
        rw [hfl] at hL_end hR_end
        dsimp only at hL_end hR_end
        omega
      | some f =>
        rw [hfl] at hL_end hR_end
        cases hrl : R.offsets.getLast? with
        | none =>
          rw [hrl] at hR_end
          cases hR_end
        | some o =>
          rw [hrl] at hL_end hR_end
          dsimp only at hL_end hR_end
          omega
    have hal : L.align = R.align := by
      have hLR : L.align ≤ R.align := hL_al.2.2.2 R.align hR_al.1 hR_al.2.1 hR_al.2.2.1
      have hRL : R.align ≤ L.align := hR_al.2.2.2 L.align hL_al.1 hL_al.2.1 hL_al.2.2.1
      omega
    have hsz : L.size = R.size := by
      unfold SizeMinimalAligned at hL_sz hR_sz
      rw [hend, hal] at hL_sz
      exact isLeastMultipleGe_unique hL_sz hR_sz
    cases L
    cases R
    dsimp only at hoffs hend hal hsz
    subst hoffs hend hal hsz
    rfl

theorem nv_reprCStruct_eq_iff_of_align_pos :
    let m := ReprModifier.none
    let fields : List FieldLayout := [⟨1, 1⟩, ⟨4, 4⟩]
    (∀ f ∈ fields, AlignPos f) ∧ ModifierPackPos m := by
  refine ⟨?_, ex_modifierPackPos_pos_none⟩
  intro f hf
  simp [AlignPos] at hf ⊢
  rcases hf with rfl | rfl <;> decide

/-- Canonical counterexample dropping `h_fields` from `reprCStruct_eq_iff_of_align_pos`:
    with `fields = [⟨1, 1⟩, ⟨1, 0⟩]` and `L = reprCStruct .none fields`, `L = reprCStruct .none fields`
    holds trivially while `OffsetsGreedyMinimal` fails (`IsLeastMultipleGe 1 1 0` requires `0 ∣ 1`). -/
theorem ce_reprCStruct_eq_iff_drop_fields_align_pos :
    let m := ReprModifier.none
    let fields : List FieldLayout := [⟨1, 1⟩, ⟨1, 0⟩]
    let L := reprCStruct m fields
    ModifierPackPos m ∧
    ¬ (L = reprCStruct m fields ↔
        OffsetsLengthMatch fields L ∧
        OffsetsGreedyMinimal m fields L ∧
        EndOffsetExact fields L ∧
        AlignIsMaxEffective m fields L ∧
        SizeMinimalAligned L) := by
  refine ⟨ex_modifierPackPos_pos_none, ?_⟩
  intro hiff
  have hrhs := hiff.mp rfl
  have hstep := hrhs.2.1.2 0 (by decide) (by decide)
  rcases hstep.2.1 with ⟨q, hq⟩
  simp [reprCStruct, placeFields, effFieldAlign, alignUp, paddingNeeded] at hq

/-- Canonical counterexample dropping `h_pack` from `reprCStruct_eq_iff_of_align_pos`:
    with `m = .packed 0`, `fields = [⟨1, 1⟩, ⟨1, 4⟩]`, and `L = reprCStruct m fields`,
    the left-hand side holds while `OffsetsGreedyMinimal` fails (`¬ (0 ∣ 1)`). -/
theorem ce_reprCStruct_eq_iff_drop_pack_pos :
    let m := ReprModifier.packed 0
    let fields : List FieldLayout := [⟨1, 1⟩, ⟨1, 4⟩]
    let L := reprCStruct m fields
    (∀ f ∈ fields, AlignPos f) ∧
    ¬ (L = reprCStruct m fields ↔
        OffsetsLengthMatch fields L ∧
        OffsetsGreedyMinimal m fields L ∧
        EndOffsetExact fields L ∧
        AlignIsMaxEffective m fields L ∧
        SizeMinimalAligned L) := by
  refine ⟨?_, ?_⟩
  · intro f hf
    simp [AlignPos] at hf ⊢
    rcases hf with rfl | rfl <;> decide
  · intro hiff
    have hrhs := hiff.mp rfl
    have hstep := hrhs.2.1.2 0 (by decide) (by decide)
    rcases hstep.2.1 with ⟨q, hq⟩
    simp [reprCStruct, placeFields, effFieldAlign, alignUp, paddingNeeded] at hq

/-- Main Result 1c: Power-of-two alignments make the struct alignment a power of two
    that is divisible by every field's effective (possibly `packed`-reduced) alignment
    (since `max = lcm` on powers of two). -/
theorem reprCStruct_align_pow2_divides
    (m : ReprModifier) (fields : List FieldLayout)
    (h_fields : ∀ f ∈ fields, AlignPow2 f)
    (h_mod : ModifierPow2 m) :
    let L := reprCStruct m fields
    IsPowerOfTwo L.align ∧ ∀ f ∈ fields, effFieldAlign m f.align ∣ L.align := by
  dsimp only
  have hparts := reprCStruct_eq_parts m fields
  have hpow_max : IsPowerOfTwo (fieldsMaxAlign m fields) := by
    unfold fieldsMaxAlign
    exact foldl_max_pow2_gen (fun (f : FieldLayout) => effFieldAlign m f.align) fields 1
      ex_isPowerOfTwo_pos_1
      (fun f hf => effFieldAlign_pow2 (h_fields f hf) h_mod)
  have hpow_align : IsPowerOfTwo (structAlign m fields) := by
    cases m with
    | none => exact hpow_max
    | packed _ => exact hpow_max
    | aligned n => exact isPowerOfTwo_max hpow_max h_mod
  rw [hparts]
  dsimp only
  refine ⟨hpow_align, ?_⟩
  intro f hf
  exact isPowerOfTwo_dvd_of_le
    (effFieldAlign_pow2 (h_fields f hf) h_mod)
    hpow_align
    (structAlign_ge_field m fields hf)

theorem nv_reprCStruct_align_pow2_divides :
    let m := ReprModifier.aligned 8
    let fields : List FieldLayout := [⟨1, 1⟩, ⟨4, 4⟩]
    (∀ f ∈ fields, AlignPow2 f) ∧ ModifierPow2 m := by
  refine ⟨?_, ex_modifierPow2_pos_aligned⟩
  intro f hf
  simp at hf
  rcases hf with rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨2, rfl⟩

/-- Canonical counterexample dropping `h_fields` from `reprCStruct_align_pow2_divides`:
    `m = .none` satisfies `ModifierPow2`, yet `[⟨2, 2⟩, ⟨3, 3⟩]` has `L.align = 3`,
    which is neither a power of two nor divisible by `2`. -/
theorem ce_reprCStruct_align_dvd_drop_fields_pow2 :
    let m := ReprModifier.none
    let fields : List FieldLayout := [⟨2, 2⟩, ⟨3, 3⟩]
    let L := reprCStruct m fields
    ModifierPow2 m ∧
    ¬ (IsPowerOfTwo L.align ∧ ∀ f ∈ fields, effFieldAlign m f.align ∣ L.align) := by
  refine ⟨trivial, ?_⟩
  intro ⟨hpow, _⟩
  exact ex_isPowerOfTwo_neg_3 hpow

/-- Canonical counterexample dropping `h_mod` from `reprCStruct_align_pow2_divides`:
    all fields satisfy `AlignPow2`, yet `m = .aligned 3` gives `L.align = 3`,
    violating both `IsPowerOfTwo L.align` and `2 ∣ L.align`. -/
theorem ce_reprCStruct_align_dvd_drop_mod_pow2 :
    let m := ReprModifier.aligned 3
    let fields : List FieldLayout := [⟨2, 2⟩]
    let L := reprCStruct m fields
    (∀ f ∈ fields, AlignPow2 f) ∧
    ¬ (IsPowerOfTwo L.align ∧ ∀ f ∈ fields, effFieldAlign m f.align ∣ L.align) := by
  refine ⟨?_, ?_⟩
  · intro f hf
    simp at hf
    rcases hf with rfl
    exact ⟨1, rfl⟩
  · intro ⟨hpow, _⟩
    exact ex_isPowerOfTwo_neg_3 hpow

/-! ### Five Variant Layout Algorithms Demonstrating Mutual Independence -/

/-- Variant 1: packs fields sequentially with no alignment padding while keeping
    natural `structAlign` and final alignment rounding. On `sampleStructAsc`, violates
    only `OffsetsAligned`. -/
def unalignedPackingLayout (fields : List FieldLayout) : StructLayout :=
  let (offs, endOff) := placeFields (.packed 1) 0 fields
  let a := structAlign .none fields
  { offsets := offs, endOffset := endOff, size := alignUp endOff a, align := a }

/-- Variant 2: lays out fields in reverse declaration order (modeling `#[repr(Rust)]`
    field reordering on ascending-alignment structs). On `sampleStructAsc`, violates
    only `OffsetsMonotone`. -/
def reversedOrderLayout (fields : List FieldLayout) : StructLayout :=
  let rev := reprCStruct .none fields.reverse
  { offsets := rev.offsets.reverse, endOffset := rev.endOffset, size := rev.size, align := rev.align }

/-- Variant 3: places every field at offset `0` (union-like placement) with `endOffset`
    equal to the maximum field size. On `sampleStructAsc`, violates only `FieldsDisjoint`. -/
def overlappingUnionLayout (fields : List FieldLayout) : StructLayout :=
  let maxSz := fields.foldl (fun acc f => max acc f.size) 0
  let a := structAlign .none fields
  { offsets := List.replicate fields.length 0, endOffset := maxSz, size := alignUp maxSz a, align := a }

/-- Variant 4: computes `#[repr(C)]` offsets correctly, but sets `endOffset` to the
    start of the last field (forgetting to add the last field's size). On `sampleStructAsc`,
    violates only `FieldsInBounds`. -/
def truncatedEndLayout (fields : List FieldLayout) : StructLayout :=
  let base := reprCStruct .none fields
  let truncEnd := base.offsets.getLastD 0
  { offsets := base.offsets, endOffset := truncEnd, size := alignUp truncEnd base.align, align := base.align }

/-- Variant 5: computes `#[repr(C)]` offsets and `endOffset` correctly, but omits
    final alignment rounding (`size := endOffset`). On `sampleStructDesc`, violates
    only `SizeMinimalAligned`. -/
def unroundedTailLayout (fields : List FieldLayout) : StructLayout :=
  let base := reprCStruct .none fields
  { offsets := base.offsets, endOffset := base.endOffset, size := base.endOffset, align := base.align }

/-- Concrete struct `[u8, u32]` used to test variants 1–4. -/
def sampleStructAsc : List FieldLayout := [⟨1, 1⟩, ⟨4, 4⟩]

/-- Concrete struct `[u32, u8]` used to test variant 5 (has trailing padding under `repr(C)`). -/
def sampleStructDesc : List FieldLayout := [⟨4, 4⟩, ⟨1, 1⟩]

private theorem unaligned_eval :
    unalignedPackingLayout sampleStructAsc =
      { offsets := [0, 1], endOffset := 5, size := 8, align := 4 } := rfl

private theorem reordered_eval :
    reversedOrderLayout sampleStructAsc =
      { offsets := [4, 0], endOffset := 5, size := 8, align := 4 } := rfl

private theorem overlapping_eval :
    overlappingUnionLayout sampleStructAsc =
      { offsets := [0, 0], endOffset := 4, size := 4, align := 4 } := rfl

private theorem truncated_eval :
    truncatedEndLayout sampleStructAsc =
      { offsets := [0, 4], endOffset := 4, size := 4, align := 4 } := rfl

private theorem unrounded_eval :
    unroundedTailLayout sampleStructDesc =
      { offsets := [0, 4], endOffset := 5, size := 5, align := 4 } := rfl

theorem variant_unaligned_violates_only_aligned :
    let L := unalignedPackingLayout sampleStructAsc
    OffsetsLengthMatch sampleStructAsc L ∧
    ¬ OffsetsAligned .none sampleStructAsc L ∧
    OffsetsMonotone L ∧
    FieldsDisjoint sampleStructAsc L ∧
    FieldsInBounds sampleStructAsc L ∧
    SizeMinimalAligned L := by
  dsimp only
  rw [unaligned_eval]
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have h1 := h 1 (by decide) (by decide)
    rcases h1 with ⟨q, hq⟩
    simp [sampleStructAsc, effFieldAlign] at hq
    omega
  · intro i j hi hj hij
    match i, j with
    | 0, 0 | 0, 1 | 1, 1 => simp
    | 1, 0 => omega
    | _ + 2, _ => simp at hi; omega
    | _, _ + 2 => simp at hj; omega
  · intro i j hi hj hoi hoj hne
    match i, j with
    | 0, 0 | 1, 1 => exact absurd rfl hne
    | 0, 1 => left; simp [sampleStructAsc]
    | 1, 0 => right; simp [sampleStructAsc]
    | _ + 2, _ => simp [sampleStructAsc] at hi; omega
    | _, _ + 2 => simp [sampleStructAsc] at hj; omega
  · intro i hf ho
    match i with
    | 0 | 1 => simp [sampleStructAsc]
    | _ + 2 => simp [sampleStructAsc] at hf; omega
  · refine ⟨by decide, ⟨2, rfl⟩, ?_⟩
    rintro m hle ⟨q, rfl⟩
    dsimp at hle ⊢
    omega

theorem variant_reordered_violates_only_monotone :
    let L := reversedOrderLayout sampleStructAsc
    OffsetsLengthMatch sampleStructAsc L ∧
    OffsetsAligned .none sampleStructAsc L ∧
    ¬ OffsetsMonotone L ∧
    FieldsDisjoint sampleStructAsc L ∧
    FieldsInBounds sampleStructAsc L ∧
    SizeMinimalAligned L := by
  dsimp only
  rw [reordered_eval]
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hf ho
    match i with
    | 0 => exact ⟨4, rfl⟩
    | 1 => exact ⟨0, rfl⟩
    | _ + 2 => simp [sampleStructAsc] at hf; omega
  · intro h
    have h01 := h 0 1 (by decide) (by decide) (by omega)
    simp at h01
  · intro i j hi hj hoi hoj hne
    match i, j with
    | 0, 0 | 1, 1 => exact absurd rfl hne
    | 0, 1 => right; simp [sampleStructAsc]
    | 1, 0 => left; simp [sampleStructAsc]
    | _ + 2, _ => simp [sampleStructAsc] at hi; omega
    | _, _ + 2 => simp [sampleStructAsc] at hj; omega
  · intro i hf ho
    match i with
    | 0 | 1 => simp [sampleStructAsc]
    | _ + 2 => simp [sampleStructAsc] at hf; omega
  · refine ⟨by decide, ⟨2, rfl⟩, ?_⟩
    rintro m hle ⟨q, rfl⟩
    dsimp at hle ⊢
    omega

theorem variant_overlapping_violates_only_disjoint :
    let L := overlappingUnionLayout sampleStructAsc
    OffsetsLengthMatch sampleStructAsc L ∧
    OffsetsAligned .none sampleStructAsc L ∧
    OffsetsMonotone L ∧
    ¬ FieldsDisjoint sampleStructAsc L ∧
    FieldsInBounds sampleStructAsc L ∧
    SizeMinimalAligned L := by
  dsimp only
  rw [overlapping_eval]
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hf ho
    match i with
    | 0 => exact ⟨0, rfl⟩
    | 1 => exact ⟨0, rfl⟩
    | _ + 2 => simp [sampleStructAsc] at hf; omega
  · intro i j hi hj hij
    match i, j with
    | 0, 0 | 0, 1 | 1, 1 => simp
    | 1, 0 => omega
    | _ + 2, _ => simp at hi; omega
    | _, _ + 2 => simp at hj; omega
  · intro h
    have h01 := h 0 1 (by decide) (by decide) (by decide) (by decide) (by decide)
    simp [sampleStructAsc] at h01
  · intro i hf ho
    match i with
    | 0 | 1 => simp [sampleStructAsc]
    | _ + 2 => simp [sampleStructAsc] at hf; omega
  · refine ⟨by decide, ⟨1, rfl⟩, ?_⟩
    rintro m hle ⟨q, rfl⟩
    dsimp at hle ⊢
    omega

theorem variant_truncated_end_violates_only_in_bounds :
    let L := truncatedEndLayout sampleStructAsc
    OffsetsLengthMatch sampleStructAsc L ∧
    OffsetsAligned .none sampleStructAsc L ∧
    OffsetsMonotone L ∧
    FieldsDisjoint sampleStructAsc L ∧
    ¬ FieldsInBounds sampleStructAsc L ∧
    SizeMinimalAligned L := by
  dsimp only
  rw [truncated_eval]
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hf ho
    match i with
    | 0 => exact ⟨0, rfl⟩
    | 1 => exact ⟨1, rfl⟩
    | _ + 2 => simp [sampleStructAsc] at hf; omega
  · intro i j hi hj hij
    match i, j with
    | 0, 0 | 0, 1 | 1, 1 => simp
    | 1, 0 => omega
    | _ + 2, _ => simp at hi; omega
    | _, _ + 2 => simp at hj; omega
  · intro i j hi hj hoi hoj hne
    match i, j with
    | 0, 0 | 1, 1 => exact absurd rfl hne
    | 0, 1 => left; simp [sampleStructAsc]
    | 1, 0 => right; simp [sampleStructAsc]
    | _ + 2, _ => simp [sampleStructAsc] at hi; omega
    | _, _ + 2 => simp [sampleStructAsc] at hj; omega
  · intro h
    have h1 := h 1 (by decide) (by decide)
    simp [sampleStructAsc] at h1
  · refine ⟨by decide, ⟨1, rfl⟩, ?_⟩
    rintro m hle ⟨q, rfl⟩
    dsimp at hle ⊢
    omega

theorem variant_unrounded_tail_violates_only_size_minimal :
    let L := unroundedTailLayout sampleStructDesc
    OffsetsLengthMatch sampleStructDesc L ∧
    OffsetsAligned .none sampleStructDesc L ∧
    OffsetsMonotone L ∧
    FieldsDisjoint sampleStructDesc L ∧
    FieldsInBounds sampleStructDesc L ∧
    ¬ SizeMinimalAligned L := by
  dsimp only
  rw [unrounded_eval]
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hf ho
    match i with
    | 0 => exact ⟨0, rfl⟩
    | 1 => exact ⟨4, rfl⟩
    | _ + 2 => simp [sampleStructDesc] at hf; omega
  · intro i j hi hj hij
    match i, j with
    | 0, 0 | 0, 1 | 1, 1 => simp
    | 1, 0 => omega
    | _ + 2, _ => simp at hi; omega
    | _, _ + 2 => simp at hj; omega
  · intro i j hi hj hoi hoj hne
    match i, j with
    | 0, 0 | 1, 1 => exact absurd rfl hne
    | 0, 1 => left; simp [sampleStructDesc]
    | 1, 0 => right; simp [sampleStructDesc]
    | _ + 2, _ => simp [sampleStructDesc] at hi; omega
    | _, _ + 2 => simp [sampleStructDesc] at hj; omega
  · intro i hf ho
    match i with
    | 0 | 1 => simp [sampleStructDesc]
    | _ + 2 => simp [sampleStructDesc] at hf; omega
  · intro ⟨_, ⟨q, hq⟩, _⟩
    dsimp at hq
    omega

/-- Main Result 1d (fully proved, definition-adequacy reference point): None of the five
    struct-layout invariants (`OffsetsAligned`, `OffsetsMonotone`, `FieldsDisjoint`,
    `FieldsInBounds`, `SizeMinimalAligned`) is implied by the conjunction of the other four
    together with `OffsetsLengthMatch` — witnessed on the concrete sample structs
    `sampleStructAsc = [u8, u32]` and `sampleStructDesc = [u32, u8]`. -/
theorem struct_invariants_mutually_independent :
    (let L := unalignedPackingLayout sampleStructAsc
     OffsetsLengthMatch sampleStructAsc L ∧ ¬ OffsetsAligned .none sampleStructAsc L ∧
     OffsetsMonotone L ∧ FieldsDisjoint sampleStructAsc L ∧
     FieldsInBounds sampleStructAsc L ∧ SizeMinimalAligned L) ∧
    (let L := reversedOrderLayout sampleStructAsc
     OffsetsLengthMatch sampleStructAsc L ∧ OffsetsAligned .none sampleStructAsc L ∧
     ¬ OffsetsMonotone L ∧ FieldsDisjoint sampleStructAsc L ∧
     FieldsInBounds sampleStructAsc L ∧ SizeMinimalAligned L) ∧
    (let L := overlappingUnionLayout sampleStructAsc
     OffsetsLengthMatch sampleStructAsc L ∧ OffsetsAligned .none sampleStructAsc L ∧
     OffsetsMonotone L ∧ ¬ FieldsDisjoint sampleStructAsc L ∧
     FieldsInBounds sampleStructAsc L ∧ SizeMinimalAligned L) ∧
    (let L := truncatedEndLayout sampleStructAsc
     OffsetsLengthMatch sampleStructAsc L ∧ OffsetsAligned .none sampleStructAsc L ∧
     OffsetsMonotone L ∧ FieldsDisjoint sampleStructAsc L ∧
     ¬ FieldsInBounds sampleStructAsc L ∧ SizeMinimalAligned L) ∧
    (let L := unroundedTailLayout sampleStructDesc
     OffsetsLengthMatch sampleStructDesc L ∧ OffsetsAligned .none sampleStructDesc L ∧
     OffsetsMonotone L ∧ FieldsDisjoint sampleStructDesc L ∧
     FieldsInBounds sampleStructDesc L ∧ ¬ SizeMinimalAligned L) :=
  ⟨variant_unaligned_violates_only_aligned,
   variant_reordered_violates_only_monotone,
   variant_overlapping_violates_only_disjoint,
   variant_truncated_end_violates_only_in_bounds,
   variant_unrounded_tail_violates_only_size_minimal⟩

/-! ## Result 2: `packed(N)` and `align(N)` Modifier Laws -/

private theorem placeFields_end_ge_sum (m : ReprModifier) (c : Nat) (fs : List FieldLayout) :
    c + totalFieldSize fs ≤ (placeFields m c fs).2 := by
  induction fs generalizing c with
  | nil => simp [placeFields, totalFieldSize]
  | cons f fs ih =>
    rw [placeFields_cons]
    dsimp only [totalFieldSize]
    have h1 := le_alignUp c (effFieldAlign m f.align)
    have h2 := ih (alignUp c (effFieldAlign m f.align) + f.size)
    omega

private theorem placeFields_occupies_of_end_eq_sum (m : ReprModifier) (c : Nat)
    (fs : List FieldLayout)
    (heq : (placeFields m c fs).2 = c + totalFieldSize fs)
    (b : Nat) (hlo : c ≤ b) (hhi : b < c + totalFieldSize fs) :
    ∃ (i : Nat) (hf : i < fs.length) (ho : i < (placeFields m c fs).1.length),
      (placeFields m c fs).1[i] ≤ b ∧ b < (placeFields m c fs).1[i] + fs[i].size := by
  induction fs generalizing c with
  | nil =>
    simp [totalFieldSize] at hhi
    omega
  | cons f fs ih =>
    rw [placeFields_cons] at heq ⊢
    dsimp only [totalFieldSize] at heq hhi ⊢
    have h1 : c ≤ alignUp c (effFieldAlign m f.align) :=
      le_alignUp c (effFieldAlign m f.align)
    have h2 :
        (alignUp c (effFieldAlign m f.align) + f.size) + totalFieldSize fs ≤
          (placeFields m (alignUp c (effFieldAlign m f.align) + f.size) fs).2 :=
      placeFields_end_ge_sum m (alignUp c (effFieldAlign m f.align) + f.size) fs
    have hoff : alignUp c (effFieldAlign m f.align) = c := by omega
    have hend :
        (placeFields m (alignUp c (effFieldAlign m f.align) + f.size) fs).2 =
          (alignUp c (effFieldAlign m f.align) + f.size) + totalFieldSize fs := by
      omega
    by_cases hb : b < c + f.size
    · refine ⟨0, by simp, by simp, ?_, ?_⟩
      · simp only [List.getElem_cons_zero]
        omega
      · simp only [List.getElem_cons_zero]
        omega
    · rcases ih (alignUp c (effFieldAlign m f.align) + f.size) hend (by omega) (by omega) with
        ⟨i, hf, ho, hlo_i, hhi_i⟩
      refine ⟨i + 1, by simp; omega, by simp; omega, ?_, ?_⟩
      · simpa only [List.getElem_cons_succ] using hlo_i
      · simpa only [List.getElem_cons_succ] using hhi_i

private theorem placeFields_end_eq_sum_of_occupies (m : ReprModifier) (c : Nat)
    (fs : List FieldLayout)
    (hocc : ∀ b : Nat, c ≤ b → b < (placeFields m c fs).2 →
      ∃ (i : Nat) (hf : i < fs.length) (ho : i < (placeFields m c fs).1.length),
        (placeFields m c fs).1[i] ≤ b ∧ b < (placeFields m c fs).1[i] + fs[i].size) :
    (placeFields m c fs).2 = c + totalFieldSize fs := by
  induction fs generalizing c with
  | nil => simp [placeFields, totalFieldSize]
  | cons f fs ih =>
    rw [placeFields_cons] at hocc ⊢
    dsimp only [totalFieldSize] at hocc ⊢
    have hc_le_off : c ≤ alignUp c (effFieldAlign m f.align) :=
      le_alignUp c (effFieldAlign m f.align)
    have hoff_le_end :
        alignUp c (effFieldAlign m f.align) + f.size ≤
          (placeFields m (alignUp c (effFieldAlign m f.align) + f.size) fs).2 :=
      cursor_le_placeFields_end m (alignUp c (effFieldAlign m f.align) + f.size) fs
    have hoff : alignUp c (effFieldAlign m f.align) = c := by
      by_cases hlt : c < alignUp c (effFieldAlign m f.align)
      · rcases hocc c (Nat.le_refl c) (by omega) with ⟨i, _, ho, hlo, _⟩
        cases i with
        | zero =>
          simp only [List.getElem_cons_zero] at hlo
          omega
        | succ j =>
          simp only [List.getElem_cons_succ] at hlo
          have hj : j < (placeFields m (alignUp c (effFieldAlign m f.align) + f.size) fs).1.length := by
            simp at ho; omega
          have hcur := cursor_le_placeFields_getElem m
            (alignUp c (effFieldAlign m f.align) + f.size) fs j hj
          omega
      · omega
    have hend_fs :
        (placeFields m (alignUp c (effFieldAlign m f.align) + f.size) fs).2 =
          (alignUp c (effFieldAlign m f.align) + f.size) + totalFieldSize fs := by
      apply ih (alignUp c (effFieldAlign m f.align) + f.size)
      intro b hblo hbhi
      rcases hocc b (by omega) hbhi with ⟨i, hf, ho, hlo, hhi⟩
      cases i with
      | zero =>
        simp only [List.getElem_cons_zero] at hhi
        omega
      | succ j =>
        exact ⟨j, by simp at hf; omega, by simp at ho; omega,
          by simpa only [List.getElem_cons_succ] using hlo,
          by simpa only [List.getElem_cons_succ] using hhi⟩
    omega

private theorem fieldsMaxAlign_packed_one (fs : List FieldLayout) :
    fieldsMaxAlign (.packed 1) fs = 1 := by
  apply Nat.le_antisymm
  · unfold fieldsMaxAlign
    apply foldl_max_le_gen (fun (f : FieldLayout) => effFieldAlign (.packed 1) f.align) fs 1 1 (Nat.le_refl 1)
    intro f _
    simp only [effFieldAlign]
    omega
  · exact foldl_max_ge_init_gen (fun (f : FieldLayout) => effFieldAlign (.packed 1) f.align) fs 1

private theorem placeFields_packed_one_end (c : Nat) (fs : List FieldLayout) :
    (placeFields (.packed 1) c fs).2 = c + totalFieldSize fs := by
  induction fs generalizing c with
  | nil => simp [placeFields, totalFieldSize]
  | cons f fs ih =>
    rw [placeFields_cons, alignUp_packed_one_eff]
    dsimp only [totalFieldSize]
    rw [ih (c + f.size)]
    omega

private theorem placeFields_packed_one_offset (c : Nat) (fs : List FieldLayout)
    (i : Nat) (hf : i < fs.length) (ho : i < (placeFields (.packed 1) c fs).1.length) :
    (placeFields (.packed 1) c fs).1[i] = c + totalFieldSize (fs.take i) := by
  induction fs generalizing c i with
  | nil => cases hf
  | cons f fs ih =>
    revert ho
    rw [placeFields_cons]
    dsimp only
    intro ho
    cases i with
    | zero =>
      simp [alignUp_packed_one_eff, totalFieldSize]
    | succ i =>
      simp only [List.getElem_cons_succ, List.take_succ_cons, totalFieldSize]
      have halign : alignUp c (effFieldAlign (.packed 1) f.align) = c :=
        alignUp_packed_one_eff c f.align
      have hih := ih (alignUp c (effFieldAlign (.packed 1) f.align) + f.size) i
        (by simp at hf; omega)
        (by simp at ho; omega)
      omega

set_option linter.unusedVariables false in
/-- Main Result 2a: `#[repr(C, packed(1))]` yields zero shallow padding (`AllBytesOccupied`),
    alignment `1`, size equal to `totalFieldSize`, and exact prefix-sum field offsets. -/
theorem reprCStruct_packed_one_no_padding (fields : List FieldLayout) :
    let L := reprCStruct (.packed 1) fields
    AllBytesOccupied fields L ∧
    L.size = totalFieldSize fields ∧
    L.endOffset = totalFieldSize fields ∧
    L.align = 1 ∧
    ∀ (i : Nat) (hf : i < fields.length) (ho : i < L.offsets.length),
      L.offsets[i] = totalFieldSize (fields.take i) := by
  dsimp only
  have hparts := reprCStruct_eq_parts (.packed 1) fields
  have hal : structAlign (.packed 1) fields = 1 := fieldsMaxAlign_packed_one fields
  have hend : (placeFields (.packed 1) 0 fields).2 = totalFieldSize fields := by
    simpa using placeFields_packed_one_end 0 fields
  have hsz : alignUp (placeFields (.packed 1) 0 fields).2 (structAlign (.packed 1) fields) =
      totalFieldSize fields := by
    rw [hend, hal, alignUp_one]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold AllBytesOccupied
    rw [hparts]
    dsimp only
    rw [hsz]
    intro b hb
    exact placeFields_occupies_of_end_eq_sum (.packed 1) 0 fields
      (by omega) b (Nat.zero_le b) (by omega)
  · rw [hparts]; exact hsz
  · rw [hparts]; exact hend
  · rw [hparts]; exact hal
  · rw [hparts]
    intro i _hf ho
    simpa using placeFields_packed_one_offset 0 fields i _hf ho

theorem nv_reprCStruct_packed_one_no_padding :
    reprCStruct (.packed 1) [⟨1, 1⟩, ⟨4, 4⟩, ⟨1, 1⟩] =
      { offsets := [0, 1, 5], endOffset := 6, size := 6, align := 1 } := rfl

/-- Main Result 2b: For any `n` and `fields`, `#[repr(C, packed(n))]` caps overall struct
    alignment at both `max 1 n` and the unpacked struct's alignment. -/
theorem reprCStruct_packed_align_le (fields : List FieldLayout) (n : Nat) :
    (reprCStruct (.packed n) fields).align ≤ max 1 n ∧
    (reprCStruct (.packed n) fields).align ≤ (reprCStruct .none fields).align := by
  rw [reprCStruct_eq_parts (.packed n) fields, reprCStruct_eq_parts .none fields]
  dsimp only [structAlign, fieldsMaxAlign]
  constructor
  · apply foldl_max_le_gen (fun (f : FieldLayout) => effFieldAlign (.packed n) f.align) fields 1 (max 1 n)
      (Nat.le_max_left 1 n)
    intro f _
    simp only [effFieldAlign]
    have h1 : min f.align n ≤ n := Nat.min_le_right f.align n
    have h2 : n ≤ max 1 n := Nat.le_max_right 1 n
    omega
  · apply foldl_max_le_gen (fun (f : FieldLayout) => effFieldAlign (.packed n) f.align) fields 1
      (fields.foldl (fun acc f => max acc (effFieldAlign .none f.align)) 1)
      (foldl_max_ge_init_gen (fun (f : FieldLayout) => effFieldAlign .none f.align) fields 1)
    intro f hf
    have h1 : effFieldAlign (.packed n) f.align ≤ effFieldAlign .none f.align := by
      simp [effFieldAlign, Nat.min_le_left]
    have h2 := foldl_max_ge_mem_gen (fun (g : FieldLayout) => effFieldAlign .none g.align) fields 1 hf
    omega

theorem nv_reprCStruct_packed_align_le :
    let fields : List FieldLayout := [⟨1, 1⟩, ⟨8, 8⟩]
    (reprCStruct (.packed 2) fields).align = 2 ∧
    (reprCStruct .none fields).align = 8 ∧
    (reprCStruct (.packed 2) fields).align ≤ max 1 2 ∧
    (reprCStruct (.packed 2) fields).align ≤ (reprCStruct .none fields).align := by
  decide

/-- Witness supporting the non-claim on `reprCStruct_packed_align_le`: in the unconstrained
    `Nat` domain with non-power-of-two alignments, `packed(2)` can strictly increase struct
    size (`8 > 6` on `[⟨3, 3⟩, ⟨3, 3⟩]`). -/
theorem ex_packed_non_pow2_increases_size :
    (reprCStruct .none [⟨3, 3⟩, ⟨3, 3⟩]).size = 6 ∧
    (reprCStruct (.packed 2) [⟨3, 3⟩, ⟨3, 3⟩]).size = 8 := by
  decide

private theorem placeFields_packed_ge_eq (c n : Nat) (fs : List FieldLayout)
    (h_ge : ∀ f ∈ fs, f.align ≤ n) :
    placeFields (.packed n) c fs = placeFields .none c fs := by
  induction fs generalizing c with
  | nil => rfl
  | cons f fs ih =>
    rw [placeFields_cons, placeFields_cons]
    have heff : effFieldAlign (.packed n) f.align = effFieldAlign .none f.align := by
      have hf := h_ge f (by simp)
      simp [effFieldAlign, Nat.min_eq_left hf]
    rw [heff, ih _ (fun g hg => h_ge g (by simp [hg]))]

private theorem fieldsMaxAlign_packed_ge_eq (n : Nat) (fs : List FieldLayout) (init : Nat)
    (h_ge : ∀ f ∈ fs, f.align ≤ n) :
    fs.foldl (fun acc f => max acc (effFieldAlign (.packed n) f.align)) init =
      fs.foldl (fun acc f => max acc (effFieldAlign .none f.align)) init := by
  induction fs generalizing init with
  | nil => rfl
  | cons f fs ih =>
    simp only [List.foldl_cons]
    have heff : effFieldAlign (.packed n) f.align = effFieldAlign .none f.align := by
      have hf := h_ge f (by simp)
      simp [effFieldAlign, Nat.min_eq_left hf]
    rw [heff]
    exact ih _ (fun g hg => h_ge g (by simp [hg]))

/-- Main Result 2c: `#[repr(C, packed(N))]` is a complete no-op on layout whenever `N` is at
    least every field's natural alignment (`r[layout.repr.alignment.packed]`). -/
theorem reprCStruct_packed_ge_fields_noop
    (fields : List FieldLayout) (n : Nat)
    (h_ge : ∀ f ∈ fields, f.align ≤ n) :
    reprCStruct (.packed n) fields = reprCStruct .none fields := by
  rw [reprCStruct_eq_parts (.packed n) fields, reprCStruct_eq_parts .none fields]
  have hp := placeFields_packed_ge_eq 0 n fields h_ge
  have ha : structAlign (.packed n) fields = structAlign .none fields := by
    unfold structAlign fieldsMaxAlign
    exact fieldsMaxAlign_packed_ge_eq n fields 1 h_ge
  rw [hp, ha]

theorem nv_reprCStruct_packed_ge_fields_noop :
    let fields : List FieldLayout := [⟨1, 1⟩, ⟨4, 4⟩]
    let n := 4
    ∀ f ∈ fields, f.align ≤ n := by
  dsimp only
  intro f hf
  simp at hf
  rcases hf with rfl | rfl <;> decide

/-- Canonical counterexample dropping `h_ge` from `reprCStruct_packed_ge_fields_noop`:
    with `n = 2 < 4` on `[u8, u32]`, `packed(2)` changes offsets, size, and alignment. -/
theorem ce_packed_noop_drop_ge :
    let fields : List FieldLayout := [⟨1, 1⟩, ⟨4, 4⟩]
    let n := 2
    reprCStruct (.packed n) fields ≠ reprCStruct .none fields := by
  decide

private theorem placeFields_aligned_eq_none (n c : Nat) (fs : List FieldLayout) :
    placeFields (.aligned n) c fs = placeFields .none c fs := by
  induction fs generalizing c with
  | nil => rfl
  | cons f fs ih =>
    rw [placeFields_cons, placeFields_cons]
    dsimp only [effFieldAlign]
    rw [ih]

private theorem fieldsMaxAlign_aligned_eq_none (n : Nat) (fs : List FieldLayout) (init : Nat) :
    fs.foldl (fun acc f => max acc (effFieldAlign (.aligned n) f.align)) init =
      fs.foldl (fun acc f => max acc (effFieldAlign .none f.align)) init := by
  simp only [effFieldAlign]

/-- Main Result 2d (definitional in the model): `#[repr(C, align(N))]` leaves field offsets
    and `endOffset` equal to those of `reprCStruct .none fields`, sets `align` to
    `max base.align n`, and sets `size` to `alignUp base.endOffset (max base.align n)`. -/
theorem reprCStruct_aligned_preserves_offsets (fields : List FieldLayout) (n : Nat) :
    let base := reprCStruct .none fields
    let aligned := reprCStruct (.aligned n) fields
    aligned.offsets = base.offsets ∧
    aligned.endOffset = base.endOffset ∧
    aligned.align = max base.align n ∧
    aligned.size = alignUp base.endOffset (max base.align n) := by
  dsimp only
  rw [reprCStruct_eq_parts .none fields, reprCStruct_eq_parts (.aligned n) fields]
  dsimp only
  have hp := placeFields_aligned_eq_none n 0 fields
  have hmax : fieldsMaxAlign (.aligned n) fields = fieldsMaxAlign .none fields :=
    fieldsMaxAlign_aligned_eq_none n fields 1
  have hal : structAlign (.aligned n) fields = max (structAlign .none fields) n := by
    unfold structAlign
    rw [hmax]
  rw [hp, hal]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem nv_reprCStruct_aligned_preserves_offsets :
    let fields : List FieldLayout := [⟨2, 2⟩, ⟨1, 1⟩]
    (reprCStruct (.aligned 8) fields).offsets = (reprCStruct .none fields).offsets ∧
    (reprCStruct (.aligned 8) fields).align = 8 ∧
    (reprCStruct (.aligned 8) fields).size = 8 := by
  decide

/-- Main Result 2e: When all field alignments and `n` are powers of two, the `align(N)`
    rounded size `alignUp base.endOffset (max base.align n)` also equals
    `alignUp base.size (max base.align n)` (justifying post-hoc size rounding of an
    already-rounded `#[repr(C)]` struct layout). -/
theorem reprCStruct_aligned_size_eq_alignUp_base_size_of_pow2
    (fields : List FieldLayout) (n : Nat)
    (h_fields : ∀ f ∈ fields, AlignPow2 f)
    (h_n : IsPowerOfTwo n) :
    let base := reprCStruct .none fields
    (reprCStruct (.aligned n) fields).size = alignUp base.size (max base.align n) := by
  dsimp only
  let base := reprCStruct .none fields
  have hpres := reprCStruct_aligned_preserves_offsets fields n
  have hbase_sz : base.size = alignUp base.endOffset base.align := by
    change (reprCStruct .none fields).size =
      alignUp (reprCStruct .none fields).endOffset (reprCStruct .none fields).align
    rw [reprCStruct_eq_parts .none fields]
  have hpow_base : IsPowerOfTwo base.align :=
    (reprCStruct_align_pow2_divides .none fields h_fields trivial).1
  have hpow_max : IsPowerOfTwo (max base.align n) := isPowerOfTwo_max hpow_base h_n
  have hdvd : base.align ∣ max base.align n :=
    isPowerOfTwo_dvd_of_le hpow_base hpow_max (Nat.le_max_left _ _)
  rw [hpres.2.2.2, hbase_sz]
  exact (alignUp_alignUp_of_dvd (isPowerOfTwo_pos hpow_max) hdvd).symm

theorem nv_reprCStruct_aligned_size_eq_alignUp_base_size_of_pow2 :
    let fields : List FieldLayout := [⟨4, 4⟩, ⟨1, 1⟩]
    let n := 8
    (∀ f ∈ fields, AlignPow2 f) ∧ IsPowerOfTwo n := by
  refine ⟨?_, ⟨3, rfl⟩⟩
  intro f hf
  simp at hf
  rcases hf with rfl | rfl
  · exact ⟨2, rfl⟩
  · exact ⟨0, rfl⟩

/-- Canonical counterexample dropping `h_fields` from
    `reprCStruct_aligned_size_eq_alignUp_base_size_of_pow2`: with non-power-of-two field
    alignment `3`, `base.endOffset = 4` gives `base.size = 6`; raising to `align(4)` yields
    `alignUp 4 4 = 4 ≠ 8 = alignUp 6 4`. -/
theorem ce_aligned_size_drop_fields_pow2 :
    let fields : List FieldLayout := [⟨3, 3⟩, ⟨1, 1⟩]
    let n := 4
    let base := reprCStruct .none fields
    IsPowerOfTwo n ∧
    (reprCStruct (.aligned n) fields).size ≠ alignUp base.size (max base.align n) := by
  exact ⟨⟨2, rfl⟩, by decide⟩

/-- Canonical counterexample dropping `h_n` from
    `reprCStruct_aligned_size_eq_alignUp_base_size_of_pow2`: with power-of-two fields
    `[⟨4, 4⟩, ⟨1, 1⟩]` (`base.endOffset = 5`, `base.size = 8`) and non-power-of-two `n = 6`,
    `alignUp 5 6 = 6 ≠ 12 = alignUp 8 6`. -/
theorem ce_aligned_size_drop_n_pow2 :
    let fields : List FieldLayout := [⟨4, 4⟩, ⟨1, 1⟩]
    let n := 6
    let base := reprCStruct .none fields
    (∀ f ∈ fields, AlignPow2 f) ∧
    (reprCStruct (.aligned n) fields).size ≠ alignUp base.size (max base.align n) := by
  refine ⟨?_, by decide⟩
  intro f hf
  simp at hf
  rcases hf with rfl | rfl
  · exact ⟨2, rfl⟩
  · exact ⟨0, rfl⟩

/-! ## Result 3: Shallow Padding Characterization -/

/-- Main Result 3a: A `#[repr(C)]` struct (with any modifier `m`) has no shallow padding
    (`AllBytesOccupied`) if and only if its total padded size equals the sum of its
    declared field sizes. -/
theorem reprCStruct_no_padding_iff_size_eq_sum
    (m : ReprModifier) (fields : List FieldLayout) :
    AllBytesOccupied fields (reprCStruct m fields) ↔
      (reprCStruct m fields).size = totalFieldSize fields := by
  have hparts := reprCStruct_eq_parts m fields
  have hsum_le_end : totalFieldSize fields ≤ (placeFields m 0 fields).2 := by
    simpa using placeFields_end_ge_sum m 0 fields
  have hend_le_sz :
      (placeFields m 0 fields).2 ≤ alignUp (placeFields m 0 fields).2 (structAlign m fields) :=
    le_alignUp (placeFields m 0 fields).2 (structAlign m fields)
  constructor
  · intro hocc
    unfold AllBytesOccupied at hocc
    rw [hparts] at hocc ⊢
    dsimp only at hocc ⊢
    have hsz_eq_end :
        alignUp (placeFields m 0 fields).2 (structAlign m fields) =
          (placeFields m 0 fields).2 := by
      by_cases hlt :
          (placeFields m 0 fields).2 <
            alignUp (placeFields m 0 fields).2 (structAlign m fields)
      · rcases hocc (placeFields m 0 fields).2 hlt with ⟨i, hf, ho, _, hhi⟩
        have hin := placeFields_inBounds m 0 fields i hf ho
        omega
      · omega
    have hend_eq_sum : (placeFields m 0 fields).2 = 0 + totalFieldSize fields := by
      apply placeFields_end_eq_sum_of_occupies m 0 fields
      intro b _ hb
      exact hocc b (by omega)
    omega
  · intro hsz_eq
    unfold AllBytesOccupied
    rw [hparts] at hsz_eq ⊢
    dsimp only at hsz_eq ⊢
    have hend_eq : (placeFields m 0 fields).2 = 0 + totalFieldSize fields := by omega
    intro b hb
    exact placeFields_occupies_of_end_eq_sum m 0 fields hend_eq b (Nat.zero_le b) (by omega)

theorem nv_reprCStruct_no_padding_iff :
    let m := ReprModifier.none
    let fields : List FieldLayout := [⟨2, 2⟩, ⟨2, 2⟩]
    AllBytesOccupied fields (reprCStruct m fields) ∧
      (reprCStruct m fields).size = totalFieldSize fields :=
  ⟨ex_allBytesOccupied_pos, rfl⟩

private theorem placeFields_replicate_dvd_end (c k : Nat) (f : FieldLayout)
    (hdvd_sz : f.align ∣ f.size) (hdvd_c : f.align ∣ c) :
    (placeFields .none c (List.replicate k f)).2 = c + totalFieldSize (List.replicate k f) := by
  induction k generalizing c with
  | zero => simp [List.replicate, placeFields, totalFieldSize]
  | succ k ih =>
    simp only [List.replicate_succ, totalFieldSize]
    rw [placeFields_cons]
    dsimp only [effFieldAlign]
    rw [alignUp_eq_self_of_dvd hdvd_c]
    have hdvd_next : f.align ∣ (c + f.size) := Nat.dvd_add hdvd_c hdvd_sz
    rw [ih (c + f.size) hdvd_next]
    omega

private theorem totalFieldSize_replicate_dvd (k : Nat) (f : FieldLayout)
    (hdvd_sz : f.align ∣ f.size) :
    f.align ∣ totalFieldSize (List.replicate k f) := by
  induction k with
  | zero =>
    simp only [List.replicate, totalFieldSize]
    exact Nat.dvd_zero f.align
  | succ k ih =>
    simp only [List.replicate_succ, totalFieldSize]
    exact Nat.dvd_add hdvd_sz ih

private theorem fieldsMaxAlign_replicate_succ (k : Nat) (f : FieldLayout) (hpos : 0 < f.align) :
    fieldsMaxAlign .none (List.replicate (k + 1) f) = f.align := by
  apply Nat.le_antisymm
  · unfold fieldsMaxAlign
    apply foldl_max_le_gen (fun (g : FieldLayout) => effFieldAlign .none g.align)
      (List.replicate (k + 1) f) 1 f.align hpos
    intro g hg
    have hgeq : g = f := List.eq_of_mem_replicate hg
    subst hgeq
    exact Nat.le_refl _
  · unfold fieldsMaxAlign
    have hmem : f ∈ List.replicate (k + 1) f := by
      rw [List.replicate_succ]
      simp
    exact foldl_max_ge_mem_gen (fun (g : FieldLayout) => effFieldAlign .none g.align)
      (List.replicate (k + 1) f) 1 hmem

/-- Main Result 3b (exact characterization under `AlignPos`): For any field layout `f` with
    positive alignment (`0 < f.align`), every homogeneous `#[repr(C)]` struct
    `List.replicate k f` has no shallow padding if and only if `f.align ∣ f.size`. -/
theorem reprCStruct_homogeneous_no_padding_iff_of_align_pos
    (f : FieldLayout) (h_pos : AlignPos f) :
    (∀ k : Nat, AllBytesOccupied (List.replicate k f) (reprCStruct .none (List.replicate k f))) ↔
      SizeMultipleOfAlign f := by
  unfold AlignPos at h_pos
  unfold SizeMultipleOfAlign
  constructor
  · intro hall
    have h1 := (reprCStruct_no_padding_iff_size_eq_sum .none (List.replicate 1 f)).mp (hall 1)
    have hsz1 : (reprCStruct .none (List.replicate 1 f)).size = alignUp f.size f.align := by
      rw [reprCStruct_eq_parts .none (List.replicate 1 f)]
      dsimp only
      have hal1 : structAlign .none (List.replicate 1 f) = f.align :=
        fieldsMaxAlign_replicate_succ 0 f h_pos
      have hend1 : (placeFields .none 0 [f]).2 = f.size := by
        rw [placeFields_cons]
        simp [placeFields, effFieldAlign, alignUp_zero]
      rw [hal1]
      simpa [List.replicate] using congrArg (fun x => alignUp x f.align) hend1
    have htot1 : totalFieldSize (List.replicate 1 f) = f.size := by
      simp [List.replicate, totalFieldSize]
    rw [hsz1, htot1] at h1
    rw [← h1]
    exact dvd_alignUp h_pos
  · intro hdvd k
    rw [reprCStruct_no_padding_iff_size_eq_sum]
    rw [reprCStruct_eq_parts .none (List.replicate k f)]
    dsimp only
    have hend := placeFields_replicate_dvd_end 0 k f hdvd (Nat.dvd_zero f.align)
    rw [Nat.zero_add] at hend
    rw [hend]
    cases k with
    | zero =>
      simp [List.replicate, totalFieldSize, structAlign, fieldsMaxAlign, alignUp_one]
    | succ k =>
      have hal : structAlign .none (List.replicate (k + 1) f) = f.align :=
        fieldsMaxAlign_replicate_succ k f h_pos
      rw [hal]
      exact alignUp_eq_self_of_dvd (totalFieldSize_replicate_dvd (k + 1) f hdvd)

theorem nv_reprCStruct_homogeneous_no_padding_iff_of_align_pos :
    AlignPos ⟨4, 4⟩ := by
  simp [AlignPos]

private theorem placeFields_none_unit0 (c k : Nat) :
    placeFields .none c (List.replicate k ⟨1, 0⟩) = (List.range' c k, c + k) := by
  induction k generalizing c with
  | zero => simp [placeFields, List.range']
  | succ k ih =>
    simp only [List.replicate_succ, placeFields, effFieldAlign, alignUp, paddingNeeded,
      ↓reduceIte, Nat.add_zero]
    rw [ih (c + 1)]
    simp [List.range'_succ]
    omega

private theorem foldl_max_zero (k acc : Nat) :
    (List.replicate k (⟨1, 0⟩ : FieldLayout)).foldl
      (fun a f => max a (effFieldAlign .none f.align)) acc = acc := by
  induction k generalizing acc with
  | zero => rfl
  | succ k ih =>
    simp only [List.replicate_succ, List.foldl_cons, effFieldAlign, Nat.max_zero]
    exact ih acc

/-- Canonical counterexample dropping `h_pos` from
    `reprCStruct_homogeneous_no_padding_iff_of_align_pos`: at `f = ⟨1, 0⟩`, every
    homogeneous struct `List.replicate k ⟨1, 0⟩` is padding-free (`offsets = [0..k-1]`,
    `size = k`), yet `¬ SizeMultipleOfAlign ⟨1, 0⟩` (`¬ (0 ∣ 1)`). -/
theorem ce_homogeneous_no_padding_iff_drop_align_pos :
    let f : FieldLayout := ⟨1, 0⟩
    ¬ ((∀ k : Nat, AllBytesOccupied (List.replicate k f) (reprCStruct .none (List.replicate k f))) ↔
        SizeMultipleOfAlign f) := by
  dsimp only
  intro hiff
  have hall : ∀ k : Nat,
      AllBytesOccupied (List.replicate k ⟨1, 0⟩) (reprCStruct .none (List.replicate k ⟨1, 0⟩)) := by
    intro k
    have hL : reprCStruct .none (List.replicate k ⟨1, 0⟩) =
        { offsets := List.range' 0 k, endOffset := k, size := k, align := 1 } := by
      unfold reprCStruct structAlign fieldsMaxAlign
      rw [placeFields_none_unit0 0 k, foldl_max_zero k 1]
      simp [alignUp, paddingNeeded, Nat.mod_one]
    rw [hL]
    intro b hb
    refine ⟨b, by simp [hb], by simp [hb], ?_, ?_⟩
    · simp
    · simp
  have hdvd : SizeMultipleOfAlign ⟨1, 0⟩ := hiff.mp hall
  rcases hdvd with ⟨q, hq⟩
  simp at hq

/-- Concrete witness for the positive-alignment failure of `SizeMultipleOfAlign`:
    `f = ⟨3, 2⟩` satisfies `AlignPos` (`0 < 2`) and fails `2 ∣ 3`, yielding trailing padding
    at `k = 1` (`size = 4`, byte `3` uncovered). -/
theorem ex_homogeneous_non_dvd_has_padding :
    let f : FieldLayout := ⟨3, 2⟩
    AlignPos f ∧ ¬ SizeMultipleOfAlign f ∧
    ¬ ∀ k : Nat, AllBytesOccupied (List.replicate k f) (reprCStruct .none (List.replicate k f)) := by
  refine ⟨by simp [AlignPos], ?_, ?_⟩
  · rintro ⟨q, hq⟩; simp at hq; omega
  · intro h
    have h1 := h 1
    rcases h1 3 (by decide) with ⟨i, hf, ho, _, hhi⟩
    match i with
    | 0 => simp [List.replicate, reprCStruct, placeFields, effFieldAlign, alignUp, paddingNeeded] at hhi
    | _ + 1 => simp [List.replicate] at hf

/-- Main Result 3c (fully proved): Heterogeneous `#[repr(C)]` struct `[u8, u16]`
    (`⟨1, 1⟩, ⟨2, 2⟩`) has both fields well-formed (`AlignPow2` and `SizeMultipleOfAlign`),
    yet has inter-field padding at byte `1` (`size = 4 ≠ 3 = totalFieldSize`), showing
    homogeneity cannot be dropped from `reprCStruct_homogeneous_no_padding_iff_of_align_pos`. -/
theorem ce_heterogeneous_u8_u16_has_padding :
    let fields : List FieldLayout := [⟨1, 1⟩, ⟨2, 2⟩]
    let L := reprCStruct .none fields
    (∀ f ∈ fields, AlignPow2 f ∧ SizeMultipleOfAlign f) ∧
    ¬ AllBytesOccupied fields L ∧
    L.size = 4 ∧
    totalFieldSize fields = 3 ∧
    L.size ≠ totalFieldSize fields := by
  refine ⟨?_, ex_allBytesOccupied_neg, rfl, rfl, by decide⟩
  intro f hf
  simp at hf
  rcases hf with rfl | rfl
  · exact ⟨⟨0, rfl⟩, ⟨1, rfl⟩⟩
  · exact ⟨⟨1, rfl⟩, ⟨1, rfl⟩⟩

/-- Dual trailing-padding example `[u16, u8]` (`⟨2, 2⟩, ⟨1, 1⟩`): both fields are
    well-formed and there is zero inter-field padding (`offsets = [0, 2]`), yet trailing
    padding occupies byte `3` (`size = 4 ≠ 3 = totalFieldSize`). -/
theorem ce_heterogeneous_u16_u8_has_trailing_padding :
    let fields : List FieldLayout := [⟨2, 2⟩, ⟨1, 1⟩]
    let L := reprCStruct .none fields
    (∀ f ∈ fields, AlignPow2 f ∧ SizeMultipleOfAlign f) ∧
    ¬ AllBytesOccupied fields L ∧
    L.offsets = [0, 2] ∧
    L.size = 4 ∧
    totalFieldSize fields = 3 := by
  refine ⟨?_, ?_, rfl, rfl, rfl⟩
  · intro f hf
    simp at hf
    rcases hf with rfl | rfl
    · exact ⟨⟨1, rfl⟩, ⟨1, rfl⟩⟩
    · exact ⟨⟨0, rfl⟩, ⟨1, rfl⟩⟩
  · intro h
    rcases h 3 (by decide) with ⟨i, hf, ho, _, hhi⟩
    match i with
    | 0 => simp [reprCStruct, placeFields, effFieldAlign, alignUp, paddingNeeded] at hhi
    | 1 => simp [reprCStruct, placeFields, effFieldAlign, alignUp, paddingNeeded] at hhi
    | _ + 2 => simp at hf; omega

end Toy.Layout
