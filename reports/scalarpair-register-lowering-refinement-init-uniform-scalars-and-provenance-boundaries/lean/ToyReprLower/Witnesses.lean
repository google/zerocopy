import ToyReprLower.Examples
import ToyReprLower.Lowering

/-!
# Counterexamples (tightness witnesses), positive controls and non-vacuity witnesses

Each counterexample is stated in canonical form: a concrete instance satisfies all the other
hypotheses of the named result and its conclusion (or the named direction) fails.
-/

namespace Toy.ReprLower

/-! ## Lowering (`scalar_roundTrip_refines_iff`, `pair_roundTrip_refines_iff`) -/

/-- Condition (a) cannot be dropped from the `←` direction: padding that carries a byte through a
byte-level transmute. Size `2`, one `initialized` 1-byte integer scalar, the value
`[bits 7, bits 9]`: `hlen`, (b), (d), (c) hold, (a) fails, the round trip does not refine, and the
typed read of byte `1` is defined before lowering and UB after. -/
theorem cex_scalar_padding_carries_bytes :
    let s : Scalar := .initialized (.int 1) fullRange
    let V : List AByte → Prop := (· = [.bits 7, .bits 9])
    (∀ x, V x → x.length = 2) ∧ InitUniform (.scalar s) V ∧
      RangeIncl (.scalar s) V ∧ ProvCoherent (.scalar s) V ∧
      ¬ OutsideExtentsUninit 2 (.scalar s) V ∧ ¬ RoundTripRefines 2 (.scalar s) V ∧
      readInt 1 1 [.bits 7, .bits 9] = some (.int [9]) ∧
      readInt 1 1 (raise 2 (.scalar s) (lower (.scalar s) [.bits 7, .bits 9])) = none := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide⟩
  all_goals first
    | (intro x hx; cases hx; decide)
    | (intro h; have := h _ rfl; revert this; decide)
    | (intro h; have := h _ rfl 1 (by decide) (by decide); revert this; decide)

/-- Condition (b) cannot be dropped from the `←` direction: a partially initialized
`initialized` scalar. -/
theorem cex_scalar_partial_init :
    let s : Scalar := .initialized (.int 2) fullRange
    let V : List AByte → Prop := (· = [.bits 7, .uninit])
    (∀ x, V x → x.length = 2) ∧ OutsideExtentsUninit 2 (.scalar s) V ∧
      RangeIncl (.scalar s) V ∧ ProvCoherent (.scalar s) V ∧
      ¬ InitUniform (.scalar s) V ∧ ¬ RoundTripRefines 2 (.scalar s) V ∧
      readInt 0 1 [.bits 7, .uninit] = some (.int [7]) ∧
      readInt 0 1 (raise 2 (.scalar s) (lower (.scalar s) [.bits 7, .uninit])) = none := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide⟩
  all_goals first
    | (intro x hx; cases hx; decide)
    | (intro h; have := h _ rfl; revert this; decide)

/-- Condition (d) cannot be dropped from the `←` direction: a value outside an `initialized`
scalar's range. -/
theorem cex_scalar_out_of_range :
    let s : Scalar := .initialized (.int 1) nonZeroRange
    let V : List AByte → Prop := (· = [.bits 0])
    (∀ x, V x → x.length = 1) ∧ OutsideExtentsUninit 1 (.scalar s) V ∧
      InitUniform (.scalar s) V ∧ ProvCoherent (.scalar s) V ∧
      ¬ RangeIncl (.scalar s) V ∧ ¬ RoundTripRefines 1 (.scalar s) V ∧
      readInt 0 1 [.bits 0] = some (.int [0]) ∧
      readInt 0 1 (raise 1 (.scalar s) (lower (.scalar s) [.bits 0])) = none := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide⟩
  all_goals first
    | (intro x hx; cases hx; decide)
    | (intro h; have := h _ rfl; revert this; decide)

/-- Condition (c) cannot be dropped from the `←` direction (integer scalar): pointer fragments
under an integer scalar lose their provenance; a typed pointer read afterwards returns a
provenance-free pointer, which is less defined. -/
theorem cex_scalar_frags_under_int :
    let s : Scalar := .initialized (.int 2) fullRange
    let x : List AByte := [.ptrFrag 1 7 0, .ptrFrag 2 7 1]
    let V : List AByte → Prop := (· = x)
    (∀ y, V y → y.length = 2) ∧ OutsideExtentsUninit 2 (.scalar s) V ∧
      InitUniform (.scalar s) V ∧ RangeIncl (.scalar s) V ∧
      ¬ ProvCoherent (.scalar s) V ∧ ¬ RoundTripRefines 2 (.scalar s) V ∧
      readPtr 0 2 x = some (.ptr (some 7) [1, 2]) ∧
      readPtr 0 2 (raise 2 (.scalar s) (lower (.scalar s) x)) = some (.ptr none [1, 2]) ∧
      ¬ OutLe (readPtr 0 2 x) (readPtr 0 2 (raise 2 (.scalar s) (lower (.scalar s) x))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide⟩
  all_goals first
    | (intro x hx; cases hx; decide)
    | (intro h; have := h _ rfl; revert this; decide)

/-- Condition (c) cannot be dropped from the `←` direction (pointer scalar): fragments with two
different provenances under one pointer scalar lower to a provenance-free pointer. -/
theorem cex_scalar_mixed_provenance_ptr :
    let s : Scalar := .initialized (.ptr 2) fullRange
    let x : List AByte := [.ptrFrag 1 7 0, .ptrFrag 2 8 1]
    let V : List AByte → Prop := (· = x)
    (∀ y, V y → y.length = 2) ∧ OutsideExtentsUninit 2 (.scalar s) V ∧
      InitUniform (.scalar s) V ∧ RangeIncl (.scalar s) V ∧
      ¬ ProvCoherent (.scalar s) V ∧ ¬ RoundTripRefines 2 (.scalar s) V ∧
      raise 2 (.scalar s) (lower (.scalar s) x) = [.bits 1, .bits 2] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by decide⟩
  all_goals first
    | (intro x hx; cases hx; decide)
    | (intro h; have := h _ rfl; revert this; decide)

/-- `hlen` cannot be dropped from the `←` direction of `scalar_roundTrip_refines_iff` (and of
`union_scalar_roundTrip_refines_iff_outsideExtentsUninit`): with `V` containing a value of the
wrong length, all four conditions hold but the round trip does not refine. -/
theorem cex_scalar_hlen :
    let s : Scalar := .union (.int 1)
    let V : List AByte → Prop := (· = [])
    ¬ (∀ x, V x → x.length = 1) ∧
      OutsideExtentsUninit 1 (.scalar s) V ∧ InitUniform (.scalar s) V ∧
      RangeIncl (.scalar s) V ∧ ProvCoherent (.scalar s) V ∧
      ¬ RoundTripRefines 1 (.scalar s) V := by
  refine ⟨fun h => absurd (h [] rfl) (by decide), ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (intro x hx; cases hx; decide)
    | (intro h; have := h _ rfl; revert this; decide)

/-- Condition (c) cannot be dropped from the `←` direction (pair of pointer scalars): a pointer
split across the `a`/`b` boundary. Size `4`, two `initialized` 2-byte pointer scalars at offsets
`0` and `2`, a pointer's fragments at bytes `1, 2`: the other hypotheses hold, the round trip does
not refine, and the typed pointer read at offset `1` returns a pointer with provenance before
lowering and a provenance-free pointer after (each scalar lowers to a provenance-free pointer). -/
theorem cex_pair_ptr_split_across_boundary :
    let a : Scalar := .initialized (.ptr 2) fullRange
    let x : List AByte := [.bits 0, .ptrFrag 1 7 0, .ptrFrag 2 7 1, .bits 3]
    let V : List AByte → Prop := (· = x)
    (∀ y, V y → y.length = 4) ∧ a.size ≤ 2 ∧
      OutsideExtentsUninit 4 (.pair a a 2) V ∧ InitUniform (.pair a a 2) V ∧
      RangeIncl (.pair a a 2) V ∧ ¬ ProvCoherent (.pair a a 2) V ∧
      ¬ RoundTripRefines 4 (.pair a a 2) V ∧
      readPtr 1 2 x = some (.ptr (some 7) [1, 2]) ∧
      readPtr 1 2 (raise 4 (.pair a a 2) (lower (.pair a a 2) x)) = some (.ptr none [1, 2]) ∧
      ¬ OutLe (readPtr 1 2 x) (readPtr 1 2 (raise 4 (.pair a a 2) (lower (.pair a a 2) x))) := by
  refine ⟨?_, by decide, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide⟩
  all_goals first
    | (intro x hx; cases hx; decide)
    | (intro h; have := h _ rfl; revert this; decide)

/-- Condition (a) cannot be dropped from the `←` direction (pair): padding between the two
scalars carries a byte. -/
theorem cex_pair_padding_carries_bytes :
    let a : Scalar := .initialized (.int 1) fullRange
    let V : List AByte → Prop := (· = [.bits 1, .bits 9, .bits 2])
    (∀ y, V y → y.length = 3) ∧ a.size ≤ 2 ∧
      InitUniform (.pair a a 2) V ∧ RangeIncl (.pair a a 2) V ∧ ProvCoherent (.pair a a 2) V ∧
      ¬ OutsideExtentsUninit 3 (.pair a a 2) V ∧ ¬ RoundTripRefines 3 (.pair a a 2) V := by
  refine ⟨?_, by decide, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (intro x hx; cases hx; decide)
    | (intro h; have := h _ rfl; revert this; decide)
    | (intro h; have := h _ rfl 1 (by decide) (by decide); revert this; decide)

/-- Condition (b) cannot be dropped from the `←` direction (pair). -/
theorem cex_pair_partial_init :
    let a : Scalar := .initialized (.int 2) fullRange
    let b : Scalar := .initialized (.int 1) fullRange
    let V : List AByte → Prop := (· = [.bits 7, .uninit, .bits 1])
    (∀ y, V y → y.length = 3) ∧ a.size ≤ 2 ∧
      OutsideExtentsUninit 3 (.pair a b 2) V ∧ RangeIncl (.pair a b 2) V ∧
      ProvCoherent (.pair a b 2) V ∧
      ¬ InitUniform (.pair a b 2) V ∧ ¬ RoundTripRefines 3 (.pair a b 2) V := by
  refine ⟨?_, by decide, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (intro x hx; cases hx; decide)
    | (intro h; have := h _ rfl; revert this; decide)

/-- Condition (d) cannot be dropped from the `←` direction (pair). -/
theorem cex_pair_out_of_range :
    let a : Scalar := .initialized (.int 1) nonZeroRange
    let b : Scalar := .initialized (.int 1) fullRange
    let V : List AByte → Prop := (· = [.bits 0, .bits 1])
    (∀ y, V y → y.length = 2) ∧ a.size ≤ 1 ∧
      OutsideExtentsUninit 2 (.pair a b 1) V ∧ InitUniform (.pair a b 1) V ∧
      ProvCoherent (.pair a b 1) V ∧
      ¬ RangeIncl (.pair a b 1) V ∧ ¬ RoundTripRefines 2 (.pair a b 1) V := by
  refine ⟨?_, by decide, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (intro x hx; cases hx; decide)
    | (intro h; have := h _ rfl; revert this; decide)

/-- `hlen` cannot be dropped from the `←` direction of `pair_roundTrip_refines_iff`. -/
theorem cex_pair_hlen :
    let a : Scalar := .union (.int 1)
    let V : List AByte → Prop := (· = [])
    ¬ (∀ x, V x → x.length = 2) ∧ a.size ≤ 1 ∧ OutsideExtentsUninit 2 (.pair a a 1) V ∧
      InitUniform (.pair a a 1) V ∧ RangeIncl (.pair a a 1) V ∧ ProvCoherent (.pair a a 1) V ∧
      ¬ RoundTripRefines 2 (.pair a a 1) V := by
  refine ⟨fun h => absurd (h [] rfl) (by decide), by decide, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (intro x hx; cases hx; decide)
    | (intro h; have := h _ rfl; revert this; decide)

/-- Disjointness (`hab : a.size ≤ bOff`) cannot be dropped from the `→` direction of
`pair_roundTrip_refines_iff`: with overlapping extents the round trip refines although
condition (c) fails for `b` (the overlapping byte is raised from `a`). -/
theorem cex_pair_overlap :
    let a : Scalar := .initialized (.ptr 2) fullRange
    let b : Scalar := .initialized (.int 2) fullRange
    let V : List AByte → Prop := (· = [.ptrFrag 0 7 0, .ptrFrag 1 7 1, .bits 7])
    (∀ y, V y → y.length = 3) ∧ ¬ a.size ≤ 1 ∧
      RoundTripRefines 3 (.pair a b 1) V ∧ ¬ ProvCoherent (.pair a b 1) V := by
  refine ⟨?_, by decide, ?_, ?_⟩
  all_goals first
    | (intro x hx; cases hx; decide)
    | (intro h; have := h _ rfl; revert this; decide)

/-! ## `union` scalars -/

/-- `hcov : n ≤ p.size` cannot be dropped from `union_scalar_roundTrip_refines_of_covers_value`:
a 1-byte `union` scalar in a 2-byte value whose second byte carries data does not refine. -/
theorem cex_union_size_lt :
    (∀ x, (· = [AByte.bits 7, .bits 9]) x → x.length = 2) ∧ ¬ 2 ≤ (Prim.int 1).size ∧
      ¬ RoundTripRefines 2 (.scalar (.union (.int 1))) (· = [.bits 7, .bits 9]) := by
  refine ⟨?_, by decide, ?_⟩
  · intro x hx; cases hx; rfl
  · intro h; have := h _ rfl; revert this; decide

/-- `hlen` cannot be dropped from `union_scalar_roundTrip_refines_of_covers_value`: a 1-byte
`union` scalar covering a 1-byte value, with `V` containing the empty list. -/
theorem cex_union_covers_value_hlen :
    1 ≤ (Prim.int 1).size ∧ ¬ (∀ x, (· = ([] : List AByte)) x → x.length = 1) ∧
      ¬ RoundTripRefines 1 (.scalar (.union (.int 1))) (· = []) := by
  refine ⟨by decide, fun h => absurd (h [] rfl) (by decide), ?_⟩
  intro h; have := h _ rfl; revert this; decide

/-- **For every primitive of positive width and every range, some value round-trips through the
`union` scalar but not through the `initialized` one.** For every primitive `p` with
`1 ≤ p.size` and every range `rng`, the value `ptrFrag 0 0 1 :: replicate (p.size - 1) uninit`
(a stray pointer fragment followed by uninitialized bytes) round-trips through `Scalar (union p)`
and does not round-trip through `Scalar (initialized p rng)`. -/
theorem initialized_lowering_not_refines_some_union_value (p : Prim) (rng : List Nat → Bool)
    (hp : 1 ≤ p.size) :
    RoundTripRefines p.size (.scalar (.union p))
        (· = .ptrFrag 0 0 1 :: List.replicate (p.size - 1) .uninit) ∧
      ¬ RoundTripRefines p.size (.scalar (.initialized p rng))
        (· = .ptrFrag 0 0 1 :: List.replicate (p.size - 1) .uninit) := by
  obtain ⟨k, hk⟩ : ∃ k, p.size = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hp).symm⟩
  have hlen : ∀ x : List AByte, x = .ptrFrag 0 0 1 :: List.replicate (p.size - 1) .uninit →
      x.length = p.size := by
    intro x hx; subst hx; simp; omega
  refine ⟨union_scalar_roundTrip_refines_of_covers_value _ p _ hlen (Nat.le_refl _), ?_⟩
  intro h
  obtain ⟨_, hb, _, hc⟩ := scalar_conditions_of_roundTrip_refines _ _ _ h
  have hb' := hb _ rfl
  have hc' := hc _ rfl
  have hsz : (Scalar.initialized p rng).size = k + 1 := hk
  have hseg : seg (.ptrFrag 0 0 1 :: List.replicate (p.size - 1) .uninit) 0
      (Scalar.initialized p rng).size = .ptrFrag 0 0 1 :: List.replicate k .uninit := by
    rw [hsz, hk]; simp [seg]
  simp only [BRepr.comps, List.all_cons, List.all_nil, Bool.and_true, hseg] at hb' hc'
  cases k with
  | zero =>
    cases p <;> simp [provCoherentAt, coherentFor, allUninit, AByte.isFrag, ptrProv, fragProv,
      fragsFrom] at hc'
  | succ k =>
    simp [initUniformAt, allInit, allUninit, List.replicate_succ, AByte.isInit] at hb'

/-- Non-vacuity of `initialized_lowering_not_refines_some_union_value`: the 1-byte integer
primitive with the full range. -/
theorem nonvacuous_initialized_lowering_union_value :
    1 ≤ (Prim.int 1).size ∧
      RoundTripRefines (Prim.int 1).size (.scalar (.union (.int 1)))
        (· = .ptrFrag 0 0 1 :: List.replicate ((Prim.int 1).size - 1) .uninit) ∧
      ¬ RoundTripRefines (Prim.int 1).size (.scalar (.initialized (.int 1) fullRange))
        (· = .ptrFrag 0 0 1 :: List.replicate ((Prim.int 1).size - 1) .uninit) :=
  ⟨by decide, initialized_lowering_not_refines_some_union_value (.int 1) fullRange (by decide)⟩

/-- Positive control for `initialized_lowering_not_refines_some_union_value`: a plain, in-range
value round-trips through an `initialized` scalar with a non-trivial range. -/
theorem initialized_lowering_refines_plain_in_range_value :
    RoundTripRefines 1 (.scalar (.initialized (.int 1) nonZeroRange)) (· = [.bits 5]) := by
  intro x hx; cases hx; decide

/-- `hp : 1 ≤ p.size` cannot be dropped from
`initialized_lowering_not_refines_some_union_value`: at width `0` the named value has the wrong
length, so the conclusion fails; moreover every set of width-`0` values round-trips through every
`initialized` width-`0` scalar, so no width-`0` value separates the two lowerings. -/
theorem cex_initialized_lowering_width_zero (rng : List Nat → Bool) :
    ¬ (RoundTripRefines (Prim.int 0).size (.scalar (.union (.int 0)))
          (· = .ptrFrag 0 0 1 :: List.replicate ((Prim.int 0).size - 1) .uninit) ∧
        ¬ RoundTripRefines (Prim.int 0).size (.scalar (.initialized (.int 0) rng))
          (· = .ptrFrag 0 0 1 :: List.replicate ((Prim.int 0).size - 1) .uninit)) ∧
      ∀ V : List AByte → Prop, (∀ x, V x → x.length = 0) →
        RoundTripRefines 0 (.scalar (.initialized (.int 0) rng)) V := by
  refine ⟨fun ⟨h, _⟩ => ?_, fun V hV x hx => ?_⟩
  · have := h _ rfl; revert this; decide
  · have h0 := hV x hx
    match x, h0 with
    | [], _ => exact bytesLe_refl []

/-- Strips provenance from pointer fragments (what a register without provenance would do). -/
def stripProv (bs : List AByte) : List AByte :=
  bs.map fun b => match b with | .ptrFrag d _ _ => .bits d | b => b

/-- The `union` result depends on the modelling assumption that a union register holds
fragments: a register that stripped provenance would not refine a fragment-carrying byte. -/
theorem provenanceStripping_register_not_refines :
    ¬ BytesLe [.ptrFrag 1 7 0] (stripProv [.ptrFrag 1 7 0]) := by decide

/-! ## Reinterpretation -/

/-- `hw` (equal widths) cannot be dropped from `regCast_scalar_agrees_iff_disciplineCompat`:
a 1-byte `initialized` integer reinterpreted as a 2-byte one, with compatible disciplines,
disagrees with the memory transmute. -/
theorem cex_regCast_scalar_width_mismatch :
    (Scalar.initialized (.int 1) fullRange).size ≠ (Scalar.initialized (.int 2) fullRange).size ∧
      1 ≤ (Scalar.initialized (.int 1) fullRange).size ∧
      (Scalar.initialized (.int 1) fullRange).size ≤ 2 ∧
      DisciplineCompat (.initialized (.int 1) fullRange) (.initialized (.int 2) fullRange) ∧
      ¬ CastAgrees 2 (.scalar (.initialized (.int 1) fullRange))
        (.scalar (.initialized (.int 2) fullRange)) := by
  refine ⟨by decide, by decide, by decide, fun _ _ _ => rfl, fun h => ?_⟩
  have := h [.bits 1, .bits 2] rfl
  revert this; decide

/-- `hpos` cannot be dropped from the `→` direction: at width `0`, a `union` to `initialized`
reinterpretation agrees with the memory transmute although the disciplines are not
compatible. -/
theorem cex_regCast_scalar_width_zero :
    (Scalar.union (.int 0)).size = (Scalar.initialized (.int 0) fullRange).size ∧
      ¬ 1 ≤ (Scalar.union (.int 0)).size ∧ (Scalar.union (.int 0)).size ≤ 1 ∧
      CastAgrees 1 (.scalar (.union (.int 0))) (.scalar (.initialized (.int 0) fullRange)) ∧
      ¬ DisciplineCompat (.union (.int 0)) (.initialized (.int 0) fullRange) := by
  refine ⟨rfl, by decide, by decide, ?_, id⟩
  intro x hx
  match x, hx with
  | [_], _ => rfl

/-- `hn` (width at most `n`) cannot be dropped from the `→` direction, even for ranges that do
not depend on the data length: at `n = 0` every reinterpretation agrees (there is no byte), while
the full range is not included in the non-zero range. -/
theorem cex_regCast_scalar_hn_length_indep :
    let s : Scalar := .initialized (.int 1) fullRange
    let t : Scalar := .initialized (.int 1) nonZeroRange
    s.size = t.size ∧ 1 ≤ s.size ∧ ¬ s.size ≤ 0 ∧
      CastAgrees 0 (.scalar s) (.scalar t) ∧ ¬ DisciplineCompat s t := by
  refine ⟨rfl, by decide, by decide, ?_, ?_⟩
  · intro x hx
    match x, hx with
    | [], _ => rfl
  · intro h; have := h [0] rfl rfl; revert this; decide

/-- `hn` cannot be dropped from the `←` direction with `n ≥ 1`, for a range that depends
on the data length: a reinterpretation into a narrower value disagrees although the disciplines
are compatible on full-width data. -/
theorem cex_regCast_scalar_wider_than_value :
    (Scalar.initialized (.int 2) fullRange).size = (Scalar.initialized (.int 2) len2Range).size ∧
      1 ≤ (Scalar.initialized (.int 2) fullRange).size ∧
      ¬ (Scalar.initialized (.int 2) fullRange).size ≤ 1 ∧
      DisciplineCompat (.initialized (.int 2) fullRange) (.initialized (.int 2) len2Range) ∧
      ¬ CastAgrees 1 (.scalar (.initialized (.int 2) fullRange))
        (.scalar (.initialized (.int 2) len2Range)) := by
  refine ⟨rfl, by decide, by decide, fun ds hl _ => by simp [len2Range, hl, Prim.size], fun h => ?_⟩
  have := h [.bits 5] rfl
  revert this; decide

/-- Sensitivity of `regCast_scalar_agrees_iff_disciplineCompat` to `regCastScalar` keeping
provenance fragments of a `raw` register in an `initialized` integer target: a variant that strips
provenance on that cast. -/
def regCastScalarStrip (s t : Scalar) (v : RVal) : RVal :=
  match t with
  | .union _ => .raw (raiseScalar s v)
  | .initialized q _ =>
    match v, q with
    | .poison, _ => .poison
    | .int ds, .int _ => .int ds
    | .int ds, .ptr _ => .ptr none ds
    | .ptr _ ds, .int _ => .int ds
    | .ptr pr ds, .ptr _ => .ptr pr ds
    | .raw bs, .int _ => .raw (stripProv bs)
    | .raw bs, .ptr _ => .raw bs

/-- Under `regCastScalarStrip`, a 1-byte `union` integer cast to a 1-byte `initialized` integer
with the full range agrees with the memory transmute on every 1-byte value, although the
disciplines are not compatible: at width `1`, the `→` direction of
`regCast_scalar_agrees_iff_disciplineCompat` rests on `regCastScalar` keeping fragments. -/
theorem regCastStrip_width1_union_to_initialized_agrees :
    let s : Scalar := .union (.int 1)
    let t : Scalar := .initialized (.int 1) fullRange
    (∀ x : List AByte, x.length = 1 →
      raise 1 (.scalar t) (.one (regCastScalarStrip s t (lowerScalar s (seg x 0 s.size)))) =
        raise 1 (.scalar t) (lower (.scalar t) (raise 1 (.scalar s) (lower (.scalar s) x)))) ∧
    ¬ DisciplineCompat s t := by
  refine ⟨fun x hx => ?_, id⟩
  match x, hx with
  | [b], _ => cases b <;> rfl

/-- One-sided refinement holds where agreement fails: a `union` to `initialized` reinterpretation
(1 byte) refines the memory transmute but does not agree with it. -/
theorem regCast_union_to_initialized_refines_not_agrees :
    let s : Scalar := .union (.int 1)
    let t : Scalar := .initialized (.int 1) fullRange
    s.size = t.size ∧ s.size ≤ 1 ∧ ¬ DisciplineCompat s t ∧
      CastRefines 1 (.scalar s) (.scalar t) ∧ ¬ CastAgrees 1 (.scalar s) (.scalar t) := by
  intro s t
  refine ⟨rfl, by decide, id, regCast_scalar_refines_transmute 1 s t,
    fun h => ?_⟩
  have := h [.ptrFrag 0 0 1] rfl
  revert this; decide

/-- Offset equality cannot be dropped from `regCast_pair_agrees_of_offsetEq_disciplineCompat`:
pairs whose `b` offsets differ (`1` versus `2`) disagree with the memory transmute, although
every other hypothesis holds for each offset. -/
theorem cex_regCast_pair_offset_mismatch :
    let a : Scalar := .initialized (.int 1) fullRange
    a.size = a.size ∧ a.size ≤ 1 ∧ a.size ≤ 2 ∧ 1 + a.size ≤ 3 ∧ 2 + a.size ≤ 3 ∧
      DisciplineCompat a a ∧ ¬ CastAgrees 3 (.pair a a 1) (.pair a a 2) := by
  intro a
  refine ⟨rfl, by decide, by decide, by decide, by decide, fun _ _ _ => rfl, fun h => ?_⟩
  have := h [.bits 1, .bits 2, .uninit] rfl
  revert this; decide

/-- The empty range: no data vector. -/
def emptyRange : List Nat → Bool := fun _ => false

/-- The converse of `regCast_pair_agrees_of_offsetEq_disciplineCompat` fails in general: when the
source `b` component has an empty range (it always lowers to poison), pairs whose `b` offsets
differ (`1` versus `2`) still agree with the memory transmute on every 3-byte value. -/
theorem regCast_pair_agrees_despite_offset_mismatch_of_empty_range :
    let a : Scalar := .initialized (.int 1) fullRange
    let e : Scalar := .initialized (.int 1) emptyRange
    CastAgrees 3 (.pair a e 1) (.pair a a 2) := by
  intro a e x hx
  match x, hx with
  | [x0, x1, _], _ => cases x0 <;> cases x1 <;> rfl

/-- Discipline compatibility of the `a` components cannot be dropped (pair): a `union` component
reinterpreted as an `initialized` one, all other hypotheses holding. -/
theorem cex_regCast_pair_discipline :
    let u : Scalar := .union (.int 1)
    let i : Scalar := .initialized (.int 1) fullRange
    u.size = i.size ∧ i.size = i.size ∧ u.size ≤ 1 ∧ 1 + i.size ≤ 2 ∧ DisciplineCompat i i ∧
      ¬ DisciplineCompat u i ∧ ¬ CastAgrees 2 (.pair u i 1) (.pair i i 1) := by
  intro u i
  refine ⟨rfl, rfl, by decide, by decide, fun _ _ _ => rfl, id, fun h => ?_⟩
  have := h [.ptrFrag 0 0 1, .bits 0] rfl
  revert this; decide

/-- Discipline compatibility of the `b` components cannot be dropped (pair). -/
theorem cex_regCast_pair_discipline_b :
    let u : Scalar := .union (.int 1)
    let i : Scalar := .initialized (.int 1) fullRange
    i.size = i.size ∧ u.size = i.size ∧ i.size ≤ 1 ∧ 1 + u.size ≤ 2 ∧ DisciplineCompat i i ∧
      ¬ DisciplineCompat u i ∧ ¬ CastAgrees 2 (.pair i u 1) (.pair i i 1) := by
  intro u i
  refine ⟨rfl, rfl, by decide, by decide, fun _ _ _ => rfl, id, fun h => ?_⟩
  have := h [.bits 0, .ptrFrag 0 0 1] rfl
  revert this; decide

/-- Disjointness cannot be dropped (pair reinterpretation): with overlapping extents, an
identity reinterpretation disagrees with the memory transmute. -/
theorem cex_regCast_pair_overlap :
    let a : Scalar := .initialized (.int 2) fullRange
    let b : Scalar := .initialized (.ptr 2) fullRange
    a.size = a.size ∧ b.size = b.size ∧ DisciplineCompat a a ∧ DisciplineCompat b b ∧
      ¬ a.size ≤ 1 ∧ 1 + b.size ≤ 3 ∧ ¬ CastAgrees 3 (.pair a b 1) (.pair a b 1) := by
  intro a b
  refine ⟨rfl, rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, by decide, by decide, fun h => ?_⟩
  have := h [.bits 0, .ptrFrag 1 7 0, .ptrFrag 2 7 1] rfl
  revert this; decide

/-- In-bounds (`hbn`) cannot be dropped from the pair reinterpretation result, for a range that
depends on the data length. -/
theorem cex_regCast_pair_out_of_bounds :
    let a : Scalar := .initialized (.int 1) fullRange
    let b : Scalar := .initialized (.int 2) fullRange
    let b' : Scalar := .initialized (.int 2) len2Range
    a.size = a.size ∧ b.size = b'.size ∧ DisciplineCompat a a ∧ DisciplineCompat b b' ∧
      a.size ≤ 1 ∧ ¬ 1 + b.size ≤ 2 ∧ ¬ CastAgrees 2 (.pair a b 1) (.pair a b' 1) := by
  intro a b b'
  refine ⟨rfl, rfl, fun _ _ _ => rfl,
    fun ds hl _ => by simp [len2Range, hl, Prim.size], by decide, by decide, fun h => ?_⟩
  have := h [.bits 0, .bits 1] rfl
  revert this; decide

/-- Equal widths (`hwa`) cannot be dropped from the pair reinterpretation result. -/
theorem cex_regCast_pair_width_mismatch :
    let a : Scalar := .initialized (.int 1) fullRange
    let a' : Scalar := .initialized (.int 2) fullRange
    a.size ≠ a'.size ∧ a.size = a.size ∧ DisciplineCompat a a' ∧ DisciplineCompat a a ∧
      a.size ≤ 2 ∧ 2 + a.size ≤ 3 ∧ ¬ CastAgrees 3 (.pair a a 2) (.pair a' a 2) := by
  intro a a'
  refine ⟨by decide, rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, by decide, by decide, fun h => ?_⟩
  have := h [.bits 1, .bits 9, .bits 2] rfl
  revert this; decide

/-- Equal widths (`hwb`) cannot be dropped from the pair reinterpretation result. -/
theorem cex_regCast_pair_width_mismatch_b :
    let a : Scalar := .initialized (.int 1) fullRange
    let b' : Scalar := .initialized (.int 2) fullRange
    a.size = a.size ∧ a.size ≠ b'.size ∧ DisciplineCompat a a ∧ DisciplineCompat a b' ∧
      a.size ≤ 1 ∧ 1 + a.size ≤ 3 ∧ ¬ CastAgrees 3 (.pair a a 1) (.pair a b' 1) := by
  intro a b'
  refine ⟨rfl, by decide, fun _ _ _ => rfl, fun _ _ _ => rfl, by decide, by decide, fun h => ?_⟩
  have := h [.bits 1, .bits 2, .bits 3] rfl
  revert this; decide

/-- **A pair-to-`union`-scalar reinterpretation across padding disagrees with the memory
transmute.** A pair of 1-byte integers at offsets `0` and `2` (byte `1` is padding) of a 3-byte
value, reinterpreted by concatenating the two registers into one 2-byte `union` scalar at offset
`0`: the register path yields `[bits 1, bits 2, uninit]`, while the memory path yields
`[bits 1, uninit, uninit]` (the 2-byte `union` scalar reads the padding byte, not `b`). -/
theorem regCast_pair_to_union_scalar_across_padding_disagrees :
    let a : Scalar := .initialized (.int 1) fullRange
    let t : Scalar := .union (.int 2)
    let x : List AByte := [.bits 1, .uninit, .bits 2]
    raise 3 (.scalar t) (regCast (.pair a a 2) (.scalar t) (lower (.pair a a 2) x)) =
        [.bits 1, .bits 2, .uninit] ∧
      raise 3 (.scalar t) (lower (.scalar t) (raise 3 (.pair a a 2) (lower (.pair a a 2) x))) =
        [.bits 1, .uninit, .uninit] ∧
      ¬ CastAgrees 3 (.pair a a 2) (.scalar t) := by
  intro a t x
  refine ⟨by decide, by decide, fun h => ?_⟩
  have := h x rfl
  revert this; decide

/-- An instance of `regCast_pair_to_union_scalar_agrees_of_no_padding`: two 1-byte integers at
offsets `0` and `1` of a 2-byte value, concatenated into a 2-byte `union` scalar. -/
theorem regCast_pair_to_union_scalar_agrees_no_padding_instance :
    let a : Scalar := .initialized (.int 1) fullRange
    (Prim.int 2).size = a.size + a.size ∧ a.size + a.size ≤ 2 ∧
      CastAgrees 2 (.pair a a a.size) (.scalar (.union (.int 2))) := by
  intro a
  exact ⟨rfl, by decide, regCast_pair_to_union_scalar_agrees_of_no_padding 2 a a (.int 2) rfl
    (by decide)⟩

/-- A cast that attaches a provenance `p` to an integer (as a provenance-picking
integer-to-pointer cast would) instead of reinterpreting it. -/
def attachProvCast (p : Nat) : RVal → RVal
  | .int ds => .ptr (some p) ds
  | v => v

/-- **Attaching provenance is not the reinterpretation.** For a 1-byte integer `5`, the
memory transmute to a 1-byte pointer scalar yields the provenance-free byte `bits 5`, which
`regCast` reproduces, while `attachProvCast 7` yields the fragment `ptrFrag 5 7 0`. -/
theorem provenanceAttachingCast_differs_from_transmute :
    let s : Scalar := .initialized (.int 1) fullRange
    let t : Scalar := .initialized (.ptr 1) fullRange
    raise 1 (.scalar t) (lower (.scalar t) (raise 1 (.scalar s) (lower (.scalar s) [.bits 5]))) =
        [.bits 5] ∧
      raise 1 (.scalar t) (regCast (.scalar s) (.scalar t) (lower (.scalar s) [.bits 5])) =
        [.bits 5] ∧
      raise 1 (.scalar t) (.one (attachProvCast 7 (lowerScalar s [.bits 5]))) =
        [.ptrFrag 5 7 0] := by
  decide

/-- In the definedness order, the provenance-attaching result is above the transmute's result:
`[bits 5] ⊑ [ptrFrag 5 7 0]`. -/
theorem bytesLe_bits_ptrFrag_attach : BytesLe [.bits 5] [.ptrFrag 5 7 0] := by decide

/-! ## Unions -/

/-- Non-vacuity of `unionMove_trivial_defined_iff_size_and_readField_ub_iff_invalid`: in
`nzOrU8`, the byte list `[bits 0]` has the union's size and moves without UB, and reading the
`NonZeroU8` field is UB because the field's bytes are invalid. -/
theorem nonvacuous_unionMove_readField :
    [AByte.bits 0].length = nzOrU8.size ∧
      unionMove trivialUnionValidity nzOrU8 [.bits 0] = some [.bits 0] ∧
      readField nonZeroU8Field [.bits 0] = none ∧
      nonZeroU8Field.valid (seg [.bits 0] nonZeroU8Field.off nonZeroU8Field.size) = false := by
  decide

/-- Non-vacuity of `unreachableRewrite_refines_iff_no_wholeValue_valid`: the always-firing gate
on `neverUnion` under empty and under trivial whole-value validity (both sides true, respectively
both sides false). -/
theorem nonvacuous_unreachableRewrite_iff :
    (fun _ => true : UnionTy → Bool) neverUnion = true ∧
      (∀ x : List AByte, x.length = neverUnion.size → emptyUnionValidity neverUnion x = false) ∧
      ¬ (∀ x : List AByte, x.length = neverUnion.size →
        trivialUnionValidity neverUnion x = false) := by
  refine ⟨rfl, fun _ _ => rfl, fun h => ?_⟩
  have := h [.uninit] rfl
  revert this; decide

/-- `hgate` cannot be dropped from `unreachableRewrite_refines_iff_no_wholeValue_valid`: with a gate
that does not fire, the program is unchanged and refines itself, while trivial whole-value
validity admits a value of `neverUnion`'s size. -/
theorem cex_unreachableRewrite_gate_false :
    (fun _ => false : UnionTy → Bool) neverUnion ≠ true ∧
      (∀ x : List AByte, x.length = neverUnion.size →
        OutLe (moveThenRet trivialUnionValidity neverUnion x)
          (gatedUnreachable ((fun _ => false : UnionTy → Bool) neverUnion)
            (moveThenRet trivialUnionValidity neverUnion x))) ∧
      ¬ (∀ x : List AByte, x.length = neverUnion.size →
        trivialUnionValidity neverUnion x = false) := by
  refine ⟨by decide, fun x hx => ?_, fun h => ?_⟩
  · match x, hx with
    | [_], _ => simp [moveThenRet, unionMove, trivialUnionValidity, gatedUnreachable, OutLe,
        neverUnion, Val.leb]
  · have := h [.uninit] rfl
    revert this; decide

/-- Non-vacuity of `fieldwiseUninhabited_gate_not_refinement_of_trivialValidity`: the
always-firing gate fires on every `FieldwiseUninhabited` union. -/
theorem nonvacuous_fieldwiseGate :
    ∀ u, FieldwiseUninhabited u → (fun _ => true : UnionTy → Bool) u = true :=
  fun _ _ => rfl

/-- `hgate` cannot be dropped from
`fieldwiseUninhabited_gate_not_refinement_of_trivialValidity`: the never-firing gate does not fire
on the `FieldwiseUninhabited` union `neverUnion`, and the (unchanged) program refines itself. -/
theorem cex_fieldwiseGate_never_fires :
    ¬ (∀ u, FieldwiseUninhabited u → (fun _ => false : UnionTy → Bool) u = true) ∧
      OutLe (moveThenRet trivialUnionValidity neverUnion [.uninit])
        (gatedUnreachable ((fun _ => false : UnionTy → Bool) neverUnion)
          (moveThenRet trivialUnionValidity neverUnion [.uninit])) := by
  refine ⟨fun h => ?_, by decide⟩
  have hf : FieldwiseUninhabited neverUnion := by
    intro f hf bs
    simp [neverUnion] at hf
    subst hf
    rfl
  exact absurd (h _ hf) (by decide)

/-- Positive control for `fieldwiseUninhabited_gate_not_refinement_of_trivialValidity`: under
empty whole-value validity, every gate that fires on `neverUnion` gives a refinement on every
byte list of its size. -/
theorem gate_refines_of_emptyValidity (gate : UnionTy → Bool) (hgate : gate neverUnion = true) :
    ∀ x : List AByte, x.length = neverUnion.size →
      OutLe (moveThenRet emptyUnionValidity neverUnion x)
        (gatedUnreachable (gate neverUnion) (moveThenRet emptyUnionValidity neverUnion x)) :=
  (unreachableRewrite_refines_iff_no_wholeValue_valid emptyUnionValidity neverUnion gate hgate).2
    (fun _ _ => rfl)

/-- `hp` cannot be dropped from `noundef_on_union_scalar_introduces_ub`: at width `0` the
all-`uninit` value is empty and passes `noundef`. -/
theorem cex_noundef_width_zero :
    ¬ 1 ≤ (Prim.int 0).size ∧
      passArg true (lowerScalar (.union (.int 0)) (List.replicate (Prim.int 0).size .uninit)) ≠
        none := by
  decide

/-- An all-`uninit` value satisfies every condition of `scalar_roundTrip_refines_iff` for a
1-byte `initialized` integer scalar and round-trips, yet its lowered register (`poison`) trips
`noundef`. -/
theorem initialized_allUninit_roundTrips_but_noundef_ub :
    let s : Scalar := .initialized (.int 1) fullRange
    let V : List AByte → Prop := (· = [.uninit])
    (∀ x, V x → x.length = 1) ∧ RoundTripRefines 1 (.scalar s) V ∧
      OutsideExtentsUninit 1 (.scalar s) V ∧ InitUniform (.scalar s) V ∧
      RangeIncl (.scalar s) V ∧ ProvCoherent (.scalar s) V ∧
      lowerScalar s [.uninit] = .poison ∧ passArg true (lowerScalar s [.uninit]) = none := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide⟩ <;> (intro x hx; cases hx; decide)

/-! ## Typed reads -/

/-- The premise `BytesLe x y` cannot be dropped from `typedReads_mono_of_bytesLe`: an
initialized byte replaced by `uninit` makes a typed read less defined. -/
theorem cex_typedReads_without_bytesLe :
    ¬ BytesLe [.bits 1] [.uninit] ∧ ¬ OutLe (readInt 0 1 [.bits 1]) (readInt 0 1 [.uninit]) := by
  decide

/-- The converse of `typedReads_mono_of_bytesLe` fails: a stray fragment `ptrFrag 1 7 1` and the
plain byte `bits 1` give equal typed integer and pointer reads at every offset and width, yet the
fragment is not below the plain byte. -/
theorem typedReads_agree_without_bytesLe :
    (∀ off w : Nat, readInt off w [.ptrFrag 1 7 1] = readInt off w [.bits 1] ∧
      readPtr off w [.ptrFrag 1 7 1] = readPtr off w [.bits 1]) ∧
      ¬ BytesLe [.ptrFrag 1 7 1] [.bits 1] := by
  refine ⟨fun off w => ?_, by decide⟩
  rcases off with _ | off
  · rcases w with _ | w
    · decide
    · simp [readInt, readPtr, seg, allInit, AByte.isInit, datas, AByte.data, ptrProv, fragProv,
        fragsFrom]
  · simp [readInt, readPtr, seg]

/-- Degenerate edge of the typed reads: at width `0` both reads return an empty value at every
offset, including offsets past the end of the byte list. -/
theorem readInt_readPtr_width_zero (off : Nat) (x : List AByte) :
    readInt off 0 x = some (.int []) ∧ readPtr off 0 x = some (.ptr none []) := by
  simp [readInt, readPtr, seg, allInit, datas, ptrProv, fragProv]

/-! ## Non-vacuity witnesses -/

/-- Non-vacuity of `scalar_roundTrip_refines_iff`: a 2-byte `initialized` pointer scalar in a
3-byte value whose last byte is `uninit` padding, holding one pointer's fragments; the hypothesis
holds and both sides are true. -/
theorem nonvacuous_scalar_roundTrip :
    let s : Scalar := .initialized (.ptr 2) fullRange
    let V : List AByte → Prop := (· = [.ptrFrag 1 7 0, .ptrFrag 2 7 1, .uninit])
    (∀ x, V x → x.length = 3) ∧ RoundTripRefines 3 (.scalar s) V ∧
      OutsideExtentsUninit 3 (.scalar s) V ∧ InitUniform (.scalar s) V ∧
      RangeIncl (.scalar s) V ∧ ProvCoherent (.scalar s) V := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro x hx; cases hx; decide)

/-- Non-vacuity of `pair_roundTrip_refines_iff`: a (pointer, length) pair at offsets `0` and `3`
of a 5-byte value with one `uninit` padding byte, holding a pointer with provenance and an
integer. -/
theorem nonvacuous_pair_roundTrip :
    let a : Scalar := .initialized (.ptr 2) nonZeroRange
    let b : Scalar := .initialized (.int 2) fullRange
    let V : List AByte → Prop :=
      (· = [.ptrFrag 1 7 0, .ptrFrag 2 7 1, .uninit, .bits 3, .bits 0])
    (∀ x, V x → x.length = 5) ∧ a.size ≤ 3 ∧
      RoundTripRefines 5 (.pair a b 3) V ∧ OutsideExtentsUninit 5 (.pair a b 3) V ∧
      InitUniform (.pair a b 3) V ∧ RangeIncl (.pair a b 3) V ∧ ProvCoherent (.pair a b 3) V := by
  refine ⟨?_, by decide, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro x hx; cases hx; decide)

/-- Non-vacuity of `union_scalar_roundTrip_refines_iff_outsideExtentsUninit`: a partially
initialized, fragment-carrying value of a 3-byte `union` scalar in a 4-byte value whose last byte
is `uninit`. -/
theorem nonvacuous_union_roundTrip :
    let V : List AByte → Prop := (· = [.ptrFrag 1 7 0, .uninit, .bits 4, .uninit])
    (∀ x, V x → x.length = 4) ∧
      RoundTripRefines 4 (.scalar (.union (.int 3))) V ∧
      OutsideExtentsUninit 4 (.scalar (.union (.int 3))) V := by
  refine ⟨?_, ?_, ?_⟩ <;> (intro x hx; cases hx; decide)

/-- Non-vacuity of `union_scalar_roundTrip_refines_of_covers_value`: a partially initialized,
fragment-carrying value of a 3-byte `union` scalar covering the 3-byte value. -/
theorem nonvacuous_union_covers_value :
    let V : List AByte → Prop := (· = [.ptrFrag 1 7 0, .uninit, .bits 4])
    (∀ x, V x → x.length = 3) ∧ 3 ≤ (Prim.int 3).size ∧
      RoundTripRefines 3 (.scalar (.union (.int 3))) V := by
  refine ⟨?_, by decide, ?_⟩ <;> (intro x hx; cases hx; decide)

/-- Non-vacuity of `typedReads_mono_of_bytesLe`. -/
theorem nonvacuous_typedReads_mono : BytesLe [.uninit, .bits 1] [.bits 0, .ptrFrag 1 7 0] := by
  decide

/-- Non-vacuity of `regCast_scalar_agrees_iff_disciplineCompat`: a pointer-to-integer
reinterpretation (2 bytes) satisfies the hypotheses and both sides hold. -/
theorem nonvacuous_regCast_scalar :
    let s : Scalar := .initialized (.ptr 2) nonZeroRange
    let t : Scalar := .initialized (.int 2) fullRange
    s.size = t.size ∧ 1 ≤ s.size ∧ s.size ≤ 2 ∧ DisciplineCompat s t ∧
      CastAgrees 2 (.scalar s) (.scalar t) := by
  intro s t
  have hc : DisciplineCompat s t := fun _ _ _ => rfl
  exact ⟨rfl, by decide, by decide, hc,
    (regCast_scalar_agrees_iff_disciplineCompat 2 s t rfl (by decide) (by decide)).2 hc⟩

/-- Integer-to-pointer reinterpretation agrees with the memory transmute (an instance of
`regCast_scalar_agrees_iff_disciplineCompat`). -/
theorem regCast_int_to_ptr_agrees :
    CastAgrees 2 (.scalar (.initialized (.int 2) fullRange))
      (.scalar (.initialized (.ptr 2) fullRange)) :=
  (regCast_scalar_agrees_iff_disciplineCompat 2 (.initialized (.int 2) fullRange)
    (.initialized (.ptr 2) fullRange) rfl (by decide) (by decide)).2 (fun _ _ _ => rfl)

/-- Non-vacuity of `regCast_pair_agrees_of_offsetEq_disciplineCompat`: a (pointer, integer) pair
reinterpreted as an (integer, union) pair. -/
theorem nonvacuous_regCast_pair :
    let a : Scalar := .initialized (.ptr 2) nonZeroRange
    let b : Scalar := .initialized (.int 2) fullRange
    let a' : Scalar := .initialized (.int 2) fullRange
    let b' : Scalar := .union (.int 2)
    a.size = a'.size ∧ b.size = b'.size ∧ a.size ≤ 2 ∧ 2 + b.size ≤ 4 ∧
      DisciplineCompat a a' ∧ DisciplineCompat b b' ∧
      CastAgrees 4 (.pair a b 2) (.pair a' b' 2) := by
  intro a b a' b'
  have hca : DisciplineCompat a a' := fun _ _ _ => rfl
  have hcb : DisciplineCompat b b' := trivial
  exact ⟨rfl, rfl, by decide, by decide, hca, hcb,
    regCast_pair_agrees_of_offsetEq_disciplineCompat 4 a b a' b' 2 rfl rfl (by decide) (by decide)
      hca hcb⟩

/-- Non-vacuity of `regCast_pair_agrees_of_offsetEq_disciplineCompatAnyLen`: a pair whose `b`
extent runs past the end of a 3-byte value (`2 + 2 > 3`), with length-independent ranges. -/
theorem nonvacuous_regCast_pair_anyLen :
    let a : Scalar := .initialized (.int 1) fullRange
    let b : Scalar := .initialized (.int 2) nonZeroRange
    let b' : Scalar := .initialized (.int 2) fullRange
    a.size = a.size ∧ b.size = b'.size ∧ a.size ≤ 2 ∧ ¬ 2 + b.size ≤ 3 ∧
      DisciplineCompatAnyLen a a ∧ DisciplineCompatAnyLen b b' ∧
      CastAgrees 3 (.pair a b 2) (.pair a b' 2) := by
  intro a b b'
  have hca : DisciplineCompatAnyLen a a := fun _ _ => rfl
  have hcb : DisciplineCompatAnyLen b b' := fun _ _ => rfl
  exact ⟨rfl, rfl, by decide, by decide, hca, hcb,
    regCast_pair_agrees_of_offsetEq_disciplineCompatAnyLen 3 a b a b' 2 rfl rfl (by decide)
      hca hcb⟩

/-- Non-vacuity of `writeBytes_frame` (no hypotheses): a write inside the value and a write that
runs past its end. -/
theorem nonvacuous_writeBytes_frame :
    writeBytes [.bits 7, .uninit, .bits 9] 1 [.bits 1] = [.bits 7, .bits 1, .bits 9] ∧
      writeBytes [.bits 7] 0 [.bits 1, .bits 2] = [.bits 1] := by
  decide

/-- Non-vacuity of `readWider_after_partial_write`: writing one byte at offset `1` of
`[bits 7, uninit, bits 9]` and reading three bytes at offset `0`; byte `1` (written) and byte `2`
(untouched) of the read, with `hj` and `hin` holding for both. -/
theorem nonvacuous_readWider :
    (1 : Nat) < 3 ∧ 0 + 1 < [AByte.bits 7, .uninit, .bits 9].length ∧
      (seg (writeBytes [.bits 7, .uninit, .bits 9] 1 [.bits 1]) 0 3).getD 1 .uninit = .bits 1 ∧
      (2 : Nat) < 3 ∧ 0 + 2 < [AByte.bits 7, .uninit, .bits 9].length ∧
      (seg (writeBytes [.bits 7, .uninit, .bits 9] 1 [.bits 1]) 0 3).getD 2 .uninit = .bits 9 := by
  decide

/-- `hj : j < k` cannot be dropped from `readWider_after_partial_write`. -/
theorem cex_readWider_hj :
    ¬ (1 : Nat) < 1 ∧ (0 : Nat) + 1 < [AByte.bits 7, .bits 9].length ∧
      (seg (writeBytes [.bits 7, .bits 9] 0 [.bits 1]) 0 1).getD 1 .uninit ≠
        (if 0 ≤ 0 + 1 ∧ 0 + 1 < 0 + [AByte.bits 1].length then [AByte.bits 1].getD (0 + 1 - 0) .uninit
          else [AByte.bits 7, .bits 9].getD (0 + 1) .uninit) := by
  decide

/-- `hin : o' + j < x.length` cannot be dropped from `readWider_after_partial_write`. -/
theorem cex_readWider_hin :
    (0 : Nat) < 1 ∧ ¬ (0 : Nat) + 0 < ([] : List AByte).length ∧
      (seg (writeBytes [] 0 [AByte.bits 1]) 0 1).getD 0 .uninit ≠
        (if 0 ≤ 0 + 0 ∧ 0 + 0 < 0 + [AByte.bits 1].length then [AByte.bits 1].getD (0 + 0 - 0) .uninit
          else ([] : List AByte).getD (0 + 0) .uninit) := by
  decide

/-- Non-vacuity of `unionRegister_mergeWrite_eq_memoryWrite`: a 2-byte `union` register and a
2-byte value, one byte written at offset `1`. -/
theorem nonvacuous_mergeWrite :
    2 ≤ (Prim.int 2).size ∧ [AByte.bits 7, .uninit].length = 2 ∧
      raise 2 (.scalar (.union (.int 2)))
          (.one (mergeWrite (lowerScalar (.union (.int 2)) (seg [.bits 7, .uninit] 0 2)) 1 [.bits 1]))
        = [.bits 7, .bits 1] := by
  decide

/-- `hn : n ≤ p.size` cannot be dropped from `unionRegister_mergeWrite_eq_memoryWrite`: with a
1-byte `union` register in a 2-byte value, the byte outside the register is lost. -/
theorem cex_mergeWrite_size_lt :
    ¬ 2 ≤ (Prim.int 1).size ∧ [AByte.bits 7, .bits 9].length = 2 ∧
      raise 2 (.scalar (.union (.int 1)))
          (.one (mergeWrite (lowerScalar (.union (.int 1)) (seg [.bits 7, .bits 9] 0 1)) 0 [.bits 1]))
        ≠ writeBytes [.bits 7, .bits 9] 0 [.bits 1] := by
  decide

/-- `hx : x.length = n` cannot be dropped from `unionRegister_mergeWrite_eq_memoryWrite`. -/
theorem cex_mergeWrite_hx :
    1 ≤ (Prim.int 1).size ∧ ([] : List AByte).length ≠ 1 ∧
      raise 1 (.scalar (.union (.int 1)))
          (.one (mergeWrite (lowerScalar (.union (.int 1)) (seg [] 0 1)) 0 [.bits 1]))
        ≠ writeBytes [] 0 [.bits 1] := by
  decide

/-- Non-vacuity of `memory_roundTrip_refines`: a partially initialized, fragment-carrying value. -/
theorem nonvacuous_memory_roundTrip :
    RoundTripRefines 2 .memory (· = [.ptrFrag 1 7 0, .uninit]) :=
  memory_roundTrip_refines 2 _

/-- The two fills `uninit` and `bits 0` in detail: in a two-byte union holding
`[bits 7, bits 9]`, writing `bits 1` at offset `0` and reading both bytes gives `[1, 9]`; after
the whole-register write with `uninit` fill the read is UB, and with `bits 0` fill it gives
`[1, 0]`. -/
theorem wholeRegisterWrite_uninit_and_zero_fills_instance :
    readInt 0 2 (writeBytes [.bits 7, .bits 9] 0 [.bits 1]) = some (.int [1, 9]) ∧
    readInt 0 2 (raiseScalar (.union (.int 2)) (wholeWrite 2 .uninit 0 [.bits 1])) = none ∧
    readInt 0 2 (raiseScalar (.union (.int 2)) (wholeWrite 2 (.bits 0) 0 [.bits 1])) =
      some (.int [1, 0]) := by
  decide

/-- An instance of `wholeWrite_uninit_eq_writeBytes_of_untouched_uninit`: the untouched byte of
`[bits 7, uninit]` is already `uninit`. -/
theorem wholeWrite_untouched_uninit_instance :
    raiseScalar (.union (.int 2)) (wholeWrite 2 .uninit 0 [.bits 1]) =
      writeBytes [.bits 7, .uninit] 0 [.bits 1] := by
  decide

/-- An instance of `wholeWrite_eq_writeBytes_of_full_width`: a two-byte write at offset `0` into
a two-byte register, with fill `bits 0`. -/
theorem wholeWrite_full_width_instance :
    raiseScalar (.union (.int 2)) (wholeWrite 2 (.bits 0) 0 [.bits 1, .bits 2]) =
      writeBytes [.bits 7, .bits 9] 0 [.bits 1, .bits 2] := by
  decide

/-- Non-vacuity of `noundef_on_union_scalar_introduces_ub`: the 1-byte integer primitive. -/
theorem nonvacuous_noundef_union :
    1 ≤ (Prim.int 1).size ∧
      passArg false (lowerScalar (.union (.int 1)) (List.replicate (Prim.int 1).size .uninit)) =
        some (lowerScalar (.union (.int 1)) (List.replicate (Prim.int 1).size .uninit)) ∧
      passArg true (lowerScalar (.union (.int 1)) (List.replicate (Prim.int 1).size .uninit)) =
        none := by
  decide

/-- Non-vacuity of `noundef_passes_initialized_nonpoison`: an initialized 1-byte integer. -/
theorem nonvacuous_noundef_initialized :
    lowerScalar (.initialized (.int 1) fullRange) [.bits 1] ≠ .poison ∧
      passArg true (lowerScalar (.initialized (.int 1) fullRange) [.bits 1]) =
        some (lowerScalar (.initialized (.int 1) fullRange) [.bits 1]) := by
  decide

/-- `regCast_scalar_refines_transmute` beyond equal widths and beyond extents inside the value:
for 1- and 2-byte `initialized` integers, both reinterpretations between unequal widths refine
the memory transmute on 2-byte values while one of them does not agree with it; and a 2-byte
scalar reinterpreted on 1-byte values (extent wider than the value) refines without agreeing. -/
theorem castRefines_unequal_widths_and_wider_than_value :
    let s1 : Scalar := .initialized (.int 1) fullRange
    let s2 : Scalar := .initialized (.int 2) fullRange
    let s2len : Scalar := .initialized (.int 2) len2Range
    (s1.size ≠ s2.size ∧ CastRefines 2 (.scalar s1) (.scalar s2) ∧
      CastRefines 2 (.scalar s2) (.scalar s1) ∧ ¬ CastAgrees 2 (.scalar s2) (.scalar s1)) ∧
    (¬ s2.size ≤ 1 ∧ CastRefines 1 (.scalar s2) (.scalar s2len) ∧
      ¬ CastAgrees 1 (.scalar s2) (.scalar s2len)) := by
  intro s1 s2 s2len
  refine ⟨⟨by decide, regCast_scalar_refines_transmute 2 s1 s2,
    regCast_scalar_refines_transmute 2 s2 s1, fun h => ?_⟩,
    ⟨by decide, regCast_scalar_refines_transmute 1 s2 s2len, fun h => ?_⟩⟩
  · have := h [.bits 5, .bits 9] rfl; revert this; decide
  · have := h [.bits 5] rfl; revert this; decide

end Toy.ReprLower
