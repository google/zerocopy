/-!
# Soundness Model: Wrapping-Niche Enum Discriminant Inversion, Native DWARF Default-Variant Decoding,
# `.debug_gdb_scripts` Executable `.text` Mutation, `thorin` `.dwp` Remap Determinism,
# `#![debugger_visualizer]` `path_erased` Asymmetry, and `#[collapse_debuginfo]` Precedence

Kernel-checked in Lean `v4.34.1` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`)
with zero `sorry`, zero `Classical.choice`, zero `omega`, zero `bv_decide`, zero `native_decide`,
zero `partial def`, and zero `._unsafe_rec` auxiliary constants.
-/

namespace RustcDwarfNicheGdbSoundness

/-! ## Part 1: Circular Modular Ranges and `rustc`'s `min`/`max` Inversion Bug -/

/-- Inclusive circular modular range membership on `[0, modulus)`, matching
`rustc_abi::WrappingRange::contains` (`Miri.ABI.WrappingRange.contains`) and
`src/etc/natvis/intrinsic.natvis` `in_range` for tags `< modulus`. -/
def inCircularRange (modulus begin end_ x : Nat) : Bool :=
  decide (x < modulus) &&
    if begin ≤ end_ then
      decide (begin ≤ x) && decide (x ≤ end_)
    else
      decide (begin ≤ x) || decide (x ≤ end_)

/-- Literal `in_range` predicate from `src/etc/natvis/intrinsic.natvis` (L306):
`(begin <= end) ? ((x >= begin) && (x <= end)) : ((x >= begin) || (x <= end))`. -/
def natvisInRangeRaw (begin end_ x : Nat) : Bool :=
  if begin ≤ end_ then
    decide (begin ≤ x) && decide (x ≤ end_)
  else
    decide (begin ≤ x) || decide (x ≤ end_)

/-- Model of `compute_discriminant_value`'s untagged niche range calculation in
`compiler/rustc_codegen_llvm/src/debuginfo/metadata/enums/mod.rs` (L420-426):
unconditionally sorts `(start, end_)` via `.min` and `.max`. -/
def computeDiscriminantRange (start end_ : Nat) : Nat × Nat :=
  (min start end_, max start end_)

/-- Corrected untagged niche range calculation: preserves `(start, end_)` modulo
`modulus` without sorting endpoints. -/
def computeDiscriminantRangeFixed (modulus start end_ : Nat) : Nat × Nat :=
  (start % modulus, end_ % modulus)

theorem inCircularRange_eq_natvisInRangeRaw {modulus begin end_ x : Nat} (hx : x < modulus) :
    inCircularRange modulus begin end_ x = natvisInRangeRaw begin end_ x := by
  unfold inCircularRange natvisInRangeRaw
  have hdx : decide (x < modulus) = true := decide_eq_true hx
  rw [hdx, Bool.true_and]

theorem computeDiscriminantRange_sorted (start end_ : Nat) :
    (computeDiscriminantRange start end_).1 ≤ (computeDiscriminantRange start end_).2 := by
  unfold computeDiscriminantRange
  exact Nat.le_trans (Nat.min_le_left start end_) (Nat.le_max_left start end_)

/-- Because `computeDiscriminantRange` always outputs `min ≤ max`, the wrapping
branch (`begin > end`) of `intrinsic.natvis`'s `in_range` is unreachable dead code
across every enum emitted by `rustc`. -/
theorem natvis_wrapping_branch_dead_code (modulus start end_ x : Nat) :
    inCircularRange modulus
      (computeDiscriminantRange start end_).1
      (computeDiscriminantRange start end_).2 x =
    (decide (x < modulus) &&
      (decide (min start end_ ≤ x) && decide (x ≤ max start end_))) := by
  unfold inCircularRange computeDiscriminantRange
  have hle : min start end_ ≤ max start end_ :=
    Nat.le_trans (Nat.min_le_left start end_) (Nat.le_max_left start end_)
  simp only [hle, ↓reduceIte]

/-- Non-wrapping niche ranges (`start ≤ end_`) are unaffected by `min`/`max`. -/
theorem computeDiscriminantRange_id_of_le {start end_ : Nat} (h : start ≤ end_) :
    computeDiscriminantRange start end_ = (start, end_) := by
  unfold computeDiscriminantRange
  rw [Nat.min_eq_left h, Nat.max_eq_right h]

/-- Wrapping niche ranges (`end_ < start`) have their endpoints unconditionally swapped. -/
theorem computeDiscriminantRange_swaps_wrapping {start end_ : Nat} (h : end_ < start) :
    computeDiscriminantRange start end_ = (end_, start) := by
  unfold computeDiscriminantRange
  have hle : end_ ≤ start := Nat.le_of_lt h
  rw [Nat.min_eq_right hle, Nat.max_eq_left hle]

/-- **Universal Wrapping-Range Inversion Theorem (Interior False Negatives):**
When `end_ < start` and `x < modulus`, every value strictly inside the true
wrapping interval (`x < end_` or `start < x`) belongs to the true circular range
but is REJECTED by `computeDiscriminantRange`. -/
theorem wrapping_interior_false_negative {modulus start end_ x : Nat}
    (hwrap : end_ < start) (hx : x < modulus) (hint : x < end_ ∨ start < x) :
    inCircularRange modulus start end_ x = true ∧
    inCircularRange modulus
      (computeDiscriminantRange start end_).1
      (computeDiscriminantRange start end_).2 x = false := by
  rw [computeDiscriminantRange_swaps_wrapping hwrap]
  rw [inCircularRange_eq_natvisInRangeRaw hx, inCircularRange_eq_natvisInRangeRaw hx]
  unfold natvisInRangeRaw
  have hnotle : ¬ (start ≤ end_) := Nat.not_le_of_gt hwrap
  have hle : end_ ≤ start := Nat.le_of_lt hwrap
  simp only [hnotle, hle, ↓reduceIte]
  cases hint with
  | inl hlt =>
    have h1 : decide (x ≤ end_) = true := decide_eq_true (Nat.le_of_lt hlt)
    have h2 : decide (end_ ≤ x) = false := decide_eq_false (Nat.not_le_of_gt hlt)
    rw [h1, Bool.or_true, h2, Bool.false_and]
    exact ⟨rfl, rfl⟩
  | inr hgt =>
    have h1 : decide (start ≤ x) = true := decide_eq_true (Nat.le_of_lt hgt)
    have h2 : decide (x ≤ start) = false := decide_eq_false (Nat.not_le_of_gt hgt)
    rw [h1, Bool.true_or, h2, Bool.and_false]
    exact ⟨rfl, rfl⟩

/-- **Universal Wrapping-Range Inversion Theorem (Exterior False Positives):**
When `end_ < start` and `x < modulus`, every value strictly in the complement gap
(`end_ < x ∧ x < start`) is OUTSIDE the true circular range but is FALSELY ACCEPTED
by `computeDiscriminantRange`. -/
theorem wrapping_exterior_false_positive {modulus start end_ x : Nat}
    (hwrap : end_ < start) (hx : x < modulus) (hgap : end_ < x ∧ x < start) :
    inCircularRange modulus start end_ x = false ∧
    inCircularRange modulus
      (computeDiscriminantRange start end_).1
      (computeDiscriminantRange start end_).2 x = true := by
  rw [computeDiscriminantRange_swaps_wrapping hwrap]
  rw [inCircularRange_eq_natvisInRangeRaw hx, inCircularRange_eq_natvisInRangeRaw hx]
  unfold natvisInRangeRaw
  have hnotle : ¬ (start ≤ end_) := Nat.not_le_of_gt hwrap
  have hle : end_ ≤ start := Nat.le_of_lt hwrap
  simp only [hnotle, hle, ↓reduceIte]
  have h1 : decide (start ≤ x) = false := decide_eq_false (Nat.not_le_of_gt hgap.2)
  have h2 : decide (x ≤ end_) = false := decide_eq_false (Nat.not_le_of_gt hgap.1)
  have h3 : decide (end_ ≤ x) = true := decide_eq_true (Nat.le_of_lt hgap.1)
  have h4 : decide (x ≤ start) = true := decide_eq_true (Nat.le_of_lt hgap.2)
  rw [h1, h2, h3, h4]
  exact ⟨rfl, rfl⟩

/-- **Exact Complement-Except-Endpoints Theorem:**
For any wrapping range (`end_ < start`) and any `x < modulus` other than the two
boundary endpoints `start` and `end_`, `computeDiscriminantRange` computes the
exact Boolean negation of the true circular membership predicate. -/
theorem wrapping_bug_is_exact_negation_off_endpoints {modulus start end_ x : Nat}
    (hwrap : end_ < start) (hx : x < modulus) (hneS : x ≠ start) (hneE : x ≠ end_) :
    inCircularRange modulus
      (computeDiscriminantRange start end_).1
      (computeDiscriminantRange start end_).2 x =
    !(inCircularRange modulus start end_ x) := by
  cases Nat.lt_or_ge x end_ with
  | inl hlt =>
    have h := wrapping_interior_false_negative hwrap hx (Or.inl hlt)
    rw [h.1, h.2]
    rfl
  | inr hgeE =>
    have hgtE : end_ < x := Nat.lt_of_le_of_ne hgeE (Ne.symm hneE)
    cases Nat.lt_or_ge x start with
    | inl hltS =>
      have h := wrapping_exterior_false_positive hwrap hx ⟨hgtE, hltS⟩
      rw [h.1, h.2]
      rfl
    | inr hgeS =>
      have hgtS : start < x := Nat.lt_of_le_of_ne hgeS (Ne.symm hneS)
      have h := wrapping_interior_false_negative hwrap hx (Or.inr hgtS)
      rw [h.1, h.2]
      rfl

/-- The two boundary endpoints `start` and `end_` are the ONLY valid elements of a
wrapping range that survive the `min`/`max` bug. -/
theorem wrapping_endpoints_survive {modulus start end_ : Nat}
    (hwrap : end_ < start) (hs : start < modulus) (he : end_ < modulus) :
    inCircularRange modulus
      (computeDiscriminantRange start end_).1
      (computeDiscriminantRange start end_).2 start = true ∧
    inCircularRange modulus
      (computeDiscriminantRange start end_).1
      (computeDiscriminantRange start end_).2 end_ = true := by
  rw [computeDiscriminantRange_swaps_wrapping hwrap]
  rw [inCircularRange_eq_natvisInRangeRaw hs, inCircularRange_eq_natvisInRangeRaw he]
  unfold natvisInRangeRaw
  have hle : end_ ≤ start := Nat.le_of_lt hwrap
  simp only [hle, ↓reduceIte]
  have h2 : decide (start ≤ start) = true := decide_eq_true (Nat.le_refl start)
  have h3 : decide (end_ ≤ end_) = true := decide_eq_true (Nat.le_refl end_)
  rw [h2, h3]
  exact ⟨rfl, rfl⟩

/-! ## Part 2: Decoder Models (NatVis, `cpp_like.rs`, Fixed Circular, Native DWARF) -/

/-- Decoded enum variant outcome for a debugger visualizer or DWARF consumer. -/
inductive DecodedVariant where
  | untagged
  | tagged (variantIdx : Nat)
  | unmatched

def DecodedVariant.beq : DecodedVariant → DecodedVariant → Bool
  | .untagged, .untagged => true
  | .tagged a, .tagged b => Nat.beq a b
  | .unmatched, .unmatched => true
  | _, _ => false

theorem DecodedVariant.eq_of_beq : ∀ {a b : DecodedVariant}, DecodedVariant.beq a b = true → a = b
  | .untagged, .untagged, _ => rfl
  | .tagged a, .tagged b, h => by
    have hab : a = b := Nat.eq_of_beq_eq_true h
    rw [hab]
  | .unmatched, .unmatched, _ => rfl

/-- Exact-tag lookup over `(variantIdx, tagValue)` pairs, matching `DISCR_EXACT`
or `DW_AT_discr_value` (`noncomputable` suppresses codegen `._unsafe_rec`). -/
noncomputable def findExactTag (tags : List (Nat × Nat)) (x : Nat) : Option Nat :=
  List.rec none (fun p _ ih => if Nat.beq p.2 x then some p.1 else ih) tags

/-- NatVis `<DisplayString>` decoder (`src/etc/natvis/intrinsic.natvis` L346-378):
checks all `DISCR_EXACT` rules before all `in_range(tag, DISCR_BEGIN, DISCR_END)` rules. -/
noncomputable def decodeNatvisDisplay (modulus begin end_ : Nat) (tags : List (Nat × Nat))
    (x : Nat) : DecodedVariant :=
  if decide (x < modulus) then
    match findExactTag tags x with
    | some idx => .tagged idx
    | none =>
      if inCircularRange modulus begin end_ x then .untagged else .unmatched
  else
    .unmatched

/-- `cpp_like.rs` (L122-137) field-order decoder when `variant0` is the untagged
range variant: checks `in_range(tag, DISCR_BEGIN, DISCR_END)` before subsequent
`variant1..variantK` `DISCR_EXACT` fields. -/
noncomputable def decodeCppLikeFieldOrder (modulus begin end_ : Nat) (tags : List (Nat × Nat))
    (x : Nat) : DecodedVariant :=
  if decide (x < modulus) then
    if inCircularRange modulus begin end_ x then
      .untagged
    else
      match findExactTag tags x with
      | some idx => .tagged idx
      | none => .unmatched
  else
    .unmatched

/-- Predicate capturing NatVis `<Expand>` simultaneous dual-match hazard
(`src/etc/natvis/intrinsic.natvis` L414-447): both a `DISCR_EXACT` rule and an
`in_range` rule evaluate to `true` on the same tag byte `x`. -/
noncomputable def decodeNatvisExpandDualMatch (modulus begin end_ : Nat) (tags : List (Nat × Nat))
    (x : Nat) : Bool :=
  match findExactTag tags x with
  | some _ => inCircularRange modulus begin end_ x
  | none => false

/-- Linux native DWARF decoder (`compiler/rustc_codegen_llvm/src/debuginfo/metadata/enums/native.rs`
L437, DWARF v5 §5.7.10 default-variant rule): `DiscrResult::Range` maps via
`opt_single_val()` to `None`, omitting `DW_AT_discr_value` on the untagged
`DW_TAG_variant` so any tag not matching an explicit `DW_AT_discr_value` falls
back to `.untagged`. -/
noncomputable def decodeNativeDwarf (modulus : Nat) (tags : List (Nat × Nat)) (x : Nat) :
    DecodedVariant :=
  if decide (x < modulus) then
    match findExactTag tags x with
    | some idx => .tagged idx
    | none => .untagged
  else
    .unmatched

/-- Well-formedness of a niche-layout enum's tag encoding: every exact tag is
`< modulus` and disjoint from the untagged valid circular range
(primitive `List.rec` — zero `._unsafe_rec`). -/
def ExactTagsDisjointFromRange (modulus start end_ : Nat) (tags : List (Nat × Nat)) : Prop :=
  List.rec True
    (fun p _ ih => p.2 < modulus ∧ inCircularRange modulus start end_ p.2 = false ∧ ih)
    tags

theorem findExactTag_none_of_in_range {modulus start end_ x : Nat} :
    ∀ {tags : List (Nat × Nat)},
      ExactTagsDisjointFromRange modulus start end_ tags →
      inCircularRange modulus start end_ x = true →
      findExactTag tags x = none
  | [], _, _ => rfl
  | (_, tag) :: rest, ⟨_, hnotin, hrest⟩, hxin => by
    change (if Nat.beq tag x then some _ else findExactTag rest x) = none
    cases hbeq : Nat.beq tag x with
    | true =>
      have heq : tag = x := Nat.eq_of_beq_eq_true hbeq
      rw [heq] at hnotin
      rw [hnotin] at hxin
      cases hxin
    | false =>
      exact findExactTag_none_of_in_range hrest hxin

theorem inCircularRange_false_of_findExactTag_some {modulus start end_ x idx : Nat} :
    ∀ {tags : List (Nat × Nat)},
      ExactTagsDisjointFromRange modulus start end_ tags →
      findExactTag tags x = some idx →
      x < modulus ∧ inCircularRange modulus start end_ x = false
  | [], _, h => by cases h
  | (_, tag) :: rest, ⟨hlt, hnotin, hrest⟩, h => by
    change (if Nat.beq tag x then some _ else findExactTag rest x) = some idx at h
    cases hbeq : Nat.beq tag x with
    | true =>
      have heq : tag = x := Nat.eq_of_beq_eq_true hbeq
      rw [← heq]
      exact ⟨hlt, hnotin⟩
    | false =>
      rw [hbeq] at h
      exact inCircularRange_false_of_findExactTag_some hrest h

/-- **Soundness and Bijectivity of Preserving `(start, end_)` Unsorted:**
For ANY well-formed niche enum (wrapping OR non-wrapping), emitting `(start, end_)`
unsorted yields exact, unambiguous decoding across BOTH `decodeNatvisDisplay` and
`decodeCppLikeFieldOrder`, with zero `<Expand>` dual-matches and zero false
positives on invalid unused niche bytes. -/
theorem unsorted_circular_range_sound_and_exact
    {modulus start end_ : Nat} {tags : List (Nat × Nat)}
    (hwf : ExactTagsDisjointFromRange modulus start end_ tags) :
    (∀ x, x < modulus → inCircularRange modulus start end_ x = true →
      decodeNatvisDisplay modulus start end_ tags x = .untagged ∧
      decodeCppLikeFieldOrder modulus start end_ tags x = .untagged ∧
      decodeNatvisExpandDualMatch modulus start end_ tags x = false) ∧
    (∀ x idx, findExactTag tags x = some idx →
      decodeNatvisDisplay modulus start end_ tags x = .tagged idx ∧
      decodeCppLikeFieldOrder modulus start end_ tags x = .tagged idx ∧
      decodeNatvisExpandDualMatch modulus start end_ tags x = false) ∧
    (∀ x, x < modulus → inCircularRange modulus start end_ x = false →
      findExactTag tags x = none →
      decodeNatvisDisplay modulus start end_ tags x = .unmatched ∧
      decodeCppLikeFieldOrder modulus start end_ tags x = .unmatched) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx hin
    have hnone := findExactTag_none_of_in_range hwf hin
    have hdx : decide (x < modulus) = true := decide_eq_true hx
    unfold decodeNatvisDisplay decodeCppLikeFieldOrder decodeNatvisExpandDualMatch
    rw [hdx, hnone, hin]
    exact ⟨rfl, rfl, rfl⟩
  · intro x idx hsome
    have ⟨hx, hnotin⟩ := inCircularRange_false_of_findExactTag_some hwf hsome
    have hdx : decide (x < modulus) = true := decide_eq_true hx
    unfold decodeNatvisDisplay decodeCppLikeFieldOrder decodeNatvisExpandDualMatch
    rw [hdx, hsome, hnotin]
    exact ⟨rfl, rfl, rfl⟩
  · intro x hx hnotin hnone
    have hdx : decide (x < modulus) = true := decide_eq_true hx
    unfold decodeNatvisDisplay decodeCppLikeFieldOrder
    rw [hdx, hnone, hnotin]
    exact ⟨rfl, rfl⟩

/-- **Soundness of Linux Native DWARF Default-Variant Omission on Inhabited Values:**
Omitting `DW_AT_discr_value` on the untagged variant (`native.rs:437`) decodes EVERY
inhabited payload and exact tag identically to the unsorted circular decoder,
completely immune to wrapping-range endpoint ordering. -/
theorem native_dwarf_sound_on_inhabited
    {modulus start end_ : Nat} {tags : List (Nat × Nat)}
    (hwf : ExactTagsDisjointFromRange modulus start end_ tags) :
    (∀ x, x < modulus → inCircularRange modulus start end_ x = true →
      decodeNativeDwarf modulus tags x = .untagged) ∧
    (∀ x idx, findExactTag tags x = some idx →
      decodeNativeDwarf modulus tags x = .tagged idx) := by
  constructor
  · intro x hx hin
    have hnone := findExactTag_none_of_in_range hwf hin
    have hdx : decide (x < modulus) = true := decide_eq_true hx
    unfold decodeNativeDwarf
    rw [hdx, hnone]
    rfl
  · intro x idx hsome
    have ⟨hx, _⟩ := inCircularRange_false_of_findExactTag_some hwf hsome
    have hdx : decide (x < modulus) = true := decide_eq_true hx
    unfold decodeNativeDwarf
    rw [hdx, hsome]
    rfl

/-- **Honest Boundary of DWARF's Default-Variant Rule:**
On uninhabited (UB) unused niche bytes (`x < modulus`, not in `tags`), DWARF's
default-variant fallback reports `.untagged` rather than `.unmatched` because
`DW_TAG_variant` without `DW_AT_discr_value` carries no validity bounds. -/
theorem native_dwarf_maps_unused_niche_to_default
    {modulus x : Nat} {tags : List (Nat × Nat)}
    (hx : x < modulus) (hnone : findExactTag tags x = none) :
    decodeNativeDwarf modulus tags x = .untagged := by
  unfold decodeNativeDwarf
  rw [decide_eq_true hx, hnone]
  rfl

/-! ## Part 3: Concrete Exhaustive Mechanization of `SignedWrap`, `SignedWrap128`, and `Enum17` -/

/-- Exact tag specification for
`enum SignedWrap { Valid(pattern_type!(i8 is -10..=10)), TagA, TagB }`:
modulus 256, wrapping valid range `246..=10`, exact tags `TagA = 11` (variant 1),
`TagB = 12` (variant 2). -/
def signedWrapMod : Nat := 256
def signedWrapStart : Nat := 246
def signedWrapEnd : Nat := 10
def signedWrapTags : List (Nat × Nat) := [(1, 11), (2, 12)]

theorem signedWrap_wf :
    ExactTagsDisjointFromRange signedWrapMod signedWrapStart signedWrapEnd signedWrapTags := by
  unfold ExactTagsDisjointFromRange signedWrapMod signedWrapStart signedWrapEnd signedWrapTags
  refine ⟨by decide, by decide, by decide, by decide, trivial⟩

theorem signedWrap_buggy_range_eq :
    computeDiscriminantRange signedWrapStart signedWrapEnd = (10, 246) := by
  decide

/-- Balanced binary-tree counter over `[lo, lo + 2^depth)`. Recursion depth is
`O(depth)` (`8` for `256`), defined via primitive `Nat.rec` (`noncomputable` — zero `._unsafe_rec`). -/
noncomputable def countPow2 (p : Nat → Bool) (depth : Nat) : Nat → Nat :=
  Nat.rec (fun lo => if p lo then 1 else 0)
    (fun d ih lo => ih lo + ih (lo + Nat.pow 2 d))
    depth

/-- Exact count over `[0, 256)` via balanced depth-8 tree (`2^8 = 256`). -/
noncomputable def countU8 (p : Nat → Bool) : Nat := countPow2 p 8 0

/-- Exact count of valid `SignedWrap::Valid` payloads in `[0, 256)` is `21` (`-10..=10`). -/
theorem signedWrap_valid_count :
    countU8 (fun x => inCircularRange signedWrapMod signedWrapStart signedWrapEnd x) = 21 := by
  decide

/-- Under `rustc`'s buggy `(10, 246)` bounds, `intrinsic.natvis` fails
(`UNMATCHED_NATVIS_FAILURE`) on exactly `19` of the `21` valid `SignedWrap::Valid`
payloads (`-9..=9`, raw bytes `{0..9} ∪ {247..255}`). -/
theorem signedWrap_buggy_natvis_unmatched_valid_count :
    countU8 (fun x =>
      inCircularRange signedWrapMod signedWrapStart signedWrapEnd x &&
      DecodedVariant.beq
        (decodeNatvisDisplay signedWrapMod 10 246 signedWrapTags x) .unmatched) = 19 := by
  decide

/-- Under `rustc`'s buggy `(10, 246)` bounds, ONLY `2` of the `21` valid payloads
(`Valid(-10) = 246` and `Valid(10) = 10`) match `Valid`. -/
theorem signedWrap_buggy_natvis_matched_valid_count :
    countU8 (fun x =>
      inCircularRange signedWrapMod signedWrapStart signedWrapEnd x &&
      DecodedVariant.beq
        (decodeNatvisDisplay signedWrapMod 10 246 signedWrapTags x) .untagged) = 2 := by
  decide

/-- Concrete witnesses matching the empirical probe: `Valid(-5) = 251` and `Valid(0) = 0`
both fail in buggy NatVis, while `Valid(-10) = 246` and `Valid(10) = 10` survive. -/
theorem signedWrap_buggy_concrete_witnesses :
    decodeNatvisDisplay signedWrapMod 10 246 signedWrapTags 251 = .unmatched ∧
    decodeNatvisDisplay signedWrapMod 10 246 signedWrapTags 0 = .unmatched ∧
    decodeNatvisDisplay signedWrapMod 10 246 signedWrapTags 246 = .untagged ∧
    decodeNatvisDisplay signedWrapMod 10 246 signedWrapTags 10 = .untagged ∧
    decodeNatvisDisplay signedWrapMod 10 246 signedWrapTags 11 = .tagged 1 ∧
    decodeNatvisDisplay signedWrapMod 10 246 signedWrapTags 12 = .tagged 2 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- All `233` invalid unused niche bytes (`13..=245`) are FALSELY matched as `Valid`
by buggy `(10, 246)` NatVis. -/
theorem signedWrap_buggy_unused_niche_false_positive_count :
    countU8 (fun x =>
      !(inCircularRange signedWrapMod signedWrapStart signedWrapEnd x) &&
      (findExactTag signedWrapTags x).isNone &&
      DecodedVariant.beq
        (decodeNatvisDisplay signedWrapMod 10 246 signedWrapTags x) .untagged) = 233 := by
  decide

/-- Exact total partition of all `256` byte values: `21` valid + `2` exact tags + `233` unused niche. -/
theorem signedWrap_256_partition :
    countU8 (fun x => inCircularRange signedWrapMod signedWrapStart signedWrapEnd x) +
    countU8 (fun x => (findExactTag signedWrapTags x).isSome) +
    countU8 (fun x =>
      !(inCircularRange signedWrapMod signedWrapStart signedWrapEnd x) &&
      (findExactTag signedWrapTags x).isNone) = 256 := by
  decide

/-- Under buggy `(10, 246)`, BOTH `TagA (11)` and `TagB (12)` trigger NatVis `<Expand>`
dual-match AND are misclassified as `Valid` (`.untagged`) by `cpp_like.rs`'s
variant-order scan (`variant0` before `variant1..2`). -/
theorem signedWrap_buggy_tagA_tagB_dual_match_and_cpplike_hijack :
    decodeNatvisExpandDualMatch signedWrapMod 10 246 signedWrapTags 11 = true ∧
    decodeNatvisExpandDualMatch signedWrapMod 10 246 signedWrapTags 12 = true ∧
    decodeCppLikeFieldOrder signedWrapMod 10 246 signedWrapTags 11 = .untagged ∧
    decodeCppLikeFieldOrder signedWrapMod 10 246 signedWrapTags 12 = .untagged := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Preserving `(246, 10)` unsorted recovers `21/21` valid payloads, `2/2` exact tags,
`0/233` false positives, and `0` `<Expand>` dual matches. -/
theorem signedWrap_fixed_exact_counts :
    countU8 (fun x =>
      inCircularRange signedWrapMod signedWrapStart signedWrapEnd x &&
      DecodedVariant.beq
        (decodeNatvisDisplay signedWrapMod 246 10 signedWrapTags x) .untagged) = 21 ∧
    countU8 (fun x =>
      !(inCircularRange signedWrapMod signedWrapStart signedWrapEnd x) &&
      (findExactTag signedWrapTags x).isNone &&
      DecodedVariant.beq
        (decodeNatvisDisplay signedWrapMod 246 10 signedWrapTags x) .unmatched) = 233 ∧
    countU8 (fun x => decodeNatvisExpandDualMatch signedWrapMod 246 10 signedWrapTags x) = 0 := by
  exact ⟨by decide, by decide, by decide⟩

/-- Linux native DWARF decodes all `21/21` `Valid` payloads and `2/2` exact tags cleanly. -/
theorem signedWrap_native_dwarf_counts :
    countU8 (fun x =>
      inCircularRange signedWrapMod signedWrapStart signedWrapEnd x &&
      DecodedVariant.beq (decodeNativeDwarf signedWrapMod signedWrapTags x) .untagged) = 21 ∧
    decodeNativeDwarf signedWrapMod signedWrapTags 11 = .tagged 1 ∧
    decodeNativeDwarf signedWrapMod signedWrapTags 12 = .tagged 2 := by
  exact ⟨by decide, rfl, rfl⟩

/-- 128-bit wrapping niche `SignedWrap128` (`pattern_type!(i128 is -10..=10)`, `TagA=11`, `TagB=12`):
`computeDiscriminantRange` produces the identical inversion over `2^128`. -/
def pow2_128 : Nat := Nat.pow 2 128
def signedWrap128Start : Nat := pow2_128 - 10
def signedWrap128End : Nat := 10

theorem signedWrap128_buggy_inversion :
    computeDiscriminantRange signedWrap128Start signedWrap128End = (10, pow2_128 - 10) ∧
    inCircularRange pow2_128 10 (pow2_128 - 10) 0 = false ∧
    inCircularRange pow2_128 10 (pow2_128 - 10) (pow2_128 - 5) = false ∧
    inCircularRange pow2_128 10 (pow2_128 - 10) 13 = true ∧
    inCircularRange pow2_128 signedWrap128Start signedWrap128End 0 = true ∧
    inCircularRange pow2_128 signedWrap128Start signedWrap128End (pow2_128 - 5) = true ∧
    inCircularRange pow2_128 signedWrap128Start signedWrap128End 13 = false := by
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- `src/etc/natvis/intrinsic.natvis` (L346-481) enumerates only `variant0..variant15`
(16 variants max), whereas `cpp_like.rs` (L925-949) emits `variant16`, `variant17`, ...
for enums with `> 16` variants. -/
def natvisCappedDecode (variantIdx : Nat) : DecodedVariant :=
  if decide (variantIdx < 16) then .tagged variantIdx else .unmatched

theorem natvis_16_variant_cap_drops_variant16 :
    natvisCappedDecode 15 = .tagged 15 ∧
    natvisCappedDecode 16 = .unmatched ∧
    ∀ k, 16 ≤ k → natvisCappedDecode k = .unmatched := by
  refine ⟨rfl, rfl, ?_⟩
  intro k hk
  unfold natvisCappedDecode
  have hnotlt : ¬ (k < 16) := Nat.not_lt_of_ge hk
  rw [decide_eq_false hnotlt]
  rfl

/-! ## Part 4: `.debug_gdb_scripts` Executable `.text` Non-Invariance -/

inductive DebugInfoLevel where
  | none
  | lineDirectivesOnly
  | lineTablesOnly
  | limited
  | full

inductive CrateType where
  | executable
  | dylib
  | cdylib
  | staticlib
  | sdylib
  | procMacro
  | rlib

inductive StripMode where
  | none
  | debuginfo
  | symbols

def DebugInfoLevel.isNonZero : DebugInfoLevel → Bool
  | .none => false
  | .lineDirectivesOnly => true
  | .lineTablesOnly => true
  | .limited => true
  | .full => true

def CrateType.embedVisualizers : CrateType → Bool
  | .executable => true
  | .dylib => true
  | .cdylib => true
  | .staticlib => true
  | .sdylib => true
  | .procMacro => false
  | .rlib => false

def CrateType.hasCMainShim : CrateType → Bool
  | .executable => true
  | _ => false

/-- Exact predicate `needs_gdb_debug_scripts_section` from
`compiler/rustc_codegen_llvm/src/debuginfo/gdb.rs` (L84-116). -/
def needsGdbDebugScriptsSection (lvl : DebugInfoLevel) (targetEmitGdbScripts : Bool)
    (ct : CrateType) : Bool :=
  lvl.isNonZero && targetEmitGdbScripts && ct.embedVisualizers

/-- Opaque machine-code byte sequence for the injected volatile load
`movzbl __rustc_debug_gdb_scripts_section__(%rip), %eax` (7 bytes on x86_64 PIC/PIE). -/
def volatileLoadMovzblBytes : List Nat := [0x0f, 0xb6, 0x05, 0x00, 0x00, 0x00, 0x00]

/-- Executable `.text` section model for `create_entry_fn` (`compiler/rustc_codegen_ssa/src/base.rs`
L563) + `insert_reference_to_gdb_debug_scripts_section_global` (`gdb.rs` L18-25):
`-C strip={debuginfo,symbols}` cannot remove executable `.text` instructions or the
relocation-pinned `.debug_gdb_scripts` section. -/
def emitEntryShimText (baseText : List Nat) (lvl : DebugInfoLevel)
    (targetEmitGdbScripts : Bool) (ct : CrateType) (_strip : StripMode) : List Nat :=
  if ct.hasCMainShim && needsGdbDebugScriptsSection lvl targetEmitGdbScripts ct then
    volatileLoadMovzblBytes ++ baseText
  else
    baseText

/-- Whether `.debug_gdb_scripts` survives in the final linked artifact (referenced by
the volatile load in executables, hence surviving `--gc-sections` and `-C strip=*`). -/
def linkedArtifactRetainsGdbScripts (lvl : DebugInfoLevel) (targetEmitGdbScripts : Bool)
    (ct : CrateType) (_strip : StripMode) : Bool :=
  ct.hasCMainShim && needsGdbDebugScriptsSection lvl targetEmitGdbScripts ct

theorem list_append_ne_self_of_nonempty {α : Type} {a b : List α} (ha : a ≠ []) :
    a ++ b ≠ b := by
  intro heq
  have hlen : (a ++ b).length = b.length := congrArg List.length heq
  rw [List.length_append] at hlen
  cases a with
  | nil => exact ha rfl
  | cons x xs =>
    have hpos : 0 < (x :: xs).length := Nat.zero_lt_succ xs.length
    have hlt : b.length < (x :: xs).length + b.length := Nat.lt_add_of_pos_left hpos
    rw [hlen] at hlt
    exact Nat.lt_irrefl b.length hlt

/-- **Executable `.text` Non-Invariance Theorem:**
On any target with `emit_debug_gdb_scripts = true` (such as `x86_64-unknown-linux-gnu`),
enabling ANY non-zero `-C debuginfo` level (`line-directives-only`, `line-tables-only`,
`1`/`limited`, `2`/`full`) strictly mutates executable `.text` machine code relative to
`-C debuginfo=0`, and `-C strip={debuginfo,symbols}` does NOT undo the mutation or
remove `.debug_gdb_scripts`. -/
theorem text_mutated_for_every_nonzero_debuginfo (baseText : List Nat)
    (lvl : DebugInfoLevel) (strip : StripMode) (hnonzero : lvl ≠ .none) :
    emitEntryShimText baseText lvl true .executable strip ≠
      emitEntryShimText baseText .none true .executable .none ∧
    linkedArtifactRetainsGdbScripts lvl true .executable strip = true := by
  cases lvl with
  | none => exact False.elim (hnonzero rfl)
  | lineDirectivesOnly | lineTablesOnly | limited | full =>
    constructor
    · unfold emitEntryShimText needsGdbDebugScriptsSection
        CrateType.hasCMainShim CrateType.embedVisualizers DebugInfoLevel.isNonZero
      exact list_append_ne_self_of_nonempty (by intro h; cases h)
    · rfl

/-- All four non-zero `-C debuginfo` levels produce identical entry-shim `.text` bytes
(matching the empirical SHA-256 identity across `line-directives-only`, `line-tables-only`,
`1`, `2`, `2 + strip=debuginfo`, and `2 + strip=symbols`). -/
theorem text_identical_across_all_nonzero_levels (baseText : List Nat)
    (l1 l2 : DebugInfoLevel) (s1 s2 : StripMode)
    (h1 : l1 ≠ .none) (h2 : l2 ≠ .none) :
    emitEntryShimText baseText l1 true .executable s1 =
    emitEntryShimText baseText l2 true .executable s2 := by
  cases l1 with
  | none => exact False.elim (h1 rfl)
  | lineDirectivesOnly | lineTablesOnly | limited | full =>
    cases l2 with
    | none => exact False.elim (h2 rfl)
    | lineDirectivesOnly | lineTablesOnly | limited | full => rfl

/-- Targets with `emit_debug_gdb_scripts = false` (e.g., `x86_64-pc-windows-msvc`,
`riscv64gc-unknown-none-elf`) and non-executable crate types (`rlib`, `cdylib`, `staticlib`)
suffer zero entry-shim `.text` mutation across all `-C debuginfo` levels. -/
theorem text_invariant_when_disabled_or_non_executable (baseText : List Nat)
    (lvl : DebugInfoLevel) (targetEmit : Bool) (ct : CrateType) (strip : StripMode)
    (h : targetEmit = false ∨ ct ≠ .executable) :
    emitEntryShimText baseText lvl targetEmit ct strip = baseText := by
  cases h with
  | inl hf =>
    subst hf
    unfold emitEntryShimText needsGdbDebugScriptsSection
    cases ct <;> cases lvl <;> rfl
  | inr hne =>
    cases ct with
    | executable => exact False.elim (hne rfl)
    | dylib | cdylib | staticlib | sdylib | procMacro | rlib => rfl

/-! ## Part 5: `thorin` `.dwp` Path-Remap Determinism -/

/-- A build unit's unremapped DWARF input: `(buildDirPrefix, relPath, unitPayload)`. -/
structure DwarfUnitInput where
  buildDirPrefix : List Nat
  relPath : List Nat
  payload : List Nat

/-- Canonical `--remap-path-prefix=<buildDirPrefix>=<canonical>` normalization applied
before `.dwo` emission and `thorin::DwarfPackage` packaging (`link.rs:950-1010`). -/
def remapUnit (canonical : List Nat) (u : DwarfUnitInput) : List Nat × List Nat :=
  (canonical ++ u.relPath, u.payload)

/-- Abstract deterministic `thorin::DwarfPackage` serializer operating on remapped units
sorted into canonical crate-input order (`into_sorted_stable_ord`, `link.rs:978`). -/
def assembleDwp (canonical : List Nat) (units : List DwarfUnitInput) :
    List (List Nat × List Nat) :=
  units.map (remapUnit canonical)

/-- Two build trees with arbitrary distinct directory prefixes (`dir1` vs `dir2`)
produce identical `thorin` `.dwp` artifacts once `--remap-path-prefix` maps each build
prefix to the same canonical prefix and relative paths + payloads match. -/
theorem thorin_dwp_bit_identical_under_remap (canonical : List Nat) :
    ∀ (u1 u2 : List DwarfUnitInput),
      u1.length = u2.length →
      (∀ i (h1 : i < u1.length) (h2 : i < u2.length),
        (u1[i]'h1).relPath = (u2[i]'h2).relPath ∧
        (u1[i]'h1).payload = (u2[i]'h2).payload) →
      assembleDwp canonical u1 = assembleDwp canonical u2
  | [], [], _, _ => rfl
  | a :: as, [], hlen, _ => by cases hlen
  | [], b :: bs, hlen, _ => by cases hlen
  | a :: as, b :: bs, hlen, hmatch => by
    unfold assembleDwp
    simp only [List.map_cons]
    have h0 := hmatch 0 (Nat.zero_lt_succ as.length) (Nat.zero_lt_succ bs.length)
    dsimp only [List.getElem_cons_zero] at h0
    have hhead : remapUnit canonical a = remapUnit canonical b := by
      unfold remapUnit
      rw [h0.1, h0.2]
    have htail_len : as.length = bs.length := Nat.succ.inj hlen
    have htail : assembleDwp canonical as = assembleDwp canonical bs :=
      thorin_dwp_bit_identical_under_remap canonical as bs htail_len (fun i h1 h2 =>
        hmatch (i + 1) (Nat.succ_lt_succ h1) (Nat.succ_lt_succ h2))
    unfold assembleDwp at htail
    rw [hhead, htail]

/-! ## Part 6: `#![debugger_visualizer]` `path_erased` Deduplication Asymmetry -/

/-- Model of `DebuggerVisualizerFile` (`rustc_middle/src/middle/debugger_visualizer.rs` L10-20):
`src` is the script byte digest, `path` is `some p` for `LOCAL_CRATE` and `none` for
upstream `.rlib`s encoded via `path_erased()` (`rustc_metadata/src/rmeta/encoder.rs` L2065). -/
structure VisualizerFile where
  srcId : Nat
  path : Option Nat

def VisualizerFile.beq (a b : VisualizerFile) : Bool :=
  Nat.beq a.srcId b.srcId &&
    match a.path, b.path with
    | none, none => true
    | some p1, some p2 => Nat.beq p1 p2
    | _, _ => false

def VisualizerFile.pathErased (v : VisualizerFile) : VisualizerFile :=
  { srcId := v.srcId, path := none }

noncomputable def containsVis (v : VisualizerFile) (xs : List VisualizerFile) : Bool :=
  List.rec false (fun h _ ih => if VisualizerFile.beq v h then true else ih) xs

/-- Structural deduplication modeling `BTreeSet<DebuggerVisualizerFile>` in
`collect_debugger_visualizers_transitive` (`rustc_codegen_ssa/src/base.rs` L640-658),
defined via primitive `List.rec` (`noncomputable` — zero `._unsafe_rec`). -/
noncomputable def dedupVis (xs : List VisualizerFile) : List VisualizerFile :=
  List.rec [] (fun h _ rest => if containsVis h rest then rest else h :: rest) xs

/-- Upstream diamond deduplication: two upstream `.rlib`s sharing identical script bytes
both have `path = none` (`path_erased`), so they deduplicate to a single entry. -/
theorem upstream_diamond_deduplicates (src : Nat) :
    (dedupVis [VisualizerFile.mk src none, VisualizerFile.mk src none]).length = 1 := by
  change (if (if Nat.beq src src && true then true else false) then
    [VisualizerFile.mk src none]
  else
    VisualizerFile.mk src none :: [VisualizerFile.mk src none]).length = 1
  rw [Nat.beq_refl]
  rfl

/-- **Local-vs-Upstream `path_erased` Asymmetry Bug (`base.rs:644`):**
Because `collect_debugger_visualizers_transitive` does NOT call `.path_erased()` on
`tcx.debugger_visualizers(LOCAL_CRATE)`, a local script `(src, some p)` and an upstream
byte-identical script `(src, none)` fail to deduplicate (`length = 2`), whereas applying
`pathErased` restores `length = 1`. -/
theorem local_vs_upstream_fails_dedup_without_path_erase (src p : Nat) :
    (dedupVis [VisualizerFile.mk src (some p), VisualizerFile.mk src none]).length = 2 ∧
    (dedupVis
      ([VisualizerFile.mk src (some p), VisualizerFile.mk src none].map
        VisualizerFile.pathErased)).length = 1 := by
  constructor
  · change (if (if Nat.beq src src && false then true else false) then
      [VisualizerFile.mk src none]
    else
      VisualizerFile.mk src (some p) :: [VisualizerFile.mk src none]).length = 2
    rw [Bool.and_false]
    rfl
  · change (if (if Nat.beq src src && true then true else false) then
      [VisualizerFile.mk src none]
    else
      VisualizerFile.mk src none :: [VisualizerFile.mk src none]).length = 1
    rw [Nat.beq_refl]
    rfl

/-! ## Part 7: `#[collapse_debuginfo]` 4×4 Precedence Table (`rustc_expand/src/base.rs` L844-862) -/

inductive CollapseOpt where
  | no
  | unspecified
  | external
  | yes

/-- Exact 4×4 `collapse_table` from `compiler/rustc_expand/src/base.rs` (L844-862). -/
def getCollapseDebuginfo (cliFlag attrOpt : CollapseOpt) (isExternal isBuiltin : Bool) : Bool :=
  let effectiveAttr : CollapseOpt :=
    match attrOpt with
    | .unspecified => if isBuiltin then .yes else .unspecified
    | other => other
  match cliFlag, effectiveAttr with
  | .no, _ => false
  | .yes, _ => true
  | .unspecified, .no | .external, .no => false
  | .unspecified, .yes | .external, .yes => true
  | .unspecified, .unspecified | .unspecified, .external
  | .external, .unspecified | .external, .external => isExternal

theorem collapse_cli_overrides_all (attr : CollapseOpt) (ext bi : Bool) :
    getCollapseDebuginfo .yes attr ext bi = true ∧
    getCollapseDebuginfo .no attr ext bi = false := by
  cases attr <;> cases bi <;> exact ⟨rfl, rfl⟩

theorem collapse_default_and_external_behavior (ext : Bool) :
    getCollapseDebuginfo .unspecified .unspecified ext false = ext ∧
    getCollapseDebuginfo .unspecified .external ext false = ext ∧
    getCollapseDebuginfo .unspecified .yes ext false = true ∧
    getCollapseDebuginfo .unspecified .no ext false = false ∧
    getCollapseDebuginfo .unspecified .unspecified ext true = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end RustcDwarfNicheGdbSoundness
