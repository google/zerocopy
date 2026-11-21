import Toy.WrapNiche.Corollaries
import Toy.WrapNiche.Examples

/-!
# Witnesses (fully proved): non-vacuity, counterexamples, positive controls

Naming: `nv_<result>` states that a concrete instance satisfies all hypotheses of a main
result (for hypothesis-free results: the instance and its conclusion, checked);
`cex_<result>_<hyp>` states that a concrete instance satisfies every hypothesis of a main
result except `<hyp>` and the conclusion fails; `pc_<result>` is a positive control for an
impossibility; `cex_folklore_<name>` refutes an informal claim discussed in the report;
`ex_<name>` is an illustrative instance.
-/

namespace Toy.WrapNiche

open Imported

/-! ## Group 1 -/

/-- Instance of `mem_iff_offset_le_offset` (no hypotheses), conclusion checked: `[255, 0]`
mod 256 at `x = 0`. -/
theorem nv_mem_iff_offset_le_offset :
    ((⟨255, 0⟩ : WrapInterval 256).Mem 0 ↔ offset (255 : Fin 256) 0 ≤ offset (255 : Fin 256) 0) ∧
      (⟨255, 0⟩ : WrapInterval 256).Mem 0 := by decide +kernel

theorem nv_compl_mem_iff_not_mem_of_size_lt : (⟨255, 0⟩ : WrapInterval 256).size < 256 := by
  decide

/-- Dropping `size < M`: for the full interval `[0, 3]` of `Fin 4`, `[e + 1, s - 1]` is again
`[0, 3]`, which contains `0` although `0` is a member. -/
theorem cex_compl_mem_iff_not_mem_of_size_lt_hI :
    ¬ (⟨0, 3⟩ : WrapInterval 4).size < 4 ∧
      ¬ ((⟨0, 3⟩ : WrapInterval 4).compl.Mem 0 ↔ ¬ (⟨0, 3⟩ : WrapInterval 4).Mem 0) := by decide +kernel

/-- Instance of `originTest_exactFor_iff_offset_le` (no hypotheses), conclusion checked. -/
theorem nv_originTest_exactFor_iff_offset_le :
    (ExactFor (originTest (0 : Fin 8)) ⟨2, 5⟩ ↔ offset (0 : Fin 8) 2 ≤ offset (0 : Fin 8) 5) ∧
      ExactFor (originTest (0 : Fin 8)) ⟨2, 5⟩ := by decide +kernel

/-- Folklore "a range check is `s ≤ x ≤ e`" fails on `[255, 0]` mod 256 at `x = 255`. -/
theorem cex_folklore_unsignedTest_255_0 :
    (⟨255, 0⟩ : WrapInterval 256).Mem 255 ∧ ¬ unsignedTest (⟨255, 0⟩ : WrapInterval 256) 255 := by decide +kernel

/-- The fixed signed (`i8`) test fails on `[127, 128]` mod 256, which wraps at the signed
boundary: `127` is a member but `127 ≤ toI8 127 ≤ toI8 128 = -128` is false. -/
theorem cex_folklore_signedTestI8_127_128 :
    (⟨127, 128⟩ : WrapInterval 256).Mem 127 ∧ ¬ signedTestI8 ⟨127, 128⟩ 127 := by decide +kernel

/-- Each fixed test is exact on some wrapping intervals: the signed test on `[255, 0]`, the
unsigned test on `[127, 128]`. -/
theorem pc_signed_and_unsigned_exact_elsewhere :
    ExactFor signedTestI8 ⟨255, 0⟩ ∧ ExactFor unsignedTest (⟨127, 128⟩ : WrapInterval 256) := by
  decide +kernel

theorem nv_not_exactFor_originTest_wrapSub_one_of_two_le : 2 ≤ 256 := by decide +kernel

/-- Dropping `2 ≤ M`: for `M = 1` (so `2 ≤ M` fails) the fixed-origin test at `0` is exact for
the only interval `[0 - 1, 0] = [0, 0]`, so the conclusion fails. -/
theorem cex_not_exactFor_originTest_wrapSub_one_of_two_le_hM :
    ¬ 2 ≤ 1 ∧ ¬ ¬ ExactFor (originTest (0 : Fin 1)) ⟨wrapSub 0 1, 0⟩ := by decide +kernel

/-- Positive control (escape hatch): the two-branch test with a fixed origin `o` is exact for
every interval, for every `M` and every origin. -/
theorem pc_twoBranchTest_exactFor {M : Nat} (o : Fin M) (I : WrapInterval M) :
    ExactFor (twoBranchTest o) I := by
  intro x
  unfold twoBranchTest
  by_cases h : offset o I.s ≤ offset o I.e
  · simp only [h, ↓reduceIte]
    exact (originTest_exactFor_iff_offset_le o I).mpr h x
  · simp only [h, ↓reduceIte]
    rw [mem_iff_offset_le_offset, offset_shift o I.s x, offset_shift o I.s I.e]
    have hos := offset_lt o I.s
    have hoe := offset_lt o I.e
    have hox := offset_lt o x
    have he' : (offset o I.e + (M - offset o I.s)) % M = offset o I.e + (M - offset o I.s) :=
      Nat.mod_eq_of_lt (by omega)
    rw [he']
    by_cases hx : offset o I.s ≤ offset o x
    · rw [show offset o x + (M - offset o I.s) = (offset o x - offset o I.s) + M by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
    · rw [Nat.mod_eq_of_lt (by omega)]; omega

/-- Positive control (escape hatch), checked for every origin and interval of `Fin 8`: the
fixed-origin test applied to the interval when it does not wrap past the origin, and the
negated fixed-origin test applied to `[e + 1, s - 1]` otherwise, is exact. -/
theorem pc_complTest_exactFor_fin8 : ∀ (o : Fin 8) (I : WrapInterval 8),
    ExactFor (fun J y => if offset o J.s ≤ offset o J.e then originTest o J y
      else ¬ originTest o J.compl y) I := by decide +kernel

/-- Positive control: the single-subtraction test (the fixed-origin test whose origin is the
interval's own start) is exact for every interval of `Fin 8`. -/
theorem pc_subTest_exactFor_all_fin8 : ∀ I : WrapInterval 8, ExactFor subTest I := by decide +kernel

/-! ## Group 2 -/

/-- Instance of `affineLayout_eq_nicheLayoutK_affineTags` (no hypotheses), conclusion checked
pointwise on decoders (encoders agree definitionally), including a colliding span `300 ≥ 256`. -/
theorem nv_affineLayout_eq_nicheLayoutK_affineTags :
    (∀ p, (affineLayout Vmid A0).dec p = (nicheLayoutK Vmid (affineTags A0)).dec p) ∧
    (∀ p, (affineLayout Vmid ⟨0, 300, 7⟩).dec p =
      (nicheLayoutK Vmid (affineTags (⟨0, 300, 7⟩ : AffineNiche 256))).dec p) := by
  decide +kernel

/-- Both sides of `affineLayout_lawful_iff_span_lt_and_tagsDisjoint` hold for wrapping tags
`254, 255, 0` over valid values `1..=253`. -/
theorem nv_affineLayout_lawful_iff_span_lt_and_tagsDisjoint :
    A0.span < 256 ^ 1 ∧ TagsDisjoint Vmid A0.nicheStart A0.span := by decide +kernel

/-- The tag condition is needed: with every value valid, the valid payload `254` is decoded as
the niche variant of relative index 0, and the layout is not lawful (`span < 256` holds). -/
theorem cex_affineLayout_lawful_overlap :
    A0.span < 256 ^ 1 ∧ ¬ TagsDisjoint (allV 1) A0.nicheStart A0.span ∧
      (affineLayout (allV 1) A0).dec 254 = some (.inl ⟨0, by decide +kernel⟩) ∧
      ¬ Lawful (affineLayout (allV 1) A0) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, ex_affineLayout_neg⟩

/-- The span condition is needed: with no valid value every tag is invalid, but for
`span = 256` the tags of relative indices `0` and `256` coincide and the layout is not lawful. -/
theorem cex_affineLayout_lawful_span :
    ¬ (⟨0, 256, 0⟩ : AffineNiche (256 ^ 1)).span < 256 ^ 1 ∧
      TagsDisjoint (fun _ : Pat 1 => false) 0 256 ∧
      ¬ Lawful (affineLayout (fun _ : Pat 1 => false) ⟨0, 256, 0⟩) := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro h
  have h1 := h.1 (.inl ⟨256, by decide +kernel⟩)
  revert h1
  decide

/-- An instance of the general-shape example layout with `span < M` and disjoint tags (generic
`M = 8`: tags `5, 6, 7`, valid values `0..=4`). -/
theorem nv_classify_valid_iff_and_decodeIdx_of_span_lt_of_tagsDisjoint :
    (⟨0, 2, 5⟩ : AffineNiche 8).span < 8 ∧
      TagsDisjoint (fun x : Fin 8 => decide (x.val < 5)) 5 2 := by decide +kernel

/-- Dropping the tag condition: with every value valid, the tag `5` is valid but classified
`liveTag` (other hypothesis `span < 8` holds). -/
theorem cex_classify_valid_iff_and_decodeIdx_hdisj :
    (⟨0, 2, 5⟩ : AffineNiche 8).span < 8 ∧ ¬ TagsDisjoint (fun _ : Fin 8 => true) 5 2 ∧
      ¬ ((classify E1 ⟨0, 2, 5⟩ (fun _ : Fin 8 => true) 5 = .valid ↔
        (fun _ : Fin 8 => true) 5 = true) ∧
      (classify E1 ⟨0, 2, 5⟩ (fun _ : Fin 8 => true) 5 = .valid →
        decodeIdx E1.u ⟨0, 2, 5⟩ (5 : Fin 8) = E1.u) ∧
      (classify E1 ⟨0, 2, 5⟩ (fun _ : Fin 8 => true) 5 = .unusedNiche →
        decodeIdx E1.u ⟨0, 2, 5⟩ (5 : Fin 8) = E1.u) ∧
      (∀ r, r ≤ 2 → (5 : Fin 8) = (⟨0, 2, 5⟩ : AffineNiche 8).tagOf r →
        decodeIdx E1.u ⟨0, 2, 5⟩ (5 : Fin 8) = 0 + r ∧
          (⟨0, 2, 5⟩ : AffineNiche 8).tagInterval.Mem 5) ∧
      (classify E1 ⟨0, 2, 5⟩ (fun _ : Fin 8 => true) 5 = .liveTag ∨
          classify E1 ⟨0, 2, 5⟩ (fun _ : Fin 8 => true) 5 = .deadTag →
        ∃ r, r ≤ 2 ∧ (5 : Fin 8) = (⟨0, 2, 5⟩ : AffineNiche 8).tagOf r ∧
          decodeIdx E1.u ⟨0, 2, 5⟩ (5 : Fin 8) = 0 + r)) := by decide +kernel

/-- Dropping `span < M`: for `M = 2`, `span = 2`, no valid value, the tag of relative index
`2` is `0`, which decodes to `first + 0`, not `first + 2`. -/
theorem cex_classify_valid_iff_and_decodeIdx_hspan :
    ¬ (⟨0, 2, 0⟩ : AffineNiche 2).span < 2 ∧ TagsDisjoint (fun _ : Fin 2 => false) 0 2 ∧
      ¬ ((classify E1 ⟨0, 2, 0⟩ (fun _ : Fin 2 => false) 0 = .valid ↔
        (fun _ : Fin 2 => false) 0 = true) ∧
      (classify E1 ⟨0, 2, 0⟩ (fun _ : Fin 2 => false) 0 = .valid →
        decodeIdx E1.u ⟨0, 2, 0⟩ (0 : Fin 2) = E1.u) ∧
      (classify E1 ⟨0, 2, 0⟩ (fun _ : Fin 2 => false) 0 = .unusedNiche →
        decodeIdx E1.u ⟨0, 2, 0⟩ (0 : Fin 2) = E1.u) ∧
      (∀ r, r ≤ 2 → (0 : Fin 2) = (⟨0, 2, 0⟩ : AffineNiche 2).tagOf r →
        decodeIdx E1.u ⟨0, 2, 0⟩ (0 : Fin 2) = 0 + r ∧
          (⟨0, 2, 0⟩ : AffineNiche 2).tagInterval.Mem 0) ∧
      (classify E1 ⟨0, 2, 0⟩ (fun _ : Fin 2 => false) 0 = .liveTag ∨
          classify E1 ⟨0, 2, 0⟩ (fun _ : Fin 2 => false) 0 = .deadTag →
        ∃ r, r ≤ 2 ∧ (0 : Fin 2) = (⟨0, 2, 0⟩ : AffineNiche 2).tagOf r ∧
          decodeIdx E1.u ⟨0, 2, 0⟩ (0 : Fin 2) = 0 + r)) := by decide +kernel

theorem nv_genLayout_dec_isSome_iff_classify_of_span_lt : Ag.span < 256 ^ 1 := by decide +kernel

/-- Dropping `span < M`: with `span = 256` the tag interval is `[0, 0]`, so `1` is classified
`unusedNiche`, yet the checked decoder accepts it as live variant `1`. -/
theorem cex_genLayout_dec_isSome_iff_classify_hspan :
    ¬ (⟨0, 256, 0⟩ : AffineNiche (256 ^ 1)).span < 256 ^ 1 ∧
      ¬ (((genLayout ⟨258, 257, fun _ => true⟩ ⟨0, 256, 0⟩ (fun _ : Pat 1 => false)).dec 1).isSome
          = true ↔
        (classify ⟨258, 257, fun _ => true⟩ ⟨0, 256, 0⟩ (fun _ : Pat 1 => false) 1 = .valid ∨
          classify ⟨258, 257, fun _ => true⟩ ⟨0, 256, 0⟩ (fun _ : Pat 1 => false) 1 = .liveTag))
    := by decide +kernel

theorem nv_genLayout_lawful_of_span_lt_of_tagsDisjoint_of_liveInRange :
    Ag.span < 256 ^ 1 ∧ TagsDisjoint Vlow Ag.nicheStart Ag.span ∧ LiveInRange E1 Ag := by decide +kernel

/-- Dropping `span < M`: 257 live variants in a 256-value field; the tags of variants `0` and
`256` coincide. -/
theorem cex_genLayout_lawful_hspan :
    ¬ (⟨0, 256, 0⟩ : AffineNiche (256 ^ 1)).span < 256 ^ 1 ∧
      TagsDisjoint (fun _ : Pat 1 => false) 0 256 ∧
      LiveInRange ⟨258, 257, fun _ => true⟩ (⟨0, 256, 0⟩ : AffineNiche (256 ^ 1)) ∧
      ¬ Lawful (genLayout ⟨258, 257, fun _ => true⟩ ⟨0, 256, 0⟩ (fun _ : Pat 1 => false)) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro h
  have h1 := h.1 (.inl ⟨256, by decide +kernel⟩)
  revert h1
  decide

/-- Dropping the tag condition: every value valid; the valid payload `253` is decoded as
variant `0`. -/
theorem cex_genLayout_lawful_hdisj :
    Ag.span < 256 ^ 1 ∧ ¬ TagsDisjoint (allV 1) Ag.nicheStart Ag.span ∧ LiveInRange E1 Ag ∧
      ¬ Lawful (genLayout E1 Ag (allV 1)) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, ex_genLayout_neg⟩

/-- Dropping the tag condition at a dead slot: valid values `0..=252` and `254`; the valid
payload `254` sits at the dead slot of `u` (classified `deadTag`), the checked decoder rejects
it, and the layout is not lawful. -/
theorem cex_genLayout_lawful_hdisj_deadSlot :
    Ag.span < 256 ^ 1 ∧
      ¬ TagsDisjoint (fun x : Pat 1 => decide (x.val < 253 ∨ x.val = 254)) Ag.nicheStart Ag.span ∧
      LiveInRange E1 Ag ∧
      classify E1 Ag (fun x : Pat 1 => decide (x.val < 253 ∨ x.val = 254)) 254 = .deadTag ∧
      (genLayout E1 Ag (fun x : Pat 1 => decide (x.val < 253 ∨ x.val = 254))).dec 254 = none ∧
      ¬ Lawful (genLayout E1 Ag (fun x : Pat 1 => decide (x.val < 253 ∨ x.val = 254))) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, ?_⟩
  intro h
  have h1 := h.1 (.inr ⟨254, by decide⟩)
  revert h1
  decide

/-- Dropping `LiveInRange`: range `[1, 2]` misses live variant `0`, whose encoding (relative
index `0 - 1 = 0`, truncated) decodes to the dead slot of `u = 1`. -/
theorem cex_genLayout_lawful_hlive :
    (⟨1, 1, 253⟩ : AffineNiche (256 ^ 1)).span < 256 ^ 1 ∧ TagsDisjoint Vlow 253 1 ∧
      ¬ LiveInRange E1 (⟨1, 1, 253⟩ : AffineNiche (256 ^ 1)) ∧
      ¬ Lawful (genLayout E1 ⟨1, 1, 253⟩ Vlow) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro h
  have h1 := h.1 (.inl ⟨0, by decide +kernel⟩)
  revert h1
  decide

/-- `span < 256 ^ n` is not necessary for lawfulness of `genLayout`: 256 live variants and the
untagged variant `u = 256` at relative index `256` (a dead slot), no valid payload value. -/
theorem ex_genLayout_lawful_span_eq_card :
    ¬ (⟨0, 256, 0⟩ : AffineNiche (256 ^ 1)).span < 256 ^ 1 ∧
      Lawful (genLayout ⟨257, 256, fun _ => true⟩ ⟨0, 256, 0⟩ (fun _ : Pat 1 => false)) :=
  ⟨by decide +kernel, by unfold DecEnc; decide +kernel, canonical_of_forall_pat _ (by decide +kernel)⟩

/-- Folklore "every tag in the niche interval encodes a variant" fails: `254` lies in the tag
interval `[253, 255]` at the dead slot of `u`; the single-subtraction decoder returns `u` and
the checked decoder rejects it. -/
theorem cex_folklore_dead_slot :
    Ag.tagInterval.Mem 254 ∧ classify E1 Ag Vlow 254 = .deadTag ∧
      decodeIdx E1.u Ag 254 = E1.u ∧ (genLayout E1 Ag Vlow).dec 254 = none := by decide +kernel

/-! ## Group 3 -/

theorem nv_exists_tagsDisjoint_iff_span_succ_le_sub_size_of_isHull :
    (∃ x, V01 x = true) ∧ IsHull V01 ⟨0, 1⟩ := by decide +kernel

/-- Dropping "some value is valid": with no valid value the hull is a singleton, yet all four
values can be tags (`span = 3`). -/
theorem cex_exists_tagsDisjoint_iff_span_succ_le_hne :
    ¬ (∃ x, (fun _ : Fin 4 => false) x = true) ∧ IsHull (fun _ : Fin 4 => false) ⟨0, 0⟩ ∧
      ¬ ((∃ ns : Fin 4, TagsDisjoint (fun _ => false) ns 3) ↔
        3 + 1 ≤ 4 - (⟨0, 0⟩ : WrapInterval 4).size) := by decide +kernel

/-- Dropping the hull condition: `[0, 1]` covers `{0}` but is not smallest. -/
theorem cex_exists_tagsDisjoint_iff_span_succ_le_hH :
    (∃ x, V0 x = true) ∧ ¬ IsHull V0 ⟨0, 1⟩ ∧
      ¬ ((∃ ns : Fin 4, TagsDisjoint V0 ns 2) ↔ 2 + 1 ≤ 4 - (⟨0, 1⟩ : WrapInterval 4).size) := by
  decide

/-- Fragmented validity costs capacity: `{0, 2}` in `Fin 4` has hull `[0, 2]`, contiguous
capacity `1`, but two niches. -/
theorem cex_folklore_fragmented_capacity_lt_nichesCount :
    IsHull V02 ⟨0, 2⟩ ∧ 4 - (⟨0, 2⟩ : WrapInterval 4).size < nichesCount V02 ∧
      ¬ (∃ ns : Fin 4, TagsDisjoint V02 ns 1) := by decide +kernel

/-- `[0, 2]` covers `{0, 2}` in `Fin 4` (it is also a hull); `[0, 3]` covers it and is not a hull. -/
theorem nv_sub_size_le_nichesCount_and_eq_iff_of_covers :
    Covers (⟨0, 2⟩ : WrapInterval 4) V02 ∧ Covers (⟨0, 3⟩ : WrapInterval 4) V02 := by decide +kernel

/-- Dropping the covering condition: `[0, 0]` does not cover `{0, 1}`, and `4 - 1 ≤ 2` fails. -/
theorem cex_sub_size_le_nichesCount_and_eq_iff_of_covers_hcov :
    ¬ Covers (⟨0, 0⟩ : WrapInterval 4) V01 ∧
      ¬ (4 - (⟨0, 0⟩ : WrapInterval 4).size ≤ nichesCount V01 ∧
        (4 - (⟨0, 0⟩ : WrapInterval 4).size = nichesCount V01 ↔
          ∀ x, (⟨0, 0⟩ : WrapInterval 4).Mem x → V01 x = true)) := by decide +kernel

/-- The minimality half of `IsHull` is tight for
`sub_size_eq_nichesCount_iff_isWrapIntervalSet_of_isHull` (witness class `M = 4`, `V = {0, 1}`,
`H = [0, 2]`): `[0, 2]` covers `{0, 1}` but is not a hull, and `4 - 3 = 2` fails. -/
theorem cex_sub_size_eq_nichesCount_iff_isWrapIntervalSet_hH :
    Covers (⟨0, 2⟩ : WrapInterval 4) V01 ∧ ¬ IsHull V01 ⟨0, 2⟩ ∧
      ¬ (4 - (⟨0, 2⟩ : WrapInterval 4).size = nichesCount V01 ↔ IsWrapIntervalSet V01) := by
  decide +kernel

/-- Instance of `nichesCount_intervalV` (no hypotheses), conclusion checked. -/
theorem nv_nichesCount_intervalV :
    nichesCount (intervalV (⟨3, 1⟩ : WrapInterval 4)) = 4 - (⟨3, 1⟩ : WrapInterval 4).size := by
  decide

/-! ## Group 4 -/

theorem nv_exists_tagsDisjoint_naturalSpan_iff_untagged_first_or_last :
    (∃ x, V01 x = true) ∧ IsHull V01 ⟨0, 1⟩ ∧ 2 ≤ 3 ∧ 4 - (⟨0, 1⟩ : WrapInterval 4).size = 3 - 1 :=
  by decide +kernel

/-- Dropping "some value is valid": `M = 3`, no valid value, `k = 3`, `u = 1` in the middle,
yet the three natural tags fit. -/
theorem cex_naturalSpan_hne :
    ¬ (∃ x, (fun _ : Fin 3 => false) x = true) ∧ IsHull (fun _ : Fin 3 => false) ⟨0, 0⟩ ∧
      2 ≤ 3 ∧ 3 - (⟨0, 0⟩ : WrapInterval 3).size = 3 - 1 ∧
      ¬ ((∃ ns : Fin 3, TagsDisjoint (fun _ => false) ns (naturalSpan 3 1)) ↔
        (1 = 0 ∨ 1 = 3 - 1)) := by decide +kernel

/-- Dropping the hull condition: `[0, 1]` covers `{0}` but is not smallest; `u = 1` in the
middle, yet the natural tags `1, 2, 3` fit. -/
theorem cex_naturalSpan_hH :
    (∃ x, V0 x = true) ∧ ¬ IsHull V0 ⟨0, 1⟩ ∧ 2 ≤ 3 ∧
      4 - (⟨0, 1⟩ : WrapInterval 4).size = 3 - 1 ∧
      ¬ ((∃ ns : Fin 4, TagsDisjoint V0 ns (naturalSpan 3 1)) ↔ (1 = 0 ∨ 1 = 3 - 1)) := by decide +kernel

/-- Dropping `2 ≤ k`: `k = 1`, `u = 0`, no niche; the right side holds, the left side fails
(the natural span is `0`, truncated, and still needs one niche). -/
theorem cex_naturalSpan_hk :
    (∃ x, (fun _ : Fin 2 => true) x = true) ∧ IsHull (fun _ : Fin 2 => true) ⟨0, 1⟩ ∧
      ¬ 2 ≤ 1 ∧ 2 - (⟨0, 1⟩ : WrapInterval 2).size = 1 - 1 ∧
      ¬ ((∃ ns : Fin 2, TagsDisjoint (fun _ => true) ns (naturalSpan 1 0)) ↔
        (0 = 0 ∨ 0 = 1 - 1)) := by decide +kernel

/-- Dropping the exact-capacity condition: with `k` (not `k - 1`) values outside the hull, the
middle position also fits. -/
theorem cex_naturalSpan_hcap :
    (∃ x, V0 x = true) ∧ IsHull V0 ⟨0, 0⟩ ∧ 2 ≤ 3 ∧
      4 - (⟨0, 0⟩ : WrapInterval 4).size ≠ 3 - 1 ∧
      ¬ ((∃ ns : Fin 4, TagsDisjoint V0 ns (naturalSpan 3 1)) ↔ (1 = 0 ∨ 1 = 3 - 1)) := by decide +kernel

/-- Declaration order matters with the multiset of variant payloads fixed: one-byte payload
with valid values `0..=253` (two niches), three variants. With `u` first or last the natural
range fits; with `u` in the middle it does not; yet an enum with two dataless variants over
this payload has a lawful layout in one byte (imported cardinality theorem, lookup decoder). -/
theorem cex_folklore_fit_depends_on_untagged_position :
    (∃ ns : Fin 256, TagsDisjoint Vlt254 ns (naturalSpan 3 0)) ∧
      (∃ ns : Fin 256, TagsDisjoint Vlt254 ns (naturalSpan 3 2)) ∧
      ¬ (∃ ns : Fin 256, TagsDisjoint Vlt254 ns (naturalSpan 3 1)) ∧
      (∃ L : Layout (ExtEnum 2 Vlt254) 1, Lawful L) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  exact (le_numInvalid_iff_exists_lawful_layout_iff_lawful_nicheLayoutK_firstNiches Vlt254 2).1.1
    (by decide +kernel)

/-- All hypotheses of `rotDecodeIdx_exact_of_lt_of_le_succ_of_rotTagsInvalid` hold for `k = 3`,
`u = 1`, start `254`, valid values `0..=253`; and for `k = 1`, `u = 0` over a two-value field
with every value valid (no rotated tag is needed). -/
theorem nv_rotDecodeIdx_exact :
    (1 < 3 ∧ 3 ≤ 256 + 1 ∧ RotTagsInvalid Vlt254 3 254) ∧
      (0 < 1 ∧ 1 ≤ 2 + 1 ∧ RotTagsInvalid (fun _ : Fin 2 => true) 1 0) := by decide +kernel

/-- Dropping `u < k`: `k = 2`, `u = 2`; variant `0` gets rotated index `1`, which is not a
rotated index (`1 + 1 < 2` fails), so its tag decodes to `u`. -/
theorem cex_rotDecodeIdx_hu :
    ¬ 2 < 2 ∧ 2 ≤ 2 + 1 ∧ RotTagsInvalid (fun _ : Fin 2 => false) 2 0 ∧
      ¬ ((∀ i, i < 2 → i ≠ 2 → rotDecodeIdx 2 2 (0 : Fin 2) (rotTag 2 2 (0 : Fin 2) i) = i) ∧
        (∀ x, (fun _ : Fin 2 => false) x = true → rotDecodeIdx 2 2 (0 : Fin 2) x = 2)) := by
  decide +kernel

/-- Dropping `k ≤ M + 1`: `M = 2`, `k = 4`, `u = 3`; the rotated tags of variants `0` and `2`
coincide. -/
theorem cex_rotDecodeIdx_hkM :
    3 < 4 ∧ ¬ 4 ≤ 2 + 1 ∧ RotTagsInvalid (fun _ : Fin 2 => false) 4 0 ∧
      ¬ ((∀ i, i < 4 → i ≠ 3 → rotDecodeIdx 4 3 (0 : Fin 2) (rotTag 4 3 (0 : Fin 2) i) = i) ∧
        (∀ x, (fun _ : Fin 2 => false) x = true → rotDecodeIdx 4 3 (0 : Fin 2) x = 3)) := by
  decide +kernel

/-- Dropping the tag condition: every value valid; the valid value `0` is the rotated tag of
variant `1` and is not decoded to `u = 0`. -/
theorem cex_rotDecodeIdx_hdisj :
    0 < 2 ∧ 2 ≤ 4 + 1 ∧ ¬ RotTagsInvalid (fun _ : Fin 4 => true) 2 0 ∧
      ¬ ((∀ i, i < 2 → i ≠ 0 → rotDecodeIdx 2 0 (0 : Fin 4) (rotTag 2 0 (0 : Fin 4) i) = i) ∧
        (∀ x, (fun _ : Fin 4 => true) x = true → rotDecodeIdx 2 0 (0 : Fin 4) x = 0)) := by
  decide +kernel

/-! ## Group 5 -/

theorem nv_extend_spec_of_size_lt : (⟨1, 1⟩ : WrapInterval 4).size < 4 := by decide +kernel

/-- Dropping `size < M`: the full interval `[0, 3]` contains its "adjacent" value `0`, so the
conclusion fails. -/
theorem cex_extend_spec_hI :
    ¬ (⟨0, 3⟩ : WrapInterval 4).size < 4 ∧
      ¬ (¬ (⟨0, 3⟩ : WrapInterval 4).Mem (adjNiche ⟨0, 3⟩ .high) ∧
        (∀ x, (extend (⟨0, 3⟩ : WrapInterval 4) .high).Mem x ↔
          ((⟨0, 3⟩ : WrapInterval 4).Mem x ∨ x = adjNiche ⟨0, 3⟩ .high)) ∧
        (extend (⟨0, 3⟩ : WrapInterval 4) .high).size = (⟨0, 3⟩ : WrapInterval 4).size + 1) := by
  decide +kernel

/-- The `NonZero` valid range `[1, 255]` is not full. -/
theorem nv_nicheLayout_adjNiche_lawful : (⟨1, 255⟩ : WrapInterval (256 ^ 1)).size < 256 ^ 1 := by
  decide

/-- Dropping `size < M`: for the full range `[0, 255]` the reserved value `0` is valid and the
niche-filled layout is not lawful. -/
theorem cex_nicheLayout_adjNiche_lawful_hI :
    ¬ (⟨0, 255⟩ : WrapInterval (256 ^ 1)).size < 256 ^ 1 ∧
      ¬ (Lawful (nicheLayout (intervalV (⟨0, 255⟩ : WrapInterval (256 ^ 1)))
          (adjNiche ⟨0, 255⟩ .high)) ∧
        ∀ p, ((nicheLayout (intervalV (⟨0, 255⟩ : WrapInterval (256 ^ 1)))
          (adjNiche ⟨0, 255⟩ .high)).dec p).isSome =
            intervalV (extend (⟨0, 255⟩ : WrapInterval (256 ^ 1)) .high) p) := by
  refine ⟨by decide +kernel, ?_⟩
  rintro ⟨h, _⟩
  have h1 := h.1 (some ⟨0, by decide +kernel⟩)
  revert h1
  decide

/-- The innermost valid set `[1, 255]` of the imported `nonZeroV 1` (the imported
two-level impossibility `opt_opt_nonZero_no_decEnc_layout_in_payload_size` is the case
`j = 2` of `exists_lawful_extEnum_intervalV_iff_le_sub_size` up to the flattening of nested
`Option` into `ExtEnum`). -/
theorem ex_intervalV_nonZero :
    ∀ p : Pat 1, intervalV (⟨1, 255⟩ : WrapInterval (256 ^ 1)) p = nonZeroV 1 p := by decide +kernel

/-- Instance of `levelsReserveNiches_iff_length_le_and_nest_size` (no hypotheses), conclusion
checked for both all-low and all-high side choices. -/
theorem nv_levelsReserveNiches_iff_length_le_and_nest_size :
    (LevelsReserveNiches (⟨1, 1⟩ : WrapInterval 4) [.low, .low, .low] ↔ 3 ≤ 4 - 1) ∧
      (LevelsReserveNiches (⟨1, 1⟩ : WrapInterval 4) [.high, .high, .high] ↔ 3 ≤ 4 - 1) ∧
      (nest (⟨1, 1⟩ : WrapInterval 4) [.low, .low, .low]).size = 4 ∧
      (nest (⟨1, 1⟩ : WrapInterval 4) [.high, .high, .high]).size = 4 := by decide +kernel

/-- Instance of `exists_lawful_extEnum_intervalV_iff_le_sub_size` (no hypotheses): the
`NonZero` interval admits one dataless variant (via the imported cardinality theorem). -/
theorem nv_exists_lawful_extEnum_intervalV :
    ∃ L : Layout (ExtEnum 1 (intervalV (⟨1, 255⟩ : WrapInterval (256 ^ 1)))) 1, Lawful L :=
  (le_numInvalid_iff_exists_lawful_layout_iff_lawful_nicheLayoutK_firstNiches
    (intervalV (⟨1, 255⟩ : WrapInterval (256 ^ 1))) 1).1.1 (by decide +kernel)

/-- Past capacity, adjacent reservation fails and `nest` wraps: over `[1, 1]` in `Fin 4`, four
upward levels exceed `4 - 1 = 3`; the third level makes the interval full (`[1, 0]`), and the
fourth collapses it to the singleton `[1, 1]` (size `1`, not `1 + 4`). -/
theorem ex_nest_past_capacity :
    ¬ LevelsReserveNiches (⟨1, 1⟩ : WrapInterval 4) [.high, .high, .high, .high] ∧
      nest (⟨1, 1⟩ : WrapInterval 4) [.high, .high, .high] = ⟨1, 0⟩ ∧
      nest (⟨1, 1⟩ : WrapInterval 4) [.high, .high, .high, .high] = ⟨1, 1⟩ ∧
      (nest (⟨1, 1⟩ : WrapInterval 4) [.high, .high, .high, .high]).size = 1 := by decide +kernel

/-- A non-adjacent reservation is lawful for one level but fragments the valid set: over
`[0, 1]` in `Fin 8`, reserving `4` gives `{0, 1, 4}`, which is not a wrapping interval and has
hull `[0, 4]`; four contiguous tags no longer fit, whereas after adjacent reservation (`[0, 2]`)
five do. Both sets have five niches. -/
theorem cex_folklore_nonadjacent_reservation_fragments :
    intervalV (⟨0, 1⟩ : WrapInterval 8) 4 = false ∧
      ¬ IsWrapIntervalSet (fun x : Fin 8 => intervalV ⟨0, 1⟩ x || x == 4) ∧
      IsHull (fun x : Fin 8 => intervalV ⟨0, 1⟩ x || x == 4) ⟨0, 4⟩ ∧
      ¬ (∃ ns : Fin 8, TagsDisjoint (fun x => intervalV ⟨0, 1⟩ x || x == 4) ns 3) ∧
      (∃ ns : Fin 8, TagsDisjoint (intervalV (extend (⟨0, 1⟩ : WrapInterval 8) .high)) ns 4) ∧
      nichesCount (fun x : Fin 8 => intervalV ⟨0, 1⟩ x || x == 4) = 5 ∧
      nichesCount (intervalV (extend (⟨0, 1⟩ : WrapInterval 8) .high)) = 5 := by decide +kernel

/-! ## Group 6 -/

/-- `Lop` with every value valid (so tags overlap valid values). -/
def LopAll : OpLayout := { Lop with V := allV 1 }

theorem nv_setDisc_operational_untagged_isSome_iff :
    TagsDisjoint Lop.V Lop.A.nicheStart Lop.A.span := by decide +kernel

/-- Dropping the tag condition: the valid value `253` is variant `0`'s tag, so after writing it
(the niche field lies inside the three-byte place) operational `SetDiscriminant u` is undefined
behaviour, and the conclusion fails. -/
theorem cex_setDisc_operational_untagged_isSome_iff_hdisj :
    ¬ TagsDisjoint LopAll.V LopAll.A.nicheStart LopAll.A.span ∧
      LopAll.no + LopAll.nw ≤ uninit3.length ∧ LopAll.V 253 = true ∧
      (setDisc .operational LopAll LopAll.E.u (LopAll.writeNiche uninit3 253)).isSome = false ∧
      ¬ ((∀ p, (setDisc .operational LopAll LopAll.E.u p).isSome = true ↔
            ∃ x, LopAll.readNiche p = some x ∧ LopAll.V x = true) ∧
         (∀ p (x : Pat LopAll.nw), LopAll.no + LopAll.nw ≤ p.length →
            ((setDisc .operational LopAll LopAll.E.u (LopAll.writeNiche p x)).isSome = true ↔
              LopAll.V x = true))) := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  rintro ⟨_, h2⟩
  have h := (h2 uninit3 253 (by decide)).mpr rfl
  revert h; decide

/-- Payload write and operational `SetDiscriminant u` do not commute: from uninitialized bytes,
or from a place holding variant `0`'s tag, "`SetDiscriminant u`; write payload" is undefined
behaviour, while "write payload; `SetDiscriminant u`" is defined. -/
theorem cex_folklore_payload_write_setDisc_noncommuting :
    run .operational Lop [.write 1 [5], .setDisc 1] (uninit3, []) =
        some ([none, some 5, none], []) ∧
      run .operational Lop [.setDisc 1, .write 1 [5]] (uninit3, []) = none ∧
      run .operational Lop [.write 1 [5], .setDisc 1] ([none, some 253, none], []) =
        some ([none, some 5, none], []) ∧
      run .operational Lop [.setDisc 1, .write 1 [5]] ([none, some 253, none], []) = none := by
  decide

/-- Instance of `run_erased_eq_some_of_run_operational_eq_some` (no hypotheses), conclusion
checked. -/
theorem nv_run_erased_eq_some_of_run_operational_eq_some :
    run .operational Lop [.write 1 [5], .setDisc 1, .readDisc] (uninit3, []) =
        some ([none, some 5, none], [1]) ∧
      run .erased Lop [.write 1 [5], .setDisc 1, .readDisc] (uninit3, []) =
        some ([none, some 5, none], [1]) := by decide +kernel

/-- Erasure is not equivalent: operational `SetDiscriminant u` on uninitialized bytes is
undefined behaviour, the erased one is a no-op. -/
theorem cex_folklore_erasure_not_equivalent :
    run .operational Lop [.setDisc 1] (uninit3, []) = none ∧
      run .erased Lop [.setDisc 1] (uninit3, []) = some (uninit3, []) := by decide +kernel

/-- The write of `[9]` at byte `0` does not overlap the niche byte `1` of `Lop`; both orders of
that write and `SetDiscriminant 0` give the same place. -/
theorem nv_run_write_setDisc_comm_of_disjointFromNiche :
    Lop.DisjointFromNiche 0 ([9] : List (Fin 256)).length ∧
      run .operational Lop [.write 0 [9], .setDisc 0] (uninit3, []) =
        some ([some 9, some 253, none], []) ∧
      run .operational Lop [.setDisc 0, .write 0 [9]] (uninit3, []) =
        some ([some 9, some 253, none], []) := by decide +kernel

/-- Dropping disjointness: a write of `255` over the niche byte does not commute with
`SetDiscriminant 0` (in one order the tag `253` survives, in the other it is clobbered and the
value then reads as variant `2`). -/
theorem cex_run_write_setDisc_comm_hdis :
    ¬ Lop.DisjointFromNiche 1 ([255] : List (Fin 256)).length ∧
      ¬ (run .operational Lop [.write 1 [255], .setDisc 0] (uninit3, []) =
          run .operational Lop [.setDisc 0, .write 1 [255]] (uninit3, [])) ∧
      run .operational Lop [.write 1 [255], .setDisc 0] (uninit3, []) =
        some ([none, some 253, none], []) ∧
      run .operational Lop [.setDisc 0, .write 1 [255], .readDisc] (uninit3, []) =
        some ([none, some 255, none], [2]) := by decide +kernel

/-- `Lop` with no valid niche value (an uninhabited untagged variant). -/
def LopNone : OpLayout := { Lop with V := fun _ => false }

/-- With an uninhabited untagged variant, operational `SetDiscriminant u` is undefined
behaviour on every place (no niche value is valid), while erased `SetDiscriminant u` is a
no-op. -/
theorem ex_setDisc_untagged_uninhabited :
    setDisc .operational LopNone LopNone.E.u [none, some 5, none] = none ∧
      setDisc .erased LopNone LopNone.E.u [none, some 5, none] = some [none, some 5, none] ∧
      (∀ p, (setDisc .operational LopNone LopNone.E.u p).isSome = true ↔
        ∃ x, LopNone.readNiche p = some x ∧ LopNone.V x = true) := by
  refine ⟨by decide, by decide, ?_⟩
  exact (setDisc_operational_untagged_isSome_iff_of_tagsDisjoint LopNone (by decide)).1

/-- All hypotheses of `run_fields_then_setDisc_readDisc_of_disjoint` hold for `Lop`, three
uninitialized bytes, and field writes at bytes `0` and `2`. -/
theorem nv_run_fields_then_setDisc_readDisc_of_disjoint :
    Lop.no + Lop.nw ≤ uninit3.length ∧ Lop.A.span < 256 ^ Lop.nw ∧
      TagsDisjoint Lop.V Lop.A.nicheStart Lop.A.span ∧
      (∀ w ∈ [((0 : Nat), [(9 : Fin 256)]), (2, [7])], w.1 + w.2.length ≤ uninit3.length) ∧
      [((0 : Nat), [(9 : Fin 256)]), (2, [7])].Pairwise
        (fun a b => a.1 + a.2.length ≤ b.1 ∨ b.1 + b.2.length ≤ a.1) ∧
      (∀ w ∈ [((0 : Nat), [(9 : Fin 256)]), (2, [7])], Lop.DisjointFromNiche w.1 w.2.length) ∧
      Lop.Encodable 0 ∧ Lop.V 0 = true := by
  decide

/-- `Lop` with the niche field moved to byte 5, outside a three-byte place. -/
def LopFar : OpLayout := { Lop with no := 5 }

/-- Dropping "the niche field lies inside the place": `SetDiscriminant 0` would write the tag
outside the place, which is undefined behaviour (no field writes). -/
theorem cex_run_fields_then_setDisc_hfit :
    ¬ (LopFar.no + LopFar.nw ≤ uninit3.length) ∧
      LopFar.A.span < 256 ^ LopFar.nw ∧
      TagsDisjoint LopFar.V LopFar.A.nicheStart LopFar.A.span ∧
      (∀ w ∈ ([] : List (Nat × List (Fin 256))), w.1 + w.2.length ≤ uninit3.length) ∧
      ([] : List (Nat × List (Fin 256))).Pairwise
        (fun a b => a.1 + a.2.length ≤ b.1 ∨ b.1 + b.2.length ≤ a.1) ∧
      (∀ w ∈ ([] : List (Nat × List (Fin 256))), LopFar.DisjointFromNiche w.1 w.2.length) ∧
      LopFar.Encodable 0 ∧
      run .operational LopFar (writesOf ([] : List (Nat × List (Fin 256))) ++ [.setDisc 0, .readDisc]) (uninit3, []) =
        none ∧
      ¬ ((∀ v, LopFar.Encodable v → ∃ q,
          run .operational LopFar (writesOf ([] : List (Nat × List (Fin 256))) ++ [.setDisc v, .readDisc]) (uninit3, []) =
            some (q, [v]) ∧
          LopFar.readNiche q = some (LopFar.A.tagOf (v - LopFar.A.first)) ∧
          ∀ w ∈ ([] : List (Nat × List (Fin 256))), readBytes q w.1 w.2.length = some w.2) ∧
        (∀ x : Pat LopFar.nw, LopFar.V x = true → ∃ q,
          run .operational LopFar (writesOf ([] : List (Nat × List (Fin 256))) ++
            [.write LopFar.no (leBytes LopFar.nw x.val), .setDisc LopFar.E.u, .readDisc]) (uninit3, []) =
            some (q, [LopFar.E.u]) ∧
          LopFar.readNiche q = some x ∧
          ∀ w ∈ ([] : List (Nat × List (Fin 256))), readBytes q w.1 w.2.length = some w.2)) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, ?_⟩
  rintro ⟨h1, _⟩
  obtain ⟨q, hq, _⟩ := h1 0 (by decide)
  have hnone : run .operational LopFar (writesOf ([] : List (Nat × List (Fin 256))) ++ [.setDisc 0, .readDisc])
      (uninit3, []) = none := by decide
  rw [hnone] at hq; cases hq

/-- A layout with 257 live variants in a one-byte field (`span = 256`, no valid value). -/
def LopWide : OpLayout := ⟨1, 1, ⟨258, 257, fun _ => true⟩, ⟨0, 256, 0⟩, fun _ => false⟩

/-- Dropping `span < 256 ^ nw`: variant `256`'s tag is `0`, which reads back as variant `0`. -/
theorem cex_run_fields_then_setDisc_hspan :
    LopWide.no + LopWide.nw ≤ uninit3.length ∧
      ¬ (LopWide.A.span < 256 ^ LopWide.nw) ∧
      TagsDisjoint LopWide.V LopWide.A.nicheStart LopWide.A.span ∧
      (∀ w ∈ ([] : List (Nat × List (Fin 256))), w.1 + w.2.length ≤ uninit3.length) ∧
      ([] : List (Nat × List (Fin 256))).Pairwise
        (fun a b => a.1 + a.2.length ≤ b.1 ∨ b.1 + b.2.length ≤ a.1) ∧
      (∀ w ∈ ([] : List (Nat × List (Fin 256))), LopWide.DisjointFromNiche w.1 w.2.length) ∧
      LopWide.Encodable 256 ∧
      run .operational LopWide (writesOf ([] : List (Nat × List (Fin 256))) ++ [.setDisc 256, .readDisc]) (uninit3, []) =
        some ([none, some 0, none], [0]) ∧
      ¬ ((∀ v, LopWide.Encodable v → ∃ q,
          run .operational LopWide (writesOf ([] : List (Nat × List (Fin 256))) ++ [.setDisc v, .readDisc]) (uninit3, []) =
            some (q, [v]) ∧
          LopWide.readNiche q = some (LopWide.A.tagOf (v - LopWide.A.first)) ∧
          ∀ w ∈ ([] : List (Nat × List (Fin 256))), readBytes q w.1 w.2.length = some w.2) ∧
        (∀ x : Pat LopWide.nw, LopWide.V x = true → ∃ q,
          run .operational LopWide (writesOf ([] : List (Nat × List (Fin 256))) ++
            [.write LopWide.no (leBytes LopWide.nw x.val), .setDisc LopWide.E.u, .readDisc]) (uninit3, []) =
            some (q, [LopWide.E.u]) ∧
          LopWide.readNiche q = some x ∧
          ∀ w ∈ ([] : List (Nat × List (Fin 256))), readBytes q w.1 w.2.length = some w.2)) := by
  refine ⟨by decide, by decide, by decide +kernel, by decide, by decide, by decide, by decide,
    by decide +kernel, ?_⟩
  rintro ⟨h1, _⟩
  obtain ⟨q, hq, _⟩ := h1 256 (by decide)
  have hres : run .operational LopWide (writesOf ([] : List (Nat × List (Fin 256))) ++ [.setDisc 256, .readDisc])
      (uninit3, []) = some ([none, some 0, none], [0]) := by decide +kernel
  rw [hres] at hq; cases hq

/-- Dropping the tag condition: the valid niche value `253` is variant `0`'s tag, so
operational `SetDiscriminant u` after writing it is undefined behaviour. -/
theorem cex_run_fields_then_setDisc_hdisj :
    LopAll.no + LopAll.nw ≤ uninit3.length ∧
      LopAll.A.span < 256 ^ LopAll.nw ∧
      ¬ (TagsDisjoint LopAll.V LopAll.A.nicheStart LopAll.A.span) ∧
      (∀ w ∈ ([] : List (Nat × List (Fin 256))), w.1 + w.2.length ≤ uninit3.length) ∧
      ([] : List (Nat × List (Fin 256))).Pairwise
        (fun a b => a.1 + a.2.length ≤ b.1 ∨ b.1 + b.2.length ≤ a.1) ∧
      (∀ w ∈ ([] : List (Nat × List (Fin 256))), LopAll.DisjointFromNiche w.1 w.2.length) ∧
      LopAll.V 253 = true ∧
      run .operational LopAll
        (writesOf ([] : List (Nat × List (Fin 256))) ++ [.write LopAll.no (leBytes LopAll.nw 253), .setDisc LopAll.E.u, .readDisc])
        (uninit3, []) = none ∧
      ¬ ((∀ v, LopAll.Encodable v → ∃ q,
          run .operational LopAll (writesOf ([] : List (Nat × List (Fin 256))) ++ [.setDisc v, .readDisc]) (uninit3, []) =
            some (q, [v]) ∧
          LopAll.readNiche q = some (LopAll.A.tagOf (v - LopAll.A.first)) ∧
          ∀ w ∈ ([] : List (Nat × List (Fin 256))), readBytes q w.1 w.2.length = some w.2) ∧
        (∀ x : Pat LopAll.nw, LopAll.V x = true → ∃ q,
          run .operational LopAll (writesOf ([] : List (Nat × List (Fin 256))) ++
            [.write LopAll.no (leBytes LopAll.nw x.val), .setDisc LopAll.E.u, .readDisc]) (uninit3, []) =
            some (q, [LopAll.E.u]) ∧
          LopAll.readNiche q = some x ∧
          ∀ w ∈ ([] : List (Nat × List (Fin 256))), readBytes q w.1 w.2.length = some w.2)) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide +kernel, ?_⟩
  rintro ⟨_, h2⟩
  obtain ⟨q, hq, _⟩ := h2 (253 : Pat LopAll.nw) rfl
  have hnone : run .operational LopAll
      (writesOf ([] : List (Nat × List (Fin 256))) ++ [.write LopAll.no (leBytes LopAll.nw (253 : Pat LopAll.nw).val),
        .setDisc LopAll.E.u, .readDisc])
      (uninit3, []) = none := by decide +kernel
  rw [hnone] at hq; cases hq

/-- Dropping "field writes lie inside the place": a two-byte write at offset `2` of a three-byte
place is undefined behaviour. -/
theorem cex_run_fields_then_setDisc_hin :
    Lop.no + Lop.nw ≤ uninit3.length ∧
      Lop.A.span < 256 ^ Lop.nw ∧
      TagsDisjoint Lop.V Lop.A.nicheStart Lop.A.span ∧
      ¬ (∀ w ∈ [((2 : Nat), [(7 : Fin 256), 8])], w.1 + w.2.length ≤ uninit3.length) ∧
      [((2 : Nat), [(7 : Fin 256), 8])].Pairwise
        (fun a b => a.1 + a.2.length ≤ b.1 ∨ b.1 + b.2.length ≤ a.1) ∧
      (∀ w ∈ [((2 : Nat), [(7 : Fin 256), 8])], Lop.DisjointFromNiche w.1 w.2.length) ∧
      run .operational Lop (writesOf [((2 : Nat), [(7 : Fin 256), 8])] ++ [.setDisc 0, .readDisc])
        (uninit3, []) = none ∧
      ¬ ((∀ v, Lop.Encodable v → ∃ q,
          run .operational Lop (writesOf [((2 : Nat), [(7 : Fin 256), 8])] ++ [.setDisc v, .readDisc]) (uninit3, []) =
            some (q, [v]) ∧
          Lop.readNiche q = some (Lop.A.tagOf (v - Lop.A.first)) ∧
          ∀ w ∈ [((2 : Nat), [(7 : Fin 256), 8])], readBytes q w.1 w.2.length = some w.2) ∧
        (∀ x : Pat Lop.nw, Lop.V x = true → ∃ q,
          run .operational Lop (writesOf [((2 : Nat), [(7 : Fin 256), 8])] ++
            [.write Lop.no (leBytes Lop.nw x.val), .setDisc Lop.E.u, .readDisc]) (uninit3, []) =
            some (q, [Lop.E.u]) ∧
          Lop.readNiche q = some x ∧
          ∀ w ∈ [((2 : Nat), [(7 : Fin 256), 8])], readBytes q w.1 w.2.length = some w.2)) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide +kernel, ?_⟩
  rintro ⟨h1, _⟩
  obtain ⟨q, hq, _⟩ := h1 0 (by decide)
  have hnone : run .operational Lop (writesOf [((2 : Nat), [(7 : Fin 256), 8])] ++
      [.setDisc 0, .readDisc]) (uninit3, []) = none := by decide +kernel
  rw [hnone] at hq; cases hq

/-- Dropping pairwise disjointness: two writes to byte `0`; the first does not read back. -/
theorem cex_run_fields_then_setDisc_hpw :
    Lop.no + Lop.nw ≤ uninit3.length ∧
      Lop.A.span < 256 ^ Lop.nw ∧
      TagsDisjoint Lop.V Lop.A.nicheStart Lop.A.span ∧
      (∀ w ∈ [((0 : Nat), [(9 : Fin 256)]), (0, [8])], w.1 + w.2.length ≤ uninit3.length) ∧
      ¬ [((0 : Nat), [(9 : Fin 256)]), (0, [8])].Pairwise
        (fun a b => a.1 + a.2.length ≤ b.1 ∨ b.1 + b.2.length ≤ a.1) ∧
      (∀ w ∈ [((0 : Nat), [(9 : Fin 256)]), (0, [8])], Lop.DisjointFromNiche w.1 w.2.length) ∧
      run .operational Lop (writesOf [((0 : Nat), [(9 : Fin 256)]), (0, [8])] ++
        [.setDisc 0, .readDisc]) (uninit3, []) = some ([some 8, some 253, none], [0]) ∧
      readBytes [some 8, some 253, none] 0 1 ≠ some [9] ∧
      ¬ ((∀ v, Lop.Encodable v → ∃ q,
          run .operational Lop (writesOf [((0 : Nat), [(9 : Fin 256)]), (0, [8])] ++ [.setDisc v, .readDisc]) (uninit3, []) =
            some (q, [v]) ∧
          Lop.readNiche q = some (Lop.A.tagOf (v - Lop.A.first)) ∧
          ∀ w ∈ [((0 : Nat), [(9 : Fin 256)]), (0, [8])], readBytes q w.1 w.2.length = some w.2) ∧
        (∀ x : Pat Lop.nw, Lop.V x = true → ∃ q,
          run .operational Lop (writesOf [((0 : Nat), [(9 : Fin 256)]), (0, [8])] ++
            [.write Lop.no (leBytes Lop.nw x.val), .setDisc Lop.E.u, .readDisc]) (uninit3, []) =
            some (q, [Lop.E.u]) ∧
          Lop.readNiche q = some x ∧
          ∀ w ∈ [((0 : Nat), [(9 : Fin 256)]), (0, [8])], readBytes q w.1 w.2.length = some w.2)) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide +kernel,
    by decide, ?_⟩
  rintro ⟨h1, _⟩
  obtain ⟨q, hq, _, hrb⟩ := h1 0 (by decide)
  have hres : run .operational Lop (writesOf [((0 : Nat), [(9 : Fin 256)]), (0, [8])] ++
      [.setDisc 0, .readDisc]) (uninit3, []) = some ([some 8, some 253, none], [0]) := by
    decide +kernel
  rw [hres] at hq; cases hq
  have hbad := hrb ((0 : Nat), [(9 : Fin 256)]) (List.mem_cons_self ..)
  revert hbad; decide

/-- Dropping disjointness from the niche field: a field write to byte `1` is overwritten by the
tag of variant `0`. -/
theorem cex_run_fields_then_setDisc_hws :
    Lop.no + Lop.nw ≤ uninit3.length ∧
      Lop.A.span < 256 ^ Lop.nw ∧
      TagsDisjoint Lop.V Lop.A.nicheStart Lop.A.span ∧
      (∀ w ∈ [((1 : Nat), [(9 : Fin 256)])], w.1 + w.2.length ≤ uninit3.length) ∧
      [((1 : Nat), [(9 : Fin 256)])].Pairwise
        (fun a b => a.1 + a.2.length ≤ b.1 ∨ b.1 + b.2.length ≤ a.1) ∧
      ¬ (∀ w ∈ [((1 : Nat), [(9 : Fin 256)])], Lop.DisjointFromNiche w.1 w.2.length) ∧
      run .operational Lop (writesOf [((1 : Nat), [(9 : Fin 256)])] ++ [.setDisc 0, .readDisc])
        (uninit3, []) = some ([none, some 253, none], [0]) ∧
      readBytes [none, some 253, none] 1 1 ≠ some [9] ∧
      ¬ ((∀ v, Lop.Encodable v → ∃ q,
          run .operational Lop (writesOf [((1 : Nat), [(9 : Fin 256)])] ++ [.setDisc v, .readDisc]) (uninit3, []) =
            some (q, [v]) ∧
          Lop.readNiche q = some (Lop.A.tagOf (v - Lop.A.first)) ∧
          ∀ w ∈ [((1 : Nat), [(9 : Fin 256)])], readBytes q w.1 w.2.length = some w.2) ∧
        (∀ x : Pat Lop.nw, Lop.V x = true → ∃ q,
          run .operational Lop (writesOf [((1 : Nat), [(9 : Fin 256)])] ++
            [.write Lop.no (leBytes Lop.nw x.val), .setDisc Lop.E.u, .readDisc]) (uninit3, []) =
            some (q, [Lop.E.u]) ∧
          Lop.readNiche q = some x ∧
          ∀ w ∈ [((1 : Nat), [(9 : Fin 256)])], readBytes q w.1 w.2.length = some w.2)) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide +kernel,
    by decide, ?_⟩
  rintro ⟨h1, _⟩
  obtain ⟨q, hq, _, hrb⟩ := h1 0 (by decide)
  have hres : run .operational Lop (writesOf [((1 : Nat), [(9 : Fin 256)])] ++
      [.setDisc 0, .readDisc]) (uninit3, []) = some ([none, some 253, none], [0]) := by
    decide +kernel
  rw [hres] at hq; cases hq
  have hbad := hrb ((1 : Nat), [(9 : Fin 256)]) (List.mem_cons_self ..)
  revert hbad; decide

end Toy.WrapNiche
