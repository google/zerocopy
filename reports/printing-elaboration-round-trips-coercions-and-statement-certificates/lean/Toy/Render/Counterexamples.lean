import Toy.Render.Examples
import Toy.Render.Statements

/-!
# Counterexample results and tightness counterexamples (`Toy.Render`)

The short counterexample results of the package, fully proved by evaluation, and,
for each hypothesis of a main statement marked `tight`, a concrete instance in
canonical form: the other hypotheses hold (if any) and the conclusion fails.
-/

namespace Toy.Render

/-! ## Counterexample results -/

/-- **The default printer is not injective, and the collision changes truth.**
`(2 : Nat) - 3 = 0` and `(2 : Int) - 3 = 0` are distinct terms with the same default
text `2 - 3 = 0`; the first is valid, the second is not; consequently no reader
(any function from text to terms) recovers both from their default text. -/
theorem ppDefault_collision_natSub_intSub_changes_truth :
    tNatSub ≠ tIntSub ∧ ppDefault tNatSub = ppDefault tIntSub ∧
      Valid S₀ tNatSub ∧ ¬ Valid S₀ tIntSub ∧
      ∀ R : Reader, R S₀ (ppDefault tNatSub) ≠ some tNatSub ∨
        R S₀ (ppDefault tIntSub) ≠ some tIntSub := by
  refine ⟨by decide, by decide, valid_tNatSub, not_valid_tIntSub, ?_⟩
  intro R
  by_cases h : R S₀ (ppDefault tNatSub) = some tNatSub
  · right
    intro h'
    rw [show ppDefault tIntSub = ppDefault tNatSub by decide, h] at h'
    exact absurd (Option.some.inj h') (by decide)
  · exact .inl h

/-- **Positive control for the collision.** The explicit printer separates the two
terms, and the system elaborator recovers each from its explicit text. -/
theorem ppExplicit_separates_natSub_intSub :
    ppExplicit tNatSub ≠ ppExplicit tIntSub ∧
      elabSys S₀ (ppExplicit tNatSub) = some tNatSub ∧
      elabSys S₀ (ppExplicit tIntSub) = some tIntSub := by
  decide

/-- `a - b = a - b` at `Nat` is valid. -/
theorem valid_tReread : Valid S₀ tReread := by
  intro ρ
  simp [Denote, eval, S₀, evalD, evalWith, tReread, vA, vB, Val.toNat, Val.toBool]

/-- `↑(a - b) = ↑a - ↑b` is false at `a = 0`, `b = 1`. -/
theorem not_valid_tTrunc : ¬ Valid S₀ tTrunc := fun h => absurd (h ρ₀) (by decide)

/-- **A textual round trip does not certify the term.** The default text of
`↑(a - b) = ↑a - ↑b` (at `Int`) is `a - b = a - b`; it re-prints identically after
re-reading, but it re-reads as the `Nat` tautology `a - b = a - b`, a different term
that is valid although the original is not (the original fails at `a = 0, b = 1`). -/
theorem textual_round_trip_passes_on_tTrunc_but_term_and_truth_change :
    (elabSys S₀ (ppDefault tTrunc)).map ppDefault = some (ppDefault tTrunc) ∧
      elabSys S₀ (ppDefault tTrunc) = some tReread ∧ tReread ≠ tTrunc ∧
      Valid S₀ tReread ∧ ¬ Valid S₀ tTrunc ∧ ¬ Denote S₀ tTrunc ρ₀ :=
  ⟨by decide, by decide, by decide, valid_tReread, not_valid_tTrunc, by decide⟩

/-- **Faithfulness is relative to the reader.** The default text `a - b = z` of
`↑(a - b) = z` is faithful for the system elaborator (and is its deletion-greedy
rendering), but the leaf-coercion reader reads it as `↑a - ↑b = z`, which differs in
truth at `a = 0, b = 1, z = 0`. Likewise `2 - 3 = 0` is the faithful deletion-greedy
rendering of `(2 : Nat) - 3 = 0` for the system elaborator, but the `Int`-numeral
reader reads it as the invalid `(2 : Int) - 3 = 0`. Both readers read the explicit
texts correctly. -/
theorem default_and_min_texts_faithful_for_cfg0_but_not_other_readers :
    Faithful cfg0 S₀ (ppDefault tZ) tZ ∧ ppMin cfg0 S₀ tZ = ppDefault tZ ∧
      elabWith cfgLeaves S₀ (ppDefault tZ) = some tZLeaves ∧
      Denote S₀ tZ ρ₀ ∧ ¬ Denote S₀ tZLeaves ρ₀ ∧
      Faithful cfg0 S₀ (ppDefault tNatSub) tNatSub ∧ ppMin cfg0 S₀ tNatSub = ppDefault tNatSub ∧
      elabWith cfgIntNumerals S₀ (ppDefault tNatSub) = some tIntSub ∧
      Valid S₀ tNatSub ∧ ¬ Valid S₀ tIntSub ∧
      Faithful cfgLeaves S₀ (ppExplicit tZ) tZ ∧
      Faithful cfgIntNumerals S₀ (ppExplicit tNatSub) tNatSub :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    valid_tNatSub, not_valid_tIntSub, by decide, by decide⟩

/-- The text `a - b = z` with the type argument `Int` on `-`: type-correct, but not
the type `-` has in `tZ`. -/
def sWrongSub : Stx := .eq none (.sub (some .int) (.var 0) (.var 1)) (.var 2)

/-- **A type-correct but wrong annotation silently changes the term.** Adding the
annotation `@sub Int` to the faithful default text of `↑(a - b) = z` yields a text
with the same erased (default) form that elaborates without error to the
well-typed `↑a - ↑b = z`, which differs in truth at `a = 0, b = 1, z = 0`. -/
theorem wrong_type_annotation_changes_term_tZ :
    sWrongSub.erase = ppDefault tZ ∧ Faithful cfg0 S₀ (ppDefault tZ) tZ ∧
      elabSys S₀ sWrongSub = some tZLeaves ∧ WellTyped S₀ tZLeaves ∧ tZLeaves ≠ tZ ∧
      Denote S₀ tZ ρ₀ ∧ ¬ Denote S₀ tZLeaves ρ₀ := by
  decide

/-- A hand rendering of `PQ` (name 2) with its definitions unfolded but its
conjuncts swapped: `z = 0 ∧ a = b`. -/
def rSwapped : Stx := .and (.eq none (.var 2) (.num 0)) (.eq none (.var 0) (.var 1))

/-- The reading of `rSwapped`. -/
def tSwapped : Tm := .and (.eq .int vZ (.lit .int 0)) (.eq .nat vA vB)

/-- **The δ-normal-form check is incomplete.** The unfolded, conjunct-swapped
rendering `z = 0 ∧ a = b` of `PQ` reads back as a term whose δ-normal form differs
from that of `PQ`, although the two evaluate identically in every environment. -/
theorem deltaNF_check_rejects_reordered_unfolded_rendering :
    elabSys S₀ rSwapped = some tSwapped ∧ deltaNF S₀ tSwapped ≠ deltaNF S₀ (.const 2) ∧
      ∀ ρ, eval S₀ ρ tSwapped = eval S₀ ρ (.const 2) := by
  refine ⟨by decide, by decide, ?_⟩
  intro ρ
  simp [eval, evalD, evalWith, S₀, tSwapped, vA, vB, vZ, Val.toNat, Val.toInt, Val.toBool]
  exact Bool.and_comm _ _

/-- **Default text is incoherent.** The default text `a - b = z` has two declarative
elaborations, chosen by the operator-coercion (system) and leaf-coercion readers
respectively, that differ in truth at `a = 0, b = 1, z = 0`. -/
theorem default_text_incoherent_operator_vs_leaf_coercion :
    Elabs S₀ (ppDefault tZ) .prop tZ ∧ Elabs S₀ (ppDefault tZ) .prop tZLeaves ∧
      elabSys S₀ (ppDefault tZ) = some tZ ∧
      elabWith cfgLeaves S₀ (ppDefault tZ) = some tZLeaves ∧
      Denote S₀ tZ ρ₀ ∧ ¬ Denote S₀ tZLeaves ρ₀ :=
  ⟨elabs_ppDefault_tZ_tZ, elabs_ppDefault_tZ_tZLeaves, by decide, by decide, by decide,
    by decide⟩

/-- `a = b` at `Nat`. -/
def tEqAB : Tm := .eq .nat vA vB

/-- **Partial annotation can suffice for a fixed set of readers.** The default text
`a = b` is not fully annotated, yet the system, `Int`-numeral and leaf-coercion
readers all read it faithfully. -/
theorem ppDefault_tEqAB_faithful_for_named_readers :
    (ppDefault tEqAB).fullyAnnotated = false ∧ Faithful cfg0 S₀ (ppDefault tEqAB) tEqAB ∧
      Faithful cfgIntNumerals S₀ (ppDefault tEqAB) tEqAB ∧
      Faithful cfgLeaves S₀ (ppDefault tEqAB) tEqAB := by
  decide

/-! ## Tightness counterexamples (canonical form) -/

/-- `elabWith_ppExplicit_of_wellTyped` without `WellTyped`: the ill-typed `tIll`
(`a` annotated as `Int`) is not recovered from its explicit text. -/
theorem ce_elabWith_ppExplicit_drop_wellTyped :
    ¬ WellTyped S₀ tIll ∧ elabWith cfg0 S₀ (ppExplicit tIll) ≠ some tIll := by
  decide

/-- `elabSys_ppDefault_of_defaultRecoverable` without its hypothesis: `tTrunc`. -/
theorem ce_elabSys_ppDefault_drop_defaultRecoverable :
    ¬ DefaultRecoverable S₀ tTrunc ∧ elabSys S₀ (ppDefault tTrunc) ≠ some tTrunc := by
  decide

/-- `defaultRecoverable_of_elabSys_ppDefault` without its hypothesis: `tTrunc`. -/
theorem ce_defaultRecoverable_drop_faithful :
    elabSys S₀ (ppDefault tTrunc) ≠ some tTrunc ∧ ¬ DefaultRecoverable S₀ tTrunc := by
  decide

/-- `textual_round_trip_of_faithful` without faithfulness (`p = ppDefault`, `cfg0`):
the default text `a ↔ a` of the ill-typed `tIffNat` does not elaborate, so the
textual round trip fails. -/
theorem ce_textual_round_trip_drop_faithful :
    elabSys S₀ (ppDefault tIffNat) ≠ some tIffNat ∧
      (elabSys S₀ (ppDefault tIffNat)).map ppDefault ≠ some (ppDefault tIffNat) := by
  decide

/-- `ppDefault_elabWith_of_annotationFree` without annotation-freeness: `(2 : Int)`. -/
theorem ce_ppDefault_elabWith_drop_annotationFree :
    (Stx.asc (.num 2) .int).annCount ≠ 0 ∧
      elabSys S₀ (.asc (.num 2) .int) = some (.lit .int 2) ∧
      ppDefault (.lit .int 2) ≠ .asc (.num 2) .int := by
  decide

/-- `ppDefault_elabWith_of_annotationFree` without the elaboration hypothesis. -/
theorem ce_ppDefault_elabWith_drop_elab :
    (ppDefault tIffNat).annCount = 0 ∧ elabSys S₀ (ppDefault tIffNat) ≠ some (.lit .nat 0) ∧
      ppDefault (.lit .nat 0) ≠ ppDefault tIffNat := by
  decide

/-- `faithful_reading_unique_and_same_denotation` without faithfulness: the default
text of `tTrunc` is read as `tReread ≠ tTrunc`. -/
theorem ce_faithful_reading_drop_faithful :
    ¬ Faithful cfg0 S₀ (ppDefault tTrunc) tTrunc ∧
      elabWith cfg0 S₀ (ppDefault tTrunc) = some tReread ∧ tReread ≠ tTrunc := by
  decide

/-- `ppMin_faithful_of_wellTyped` without `WellTyped`: `tIll`. -/
theorem ce_ppMin_faithful_drop_wellTyped :
    ¬ WellTyped S₀ tIll ∧ ¬ Faithful cfg0 S₀ (ppMin cfg0 S₀ tIll) tIll := by
  decide

/-- `ppMin_eq_ppDefault_of_faithful_ppDefault` without its hypothesis: `tTrunc`. -/
theorem ce_ppMin_eq_ppDefault_drop_faithful :
    ¬ Faithful cfg0 S₀ (ppDefault tTrunc) tTrunc ∧ ppMin cfg0 S₀ tTrunc ≠ ppDefault tTrunc := by
  decide

/-- `agreeing_reader_reads_ppExplicit` without `WellTyped` (reader: the system
elaborator itself, which agrees). -/
theorem ce_agreeing_reader_drop_wellTyped :
    AgreeOnFull elabSys elabSys ∧ ¬ WellTyped S₀ tIll ∧
      elabSys S₀ (ppExplicit tIll) ≠ some tIll :=
  ⟨agreeOnFull_refl, by decide, by decide⟩

/-- `agreeing_reader_reads_ppExplicit` without agreement: the reader that never
answers. -/
theorem ce_agreeing_reader_drop_agree :
    WellTyped S₀ tTrunc ∧ ¬ AgreeOnFull elabSys (fun _ _ => none) ∧
      (fun (_ : Sig) (_ : Stx) => (none : Option Tm)) S₀ (ppExplicit tTrunc) ≠ some tTrunc :=
  ⟨wellTyped_tTrunc, not_agreeOnFull_none, by decide⟩

/-- `faithful_ppMask_mono` without `m ≤ m'`: all annotations versus none, on `tTrunc`. -/
theorem ce_faithful_ppMask_mono_drop_le :
    ¬ (∀ p k, (fun _ _ => true : Mask) p k = true → (fun _ _ => false : Mask) p k = true) ∧
      Faithful cfg0 S₀ (ppMask (fun _ _ => true) [] tTrunc) tTrunc ∧
      ¬ Faithful cfg0 S₀ (ppMask (fun _ _ => false) [] tTrunc) tTrunc := by
  refine ⟨fun h => absurd (h [] .typeArg rfl) (by decide), by decide, by decide⟩

/-- `faithful_ppMask_mono` without the faithfulness hypothesis: no annotations on
`tTrunc`, before and after. -/
theorem ce_faithful_ppMask_mono_drop_faithful :
    (∀ p k, (fun _ _ => false : Mask) p k = true → (fun _ _ => false : Mask) p k = true) ∧
      ¬ Faithful cfg0 S₀ (ppMask (fun _ _ => false) [] tTrunc) tTrunc :=
  ⟨fun _ _ h => h, by decide⟩

/-- `eval_eq_of_deltaNF_eq` without equal δ-normal forms. -/
theorem ce_eval_eq_drop_deltaNF :
    deltaNF S₀ tNatSub ≠ deltaNF S₀ tIntSub ∧ eval S₀ ρ₀ tNatSub ≠ eval S₀ ρ₀ tIntSub := by
  decide

/-- `elabE_sound` without its hypothesis: `(var 0, lit Nat 5)` at `Nat`. -/
theorem ce_elabE_sound_drop_elab :
    elabE cfg0 S₀ none (.var 0) ≠ some (.lit .nat 5, .nat) ∧
      ¬ Elabs S₀ (.var 0) .nat (.lit .nat 5) := by
  refine ⟨by decide, ?_⟩
  intro h
  cases h

/-- `elabs_coherent_of_subFree` without `subFree`: the default text `a - b = z`. -/
theorem ce_elabs_coherent_drop_subFree :
    (ppDefault tZ).subFree = false ∧ Elabs S₀ (ppDefault tZ) .prop tZ ∧
      Elabs S₀ (ppDefault tZ) .prop tZLeaves ∧ eval S₀ ρ₀ tZ ≠ eval S₀ ρ₀ tZLeaves :=
  ⟨by decide, elabs_ppDefault_tZ_tZ, elabs_ppDefault_tZ_tZLeaves, by decide⟩

/-- `elabs_coherent_of_fullyAnnotated` without `fullyAnnotated`: the default text
`a - b = z`. -/
theorem ce_elabs_coherent_drop_fullyAnnotated :
    (ppDefault tZ).fullyAnnotated = false ∧ Elabs S₀ (ppDefault tZ) .prop tZ ∧
      Elabs S₀ (ppDefault tZ) .prop tZLeaves ∧ eval S₀ ρ₀ tZ ≠ eval S₀ ρ₀ tZLeaves :=
  ⟨by decide, elabs_ppDefault_tZ_tZ, elabs_ppDefault_tZ_tZLeaves, by decide⟩

/-- `elabs_coherent_of_subFree` without the hypothesis that `t₁` elaborates `s` (only
`t₂` does): `s` is the default text `a + b = z`, `t₂ = ↑(a + b) = z`,
`t₁ = (2 : Nat) - 3 = 0`. -/
theorem ce_elabs_coherent_of_subFree_drop_elabs :
    (ppDefault tAddOp).subFree = true ∧ Elabs S₀ (ppDefault tAddOp) .prop tAddOp ∧
      eval S₀ ρ₀ tNatSub ≠ eval S₀ ρ₀ tAddOp :=
  ⟨by decide,
    .eq (τ := .int) rfl (.inl rfl) (.coeIns (.add rfl (.inl rfl) (.var rfl) (.var rfl))) (.var rfl),
    by decide⟩

/-- `elabs_coherent_of_fullyAnnotated` without the hypothesis that `t₁` elaborates `s`
(only `t₂` does): `s = @eq Int (2 : Int) z`, `t₂ = (2 : Int) = z`,
`t₁ = (2 : Nat) - 3 = 0`. -/
theorem ce_elabs_coherent_of_fullyAnnotated_drop_elabs :
    sTwoEqZ.fullyAnnotated = true ∧ Elabs S₀ sTwoEqZ .prop (.eq .int (.lit .int 2) vZ) ∧
      eval S₀ ρ₀ tNatSub ≠ eval S₀ ρ₀ (.eq .int (.lit .int 2) vZ) :=
  ⟨by decide, .eq (τ := .int) rfl (.inr rfl) (.asc (.num rfl)) (.var rfl), by decide⟩

/-! ## The deletion-greedy printer is not a minimum-size printer -/

/-- `↑(0 : Nat) = (0 : Int)` at `Int`. -/
def tCoeZeroEqZero : Tm := .eq .int (.coe (.lit .nat 0)) (.lit .int 0)

/-- **`ppMin` is not globally minimal under the system elaborator.** On the
well-typed `↑(0 : Nat) = (0 : Int)`, `ppMin cfg0` keeps 2 annotations, while the
1-annotation rendering `↑0 = 0` (coercion shown, nothing else) is faithful. -/
theorem ppMin_not_globally_minimal_cfg0 :
    WellTyped S₀ tCoeZeroEqZero ∧ (ppMin cfg0 S₀ tCoeZeroEqZero).annCount = 2 ∧
      Faithful cfg0 S₀ (ppMask (maskOf [([0], .coercion)]) [] tCoeZeroEqZero) tCoeZeroEqZero ∧
      (ppMask (maskOf [([0], .coercion)]) [] tCoeZeroEqZero).annCount = 1 := by
  decide

/-- **`ppMin` is not globally minimal under the leaf-coercion reader.** On `tTrunc`,
`ppMin cfgLeaves` keeps 2 annotations, while `↑(a - b) = a - b` (one coercion shown)
is faithful for that reader. -/
theorem ppMin_not_globally_minimal_on_tTrunc_cfgLeaves :
    WellTyped S₀ tTrunc ∧ (ppMin cfgLeaves S₀ tTrunc).annCount = 2 ∧
      Faithful cfgLeaves S₀ (ppMask (maskOf [([0], .coercion)]) [] tTrunc) tTrunc ∧
      (ppMask (maskOf [([0], .coercion)]) [] tTrunc).annCount = 1 := by
  decide

/-- `↑a = ↑b` at `Int`. -/
def tCoeEqCoe : Tm := .eq .int (.coe vA) (.coe vB)

/-- **A kept position is not globally necessary.** On `↑a = ↑b`, `minMask cfg0` keeps
only the coercion on `b`, yet two other single-position selections (the coercion on
`a`; the type argument of `=`) are also faithful. -/
theorem ppMin_kept_position_not_globally_necessary :
    WellTyped S₀ tCoeEqCoe ∧ minMask cfg0 S₀ tCoeEqCoe = [([1], .coercion)] ∧
      Faithful cfg0 S₀ (ppMask (maskOf [([0], .coercion)]) [] tCoeEqCoe) tCoeEqCoe ∧
      Faithful cfg0 S₀ (ppMask (maskOf [([], .typeArg)]) [] tCoeEqCoe) tCoeEqCoe := by
  decide

/-- The deletion-greedy selection visiting positions in reverse pre-order. -/
def minMaskRev (cfg : ElabCfg) (S : Sig) (t : Tm) : List (Path × AnnKind) :=
  (annPos [] t).reverse.foldl
    (fun M q => if faithfulB cfg S (ppMask (maskOf (M.erase q)) [] t) t then M.erase q else M)
    (annPos [] t)

/-- **The kept set depends on the visiting order.** On `tTrunc` under `cfg0`, the
pre-order greedy selection keeps the coercion on `b`; the reverse-order one keeps the
type argument of the right-hand `-`, and is also faithful. -/
theorem visiting_order_changes_kept_set_on_tTrunc :
    minMask cfg0 S₀ tTrunc = [([1, 1], .coercion)] ∧
      minMaskRev cfg0 S₀ tTrunc = [([1], .typeArg)] ∧
      Faithful cfg0 S₀ (ppMask (maskOf (minMaskRev cfg0 S₀ tTrunc)) [] tTrunc) tTrunc := by
  decide

/-- **The converse of `ppMin_eq_ppDefault_of_faithful_ppDefault` fails.** On the
ill-typed `tIll`, `ppMin` returns the default text although that text is not
faithful. -/
theorem ppMin_eq_ppDefault_converse_false_on_tIll :
    ppMin cfg0 S₀ tIll = ppDefault tIll ∧ ¬ Faithful cfg0 S₀ (ppDefault tIll) tIll := by
  decide

/-! ## Reader-relativity: what full annotation is and is not needed for -/

/-- **Partial annotation can be faithful for every configuration.** The rendering of
`(2 : Int) - 3 = 0` showing only its two type arguments is not fully annotated, yet
every configuration of the family (including those with numeral default `Prop`)
reads it faithfully. -/
theorem partial_annotation_faithful_for_every_configuration :
    (ppWith (fun k => decide (k = .typeArg)) tIntSub).fullyAnnotated = false ∧
      (ppWith (fun k => decide (k = .typeArg)) tIntSub).annCount = 2 ∧
      ∀ cfg : ElabCfg, Faithful cfg S₀ (ppWith (fun k => decide (k = .typeArg)) tIntSub) tIntSub := by
  refine ⟨by decide, by decide, ?_⟩
  intro ⟨nd, rl⟩
  cases nd <;> cases rl <;> decide

/-- **A definitional remark (not a result).** For any predicate `P` on texts and any
reader `f`: a text is read as `t` by every reader that agrees with `f` wherever `P`
holds iff `P` holds of the text and `f` reads it as `t`. Nothing about syntax or
elaboration is used. -/
theorem read_by_all_readers_agreeing_on_pred_iff (P : Sig → Stx → Bool) (f : Reader)
    (S : Sig) (r : Stx) (t : Tm) :
    (∀ e' : Reader, (∀ S' s', P S' s' = true → e' S' s' = f S' s') → e' S r = some t) ↔
      (P S r = true ∧ f S r = some t) := by
  constructor
  · intro H
    have hf : f S r = some t := H f (fun _ _ _ => rfl)
    by_cases hp : P S r = true
    · exact ⟨hp, hf⟩
    · let adv : Reader := fun S' s' => if P S' s' = true then f S' s' else none
      have := H adv (fun S' s' hs => by simp [adv, hs])
      simp [adv, hp] at this
  · rintro ⟨hp, hf⟩ e' hag
    rw [hag S r hp, hf]

/-- The instance of `read_by_all_readers_agreeing_on_pred_iff` with
`P = fullyAnnotated` and `f = elabSys` (a definitional remark, not a result). -/
theorem read_by_all_agreeing_readers_iff (S : Sig) (r : Stx) (t : Tm) :
    (∀ e' : Reader, AgreeOnFull elabSys e' → e' S r = some t) ↔
      (r.fullyAnnotated = true ∧ elabSys S r = some t) :=
  read_by_all_readers_agreeing_on_pred_iff (fun _ s => s.fullyAnnotated) elabSys S r t

/-- **Coherent text can still fail the term round trip across readers.** The
subtraction-free default text `a + b = z` is faithful to `↑(a + b) = z` for the system
elaborator, but the leaf-coercion reader reads it as `↑a + ↑b = z`. -/
theorem subFree_term_round_trip_fails_across_readers :
    (ppDefault tAddOp).subFree = true ∧ Faithful cfg0 S₀ (ppDefault tAddOp) tAddOp ∧
      elabWith cfgLeaves S₀ (ppDefault tAddOp) = some tAddLeaves ∧
      ¬ Faithful cfgLeaves S₀ (ppDefault tAddOp) tAddOp := by
  decide

/-- **The declarative judgment is wider than the configuration family.** The fully
annotated `@eq Int (2 : Int) z` admits the elaboration `↑(2 : Nat) = z`, which no
configuration chooses. -/
theorem elabs_not_complete_for_elabWith :
    Elabs S₀ sTwoEqZ .prop (.eq .int (.coe (.lit .nat 2)) vZ) ∧
      ∀ cfg : ElabCfg, elabWith cfg S₀ sTwoEqZ ≠ some (.eq .int (.coe (.lit .nat 2)) vZ) := by
  refine ⟨.eq (τ := .int) rfl (.inr rfl) (.asc (.coeIns (.num rfl))) (.var rfl), ?_⟩
  intro ⟨nd, rl⟩
  cases nd <;> cases rl <;> decide

/-! ## Textual round trips of annotation-showing printers -/

/-- The ill-typed `a = z` at `Int` with `a : Nat` annotated as `Int`. -/
def tIllEq : Tm := .eq .int (.var 0 .int) vZ

/-- **The textual round trip of an annotation-showing printer can fail.** The
coercion-showing text of `tIllEq` is `a = z`; the system elaborator reads it as
`↑a = z`, whose coercion-showing text `↑a = z` differs. -/
theorem ppCoercions_textual_round_trip_fails :
    elabSys S₀ (ppCoercions tIllEq) = some (.eq .int (.coe vA) vZ) ∧
      (elabSys S₀ (ppCoercions tIllEq)).map ppCoercions ≠ some (ppCoercions tIllEq) := by
  decide

/-! ## δ-unfolding boundaries -/

/-- A signature whose single definition is ill typed: `c₀ : Prop := (x₉₉ : Int)`
with `x₉₉` not in the context. -/
def S_illDef : Sig := { ctx := [], defs := [⟨0, .prop, .var 99 .int⟩] }

/-- **δ-unfolding need not preserve typing when definitions are ill typed.** -/
theorem deltaNF_not_wellTyped_of_illTyped_defs :
    WellTyped S_illDef (.const 0) ∧ ¬ WellTyped S_illDef (deltaNF S_illDef (.const 0)) ∧
      elabSys S_illDef (ppExplicit (deltaNF S_illDef (.const 0))) = none := by
  decide

/-- `0 = 0` at `Nat`. -/
def tZeroEqZero : Tm := .eq .nat (.lit .nat 0) (.lit .nat 0)

/-- **Equal evaluation is coarse.** The distinct terms `0 = 0`, `a - b = a - b` and
`(2 : Nat) - 3 = 0` evaluate identically in every environment (all are valid). -/
theorem eval_equivalence_identifies_distinct_valid_terms :
    tZeroEqZero ≠ tReread ∧ tZeroEqZero ≠ tNatSub ∧
      (∀ ρ, eval S₀ ρ tZeroEqZero = eval S₀ ρ tReread) ∧
      (∀ ρ, eval S₀ ρ tZeroEqZero = eval S₀ ρ tNatSub) := by
  refine ⟨by decide, by decide, ?_, fun _ => rfl⟩
  intro ρ
  simp [eval, S₀, evalD, evalWith, tZeroEqZero, tReread, vA, vB, Val.toNat]

/-! ## Additional tightness counterexamples (canonical form) -/

/-- An ill-typed proposition-typed numeral. -/
def tLitProp : Tm := .lit .prop 0

/-- `ppMin_locally_minimal_of_wellTyped` without `WellTyped`: on the ill-typed
`.lit .prop 0`, the position `([], numType)` is kept (`hq` holds), and the conclusion
fails because `ppMin` itself is not faithful. -/
theorem ce_ppMin_locally_minimal_drop_wellTyped :
    ¬ WellTyped S₀ tLitProp ∧ ([], AnnKind.numType) ∈ minMask cfg0 S₀ tLitProp ∧
      ¬ (Faithful cfg0 S₀ (ppMin cfg0 S₀ tLitProp) tLitProp ∧
        ¬ Faithful cfg0 S₀
          (ppMask (maskOf ((minMask cfg0 S₀ tLitProp).erase ([], .numType))) [] tLitProp)
          tLitProp) := by
  decide

/-- `ppMin_locally_minimal_of_wellTyped` without `q ∈ minMask cfg S t`: on the
well-typed `tTrunc`, the position `([], typeArg)` was dropped by `minMask`, so erasing
it changes nothing and the rendering stays faithful. -/
theorem ce_ppMin_locally_minimal_drop_mem :
    WellTyped S₀ tTrunc ∧
      ¬ (Faithful cfg0 S₀ (ppMin cfg0 S₀ tTrunc) tTrunc ∧
        ¬ Faithful cfg0 S₀
          (ppMask (maskOf ((minMask cfg0 S₀ tTrunc).erase ([], .typeArg))) [] tTrunc) tTrunc) := by
  decide

/-- `elabWith_eq_elabSys_of_fullyAnnotated` without full annotation: the
leaf-coercion reader and the system elaborator read the default text `a - b = z`
differently. -/
theorem ce_elabWith_eq_elabSys_drop_fullyAnnotated :
    (ppDefault tZ).fullyAnnotated = false ∧
      elabWith cfgLeaves S₀ (ppDefault tZ) ≠ elabSys S₀ (ppDefault tZ) := by
  decide

/-- `elabs_coherent_of_subAnnotated` without `subAnnotated`: the default text
`a - b = z`. -/
theorem ce_elabs_coherent_drop_subAnnotated :
    (ppDefault tZ).subAnnotated = false ∧ Elabs S₀ (ppDefault tZ) .prop tZ ∧
      Elabs S₀ (ppDefault tZ) .prop tZLeaves ∧ eval S₀ ρ₀ tZ ≠ eval S₀ ρ₀ tZLeaves :=
  ⟨by decide, elabs_ppDefault_tZ_tZ, elabs_ppDefault_tZ_tZLeaves, by decide⟩

/-- `elabs_coherent_of_subAnnotated` without the hypothesis that `t₁` elaborates `s`
(only `t₂` does): `s` is the default text `a + b = z`, `t₂ = ↑(a + b) = z`,
`t₁ = (2 : Nat) - 3 = 0`. -/
theorem ce_elabs_coherent_of_subAnnotated_drop_elabs :
    (ppDefault tAddOp).subAnnotated = true ∧ Elabs S₀ (ppDefault tAddOp) .prop tAddOp ∧
      eval S₀ ρ₀ tNatSub ≠ eval S₀ ρ₀ tAddOp :=
  ⟨by decide,
    .eq (τ := .int) rfl (.inl rfl) (.coeIns (.add rfl (.inl rfl) (.var rfl) (.var rfl))) (.var rfl),
    by decide⟩

/-- **Within elaborating default texts the textual round trip always passes.** For
every configuration, signature and term: if the default text of `t` elaborates (to
any term), then default-printing the re-read term gives back the default text of
`t`. (So in `textual_round_trip_of_faithful` with `p = ppDefault`, the faithfulness
hypothesis is tight only through texts that do not elaborate.) -/
theorem textual_round_trip_holds_on_elaborating_ppDefault (cfg : ElabCfg) (S : Sig)
    (t t' : Tm) (helab : elabWith cfg S (ppDefault t) = some t') :
    (elabWith cfg S (ppDefault t)).map ppDefault = some (ppDefault t) := by
  rw [helab]
  simp only [Option.map_some]
  exact congrArg some (ppDefault_elabWith_of_annotationFree cfg S (ppDefault t) t'
    (ppDefault_annCount_zero [] t) helab)

end Toy.Render
