import Implicature.Examples

/-!
# Results

Every result is proved. Countermodels, tightness counterexamples, non-vacuity witnesses and
positive controls are proved by kernel evaluation (`decide +kernel`); the general theorems are
assembled from the lemmas in `Lemmas.lean`.

Reader convention: unless a statement quantifies over the alternative function `alt`, "the
reader" is the one-step reader `readings` with the standard alternatives `stdAlt S`.
-/

namespace Toy.Implicature

/-! ## Literal safety does not imply strengthening safety -/

/-- Perfection: the report proves `∀x, A → B` and refutes the converse; the rendering
`∀x, A → B` is literally safe, but its perfected reading `∀x, A ↔ B` is drawn and is
contradicted by the (consistent) report. -/
theorem perfection_reading_contradicted_though_literally_safe :
    Sat S22 E_notConv ∧ LiterallySafe S22 E_notConv (.all (.imp xA xB)) ∧
    (Claim.all (.iff xA xB)) ∈ readings S22 (stdAlt S22) [] (.all (.imp xA xB)) ∧
    Contradicts S22 E_notConv (.all (.iff xA xB)) ∧
    ¬ StrengtheningSafe S22 (stdAlt S22) [] E_notConv (.all (.imp xA xB)) := by
  decide +kernel

/-- In the perfection countermodel the exhaustified reading of the same rendering is entailed by
the report. -/
theorem perfection_countermodel_exhaustified_reading_entailed :
    Entails S22 E_notConv
      (exh S22 (stdAlt S22 (.all (.imp xA xB))) (.all (.imp xA xB))) := by
  decide +kernel

/-- Exhaustification: the report proves `∀x, A`; the rendering `∃x, A` is literally safe, but its
exhaustified reading (equivalent to `∃x, A ∧ ¬∀x, A`) is drawn and is contradicted. -/
theorem exhaustification_reading_contradicted_though_literally_safe :
    Sat S12 [.all xA] ∧ LiterallySafe S12 [.all xA] (.ex xA) ∧
    exh S12 (stdAlt S12 (.ex xA)) (.ex xA) ∈ readings S12 (stdAlt S12) [] (.ex xA) ∧
    Equiv S12 (exh S12 (stdAlt S12 (.ex xA)) (.ex xA)) (.and (.ex xA) (.not (.all xA))) ∧
    Contradicts S12 [.all xA] (exh S12 (stdAlt S12 (.ex xA)) (.ex xA)) ∧
    ¬ StrengtheningSafe S12 (stdAlt S12) [] [.all xA] (.ex xA) := by
  decide +kernel

/-- The report of the qualifier-dropping countermodel: `∀x, H ⇒ A`, and `∀x, A` fails. -/
def E_qual : List Claim := [.all (.rel xH xA), .not (.all xA)]

/-- Qualifier dropping: the report proves `∀x, H ⇒ A` and refutes `∀x, A`; the rendering
`∀x, H ⇒ A` is literally safe, but the hasty reading `∀x, A` is drawn and is contradicted. -/
theorem qualifier_drop_reading_contradicted_though_literally_safe :
    Sat S32 E_qual ∧ LiterallySafe S32 E_qual (.all (.rel xH xA)) ∧
    (Claim.all xA) ∈ readings S32 (stdAlt S32) [] (.all (.rel xH xA)) ∧
    Contradicts S32 E_qual (.all xA) ∧
    ¬ StrengtheningSafe S32 (stdAlt S32) [] E_qual (.all (.rel xH xA)) := by
  decide +kernel

/-! ## Weakening preserves literal safety but can break strengthening safety -/

/-- Literal safety is closed under literal weakening. -/
theorem literal_safety_closed_under_literal_weakening (S : Space) (E : List Claim)
    (σ σ' : Claim) (hsafe : LiterallySafe S E σ) (hweak : Entails S [σ] σ') :
    LiterallySafe S E σ' :=
  fun w hw hE => hweak w hw (by simp [hsafe w hw hE])

/-- Tightness of `hsafe` (the other hypothesis `hweak` holds; the conclusion fails): `S21`, empty
report, `σ = σ' = p0`. -/
theorem literal_weakening_tight_hsafe : Entails S21 [p0] p0 ∧ ¬ LiterallySafe S21 [] p0 := by
  decide +kernel

/-- Tightness of `hweak` (the other hypothesis `hsafe` holds; the conclusion fails): `S21`,
report `[p0]`, `σ = p0`, `σ' = q0`. -/
theorem literal_weakening_tight_hweak :
    LiterallySafe S21 [p0] p0 ∧ ¬ LiterallySafe S21 [p0] q0 := by
  decide +kernel

/-- Non-vacuity: `E = [p0 ∧ q0]`, `σ = p0 ∧ q0`, `σ' = p0`. -/
theorem literal_weakening_nonvacuous :
    LiterallySafe S21 [.and p0 q0] (.and p0 q0) ∧ Entails S21 [.and p0 q0] p0 := by
  decide +kernel

/-- The rendering "for all x, A gives B, and not conversely". -/
def σ_notConv : Claim := .and (.all (.imp xA xB)) (.not (.all (.imp xB xA)))

/-- Dropping the "not conversely" conjunct is a literal weakening that turns a
strengthening-safe rendering into a strengthening-unsafe one (no blocker flags anywhere). The
perfected reading of the full rendering is generated at its first conjunct and cancelled because
it is inconsistent with the rendering. -/
theorem blocker_conjunct_drop_breaks_strengthening_safety :
    Entails S22 [σ_notConv] (.all (.imp xA xB)) ∧ Sat S22 [σ_notConv] ∧
    (Claim.and (.all (.iff xA xB)) (.not (.all (.imp xB xA)))) ∈
      step S22 (stdAlt S22) .perfection σ_notConv ∧
    (Claim.and (.all (.iff xA xB)) (.not (.all (.imp xB xA)))) ∉
      readings S22 (stdAlt S22) [] σ_notConv ∧
    StrengtheningSafe S22 (stdAlt S22) [] [σ_notConv] σ_notConv ∧
    ¬ StrengtheningSafe S22 (stdAlt S22) [] [σ_notConv] (.all (.imp xA xB)) := by
  decide +kernel

/-! ## Innocent versus naive exhaustification -/

/-- Naive exhaustification of `p ∨ q` with alternatives `p`, `q`, `p ∧ q` negates all three and
is inconsistent; innocent exclusion negates only `p ∧ q` (exclusive "or"). -/
theorem naive_exhaustification_of_disjunction_inconsistent :
    Sat S21 [pOrQ] ∧ naiveExcl S21 pOrQ disjAlts = disjAlts ∧
    ¬ Sat S21 [naiveExh S21 disjAlts pOrQ] ∧
    ieList S21 pOrQ disjAlts = [.and p0 q0] ∧ Sat S21 [exh S21 disjAlts pOrQ] ∧
    Equiv S21 (exh S21 disjAlts pOrQ) (.and pOrQ (.not (.and p0 q0))) := by
  decide +kernel

/-- Without the conjunctive alternative (alternatives `p`, `q` only), naive exhaustification of
`p ∨ q` is still inconsistent, while innocent exclusion excludes nothing and returns the
inclusive disjunction. -/
theorem disjunction_without_conjunctive_alternative :
    naiveExcl S21 pOrQ [p0, q0] = [p0, q0] ∧ ¬ Sat S21 [naiveExh S21 [p0, q0] pOrQ] ∧
    ieList S21 pOrQ [p0, q0] = [] ∧ Equiv S21 (exh S21 [p0, q0] pOrQ) pOrQ := by
  decide +kernel

/-- Innocent exclusion is consistent: for every finite alternative list `A`, if `σ` is
satisfiable then so is `exh S A σ`. -/
theorem innocent_exhaustification_consistent_of_sat (S : Space) (A : List Claim) (σ : Claim)
    (hσ : Sat S [σ]) : Sat S [exh S A σ] :=
  exh_sat_of_sat hσ

/-- Tightness of `hσ` (no other hypotheses; the conclusion fails): `S21`, the contradictory
prejacent `p0 ∧ ¬p0`, empty alternative list. -/
theorem innocent_exh_consistent_tight : ¬ Sat S21 [exh S21 [] (.and p0 (.not p0))] := by
  decide +kernel

/-- Non-vacuity: `p0 ∨ q0` is satisfiable (and so is its exhaustification). -/
theorem innocent_exh_consistent_nonvacuous :
    Sat S21 [pOrQ] ∧ Sat S21 [exh S21 disjAlts pOrQ] := by
  decide +kernel

/-- The computed innocent-exclusion list agrees with the textbook definition (membership in
every maximal set of alternatives whose negations are jointly consistent with `σ`). -/
theorem mem_ieList_iff_innocentlyExcludable (S : Space) (σ : Claim) (A : List Claim)
    (a : Claim) : a ∈ ieList S σ A ↔ InnocentlyExcludable S σ A a :=
  mem_ieList_iff_innocentlyExcludable_aux S σ A a

/-- Non-vacuity: an instance where both sides hold ("all" for "some"). -/
theorem ieList_characterization_instance :
    (Claim.all xA) ∈ ieList S12 (.ex xA) [.all xA] ∧
      InnocentlyExcludable S12 (.ex xA) [.all xA] (.all xA) :=
  ⟨by decide +kernel, innocentlyExcludable_pos⟩

/-- `exh` is weaker than restricting to the worlds with maximal falsified sets: for `p ∨ q` with
alternatives `p`, `q`, every such world falsifies `p ∧ q`, yet `exh` holds at a world where
`p ∧ q` holds. -/
theorem exh_weaker_than_maximal_falsified_worlds :
    (∀ w ∈ S21.worlds, maxFals S21 pOrQ [p0, q0] w = true → S21.holds w (.and p0 q0) = false) ∧
    (∃ w ∈ S21.worlds, S21.holds w (exh S21 [p0, q0] pOrQ) = true ∧
      S21.holds w (.and p0 q0) = true) := by
  decide +kernel

/-- For an unsatisfiable prejacent both sides of the characterization hold for every
alternative. -/
theorem ieList_characterization_unsat_prejacent (S : Space) (σ : Claim) (A : List Claim)
    (hσ : ¬ Sat S [σ]) :
    ieList S σ A = A ∧ ∀ a ∈ A, InnocentlyExcludable S σ A a :=
  ⟨ieList_eq_self_of_not_sat A hσ, fun _ ha => innocentlyExcludable_of_not_sat hσ ha⟩

/-- Naive exhaustification always entails innocent exhaustification (same alternatives). -/
theorem naive_exh_entails_innocent_exh (S : Space) (A : List Claim) (σ : Claim) :
    Entails S [naiveExh S A σ] (exh S A σ) :=
  naiveExh_entails_exh S A σ

/-- Non-vacuity: an instance with a satisfiable naive exhaustification. -/
theorem naive_exh_entails_innocent_instance :
    Sat S12 [naiveExh S12 [.all xA] (.ex xA)] ∧
      Entails S12 [naiveExh S12 [.all xA] (.ex xA)] (exh S12 [.all xA] (.ex xA)) := by
  decide +kernel

/-- The converse entailment fails (disjunction). -/
theorem innocent_exh_not_entails_naive_exh :
    ¬ Entails S21 [exh S21 disjAlts pOrQ] (naiveExh S21 disjAlts pOrQ) := by
  decide +kernel

/-- For a satisfiable prejacent, innocent and naive exhaustification are equivalent exactly
when naive exhaustification is consistent. -/
theorem innocent_equiv_naive_iff_naive_sat (S : Space) (A : List Claim) (σ : Claim)
    (hσ : Sat S [σ]) :
    Equiv S (exh S A σ) (naiveExh S A σ) ↔ Sat S [naiveExh S A σ] :=
  exh_equiv_naiveExh_iff_sat S A σ hσ

/-- Tightness of `hσ` (no other hypotheses; the conclusion fails): `S21`, contradictory prejacent
`p0 ∧ ¬p0`, alternatives `[p0]`; the two readings are equivalent (both unsatisfiable) but the
naive one is not satisfiable. -/
theorem innocent_equiv_naive_tight :
    ¬ (Equiv S21 (exh S21 [p0] (.and p0 (.not p0))) (naiveExh S21 [p0] (.and p0 (.not p0))) ↔
      Sat S21 [naiveExh S21 [p0] (.and p0 (.not p0))]) := by
  decide +kernel

/-- Non-vacuity: satisfiable prejacents with both truth values of the two sides. -/
theorem innocent_equiv_naive_nonvacuous :
    Sat S12 [.ex xA] ∧ Equiv S12 (exh S12 [.all xA] (.ex xA)) (naiveExh S12 [.all xA] (.ex xA)) ∧
    Sat S21 [pOrQ] ∧ ¬ Equiv S21 (exh S21 disjAlts pOrQ) (naiveExh S21 disjAlts pOrQ) := by
  decide +kernel

/-- Exhaustification (standard alternatives) is neither monotone nor antitone in entailment:
`∀x, A ⊨ ∃x, A`, yet neither exhaustified reading entails the other (they are
contradictory). -/
theorem exh_neither_monotone_nor_antitone :
    Entails S12 [.all xA] (.ex xA) ∧
    ¬ Entails S12 [exh S12 (stdAlt S12 (.all xA)) (.all xA)]
        (exh S12 (stdAlt S12 (.ex xA)) (.ex xA)) ∧
    ¬ Entails S12 [exh S12 (stdAlt S12 (.ex xA)) (.ex xA)]
        (exh S12 (stdAlt S12 (.all xA)) (.all xA)) := by
  decide +kernel

/-- Entailment between exhaustified readings does not reflect entailment between the
prejacents: `exh (∃x, A) ⊨ exh (¬∀x, A)` but `∃x, A ⊭ ¬∀x, A`. -/
theorem exh_entailment_does_not_reflect :
    Entails S12 [exh S12 (stdAlt S12 (.ex xA)) (.ex xA)]
      (exh S12 (stdAlt S12 (.not (.all xA))) (.not (.all xA))) ∧
    ¬ Entails S12 [.ex xA] (.not (.all xA)) := by
  decide +kernel

/-! ## Computed blockers restore safety and are the least safe flag set -/

/-- Soundness: flagging the computed blocker set makes every literally safe rendering
strengthening-safe (one-step reader, any alternative function). -/
theorem blockers_sound (S : Space) (alt : Claim → List Claim) (E : List Claim) (σ : Claim)
    (hlit : LiterallySafe S E σ) : StrengtheningSafe S alt (blockers S alt E σ) E σ :=
  blockers_sound_aux S alt E σ hlit

/-- Tightness of `hlit` (no other hypotheses; the conclusion fails): `S21`, empty report,
`σ = p0`. -/
theorem blockers_sound_tight :
    ¬ StrengtheningSafe S21 (stdAlt S21) (blockers S21 (stdAlt S21) [] p0) [] p0 := by
  decide +kernel

/-- Non-vacuity: the running example. -/
theorem blockers_sound_nonvacuous :
    LiterallySafe S22 E_notConv (.all (.imp xA xB)) ∧
    blockers S22 (stdAlt S22) E_notConv (.all (.imp xA xB)) = [.perfection] ∧
    StrengtheningSafe S22 (stdAlt S22) [.perfection] E_notConv (.all (.imp xA xB)) := by
  decide +kernel

/-- Minimality: every flag set that makes the rendering strengthening-safe contains the
computed blocker set (one-step reader, any alternative function). -/
theorem blockers_subset_of_strengtheningSafe (S : Space) (alt : Claim → List Claim)
    (E : List Claim) (σ : Claim) (F : List Rule) (hsafe : StrengtheningSafe S alt F E σ) :
    ∀ r ∈ blockers S alt E σ, r ∈ F :=
  blockers_subset_aux S alt E σ F hsafe

/-- Least safe flag set: for a literally safe rendering, the safe flag sets are exactly the flag
sets containing every rule of the computed blocker set (one-step reader, any alternative
function). -/
theorem strengtheningSafe_iff_blockers_subset (S : Space) (alt : Claim → List Claim)
    (E : List Claim) (σ : Claim) (F : List Rule) (hlit : LiterallySafe S E σ) :
    StrengtheningSafe S alt F E σ ↔ ∀ r ∈ blockers S alt E σ, r ∈ F :=
  strengtheningSafe_iff_aux S alt E σ F hlit

/-- Tightness of `hsafe` in `blockers_subset_of_strengtheningSafe` (no other hypotheses; the
conclusion fails): `S22`, `E_notConv`, `σ = ∀x, A → B`, `F = []`. -/
theorem blockers_minimal_tight :
    ¬ (∀ r ∈ blockers S22 (stdAlt S22) E_notConv (.all (.imp xA xB)), r ∈ ([] : List Rule)) := by
  decide +kernel

/-- Tightness of `hlit` in `strengtheningSafe_iff_blockers_subset` (no other hypotheses; the
conclusion fails): `S21`, empty report, `σ = p0`, `F` the computed blocker set. -/
theorem blockers_iff_tight_hlit :
    ¬ LiterallySafe S21 [] p0 ∧
    ¬ (StrengtheningSafe S21 (stdAlt S21) (blockers S21 (stdAlt S21) [] p0) [] p0 ↔
        ∀ r ∈ blockers S21 (stdAlt S21) [] p0, r ∈ blockers S21 (stdAlt S21) [] p0) := by
  decide +kernel

/-- The report of the composing-reader countermodel: `∀x, A → B`, `∀x, H ⇒ (B → A)`, and
`∃x, B ∧ ¬A`. -/
def E_relCond : List Claim :=
  [.all (.imp xA xB), .all (.rel xH (.imp xB xA)), .ex (.and xB (.not xA))]

/-- For the composing reader the least safe flag set need not exist: the rendering
"for all x, under H, A gives B" has exactly two minimal safe flag sets,
`{exhaustification, qualifierDrop}` and `{exhaustification, perfection}`, while the one-step
blocker set `{exhaustification}` is safe for the one-step reader only. -/
theorem composing_reader_minimal_blocker_sets_not_unique :
    LiterallySafe S32 E_relCond σ_relCond ∧
    blockers S32 (stdAlt S32) E_relCond σ_relCond = [.exhaustification] ∧
    StrengtheningSafe S32 (stdAlt S32) [.exhaustification] E_relCond σ_relCond ∧
    ¬ StrengtheningSafeStar S32 (stdAlt S32) [] E_relCond σ_relCond ∧
    ¬ StrengtheningSafeStar S32 (stdAlt S32) [.exhaustification] E_relCond σ_relCond ∧
    ¬ StrengtheningSafeStar S32 (stdAlt S32) [.qualifierDrop] E_relCond σ_relCond ∧
    ¬ StrengtheningSafeStar S32 (stdAlt S32) [.perfection] E_relCond σ_relCond ∧
    ¬ StrengtheningSafeStar S32 (stdAlt S32) [.qualifierDrop, .perfection] E_relCond σ_relCond ∧
    StrengtheningSafeStar S32 (stdAlt S32) [.exhaustification, .qualifierDrop] E_relCond σ_relCond ∧
    StrengtheningSafeStar S32 (stdAlt S32) [.exhaustification, .perfection] E_relCond σ_relCond := by
  decide +kernel

/-- For the composing reader, some flag set is safe iff the rendering is literally safe (flag
every rule; conversely the literal reading is always drawn). -/
theorem composing_reader_some_safe_flag_set_iff_literally_safe (S : Space)
    (alt : Claim → List Claim) (E : List Claim) (σ : Claim) :
    (∃ F, StrengtheningSafeStar S alt F E σ) ↔ LiterallySafe S E σ :=
  ⟨fun ⟨_, h⟩ => h σ List.mem_cons_self,
    fun h => ⟨allRules, strengtheningSafeStar_allRules_of_literallySafe h⟩⟩

/-! ## Compression by dropping whole conclusions -/

/-- Dropping whole conclusions of a normal-form claim (keeping its hypothesis and quantifier
domain) preserves literal safety. -/
theorem conclusion_dropping_preserves_literal_safety (S : Space) (E : List Claim) (H : Claim)
    (Cs Cs' : List Claim) (hE : LiterallySafe S E (nf H Cs)) (hsub : ∀ c ∈ Cs', c ∈ Cs) :
    LiterallySafe S E (nf H Cs') :=
  nf_conclusion_drop S E H Cs Cs' hE hsub

/-- Tightness of `hE` (the other hypothesis `hsub` holds; the conclusion fails): `S32`, empty
report, `H = xH`, `Cs = Cs' = [xA]`. -/
theorem conclusion_dropping_tight_hE :
    (∀ c ∈ [xA], c ∈ [xA]) ∧ ¬ LiterallySafe S32 [] (nf xH [xA]) := by
  decide +kernel

/-- Tightness of `hsub` (the other hypothesis `hE` holds; the conclusion fails): `S32`, report
`[nf xH [xA]]`, adding the conclusion `xB`. -/
theorem conclusion_dropping_tight_hsub :
    LiterallySafe S32 [nf xH [xA]] (nf xH [xA]) ∧
    ¬ LiterallySafe S32 [nf xH [xA]] (nf xH [xA, xB]) := by
  decide +kernel

/-- Non-vacuity. -/
theorem conclusion_dropping_nonvacuous :
    LiterallySafe S32 [nf xH [xA, xB]] (nf xH [xA, xB]) ∧ (∀ c ∈ [xB], c ∈ [xA, xB]) ∧
    LiterallySafe S32 [nf xH [xA, xB]] (nf xH [xB]) := by
  decide +kernel

/-- Every conclusion-dropping compression of normal-form claims that the report proves,
rendered with the blocker set recomputed for the compressed rendering, is
strengthening-safe (one-step reader, any alternative function). -/
theorem compression_with_recomputed_blockers_strengthening_safe (S : Space)
    (alt : Claim → List Claim) (E : List Claim) (R comp : List (Claim × List Claim))
    (hR : ∀ q ∈ R, LiterallySafe S E (nfOf q)) (hcomp : ConclusionDropping R comp) :
    StrengtheningSafe S alt (blockers S alt E (renderComp comp)) E (renderComp comp) :=
  blockers_sound_aux S alt E _ (renderComp_literallySafe_of_conclusionDropping S E R comp hR hcomp)

/-- The blocker set may be computed from the normal-form entries alone (taking `R` as the report)
and used for any report that proves `R`. -/
theorem compression_with_entry_blockers_strengthening_safe (S : Space)
    (alt : Claim → List Claim) (E : List Claim) (R comp : List (Claim × List Claim))
    (hR : ∀ q ∈ R, LiterallySafe S E (nfOf q)) (hcomp : ConclusionDropping R comp) :
    StrengtheningSafe S alt (blockers S alt (R.map nfOf) (renderComp comp)) E
      (renderComp comp) := by
  have hlitE := renderComp_literallySafe_of_conclusionDropping S E R comp hR hcomp
  rw [strengtheningSafe_iff_aux S alt E (renderComp comp) _ hlitE]
  intro r hr
  obtain ⟨ρ, hρ, hn⟩ := mem_blockers_iff.mp hr
  refine mem_blockers_iff.mpr ⟨ρ, hρ, fun hR' => hn fun w hw hEw => hR' w hw fun e he => ?_⟩
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he
  exact hR q hq w hw hEw

/-- Tightness of `hR` for both compression theorems (the other hypothesis `hcomp` holds; both
conclusions fail): `S32`, empty report, `R = comp = [(xH, [xA])]`. -/
theorem compression_tight_hR :
    ConclusionDropping [(xH, [xA])] [(xH, [xA])] ∧
    ¬ StrengtheningSafe S32 (stdAlt S32) (blockers S32 (stdAlt S32) [] (renderComp [(xH, [xA])])) []
        (renderComp [(xH, [xA])]) ∧
    ¬ StrengtheningSafe S32 (stdAlt S32)
        (blockers S32 (stdAlt S32) ([(xH, [xA])].map nfOf) (renderComp [(xH, [xA])])) []
        (renderComp [(xH, [xA])]) := by
  decide +kernel

/-- Tightness of `hcomp` for both compression theorems (the other hypothesis `hR` holds; both
conclusions fail): `S32`, report `[nf xH [xA]]`, dropping the hypothesis instead of a
conclusion. -/
theorem compression_tight_hcomp :
    (∀ q ∈ [(xH, [xA])], LiterallySafe S32 [nf xH [xA]] (nfOf q)) ∧
    ¬ StrengtheningSafe S32 (stdAlt S32)
        (blockers S32 (stdAlt S32) [nf xH [xA]] (renderComp [(.top, [xA])])) [nf xH [xA]]
        (renderComp [(.top, [xA])]) ∧
    ¬ StrengtheningSafe S32 (stdAlt S32)
        (blockers S32 (stdAlt S32) ([(xH, [xA])].map nfOf) (renderComp [(.top, [xA])]))
        [nf xH [xA]] (renderComp [(.top, [xA])]) := by
  decide +kernel

/-- The normal-form entries of the compression countermodel. -/
def R_comp : List (Claim × List Claim) := [(xH, [xA, xB])]

/-- The report of the compression countermodel: `∀x, H ⇒ A`, `∀x, H ⇒ B`, `∀x, A`, and `∀x, B`
fails. -/
def E_comp : List Claim := [nf xH [xA, xB], .all xA, .not (.all xB)]

/-- Non-vacuity of both compression theorems. -/
theorem compression_nonvacuous :
    (∀ q ∈ R_comp, LiterallySafe S32 E_comp (nfOf q)) ∧ ConclusionDropping R_comp [(xH, [xA])] ∧
    StrengtheningSafe S32 (stdAlt S32) (blockers S32 (stdAlt S32) E_comp (renderComp [(xH, [xA])]))
      E_comp (renderComp [(xH, [xA])]) ∧
    StrengtheningSafe S32 (stdAlt S32)
      (blockers S32 (stdAlt S32) (R_comp.map nfOf) (renderComp [(xH, [xA])]))
      E_comp (renderComp [(xH, [xA])]) := by
  decide +kernel

/-- Duplicating a conclusion is a conclusion-dropping compression, and it does not hide the
perfected reading: each copy is its own site. -/
theorem duplicated_conclusion_keeps_perfection_hazard :
    ConclusionDropping [(.top, [.imp xA xB])] [(.top, [.imp xA xB, .imp xA xB])] ∧
    blockers S22 (stdAlt S22) E_notConv (renderComp [(.top, [.imp xA xB])]) = [.perfection] ∧
    blockers S22 (stdAlt S22) E_notConv (renderComp [(.top, [.imp xA xB, .imp xA xB])]) =
      [.perfection] := by
  decide +kernel

/-- The normal-form entries of the uncancelling countermodel: unconditionally, `A → B` and
`B ∧ ¬A`. -/
def R_unc : List (Claim × List Claim) := [(.top, [.imp xA xB, .and xB (.not xA)])]

/-- The report of the uncancelling countermodel: exactly the normal-form claims of `R_unc`. -/
def E_unc : List Claim := R_unc.map nfOf

/-- Inherited blockers can be insufficient after a conclusion drop. In the full rendering of
`R_unc` the perfected reading of the first conclusion is cancelled (it is inconsistent with the
second conclusion), so the computed blocker set is empty and the unflagged full rendering is
safe; after dropping the second conclusion, the perfected reading `∀x, ⊤ ⇒ (A ↔ B)` is drawn and
is contradicted by the report, so the inherited (empty) flag set leaves the compressed rendering
unsafe; its computed blocker set is `{perfection}`. -/
theorem inherited_blockers_insufficient_after_conclusion_drop :
    Sat S22 E_unc ∧ (∀ q ∈ R_unc, LiterallySafe S22 E_unc (nfOf q)) ∧
    ConclusionDropping R_unc [(.top, [.imp xA xB])] ∧
    (Claim.and (.all (.rel .top (.iff xA xB))) (.all (.rel .top (.and xB (.not xA))))) ∈
      step S22 (stdAlt S22) .perfection (renderComp R_unc) ∧
    ¬ Sat S22 [renderComp R_unc,
      .and (.all (.rel .top (.iff xA xB))) (.all (.rel .top (.and xB (.not xA))))] ∧
    blockers S22 (stdAlt S22) E_unc (renderComp R_unc) = [] ∧
    StrengtheningSafe S22 (stdAlt S22) [] E_unc (renderComp R_unc) ∧
    (Claim.all (.rel .top (.iff xA xB))) ∈
      readings S22 (stdAlt S22) [] (renderComp [(.top, [.imp xA xB])]) ∧
    Contradicts S22 E_unc (.all (.rel .top (.iff xA xB))) ∧
    blockers S22 (stdAlt S22) E_unc (renderComp [(.top, [.imp xA xB])]) = [.perfection] ∧
    ¬ StrengtheningSafe S22 (stdAlt S22) [] E_unc (renderComp [(.top, [.imp xA xB])]) := by
  decide +kernel

/-- Inherited blockers can be superfluous after a conclusion drop. For `E_comp`, the full
rendering of `R_comp` needs `{qualifierDrop, exhaustification}`, the compressed rendering
`∀x, H ⇒ A` needs only `{exhaustification}` (its exhaustified reading, equivalent to
`(∀x, H ⇒ A) ∧ ¬∀x, A`, is contradicted by the report and does not entail "H is needed for A"),
and the inherited flags are sufficient but contain the unneeded `qualifierDrop`. -/
theorem inherited_blockers_superfluous_after_conclusion_drop :
    Sat S32 E_comp ∧ (∀ q ∈ R_comp, LiterallySafe S32 E_comp (nfOf q)) ∧
    ConclusionDropping R_comp [(xH, [xA])] ∧
    blockers S32 (stdAlt S32) E_comp (renderComp R_comp) = [.qualifierDrop, .exhaustification] ∧
    blockers S32 (stdAlt S32) E_comp (renderComp [(xH, [xA])]) = [.exhaustification] ∧
    Equiv S32 (exh S32 (stdAlt S32 (renderComp [(xH, [xA])])) (renderComp [(xH, [xA])]))
      (.and (.all (.rel xH xA)) (.not (.all xA))) ∧
    Contradicts S32 E_comp
      (exh S32 (stdAlt S32 (renderComp [(xH, [xA])])) (renderComp [(xH, [xA])])) ∧
    ¬ Entails S32 [exh S32 (stdAlt S32 (renderComp [(xH, [xA])])) (renderComp [(xH, [xA])])]
      (needed xH xA) ∧
    StrengtheningSafe S32 (stdAlt S32) [.qualifierDrop, .exhaustification] E_comp
      (renderComp [(xH, [xA])]) ∧
    StrengtheningSafe S32 (stdAlt S32) [.exhaustification] E_comp (renderComp [(xH, [xA])]) := by
  decide +kernel

/-- Replacing the hypothesis of a normal-form claim by `⊤` gives a rendering that is literally
safe iff the hypothesis-free claim `∀x, ⋀Cs` is. -/
theorem nf_top_literally_safe_iff_unconditional (S : Space) (E : List Claim) (Cs : List Claim) :
    LiterallySafe S E (nf .top Cs) ↔ LiterallySafe S E (.all (conjList Cs)) := by
  unfold LiterallySafe Entails
  apply forall_congr'
  intro w
  apply imp_congr_right
  intro _
  apply imp_congr_right
  intro _
  rw [holds_nf, holds_all_eq]
  simp only [evalAt_conjList, holds_rel_all, List.all_eq_true]
  constructor
  · intro h y hy c hc
    simpa [Space.evalAt] using h c hc y hy
  · intro h c hc y hy
    simpa [Space.evalAt] using h y hy c hc

/-- When may a summary omit a hypothesis? Given that the report proves the normal-form claim
`∀x, H ⇒ Cᵢ` for every conclusion, dropping the hypothesis (replacing it by `⊤`) is literally safe
iff the report also proves every conclusion where the hypothesis fails (`∀x, ¬H ⇒ Cᵢ`). -/
theorem hypothesis_dropping_literally_safe_iff_proved_where_hypothesis_fails (S : Space)
    (E : List Claim) (H : Claim) (Cs : List Claim) (hE : LiterallySafe S E (nf H Cs)) :
    LiterallySafe S E (nf .top Cs) ↔ LiterallySafe S E (nf (.not H) Cs) := by
  constructor
  · intro h w hw hEw
    have h1 := h w hw hEw
    rw [holds_nf, List.all_eq_true] at h1 ⊢
    intro c hc
    have h2 := h1 c hc
    rw [holds_rel_all, List.all_eq_true] at h2 ⊢
    intro y hy
    have := h2 y hy
    simp only [Space.evalAt] at this ⊢
    cases hc' : S.evalAt w y c <;> simp_all
  · intro h w hw hEw
    have h1 := h w hw hEw
    have h0 := hE w hw hEw
    rw [holds_nf, List.all_eq_true] at h1 h0 ⊢
    intro c hc
    have h2 := h1 c hc
    have h3 := h0 c hc
    rw [holds_rel_all, List.all_eq_true] at h2 h3 ⊢
    intro y hy
    have e2 := h2 y hy
    have e3 := h3 y hy
    simp only [Space.evalAt] at e2 e3 ⊢
    cases hH : S.evalAt w y H <;> cases hc' : S.evalAt w y c <;> simp_all

/-- Tightness of `hE` (no other hypotheses; the conclusion fails): `S32`, report
`[nf (¬xH) [xA]]`, which proves the conclusion where `H` fails but not where it holds. -/
theorem hypothesis_dropping_tight_hE :
    ¬ (LiterallySafe S32 [nf (.not xH) [xA]] (nf .top [xA]) ↔
        LiterallySafe S32 [nf (.not xH) [xA]] (nf (.not xH) [xA])) := by
  decide +kernel

/-- Non-vacuity, both truth values: a report proving `A` under `H` and under `¬H` licenses
dropping `H`; a report proving `A` only under `H` does not. -/
theorem hypothesis_dropping_nonvacuous :
    LiterallySafe S32 [nf xH [xA], nf (.not xH) [xA]] (nf xH [xA]) ∧
    LiterallySafe S32 [nf xH [xA], nf (.not xH) [xA]] (nf .top [xA]) ∧
    LiterallySafe S32 [nf xH [xA], nf (.not xH) [xA]] (nf (.not xH) [xA]) ∧
    LiterallySafe S32 [nf xH [xA]] (nf xH [xA]) ∧
    ¬ LiterallySafe S32 [nf xH [xA]] (nf .top [xA]) ∧
    ¬ LiterallySafe S32 [nf xH [xA]] (nf (.not xH) [xA]) := by
  decide +kernel

/-! ## Necessity words -/

/-- "`X` is needed for `Y`" (read `∀x, Y → X`) is contradicted by the report exactly when the
report proves a counterexample `∃x, Y ∧ ¬X`. -/
theorem necessity_rendering_contradicted_iff_counterexample (S : Space) (E : List Claim)
    (X Y : Claim) : Contradicts S E (needed X Y) ↔ Entails S E (.ex (.and Y (.not X))) := by
  simp [Contradicts, Entails, needed, Space.holds, Space.evalAt]

/-- Non-vacuity, both truth values: over `S22`, the report `[∃x, B ∧ ¬A]` contradicts "A is
needed for B" and proves the counterexample; the empty report does neither. -/
theorem necessity_rendering_nonvacuous :
    Contradicts S22 [.ex (.and xB (.not xA))] (needed xA xB) ∧
    Entails S22 [.ex (.and xB (.not xA))] (.ex (.and xB (.not xA))) ∧
    ¬ Contradicts S22 [] (needed xA xB) ∧ ¬ Entails S22 [] (.ex (.and xB (.not xA))) := by
  decide +kernel

/-- Natural instance in a single interpreted world over `0 … 7` (so the empty report already
decides every claim): divisibility by 4 gives evenness; "divisibility by 4 is needed for
evenness" is false; the hypothesis divisibility by 4 is tight for "under div4, even" (1 is
neither); and the exhaustified reading of that claim holds. -/
theorem natural_instance_tight_sufficient_condition_not_needed :
    Entails natSpace [] (.all (.imp div4 even)) ∧ Contradicts natSpace [] (needed div4 even) ∧
    Entails natSpace [] (tightFor div4 even) ∧
    Entails natSpace []
      (exh natSpace (stdAlt natSpace (.all (.rel div4 even))) (.all (.rel div4 even))) := by
  decide +kernel

/-- The report of the multi-world instance: `∀x, A ⇒ B`, a counterexample to the converse
`∃x, B ∧ ¬A`, and the tightness witness `∃x, ¬A ∧ ¬B`. -/
def E_tight : List Claim := [.all (.rel xA xB), .ex (.and xB (.not xA)), tightFor xA xB]

/-- Multi-world instance over `S22`: the consistent report `E_tight` proves `∀x, A ⇒ B`, proves
that `A` is tight for it, and entails its exhaustified reading, yet contradicts "A is needed for
B"; tightness is not entailed by the empty report, so the report does the work. -/
theorem tight_hypothesis_not_needed :
    Sat S22 E_tight ∧ ¬ Entails S22 [] (tightFor xA xB) ∧
    Entails S22 E_tight (.all (.rel xA xB)) ∧ Entails S22 E_tight (tightFor xA xB) ∧
    Entails S22 E_tight (exh S22 (stdAlt S22 (.all (.rel xA xB))) (.all (.rel xA xB))) ∧
    Contradicts S22 E_tight (needed xA xB) := by
  decide +kernel

/-! ## Disclaimers -/

/-- For a true disclaimer "`c` is not shown", the reader rule "not shown ↦ false" is unsafe
exactly when the report leaves `c` open. -/
theorem not_shown_read_as_false_unsafe_iff_open (S : Space) (E : List Claim) (c : Claim)
    (htrue : DisclaimerTrue S E (.notShown c)) :
    ¬ DisclaimerSafe S E (.notShown c) ↔ Open S E c := by
  simp only [DisclaimerSafe, DisclaimerTrue, disclaimerReadings, Open, List.mem_singleton,
    forall_eq] at htrue ⊢
  exact ⟨fun h => ⟨htrue, fun hc => h ⟨htrue, hc⟩⟩, fun ⟨_, hnc⟩ ⟨_, hc⟩ => hnc hc⟩

/-- The blocked disclaimer "`c` is not shown, and not refuted" is safe exactly when the report
leaves `c` open. -/
theorem not_shown_not_refuted_safe_iff_open (S : Space) (E : List Claim) (c : Claim) :
    DisclaimerSafe S E (.notShownNotRefuted c) ↔ Open S E c := by
  simp [DisclaimerSafe, DisclaimerTrue, disclaimerReadings, Open]

/-- Tightness of `htrue` (no other hypotheses; the first conclusion fails): `S21`, report `[p0]`,
which proves `p0`, making the disclaimer false. -/
theorem not_shown_tight_htrue :
    ¬ (¬ DisclaimerSafe S21 [p0] (.notShown p0) ↔ Open S21 [p0] p0) := by
  decide +kernel

/-- Non-vacuity: the empty report leaves `p0` open; the bare disclaimer is unsafe and the
blocked one is safe. -/
theorem disclaimer_nonvacuous :
    DisclaimerTrue S21 [] (.notShown p0) ∧ Open S21 [] p0 ∧
    ¬ DisclaimerSafe S21 [] (.notShown p0) ∧ DisclaimerSafe S21 [] (.notShownNotRefuted p0) := by
  decide +kernel

/-- Positive control: when the report refutes `c`, "not shown" read as "false" is safe. -/
theorem not_shown_read_as_false_safe_when_refuted :
    DisclaimerTrue S21 [.not p0] (.notShown p0) ∧ DisclaimerSafe S21 [.not p0] (.notShown p0) := by
  decide +kernel

/-! ## A universal conditional is unsafe without blockers when its perfected reading and the
failure of its converse are both consistent with it -/

/-- For the standard alternatives, if `∀x, a → b` is consistent with its perfected reading
(`PerfectionConsistent`) and with the failure of its converse (`ConverseExcludable`), then for
every consistent report the unblocked one-step reader of `∀x, a → b` draws a reading the report
does not entail. -/
theorem forall_conditional_unblocked_unsafe_of_perfection_consistent_of_converse_excludable
    (S : Space) (E : List Claim) (a b : Claim) (hE : Sat S E)
    (hperf : PerfectionConsistent S a b) (hconv : ConverseExcludable S a b) :
    ¬ StrengtheningSafe S (stdAlt S) [] E (.all (.imp a b)) :=
  forall_conditional_unblocked_unsafe_aux S E a b hE hperf hconv

/-- The computed blocker set of a literally safe `∀x, a → b` (standard alternatives, consistent
report, both non-degeneracy conditions) is determined by what the report says about the converse
`∀x, b → a`: `{perfection}` if the report refutes it, `{exhaustification}` if the report proves
it, and `{perfection, exhaustification}` if the report leaves it open. -/
theorem forall_conditional_blockers_by_converse_status (S : Space) (E : List Claim) (a b : Claim)
    (hE : Sat S E) (hlit : LiterallySafe S E (.all (.imp a b)))
    (hperf : PerfectionConsistent S a b) (hconv : ConverseExcludable S a b) :
    blockers S (stdAlt S) E (.all (.imp a b)) =
      if Entails S E (.not (.all (.imp b a))) then [.perfection]
      else if Entails S E (.all (.imp b a)) then [.exhaustification]
      else [.perfection, .exhaustification] :=
  forall_conditional_blockers_aux S E a b hE hlit hperf hconv

/-- If the report leaves the converse open, the computed blocker set of `∀x, a → b` (standard
alternatives) is `{perfection, exhaustification}` whenever perfection is consistent; no literal
safety, report consistency or converse-excludability assumption is used. -/
theorem forall_conditional_blockers_of_open_converse (S : Space) (E : List Claim) (a b : Claim)
    (hperf : PerfectionConsistent S a b) (hopen : Open S E (.all (.imp b a))) :
    blockers S (stdAlt S) E (.all (.imp a b)) = [.perfection, .exhaustification] :=
  forall_conditional_blockers_of_open_aux S E a b hperf hopen

/-- Corollary: if the report proves `∀x, a → b`, perfection is consistent, and the report leaves
the converse open, a flag set makes `∀x, a → b` strengthening-safe iff it contains both the
perfection and the exhaustification flags. -/
theorem forall_conditional_open_converse_safe_iff_both_flags (S : Space) (E : List Claim)
    (a b : Claim) (F : List Rule) (hlit : LiterallySafe S E (.all (.imp a b)))
    (hperf : PerfectionConsistent S a b) (hopen : Open S E (.all (.imp b a))) :
    StrengtheningSafe S (stdAlt S) F E (.all (.imp a b)) ↔
      Rule.perfection ∈ F ∧ Rule.exhaustification ∈ F :=
  forall_conditional_open_converse_safe_iff_aux S E a b F hlit hperf hopen

/-- Tightness of `hE` in the impossibility (the other hypotheses hold; the conclusion fails):
`S22`, `a = xA`, `b = xB`, inconsistent report `[p0, ¬p0]`. -/
theorem forall_conditional_tight_hE :
    PerfectionConsistent S22 xA xB ∧ ConverseExcludable S22 xA xB ∧
    StrengtheningSafe S22 (stdAlt S22) [] [p0, .not p0] (.all (.imp xA xB)) := by
  decide +kernel

/-- Tightness of `hperf` in the impossibility, outside full valuation spaces (the other
hypotheses hold; the conclusion fails): the two-world `disagreeSpace` where atoms 0 and 1 always
disagree, report `[∀x, A → B]`. -/
theorem forall_conditional_tight_hperf :
    Sat disagreeSpace [.all (.imp xA xB)] ∧ ConverseExcludable disagreeSpace xA xB ∧
    StrengtheningSafe disagreeSpace (stdAlt disagreeSpace) [] [.all (.imp xA xB)]
      (.all (.imp xA xB)) := by
  decide +kernel

/-- Tightness of `hperf` in the impossibility, inside a full valuation space (the other
hypotheses hold; the conclusion fails): `S12`, `a = xA`, `b = ¬xA`, report `[∀x, A → ¬A]`. -/
theorem forall_conditional_tight_hperf_full :
    Sat S12 [.all (.imp xA (.not xA))] ∧ ConverseExcludable S12 xA (.not xA) ∧
    ¬ PerfectionConsistent S12 xA (.not xA) ∧
    StrengtheningSafe S12 (stdAlt S12) [] [.all (.imp xA (.not xA))]
      (.all (.imp xA (.not xA))) := by
  decide +kernel

/-- Tightness of `hconv` in the impossibility (the other hypotheses hold; the conclusion fails):
`S12`, `a = b = xA` (the conditional entails its converse), empty report. -/
theorem forall_conditional_tight_hconv :
    Sat S12 [] ∧ PerfectionConsistent S12 xA xA ∧
    StrengtheningSafe S12 (stdAlt S12) [] [] (.all (.imp xA xA)) := by
  decide +kernel

/-- Non-vacuity of the impossibility: the running example satisfies all three hypotheses. -/
theorem forall_conditional_nonvacuous :
    Sat S22 E_notConv ∧ PerfectionConsistent S22 xA xB ∧ ConverseExcludable S22 xA xB := by
  decide +kernel

/-- Tightness of `hE` in the blocker characterization (the other hypotheses hold; the conclusion
fails): `S22`, inconsistent report `[p0, ¬p0]`; the computed blocker set is empty although the
report entails the failure of the converse. -/
theorem forall_conditional_blockers_tight_hE :
    LiterallySafe S22 [p0, .not p0] (.all (.imp xA xB)) ∧ PerfectionConsistent S22 xA xB ∧
    ConverseExcludable S22 xA xB ∧
    Entails S22 [p0, .not p0] (.not (.all (.imp xB xA))) ∧
    blockers S22 (stdAlt S22) [p0, .not p0] (.all (.imp xA xB)) = [] := by
  decide +kernel

/-- Tightness of `hlit` in the blocker characterization (the other hypotheses hold; the
conclusion fails): `S22`, report `[¬∀x, B → A]`, which refutes the converse but does not prove the
rendering. -/
theorem forall_conditional_blockers_tight_hlit :
    Sat S22 [.not (.all (.imp xB xA))] ∧ PerfectionConsistent S22 xA xB ∧
    ConverseExcludable S22 xA xB ∧
    Entails S22 [.not (.all (.imp xB xA))] (.not (.all (.imp xB xA))) ∧
    blockers S22 (stdAlt S22) [.not (.all (.imp xB xA))] (.all (.imp xA xB)) =
      [.perfection, .exhaustification] := by
  decide +kernel

/-- Tightness of `hperf` in the blocker characterization (the other hypotheses hold; the
conclusion fails): `disagreeSpace`, report `E_notConv = [∀x, A → B, ¬∀x, B → A]`. -/
theorem forall_conditional_blockers_tight_hperf :
    Sat disagreeSpace E_notConv ∧ LiterallySafe disagreeSpace E_notConv (.all (.imp xA xB)) ∧
    ConverseExcludable disagreeSpace xA xB ∧
    Entails disagreeSpace E_notConv (.not (.all (.imp xB xA))) ∧
    blockers disagreeSpace (stdAlt disagreeSpace) E_notConv (.all (.imp xA xB)) = [] := by
  decide +kernel

/-- Tightness of `hconv` in the blocker characterization (the other hypotheses hold; the
conclusion fails): `S12`, `a = b = xA`, empty report, which proves the (trivial) converse. -/
theorem forall_conditional_blockers_tight_hconv :
    Sat S12 [] ∧ LiterallySafe S12 [] (.all (.imp xA xA)) ∧ PerfectionConsistent S12 xA xA ∧
    ¬ Entails S12 [] (.not (.all (.imp xA xA))) ∧ Entails S12 [] (.all (.imp xA xA)) ∧
    blockers S12 (stdAlt S12) [] (.all (.imp xA xA)) = [] := by
  decide +kernel

/-- Non-vacuity of the blocker characterization, one report per branch (`S22`, `a = xA`,
`b = xB`): `E_notConv` refutes the converse, `[∀x, A ↔ B]` proves it, `[∀x, A → B]` leaves it
open; all hypotheses hold in each case. -/
theorem forall_conditional_blockers_nonvacuous :
    PerfectionConsistent S22 xA xB ∧ ConverseExcludable S22 xA xB ∧
    Sat S22 E_notConv ∧ LiterallySafe S22 E_notConv (.all (.imp xA xB)) ∧
    Entails S22 E_notConv (.not (.all (.imp xB xA))) ∧
    blockers S22 (stdAlt S22) E_notConv (.all (.imp xA xB)) = [.perfection] ∧
    Sat S22 [.all (.iff xA xB)] ∧ LiterallySafe S22 [.all (.iff xA xB)] (.all (.imp xA xB)) ∧
    Entails S22 [.all (.iff xA xB)] (.all (.imp xB xA)) ∧
    blockers S22 (stdAlt S22) [.all (.iff xA xB)] (.all (.imp xA xB)) = [.exhaustification] ∧
    Sat S22 [.all (.imp xA xB)] ∧ LiterallySafe S22 [.all (.imp xA xB)] (.all (.imp xA xB)) ∧
    Open S22 [.all (.imp xA xB)] (.all (.imp xB xA)) ∧
    blockers S22 (stdAlt S22) [.all (.imp xA xB)] (.all (.imp xA xB)) =
      [.perfection, .exhaustification] := by
  decide +kernel

/-- Tightness of `hperf` in `forall_conditional_blockers_of_open_converse` (the other hypothesis
holds; the conclusion fails): `disagreeSpace`, empty report. -/
theorem forall_conditional_open_tight_hperf :
    Open disagreeSpace [] (.all (.imp xB xA)) ∧
    blockers disagreeSpace (stdAlt disagreeSpace) [] (.all (.imp xA xB)) =
      [.exhaustification] := by
  decide +kernel

/-- Tightness of `hopen` in `forall_conditional_blockers_of_open_converse` (the other hypothesis
holds; the conclusion fails): `S22`, `E_notConv`, which refutes the converse. -/
theorem forall_conditional_open_tight_hopen :
    PerfectionConsistent S22 xA xB ∧
    blockers S22 (stdAlt S22) E_notConv (.all (.imp xA xB)) = [.perfection] := by
  decide +kernel

/-- Non-vacuity of `forall_conditional_blockers_of_open_converse`: `S22`, report
`[∀x, A → B]`. -/
theorem forall_conditional_open_nonvacuous :
    PerfectionConsistent S22 xA xB ∧ Open S22 [.all (.imp xA xB)] (.all (.imp xB xA)) := by
  decide +kernel

/-- Positive controls: flags restore safety. A report that refutes the converse needs only the
perfection flag; a report that proves the converse needs only the exhaustification flag; a report
that leaves the converse open needs both, and either flag alone is insufficient. -/
theorem forall_conditional_safe_with_blockers :
    StrengtheningSafe S22 (stdAlt S22) [.perfection] E_notConv (.all (.imp xA xB)) ∧
    StrengtheningSafe S22 (stdAlt S22) [.exhaustification] [.all (.iff xA xB)]
      (.all (.imp xA xB)) ∧
    StrengtheningSafe S22 (stdAlt S22) [.perfection, .exhaustification] [.all (.imp xA xB)]
      (.all (.imp xA xB)) ∧
    ¬ StrengtheningSafe S22 (stdAlt S22) [.perfection] [.all (.imp xA xB)] (.all (.imp xA xB)) ∧
    ¬ StrengtheningSafe S22 (stdAlt S22) [.exhaustification] [.all (.imp xA xB)]
      (.all (.imp xA xB)) := by
  decide +kernel

/-- In the full valuation spaces `S22` and `S32`, the distinct atoms `xA`, `xB` satisfy both
non-degeneracy conditions. -/
theorem distinct_atoms_nondegenerate_in_full_spaces :
    PerfectionConsistent S22 xA xB ∧ ConverseExcludable S22 xA xB ∧
    PerfectionConsistent S32 xA xB ∧ ConverseExcludable S32 xA xB := by
  decide +kernel

/-- If the report leaves the converse `∀x, b → a` open, neither the biconditional rendering
`∀x, a ↔ b` nor the rendering `(∀x, a → b) ∧ ¬(∀x, b → a)` is literally safe. -/
theorem open_converse_rewordings_not_literally_safe (S : Space) (E : List Claim) (a b : Claim)
    (hopen : Open S E (.all (.imp b a))) :
    ¬ LiterallySafe S E (.all (.iff a b)) ∧
    ¬ LiterallySafe S E (.and (.all (.imp a b)) (.not (.all (.imp b a)))) := by
  refine ⟨fun h => hopen.1 fun w hw hEw => holds_conv_of_holds_iff (h w hw hEw),
    fun h => hopen.2 fun w hw hEw => ?_⟩
  have := h w hw hEw
  rw [holds_and_eq, Bool.and_eq_true] at this
  exact this.2

/-- A quantifier-free single-value conditional also gets neighbouring-value alternatives: in
`S22`, for `p0 → q0` and a report refuting `q0 → p0`, the perfection flag alone is not enough
(exhaustification also negates `P0(1) → P1(1)`). -/
theorem single_value_conditional_needs_exhaustification_flag :
    Sat S22 [.imp p0 q0, .not (.imp q0 p0)] ∧
    LiterallySafe S22 [.imp p0 q0, .not (.imp q0 p0)] (.imp p0 q0) ∧
    blockers S22 (stdAlt S22) [.imp p0 q0, .not (.imp q0 p0)] (.imp p0 q0) =
      [.perfection, .exhaustification] ∧
    ¬ StrengtheningSafe S22 (stdAlt S22) [.perfection] [.imp p0 q0, .not (.imp q0 p0)]
      (.imp p0 q0) := by
  decide +kernel

/-- Blockers computed from the normal-form entries alone can be strictly larger than blockers
computed from the report: for `R_comp` and `E_comp` (which proves `R_comp`), the compressed
rendering `∀x, H ⇒ A` has entry blocker set `{qualifierDrop, exhaustification}` and report blocker
set `{exhaustification}`. -/
theorem entry_blockers_strictly_larger_than_report_blockers :
    (∀ q ∈ R_comp, LiterallySafe S32 E_comp (nfOf q)) ∧
    ConclusionDropping R_comp [(xH, [xA])] ∧
    blockers S32 (stdAlt S32) (R_comp.map nfOf) (renderComp [(xH, [xA])]) =
      [.qualifierDrop, .exhaustification] ∧
    blockers S32 (stdAlt S32) E_comp (renderComp [(xH, [xA])]) = [.exhaustification] := by
  decide +kernel

end Toy.Implicature
