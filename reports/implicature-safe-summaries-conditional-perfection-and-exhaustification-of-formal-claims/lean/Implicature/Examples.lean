import Implicature.Lemmas

/-!
# Fixtures and definition examples

Concrete atoms, spaces, and the proved positive and negative examples for every core
definition. All proofs are by evaluation (`decide +kernel`) or by short arguments from the
definitions.
-/

namespace Toy.Implicature

/-! ## Fixtures -/

/-- Atom `0` at the bound variable. -/
def xA : Claim := .atom 0 .var
/-- Atom `1` at the bound variable. -/
def xB : Claim := .atom 1 .var
/-- Atom `2` at the bound variable (used as a hypothesis). -/
def xH : Claim := .atom 2 .var
/-- Atom `0` at parameter value `0` (a closed propositional atom). -/
def p0 : Claim := .atom 0 (.lit 0)
/-- Atom `1` at parameter value `0` (a closed propositional atom). -/
def q0 : Claim := .atom 1 (.lit 0)

/-- One atom over two parameter values (4 worlds). -/
def S12 : Space := Space.full 1 2
/-- Two atoms over one parameter value (4 worlds): propositional logic in `p0`, `q0`. -/
def S21 : Space := Space.full 2 1
/-- Two atoms over two parameter values (16 worlds). -/
def S22 : Space := Space.full 2 2
/-- Three atoms over two parameter values (64 worlds). -/
def S32 : Space := Space.full 3 2

/-- A single interpreted world over the parameter values `0 … 7`: atom `0` is
"divisible by 4", atom `1` is "even"; other atoms are false. -/
def natSpace : Space :=
  Space.interp (List.range 8) fun a k =>
    if a = 0 then k % 4 == 0 else if a = 1 then k % 2 == 0 else false

/-- "`x` is divisible by 4" in `natSpace`. -/
def div4 : Claim := .atom 0 .var
/-- "`x` is even" in `natSpace`. -/
def even : Claim := .atom 1 .var

/-- A two-world space over one parameter value in which atoms `0` and `1` always disagree
(world `false`: `P0` false, `P1` true; world `true`: `P0` true, `P1` false). -/
def disagreeSpace : Space where
  World := Bool
  worlds := [false, true]
  params := [0]
  val w a _ := if a = 0 then w else !w

instance decConclusionDropping (R comp : List (Claim × List Claim)) :
    Decidable (ConclusionDropping R comp) := by
  unfold ConclusionDropping; infer_instance

/-! ## `Space.full` and `Space.holds` -/

/-- `Space.full 2 2` has the intended 16 worlds. -/
theorem full_world_count : S22.worlds.length = 16 := by decide +kernel

/-- Positive: world `3` (atom 0 true at values 0 and 1) satisfies `∀x, P0 x`. -/
theorem holds_pos_all_true_world : S12.holds (show S12.World from (3 : Nat)) (.all xA) = true := by
  decide +kernel

/-- Negative: world `1` (atom 0 true at value 0 only) does not satisfy `∀x, P0 x`. -/
theorem holds_neg_partial_world : S12.holds (show S12.World from (1 : Nat)) (.all xA) = false := by
  decide +kernel

/-- Negative: atoms outside the declared range are false in `Space.full`. -/
theorem full_out_of_range_atom_false :
    S12.holds (show S12.World from (3 : Nat)) (.ex (.atom 1 .var)) = false := by
  decide +kernel

/-! ## `Entails`, `Sat`, `Contradicts`, `Equiv` -/

/-- Positive: modus ponens is an entailment. -/
theorem entails_pos_modus_ponens : Entails S21 [p0, .imp p0 q0] q0 := by decide +kernel

/-- Negative: affirming the consequent is not an entailment. -/
theorem entails_neg_affirming_consequent : ¬ Entails S21 [.imp p0 q0, q0] p0 := by
  decide +kernel

/-- Positive: "for all x, A gives B, and not conversely" is satisfiable. -/
theorem sat_pos_not_conversely :
    Sat S22 [.all (.imp xA xB), .not (.all (.imp xB xA))] := by decide +kernel

/-- Negative: the biconditional together with the failure of the converse is unsatisfiable. -/
theorem sat_neg_iff_not_converse :
    ¬ Sat S22 [.all (.iff xA xB), .not (.all (.imp xB xA))] := by decide +kernel

/-- Positive: a report refuting the converse contradicts the biconditional. -/
theorem contradicts_pos :
    Contradicts S22 [.not (.all (.imp xB xA))] (.all (.iff xA xB)) := by decide +kernel

/-- Negative: a report that only proves `A → B` does not contradict the biconditional. -/
theorem contradicts_neg : ¬ Contradicts S22 [.all (.imp xA xB)] (.all (.iff xA xB)) := by
  decide +kernel

/-- Positive: `¬∀x, B → A` is equivalent to `∃x, B ∧ ¬A`. -/
theorem equiv_pos : Equiv S22 (.not (.all (.imp xB xA))) (.ex (.and xB (.not xA))) := by
  decide +kernel

/-- Negative: `∃x, A` is not equivalent to `∀x, A`. -/
theorem equiv_neg : ¬ Equiv S12 (.ex xA) (.all xA) := by decide +kernel

/-! ## Alternatives -/

/-- Positive: the alternatives of a universal conditional are its converse and its
biconditional. -/
theorem stdAlt_pos_conditional :
    stdAlt S22 (.all (.imp xA xB)) = [.all (.imp xB xA), .all (.iff xA xB)] := by decide +kernel

/-- Positive: the alternative of an existential is the universal. -/
theorem stdAlt_pos_existential : stdAlt S12 (.ex xA) = [.all xA] := by decide +kernel

/-- Positive: the alternatives of a relativized claim include the hypothesis-free claim. -/
theorem stdAlt_pos_relativized : stdAlt S32 (.all (.rel xH xA)) = [.all xA] := by decide +kernel

/-- Positive: a claim at value 1 has the neighbouring values 0 and 2 as alternatives. -/
theorem stdAlt_pos_neighbouring_values :
    stdAlt (Space.full 1 3) (.atom 0 (.lit 1)) = [.atom 0 (.lit 0), .atom 0 (.lit 2)] := by
  decide +kernel

/-- Positive: alternatives are substituted at one top-level conjunct at a time. -/
theorem stdAlt_pos_sites :
    stdAlt S22 (.and (.ex xA) (.ex xB)) = [.and (.all xA) (.ex xB), .and (.ex xA) (.all xB)] := by
  decide +kernel

/-- Negative: a universal claim has no alternatives (nothing stronger on its scale). -/
theorem stdAlt_neg_universal : stdAlt S12 (.all xA) = [] := by decide +kernel

/-- Negative: a negated quantified claim has no alternatives: the core rules do not look under
negation, and the neighbouring-value rule applies only to quantifier-free claims. (A negated
quantifier-free claim does get neighbouring-value alternatives,
`stdAlt_value_alternatives_any_connective`.) -/
theorem stdAlt_neg_under_negation : stdAlt S12 (.not (.ex xA)) = [] := by decide +kernel

/-- Negative: the neighbouring-value rule ignores values outside the parameter set. -/
theorem stdAlt_neg_value_outside_params : stdAlt S12 (.atom 0 (.lit 1)) = [.atom 0 (.lit 0)] := by
  decide +kernel

/-! ## Innocent exclusion and exhaustification -/

/-- The disjunction `p0 ∨ q0`. -/
def pOrQ : Claim := .or p0 q0
/-- The standard alternatives of a disjunction: the disjuncts and the conjunction. -/
def disjAlts : List Claim := [p0, q0, .and p0 q0]

/-- Positive: the neighbouring-value rule ignores connectives: a negated, disjunctive or
biconditional quantifier-free claim at value `0` gets the value-`1` alternative when `1` is a
parameter value; with a single parameter value (`S21`) the disjunction has no alternatives. -/
theorem stdAlt_value_alternatives_any_connective :
    stdAlt S12 (.not p0) = [.not (.atom 0 (.lit 1))] ∧
    stdAlt S22 pOrQ = [.or (.atom 0 (.lit 1)) (.atom 1 (.lit 1))] ∧
    stdAlt S22 (.iff p0 q0) = [.iff (.atom 0 (.lit 1)) (.atom 1 (.lit 1))] ∧
    stdAlt S21 pOrQ = [] := by
  decide +kernel

/-- Consequence of the value rule under negation: `¬P0(0)` is not strengthening-safe for the
report `[¬P0(0)]` in `S12`, because exhaustification adds `P0(1)`. -/
theorem negated_value_claim_exhaustified_reading_not_entailed :
    LiterallySafe S12 [.not p0] (.not p0) ∧
    ¬ StrengtheningSafe S12 (stdAlt S12) [] [.not p0] (.not p0) := by
  decide +kernel

/-- Positive: for "some", innocent exclusion negates "all". -/
theorem ieList_pos_some_not_all : ieList S12 (.ex xA) [.all xA] = [.all xA] := by decide +kernel

/-- Positive: the exhaustified "some" is "some but not all". -/
theorem exh_pos_some_but_not_all :
    Equiv S12 (exh S12 [.all xA] (.ex xA)) (.and (.ex xA) (.not (.all xA))) := by decide +kernel

/-- Positive: for a disjunction, innocent exclusion negates only the conjunction
(exclusive "or"). -/
theorem ieList_pos_disjunction : ieList S21 pOrQ disjAlts = [.and p0 q0] := by decide +kernel

/-- Negative: an alternative entailed by a satisfiable prejacent is not excluded. -/
theorem ieList_neg_entailed : ieList S12 (.all xA) [.ex xA] = [] := by decide +kernel

/-- Positive (textbook definition): "all" is innocently excludable for "some". -/
theorem innocentlyExcludable_pos :
    InnocentlyExcludable S12 (.ex xA) [.all xA] (.all xA) :=
  innocentlyExcludable_of_all_excludable (by decide) (by decide +kernel)

/-- Negative (textbook definition): "some" is not innocently excludable for "all": the empty
exclusion is maximal. -/
theorem innocentlyExcludable_neg :
    ¬ InnocentlyExcludable S12 (.all xA) [.ex xA] (.ex xA) := by
  intro ⟨_, h⟩
  have key : ∀ w ∈ S12.worlds, S12.holds w (.all xA) = true → S12.holds w (.ex xA) = true := by
    decide +kernel
  have hmax : MaximalExclusion S12 (.all xA) [.ex xA] [] := by
    refine ⟨⟨by simp, ?_⟩, ?_⟩
    · exact ⟨(3 : Nat), (List.mem_range.mpr (by decide) : (3 : Nat) ∈ List.range (2 ^ (1 * 2))),
        by decide +kernel, by simp⟩
    · intro Y ⟨hYA, w, hw, hσ, hY⟩ _ b hb
      have hb' : b = .ex xA := by simpa using hYA b hb
      subst hb'
      have := key w hw hσ
      rw [hY _ hb] at this
      cases this
  exact absurd (h [] hmax) (by simp)

/-- Negative (textbook definition): in a disjunction, a disjunct is not innocently excludable
(there is a maximal exclusion that keeps it). -/
theorem innocentlyExcludable_neg_disjunct : ¬ InnocentlyExcludable S21 pOrQ disjAlts p0 := by
  intro ⟨_, h⟩
  have key : ∀ w ∈ S21.worlds, S21.holds w pOrQ = true → S21.holds w p0 = false →
      S21.holds w q0 = false → False := by
    decide +kernel
  have hmax : MaximalExclusion S21 pOrQ disjAlts [q0, .and p0 q0] := by
    refine ⟨⟨by decide, (1 : Nat),
      (List.mem_range.mpr (by decide) : (1 : Nat) ∈ List.range (2 ^ (2 * 1))),
      by decide +kernel, by decide +kernel⟩, ?_⟩
    intro Y ⟨hYA, w, hw, hσ, hY⟩ hXY b hb
    have hq := hY q0 (hXY q0 (by simp))
    have hbA := hYA b hb
    simp only [disjAlts, List.mem_cons, List.mem_nil_iff, or_false] at hbA
    rcases hbA with rfl | rfl | rfl
    · exact (key w hw hσ (hY _ hb) hq).elim
    · simp
    · simp
  exact absurd (h _ hmax) (by decide)

/-- Positive: naive exhaustification of a disjunction negates every alternative. -/
theorem naiveExcl_pos_disjunction : naiveExcl S21 pOrQ disjAlts = disjAlts := by decide +kernel

/-- Negative: naive exhaustification keeps alternatives the prejacent entails. -/
theorem naiveExcl_neg_entailed : naiveExcl S12 (.all xA) [.ex xA] = [] := by decide +kernel

/-! ## Reader rules, readings, blockers -/

/-- Positive: perfection turns a universal conditional into a universal biconditional. -/
theorem step_perfection_pos :
    step S22 (stdAlt S22) .perfection (.all (.imp xA xB)) = [.all (.iff xA xB)] := by
  decide +kernel

/-- Negative: perfection does not apply to an existential. -/
theorem step_perfection_neg : step S12 (stdAlt S12) .perfection (.ex xA) = [] := by
  decide +kernel

/-- Positive: qualifier dropping removes the hypothesis of a relativized claim. -/
theorem step_drop_pos : step S32 (stdAlt S32) .qualifierDrop (.all (.rel xH xA)) = [.all xA] := by
  decide +kernel

/-- Negative: a stated conditional result is not a qualifier and is not dropped. -/
theorem step_drop_neg : step S22 (stdAlt S22) .qualifierDrop (.all (.imp xA xB)) = [] := by
  decide +kernel

/-- Positive: the unblocked reader of "for all x, A gives B" draws the perfected reading. -/
theorem readings_pos_perfection :
    (Claim.all (.iff xA xB)) ∈ readings S22 (stdAlt S22) [] (.all (.imp xA xB)) := by
  decide +kernel

/-- Negative: the perfection blocker removes the perfected reading. -/
theorem readings_neg_blocked :
    (Claim.all (.iff xA xB)) ∉ readings S22 (stdAlt S22) [.perfection] (.all (.imp xA xB)) := by
  decide +kernel

/-- Negative (cancellation): with an explicit "and not conversely", the perfected reading
contradicts the literal content and is not drawn. -/
theorem readings_neg_cancelled :
    (Claim.and (.all (.iff xA xB)) (.not (.all (.imp xB xA)))) ∉
      readings S22 (stdAlt S22) [] (.and (.all (.imp xA xB)) (.not (.all (.imp xB xA)))) := by
  decide +kernel

/-- The report of the running example: `∀x, A → B` and the converse fails. -/
def E_notConv : List Claim := [.all (.imp xA xB), .not (.all (.imp xB xA))]

/-- Positive: with the perfection blocker, "for all x, A gives B" is strengthening-safe for
`E_notConv`. -/
theorem strengtheningSafe_pos :
    StrengtheningSafe S22 (stdAlt S22) [.perfection] E_notConv (.all (.imp xA xB)) := by
  decide +kernel

/-- Negative: without blockers it is not. -/
theorem strengtheningSafe_neg :
    ¬ StrengtheningSafe S22 (stdAlt S22) [] E_notConv (.all (.imp xA xB)) := by
  decide +kernel

/-- Positive: the computed blocker set of the running example is exactly `[perfection]`. -/
theorem blockers_pos : blockers S22 (stdAlt S22) E_notConv (.all (.imp xA xB)) = [.perfection] := by
  decide +kernel

/-- Negative: a biconditional rendering of a proved biconditional needs no blocker. -/
theorem blockers_neg : blockers S22 (stdAlt S22) [.all (.iff xA xB)] (.all (.iff xA xB)) = [] := by
  decide +kernel

/-- The rendering "for all x, under H, A gives B". -/
def σ_relCond : Claim := .all (.rel xH (.imp xA xB))

/-- Positive: the composing reader draws "for all x, A iff B" from `σ_relCond` (drop, then
perfect). -/
theorem readingsStar_pos : (Claim.all (.iff xA xB)) ∈ readingsStar S32 (stdAlt S32) [] σ_relCond := by
  decide +kernel

/-- Negative: the one-step reader does not draw that reading. -/
theorem readings_neg_no_composition :
    (Claim.all (.iff xA xB)) ∉ readings S32 (stdAlt S32) [] σ_relCond := by decide +kernel

/-- Negative: with the qualifier-drop flag the composing reader no longer draws that reading. -/
theorem readingsStar_neg_blocked :
    (Claim.all (.iff xA xB)) ∉ readingsStar S32 (stdAlt S32) [.qualifierDrop] σ_relCond := by
  decide +kernel

/-- Positive: with the perfection flag, "for all x, A gives B" is strengthening-safe for the
composing reader and `E_notConv`. -/
theorem strengtheningSafeStar_pos :
    StrengtheningSafeStar S22 (stdAlt S22) [.perfection] E_notConv (.all (.imp xA xB)) := by
  decide +kernel

/-- Negative: without flags it is not. -/
theorem strengtheningSafeStar_neg :
    ¬ StrengtheningSafeStar S22 (stdAlt S22) [] E_notConv (.all (.imp xA xB)) := by
  decide +kernel

/-! ## Non-degeneracy conditions -/

/-- Positive: "for all x, A gives B" is consistent with "for all x, A iff B" in `S22`. -/
theorem perfectionConsistent_pos : PerfectionConsistent S22 xA xB := by decide +kernel

/-- Negative: "for all x, A gives not A" is inconsistent with "for all x, A iff not A". -/
theorem perfectionConsistent_neg : ¬ PerfectionConsistent S12 xA (.not xA) := by decide +kernel

/-- Positive: "for all x, A gives B" is consistent with the failure of its converse in `S22`. -/
theorem converseExcludable_pos : ConverseExcludable S22 xA xB := by decide +kernel

/-- Negative: "for all x, A gives A" entails its converse. -/
theorem converseExcludable_neg : ¬ ConverseExcludable S12 xA xA := by decide +kernel

/-! ## Normal form and compression -/

/-- Positive: keeping the hypothesis and a subset of the conclusions is conclusion dropping. -/
theorem conclusionDropping_pos : ConclusionDropping [(xH, [xA, xB])] [(xH, [xA])] := by
  decide +kernel

/-- Negative: replacing the hypothesis by `top` (dropping it) is not conclusion dropping. -/
theorem conclusionDropping_neg : ¬ ConclusionDropping [(xH, [xA, xB])] [(.top, [xA])] := by
  decide +kernel

/-- Negative: adding a conclusion is not conclusion dropping. -/
theorem conclusionDropping_neg_added : ¬ ConclusionDropping [(xH, [xA])] [(xH, [xA, xB])] := by
  decide +kernel

/-! ## Necessity words, tightness, disclaimers -/

/-- Positive: "evenness is needed for divisibility by 4" is true in `natSpace`. -/
theorem needed_pos : Entails natSpace [] (needed even div4) := by decide +kernel

/-- Negative: "divisibility by 4 is needed for evenness" is false in `natSpace`. -/
theorem needed_neg : Contradicts natSpace [] (needed div4 even) := by decide +kernel

/-- Positive: in `natSpace`, divisibility by 4 is tight for "under div4, even" (1 is neither). -/
theorem tightFor_pos : Entails natSpace [] (tightFor div4 even) := by decide +kernel

/-- Negative: no hypothesis is tight for a conclusion that holds everywhere. -/
theorem tightFor_neg : Contradicts natSpace [] (tightFor div4 (.or even (.not even))) := by
  decide +kernel

/-- `tightFor` does not check the theorem: `tightFor div4 (¬even)` holds in `natSpace` although
`∀x, div4 ⇒ ¬even` is false there. -/
theorem tightFor_does_not_check_theorem :
    Contradicts natSpace [] (.all (.rel div4 (.not even))) ∧
    Entails natSpace [] (tightFor div4 (.not even)) := by
  decide +kernel

/-- Positive: the empty report leaves `p0` open. -/
theorem open_pos : Open S21 [] p0 := by decide +kernel

/-- Negative: a report proving `p0` does not leave it open. -/
theorem open_neg : ¬ Open S21 [p0] p0 := by decide +kernel

/-- Positive: "`p0` is not shown, and not refuted" is safe for the empty report. -/
theorem disclaimerSafe_pos : DisclaimerSafe S21 [] (.notShownNotRefuted p0) := by decide +kernel

/-- Negative: "`p0` is not shown", read as "`p0` is false", is unsafe for the empty report. -/
theorem disclaimerSafe_neg : ¬ DisclaimerSafe S21 [] (.notShown p0) := by decide +kernel

/-- Negative: a false disclaimer is not safe ("not shown" when `E` proves `p0`). -/
theorem disclaimerTrue_neg : ¬ DisclaimerTrue S21 [p0] (.notShown p0) := by decide +kernel

end Toy.Implicature
