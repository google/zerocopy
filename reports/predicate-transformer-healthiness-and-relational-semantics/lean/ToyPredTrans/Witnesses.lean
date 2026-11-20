import ToyPredTrans.Programs
import ToyPredTrans.SmallStateSpaces

/-!
# Tightness witnesses, non-vacuity theorems and positive controls

Everything in this file is fully proved, and nothing here depends on the main statements of
`Main`.  Tightness counterexamples are stated in canonical form: a concrete instance satisfies
the listed laws and fails the listed conclusion.

Classical logic cannot be removed by exhibiting a countermodel inside Lean, whose logic
includes excluded middle and choice.  Its necessity is witnessed instead in the
reverse-mathematics form: a theorem whose hypothesis is the statement in question (restricted
to the one-point state type `Unit`) and whose conclusion is excluded middle
(`∀ P : Prop, P ∨ ¬ P`) or the limited principle of omniscience, proved without
`Classical.choice` (`#print axioms` reports no axiom at all for every such witness except
`lem_of_chaosNormal_unique_of_wp_eq`, which uses only `propext` and `Quot.sound`; see the
package's axiom audit).
-/

namespace Toy.PredTrans

/-! ## The lawful-but-unintended transformer `eventually` -/

/-- `eventually` is not the `wp` of any relational program. -/
theorem eventually_ne_wp (R : Rel Nat) (term : Pred Nat) : eventually ≠ wp R term := by
  intro h
  apply not_conjNonempty_eventually
  rw [h]
  exact conjNonempty_wp R term

/-- `eventually` is not the `wlp` of any relation. -/
theorem eventually_ne_wlp (R : Rel Nat) : eventually ≠ wlp R := by
  intro h
  rw [wlp_eq_wp_true] at h
  exact eventually_ne_wp R _ h

/-- **Finitary laws do not pin down relational semantics.**  The transformer `eventually` on
`Nat` ("the postcondition holds of all but finitely many numbers") is monotone, binary
conjunctive, top preserving and strict, yet it is neither the `wlp` of any relation nor the
`wp` of any relation with any non-abortion predicate.  It is not ω-continuous and not
positively conjunctive. -/
theorem eventually_finitary_laws_not_relational :
    Monotone eventually ∧ ConjBin eventually ∧ TopPreserving eventually ∧ Strict eventually ∧
      ¬ OmegaContinuous eventually ∧ ¬ ConjNonempty eventually ∧
      (¬ ∃ R : Rel Nat, eventually = wlp R) ∧
      (¬ ∃ (R : Rel Nat) (term : Pred Nat), eventually = wp R term) := by
  refine ⟨monotone_eventually, conjBin_eventually, topPreserving_eventually,
    strict_eventually, not_omegaContinuous_eventually, not_conjNonempty_eventually, ?_, ?_⟩
  · intro h
    obtain ⟨R, hR⟩ := h
    exact eventually_ne_wlp R hR
  · intro h
    obtain ⟨R, term, hR⟩ := h
    exact eventually_ne_wp R term hR

/-- `eventually` distributes over the conjunction of every finite list of postconditions:
only infinite conjunctions separate it from a `wlp`. -/
theorem eventually_conjList (l : List (Pred Nat)) (s : Nat) :
    eventually (fun t => ∀ Q, Q ∈ l → Q t) s ↔ ∀ Q, Q ∈ l → eventually Q s :=
  conjList_of_conjBin_of_topPreserving conjBin_eventually topPreserving_eventually l s

/-- The same fact as a failed implication: monotonicity, binary conjunctivity, top
preservation and strictness together do not imply that a transformer on `Nat` is a `wp`. -/
theorem finitary_laws_do_not_imply_relational :
    ¬ ∀ T : Transformer Nat, Monotone T → ConjBin T → TopPreserving T → Strict T →
        ∃ (R : Rel Nat) (term : Pred Nat), T = wp R term := by
  intro h
  obtain ⟨R, term, hR⟩ :=
    h eventually monotone_eventually conjBin_eventually topPreserving_eventually
      strict_eventually
  exact eventually_ne_wp R term hR

/-- Positive control: with the threshold fixed, the transformer *is* a `wlp`.  `fromN N` is
the `wlp` of "set the state to any number `≥ N`". -/
theorem fromN_eq_wlp (N : Nat) : fromN N = wlp (fun _ s' => N ≤ s') :=
  trans_ext fun _ _ => Iff.rfl

/-- `eventually` is the angelic choice, over the threshold `N`, of the relational
transformers `fromN N`.  The failure to be relational comes entirely from this outer angelic
choice. -/
theorem eventually_iff_exists_fromN (Q : Pred Nat) (s : Nat) :
    eventually Q s ↔ ∃ N, fromN N Q s :=
  Iff.rfl

/-! ## Characterization of `wlp`: witnesses -/

/-- Non-vacuity: the `wlp` of the two-way choice `stepR` is universally conjunctive, and
`eventually` is not; both sides of the characterization occur. -/
theorem conjAll_wlp_stepR_and_not_conjAll_eventually :
    ConjAll (wlp stepR) ∧ ¬ ConjAll eventually :=
  ⟨conjAll_wlp stepR, not_conjAll_eventually⟩

/-- The empty family cannot be dropped from universal conjunctivity: `abortT` is positively
conjunctive (and strict, and monotone) but is not the `wlp` of any relation. -/
theorem abortT_conjNonempty_not_wlp :
    ConjNonempty (abortT : Transformer Unit) ∧ Strict (abortT : Transformer Unit) ∧
      ¬ ∃ R : Rel Unit, (abortT : Transformer Unit) = wlp R := by
  refine ⟨conjNonempty_abortT, strict_abortT, ?_⟩
  intro h
  obtain ⟨R, hR⟩ := h
  apply not_topPreserving_abortT
  rw [hR]
  exact topPreserving_wlp R

/-- An honest partial program separates the two characterizations: the `wp` of the partial
decrement is positively conjunctive but is not the `wlp` of any relation. -/
theorem wp_predR_posP_conjNonempty_not_wlp :
    ConjNonempty (wp predR posP) ∧ ¬ ∃ R : Rel Nat, wp predR posP = wlp R := by
  refine ⟨conjNonempty_wp predR posP, ?_⟩
  intro h
  obtain ⟨R, hR⟩ := h
  have ht : TopPreserving (wp predR posP) := by
    rw [hR]
    exact topPreserving_wlp R
  exact (ht 0).1 rfl

/-! ## Characterization of `wp`: witnesses -/

/-- Non-vacuity: the `wp` of the partial decrement is positively conjunctive, and
`eventually` is not; both sides of the characterization occur. -/
theorem conjNonempty_wp_predR_posP_and_not_conjNonempty_eventually :
    ConjNonempty (wp predR posP) ∧ ¬ ConjNonempty eventually :=
  ⟨conjNonempty_wp predR posP, not_conjNonempty_eventually⟩

/-- Conjunctivity cannot be weakened to monotonicity, even together with strictness, top
preservation and ω-continuity: angelic havoc on `Bool` satisfies all four and is not a
`wp`. -/
theorem angelic_laws_not_wp :
    Monotone (angelic : Transformer Bool) ∧ Strict (angelic : Transformer Bool) ∧
      TopPreserving (angelic : Transformer Bool) ∧ OmegaContinuous (angelic : Transformer Bool) ∧
      ¬ ∃ (R : Rel Bool) (term : Pred Bool), (angelic : Transformer Bool) = wp R term := by
  refine ⟨monotone_angelic, ?_, fun _ => ⟨true, trivial⟩, omegaContinuous_angelic, ?_⟩
  · intro s h
    obtain ⟨_, hx⟩ := h
    exact hx
  · intro h
    obtain ⟨R, term, hR⟩ := h
    apply not_conjNonempty_angelic
    rw [hR]
    exact conjNonempty_wp R term

/-- A non-monotone transformer is not a `wp`. -/
theorem negT_ne_wp (R : Rel Unit) (term : Pred Unit) : (negT : Transformer Unit) ≠ wp R term := by
  intro h
  apply not_monotone_negT
  rw [h]
  exact monotone_wp R term

/-- Canonical form: negation is not monotone and is not the `wp` of any relational program. -/
theorem negT_not_monotone_not_wp :
    ¬ Monotone (negT : Transformer Unit) ∧
      ¬ ∃ (R : Rel Unit) (term : Pred Unit), (negT : Transformer Unit) = wp R term :=
  ⟨not_monotone_negT, fun ⟨R, term, h⟩ => negT_ne_wp R term h⟩

/-- The class of `wp`s deliberately contains transformers that are neither strict nor top
preserving: the constant transformer with precondition "the state is `true`" on `Bool` is
positively conjunctive, miraculous at `true` and aborting at `false`. -/
theorem constT_conjNonempty_not_strict_not_topPreserving :
    ConjNonempty (constT (fun b : Bool => b = true)) ∧
      ¬ Strict (constT (fun b : Bool => b = true)) ∧
      ¬ TopPreserving (constT (fun b : Bool => b = true)) := by
  refine ⟨?_, fun h => h true rfl, fun h => ?_⟩
  · rw [constT_eq_wp_emptyR]
    exact conjNonempty_wp _ _
  · have h1 : false = true := h false
    cases h1

/-- The relation of a `wp` is not determined outside the termination predicate: the partial
decrement and its chaos normal form are different relations with the same `wp` (and the same
termination predicate). -/
theorem wp_same_with_different_relations :
    wp (fun s s' => posP s → predR s s') posP = wp predR posP ∧
      (fun s s' => posP s → predR s s') ≠ predR := by
  refine ⟨wp_chaos_eq predR posP, ?_⟩
  intro h
  have h1 : (posP 0 → predR 0 0) = predR 0 0 := congrFun (congrFun h 0) 0
  have h2 : predR 0 0 := h1.mp fun hp => (hp rfl).elim
  have e : (0 : Nat) = 0 + 1 := h2
  omega

/-! ## Strictness: witnesses -/

/-- The partial decrement with termination predicate "nonzero" is strict. -/
theorem strict_wp_predR_posP : Strict (wp predR posP) := by
  intro s h
  obtain ⟨hs, hw⟩ := h
  have hs' : s ≠ 0 := hs
  exact hw (s - 1) (show s = s - 1 + 1 by omega)

/-- The decrement with the everywhere-true termination predicate is not strict: state `0`
is a miracle. -/
theorem not_strict_wp_predR_true : ¬ Strict (wp predR (fun _ => True)) := by
  intro h
  apply h 0
  refine ⟨trivial, ?_⟩
  intro s' hs
  have e : 0 = s' + 1 := hs
  omega

/-- Non-vacuity for the strictness correspondence: an instance where both sides hold and an
instance where both sides fail. -/
theorem strict_wp_both_sides_occur :
    (Strict (wp predR posP) ∧ TotalOn predR posP) ∧
      (¬ Strict (wp predR (fun _ => True)) ∧ ¬ TotalOn predR (fun _ => True)) :=
  ⟨⟨strict_wp_predR_posP, totalOn_predR_posP⟩,
   ⟨not_strict_wp_predR_true, not_totalOn_predR_true⟩⟩

/-- The restriction to terminating start states is needed: `wp predR posP` is strict although
`predR` is not total on all states. -/
theorem strict_wp_without_total_relation :
    Strict (wp predR posP) ∧ ¬ ∀ s, ∃ s', predR s s' := by
  refine ⟨strict_wp_predR_posP, ?_⟩
  intro h
  obtain ⟨s', hs'⟩ := h 0
  have e : 0 = s' + 1 := hs'
  omega

/-! ## Continuity: witnesses -/

/-- The `wp` of the two-way choice with the everywhere-true termination predicate is
ω-continuous. -/
theorem omegaContinuous_wp_stepR_true : OmegaContinuous (wp stepR (fun _ => True)) := by
  rw [← wlp_eq_wp_true]
  exact omegaContinuous_wlp_stepR

/-- The `wp` of `havoc` on `Nat` with the everywhere-true termination predicate is not
ω-continuous. -/
theorem not_omegaContinuous_wp_havocR_nat_true :
    ¬ OmegaContinuous (wp (havocR : Rel Nat) (fun _ => True)) := by
  rw [← wlp_eq_wp_true]
  exact not_omegaContinuous_wlp_havocR_nat

/-- Non-vacuity for the continuity correspondence: an instance where both sides hold and an
instance where both sides fail. -/
theorem omegaContinuous_wp_both_sides_occur :
    (OmegaContinuous (wp stepR (fun _ => True)) ∧ ∀ s, True → FiniteImage stepR s) ∧
      (¬ OmegaContinuous (wp (havocR : Rel Nat) (fun _ => True)) ∧
        ¬ ∀ s, True → FiniteImage (havocR : Rel Nat) s) :=
  ⟨⟨omegaContinuous_wp_stepR_true, fun s _ => finiteImage_stepR s⟩,
   ⟨not_omegaContinuous_wp_havocR_nat_true, fun h => not_finiteImage_havocR_nat 0 (h 0 trivial)⟩⟩

/-- The restriction to terminating start states is needed: `abort`, presented with the
`havoc` relation, is ω-continuous although the relation has an infinite image at every
state. -/
theorem omegaContinuous_wp_with_infinite_image_outside_term :
    OmegaContinuous (wp (havocR : Rel Nat) (fun _ => False)) ∧
      ∀ s, ¬ FiniteImage (havocR : Rel Nat) s :=
  ⟨fun _ _ _ h => False.elim h.1, not_finiteImage_havocR_nat⟩

/-- ω-continuity is not implied by the other laws, and demanding it excludes an honest
program: the `wlp` of `havoc` on `Nat` is universally conjunctive and strict but not
ω-continuous. -/
theorem havocR_nat_conjAll_strict_not_omegaContinuous :
    ConjAll (wlp (havocR : Rel Nat)) ∧ Strict (wlp (havocR : Rel Nat)) ∧
      ¬ OmegaContinuous (wlp (havocR : Rel Nat)) :=
  ⟨conjAll_wlp _, fun s h => h s trivial, not_omegaContinuous_wlp_havocR_nat⟩

/-! ## Refinement: witnesses -/

/-- Non-vacuity for the refinement correspondence: `havoc` is refined by the two-way choice,
and not conversely. -/
theorem refinedBy_wp_both_sides_occur :
    RefinedBy (wp (havocR : Rel Nat) (fun _ => True)) (wp stepR (fun _ => True)) ∧
      ¬ RefinedBy (wp stepR (fun _ => True)) (wp (havocR : Rel Nat) (fun _ => True)) := by
  refine ⟨fun _ _ h => ⟨trivial, fun s' _ => h.2 s' trivial⟩, ?_⟩
  intro h
  have h0 := h (fun n => 0 < n) 0 ⟨trivial, wlp_stepR_pos⟩
  have h1 : 0 < 0 := h0.2 0 trivial
  omega

/-- The comparison of relations must be restricted to terminating start states of the
refined program: `abort` presented with the empty relation is refined by `havoc`, although
`havoc`'s relation is not included in the empty relation. -/
theorem refinedBy_wp_without_global_relation_inclusion :
    RefinedBy (wp (emptyR : Rel Unit) (fun _ => False)) (wp (havocR : Rel Unit) (fun _ => True)) ∧
      ¬ ∀ s s', (havocR : Rel Unit) s s' → (emptyR : Rel Unit) s s' :=
  ⟨fun _ _ h => False.elim h.1, fun h => h () () trivial⟩

/-- Inclusion of termination predicates cannot be dropped, even for pairs in chaos normal
form: `havoc` and `abort` (both presented with the `havoc` relation, both in chaos normal
form, relations equal) are not in the refinement relation. -/
theorem relation_inclusion_without_term_inclusion_not_refinedBy :
    ChaosNormal (havocR : Rel Unit) (fun _ => True) ∧
      ChaosNormal (havocR : Rel Unit) (fun _ => False) ∧
      (∀ s s', (havocR : Rel Unit) s s' → (havocR : Rel Unit) s s') ∧
      ¬ RefinedBy (wp (havocR : Rel Unit) (fun _ => True))
          (wp (havocR : Rel Unit) (fun _ => False)) :=
  ⟨fun _ _ _ => trivial, fun _ _ _ => trivial, fun _ _ h => h,
   fun h => (h (fun _ => True) () ⟨trivial, fun _ _ => trivial⟩).1⟩

/-! ## Finite state types: witnesses -/

/-- Non-vacuity: `Bool` is finite and the `wlp` of `skip` on `Bool` is binary conjunctive. -/
theorem finiteState_conjBin_nonvacuous :
    FiniteState Bool ∧ ConjBin (wlp (skipR : Rel Bool)) :=
  ⟨finiteState_bool, conjBin_wlp _⟩

/-- Finiteness of the state type cannot be dropped: on `Nat` (not finite), `eventually` is
binary conjunctive but not positively conjunctive. -/
theorem eventually_infinite_conjBin_not_conjNonempty :
    ¬ FiniteState Nat ∧ ConjBin eventually ∧ ¬ ConjNonempty eventually :=
  ⟨not_finiteState_nat, conjBin_eventually, not_conjNonempty_eventually⟩

/-- Binary conjunctivity cannot be weakened to monotonicity, even on a finite state type:
angelic havoc on `Bool` is monotone but not positively conjunctive. -/
theorem angelic_finiteState_monotone_not_conjNonempty :
    FiniteState Bool ∧ Monotone (angelic : Transformer Bool) ∧ ¬ ConjNonempty (angelic : Transformer Bool) :=
  ⟨finiteState_bool, monotone_angelic, not_conjNonempty_angelic⟩

/-! ## Countable continuity: witnesses -/

/-- Non-vacuity: `Nat` is countable and the `wlp` of the two-way choice is binary conjunctive
and ω-continuous. -/
theorem countable_conjBin_omegaContinuous_nonvacuous :
    CountableState Nat ∧ ConjBin (wlp stepR) ∧ OmegaContinuous (wlp stepR) :=
  ⟨countableState_nat, conjBin_wlp stepR, omegaContinuous_wlp_stepR⟩

/-- Binary conjunctivity cannot be dropped (or weakened to monotonicity): angelic havoc on
the countable type `Bool` is monotone and ω-continuous but not positively conjunctive. -/
theorem angelic_countable_omegaContinuous_not_conjNonempty :
    CountableState Bool ∧ Monotone (angelic : Transformer Bool) ∧
      OmegaContinuous (angelic : Transformer Bool) ∧ ¬ ConjNonempty (angelic : Transformer Bool) :=
  ⟨countableState_bool, monotone_angelic, omegaContinuous_angelic, not_conjNonempty_angelic⟩

/-- ω-continuity cannot be dropped: `eventually` on the countable type `Nat` is binary
conjunctive but not positively conjunctive. -/
theorem eventually_countable_conjBin_not_conjNonempty :
    CountableState Nat ∧ ConjBin eventually ∧ ¬ ConjNonempty eventually :=
  ⟨countableState_nat, conjBin_eventually, not_conjNonempty_eventually⟩

/-! ## Finitary laws: further scope witnesses -/

/-- `eventually` is not binary disjunctive: the even and the odd numbers together hold of
every number, but neither holds of all sufficiently large numbers.  So the example says
nothing about the list of finitary laws extended by binary disjunctivity. -/
theorem not_disjBin_eventually :
    eventually (fun n => n % 2 = 0 ∨ n % 2 = 1) 0 ∧
      ¬ eventually (fun n => n % 2 = 0) 0 ∧ ¬ eventually (fun n => n % 2 = 1) 0 := by
  refine ⟨⟨0, fun n _ => by omega⟩, ?_, ?_⟩
  · intro h
    obtain ⟨N, hN⟩ := h
    have h1 := hN (2 * N + 1) (by omega)
    omega
  · intro h
    obtain ⟨N, hN⟩ := h
    have h1 := hN (2 * N + 2) (by omega)
    omega

/-- The finiteness that matters is that of the whole state type, not of the relation read off
by `relOf`: `relOf eventually` is the empty relation (finite image everywhere), yet
`eventually` is not positively conjunctive. -/
theorem relOf_eventually_finite_not_conjNonempty :
    (∀ s, FiniteImage (relOf eventually) s) ∧ ¬ ConjNonempty eventually := by
  refine ⟨fun s => ?_, not_conjNonempty_eventually⟩
  rw [relOf_eventually]
  exact finiteImage_emptyR s

/-- Positive conjunctivity on a finite state type does not give universal conjunctivity:
`abort` on the one-point state type is binary conjunctive (indeed positively conjunctive) but
not universally conjunctive. -/
theorem abortT_finiteState_conjBin_not_conjAll :
    FiniteState Unit ∧ ConjBin (abortT : Transformer Unit) ∧ ¬ ConjAll (abortT : Transformer Unit) :=
  ⟨⟨[()], fun _ => List.mem_cons_self⟩, conjBin_of_conjNonempty conjNonempty_abortT,
    not_conjAll_abortT⟩

/-! ## `wlp` and `wp` are not disjunctive for nondeterministic programs -/

/-- The `wlp` of the two-way choice `stepR` is not binary disjunctive: from `0` the final state
is `1` or `2`, but neither "the final state is `1`" nor "the final state is `2`" is
guaranteed. -/
theorem not_disjBin_wlp_stepR :
    wlp stepR (fun n => n = 1 ∨ n = 2) 0 ∧
      ¬ wlp stepR (fun n => n = 1) 0 ∧ ¬ wlp stepR (fun n => n = 2) 0 := by
  refine ⟨fun s' hs => ?_, not_wlp_stepR_eq_one, fun h => ?_⟩
  · have hs' : s' = 0 + 1 ∨ s' = 0 + 2 := hs
    omega
  · have h1 : (1 : Nat) = 2 := h 1 (Or.inl rfl)
    omega

/-! ## The non-abortion domain includes miracles -/

/-- `termOf` holds at a miraculous state, which has no possible outcome: for the demonic update
of the empty relation, `termOf` holds at the only state, which has no successor. -/
theorem termOf_wlp_emptyR_no_outcome :
    termOf (wlp (emptyR : Rel Unit)) () ∧ ¬ ∃ s', (emptyR : Rel Unit) () s' :=
  ⟨fun _ h => False.elim h, fun ⟨_, h⟩ => h⟩

/-! ## The relational refinement criterion applies to `wp`s only -/

/-- For transformers that are not `wp`s, the relational criterion read off by `termOf` and
`relOf` does not characterize refinement: the demonic update of the empty relation (`magic`)
and `eventually` have the same non-abortion domain (everything) and the same `relOf` (empty),
so the criterion holds in both directions, yet `magic` is not refined by `eventually`. -/
theorem relational_criterion_fails_off_wp :
    (∀ s, termOf (wlp (emptyR : Rel Nat)) s → termOf eventually s) ∧
      (∀ s, termOf (wlp (emptyR : Rel Nat)) s → ∀ s',
        relOf eventually s s' → relOf (wlp (emptyR : Rel Nat)) s s') ∧
      ¬ RefinedBy (wlp (emptyR : Rel Nat)) eventually := by
  refine ⟨fun s _ => topPreserving_eventually s, fun s _ s' h => ?_, fun h => ?_⟩
  · rw [relOf_eventually] at h
    exact False.elim h
  · exact strict_eventually 0 (h (fun _ => False) 0 fun _ hr => False.elim hr)

/-! ## Classical logic: strictness -/

/-- The strictness correspondence, restricted to `Unit`, implies excluded middle.  Proved
without any axiom. -/
theorem lem_of_strict_wp_iff_totalOn
    (h : ∀ (R : Rel Unit) (term : Pred Unit), Strict (wp R term) ↔ TotalOn R term) :
    ∀ P : Prop, P ∨ ¬ P := by
  intro P
  let R : Rel Unit := fun _ _ => P ∨ ¬ P
  let term : Pred Unit := fun _ => True
  have hst : Strict (wp R term) := fun _ hw => hw.2 () (Or.inr fun hp => hw.2 () (Or.inl hp))
  obtain ⟨_, hp⟩ := (h R term).mp hst () trivial
  exact hp

/-- The strictness correspondence for `wlp`, restricted to `Unit`, implies excluded middle.
Proved without any axiom. -/
theorem lem_of_strict_wlp_iff
    (h : ∀ R : Rel Unit, Strict (wlp R) ↔ ∀ s, ∃ s', R s s') :
    ∀ P : Prop, P ∨ ¬ P := by
  intro P
  let R : Rel Unit := fun _ _ => P ∨ ¬ P
  have hst : Strict (wlp R) := fun _ hw => hw () (Or.inr fun hp => hw () (Or.inl hp))
  obtain ⟨_, hp⟩ := (h R).mp hst ()
  exact hp

/-! ## Classical logic: chaos normal form -/

/-- Recovery of a chaos-normal relation by `relOf`, restricted to `Unit`, implies excluded
middle.  Proved without any axiom. -/
theorem lem_of_relOf_wp_of_chaosNormal
    (h : ∀ (R : Rel Unit) (term : Pred Unit), ChaosNormal R term → relOf (wp R term) = R) :
    ∀ P : Prop, P ∨ ¬ P := by
  intro P
  let R : Rel Unit := fun _ _ => P ∨ ¬ P
  let term : Pred Unit := fun _ => P
  have hcn : ChaosNormal R term := fun _ hnp _ => Or.inr hnp
  have heq : relOf (wp R term) () () = R () () := congrFun (congrFun (h R term hcn) ()) ()
  have hrel : relOf (wp R term) () () := fun _ hw => hw.2 () (Or.inl hw.1)
  exact heq.mp hrel

/-- Uniqueness of the chaos normal form, restricted to `Unit`, implies excluded middle.  The
proof uses no axiom other than `propext` and `Quot.sound` (to compare two transformers
extensionally); in particular it uses no choice. -/
theorem lem_of_chaosNormal_unique_of_wp_eq
    (h : ∀ {R R' : Rel Unit} {t t' : Pred Unit},
      ChaosNormal R t → ChaosNormal R' t' → wp R t = wp R' t' → R = R' ∧ t = t') :
    ∀ P : Prop, P ∨ ¬ P := by
  intro P
  let R₁ : Rel Unit := fun _ _ => P ∨ ¬ P
  let R₂ : Rel Unit := fun _ _ => True
  let t : Pred Unit := fun _ => P
  have hcn₁ : ChaosNormal R₁ t := fun _ hnp _ => Or.inr hnp
  have hcn₂ : ChaosNormal R₂ t := fun _ _ _ => trivial
  have hwp : wp R₁ t = wp R₂ t :=
    trans_ext fun _ _ =>
      ⟨fun h1 => ⟨h1.1, fun _ _ => h1.2 () (Or.inl h1.1)⟩,
       fun h2 => ⟨h2.1, fun _ _ => h2.2 () trivial⟩⟩
  have heq : R₁ () () = R₂ () () := congrFun (congrFun (h hcn₁ hcn₂ hwp).1 ()) ()
  exact heq.mpr trivial

/-- The global-inclusion form of the refinement correspondence, restricted to `Unit`, implies
excluded middle.  Proved without any axiom. -/
theorem lem_of_refinedBy_wp_iff_of_chaosNormal
    (h : ∀ {R₁ R₂ : Rel Unit} {t₁ t₂ : Pred Unit},
      ChaosNormal R₁ t₁ →
      (RefinedBy (wp R₁ t₁) (wp R₂ t₂) ↔ (∀ s, t₁ s → t₂ s) ∧ ∀ s s', R₂ s s' → R₁ s s')) :
    ∀ P : Prop, P ∨ ¬ P := by
  intro P
  let R₁ : Rel Unit := fun _ _ => P ∨ ¬ P
  let R₂ : Rel Unit := fun _ _ => True
  let t₁ : Pred Unit := fun _ => P
  let t₂ : Pred Unit := fun _ => True
  have hcn : ChaosNormal R₁ t₁ := fun _ hnp _ => Or.inr hnp
  have href : RefinedBy (wp R₁ t₁) (wp R₂ t₂) :=
    fun _ _ h1 => ⟨trivial, fun _ _ => h1.2 () (Or.inl h1.1)⟩
  exact ((h hcn).mp href).2 () () trivial

/-! ## Classical logic: finite, continuum and directed conjunctivity results -/

/-- The transformer `Q ↦ Q () ∨ B` on `Unit`, for a fixed proposition `B`. -/
def orT (B : Prop) : Transformer Unit := fun Q _ => Q () ∨ B

/-- `orT B` is binary conjunctive, without any axiom. -/
theorem conjBin_orT (B : Prop) : ConjBin (orT B) := by
  intro P Q _
  constructor
  · intro h
    cases h with
    | inl hpq => exact ⟨Or.inl hpq.1, Or.inl hpq.2⟩
    | inr hb => exact ⟨Or.inr hb, Or.inr hb⟩
  · intro h
    cases h.1 with
    | inl hp =>
      cases h.2 with
      | inl hq => exact Or.inl ⟨hp, hq⟩
      | inr hb => exact Or.inr hb
    | inr hb => exact Or.inr hb

/-- `orT B` is ω-continuous, without any axiom. -/
theorem omegaContinuous_orT (B : Prop) : OmegaContinuous (orT B) := by
  intro Q _ _ hq
  cases hq with
  | inl hn =>
    obtain ⟨n, hn⟩ := hn
    exact ⟨n, Or.inl hn⟩
  | inr hb => exact ⟨0, Or.inr hb⟩

/-- `orT B` is continuous over directed families, without any axiom. -/
theorem dirContinuous_orT (B : Prop) : DirContinuous (orT B) := by
  intro ι Q hdir _ hq
  cases hq with
  | inl hn =>
    obtain ⟨i, hi⟩ := hn
    exact ⟨i, Or.inl hi⟩
  | inr hb =>
    obtain ⟨i₀⟩ := hdir.1
    exact ⟨i₀, Or.inr hb⟩

/-- If `orT B` is positively conjunctive then `B ∨ ¬ B`; without any axiom. -/
theorem em_of_conjNonempty_orT (B : Prop) (h : ConjNonempty (orT B)) : B ∨ ¬ B := by
  let ι : Type := { P : Prop // P ∨ B }
  have hne : Nonempty ι := ⟨⟨True, Or.inl trivial⟩⟩
  have hres : (∀ i : ι, i.1) ∨ B := (h ι (fun i _ => i.1) hne ()).mpr fun i => i.2
  cases hres with
  | inl h0 => exact Or.inr fun hb => h0 ⟨False, Or.inr hb⟩
  | inr hb => exact Or.inl hb

/-- The finite-state result, restricted to `Unit`, implies excluded middle.  Proved without
any axiom. -/
theorem lem_of_conjNonempty_of_conjBin_of_finiteState
    (h : FiniteState Unit → ∀ {T : Transformer Unit}, ConjBin T → ConjNonempty T) :
    ∀ B : Prop, B ∨ ¬ B :=
  fun B => em_of_conjNonempty_orT B (h ⟨[()], fun _ => List.mem_cons_self⟩ (conjBin_orT B))

/-- The continuum-state result, restricted to `Unit`, implies excluded middle.  Proved without
any axiom. -/
theorem lem_of_conjNonempty_of_conjBin_of_omegaContinuous_of_continuumState
    (h : ContinuumState Unit → ∀ {T : Transformer Unit},
      ConjBin T → OmegaContinuous T → ConjNonempty T) :
    ∀ B : Prop, B ∨ ¬ B :=
  fun B => em_of_conjNonempty_orT B
    (h ⟨fun _ _ => false, fun _ _ _ => rfl⟩ (conjBin_orT B) (omegaContinuous_orT B))

/-- The countable-state result, restricted to `Unit`, implies excluded middle.  Proved without
any axiom. -/
theorem lem_of_conjNonempty_of_conjBin_of_omegaContinuous_of_countable
    (h : CountableState Unit → ∀ {T : Transformer Unit},
      ConjBin T → OmegaContinuous T → ConjNonempty T) :
    ∀ B : Prop, B ∨ ¬ B :=
  fun B => em_of_conjNonempty_orT B
    (h ⟨fun _ => 0, fun _ _ _ => rfl⟩ (conjBin_orT B) (omegaContinuous_orT B))

/-- The directed-continuity result, restricted to `Unit`, implies excluded middle.  Proved
without any axiom. -/
theorem lem_of_conjNonempty_of_conjBin_of_dirContinuous
    (h : ∀ {T : Transformer Unit}, ConjBin T → DirContinuous T → ConjNonempty T) :
    ∀ B : Prop, B ∨ ¬ B :=
  fun B => em_of_conjNonempty_orT B (h (conjBin_orT B) (dirContinuous_orT B))

/-! ## Classical logic: continuity -/

/-- Decides, for `f : Nat → Bool`, whether `f` takes the value `true` below `n`; no axiom. -/
theorem decideExistsLt (f : Nat → Bool) :
    ∀ n : Nat, (∃ k, k < n ∧ f k = true) ∨ (∀ k, k < n → f k = false)
  | 0 => Or.inr fun _ hk => absurd hk (Nat.not_lt_zero _)
  | n + 1 =>
    match decideExistsLt f n with
    | Or.inl ⟨k, hk, hfk⟩ => Or.inl ⟨k, Nat.lt_succ_of_lt hk, hfk⟩
    | Or.inr hall =>
      match hfn : f n with
      | true => Or.inl ⟨n, Nat.lt_succ_self n, hfn⟩
      | false =>
        Or.inr fun k hk =>
          match Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with
          | Or.inl hlt => hall k hlt
          | Or.inr heq => heq ▸ hfn

/-- The easy direction of the continuity correspondence (finite image on the non-abortion
domain implies ω-continuity), restricted to `Unit`, implies the limited principle of
omniscience.  Proved without any axiom.  So that direction is not constructively provable:
`FiniteImage` gives a list containing every successor, without deciding which list members
are successors. -/
theorem lpo_of_finiteImage_imp_omegaContinuous_wp
    (h : ∀ (R : Rel Unit) (term : Pred Unit),
      (∀ s, term s → FiniteImage R s) → OmegaContinuous (wp R term)) :
    ∀ f : Nat → Bool, (∃ k, f k = true) ∨ (∀ k, f k = false) := by
  intro f
  let B : Nat → Pred Unit := fun n _ => ∃ k, k < n ∧ f k = true
  have hchain : Chain B := fun _ _ ⟨k, hk, hfk⟩ => ⟨k, Nat.lt_succ_of_lt hk, hfk⟩
  let R : Rel Unit := fun _ _ => ∃ n, B n ()
  let term : Pred Unit := fun _ => True
  have hfin : ∀ s : Unit, term s → FiniteImage R s :=
    fun _ _ => ⟨[()], fun _ _ => List.mem_cons_self⟩
  have hc := h R term hfin
  have hpre : wp R term (fun t => ∃ n, B n t) () := ⟨trivial, fun _ hp => hp⟩
  obtain ⟨n, _, hn⟩ := hc B hchain () hpre
  cases decideExistsLt f n with
  | inl hk =>
    obtain ⟨k, _, hfk⟩ := hk
    exact Or.inl ⟨k, hfk⟩
  | inr hno =>
    apply Or.inr
    intro k
    cases hfk : f k with
    | false => rfl
    | true =>
      obtain ⟨j, hj, hfj⟩ := hn () ⟨k + 1, k, Nat.lt_succ_self k, hfk⟩
      have hfalse := hno j hj
      rw [hfalse] at hfj
      cases hfj

/-! ## Continuity: canonical and non-degenerate witnesses -/

/-- Canonical form of the chain restriction in `OmegaContinuous`: for the two-way choice, every
non-abortion state has a finite image and the `wp` is ω-continuous, yet the same implication
for arbitrary `Nat`-indexed families fails. -/
theorem not_continuous_on_arbitrary_families_stepR_canonical :
    (∀ s : Nat, True → FiniteImage stepR s) ∧
      OmegaContinuous (wp stepR (fun _ => True)) ∧
      ¬ ∀ Q : Nat → Pred Nat, ∀ s,
          wp stepR (fun _ => True) (fun t => ∃ n, Q n t) s →
          ∃ n, wp stepR (fun _ => True) (Q n) s := by
  refine ⟨fun s _ => finiteImage_stepR s, omegaContinuous_wp_stepR_true, ?_⟩
  intro h
  apply not_continuous_on_arbitrary_families_stepR
  intro Q s hQ
  rw [wlp_eq_wp_true] at hQ ⊢
  exact h Q s hQ

/-- "At `0` anything may happen; elsewhere `skip`": the partial program used, with
non-abortion predicate `posP`, to show that the image outside the non-abortion domain is
unconstrained. -/
def zeroHavocR : Rel Nat := fun s s' => s = 0 ∨ s' = s

/-- With a non-degenerate non-abortion predicate: `wp zeroHavocR posP` is ω-continuous and has
a finite image at every non-abortion state, yet the image at the aborting state `0` is
infinite.  So finiteness is required only on the non-abortion domain. -/
theorem omegaContinuous_wp_partial_infinite_image_outside_term :
    OmegaContinuous (wp zeroHavocR posP) ∧ (∀ s, posP s → FiniteImage zeroHavocR s) ∧
      ¬ FiniteImage zeroHavocR 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro Q _ s h
    obtain ⟨hpos, hw⟩ := h
    obtain ⟨n, hn⟩ := hw s (Or.inr rfl)
    refine ⟨n, hpos, fun s' hr => ?_⟩
    rcases hr with h0 | heq
    · exact absurd h0 hpos
    · rw [heq]
      exact hn
  · intro s hs
    refine ⟨[s], fun s' hr => ?_⟩
    rcases hr with h0 | heq
    · exact absurd h0 hs
    · rw [heq]
      exact List.mem_cons_self
  · intro h
    obtain ⟨l, hl⟩ := h
    obtain ⟨b, hb⟩ := list_nat_bounded l
    have := hb b (hl b (Or.inl rfl))
    omega

/-- Non-vacuity of the continuity correspondence with a partial non-abortion predicate: both
sides hold for `(zeroHavocR, posP)` and both fail for `(havocR, posP)`. -/
theorem omegaContinuous_wp_partial_both_sides_occur :
    (OmegaContinuous (wp zeroHavocR posP) ∧ ∀ s, posP s → FiniteImage zeroHavocR s) ∧
      (¬ OmegaContinuous (wp (havocR : Rel Nat) posP) ∧
        ¬ ∀ s, posP s → FiniteImage (havocR : Rel Nat) s) := by
  refine ⟨⟨omegaContinuous_wp_partial_infinite_image_outside_term.1,
      omegaContinuous_wp_partial_infinite_image_outside_term.2.1⟩, ?_, ?_⟩
  · intro h
    have h1 : wp (havocR : Rel Nat) posP (fun t => ∃ n, t ≤ n) 1 :=
      ⟨by show (1 : Nat) ≠ 0; omega, fun s' _ => ⟨s', Nat.le_refl s'⟩⟩
    obtain ⟨n, _, hn⟩ := h (fun n s => s ≤ n) chain_le 1 h1
    have h2 : n + 1 ≤ n := hn (n + 1) trivial
    omega
  · intro h
    exact not_finiteImage_havocR_nat 1 (h 1 (by show (1 : Nat) ≠ 0; omega))

/-! ## Refinement: canonical and non-degenerate witnesses -/

/-- Canonical form of the chaos-normal-form hypothesis of the global-inclusion refinement
criterion: `abort`, presented with the empty relation, is not in chaos normal form; it is
refined by `havoc`; and the global criterion (termination inclusion together with global
reverse inclusion of relations) fails. -/
theorem refinedBy_wp_global_inclusion_needs_chaosNormal :
    ¬ ChaosNormal (emptyR : Rel Unit) (fun _ => False) ∧
      RefinedBy (wp (emptyR : Rel Unit) (fun _ => False)) (wp (havocR : Rel Unit) (fun _ => True)) ∧
      ¬ ((∀ s : Unit, (fun _ => False) s → (fun _ => True) s) ∧
          ∀ s s' : Unit, (havocR : Rel Unit) s s' → (emptyR : Rel Unit) s s') :=
  ⟨fun h => h () (fun hf => hf) (), fun _ _ h => False.elim h.1, fun h => h.2 () () trivial⟩

/-- Non-vacuity of the refinement correspondence with a partial non-abortion predicate: the
partial decrement is refined by the same relation with the everywhere-true non-abortion
predicate (both sides hold), and not conversely (both sides fail). -/
theorem refinedBy_wp_partial_both_sides_occur :
    (RefinedBy (wp predR posP) (wp predR (fun _ => True)) ∧
        ((∀ s, posP s → (fun _ => True) s) ∧ ∀ s, posP s → ∀ s', predR s s' → predR s s')) ∧
      (¬ RefinedBy (wp predR (fun _ => True)) (wp predR posP) ∧
        ¬ ((∀ s, (fun _ => True) s → posP s) ∧
            ∀ s, (fun _ => True) s → ∀ s', predR s s' → predR s s')) := by
  refine ⟨⟨fun _ _ h => ⟨trivial, h.2⟩, fun _ _ => trivial, fun _ _ _ h => h⟩, ?_, ?_⟩
  · intro h
    have h1 := h (fun _ => True) 0 ⟨trivial, fun _ _ => trivial⟩
    exact h1.1 rfl
  · intro h
    exact h.1 0 trivial rfl

/-- Non-vacuity of the global-inclusion form with a partial non-abortion predicate: the chaos
normal form of the partial decrement (chaotic at `0`) is refined by the decrement with the
everywhere-true non-abortion predicate, and the global criterion holds. -/
theorem refinedBy_wp_chaosNormal_partial_nonvacuous :
    ChaosNormal (fun s s' => posP s → predR s s') posP ∧
      RefinedBy (wp (fun s s' => posP s → predR s s') posP) (wp predR (fun _ => True)) ∧
      ((∀ s, posP s → (fun _ => True) s) ∧
        ∀ s s', predR s s' → (fun s s' => posP s → predR s s') s s') :=
  ⟨chaosNormal_chaos predR posP,
   fun _ _ h => ⟨trivial, fun s' hr => h.2 s' fun _ => hr⟩,
   fun _ _ => trivial, fun _ _ hr _ => hr⟩

/-! ## Countable and continuum state types: witnesses -/

/-- `Nat → Bool` is not countable, yet on it binary conjunctivity and ω-continuity already
force positive conjunctivity.  So countability of the state type is not necessary for that
implication. -/
theorem nat_to_bool_uncountable_conjBin_omegaContinuous_conjNonempty :
    ¬ CountableState (Nat → Bool) ∧
      ∀ T : Transformer (Nat → Bool), ConjBin T → OmegaContinuous T → ConjNonempty T :=
  ⟨not_countableState_nat_to_bool, fun _ hb hc =>
    conjNonempty_of_conjBin_of_omegaContinuous_of_continuumState continuumState_nat_to_bool hb hc⟩

/-- Non-vacuity on an uncountable state type: `Nat → Bool` injects into itself, and the `wp` of
`skip` on it is binary conjunctive and ω-continuous. -/
theorem continuum_conjBin_omegaContinuous_nonvacuous :
    ContinuumState (Nat → Bool) ∧ ¬ CountableState (Nat → Bool) ∧
      ConjBin (wp (skipR : Rel (Nat → Bool)) (fun _ => True)) ∧
      OmegaContinuous (wp (skipR : Rel (Nat → Bool)) (fun _ => True)) :=
  ⟨continuumState_nat_to_bool, not_countableState_nat_to_bool, conjBin_wp _ _,
    omegaContinuous_wp_skipR _⟩

/-- Binary conjunctivity cannot be dropped (or weakened to monotonicity) in the continuum
result: angelic havoc on `Bool` is monotone and ω-continuous but not positively
conjunctive. -/
theorem angelic_continuum_omegaContinuous_not_conjNonempty :
    ContinuumState Bool ∧ Monotone (angelic : Transformer Bool) ∧
      OmegaContinuous (angelic : Transformer Bool) ∧ ¬ ConjNonempty (angelic : Transformer Bool) :=
  ⟨continuumState_of_countableState countableState_bool, monotone_angelic, omegaContinuous_angelic,
    not_conjNonempty_angelic⟩

/-- ω-continuity cannot be dropped in the continuum result: `eventually` on `Nat` is binary
conjunctive but not positively conjunctive. -/
theorem eventually_continuum_conjBin_not_conjNonempty :
    ContinuumState Nat ∧ ConjBin eventually ∧ ¬ ConjNonempty eventually :=
  ⟨continuumState_nat, conjBin_eventually, not_conjNonempty_eventually⟩

/-! ## Directed continuity: witnesses -/

/-- Non-vacuity of the directed-continuity result on a state type to which the continuum result
does not apply: on `(Nat → Bool) → Bool`, which does not inject into `Nat → Bool`, the `wp` of
`skip` is binary conjunctive and continuous over directed families. -/
theorem conjBin_dirContinuous_nonvacuous_beyond_continuum :
    ¬ ContinuumState ((Nat → Bool) → Bool) ∧
      ConjBin (wp (skipR : Rel ((Nat → Bool) → Bool)) (fun _ => True)) ∧
      DirContinuous (wp (skipR : Rel ((Nat → Bool) → Bool)) (fun _ => True)) :=
  ⟨not_continuumState_pred_nat_to_bool, conjBin_wp _ _, dirContinuous_wp_skipR _⟩

/-- Binary conjunctivity cannot be dropped (or weakened to monotonicity) in the directed
result: angelic havoc on `Bool` is monotone and continuous over directed families but not
positively conjunctive. -/
theorem angelic_dirContinuous_monotone_not_conjNonempty :
    Monotone (angelic : Transformer Bool) ∧ DirContinuous (angelic : Transformer Bool) ∧
      ¬ ConjNonempty (angelic : Transformer Bool) :=
  ⟨monotone_angelic, dirContinuous_angelic, not_conjNonempty_angelic⟩

/-- Directed continuity cannot be dropped: `eventually` is binary conjunctive, not continuous
over directed families, and not positively conjunctive. -/
theorem eventually_conjBin_not_dirContinuous_not_conjNonempty :
    ConjBin eventually ∧ ¬ DirContinuous eventually ∧ ¬ ConjNonempty eventually :=
  ⟨conjBin_eventually, not_dirContinuous_eventually, not_conjNonempty_eventually⟩

end Toy.PredTrans
