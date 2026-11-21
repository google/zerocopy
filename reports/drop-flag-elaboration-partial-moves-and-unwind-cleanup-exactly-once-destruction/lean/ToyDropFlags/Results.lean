import ToyDropFlags.Counterexamples
import ToyDropFlags.AnalysisFacts
import ToyDropFlags.Necessity
import ToyDropFlags.Sufficiency

/-!
# Main results (statements)

All results are fully proved. The sufficiency and continue-unwinding theorems rest on the
invariant-based simulation of `ToyDropFlags.Sufficiency` (`runElab_good`); the necessity
theorems rest on `ToyDropFlags.Necessity`. Every counterexample, non-vacuity witness and positive
control they refer to is fully proved in `ToyDropFlags.Counterexamples` and
`ToyDropFlags.Examples`.

Vocabulary. *Exactly-once* (`ExactlyOnce`) is a property of one run. *Elaboration-correct*
(`ElabCorrect`) is a property of an elaborated program: every run terminates and is exactly-once.
-/

namespace Toy.DropFlags

/-- **Sufficiency of compatible decisions (abort rule).** Assume the program is forward, its
places are move paths, it moves only definitely-initialized places (call arguments pairwise
disjoint), it initializes only definitely-uninitialized places, and no `resume` node is
reachable along normal edges only. Then, with the standard flag maintenance and the abort rule
for destructor panics during unwinding, every decision map that is compatible with the fine
analyses at every forward-reachable drop point is elaboration-correct. -/
theorem elabCorrect_of_allCompatible_of_forward_moveChecked_noNormalPathToResume (s : SProg)
    (hfwd : Forward s) (hplaces : PlacesAreMovePaths s) (hmoves : MovesFromInit s)
    (hinits : InitsIntoUninit s) (hclean : NoNormalPathToResume s)
    (d : Nat → Place → Decision) (hcompat : AllCompatible s d) :
    ElabCorrect .abort .std d s := by
  intro inp
  obtain ⟨hndd, hterm, hleak⟩ := runElab_good .abort d s hfwd hplaces hmoves hcompat inp
  exact ⟨⟨hndd, hleak rfl hinits hclean⟩, hterm⟩

/-- **Exactly-once for the standard elaboration (abort rule).** Assume the program is forward,
its places are move paths, it moves only definitely-initialized places (call arguments pairwise
disjoint), it initializes only definitely-uninitialized places, and no `resume` node is
reachable along normal edges only; and assume that a destructor panic during unwinding aborts.
Then the standard elaboration — flags set at every `init`, cleared at every `move` and, for call
arguments, before the call, set for a call's destination on its normal edge; an unconditional
drop where must-init, nothing where not may-init, a flag test elsewhere; cleanup drops without
landing pads — terminates on every input, never destroys a value twice, never destroys an
uncreated value or runs a destructor on unwritten memory, and on every run that returns or
completes an unwind destroys every created value. (Follows from the sufficiency theorem, since
the standard decisions are always compatible.) -/
theorem stdElab_correct_of_forward_moveChecked_noNormalPathToResume (s : SProg)
    (hfwd : Forward s) (hplaces : PlacesAreMovePaths s) (hmoves : MovesFromInit s)
    (hinits : InitsIntoUninit s) (hclean : NoNormalPathToResume s) :
    ElabCorrect .abort .std (stdMap s .fine) s :=
  elabCorrect_of_allCompatible_of_forward_moveChecked_noNormalPathToResume s hfwd hplaces hmoves
    hinits hclean _ (fun _ _ _ _ _ _ => stdDecision_compatible _ _)

/-- **Necessity of compatible decisions.** Assume only that the program's places are move paths.
If every run of the elaboration of a decision map `d` (standard flag maintenance, abort rule) is
exactly-once, then `d` is compatible with the fine analyses at every forward-reachable drop
point: it drops unconditionally only must-init atoms and does nothing only for atoms that are
not may-init. Forwardness, the other move-checker conditions, `NoNormalPathToResume` and
termination are not assumed. -/
theorem allCompatible_of_exactlyOnce_of_placesAreMovePaths (s : SProg)
    (hplaces : PlacesAreMovePaths s) (d : Nat → Place → Decision)
    (hd : ∀ inp, ExactlyOnce (runElab .abort .std d s inp)) :
    AllCompatible s d := by
  intro i _ hdp hreach a ha
  cases hdi : d i a with
  | test => rfl
  | drop =>
    cases hm : mustInit s .fine i a with
    | true => rfl
    | false =>
      obtain ⟨inp, hinp⟩ := drop_fails_of_not_mustInit d s hplaces i hdp hreach a ha hm hdi
      exact absurd (hd inp).1 hinp
  | skip =>
    cases hm : mayInit s .fine i a with
    | false => rfl
    | true =>
      obtain ⟨inp, hc, hnl⟩ := skip_fails_of_mayInit d s hplaces i hdp a hm hdi
      exact absurd ((hd inp).2 hc) hnl

/-- **Characterization of correct drop decisions.** Under the hypotheses of the exactly-once
theorem and with the standard flag maintenance and the abort rule, a decision map is
elaboration-correct if and only if, at every forward-reachable drop point and for every atom,
its decision is compatible with the fine analyses: a flag test always is, an unconditional drop
only where the atom is must-init, and nothing only where it is not may-init. By
`staticChoice_compatible_iff`, some static choice (unconditional drop or nothing) is compatible
for an atom exactly when the atom is not both may-init and not must-init there; so a flag test
is required precisely at the forward-reachable drop points where it is may-init but not
must-init. -/
theorem elabCorrect_iff_allCompatible_of_forward_moveChecked_noNormalPathToResume (s : SProg)
    (hfwd : Forward s) (hplaces : PlacesAreMovePaths s) (hmoves : MovesFromInit s)
    (hinits : InitsIntoUninit s) (hclean : NoNormalPathToResume s)
    (d : Nat → Place → Decision) :
    ElabCorrect .abort .std d s ↔ AllCompatible s d :=
  ⟨fun h => allCompatible_of_exactlyOnce_of_placesAreMovePaths s hplaces d (fun inp => (h inp).1),
   elabCorrect_of_allCompatible_of_forward_moveChecked_noNormalPathToResume s hfwd hplaces hmoves
     hinits hclean d⟩

/-- **A static choice where the analyses disagree fails.** Assume only that the program's places
are move paths. If at a drop point an atom is may-init but not must-init, then replacing the
flag test of the standard elaboration there by an unconditional drop yields a run with a double
destruction (or a destructor on unwritten memory), and replacing it by nothing yields a run that
returns or completes an unwind and leaks. Forwardness, the other move-checker conditions and
`NoNormalPathToResume` are not assumed. (`i < s.nodes.length` follows from `hdrop` by
`lt_of_isDropPoint`; forward reachability of `i` and `a ∈ allAtoms s.locals` follow from `hmay` by
`forwardReachable_and_mem_allAtoms_of_mayInit`.) -/
theorem staticChoice_at_disagreement_fails_of_placesAreMovePaths (s : SProg)
    (hplaces : PlacesAreMovePaths s) (i : Nat) (hdrop : isDropPoint s i = true) (a : Place)
    (hmay : mayInit s .fine i a = true) (hmust : mustInit s .fine i a = false) :
    (∃ inp, ¬ NoDoubleDrop
        (runElab .abort .std (overrideAt (stdMap s .fine) i a .drop) s inp).log) ∧
    (∃ inp,
        (runElab .abort .std (overrideAt (stdMap s .fine) i a .skip) s inp).outcome.complete = true ∧
        ¬ NoLeak (runElab .abort .std (overrideAt (stdMap s .fine) i a .skip) s inp).log) := by
  have hreach := (forwardReachable_and_mem_allAtoms_of_mayInit s i a hmay).1
  have ha := (forwardReachable_and_mem_allAtoms_of_mayInit s i a hmay).2
  exact ⟨drop_fails_of_not_mustInit _ s hplaces i hdrop hreach a ha hmust (by simp [overrideAt]),
    skip_fails_of_mayInit _ s hplaces i hdrop a hmay (by simp [overrideAt])⟩

/-- **Under the continue-unwinding rule, still no double drop.** Assume the program is forward,
its places are move paths, and it moves only definitely-initialized places; and assume that a
destructor panic during unwinding continues unwinding (here: leaves the frame, since cleanup
drops have no landing pad). Then on every input the standard elaboration terminates, never
destroys a value twice, never destroys an uncreated value and never runs a destructor on
unwritten memory. `InitsIntoUninit` and `NoNormalPathToResume` are not assumed. -/
theorem stdElab_noDoubleDrop_continueUnwind_of_forward_placesAreMovePaths_movesFromInit
    (s : SProg)
    (hfwd : Forward s) (hplaces : PlacesAreMovePaths s) (hmoves : MovesFromInit s) :
    ∀ inp,
      NoDoubleDrop (runElab .continueUnwind .std (stdMap s .fine) s inp).log ∧
      (runElab .continueUnwind .std (stdMap s .fine) s inp).outcome.terminated = true := by
  intro inp
  obtain ⟨hndd, hterm, _⟩ := runElab_good .continueUnwind (stdMap s .fine) s hfwd hplaces hmoves
    (fun _ _ _ _ _ _ => stdDecision_compatible _ _) inp
  exact ⟨hndd, hterm⟩

/-- **Under the continue-unwinding rule, a completed unwind can leak (impossibility).** If a
destructor panic during unwinding continues unwinding instead of aborting, then there is a
program satisfying every hypothesis of the exactly-once theorem and an input on which the run
of its standard elaboration completes an unwind, destroys no value twice, and leaks a created
value. Witness: `progUnwind` (a two-field struct live across a call) with input `[true, true]`
(`continueUnwind_leaks_partially_dropped`). -/
theorem continueUnwind_completedUnwind_leaks_of_forward_moveChecked :
    ∃ (s : SProg) (inp : List Bool),
      Forward s ∧ PlacesAreMovePaths s ∧ MovesFromInit s ∧ InitsIntoUninit s ∧
      NoNormalPathToResume s ∧
      (runElab .continueUnwind .std (stdMap s .fine) s inp).outcome = .unwound ∧
      NoDoubleDrop (runElab .continueUnwind .std (stdMap s .fine) s inp).log ∧
      ¬ NoLeak (runElab .continueUnwind .std (stdMap s .fine) s inp).log :=
  have h := continueUnwind_leaks_partially_dropped
  ⟨progUnwind, [true, true], h.1, h.2.1.1, h.2.1.2.1, h.2.1.2.2, h.2.2.1, h.2.2.2.1,
    h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

/-- Corollary of the previous theorem: under the continue-unwinding rule, the standard
elaboration is not elaboration-correct for every program satisfying the hypotheses of the
exactly-once theorem. -/
theorem continueUnwind_not_elabCorrect_for_all_forward_moveChecked :
    ¬ ∀ s : SProg, Forward s → PlacesAreMovePaths s → MovesFromInit s → InitsIntoUninit s →
        NoNormalPathToResume s → ElabCorrect .continueUnwind .std (stdMap s .fine) s := by
  intro h
  obtain ⟨s, inp, hf, hp, hm, hi, hc, hout, _, hleak⟩ :=
    continueUnwind_completedUnwind_leaks_of_forward_moveChecked
  exact hleak ((h s hf hp hm hi hc inp).1.2 (by rw [hout]; rfl))

/-- **The standard flag set is a lower bound.** Assume only that the program's places are move
paths. If every run of the elaboration of a decision map `d` (same CFG, one flag per atom,
standard flag maintenance, abort rule) is exactly-once, then `d` tests, at some
forward-reachable drop point, every atom that the standard map tests at some forward-reachable
drop point. This does not say the standard map is itself elaboration-correct (see
`stdMap_correct_and_flagSet_least_of_forward_moveChecked_noNormalPathToResume`). -/
theorem stdFlagSet_subset_of_exactlyOnce_of_placesAreMovePaths (s : SProg)
    (hplaces : PlacesAreMovePaths s) (d : Nat → Place → Decision)
    (hd : ∀ inp, ExactlyOnce (runElab .abort .std d s inp)) :
    ∀ a ∈ flagSet s (stdMap s .fine), a ∈ flagSet s d := by
  have hc := allCompatible_of_exactlyOnce_of_placesAreMovePaths s hplaces d hd
  intro a ha
  unfold flagSet at ha ⊢
  rw [List.mem_filter] at ha ⊢
  obtain ⟨haA, hany⟩ := ha
  refine ⟨haA, ?_⟩
  rw [List.any_eq_true] at hany ⊢
  obtain ⟨i, hi, hcond⟩ := hany
  refine ⟨i, hi, ?_⟩
  simp only [Bool.and_eq_true, beq_iff_eq] at hcond ⊢
  obtain ⟨⟨hdp, hreach⟩, htest⟩ := hcond
  refine ⟨⟨hdp, hreach⟩, ?_⟩
  have hcompat := hc i (List.mem_range.1 hi) hdp hreach a haA
  have hmm : mayInit s .fine i a = true ∧ mustInit s .fine i a = false := by
    unfold stdMap stdDecision at htest
    cases hm : mayInit s .fine i a <;> cases hn : mustInit s .fine i a <;> simp_all
  rw [hmm.1, hmm.2] at hcompat
  cases hdia : d i a <;> simp_all [Compatible]

/-- **Under the exactly-once hypotheses the standard flag set is least.** Under the hypotheses of
the exactly-once theorem (abort rule, standard flag maintenance), the standard decision map is
elaboration-correct, and every elaboration-correct decision map tests every atom the standard
map tests: the standard flag set is the least flag set among elaboration-correct decision maps
(same CFG, one flag per atom). (Its first conjunct is the exactly-once theorem.) -/
theorem stdMap_correct_and_flagSet_least_of_forward_moveChecked_noNormalPathToResume (s : SProg)
    (hfwd : Forward s) (hplaces : PlacesAreMovePaths s) (hmoves : MovesFromInit s)
    (hinits : InitsIntoUninit s) (hclean : NoNormalPathToResume s) :
    ElabCorrect .abort .std (stdMap s .fine) s ∧
    ∀ d : Nat → Place → Decision, ElabCorrect .abort .std d s →
      ∀ a ∈ flagSet s (stdMap s .fine), a ∈ flagSet s d :=
  ⟨stdElab_correct_of_forward_moveChecked_noNormalPathToResume s hfwd hplaces hmoves hinits hclean,
   fun d hd => stdFlagSet_subset_of_exactlyOnce_of_placesAreMovePaths s hplaces d
     (fun inp => (hd inp).1)⟩

/-- **Fewer flags than the standard map is not exactly-once (impossibility).** Assume only that
the program's places are move paths. A decision map that tests strictly fewer atoms (at
forward-reachable drop points) than the standard map has an input on which the run of its
elaboration (same CFG, one flag per atom, standard flag maintenance, abort rule) is not
exactly-once. See the positive controls `dupProg_matches_stdElab_progJoin`,
`shareProg_matches_stdElab_progShare` and `earlyDropProg_matches_stdElab_progJoin` for
elaborations outside this class. -/
theorem fewerFlags_than_std_not_exactlyOnce_of_placesAreMovePaths (s : SProg)
    (hplaces : PlacesAreMovePaths s) (d : Nat → Place → Decision)
    (hlt : (flagSet s d).length < (flagSet s (stdMap s .fine)).length) :
    ∃ inp, ¬ ExactlyOnce (runElab .abort .std d s inp) := by
  apply Classical.byContradiction
  intro hne
  have hall : ∀ inp, ExactlyOnce (runElab .abort .std d s inp) := fun inp =>
    Classical.byContradiction fun h => hne ⟨inp, h⟩
  have hle := filter_length_le_of_subset (allAtoms s.locals) _ _
    (stdFlagSet_subset_of_exactlyOnce_of_placesAreMovePaths s hplaces d hall)
  unfold flagSet at hlt
  omega

end Toy.DropFlags
