import Toy.Sep.Examples

/-!
# Non-vacuity witnesses for the main results (all proved)

For each main result, a concrete instance satisfying all of its hypotheses. For
characterizations (`↔`), an instance where both sides hold and one where both
sides fail.
-/

namespace Toy.Sep

open SepStruct

/-- `{0 ↦ 1} assertAlloc 0 {0 ↦ 1}`. -/
theorem triple_assertAlloc :
    Triple (sing (Heap.pt 0 1)) (assertAlloc (V := Nat) 0) (sing (Heap.pt 0 1)) := by
  intro h hh
  have hh : h = Heap.pt 0 1 := hh
  subst hh
  refine ⟨(safe_assertAlloc_iff _ _).2 (by simp), ?_⟩
  rintro h' (⟨_, hf⟩ | ⟨_, he⟩)
  · cases hf
  · injection he

/-- Non-vacuity of `frame_rule_of_safetyMono_of_frameProp`: the command
`assertAlloc 0` (which can fault) is safety-monotone, has the frame property, and
satisfies the premise triple `{0 ↦ 1} assertAlloc 0 {0 ↦ 1}`. -/
theorem frame_rule_of_safetyMono_of_frameProp_nonvacuous :
    SafetyMono (assertAlloc (V := Nat) 0) ∧ FrameProp (assertAlloc (V := Nat) 0) ∧
    Triple (sing (Heap.pt 0 1)) (assertAlloc (V := Nat) 0) (sing (Heap.pt 0 1)) :=
  ⟨assertAlloc_safetyMono 0, assertAlloc_frameProp 0, triple_assertAlloc⟩

/-- Non-vacuity of `safetyMono_and_frameProp_of_frameRuleAtSingletons`: the
command `assertAlloc 0` satisfies the frame rule at all singleton instances
(proved directly). -/
theorem frameRuleAtSingletons_assertAlloc :
    FrameRuleAtSingletons (assertAlloc (V := Nat) 0) := by
  intro h h' ht x ⟨a, b, hd, hx, ha, hb⟩
  have ha : a = h := ha
  have hb : b = h' := hb
  subst ha; subst hb
  have hs : a.val 0 ≠ none := (safe_assertAlloc_iff 0 a).1 (ht a rfl).1
  have hsx : Safe (assertAlloc (V := Nat) 0) x :=
    hx ▸ assertAlloc_safetyMono 0 a b hd ((safe_assertAlloc_iff 0 a).2 hs)
  refine ⟨hsx, ?_⟩
  rintro x' (⟨_, hf⟩ | ⟨_, he⟩)
  · cases hf
  · injection he with he
    subst he
    exact ⟨a, b, hd, hx, Or.inr ⟨hs, rfl⟩, rfl⟩

/-- Non-vacuity of the characterization
`frameRuleSound_iff_safetyMono_and_frameProp`: both sides hold for `skip` and both
fail for `allocAt 0 1`. -/
theorem frameRuleSound_iff_nonvacuous :
    (FrameRuleSound (skip : Cmd (Heap Nat)) ∧
      (SafetyMono (skip : Cmd (Heap Nat)) ∧ FrameProp (skip : Cmd (Heap Nat)))) ∧
    (¬ FrameRuleSound (allocAt 0 (1 : Nat)) ∧
      ¬ (SafetyMono (allocAt 0 (1 : Nat)) ∧ FrameProp (allocAt 0 (1 : Nat)))) :=
  ⟨⟨skip_frameRuleSound, skip_safetyMono, skip_frameProp⟩,
    ⟨allocAt_not_frameRuleSound, allocAt_not_local⟩⟩

/-- Non-vacuity of `safetyMono_and_frameProp_of_frameRuleForPreciseFrames`. -/
theorem frameRuleForPreciseFrames_nonvacuous :
    FrameRuleForPreciseFrames (skip : Cmd (Heap Nat)) :=
  skip_frameRuleForPreciseFrames

/-- Non-vacuity of `conjDistrib_iff_uniqueFrame`: both sides hold for `forkR` in
`Fork`; both fail for `oneCell` in the heap model. -/
theorem conjDistrib_iff_uniqueFrame_nonvacuous :
    (ConjDistrib forkR ∧ UniqueFrame forkR) ∧
    (¬ ConjDistrib oneCell ∧ ¬ UniqueFrame oneCell) :=
  ⟨⟨forkR_conjDistrib, forkR_uniqueFrame⟩, ⟨oneCell_not_conjDistrib, oneCell_not_uniqueFrame⟩⟩

/-- Non-vacuity of `conjDistrib_of_precise_of_rightCancel`: the heap model is
right-cancellative and `0 ↦ -` is precise. -/
theorem conjDistrib_of_precise_of_rightCancel_nonvacuous :
    RightCancel (Heap Nat) ∧ Precise (ptAny 0) :=
  ⟨heap_rightCancel Nat, ptAny_precise 0⟩

/-- Non-vacuity of `precise_of_conjDistrib_of_leftCancel`: the heap model is
left-cancellative and `0 ↦ -` satisfies the distribution law (proved directly). -/
theorem precise_of_conjDistrib_of_leftCancel_nonvacuous :
    LeftCancel (Heap Nat) ∧ ConjDistrib (ptAny 0) :=
  ⟨heap_leftCancel Nat, ptAny_conjDistrib 0⟩

/-- Non-vacuity of `heap_precise_iff_conjDistrib`: both sides hold for `0 ↦ -`;
both fail for `oneCell`. -/
theorem heap_precise_iff_conjDistrib_nonvacuous :
    (Precise (ptAny 0) ∧ ConjDistrib (ptAny 0)) ∧
    (¬ Precise oneCell ∧ ¬ ConjDistrib oneCell) :=
  ⟨⟨ptAny_precise 0, ptAny_conjDistrib 0⟩, ⟨oneCell_not_precise, oneCell_not_conjDistrib⟩⟩

/-- Non-vacuity of the heap-command locality results: for each of the five
commands, an instance where the antecedents of both `SafetyMono` and `FrameProp`
hold with a non-empty frame (`disj h h'`, `Safe c h`) and the command has a normal
run from `h ∘ h'`. So neither property holds merely because the command is never
safe or never runs. -/
theorem heap_commands_framed_runs_nonvacuous :
    (let h := union (Heap.pt 0 5 : Heap Nat) (Heap.pt 1 0)
     let h' := Heap.pt 2 9
     disj h h' ∧ Safe (lookup 0 1) h ∧
       lookup 0 1 (union h h') (.ok ((union h h').set 1 (some 5)))) ∧
    (let h := (Heap.pt 0 1 : Heap Nat)
     let h' := Heap.pt 2 9
     disj h h' ∧ Safe (mutate 0 5) h ∧
       mutate 0 5 (union h h') (.ok ((union h h').set 0 (some 5)))) ∧
    (let h := (Heap.emp : Heap Nat)
     let h' := Heap.pt 2 9
     disj h h' ∧ Safe (alloc 1) h ∧
       alloc 1 (union h h') (.ok ((union h h').set 0 (some 1)))) ∧
    (let h := (Heap.pt 0 0 : Heap Nat)
     let h' := Heap.pt 2 9
     disj h h' ∧ Safe (allocInto 0 7) h ∧
       allocInto 0 7 (union h h') (.ok (((union h h').set 1 (some 7)).set 0 (some 1)))) ∧
    (let h := (Heap.pt 0 1 : Heap Nat)
     let h' := Heap.pt 2 9
     disj h h' ∧ Safe (free 0) h ∧
       free 0 (union h h') (.ok ((union h h').set 0 none))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, (safe_lookup_iff 0 1 _).2 ⟨by simp, by simp⟩, Or.inr ⟨by simp, by simp, rfl⟩⟩
    intro j; by_cases hj0 : j = 0 <;> by_cases hj1 : j = 1 <;> simp [hj0, hj1]
  · refine ⟨?_, (safe_mutate_iff 0 5 _).2 (by simp), Or.inr ⟨by simp, rfl⟩⟩
    intro j; by_cases hj : j = 0 <;> simp [hj]
  · exact ⟨fun _ => Or.inl rfl, safe_alloc 1 _, ⟨0, by simp, rfl⟩⟩
  · refine ⟨?_, (safe_allocInto_iff 0 7 _).2 (by simp), Or.inr ⟨by simp, 1, by simp, rfl⟩⟩
    intro j; by_cases hj : j = 0 <;> simp [hj]
  · refine ⟨?_, (safe_free_iff 0 _).2 (by simp), Or.inr ⟨by simp, rfl⟩⟩
    intro j; by_cases hj : j = 0 <;> simp [hj]

/-- Non-vacuity of the cancellation-law lemmas: the heap model satisfies all of
their hypotheses (and both conclusions) at once. -/
theorem cancel_coincide_nonvacuous :
    DisjSymm (Heap Nat) ∧ UnionComm (Heap Nat) ∧
    LeftCancel (Heap Nat) ∧ RightCancel (Heap Nat) :=
  ⟨heap_disjSymm Nat, heap_unionComm Nat, heap_leftCancel Nat, heap_rightCancel Nat⟩

/-- Non-vacuity of `fqTriple_frame_of_unionAssoc_of_unionAssocRev`: the heap model
has both associativity directions, and a frame-quantified triple holds for the
non-local command `allocLeast 1`. -/
theorem fqTriple_frame_nonvacuous :
    UnionAssoc (Heap Nat) ∧ UnionAssocRev (Heap Nat) ∧
    FQTriple (sing Heap.emp) (allocLeast (1 : Nat)) (fun h => ∃ k, h = Heap.pt k 1) :=
  ⟨heap_unionAssoc Nat, heap_unionAssocRev Nat, allocLeast_fqTriple_someCell⟩

/-- Non-vacuity of `triple_of_fqTriple_of_rightUnitLaw`: `emp` is a right unit of
the heap model, and a frame-quantified triple holds for `allocLeast 1`. -/
theorem triple_of_fqTriple_nonvacuous :
    RightUnitLaw (Heap.emp : Heap Nat) ∧
    FQTriple (sing Heap.emp) (allocLeast (1 : Nat)) (fun h => ∃ k, h = Heap.pt k 1) :=
  ⟨heap_rightUnitLaw Nat, allocLeast_fqTriple_someCell⟩

end Toy.Sep
