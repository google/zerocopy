import ToySymEx.Examples
import ToySymEx.Statements

/-!
Tightness counterexamples (canonical form: every other hypothesis holds and the
conclusion fails), non-vacuity witnesses (every hypothesis holds), and positive
controls. Every proof in this file is self-contained: none uses a theorem from
`ToySymEx.Statements`.
-/

namespace Toy.SymEx

open Term

/-! ## Helpers -/

/-- Postcondition `True`. -/
def Qtrue : Store → Prop := fun _ => True

/-- Postcondition `x1 = x0 + 1`. -/
def Qplus1 : Store → Prop := fun st => st 1 = .int ((st 0).toInt + 1)

theorem not_leavesProve_of_bad_leaf (L : List Leaf) (Q : Store → Prop) (l : Leaf) (hl : l ∈ L)
    (htag : l.res.tag ≠ 0) (ρ : Valuation) (hρ : holds l.pc ρ) : ¬ LeavesProve L Q := by
  intro h
  have := h l hl ρ hρ
  cases hr : l.res <;> simp_all [SymOutcome.tag, SymOutcome.inst, OkWith]

theorem not_leavesProveLax_of_panic_leaf (L : List Leaf) (Q : Store → Prop) (l : Leaf)
    (hl : l ∈ L) (htag : l.res.tag = 1) (ρ : Valuation) (hρ : holds l.pc ρ) :
    ¬ LeavesProveLax L Q := by
  intro h
  have := h l hl ρ hρ
  cases hr : l.res <;> simp_all [SymOutcome.tag, SymOutcome.inst, OkWithOrOutOfFuel]

theorem leavesProveLax_of_leavesProve (L : List Leaf) (Q : Store → Prop)
    (h : LeavesProve L Q) : LeavesProveLax L Q := by
  intro l hl ρ hρ
  have := h l hl ρ hρ
  revert this
  cases l.res.inst ρ <;> simp [OkWith, OkWithOrOutOfFuel]

theorem leavesSound_exPanicIfZero : LeavesSound exPanicIfZero 2 (symExec exPanicIfZero 2) := by
  intro l hl ρ hρ
  rw [symExec_exPanicIfZero] at hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rw [exec_exPanicIfZero]
  rcases hl with rfl | rfl
  · simp only [(holds_pzPanicPc ρ).1 hρ, ↓reduceIte]; rfl
  · simp only [(holds_pzOkPc ρ).1 hρ, ↓reduceIte]; rfl

theorem leavesExhaustive_exPanicIfZero : LeavesExhaustive (symExec exPanicIfZero 2) := by
  intro ρ
  rw [symExec_exPanicIfZero]
  by_cases h : ρ 0 = .int 0
  · exact ⟨_, List.mem_cons_self .., (holds_pzPanicPc ρ).2 h⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), (holds_pzOkPc ρ).2 h⟩

theorem exPanicIfZero_panics_at_ρ0 :
    exec exPanicIfZero 2 (SymStore.init.inst ρ0) = .panic ⟨0, 0⟩ := rfl

theorem symExec_exDiamond_6 : symExec exDiamond 6 = symExec exDiamond 4 := rfl

/-! ## `eval_subst` -/

theorem nonvacuity_eval_subst :
    ((add (var 1) (var 1)).subst dσ₁).eval ρ5 = (add (var 1) (var 1)).eval (dσ₁.inst ρ5) := by
  decide

/-! ## `symExec_leaf_sound` -/

/-- All hypotheses of `symExec_leaf_sound` hold for the `x0 = 0` leaf of
`exDiamond` at `ρ0`. -/
theorem nonvacuity_symExec_leaf_sound :
    (⟨dc₁, .ok dσ₁⟩ : Leaf) ∈ symExec exDiamond 4 ∧ holds dc₁ ρ0 :=
  ⟨by rw [symExec_exDiamond]; exact List.mem_cons_self .., by decide⟩

/-- Tightness of `hl`: a leaf that `symExec` does not produce (`(true, ok init)`)
satisfies `hpc` at `ρ0`, yet the concrete run panics. -/
theorem symExec_leaf_sound_needs_membership :
    holds Term.tt ρ0 ∧
      exec exPanicIfZero 2 (SymStore.init.inst ρ0) ≠ SymOutcome.inst (.ok SymStore.init) ρ0 := by
  refine ⟨rfl, ?_⟩
  intro h
  have := congrArg Outcome.tag h
  revert this; decide

/-- Tightness of `hpc`: the success leaf of `exPanicIfZero` is produced by
`symExec`, its path condition fails at `ρ0`, and there the concrete run panics
while the leaf records success (a spurious success if the path condition is
ignored). -/
theorem symExec_leaf_sound_needs_pc :
    (⟨pzOkPc, .ok SymStore.init⟩ : Leaf) ∈ symExec exPanicIfZero 2 ∧ ¬ holds pzOkPc ρ0 ∧
      exec exPanicIfZero 2 (SymStore.init.inst ρ0) ≠ SymOutcome.inst (.ok SymStore.init) ρ0 := by
  refine ⟨by rw [symExec_exPanicIfZero]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..),
    by decide, ?_⟩
  intro h
  have := congrArg Outcome.tag h
  revert this; decide

/-! ## Path coverage -/

/-- Instance: the two `exDiamond` leaves cover every input and are disjoint. -/
theorem nonvacuity_path_coverage :
    (∀ ρ, ∃ l ∈ symExec exDiamond 4, holds l.pc ρ) ∧
      (symExec exDiamond 4).Pairwise (fun l₁ l₂ => Disjoint l₁.pc l₂.pc) ∧
      (symExec exDiamond 4).length = 2 := by
  refine ⟨leavesExhaustive_exDiamond, ?_, rfl⟩
  rw [symExec_exDiamond]
  refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ List.Pairwise.nil)
  · intro a ha
    rw [List.mem_singleton] at ha
    subst ha
    exact disjoint_dc₁_dc₂
  · intro a ha
    simp at ha

/-! ## Transfer from leaf checks to concrete runs -/

theorem nonvacuity_transfer :
    LeavesSound exDiamond 4 (symExec exDiamond 4) ∧ LeavesExhaustive (symExec exDiamond 4) ∧
      LeavesProve (symExec exDiamond 4) QneDiamond ∧
      LeavesProveLax (symExec exDiamond 4) QneDiamond :=
  ⟨leavesSound_exDiamond, leavesExhaustive_exDiamond, provesStrict_exDiamond,
    leavesProveLax_of_leavesProve _ _ provesStrict_exDiamond⟩

/-- Tightness of `hsound`: `[(true, ok init)]` is exhaustive and passes both
checks for `True`, but `exPanicIfZero` panics at `ρ0`. -/
theorem transfer_needs_leavesSound :
    LeavesExhaustive [⟨tt, .ok SymStore.init⟩] ∧
      LeavesProve [⟨tt, .ok SymStore.init⟩] Qtrue ∧
      LeavesProveLax [⟨tt, .ok SymStore.init⟩] Qtrue ∧
      ¬ OkWith Qtrue (exec exPanicIfZero 2 (SymStore.init.inst ρ0)) ∧
      ¬ OkWithOrOutOfFuel Qtrue (exec exPanicIfZero 2 (SymStore.init.inst ρ0)) := by
  refine ⟨fun _ => ⟨_, List.mem_singleton_self _, rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro l hl ρ _; rw [List.mem_singleton] at hl; subst hl; exact trivial
  · intro l hl ρ _; rw [List.mem_singleton] at hl; subst hl; exact trivial
  · rw [exPanicIfZero_panics_at_ρ0]; exact id
  · rw [exPanicIfZero_panics_at_ρ0]; exact id

/-- Tightness of `hexh`: keeping only the success leaf of `exPanicIfZero` (whose
path condition is not valid) gives a sound list that passes both checks, but the
program panics at `ρ0`. -/
theorem transfer_needs_exhaustive :
    LeavesSound exPanicIfZero 2 [⟨pzOkPc, .ok SymStore.init⟩] ∧
      LeavesProve [⟨pzOkPc, .ok SymStore.init⟩] Qtrue ∧
      LeavesProveLax [⟨pzOkPc, .ok SymStore.init⟩] Qtrue ∧
      ¬ OkWith Qtrue (exec exPanicIfZero 2 (SymStore.init.inst ρ0)) ∧
      ¬ OkWithOrOutOfFuel Qtrue (exec exPanicIfZero 2 (SymStore.init.inst ρ0)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro l hl
    apply leavesSound_exPanicIfZero l
    rw [List.mem_singleton] at hl; subst hl
    rw [symExec_exPanicIfZero]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  · intro l hl ρ _; rw [List.mem_singleton] at hl; subst hl; exact trivial
  · intro l hl ρ _; rw [List.mem_singleton] at hl; subst hl; exact trivial
  · rw [exPanicIfZero_panics_at_ρ0]; exact id
  · rw [exPanicIfZero_panics_at_ρ0]; exact id

/-- Tightness of `hprove`: the leaves of `exPanicIfZero` are sound and
exhaustive, the check fails, and so does the conclusion. -/
theorem transfer_needs_leaf_check :
    LeavesSound exPanicIfZero 2 (symExec exPanicIfZero 2) ∧
      LeavesExhaustive (symExec exPanicIfZero 2) ∧
      ¬ OkWith Qtrue (exec exPanicIfZero 2 (SymStore.init.inst ρ0)) ∧
      ¬ OkWithOrOutOfFuel Qtrue (exec exPanicIfZero 2 (SymStore.init.inst ρ0)) := by
  refine ⟨leavesSound_exPanicIfZero, leavesExhaustive_exPanicIfZero, ?_, ?_⟩
  · rw [exPanicIfZero_panics_at_ρ0]; exact id
  · rw [exPanicIfZero_panics_at_ρ0]; exact id

/-! ## `provesLax_iff_forall_exec_okWithOrOutOfFuel` -/

/-- Postcondition `x1 = 1`. -/
def Qx1eq1 : Store → Prop := fun st => st 1 = .int 1

/-- Both sides of the lax characterization hold non-trivially for `exHalfDone` at
fuel 3 with the satisfiable postcondition `x1 = 1`: the lax check passes, the
strict check fails, the input `x0 = 0` returns with `x1 = 1`, and the input
`x0 = 5` runs out of fuel. -/
theorem nonvacuity_provesLax_iff :
    ProvesLax exHalfDone 3 Qx1eq1 ∧
      (∀ ρ, OkWithOrOutOfFuel Qx1eq1 (exec exHalfDone 3 (SymStore.init.inst ρ))) ∧
      ¬ ProvesStrict exHalfDone 3 Qx1eq1 ∧
      OkWith Qx1eq1 (exec exHalfDone 3 (SymStore.init.inst ρ0)) ∧
      exec exHalfDone 3 (SymStore.init.inst ρ5) = .outOfFuel := by
  refine ⟨?_, ?_, ?_, rfl, rfl⟩
  · intro l hl ρ _
    simp [symExec, exHalfDone, symBlock, forkSwitch] at hl
    rcases hl with rfl | rfl
    · simp [SymOutcome.inst, OkWithOrOutOfFuel, Qx1eq1, SymStore.inst, SymStore.set, Term.subst,
        Term.int, Term.eval]
    · exact trivial
  · intro ρ
    by_cases h : ρ 0 = .int 0
    · simp [exec, exHalfDone, runBlock, select, SymStore.inst, SymStore.init, h, Term.eval,
        Term.int, OkWithOrOutOfFuel, Qx1eq1, Store.set]
    · simp [exec, exHalfDone, runBlock, select, SymStore.inst, SymStore.init, h, Term.eval,
        Term.int, OkWithOrOutOfFuel]
  · have hbad : ∃ l ∈ symExec exHalfDone 3, l.res.tag = 2 ∧ holds l.pc ρ5 := by decide
    obtain ⟨l, hl, ht, hρ⟩ := hbad
    exact not_leavesProve_of_bad_leaf _ _ l hl (by omega) ρ5 hρ

/-! ## Dropping path conditions -/

theorem nonvacuity_leavesProve_dropPcs : LeavesProve (dropPcs (symExec exDiamond 4)) QneDiamond := by
  intro l hl ρ _
  rw [symExec_exDiamond] at hl
  simp only [dropPcs, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hl
  rcases hl with rfl | rfl <;>
  · simp only [SymOutcome.inst, OkWith, QneDiamond]
    cases h0 : ρ 0 <;>
      simp [dσ₁, dσ₂, SymStore.inst, SymStore.set, SymStore.init, Term.eval, Term.int, Val.toInt, h0] <;>
      omega

/-- Tightness of `h`: neither the dropped nor the original check passes for
`exPanicIfZero`. -/
theorem leavesProve_dropPcs_needed :
    ¬ LeavesProve (dropPcs (symExec exPanicIfZero 2)) Qtrue ∧
      ¬ LeavesProve (symExec exPanicIfZero 2) Qtrue := by
  refine ⟨?_, not_provesStrict_exPanicIfZero⟩
  have : ∃ l ∈ dropPcs (symExec exPanicIfZero 2), l.res.tag = 1 ∧ holds l.pc ρ0 := by decide
  obtain ⟨l, hl, ht, hρ⟩ := this
  exact not_leavesProve_of_bad_leaf _ _ l hl (by omega) ρ0 hρ

/-- The converse fails (dropping path conditions causes false alarms):
`exAssertTrue` passes the strict check, but not after dropping path conditions,
because its infeasible panic leaf becomes feasible. -/
theorem dropPcs_false_alarm :
    LeavesProve (symExec exAssertTrue 2) Qtrue ∧
      ¬ LeavesProve (dropPcs (symExec exAssertTrue 2)) Qtrue := by
  constructor
  · intro l hl ρ hρ
    simp only [symExec, exAssertTrue, symBlock, List.getElem?_cons_zero, List.mem_cons,
      List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · simp [holds, Term.and, Term.not, Term.tt, Term.ff, Term.eval, Term.subst, Val.toBool] at hρ
    · exact trivial
  · have : ∃ l ∈ dropPcs (symExec exAssertTrue 2), l.res.tag = 1 ∧ holds l.pc ρ0 := by decide
    obtain ⟨l, hl, ht, hρ⟩ := this
    exact not_leavesProve_of_bad_leaf _ _ l hl (by omega) ρ0 hρ

/-! ## Guarded merge -/

theorem guardedSound_merge_dia :
    GuardedSound Rdia Outcome.ok (Term.or dc₁ dc₂) (mergeStore dc₁ dσ₁ dσ₂) := by
  intro ρ _
  by_cases h1 : holds dc₁ ρ
  · rw [mergeStore_inst_of_holds _ _ _ _ h1]; exact guardedSound_dc₁_dσ₁ ρ h1
  · rw [mergeStore_inst_of_not_holds _ _ _ _ h1]
    exact guardedSound_dc₂_dσ₂ ρ ((holds_dc₂ ρ).2 (fun h => h1 ((holds_dc₁ ρ).2 h)))

/-- Both hypotheses hold for the two branch states of `exDiamond` (disjoint
guards) and also for an overlapping pair: the first branch state and the merged
state, whose guards `dc₁` and `dc₁ ∨ dc₂` overlap. -/
theorem nonvacuity_guardedMerge_sound :
    (GuardedSound Rdia Outcome.ok dc₁ dσ₁ ∧ GuardedSound Rdia Outcome.ok dc₂ dσ₂) ∧
      (GuardedSound Rdia Outcome.ok dc₁ dσ₁ ∧
        GuardedSound Rdia Outcome.ok (Term.or dc₁ dc₂) (mergeStore dc₁ dσ₁ dσ₂) ∧
        ¬ Disjoint dc₁ (Term.or dc₁ dc₂)) :=
  ⟨⟨guardedSound_dc₁_dσ₁, guardedSound_dc₂_dσ₂⟩,
    ⟨guardedSound_dc₁_dσ₁, guardedSound_merge_dia, fun h => h ρ0 ⟨by decide, by decide⟩⟩⟩

/-- Overlap is harmless: `dc₁` overlaps `dc₁ ∨ dc₂`, both guarded states are
sound for `exDiamond`, and so is their guarded merge. -/
theorem guardedMerge_sound_overlapping_instance :
    ¬ Disjoint dc₁ (Term.or dc₁ dc₂) ∧
      GuardedSound Rdia Outcome.ok dc₁ dσ₁ ∧
      GuardedSound Rdia Outcome.ok (Term.or dc₁ dc₂) (mergeStore dc₁ dσ₁ dσ₂) ∧
      GuardedSound Rdia Outcome.ok (Term.or dc₁ (Term.or dc₁ dc₂))
        (mergeStore dc₁ dσ₁ (mergeStore dc₁ dσ₁ dσ₂)) := by
  refine ⟨fun h => h ρ0 ⟨by decide, by decide⟩, guardedSound_dc₁_dσ₁, guardedSound_merge_dia, ?_⟩
  intro ρ hρ
  by_cases h1 : holds dc₁ ρ
  · rw [mergeStore_inst_of_holds _ _ _ _ h1]; exact guardedSound_dc₁_dσ₁ ρ h1
  · rw [mergeStore_inst_of_not_holds _ _ _ _ h1]
    exact guardedSound_merge_dia ρ (((holds_or _ _ ρ).1 hρ).resolve_left h1)

/-- Tightness of `h₁`: with an unsound first state the merge is unsound. -/
theorem guardedMerge_needs_first_sound :
    GuardedSound Rdia Outcome.ok dc₂ dσ₂ ∧
      ¬ GuardedSound Rdia Outcome.ok (Term.or dc₁ dc₂) (mergeStore dc₁ dσ₂ dσ₂) := by
  refine ⟨guardedSound_dc₂_dσ₂, fun h => ?_⟩
  have := congrArg (Outcome.get? 1) (h ρ0 (by decide))
  revert this; decide

/-- Tightness of `h₂`: with an unsound second state the merge is unsound. -/
theorem guardedMerge_needs_second_sound :
    GuardedSound Rdia Outcome.ok dc₁ dσ₁ ∧
      ¬ GuardedSound Rdia Outcome.ok (Term.or dc₁ dc₂) (mergeStore dc₁ dσ₁ dσ₁) := by
  refine ⟨guardedSound_dc₁_dσ₁, fun h => ?_⟩
  have := congrArg (Outcome.get? 1) (h ρ5 (by decide))
  revert this; decide

/-! ## Merging leaves -/

theorem nonvacuity_mergeLeaf :
    LeavesSound exDiamond 4 [⟨dc₁, .ok dσ₁⟩, ⟨dc₂, .ok dσ₂⟩] ∧
      LeavesExhaustive [⟨dc₁, .ok dσ₁⟩, ⟨dc₂, .ok dσ₂⟩] :=
  ⟨symExec_exDiamond ▸ leavesSound_exDiamond, symExec_exDiamond ▸ leavesExhaustive_exDiamond⟩

/-- Tightness of `hs`: an exhaustive list whose first leaf is unsound (the
`x0 ≠ 0` store under the `x0 = 0` guard) merges into an unsound leaf. -/
theorem mergeLeaf_needs_leavesSound :
    ¬ LeavesSound exDiamond 4 [⟨dc₁, .ok dσ₂⟩, ⟨dc₂, .ok dσ₂⟩] ∧
      LeavesExhaustive [⟨dc₁, .ok dσ₂⟩, ⟨dc₂, .ok dσ₂⟩] ∧
      ¬ LeavesSound exDiamond 4 [mergeLeaf dc₁ dσ₂ dc₂ dσ₂] := by
  refine ⟨?_, ?_, ?_⟩
  · intro hs
    have h := congrArg (Outcome.get? 1) (hs ⟨dc₁, .ok dσ₂⟩ (List.mem_cons_self ..) ρ0 (by decide))
    revert h; decide
  · intro ρ
    by_cases h0 : ρ 0 = .int 0
    · exact ⟨_, List.mem_cons_self .., (holds_dc₁ ρ).2 h0⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), (holds_dc₂ ρ).2 h0⟩
  · intro h
    have := congrArg (Outcome.get? 1) (h _ (List.mem_singleton_self _) ρ0 (by decide))
    revert this; decide

/-- The converse of `mergeLeaf_preserves_leavesSound` fails: an unsound second
leaf whose guard is covered by the first guard disappears in the merge. -/
theorem mergeLeaf_leavesSound_converse_fails :
    ¬ LeavesSound exDiamond 4 [⟨dc₁, .ok dσ₁⟩, ⟨dc₁, .ok dσ₂⟩] ∧
      LeavesSound exDiamond 4 [mergeLeaf dc₁ dσ₁ dc₁ dσ₂] := by
  refine ⟨?_, ?_⟩
  · intro hs
    have h := congrArg (Outcome.get? 1)
      (hs ⟨dc₁, .ok dσ₂⟩ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) ρ0 (by decide))
    revert h; decide
  · intro l hl ρ hpc
    rw [List.mem_singleton] at hl; subst hl
    have hdc₁ : holds dc₁ ρ := by
      rcases (holds_or dc₁ dc₁ ρ).1 hpc with h | h <;> exact h
    show exec exDiamond 4 (SymStore.init.inst ρ) = Outcome.ok ((mergeStore dc₁ dσ₁ dσ₂).inst ρ)
    rw [mergeStore_inst_of_holds _ _ _ _ hdc₁]
    exact guardedSound_dc₁_dσ₁ ρ hdc₁

/-! ## Unguarded merge: spurious success -/

/-- The unguarded merge of the two sound `exDiamond` leaves is exhaustive and
passes the strict check for `x1 = x0 + 1`; at the input `x0 = 5`, whose path
condition `c₁ ∨ c₂` holds, the unguarded leaf claims `x1 = 6` while the concrete
run ends with `x1 = 7`: a spurious success. -/
theorem unguardedMerge_spurious_success :
    LeavesSound exDiamond 4 [⟨dc₁, .ok dσ₁⟩, ⟨dc₂, .ok dσ₂⟩] ∧
      LeavesExhaustive [mergeLeafUnguarded dc₁ dσ₁ dc₂ dσ₂] ∧
      LeavesProve [mergeLeafUnguarded dc₁ dσ₁ dc₂ dσ₂] Qplus1 ∧
      holds (Term.or dc₁ dc₂) ρ5 ∧ dσ₁.inst ρ5 1 = .int 6 ∧
      (∃ st, exec exDiamond 4 (SymStore.init.inst ρ5) = .ok st ∧ st 1 = .int 7) ∧
      ¬ OkWith Qplus1 (exec exDiamond 4 (SymStore.init.inst ρ5)) ∧
      ¬ LeavesSound exDiamond 4 [mergeLeafUnguarded dc₁ dσ₁ dc₂ dσ₂] := by
  refine ⟨nonvacuity_mergeLeaf.1, ?_, ?_, by decide, by decide, ⟨_, rfl, by decide⟩,
    by show ¬ (Val.int 7 = Val.int 6); decide, ?_⟩
  · intro ρ
    refine ⟨_, List.mem_singleton_self _, (holds_or _ _ ρ).2 ?_⟩
    by_cases h : ρ 0 = .int 0
    · exact Or.inl ((holds_dc₁ ρ).2 h)
    · exact Or.inr ((holds_dc₂ ρ).2 h)
  · intro l hl ρ _
    rw [List.mem_singleton] at hl; subst hl
    simp [mergeLeafUnguarded, SymOutcome.inst, OkWith, Qplus1, dσ₁, SymStore.inst, SymStore.set,
      SymStore.init, Term.eval, Term.int, Val.toInt]
  · intro h
    have := congrArg (Outcome.get? 1) (h _ (List.mem_singleton_self _) ρ5 (by decide))
    revert this; decide

/-- Positive control: the guarded merge of the same leaves is sound and the
strict check correctly rejects `x1 = x0 + 1`. -/
theorem guardedMerge_rejects_Qplus1 :
    LeavesSound exDiamond 4 [mergeLeaf dc₁ dσ₁ dc₂ dσ₂] ∧
      ¬ LeavesProve [mergeLeaf dc₁ dσ₁ dc₂ dσ₂] Qplus1 := by
  refine ⟨?_, fun h => ?_⟩
  · intro l hl ρ hρ
    rw [List.mem_singleton] at hl; subst hl
    exact guardedSound_merge_dia ρ hρ
  · have := h _ (List.mem_singleton_self _) ρ5 (by decide)
    exact absurd (show Val.int 7 = Val.int 6 from this) (by decide)

/-! ## Coverage under merging -/

/-- Two behaviours (`1` and `2`) for every valuation. -/
def B₁₂ : Valuation → Val → Prop := fun _ a => a = .int 1 ∨ a = .int 2
/-- Observe local `0`. -/
def K₀ : Store → Val := fun st => st 0
/-- Constant store `1`. -/
def s₁ : SymStore := fun _ => int 1
/-- Constant store `2`. -/
def s₂ : SymStore := fun _ => int 2

/-- Tightness of `hagree`: two fully overlapping guarded states cover both
behaviours; their guarded merge produces only behaviour `1`. -/
theorem overlapping_merge_loses_behaviour :
    Covers B₁₂ K₀ [(tt, s₁), (tt, s₂)] ∧
      ¬ Covers B₁₂ K₀ [(Term.or tt tt, mergeStore tt s₁ s₂)] := by
  constructor
  · intro ρ a ha
    rcases ha with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., rfl, rfl⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl, rfl⟩
  · intro h
    obtain ⟨cs, hcs, _, hK⟩ := h ρ0 (.int 2) (Or.inr rfl)
    rw [List.mem_singleton] at hcs; subst hcs
    revert hK; decide

/-- Tightness of `hcov`: agreement holds trivially for two copies of one state,
but a non-covering list stays non-covering after merging. -/
theorem covers_merge_needs_covers :
    (∀ ρ, holds dc₁ ρ → holds dc₁ ρ → Outcome.ok (dσ₁.inst ρ) = Outcome.ok (dσ₁.inst ρ)) ∧
      ¬ Covers (fun ρ o => Rdia ρ = o) Outcome.ok [(Term.or dc₁ dc₁, mergeStore dc₁ dσ₁ dσ₁)] := by
  refine ⟨fun _ _ _ => rfl, fun h => ?_⟩
  obtain ⟨cs, hcs, hg, _⟩ := h ρ5 _ rfl
  rw [List.mem_singleton] at hcs; subst hcs
  revert hg; decide

/-- Store that increments local `0`. -/
def σx0plus1 : SymStore := SymStore.init.set 0 (add (var 0) (int 1))

/-- All hypotheses hold with genuine overlap: the behaviour relation `B₁₂` has
two behaviours at every valuation; the two states to be merged, `(tt, s₁)` and
`(dc₁, σx0plus1)`, have overlapping guards (both hold at `ρ0`) and different
stores (they differ at `ρ5`), yet agree through `K₀` on the overlap; the second
behaviour is carried by the unmerged state `(tt, s₂)`. -/
theorem nonvacuity_covers_merge :
    Covers B₁₂ K₀ [(tt, s₁), (dc₁, σx0plus1), (tt, s₂)] ∧
      (∀ ρ, holds tt ρ → holds dc₁ ρ → K₀ (σx0plus1.inst ρ) = K₀ (s₁.inst ρ)) ∧
      holds tt ρ0 ∧ holds dc₁ ρ0 ∧ B₁₂ ρ0 (.int 1) ∧ B₁₂ ρ0 (.int 2) ∧
      s₁.inst ρ5 0 ≠ σx0plus1.inst ρ5 0 := by
  refine ⟨?_, ?_, rfl, by decide, Or.inl rfl, Or.inr rfl, by decide⟩
  · intro ρ a ha
    rcases ha with rfl | rfl
    · exact ⟨(tt, s₁), List.mem_cons_self .., rfl, rfl⟩
    · exact ⟨(tt, s₂), List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
        rfl, rfl⟩
  · intro ρ _ hdc₁
    have h0 : ρ 0 = .int 0 := (holds_dc₁ ρ).1 hdc₁
    simp [K₀, σx0plus1, s₁, SymStore.inst, SymStore.set, Term.eval, Term.int, h0, Val.toInt]

/-! ## Fuel monotonicity -/

theorem nonvacuity_exec_fuel_mono : exec exStraight 5 ρ5 ≠ .outOfFuel ∧ 5 ≤ 6 := by
  refine ⟨fun h => ?_, by decide⟩
  have := congrArg Outcome.tag h; revert this; decide

/-- Tightness of `hne`: at fuel 4 `exStraight` runs out of fuel; at fuel 5 it
returns. -/
theorem exec_fuel_mono_needs_ne_outOfFuel :
    4 ≤ 5 ∧ exec exStraight 5 ρ5 ≠ exec exStraight 4 ρ5 := by
  refine ⟨by decide, fun h => ?_⟩
  have := congrArg Outcome.tag h; revert this; decide

/-- Tightness of `hle`: fuel can not be decreased. -/
theorem exec_fuel_mono_needs_le :
    exec exStraight 5 ρ5 ≠ .outOfFuel ∧ exec exStraight 4 ρ5 ≠ exec exStraight 5 ρ5 := by
  refine ⟨nonvacuity_exec_fuel_mono.1, fun h => ?_⟩
  have := congrArg Outcome.tag h; revert this; decide

theorem nonvacuity_provesStrict_mono : ProvesStrict exDiamond 4 QneDiamond ∧ 4 ≤ 5 :=
  ⟨provesStrict_exDiamond, by decide⟩

/-- Tightness of `h` (for both `provesStrict_mono` and
`exec_okWith_of_provesStrict_of_le`): with `f = f' = 2`, `exPanicIfZero` fails
the strict check and its run from `ρ0` panics. -/
theorem provesStrict_mono_needs_provesStrict :
    2 ≤ 2 ∧ ¬ ProvesStrict exPanicIfZero 2 Qtrue ∧
      ¬ OkWith Qtrue (exec exPanicIfZero 2 (SymStore.init.inst ρ0)) :=
  ⟨by decide, not_provesStrict_exPanicIfZero, by rw [exPanicIfZero_panics_at_ρ0]; exact id⟩

/-- Tightness of `hle`: `exDiamond` passes the strict check at fuel 4 but not at
fuel 3, where its run from `ρ0` runs out of fuel. -/
theorem provesStrict_mono_needs_le :
    ProvesStrict exDiamond 4 QneDiamond ∧ ¬ ProvesStrict exDiamond 3 QneDiamond ∧
      ¬ OkWith QneDiamond (exec exDiamond 3 (SymStore.init.inst ρ0)) := by
  refine ⟨provesStrict_exDiamond, ?_, id⟩
  have : ∃ l ∈ symExec exDiamond 3, l.res.tag = 2 ∧ holds l.pc ρ0 := by decide
  obtain ⟨l, hl, ht, hρ⟩ := this
  exact not_leavesProve_of_bad_leaf _ _ l hl (by omega) ρ0 hρ

/-! ## Out-of-fuel leaves must not count as success -/

theorem symBlock_exSelfLoop (f : Nat) (c : Term) (σ : SymStore) :
    symBlock exSelfLoop f 0 0 [] (.goto 0) c σ = [⟨c, .outOfFuel⟩] := by
  induction f with
  | zero => rfl
  | succ n ih => exact ih

theorem runBlock_exSelfLoop (f : Nat) (st : Store) :
    runBlock exSelfLoop f 0 0 [] (.goto 0) st = .outOfFuel := by
  induction f with
  | zero => rfl
  | succ n ih => exact ih

/-- Treating `outOfFuel` as success "proves" that the assertion failure after a
three-iteration loop never happens (and even postcondition `False`) at fuel 4,
yet with fuel 13 every input panics at that assertion. -/
theorem provesLax_loopThenAssertFalse_but_panics :
    ProvesLax exLoopThenAssertFalse 4 (fun _ => False) ∧
      ∀ ρ, exec exLoopThenAssertFalse 13 (SymStore.init.inst ρ) = .panic ⟨3, 0⟩ := by
  refine ⟨?_, fun ρ => rfl⟩
  intro l hl ρ hρ
  simp [symExec, exLoopThenAssertFalse, symBlock, forkSwitch] at hl
  rcases hl with rfl | rfl | rfl <;>
    simp_all [holds, Term.eval, OkWithOrOutOfFuel, SymOutcome.inst, Term.and, Term.not, Term.tt,
      Term.ff, Term.int, Val.toBool, Term.subst, SymStore.set, SymStore.init]

/-- Treating `outOfFuel` as success "proves" postcondition `False` for the
infinite loop at every fuel, although no run ever returns. -/
theorem provesLax_selfLoop_every_fuel_but_never_returns :
    (∀ f, ProvesLax exSelfLoop f (fun _ => False)) ∧
      ∀ f ρ, exec exSelfLoop f (SymStore.init.inst ρ) = .outOfFuel := by
  refine ⟨fun f => ?_, fun f ρ => runBlock_exSelfLoop f _⟩
  intro l hl ρ _
  have hs : symExec exSelfLoop f = [⟨Term.tt, .outOfFuel⟩] := symBlock_exSelfLoop f _ _
  rw [hs, List.mem_singleton] at hl; subst hl
  exact trivial

/-- Positive control: the strict check rejects both programs. -/
theorem provesStrict_rejects_out_of_fuel :
    ¬ ProvesStrict exLoopThenAssertFalse 4 Qtrue ∧ ∀ f, ¬ ProvesStrict exSelfLoop f Qtrue := by
  refine ⟨?_, fun f => ?_⟩
  · have : ∃ l ∈ symExec exLoopThenAssertFalse 4, l.res.tag = 2 ∧ holds l.pc ρ0 := by decide
    obtain ⟨l, hl, ht, hρ⟩ := this
    exact not_leavesProve_of_bad_leaf _ _ l hl (by omega) ρ0 hρ
  · have hs : symExec exSelfLoop f = [⟨Term.tt, .outOfFuel⟩] := symBlock_exSelfLoop f _ _
    exact not_leavesProve_of_bad_leaf _ _ ⟨Term.tt, .outOfFuel⟩ (hs ▸ List.mem_singleton_self _)
      (by decide) ρ0 rfl

/-! ## Fuel bounds -/

/-- Both hypotheses hold for `exDiamond` (forward edges) and for `exDag`
(acyclic but not numbered in topological order). -/
theorem nonvacuity_acyclic_fuelBound :
    (Acyclic exDiamond ∧ fuelBound exDiamond ≤ 6) ∧
      (Acyclic exDag ∧ ¬ ForwardEdges exDag ∧ fuelBound exDag ≤ 3) :=
  ⟨⟨acyclic_exDiamond, by decide⟩, ⟨acyclic_exDag, by decide, by decide⟩⟩

/-- Tightness of `hacyc`: the self-loop has `fuelBound = 1` but runs out of fuel. -/
theorem acyclic_fuelBound_needs_acyclic :
    ¬ Acyclic exSelfLoop ∧ fuelBound exSelfLoop ≤ 1 ∧ exec exSelfLoop 1 ρ0 = .outOfFuel :=
  ⟨not_acyclic_exSelfLoop, by decide, rfl⟩

/-- Tightness of `hf`: one unit below the bound, `exStraight` runs out of fuel. -/
theorem acyclic_fuelBound_needs_bound :
    Acyclic exStraight ∧ exec exStraight 4 ρ5 = .outOfFuel := ⟨acyclic_exStraight, rfl⟩

/-- All hypotheses of both straight-line theorems hold for `exStraight` from
`x0 = 5`: it returns at fuel 5 = `fuelBound` and runs out of fuel below. -/
theorem nonvacuity_straightLine_fuelBound :
    StraightLine exStraight ∧ (∃ s, exec exStraight 5 ρ5 = .ok s) ∧ fuelBound exStraight = 5 ∧
      ∀ f' < 5, exec exStraight f' ρ5 = .outOfFuel := by
  refine ⟨by decide, ⟨_, rfl⟩, by decide, ?_⟩
  intro f' hf'
  rcases f' with _ | _ | _ | _ | _ | f' <;> first | rfl | omega

/-- Tightness of `hsl`, for both straight-line theorems. With a branch
(`exDiamond` from `ρ0`), the run returns after 4 steps, below `fuelBound = 6`;
with an unreachable block (`exDeadBlock`), the run returns after 1 step, below
`fuelBound = 2`. In both cases the run returns, the lower bound fails, and so
does the exact-minimality equivalence. -/
theorem straightLine_fuelBound_needs_straightLine :
    (∃ s, exec exDiamond 4 ρ0 = .ok s ∧ ¬ fuelBound exDiamond ≤ 4 ∧
      ¬ (exec exDiamond (fuelBound exDiamond) ρ0 = .ok s ∧
        ∀ f' < fuelBound exDiamond, exec exDiamond f' ρ0 = .outOfFuel)) ∧
    (∃ s, exec exDeadBlock 1 ρ0 = .ok s ∧ ¬ fuelBound exDeadBlock ≤ 1 ∧
      ¬ (exec exDeadBlock (fuelBound exDeadBlock) ρ0 = .ok s ∧
        ∀ f' < fuelBound exDeadBlock, exec exDeadBlock f' ρ0 = .outOfFuel)) := by
  refine ⟨⟨_, rfl, by decide, fun ⟨_, h⟩ => ?_⟩, ⟨_, rfl, by decide, fun ⟨_, h⟩ => ?_⟩⟩
  · have := congrArg Outcome.tag (h 4 (by decide)); revert this; decide
  · have := congrArg Outcome.tag (h 1 (by decide)); revert this; decide

/-- Tightness of `hok` (lower bound only): a straight-line run that panics needs
less fuel. -/
theorem straightLine_fuelBound_needs_ok :
    StraightLine exPanicIfZero ∧ exec exPanicIfZero 1 ρ0 = .panic ⟨0, 0⟩ ∧
      ¬ fuelBound exPanicIfZero ≤ 1 :=
  ⟨by decide, rfl, by decide⟩

/-! ## Simplification -/

theorem nonvacuity_simpSoundUnder :
    SimpSoundUnder dc₁ (Term.substVar 0 (int 0)) ∧ ¬ SimpSoundUnder tt (Term.substVar 0 (int 0)) :=
  ⟨simpSoundUnder_dc₁, not_simpSoundUnder_tt⟩

/-- For one fixed continuation the equivalence fails: with a constant
continuation every rewrite preserves guarded soundness, including one that is
not sound under the path condition. -/
theorem simpSound_iff_fails_for_fixed_continuation :
    ¬ SimpSoundUnder tt (Term.substVar 0 (int 0)) ∧
      ∀ (R : Valuation → Unit) (σ : SymStore),
        GuardedSound R (fun _ => ()) tt σ →
          GuardedSound R (fun _ => ()) tt (fun x => Term.substVar 0 (int 0) (σ x)) :=
  ⟨not_simpSoundUnder_tt, fun _ _ _ _ _ => rfl⟩

/-- Rewriting the path condition itself with a simplifier that is sound under
that path condition can break soundness: `x0 ↦ 0` turns `dc₁` (`x0 = 0`) into a
condition that also holds at `x0 = 5`. -/
theorem simp_pathCondition_breaks_guardedSound :
    SimpSoundUnder dc₁ (Term.substVar 0 (int 0)) ∧ GuardedSound Rdia Outcome.ok dc₁ dσ₁ ∧
      holds (Term.substVar 0 (int 0) dc₁) ρ5 ∧
      ¬ GuardedSound Rdia Outcome.ok (Term.substVar 0 (int 0) dc₁) dσ₁ := by
  refine ⟨simpSoundUnder_dc₁, guardedSound_dc₁_dσ₁, by decide, ?_⟩
  intro hG
  have h := congrArg (Outcome.get? 1) (hG ρ5 (by decide))
  revert h; decide

/-- Simplifying with a fact that holds on only one path (`x0 = 0`, sound under
`dc₁`) after merging breaks soundness of the merged leaf. The rewrite also
reaches the merge guard: `x0 ↦ 0` turns `dc₁` into a condition that holds at
`x0 = 5`, so at that input the rewritten leaf selects the first branch and
claims `x1 = 1`, while the concrete run ends with `x1 = 7`. -/
theorem pathSimp_after_merge_breaks_soundness :
    SimpSoundUnder dc₁ (Term.substVar 0 (int 0)) ∧
      LeavesSound exDiamond 4 [mergeLeaf dc₁ dσ₁ dc₂ dσ₂] ∧
      ¬ holds dc₁ ρ5 ∧ holds (Term.substVar 0 (int 0) dc₁) ρ5 ∧
      holds (Term.or dc₁ dc₂) ρ5 ∧
      SymStore.inst (fun x => Term.substVar 0 (int 0) (mergeStore dc₁ dσ₁ dσ₂ x)) ρ5 1 = .int 1 ∧
      (∃ st, exec exDiamond 4 (SymStore.init.inst ρ5) = .ok st ∧ st 1 = .int 7) ∧
      ¬ LeavesSound exDiamond 4
        [⟨Term.or dc₁ dc₂, .ok (fun x => Term.substVar 0 (int 0) (mergeStore dc₁ dσ₁ dσ₂ x))⟩] := by
  refine ⟨simpSoundUnder_dc₁, guardedMerge_rejects_Qplus1.1, by decide, by decide, by decide,
    by decide, ⟨_, rfl, by decide⟩, fun h => ?_⟩
  have := congrArg (Outcome.get? 1) (h _ (List.mem_singleton_self _) ρ5 (by decide))
  revert this; decide

/-- Positive control: simplifying inside the `dc₁` branch before merging keeps
the merged leaf sound. -/
theorem pathSimp_before_merge_sound :
    LeavesSound exDiamond 4
      [mergeLeaf dc₁ (fun x => Term.substVar 0 (int 0) (dσ₁ x)) dc₂ dσ₂] := by
  intro l hl ρ hρ
  rw [List.mem_singleton] at hl; subst hl
  show exec exDiamond 4 (SymStore.init.inst ρ) = Outcome.ok _
  by_cases h1 : holds dc₁ ρ
  · rw [mergeStore_inst_of_holds _ _ _ _ h1]
    have : SymStore.inst (fun x => Term.substVar 0 (int 0) (dσ₁ x)) ρ = dσ₁.inst ρ := by
      funext x; exact simpSoundUnder_dc₁ (dσ₁ x) ρ h1
    rw [this]; exact guardedSound_dc₁_dσ₁ ρ h1
  · rw [mergeStore_inst_of_not_holds _ _ _ _ h1]
    exact guardedSound_dc₂_dσ₂ ρ ((holds_dc₂ ρ).2 (fun h => h1 ((holds_dc₁ ρ).2 h)))

/-! ## Completeness -/

/-- Instances of the same-fuel characterization: `exDiamond` at fuel 4, and the
three-iteration loop `exLoop3` (not acyclic) at fuel 13, where both sides
hold. -/
theorem nonvacuity_provesStrict_iff :
    ProvesStrict exDiamond 4 QneDiamond ∧ ¬ Acyclic exLoop3 ∧ ProvesStrict exLoop3 13 Qtrue ∧
      (∀ ρ, OkWith Qtrue (exec exLoop3 13 (SymStore.init.inst ρ))) :=
  ⟨provesStrict_exDiamond, not_acyclic_exLoop3,
    leavesProve_of_closed_check _ _ (fun _ => trivial) (by decide), fun _ => trivial⟩

theorem nonvacuity_acyclic_completeness :
    Acyclic exDiamond ∧ ProvesStrict exDiamond (fuelBound exDiamond) QneDiamond := by
  refine ⟨acyclic_exDiamond, ?_⟩
  show LeavesProve (symExec exDiamond 6) QneDiamond
  rw [symExec_exDiamond_6]; exact provesStrict_exDiamond

/-- Tightness of `hacyc`: every input of the three-iteration loop returns (at
fuel 13), but the strict check fails at `fuelBound exLoop3 = 6`. -/
theorem acyclic_completeness_needs_acyclic :
    ¬ Acyclic exLoop3 ∧ (∀ ρ, ∃ f, OkWith Qtrue (exec exLoop3 f (SymStore.init.inst ρ))) ∧
      ¬ ProvesStrict exLoop3 (fuelBound exLoop3) Qtrue := by
  refine ⟨not_acyclic_exLoop3, fun ρ => ⟨13, trivial⟩, ?_⟩
  have : ∃ l ∈ symExec exLoop3 (fuelBound exLoop3), l.res.tag = 2 ∧ holds l.pc ρ0 := by decide
  obtain ⟨l, hl, ht, hρ⟩ := this
  exact not_leavesProve_of_bad_leaf _ _ l hl (by omega) ρ0 hρ

/-! ## Lax and strict checks coincide for acyclic CFGs at the fuel bound -/

theorem nonvacuity_acyclic_lax_iff_strict :
    Acyclic exDiamond ∧ fuelBound exDiamond ≤ 6 ∧ ProvesStrict exDiamond 6 QneDiamond ∧
      ProvesLax exDiamond 6 QneDiamond := by
  refine ⟨acyclic_exDiamond, by decide, ?_, ?_⟩
  · show LeavesProve (symExec exDiamond 6) QneDiamond
    rw [symExec_exDiamond_6]; exact provesStrict_exDiamond
  · show LeavesProveLax (symExec exDiamond 6) QneDiamond
    rw [symExec_exDiamond_6]; exact leavesProveLax_of_leavesProve _ _ provesStrict_exDiamond

/-- Tightness of `hacyc`: the loop followed by `assert false` has
`fuelBound = 7`; at fuel 7 every feasible path is still looping, so the lax check
passes even for postcondition `False`, while the strict check fails. -/
theorem acyclic_lax_iff_strict_needs_acyclic :
    ¬ Acyclic exLoopThenAssertFalse ∧ fuelBound exLoopThenAssertFalse ≤ 7 ∧
      ProvesLax exLoopThenAssertFalse 7 (fun _ => False) ∧
      ¬ ProvesStrict exLoopThenAssertFalse 7 (fun _ => False) := by
  refine ⟨not_acyclic_exLoopThenAssertFalse, by decide,
    leavesProveLax_false_of_closed_check _ (by decide), ?_⟩
  have : ∃ l ∈ symExec exLoopThenAssertFalse 7, l.res.tag = 2 ∧ holds l.pc ρ0 := by decide
  obtain ⟨l, hl, ht, hρ⟩ := this
  exact not_leavesProve_of_bad_leaf _ _ l hl (by omega) ρ0 hρ

/-- Tightness of `hf`: below the bound, the acyclic `exStraight` passes the lax
check for `False` at fuel 4 but fails the strict check. -/
theorem acyclic_lax_iff_strict_needs_bound :
    Acyclic exStraight ∧ ProvesLax exStraight 4 (fun _ => False) ∧
      ¬ ProvesStrict exStraight 4 (fun _ => False) := by
  refine ⟨acyclic_exStraight, provesLax_exStraight_4, ?_⟩
  have : ∃ l ∈ symExec exStraight 4, l.res.tag = 2 ∧ holds l.pc ρ0 := by decide
  obtain ⟨l, hl, ht, hρ⟩ := this
  exact not_leavesProve_of_bad_leaf _ _ l hl (by omega) ρ0 hρ

end Toy.SymEx
