import ToyRelax.Unwind.Completeness

/-!
# Concrete bodies, definition examples, and counterexamples for unwind tables
-/

namespace Toy.Unwind

/-- Save callee-saved register 3 with a push, then clobber it. -/
def bodyPush : List Op := [.push 3, .setReg 3 0]

/-- Prologue/epilogue: save register 3, clobber it, restore it with a pop. -/
def bodyPop : List Op := [.push 3, .setReg 3 0, .pop 3]

/-- As `bodyPop`, followed by a push of register 4 that reuses the freed
slot. -/
def bodyReuse : List Op := [.push 3, .setReg 3 0, .pop 3, .push 4]

/-- Allocate a frame with `subSp`, save register 3 into it with `saveAt`,
clobber register 3, reload it with `addSp`/`pop`. -/
def bodyFrame : List Op := [.subSp 2, .saveAt 3 1, .setReg 3 7, .addSp 1, .pop 3]

/-- Clobber register 1 without saving it. -/
def bodyClobber : List Op := [.setReg 1 5]

/-- The caller-visible register set used in the examples. -/
def cs3 : List Nat := [3]

/-- An entry state with distinct register values. -/
def s0ex : MState := ⟨100, fun r => (r : Int) + 10, fun _ => 0⟩

/-- Off by one, late: the row describing the state after the push takes effect
one instruction late (offset 1 still uses the entry row). -/
def tblLate : Table := fun i => if i = 1 then genTable bodyPush 0 else genTable bodyPush i

/-- Off by one, early: the row describing the state after the push already
applies at the push itself (offset 0). -/
def tblEarly : Table := fun i => if i = 0 then genTable bodyPush 1 else genTable bodyPush i

/-- Missing row after the pop: offset 3 keeps the row of offset 2. -/
def tblNoRowAfterPop : Table := fun i => if i = 3 then genTable bodyPop 2 else genTable bodyPop i

/-- CFA updated after the pop, but register 3 keeps its `savedAt` rule instead
of being restored to `sameValue`. -/
def tblStaleRule (body : List Op) (fromRow : Nat) (rows : List Nat) : Table := fun i =>
  if i ∈ rows then { cfa := (genTable body i).cfa, rule := (genTable body fromRow).rule }
  else genTable body i

/-! ### Definition examples: `execOp`, `run`, `recoverReg` -/

theorem run_example : (run bodyPush s0ex).sp = 99 ∧ (run bodyPush s0ex).mem 99 = 13 ∧
    (run bodyPush s0ex).regs 3 = 0 := by decide

theorem recoverReg_example_savedAt :
    recoverReg ⟨1, fun _ => .savedAt 1⟩ (run bodyPush s0ex) 3 = some 13 := by decide

theorem recoverReg_example_undefined :
    recoverReg ⟨1, fun _ => .undefined⟩ (run bodyPush s0ex) 3 = none := by decide

/-! ### Definition examples: `absRun`, `genTable`, `checkTable` -/

theorem genTable_example :
    (genTable bodyPush 0).cfa = 0 ∧ (genTable bodyPush 0).rule 3 = .sameValue ∧
    (genTable bodyPush 1).cfa = 1 ∧ (genTable bodyPush 1).rule 3 = .sameValue ∧
    (genTable bodyPush 2).cfa = 1 ∧ (genTable bodyPush 2).rule 3 = .savedAt 1 := by decide

theorem genTable_example_pop :
    (genTable bodyPop 3).cfa = 0 ∧ (genTable bodyPop 3).rule 3 = .sameValue := by decide

theorem genTable_example_frame :
    (genTable bodyFrame 3).cfa = 2 ∧ (genTable bodyFrame 3).rule 3 = .savedAt 1 ∧
    (genTable bodyFrame 5).cfa = 0 ∧ (genTable bodyFrame 5).rule 3 = .sameValue := by decide

theorem checkTable_example_pos : checkTable bodyPush cs3 (genTable bodyPush) = true := by decide
theorem checkTable_example_neg : checkTable bodyPush cs3 tblLate = false := by decide

/-! ### Definition examples: `TableCorrect` -/

theorem tableCorrect_example_pos : TableCorrect bodyPush cs3 (genTable bodyPush) :=
  checkTable_sound (by decide)

theorem tableCorrect_example_pos_frame : TableCorrect bodyFrame cs3 (genTable bodyFrame) :=
  checkTable_sound (by decide)

theorem tableCorrect_example_pos_pop : TableCorrect bodyPop cs3 (genTable bodyPop) :=
  checkTable_sound (by decide)

/-- The slot-reuse body admits a correct table (its generated one). -/
theorem tableCorrect_example_pos_reuse : TableCorrect bodyReuse cs3 (genTable bodyReuse) :=
  checkTable_sound (by decide)

/-- `TableCorrect` does not protect the caller's frame: a body that stores a
register at `sp + 5` (inside the caller's frame) has a correct table. -/
theorem tableCorrect_permits_caller_frame_write :
    TableCorrect [.saveAt 3 5, .setReg 3 0] cs3 (genTable [.saveAt 3 5, .setReg 3 0]) ∧
    ∀ s0 : MState, (run [.saveAt 3 5] s0).mem (s0.sp + 5) = s0.regs 3 :=
  ⟨checkTable_sound (by decide), fun s0 => by simp [run, execOp, upd]⟩

/-- `TableCorrect` does not require the body to restore `sp`: a body that
only allocates 10 words has a correct table. -/
theorem tableCorrect_permits_unrestored_sp :
    TableCorrect [.subSp 10] cs3 (genTable [.subSp 10]) ∧
    ∀ s0 : MState, (run [.subSp 10] s0).sp = s0.sp - 10 :=
  ⟨checkTable_sound (by decide), fun s0 => by simp [run, execOp]⟩

/-- A table whose only fault is the CFA rule is rejected even though it never
mentions registers. -/
theorem tableCorrect_example_neg_cfa :
    ¬ TableCorrect bodyPush [] (fun _ => ⟨0, fun _ => .sameValue⟩) := by
  intro h
  have := (h s0ex 1 (by decide)).1
  revert this
  decide

/-! ## Result 6: counterexamples for faulty tables -/

/-- **Counterexample (off-by-one at a push boundary).**  For the body
`[push 3, setReg 3 0]`, both the late placement (offset 1 keeps the entry row)
and the early placement (offset 0 already uses the post-push row) of the CFA
row of the push give an incorrect table: at the misplaced offset the computed
CFA is one word below (late) or above (early) the caller's `sp`, for every
entry state. -/
theorem offByOne_push_tables_incorrect :
    ¬ TableCorrect bodyPush cs3 tblLate ∧ ¬ TableCorrect bodyPush cs3 tblEarly ∧
    (∀ s0 : MState, (run (bodyPush.take 1) s0).sp + (tblLate 1).cfa = s0.sp - 1) ∧
    (∀ s0 : MState, (run (bodyPush.take 0) s0).sp + (tblEarly 0).cfa = s0.sp + 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · intro s0
    simp [bodyPush, run, execOp, tblLate, genTable, absRun, AState.init]
  · intro s0
    simp [bodyPush, run, tblEarly, genTable, absRun, absOp, AState.init]
  · intro h
    have := (h s0ex 1 (by decide)).1
    revert this
    decide
  · intro h
    have := (h s0ex 0 (by decide)).1
    revert this
    decide

/-- **Counterexample (missing row after a pop).**  For the body
`[push 3, setReg 3 0, pop 3]`, if the row after the pop is missing (offset 3
reuses the row of offset 2), the table is incorrect: after the pop the
computed CFA is one word above the caller's `sp`, for every entry state. -/
theorem missing_row_after_pop_incorrect :
    ¬ TableCorrect bodyPop cs3 tblNoRowAfterPop ∧
    ∀ s0 : MState, (run (bodyPop.take 3) s0).sp + (tblNoRowAfterPop 3).cfa = s0.sp + 1 := by
  refine ⟨?_, ?_⟩
  rotate_left
  · intro s0
    simp [bodyPop, run, execOp, tblNoRowAfterPop, genTable, absRun, absOp, AState.init]
  intro h
  have := (h s0ex 3 (by decide)).1
  revert this
  decide

/-- **Counterexample (missing register restore after a pop, then slot
reuse).**  For the body `[push 3, setReg 3 0, pop 3, push 4]`, with the CFA
updated after the pop but register 3 still described as `savedAt 1`, the
table is incorrect: at offset 4, after `push 4` has overwritten the freed
slot, the unwinder reports register 4's entry value for register 3, for every
entry state. -/
theorem stale_savedAt_after_pop_incorrect_after_slot_reuse :
    ¬ TableCorrect bodyReuse cs3 (tblStaleRule bodyReuse 2 [3, 4]) ∧
    ∀ s0 : MState, recoverReg (tblStaleRule bodyReuse 2 [3, 4] 4) (run (bodyReuse.take 4) s0) 3 =
      some (s0.regs 4) := by
  refine ⟨?_, ?_⟩
  rotate_left
  · intro s0
    simp [tblStaleRule, genTable, genRule, absRun, absOp, AState.init, upd, recoverReg, run,
      execOp, bodyReuse]
  intro h
  have := (h s0ex 4 (by decide)).2 3 (by decide)
  revert this
  decide

/-- **Positive control for the previous counterexample.**  Without slot reuse
the same stale `savedAt` rule is still correct, because a pop does not erase
the slot: a missing register-restore row is a latent fault, not an immediate
one, in this model. -/
theorem stale_savedAt_after_pop_correct_without_reuse :
    TableCorrect bodyPop cs3 (tblStaleRule bodyPop 2 [3]) :=
  checkTable_sound (by decide)

/-- Not every later push breaks the stale rule: a push of register 3 itself,
after the pop has restored its entry value, stores that entry value in the
freed slot, so the stale `savedAt 1` rule stays correct. -/
theorem stale_savedAt_survives_push_of_same_value :
    TableCorrect [.push 3, .setReg 3 0, .pop 3, .push 3] cs3
      (tblStaleRule [.push 3, .setReg 3 0, .pop 3, .push 3] 2 [3, 4]) :=
  checkTable_sound (by decide)

/-- **Counterexample for Result 6a's hypothesis.**  A body that clobbers a
caller-visible register without saving it: the generated table marks it
`undefined`, and it is not correct. -/
theorem genTable_with_undefined_incorrect :
    (genTable bodyClobber 1).rule 1 = .undefined ∧ ¬ TableCorrect bodyClobber [1] (genTable bodyClobber) := by
  refine ⟨by decide, ?_⟩
  intro h
  have := (h s0ex 1 (by decide)).2 1 (by decide)
  revert this
  decide

/-- Non-vacuity for Result 6a: the hypothesis holds on a prologue/epilogue
body with a frame allocation. -/
theorem genTable_no_undefined_nonvacuity :
    ∀ i, i ≤ bodyFrame.length → ∀ r ∈ cs3, (genTable bodyFrame i).rule r ≠ .undefined := by
  decide

/-- Canonical counterexample for the premises of both Result 7a (soundness,
premise `checkTable body cs tbl = true`) and Result 7b (completeness, premise
`TableCorrect body cs tbl`): a table the checker rejects is indeed incorrect,
so neither premise can be dropped (not every table is correct, and the checker
does not accept every table). -/
theorem checker_premise_needed :
    checkTable bodyPush cs3 tblLate = false ∧ ¬ TableCorrect bodyPush cs3 tblLate :=
  ⟨by decide, offByOne_push_tables_incorrect.1⟩

/-- Non-vacuity for Result 7b: a correct table (the hypothesis of
completeness) for the frame body, and an incorrect one. -/
theorem tableCorrect_nonvacuity :
    TableCorrect bodyFrame cs3 (genTable bodyFrame) ∧ ¬ TableCorrect bodyPop cs3 tblNoRowAfterPop :=
  ⟨tableCorrect_example_pos_frame, missing_row_after_pop_incorrect.1⟩

/-- Non-vacuity for Result 7a (checker soundness): the checker accepts a
non-trivial table, so the hypothesis of Result 7a is satisfiable; it also
rejects a faulty one. -/
theorem checkTable_nonvacuity :
    checkTable bodyFrame cs3 (genTable bodyFrame) = true ∧
    checkTable bodyPop cs3 tblNoRowAfterPop = false := by decide

end Toy.Unwind
