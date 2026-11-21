import ToyCFI.Lemmas

/-!
# Dynamic CFA base switching in a stack-probing loop

`probeFn page`: `push fp; movReg fp sp` (block 0), a loop `subSp page`
(block 1, address 2), then `movReg sp fp; pop fp; ret` (block 2).  While the
loop runs, `sp` decreases by `page` per iteration and `fp` holds a fixed anchor
(`CFA - 1`).
-/

namespace Toy.CFI

/-- Hand-written annotation for `probeFn` (independent of `page`): in the loop
and after it, `sp` is unknown and `fp` is the anchor `CFA - 1`, with the
caller's `fp` saved at `CFA - 1`. -/
def probeAnn : Ann
  | 0 => some absInit
  | 1 => some { regs := ⟨.unknown, .cfaRel (-1), .callerOf .s1, .callerOf .t1⟩,
                slots := [(-1, .callerOf .fp)] }
  | 2 => some { regs := ⟨.unknown, .cfaRel (-1), .callerOf .s1, .callerOf .t1⟩,
                slots := [(-1, .callerOf .fp)] }
  | _ => none

theorem probeAnn_sound (page : Nat) : annSoundB (probeFn page) probeAnn = true := by rfl

/-- Anchor-relative table: after `movReg fp sp` the CFA is `fp + 1`. -/
def probeAnchorCFI : List CFIInst :=
  [.advanceLoc 1, .defCfaOffset 1, .advanceLoc 1, .defCfaRegister .fp, .offset .fp (-1),
   .advanceLoc 1, .advanceLoc 1, .advanceLoc 1, .defCfa .sp 0, .restore .fp, .advanceLoc 1]

/-- SP-relative table: the CFA stays `sp + 1` (fixed offset) through the loop. -/
def probeSpCFI : List CFIInst :=
  [.advanceLoc 1, .defCfaOffset 1, .advanceLoc 1, .offset .fp (-1),
   .advanceLoc 1, .advanceLoc 1, .advanceLoc 1, .defCfaOffset 0, .restore .fp, .advanceLoc 1]

/-- The anchor-relative program is what the generator emits. -/
theorem genCFI_probeFn_eq (page : Nat) : genCFI (probeFn page) probeAnn = probeAnchorCFI := by rfl

/-- State on entry to the loop block after `n` iterations. -/
def probeLoopState (page : Nat) (c : Caller) (m : Int → Int) : Nat → MState
  | 0 => step (step (entryState c m) (.push .fp)) (.movReg .fp .sp)
  | n + 1 => step (probeLoopState page c m n) (.subSp page)

/-- Every iteration's state is reachable at the loop PC (block 1, offset 0). -/
theorem probeLoopState_reach (page : Nat) (c : Caller) (m : Int → Int) (n : Nat) :
    Reach (probeFn page) c m 1 0 (probeLoopState page c m n) := by
  induction n with
  | zero =>
    exact Reach.edge (Reach.next (Reach.entry (by simp [probeFn, Func.blockOps])) rfl
      (by simp [probeFn, Func.blockOps])) rfl (by simp [probeFn, Func.blockOps])
      (by simp [probeFn, Func.succs]) (by simp [probeFn, Func.blockOps])
  | succ n ih =>
    exact Reach.edge ih rfl (by simp [probeFn, Func.blockOps]) (by simp [probeFn, Func.succs])
      (by simp [probeFn, Func.blockOps])

theorem probeLoopState_zero_regs (page : Nat) (c : Caller) (m : Int → Int) :
    (probeLoopState page c m 0).regs = ⟨c.cfa - 1, c.cfa - 1, c.regs.s1, c.regs.t1⟩ := by
  simp [probeLoopState, step, entryState, RegFile.get, RegFile.set]

theorem probeLoopState_one_regs (page : Nat) (c : Caller) (m : Int → Int) :
    (probeLoopState page c m 1).regs =
      ⟨c.cfa - 1 - (page : Int), c.cfa - 1, c.regs.s1, c.regs.t1⟩ := by
  simp [probeLoopState, step, entryState, RegFile.get, RegFile.set]

/-- Every reachable state at the loop PC has the anchor `fp = CFA - 1`. -/
theorem probe_loop_fp_anchor (page : Nat) {c : Caller} {m : Int → Int} {st : MState}
    (h : Reach (probeFn page) c m 1 0 st) : st.regs.get .fp = c.cfa - 1 := by
  obtain ⟨A, hA, hinv⟩ := reach_inv_of_annSound (probeAnn_sound page) h
  simp only [probeAnn] at hA
  cases hA
  have := hinv.1 .fp
  simp only [absAt, List.take_zero, absRun, List.foldl, RegFile.get, SymHolds] at this
  simp only [RegFile.get]
  omega

/-- **Characterization.** For `page > 0`, a row computes the correct CFA at every
reachable state of the loop PC (every iteration, every caller, every memory)
if and only if its CFA rule is the anchor rule `fp + 1`. -/
theorem probeLoop_cfa_correct_at_every_iteration_iff_fp_anchor (page : Nat) (hpage : 0 < page)
    (R : Row) :
    (∀ c m st, Reach (probeFn page) c m 1 0 st → cfaOf R st = c.cfa) ↔
      (R.cfaReg = .fp ∧ R.cfaOff = 1) := by
  constructor
  · intro h
    let m0 : Int → Int := fun _ => 0
    let c1 : Caller := ⟨100, ⟨0, 0, 0, 0⟩⟩
    let c2 : Caller := ⟨100, ⟨0, 1, 1, 1⟩⟩
    have h0 := h c1 m0 _ (probeLoopState_reach page c1 m0 0)
    have h1 := h c1 m0 _ (probeLoopState_reach page c1 m0 1)
    have h2 := h c2 m0 _ (probeLoopState_reach page c2 m0 0)
    simp only [cfaOf, probeLoopState_zero_regs, probeLoopState_one_regs] at h0 h1 h2
    obtain ⟨reg, off, rules⟩ := R
    cases reg <;> simp [RegFile.get, c1, c2] at h0 h1 h2 ⊢ <;> omega
  · rintro ⟨hreg, hoff⟩ c m st hr
    simp only [cfaOf, hreg, hoff, probe_loop_fp_anchor page hr]
    omega

/-- The SP-relative row `CFA = sp + 1` evaluated at the first two iterations of
the loop: `CFA` on entry, `CFA - page` after one iteration (any `page`). -/
theorem spRelative_cfa_at_first_two_iterations (page : Nat)
    (c : Caller) (m : Int → Int) (rules : RegFile RegRule) :
    cfaOf ⟨.sp, 1, rules⟩ (probeLoopState page c m 0) = c.cfa ∧
      cfaOf ⟨.sp, 1, rules⟩ (probeLoopState page c m 1) = c.cfa - page := by
  simp only [cfaOf, probeLoopState_zero_regs, probeLoopState_one_regs, RegFile.get]
  omega

/-- The anchor-relative table is correct for every `page`. -/
theorem probeAnchorCFI_tableCorrect (page : Nat) : TableCorrect (probeFn page) probeAnchorCFI :=
  checkWith_sound (ann := probeAnn) (by rfl)

/-- The SP-relative table is incorrect for every `page > 0`. -/
theorem probeSpCFI_not_tableCorrect (page : Nat) (hpage : 0 < page) :
    ¬ TableCorrect (probeFn page) probeSpCFI := by
  let c : Caller := ⟨100, ⟨0, 0, 0, 0⟩⟩
  refine not_tableCorrect_of_bad_row (probeLoopState_reach page c (fun _ => 0) 1)
    (pc := 2) rfl (R := ⟨.sp, 1, ⟨.same, .offset (-1), .same, .same⟩⟩) rfl ?_
  rw [(spRelative_cfa_at_first_two_iterations page c _ _).2]
  omega

/-- **SP-relative CFA with a fixed offset is right on loop entry and wrong after
the first iteration, for `page > 0`.** For every caller, memory and register
rules, the row `CFA = sp + 1` computes the true CFA at the loop PC on entry and
`CFA - page ≠ CFA` after one iteration; consequently the SP-relative table
`probeSpCFI` is not correct for `probeFn page`. -/
theorem spRelative_cfa_right_on_entry_wrong_after_first_iteration_of_pos_page (page : Nat)
    (hpage : 0 < page) (c : Caller) (m : Int → Int) (rules : RegFile RegRule) :
    cfaOf ⟨.sp, 1, rules⟩ (probeLoopState page c m 0) = c.cfa ∧
      cfaOf ⟨.sp, 1, rules⟩ (probeLoopState page c m 1) = c.cfa - page ∧
      cfaOf ⟨.sp, 1, rules⟩ (probeLoopState page c m 1) ≠ c.cfa ∧
      ¬ TableCorrect (probeFn page) probeSpCFI := by
  obtain ⟨h0, h1⟩ := spRelative_cfa_at_first_two_iterations page c m rules
  exact ⟨h0, h1, by rw [h1]; omega, probeSpCFI_not_tableCorrect page hpage⟩

/-- Annotation for `probeFn 0` (the loop does not move `sp`). -/
def probeAnnZero : Ann
  | 0 => some absInit
  | 1 => some { regs := ⟨.cfaRel (-1), .cfaRel (-1), .callerOf .s1, .callerOf .t1⟩,
                slots := [(-1, .callerOf .fp)] }
  | 2 => some { regs := ⟨.cfaRel (-1), .cfaRel (-1), .callerOf .s1, .callerOf .t1⟩,
                slots := [(-1, .callerOf .fp)] }
  | _ => none

/-- Tightness of `0 < page`: with `page = 0` the SP-relative rule `sp + 1` is
correct at every reachable loop state, so the characterization fails. -/
theorem probeLoop_characterization_fails_for_page_zero :
    ∃ R : Row, (∀ c m st, Reach (probeFn 0) c m 1 0 st → cfaOf R st = c.cfa) ∧
      ¬ (R.cfaReg = .fp ∧ R.cfaOff = 1) := by
  refine ⟨⟨.sp, 1, RegFile.const .same⟩, fun c m st hr => ?_, by simp⟩
  obtain ⟨A, hA, hinv⟩ := reach_inv_of_annSound (ann := probeAnnZero) (by decide) hr
  simp only [probeAnnZero] at hA
  cases hA
  have := hinv.1 .sp
  simp only [absAt, List.take_zero, absRun, List.foldl, RegFile.get, SymHolds] at this
  simp only [cfaOf, RegFile.get]
  omega

/-- Non-vacuity of the characterization: for `page = 4096` the anchor rule
satisfies the left side and the SP-relative rule `sp + 1` does not. -/
theorem probeLoop_characterization_nonvacuity (rules : RegFile RegRule) :
    0 < 4096 ∧ (∀ c m st, Reach (probeFn 4096) c m 1 0 st → cfaOf ⟨.fp, 1, rules⟩ st = c.cfa) ∧
      ¬ (∀ c m st, Reach (probeFn 4096) c m 1 0 st → cfaOf ⟨.sp, 1, rules⟩ st = c.cfa) := by
  refine ⟨by decide, (probeLoop_cfa_correct_at_every_iteration_iff_fp_anchor 4096 (by decide) _).2
    ⟨rfl, rfl⟩, fun h => ?_⟩
  have := (probeLoop_cfa_correct_at_every_iteration_iff_fp_anchor 4096 (by decide) _).1 h
  simp at this

/-- Tightness of `0 < page` for the SP-relative statement: with `page = 0` the
row `CFA = sp + 1` is right after the first iteration too, so the conclusion
fails for every caller, memory and register rules. -/
theorem spRelative_wrong_after_first_iteration_fails_for_page_zero :
    ¬ (0 < 0) ∧ ∀ (c : Caller) (m : Int → Int) (rules : RegFile RegRule),
      ¬ (cfaOf ⟨.sp, 1, rules⟩ (probeLoopState 0 c m 0) = c.cfa ∧
        cfaOf ⟨.sp, 1, rules⟩ (probeLoopState 0 c m 1) = c.cfa - (0 : Nat) ∧
        cfaOf ⟨.sp, 1, rules⟩ (probeLoopState 0 c m 1) ≠ c.cfa ∧
        ¬ TableCorrect (probeFn 0) probeSpCFI) := by
  refine ⟨by decide, fun c m rules h => h.2.2.1 ?_⟩
  have := (spRelative_cfa_at_first_two_iterations 0 c m rules).2
  rw [this]; omega

/-- Non-vacuity of the SP-relative statement: its hypothesis holds for
`page = 4096`. -/
theorem spRelative_wrong_after_first_iteration_nonvacuity :
    0 < 4096 ∧ ¬ TableCorrect (probeFn 4096) probeSpCFI :=
  ⟨by decide, probeSpCFI_not_tableCorrect 4096 (by decide)⟩

end Toy.CFI
