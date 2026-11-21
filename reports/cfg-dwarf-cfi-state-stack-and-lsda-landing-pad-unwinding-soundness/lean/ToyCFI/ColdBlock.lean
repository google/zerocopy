import ToyCFI.Lemmas

/-!
# Necessity of `rememberState`/`restoreState` (or explicit re-definition) when an
epilogue physically precedes a cold block

In `coldFn` the layout is `0, 1, 2`: the epilogue (block 1, addresses 3–5) sits
between the prologue and the cold block (block 2, address 6).  A CFI program is
interpreted linearly, so unless some instruction is located at address 6, the
row at the cold block's first PC is the row at the epilogue's `ret` (address 5).
-/

namespace Toy.CFI

/-- State after the prologue's first two operations. -/
def coldSt02 (c : Caller) (m : Int → Int) : MState :=
  step (step (entryState c m) (.push .fp)) (.movReg .fp .sp)

/-- State at the epilogue's `ret` (block 1, offset 2, address 5). -/
def coldStRet (c : Caller) (m : Int → Int) : MState :=
  step (step (step (coldSt02 c m) .call) (.movReg .sp .fp)) (.pop .fp)

/-- State at the cold block's first PC (block 2, offset 0, address 6). -/
def coldStCold (c : Caller) (m : Int → Int) : MState := step (coldSt02 c m) .call

theorem coldFn_reach_ret (c : Caller) (m : Int → Int) : Reach coldFn c m 1 2 (coldStRet c m) :=
  Reach.next (Reach.next (Reach.edge (Reach.next (Reach.next (Reach.entry (by decide))
    rfl (by decide)) rfl (by decide)) rfl (by decide) (by decide) (by decide))
    rfl (by decide)) rfl (by decide)

theorem coldFn_reach_cold (c : Caller) (m : Int → Int) :
    Reach coldFn c m 2 0 (coldStCold c m) :=
  Reach.edge (Reach.next (Reach.next (Reach.entry (by decide)) rfl (by decide)) rfl (by decide))
    rfl (by decide) (by decide) (by decide)

theorem coldStRet_regs (c : Caller) (m : Int → Int) :
    (coldStRet c m).regs = ⟨c.cfa, c.regs.fp, c.regs.s1, c.regs.t1⟩ := by
  simp [coldStRet, coldSt02, step, entryState, RegFile.get, RegFile.set, write]

theorem coldStCold_regs (c : Caller) (m : Int → Int) :
    (coldStCold c m).regs = ⟨c.cfa - 1, c.cfa - 1, c.regs.s1, c.regs.t1⟩ := by
  simp [coldStCold, coldSt02, step, entryState, RegFile.get, RegFile.set]

/-- Non-vacuity: both PCs are reachable for every caller and memory, with
different `sp` offsets (`CFA` at address 5, `CFA - 1` at address 6). -/
theorem coldFn_both_pcs_reachable (c : Caller) (m : Int → Int) :
    Reach coldFn c m 1 2 (coldStRet c m) ∧ Reach coldFn c m 2 0 (coldStCold c m) ∧
      (coldStRet c m).regs.get .sp = c.cfa ∧ (coldStCold c m).regs.get .sp = c.cfa - 1 := by
  refine ⟨coldFn_reach_ret c m, coldFn_reach_cold c m, ?_, ?_⟩
  · rw [coldStRet_regs]; rfl
  · rw [coldStCold_regs]; rfl

/-- The `coldFn` instance of the layout-independent impossibility below. -/
theorem coldFn_no_row_recovers_at_both_epilogue_ret_and_cold_entry :
    ¬ ∃ R : Row, (∀ c m st, Reach coldFn c m 1 2 st → Recovers R c st) ∧
      (∀ c m st, Reach coldFn c m 2 0 st → Recovers R c st) := by
  rintro ⟨R, hret, hcold⟩
  let m0 : Int → Int := fun _ => 0
  let c1 : Caller := ⟨100, ⟨0, 0, 0, 0⟩⟩
  let c2 : Caller := ⟨100, ⟨0, 1, 1, 1⟩⟩
  have h1 := (hret c1 m0 _ (coldFn_reach_ret c1 m0)).1
  have h2 := (hcold c1 m0 _ (coldFn_reach_cold c1 m0)).1
  have h3 := (hcold c2 m0 _ (coldFn_reach_cold c2 m0)).1
  simp only [cfaOf, coldStRet_regs, coldStCold_regs] at h1 h2 h3
  obtain ⟨reg, off, rules⟩ := R
  cases reg <;> simp [RegFile.get, c1, c2] at h1 h2 h3 <;> omega

/-- **No single row serves the epilogue's `ret` and the cold block's entry, in
any layout.** For the blocks of `coldFn` (prologue; epilogue
`movReg sp fp; pop fp; ret`; cold block entered with the frame established)
placed in an arbitrary layout `lay`, no row recovers the caller both at every
reachable state of the epilogue's `ret` (block 1, offset 2) and at every
reachable state of the cold block's first PC (block 2, offset 0).  This is a
statement about two CFG program points, not about addresses: reachability does
not depend on the layout (`Reach.layout_irrelevant`).  What the layout decides
is whether the two points receive the same row
(`coldFn_not_tableCorrect_of_cold_entry_row_eq_epilogue_ret_row`). -/
theorem coldBlocks_no_row_recovers_at_both_epilogue_ret_and_cold_entry (lay : List Nat) :
    ¬ ∃ R : Row, (∀ c m st, Reach ⟨coldBlocks, lay⟩ c m 1 2 st → Recovers R c st) ∧
      (∀ c m st, Reach ⟨coldBlocks, lay⟩ c m 2 0 st → Recovers R c st) := by
  rintro ⟨R, h1, h2⟩
  exact coldFn_no_row_recovers_at_both_epilogue_ret_and_cold_entry
    ⟨R, fun c m st hr => h1 c m st ((Reach.layout_irrelevant coldBlocks [0, 1, 2] lay).mp hr),
        fun c m st hr => h2 c m st ((Reach.layout_irrelevant coldBlocks [0, 1, 2] lay).mp hr)⟩

/-- **Inherited row is wrong.** Any CFI program whose row at the cold block's
first PC (address 6) equals its row at the epilogue's `ret` (address 5) — as
happens when no instruction is located at address 6 — is not correct for
`coldFn` (layout `0, 1, 2`). -/
theorem coldFn_not_tableCorrect_of_cold_entry_row_eq_epilogue_ret_row (prog : List CFIInst)
    (hinh : rowAt? prog 6 = rowAt? prog 5) : ¬ TableCorrect coldFn prog := by
  intro h
  apply coldFn_no_row_recovers_at_both_epilogue_ret_and_cold_entry
  obtain ⟨R, hR, -⟩ := h.row_at (coldFn_reach_ret ⟨0, ⟨0, 0, 0, 0⟩⟩ (fun _ => 0))
    (show coldFn.pcOf 1 2 = some 5 by decide)
  refine ⟨R, fun c m st hr => ?_, fun c m st hr => ?_⟩
  · obtain ⟨R', hR', hrec⟩ := h.row_at hr (show coldFn.pcOf 1 2 = some 5 by decide)
    rw [hR] at hR'; cases hR'; exact hrec
  · obtain ⟨R', hR', hrec⟩ := h.row_at hr (show coldFn.pcOf 2 0 = some 6 by decide)
    rw [hinh, hR] at hR'; cases hR'; exact hrec

/-- The inferred annotation of `coldFn` is sound. -/
theorem coldFn_annSound : annSoundB coldFn (inferredAnn coldFn) = true := by decide

/-- The inferred entry state of the cold block. -/
theorem coldFn_inferred_cold_entry :
    inferredAnn coldFn 2 =
      some { regs := ⟨.cfaRel (-1), .cfaRel (-1), .callerOf .s1, .callerOf .t1⟩,
             slots := [(-1, .callerOf .fp)] } := by decide

/-- **The naive (per-block, no boundary compensation) program computes a bogus
CFA in the cold block.** Its row at address 6 is the post-epilogue row
`initRow` (`CFA = sp + 0`, all registers `same`), and for every caller and every
reachable state at the cold block's first PC that row yields `CFA - 1`. -/
theorem naiveCFI_coldFn_cold_entry_cfa_is_true_cfa_minus_one :
    rowAt? (naiveCFI coldFn (inferredAnn coldFn)) 6 = some initRow ∧
      ∀ c m st, Reach coldFn c m 2 0 st → cfaOf initRow st = c.cfa - 1 := by
  refine ⟨by decide, fun c m st hr => ?_⟩
  obtain ⟨A, hA, hinv⟩ := reach_inv_inferred coldFn_annSound hr
  rw [coldFn_inferred_cold_entry] at hA
  cases hA
  have := hinv.1 .sp
  simp only [absAt, List.take_zero, absRun, List.foldl, RegFile.get, SymHolds] at this
  simp only [cfaOf, initRow, RegFile.get]
  omega

theorem naiveCFI_coldFn_not_tableCorrect : ¬ TableCorrect coldFn (naiveCFI coldFn (inferredAnn coldFn)) :=
  coldFn_not_tableCorrect_of_cold_entry_row_eq_epilogue_ret_row _ (by decide)

/-- Positive control (layout): with the CFG-order layout `0, 2, 1` the same naive
emitter is correct. -/
theorem naiveCFI_coldFnFallthrough_tableCorrect :
    TableCorrect coldFnFallthrough (naiveCFI coldFnFallthrough (inferredAnn coldFnFallthrough)) :=
  checkCFI_sound (by decide)

/-- Positive control (compensation): for the layout `0, 1, 2`, the generator's
program, which remembers the row at the start of the epilogue block and restores
it at the start of the cold block, is correct. -/
theorem genCFI_coldFn_tableCorrect : TableCorrect coldFn (genCFI coldFn (inferredAnn coldFn)) :=
  checkCFI_sound (by decide)

/-- The generator's program for `coldFn`, verbatim. -/
theorem genCFI_coldFn_eq : genCFI coldFn (inferredAnn coldFn) =
    [.advanceLoc 1, .defCfaOffset 1, .advanceLoc 1, .defCfaRegister .fp, .offset .fp (-1),
     .advanceLoc 1, .rememberState, .advanceLoc 1, .advanceLoc 1, .defCfa .sp 0, .restore .fp,
     .advanceLoc 1, .restoreState, .advanceLoc 1] := by decide

/-- Tightness of the inherited-row hypothesis: in the generator's (correct)
program the rows at addresses 5 and 6 differ. -/
theorem genCFI_coldFn_rows_differ_and_tableCorrect :
    rowAt? (genCFI coldFn (inferredAnn coldFn)) 6 ≠ rowAt? (genCFI coldFn (inferredAnn coldFn)) 5 ∧
      TableCorrect coldFn (genCFI coldFn (inferredAnn coldFn)) :=
  ⟨by decide, genCFI_coldFn_tableCorrect⟩

/-- An explicit re-definition at address 6 (instead of `restoreState`) also works:
the naive program with `defCfa fp 1; offset fp (-1)` inserted before the last
`advanceLoc`. -/
def coldExplicitCFI : List CFIInst :=
  [.advanceLoc 1, .defCfaOffset 1, .advanceLoc 1, .defCfaRegister .fp, .offset .fp (-1),
   .advanceLoc 1, .advanceLoc 1, .advanceLoc 1, .defCfa .sp 0, .restore .fp,
   .advanceLoc 1, .defCfa .fp 1, .offset .fp (-1), .advanceLoc 1]

theorem coldExplicitCFI_tableCorrect : TableCorrect coldFn coldExplicitCFI :=
  checkCFI_sound (by decide)

/-- The naive program's rows at addresses 6 and 5 coincide (it emits nothing at
the cold block's address). -/
theorem naiveCFI_coldFn_rows_equal :
    rowAt? (naiveCFI coldFn (inferredAnn coldFn)) 6 = rowAt? (naiveCFI coldFn (inferredAnn coldFn)) 5 := by
  decide

/-- Positive control for the layout-independent impossibility: in every layout
of the same blocks, one row (`CFA = fp + 1`, `fp` saved at `CFA - 1`) recovers
the caller both at the epilogue's first PC (block 1, offset 0) and at the cold
block's first PC (block 2, offset 0), so "no single row serves two program
points" is specific to the pair (epilogue `ret`, cold entry). -/
theorem coldBlocks_one_row_recovers_at_epilogue_entry_and_cold_entry (lay : List Nat) :
    ∃ R : Row, (∀ c m st, Reach ⟨coldBlocks, lay⟩ c m 1 0 st → Recovers R c st) ∧
      (∀ c m st, Reach ⟨coldBlocks, lay⟩ c m 2 0 st → Recovers R c st) := by
  refine ⟨⟨.fp, 1, ⟨.same, .offset (-1), .same, .same⟩⟩, ?_, ?_⟩
  · intro c m st hr
    have hr' := (Reach.layout_irrelevant coldBlocks lay [0, 1, 2]).mp hr
    obtain ⟨A, hA, hinv⟩ := reach_inv_inferred coldFn_annSound hr'
    have h1 : inferredAnn coldFn 1 =
        some { regs := ⟨.cfaRel (-1), .cfaRel (-1), .callerOf .s1, .callerOf .t1⟩,
               slots := [(-1, .callerOf .fp)] } := by decide
    rw [h1] at hA; cases hA
    exact entails_sound (by decide) hinv
  · intro c m st hr
    have hr' := (Reach.layout_irrelevant coldBlocks lay [0, 1, 2]).mp hr
    obtain ⟨A, hA, hinv⟩ := reach_inv_inferred coldFn_annSound hr'
    rw [coldFn_inferred_cold_entry] at hA; cases hA
    exact entails_sound (by decide) hinv

end Toy.CFI
