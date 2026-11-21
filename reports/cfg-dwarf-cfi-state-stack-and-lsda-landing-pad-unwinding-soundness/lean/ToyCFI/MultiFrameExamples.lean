import ToyCFI.MultiFrame

/-!
# Multi-frame composition: witness and counterexamples
-/

namespace Toy.CFI

/-! ## Functions -/

/-- Inner function: frame-pointer prologue, a call (at address 2), epilogue. -/
def innerFn : Func :=
  { blocks := [⟨[.push .fp, .movReg .fp .sp, .call, .movReg .sp .fp, .pop .fp, .ret], []⟩],
    layout := [0] }

/-- Outer function: allocate two words, call (at address 1), release, return. -/
def outerFn : Func := { blocks := [⟨[.subSp 2, .call, .addSp 2, .ret], []⟩], layout := [0] }

/-- Inner function that also overwrites the scratch register `t1` before its call
(at address 3). -/
def innerT1Fn : Func :=
  { blocks := [⟨[.push .fp, .movReg .fp .sp, .movReg .t1 .sp, .call, .movReg .sp .fp, .pop .fp,
      .ret], []⟩],
    layout := [0] }

/-- Outer function anchoring its CFA in the scratch register `t1`; call at address 2. -/
def outerT1Fn : Func :=
  { blocks := [⟨[.movReg .t1 .sp, .subSp 2, .call, .addSp 2, .ret], []⟩], layout := [0] }

/-- `outerT1Fn`'s table: `CFA = t1 + 0` from address 1 on. -/
def outerT1CFI : List CFIInst :=
  [.advanceLoc 1, .defCfaRegister .t1, .advanceLoc 1, .advanceLoc 1, .advanceLoc 1, .advanceLoc 1]

/-- Innermost function that stores `t1` at its own CFA (into its caller's frame),
then calls (at address 1). -/
def clobberFn : Func := { blocks := [⟨[.saveAt .t1 0, .call, .ret], []⟩], layout := [0] }

theorem innerFn_tableCorrect : TableCorrect innerFn (genCFI innerFn (inferredAnn innerFn)) :=
  checkCFI_sound (by decide)
theorem outerFn_tableCorrect : TableCorrect outerFn (genCFI outerFn (inferredAnn outerFn)) :=
  checkCFI_sound (by decide)
theorem innerT1Fn_tableCorrect :
    TableCorrect innerT1Fn (genCFI innerT1Fn (inferredAnn innerT1Fn)) :=
  checkCFI_sound (by decide)
theorem outerT1Fn_tableCorrect : TableCorrect outerT1Fn outerT1CFI := checkCFI_sound (by decide)
theorem clobberFn_tableCorrect : TableCorrect clobberFn (genCFI clobberFn (inferredAnn clobberFn)) :=
  checkCFI_sound (by decide)

/-! ## Frames and true states -/

def innerFrame : Frame :=
  { fn := innerFn, prog := genCFI innerFn (inferredAnn innerFn), lsda := none, callPC := 2,
    frameSize := 1 }
def outerFrame : Frame :=
  { fn := outerFn, prog := genCFI outerFn (inferredAnn outerFn), lsda := some [⟨1, 2, some 7⟩],
    callPC := 1, frameSize := 2 }

def topCaller : Caller := ⟨1000, ⟨0, 11, 22, 33⟩⟩
def topMem : Int → Int := fun _ => 0

/-- True state of the outer frame at its call. -/
def outerSt : MState := step (entryState topCaller topMem) (.subSp 2)
/-- Caller context of a frame called from state `s`. -/
def ctxOf (s : MState) : Caller := ⟨s.regs.get .sp, s.regs⟩
/-- True state of the inner frame at its call (called from `outerSt`). -/
def innerSt : MState :=
  step (step (entryState (ctxOf outerSt) outerSt.mem) (.push .fp)) (.movReg .fp .sp)

def frames2 : List Frame := [innerFrame, outerFrame]
def truth2 : List MState := [innerSt, outerSt]

theorem innerFn_reach_call (c : Caller) (m : Int → Int) :
    Reach innerFn c m 0 2 (step (step (entryState c m) (.push .fp)) (.movReg .fp .sp)) :=
  Reach.next (Reach.next (Reach.entry (by decide)) rfl (by decide)) rfl (by decide)

theorem outerFn_reach_call (c : Caller) (m : Int → Int) :
    Reach outerFn c m 0 1 (step (entryState c m) (.subSp 2)) :=
  Reach.next (Reach.entry (by decide)) rfl (by decide)

theorem chain2 : ChainReachable frames2 truth2 topCaller := by
  refine ⟨rfl, fun j fr st hf ht => ?_⟩
  match j, hf, ht with
  | 0, hf, ht =>
    simp only [frames2, truth2, List.getElem?_cons_zero, Option.some.injEq] at hf ht
    subst hf; subst ht
    exact ⟨outerSt.mem, 0, 2, by decide, rfl, innerFn_reach_call _ _⟩
  | 1, hf, ht =>
    simp only [frames2, truth2, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.some.injEq] at hf ht
    subst hf; subst ht
    exact ⟨topMem, 0, 1, by decide, rfl, outerFn_reach_call _ _⟩
  | j + 2, hf, _ => simp [frames2] at hf

theorem frames2_tables : ∀ fr ∈ frames2, TableCorrect fr.fn fr.prog := by
  intro fr h
  simp only [frames2, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl
  · exact innerFn_tableCorrect
  · exact outerFn_tableCorrect

theorem outerFrame_row : rowAt? outerFrame.prog outerFrame.callPC =
    some ⟨.sp, 2, RegFile.const .same⟩ := by decide

/-! ## Helpers for the named hypotheses -/

theorem tablesUpTo_of_all {frames : List Frame} {j : Nat}
    (h : ∀ fr ∈ frames, TableCorrect fr.fn fr.prog) : TablesUpTo frames j :=
  fun _ fr _ hf => h fr (List.mem_of_getElem? hf)

theorem slotsPreservedBelow_one (frames : List Frame) (truth : List MState) (M : Int → Int) :
    SlotsPreservedBelow frames truth M 1 :=
  fun _ _ _ _ h0 h1 => absurd h1 (by omega)

theorem skippedBelow_one {a : Frame} {rest : List Frame} (h : frameAction a = .skip) :
    SkippedBelow (a :: rest) 1 := by
  intro i fr hi hf
  obtain rfl : i = 0 := by omega
  simp only [List.getElem?_cons_zero, Option.some.injEq] at hf
  subst hf; exact h

theorem baseSafeUpTo_one {a b : Frame} {rest : List Frame}
    (h : ∀ R, rowAt? b.prog b.callPC = some R → CfaBaseSafe R) : BaseSafeUpTo (a :: b :: rest) 1 := by
  intro i fr R hi hi1 hf hR
  obtain rfl : i = 1 := by omega
  simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hf
  subst hf; exact h R hR

theorem outerFrame_baseSafe : ∀ R, rowAt? outerFrame.prog outerFrame.callPC = some R → CfaBaseSafe R := by
  intro R hR
  rw [outerFrame_row] at hR
  cases hR
  exact Or.inl rfl

/-- Chain for a two-frame list whose inner frame runs `innerFn`. -/
theorem chain_inner_outer (a b : Frame) (ha : a.fn = innerFn ∧ a.callPC = 2)
    (hb : b.fn = outerFn ∧ b.callPC = 1) : ChainUpTo [a, b] truth2 topCaller 1 := by
  intro i fr st hi hf ht
  match i, hf, ht with
  | 0, hf, ht =>
    simp only [truth2, List.getElem?_cons_zero, Option.some.injEq] at hf ht
    subst hf; subst ht
    refine ⟨outerSt.mem, 0, 2, ?_, ?_, ?_⟩ <;> rw [ha.1] <;> try rw [ha.2]
    · decide
    · rfl
    · exact innerFn_reach_call _ _
  | 1, hf, ht =>
    simp only [truth2, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.some.injEq] at hf ht
    subst hf; subst ht
    refine ⟨topMem, 0, 1, ?_, ?_, ?_⟩ <;> rw [hb.1] <;> try rw [hb.2]
    · decide
    · rfl
    · exact outerFn_reach_call _ _
  | j + 2, hf, _ => simp at hf

/-! ## Non-vacuity -/

/-- **Non-vacuity.** The two-frame chain (inner frame without call-site table,
outer frame with landing pad `7` at its call) satisfies every hypothesis of
`unwind_caught_at_first_handler_frame_with_caller_registers` with `j = 1`. -/
theorem multiFrame_hypotheses_hold :
    ChainUpTo frames2 truth2 topCaller 1 ∧ TablesUpTo frames2 1 ∧
      truth2[0]? = some innerSt ∧ frames2[1]? = some outerFrame ∧ truth2[1]? = some outerSt ∧
      SkippedBelow frames2 1 ∧ frameAction outerFrame = .handle 7 ∧
      BaseSafeUpTo frames2 1 ∧ SlotsPreservedBelow frames2 truth2 innerSt.mem 1 :=
  ⟨chain_inner_outer _ _ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩, tablesUpTo_of_all frames2_tables, rfl, rfl, rfl,
    skippedBelow_one rfl, by decide, baseSafeUpTo_one outerFrame_baseSafe,
    slotsPreservedBelow_one _ _ _⟩

/-- The concrete outcome: caught at depth 1 with landing pad 7; the reconstructed
state has the outer frame's `sp = 998`, `fp = 11`, `s1 = 22`. -/
theorem multiFrame_outcome :
    unwind frames2 innerSt = .caught 1 7 (unwindRegs
      ((rowAt? innerFrame.prog innerFrame.callPC).getD initRow) innerSt) ∧
    (unwindRegs ((rowAt? innerFrame.prog innerFrame.callPC).getD initRow) innerSt).regs.sp = 998 ∧
    (unwindRegs ((rowAt? innerFrame.prog innerFrame.callPC).getD initRow) innerSt).regs.fp = 11 ∧
    (unwindRegs ((rowAt? innerFrame.prog innerFrame.callPC).getD initRow) innerSt).regs.s1 = 22 := by
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> decide

/-! ## Counterexamples (each: the named hypothesis fails, all other hypotheses
hold, and the conclusion fails) -/

/-- The inner frame with the empty program (the initial row everywhere). -/
def innerFrameBad : Frame := { innerFrame with prog := [] }

theorem multiFrame_fails_without_tablesUpTo :
    ChainUpTo [innerFrameBad, outerFrame] truth2 topCaller 1 ∧
      ¬ TablesUpTo [innerFrameBad, outerFrame] 1 ∧
      truth2[0]? = some innerSt ∧ [innerFrameBad, outerFrame][1]? = some outerFrame ∧
      truth2[1]? = some outerSt ∧ SkippedBelow [innerFrameBad, outerFrame] 1 ∧
      frameAction outerFrame = .handle 7 ∧ BaseSafeUpTo [innerFrameBad, outerFrame] 1 ∧
      SlotsPreservedBelow [innerFrameBad, outerFrame] truth2 innerSt.mem 1 ∧
      ¬ CaughtWithCallerState [innerFrameBad, outerFrame] truth2 topCaller innerSt 1 7 outerFrame
        outerSt := by
  refine ⟨chain_inner_outer _ _ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩, fun h => ?_, rfl, rfl, rfl,
    skippedBelow_one rfl, by decide, baseSafeUpTo_one outerFrame_baseSafe,
    slotsPreservedBelow_one _ _ _, ?_⟩
  · exact not_tableCorrect_of_bad_row (innerFn_reach_call topCaller topMem) (pc := 2) (by decide)
      (R := initRow) (by decide) (by decide) (h 0 innerFrameBad (Nat.zero_le _) rfl)
  · rintro ⟨st, -, hrun, hag, -⟩
    have : unwind [innerFrameBad, outerFrame] innerSt = .caught 1 7 (unwindRegs initRow innerSt) :=
      rfl
    rw [this] at hrun
    cases hrun
    have := hag.1
    revert this
    decide

/-- The inner frame with an empty call-site table: its call PC is not found and
the toy personality terminates. -/
def innerFrameTerm : Frame := { innerFrame with lsda := some [] }

theorem multiFrame_fails_without_skippedBelow :
    ChainUpTo [innerFrameTerm, outerFrame] truth2 topCaller 1 ∧
      TablesUpTo [innerFrameTerm, outerFrame] 1 ∧
      truth2[0]? = some innerSt ∧ [innerFrameTerm, outerFrame][1]? = some outerFrame ∧
      truth2[1]? = some outerSt ∧ ¬ SkippedBelow [innerFrameTerm, outerFrame] 1 ∧
      frameAction outerFrame = .handle 7 ∧ BaseSafeUpTo [innerFrameTerm, outerFrame] 1 ∧
      SlotsPreservedBelow [innerFrameTerm, outerFrame] truth2 innerSt.mem 1 ∧
      ¬ CaughtWithCallerState [innerFrameTerm, outerFrame] truth2 topCaller innerSt 1 7 outerFrame
        outerSt := by
  refine ⟨chain_inner_outer _ _ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩, tablesUpTo_of_all ?_, rfl, rfl, rfl,
    fun h => ?_, by decide, baseSafeUpTo_one outerFrame_baseSafe, slotsPreservedBelow_one _ _ _, ?_⟩
  · intro fr h
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact innerFn_tableCorrect
    · exact outerFn_tableCorrect
  · have := h 0 innerFrameTerm Nat.zero_lt_one rfl
    revert this; decide
  · rintro ⟨st, -, hrun, -⟩
    have : unwind [innerFrameTerm, outerFrame] innerSt = .terminated 0 := rfl
    rw [this] at hrun
    cases hrun

/-- The outer frame without a call-site table: it is skipped too. -/
def outerFrameNoLsda : Frame := { outerFrame with lsda := none }

theorem multiFrame_fails_without_handler :
    ChainUpTo [innerFrame, outerFrameNoLsda] truth2 topCaller 1 ∧
      TablesUpTo [innerFrame, outerFrameNoLsda] 1 ∧
      truth2[0]? = some innerSt ∧ [innerFrame, outerFrameNoLsda][1]? = some outerFrameNoLsda ∧
      truth2[1]? = some outerSt ∧ SkippedBelow [innerFrame, outerFrameNoLsda] 1 ∧
      frameAction outerFrameNoLsda ≠ .handle 7 ∧ BaseSafeUpTo [innerFrame, outerFrameNoLsda] 1 ∧
      SlotsPreservedBelow [innerFrame, outerFrameNoLsda] truth2 innerSt.mem 1 ∧
      ¬ CaughtWithCallerState [innerFrame, outerFrameNoLsda] truth2 topCaller innerSt 1 7
        outerFrameNoLsda outerSt := by
  refine ⟨chain_inner_outer _ _ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩, tablesUpTo_of_all ?_, rfl, rfl, rfl,
    skippedBelow_one rfl, by decide, baseSafeUpTo_one outerFrame_baseSafe,
    slotsPreservedBelow_one _ _ _, ?_⟩
  · intro fr h
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact innerFn_tableCorrect
    · exact outerFn_tableCorrect
  · rintro ⟨st, -, hrun, -⟩
    have : unwind [innerFrame, outerFrameNoLsda] innerSt = .escaped := rfl
    rw [this] at hrun
    cases hrun

/-! ### Scratch-register CFA base -/

def innerT1Frame : Frame :=
  { fn := innerT1Fn, prog := genCFI innerT1Fn (inferredAnn innerT1Fn), lsda := none, callPC := 3,
    frameSize := 1 }
def outerT1Frame : Frame :=
  { fn := outerT1Fn, prog := outerT1CFI, lsda := some [⟨2, 3, some 7⟩], callPC := 2,
    frameSize := 2 }

def outerT1St : MState :=
  step (step (entryState topCaller topMem) (.movReg .t1 .sp)) (.subSp 2)
def innerT1St : MState :=
  step (step (step (entryState (ctxOf outerT1St) outerT1St.mem) (.push .fp)) (.movReg .fp .sp))
    (.movReg .t1 .sp)

theorem chainT1 : ChainReachable [innerT1Frame, outerT1Frame] [innerT1St, outerT1St] topCaller := by
  refine ⟨rfl, fun j fr st hf ht => ?_⟩
  match j, hf, ht with
  | 0, hf, ht =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hf ht
    subst hf; subst ht
    exact ⟨outerT1St.mem, 0, 3, by decide, rfl,
      Reach.next (Reach.next (Reach.next (Reach.entry (by decide)) rfl (by decide)) rfl
        (by decide)) rfl (by decide)⟩
  | 1, hf, ht =>
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hf ht
    subst hf; subst ht
    exact ⟨topMem, 0, 2, by decide, rfl,
      Reach.next (Reach.next (Reach.entry (by decide)) rfl (by decide)) rfl (by decide)⟩
  | j + 2, hf, _ => simp at hf

/-- Tightness of the CFA-base condition: the outer frame anchors its CFA in the
scratch register `t1`, which the inner frame overwrites (and, `t1` not being
callee-saved, need not recover); the outer frame's computed frame base is
wrong. -/
theorem multiFrame_fails_without_baseSafeUpTo :
    ChainUpTo [innerT1Frame, outerT1Frame] [innerT1St, outerT1St] topCaller 1 ∧
      TablesUpTo [innerT1Frame, outerT1Frame] 1 ∧
      [innerT1St, outerT1St][0]? = some innerT1St ∧
      [innerT1Frame, outerT1Frame][1]? = some outerT1Frame ∧
      [innerT1St, outerT1St][1]? = some outerT1St ∧ SkippedBelow [innerT1Frame, outerT1Frame] 1 ∧
      frameAction outerT1Frame = .handle 7 ∧ ¬ BaseSafeUpTo [innerT1Frame, outerT1Frame] 1 ∧
      SlotsPreservedBelow [innerT1Frame, outerT1Frame] [innerT1St, outerT1St] innerT1St.mem 1 ∧
      ¬ CaughtWithCallerState [innerT1Frame, outerT1Frame] [innerT1St, outerT1St] topCaller innerT1St
        1 7 outerT1Frame outerT1St := by
  refine ⟨chainT1.upTo 1, tablesUpTo_of_all ?_, rfl, rfl, rfl, skippedBelow_one rfl, by decide,
    fun h => ?_, slotsPreservedBelow_one _ _ _, ?_⟩
  · intro fr h
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact innerT1Fn_tableCorrect
    · exact outerT1Fn_tableCorrect
  · have := h 1 outerT1Frame ⟨.t1, 0, RegFile.const .same⟩ Nat.one_pos (Nat.le_refl _) rfl
      (by decide)
    simp [CfaBaseSafe, calleeSaved] at this
  · rintro ⟨st, R, hrun, -, -, hRj, -, hfb⟩
    have hR : rowAt? innerT1Frame.prog innerT1Frame.callPC =
        some ⟨.fp, 1, ⟨.same, .offset (-1), .same, .same⟩⟩ := by decide
    have : unwind [innerT1Frame, outerT1Frame] innerT1St =
        .caught 1 7 (unwindRegs ⟨.fp, 1, ⟨.same, .offset (-1), .same, .same⟩⟩ innerT1St) := by
      simp only [unwind, unwindFrom, hR]; rfl
    rw [this] at hrun
    cases hrun
    have hRo : rowAt? outerT1Frame.prog outerT1Frame.callPC = some ⟨.t1, 0, RegFile.const .same⟩ := by
      decide
    rw [hRo] at hRj
    cases hRj
    revert hfb
    decide

/-! ### Clobbered save slot (three frames) -/

def middleFrame : Frame := { innerFrame with lsda := none }
def clobberFrame : Frame :=
  { fn := clobberFn, prog := genCFI clobberFn (inferredAnn clobberFn), lsda := none, callPC := 1,
    frameSize := 0 }

/-- True state of the middle frame (the inner function called from `outerSt`). -/
def middleSt : MState := innerSt
/-- True state of the innermost frame: it stored `t1` at its CFA, which is the
middle frame's save slot for `fp`. -/
def clobberSt : MState := step (entryState (ctxOf middleSt) middleSt.mem) (.saveAt .t1 0)

def frames3 : List Frame := [clobberFrame, middleFrame, outerFrame]
def truth3 : List MState := [clobberSt, middleSt, outerSt]

theorem chain3 : ChainReachable frames3 truth3 topCaller := by
  refine ⟨rfl, fun j fr st hf ht => ?_⟩
  match j, hf, ht with
  | 0, hf, ht =>
    simp only [frames3, truth3, List.getElem?_cons_zero, Option.some.injEq] at hf ht
    subst hf; subst ht
    exact ⟨middleSt.mem, 0, 1, by decide, rfl, Reach.next (Reach.entry (by decide)) rfl (by decide)⟩
  | 1, hf, ht =>
    simp only [frames3, truth3, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.some.injEq] at hf ht
    subst hf; subst ht
    exact ⟨outerSt.mem, 0, 2, by decide, rfl, innerFn_reach_call _ _⟩
  | 2, hf, ht =>
    simp only [frames3, truth3, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.some.injEq] at hf ht
    subst hf; subst ht
    exact ⟨topMem, 0, 1, by decide, rfl, outerFn_reach_call _ _⟩
  | j + 3, hf, _ => simp [frames3] at hf

theorem middleFrame_row : rowAt? middleFrame.prog middleFrame.callPC =
    some ⟨.fp, 1, ⟨.same, .offset (-1), .same, .same⟩⟩ := by decide

/-- Tightness of save-slot preservation: the innermost frame overwrites the middle
frame's saved `fp`; every other hypothesis holds (`j = 2`), but the
reconstructed outer `fp` is wrong. -/
theorem multiFrame_fails_without_slotsPreservedBelow :
    ChainUpTo frames3 truth3 topCaller 2 ∧ TablesUpTo frames3 2 ∧
      truth3[0]? = some clobberSt ∧ frames3[2]? = some outerFrame ∧ truth3[2]? = some outerSt ∧
      SkippedBelow frames3 2 ∧ frameAction outerFrame = .handle 7 ∧ BaseSafeUpTo frames3 2 ∧
      ¬ SlotsPreservedBelow frames3 truth3 clobberSt.mem 2 ∧
      ¬ CaughtWithCallerState frames3 truth3 topCaller clobberSt 2 7 outerFrame outerSt := by
  refine ⟨chain3.upTo 2, tablesUpTo_of_all ?_, rfl, rfl, rfl, ?_, by decide, ?_, fun h => ?_, ?_⟩
  · intro fr h
    simp only [frames3, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · exact clobberFn_tableCorrect
    · exact innerFn_tableCorrect
    · exact outerFn_tableCorrect
  · intro i fr hi hf
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · simp only [frames3, List.getElem?_cons_zero, Option.some.injEq] at hf; subst hf; rfl
    · simp only [frames3, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq] at hf
      subst hf; rfl
  · intro i fr R hi hi2 hf hR
    obtain rfl | rfl : i = 1 ∨ i = 2 := by omega
    · simp only [frames3, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq] at hf
      subst hf
      rw [middleFrame_row] at hR; cases hR
      exact Or.inr (by decide)
    · simp only [frames3, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq] at hf
      subst hf
      exact outerFrame_baseSafe R hR
  · have := h 1 middleFrame middleSt _ Nat.one_pos (by omega) rfl rfl middleFrame_row .fp
      (by decide) (-1) rfl
    revert this
    decide
  · rintro ⟨st, -, hrun, hag, -⟩
    have h0 : rowAt? clobberFrame.prog clobberFrame.callPC = some initRow := by decide
    have : unwind frames3 clobberSt = .caught 2 7 (unwindRegs
        ⟨.fp, 1, ⟨.same, .offset (-1), .same, .same⟩⟩ (unwindRegs initRow clobberSt)) := by
      simp only [unwind, frames3, unwindFrom, h0, middleFrame_row]; rfl
    rw [this] at hrun
    cases hrun
    have := hag.2 .fp (by decide)
    revert this
    decide

/-! ### Unreachable "true" state -/

/-- `innerSt` with `fp` replaced by `900`: not a reachable state of `innerFn`. -/
def innerStBad : MState := { innerSt with regs := innerSt.regs.set .fp 900 }

theorem innerFn_pcOf_eq_two {b k : Nat} (h : innerFn.pcOf b k = some 2) : b = 0 ∧ k = 2 := by
  cases b with
  | zero =>
    simp [Func.pcOf, Func.blockStart, Func.startIn, innerFn] at h
    exact ⟨rfl, h⟩
  | succ n => simp [Func.pcOf, Func.blockStart, Func.startIn, innerFn] at h

/-- Tightness of the chain hypothesis: with an unreachable innermost "true"
state, every other hypothesis holds but the reconstructed outer `sp` is wrong. -/
theorem multiFrame_fails_without_chainUpTo :
    ¬ ChainUpTo frames2 [innerStBad, outerSt] topCaller 1 ∧ TablesUpTo frames2 1 ∧
      [innerStBad, outerSt][0]? = some innerStBad ∧ frames2[1]? = some outerFrame ∧
      [innerStBad, outerSt][1]? = some outerSt ∧ SkippedBelow frames2 1 ∧
      frameAction outerFrame = .handle 7 ∧ BaseSafeUpTo frames2 1 ∧
      SlotsPreservedBelow frames2 [innerStBad, outerSt] innerStBad.mem 1 ∧
      ¬ CaughtWithCallerState frames2 [innerStBad, outerSt] topCaller innerStBad 1 7 outerFrame
        outerSt := by
  refine ⟨fun h => ?_, tablesUpTo_of_all frames2_tables, rfl, rfl, rfl, skippedBelow_one rfl,
    by decide, baseSafeUpTo_one outerFrame_baseSafe, slotsPreservedBelow_one _ _ _, ?_⟩
  · obtain ⟨m, b, k, hpc, -, hr⟩ := h 0 innerFrame innerStBad (Nat.zero_le _) rfl rfl
    obtain ⟨rfl, rfl⟩ := innerFn_pcOf_eq_two hpc
    obtain ⟨A, hA, hinv⟩ := reach_inv_inferred (f := innerFn) (by decide) hr
    have hA' : inferredAnn innerFn 0 = some absInit := by decide
    rw [hA'] at hA
    cases hA
    have := hinv.1 .fp
    have e : (absAt innerFn absInit 0 2).regs.get .fp = .cfaRel (-1) := by decide
    rw [e] at this
    simp only [SymHolds] at this
    revert this
    decide
  · rintro ⟨st, -, hrun, hag, -⟩
    have hR : rowAt? innerFrame.prog innerFrame.callPC =
        some ⟨.fp, 1, ⟨.same, .offset (-1), .same, .same⟩⟩ := by decide
    have : unwind frames2 innerStBad =
        .caught 1 7 (unwindRegs ⟨.fp, 1, ⟨.same, .offset (-1), .same, .same⟩⟩ innerStBad) := by
      simp only [unwind, frames2, unwindFrom, hR]; rfl
    rw [this] at hrun
    cases hrun
    have := hag.1
    revert this
    decide

/-! ### Object-naming hypotheses carry substance -/

/-- Tightness of `hj : frames[j]? = some frj` (it carries `j < frames.length`):
with no frames every other hypothesis holds (vacuously or concretely) and
unwinding escapes. -/
theorem multiFrame_fails_without_hj :
    ChainUpTo [] truth2 topCaller 1 ∧ TablesUpTo [] 1 ∧
      truth2[0]? = some innerSt ∧ ([] : List Frame)[1]? ≠ some outerFrame ∧
      truth2[1]? = some outerSt ∧ SkippedBelow [] 1 ∧
      frameAction outerFrame = .handle 7 ∧ BaseSafeUpTo [] 1 ∧
      SlotsPreservedBelow [] truth2 innerSt.mem 1 ∧
      ¬ CaughtWithCallerState [] truth2 topCaller innerSt 1 7 outerFrame outerSt := by
  refine ⟨fun _ _ _ _ hf => by simp at hf, fun _ _ _ hf => by simp at hf, rfl, by simp, rfl,
    fun _ _ _ hf => by simp at hf, by decide, fun _ _ _ _ _ hf => by simp at hf,
    fun _ _ _ _ _ _ hf => by simp at hf, ?_⟩
  rintro ⟨st, -, hrun, -⟩
  simp [unwind, unwindFrom] at hrun

/-- Tightness of `htj : truth[j]? = some stj` (it carries `j < truth.length`):
with a one-element truth list, `ChainUpTo` no longer constrains frame `1` and
`callerCtx` falls back to the context of the outer frame's state; every other
hypothesis holds for an arbitrary `stj` (here `innerStBad`), and the
reconstructed state does not agree with it. -/
theorem multiFrame_fails_without_htj :
    ChainUpTo frames2 [innerSt] (ctxOf outerSt) 1 ∧ TablesUpTo frames2 1 ∧
      [innerSt][0]? = some innerSt ∧ frames2[1]? = some outerFrame ∧
      ([innerSt][1]? : Option MState) ≠ some innerStBad ∧ SkippedBelow frames2 1 ∧
      frameAction outerFrame = .handle 7 ∧ BaseSafeUpTo frames2 1 ∧
      SlotsPreservedBelow frames2 [innerSt] innerSt.mem 1 ∧
      ¬ CaughtWithCallerState frames2 [innerSt] (ctxOf outerSt) innerSt 1 7 outerFrame innerStBad := by
  refine ⟨?_, tablesUpTo_of_all frames2_tables, rfl, rfl, by simp,
    skippedBelow_one rfl, by decide, baseSafeUpTo_one outerFrame_baseSafe,
    slotsPreservedBelow_one _ _ _, ?_⟩
  · intro i fr st hi hf ht
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · simp only [frames2, List.getElem?_cons_zero, Option.some.injEq] at hf ht
      subst hf; subst ht
      exact ⟨outerSt.mem, 0, 2, by decide, rfl, innerFn_reach_call _ _⟩
    · simp at ht
  · rintro ⟨st, -, hrun, hag, -⟩
    have hR : rowAt? innerFrame.prog innerFrame.callPC =
        some ⟨.fp, 1, ⟨.same, .offset (-1), .same, .same⟩⟩ := by decide
    have : unwind frames2 innerSt =
        .caught 1 7 (unwindRegs ⟨.fp, 1, ⟨.same, .offset (-1), .same, .same⟩⟩ innerSt) := by
      simp only [unwind, frames2, unwindFrom, hR]; rfl
    rw [this] at hrun; cases hrun
    have := hag.2 .fp (by decide)
    revert this; decide

/-- Tightness of `h0 : truth[0]? = some st0` (it ties the starting state to
frame `0`'s true state): starting from `innerStBad` instead of `truth2[0]`,
every other hypothesis holds and the reconstructed `sp` is wrong. -/
theorem multiFrame_fails_without_h0 :
    ChainUpTo frames2 truth2 topCaller 1 ∧ TablesUpTo frames2 1 ∧
      truth2[0]? ≠ some innerStBad ∧ frames2[1]? = some outerFrame ∧
      truth2[1]? = some outerSt ∧ SkippedBelow frames2 1 ∧
      frameAction outerFrame = .handle 7 ∧ BaseSafeUpTo frames2 1 ∧
      SlotsPreservedBelow frames2 truth2 innerStBad.mem 1 ∧
      ¬ CaughtWithCallerState frames2 truth2 topCaller innerStBad 1 7 outerFrame outerSt := by
  refine ⟨chain2.upTo 1, tablesUpTo_of_all frames2_tables, ?_, rfl, rfl,
    skippedBelow_one rfl, by decide, baseSafeUpTo_one outerFrame_baseSafe,
    slotsPreservedBelow_one _ _ _, ?_⟩
  · intro h
    simp only [truth2, List.getElem?_cons_zero, Option.some.injEq] at h
    have := congrArg (fun s : MState => s.regs.get .fp) h
    revert this; decide
  · rintro ⟨st, -, hrun, hag, -⟩
    have hR : rowAt? innerFrame.prog innerFrame.callPC =
        some ⟨.fp, 1, ⟨.same, .offset (-1), .same, .same⟩⟩ := by decide
    have : unwind frames2 innerStBad =
        .caught 1 7 (unwindRegs ⟨.fp, 1, ⟨.same, .offset (-1), .same, .same⟩⟩ innerStBad) := by
      simp only [unwind, frames2, unwindFrom, hR]; rfl
    rw [this] at hrun; cases hrun
    have := hag.1
    revert this; decide

/-! ### The conclusion requires a row at the handler frame's call site -/

/-- The outer frame with a malformed program (`restoreState` on an empty
stack): it has no row at its call site. -/
def outerFrameMalformed : Frame := { outerFrame with prog := [.restoreState] }

/-- `CaughtWithCallerState` examples: it holds for the two-frame witness, and it
fails when the handler frame's program has no row at its call site, even though
unwinding itself reports `caught 1 7` there (the personality routine does not
consult the handler frame's row). -/
theorem caughtWithCallerState_examples :
    CaughtWithCallerState frames2 truth2 topCaller innerSt 1 7 outerFrame outerSt ∧
      rowAt? outerFrameMalformed.prog outerFrameMalformed.callPC = none ∧
      (∃ st, unwind [innerFrame, outerFrameMalformed] innerSt = .caught 1 7 st) ∧
      ¬ CaughtWithCallerState [innerFrame, outerFrameMalformed] truth2 topCaller innerSt 1 7
        outerFrameMalformed outerSt := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := multiFrame_hypotheses_hold
  refine ⟨unwind_caught_at_first_handler_frame_with_caller_registers _ _ _ _ _ _ _ _
      h1 h2 h3 h4 h5 h6 h7 h8 h9, by decide, ?_, ?_⟩
  · have hR : rowAt? innerFrame.prog innerFrame.callPC =
        some ⟨.fp, 1, ⟨.same, .offset (-1), .same, .same⟩⟩ := by decide
    exact ⟨_, by simp only [unwind, unwindFrom, hR]; rfl⟩
  · rintro ⟨_, R, _, _, _, hR, _, _⟩
    have hnone : rowAt? outerFrameMalformed.prog outerFrameMalformed.callPC = none := by decide
    rw [hnone] at hR; cases hR

/-! ### Declarative call-site tables: witness and counterexamples -/

theorem lsdaWellFormedUpTo_of_forall {frames : List Frame} {j : Nat}
    (h : ∀ fr ∈ frames, fr.lsda = none ∨ ∃ e, fr.lsda = some [e]) : LsdaWellFormedUpTo frames j := by
  intro _ fr t _ hf ht
  rcases h fr (List.mem_of_getElem? hf) with hn | ⟨e, he⟩
  · rw [hn] at ht; cases ht
  · rw [he] at ht; cases ht
    refine ⟨by simp [SortedByStart], fun e₁ h1 e₂ h2 _ _ => ?_⟩
    simp at h1 h2; rw [h1, h2]

theorem declarativeSkippedBelow_one {a : Frame} {rest : List Frame} (h : a.lsda = none) :
    DeclarativeSkippedBelow (a :: rest) 1 := by
  intro i fr hi hf
  obtain rfl : i = 0 := by omega
  simp only [List.getElem?_cons_zero, Option.some.injEq] at hf
  subst hf; exact Or.inl h

theorem declarativeCatch_outerFrame : DeclarativeCatch outerFrame 7 :=
  ⟨_, ⟨1, 2, some 7⟩, rfl, by simp, by decide, rfl⟩

theorem lsdaWellFormed_frames2 : LsdaWellFormedUpTo frames2 1 :=
  lsdaWellFormedUpTo_of_forall (by
    intro fr h
    simp only [frames2, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr ⟨_, rfl⟩)

/-- **Non-vacuity** of the declarative composition theorem: the two-frame chain
satisfies all of its hypotheses with `j = 1`. -/
theorem multiFrame_declarative_hypotheses_hold :
    ChainUpTo frames2 truth2 topCaller 1 ∧ TablesUpTo frames2 1 ∧ LsdaWellFormedUpTo frames2 1 ∧
      truth2[0]? = some innerSt ∧ frames2[1]? = some outerFrame ∧ truth2[1]? = some outerSt ∧
      DeclarativeSkippedBelow frames2 1 ∧ DeclarativeCatch outerFrame 7 ∧
      BaseSafeUpTo frames2 1 ∧ SlotsPreservedBelow frames2 truth2 innerSt.mem 1 :=
  ⟨chain_inner_outer _ _ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩, tablesUpTo_of_all frames2_tables,
    lsdaWellFormed_frames2, rfl, rfl, rfl, declarativeSkippedBelow_one rfl,
    declarativeCatch_outerFrame, baseSafeUpTo_one outerFrame_baseSafe,
    slotsPreservedBelow_one _ _ _⟩

/-- The outer frame with an unsorted table whose second entry covers the call
PC with landing pad `7`. -/
def outerFrameUnsorted : Frame :=
  { outerFrame with lsda := some [⟨10, 20, some 1⟩, ⟨1, 2, some 7⟩] }

/-- Tightness of `LsdaWellFormedUpTo`: the outer frame's table is unsorted; it
has an entry covering the call PC with landing pad `7`, so the declarative
catch condition holds, but the early-exit scan stops at the first entry and the
personality routine terminates. -/
theorem multiFrameDecl_fails_without_lsdaWellFormed :
    ChainUpTo [innerFrame, outerFrameUnsorted] truth2 topCaller 1 ∧
      TablesUpTo [innerFrame, outerFrameUnsorted] 1 ∧
      ¬ LsdaWellFormedUpTo [innerFrame, outerFrameUnsorted] 1 ∧
      truth2[0]? = some innerSt ∧ [innerFrame, outerFrameUnsorted][1]? = some outerFrameUnsorted ∧
      truth2[1]? = some outerSt ∧ DeclarativeSkippedBelow [innerFrame, outerFrameUnsorted] 1 ∧
      DeclarativeCatch outerFrameUnsorted 7 ∧ BaseSafeUpTo [innerFrame, outerFrameUnsorted] 1 ∧
      SlotsPreservedBelow [innerFrame, outerFrameUnsorted] truth2 innerSt.mem 1 ∧
      ¬ CaughtWithCallerState [innerFrame, outerFrameUnsorted] truth2 topCaller innerSt 1 7
        outerFrameUnsorted outerSt := by
  refine ⟨chain_inner_outer _ _ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩, tablesUpTo_of_all ?_, fun h => ?_, rfl, rfl,
    rfl, declarativeSkippedBelow_one rfl, ⟨_, ⟨1, 2, some 7⟩, rfl, by simp, by decide, rfl⟩,
    baseSafeUpTo_one outerFrame_baseSafe, slotsPreservedBelow_one _ _ _, ?_⟩
  · intro fr h
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact innerFn_tableCorrect
    · exact outerFn_tableCorrect
  · have := (h 1 outerFrameUnsorted _ (Nat.le_refl _) rfl rfl).1
    simp [SortedByStart] at this
  · rintro ⟨st, -, hrun, -⟩
    have hR : rowAt? innerFrame.prog innerFrame.callPC =
        some ⟨.fp, 1, ⟨.same, .offset (-1), .same, .same⟩⟩ := by decide
    have : unwind [innerFrame, outerFrameUnsorted] innerSt = .terminated 1 := by
      simp only [unwind, unwindFrom, hR]; rfl
    rw [this] at hrun; cases hrun

/-- Tightness of `DeclarativeSkippedBelow`: the inner frame has an empty table
(no entry covers its call PC); every other hypothesis holds and the personality
routine terminates at depth 0. -/
theorem multiFrameDecl_fails_without_declarativeSkippedBelow :
    ChainUpTo [innerFrameTerm, outerFrame] truth2 topCaller 1 ∧
      TablesUpTo [innerFrameTerm, outerFrame] 1 ∧ LsdaWellFormedUpTo [innerFrameTerm, outerFrame] 1 ∧
      truth2[0]? = some innerSt ∧ [innerFrameTerm, outerFrame][1]? = some outerFrame ∧
      truth2[1]? = some outerSt ∧ ¬ DeclarativeSkippedBelow [innerFrameTerm, outerFrame] 1 ∧
      DeclarativeCatch outerFrame 7 ∧ BaseSafeUpTo [innerFrameTerm, outerFrame] 1 ∧
      SlotsPreservedBelow [innerFrameTerm, outerFrame] truth2 innerSt.mem 1 ∧
      ¬ CaughtWithCallerState [innerFrameTerm, outerFrame] truth2 topCaller innerSt 1 7 outerFrame
        outerSt := by
  obtain ⟨a1, a2, a3, a4, a5, -, -, a8, a9, a10⟩ := multiFrame_fails_without_skippedBelow
  refine ⟨a1, a2, ?_, a3, a4, a5, fun h => ?_, declarativeCatch_outerFrame, a8, a9, a10⟩
  · intro i fr t _ hf ht
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hf
      subst hf; simp only [innerFrameTerm, Option.some.injEq] at ht; subst ht
      exact ⟨List.Pairwise.nil, fun _ h => by cases h⟩
    · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hf
      subst hf; simp only [outerFrame, Option.some.injEq] at ht; subst ht
      refine ⟨by simp [SortedByStart], fun e₁ h1 e₂ h2 _ _ => ?_⟩
      simp at h1 h2; rw [h1, h2]
  · rcases h 0 innerFrameTerm Nat.zero_lt_one rfl with hn | ⟨t, e, ht, he, -, -⟩
    · cases hn
    · simp only [innerFrameTerm, Option.some.injEq] at ht; subst ht; cases he

/-- Tightness of `DeclarativeCatch`: the outer frame has no table; every other
hypothesis holds and unwinding escapes. -/
theorem multiFrameDecl_fails_without_declarativeCatch :
    ChainUpTo [innerFrame, outerFrameNoLsda] truth2 topCaller 1 ∧
      TablesUpTo [innerFrame, outerFrameNoLsda] 1 ∧
      LsdaWellFormedUpTo [innerFrame, outerFrameNoLsda] 1 ∧
      truth2[0]? = some innerSt ∧ [innerFrame, outerFrameNoLsda][1]? = some outerFrameNoLsda ∧
      truth2[1]? = some outerSt ∧ DeclarativeSkippedBelow [innerFrame, outerFrameNoLsda] 1 ∧
      ¬ DeclarativeCatch outerFrameNoLsda 7 ∧ BaseSafeUpTo [innerFrame, outerFrameNoLsda] 1 ∧
      SlotsPreservedBelow [innerFrame, outerFrameNoLsda] truth2 innerSt.mem 1 ∧
      ¬ CaughtWithCallerState [innerFrame, outerFrameNoLsda] truth2 topCaller innerSt 1 7
        outerFrameNoLsda outerSt := by
  obtain ⟨a1, a2, a3, a4, a5, -, -, a8, a9, a10⟩ := multiFrame_fails_without_handler
  refine ⟨a1, a2, lsdaWellFormedUpTo_of_forall ?_, a3, a4, a5, declarativeSkippedBelow_one rfl,
    ?_, a8, a9, a10⟩
  · intro fr h
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> exact Or.inl rfl
  · rintro ⟨t, e, ht, -⟩; cases ht

/-- Tightness of `ChainUpTo` for the declarative theorem (same instance as for
the operational one). -/
theorem multiFrameDecl_fails_without_chainUpTo :
    ¬ ChainUpTo frames2 [innerStBad, outerSt] topCaller 1 ∧ TablesUpTo frames2 1 ∧
      LsdaWellFormedUpTo frames2 1 ∧
      [innerStBad, outerSt][0]? = some innerStBad ∧ frames2[1]? = some outerFrame ∧
      [innerStBad, outerSt][1]? = some outerSt ∧ DeclarativeSkippedBelow frames2 1 ∧
      DeclarativeCatch outerFrame 7 ∧ BaseSafeUpTo frames2 1 ∧
      SlotsPreservedBelow frames2 [innerStBad, outerSt] innerStBad.mem 1 ∧
      ¬ CaughtWithCallerState frames2 [innerStBad, outerSt] topCaller innerStBad 1 7 outerFrame
        outerSt := by
  obtain ⟨a1, a2, a3, a4, a5, -, -, a8, a9, a10⟩ := multiFrame_fails_without_chainUpTo
  exact ⟨a1, a2, lsdaWellFormed_frames2, a3, a4, a5, declarativeSkippedBelow_one rfl,
    declarativeCatch_outerFrame, a8, a9, a10⟩

/-- Tightness of `TablesUpTo` for the declarative theorem. -/
theorem multiFrameDecl_fails_without_tablesUpTo :
    ChainUpTo [innerFrameBad, outerFrame] truth2 topCaller 1 ∧
      ¬ TablesUpTo [innerFrameBad, outerFrame] 1 ∧ LsdaWellFormedUpTo [innerFrameBad, outerFrame] 1 ∧
      truth2[0]? = some innerSt ∧ [innerFrameBad, outerFrame][1]? = some outerFrame ∧
      truth2[1]? = some outerSt ∧ DeclarativeSkippedBelow [innerFrameBad, outerFrame] 1 ∧
      DeclarativeCatch outerFrame 7 ∧ BaseSafeUpTo [innerFrameBad, outerFrame] 1 ∧
      SlotsPreservedBelow [innerFrameBad, outerFrame] truth2 innerSt.mem 1 ∧
      ¬ CaughtWithCallerState [innerFrameBad, outerFrame] truth2 topCaller innerSt 1 7 outerFrame
        outerSt := by
  obtain ⟨a1, a2, a3, a4, a5, -, -, a8, a9, a10⟩ := multiFrame_fails_without_tablesUpTo
  refine ⟨a1, a2, lsdaWellFormedUpTo_of_forall ?_, a3, a4, a5, declarativeSkippedBelow_one rfl,
    declarativeCatch_outerFrame, a8, a9, a10⟩
  intro fr h
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr ⟨_, rfl⟩

/-- Tightness of `h0` for the declarative theorem. -/
theorem multiFrameDecl_fails_without_h0 :
    ChainUpTo frames2 truth2 topCaller 1 ∧ TablesUpTo frames2 1 ∧ LsdaWellFormedUpTo frames2 1 ∧
      truth2[0]? ≠ some innerStBad ∧ frames2[1]? = some outerFrame ∧
      truth2[1]? = some outerSt ∧ DeclarativeSkippedBelow frames2 1 ∧
      DeclarativeCatch outerFrame 7 ∧ BaseSafeUpTo frames2 1 ∧
      SlotsPreservedBelow frames2 truth2 innerStBad.mem 1 ∧
      ¬ CaughtWithCallerState frames2 truth2 topCaller innerStBad 1 7 outerFrame outerSt := by
  obtain ⟨a1, a2, a3, a4, a5, -, -, a8, a9, a10⟩ := multiFrame_fails_without_h0
  exact ⟨a1, a2, lsdaWellFormed_frames2, a3, a4, a5, declarativeSkippedBelow_one rfl,
    declarativeCatch_outerFrame, a8, a9, a10⟩

/-- Tightness of `hj` for the declarative theorem. -/
theorem multiFrameDecl_fails_without_hj :
    ChainUpTo [] truth2 topCaller 1 ∧ TablesUpTo [] 1 ∧ LsdaWellFormedUpTo [] 1 ∧
      truth2[0]? = some innerSt ∧ ([] : List Frame)[1]? ≠ some outerFrame ∧
      truth2[1]? = some outerSt ∧ DeclarativeSkippedBelow [] 1 ∧
      DeclarativeCatch outerFrame 7 ∧ BaseSafeUpTo [] 1 ∧
      SlotsPreservedBelow [] truth2 innerSt.mem 1 ∧
      ¬ CaughtWithCallerState [] truth2 topCaller innerSt 1 7 outerFrame outerSt := by
  obtain ⟨a1, a2, a3, a4, a5, -, -, a8, a9, a10⟩ := multiFrame_fails_without_hj
  exact ⟨a1, a2, fun _ _ _ _ hf => by simp at hf, a3, a4, a5, fun _ _ _ hf => by simp at hf,
    declarativeCatch_outerFrame, a8, a9, a10⟩

/-- Tightness of `htj` for the declarative theorem. -/
theorem multiFrameDecl_fails_without_htj :
    ChainUpTo frames2 [innerSt] (ctxOf outerSt) 1 ∧ TablesUpTo frames2 1 ∧
      LsdaWellFormedUpTo frames2 1 ∧
      [innerSt][0]? = some innerSt ∧ frames2[1]? = some outerFrame ∧
      ([innerSt][1]? : Option MState) ≠ some innerStBad ∧ DeclarativeSkippedBelow frames2 1 ∧
      DeclarativeCatch outerFrame 7 ∧ BaseSafeUpTo frames2 1 ∧
      SlotsPreservedBelow frames2 [innerSt] innerSt.mem 1 ∧
      ¬ CaughtWithCallerState frames2 [innerSt] (ctxOf outerSt) innerSt 1 7 outerFrame innerStBad := by
  obtain ⟨a1, a2, a3, a4, a5, -, -, a8, a9, a10⟩ := multiFrame_fails_without_htj
  exact ⟨a1, a2, lsdaWellFormed_frames2, a3, a4, a5, declarativeSkippedBelow_one rfl,
    declarativeCatch_outerFrame, a8, a9, a10⟩

/-- Tightness of `BaseSafeUpTo` for the declarative theorem. -/
theorem multiFrameDecl_fails_without_baseSafeUpTo :
    ChainUpTo [innerT1Frame, outerT1Frame] [innerT1St, outerT1St] topCaller 1 ∧
      TablesUpTo [innerT1Frame, outerT1Frame] 1 ∧ LsdaWellFormedUpTo [innerT1Frame, outerT1Frame] 1 ∧
      [innerT1St, outerT1St][0]? = some innerT1St ∧
      [innerT1Frame, outerT1Frame][1]? = some outerT1Frame ∧
      [innerT1St, outerT1St][1]? = some outerT1St ∧
      DeclarativeSkippedBelow [innerT1Frame, outerT1Frame] 1 ∧ DeclarativeCatch outerT1Frame 7 ∧
      ¬ BaseSafeUpTo [innerT1Frame, outerT1Frame] 1 ∧
      SlotsPreservedBelow [innerT1Frame, outerT1Frame] [innerT1St, outerT1St] innerT1St.mem 1 ∧
      ¬ CaughtWithCallerState [innerT1Frame, outerT1Frame] [innerT1St, outerT1St] topCaller innerT1St
        1 7 outerT1Frame outerT1St := by
  obtain ⟨a1, a2, a3, a4, a5, -, -, a8, a9, a10⟩ := multiFrame_fails_without_baseSafeUpTo
  refine ⟨a1, a2, lsdaWellFormedUpTo_of_forall ?_, a3, a4, a5, declarativeSkippedBelow_one rfl,
    ⟨_, ⟨2, 3, some 7⟩, rfl, by simp, by decide, rfl⟩, a8, a9, a10⟩
  intro fr h
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr ⟨_, rfl⟩

/-- Tightness of `SlotsPreservedBelow` for the declarative theorem. -/
theorem multiFrameDecl_fails_without_slotsPreservedBelow :
    ChainUpTo frames3 truth3 topCaller 2 ∧ TablesUpTo frames3 2 ∧ LsdaWellFormedUpTo frames3 2 ∧
      truth3[0]? = some clobberSt ∧ frames3[2]? = some outerFrame ∧ truth3[2]? = some outerSt ∧
      DeclarativeSkippedBelow frames3 2 ∧ DeclarativeCatch outerFrame 7 ∧ BaseSafeUpTo frames3 2 ∧
      ¬ SlotsPreservedBelow frames3 truth3 clobberSt.mem 2 ∧
      ¬ CaughtWithCallerState frames3 truth3 topCaller clobberSt 2 7 outerFrame outerSt := by
  obtain ⟨a1, a2, a3, a4, a5, -, -, a8, a9, a10⟩ := multiFrame_fails_without_slotsPreservedBelow
  refine ⟨a1, a2, lsdaWellFormedUpTo_of_forall ?_, a3, a4, a5, ?_, declarativeCatch_outerFrame,
    a8, a9, a10⟩
  · intro fr h
    simp only [frames3, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inr ⟨_, rfl⟩
  · intro i fr hi hf
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · simp only [frames3, List.getElem?_cons_zero, Option.some.injEq] at hf; subst hf
      exact Or.inl rfl
    · simp only [frames3, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq] at hf
      subst hf; exact Or.inl rfl

end Toy.CFI
