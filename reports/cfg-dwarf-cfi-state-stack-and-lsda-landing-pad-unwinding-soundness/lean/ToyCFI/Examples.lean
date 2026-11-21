import ToyCFI.Generic
import ToyCFI.ProbeLoop
import ToyCFI.MultiFrameExamples
import ToyCFI.Incomplete

/-!
# Positive and negative examples for the definitions

Examples proved elsewhere are referenced in the comments next to each group.
-/

namespace Toy.CFI

/-! ## `step` -/

/-- `push fp` decrements `sp` and stores the old `fp` at the new `sp`. -/
theorem step_push_example :
    let st : MState := ⟨⟨100, 7, 0, 0⟩, fun _ => 0⟩
    (step st (.push .fp)).regs.get .sp = 99 ∧ (step st (.push .fp)).mem 99 = 7 := by decide

/-- Negative: `push` is not frame-neutral. -/
theorem step_push_moves_sp :
    let st : MState := ⟨⟨100, 7, 0, 0⟩, fun _ => 0⟩
    (step st (.push .fp)).regs.get .sp ≠ st.regs.get .sp := by decide

/-! ## `Func.pcOf` -/

theorem pcOf_cold_block_example : coldFn.pcOf 2 0 = some 6 := by decide
/-- Negative: a block absent from the layout has no address. -/
theorem pcOf_missing_block_example : coldFnMissing.pcOf 2 0 = none := by decide

/-! ## `Reach` (positive: `coldFn_reach_cold`, `probeLoopState_reach`) -/

/-- Negative: at the cold block's first PC, `sp` is never the CFA. -/
theorem not_reach_coldFn_cold_with_sp_eq_cfa (c : Caller) (m : Int → Int) (st : MState)
    (hsp : st.regs.get .sp = c.cfa) : ¬ Reach coldFn c m 2 0 st := by
  intro hr
  obtain ⟨A, hA, hinv⟩ := reach_inv_inferred coldFn_annSound hr
  rw [coldFn_inferred_cold_entry] at hA
  cases hA
  have := hinv.1 .sp
  simp only [absAt, List.take_zero, absRun, List.foldl, RegFile.get, SymHolds] at this
  simp only [RegFile.get] at hsp
  omega

/-! ## `rowAt?` -/

/-- Instructions before the first `advanceLoc` apply at address 0; those after
`advanceLoc 1` apply from address 1 on. -/
theorem rowAt_example :
    rowAt? [.defCfaOffset 2, .advanceLoc 1, .defCfaRegister .fp] 0 = some ⟨.sp, 2, RegFile.const .same⟩ ∧
      rowAt? [.defCfaOffset 2, .advanceLoc 1, .defCfaRegister .fp] 1 =
        some ⟨.fp, 2, RegFile.const .same⟩ := by decide

/-- `restoreState` restores the CFA rule as well as the register rules. -/
theorem rowAt_restoreState_restores_cfa :
    rowAt? [.defCfa .fp 1, .offset .fp (-1), .rememberState, .defCfa .sp 0, .restore .fp,
      .restoreState] 0 = some ⟨.fp, 1, ⟨.same, .offset (-1), .same, .same⟩⟩ := by decide

/-- Negative: `restoreState` on an empty stack has no row. -/
theorem rowAt_underflow_none : rowAt? [.restoreState] 0 = none := by decide

/-! ## `Recovers` -/

/-- Positive: the frame-on row recovers the caller at the cold block's first PC. -/
theorem recovers_cold_entry_example (c : Caller) (m : Int → Int) :
    Recovers ⟨.fp, 1, ⟨.same, .offset (-1), .same, .same⟩⟩ c (coldStCold c m) := by
  refine ⟨?_, fun r hr => ?_⟩
  · simp only [cfaOf, coldStCold_regs, RegFile.get]; omega
  · simp only [calleeSaved, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp [ruleVal, cfaOf, RegFile.get, coldStCold, coldSt02, step, entryState, RegFile.set,
        write]
      intro h; omega
    · simp [ruleVal, RegFile.get, coldStCold, coldSt02, step, entryState, RegFile.set]

/-- Negative: the post-epilogue row does not recover the caller there. -/
theorem not_recovers_cold_entry_initRow (c : Caller) (m : Int → Int) :
    ¬ Recovers initRow c (coldStCold c m) := by
  intro h
  have := h.1
  simp only [cfaOf, coldStCold_regs, initRow, RegFile.get] at this
  omega

/-! ## `Inv` (positive: `absInit_sound`) -/

/-- Negative: the entry abstract state rejects a state whose `sp` is not the CFA. -/
theorem not_inv_absInit_example :
    ¬ Inv absInit ⟨100, ⟨0, 0, 0, 0⟩⟩ ⟨⟨99, 0, 0, 0⟩, fun _ => 0⟩ := by
  intro h
  have := h.1 .sp
  simp [absInit, RegFile.get, SymHolds] at this

/-! ## `entails` -/

/-- The abstract state at the cold block's entry. -/
def coldEntryA : AState :=
  { regs := ⟨.cfaRel (-1), .cfaRel (-1), .callerOf .s1, .callerOf .t1⟩, slots := [(-1, .callerOf .fp)] }

theorem entails_example : entails coldEntryA ⟨.fp, 1, ⟨.same, .offset (-1), .same, .same⟩⟩ = true ∧
    entails coldEntryA ⟨.sp, 1, ⟨.same, .offset (-1), .same, .same⟩⟩ = true := by decide

/-- Negative: the post-epilogue row, and a row claiming `fp` is unchanged. -/
theorem not_entails_example : entails coldEntryA initRow = false ∧
    entails coldEntryA ⟨.fp, 1, RegFile.const .same⟩ = false := by decide

/-! ## `leqA` -/

theorem leqA_example :
    leqA coldEntryA { coldEntryA with regs := coldEntryA.regs.set .sp .unknown } = true := by decide

/-- Negative: the less precise state does not entail the more precise one. -/
theorem not_leqA_example :
    leqA { coldEntryA with regs := coldEntryA.regs.set .sp .unknown } coldEntryA = false := by decide

/-- An abstract state equivalent to `absInit` whose slot list has a shadowed
entry: the first entry for offset `-1` is `unknown`, a later one claims the
caller's `fp`.  `Inv` (through `slotAt`) ignores the later entry. -/
def shadowedInit : AState :=
  { regs := absInit.regs, slots := [(-1, .unknown), (-1, .callerOf .fp)] }

/-- `leqA` ignores shadowed entries: it is reflexive on `shadowedInit` and
`absInit` and `shadowedInit` are mutually `leqA`-related. -/
theorem leqA_shadowed_examples :
    leqA shadowedInit shadowedInit = true ∧ leqA absInit shadowedInit = true ∧
      leqA shadowedInit absInit = true := by decide

/-! ## `stateRecoverableB`, `ruleChoice` -/

/-- Positive: the cold block's entry state is recoverable (`fp` is CFA-relative,
`fp`'s caller value is saved at `CFA - 1`).  Negative: with `sp` and `fp`
unknown no register is CFA-relative. -/
theorem stateRecoverableB_examples :
    stateRecoverableB coldEntryA = true ∧
      stateRecoverableB { coldEntryA with regs := ⟨.unknown, .unknown, .callerOf .s1, .callerOf .t1⟩ }
        = false := by decide

/-- A state whose slot list shadows a stale claim: slot `-1` reads `unknown`
(first entry) although a later entry claims the caller's `fp`; the caller's
`fp` is really at `-2`. -/
def shadowedB : AState :=
  { regs := ⟨.cfaRel (-2), .cfaRel (-2), .callerOf .s1, .callerOf .t1⟩,
    slots := [(-1, .unknown), (-1, .callerOf .fp), (-2, .callerOf .fp)] }

/-- `ruleChoice` skips shadowed entries: it picks offset `-2` for `fp`, not the
stale `-1`. -/
theorem ruleChoice_shadowed_example : ruleChoice shadowedB .fp = .offset (-2) := by decide

/-- Two pushes of `fp`, a store of `t1` over the first save slot, then a frame
pointer: the caller's `fp` survives only at `CFA - 2`. -/
def shadowedClobberFn : Func :=
  { blocks := [⟨[.push .fp, .push .fp, .saveAt .t1 1, .movReg .fp .sp], [1]⟩, ⟨[.ret], []⟩],
    layout := [0, 1] }

/-- An annotation using the shadowed state `shadowedB` at block 1. -/
def shadowedAnn : Ann
  | 0 => some absInit
  | 1 => some shadowedB
  | _ => none

/-- Positive instance of generator correctness on a user-supplied annotation
with shadowed slot entries: the hypotheses hold, and the generated table (which
recovers `fp` from `CFA - 2`) is correct. -/
theorem genCFI_shadowedClobberFn_tableCorrect :
    LayoutCovers shadowedClobberFn ∧ annSoundB shadowedClobberFn shadowedAnn = true ∧
      annRecoverableB shadowedClobberFn shadowedAnn = true ∧
      rowAt? (genCFI shadowedClobberFn shadowedAnn) 4 =
        some ⟨.fp, 2, ⟨.same, .offset (-2), .same, .same⟩⟩ ∧
      TableCorrect shadowedClobberFn (genCFI shadowedClobberFn shadowedAnn) := by
  have h1 : LayoutCovers shadowedClobberFn := layoutCovers_of_layout_range (by decide)
  have h2 : annSoundB shadowedClobberFn shadowedAnn = true := by decide
  have h3 : annRecoverableB shadowedClobberFn shadowedAnn = true := by decide
  exact ⟨h1, h2, h3, by decide,
    genCFI_tableCorrect_of_sound_recoverable_annotation _ _ h1 h2 h3⟩

/-! ## `annSoundB`, `annRecoverableB`, `LayoutCovers`, `checkCFI`
(positive: `genCFI_hypotheses_hold_coldFn`; negatives: `genCFI_incorrect_without_annSound`,
`mergeFn_inferred_sound_not_recoverable`, `genCFI_incorrect_without_layoutCovers`) -/

theorem checkCFI_examples :
    checkCFI coldFn (genCFI coldFn (inferredAnn coldFn)) = true ∧
      checkCFI coldFn (naiveCFI coldFn (inferredAnn coldFn)) = false := by decide

/-- Tightness of `h : checkCFI f prog = true` in checker soundness: the naive
program for `coldFn` is rejected and is incorrect. -/
theorem checkCFI_sound_fails_without_check :
    checkCFI coldFn (naiveCFI coldFn (inferredAnn coldFn)) = false ∧
      ¬ TableCorrect coldFn (naiveCFI coldFn (inferredAnn coldFn)) :=
  ⟨checkCFI_examples.2, naiveCFI_coldFn_not_tableCorrect⟩

/-- Non-vacuity of `reach_inv_of_annSound`: both hypotheses (a sound annotation
and a reachable state) hold for `coldFn` at the cold block's entry. -/
theorem reach_inv_of_annSound_nonvacuity (c : Caller) (m : Int → Int) :
    annSoundB coldFn (inferredAnn coldFn) = true ∧ Reach coldFn c m 2 0 (coldStCold c m) :=
  ⟨coldFn_annSound, coldFn_reach_cold c m⟩

/-- Tightness of `h : Reach f c m b k st` in `reach_inv_of_annSound`: with the
sound inferred annotation of `coldFn`, a state at the entry PC whose `sp` is not
the CFA is not reachable, and it violates the annotated abstract state. -/
theorem reach_inv_fails_without_reach :
    let c : Caller := ⟨100, ⟨0, 0, 0, 0⟩⟩
    let st : MState := ⟨⟨99, 0, 0, 0⟩, fun _ => 0⟩
    annSoundB coldFn (inferredAnn coldFn) = true ∧ ¬ Reach coldFn c (fun _ => 0) 0 0 st ∧
      ¬ (∃ A, inferredAnn coldFn 0 = some A ∧ Inv (absAt coldFn A 0 0) c st) := by
  intro c st
  have hnot : ¬ (∃ A, inferredAnn coldFn 0 = some A ∧ Inv (absAt coldFn A 0 0) c st) := by
    rintro ⟨A, hA, hinv⟩
    have h0 : inferredAnn coldFn 0 = some absInit := by decide
    rw [h0] at hA; cases hA
    exact not_inv_absInit_example hinv
  exact ⟨coldFn_annSound, fun hr => hnot (reach_inv_of_annSound coldFn_annSound hr), hnot⟩

/-! ## Call-site tables -/

theorem contains_examples : (⟨0, 4, some 1⟩ : CallSite).contains 3 ∧
    ¬ (⟨0, 4, some 1⟩ : CallSite).contains 4 := by decide

theorem uniqueAt_examples : UniqueAt lsdaAdjacent 4 ∧ ¬ UniqueAt lsdaOverlap 7 :=
  ⟨uniqueAt_of_nonOverlapping lsdaAdjacent_wellFormed.2 4,
    lookupFirst_wrong_without_uniqueAt.2.2.1⟩

theorem nonOverlapping_examples : NonOverlapping lsdaAdjacent ∧ ¬ NonOverlapping lsdaOverlap := by
  refine ⟨lsdaAdjacent_wellFormed.2, fun h => ?_⟩
  exact lookupFirst_wrong_without_uniqueAt.2.2.1 (uniqueAt_of_nonOverlapping h 7)

theorem sortedByStart_examples : SortedByStart lsdaAdjacent ∧ ¬ SortedByStart lsdaUnsorted :=
  ⟨lsdaAdjacent_wellFormed.1, lookupScan_wrong_without_sorted.1⟩

/-! ## Frames -/

theorem frameAction_examples :
    frameAction outerFrame = .handle 7 ∧ frameAction innerFrame = .skip ∧
      frameAction innerFrameTerm = .terminate ∧
      frameAction { outerFrame with lsda := some [⟨1, 2, none⟩] } = .skip := by decide

theorem cfaBaseSafe_examples :
    CfaBaseSafe ⟨.sp, 2, RegFile.const .same⟩ ∧ CfaBaseSafe ⟨.fp, 1, RegFile.const .same⟩ ∧
      ¬ CfaBaseSafe ⟨.t1, 0, RegFile.const .same⟩ := by
  refine ⟨Or.inl rfl, Or.inr (by decide), ?_⟩
  simp [CfaBaseSafe, calleeSaved]

theorem agree_examples : Agree innerSt innerSt ∧ ¬ Agree innerStBad innerSt := by
  refine ⟨⟨rfl, fun _ _ => rfl⟩, fun h => ?_⟩
  have := h.2 .fp (by decide)
  revert this
  decide

/-- `SlotsPreserved`: the middle frame's slot survives when nothing overwrites
it, and is reported clobbered in the three-frame counterexample. -/
theorem slotsPreserved_examples :
    SlotsPreserved ⟨.fp, 1, ⟨.same, .offset (-1), .same, .same⟩⟩ middleSt.mem middleSt ∧
      ¬ SlotsPreserved ⟨.fp, 1, ⟨.same, .offset (-1), .same, .same⟩⟩ clobberSt.mem middleSt :=
  ⟨fun _ _ _ _ => rfl, fun h => by
    have := h .fp (by decide) (-1) rfl
    revert this
    decide⟩

end Toy.CFI
