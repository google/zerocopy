import Toy.PlaceEval.Markers

/-!
# Non-vacuity witnesses and hypothesis-tightness counterexamples

Every theorem here is fully proved.
-/

namespace Toy.PlaceEval

/-! ## Place evaluation -/

/-- Instance of `evalPlace_eq_none_iff` on both sides: one place whose evaluation fails
(disjunct (b)) and one whose evaluation succeeds. -/
theorem evalPlace_eq_none_iff_instance :
    evalPlace stEx ⟨0, [.deref, .deref]⟩ = none ∧ evalPlace stEx ⟨0, [.deref]⟩ ≠ none := by
  decide

/-- Instance of `evalPlace_deref_zeroFields` with `k = 2`. -/
theorem evalPlace_deref_zeroFields_instance :
    evalPlace stEx ⟨0, [.deref, .field 0, .field 0]⟩ = some ⟨some 0, 6⟩ := by decide

/-! ## Erasing `placeMention` -/

/-- The hypothesis of `erasePlaceMention_refinesPP` and `erasePlaceMention_equivPP_iff_slots`
holds for `pDerefUninit` at `(0, 2)`. -/
theorem erasePlaceMention_nonvacuous :
    (pDerefUninit.blk 0).stmts[2]? = some (.placeMention ⟨0, [.deref, .deref]⟩) := by decide

/-- The hypotheses of `erasePlaceMention_equivPP_of_evalPlace_reachable` hold for
`pDanglingMention 0` at `(0, 3)` under `SEx` (the place `(*p).field 0` evaluates at every
reachable state, although `p` dangles). -/
theorem erasePlaceMention_equiv_nonvacuous :
    ((pDanglingMention 0).blk 0).stmts[3]? = some (.placeMention ⟨0, [.deref, .field 0]⟩) ∧
      ∀ st, ReachableAt SEx (pDanglingMention 0) 0 3 st →
        (evalPlace st ⟨0, [.deref, .field 0]⟩).isSome = true := by
  refine ⟨by decide, fun st h => ?_⟩
  have hm := reachableAt_slots_mem (N := 8) (by decide) h
  have key : ∀ c ∈ reachCfgs (.slots sEx) (pDanglingMention 0) 8, c.lbl = 0 →
      c.rest = ((pDanglingMention 0).blk 0).stmts.drop 3 →
        (evalPlace c.st ⟨0, [.deref, .field 0]⟩).isSome = true := by decide
  exact key _ hm rfl rfl

/-- The hypotheses of `ubFree_of_ubFree_erasePlaceMention_of_evalPlace_reachable` hold for
`pDanglingMention 0` at `(0, 3)` under `SEx`. -/
theorem ubFree_erasePlaceMention_nonvacuous :
    ((pDanglingMention 0).blk 0).stmts[3]? = some (.placeMention ⟨0, [.deref, .field 0]⟩) ∧
      (∀ st, ReachableAt SEx (pDanglingMention 0) 0 3 st →
        (evalPlace st ⟨0, [.deref, .field 0]⟩).isSome = true) ∧
      UBFree SEx (deleteStmt (pDanglingMention 0) 0 3) := by
  refine ⟨erasePlaceMention_equiv_nonvacuous.1, erasePlaceMention_equiv_nonvacuous.2, ?_⟩
  intro t h
  have := (beh_slots_eq (n := 10) (o := .term []) (by decide) (by rfl) _).1 h
  cases this

/-- A one-statement program `emit 1` with one always-allocated local. -/
def pEmitL : Prog := ⟨[⟨1, 1⟩], [⟨[.emit (.use (.const (.int 1)))], .halt⟩]⟩

theorem pEmitL_beh (b : Beh) : HasBeh SEx pEmitL b ↔ b = .term [1] :=
  beh_slots_eq (n := 10) (by decide) (by rfl) b

/-- **Tightness of "the deleted statement is a `placeMention`".** In `pEmitL` the place
`⟨0, []⟩` evaluates at every reachable state of `(0, 0)`, but the statement there is an
`emit`, and deleting it is not a refinement (the trace changes). -/
theorem deleteStmt_emit_counterexample :
    (∀ st, ReachableAt SEx pEmitL 0 0 st → (evalPlace st ⟨0, []⟩).isSome = true) ∧
      ¬ RefinesPP SEx pEmitL (deleteStmt pEmitL 0 0) := by
  refine ⟨fun st h => ?_, ?_⟩
  · have hm := reachableAt_slots_mem (N := 4) (by decide) h
    have key : ∀ c ∈ reachCfgs (.slots sEx) pEmitL 4, c.lbl = 0 →
        c.rest = (pEmitL.blk 0).stmts.drop 0 → (evalPlace c.st ⟨0, []⟩).isSome = true := by
      decide
    exact key _ hm rfl rfl
  · rw [refinesPP_iff_of_beh pEmitL_beh
      (beh_slots_eq (n := 10) (o := .term []) (by decide) (by rfl))]
    exact not_improvesPP_term_term (by decide)

/-- **Tightness of `hs` for the equivalence (all other hypotheses hold, the conclusion
fails).** -/
theorem erasePlaceMention_equiv_hs_counterexample :
    (∀ st, ReachableAt SEx pEmitL 0 0 st → (evalPlace st ⟨0, []⟩).isSome = true) ∧
      ¬ EquivPP SEx pEmitL (deleteStmt pEmitL 0 0) :=
  ⟨deleteStmt_emit_counterexample.1, fun h => deleteStmt_emit_counterexample.2 h.1⟩

/-- **Tightness of `hok` (all other hypotheses hold, the conclusion fails).** -/
theorem erasePlaceMention_equiv_hok_counterexample :
    (pDerefUninit.blk 0).stmts[2]? = some (.placeMention ⟨0, [.deref, .deref]⟩) ∧
      ¬ EquivPP SEx pDerefUninit (deleteStmt pDerefUninit 0 2) :=
  ⟨erasePlaceMention_erases_place_ub.1.1, fun h => erasePlaceMention_erases_place_ub.1.2.2 h.2⟩

/-- **Tightness of `hs` for the exact condition: the biconditional fails** (the left side is
false, and the right side holds because evaluation never fails). -/
theorem erasePlaceMention_iff_hs_counterexample :
    ¬ (EquivPP SEx pEmitL (deleteStmt pEmitL 0 0) ↔
        ∀ st, ReachableAt SEx pEmitL 0 0 st → evalPlace st ⟨0, []⟩ = none →
          GoesWrongFrom SEx (deleteStmt pEmitL 0 0) ((deleteStmt pEmitL 0 0).at 0 0 st) []) := by
  intro hiff
  obtain ⟨hok, hnotref⟩ := deleteStmt_emit_counterexample
  refine hnotref (hiff.2 fun st hr hnone => ?_).1
  have hs := hok st hr
  rw [hnone] at hs
  cases hs

/-- `placeMention l0; unreachable` with `l0` always allocated. -/
def pMentionUnreach : Prog :=
  ⟨[⟨1, 1⟩], [⟨[.placeMention ⟨0, []⟩], .unreachable⟩]⟩

/-- **Tightness of `htgt` (all other hypotheses hold, the conclusion fails).** In
`pMentionUnreach` the deleted statement is a `placeMention` whose evaluation succeeds at every
reachable state, but the program is not UB-free (it reaches `unreachable`). -/
theorem ubFree_erasePlaceMention_htgt_counterexample :
    (pMentionUnreach.blk 0).stmts[0]? = some (.placeMention ⟨0, []⟩) ∧
    (∀ st, ReachableAt SEx pMentionUnreach 0 0 st → (evalPlace st ⟨0, []⟩).isSome = true) ∧
    ¬ UBFree SEx pMentionUnreach := by
  refine ⟨by decide, fun st h => ?_, ?_⟩
  · have hm := reachableAt_slots_mem (N := 4) (by decide) h
    have key : ∀ c ∈ reachCfgs (.slots sEx) pMentionUnreach 4, c.lbl = 0 →
        c.rest = (pMentionUnreach.blk 0).stmts.drop 0 →
          (evalPlace c.st ⟨0, []⟩).isSome = true := by decide
    exact key _ hm rfl rfl
  · intro h
    exact h [] ((beh_slots_eq (n := 6) (o := .wrong []) (by decide) (by rfl) _).2 rfl)

/-! ## Equal-target switches -/

/-- The hypotheses of `switchToGoto_refinesPP` and `switchToGoto_equivPP_iff_slots` hold
for `pSwUninit` at block `0`. -/
theorem switchToGoto_nonvacuous :
    (pSwUninit.blk 0).term = .switchInt (.copy ⟨0, []⟩ u8) [(0, 1)] 1 ∧
      ∀ a ∈ ([(0, 1)] : List (Nat × Label)), a.2 = 1 := by decide

/-- The hypotheses of `switchToGoto_equivPP_of_operand_reachable` hold for `pSwTag 1`. -/
theorem switchToGoto_equiv_nonvacuous :
    ((pSwTag 1).blk 0).term = .switchInt (.copy ⟨0, []⟩ bool2) [(0, 1)] 1 ∧
      (∀ a ∈ ([(0, 1)] : List (Nat × Label)), a.2 = 1) ∧
      ∀ st, ReachableAt SEx (pSwTag 1) 0 ((pSwTag 1).blk 0).stmts.length st →
        ((Operand.copy ⟨0, []⟩ bool2).evalInt st).isSome = true := by
  refine ⟨by decide, by decide, fun st h => ?_⟩
  have hm := reachableAt_slots_mem (N := 6) (by decide) h
  have key : ∀ c ∈ reachCfgs (.slots sEx) (pSwTag 1) 6, c.lbl = 0 →
      c.rest = ((pSwTag 1).blk 0).stmts.drop ((pSwTag 1).blk 0).stmts.length →
        ((Operand.copy ⟨0, []⟩ bool2).evalInt c.st).isSome = true := by decide
  exact key _ hm rfl rfl

/-- A switch whose targets differ: `x := 0; switchInt x [0 → 1] otherwise 2`, where block
`1` emits `1` and block `2` emits `2`. -/
def pSwDiff : Prog :=
  ⟨[⟨1, 1⟩],
   [⟨[.assign ⟨0, []⟩ u8 (.use (.const (.int 0)))], .switchInt (.copy ⟨0, []⟩ u8) [(0, 1)] 2⟩,
    ⟨[.emit (.use (.const (.int 1)))], .halt⟩, ⟨[.emit (.use (.const (.int 2)))], .halt⟩]⟩

theorem pSwDiff_beh (b : Beh) : HasBeh SEx pSwDiff b ↔ b = .term [1] :=
  beh_slots_eq (n := 10) (by decide) (by rfl) b
theorem pSwDiff_goto_beh (b : Beh) : HasBeh SEx (setTerm pSwDiff 0 (.goto 2)) b ↔ b = .term [2] :=
  beh_slots_eq (n := 10) (by decide) (by rfl) b

/-- **Tightness of "all arms target `b`".** In `pSwDiff` the operand evaluates at every
reachable state of the switch, but the arm `0 → 1` differs from the `otherwise` label `2`,
and replacing the switch by `goto 2` is not a refinement. -/
theorem switchToGoto_differentTargets_counterexample :
    (pSwDiff.blk 0).term = .switchInt (.copy ⟨0, []⟩ u8) [(0, 1)] 2 ∧
      (∀ st, ReachableAt SEx pSwDiff 0 (pSwDiff.blk 0).stmts.length st →
        ((Operand.copy ⟨0, []⟩ u8).evalInt st).isSome = true) ∧
      ¬ RefinesPP SEx pSwDiff (setTerm pSwDiff 0 (.goto 2)) := by
  refine ⟨by decide, fun st h => ?_, ?_⟩
  · have hm := reachableAt_slots_mem (N := 6) (by decide) h
    have key : ∀ c ∈ reachCfgs (.slots sEx) pSwDiff 6, c.lbl = 0 →
        c.rest = (pSwDiff.blk 0).stmts.drop (pSwDiff.blk 0).stmts.length →
          ((Operand.copy ⟨0, []⟩ u8).evalInt c.st).isSome = true := by decide
    exact key _ hm rfl rfl
  · rw [refinesPP_iff_of_beh pSwDiff_beh pSwDiff_goto_beh]
    exact not_improvesPP_term_term (by decide)

/-- Block `0` halts; block `1` emits `1`. -/
def pHaltEmit : Prog := ⟨[], [⟨[], .halt⟩, ⟨[.emit (.use (.const (.int 1)))], .halt⟩]⟩

theorem pHaltEmit_beh (b : Beh) : HasBeh SEx pHaltEmit b ↔ b = .term [] :=
  beh_slots_eq (n := 10) (by decide) (by rfl) b
theorem pHaltEmit_goto_beh (b : Beh) :
    HasBeh SEx (setTerm pHaltEmit 0 (.goto 1)) b ↔ b = .term [1] :=
  beh_slots_eq (n := 10) (by decide) (by rfl) b

/-- **Tightness of "the terminator is the switch".** Replacing the `halt` terminator of
block `0` of `pHaltEmit` by `goto 1` (arms `[]`, so the arm condition holds vacuously; the
constant operand `0` evaluates everywhere) is not a refinement. -/
theorem setTerm_nonSwitch_counterexample :
    (∀ a ∈ ([] : List (Nat × Label)), a.2 = 1) ∧
      (∀ st, ReachableAt SEx pHaltEmit 0 (pHaltEmit.blk 0).stmts.length st →
        ((Operand.const (.int 0)).evalInt st).isSome = true) ∧
      ¬ RefinesPP SEx pHaltEmit (setTerm pHaltEmit 0 (.goto 1)) := by
  refine ⟨by decide, fun _ _ => rfl, ?_⟩
  rw [refinesPP_iff_of_beh pHaltEmit_beh pHaltEmit_goto_beh]
  exact not_improvesPP_term_term (by decide)

/-- **Tightness of `ht` for the equivalence (all other hypotheses hold, the conclusion
fails).** -/
theorem switchToGoto_equiv_ht_counterexample :
    (∀ a ∈ ([] : List (Nat × Label)), a.2 = 1) ∧
      (∀ st, ReachableAt SEx pHaltEmit 0 (pHaltEmit.blk 0).stmts.length st →
        ((Operand.const (.int 0)).evalInt st).isSome = true) ∧
      ¬ EquivPP SEx pHaltEmit (setTerm pHaltEmit 0 (.goto 1)) :=
  ⟨setTerm_nonSwitch_counterexample.1, setTerm_nonSwitch_counterexample.2.1,
    fun h => setTerm_nonSwitch_counterexample.2.2 h.1⟩

/-- **Tightness of `hall` for the equivalence (all other hypotheses hold, the conclusion
fails).** -/
theorem switchToGoto_equiv_hall_counterexample :
    (pSwDiff.blk 0).term = .switchInt (.copy ⟨0, []⟩ u8) [(0, 1)] 2 ∧
      (∀ st, ReachableAt SEx pSwDiff 0 (pSwDiff.blk 0).stmts.length st →
        ((Operand.copy ⟨0, []⟩ u8).evalInt st).isSome = true) ∧
      ¬ EquivPP SEx pSwDiff (setTerm pSwDiff 0 (.goto 2)) :=
  ⟨switchToGoto_differentTargets_counterexample.1,
    switchToGoto_differentTargets_counterexample.2.1,
    fun h => switchToGoto_differentTargets_counterexample.2.2 h.1⟩

/-- **Tightness of `hok` for the equivalence (all other hypotheses hold, the conclusion
fails).** -/
theorem switchToGoto_equiv_hok_counterexample :
    (pSwUninit.blk 0).term = .switchInt (.copy ⟨0, []⟩ u8) [(0, 1)] 1 ∧
      (∀ a ∈ ([(0, 1)] : List (Nat × Label)), a.2 = 1) ∧
      ¬ EquivPP SEx pSwUninit (setTerm pSwUninit 0 (.goto 1)) :=
  ⟨switchToGoto_erases_operand_ub.1.1, switchToGoto_erases_operand_ub.2.2,
    fun h => switchToGoto_erases_operand_ub.1.2.2 h.2⟩

/-- **Tightness of `ht` for the exact condition: the biconditional fails.** -/
theorem switchToGoto_iff_ht_counterexample :
    (∀ a ∈ ([] : List (Nat × Label)), a.2 = 1) ∧
    ¬ (EquivPP SEx pHaltEmit (setTerm pHaltEmit 0 (.goto 1)) ↔
        ∀ st, ReachableAt SEx pHaltEmit 0 (pHaltEmit.blk 0).stmts.length st →
          (Operand.const (.int 0)).evalInt st = none →
          GoesWrongFrom SEx (setTerm pHaltEmit 0 (.goto 1))
            ((setTerm pHaltEmit 0 (.goto 1)).entry 1 st) []) := by
  obtain ⟨hall, hok, hnotref⟩ := setTerm_nonSwitch_counterexample
  refine ⟨hall, fun hiff => hnotref (hiff.2 fun st hr hnone => ?_).1⟩
  have hs := hok st hr
  rw [hnone] at hs
  cases hs

/-- **Tightness of `hall` for the exact condition: the biconditional fails.** -/
theorem switchToGoto_iff_hall_counterexample :
    (pSwDiff.blk 0).term = .switchInt (.copy ⟨0, []⟩ u8) [(0, 1)] 2 ∧
    ¬ (EquivPP SEx pSwDiff (setTerm pSwDiff 0 (.goto 2)) ↔
        ∀ st, ReachableAt SEx pSwDiff 0 (pSwDiff.blk 0).stmts.length st →
          (Operand.copy ⟨0, []⟩ u8).evalInt st = none →
          GoesWrongFrom SEx (setTerm pSwDiff 0 (.goto 2))
            ((setTerm pSwDiff 0 (.goto 2)).entry 2 st) []) := by
  obtain ⟨ht, hok, hnotref⟩ := switchToGoto_differentTargets_counterexample
  refine ⟨ht, fun hiff => hnotref (hiff.2 fun st hr hnone => ?_).1⟩
  have hs := hok st hr
  rw [hnone] at hs
  cases hs

/-- Instance of `evalInt_copy_eq_none_iff`: in `stEx`, local `0` holds pointer fragments, so
reading it at `bool2` fails. -/
theorem evalInt_copy_instance : (Operand.copy ⟨0, []⟩ bool2).evalInt stEx = none := by decide

/-! ## `&raw` versus `&` -/

/-- The hypothesis of `refToRaw_refinesPP` holds for `pRefDangling` at `(0, 3)`. -/
theorem refToRaw_nonvacuous :
    (pRefDangling.blk 0).stmts[3]? = some (.assign ⟨2, []⟩ .ptr (.ref ⟨0, [.deref]⟩ ⟨4, 2⟩)) := by
  decide

/-- **Tightness of "the replaced statement is `dst := &p`".** Replacing the `emit 1` of
`pEmitL` by `x := &raw x` is not a refinement. -/
theorem setStmt_nonRef_counterexample :
    ¬ RefinesPP SEx pEmitL (setStmt pEmitL 0 0 (.assign ⟨0, []⟩ .ptr (.rawRef ⟨0, []⟩))) := by
  rw [refinesPP_iff_of_beh pEmitL_beh (bt := .wrong [])
    (beh_slots_eq (n := 10) (by decide) (by rfl))]
  rintro (h | ⟨t, h, _⟩) <;> cases h

/-- Instances of `rawRef_eval_eq_none_iff` / `ref_eval_eq_none_iff`: in `stEx`,
`&raw (*p).field 1` evaluates (to the odd address `7`), while `&(*p).field 1` at a 2-aligned
pointee is UB. -/
theorem ref_eval_instance :
    (Rvalue.rawRef ⟨0, [.deref, .field 1]⟩).eval stEx = some (.ptr ⟨some 0, 7⟩) ∧
      (Rvalue.ref ⟨0, [.deref, .field 1]⟩ ⟨2, 2⟩).eval stEx = none := by decide

/-! ## Storage markers -/

/-- Two always-allocated one-byte locals: `x0 := 1; x1 := 2; emit x0`. -/
def pAlias : Prog :=
  ⟨[⟨1, 1⟩, ⟨1, 1⟩],
   [⟨[.assign ⟨0, []⟩ u8 (.use (.const (.int 1))), .assign ⟨1, []⟩ u8 (.use (.const (.int 2))),
      .emit (.use (.copy ⟨0, []⟩ u8))], .halt⟩]⟩

/-- The slot assignment placing every local at address `4`. -/
def sAlias : Local → Nat := fun _ => 4

theorem pAlias_fresh_beh (ω : Nat → Nat) (b : Beh) (h : HasBehIn (.fresh ω) pAlias b) :
    b = .term [1] := by
  by_cases d : disjointRanges (ω 1 + 1) 1 (ω 0 + 1) 1 = true
  · have d' := d
    simp only [disjointRanges] at d'
    simp at d'
    have hne : ω 1 ≠ ω 0 := by omega
    rw [hasBehIn_iff_toBeh (n := 10) (by simp_run [pAlias, u8, d, hne])] at h
    simp_run [pAlias, u8, d, hne] at h
    exact h.symm
  · rw [hasBehIn_iff_toBeh (n := 10) (by simp_run [pAlias, u8, d])] at h
    simp_run [pAlias, u8, d] at h

/-- **Tightness of the slot-validity hypothesis of
`eraseMarkers_slots_refinesAcross_fresh_of_noProvConst`.** `pAlias` has no pointer constant
with provenance. `sAlias` places its two simultaneously live locals at the same address, so
the slot execution emits `2` while every fresh execution emits `1`; erasing the (absent)
markers of local `0` leaves `pAlias` unchanged, and the end-to-end refinement fails. -/
theorem eraseMarkers_slots_invalid_counterexample :
    NoProvConst pAlias ∧ eraseMarkers pAlias 0 = pAlias ∧
      ¬ RefinesAcross .fresh pAlias (.slots sAlias) (eraseMarkers pAlias 0) := by
  have he : eraseMarkers pAlias 0 = pAlias := by decide
  refine ⟨by decide, he, ?_⟩
  rw [he]
  intro h
  obtain ⟨bs, ⟨ω, hbs⟩, himp⟩ :=
    h (.term [2]) ((beh_slots_eq (n := 10) (o := .term [2]) (by decide) (by rfl) _).2 rfl)
  rw [pAlias_fresh_beh ω bs hbs] at himp
  exact not_improvesPP_term_term (by decide) himp

/-! ## Examples of the semantic predicates -/

/-- `ReachableAt` holds at the reached point of `pDanglingMention 0`. -/
theorem reachableAt_ex_pos :
    ReachableAt SEx (pDanglingMention 0) 0 3
      (match runFromInit (.slots sEx) (pDanglingMention 0) 3 with
       | .running c _ => c.st
       | _ => ⟨⟨[], []⟩, []⟩) :=
  ⟨fun _ => 0, initEx (pDanglingMention 0), 3, [], by decide, by decide⟩

/-- `ReachableAt` fails at block `1` of `pHaltEmit` (block `0` halts). -/
theorem reachableAt_ex_neg (st : State) : ¬ ReachableAt SEx pHaltEmit 1 0 st := by
  intro h
  have hm := reachableAt_slots_mem (N := 3) (by decide) h
  have key : ∀ c ∈ reachCfgs (.slots sEx) pHaltEmit 3, c.lbl ≠ 1 := by decide
  exact key _ hm rfl

/-- `GoesWrongFrom` holds for `pDerefUninit` from its entry. -/
theorem goesWrongFrom_ex_pos :
    GoesWrongFrom SEx pDerefUninit (pDerefUninit.entry 0 (initEx pDerefUninit)) [] :=
  ⟨fun _ => 0, 4, by decide⟩

/-- `GoesWrongFrom` fails for `pHalt`, which halts. -/
theorem goesWrongFrom_ex_neg (t : List Nat) :
    ¬ GoesWrongFrom SEx pHalt (pHalt.entry 0 (initEx pHalt)) t := by
  rintro ⟨ω, n, h⟩
  have hd : run (SEx.mode ω) pHalt 1 (pHalt.entry 0 (initEx pHalt)) =
      .done [] (initEx pHalt) := by
    show run (.slots sEx) pHalt 1 (pHalt.entry 0 (initEx pHalt)) = .done [] (initEx pHalt)
    decide
  have := run_finished_mono rfl hd (Nat.le_max_left 1 n)
  have h' := run_finished_mono rfl h (Nat.le_max_right 1 n)
  rw [this] at h'
  cases h'

/-- The constant-`true` checker is not exact. -/
theorem not_exactUBChecker_const_true : ¬ ExactUBChecker SEx (fun _ => true) := by
  intro h
  exact ((h pDerefUninit).1 rfl) [] ((pDerefUninit_beh _).2 rfl)

/-- `x0 := copy x1` with `x1` uninitialized (both one-byte, always allocated). -/
def pUBAssign : Prog :=
  ⟨[⟨1, 1⟩, ⟨1, 1⟩], [⟨[.assign ⟨0, []⟩ u8 (.use (.copy ⟨1, []⟩ u8))], .halt⟩]⟩

/-- **Tightness of "the deleted statement is a `placeMention`" for the UB-check transfer.**
In `pUBAssign` the place `⟨0, []⟩` evaluates at every reachable state of `(0, 0)` and the
program with statement `(0, 0)` deleted is UB-free, but `pUBAssign` (whose statement there is
an assignment reading an uninitialized local) is not. -/
theorem deleteStmt_ubAssign_counterexample :
    (∀ st, ReachableAt SEx pUBAssign 0 0 st → (evalPlace st ⟨0, []⟩).isSome = true) ∧
      UBFree SEx (deleteStmt pUBAssign 0 0) ∧ ¬ UBFree SEx pUBAssign := by
  refine ⟨fun st h => ?_, ?_, ?_⟩
  · have hm := reachableAt_slots_mem (N := 4) (by decide) h
    have key : ∀ c ∈ reachCfgs (.slots sEx) pUBAssign 4, c.lbl = 0 →
        c.rest = (pUBAssign.blk 0).stmts.drop 0 → (evalPlace c.st ⟨0, []⟩).isSome = true := by
      decide
    exact key _ hm rfl rfl
  · intro t h
    have := (beh_slots_eq (n := 10) (o := .term []) (by decide) (by rfl) _).1 h
    cases this
  · intro h
    exact h [] ((beh_slots_eq (n := 10) (o := .wrong []) (by decide) (by rfl) _).2 rfl)

end Toy.PlaceEval
