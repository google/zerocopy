import ToyContracts.Examples

/-!
# Counterexamples (fully proved)

Each tightness witness is stated in canonical form: a concrete instance satisfies every other
hypothesis of the named result, and its conclusion fails.
-/

namespace Toy.Contracts

/-! ## Multi-exit placement -/

/-- Tightness of the premise of `req_and_ens_of_halts_ret_instr_allExits_lower`: for `gEarly`,
input `0` and value `7` under `c1`, the instrumented lowered function does not halt with a return
of `7`, and `Req 0 ∧ Ens 0 7` fails. -/
theorem cex_req_and_ens_premise :
    ¬ Halts c1 (instr .allExits (lower gEarly)) 0 ⟨[], .ret 7⟩ ∧
    ¬ (c1.req 0 = true ∧ c1.ens 0 7 = true) := by
  refine ⟨fun ⟨_, n, hn⟩ => ?_, by decide⟩
  rcases n with _ | _ | n
  · cases hn
  · cases hn
  · cases hn

/-- Tail-only placement misses an early return: `gEarly` (lowered) on `0` satisfies `Req`, halts
with no events and a normal return of `7` (along the edge `ret .early (.lit 7)` of its block `2`),
`Ens 0 7` fails, the tail-only instrumentation still halts with no events and a return of `7`, and
the all-exits instrumentation halts with no events and an `ensures` failure. -/
theorem cex_tailOnly_misses_early_return :
    Lowered gEarly ∧ c1.req 0 = true ∧ Halts c1 gEarly 0 ⟨[], .ret 7⟩ ∧ c1.ens 0 7 = false ∧
    Halts c1 (instr .tailOnly gEarly) 0 ⟨[], .ret 7⟩ ∧
    Halts c1 (instr .allExits gEarly) 0 ⟨[], .checkFail .post⟩ :=
  ⟨by decide, rfl, (halts_gEarly_0 _).2 rfl, rfl, ⟨by decide, 2, rfl⟩, ⟨by decide, 2, rfl⟩⟩

/-- Tail-only placement misses a `?` error path even after lowering: `gTry` on `1` satisfies
`Req` and halts with no events and a return of `9` (the value of the `?` error path), `Ens 1 9`
fails, `lower gTry` is lowered, the tail-only instrumentation of `lower gTry` halts with no events
and a return of `9`, and the all-exits instrumentation halts with no events and an `ensures`
failure. -/
theorem cex_tailOnly_misses_try_error_after_lowering :
    c1.req 1 = true ∧ Halts c1 gTry 1 ⟨[], .ret 9⟩ ∧ c1.ens 1 9 = false ∧ Lowered (lower gTry) ∧
    Halts c1 (instr .tailOnly (lower gTry)) 1 ⟨[], .ret 9⟩ ∧
    Halts c1 (instr .allExits (lower gTry)) 1 ⟨[], .checkFail .post⟩ :=
  ⟨rfl, (halts_gTry_1 c1 _).2 rfl, rfl, by decide, ⟨by decide, 3, rfl⟩, ⟨by decide, 3, rfl⟩⟩

/-- Instrumenting before lowering misses `?` (tightness of `Lowered` in
`run_instr_allExits_eq_instrObs_of_lowered`): `gTry` is not lowered; at input `1` and fuel `1`
under `c1` the all-exits instrumentation gives a return of `9` with no events while the contract
wrapper gives an `ensures` failure with no events, so the two sides of the equation differ; the
instrumented `gTry` halts on `1` with a return of `9`, and `Ens 1 9` fails. -/
theorem cex_instr_before_lower_misses_try :
    ¬ Lowered gTry ∧
    run c1 (instr .allExits gTry) 1 1 = ⟨[], .ret 9⟩ ∧
    instrObs c1 1 (run c1 gTry 1 1) = ⟨[], .checkFail .post⟩ ∧
    run c1 (instr .allExits gTry) 1 1 ≠ instrObs c1 1 (run c1 gTry 1 1) ∧
    Halts c1 (instr .allExits gTry) 1 ⟨[], .ret 9⟩ ∧ c1.ens 1 9 = false :=
  ⟨by decide, rfl, rfl, by decide, (halts_instr_allExits_gTry_1 c1 rfl _).2 rfl, rfl⟩

/-- Tightness of `JumpsInRange` in `halts_lower_iff_of_jumpsInRange` (out-of-range jump target):
`fOut` jumps to the missing index `3`; `lower fOut` halts on `0` with a return of `5` (index `3` is
now the fresh block of the `?` in block `1`), while `fOut` does not. -/
theorem cex_lower_jumpsInRange :
    ¬ JumpsInRange fOut ∧ Halts c1 (lower fOut) 0 ⟨[], .ret 5⟩ ∧ ¬ Halts c1 fOut 0 ⟨[], .ret 5⟩ := by
  refine ⟨by decide, (halts_lower_fOut _).2 rfl, fun h => ?_⟩
  rw [halts_fOut] at h
  cases h

/-- Tightness of `JumpsInRange` in `halts_lower_iff_of_jumpsInRange` (out-of-range entry, every
jump target in range): `lower fBadEntry` halts on `0` with a return of `5`, while `fBadEntry` does
not. -/
theorem cex_lower_entry_out_of_range :
    ¬ JumpsInRange fBadEntry ∧
    fBadEntry.blocks.all (fun blk => blk.term.targets.all (· < fBadEntry.blocks.length)) = true ∧
    Halts c1 (lower fBadEntry) 0 ⟨[], .ret 5⟩ ∧ ¬ Halts c1 fBadEntry 0 ⟨[], .ret 5⟩ := by
  refine ⟨by decide, by decide, ⟨by decide, 1, rfl⟩, fun ⟨_, n, hn⟩ => ?_⟩
  rcases n with _ | n <;> cases hn

/-! ## Erasure equivalence -/

/-- Tightness of `NoChecks` in `erase_instr_eq_of_noChecks`. -/
theorem cex_erase_instr_noChecks : ¬ NoChecks gInt ∧ erase (instr .allExits gInt) ≠ gInt := by
  decide

theorem runEqAt_erase_instr_gTry_1 (c : Contract) (hr : c.req 1 = true) :
    RunEqAt c (erase (instr .allExits gTry)) (instr .allExits gTry) 1 := by
  intro n
  rcases n with _ | n
  · simp [run, erase, instr, gTry, instrBlock, execStmts, runFrom, Stmt.isContract, hr]
  · simp [run, erase, instr, gTry, instrBlock, execStmts, runFrom, Stmt.isContract, evalOp,
      evalRv, Store.set, hr]

theorem runEqAt_instr_gTry_1 (c : Contract) (hr : c.req 1 = true) :
    RunEqAt c (instr .allExits gTry) gTry 1 := by
  intro n
  rcases n with _ | n
  · simp [run, instr, gTry, instrBlock, execStmts, runFrom, hr]
  · simp [run, instr, gTry, instrBlock, execStmts, runFrom, evalOp, evalRv, Store.set, hr]

theorem not_ensOnReturnsAt_gTry_1 : ¬ EnsOnReturnsAt cOne gTry 1 := by
  intro h
  have := h [] 9 ((halts_gTry_1 cOne _).2 rfl)
  revert this; decide

theorem runEqAt_erase_instr_gInt_ne : ¬ RunEqAt cThree (erase (instr .allExits gInt))
    (instr .allExits gInt) 3 := by
  intro h; have := h 1; revert this; decide

theorem ensOnReturnsAt_gInt_3 : EnsOnReturnsAt cThree gInt 3 := by
  intro tr r h
  rw [halts_gInt_3] at h
  cases h

/-- Tightness of `Lowered` in `instr_allExits_obsEq_self_iff_ensOnReturnsAt_of_lowered_of_req`:
for `gTry` on `1` under `cOne`, the all-exits instrumentation is fuel-exactly identical to `gTry`
(the `?` exit is unchecked) while `Ens 1 9` fails at a normal return. -/
theorem cex_instrSelf_lowered :
    ¬ Lowered gTry ∧ cOne.req 1 = true ∧
    ¬ ((RunEqAt cOne (instr .allExits gTry) gTry 1 ↔ EnsOnReturnsAt cOne gTry 1) ∧
       (HaltsEqAt cOne (instr .allExits gTry) gTry 1 ↔ EnsOnReturnsAt cOne gTry 1)) := by
  refine ⟨by decide, rfl, fun ⟨h, _⟩ => ?_⟩
  exact not_ensOnReturnsAt_gTry_1 (h.1 (runEqAt_instr_gTry_1 cOne rfl))

/-- Tightness of `Req x` in `instr_allExits_obsEq_self_iff_ensOnReturnsAt_of_lowered_of_req`: for
`gGood` on `100` (where `Req` fails) every normal return satisfies `Ens`, yet the instrumentation
and `gGood` differ at fuel `0`. -/
theorem cex_instrSelf_req :
    Lowered gGood ∧ c1.req 100 = false ∧
    ¬ ((RunEqAt c1 (instr .allExits gGood) gGood 100 ↔ EnsOnReturnsAt c1 gGood 100) ∧
       (HaltsEqAt c1 (instr .allExits gGood) gGood 100 ↔ EnsOnReturnsAt c1 gGood 100)) := by
  refine ⟨by decide, rfl, fun ⟨h, _⟩ => ?_⟩
  have := h.2 (ensOnReturnsAt_gGood 100) 0
  revert this; decide

/-- Tightness of `Lowered` in `erasure_obsEq_iff_ensOnReturnsAt_of_lowered_of_noChecks_of_req`:
for `gTry` on `1` under `cOne`, erasure is fuel-exactly identical to the all-exits
instrumentation (the `?` exit is unchecked) while `Ens 1 9` fails at a normal return. -/
theorem cex_erasure_lowered :
    ¬ Lowered gTry ∧ NoChecks gTry ∧ cOne.req 1 = true ∧
    ¬ ((RunEqAt cOne (erase (instr .allExits gTry)) (instr .allExits gTry) 1 ↔
          EnsOnReturnsAt cOne gTry 1) ∧
       (HaltsEqAt cOne (erase (instr .allExits gTry)) (instr .allExits gTry) 1 ↔
          EnsOnReturnsAt cOne gTry 1)) := by
  refine ⟨by decide, by decide, rfl, fun ⟨h, _⟩ => ?_⟩
  exact not_ensOnReturnsAt_gTry_1 (h.1 (runEqAt_erase_instr_gTry_1 cOne rfl))

/-- Tightness of `NoChecks` in `erasure_obsEq_iff_ensOnReturnsAt_of_lowered_of_noChecks_of_req`:
`gInt` already contains a failing `ensures` check; on `3` under `cThree` it never returns (so the
right-hand side holds vacuously), while erasure returns `3` and instrumentation fails. -/
theorem cex_erasure_noChecks :
    Lowered gInt ∧ ¬ NoChecks gInt ∧ cThree.req 3 = true ∧
    ¬ ((RunEqAt cThree (erase (instr .allExits gInt)) (instr .allExits gInt) 3 ↔
          EnsOnReturnsAt cThree gInt 3) ∧
       (HaltsEqAt cThree (erase (instr .allExits gInt)) (instr .allExits gInt) 3 ↔
          EnsOnReturnsAt cThree gInt 3)) := by
  refine ⟨by decide, by decide, rfl, fun ⟨h, _⟩ => ?_⟩
  exact runEqAt_erase_instr_gInt_ne (h.2 ensOnReturnsAt_gInt_3)

/-- Tightness of `Req x` in `erasure_obsEq_iff_ensOnReturnsAt_of_lowered_of_noChecks_of_req`: for
`gGood` on `100` (where `Req` fails) every normal return satisfies `Ens`, yet erasure and
instrumentation differ. -/
theorem cex_erasure_req :
    Lowered gGood ∧ NoChecks gGood ∧ c1.req 100 = false ∧
    ¬ ((RunEqAt c1 (erase (instr .allExits gGood)) (instr .allExits gGood) 100 ↔
          EnsOnReturnsAt c1 gGood 100) ∧
       (HaltsEqAt c1 (erase (instr .allExits gGood)) (instr .allExits gGood) 100 ↔
          EnsOnReturnsAt c1 gGood 100)) := by
  refine ⟨by decide, by decide, rfl, fun ⟨h, _⟩ => ?_⟩
  exact not_runEqAt_erase_instr_gGood_100 (h.2 (ensOnReturnsAt_gGood 100))

/-- With tail-only placement the forward direction of
`erasure_obsEq_iff_ensOnReturnsAt_of_lowered_of_noChecks_of_req` fails: for `gEarly` on `0` under
`c1` (lowered, without contract statements, `Req 0` holds), the erasure of the tail-only
instrumentation is fuel-exactly identical to it, while the early return `7` violates `Ens`. -/
theorem cex_erasure_tailOnly :
    Lowered gEarly ∧ NoChecks gEarly ∧ c1.req 0 = true ∧
    RunEqAt c1 (erase (instr .tailOnly gEarly)) (instr .tailOnly gEarly) 0 ∧
    ¬ EnsOnReturnsAt c1 gEarly 0 := by
  refine ⟨by decide, by decide, rfl, fun n => ?_, not_ensOnReturnsAt_gEarly_0⟩
  rcases n with _ | _ | n <;> rfl

/-- Tightness of `Lowered` in
`erasure_obsEq_onReq_iff_staticObligation_of_lowered_of_noChecks`: `gTry` under `cOne` (whose
`Req` admits exactly the input `1`). -/
theorem cex_erasure_global_lowered :
    ¬ Lowered gTry ∧ NoChecks gTry ∧
    ¬ (((∀ x, cOne.req x = true →
            RunEqAt cOne (erase (instr .allExits gTry)) (instr .allExits gTry) x) ↔
          StaticObligation cOne gTry) ∧
       ((∀ x, cOne.req x = true →
            HaltsEqAt cOne (erase (instr .allExits gTry)) (instr .allExits gTry) x) ↔
          StaticObligation cOne gTry)) := by
  refine ⟨by decide, by decide, fun ⟨h, _⟩ => ?_⟩
  have hall : ∀ x, cOne.req x = true →
      RunEqAt cOne (erase (instr .allExits gTry)) (instr .allExits gTry) x := by
    intro x hx
    have : x = 1 := by simpa [cOne] using hx
    subst this
    exact runEqAt_erase_instr_gTry_1 cOne rfl
  exact not_ensOnReturnsAt_gTry_1 (h.1 hall 1 rfl)

/-- Tightness of `NoChecks` in
`erasure_obsEq_onReq_iff_staticObligation_of_lowered_of_noChecks`: `gInt` under `cThree` (whose
`Req` admits exactly the input `3`). -/
theorem cex_erasure_global_noChecks :
    Lowered gInt ∧ ¬ NoChecks gInt ∧
    ¬ (((∀ x, cThree.req x = true →
            RunEqAt cThree (erase (instr .allExits gInt)) (instr .allExits gInt) x) ↔
          StaticObligation cThree gInt) ∧
       ((∀ x, cThree.req x = true →
            HaltsEqAt cThree (erase (instr .allExits gInt)) (instr .allExits gInt) x) ↔
          StaticObligation cThree gInt)) := by
  refine ⟨by decide, by decide, fun ⟨h, _⟩ => ?_⟩
  have hob : StaticObligation cThree gInt := by
    intro x hx
    have : x = 3 := by simpa [cThree] using hx
    subst this
    exact ensOnReturnsAt_gInt_3
  exact runEqAt_erase_instr_gInt_ne (h.2 hob 3 rfl)

/-- Tightness of `Req x = false` in `not_haltsEqAt_erase_instr_of_req_false`: on `5`, where `Req`
holds, the conclusion fails for `gGood` (erasure and instrumentation have the same halting
observations, and the instrumentation does not end with a `requires` failure). -/
theorem cex_not_haltsEq_req_true :
    c1.req 5 = true ∧
    ¬ ((∀ n, run c1 (instr .allExits gGood) 5 n = ⟨[], .checkFail .pre⟩) ∧
       NoChecks (erase (instr .allExits gGood)) ∧
       (∀ n k, (run c1 (erase (instr .allExits gGood)) 5 n).outcome ≠ .checkFail k) ∧
       ¬ HaltsEqAt c1 (erase (instr .allExits gGood)) (instr .allExits gGood) 5) :=
  ⟨rfl, fun ⟨_, _, _, h⟩ => h (haltsEqAt_of_runEqAt runEqAt_erase_instr_gGood_5)⟩

/-- Tightness of `NoChecks` in
`instr_allExits_ubRefinesAt_assumeErase_of_noChecks_of_staticObligationAt`: `gInt` on `3` under
`cThree`. -/
theorem cex_ubRefines_noChecks :
    ¬ NoChecks gInt ∧ StaticObligationAt cThree gInt 3 ∧
    ¬ UBRefinesAt cThree (instr .allExits gInt) (assumeErase (instr .allExits gInt)) 3 := by
  refine ⟨by decide, fun _ => ensOnReturnsAt_gInt_3, fun h => ?_⟩
  rcases h _ ((halts_instr_allExits_gInt_3 _).2 rfl) with h1 | ⟨tr, h1, _⟩
  · rw [halts_assumeErase_instr_gInt_3] at h1; cases h1
  · rw [halts_assumeErase_instr_gInt_3] at h1; cases h1

/-- Tightness of the static obligation in
`instr_allExits_ubRefinesAt_assumeErase_of_noChecks_of_staticObligationAt`: `gEarly` on `0`. -/
theorem cex_ubRefines_obligation :
    NoChecks gEarly ∧ ¬ StaticObligationAt c1 gEarly 0 ∧
    ¬ UBRefinesAt c1 (instr .allExits gEarly) (assumeErase (instr .allExits gEarly)) 0 :=
  ⟨by decide, not_staticObligationAt_gEarly_0, not_ubRefinesAt_instr_assumeErase_gEarly_0⟩

/-- Tightness of `Req x = false` in `not_assumeErase_ubRefinesAt_instr_of_req_false`: on `5`, where
`Req` holds, the conclusion fails for `gGood` (the assume-erased `gGood` UB-refines the checked
one, and neither run is UB or a `requires` failure). -/
theorem cex_not_ubRefines_req_true :
    c1.req 5 = true ∧
    UBRefinesAt c1 (assumeErase (instr .allExits gGood)) (instr .allExits gGood) 5 ∧
    ¬ ((∀ n, run c1 (assumeErase (instr .allExits gGood)) 5 n = ⟨[], .ub⟩) ∧
       (∀ n, run c1 (instr .allExits gGood) 5 n = ⟨[], .checkFail .pre⟩) ∧
       ¬ UBRefinesAt c1 (assumeErase (instr .allExits gGood)) (instr .allExits gGood) 5) := by
  have href : UBRefinesAt c1 (assumeErase (instr .allExits gGood)) (instr .allExits gGood) 5 := by
    intro o ho
    refine .inl ?_
    obtain ⟨hne, n, hn⟩ := ho
    refine ⟨hne, n, ?_⟩
    rw [← hn]
    rcases n with _ | n <;> rfl
  exact ⟨rfl, href, fun ⟨_, _, h⟩ => h href⟩

/-! ## Flag scoping -/

/-- Tightness of `Lowered` in `callRun_eq_ite_governingFlag_of_lowered`: callee-side placement with
every flag on, for the unlowered `gTry` on `1` under `cOne`, at fuel `1`. -/
theorem cex_callRun_lowered :
    ¬ Lowered gTry ∧
    callRun (fun _ => true) .calleeSide .atDefinition cs1 cOne gTry 1 1 ≠
      (if (fun _ => true) (governingCrate .calleeSide .atDefinition cs1)
        then instrObs cOne 1 (run cOne gTry 1 1) else run cOne gTry 1 1) := by
  decide

theorem not_detects_gTry_1 :
    ¬ Detects (fun _ => true) .calleeSide .atDefinition cs1 cOne gTry 1 := by
  rintro ⟨n, tr, k, h⟩
  rcases n with _ | n
  · cases h
  · have e : callRun (fun _ => true) .calleeSide .atDefinition cs1 cOne gTry 1 (n + 1) =
        ⟨[], .ret 9⟩ := by
      simp [callRun, compileInDefCrate, instantiateIn, callInCallerCrate, run, instr, gTry,
        instrBlock, execStmts, runFrom, evalOp, evalRv, Store.set, cOne]
    rw [e] at h
    cases h

/-- Tightness of `Lowered` in `detects_iff_governingFlag_of_lowered_of_noChecks_of_violation`:
`gTry` on `1` under `cOne` violates `Ens` through `?`; with every flag on, callee-side placement
reports nothing. -/
theorem cex_detects_lowered :
    ¬ Lowered gTry ∧ NoChecks gTry ∧ ViolationAt cOne gTry 1 ∧
    ¬ (Detects (fun _ => true) .calleeSide .atDefinition cs1 cOne gTry 1 ↔
        (fun _ => true) (governingCrate .calleeSide .atDefinition cs1) = true) :=
  ⟨by decide, by decide, .inr ⟨rfl, [], 9, (halts_gTry_1 cOne _).2 rfl, rfl⟩,
    fun h => not_detects_gTry_1 (h.2 rfl)⟩

/-- Tightness of `NoChecks` in `detects_iff_governingFlag_of_lowered_of_noChecks_of_violation`:
`gIntReq` contains its own `requires` check; on `100` (where `Req` fails) a failed check is
reported with every flag off. -/
theorem cex_detects_noChecks :
    Lowered gIntReq ∧ ¬ NoChecks gIntReq ∧ ViolationAt c1 gIntReq 100 ∧
    ¬ (Detects (fun _ => false) .calleeSide .atDefinition cs1 c1 gIntReq 100 ↔
        (fun _ => false) (governingCrate .calleeSide .atDefinition cs1) = true) :=
  ⟨by decide, by decide, .inl rfl, fun h => absurd (h.1 ⟨1, [], .pre, rfl⟩) (by decide)⟩

/-- Tightness of `ViolationAt` in `detects_iff_governingFlag_of_lowered_of_noChecks_of_violation`:
`gGood` on `5` has no violation; with every flag on nothing is reported. -/
theorem cex_detects_violation :
    Lowered gGood ∧ NoChecks gGood ∧ ¬ ViolationAt c1 gGood 5 ∧
    ¬ (Detects (fun _ => true) .calleeSide .atDefinition cs1 c1 gGood 5 ↔
        (fun _ => true) (governingCrate .calleeSide .atDefinition cs1) = true) :=
  ⟨by decide, by decide, not_violationAt_gGood_5, fun h => not_detects_gGood_5 (h.2 rfl)⟩

/-- Tightness of `¬ ViolationAt` in `callRun_eq_run_of_not_violation`: `gEarly` on `0`. -/
theorem cex_callRun_violation :
    ViolationAt c1 gEarly 0 ∧
    callRun (fun _ => true) .calleeSide .atDefinition cs1 c1 gEarly 0 2 ≠ run c1 gEarly 0 2 :=
  ⟨violationAt_gEarly_0, by decide⟩

/-- The same flags give different verdicts under the two placements: with the caller crate's
flag on and the defining crate's flag off, `gEarly`'s violation on `0` is reported under
caller-side placement and not under callee-side placement (resolution at definition). -/
theorem cex_same_flags_detection_depends_on_placement :
    flCallerOn cs1.callerCrate = true ∧ flCallerOn cs1.defCrate = false ∧
    ViolationAt c1 gEarly 0 ∧
    Detects flCallerOn .callerSide .atDefinition cs1 c1 gEarly 0 ∧
    ¬ Detects flCallerOn .calleeSide .atDefinition cs1 c1 gEarly 0 :=
  ⟨rfl, rfl, violationAt_gEarly_0, detects_callerOn_callerSide_gEarly_0,
    not_detects_calleeSide_off_gEarly_0 _ _ _ rfl⟩

/-- The flag of the crate holding a callee-side check is not always decisive: for the generic
callee of `csGen` (instantiated in the calling crate) with resolution at instantiation, the flag of
the holding (defining) crate is on, the flag of the instantiating (calling) crate is off, and
`gEarly`'s violation on `0` is not reported; it is reported with resolution at definition, and with
resolution at instantiation for the non-generic call `cs1`. -/
theorem cex_calleeSide_atInstantiation_definingFlag_on_undetected :
    holder .calleeSide csGen = csGen.defCrate ∧
    flDefOn (holder .calleeSide csGen) = true ∧ flDefOn csGen.instCrate = false ∧
    ViolationAt c1 gEarly 0 ∧
    ¬ Detects flDefOn .calleeSide .atInstantiation csGen c1 gEarly 0 ∧
    Detects flDefOn .calleeSide .atDefinition csGen c1 gEarly 0 ∧
    Detects flDefOn .calleeSide .atInstantiation cs1 c1 gEarly 0 :=
  ⟨rfl, rfl, rfl, violationAt_gEarly_0, not_detects_calleeSide_off_gEarly_0 _ _ _ rfl,
    ⟨2, [], .post, rfl⟩, ⟨2, [], .post, rfl⟩⟩

/-! ## Compile-time evaluation -/

/-- A `requires`-violating compile-time call yields a constant while the runtime call fails the
check: on `100` (where `Req` fails), check-skipping compile-time evaluation of the all-exits
instrumentation of `gEarly` gives `100`, the static obligation at `100` holds vacuously, the
all-exits runtime-checked call halts with a `requires` failure and no events at every fuel and
returns no value, and check-evaluating compile-time evaluation gives no constant. -/
theorem cex_ctfeSkip_requires_violation :
    Lowered gEarly ∧ NoChecks gEarly ∧ c1.req 100 = false ∧
    CtfeConst .allExits .skipChecks c1 gEarly 100 100 ∧ StaticObligationAt c1 gEarly 100 ∧
    (∀ n, run c1 (instr .allExits gEarly) 100 n = ⟨[], .checkFail .pre⟩) ∧
    (∀ r, ¬ RuntimeValue .allExits c1 gEarly 100 r) ∧
    (∀ r, ¬ CtfeConst .allExits .evalChecks c1 gEarly 100 r) :=
  ⟨by decide, by decide, rfl, ctfeConst_skip_gEarly_100, staticObligationAt_gEarly_100,
    run_instr_gEarly_100 .allExits, not_runtimeValue_gEarly_100, not_ctfeConst_eval_gEarly_100⟩

/-- An `ensures`-violating compile-time call yields a constant while the runtime call fails the
check: on `0` (where `Req` holds), check-skipping compile-time evaluation of the all-exits
instrumentation of `gEarly` gives `7`, `Ens 0 7` fails, the all-exits runtime-checked call halts
with an `ensures` failure and no events and returns no value, and check-evaluating compile-time
evaluation gives no constant. -/
theorem cex_ctfeSkip_ensures_violation :
    Lowered gEarly ∧ NoChecks gEarly ∧ c1.req 0 = true ∧ c1.ens 0 7 = false ∧
    CtfeConst .allExits .skipChecks c1 gEarly 0 7 ∧
    Halts c1 (instr .allExits gEarly) 0 ⟨[], .checkFail .post⟩ ∧
    (∀ r, ¬ RuntimeValue .allExits c1 gEarly 0 r) ∧
    (∀ r, ¬ CtfeConst .allExits .evalChecks c1 gEarly 0 r) := by
  refine ⟨by decide, by decide, rfl, rfl, ⟨2, [], rfl⟩, (halts_instr_allExits_gEarly_0 _).2 rfl,
    fun r => (runtimeValue_gEarly_0_placement r).2, fun r ⟨n, tr, h⟩ => ?_⟩
  rw [ctfeRun_evalChecks_eq] at h
  have hh : Halts c1 (instr .allExits gEarly) 0 ⟨tr, .ret r⟩ := ⟨nofun, n, h⟩
  rw [halts_instr_allExits_gEarly_0] at hh
  cases hh

theorem ctfeConst_skip_gTry_1 : CtfeConst .allExits .skipChecks c1 gTry 1 9 := ⟨1, [], rfl⟩

theorem runtimeValue_gTry_1 : RuntimeValue .allExits c1 gTry 1 9 :=
  ⟨[], (halts_instr_allExits_gTry_1 c1 rfl _).2 rfl⟩

theorem not_runtimeValue_gInt_3 : ¬ RuntimeValue .allExits cThree gInt 3 3 := by
  rintro ⟨tr, h⟩
  rw [halts_instr_allExits_gInt_3] at h
  cases h

theorem not_runtimeValue_gGood_5_4 : ¬ RuntimeValue .allExits c1 gGood 5 4 := by
  rintro ⟨tr, h⟩
  rw [halts_instr_allExits_gGood 5 (by decide)] at h
  cases h

theorem not_ctfeConst_skip_gGood_5_4 : ¬ CtfeConst .allExits .skipChecks c1 gGood 5 4 := by
  rintro ⟨n, tr, h⟩
  rcases n with _ | n <;> cases h

/-- Tightness of `Lowered` in
`runtimeValue_iff_req_and_ens_of_lowered_of_noChecks_of_ctfeSkipConst`: `gTry` on `1` returns `9`
through the unchecked `?` at run time although `Ens 1 9` fails. -/
theorem cex_runtimeValue_lowered :
    ¬ Lowered gTry ∧ NoChecks gTry ∧ CtfeConst .allExits .skipChecks c1 gTry 1 9 ∧
    ¬ (RuntimeValue .allExits c1 gTry 1 9 ↔ c1.req 1 = true ∧ c1.ens 1 9 = true) :=
  ⟨by decide, by decide, ctfeConst_skip_gTry_1,
    fun h => absurd (h.1 runtimeValue_gTry_1).2 (by decide)⟩

/-- Tightness of `NoChecks` in
`runtimeValue_iff_req_and_ens_of_lowered_of_noChecks_of_ctfeSkipConst`: `gInt` on `3` under
`cThree`. -/
theorem cex_runtimeValue_noChecks :
    Lowered gInt ∧ ¬ NoChecks gInt ∧ CtfeConst .allExits .skipChecks cThree gInt 3 3 ∧
    ¬ (RuntimeValue .allExits cThree gInt 3 3 ↔ cThree.req 3 = true ∧ cThree.ens 3 3 = true) :=
  ⟨by decide, by decide, ⟨1, [], rfl⟩, fun h => not_runtimeValue_gInt_3 (h.2 ⟨rfl, rfl⟩)⟩

/-- Tightness of the compile-time constant hypothesis in
`runtimeValue_iff_req_and_ens_of_lowered_of_noChecks_of_ctfeSkipConst`: for `gGood` on `5` and
the value `4` (which `gGood` does not return), the constant hypothesis fails, `Req 5` and `Ens 5 4`
hold, but the runtime value is not `4`. -/
theorem cex_runtimeValue_ctfeConst :
    Lowered gGood ∧ NoChecks gGood ∧ ¬ CtfeConst .allExits .skipChecks c1 gGood 5 4 ∧
    ¬ (RuntimeValue .allExits c1 gGood 5 4 ↔ c1.req 5 = true ∧ c1.ens 5 4 = true) :=
  ⟨by decide, by decide, not_ctfeConst_skip_gGood_5_4,
    fun h => not_runtimeValue_gGood_5_4 (h.2 ⟨rfl, rfl⟩)⟩

/-- The all-exits placement in `runtimeValue_iff_req_and_ens_of_lowered_of_noChecks_of_ctfeSkipConst`
cannot be replaced by tail-only placement: for `gEarly` on `0`, check-skipping compile-time
evaluation of the tail-only instrumentation gives `7`, the tail-only runtime-checked call returns
`7`, and `Ens 0 7` fails. -/
theorem cex_runtimeValue_tailOnly :
    Lowered gEarly ∧ NoChecks gEarly ∧ CtfeConst .tailOnly .skipChecks c1 gEarly 0 7 ∧
    ¬ (RuntimeValue .tailOnly c1 gEarly 0 7 ↔ c1.req 0 = true ∧ c1.ens 0 7 = true) :=
  ⟨by decide, by decide, ⟨2, [], rfl⟩,
    fun h => absurd (h.1 (runtimeValue_gEarly_0_placement 0).1).2 (by decide)⟩

/-- Tightness of `Lowered` in
`runtimeValue_iff_staticObligationAt_of_lowered_of_noChecks_of_req_of_ctfeSkipConst`. -/
theorem cex_runtimeValue_obl_lowered :
    ¬ Lowered gTry ∧ NoChecks gTry ∧ c1.req 1 = true ∧
    CtfeConst .allExits .skipChecks c1 gTry 1 9 ∧
    ¬ (RuntimeValue .allExits c1 gTry 1 9 ↔ StaticObligationAt c1 gTry 1) := by
  refine ⟨by decide, by decide, rfl, ctfeConst_skip_gTry_1, fun h => ?_⟩
  have := h.1 runtimeValue_gTry_1 rfl [] 9 ((halts_gTry_1 c1 _).2 rfl)
  revert this; decide

/-- Tightness of `NoChecks` in
`runtimeValue_iff_staticObligationAt_of_lowered_of_noChecks_of_req_of_ctfeSkipConst`. -/
theorem cex_runtimeValue_obl_noChecks :
    Lowered gInt ∧ ¬ NoChecks gInt ∧ cThree.req 3 = true ∧
    CtfeConst .allExits .skipChecks cThree gInt 3 3 ∧
    ¬ (RuntimeValue .allExits cThree gInt 3 3 ↔ StaticObligationAt cThree gInt 3) :=
  ⟨by decide, by decide, rfl, ⟨1, [], rfl⟩,
    fun h => not_runtimeValue_gInt_3 (h.2 fun _ => ensOnReturnsAt_gInt_3)⟩

/-- Tightness of `Req x` in
`runtimeValue_iff_staticObligationAt_of_lowered_of_noChecks_of_req_of_ctfeSkipConst` (without
`Req x`, the static obligation at `x` is not equivalent to the runtime value): `gEarly` on `100`. -/
theorem cex_runtimeValue_obl_req :
    Lowered gEarly ∧ NoChecks gEarly ∧ c1.req 100 = false ∧
    CtfeConst .allExits .skipChecks c1 gEarly 100 100 ∧
    ¬ (RuntimeValue .allExits c1 gEarly 100 100 ↔ StaticObligationAt c1 gEarly 100) :=
  ⟨by decide, by decide, rfl, ctfeConst_skip_gEarly_100,
    fun h => not_runtimeValue_gEarly_100 100 (h.2 staticObligationAt_gEarly_100)⟩

/-- Tightness of the compile-time constant hypothesis in
`runtimeValue_iff_staticObligationAt_of_lowered_of_noChecks_of_req_of_ctfeSkipConst`. -/
theorem cex_runtimeValue_obl_ctfeConst :
    Lowered gGood ∧ NoChecks gGood ∧ c1.req 5 = true ∧
    ¬ CtfeConst .allExits .skipChecks c1 gGood 5 4 ∧
    ¬ (RuntimeValue .allExits c1 gGood 5 4 ↔ StaticObligationAt c1 gGood 5) :=
  ⟨by decide, by decide, rfl, not_ctfeConst_skip_gGood_5_4,
    fun h => not_runtimeValue_gGood_5_4 (h.2 fun _ => ensOnReturnsAt_gGood 5)⟩

/-- The all-exits placement in
`runtimeValue_iff_staticObligationAt_of_lowered_of_noChecks_of_req_of_ctfeSkipConst` cannot be
replaced by tail-only placement: for `gEarly` on `0` under `c1` (lowered, without contract
statements, `Req 0` holds), check-skipping compile-time evaluation of the tail-only
instrumentation gives `7`, the tail-only runtime-checked call returns `7`, and the static
obligation at `0` fails. -/
theorem cex_runtimeValue_obl_tailOnly :
    Lowered gEarly ∧ NoChecks gEarly ∧ c1.req 0 = true ∧
    CtfeConst .tailOnly .skipChecks c1 gEarly 0 7 ∧
    ¬ (RuntimeValue .tailOnly c1 gEarly 0 7 ↔ StaticObligationAt c1 gEarly 0) :=
  ⟨by decide, by decide, rfl, ⟨2, [], rfl⟩,
    fun h => not_staticObligationAt_gEarly_0 (h.1 (runtimeValue_gEarly_0_placement 0).1)⟩

end Toy.Contracts
