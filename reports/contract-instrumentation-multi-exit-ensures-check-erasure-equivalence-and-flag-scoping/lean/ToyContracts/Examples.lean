import ToyContracts.Consequences

/-!
# Closed-form runs of the concrete programs, and definition examples (fully proved)
-/

namespace Toy.Contracts

/-! ## Closed-form halting observations -/

theorem halts_gEarly_0 (o : Obs) : Halts c1 gEarly 0 o ↔ o = ⟨[], .ret 7⟩ :=
  halts_iff_of_run_const 2 _ (fun _ => rfl)
    (by intro n hn; rcases n with _ | _ | n <;> first | rfl | omega) (by decide) o

theorem halts_gEarly_100 (o : Obs) : Halts c1 gEarly 100 o ↔ o = ⟨[100], .ret 100⟩ :=
  halts_iff_of_run_const 2 _ (fun _ => rfl)
    (by intro n hn; rcases n with _ | _ | n <;> first | rfl | omega) (by decide) o

theorem halts_gGood (x : Nat) (o : Obs) : Halts c1 gGood x o ↔ o = ⟨[x], .ret x⟩ :=
  halts_iff_of_run_const 1 _ (fun _ => rfl)
    (by intro n hn; rcases n with _ | n <;> first | rfl | omega) (by simp) o

theorem run_instr_gEarly_100 (p : Placement) (n : Nat) :
    run c1 (instr p gEarly) 100 n = ⟨[], .checkFail .pre⟩ := by
  cases p <;> rfl

theorem halts_instr_gEarly_100 (p : Placement) (o : Obs) :
    Halts c1 (instr p gEarly) 100 o ↔ o = ⟨[], .checkFail .pre⟩ :=
  halts_iff_of_run_const 0 _ (fun m => run_instr_gEarly_100 p (m + 0))
    (by intro n hn; omega) (by decide) o

theorem halts_instr_allExits_gEarly_0 (o : Obs) :
    Halts c1 (instr .allExits gEarly) 0 o ↔ o = ⟨[], .checkFail .post⟩ :=
  halts_iff_of_run_const 2 _ (fun _ => rfl)
    (by intro n hn; rcases n with _ | _ | n <;> first | rfl | omega) (by decide) o

theorem halts_instr_tailOnly_gEarly_0 (o : Obs) :
    Halts c1 (instr .tailOnly gEarly) 0 o ↔ o = ⟨[], .ret 7⟩ :=
  halts_iff_of_run_const 2 _ (fun _ => rfl)
    (by intro n hn; rcases n with _ | _ | n <;> first | rfl | omega) (by decide) o

theorem halts_assumeErase_instr_gEarly_0 (o : Obs) :
    Halts c1 (assumeErase (instr .allExits gEarly)) 0 o ↔ o = ⟨[], .ret 7⟩ :=
  halts_iff_of_run_const 2 _ (fun _ => rfl)
    (by intro n hn; rcases n with _ | _ | n <;> first | rfl | omega) (by decide) o

theorem halts_instr_allExits_gGood (x : Nat) (hx : x < 100) (o : Obs) :
    Halts c1 (instr .allExits gGood) x o ↔ o = ⟨[x], .ret x⟩ := by
  have hr : c1.req x = true := by simp [c1, hx]
  have he : c1.ens x x = true := by simp [c1]
  refine halts_iff_of_run_const 1 _ (fun m => ?_) (fun n hn => ?_) (by simp) o
  · simp [run, instr, gGood, instrBlock, Placement.selects, execStmts, runFrom, evalOp, hr, he]
  · rcases n with _ | n
    · simp [run, instr, gGood, execStmts, runFrom, hr]
    · omega

theorem run_gTry_1 (c : Contract) (n : Nat) :
    run c gTry 1 (n + 1) = ⟨[], .ret 9⟩ := rfl

theorem halts_gTry_1 (c : Contract) (o : Obs) : Halts c gTry 1 o ↔ o = ⟨[], .ret 9⟩ :=
  halts_iff_of_run_const 1 _ (fun _ => rfl)
    (by intro n hn; rcases n with _ | n <;> first | rfl | omega) (by decide) o

theorem halts_lower_gTry_1 (o : Obs) : Halts c1 (lower gTry) 1 o ↔ o = ⟨[], .ret 9⟩ :=
  halts_iff_of_run_const 2 _ (fun _ => rfl)
    (by intro n hn; rcases n with _ | _ | n <;> first | rfl | omega) (by decide) o

theorem halts_instr_allExits_gTry_1 (c : Contract) (hr : c.req 1 = true) (o : Obs) :
    Halts c (instr .allExits gTry) 1 o ↔ o = ⟨[], .ret 9⟩ := by
  refine halts_iff_of_run_const 1 _ (fun m => ?_) (fun n hn => ?_) (by decide) o
  · simp [run, instr, gTry, instrBlock, execStmts, runFrom, evalOp, evalRv, Store.set, hr]
  · rcases n with _ | n
    · simp [run, instr, gTry, execStmts, runFrom, hr]
    · omega

theorem halts_instr_allExits_gInt_3 (o : Obs) :
    Halts cThree (instr .allExits gInt) 3 o ↔ o = ⟨[], .checkFail .post⟩ :=
  halts_iff_of_run_const 1 _ (fun _ => rfl)
    (by intro n hn; rcases n with _ | n <;> first | rfl | omega) (by decide) o

theorem halts_gInt_3 (o : Obs) : Halts cThree gInt 3 o ↔ o = ⟨[], .checkFail .post⟩ :=
  halts_iff_of_run_const 1 _ (fun _ => rfl)
    (by intro n hn; rcases n with _ | n <;> first | rfl | omega) (by decide) o

theorem halts_assumeErase_instr_gInt_3 (o : Obs) :
    Halts cThree (assumeErase (instr .allExits gInt)) 3 o ↔ o = ⟨[], .ret 3⟩ :=
  halts_iff_of_run_const 1 _ (fun _ => rfl)
    (by intro n hn; rcases n with _ | n <;> first | rfl | omega) (by decide) o

theorem halts_fOut (o : Obs) : Halts c1 fOut 0 o ↔ o = ⟨[], .stuck⟩ :=
  halts_iff_of_run_const 2 _ (fun _ => rfl)
    (by intro n hn; rcases n with _ | _ | n <;> first | rfl | omega) (by decide) o

theorem halts_lower_fOut (o : Obs) : Halts c1 (lower fOut) 0 o ↔ o = ⟨[], .ret 5⟩ :=
  halts_iff_of_run_const 2 _ (fun _ => rfl)
    (by intro n hn; rcases n with _ | _ | n <;> first | rfl | omega) (by decide) o

theorem run_gLoop (x n : Nat) : run c1 gLoop x n = ⟨List.replicate n 1, .fuelOut⟩ := by
  simpa [run, gLoop, execStmts] using runFrom_gLoop x n (fun _ => 0) []

/-- Without `JumpsInRange`, a return of the instrumented lowering need not be a return of the
function as written: on `5` under `c1`, `fOut` halts `stuck`, while `instr .allExits (lower fOut)`
returns `5`, and `Req 5` and `Ens 5 5` hold. -/
theorem lower_fOut_returns_where_fOut_stuck :
    ¬ JumpsInRange fOut ∧ Halts c1 fOut 5 ⟨[], .stuck⟩ ∧
    Halts c1 (instr .allExits (lower fOut)) 5 ⟨[], .ret 5⟩ ∧
    c1.req 5 = true ∧ c1.ens 5 5 = true :=
  ⟨by decide, ⟨by decide, 2, rfl⟩, ⟨by decide, 2, rfl⟩, rfl, rfl⟩

/-! ## Syntax-level predicates -/

/-- `Lowered`: admits a function whose exits are all explicit `ret` edges. -/
theorem lowered_gEarly : Lowered gEarly := by decide
/-- `Lowered`: rejects a function still containing the source form of `?`. -/
theorem not_lowered_gTry : ¬ Lowered gTry := by decide
/-- `lower` produces a lowered function. -/
theorem lowered_lower_gTry : Lowered (lower gTry) := by decide

/-- `JumpsInRange`: admits `gEarly`. -/
theorem jumpsInRange_gEarly : JumpsInRange gEarly := by decide
/-- `JumpsInRange`: rejects `fOut`, whose entry jumps to the missing index `3`. -/
theorem not_jumpsInRange_fOut : ¬ JumpsInRange fOut := by decide
/-- `JumpsInRange`: rejects the function with no blocks (its entry is not a block index), although
lowering leaves it unchanged. -/
theorem not_jumpsInRange_gStuck_and_lower_eq : ¬ JumpsInRange gStuck ∧ lower gStuck = gStuck :=
  ⟨by decide, rfl⟩

/-- `NoChecks`: admits a function as written without contract statements. -/
theorem noChecks_gEarly : NoChecks gEarly := by decide
/-- `NoChecks`: rejects a function containing an `ensures` check. -/
theorem not_noChecks_gInt : ¬ NoChecks gInt := by decide
/-- `NoChecks`: rejects an instrumented function. -/
theorem not_noChecks_instr_gEarly : ¬ NoChecks (instr .allExits gEarly) := by decide

/-- `Placement.selects`: all-exits selects early returns. -/
theorem selects_allExits_early : Placement.allExits.selects .early = true := rfl
/-- `Placement.selects`: tail-only does not select early returns or `?` error paths. -/
theorem not_selects_tailOnly_early_tryErr :
    Placement.tailOnly.selects .early = false ∧ Placement.tailOnly.selects .tryErr = false :=
  ⟨rfl, rfl⟩

/-- `instr .allExits` puts an `ensures` check before the early return of `gEarly`. -/
theorem instr_allExits_gEarly_block2 :
    (instr .allExits gEarly).blocks[2]? = some ⟨[.checkEns (.lit 7)], .ret .early (.lit 7)⟩ := by
  decide
/-- `instr .tailOnly` leaves the early return of `gEarly` unchecked. -/
theorem instr_tailOnly_gEarly_block2 :
    (instr .tailOnly gEarly).blocks[2]? = some ⟨[], .ret .early (.lit 7)⟩ := by decide
/-- `instr` puts no `ensures` check on a panic path. -/
theorem instr_allExits_gPanic_blocks : (instr .allExits gPanic).blocks = gPanic.blocks := by
  decide
/-- `instr` puts the `requires` check first in the prologue. -/
theorem instr_gEarly_prologue : (instr .allExits gEarly).prologue = [.checkReq] := rfl

/-- `erase` undoes instrumentation of a function without contract statements. -/
theorem erase_instr_allExits_gEarly : erase (instr .allExits gEarly) = gEarly := by decide
/-- `erase` also deletes contract statements present in the function as written. -/
theorem erase_gInt_ne : erase gInt ≠ gInt := by decide

/-- `assumeErase`: the prologue is exactly the `requires` assumption. -/
theorem assumeErase_instr_gEarly_prologue :
    (assumeErase (instr .allExits gEarly)).prologue = [.assumeReq] := by decide
/-- `assumeErase`: no `ensures` check remains. -/
theorem assumeErase_instr_gEarly_blocks :
    (assumeErase (instr .allExits gEarly)).blocks = gEarly.blocks := by decide

/-- `lower`: the `?` of `gTry` becomes a branch to the fresh `ret .tryErr 9` block `2`. -/
theorem lower_gTry_blocks :
    (lower gTry).blocks.take 3 =
      [⟨[.assign 0 (.sub .arg (.lit 1))], .branch (.loc 0) 1 2⟩, ⟨[], .ret .tail (.loc 0)⟩,
       ⟨[], .ret .tryErr (.lit 9)⟩] := by decide
/-- `lower`: blocks without `?` keep their terminators (here: all of `gEarly`). -/
theorem lower_gEarly_take : (lower gEarly).blocks.take 3 = gEarly.blocks := by decide
/-- `lower`: blocks are appended even when there is no `?` (three dead `panic` blocks for
`gEarly`), so the lowering differs from the function. -/
theorem lower_gEarly_ne : lower gEarly ≠ gEarly ∧ (lower gEarly).blocks.length = 6 := by decide

/-! ## Semantics -/

/-- `run`: `gEarly` on `0` takes the early return `7`. -/
theorem run_gEarly_0_eq : run c1 gEarly 0 2 = ⟨[], .ret 7⟩ := rfl
/-- `run`: a jump to a missing block is `stuck`. -/
theorem run_fOut_eq : run c1 fOut 0 2 = ⟨[], .stuck⟩ := rfl
/-- `run`: a panic ends the run with outcome `panic`, not a return. -/
theorem run_gPanic_eq : run c1 gPanic 4 1 = ⟨[4], .panic⟩ := rfl

/-- `Halts`: `gGood` halts on `5` with events `[5]` and return `5`. -/
theorem halts_gGood_5 : Halts c1 gGood 5 ⟨[5], .ret 5⟩ := (halts_gGood 5 _).2 rfl
/-- `Halts`: excludes fuel exhaustion. -/
theorem not_halts_fuelOut : ¬ Halts c1 gGood 5 ⟨[], .fuelOut⟩ := fun h => h.1 rfl
/-- `Halts`: the emitting loop has no halting observation. -/
theorem not_halts_gLoop (x : Nat) (o : Obs) : ¬ Halts c1 gLoop x o := by
  rintro ⟨hne, n, hn⟩
  rw [run_gLoop] at hn
  exact hne (hn ▸ rfl)

/-- `RunEqAt`: erasure and instrumentation of `gGood` agree at `5` at every fuel. -/
theorem runEqAt_erase_instr_gGood_5 :
    RunEqAt c1 (erase (instr .allExits gGood)) (instr .allExits gGood) 5 := by
  intro n; rcases n with _ | n <;> rfl
/-- `RunEqAt`: they differ at `100`, where `Req` fails. -/
theorem not_runEqAt_erase_instr_gGood_100 :
    ¬ RunEqAt c1 (erase (instr .allExits gGood)) (instr .allExits gGood) 100 := by
  intro h; have := h 0; revert this; decide
/-- `HaltsEqAt`: `gGood` and `gEarly` differ at `0`. -/
theorem not_haltsEqAt_gGood_gEarly_0 : ¬ HaltsEqAt c1 gGood gEarly 0 := by
  intro h
  have h1 := (h ⟨[0], .ret 0⟩).1 ((halts_gGood 0 _).2 rfl)
  rw [halts_gEarly_0] at h1
  cases h1
/-- `HaltsEqAt` without `RunEqAt`: `lower gTry` and `gTry` have the same halting observations on
`1` but differ at fuel `1` (the lowered `?` error exit takes one more block execution). -/
theorem haltsEqAt_not_runEqAt_lower_gTry_1 :
    HaltsEqAt c1 (lower gTry) gTry 1 ∧ ¬ RunEqAt c1 (lower gTry) gTry 1 := by
  refine ⟨fun o => by rw [halts_lower_gTry_1, halts_gTry_1], fun h => ?_⟩
  have h1 := h 1
  revert h1; decide

/-! ## The contract wrapper -/

/-- `wrapObs`: keeps a return satisfying `Ens`. -/
theorem wrapObs_keep : wrapObs c1 5 ⟨[5], .ret 5⟩ = ⟨[5], .ret 5⟩ := by decide
/-- `wrapObs`: turns a return violating `Ens` into an `ensures` failure with the same events. -/
theorem wrapObs_fail : wrapObs c1 0 ⟨[3], .ret 7⟩ = ⟨[3], .checkFail .post⟩ := by decide
/-- `wrapObs`: leaves a panic unchanged. -/
theorem wrapObs_panic : wrapObs c1 0 ⟨[0], .panic⟩ = ⟨[0], .panic⟩ := by decide
/-- `instrObs`: a `requires` failure with no events when `Req` fails. -/
theorem instrObs_req_false : instrObs c1 100 ⟨[100], .ret 100⟩ = ⟨[], .checkFail .pre⟩ := by
  decide

/-! ## Obligations -/

/-- `EnsOnReturnsAt`: holds for `gGood` on every `x`. -/
theorem ensOnReturnsAt_gGood (x : Nat) : EnsOnReturnsAt c1 gGood x := by
  intro tr r h
  rw [halts_gGood] at h
  cases h
  simp [c1]
/-- `EnsOnReturnsAt`: fails for `gEarly` on `0` (early return `7 > 0`). -/
theorem not_ensOnReturnsAt_gEarly_0 : ¬ EnsOnReturnsAt c1 gEarly 0 := by
  intro h
  have := h [] 7 ((halts_gEarly_0 _).2 rfl)
  revert this; decide
/-- `StaticObligation`: holds for `gGood`. -/
theorem staticObligation_gGood : StaticObligation c1 gGood := fun x _ => ensOnReturnsAt_gGood x
/-- `StaticObligation`: fails for `gEarly`. -/
theorem not_staticObligation_gEarly : ¬ StaticObligation c1 gEarly :=
  fun h => not_ensOnReturnsAt_gEarly_0 (h 0 rfl)
/-- `StaticObligationAt`: holds vacuously where `Req` fails. -/
theorem staticObligationAt_gEarly_100 : StaticObligationAt c1 gEarly 100 := by
  intro h; exact absurd h (by decide)
/-- `StaticObligationAt`: holds non-vacuously for `gGood` at `5`, where `Req` holds. -/
theorem staticObligationAt_gGood_5 : c1.req 5 = true ∧ StaticObligationAt c1 gGood 5 :=
  ⟨rfl, fun _ => ensOnReturnsAt_gGood 5⟩
/-- `StaticObligationAt`: fails for `gEarly` at `0`. -/
theorem not_staticObligationAt_gEarly_0 : ¬ StaticObligationAt c1 gEarly 0 :=
  fun h => not_ensOnReturnsAt_gEarly_0 (h rfl)

/-- `UBRefinesAt`: the checked `gGood` refines its assume-erasure at `5`. -/
theorem ubRefinesAt_instr_assumeErase_gGood_5 :
    UBRefinesAt c1 (instr .allExits gGood) (assumeErase (instr .allExits gGood)) 5 :=
  instr_allExits_ubRefinesAt_assumeErase_of_noChecks_of_staticObligationAt c1 gGood (by decide)
    5 (fun _ => ensOnReturnsAt_gGood 5)
/-- `UBRefinesAt`: the checked `gEarly` does not refine its assume-erasure at `0` (it ends with an
`ensures` failure, which the assume-erasure neither produces nor licenses by UB). -/
theorem not_ubRefinesAt_instr_assumeErase_gEarly_0 :
    ¬ UBRefinesAt c1 (instr .allExits gEarly) (assumeErase (instr .allExits gEarly)) 0 := by
  intro h
  rcases h _ ((halts_instr_allExits_gEarly_0 _).2 rfl) with h1 | ⟨tr, h1, _⟩
  · rw [halts_assumeErase_instr_gEarly_0] at h1; cases h1
  · rw [halts_assumeErase_instr_gEarly_0] at h1; cases h1
/-- `UBRefinesAt` compares halting runs of the target only: the non-halting `gLoop` refines `gGood`
at `5`, although `gGood` halts there with a return and no UB. -/
theorem ubRefinesAt_gLoop_gGood_5 :
    UBRefinesAt c1 gLoop gGood 5 ∧ Halts c1 gGood 5 ⟨[5], .ret 5⟩ ∧ (∀ o, ¬ Halts c1 gLoop 5 o) :=
  ⟨ubRefinesAt_of_forall_not_halts (not_halts_gLoop 5) gGood, halts_gGood_5, not_halts_gLoop 5⟩

/-! ## Crates and compile-time evaluation -/

/-- `holder`: callee-side checks are held by the defining crate, caller-side by the caller. -/
theorem holder_cs1 : holder .calleeSide cs1 = 1 ∧ holder .callerSide cs1 = 0 := ⟨rfl, rfl⟩
/-- `governingCrate`: at instantiation, a generic callee's callee-side check is governed by the
instantiating crate (here the calling crate `0`). -/
theorem governingCrate_csGen_atInstantiation :
    governingCrate .calleeSide .atInstantiation csGen = 0 := rfl
/-- `governingCrate`: at instantiation, a non-generic callee's check is still governed by the
defining crate. -/
theorem governingCrate_cs1_atInstantiation :
    governingCrate .calleeSide .atInstantiation cs1 = 1 := rfl
/-- `governingCrate`: for a generic callee instantiated in a third crate, resolution at
instantiation selects that crate, which is neither the calling nor the defining crate. -/
theorem governingCrate_csGen3_atInstantiation :
    governingCrate .calleeSide .atInstantiation csGen3 = 2 ∧
    governingCrate .calleeSide .atInstantiation csGen3 ≠ csGen3.callerCrate ∧
    governingCrate .calleeSide .atInstantiation csGen3 ≠ csGen3.defCrate := by decide

/-- `callRun`: with the caller's flag on, caller-side placement turns `gEarly`'s early return `7`
on `0` into an `ensures` failure, while callee-side placement (defining crate's flag off) returns
`7`. -/
theorem callRun_gEarly_0_examples :
    callRun flCallerOn .callerSide .atDefinition cs1 c1 gEarly 0 2 = ⟨[], .checkFail .post⟩ ∧
    callRun flCallerOn .calleeSide .atDefinition cs1 c1 gEarly 0 2 = ⟨[], .ret 7⟩ := ⟨rfl, rfl⟩

/-- `ViolationAt`: an `ensures` violation (`gEarly` on `0`). -/
theorem violationAt_gEarly_0 : ViolationAt c1 gEarly 0 :=
  .inr ⟨rfl, [], 7, (halts_gEarly_0 _).2 rfl, rfl⟩
/-- `ViolationAt`: a `requires` violation (`gEarly` on `100`). -/
theorem violationAt_gEarly_100 : ViolationAt c1 gEarly 100 := .inl rfl
/-- `ViolationAt`: no violation for `gGood` on `5`. -/
theorem not_violationAt_gGood_5 : ¬ ViolationAt c1 gGood 5 := by
  rintro (h | ⟨_, tr, r, h, he⟩)
  · cases h
  · rw [halts_gGood] at h; cases h; cases he

/-- `Detects`: the caller-side check (caller flag on) reports `gEarly`'s violation on `0`. -/
theorem detects_callerOn_callerSide_gEarly_0 :
    Detects flCallerOn .callerSide .atDefinition cs1 c1 gEarly 0 := ⟨2, [], .post, rfl⟩
/-- `Detects`: nothing is reported for `gGood` on `5` even with every flag on. -/
theorem not_detects_gGood_5 :
    ¬ Detects (fun _ => true) .calleeSide .atDefinition cs1 c1 gGood 5 := by
  rintro ⟨n, tr, k, h⟩
  rcases n with _ | n
  · cases h
  · cases h

/-- With the governing crate's flag off, callee-side placement never reports `gEarly`'s violation
on `0`. -/
theorem not_detects_calleeSide_off_gEarly_0 (fl : Nat → Bool) (res : Resolution) (cs : CallSite)
    (h : fl (governingCrate .calleeSide res cs) = false) :
    ¬ Detects fl .calleeSide res cs c1 gEarly 0 := by
  rintro ⟨n, tr, k, hn⟩
  rw [callRun_eq_ite_governingFlag_of_lowered fl .calleeSide res cs c1 gEarly (by decide) 0 n,
    h] at hn
  rcases n with _ | _ | n
  · cases hn
  · cases hn
  · cases hn

/-- `Detects` for a generic callee instantiated in a third crate, under callee-side placement with
resolution at instantiation: `gEarly`'s violation on `0` is reported when the instantiating crate's
flag alone is on, and not reported when the calling and defining crates' flags are on and the
instantiating crate's flag is off. -/
theorem detects_csGen3_follows_instCrate :
    Detects flTwoOn .calleeSide .atInstantiation csGen3 c1 gEarly 0 ∧
    flZeroOneOn csGen3.callerCrate = true ∧ flZeroOneOn csGen3.defCrate = true ∧
    ¬ Detects flZeroOneOn .calleeSide .atInstantiation csGen3 c1 gEarly 0 :=
  ⟨⟨2, [], .post, rfl⟩, rfl, rfl, not_detects_calleeSide_off_gEarly_0 _ _ _ rfl⟩

/-- `ctfeRun`: on `100` (where `Req` fails), check-skipping evaluation of the instrumented `gEarly`
returns `100` and check-evaluating evaluation fails the `requires` check. -/
theorem ctfeRun_gEarly_100_examples :
    ctfeRun .skipChecks c1 (instr .allExits gEarly) 100 2 = ⟨[100], .ret 100⟩ ∧
    ctfeRun .evalChecks c1 (instr .allExits gEarly) 100 2 = ⟨[], .checkFail .pre⟩ := ⟨rfl, rfl⟩

/-- `CtfeConst`: check-skipping compile-time evaluation of `gEarly` on `100` gives `100`. -/
theorem ctfeConst_skip_gEarly_100 : CtfeConst .allExits .skipChecks c1 gEarly 100 100 :=
  ⟨2, [100], rfl⟩
/-- `CtfeConst`: check-evaluating compile-time evaluation gives no constant there. -/
theorem not_ctfeConst_eval_gEarly_100 (r : Nat) :
    ¬ CtfeConst .allExits .evalChecks c1 gEarly 100 r := by
  rintro ⟨n, tr, h⟩
  rw [ctfeRun_evalChecks_eq, run_instr_gEarly_100] at h
  cases h
/-- `RuntimeValue`: the checked `gGood` returns `5` on `5`. -/
theorem runtimeValue_gGood_5 : RuntimeValue .allExits c1 gGood 5 5 :=
  ⟨[5], (halts_instr_allExits_gGood 5 (by decide) _).2 rfl⟩
/-- `RuntimeValue`: the checked `gEarly` returns nothing on `100`. -/
theorem not_runtimeValue_gEarly_100 (r : Nat) : ¬ RuntimeValue .allExits c1 gEarly 100 r := by
  rintro ⟨tr, h⟩
  rw [halts_instr_gEarly_100] at h
  cases h
/-- `RuntimeValue` depends on the placement: the tail-only checked `gEarly` returns `7` on `0`,
the all-exits checked `gEarly` returns no value there. -/
theorem runtimeValue_gEarly_0_placement (r : Nat) :
    RuntimeValue .tailOnly c1 gEarly 0 7 ∧ ¬ RuntimeValue .allExits c1 gEarly 0 r := by
  refine ⟨⟨[], (halts_instr_tailOnly_gEarly_0 _).2 rfl⟩, fun ⟨tr, h⟩ => ?_⟩
  rw [halts_instr_allExits_gEarly_0] at h
  cases h

end Toy.Contracts
