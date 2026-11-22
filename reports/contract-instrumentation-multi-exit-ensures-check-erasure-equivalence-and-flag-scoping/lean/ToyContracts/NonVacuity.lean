import ToyContracts.Counterexamples

/-!
# Non-vacuity witnesses (fully proved): concrete instances satisfying all hypotheses
-/

namespace Toy.Contracts

/-- `run_instr_allExits_eq_instrObs_of_lowered`: `gEarly` (a tail return and an early return) is
lowered. -/
theorem nonvacuity_run_instr_allExits : Lowered gEarly := by decide

/-- `req_and_ens_of_halts_ret_instr_allExits_lower`: its hypothesis holds for `gTry` on `5`
(returns `4`). -/
theorem nonvacuity_req_and_ens_lower :
    Halts c1 (instr .allExits (lower gTry)) 5 ⟨[], .ret 4⟩ := ⟨by decide, 3, rfl⟩

/-- `halts_lower_iff_of_jumpsInRange`: `gTry` has all jumps in range. -/
theorem nonvacuity_halts_lower : JumpsInRange gTry := by decide

/-- `erase_instr_eq_of_noChecks`: `gEarly` has no contract statements. -/
theorem nonvacuity_erase_instr : NoChecks gEarly := by decide

/-- `instr_allExits_obsEq_self_iff_ensOnReturnsAt_of_lowered_of_req`: two instances satisfying all
hypotheses, one where both sides hold (`gGood` on `5`) and one where both fail (`gEarly` on `0`),
and one satisfying them although `NoChecks` fails (`gInt` on `3` under `cThree`). -/
theorem nonvacuity_instrSelf :
    (Lowered gGood ∧ c1.req 5 = true ∧ EnsOnReturnsAt c1 gGood 5) ∧
    (Lowered gEarly ∧ c1.req 0 = true ∧ ¬ EnsOnReturnsAt c1 gEarly 0) ∧
    (Lowered gInt ∧ ¬ NoChecks gInt ∧ cThree.req 3 = true) :=
  ⟨⟨by decide, rfl, ensOnReturnsAt_gGood 5⟩, ⟨by decide, rfl, not_ensOnReturnsAt_gEarly_0⟩,
    ⟨by decide, by decide, rfl⟩⟩

/-- `erasure_obsEq_iff_ensOnReturnsAt_of_lowered_of_noChecks_of_req`: two instances satisfying all
hypotheses, one where both sides hold (`gGood` on `5`) and one where both fail (`gEarly` on `0`). -/
theorem nonvacuity_erasure_pointwise :
    (Lowered gGood ∧ NoChecks gGood ∧ c1.req 5 = true ∧ EnsOnReturnsAt c1 gGood 5 ∧
      RunEqAt c1 (erase (instr .allExits gGood)) (instr .allExits gGood) 5) ∧
    (Lowered gEarly ∧ NoChecks gEarly ∧ c1.req 0 = true ∧ ¬ EnsOnReturnsAt c1 gEarly 0) :=
  ⟨⟨by decide, by decide, rfl, ensOnReturnsAt_gGood 5, runEqAt_erase_instr_gGood_5⟩,
   ⟨by decide, by decide, rfl, not_ensOnReturnsAt_gEarly_0⟩⟩

/-- `erasure_obsEq_onReq_iff_staticObligation_of_lowered_of_noChecks`: `gGood` (obligation holds)
and `gEarly` (obligation fails) both satisfy the hypotheses. -/
theorem nonvacuity_erasure_global :
    (Lowered gGood ∧ NoChecks gGood ∧ StaticObligation c1 gGood) ∧
    (Lowered gEarly ∧ NoChecks gEarly ∧ ¬ StaticObligation c1 gEarly) :=
  ⟨⟨by decide, by decide, staticObligation_gGood⟩,
   ⟨by decide, by decide, not_staticObligation_gEarly⟩⟩

/-- `not_haltsEqAt_erase_instr_of_req_false` and `not_assumeErase_ubRefinesAt_instr_of_req_false`:
`Req 100` fails under `c1`. -/
theorem nonvacuity_req_false : c1.req 100 = false := rfl

/-- `run_assumeErase_eq_ite_req`: both branches occur (`Req 5` holds, `Req 100` fails). -/
theorem nonvacuity_assumeErase : c1.req 5 = true ∧ c1.req 100 = false := ⟨rfl, rfl⟩

/-- `instr_allExits_ubRefinesAt_assumeErase_of_noChecks_of_staticObligationAt`: `gGood` on `5`
(lowered), and the unlowered `gTry` on `5`. -/
theorem nonvacuity_ubRefines :
    (NoChecks gGood ∧ c1.req 5 = true ∧ StaticObligationAt c1 gGood 5) ∧
    (¬ Lowered gTry ∧ NoChecks gTry ∧ c1.req 5 = true ∧ StaticObligationAt c1 gTry 5) := by
  refine ⟨⟨by decide, rfl, fun _ => ensOnReturnsAt_gGood 5⟩,
    ⟨by decide, by decide, rfl, fun _ tr r ⟨_, n, hn⟩ => ?_⟩⟩
  rcases n with _ | _ | n <;> cases hn
  decide

/-- `callRun_eq_ite_governingFlag_of_lowered`: `gEarly` is lowered. -/
theorem nonvacuity_callRun : Lowered gEarly := by decide

/-- `detects_iff_governingFlag_of_lowered_of_noChecks_of_violation`: `gEarly` on `0` (an `ensures`
violation) and on `100` (a `requires` violation). -/
theorem nonvacuity_detects :
    Lowered gEarly ∧ NoChecks gEarly ∧ ViolationAt c1 gEarly 0 ∧ ViolationAt c1 gEarly 100 :=
  ⟨by decide, by decide, violationAt_gEarly_0, violationAt_gEarly_100⟩

/-- `callRun_eq_run_of_not_violation`: `gGood` on `5`. -/
theorem nonvacuity_not_violation : ¬ ViolationAt c1 gGood 5 := not_violationAt_gGood_5

/-- `runtimeValue_iff_req_and_ens_of_lowered_of_noChecks_of_ctfeSkipConst`: `gEarly` on `0`
(constant `7`) and on `5` (constant `5`). -/
theorem nonvacuity_ctfe :
    (Lowered gEarly ∧ NoChecks gEarly ∧ CtfeConst .allExits .skipChecks c1 gEarly 0 7) ∧
    CtfeConst .allExits .skipChecks c1 gEarly 5 5 :=
  ⟨⟨by decide, by decide, ⟨2, [], rfl⟩⟩, ⟨2, [5], rfl⟩⟩

/-- `runtimeValue_iff_staticObligationAt_of_lowered_of_noChecks_of_req_of_ctfeSkipConst`: `gEarly`
on `0`. -/
theorem nonvacuity_ctfe_req :
    Lowered gEarly ∧ NoChecks gEarly ∧ c1.req 0 = true ∧
    CtfeConst .allExits .skipChecks c1 gEarly 0 7 :=
  ⟨by decide, by decide, rfl, ⟨2, [], rfl⟩⟩

end Toy.Contracts
