import ToyContracts.Results

/-!
# Consequences of the main results used in the non-claims (fully proved)
-/

namespace Toy.Contracts

/-- When `Req x` holds, a call of a callee without contract statements that never returns normally
on `x` (it panics, diverges or gets stuck) reports nothing, under every flag assignment, placement,
resolution and call site. -/
theorem not_detects_of_noChecks_of_req_of_no_ret (fl : Nat → Bool) (s : Site) (res : Resolution)
    (cs : CallSite) (c : Contract) (g : Fn) (hnc : NoChecks g) (x : Nat)
    (hreq : c.req x = true) (hnoret : ∀ tr r, ¬ Halts c g x ⟨tr, .ret r⟩) :
    ¬ Detects fl s res cs c g x := by
  have hnov : ¬ ViolationAt c g x := by
    rintro (hr | ⟨_, tr, r, hh, _⟩)
    · rw [hreq] at hr; cases hr
    · exact hnoret tr r hh
  rintro ⟨n, tr, k, hcall⟩
  rw [callRun_eq_run_of_not_violation fl s res cs c g x hnov n] at hcall
  exact run_no_checkFail_of_noChecks (c := c) hnc x n k (by rw [hcall])

/-- When `Req x` fails and the governing crate's flag is on, every call ends with a `requires`
failure and no events at every fuel, whatever the callee does (no hypothesis on `g`). -/
theorem callRun_eq_checkFail_pre_of_req_false_of_governingFlag (fl : Nat → Bool) (s : Site)
    (res : Resolution) (cs : CallSite) (c : Contract) (g : Fn) (x : Nat) (h : c.req x = false)
    (hfl : fl (governingCrate s res cs) = true) (n : Nat) :
    callRun fl s res cs c g x n = ⟨[], .checkFail .pre⟩ := by
  have h1 := run_instr_of_req_false c .allExits g x h n
  obtain ⟨cc, dc, ic, gen⟩ := cs
  cases s <;> cases res <;> cases gen <;>
    cases hcc : fl cc <;> cases hdc : fl dc <;> cases hic : fl ic <;>
    simp_all [callRun, compileInDefCrate, instantiateIn, callInCallerCrate, governingCrate,
      instrObs]

/-- The unqualified reading "a call of a lowered callee without contract statements that panics
reports nothing even with the governing flag on" is false: `gPanic` (lowered, without contract
statements) panics on `100` as written, yet with every flag on its callee-side call reports a
failed check, because `Req 100` fails under `c1`. -/
theorem refuted_no_report_for_panicking_call_with_flag_on :
    Lowered gPanic ∧ NoChecks gPanic ∧ c1.req 100 = false ∧
    Halts c1 gPanic 100 ⟨[100], .panic⟩ ∧
    Detects (fun _ => true) .calleeSide .atDefinition cs1 c1 gPanic 100 :=
  ⟨by decide, by decide, rfl, ⟨by decide, 1, rfl⟩, ⟨0, [], .pre, rfl⟩⟩

end Toy.Contracts
