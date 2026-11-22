import ToyContracts.Lemmas

/-!
# Main results
-/

namespace Toy.Contracts

/-! ## Multi-exit placement -/

/-- For a lowered function `g`, all-exits instrumentation is the contract wrapper on observations,
at every fuel: a `requires` failure with no events if `Req x` fails, and otherwise the unchecked
observation with every normal return of a value violating `Ens` turned into an `ensures` failure
(same events); panics, failed checks, UB, stuck runs and fuel exhaustion are unchanged. -/
theorem run_instr_allExits_eq_instrObs_of_lowered (c : Contract) (g : Fn) (hg : Lowered g)
    (x n : Nat) :
    run c (instr .allExits g) x n = instrObs c x (run c g x n) := by
  simp only [run, instr, execStmts, instrObs]
  cases hreq : c.req x
  · rfl
  · simp only [↓reduceIte]
    cases hex : execStmts c x g.prologue (fun _ => 0) [] with
    | stop ev o => exact (wrapObs_of_execStmts_stop hex).symm
    | cont σ ev => exact runFrom_instr_allExits_eq_wrapObs c g hg x n g.entry σ ev

/-- For every function `f` as written: whenever the all-exits instrumentation of its lowering
returns `r` on `x`, `Req x` and `Ens x r` hold. -/
theorem req_and_ens_of_halts_ret_instr_allExits_lower (c : Contract) (f : Fn) (x : Nat)
    (tr : List Nat) (r : Nat) (h : Halts c (instr .allExits (lower f)) x ⟨tr, .ret r⟩) :
    c.req x = true ∧ c.ens x r = true := by
  obtain ⟨_, n, hn⟩ := h
  rw [run_instr_allExits_eq_instrObs_of_lowered c (lower f) (lowered_lower f) x n] at hn
  obtain ⟨h1, h2, _⟩ := instrObs_eq_ret hn
  exact ⟨h1, h2⟩

/-- For a function whose every jump target (reachable or not) and entry are in range, lowering `?`
preserves halting observations. -/
theorem halts_lower_iff_of_jumpsInRange (c : Contract) (f : Fn) (hf : JumpsInRange f) (x : Nat)
    (o : Obs) : Halts c (lower f) x o ↔ Halts c f x o := by
  obtain ⟨hent, htgt⟩ := hf
  have hpro : (lower f).prologue = f.prologue := rfl
  have he0 : (lower f).entry = f.entry := rfl
  constructor
  · rintro ⟨hfin, n, hn⟩
    refine ⟨hfin, n, ?_⟩
    unfold run at hn ⊢
    rw [hpro, he0] at hn
    cases hex : execStmts c x f.prologue (fun _ => 0) [] with
    | stop ev o' => rw [hex] at hn; exact hn
    | cont σ ev =>
      rw [hex] at hn; dsimp only at hn ⊢
      have hfin' : (runFrom c (lower f) x n f.entry σ ev).outcome ≠ .fuelOut := hn ▸ hfin
      exact (runFrom_of_lower_fin htgt x n hent σ ev hfin').trans hn
  · rintro ⟨hfin, n, hn⟩
    refine ⟨hfin, n + 1, ?_⟩
    unfold run at hn ⊢
    rw [hpro, he0]
    cases hex : execStmts c x f.prologue (fun _ => 0) [] with
    | stop ev o' => rw [hex] at hn; exact hn
    | cont σ ev =>
      rw [hex] at hn; dsimp only at hn ⊢
      have hfin' : (runFrom c f x n f.entry σ ev).outcome ≠ .fuelOut := hn ▸ hfin
      exact (runFrom_lower_of_fin htgt x n hent σ ev hfin').trans hn

/-! ## Erasure equivalence -/

/-- For a function without contract statements, erasing its instrumentation (any placement) gives
it back. -/
theorem erase_instr_eq_of_noChecks (p : Placement) (g : Fn) (hg : NoChecks g) :
    erase (instr p g) = g := by
  obtain ⟨hp, hb⟩ := hg
  cases g with
  | mk pro ent blks =>
    simp only [erase, instr, filter_checkReq_cons, filter_not_isContract_of_all hp,
      map_erase_instrBlock p hb]

/-- For a lowered function `g` (contract statements in `g` allowed) and an input `x` with `Req x`:
the all-exits instrumentation and `g` itself are fuel-exactly identical at `x`, and also have the
same halting observations at `x`, each iff every normal return of `g` on `x` satisfies `Ens`. -/
theorem instr_allExits_obsEq_self_iff_ensOnReturnsAt_of_lowered_of_req (c : Contract) (g : Fn)
    (hg : Lowered g) (x : Nat) (hreq : c.req x = true) :
    (RunEqAt c (instr .allExits g) g x ↔ EnsOnReturnsAt c g x) ∧
    (HaltsEqAt c (instr .allExits g) g x ↔ EnsOnReturnsAt c g x) := by
  have h1 : EnsOnReturnsAt c g x → RunEqAt c (instr .allExits g) g x := fun hens n => by
    rw [run_instr_allExits_eq_instrObs_of_lowered c g hg x n]
    exact instrObs_run_eq_of_req_of_ensOnReturnsAt c g x hreq hens n
  have h2 : HaltsEqAt c (instr .allExits g) g x → EnsOnReturnsAt c g x := by
    intro hh tr r hret
    obtain ⟨_, m, hm⟩ := (hh ⟨tr, .ret r⟩).mpr hret
    rw [run_instr_allExits_eq_instrObs_of_lowered c g hg x m] at hm
    exact (instrObs_eq_ret hm).2.1
  exact ⟨⟨fun h => h2 (haltsEqAt_of_runEqAt h), h1⟩,
    ⟨h2, fun hens => haltsEqAt_of_runEqAt (h1 hens)⟩⟩

/-- For a lowered function without contract statements and an input `x` with `Req x`: the erasure
of the all-exits instrumentation is fuel-exactly identical to it at `x`, and also has the same
halting observations at `x`, each iff every normal return of `g` on `x` satisfies `Ens`. -/
theorem erasure_obsEq_iff_ensOnReturnsAt_of_lowered_of_noChecks_of_req (c : Contract) (g : Fn)
    (hg : Lowered g) (hnc : NoChecks g) (x : Nat) (hreq : c.req x = true) :
    (RunEqAt c (erase (instr .allExits g)) (instr .allExits g) x ↔ EnsOnReturnsAt c g x) ∧
    (HaltsEqAt c (erase (instr .allExits g)) (instr .allExits g) x ↔ EnsOnReturnsAt c g x) := by
  rw [erase_instr_eq_of_noChecks .allExits g hnc]
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ :=
    instr_allExits_obsEq_self_iff_ensOnReturnsAt_of_lowered_of_req c g hg x hreq
  exact ⟨⟨fun h => a1 fun n => (h n).symm, fun h n => (a2 h n).symm⟩,
    ⟨fun h => b1 fun o => (h o).symm, fun h o => (b2 h o).symm⟩⟩

/-- For a lowered function without contract statements: erasure is equivalent to the all-exits
instrumentation on all `Req` inputs iff the static obligation holds (for fuel-exact identity and
for identity of halting observations). -/
theorem erasure_obsEq_onReq_iff_staticObligation_of_lowered_of_noChecks (c : Contract) (g : Fn)
    (hg : Lowered g) (hnc : NoChecks g) :
    ((∀ x, c.req x = true → RunEqAt c (erase (instr .allExits g)) (instr .allExits g) x) ↔
        StaticObligation c g) ∧
    ((∀ x, c.req x = true → HaltsEqAt c (erase (instr .allExits g)) (instr .allExits g) x) ↔
        StaticObligation c g) := by
  constructor
  · exact ⟨fun h x hx =>
        (erasure_obsEq_iff_ensOnReturnsAt_of_lowered_of_noChecks_of_req c g hg hnc x hx).1.mp
          (h x hx),
      fun h x hx =>
        (erasure_obsEq_iff_ensOnReturnsAt_of_lowered_of_noChecks_of_req c g hg hnc x hx).1.mpr
          (h x hx)⟩
  · exact ⟨fun h x hx =>
        (erasure_obsEq_iff_ensOnReturnsAt_of_lowered_of_noChecks_of_req c g hg hnc x hx).2.mp
          (h x hx),
      fun h x hx =>
        (erasure_obsEq_iff_ensOnReturnsAt_of_lowered_of_noChecks_of_req c g hg hnc x hx).2.mpr
          (h x hx)⟩

/-- For every placement and function, at an input with `Req x` false: the instrumentation ends
with a `requires` failure and no events at every fuel; the erasure contains no contract statement
and never ends with a failed check; so the two do not have the same halting observations. -/
theorem not_haltsEqAt_erase_instr_of_req_false (c : Contract) (p : Placement) (g : Fn) (x : Nat)
    (h : c.req x = false) :
    (∀ n, run c (instr p g) x n = ⟨[], .checkFail .pre⟩) ∧ NoChecks (erase (instr p g)) ∧
    (∀ n k, (run c (erase (instr p g)) x n).outcome ≠ .checkFail k) ∧
    ¬ HaltsEqAt c (erase (instr p g)) (instr p g) x := by
  have hinstr := run_instr_of_req_false c p g x h
  have hno := fun n k => run_no_checkFail_of_noChecks (c := c) (noChecks_erase (instr p g)) x n k
  refine ⟨hinstr, noChecks_erase _, hno, fun heq => ?_⟩
  obtain ⟨_, n, hn⟩ := (heq ⟨[], .checkFail .pre⟩).mpr ⟨nofun, 0, hinstr 0⟩
  exact hno n .pre (by rw [hn])

/-- For every function `q`: erasure plus an assumption of `Req` runs as the plain erasure at every
fuel on `Req` inputs, and reaches UB with no events at every fuel off `Req`. -/
theorem run_assumeErase_eq_ite_req (c : Contract) (q : Fn) (x n : Nat) :
    run c (assumeErase q) x n = if c.req x then run c (erase q) x n else ⟨[], .ub⟩ := by
  simp only [run, assumeErase, execStmts]
  cases c.req x
  · rfl
  · simp only [↓reduceIte]
    cases execStmts c x (erase q).prologue (fun _ => 0) [] with
    | stop ev o => rfl
    | cont σ ev => exact runFrom_congr_blocks c (assumeErase q) (erase q) rfl x n _ σ ev

/-- For a function without contract statements (in its prologue or in any block, reachable or not)
satisfying the static obligation at `x`, the checked program `instr .allExits g` UB-refines the
assume-erased program `assumeErase (instr .allExits g)` at `x` (refinement of halting observations;
`Lowered` is not assumed). -/
theorem instr_allExits_ubRefinesAt_assumeErase_of_noChecks_of_staticObligationAt (c : Contract)
    (g : Fn) (hnc : NoChecks g) (x : Nat) (hob : StaticObligationAt c g x) :
    UBRefinesAt c (instr .allExits g) (assumeErase (instr .allExits g)) x := by
  intro o ho
  cases hreq : c.req x
  · refine .inr ⟨[], ⟨nofun, 0, ?_⟩, List.nil_prefix⟩
    rw [run_assumeErase_eq_ite_req, hreq]; rfl
  · refine .inl ?_
    obtain ⟨hfin, n, hn⟩ := ho
    refine ⟨hfin, n, ?_⟩
    rw [run_assumeErase_eq_ite_req]
    simp only [hreq, ↓reduceIte]
    rw [erase_instr_eq_of_noChecks .allExits g hnc,
        ← run_instr_eq_of_req_of_ensOnReturnsAt c .allExits g x hreq (hob hreq) n, hn]

/-- For every placement and function, at an input with `Req x` false: the assume-erased program
reaches UB with no events at every fuel, the checked program ends with a `requires` failure and no
events at every fuel, and the assume-erased program does not UB-refine the checked program at `x`. -/
theorem not_assumeErase_ubRefinesAt_instr_of_req_false (c : Contract) (p : Placement) (g : Fn)
    (x : Nat) (h : c.req x = false) :
    (∀ n, run c (assumeErase (instr p g)) x n = ⟨[], .ub⟩) ∧
    (∀ n, run c (instr p g) x n = ⟨[], .checkFail .pre⟩) ∧
    ¬ UBRefinesAt c (assumeErase (instr p g)) (instr p g) x := by
  have hub : ∀ n, run c (assumeErase (instr p g)) x n = ⟨[], .ub⟩ := fun n => by
    simp [run, assumeErase, execStmts, h]
  have hinstr := run_instr_of_req_false c p g x h
  refine ⟨hub, hinstr, fun href => ?_⟩
  rcases href ⟨[], .ub⟩ ⟨nofun, 0, hub 0⟩ with ⟨_, n, hn⟩ | ⟨tr, ⟨_, n, hn⟩, _⟩ <;>
    rw [hinstr n] at hn <;> cases hn

/-! ## Flag scoping across crates -/

/-- For a lowered callee, a cross-crate call (built from the three per-crate steps) behaves as the
contract wrapper if the governing crate's flag is on and as the callee as written if it is off, at
every fuel, for both placements and both resolutions. -/
theorem callRun_eq_ite_governingFlag_of_lowered (fl : Nat → Bool) (s : Site) (res : Resolution)
    (cs : CallSite) (c : Contract) (g : Fn) (hg : Lowered g) (x n : Nat) :
    callRun fl s res cs c g x n =
      if fl (governingCrate s res cs) then instrObs c x (run c g x n) else run c g x n := by
  have h1 := run_instr_allExits_eq_instrObs_of_lowered c g hg x n
  obtain ⟨cc, dc, ic, gen⟩ := cs
  cases s <;> cases res <;> cases gen <;>
    cases hcc : fl cc <;> cases hdc : fl dc <;> cases hic : fl ic <;>
    simp [callRun, compileInDefCrate, instantiateIn, callInCallerCrate, governingCrate,
      hcc, hdc, hic, h1]

/-- For a lowered callee without contract statements and an input with a contract violation, the
call reports a failed check iff the governing crate's flag is on. -/
theorem detects_iff_governingFlag_of_lowered_of_noChecks_of_violation (fl : Nat → Bool)
    (s : Site) (res : Resolution) (cs : CallSite) (c : Contract) (g : Fn) (hg : Lowered g)
    (hnc : NoChecks g) (x : Nat) (hv : ViolationAt c g x) :
    Detects fl s res cs c g x ↔ fl (governingCrate s res cs) = true := by
  constructor
  · rintro ⟨n, tr, k, hcall⟩
    rw [callRun_eq_ite_governingFlag_of_lowered fl s res cs c g hg x n] at hcall
    cases hfl : fl (governingCrate s res cs)
    · simp only [hfl, Bool.false_eq_true, ↓reduceIte] at hcall
      exact absurd (by rw [hcall]) (run_no_checkFail_of_noChecks (c := c) hnc x n k)
    · rfl
  · intro hfl
    rcases hv with hreq | ⟨hreq, tr, r, ⟨_, n, hn⟩, hens⟩
    · refine ⟨0, [], .pre, ?_⟩
      rw [callRun_eq_ite_governingFlag_of_lowered fl s res cs c g hg x 0]
      simp [hfl, instrObs, hreq]
    · refine ⟨n, tr, .post, ?_⟩
      rw [callRun_eq_ite_governingFlag_of_lowered fl s res cs c g hg x n, hn]
      simp [hfl, instrObs, hreq, wrapObs, hens]

/-- On an input without a contract violation, every call (any flags, placement, resolution, call
site) runs exactly as the callee as written, at every fuel. -/
theorem callRun_eq_run_of_not_violation (fl : Nat → Bool) (s : Site) (res : Resolution)
    (cs : CallSite) (c : Contract) (g : Fn) (x : Nat) (hv : ¬ ViolationAt c g x) (n : Nat) :
    callRun fl s res cs c g x n = run c g x n := by
  have hreq : c.req x = true := by
    cases hr : c.req x
    · exact absurd (.inl hr) hv
    · rfl
  have hens : EnsOnReturnsAt c g x := by
    intro tr r hret
    cases he : c.ens x r
    · exact absurd (.inr ⟨hreq, tr, r, hret, he⟩) hv
    · rfl
  have h1 := run_instr_eq_of_req_of_ensOnReturnsAt c .allExits g x hreq hens n
  have h2 := instrObs_run_eq_of_req_of_ensOnReturnsAt c g x hreq hens n
  obtain ⟨cc, dc, ic, gen⟩ := cs
  cases s <;> cases res <;> cases gen <;>
    cases hcc : fl cc <;> cases hdc : fl dc <;> cases hic : fl ic <;>
    simp [callRun, compileInDefCrate, instantiateIn, callInCallerCrate, hcc, hdc, hic, h1, h2]

/-! ## Compile-time evaluation that skips checks -/

/-- For a lowered function without contract statements: if compile-time evaluation that skips
checks produces the constant `r` from the all-exits instrumentation, the all-exits runtime-checked
call returns `r` iff `Req x` and `Ens x r`. -/
theorem runtimeValue_iff_req_and_ens_of_lowered_of_noChecks_of_ctfeSkipConst (c : Contract)
    (g : Fn) (hg : Lowered g) (hnc : NoChecks g) (x r : Nat)
    (hk : CtfeConst .allExits .skipChecks c g x r) :
    RuntimeValue .allExits c g x r ↔ c.req x = true ∧ c.ens x r = true := by
  constructor
  · rintro ⟨tr, _, m, hm⟩
    rw [run_instr_allExits_eq_instrObs_of_lowered c g hg x m] at hm
    obtain ⟨h1, h2, _⟩ := instrObs_eq_ret hm
    exact ⟨h1, h2⟩
  · rintro ⟨hreq, hens⟩
    obtain ⟨n₀, tr₀, hk₀⟩ := hk
    simp only [ctfeRun, erase_instr_eq_of_noChecks .allExits g hnc] at hk₀
    refine ⟨tr₀, nofun, n₀, ?_⟩
    rw [run_instr_allExits_eq_instrObs_of_lowered c g hg x n₀, hk₀]
    simp [instrObs, hreq, wrapObs, hens]

/-- For a lowered function without contract statements and an input with `Req x`: if compile-time
evaluation that skips checks produces the constant `r` from the all-exits instrumentation, the
all-exits runtime-checked call returns `r` iff the static obligation holds at `x`. -/
theorem runtimeValue_iff_staticObligationAt_of_lowered_of_noChecks_of_req_of_ctfeSkipConst
    (c : Contract) (g : Fn) (hg : Lowered g) (hnc : NoChecks g) (x r : Nat)
    (hreq : c.req x = true) (hk : CtfeConst .allExits .skipChecks c g x r) :
    RuntimeValue .allExits c g x r ↔ StaticObligationAt c g x := by
  rw [runtimeValue_iff_req_and_ens_of_lowered_of_noChecks_of_ctfeSkipConst c g hg hnc x r hk]
  obtain ⟨n₀, tr₀, hk₀⟩ := hk
  simp only [ctfeRun, erase_instr_eq_of_noChecks .allExits g hnc] at hk₀
  have hhalts₀ : Halts c g x ⟨tr₀, .ret r⟩ := ⟨nofun, n₀, hk₀⟩
  constructor
  · rintro ⟨_, hens⟩ _ tr' r' hhalts'
    cases halts_unique hhalts' hhalts₀
    exact hens
  · intro hob
    exact ⟨hreq, hob hreq tr₀ r hhalts₀⟩

end Toy.Contracts
