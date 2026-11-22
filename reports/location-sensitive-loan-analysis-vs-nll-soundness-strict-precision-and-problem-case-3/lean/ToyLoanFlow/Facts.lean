import ToyLoanFlow.Programs
import ToyLoanFlow.Exec
import ToyLoanFlow.Certificates

/-!
# Kernel-checked facts about the concrete programs

Acceptance and safety facts are proved from certificates (closed lists, checked by `decide`);
rejection and unsafety facts are proved from explicit derivations and walks.
-/

namespace Toy.LoanFlow

/-! ## Typing -/

theorem pc3_wellTyped : WellTyped pc3 := by decide
theorem pc3Loop_wellTyped : WellTyped pc3Loop := by decide
theorem pReassign_wellTyped : WellTyped pReassign := by decide
theorem pCopyThenUse_wellTyped : WellTyped pCopyThenUse := by decide
theorem pVariance_wellTyped : WellTyped pVariance := by decide
theorem pUntypedHolder_not_wellTyped : ¬ WellTyped pUntypedHolder := by decide
theorem pUntypedStore_not_wellTyped : ¬ WellTyped pUntypedStore := by decide
theorem pc3NoReturn_wellTyped : WellTyped pc3NoReturn := by decide
theorem pCopyThenUseShr_wellTyped : WellTyped pCopyThenUseShr := by decide
theorem pStoreSafe_wellTyped : WellTyped pStoreSafe := by decide
theorem pUnreachUntyped_not_wellTyped : ¬ WellTyped pUnreachUntyped := by decide

/-- In `pUnreachUntyped`, every node reachable from the entry node is well typed: the entry
node is a `nop` without successors. -/
theorem pUnreachUntyped_reach_wellTyped :
    ∀ q, Reach pUnreachUntyped.succ pUnreachUntyped.entry q →
      StmtWellTyped pUnreachUntyped (pUnreachUntyped.stmt q) := by
  intro q h
  cases h with
  | refl => exact trivial
  | step hv _ =>
    have h0 : pUnreachUntyped.succ pUnreachUntyped.entry = [] := rfl
    rw [h0] at hv
    cases hv

/-! ## Safety -/

theorem pc3_safe : Safe pc3 :=
  safe_of_cert (explore pc3 200).1 (by decide) (by decide)

theorem pc3Loop_safe : Safe pc3Loop :=
  safe_of_cert (explore pc3Loop 200).1 (by decide) (by decide)

theorem pReassign_safe : Safe pReassign :=
  safe_of_cert (explore pReassign 200).1 (by decide) (by decide)

theorem pCopyThenUse_not_safe : ¬ Safe pCopyThenUse :=
  not_safe_of_reachesUB (π := [0, 1, 2, 3]) (by decide)

theorem pVariance_not_safe : ¬ Safe pVariance :=
  not_safe_of_reachesUB (π := [0, 1, 2, 3, 4, 5]) (by decide)

theorem pUntypedHolder_not_safe : ¬ Safe pUntypedHolder :=
  not_safe_of_reachesUB (π := [0, 1, 2]) (by decide)

theorem pUntypedStore_not_safe : ¬ Safe pUntypedStore :=
  not_safe_of_reachesUB (π := [0, 1, 2, 3, 4]) (by decide)

theorem pc3NoReturn_safe : Safe pc3NoReturn :=
  safe_of_cert (explore pc3NoReturn 200).1 (by decide) (by decide)

theorem pCopyThenUseShr_not_safe : ¬ Safe pCopyThenUseShr :=
  not_safe_of_reachesUB (π := [0, 1, 2, 3]) (by decide)

theorem pStoreSafe_safe : Safe pStoreSafe :=
  safe_of_cert (explore pStoreSafe 200).1 (by decide) (by decide)

/-! ## Acceptance (certificates) -/

theorem pc3_lsAccepts : LSAccepts pc3 :=
  ls_accepts_of_cert (liveList pc3) (subList .inv pc3)
    (lsList .overwrite .inv pc3) (by decide)

theorem pc3Loop_lsAccepts : LSAccepts pc3Loop :=
  ls_accepts_of_cert (liveList pc3Loop) (subList .inv pc3Loop)
    (lsList .overwrite .inv pc3Loop) (by decide)

theorem pReassign_lsAccepts : LSAccepts pReassign :=
  ls_accepts_of_cert (liveList pReassign) (subList .inv pReassign)
    (lsList .overwrite .inv pReassign) (by decide)

theorem pReassign_nllAccepts : NLLAccepts pReassign :=
  nll_accepts_of_cert (liveList pReassign) (regionList .inv pReassign) (scopeList .inv pReassign)
    (by decide)

theorem pCopyThenUse_lsCopySrcKill_accepts : LS.Accepts .overwriteAndCopySrc .inv pCopyThenUse :=
  ls_accepts_of_cert (liveList pCopyThenUse) (subList .inv pCopyThenUse)
    (lsList .overwriteAndCopySrc .inv pCopyThenUse) (by decide)

theorem pVariance_lsCov_accepts : LS.Accepts .overwrite .cov pVariance :=
  ls_accepts_of_cert (liveList pVariance) (subList .cov pVariance)
    (lsList .overwrite .cov pVariance) (by decide)

theorem pVariance_nllCov_accepts : NLL.Accepts .cov pVariance :=
  nll_accepts_of_cert (liveList pVariance) (regionList .cov pVariance) (scopeList .cov pVariance)
    (by decide)

theorem pUntypedHolder_nllAccepts : NLLAccepts pUntypedHolder :=
  nll_accepts_of_cert (liveList pUntypedHolder) (regionList .inv pUntypedHolder)
    (scopeList .inv pUntypedHolder) (by decide)

theorem pUntypedStore_lsAccepts : LSAccepts pUntypedStore :=
  ls_accepts_of_cert (liveList pUntypedStore) (subList .inv pUntypedStore)
    (lsList .overwrite .inv pUntypedStore) (by decide)

theorem pc3NoReturn_lsAccepts : LSAccepts pc3NoReturn :=
  ls_accepts_of_cert (liveList pc3NoReturn) (subList .inv pc3NoReturn)
    (lsList .overwrite .inv pc3NoReturn) (by decide)

theorem pc3NoReturn_nllAccepts : NLLAccepts pc3NoReturn :=
  nll_accepts_of_cert (liveList pc3NoReturn) (regionList .inv pc3NoReturn)
    (scopeList .inv pc3NoReturn) (by decide)

theorem pCopyThenUseShr_lsCopySrcKill_accepts :
    LS.Accepts .overwriteAndCopySrc .inv pCopyThenUseShr :=
  ls_accepts_of_cert (liveList pCopyThenUseShr) (subList .inv pCopyThenUseShr)
    (lsList .overwriteAndCopySrc .inv pCopyThenUseShr) (by decide)

theorem pStoreSafe_lsAccepts : LSAccepts pStoreSafe :=
  ls_accepts_of_cert (liveList pStoreSafe) (subList .inv pStoreSafe)
    (lsList .overwrite .inv pStoreSafe) (by decide)

theorem pStoreSafe_nllAccepts : NLLAccepts pStoreSafe :=
  nll_accepts_of_cert (liveList pStoreSafe) (regionList .inv pStoreSafe)
    (scopeList .inv pStoreSafe) (by decide)

theorem pUnreachUntyped_nllAccepts : NLLAccepts pUnreachUntyped :=
  nll_accepts_of_cert (liveList pUnreachUntyped) (regionList .inv pUnreachUntyped)
    (scopeList .inv pUnreachUntyped) (by decide)

/-! ## Rejection (explicit derivations) -/

/-- In `pc3`, the loan created at node `0` is in scope at the insertion (node `3`) for the
location-insensitive checker: the returned local's region contains every node. -/
theorem pc3_nll_loan0_inScope_at_3 : NLL.InScope .inv pc3 0 3 :=
  .next (d := 1) (q := 1) rfl (.first (d := 1) rfl (by decide) (.universal (b := 2) rfl))
    (by decide) (.universal (b := 2) rfl)

theorem pc3_not_nllAccepts : ¬ NLLAccepts pc3 :=
  fun h => h 0 3 (by decide) pc3_nll_loan0_inScope_at_3

theorem pc3Loop_not_nllAccepts : ¬ NLLAccepts pc3Loop :=
  fun h => h 0 3 (by decide)
    (.next (d := 1) (q := 1) rfl (.first (d := 1) rfl (by decide) (.universal (b := 2) rfl))
      (by decide) (.universal (b := 2) rfl))

/-- Without kills, the loan created at node `0` of `pReassign` stays in `r`'s origin after `r`
is overwritten at node `2`, and `r` is live at node `3`. -/
theorem pReassign_lsNoKill_loan0_live_at_3 : LS.LoanLive .none .inv pReassign 0 3 :=
  ⟨(2, 0), 2, .carry (q := 1) (.carry (q := 0) (.intro rfl) (by decide) rfl) (by decide) rfl,
    by decide, .step (q' := 4) (by decide) (by decide) (.use (by decide))⟩

theorem pReassign_not_lsNoKill_accepts : ¬ LS.Accepts .none .inv pReassign :=
  fun h => h 0 3 (by decide) pReassign_lsNoKill_loan0_live_at_3

theorem pCopyThenUse_not_lsAccepts : ¬ LSAccepts pCopyThenUse :=
  fun h => h 0 2 (by decide)
    ⟨(1, 0), 1, .carry (q := 0) (.intro rfl) (by decide) (by decide), by decide,
      .step (q' := 3) (by decide) (by decide) (.use (by decide))⟩

/-- With invariant `&mut`, the loan of `y` created at node `2` of `pVariance` moves into `pp`'s
inner origin at the store (node `3`) and from there, along the relation generated by
`pp := &mut c` (node `1`) and persisting to node `3`, into `c`'s origin; `c` is live at the write
to `y` (node `4`). -/
theorem pVariance_ls_loan2_live_at_4 : LS.LoanLive .overwrite .inv pVariance 2 4 :=
  ⟨(2, 0), 3,
    .sub (o₁ := (3, 1))
      (.step (q := 2) (o₁ := (4, 0)) (.intro rfl) (by decide) (by decide) (by decide))
      (.persist (q := 2)
        (.persist (q := 1) (.base (by decide)) (by decide)
          (.step (q' := 3) (by decide) (by decide) (.use (by decide)))
          (.step (q' := 3) (by decide) (by decide)
            (.step (q' := 4) (by decide) (by decide)
              (.step (q' := 5) (by decide) (by decide) (.use (by decide))))))
        (by decide) (.use (by decide))
        (.step (q' := 4) (by decide) (by decide)
          (.step (q' := 5) (by decide) (by decide) (.use (by decide))))),
    by decide, .step (q' := 5) (by decide) (by decide) (.use (by decide))⟩

theorem pVariance_not_lsAccepts : ¬ LSAccepts pVariance :=
  fun h => h 2 4 (by decide) pVariance_ls_loan2_live_at_4

theorem pVariance_not_nllAccepts : ¬ NLLAccepts pVariance := by
  intro h
  -- `c` is live at nodes 3 and 4; invariance makes `s`'s region contain `c`'s region.
  have hc : ∀ q : Fin 6, (q = 3 ∨ q = 4) → NLL.InRegion .inv pVariance (4, 0) q := by
    intro q hq
    have hlive : LiveAt pVariance 2 q := by
      rcases hq with rfl | rfl
      · exact .step (q' := 4) (by decide) (by decide)
          (.step (q' := 5) (by decide) (by decide) (.use (by decide)))
      · exact .step (q' := 5) (by decide) (by decide) (.use (by decide))
    exact .outlives (o₂ := (3, 1)) (b := 3) (by decide)
      (.outlives (o₂ := (2, 0)) (b := 1) (by decide) (.live hlive (by decide)))
  exact h 2 4 (by decide)
    (.next (d := 4) (q := 3) rfl (.first (d := 4) rfl (by decide) (hc 3 (.inl rfl))) (by decide)
      (hc 4 (.inr rfl)))

theorem pUntypedHolder_not_lsAccepts : ¬ LSAccepts pUntypedHolder :=
  fun h => h 0 1 (by decide)
    ⟨(1, 0), 0, .intro rfl, by decide,
      .step (q' := 2) (by decide) (by decide) (.use (by decide))⟩

theorem pCopyThenUseShr_not_lsAccepts : ¬ LSAccepts pCopyThenUseShr :=
  fun h => h 0 2 (by decide)
    ⟨(1, 0), 1, .carry (q := 0) (.intro rfl) (by decide) (by decide), by decide,
      .step (q' := 3) (by decide) (by decide) (.use (by decide))⟩

theorem pUnreachUntyped_not_lsAccepts : ¬ LSAccepts pUnreachUntyped :=
  fun h => h 1 2 (by decide)
    ⟨(1, 0), 1, .intro rfl, by decide,
      .step (q' := 3) (by decide) (by decide) (.use (by decide))⟩

/-- In `pReassign`, `r` is dead on entry to node `2`, which overwrites it. -/
theorem pReassign_r_dead_at_2 : ¬ LiveAt pReassign 2 2 := fun h => by
  have := mem_of_liveAt (L := liveList pReassign) (by decide) h
  revert this; decide

/-- In `pc3`, the outermost origin of the returned local `r` contains every node. -/
theorem pc3_r_region_universal : ∀ q : Fin 6, NLL.InRegion .inv pc3 (1, 0) q :=
  fun _ => .universal (b := 2) rfl

/-- In `pc3`, the loan created at node `0` is not live at the insertion (node `3`) for the
location-sensitive checker. -/
theorem pc3_ls_loan0_not_live_at_3 : ¬ LS.LoanLive .overwrite .inv pc3 0 3 :=
  fun h => pc3_lsAccepts 0 3 (by decide) h

end Toy.LoanFlow
