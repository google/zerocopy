import Toy.ZstAssume.Switch

/-!
# Backward propagation of unreachability

Replacing a whole block by `Block.unreach`: exact conditions under both UB disciplines,
counterexamples, and an instance. Divergence enters as a behaviour of the toy
semantics; the forward-progress question (whether divergence may itself be UB) is not
modelled here.
-/

namespace Toy.ZstAssume

/-- **Exact condition (prefix-preserving).** Replacing block `b` by `Block.unreach` is a
prefix-preserving refinement iff, from every reachable state at the entry of `b`, the
source run reaches UB without emitting any event (in particular without diverging). -/
theorem replaceUnreachable_refinesPP_iff (K : ZContract) (P : Prog) (b : Label) :
    RefinesPP K P (replaceUnreachable P b) ↔
      ∀ st, ReachableAt K P b 0 st → GoesWrongFrom K P (P.entry b st) [] := by
  exact ru_refinesPP_iff

/-- **Exact condition (whole-trace).** Replacing block `b` by `Block.unreach` is a
whole-trace refinement iff, from every reachable state at the entry of `b`, the source
run reaches UB (events before the UB are permitted; diverging is not). -/
theorem replaceUnreachable_refinesWT_iff (K : ZContract) (P : Prog) (b : Label) :
    RefinesWT K P (replaceUnreachable P b) ↔
      ∀ st, ReachableAt K P b 0 st → ∃ t, GoesWrongFrom K P (P.entry b st) t := by
  exact ru_refinesWT_iff

/-! ### Counterexamples and positive controls (fully proved) -/

/-- Block `0` jumps to block `1`, which emits `7` and is then unreachable. -/
def pEmitBeforeUnreach : Prog := [⟨[], .goto 1⟩, ⟨[.emit (.const 7)], .unreachable⟩]

theorem replaceUnreachable_pEmitBeforeUnreach :
    replaceUnreachable pEmitBeforeUnreach 1 = [⟨[], .goto 1⟩, Block.unreach] := by decide

/-- **An event before the UB blocks backward propagation under prefix-preserving UB but
not under whole-trace UB.** Replacing block `1` of `pEmitBeforeUnreach` by
`Block.unreach` loses the event `7`: it is not a prefix-preserving refinement, but it
is a whole-trace refinement. -/
theorem replaceUnreachable_emit_before_unreachable :
    ∀ K, ¬ RefinesPP K pEmitBeforeUnreach (replaceUnreachable pEmitBeforeUnreach 1) ∧
      RefinesWT K pEmitBeforeUnreach (replaceUnreachable pEmitBeforeUnreach 1) := by
  intro K
  rw [replaceUnreachable_pEmitBeforeUnreach]
  have hsrc : ∀ σ, run K pEmitBeforeUnreach 3 (pEmitBeforeUnreach.init σ) = .ub [7] :=
    fun σ => rfl
  have htgt : ∀ σ, run K [⟨[], .goto 1⟩, Block.unreach] 2
      (Prog.init [⟨[], .goto 1⟩, Block.unreach] σ) = .ub [] := fun σ => rfl
  refine ⟨fun h => ?_, fun σ bt hbt => ?_⟩
  · obtain ⟨bs, hbs, himp⟩ := h (mkState []) (.wrong []) ⟨2, htgt _⟩
    have := (hasBehFrom_iff_of_run_ub (hsrc (mkState [])) bs).1 hbs
    subst this
    rcases himp with h' | ⟨t, ht, hp⟩
    · cases h'
    · cases ht
      simp [Beh.HasPrefix] at hp
  · have := (hasBehFrom_iff_of_run_ub (htgt σ) bt).1 hbt
    subst this
    exact ⟨.wrong [7], ⟨3, hsrc σ⟩, Or.inr ⟨[7], rfl⟩⟩

/-- Block `0` loops on itself while local `0 = 0`, otherwise goes to the unreachable
block `1`. -/
def pLoopBeforeUnreach : Prog := [⟨[], .switch 0 [(0, 0)] 1⟩, Block.unreach]

theorem run_pLoopBeforeUnreach_zero (K : ZContract) (σ : State) (h : σ.locals 0 = 0) :
    ∀ n, run K pLoopBeforeUnreach n (pLoopBeforeUnreach.init σ) =
      .running (pLoopBeforeUnreach.init σ) []
  | 0 => rfl
  | n + 1 => by
    have hs : step K pLoopBeforeUnreach (pLoopBeforeUnreach.init σ) =
        .next none (pLoopBeforeUnreach.init σ) := by
      simp [step, pLoopBeforeUnreach, Prog.init, Prog.entry, Prog.blk, selectTarget, h]
    rw [run_succ_next n hs, run_pLoopBeforeUnreach_zero K σ h n]
    rfl

/-- **A possibly diverging loop before the UB blocks backward propagation under both
disciplines.** Replacing block `0` of `pLoopBeforeUnreach` by `Block.unreach` turns the
silent divergence on local `0 = 0` into UB: it is not even a whole-trace refinement. -/
theorem replaceUnreachable_diverging_loop_not_refinesWT (K : ZContract) :
    HasBeh K pLoopBeforeUnreach (mkState [0]) (.div []) ∧
      HasBeh K (replaceUnreachable pLoopBeforeUnreach 0) (mkState [0]) (.wrong []) ∧
      ¬ RefinesWT K pLoopBeforeUnreach (replaceUnreachable pLoopBeforeUnreach 0) := by
  have hr : replaceUnreachable pLoopBeforeUnreach 0 = [Block.unreach, Block.unreach] := by
    decide
  rw [hr]
  have hdiv : ∀ b, HasBeh K pLoopBeforeUnreach (mkState [0]) b ↔ b = .div [] :=
    hasBehFrom_iff_of_silent (fun n => ⟨_, run_pLoopBeforeUnreach_zero K _ rfl n⟩)
  have hw : HasBeh K [Block.unreach, Block.unreach] (mkState [0]) (.wrong []) := ⟨1, rfl⟩
  refine ⟨(hdiv _).2 rfl, hw, fun h => ?_⟩
  obtain ⟨bs, hbs, himp⟩ := h _ _ hw
  rw [hdiv] at hbs
  subst hbs
  rcases himp with h' | ⟨t, ht⟩
  · cases h'
  · cases ht

/-- Block `0` jumps to block `1`, which assigns local `0 := 1` and jumps to the
unreachable block `2`. -/
def pSilentToUnreach : Prog :=
  [⟨[], .goto 1⟩, ⟨[.assign 0 (.const 1)], .goto 2⟩, Block.unreach]

/-- **Non-vacuity and soundness instance.** In `pSilentToUnreach`, from every state at
the entry of block `1` the run reaches UB without emitting an event, and replacing block
`1` by `Block.unreach` is a prefix-preserving refinement. -/
theorem replaceUnreachable_pSilentToUnreach (K : ZContract) :
    (∀ st, ReachableAt K pSilentToUnreach 1 0 st →
        GoesWrongFrom K pSilentToUnreach (pSilentToUnreach.entry 1 st) []) ∧
      RefinesPP K pSilentToUnreach (replaceUnreachable pSilentToUnreach 1) := by
  have hr : replaceUnreachable pSilentToUnreach 1 =
      [⟨[], .goto 1⟩, Block.unreach, Block.unreach] := by decide
  rw [hr]
  refine ⟨fun st _ => ⟨3, rfl⟩, fun σ => ?_⟩
  exact refinesPPAt_of_tgt_ub (n := 2) (m := 4) (t := []) (t' := []) rfl rfl (prefix_nil _)

end Toy.ZstAssume
