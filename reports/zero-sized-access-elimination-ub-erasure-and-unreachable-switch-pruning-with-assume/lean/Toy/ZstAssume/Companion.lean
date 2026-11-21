import Toy.ZstAssume.ZeroSize
import Toy.ZstAssume.Switch

/-!
# Companion facts

Two facts that pin down card prose: relative to its actual input, the fact-based fold of
`pEmitFact` after pruning without `assume` is not a whole-trace refinement; and the run of
the element-loop lowering `copyLoopProg 0 1 2 ⟨4, 4⟩ 0` at count 0 from every input state.
-/

namespace Toy.ZstAssume

/-- Relative to its actual input `pruneArm pEmitFact 1 5` (not the source `pEmitFact`),
folding block `0` to `goto 4` is not a whole-trace refinement, under every contract: on the
input with local `0 = 5`, the input program emits `7`, then `0`, and halts, while the folded
program emits `0` and halts. -/
theorem emitFact_fold_after_pruneArm_not_refinesWT_input (K : ZContract) :
    ¬ RefinesWT K (pruneArm pEmitFact 1 5) (foldToGoto (pruneArm pEmitFact 1 5) 0 4) := by
  have hT1 : pruneArm pEmitFact 1 5 =
      [ ⟨[], .switch 0 [(5, 2)] 4⟩,
        ⟨[], .switch 0 [] 4⟩,
        ⟨[.emit (.const 7)], .goto 1⟩,
        Block.unreach,
        ⟨[.emit (.const 0)], .halt⟩ ] := by decide
  have hT2 : foldToGoto (pruneArm pEmitFact 1 5) 0 4 =
      [ ⟨[], .goto 4⟩,
        ⟨[], .switch 0 [] 4⟩,
        ⟨[.emit (.const 7)], .goto 1⟩,
        Block.unreach,
        ⟨[.emit (.const 0)], .halt⟩ ] := by decide
  rw [hT2, hT1]
  exact not_refinesWT_of_term_term (σ := mkState [5]) ⟨6, _, rfl⟩ ⟨3, _, rfl⟩ (by decide)

/-- At count 0, under every contract and from every input state `σ`, the element-loop
lowering `copyLoopProg 0 1 2 ⟨4, 4⟩ 0` halts after four steps with empty trace in the state
`σ.set 2 0`: counter local `2` is set to `0`, and locals `0` and `1` keep their input values
(the loop body, which advances them, does not run). -/
theorem copyLoopProg_zeroCount_run (K : ZContract) (σ : State) :
    run K (copyLoopProg 0 1 2 ⟨4, 4⟩ 0) 4 ((copyLoopProg 0 1 2 ⟨4, 4⟩ 0).init σ) =
        .done [] (σ.set 2 0) ∧
      (σ.set 2 0).locals 0 = σ.locals 0 ∧
      (σ.set 2 0).locals 1 = σ.locals 1 ∧
      (σ.set 2 0).locals 2 = 0 := by
  refine ⟨by simp_run [copyLoopProg], ?_, ?_, ?_⟩ <;> simp [State.set]

end Toy.ZstAssume
