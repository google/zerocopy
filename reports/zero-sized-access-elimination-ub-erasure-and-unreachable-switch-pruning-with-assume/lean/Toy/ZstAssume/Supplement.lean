import Toy.ZstAssume.ZeroSize
import Toy.ZstAssume.Switch

/-!
# Supplementary instances

Two concrete facts that sharpen card prose: a live-arm instance of
`pruneArm_equivPP_of_invariant_ne`, and the run of the element-loop lowering
`copyLoopProg` at count 0.
-/

namespace Toy.ZstAssume

/-- A switch whose pruned arm (value 5, target block 1) is a live block that emits 9 and
halts, while the switched local is always 1 at the switch. -/
def pSwLiveInv : Prog :=
  [⟨[.assign 0 (.const 1)], .switch 0 [(5, 1)] 2⟩, ⟨[.emit (.const 9)], .halt⟩, ⟨[], .halt⟩]

/-- `pruneArm_equivPP_of_invariant_ne` applies to a pruned arm whose target block is not
`Block.unreach`: in `pSwLiveInv` the switch has the expected shape, the target selected by
value 5 is not an unreachable block, the switched local differs from 5 in every reachable
state at the terminator, and pruning the arm is a prefix-preserving equivalence. -/
theorem pruneArm_equivPP_of_invariant_ne_live_arm_witness (K : ZContract) :
    (pSwLiveInv.blk 0).term = .switch 0 [(5, 1)] 2 ∧
      ¬ IsUnreachableBlock pSwLiveInv (selectTarget [(5, 1)] 2 5) ∧
      (∀ st, ReachableAt K pSwLiveInv 0 (pSwLiveInv.blk 0).stmts.length st → st.locals 0 ≠ 5) ∧
      EquivPP K pSwLiveInv (pruneArm pSwLiveInv 0 5) := by
  have hinv : ∀ st, ReachableAt K pSwLiveInv 0 (pSwLiveInv.blk 0).stmts.length st →
      st.locals 0 ≠ 5 := by
    rintro st ⟨σ, n, t, h⟩
    match n with
    | 0 => simp [run, Prog.init, Prog.entry, Prog.at, Prog.blk, pSwLiveInv] at h
    | 1 =>
      simp_run [pSwLiveInv, Prog.at] at h
      obtain ⟨rfl, -⟩ := h
      simp
    | 2 => simp_run [pSwLiveInv, Prog.at] at h
    | n + 3 =>
      have h₃ : run K pSwLiveInv 3 (pSwLiveInv.init σ) = .done [] (σ.set 0 1) := by
        simp_run [pSwLiveInv]
      rw [run_done_mono h₃ (by omega : 3 ≤ n + 3)] at h
      cases h
  exact ⟨by decide, by decide, hinv,
    pruneArm_equivPP_of_invariant_ne K pSwLiveInv 0 0 [(5, 1)] 2 5 (by decide) hinv⟩

/-- At count 0, the element-loop lowering `copyLoopProg 0 1 2 ⟨4, 4⟩ 0` halts after four
steps with empty trace; its final state differs from the input in counter local 2 (set to
0), while locals 0 and 1 keep their input values (the loop body, which advances them,
does not run). -/
theorem copyLoopProg_zeroCount_preserves_src_dst :
    run .aligned (copyLoopProg 0 1 2 ⟨4, 4⟩ 0) 4
      ((copyLoopProg 0 1 2 ⟨4, 4⟩ 0).init (mkState [8, 12, 42])) =
      .done [] ((mkState [8, 12, 42]).set 2 0) ∧
      ((mkState [8, 12, 42]).set 2 0).locals 0 = 8 ∧
      ((mkState [8, 12, 42]).set 2 0).locals 1 = 12 ∧
      ((mkState [8, 12, 42]).set 2 0).locals 2 = 0 := by
  refine ⟨by simp_run [copyLoopProg], rfl, rfl, rfl⟩

end Toy.ZstAssume
