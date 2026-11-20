import ToyWMM.Tightness
import ToyWMM.SourceExec

/-!
# Positive and negative examples for every definition

Each definition is tested on an intended instance it must admit and an instance it must
reject. Verdicts are by `decide` unless noted.
-/

namespace Toy.WMM

open Litmus Event

/-! ## Relations -/

theorem acyclic_example_pos : Rel.Acyclic (mkRel 3 [(0, 1), (1, 2), (0, 2)]) := by decide
theorem acyclic_example_neg : ¬ Rel.Acyclic (mkRel 3 [(0, 1), (1, 2), (2, 0)]) := by decide
theorem acyclic_example_neg_self : ¬ Rel.Acyclic (mkRel 1 [(0, 0)]) := by decide

/-! ## Consistency predicates -/

theorem scConsistent_example_pos : sbSC.SCConsistent := by decide
theorem scConsistent_example_neg : ¬ sbWeak.SCConsistent := by decide
theorem tsoConsistent_example_pos : sbWeak.TSOConsistent := by decide
theorem tsoConsistent_example_neg : ¬ mpWeak.TSOConsistent := by decide
theorem tsoGhbAcyclic_example_pos : sbWeak.TsoGhbAcyclic := by decide
theorem tsoGhbAcyclic_example_neg : ¬ sbFencedWeak.TsoGhbAcyclic := by decide
theorem perLocSC_example_pos : sbWeak.PerLocSC := by decide
theorem perLocSC_example_neg : ¬ readOwnLaterWrite.PerLocSC := by decide
theorem scConsistentErased_example_pos : sbFencedSC.SCConsistentErased := by decide
theorem scConsistentErased_example_neg : ¬ sbFencedWeak.SCConsistentErased := by decide
theorem keepSameLocWR_example_pos : sbWeak.TSOConsistentKeepSameLocWR := by decide
theorem keepSameLocWR_example_neg : ¬ n6Weak.TSOConsistentKeepSameLocWR := by decide

/-! ## Derived relations -/

/-- `fr`: SB's read of `y` (index 3) reads the initial value, so it is `fr`-before the write
of `y` (index 4); it is not `fr`-before the write of `x` (index 2). -/
theorem fr_example : sbWeak.fr ⟨3, by decide⟩ ⟨4, by decide⟩ = true ∧
    sbWeak.fr ⟨3, by decide⟩ ⟨2, by decide⟩ = false := by decide

/-- `ppo` drops SB's write→read pair and keeps MP's write→write pair; it has no fence
endpoints (SB+mfences' write→fence and fence→read `po` pairs are not in `ppo`). -/
theorem ppo_example : sbWeak.ppo ⟨2, by decide⟩ ⟨3, by decide⟩ = false ∧
    mpWeak.ppo ⟨2, by decide⟩ ⟨3, by decide⟩ = true ∧
    sbFencedWeak.ppo ⟨2, by decide⟩ ⟨3, by decide⟩ = false ∧
    sbFencedWeak.ppo ⟨3, by decide⟩ ⟨4, by decide⟩ = false := by decide

/-- `rfe`: a read of the initial value reads externally; store forwarding in n6 is internal. -/
theorem rfe_example : sbWeak.rfe ⟨1, by decide⟩ ⟨3, by decide⟩ = true ∧
    n6Weak.rfe ⟨2, by decide⟩ ⟨3, by decide⟩ = false := by decide

/-- `fenceOrd` relates SB+mfences' write and read, not SB's, and never has a fence as an
endpoint: in `W; F; F; R` the first fence is `po`-separated from the read by the second fence,
yet it is not `fenceOrd`-before the read, while the write is. -/
theorem fenceOrd_example : sbFencedWeak.fenceOrd ⟨2, by decide⟩ ⟨4, by decide⟩ = true ∧
    sbWeak.fenceOrd ⟨2, by decide⟩ ⟨3, by decide⟩ = false ∧
    (Exec.ofList [W 0 0 1, F 0, F 0, R 0 0 1] [(0, 3)] []).fenceOrd ⟨1, by decide⟩ ⟨3, by decide⟩
      = false ∧
    (Exec.ofList [W 0 0 1, F 0, F 0, R 0 0 1] [(0, 3)] []).fenceOrd ⟨0, by decide⟩ ⟨3, by decide⟩
      = true := by decide

/-- With fence events excluded from `ppo`, `fenceOrd` carries the ordering effect of fences:
SB+mfences' weak-outcome execution has no cycle in `ppo ∪ rfe ∪ co ∪ fr` and is rejected by
the TSO ordering axiom only through `fenceOrd`. -/
theorem sbFencedWeak_needs_fenceOrd :
    Rel.Acyclic (fun a b => sbFencedWeak.ppo a b || sbFencedWeak.rfe a b ||
        sbFencedWeak.co a b || sbFencedWeak.fr a b) ∧ ¬ sbFencedWeak.TsoGhbAcyclic := by
  decide

/-! ## Well-formedness conditions -/

theorem wf_example_pos :
    sbWeak.Wf ∧ mpWeak.Wf ∧ lbWeak.Wf ∧ w22Weak.Wf ∧ iriwWeak.Wf ∧ sbFencedWeak.Wf ∧
      sbOneFenceWeak.Wf ∧ rWeak.Wf ∧ n6Weak.Wf ∧ sbSC.Wf ∧ sbFencedSC.Wf := by decide

theorem poIrrefl_example_neg : ¬ (Exec.ofListPo [W 0 0 1] [(0, 0)] [] []).PoIrrefl := by decide
theorem poTrans_example_neg :
    ¬ (Exec.ofListPo [W 0 0 1, W 0 0 2, W 0 0 3] [(0, 1), (1, 2)] [] []).PoTrans := by decide
theorem poWithinThread_example_neg :
    ¬ (Exec.ofListPo [W 0 0 1, W 1 0 2] [(0, 1)] [] []).PoWithinThread := by decide
theorem poTotal_example_neg : ¬ (Exec.ofListPo [W 0 0 1, W 0 1 2] [] [] []).PoTotal := by decide
theorem rfSameLoc_example_neg : ¬ (Exec.ofList [W 0 0 1, R 1 1 1] [(0, 1)] []).RfSameLoc := by
  decide
theorem rfKinds_example_neg : ¬ (Exec.ofList [W 0 0 1, W 1 0 1] [(0, 1)] []).RfKinds := by
  decide
theorem rfSameVal_example_neg : ¬ (Exec.ofList [W 0 0 1, R 1 0 2] [(0, 1)] []).RfSameVal := by
  decide
theorem rfTotal_example_neg : ¬ (Exec.ofList [R 0 0 0] [] []).RfTotal := by decide
theorem rfFunctional_example_neg :
    ¬ (Exec.ofList [initW 0, W 0 0 0, R 1 0 0] [(0, 2), (1, 2)] [(0, 1)]).RfFunctional := by
  decide
theorem coKinds_example_neg : ¬ (Exec.ofList [W 0 0 1, W 1 1 2] [] [(0, 1)]).CoKinds := by decide
theorem coIrrefl_example_neg : ¬ (Exec.ofList [W 0 0 1] [] [(0, 0)]).CoIrrefl := by decide
theorem coTrans_example_neg :
    ¬ (Exec.ofList [W 0 0 1, W 1 0 2, W 2 0 3] [] [(0, 1), (1, 2)]).CoTrans := by decide
theorem coTotal_example_neg : ¬ (Exec.ofList [W 0 0 1, W 1 0 2] [] []).CoTotal := by decide
theorem coInitFirst_example_neg : ¬ (Exec.ofList [initW 0, W 0 0 1] [] []).CoInitFirst := by
  decide

/-! ## Fencing conditions -/

theorem fenceBetweenWR_example_pos : sbFencedWeak.FenceBetweenWR := by decide
theorem fenceBetweenWR_example_neg : ¬ sbWeak.FenceBetweenWR ∧ ¬ sbOneFenceWeak.FenceBetweenWR := by
  decide
theorem localLoc_example_pos : localWR.LocalLoc 2 := by decide
theorem localLoc_example_neg : ¬ sbWeak.LocalLoc 0 := by decide
theorem fenceBetweenSharedWR_example_pos :
    localWR.FenceBetweenSharedWR ∧ sbFencedWeak.FenceBetweenSharedWR := by decide
theorem fenceBetweenSharedWR_example_neg :
    ¬ sbOneFenceWeak.FenceBetweenSharedWR ∧ ¬ sharedWLocalR.FenceBetweenSharedWR := by decide
theorem fenceBetweenBothSharedWR_example_pos :
    localWR.FenceBetweenBothSharedWR ∧ sharedWLocalR.FenceBetweenBothSharedWR ∧
      sbFencedWeak.FenceBetweenBothSharedWR := by decide
theorem fenceBetweenBothSharedWR_example_neg :
    ¬ sbOneFenceWeak.FenceBetweenBothSharedWR ∧ ¬ sbWeak.FenceBetweenBothSharedWR := by decide
theorem coSameLoc_example_pos : sbWeak.CoSameLoc ∧ w22Weak.CoSameLoc := by decide
theorem coSameLoc_example_neg : ¬ coAcrossLocs.CoSameLoc := by decide

/-! ## Programs, executions of programs, and the mapping -/

theorem execOf_example_pos : ExecOf sbProg sbWeak ∧ ExecOf sbProg sbSC :=
  ⟨sbWeak_execOf, sbSC_execOf⟩

/-- An execution with SB's events but no `po` is not an execution of SB. -/
theorem execOf_example_neg :
    ¬ ExecOf sbProg (Exec.ofListPo [initW 0, initW 1, W 0 0 1, R 0 1 0, W 1 1 2, R 1 0 0] []
      [(1, 3), (0, 5)] [(0, 2), (1, 4)]) := by
  intro h
  have := h.po ⟨2, by decide⟩ ⟨3, by decide⟩
  revert this; decide

/-- An execution of the wrong size is not an execution of SB. -/
theorem execOf_example_neg_length : ¬ ExecOf sbProg sbFencedWeak :=
  fun h => absurd h.length (by decide)

theorem fenceAfterStores_example_pos :
    fenceAfterStores sbProg = [[.store 0 1, .mfence, .load 1], [.store 1 2, .mfence, .load 0]] :=
  fenceAfterStores_sbProg

/-- The mapping does not fence loads and leaves store-free threads unchanged, and it is not
the one-sided fencing of SB. -/
theorem fenceAfterStores_example_neg :
    fenceAfterStores [[.load 0, .load 1]] = [[.load 0, .load 1]] ∧
      fenceAfterStores sbProg ≠ sbOneFenceProg := by decide

theorem layout_example :
    layout sbProg = [initW 0, initW 1, W 0 0 1, R 0 1 0, W 1 1 2, R 1 0 0] := by decide

/-! ## Races -/

theorem conflict_example : sbWeak.Conflict ⟨2, by decide⟩ ⟨5, by decide⟩ ∧
    ¬ sbWeak.Conflict ⟨2, by decide⟩ ⟨3, by decide⟩ ∧
    ¬ sbWeak.Conflict ⟨3, by decide⟩ ⟨5, by decide⟩ := by decide

theorem hb_example : sbSC.HB ⟨2, by decide⟩ ⟨5, by decide⟩ ∧
    ¬ sbWeak.HB ⟨2, by decide⟩ ⟨5, by decide⟩ := by decide

theorem noUnfencedWRIncident_example : sbFencedWeak.NoUnfencedWRIncident ⟨2, by decide⟩ ∧
    sbFencedWeak.NoUnfencedWRIncident ⟨4, by decide⟩ ∧ ¬ sbWeak.NoUnfencedWRIncident ⟨2, by decide⟩ ∧
    ¬ sbWeak.NoUnfencedWRIncident ⟨3, by decide⟩ := by decide

/-- `NoUnfencedWRIncident` is syntactic and holds vacuously without any fence: in the fence-free
MP and LB executions every event satisfies it (no thread has a `po` write→read pair). -/
theorem noUnfencedWRIncident_vacuous_example :
    (∀ a, mpWeak.NoUnfencedWRIncident a) ∧ (∀ a, lbWeak.NoUnfencedWRIncident a) := by decide

theorem raceFree_example_pos : sbSC.RaceFree ∧ sbFencedWeak.RaceFree := by decide
theorem raceFree_example_neg : sbSeq.Race ⟨4, by decide⟩ ⟨3, by decide⟩ ∧ ¬ sbSeq.RaceFree := by
  decide

/-- In SB with one fence every conflicting pair has a side satisfying
`NoUnfencedWRIncident`, so its weak execution is race-free in the either-side sense, but it is
not race-free in the both-sides sense. -/
theorem raceFreeEither_example : sbOneFenceWeak.RaceFreeEither ∧ ¬ sbOneFenceWeak.RaceFree := by
  decide

/-- `Exec.comap` along the source-event map of `fenceAfterStores sbProg` gives an execution of
`sbProg`; along the map that takes the first six events it does not (index `3` is a fence). -/
theorem comap_example :
    ExecOf sbProg (sbFencedSC.comap sbSrcIdx) ∧
      ¬ ExecOf sbProg (sbFencedSC.comap
        (fun (a : Fin (layout sbProg).length) => ⟨a.val % 8, Nat.mod_lt _ (by decide)⟩)) := by
  refine ⟨⟨rfl, by decide, by decide, by decide, by decide, by decide⟩, fun h => ?_⟩
  have := h.kind ⟨3, by decide⟩
  revert this; decide

end Toy.WMM
