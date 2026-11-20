import ToyWMM.StraightLine

/-!
# Non-vacuity witnesses and tightness counterexamples

Every counterexample is in canonical form: a concrete instance satisfying all the *other*
hypotheses of the named theorem, for which the conclusion fails. Every non-vacuity theorem
exhibits a concrete instance satisfying all hypotheses.
-/

namespace Toy.WMM

open Litmus Event

/-! ## Executions used as counterexamples -/

/-- A read of `x` taking its value from the `po`-later write to `x` in the same thread
(violates SC per location, "CoRW"). -/
def readOwnLaterWrite : Exec 3 :=
  Exec.ofList [initW 0, R 0 0 1, W 0 0 1] [(2, 1)] [(0, 2)]

/-- A read of `y` taking its value from the `po`-later write to `x` (violates `RfSameLoc`). -/
def rfWrongLoc : Exec 2 :=
  Exec.ofList [R 0 1 1, W 0 0 1] [(1, 0)] []

/-- Thread 0: `a: x := 1`, `b: r := x` (reads `a`), `c: r' := y` (reads `0`), with only
`b →po c` (so `a` is `po`-unrelated to `b` and `c`: `PoTotal` fails, `po` stays transitive).
Thread 1: `d: y := 1; mfence; e: r'' := x` (reads `0`). -/
def poPartial : Exec 8 :=
  Exec.ofListPo [initW 0, initW 1, W 0 0 1, R 0 0 1, R 0 1 0, W 1 1 1, F 1, R 1 0 0]
    [(3, 4), (5, 6), (6, 7), (5, 7)] [(2, 3), (1, 4), (0, 7)] [(0, 2), (1, 5)]

/-- `po` relates `x := 1` and the later `r := y` in both directions (not transitive). -/
def poTwoCycle : Exec 4 :=
  Exec.ofListPo [initW 0, initW 1, W 0 0 1, R 0 1 0] [(2, 3), (3, 2)] [(1, 3)] [(0, 2)]

/-- `po` from a thread's write to an initialisation write (violates `PoWithinThread`). -/
def poIntoInit : Exec 5 :=
  Exec.ofListPo [initW 0, initW 1, W 0 0 1, W 1 1 2, R 1 0 0]
    [(2, 1), (3, 4)] [(0, 4)] [(0, 2), (1, 3)]

/-- `co` relates the initialisation writes of different locations (violates `CoKinds`). -/
def coAcrossLocs : Exec 4 :=
  Exec.ofList [initW 0, initW 1, W 0 0 1, R 0 1 0] [(1, 3)] [(0, 2), (1, 0)]

/-- Thread-local location `z = 2` written and then an unfenced read of shared `x`:
`T0: z := 1; r := x` (reads `0`) ‖ `T1: x := 2`. -/
def localWR : Exec 6 :=
  Exec.ofList [initW 0, initW 1, initW 2, W 0 2 1, R 0 0 0, W 1 0 2]
    [(0, 4)] [(0, 5), (2, 3)]

/-- A fence with a `po` self-loop. -/
def fenceSelfPo : Exec 1 := Exec.ofListPo [F 0] [(0, 0)] [] []

/-- `r := x; mfence; x := 1` with `po` not transitive and `r` reading the later write. -/
def fenceNonTransPo : Exec 3 :=
  Exec.ofListPo [R 0 0 1, F 0, W 0 0 1] [(0, 1), (1, 2)] [(2, 0)] []

/-- An `rf` edge out of a fence. -/
def rfFromFence : Exec 2 := Exec.ofListPo [W 0 0 1, F 0] [(0, 1)] [(1, 0)] []

/-- A `co` edge out of a fence. -/
def coFromFence : Exec 2 := Exec.ofListPo [W 0 0 1, F 0] [(0, 1)] [] [(1, 0)]

/-! ## Model inclusion -/

/-- Non-vacuity: the SC outcome of SB is SC-consistent. -/
theorem nonvacuity_tsoConsistent_of_scConsistent : sbSC.SCConsistent := by decide

/-- The hypothesis is needed: MP's weak outcome is not SC-consistent and not TSO-consistent. -/
theorem tsoConsistent_of_scConsistent_needs_sc :
    ¬ mpWeak.SCConsistent ∧ ¬ mpWeak.TSOConsistent := by decide

/-- The hypothesis of `tsoConsistent_of_tsoConsistentKeepSameLocWR` is needed: MP's weak
outcome is neither consistent under the variant nor TSO-consistent. -/
theorem tsoConsistent_of_tsoConsistentKeepSameLocWR_needs_keep :
    ¬ mpWeak.TSOConsistentKeepSameLocWR ∧ ¬ mpWeak.TSOConsistent := by decide

/-! ## Fence-mapping soundness -/

/-- Non-vacuity (execution level). -/
theorem nonvacuity_scConsistentErased_of_tso_of_fenceBetweenWR :
    sbFencedSC.PoTotal ∧ sbFencedSC.RfSameLoc ∧ sbFencedSC.FenceBetweenWR ∧
      sbFencedSC.PerLocSC ∧ sbFencedSC.TsoGhbAcyclic := by decide

theorem fenceBetweenWR_needs_poTotal :
    poPartial.RfSameLoc ∧ poPartial.FenceBetweenWR ∧ poPartial.PerLocSC ∧
      poPartial.TsoGhbAcyclic ∧ ¬ poPartial.PoTotal ∧ ¬ poPartial.SCConsistentErased := by
  decide

theorem fenceBetweenWR_needs_rfSameLoc :
    rfWrongLoc.PoTotal ∧ rfWrongLoc.FenceBetweenWR ∧ rfWrongLoc.PerLocSC ∧
      rfWrongLoc.TsoGhbAcyclic ∧ ¬ rfWrongLoc.RfSameLoc ∧ ¬ rfWrongLoc.SCConsistentErased := by
  decide

theorem fenceBetweenWR_needs_fenceBetweenWR :
    sbWeak.PoTotal ∧ sbWeak.RfSameLoc ∧ sbWeak.PerLocSC ∧ sbWeak.TsoGhbAcyclic ∧
      ¬ sbWeak.FenceBetweenWR ∧ ¬ sbWeak.SCConsistentErased := by decide

theorem fenceBetweenWR_needs_perLocSC :
    readOwnLaterWrite.PoTotal ∧ readOwnLaterWrite.RfSameLoc ∧
      readOwnLaterWrite.FenceBetweenWR ∧ readOwnLaterWrite.TsoGhbAcyclic ∧
      ¬ readOwnLaterWrite.PerLocSC ∧ ¬ readOwnLaterWrite.SCConsistentErased := by decide

theorem fenceBetweenWR_needs_tsoGhbAcyclic :
    sbFencedWeak.PoTotal ∧ sbFencedWeak.RfSameLoc ∧ sbFencedWeak.FenceBetweenWR ∧
      sbFencedWeak.PerLocSC ∧ ¬ sbFencedWeak.TsoGhbAcyclic ∧
      ¬ sbFencedWeak.SCConsistentErased := by decide

/-- Non-vacuity (program level): an execution of `fenceAfterStores sbProg`. -/
theorem nonvacuity_scConsistentErased_of_tso_fenceAfterStores :
    ExecOf (fenceAfterStores sbProg) sbFencedSC ∧ sbFencedSC.RfSameLoc ∧
      sbFencedSC.PerLocSC ∧ sbFencedSC.TsoGhbAcyclic :=
  ⟨sbFencedSC_execOf, by decide⟩

/-- The program-level statement needs `X` to be an execution of the *fenced* program: the SB
weak execution is an execution of `sbProg`, satisfies the other hypotheses, and is not SC. -/
theorem fenceAfterStores_needs_execOf :
    ¬ ExecOf (fenceAfterStores sbProg) sbWeak ∧ sbWeak.RfSameLoc ∧ sbWeak.PerLocSC ∧
      sbWeak.TsoGhbAcyclic ∧ ¬ sbWeak.SCConsistentErased :=
  ⟨fun h => absurd h.length (by decide), by decide⟩

theorem fenceAfterStores_needs_rfSameLoc :
    ExecOf (fenceAfterStores loadStoreProg) loadStoreFencedBadRf ∧
      loadStoreFencedBadRf.PerLocSC ∧ loadStoreFencedBadRf.TsoGhbAcyclic ∧
      ¬ loadStoreFencedBadRf.RfSameLoc ∧ ¬ loadStoreFencedBadRf.SCConsistentErased :=
  ⟨loadStoreFencedBadRf_execOf, by decide⟩

theorem fenceAfterStores_needs_perLocSC :
    ExecOf (fenceAfterStores loadStoreSameProg) loadStoreSameFencedCoRW ∧
      loadStoreSameFencedCoRW.RfSameLoc ∧ loadStoreSameFencedCoRW.TsoGhbAcyclic ∧
      ¬ loadStoreSameFencedCoRW.PerLocSC ∧ ¬ loadStoreSameFencedCoRW.SCConsistentErased :=
  ⟨loadStoreSameFencedCoRW_execOf, by decide⟩

theorem fenceAfterStores_needs_tsoGhbAcyclic :
    ExecOf (fenceAfterStores sbProg) sbFencedWeak ∧ sbFencedWeak.RfSameLoc ∧
      sbFencedWeak.PerLocSC ∧ ¬ sbFencedWeak.TsoGhbAcyclic ∧
      ¬ sbFencedWeak.SCConsistentErased :=
  ⟨sbFencedWeak_execOf, by decide⟩

/-! ## Shared-location fencing -/

/-- Thread-local location `z = 2` read after an unfenced write to shared `x`:
`T0: x := 1; r := z` (reads `0`) ‖ `T1: x := 2`. -/
def sharedWLocalR : Exec 6 :=
  Exec.ofList [initW 0, initW 1, initW 2, W 0 0 1, R 0 2 0, W 1 0 2]
    [(2, 4)] [(0, 3), (0, 5), (3, 5)]

/-- Non-vacuity: `localWR` (unfenced local write before a shared read) and `sharedWLocalR`
(unfenced shared write before a local read) satisfy every hypothesis; the first fails
`FenceBetweenWR` and the second fails `FenceBetweenSharedWR`. -/
theorem nonvacuity_scConsistentErased_of_tso_of_fenceBetweenBothSharedWR :
    (localWR.PoTrans ∧ localWR.PoWithinThread ∧ localWR.PoTotal ∧ localWR.RfSameLoc ∧
      localWR.CoSameLoc ∧ localWR.FenceBetweenBothSharedWR ∧ localWR.PerLocSC ∧
      localWR.TsoGhbAcyclic ∧ ¬ localWR.FenceBetweenWR) ∧
    (sharedWLocalR.PoTrans ∧ sharedWLocalR.PoWithinThread ∧ sharedWLocalR.PoTotal ∧
      sharedWLocalR.RfSameLoc ∧ sharedWLocalR.CoSameLoc ∧
      sharedWLocalR.FenceBetweenBothSharedWR ∧ sharedWLocalR.PerLocSC ∧
      sharedWLocalR.TsoGhbAcyclic ∧ ¬ sharedWLocalR.FenceBetweenSharedWR) := by decide

theorem fenceBetweenBothSharedWR_needs_poTrans :
    poTwoCycle.PoWithinThread ∧ poTwoCycle.PoTotal ∧ poTwoCycle.RfSameLoc ∧
      poTwoCycle.CoSameLoc ∧ poTwoCycle.FenceBetweenBothSharedWR ∧ poTwoCycle.PerLocSC ∧
      poTwoCycle.TsoGhbAcyclic ∧ ¬ poTwoCycle.PoTrans ∧ ¬ poTwoCycle.SCConsistentErased := by
  decide

theorem fenceBetweenBothSharedWR_needs_poWithinThread :
    poIntoInit.PoTrans ∧ poIntoInit.PoTotal ∧ poIntoInit.RfSameLoc ∧ poIntoInit.CoSameLoc ∧
      poIntoInit.FenceBetweenBothSharedWR ∧ poIntoInit.PerLocSC ∧ poIntoInit.TsoGhbAcyclic ∧
      ¬ poIntoInit.PoWithinThread ∧ ¬ poIntoInit.SCConsistentErased := by decide

theorem fenceBetweenBothSharedWR_needs_poTotal :
    poPartial.PoTrans ∧ poPartial.PoWithinThread ∧ poPartial.RfSameLoc ∧ poPartial.CoSameLoc ∧
      poPartial.FenceBetweenBothSharedWR ∧ poPartial.PerLocSC ∧ poPartial.TsoGhbAcyclic ∧
      ¬ poPartial.PoTotal ∧ ¬ poPartial.SCConsistentErased := by decide

theorem fenceBetweenBothSharedWR_needs_rfSameLoc :
    rfWrongLoc.PoTrans ∧ rfWrongLoc.PoWithinThread ∧ rfWrongLoc.PoTotal ∧
      rfWrongLoc.CoSameLoc ∧ rfWrongLoc.FenceBetweenBothSharedWR ∧ rfWrongLoc.PerLocSC ∧
      rfWrongLoc.TsoGhbAcyclic ∧ ¬ rfWrongLoc.RfSameLoc ∧ ¬ rfWrongLoc.SCConsistentErased := by
  decide

theorem fenceBetweenBothSharedWR_needs_coSameLoc :
    coAcrossLocs.PoTrans ∧ coAcrossLocs.PoWithinThread ∧ coAcrossLocs.PoTotal ∧
      coAcrossLocs.RfSameLoc ∧ coAcrossLocs.FenceBetweenBothSharedWR ∧ coAcrossLocs.PerLocSC ∧
      coAcrossLocs.TsoGhbAcyclic ∧ ¬ coAcrossLocs.CoSameLoc ∧
      ¬ coAcrossLocs.SCConsistentErased := by decide

theorem fenceBetweenBothSharedWR_needs_fenceBetweenBothSharedWR :
    sbWeak.PoTrans ∧ sbWeak.PoWithinThread ∧ sbWeak.PoTotal ∧ sbWeak.RfSameLoc ∧
      sbWeak.CoSameLoc ∧ sbWeak.PerLocSC ∧ sbWeak.TsoGhbAcyclic ∧
      ¬ sbWeak.FenceBetweenBothSharedWR ∧ ¬ sbWeak.SCConsistentErased := by decide

theorem fenceBetweenBothSharedWR_needs_perLocSC :
    readOwnLaterWrite.PoTrans ∧ readOwnLaterWrite.PoWithinThread ∧
      readOwnLaterWrite.PoTotal ∧ readOwnLaterWrite.RfSameLoc ∧ readOwnLaterWrite.CoSameLoc ∧
      readOwnLaterWrite.FenceBetweenBothSharedWR ∧ readOwnLaterWrite.TsoGhbAcyclic ∧
      ¬ readOwnLaterWrite.PerLocSC ∧ ¬ readOwnLaterWrite.SCConsistentErased := by decide

theorem fenceBetweenBothSharedWR_needs_tsoGhbAcyclic :
    sbFencedWeak.PoTrans ∧ sbFencedWeak.PoWithinThread ∧ sbFencedWeak.PoTotal ∧
      sbFencedWeak.RfSameLoc ∧ sbFencedWeak.CoSameLoc ∧
      sbFencedWeak.FenceBetweenBothSharedWR ∧ sbFencedWeak.PerLocSC ∧
      ¬ sbFencedWeak.TsoGhbAcyclic ∧ ¬ sbFencedWeak.SCConsistentErased := by decide

/-- **Unsoundness of partial fencing on SB.** SB with a fence after thread 0's store only has
a well-formed TSO-consistent execution that is not SC-consistent even after fence erasure. In
it, thread 0's write→read pair is separated by a fence and thread 1's is not, so the execution
fails `FenceBetweenSharedWR` and `FenceBetweenBothSharedWR`. -/
theorem sbOneFence_execution_tso_not_scErased :
    ExecOf sbOneFenceProg sbOneFenceWeak ∧ sbOneFenceWeak.Wf ∧
      sbOneFenceWeak.TSOConsistent ∧ ¬ sbOneFenceWeak.SCConsistentErased ∧
      sbOneFenceWeak.fenceOrd ⟨2, by decide⟩ ⟨4, by decide⟩ = true ∧
      sbOneFenceWeak.fenceOrd ⟨5, by decide⟩ ⟨6, by decide⟩ = false ∧
      ¬ sbOneFenceWeak.FenceBetweenSharedWR ∧ ¬ sbOneFenceWeak.FenceBetweenBothSharedWR :=
  ⟨sbOneFenceWeak_execOf, by decide⟩

/-! ## Fence erasure -/

theorem nonvacuity_scConsistent_of_scConsistentErased :
    sbFencedSC.PoIrrefl ∧ sbFencedSC.PoTrans ∧ sbFencedSC.RfKinds ∧ sbFencedSC.CoKinds ∧
      sbFencedSC.SCConsistentErased := by decide

theorem scConsistent_of_scConsistentErased_needs_poIrrefl :
    fenceSelfPo.PoTrans ∧ fenceSelfPo.RfKinds ∧ fenceSelfPo.CoKinds ∧
      fenceSelfPo.SCConsistentErased ∧ ¬ fenceSelfPo.PoIrrefl ∧
      ¬ fenceSelfPo.SCConsistent := by decide

theorem scConsistent_of_scConsistentErased_needs_poTrans :
    fenceNonTransPo.PoIrrefl ∧ fenceNonTransPo.RfKinds ∧ fenceNonTransPo.CoKinds ∧
      fenceNonTransPo.SCConsistentErased ∧ ¬ fenceNonTransPo.PoTrans ∧
      ¬ fenceNonTransPo.SCConsistent := by decide

theorem scConsistent_of_scConsistentErased_needs_rfKinds :
    rfFromFence.PoIrrefl ∧ rfFromFence.PoTrans ∧ rfFromFence.CoKinds ∧
      rfFromFence.SCConsistentErased ∧ ¬ rfFromFence.RfKinds ∧
      ¬ rfFromFence.SCConsistent := by decide

theorem scConsistent_of_scConsistentErased_needs_coKinds :
    coFromFence.PoIrrefl ∧ coFromFence.PoTrans ∧ coFromFence.RfKinds ∧
      coFromFence.SCConsistentErased ∧ ¬ coFromFence.CoKinds ∧
      ¬ coFromFence.SCConsistent := by decide

theorem scConsistent_of_scConsistentErased_needs_scErased :
    sbWeak.PoIrrefl ∧ sbWeak.PoTrans ∧ sbWeak.RfKinds ∧ sbWeak.CoKinds ∧
      ¬ sbWeak.SCConsistentErased ∧ ¬ sbWeak.SCConsistent := by decide

/-! ## Race freedom of straight-line programs -/

/-- Instances of the characterizations: a program without conflicts (`loadStoreProg`) and one
with conflicts (`sbProg`); the compiled SB program satisfies the both-sides static condition,
SB does not satisfy even the either-side condition, and SB with one fence satisfies the
either-side but not the both-sides condition. -/
theorem nonvacuity_straightLine_race_characterizations :
    (∀ a b, ¬ (skel loadStoreProg).Conflict a b) ∧ ¬ (∀ a b, ¬ (skel sbProg).Conflict a b) ∧
      (fenceAfterStores sbProg).ConflictsWRFenced ∧ ¬ sbProg.ConflictsWRFencedEither ∧
      sbOneFenceProg.ConflictsWRFencedEither ∧ ¬ sbOneFenceProg.ConflictsWRFenced := by
  decide

/-- Non-vacuity of `fenceBetweenSharedWR_of_conflictsWRFenced` and of
`scConsistent_of_tso_of_conflictsWRFenced`: the compiled SB program and its SC execution. -/
theorem nonvacuity_scConsistent_of_tso_of_conflictsWRFenced :
    (fenceAfterStores sbProg).ConflictsWRFenced ∧ ExecOf (fenceAfterStores sbProg) sbFencedSC ∧
      sbFencedSC.RfSameLoc ∧ sbFencedSC.RfKinds ∧ sbFencedSC.CoKinds ∧
      sbFencedSC.TSOConsistent :=
  ⟨by decide, sbFencedSC_execOf, by decide⟩

theorem fenceBetweenSharedWR_of_conflictsWRFenced_needs_conflictsWRFenced :
    ¬ sbProg.ConflictsWRFenced ∧ ExecOf sbProg sbWeak ∧ ¬ sbWeak.FenceBetweenSharedWR :=
  ⟨by decide, sbWeak_execOf, by decide⟩

theorem fenceBetweenSharedWR_of_conflictsWRFenced_needs_execOf :
    Prog.ConflictsWRFenced [] ∧ ¬ ExecOf [] sbWeak ∧ ¬ sbWeak.FenceBetweenSharedWR :=
  ⟨by decide, fun h => absurd h.length (by decide), by decide⟩

/-- A store-load program whose read takes its value from the `po`-later fence (`rf` out of a
fence; the fence event has location `0`). -/
def loadStoreFenceRfFromFence : Exec 4 :=
  Exec.ofList [initW 0, R 0 0 0, W 0 0 1, F 0] [(3, 1)] [(0, 2)]

/-- A store-fence program with a `co` edge out of the fence into the write. -/
def storeFenceCoFromFence : Exec 3 :=
  Exec.ofList [initW 0, W 0 0 1, F 0] [] [(0, 1), (2, 1)]

theorem loadStoreFenceRfFromFence_execOf :
    ExecOf [[.load 0, .store 0 1, .mfence]] loadStoreFenceRfFromFence :=
  ⟨rfl, by decide, by decide, by decide, by decide, by decide⟩

theorem storeFenceCoFromFence_execOf : ExecOf [[.store 0 1, .mfence]] storeFenceCoFromFence :=
  ⟨rfl, by decide, by decide, by decide, by decide, by decide⟩

theorem scConsistent_of_tso_of_conflictsWRFenced_needs_conflictsWRFenced :
    ¬ sbProg.ConflictsWRFenced ∧ ExecOf sbProg sbWeak ∧ sbWeak.RfSameLoc ∧ sbWeak.RfKinds ∧
      sbWeak.CoKinds ∧ sbWeak.TSOConsistent ∧ ¬ sbWeak.SCConsistent :=
  ⟨by decide, sbWeak_execOf, by decide⟩

theorem scConsistent_of_tso_of_conflictsWRFenced_needs_execOf :
    Prog.ConflictsWRFenced [] ∧ ¬ ExecOf [] sbWeak ∧ sbWeak.RfSameLoc ∧ sbWeak.RfKinds ∧
      sbWeak.CoKinds ∧ sbWeak.TSOConsistent ∧ ¬ sbWeak.SCConsistent :=
  ⟨by decide, fun h => absurd h.length (by decide), by decide⟩

theorem scConsistent_of_tso_of_conflictsWRFenced_needs_rfSameLoc :
    loadStoreProg.ConflictsWRFenced ∧ ExecOf loadStoreProg loadStoreBadRf ∧
      loadStoreBadRf.RfKinds ∧ loadStoreBadRf.CoKinds ∧ loadStoreBadRf.TSOConsistent ∧
      ¬ loadStoreBadRf.RfSameLoc ∧ ¬ loadStoreBadRf.SCConsistent :=
  ⟨by decide, loadStoreBadRf_execOf, by decide⟩

theorem scConsistent_of_tso_of_conflictsWRFenced_needs_rfKinds :
    Prog.ConflictsWRFenced [[.load 0, .store 0 1, .mfence]] ∧
      ExecOf [[.load 0, .store 0 1, .mfence]] loadStoreFenceRfFromFence ∧
      loadStoreFenceRfFromFence.RfSameLoc ∧ loadStoreFenceRfFromFence.CoKinds ∧
      loadStoreFenceRfFromFence.TSOConsistent ∧ ¬ loadStoreFenceRfFromFence.RfKinds ∧
      ¬ loadStoreFenceRfFromFence.SCConsistent :=
  ⟨by decide, loadStoreFenceRfFromFence_execOf, by decide⟩

theorem scConsistent_of_tso_of_conflictsWRFenced_needs_coKinds :
    Prog.ConflictsWRFenced [[.store 0 1, .mfence]] ∧
      ExecOf [[.store 0 1, .mfence]] storeFenceCoFromFence ∧
      storeFenceCoFromFence.RfSameLoc ∧ storeFenceCoFromFence.RfKinds ∧
      storeFenceCoFromFence.TSOConsistent ∧ ¬ storeFenceCoFromFence.CoKinds ∧
      ¬ storeFenceCoFromFence.SCConsistent :=
  ⟨by decide, storeFenceCoFromFence_execOf, by decide⟩

theorem scConsistent_of_tso_of_conflictsWRFenced_needs_tso :
    (fenceAfterStores sbProg).ConflictsWRFenced ∧ ExecOf (fenceAfterStores sbProg) sbFencedWeak ∧
      sbFencedWeak.RfSameLoc ∧ sbFencedWeak.RfKinds ∧ sbFencedWeak.CoKinds ∧
      ¬ sbFencedWeak.TSOConsistent ∧ ¬ sbFencedWeak.SCConsistent :=
  ⟨by decide, sbFencedWeak_execOf, by decide⟩

/-- `T0: z := 1; r := x` ‖ `T1: x := 2` with thread-local `z = 2` (the program of
`localWR`). -/
def localWRProg : Prog := [[.store 2 1, .load 0], [.store 0 2]]

theorem localWR_execOf : ExecOf localWRProg localWR :=
  ⟨rfl, by decide, by decide, by decide, by decide, by decide⟩

/-- The both-sides static condition is strictly stronger than shared-location fencing: in
`localWRProg` the read of shared `x` follows an unfenced write to thread-local `z`, so the
program fails `ConflictsWRFenced`, yet its execution `localWR` satisfies
`FenceBetweenSharedWR` (and is well formed, TSO-consistent and SC-consistent). -/
theorem localWRProg_not_conflictsWRFenced_but_fenceBetweenSharedWR :
    ¬ localWRProg.ConflictsWRFenced ∧ ExecOf localWRProg localWR ∧ localWR.Wf ∧
      localWR.TSOConsistent ∧ localWR.FenceBetweenSharedWR ∧ localWR.SCConsistent :=
  ⟨by decide, localWR_execOf, by decide⟩

/-- **The either-side static condition does not give SC on TSO.** In SB with a fence after
thread 0's store, thread 0's write and read are separated by an actual fence, so every
conflicting pair has a side satisfying `NoUnfencedWRIncident` and every well-formed SC
execution is `RaceFreeEither`; yet the program has a well-formed TSO-consistent execution that
is not SC-consistent. -/
theorem conflictsWRFencedEither_does_not_imply_sc :
    sbOneFenceProg.ConflictsWRFencedEither ∧
      (∀ (m : Nat) (Y : Exec m), ExecOf sbOneFenceProg Y → Y.Wf → Y.SCConsistent →
        Y.RaceFreeEither) ∧
      sbOneFenceWeak.fenceOrd ⟨2, by decide⟩ ⟨4, by decide⟩ = true ∧
      ExecOf sbOneFenceProg sbOneFenceWeak ∧ sbOneFenceWeak.Wf ∧
      sbOneFenceWeak.TSOConsistent ∧ ¬ sbOneFenceWeak.SCConsistent := by
  have h : sbOneFenceProg.ConflictsWRFencedEither := by decide
  exact ⟨h, (raceFreeEither_sc_executions_iff_conflictsWRFencedEither _).mpr h, by decide,
    sbOneFenceWeak_execOf, by decide⟩

end Toy.WMM
