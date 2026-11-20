import ToyWMM.DRF

/-!
# Concrete programs and their executions
-/

namespace Toy.WMM

open Litmus

/-- A one-thread program `r0 := y; x := 1` (no conflicting accesses). -/
def loadStoreProg : Prog := [[.load 1, .store 0 1]]

/-- A one-thread program `r0 := x; x := 1` (no conflicting accesses). -/
def loadStoreSameProg : Prog := [[.load 0, .store 0 1]]

/-- An SC execution of SB in which thread 0 runs to completion first:
`r0 = 0` (initial `y`) and `r1 = 1`. Its `y := 2` and `r0 := y` race. -/
def sbSeq : Exec 6 :=
  Exec.ofList [.initW 0, .initW 1, .W 0 0 1, .R 0 1 0, .W 1 1 2, .R 1 0 1]
    [(1, 3), (2, 5)] [(0, 2), (1, 4)]

theorem sbSeq_execOf : ExecOf sbProg sbSeq :=
  ⟨rfl, by decide, by decide, by decide, by decide, by decide⟩

/-- An ill-formed execution of `loadStoreProg`: the read of `y` takes its value from the
`po`-later write to `x`. -/
def loadStoreBadRf : Exec 4 :=
  Exec.ofList [.initW 0, .initW 1, .R 0 1 1, .W 0 0 1] [(3, 2)] [(0, 3)]

theorem loadStoreBadRf_execOf : ExecOf loadStoreProg loadStoreBadRf :=
  ⟨rfl, by decide, by decide, by decide, by decide, by decide⟩

/-- The same ill-formed `rf` in the fenced program `fenceAfterStores loadStoreProg`. -/
def loadStoreFencedBadRf : Exec 5 :=
  Exec.ofList [.initW 0, .initW 1, .R 0 1 1, .W 0 0 1, .F 0] [(3, 2)] [(0, 3)]

theorem loadStoreFencedBadRf_execOf :
    ExecOf (fenceAfterStores loadStoreProg) loadStoreFencedBadRf :=
  ⟨rfl, by decide, by decide, by decide, by decide, by decide⟩

/-- A per-location-SC violation in the fenced program `fenceAfterStores loadStoreSameProg`:
the read of `x` takes its value from the `po`-later write to `x`. -/
def loadStoreSameFencedCoRW : Exec 4 :=
  Exec.ofList [.initW 0, .R 0 0 1, .W 0 0 1, .F 0] [(2, 1)] [(0, 2)]

theorem loadStoreSameFencedCoRW_execOf :
    ExecOf (fenceAfterStores loadStoreSameProg) loadStoreSameFencedCoRW :=
  ⟨rfl, by decide, by decide, by decide, by decide, by decide⟩

end Toy.WMM
