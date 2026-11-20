import ToyWMM.Prog

/-!
# Litmus tests as programs and concrete candidate executions

Locations: `x = 0`, `y = 1`. Each litmus test is given as a straight-line program and as one
explicit candidate execution of that program (`ExecOf`) exhibiting the named outcome. Every
execution lists the two initialisation writes first (indices `0` and `1`), then the events of
each thread in program order. Each verdict is checked by `decide` and concerns the displayed
candidate execution only. Written values are distinct, so the value a read returns determines
its `rf` source and the final memory state determines `co`; that the displayed execution is
therefore the only well-formed candidate with the named outcome is an argument in prose, not a
proved statement.
-/

namespace Toy.WMM

/-- SB: `T0: x := 1; r0 := y` ‖ `T1: y := 2; r1 := x`. -/
def sbProg : Prog := [[.store 0 1, .load 1], [.store 1 2, .load 0]]

/-- SB with a fence after the store of thread 0 only. -/
def sbOneFenceProg : Prog := [[.store 0 1, .mfence, .load 1], [.store 1 2, .load 0]]

/-- MP: `T0: x := 1; y := 2` ‖ `T1: r0 := y; r1 := x`. -/
def mpProg : Prog := [[.store 0 1, .store 1 2], [.load 1, .load 0]]

/-- LB: `T0: r0 := x; y := 1` ‖ `T1: r1 := y; x := 2`. -/
def lbProg : Prog := [[.load 0, .store 1 1], [.load 1, .store 0 2]]

/-- 2+2W: `T0: x := 1; y := 2` ‖ `T1: y := 3; x := 4`. -/
def w22Prog : Prog := [[.store 0 1, .store 1 2], [.store 1 3, .store 0 4]]

/-- IRIW: `T0: x := 1` ‖ `T1: y := 2` ‖ `T2: r0 := x; r1 := y` ‖ `T3: r2 := y; r3 := x`. -/
def iriwProg : Prog := [[.store 0 1], [.store 1 2], [.load 0, .load 1], [.load 1, .load 0]]

/-- n6: `T0: x := 1; r0 := x; r1 := y` ‖ `T1: y := 2; x := 2`. -/
def n6Prog : Prog := [[.store 0 1, .load 0, .load 1], [.store 1 2, .store 0 2]]

/-- R: `T0: x := 1; y := 2` ‖ `T1: y := 3; r0 := x`. -/
def rProg : Prog := [[.store 0 1, .store 1 2], [.store 1 3, .load 0]]

/-- The mapping applied to SB inserts exactly the two SB+mfences fences. -/
theorem fenceAfterStores_sbProg :
    fenceAfterStores sbProg = [[.store 0 1, .mfence, .load 1], [.store 1 2, .mfence, .load 0]] := by
  decide

namespace Litmus

open Event

/-- **SB** (store buffering), weak outcome `r0 = 0 ∧ r1 = 0`.
`T0: x := 1; r0 := y` ‖ `T1: y := 2; r1 := x`. -/
def sbWeak : Exec 6 :=
  Exec.ofList [initW 0, initW 1, W 0 0 1, R 0 1 0, W 1 1 2, R 1 0 0]
    [(1, 3), (0, 5)] [(0, 2), (1, 4)]

/-- **SB+mfences**: SB with a fence between the store and the load in each thread, weak
outcome `r0 = 0 ∧ r1 = 0`. -/
def sbFencedWeak : Exec 8 :=
  Exec.ofList [initW 0, initW 1, W 0 0 1, F 0, R 0 1 0, W 1 1 2, F 1, R 1 0 0]
    [(1, 4), (0, 7)] [(0, 2), (1, 5)]

/-- **SB+mfence+po**: SB with a fence in thread 0 only, weak outcome. -/
def sbOneFenceWeak : Exec 7 :=
  Exec.ofList [initW 0, initW 1, W 0 0 1, F 0, R 0 1 0, W 1 1 2, R 1 0 0]
    [(1, 4), (0, 6)] [(0, 2), (1, 5)]

/-- **MP** (message passing), weak outcome `r0 = 2 ∧ r1 = 0`.
`T0: x := 1; y := 2` ‖ `T1: r0 := y; r1 := x`. -/
def mpWeak : Exec 6 :=
  Exec.ofList [initW 0, initW 1, W 0 0 1, W 0 1 2, R 1 1 2, R 1 0 0]
    [(3, 4), (0, 5)] [(0, 2), (1, 3)]

/-- **LB** (load buffering), weak outcome `r0 = 2 ∧ r1 = 1`.
`T0: r0 := x; y := 1` ‖ `T1: r1 := y; x := 2`. -/
def lbWeak : Exec 6 :=
  Exec.ofList [initW 0, initW 1, R 0 0 2, W 0 1 1, R 1 1 1, W 1 0 2]
    [(5, 2), (3, 4)] [(0, 5), (1, 3)]

/-- **2+2W**, weak outcome: final `x = 1 ∧ y = 3`, i.e. each thread's first write is
`co`-after the other thread's second write.
`T0: x := 1; y := 2` ‖ `T1: y := 3; x := 4`. -/
def w22Weak : Exec 6 :=
  Exec.ofList [initW 0, initW 1, W 0 0 1, W 0 1 2, W 1 1 3, W 1 0 4]
    [] [(0, 5), (5, 2), (0, 2), (1, 3), (3, 4), (1, 4)]

/-- **IRIW** (independent reads of independent writes), weak outcome: the two readers see
the two writes in opposite orders.
`T0: x := 1` ‖ `T1: y := 2` ‖ `T2: r0 := x; r1 := y` ‖ `T3: r2 := y; r3 := x`,
with `r0 = 1, r1 = 0, r2 = 2, r3 = 0`. -/
def iriwWeak : Exec 8 :=
  Exec.ofList [initW 0, initW 1, W 0 0 1, W 1 1 2, R 2 0 1, R 2 1 0, R 3 1 2, R 3 0 0]
    [(2, 4), (1, 5), (3, 6), (0, 7)] [(0, 2), (1, 3)]

/-- **n6** (from the x86-TSO papers), outcome `r0 = 1 ∧ r1 = 0` with final `x = 1`.
`T0: x := 1; r0 := x; r1 := y` ‖ `T1: y := 2; x := 2`. Thread 0 reads its own buffered
write (store forwarding) before it becomes globally visible. -/
def n6Weak : Exec 7 :=
  Exec.ofList [initW 0, initW 1, W 0 0 1, R 0 0 1, R 0 1 0, W 1 1 2, W 1 0 2]
    [(2, 3), (1, 4)] [(0, 6), (6, 2), (0, 2), (1, 5)]

/-- **R**, weak outcome `r0 = 0` with final `y = 3` (thread 0's `y := 2` is `co`-before
thread 1's `y := 3`). `T0: x := 1; y := 2` ‖ `T1: y := 3; r0 := x`. -/
def rWeak : Exec 6 :=
  Exec.ofList [initW 0, initW 1, W 0 0 1, W 0 1 2, W 1 1 3, R 1 0 0]
    [(0, 5)] [(0, 2), (1, 3), (1, 4), (3, 4)]

/-- An SC outcome of SB (`r0 = 2 ∧ r1 = 1`: each read sees the other thread's write). -/
def sbSC : Exec 6 :=
  Exec.ofList [initW 0, initW 1, W 0 0 1, R 0 1 2, W 1 1 2, R 1 0 1]
    [(4, 3), (2, 5)] [(0, 2), (1, 4)]

/-- An SC outcome of SB+mfences (`r0 = 2 ∧ r1 = 1`). -/
def sbFencedSC : Exec 8 :=
  Exec.ofList [initW 0, initW 1, W 0 0 1, F 0, R 0 1 2, W 1 1 2, F 1, R 1 0 1]
    [(5, 4), (2, 7)] [(0, 2), (1, 5)]

end Litmus

open Litmus in
theorem sbWeak_execOf : ExecOf sbProg sbWeak :=
  ⟨rfl, by decide, by decide, by decide, by decide, by decide⟩
open Litmus in
theorem sbSC_execOf : ExecOf sbProg sbSC :=
  ⟨rfl, by decide, by decide, by decide, by decide, by decide⟩
open Litmus in
theorem sbFencedWeak_execOf : ExecOf (fenceAfterStores sbProg) sbFencedWeak :=
  ⟨rfl, by decide, by decide, by decide, by decide, by decide⟩
open Litmus in
theorem sbFencedSC_execOf : ExecOf (fenceAfterStores sbProg) sbFencedSC :=
  ⟨rfl, by decide, by decide, by decide, by decide, by decide⟩
open Litmus in
theorem sbOneFenceWeak_execOf : ExecOf sbOneFenceProg sbOneFenceWeak :=
  ⟨rfl, by decide, by decide, by decide, by decide, by decide⟩
open Litmus in
theorem mpWeak_execOf : ExecOf mpProg mpWeak :=
  ⟨rfl, by decide, by decide, by decide, by decide, by decide⟩
open Litmus in
theorem lbWeak_execOf : ExecOf lbProg lbWeak :=
  ⟨rfl, by decide, by decide, by decide, by decide, by decide⟩
open Litmus in
theorem w22Weak_execOf : ExecOf w22Prog w22Weak :=
  ⟨rfl, by decide, by decide, by decide, by decide, by decide⟩
open Litmus in
theorem iriwWeak_execOf : ExecOf iriwProg iriwWeak :=
  ⟨rfl, by decide, by decide, by decide, by decide, by decide⟩
open Litmus in
theorem n6Weak_execOf : ExecOf n6Prog n6Weak :=
  ⟨rfl, by decide, by decide, by decide, by decide, by decide⟩
open Litmus in
theorem rWeak_execOf : ExecOf rProg rWeak :=
  ⟨rfl, by decide, by decide, by decide, by decide, by decide⟩

namespace Litmus

/-! ## The litmus table

Each verdict concerns the displayed candidate execution of the named program; each statement
also proves that the execution is a well-formed candidate execution of that program. -/

/-- SB: the displayed weak-outcome execution of `sbProg` is well formed, TSO-consistent and
not SC-consistent. -/
theorem sb_weak_tso_allowed_sc_forbidden :
    ExecOf sbProg sbWeak ∧ sbWeak.Wf ∧ sbWeak.TSOConsistent ∧ ¬ sbWeak.SCConsistent :=
  ⟨sbWeak_execOf, by decide⟩

/-- MP: the displayed weak-outcome execution of `mpProg` is well formed and neither
TSO-consistent nor SC-consistent. -/
theorem mp_weak_tso_forbidden_sc_forbidden :
    ExecOf mpProg mpWeak ∧ mpWeak.Wf ∧ ¬ mpWeak.TSOConsistent ∧ ¬ mpWeak.SCConsistent :=
  ⟨mpWeak_execOf, by decide⟩

/-- LB: the displayed weak-outcome execution of `lbProg` is well formed and neither
TSO-consistent nor SC-consistent. -/
theorem lb_weak_tso_forbidden_sc_forbidden :
    ExecOf lbProg lbWeak ∧ lbWeak.Wf ∧ ¬ lbWeak.TSOConsistent ∧ ¬ lbWeak.SCConsistent :=
  ⟨lbWeak_execOf, by decide⟩

/-- 2+2W: the displayed weak-outcome execution of `w22Prog` is well formed and neither
TSO-consistent nor SC-consistent. -/
theorem w22_weak_tso_forbidden_sc_forbidden :
    ExecOf w22Prog w22Weak ∧ w22Weak.Wf ∧ ¬ w22Weak.TSOConsistent ∧ ¬ w22Weak.SCConsistent :=
  ⟨w22Weak_execOf, by decide⟩

/-- IRIW: the displayed weak-outcome execution of `iriwProg` is well formed and neither
TSO-consistent nor SC-consistent. -/
theorem iriw_weak_tso_forbidden_sc_forbidden :
    ExecOf iriwProg iriwWeak ∧ iriwWeak.Wf ∧ ¬ iriwWeak.TSOConsistent ∧
      ¬ iriwWeak.SCConsistent :=
  ⟨iriwWeak_execOf, by decide⟩

/-- SB+mfences: the displayed weak-outcome execution of `fenceAfterStores sbProg` is well
formed and neither TSO-consistent nor SC-consistent (the TSO cycle uses `fenceOrd`). -/
theorem sbFenced_weak_tso_forbidden_sc_forbidden :
    ExecOf (fenceAfterStores sbProg) sbFencedWeak ∧ sbFencedWeak.Wf ∧
      ¬ sbFencedWeak.TSOConsistent ∧ ¬ sbFencedWeak.SCConsistent :=
  ⟨sbFencedWeak_execOf, by decide⟩

/-- R: the displayed weak-outcome execution of `rProg` is well formed, TSO-consistent and not
SC-consistent. -/
theorem r_weak_tso_allowed_sc_forbidden :
    ExecOf rProg rWeak ∧ rWeak.Wf ∧ rWeak.TSOConsistent ∧ ¬ rWeak.SCConsistent :=
  ⟨rWeak_execOf, by decide⟩

/-- n6: the displayed store-forwarding execution of `n6Prog` is well formed, TSO-consistent and
not SC-consistent, and it is rejected by the variant that keeps same-location write→read pairs
in `ppo`. -/
theorem n6_weak_tso_allowed_keepSameLocWR_forbidden :
    ExecOf n6Prog n6Weak ∧ n6Weak.Wf ∧ n6Weak.TSOConsistent ∧
      ¬ n6Weak.TSOConsistentKeepSameLocWR ∧ ¬ n6Weak.SCConsistent :=
  ⟨n6Weak_execOf, by decide⟩

/-- The SC outcomes of SB and SB+mfences are SC-consistent. -/
theorem sbSC_sbFencedSC_scConsistent :
    sbSC.Wf ∧ sbSC.SCConsistent ∧ sbFencedSC.Wf ∧ sbFencedSC.SCConsistent := by decide

end Litmus

end Toy.WMM
