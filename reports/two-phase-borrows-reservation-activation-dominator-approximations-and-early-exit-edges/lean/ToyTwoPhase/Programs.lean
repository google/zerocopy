import ToyTwoPhase.Checkers

/-!
# Concrete programs

Node 0 is the entry unless stated. `succ`/`unw` are given as lists indexed by node.
Every fact about these programs below is proved by `decide` (kernel evaluation of the
checkers `pathViaB`, `run`, `certOK`, each proved to agree with the definitions).
-/

namespace Toy.TwoPhase

/-- Build successor lists from a list indexed by node (missing entries: no successors). -/
def mkEdges {n : Nat} (l : List (List (Fin n))) : Edges n := fun i => l.getD i.val []

/-- Build statements from a list indexed by node (missing entries: `nop`). -/
def mkStmt {n : Nat} (l : List Stmt) : Fin n → Stmt := fun i => l.getD i.val .nop

/-- `v.push(v.len())`: `0 → R=1 → 2: readX → A=3 → 4: writeThrough`. -/
def pPush : Prog 5 where
  entry := 0
  succ := mkEdges [[1], [2], [3], [4], []]
  unw := mkEdges []
  R := 1
  A := 3
  stmt := mkStmt [.nop, .nop, .readX, .nop, .writeThrough]
  hRA := by decide

/-- `loop { v.push(v.len()) }`: `0 → R=1 → 2: readX → A=3 → 4: writeThrough → {1, 5}`. -/
def pLoopOK : Prog 6 where
  entry := 0
  succ := mkEdges [[1], [2], [3], [4], [1, 5], []]
  unw := mkEdges []
  R := 1
  A := 3
  stmt := mkStmt [.nop, .nop, .readX, .nop, .writeThrough, .nop]
  hRA := by decide

/-- Early exit (toy rendering of the reproducer of rust-lang/rust#160598): `0 → R=1 → 2`
(argument evaluation) `→ {A=3, J=4}`; the edge `2 → 4` is the `break`; `3 → 4`;
`4: borrowShared s0 → 5: useShared s0 → 6: writeThrough → 7: useShared s0`. -/
def pBreak : Prog 8 where
  entry := 0
  succ := mkEdges [[1], [2], [3, 4], [4], [5], [6], [7], []]
  unw := mkEdges []
  R := 1
  A := 3
  stmt := mkStmt [.nop, .nop, .nop, .nop, .borrowShared .s0, .useShared .s0, .writeThrough,
    .useShared .s0]
  hRA := by decide

/-- `pBreak` with the `break` hoisted above the reservation: `0 → 1 → {R=2, J=4}`,
`2 → A=3 → 4`, same tail as `pBreak`. -/
def pBreakHoisted : Prog 8 where
  entry := 0
  succ := mkEdges [[1], [2, 4], [3], [4], [5], [6], [7], []]
  unw := mkEdges []
  R := 2
  A := 3
  stmt := mkStmt [.nop, .nop, .nop, .nop, .borrowShared .s0, .useShared .s0, .writeThrough,
    .useShared .s0]
  hRA := by decide

/-- `pBreak` with the read at the join replaced by a write, `4: writeX`, and `5, 7: nop`. -/
def pBreakWrite : Prog 8 where
  entry := 0
  succ := mkEdges [[1], [2], [3, 4], [4], [5], [6], [7], []]
  unw := mkEdges []
  R := 1
  A := 3
  stmt := mkStmt [.nop, .nop, .nop, .nop, .writeX, .nop, .writeThrough, .nop]
  hRA := by decide

/-- `break` between `R` and `A` with `r` dead at the join: `0 → R=1 → 2 → {A=3, J=4}`,
`3 → 4`, `4: readX → 5`. -/
def pBreakDead : Prog 6 where
  entry := 0
  succ := mkEdges [[1], [2], [3, 4], [4], [5], []]
  unw := mkEdges []
  R := 1
  A := 3
  stmt := mkStmt [.nop, .nop, .nop, .nop, .readX, .nop]
  hRA := by decide

/-- A loop re-entering the reserved region from `A` without `R`:
`0 → R=1 → 2: readX → A=3 → {2, 4}`. -/
def pLoop1 : Prog 5 where
  entry := 0
  succ := mkEdges [[1], [2], [3], [2, 4], []]
  unw := mkEdges []
  R := 1
  A := 3
  stmt := mkStmt [.nop, .nop, .readX, .nop, .nop]
  hRA := by decide

/-- A `break` whose target loops back to `R`, so `A` still post-dominates `R`:
`0 → R=1 → 2 → {A=3, L=4}`, `3 → {4, 6}`, `4: readX → 5: writeThrough → 1`, `6` exit. -/
def pLoopBack : Prog 7 where
  entry := 0
  succ := mkEdges [[1], [2], [3, 4], [4, 6], [5], [1], []]
  unw := mkEdges []
  R := 1
  A := 3
  stmt := mkStmt [.nop, .nop, .nop, .nop, .readX, .writeThrough, .nop]
  hRA := by decide

/-- A `break` whose target diverges, so `A` still post-dominates `R`:
`0 → R=1 → 2 → {A=3, L=4}`, `3 → {4, 6}`, `4: readX → 5: writeThrough → 4`, `6` exit. -/
def pDiverge : Prog 7 where
  entry := 0
  succ := mkEdges [[1], [2], [3, 4], [4, 6], [5], [4], []]
  unw := mkEdges []
  R := 1
  A := 3
  stmt := mkStmt [.nop, .nop, .nop, .nop, .readX, .writeThrough, .nop]
  hRA := by decide

/-- A join reached from a path without `R` and from the reserved region:
`0 → 1 → {R=2, J=5}`, `2 → {A=3, 5}`, `3 → 6`, `5: readX → 6: writeThrough → 7`
(node `4` is unreachable). The write `6` executes with `r` active on the walk through `A`. -/
def pJoin : Prog 8 where
  entry := 0
  succ := mkEdges [[1], [2, 5], [3, 5], [6], [], [6], [7], []]
  unw := mkEdges []
  R := 2
  A := 3
  stmt := mkStmt [.nop, .nop, .nop, .nop, .nop, .readX, .writeThrough, .nop]
  hRA := by decide

/-- A read after the loan has ended, with a later `writeThrough`:
`0 → R=1 → A=2 → 3: endLoan → 4: readX → 5: writeThrough`. -/
def pEndThenRead : Prog 6 where
  entry := 0
  succ := mkEdges [[1], [2], [3], [4], [5], []]
  unw := mkEdges []
  R := 1
  A := 2
  stmt := mkStmt [.nop, .nop, .nop, .endLoan, .readX, .writeThrough]
  hRA := by decide

/-- A write to `x` during the reservation: `0 → R=1 → 2: writeX → A=3 → 4: writeThrough`. -/
def pWriteDuringRes : Prog 5 where
  entry := 0
  succ := mkEdges [[1], [2], [3], [4], []]
  unw := mkEdges []
  R := 1
  A := 3
  stmt := mkStmt [.nop, .nop, .writeX, .nop, .writeThrough]
  hRA := by decide

/-- A shared reborrow created during the reservation and used after the activation:
`0 → R=1 → 2: borrowShared s0 → A=3 → 4: useShared s0`. -/
def pSharedDuringRes : Prog 5 where
  entry := 0
  succ := mkEdges [[1], [2], [3], [4], []]
  unw := mkEdges []
  R := 1
  A := 3
  stmt := mkStmt [.nop, .nop, .borrowShared .s0, .nop, .useShared .s0]
  hRA := by decide

/-- A cleanup block shared by an unwinding edge before `A` and one after `A`, reading `x`
while `r` is live: normal `0 → R=1 → 2 → A=3 → 4 → 5`; unwinding `2 ⇢ 6`, `4 ⇢ 6`;
cleanup `6: readX → 7: writeThrough → 8`. -/
def pCleanup : Prog 9 where
  entry := 0
  succ := mkEdges [[1], [2], [3], [4], [5], [], [7], [8], []]
  unw := mkEdges [[], [], [6], [], [6], [], [], [], []]
  R := 1
  A := 3
  stmt := mkStmt [.nop, .nop, .nop, .nop, .nop, .nop, .readX, .writeThrough, .nop]
  hRA := by decide

/-- `v.push(v.len())` with unwinding edges before and after `A` into a cleanup block that reads
`x` only after the last use of `r`: normal `0 → R=1 → 2: readX → A=3 → 4: writeThrough → 5`;
unwinding `2 ⇢ 6`, `4 ⇢ 6`; cleanup `6: readX → 7`. -/
def pCleanupRead : Prog 8 where
  entry := 0
  succ := mkEdges [[1], [2], [3], [4], [5], [], [7], []]
  unw := mkEdges [[], [], [6], [], [6], [], [], []]
  R := 1
  A := 3
  stmt := mkStmt [.nop, .nop, .readX, .nop, .writeThrough, .nop, .readX, .nop]
  hRA := by decide

/-- A loop inside the argument, from which `A` stays reachable:
`0 → R=1 → 2: readX → {2, A=3}`, `3 → 4: writeThrough`. -/
def pArgLoop : Prog 5 where
  entry := 0
  succ := mkEdges [[1], [2], [2, 3], [4], []]
  unw := mkEdges []
  R := 1
  A := 3
  stmt := mkStmt [.nop, .nop, .readX, .nop, .writeThrough]
  hRA := by decide

/-- A `continue` back to `R` from inside the argument, with `A` still reachable from the region:
`loop { v.push(if c { continue } else { v.len() }) }` as `0 → R=1 → 2: readX → {R=1, A=3}`,
`3 → 4: writeThrough`. -/
def pContinue : Prog 5 where
  entry := 0
  succ := mkEdges [[1], [2], [1, 3], [4], []]
  unw := mkEdges []
  R := 1
  A := 3
  stmt := mkStmt [.nop, .nop, .readX, .nop, .writeThrough]
  hRA := by decide

/-- The loan ends before an activation that therefore finds no reservation:
`0 → R=1 → 2: endLoan → A=3 → 4: readX`. -/
def pEndBeforeA : Prog 5 where
  entry := 0
  succ := mkEdges [[1], [2], [3], [4], []]
  unw := mkEdges []
  R := 1
  A := 3
  stmt := mkStmt [.nop, .nop, .endLoan, .nop, .readX]
  hRA := by decide

/-- An unreachable reservation and activation flowing into reachable code:
`0 → 3: readX → 4: writeThrough`; `R=1 → A=2 → 3` (unreachable from `0`). -/
def pUnreachMerge : Prog 5 where
  entry := 0
  succ := mkEdges [[3], [2], [3], [4], []]
  unw := mkEdges []
  R := 1
  A := 2
  stmt := mkStmt [.nop, .nop, .nop, .readX, .writeThrough]
  hRA := by decide

/-- `A` unreachable from the entry: `0 → R=1 → 2`; `A=3 → 4: readX`. -/
def pUnreachA : Prog 5 where
  entry := 0
  succ := mkEdges [[1], [2], [], [4], []]
  unw := mkEdges []
  R := 1
  A := 3
  stmt := mkStmt [.nop, .nop, .nop, .nop, .readX]
  hRA := by decide

end Toy.TwoPhase
