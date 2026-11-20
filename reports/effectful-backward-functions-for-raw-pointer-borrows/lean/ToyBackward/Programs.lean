import ToyBackward.Liveness

/-!
# Named programs, heaps, and placements used by examples and counterexamples
-/

namespace Toy.Backward

/-- Two `as_mut` calls on the same pointer `p` (address `0`), with a write through the first
reference between them:
``
let r0 = unsafe { &mut *p };   // 0
let x0 = *r0;                  // 1
*r0 = c;                       // 2
let r3 = unsafe { &mut *p };   // 3
let x1 = *r3;                  // 4
``
It obeys the aliasing discipline: `r0` is last used at 2, before the next access to `*p` at 3. -/
def reborrowAfterWrite (c : Int) : Prog :=
  [.asMut 0, .read 0 0, .write 0 (.lit c), .asMut 0, .read 1 3]

/-- A raw write while the reference is still in use (violates the aliasing discipline):
`let r0 = &mut *p; *p = 7; let x0 = *r0;`. -/
def rawWriteDuringBorrow : Prog := [.asMut 0, .rawWrite 0 (.lit 7), .read 0 0]

/-- One reference, written then read: `let r0 = &mut *p; *r0 = c; let x0 = *r0;`. -/
def writeThenRead (c : Int) : Prog := [.asMut 0, .write 0 (.lit c), .read 0 0]

/-- Write through a reference, raw write, then read through the reference again (violates the
aliasing discipline): `let r0 = &mut *p; *r0 = 5; *p = 7; let x0 = *r0;`. -/
def readAfterRawWrite : Prog := [.asMut 0, .write 0 (.lit 5), .rawWrite 0 (.lit 7), .read 0 0]

/-- A single write through a reference: `let r0 = &mut *p; *r0 = 5;`. -/
def writeOnce : Prog := [.asMut 0, .write 0 (.lit 5)]

/-- A write, an unrelated raw read of another cell, then a raw read of the borrowed cell:
`let r0 = &mut *p; *r0 = 5; let x1 = *q; let x2 = *p;` with `p = 0`, `q = 1`. Its liveness
window for region 0 contains two end points (before index 2 and before index 3). -/
def writeThenOtherThenRawRead : Prog :=
  [.asMut 0, .write 0 (.lit 5), .rawRead 1 1, .rawRead 2 0]

/-- A single reborrow that is never used: `let r0 = &mut *p;`. -/
def unusedRegion : Prog := [.asMut 0]

/-- The owner reads the cell while the reference is still to be written, and the written value
depends on what the owner read (violates the aliasing discipline):
`let r0 = &mut *p; let x0 = *p; *r0 = x0 + 1;`. -/
def ownerReadThenWriteBack : Prog := [.asMut 0, .rawRead 0 0, .write 0 (.add (.var 0) (.lit 1))]

/-- Uses a reference that was never created (a scoping error). -/
def danglingUse : Prog := [.read 0 0]

/-- Uses the reference created at index 1 before index 1 (a scoping error):
`let x0 = *r1; let r1 = &mut *p;`. -/
def useBeforeCreation : Prog := [.read 0 1, .asMut 0]

/-- `reborrowAfterWrite c` obeys the aliasing discipline, for every `c`. -/
theorem aliasingDiscipline_reborrowAfterWrite (c : Int) :
    AliasingDiscipline (reborrowAfterWrite c) :=
  of_decide_eq_true (by rfl)

/-- The all-zero heap. -/
def zeroHeap : Heap := fun _ => 0

/-- Constant placement: every region ends immediately before statement `k`. -/
def endAt (k : Nat) : Placement := fun _ => k

/-- For `reborrowAfterWrite`: region 0 ends before the write at index 2 (too early); region 3 at
the end of the program. -/
def endBeforeWrite : Placement := fun i => if i = 0 then 2 else 5

/-- For `reborrowAfterWrite`: region 0 ends after the second `asMut` at index 3 (too late);
region 3 at the end of the program. -/
def endAfterReborrow : Placement := fun i => if i = 0 then 4 else 5

end Toy.Backward
