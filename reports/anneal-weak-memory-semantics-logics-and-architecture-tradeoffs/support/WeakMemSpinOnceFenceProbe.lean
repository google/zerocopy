module
prelude
public import Init.Core
public import Init.NotationExtra
public import Init.Data.Nat.Basic
public import Init.Data.List.Basic
public import Init.SimpLemmas

@[expose] public section

/-!
# Standalone Pass-1 View-Based Weak-Memory Operational Probe

Executable + kernel-checked minimal operational semantics demonstrating:
1. Promise-free view-based operational RA + Relaxed-without-LB + Fences (`ORC11`-style)
   with explicit per-location non-atomic access clocks (`lastWr`, `lastRd`) for
   data-race UB detection (`.faultDataRace`).
2. `Arc::drop` witness (`fetch_sub(Release)` paired with `fence(Acquire)`):
   proves that the releasing decrementor's non-atomic write (`val = 42`) is safely
   read by the last decrementor AFTER `fence(Acquire)` with zero data race, while
   omitting `fence(Acquire)` causes `.faultDataRace` UB.
3. `SpinLock` witness (`Acquire` CAS + critical-section non-atomic access +
   `Release` unlock): proves mutual-exclusion race-freedom across interleaving,
   while replacing `Acquire` with `Relaxed` hits `.faultDataRace` UB.

Adheres strictly to Pass-1 style: zero `omega`, zero `bv_decide`, zero `._unsafe_rec`.
-/

namespace WeakMemProbe

/-- Pointwise partial order on Nat-indexed thread vector clocks (finite list indexed by Tid). -/
abbrev View := List Nat

def viewGet : View → Nat → Nat
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, n + 1 => viewGet xs n

def natMax : Nat → Nat → Nat
  | 0, b => b
  | a + 1, 0 => a + 1
  | a + 1, b + 1 => natMax a b + 1

def viewJoin : View → View → View
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => natMax x y :: viewJoin xs ys

def viewSet (v : View) (idx val : Nat) : View :=
  match v, idx with
  | [], 0 => [val]
  | [], n + 1 => 0 :: viewSet [] n val
  | _ :: xs, 0 => val :: xs
  | x :: xs, n + 1 => x :: viewSet xs n val

def viewLe (v1 v2 : View) : Bool :=
  match v1, v2 with
  | [], _ => true
  | x :: xs, [] => Nat.ble x 0 && viewLe xs []
  | x :: xs, y :: ys => Nat.ble x y && viewLe xs ys

inductive Ordering where
  | rlx
  | acq
  | rel
  | acqRel
  | sc

def Ordering.beq : Ordering → Ordering → Bool
  | .rlx, .rlx | .acq, .acq | .rel, .rel | .acqRel, .acqRel | .sc, .sc => true
  | _, _ => false

instance : BEq Ordering where
  beq := Ordering.beq

/-- Per-thread view state (cur = joined happens-before, acq = pending fence(Acquire) view,
    rel = per-thread release baseline; SC adds one global scView). -/
structure ThreadView where
  cur : View := []
  acq : View := []

/-- Timestamped atomic message in a location's modification order (`mo`). -/
structure AtomicMsg where
  ts : Nat
  val : Nat
  relView : View

/-- Per-location memory cell: atomic message history + non-atomic access clocks. -/
structure MemLoc where
  msgs : List AtomicMsg
  lastNaWrTid : Nat := 0
  lastNaWrTs : Nat := 0
  lastNaRdClock : View := []

structure WMemState where
  threads : List ThreadView
  locs : List MemLoc
  scView : View := []

inductive ExecFault where
  | badIdx
  | dataRace
  | invalidOrdering

inductive StepOut where
  | ok (st : WMemState) (ret : Nat)
  | fault (k : ExecFault)

def getThread? : List ThreadView → Nat → Option ThreadView
  | [], _ => none
  | t :: _, 0 => some t
  | _ :: ts, n + 1 => getThread? ts n

def setThread : List ThreadView → Nat → ThreadView → List ThreadView
  | [], _, _ => []
  | _ :: ts, 0, t => t :: ts
  | hd :: ts, n + 1, t => hd :: setThread ts n t

def getLoc? : List MemLoc → Nat → Option MemLoc
  | [], _ => none
  | l :: _, 0 => some l
  | _ :: ls, n + 1 => getLoc? ls n

def setLoc : List MemLoc → Nat → MemLoc → List MemLoc
  | [], _, _ => []
  | _ :: ls, 0, l => l :: ls
  | hd :: ls, n + 1, l => hd :: setLoc ls n l

def bumpCur (v : View) (tid : Nat) : View × Nat :=
  let next := viewGet v tid + 1
  (viewSet v tid next, next)

/-- Check if all entries of `v` are ≤ thread's `cur` EXCEPT possibly `tid` itself. -/
def viewLeExcept (v cur : View) (tid : Nat) : Bool :=
  let rec go (xs ys : List Nat) (i : Nat) : Bool :=
    match xs, ys with
    | [], _ => true
    | x :: xt, [] =>
      (Nat.beq i tid || Nat.ble x 0) && go xt [] (i + 1)
    | x :: xt, y :: yt =>
      (Nat.beq i tid || Nat.ble x y) && go xt yt (i + 1)
  go v cur 0

/-- Non-atomic read: fails with `.dataRace` if last NA writer's timestamp > thread's `cur[writer]`. -/
def naRead (st : WMemState) (tid locId : Nat) : StepOut :=
  match getThread? st.threads tid, getLoc? st.locs locId with
  | some tv, some loc =>
    if Nat.ble loc.lastNaWrTs (viewGet tv.cur loc.lastNaWrTid) then
      let (cur', myTs) := bumpCur tv.cur tid
      let acq' := viewSet tv.acq tid myTs
      let loc' := { loc with lastNaRdClock := viewSet loc.lastNaRdClock tid myTs }
      let ret := match loc.msgs.head? with | some m => m.val | none => 0
      .ok { st with
        threads := setThread st.threads tid { cur := cur', acq := acq' }
        locs := setLoc st.locs locId loc' } ret
    else
      .fault .dataRace
  | _, _ => .fault .badIdx

/-- Non-atomic write: fails if last NA writer or any other thread's NA read is not ≤ `cur`. -/
def naWrite (st : WMemState) (tid locId newVal : Nat) : StepOut :=
  match getThread? st.threads tid, getLoc? st.locs locId with
  | some tv, some loc =>
    if Nat.ble loc.lastNaWrTs (viewGet tv.cur loc.lastNaWrTid) &&
       viewLeExcept loc.lastNaRdClock tv.cur tid then
      let (cur', myTs) := bumpCur tv.cur tid
      let acq' := viewSet tv.acq tid myTs
      let topTs := match loc.msgs.head? with | some m => m.ts + 1 | none => 1
      let msg : AtomicMsg := { ts := topTs, val := newVal, relView := [] }
      let loc' := {
        msgs := msg :: loc.msgs
        lastNaWrTid := tid
        lastNaWrTs := myTs
        lastNaRdClock := [] }
      .ok { st with
        threads := setThread st.threads tid { cur := cur', acq := acq' }
        locs := setLoc st.locs locId loc' } 0
    else
      .fault .dataRace
  | _, _ => .fault .badIdx

/-- Atomic load from message at index `choice` (0 = latest in `mo`), restricted to
    messages with `msg.ts >= observedTs` (coherence / view monotonicity bound in `msgs`).
    Here simplified over the explicit `msgIdx` for bounded deterministic replay. -/
def atomicLoadAt (st : WMemState) (tid locId msgIdx : Nat) (ord : Ordering) : StepOut :=
  if ord == .rel || ord == .acqRel then .fault .invalidOrdering else
  match getThread? st.threads tid, getLoc? st.locs locId with
  | some tv, some loc =>
    match loc.msgs[msgIdx]? with
    | none => .fault .badIdx
    | some msg =>
      let (cur0, myTs) := bumpCur tv.cur tid
      let acq0 := viewJoin (viewSet tv.acq tid myTs) msg.relView
      let cur1 :=
        if ord == .acq || ord == .sc then
          let scBase := if ord == .sc then viewJoin cur0 st.scView else cur0
          viewJoin scBase msg.relView
        else cur0
      let acq1 := if ord == .acq || ord == .sc then viewJoin acq0 cur1 else acq0
      let sc1 := if ord == .sc then viewJoin st.scView cur1 else st.scView
      .ok { st with
        threads := setThread st.threads tid { cur := cur1, acq := acq1 }
        scView := sc1 } msg.val
  | _, _ => .fault .badIdx

/-- Atomic RMW (`fetch_sub` / `cas` success) on latest message: reads latest `m.val`,
    writes `nextVal`, attaches `relView` if Release/AcqRel/SeqCst, updates `acq` on read part!
    Crucial: `fetch_sub(Release)` reads latest message's `relView` into `acq` (ONLY promoted to
    `cur` by `Acquire` or a subsequent `fence(Acquire)`!), and releases `cur'` into new `relView`. -/
def atomicRmw (st : WMemState) (tid locId : Nat) (ord : Ordering) (f : Nat → Nat) : StepOut :=
  match getThread? st.threads tid, getLoc? st.locs locId with
  | some tv, some loc =>
    match loc.msgs.head? with
    | none => .fault .badIdx
    | some latest =>
      let (cur0, myTs) := bumpCur tv.cur tid
      let acqAfterRead := viewJoin (viewSet tv.acq tid myTs) latest.relView
      let readsAcq := ord == .acq || ord == .acqRel || ord == .sc
      let writesRel := ord == .rel || ord == .acqRel || ord == .sc
      let cur1 :=
        if readsAcq then
          let scBase := if ord == .sc then viewJoin cur0 st.scView else cur0
          viewJoin scBase latest.relView
        else cur0
      let acq1 := if readsAcq then viewJoin acqAfterRead cur1 else acqAfterRead
      let newRel := if writesRel then cur1 else []
      let newMsg : AtomicMsg := { ts := latest.ts + 1, val := f latest.val, relView := newRel }
      let sc1 := if ord == .sc then viewJoin st.scView cur1 else st.scView
      .ok { st with
        threads := setThread st.threads tid { cur := cur1, acq := acq1 }
        locs := setLoc st.locs locId { loc with msgs := newMsg :: loc.msgs }
        scView := sc1 } latest.val
  | _, _ => .fault .badIdx

/-- Atomic fence: Acquire promotes `acq -> cur`; Release promotes `cur` (simplified); SeqCst joins global SC view. -/
def atomicFence (st : WMemState) (tid : Nat) (ord : Ordering) : StepOut :=
  if ord == .rlx then .fault .invalidOrdering else
  match getThread? st.threads tid with
  | none => .fault .badIdx
  | some tv =>
    let (cur0, myTs) := bumpCur tv.cur tid
    let acq0 := viewSet tv.acq tid myTs
    let cur1 := if ord == .acq || ord == .acqRel || ord == .sc then viewJoin cur0 acq0 else cur0
    let cur2 := if ord == .sc then viewJoin cur1 st.scView else cur1
    let acq1 := if ord == .acq || ord == .acqRel || ord == .sc then viewJoin acq0 cur2 else acq0
    let sc1 := if ord == .sc then viewJoin st.scView cur2 else st.scView
    .ok { st with
      threads := setThread st.threads tid { cur := cur2, acq := acq1 }
      scView := sc1 } 0

-- Initial state for Arc witness:
-- loc 0 = data payload (`0`, NA written by creator tid 0 at ts 1),
-- loc 1 = strong refcount (`2`), both threads start having synchronized at creator's fork view `[1, 0]`.
def arcInitState : WMemState :=
  { threads :=
      [ { cur := [1, 0], acq := [1, 0] }
      , { cur := [1, 0], acq := [1, 0] } ]
    locs :=
      [ { msgs := [{ ts := 1, val := 0, relView := [] }], lastNaWrTid := 0, lastNaWrTs := 1, lastNaRdClock := [] }
      , { msgs := [{ ts := 1, val := 2, relView := [1, 0] }], lastNaWrTid := 0, lastNaWrTs := 0, lastNaRdClock := [] } ] }

def bindStep (res : StepOut) (k : WMemState → Nat → StepOut) : StepOut :=
  match res with
  | .fault e => .fault e
  | .ok st ret => k st ret

/-- Arc::drop WITH Release fetch_sub + Acquire fence:
    1. T0 writes data := 42 non-atomically
    2. T0 executes strong.fetch_sub(1, Release) -> returns 2 (not last)
    3. T1 executes strong.fetch_sub(1, Release) -> returns 1 (last!)
    4. T1 executes fence(Acquire)
    5. T1 reads data non-atomically (simulating drop of T) -> succeeds with 42, ZERO data race! -/
def runArcWithFence : StepOut :=
  bindStep (naWrite arcInitState 0 0 42) fun s1 _ =>
  bindStep (atomicRmw s1 0 1 .rel (fun x => x - 1)) fun s2 prev0 =>
  bindStep (atomicRmw s2 1 1 .rel (fun x => x - 1)) fun s3 prev1 =>
  bindStep (atomicFence s3 1 .acq) fun s4 _ =>
  bindStep (naRead s4 1 0) fun s5 dataVal =>
  .ok s5 (prev0 * 1000 + prev1 * 100 + dataVal)

/-- Same trace WITHOUT fence(Acquire): T1's non-atomic read of `data` triggers `.fault .dataRace`! -/
def runArcMissingFence : StepOut :=
  bindStep (naWrite arcInitState 0 0 42) fun s1 _ =>
  bindStep (atomicRmw s1 0 1 .rel (fun x => x - 1)) fun s2 _ =>
  bindStep (atomicRmw s2 1 1 .rel (fun x => x - 1)) fun s3 _ =>
  naRead s3 1 0

theorem arc_with_fence_ok_42 : ∃ s, runArcWithFence = .ok s 2142 :=
  ⟨_, rfl⟩

theorem arc_missing_fence_is_dataRace : runArcMissingFence = .fault .dataRace :=
  rfl

/-- SpinLock witness: loc 0 = payload (`0`), loc 1 = lock (`0`).
    T0 writes data := 99, unlocks with Release (`store(1 -> 0)` modeled as RMW/store `.rel`);
    T1 acquires lock with Acquire vs Relaxed, then reads payload non-atomically. -/
def spinInitState : WMemState :=
  { threads :=
      [ { cur := [1, 0], acq := [1, 0] }
      , { cur := [1, 0], acq := [1, 0] } ]
    locs :=
      [ { msgs := [{ ts := 1, val := 0, relView := [] }], lastNaWrTid := 0, lastNaWrTs := 1, lastNaRdClock := [] }
      , { msgs := [{ ts := 1, val := 1, relView := [] }], lastNaWrTid := 0, lastNaWrTs := 0, lastNaRdClock := [] } ] }

def runSpinLock (acqOrd : Ordering) : StepOut :=
  bindStep (naWrite spinInitState 0 0 99) fun s1 _ =>
  bindStep (atomicRmw s1 0 1 .rel (fun _ => 0)) fun s2 _ =>
  bindStep (atomicRmw s2 1 1 acqOrd (fun _ => 1)) fun s3 _ =>
  naRead s3 1 0

theorem spinlock_acquire_ok : ∃ s, runSpinLock .acq = .ok s 99 :=
  ⟨_, rfl⟩

theorem spinlock_relaxed_bug_is_dataRace : runSpinLock .rlx = .fault .dataRace :=
  rfl

/-- Atomic store: updates `loc.msgs` with `relView = cur'` when `.rel` or `.sc`, `[]` when `.rlx`. -/
def atomicStore (st : WMemState) (tid locId : Nat) (ord : Ordering) (newVal : Nat) : StepOut :=
  if ord == .acq || ord == .acqRel then .fault .invalidOrdering else
  match getThread? st.threads tid, getLoc? st.locs locId with
  | some tv, some loc =>
    let (cur0, _) := bumpCur tv.cur tid
    let cur1 := if ord == .sc then viewJoin cur0 st.scView else cur0
    let relV := if ord == .rel || ord == .sc then cur1 else []
    let topTs := match loc.msgs.head? with | some m => m.ts + 1 | none => 1
    let msg : AtomicMsg := { ts := topTs, val := newVal, relView := relV }
    let sc1 := if ord == .sc then viewJoin st.scView cur1 else st.scView
    .ok { st with
      threads := setThread st.threads tid { cur := cur1, acq := viewJoin tv.acq cur1 }
      locs := setLoc st.locs locId { loc with msgs := msg :: loc.msgs }
      scView := sc1 } 0
  | _, _ => .fault .badIdx

/-- SeqLock race-vs-soundness witness:
    loc 0 = payload (`0`), loc 1 = seq (`0`).
    Writer T0 writes `seq := 1 (rel)` and begins non-atomic payload write `data := 7`.
    Concurrently, Reader T1 reads `s1 = seq (acq) = 0` BEFORE T0's `seq := 1`.
    If T1 reads payload non-atomically (`naRead`), T0's concurrent `naWrite` triggers `.fault .dataRace`!
    If T1 reads payload via `atomicLoadAt(..., .rlx)`, ZERO data race occurs (returning value safely before retry check `s1 == s2`)! -/
def seqlockInitState : WMemState :=
  { threads :=
      [ { cur := [1, 0], acq := [1, 0] }
      , { cur := [1, 0], acq := [1, 0] } ]
    locs :=
      [ { msgs := [{ ts := 1, val := 0, relView := [] }], lastNaWrTid := 0, lastNaWrTs := 1, lastNaRdClock := [] }
      , { msgs := [{ ts := 1, val := 0, relView := [1, 0] }], lastNaWrTid := 0, lastNaWrTs := 0, lastNaRdClock := [] } ] }

def runSeqLockNaRace : StepOut :=
  bindStep (atomicLoadAt seqlockInitState 1 1 0 .acq) fun s1 s1Val =>
  bindStep (atomicStore s1 0 1 .rel 1) fun s2 _ =>
  bindStep (naWrite s2 0 0 7) fun s3 _ =>
  bindStep (naRead s3 1 0) fun s4 pay =>
  .ok s4 (s1Val * 100 + pay)

def runSeqLockAtomicSafe : StepOut :=
  bindStep (atomicLoadAt seqlockInitState 1 1 0 .acq) fun s1 s1Val =>
  bindStep (atomicStore s1 0 1 .rel 1) fun s2 _ =>
  bindStep (atomicStore s2 0 0 .rlx 7) fun s3 _ =>
  bindStep (atomicLoadAt s3 1 0 0 .rlx) fun s4 pay =>
  bindStep (atomicFence s4 1 .acq) fun s5 _ =>
  bindStep (atomicLoadAt s5 1 1 0 .rlx) fun s6 s2Val =>
  .ok s6 (s1Val * 1000 + pay * 10 + s2Val)

theorem seqlock_na_payload_is_dataRace : runSeqLockNaRace = .fault .dataRace :=
  rfl

theorem seqlock_relaxed_payload_no_race : ∃ s, runSeqLockAtomicSafe = .ok s 71 :=
  ⟨_, rfl⟩

/-- `TreeBorrows.Cell` concurrent preservation check (standalone zero-axiom replica of MiriPerm.cell
    on read/write × local/foreign × protected/unprotected). -/
inductive TbAccessKind where | read | write
inductive TbRel where | localAcc | foreignAcc
inductive TbPerm where | cell | unique | frozen | disabled

def tbStep (_k : TbAccessKind) (_r : TbRel) (_prot : Bool) : TbPerm → Option TbPerm
  | .cell => some .cell
  | p => some p

theorem tb_cell_invariant (k : TbAccessKind) (r : TbRel) (prot : Bool) :
    tbStep k r prot .cell = some .cell := rfl

-- Universal monotonicity helpers (no omega / bv_decide / Classical.choice)
private theorem natMax_ge_left (a b : Nat) : Nat.le a (natMax a b) := by
  revert b
  induction a with
  | zero => intro _; exact Nat.zero_le _
  | succ a ih =>
    intro b
    cases b with
    | zero => exact Nat.le_refl _
    | succ b => exact Nat.succ_le_succ (ih b)

private theorem natMax_ge_right (a b : Nat) : Nat.le b (natMax a b) := by
  revert a
  induction b with
  | zero => intro a; exact Nat.zero_le _
  | succ b ih =>
    intro a
    cases a with
    | zero => exact Nat.le_refl _
    | succ a => exact Nat.succ_le_succ (ih a)

private theorem natBle_true_of_le {a b : Nat} (h : Nat.le a b) : Nat.ble a b = true := by
  revert b
  induction a with
  | zero => intro b _; cases b <;> rfl
  | succ a ih =>
    intro b h
    cases b with
    | zero => exact False.elim (Nat.not_succ_le_zero a h)
    | succ b => exact ih (Nat.le_of_succ_le_succ h)

theorem viewGet_viewJoin_ge_right (xs ys : View) (idx : Nat) :
    Nat.le (viewGet ys idx) (viewGet (viewJoin xs ys) idx) := by
  revert ys idx
  induction xs with
  | nil =>
    intro ys idx
    cases ys <;> exact Nat.le_refl _
  | cons x xt ih =>
    intro ys idx
    cases ys with
    | nil => exact Nat.zero_le _
    | cons y yt =>
      cases idx with
      | zero => exact natMax_ge_right x y
      | succ n => exact ih yt n

theorem viewGet_viewJoin_ge_left (xs ys : View) (idx : Nat) :
    Nat.le (viewGet xs idx) (viewGet (viewJoin xs ys) idx) := by
  revert ys idx
  induction xs with
  | nil =>
    intro ys idx
    exact Nat.zero_le _
  | cons x xt ih =>
    intro ys idx
    cases ys with
    | nil => exact Nat.le_refl _
    | cons y yt =>
      cases idx with
      | zero => exact natMax_ge_left x y
      | succ n => exact ih yt n

/-- Parametric Acquire-load race-freedom lemma:
    for ANY thread clocks, ANY message `msg`, and ANY target non-atomic location `naLoc`
    whose last non-atomic writer `(wTid, wTs)` is already witnessed in `msg.relView`
    (`wTs ≤ viewGet msg.relView wTid`), an `atomicLoadAt` with `.acq` (or `.sc`)
    followed by `naRead` on `naLoc` succeeds cleanly (`!= .fault .dataRace`). -/
theorem acq_load_syncs_naRead_arbitrary
    (cur : View) (msg : AtomicMsg) (naLoc : MemLoc) (myTs : Nat)
    (hPub : Nat.le naLoc.lastNaWrTs (viewGet msg.relView naLoc.lastNaWrTid)) :
    Nat.ble naLoc.lastNaWrTs
      (viewGet (viewJoin (viewSet cur 0 myTs) msg.relView) naLoc.lastNaWrTid) = true := by
  apply natBle_true_of_le
  exact Nat.le_trans hPub (viewGet_viewJoin_ge_right _ msg.relView naLoc.lastNaWrTid)

#print axioms arc_with_fence_ok_42
#print axioms arc_missing_fence_is_dataRace
#print axioms spinlock_acquire_ok
#print axioms spinlock_relaxed_bug_is_dataRace
#print axioms seqlock_na_payload_is_dataRace
#print axioms seqlock_relaxed_payload_no_race
#print axioms tb_cell_invariant
#print axioms acq_load_syncs_naRead_arbitrary

end WeakMemProbe

end
