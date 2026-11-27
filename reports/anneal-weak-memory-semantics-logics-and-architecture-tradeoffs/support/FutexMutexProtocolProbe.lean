module
prelude
public import Init.Core
public import Init.NotationExtra
public import Init.Data.Nat.Basic
public import Init.Data.List.Basic
public import Init.SimpLemmas

@[expose] public section

/-!
# Pass-1 Lean 4 Probe for `std::sys::sync::mutex::futex::Mutex` Protocol & Parametric `VProp`

Self-contained kernel-checked Pass-1 probe (`Init.*` only; zero `omega`, zero
`bv_decide`, zero `by_cases`, zero `._unsafe_rec`, zero `sorry`) modeling:

1. **Concrete 3-state `futex::Mutex` operational protocol** (`UNLOCKED = 0`,
   `LOCKED = 1`, `CONTENDED = 2`) with explicit `futex_wait` / `futex_wake` queues,
   deterministic split between matched wake-clock transfer (`spurious = false`) and
   spurious wakeup (`spurious = true` with zero Acquire transfer):
   - Spurious wakeup + `swap(2, Acquire)` followed by non-atomic critical-section
     read/write succeeds race-free (`!= .fault .dataRace`).
   - Replacing `swap(2, Acquire)` with `swap(2, Relaxed)` under spurious wakeup
     triggers `.fault .dataRace`.
   - 3-thread lost-wakeup witness: replacing `swap(2, Acquire)` in `lock_contended`
     with `cxchg(0, 1, Acquire, Relaxed)` causes `T1` to clobber `CONTENDED` back to
     `LOCKED` after `T0` unlocks once, leaving `T1` to skip `futex_wake` on unlock and
     leaving `T2` permanently parked (`isParked = true`).
2. **Parametric `Type 0` view-indexed invariant (`MutexInv`)**:
   - Upward-closed predicate `VProp := View → Prop` (`Type 0`) capturing exclusive
     ownership of a protected non-atomic location (`NaOwnedAtView`).
   - Universal theorems (for arbitrary thread IDs, histories, views, disjoint
     locations, and arbitrary `P : Nat → Prop`) showing `naWrite` + `unlock(.rel)`
     publishes `MutexInv` onto `lockLoc`'s new release message, and `lock(.acq)`
     (or matched `futex_wake` + `futex_wait(spurious := false)`) transfers `MutexInv`
     to any acquiring thread, ensuring race-free `naRead`, `P ret`, and preservation
     of `NaOwnedAtView` for subsequent critical-section updates.
-/

namespace FutexMutexProbe

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

structure ThreadView where
  cur : View := []
  acq : View := []

structure AtomicMsg where
  ts : Nat
  val : Nat
  relView : View

structure MemLoc where
  msgs : List AtomicMsg
  lastNaWrTid : Nat := 0
  lastNaWrTs : Nat := 0
  lastNaRdClock : View := []

/-- Futex wait-queue entry `(locId, tid)`. -/
abbrev FutexEntry := Nat × Nat

structure WMemState where
  threads : List ThreadView
  locs : List MemLoc
  scView : View := []
  futexParked : List FutexEntry := []
  futexWoken : List FutexEntry := []
  futexWakeClock : View := []

inductive ExecFault where
  | badIdx
  | dataRace
  | invalidOrdering
  | protocolErr

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

def viewLeExceptAux (xs ys : List Nat) (i tid : Nat) : Bool :=
  match xs, ys with
  | [], _ => true
  | x :: xt, [] =>
    (Nat.beq i tid || Nat.ble x 0) && viewLeExceptAux xt [] (i + 1) tid
  | x :: xt, y :: yt =>
    (Nat.beq i tid || Nat.ble x y) && viewLeExceptAux xt yt (i + 1) tid

def viewLeExcept (v cur : View) (tid : Nat) : Bool :=
  viewLeExceptAux v cur 0 tid

def locHeadVal (loc : MemLoc) : Nat :=
  match loc.msgs.head? with
  | some m => m.val
  | none => 0

def naRead (st : WMemState) (tid locId : Nat) : StepOut :=
  match getThread? st.threads tid, getLoc? st.locs locId with
  | some tv, some loc =>
    if Nat.ble loc.lastNaWrTs (viewGet tv.cur loc.lastNaWrTid) then
      let (cur', myTs) := bumpCur tv.cur tid
      let acq' := viewSet tv.acq tid myTs
      let loc' := { loc with lastNaRdClock := viewSet loc.lastNaRdClock tid myTs }
      .ok { st with
        threads := setThread st.threads tid { cur := cur', acq := acq' }
        locs := setLoc st.locs locId loc' } (locHeadVal loc)
    else
      .fault .dataRace
  | _, _ => .fault .badIdx

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

def atomicLoadLatest (st : WMemState) (tid locId : Nat) (ord : Ordering) : StepOut :=
  if ord == .rel || ord == .acqRel then .fault .invalidOrdering else
  match getThread? st.threads tid, getLoc? st.locs locId with
  | some tv, some loc =>
    match loc.msgs.head? with
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

/-- Atomic `compare_exchange` returning `(StepOut, succeeded)` (`1` on `Ok`, `0` on `Err`). -/
def atomicCas (st : WMemState) (tid locId expected desired : Nat)
    (succOrd failOrd : Ordering) : StepOut × Bool :=
  if failOrd == .rel || failOrd == .acqRel then (.fault .invalidOrdering, false) else
  match getThread? st.threads tid, getLoc? st.locs locId with
  | some _tv, some loc =>
    match loc.msgs.head? with
    | none => (.fault .badIdx, false)
    | some latest =>
      if Nat.beq latest.val expected then
        (atomicRmw st tid locId succOrd (fun _ => desired), true)
      else
        (atomicLoadLatest st tid locId failOrd, false)
  | _, _ => (.fault .badIdx, false)

-- Futex queue helpers
def entryEq (locId tid : Nat) (e : FutexEntry) : Bool :=
  Nat.beq e.1 locId && Nat.beq e.2 tid

def hasEntry (es : List FutexEntry) (locId tid : Nat) : Bool :=
  match es with
  | [] => false
  | e :: rest => if entryEq locId tid e then true else hasEntry rest locId tid

def removeOneEntry (es : List FutexEntry) (locId tid : Nat) : Option (List FutexEntry) :=
  match es with
  | [] => none
  | e :: rest =>
    if entryEq locId tid e then some rest
    else
      match removeOneEntry rest locId tid with
      | none => none
      | some rest' => some (e :: rest')

def popFirstForLoc (es : List FutexEntry) (locId : Nat) : Option (Nat × List FutexEntry) :=
  match es with
  | [] => none
  | e :: rest =>
    if Nat.beq e.1 locId then some (e.2, rest)
    else
      match popFirstForLoc rest locId with
      | none => none
      | some (wTid, rest') => some (wTid, e :: rest')

/-- Park waiter `tid` if current futex word equals `expected` (`Relaxed` load, no Acquire).
    Returns `0` if parked, `1` if value differed (`EAGAIN`). -/
def futexWaitPark (st : WMemState) (tid locId expected : Nat) : StepOut :=
  match getThread? st.threads tid, getLoc? st.locs locId with
  | some tv, some loc =>
    match loc.msgs.head? with
    | none => .fault .badIdx
    | some latest =>
      let (cur0, myTs) := bumpCur tv.cur tid
      let acq0 := viewSet tv.acq tid myTs
      let st1 := { st with threads := setThread st.threads tid { cur := cur0, acq := acq0 } }
      if Nat.beq latest.val expected then
        .ok { st1 with futexParked := st1.futexParked ++ [(locId, tid)] } 0
      else
        .ok st1 1
  | _, _ => .fault .badIdx

/-- Wake at most 1 waiter parked on `locId`, releasing `cur'` onto `futexWakeClock`. -/
def futexWakeOne (st : WMemState) (tid locId : Nat) : StepOut :=
  match getThread? st.threads tid with
  | none => .fault .badIdx
  | some tv =>
    let (cur0, myTs) := bumpCur tv.cur tid
    let wakeClk' := viewJoin st.futexWakeClock cur0
    let st1 := { st with
      threads := setThread st.threads tid { cur := cur0, acq := viewSet tv.acq tid myTs }
      futexWakeClock := wakeClk' }
    match popFirstForLoc st1.futexParked locId with
    | none => .ok st1 0
    | some (wTid, restParked) =>
      .ok { st1 with
        futexParked := restParked
        futexWoken := st1.futexWoken ++ [(locId, wTid)] } 1

/-- Resume `futex_wait`:
    - When `spurious = false`: consumes a matched entry from `futexWoken` and transfers
      `st.futexWakeClock` (`Release -> Acquire` handoff).
    - When `spurious = true`: removes `tid` directly from `futexParked` with **ZERO**
      Acquire view transfer (`futexWakeClock` NOT joined into `tv.cur` or `tv.acq`). -/
def futexResume (st : WMemState) (tid locId : Nat) (spurious : Bool) : StepOut :=
  match getThread? st.threads tid with
  | none => .fault .badIdx
  | some tv =>
    let (cur0, myTs) := bumpCur tv.cur tid
    let acq0 := viewSet tv.acq tid myTs
    if spurious then
      match removeOneEntry st.futexParked locId tid with
      | none => .fault .protocolErr
      | some restParked =>
        .ok { st with
          threads := setThread st.threads tid { cur := cur0, acq := acq0 }
          futexParked := restParked } 0
    else
      match removeOneEntry st.futexWoken locId tid with
      | none => .fault .protocolErr
      | some restWoken =>
        let cur1 := viewJoin cur0 st.futexWakeClock
        let acq1 := viewJoin acq0 st.futexWakeClock
        .ok { st with
          threads := setThread st.threads tid { cur := cur1, acq := acq1 }
          futexWoken := restWoken } 0

def bindStep (res : StepOut) (k : WMemState → Nat → StepOut) : StepOut :=
  match res with
  | .fault e => .fault e
  | .ok st ret => k st ret

/-!
## Part 1 (`3a`): `std::sys::sync::mutex::futex::Mutex` Concrete Witnesses
`UNLOCKED = 0`, `LOCKED = 1`, `CONTENDED = 2`.
Location `0` = non-atomic protected `data : u64`.
Location `1` = `futex : Atomic<u32>`.
-/

def UNLOCKED : Nat := 0
def LOCKED : Nat := 1
def CONTENDED : Nat := 2

/-- Initial 2-thread state where `T0` already holds the mutex (`LOCKED = 1`) and owns `data`. -/
def mutexInit2T : WMemState :=
  { threads :=
      [ { cur := [1, 0], acq := [1, 0] }
      , { cur := [1, 0], acq := [1, 0] } ]
    locs :=
      [ { msgs := [{ ts := 1, val := 0, relView := [] }], lastNaWrTid := 0, lastNaWrTs := 1, lastNaRdClock := [] }
      , { msgs := [{ ts := 1, val := LOCKED, relView := [1, 0] }], lastNaWrTid := 0, lastNaWrTs := 0, lastNaRdClock := [] } ] }

/-- 2-thread trace matching `futex.rs`:
    1. `T1` fast-path CAS `(0 -> 1)` fails (observed `LOCKED = 1`).
    2. `T1` enters `lock_contended`: `spin` sees `1`, executes `swap(CONTENDED = 2, lockSwapOrd)` -> `prev = 1`,
       calls `futex_wait(&state, 2)` -> parks `(1, 1)`.
    3. `T0` executes critical-section `naWrite(data := 77)`, then `unlock()`:
       `swap(UNLOCKED = 0, Release)` -> `prev = 2 == CONTENDED` -> `futex_wake`.
    4. `T1` wakes **spuriously** (`spurious = true`, ZERO `futexWakeClock` Acquire transfer!),
       retries loop: `spin` sees `0`, executes `swap(CONTENDED = 2, lockSwapOrd)` -> `prev = 0`,
       then reads `data` non-atomically (`naRead`). -/
def runFutex2TSpurious (lockSwapOrd : Ordering) : StepOut :=
  let (casRes, okFast) := atomicCas mutexInit2T 1 1 UNLOCKED LOCKED .acq .rlx
  if okFast then .fault .protocolErr else
  bindStep casRes fun s1 _ =>
  bindStep (atomicRmw s1 1 1 lockSwapOrd (fun _ => CONTENDED)) fun s2 _ =>
  bindStep (futexWaitPark s2 1 1 CONTENDED) fun s3 _ =>
  bindStep (naWrite s3 0 0 77) fun s4 _ =>
  bindStep (atomicRmw s4 0 1 .rel (fun _ => UNLOCKED)) fun s5 prevUnlock =>
  if !Nat.beq prevUnlock CONTENDED then .fault .protocolErr else
  -- T1 wakes SPURIOUSLY (spurious = true -> ZERO Acquire transfer from futex_wait!),
  -- then retries swap(2, lockSwapOrd) reading UNLOCKED=0 before entering critical section.
  bindStep (futexResume s5 1 1 true) fun s6 _ =>
  bindStep (atomicRmw s6 1 1 lockSwapOrd (fun _ => CONTENDED)) fun s7 prevSwap =>
  if !Nat.beq prevSwap UNLOCKED then .fault .protocolErr else
  bindStep (naRead s7 1 0) fun s8 dataVal =>
  -- T1 releases mutex and wakes if CONTENDED (unlock path).
  bindStep (atomicRmw s8 1 1 .rel (fun _ => UNLOCKED)) fun s9 _ =>
  .ok s9 dataVal

theorem futex_spurious_acq_race_free_77 : ∃ s, runFutex2TSpurious .acq = .ok s 77 :=
  ⟨_, rfl⟩

theorem futex_spurious_relaxed_is_dataRace : runFutex2TSpurious .rlx = .fault .dataRace :=
  rfl

/-- Matched non-spurious `futex_wake` + `futex_wait(spurious = false)` trace also succeeds race-free. -/
def runFutex2TMatchedWake : StepOut :=
  let (casRes, okFast) := atomicCas mutexInit2T 1 1 UNLOCKED LOCKED .acq .rlx
  if okFast then .fault .protocolErr else
  bindStep casRes fun s1 _ =>
  bindStep (atomicRmw s1 1 1 .acq (fun _ => CONTENDED)) fun s2 _ =>
  bindStep (futexWaitPark s2 1 1 CONTENDED) fun s3 _ =>
  bindStep (naWrite s3 0 0 88) fun s4 _ =>
  bindStep (atomicRmw s4 0 1 .rel (fun _ => UNLOCKED)) fun s5 _ =>
  bindStep (futexWakeOne s5 0 1) fun s6 _ =>
  bindStep (futexResume s6 1 1 false) fun s7 _ =>
  bindStep (atomicRmw s7 1 1 .acq (fun _ => CONTENDED)) fun s8 _ =>
  naRead s8 1 0

theorem futex_matched_wake_race_free_88 : ∃ s, runFutex2TMatchedWake = .ok s 88 :=
  ⟨_, rfl⟩

/-- Initial 3-thread state where `T0` holds mutex (`LOCKED = 1`). -/
def mutexInit3T : WMemState :=
  { threads :=
      [ { cur := [1, 0, 0], acq := [1, 0, 0] }
      , { cur := [1, 0, 0], acq := [1, 0, 0] }
      , { cur := [1, 0, 0], acq := [1, 0, 0] } ]
    locs :=
      [ { msgs := [{ ts := 1, val := 0, relView := [] }], lastNaWrTid := 0, lastNaWrTs := 1, lastNaRdClock := [] }
      , { msgs := [{ ts := 1, val := LOCKED, relView := [1, 0, 0] }], lastNaWrTid := 0, lastNaWrTs := 0, lastNaRdClock := [] } ] }

/-- Execute 3-thread contention trace parameterizing whether waking waiter `T1`
    uses real `swap(CONTENDED=2, Acq)` (`preserveContended = true`) vs buggy
    `compare_exchange(UNLOCKED=0, LOCKED=1, Acq, Rlx)` (`preserveContended = false`). -/
def runFutex3TWake (preserveContended : Bool) : StepOut :=
  -- 1. T1 hits contended path: swap(2, Acq) -> 1, sleeps on futex(2)
  bindStep (atomicRmw mutexInit3T 1 1 .acq (fun _ => CONTENDED)) fun s1 _ =>
  bindStep (futexWaitPark s1 1 1 CONTENDED) fun s2 _ =>
  -- 2. T2 hits contended path: spin sees 2, sleeps on futex(2)
  bindStep (atomicLoadLatest s2 2 1 .rlx) fun s3 s2Obs =>
  if !Nat.beq s2Obs CONTENDED then .fault .protocolErr else
  bindStep (futexWaitPark s3 2 1 CONTENDED) fun s4 _ =>
  -- 3. T0 unlocks: swap(0, Rel) observes CONTENDED=2 -> futex_wake(1) wakes T1 only!
  bindStep (atomicRmw s4 0 1 .rel (fun _ => UNLOCKED)) fun s5 prev0 =>
  if !Nat.beq prev0 CONTENDED then .fault .protocolErr else
  bindStep (futexWakeOne s5 0 1) fun s6 _ =>
  -- 4. T1 resumes, spins (sees 0), and re-acquires:
  bindStep (futexResume s6 1 1 false) fun s7 _ =>
  let acquireT1 : StepOut :=
    if preserveContended then
      atomicRmw s7 1 1 .acq (fun _ => CONTENDED)
    else
      (atomicCas s7 1 1 UNLOCKED LOCKED .acq .rlx).1
  bindStep acquireT1 fun s8 _ =>
  -- 5. T1 finishes and unlocks: swap(0, Rel) wakes ONLY if prev == CONTENDED!
  bindStep (atomicRmw s8 1 1 .rel (fun _ => UNLOCKED)) fun s9 prev1 =>
  if Nat.beq prev1 CONTENDED then
    futexWakeOne s9 1 1
  else
    .ok s9 prev1

/-- Omitting `CONTENDED` preservation (`cxchg(0, 1)`) leaves mutex `UNLOCKED` while `T2`
    is permanently parked (`futexParked = [(1, 2)]`, `futexWoken = []`): lost-wakeup deadlock! -/
theorem futex_3t_cxchg_lost_wakeup :
    ∃ s,
      runFutex3TWake false = .ok s LOCKED ∧
      hasEntry s.futexParked 1 2 = true ∧
      hasEntry s.futexWoken 1 2 = false ∧
      (match getLoc? s.locs 1 with | some l => locHeadVal l == UNLOCKED | none => false) = true :=
  ⟨_, rfl, rfl, rfl, rfl⟩

/-- Preserving `CONTENDED` (`swap(2, Acq)`) causes `T1`'s unlock to emit `futex_wake`,
    unparking `T2` (`futexParked = []`, `(1, 2) ∈ futexWoken`). -/
theorem futex_3t_swap_contended_wakes_t2 :
    ∃ s,
      runFutex3TWake true = .ok s 1 ∧
      hasEntry s.futexParked 1 2 = false ∧
      hasEntry s.futexWoken 1 2 = true :=
  ⟨_, rfl, rfl, rfl⟩

/-!
## Part 2 (`3b`): Parametric `Type 0` View-Indexed Mutex Ownership-Transfer Proof
Zero `sorry`, Pass-1 (`Init.*` only), `[propext]` at most.
-/

def ViewLe (v₁ v₂ : View) : Prop :=
  ∀ idx : Nat, Nat.le (viewGet v₁ idx) (viewGet v₂ idx)

/-- Upward-closed view-indexed resource predicate in `Type 0`. -/
def VProp : Type := View → Prop

def UpClosed (R : VProp) : Prop :=
  ∀ v₁ v₂ : View, ViewLe v₁ v₂ → R v₁ → R v₂

def NaOwnedAtView (loc : MemLoc) (P : Nat → Prop) (v : View) : Prop :=
  Nat.le loc.lastNaWrTs (viewGet v loc.lastNaWrTid) ∧
  (∀ tid : Nat, Nat.le (viewGet loc.lastNaRdClock tid) (viewGet v tid)) ∧
  P (locHeadVal loc)

/-- View-indexed mutex resource assertion in `Type 0`: asserts that at view `v`,
    location `dataLoc` in `st` is owned at `v` with invariant `P`. -/
def MutexInv (st : WMemState) (dataLoc : Nat) (P : Nat → Prop) : VProp :=
  fun v =>
    match getLoc? st.locs dataLoc with
    | some d => NaOwnedAtView d P v
    | none => False

-- Structural Pass-1 vector clock helpers (zero `omega` / `by_cases`)

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
  | zero => intro _; exact Nat.zero_le _
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

theorem viewGet_viewJoin_ge_left (xs ys : View) (idx : Nat) :
    Nat.le (viewGet xs idx) (viewGet (viewJoin xs ys) idx) := by
  revert ys idx
  induction xs with
  | nil => intro _ _; exact Nat.zero_le _
  | cons x xt ih =>
    intro ys idx
    cases ys with
    | nil => exact Nat.le_refl _
    | cons y yt =>
      cases idx with
      | zero => exact natMax_ge_left x y
      | succ n => exact ih yt n

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

theorem viewLe_join_left (xs ys : View) : ViewLe xs (viewJoin xs ys) :=
  fun idx => viewGet_viewJoin_ge_left xs ys idx

theorem viewLe_join_right (xs ys : View) : ViewLe ys (viewJoin xs ys) :=
  fun idx => viewGet_viewJoin_ge_right xs ys idx

theorem viewLe_refl (v : View) : ViewLe v v :=
  fun _ => Nat.le_refl _

theorem viewLe_trans {a b c : View} (h1 : ViewLe a b) (h2 : ViewLe b c) : ViewLe a c :=
  fun idx => Nat.le_trans (h1 idx) (h2 idx)

theorem viewGet_viewSet_same (v : View) (idx val : Nat) :
    viewGet (viewSet v idx val) idx = val := by
  revert v
  induction idx with
  | zero =>
    intro v
    cases v <;> rfl
  | succ n ih =>
    intro v
    cases v with
    | nil => exact ih []
    | cons _ xs => exact ih xs

theorem viewGet_bumpCur_ge (v : View) (tid idx : Nat) :
    Nat.le (viewGet v idx) (viewGet (bumpCur v tid).1 idx) := by
  revert v idx
  induction tid with
  | zero =>
    intro v idx
    cases idx with
    | zero =>
      cases v with
      | nil => exact Nat.zero_le 1
      | cons x _ => exact Nat.le_succ x
    | succ k =>
      cases v with
      | nil => exact Nat.le_refl 0
      | cons _ _ => exact Nat.le_refl _
  | succ t ih =>
    intro v idx
    cases idx with
    | zero =>
      cases v <;> exact Nat.le_refl _
    | succ k =>
      cases v with
      | nil => exact Nat.zero_le _
      | cons _ xs => exact ih xs k

theorem viewLe_bumpCur (v : View) (tid : Nat) : ViewLe v (bumpCur v tid).1 :=
  fun idx => viewGet_bumpCur_ge v tid idx

theorem viewGet_viewSet_ge_of_le (v : View) (tid val : Nat)
    (hTid : Nat.le (viewGet v tid) val) (idx : Nat) :
    Nat.le (viewGet v idx) (viewGet (viewSet v tid val) idx) := by
  revert v tid val
  induction idx with
  | zero =>
    intro v tid val hTid
    cases tid with
    | zero =>
      cases v with
      | nil => exact Nat.zero_le val
      | cons _ _ => exact hTid
    | succ _ =>
      cases v <;> exact Nat.le_refl _
  | succ k ih =>
    intro v tid val hTid
    cases tid with
    | zero =>
      cases v with
      | nil => exact Nat.le_refl 0
      | cons _ _ => exact Nat.le_refl _
    | succ t =>
      cases v with
      | nil => exact Nat.zero_le _
      | cons _ xs => exact ih xs t val hTid

private theorem viewLeExceptAux_of_le (xs ys : List Nat) (i tid : Nat)
    (h : ∀ j : Nat, Nat.le (viewGet xs j) (viewGet ys j)) :
    viewLeExceptAux xs ys i tid = true := by
  revert ys i
  induction xs with
  | nil => intro _ _ _; rfl
  | cons x xt ih =>
    intro ys i h
    cases ys with
    | nil =>
      have hble : Nat.ble x 0 = true := natBle_true_of_le (h 0)
      have htail : viewLeExceptAux xt [] (i + 1) tid = true :=
        ih [] (i + 1) (fun j => h (j + 1))
      dsimp [viewLeExceptAux]
      rw [hble, htail]
      cases Nat.beq i tid <;> rfl
    | cons y yt =>
      have hble : Nat.ble x y = true := natBle_true_of_le (h 0)
      have htail : viewLeExceptAux xt yt (i + 1) tid = true :=
        ih yt (i + 1) (fun j => h (j + 1))
      dsimp [viewLeExceptAux]
      rw [hble, htail]
      cases Nat.beq i tid <;> rfl

theorem viewLeExcept_of_le {xs ys : View} (tid : Nat) (h : ViewLe xs ys) :
    viewLeExcept xs ys tid = true :=
  viewLeExceptAux_of_le xs ys 0 tid h

theorem getLoc_setLoc_same (ls : List MemLoc) (idx : Nat) (l0 l1 : MemLoc)
    (h : getLoc? ls idx = some l0) :
    getLoc? (setLoc ls idx l1) idx = some l1 := by
  revert ls
  induction idx with
  | zero =>
    intro ls h
    cases ls with
    | nil => cases h
    | cons _ _ => rfl
  | succ n ih =>
    intro ls h
    cases ls with
    | nil => cases h
    | cons _ tl => exact ih tl h

theorem getLoc_setLoc_ne (ls : List MemLoc) (i j : Nat) (l1 : MemLoc) (hNe : i ≠ j) :
    getLoc? (setLoc ls i l1) j = getLoc? ls j := by
  revert ls j
  induction i with
  | zero =>
    intro ls j hNe
    cases ls with
    | nil => rfl
    | cons _ tl =>
      cases j with
      | zero => exact False.elim (hNe rfl)
      | succ _ => rfl
  | succ i' ih =>
    intro ls j hNe
    cases ls with
    | nil => rfl
    | cons _ tl =>
      cases j with
      | zero => rfl
      | succ j' =>
        exact ih tl j' (fun heq => hNe (congrArg Nat.succ heq))

theorem getThread_setThread_same (ts : List ThreadView) (idx : Nat) (t0 t1 : ThreadView)
    (h : getThread? ts idx = some t0) :
    getThread? (setThread ts idx t1) idx = some t1 := by
  revert ts
  induction idx with
  | zero =>
    intro ts h
    cases ts with
    | nil => cases h
    | cons _ _ => rfl
  | succ n ih =>
    intro ts h
    cases ts with
    | nil => cases h
    | cons _ tl => exact ih tl h

/-- `MutexInv` is upward-closed under `ViewLe` (valid resource predicate in `VProp : Type 0`). -/
theorem mutexInv_upClosed (st : WMemState) (dataLoc : Nat) (P : Nat → Prop) :
    UpClosed (MutexInv st dataLoc P) := by
  intro v₁ v₂ hLe hInv
  dsimp [MutexInv] at hInv ⊢
  cases hLoc : getLoc? st.locs dataLoc with
  | none =>
    rw [hLoc] at hInv
    exact False.elim hInv
  | some d =>
    rw [hLoc] at hInv
    refine ⟨Nat.le_trans hInv.1 (hLe d.lastNaWrTid), ?_, hInv.2.2⟩
    intro tid
    exact Nat.le_trans (hInv.2.1 tid) (hLe tid)

/-- Equation lemma: `naWrite` produces `.ok` deterministically from guard truth. -/
theorem naWrite_eq_ok
    (st : WMemState) (tid locId newVal : Nat) (tv : ThreadView) (loc : MemLoc)
    (hT : getThread? st.threads tid = some tv)
    (hL : getLoc? st.locs locId = some loc)
    (hWr : Nat.ble loc.lastNaWrTs (viewGet tv.cur loc.lastNaWrTid) = true)
    (hRd : viewLeExcept loc.lastNaRdClock tv.cur tid = true) :
    naWrite st tid locId newVal =
      .ok { st with
        threads := setThread st.threads tid
          { cur := (bumpCur tv.cur tid).1, acq := viewSet tv.acq tid (bumpCur tv.cur tid).2 }
        locs := setLoc st.locs locId
          { msgs := { ts := (match loc.msgs.head? with | some m => m.ts + 1 | none => 1), val := newVal, relView := [] } :: loc.msgs
            lastNaWrTid := tid
            lastNaWrTs := (bumpCur tv.cur tid).2
            lastNaRdClock := [] } } 0 := by
  dsimp [naWrite]
  rw [hT, hL]
  dsimp
  rw [hWr, hRd]
  rfl

/-- Equation lemma: `naRead` produces `.ok` deterministically from write-clock guard truth. -/
theorem naRead_eq_ok
    (st : WMemState) (tid locId : Nat) (tv : ThreadView) (loc : MemLoc)
    (hT : getThread? st.threads tid = some tv)
    (hL : getLoc? st.locs locId = some loc)
    (hWr : Nat.ble loc.lastNaWrTs (viewGet tv.cur loc.lastNaWrTid) = true) :
    naRead st tid locId =
      .ok { st with
        threads := setThread st.threads tid
          { cur := (bumpCur tv.cur tid).1, acq := viewSet tv.acq tid (bumpCur tv.cur tid).2 }
        locs := setLoc st.locs locId
          { loc with lastNaRdClock := viewSet loc.lastNaRdClock tid (bumpCur tv.cur tid).2 } }
        (locHeadVal loc) := by
  dsimp [naRead]
  rw [hT, hL]
  dsimp
  rw [hWr]
  rfl

/-- Equation lemma for `atomicRmw` with `.rel` ordering. -/
theorem atomicRmw_rel_eq_ok
    (st : WMemState) (tid locId : Nat) (f : Nat → Nat)
    (tv : ThreadView) (loc : MemLoc) (latest : AtomicMsg)
    (hT : getThread? st.threads tid = some tv)
    (hL : getLoc? st.locs locId = some loc)
    (hHead : loc.msgs.head? = some latest) :
    atomicRmw st tid locId .rel f =
      .ok { st with
        threads := setThread st.threads tid
          { cur := (bumpCur tv.cur tid).1
            acq := viewJoin (viewSet tv.acq tid (bumpCur tv.cur tid).2) latest.relView }
        locs := setLoc st.locs locId
          { loc with msgs := { ts := latest.ts + 1, val := f latest.val, relView := (bumpCur tv.cur tid).1 } :: loc.msgs } }
        latest.val := by
  dsimp [atomicRmw, BEq.beq, Ordering.beq]
  rw [hT, hL]
  dsimp
  rw [hHead]

/-- Equation lemma for `atomicRmw` with `.acq` ordering. -/
theorem atomicRmw_acq_eq_ok
    (st : WMemState) (tid locId : Nat) (f : Nat → Nat)
    (tv : ThreadView) (loc : MemLoc) (latest : AtomicMsg)
    (hT : getThread? st.threads tid = some tv)
    (hL : getLoc? st.locs locId = some loc)
    (hHead : loc.msgs.head? = some latest) :
    let cur0 := (bumpCur tv.cur tid).1
    let myTs := (bumpCur tv.cur tid).2
    let cur1 := viewJoin cur0 latest.relView
    let acq1 := viewJoin (viewJoin (viewSet tv.acq tid myTs) latest.relView) cur1
    atomicRmw st tid locId .acq f =
      .ok { st with
        threads := setThread st.threads tid { cur := cur1, acq := acq1 }
        locs := setLoc st.locs locId
          { loc with msgs := { ts := latest.ts + 1, val := f latest.val, relView := [] } :: loc.msgs } }
        latest.val := by
  dsimp [atomicRmw, BEq.beq, Ordering.beq]
  rw [hT, hL]
  dsimp
  rw [hHead]

/-- Helper: `naWrite` under exclusive data ownership succeeds, sets `P newVal`, and
    establishes `MutexInv` at the writer's post-step `cur'` view. -/
theorem naWrite_establishes_mutexInv
    (st : WMemState) (t1 dataLoc newVal : Nat) (P : Nat → Prop)
    (tv1 : ThreadView) (d : MemLoc)
    (hT1 : getThread? st.threads t1 = some tv1)
    (hData : getLoc? st.locs dataLoc = some d)
    (hOwn : NaOwnedAtView d (fun _ => True) tv1.cur)
    (hP : P newVal) :
    ∃ st1 tv1',
      naWrite st t1 dataLoc newVal = .ok st1 0 ∧
      getThread? st1.threads t1 = some tv1' ∧
      MutexInv st1 dataLoc P tv1'.cur ∧
      (∀ lockId, lockId ≠ dataLoc → getLoc? st1.locs lockId = getLoc? st.locs lockId) := by
  have hWr : Nat.ble d.lastNaWrTs (viewGet tv1.cur d.lastNaWrTid) = true :=
    natBle_true_of_le hOwn.1
  have hRd : viewLeExcept d.lastNaRdClock tv1.cur t1 = true :=
    viewLeExcept_of_le t1 hOwn.2.1
  let cur' := (bumpCur tv1.cur t1).1
  let myTs := (bumpCur tv1.cur t1).2
  let tv1' : ThreadView := { cur := cur', acq := viewSet tv1.acq t1 myTs }
  let d' : MemLoc :=
    { msgs := { ts := (match d.msgs.head? with | some m => m.ts + 1 | none => 1), val := newVal, relView := [] } :: d.msgs
      lastNaWrTid := t1
      lastNaWrTs := myTs
      lastNaRdClock := [] }
  let st1 : WMemState :=
    { st with
      threads := setThread st.threads t1 tv1'
      locs := setLoc st.locs dataLoc d' }
  refine ⟨st1, tv1', naWrite_eq_ok st t1 dataLoc newVal tv1 d hT1 hData hWr hRd, ?_, ?_, ?_⟩
  · exact getThread_setThread_same st.threads t1 tv1 tv1' hT1
  · dsimp [MutexInv]
    rw [getLoc_setLoc_same st.locs dataLoc d d' hData]
    refine ⟨?_, ?_, hP⟩
    · change Nat.le myTs (viewGet cur' t1)
      change Nat.le (viewGet tv1.cur t1 + 1) (viewGet (viewSet tv1.cur t1 (viewGet tv1.cur t1 + 1)) t1)
      rw [viewGet_viewSet_same]
      exact Nat.le_refl _
    · intro tid
      exact Nat.zero_le _
  · intro lockId hNe
    exact getLoc_setLoc_ne st.locs dataLoc lockId d' (fun eq => hNe eq.symm)

/-- Universal Release publication theorem (`unlock`):
    For ANY writer `t1`, ANY disjoint `lockLoc ≠ dataLoc`, and ANY payload `newVal` with `P newVal`,
    writing `dataLoc` followed by releasing `lockLoc` with `.rel` (`atomicRmw ... .rel`)
    succeeds without faulting and installs `MutexInv st2 dataLoc P msg.relView` on the
    published head message of `lockLoc`. -/
theorem mutex_naWrite_unlock_publishes_inv
    (st : WMemState) (t1 lockLoc dataLoc newVal : Nat) (P : Nat → Prop)
    (hNe : lockLoc ≠ dataLoc)
    (tv1 : ThreadView) (d l : MemLoc) (lHead : AtomicMsg)
    (hT1 : getThread? st.threads t1 = some tv1)
    (hData : getLoc? st.locs dataLoc = some d)
    (hLock : getLoc? st.locs lockLoc = some l)
    (hHead : l.msgs.head? = some lHead)
    (hOwn : NaOwnedAtView d (fun _ => True) tv1.cur)
    (hP : P newVal)
    (nextStateFn : Nat → Nat) :
    ∃ st1 st2 msg,
      naWrite st t1 dataLoc newVal = .ok st1 0 ∧
      atomicRmw st1 t1 lockLoc .rel nextStateFn = .ok st2 lHead.val ∧
      (match getLoc? st2.locs lockLoc with | some l' => l'.msgs.head? = some msg | none => False) ∧
      MutexInv st2 dataLoc P msg.relView := by
  cases naWrite_establishes_mutexInv st t1 dataLoc newVal P tv1 d hT1 hData hOwn hP with
  | intro st1 hRest1 =>
    cases hRest1 with
    | intro tv1' hRest2 =>
      cases hRest2 with
      | intro hW hRest3 =>
        cases hRest3 with
        | intro hT1' hRest4 =>
          cases hRest4 with
          | intro hInv1 hOther =>
            have hLock1 : getLoc? st1.locs lockLoc = some l := by
              rw [hOther lockLoc hNe]
              exact hLock
            let cur1 := (bumpCur tv1'.cur t1).1
            let msgNew : AtomicMsg := { ts := lHead.ts + 1, val := nextStateFn lHead.val, relView := cur1 }
            let l' : MemLoc := { l with msgs := msgNew :: l.msgs }
            let st2 : WMemState :=
              { st1 with
                threads := setThread st1.threads t1 { cur := cur1, acq := viewJoin (viewSet tv1'.acq t1 (bumpCur tv1'.cur t1).2) lHead.relView }
                locs := setLoc st1.locs lockLoc l' }
            refine ⟨st1, st2, msgNew, hW, atomicRmw_rel_eq_ok st1 t1 lockLoc nextStateFn tv1' l lHead hT1' hLock1 hHead, ?_, ?_⟩
            · change (match getLoc? (setLoc st1.locs lockLoc l') lockLoc with | some x => x.msgs.head? = some msgNew | none => False)
              rw [getLoc_setLoc_same st1.locs lockLoc l l' hLock1]
              rfl
            · have hDataSame : getLoc? st2.locs dataLoc = getLoc? st1.locs dataLoc :=
                getLoc_setLoc_ne st1.locs lockLoc dataLoc l' hNe
              have hInvUp : MutexInv st1 dataLoc P cur1 :=
                mutexInv_upClosed st1 dataLoc P tv1'.cur cur1 (viewLe_bumpCur tv1'.cur t1) hInv1
              dsimp [MutexInv] at hInvUp ⊢
              rw [hDataSame]
              exact hInvUp

def viewTail : View → View
  | [] => []
  | _ :: ws => ws

theorem viewGet_succ (w : View) (k : Nat) :
    viewGet w (k + 1) = viewGet (viewTail w) k := by
  cases w <;> rfl

theorem viewLe_viewSet_of_le (v w : View) (t val : Nat)
    (h1 : ViewLe v w) (h2 : Nat.le val (viewGet w t)) :
    ViewLe (viewSet v t val) w := by
  revert v w
  induction t with
  | zero =>
    intro v w h1 h2 idx
    cases idx with
    | zero =>
      cases v <;> exact h2
    | succ k =>
      cases v with
      | nil => exact Nat.zero_le _
      | cons _ _ => exact h1 (k + 1)
  | succ t' ih =>
    intro v w h1 h2 idx
    cases idx with
    | zero =>
      cases v with
      | nil => exact Nat.zero_le _
      | cons _ _ => exact h1 0
    | succ k =>
      cases v with
      | nil =>
        have h1' : ViewLe [] (viewTail w) := fun _ => Nat.zero_le _
        have h2' : Nat.le val (viewGet (viewTail w) t') := by
          rw [← viewGet_succ w t']
          exact h2
        rw [viewGet_succ w k]
        exact ih [] (viewTail w) h1' h2' k
      | cons _ xs =>
        have h1' : ViewLe xs (viewTail w) := fun j => by
          rw [← viewGet_succ w j]
          exact h1 (j + 1)
        have h2' : Nat.le val (viewGet (viewTail w) t') := by
          rw [← viewGet_succ w t']
          exact h2
        rw [viewGet_succ w k]
        exact ih xs (viewTail w) h1' h2' k

/-- Universal Acquire consumption theorem (`lock` / `naRead`):
    For ANY acquiring thread `t2`, ANY disjoint `lockLoc ≠ dataLoc`, ANY state `st`,
    and ANY payload invariant `P : Nat → Prop`, if `lockLoc`'s head message `lHead` satisfies
    `MutexInv st dataLoc P lHead.relView`, then `atomicRmw st t2 lockLoc .acq _` followed by
    `naRead _ t2 dataLoc` NEVER faults with `.dataRace` (succeeds with `.ok stFinal ret`),
    establishes **`P ret`**, AND preserves **`MutexInv stFinal dataLoc P tvFinal.cur`** so `t2`
    retains exclusive ownership of `dataLoc` for critical-section writes before unlock. -/
theorem mutex_acquire_naRead_safe
    (st : WMemState) (t2 lockLoc dataLoc : Nat) (P : Nat → Prop)
    (hNe : lockLoc ≠ dataLoc)
    (tv2 : ThreadView) (d l : MemLoc) (lHead : AtomicMsg)
    (hT2 : getThread? st.threads t2 = some tv2)
    (hData : getLoc? st.locs dataLoc = some d)
    (hLock : getLoc? st.locs lockLoc = some l)
    (hHead : l.msgs.head? = some lHead)
    (hInv : MutexInv st dataLoc P lHead.relView)
    (nextLockFn : Nat → Nat) :
    ∃ st1 st2 ret tv2',
      atomicRmw st t2 lockLoc .acq nextLockFn = .ok st1 lHead.val ∧
      naRead st1 t2 dataLoc = .ok st2 ret ∧
      P ret ∧
      getThread? st2.threads t2 = some tv2' ∧
      MutexInv st2 dataLoc P tv2'.cur := by
  let cur0 := (bumpCur tv2.cur t2).1
  let myTs0 := (bumpCur tv2.cur t2).2
  let cur1 := viewJoin cur0 lHead.relView
  let acq1 := viewJoin (viewJoin (viewSet tv2.acq t2 myTs0) lHead.relView) cur1
  let tv2Mid : ThreadView := { cur := cur1, acq := acq1 }
  let msgNew : AtomicMsg := { ts := lHead.ts + 1, val := nextLockFn lHead.val, relView := [] }
  let l' : MemLoc := { l with msgs := msgNew :: l.msgs }
  let st1 : WMemState :=
    { st with
      threads := setThread st.threads t2 tv2Mid
      locs := setLoc st.locs lockLoc l' }
  have hT2_1 : getThread? st1.threads t2 = some tv2Mid :=
    getThread_setThread_same st.threads t2 tv2 tv2Mid hT2
  have hData_1 : getLoc? st1.locs dataLoc = some d := by
    change getLoc? (setLoc st.locs lockLoc l') dataLoc = some d
    rw [getLoc_setLoc_ne st.locs lockLoc dataLoc l' hNe]
    exact hData
  have hInv1 : NaOwnedAtView d P cur1 := by
    have hUp := mutexInv_upClosed st dataLoc P lHead.relView cur1 (viewLe_join_right cur0 lHead.relView) hInv
    dsimp [MutexInv] at hUp
    rw [hData] at hUp
    exact hUp
  have hBle : Nat.ble d.lastNaWrTs (viewGet cur1 d.lastNaWrTid) = true :=
    natBle_true_of_le hInv1.1
  let cur2 := (bumpCur cur1 t2).1
  let myTs2 := (bumpCur cur1 t2).2
  let d' : MemLoc := { d with lastNaRdClock := viewSet d.lastNaRdClock t2 myTs2 }
  let tv2' : ThreadView := { cur := cur2, acq := viewSet acq1 t2 myTs2 }
  let st2 : WMemState :=
    { st1 with
      threads := setThread st1.threads t2 tv2'
      locs := setLoc st1.locs dataLoc d' }
  refine ⟨st1, st2, locHeadVal d, tv2',
    atomicRmw_acq_eq_ok st t2 lockLoc nextLockFn tv2 l lHead hT2 hLock hHead,
    naRead_eq_ok st1 t2 dataLoc tv2Mid d hT2_1 hData_1 hBle,
    hInv1.2.2, ?_, ?_⟩
  · exact getThread_setThread_same st1.threads t2 tv2Mid tv2' hT2_1
  · dsimp [MutexInv]
    rw [getLoc_setLoc_same st1.locs dataLoc d d' hData_1]
    refine ⟨?_, ?_, hInv1.2.2⟩
    · exact Nat.le_trans hInv1.1 (viewGet_bumpCur_ge cur1 t2 d.lastNaWrTid)
    · have hPrev : ViewLe d.lastNaRdClock cur2 :=
        fun k => Nat.le_trans (hInv1.2.1 k) (viewGet_bumpCur_ge cur1 t2 k)
      have hSelf : Nat.le myTs2 (viewGet cur2 t2) := by
        change Nat.le (viewGet cur1 t2 + 1) (viewGet (viewSet cur1 t2 (viewGet cur1 t2 + 1)) t2)
        rw [viewGet_viewSet_same]
        exact Nat.le_refl _
      exact viewLe_viewSet_of_le d.lastNaRdClock cur2 t2 myTs2 hPrev hSelf

#check (VProp : Type)
#print axioms futex_spurious_acq_race_free_77
#print axioms futex_spurious_relaxed_is_dataRace
#print axioms futex_matched_wake_race_free_88
#print axioms futex_3t_cxchg_lost_wakeup
#print axioms futex_3t_swap_contended_wakes_t2
#print axioms mutexInv_upClosed
#print axioms mutex_naWrite_unlock_publishes_inv
#print axioms mutex_acquire_naRead_safe

end FutexMutexProbe

end
