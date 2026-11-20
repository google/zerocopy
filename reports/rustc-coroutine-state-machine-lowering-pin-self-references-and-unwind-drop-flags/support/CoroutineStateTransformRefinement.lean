/-!
  Mechanized Lean 4 model of `rustc`'s coroutine `StateTransform` lowering:
  1. Source 2-suspend-point coroutine operational semantics (`SrcCoroState`, `stepSrcPoll`,
     `stepSrcDrop`), tracking pinned locals borrowed across `.await`, dynamic drop flags
     (`ElaborateDrops`), cancellation drop, and panic unwinding.
  2. Lowered discriminant-indexed enum state machine (`LoweredFrame`, `loweredPoll`,
     `loweredDropGlue`), modeling `Unresumed (0)`, `Returned (1)`, `Panicked (2)`,
     `Suspend0 (3)`, `Suspend1 (4)`, variant-overlapped union payload (`overlapUnionSlot`),
     promoted self-borrow / drop-flag prefix slots, and exit-only `SetDiscriminant`.
  3. Constructive lockstep refinement (`poll_step_lockstep_sim`, `cancel_drop_lockstep_sim`,
     `execTrace_lockstep_sim`) and `NoDoubleDrop` safety invariants.
  4. Two sharpness counterexamples:
     - (CE1) `ce1_noalias_on_self_ref_pin_miscompiles`: emitting LLVM `noalias` on
       `Pin<&mut Self>` for a `!Unpin` self-referential coroutine permits alias-blind
       store-load reordering across cross-activation `based_on` provenance, yielding
       stale reads (`15 ≠ 99`) and violating LLVM `noalias` UB rules.
     - (CE2) `ce2a_missing_poison_double_drops` and
       `ce2b_missing_poison_repoll_reads_uninit_payload`: omitting `SetDiscriminant(2)`
       (`Panicked`) before `UnwindResume` causes caller-unwind double-drops (`count = 2`)
       and re-poll faults on moved-out variant payload (`overlapUnionSlot = none`).
-/

namespace CoroutineStateTransformRefinement

/-- Reserved coroutine discriminants matching `rustc_middle::ty::CoroutineArgsExt`. -/
abbrev DISCR_UNRESUMED : Nat := 0
abbrev DISCR_RETURNED  : Nat := 1
abbrev DISCR_POISONED  : Nat := 2
abbrev DISCR_SUSPEND0  : Nat := 3
abbrev DISCR_SUSPEND1  : Nat := 4

private def natBeq (a b : Nat) : Bool := Nat.beq a b

private theorem natBeq_refl (a : Nat) : natBeq a a = true := Nat.beq_refl a

private theorem natBeq_eq_true_iff (a b : Nat) : natBeq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

/-- Destructor identities in the 2-suspend-point coroutine specimen. -/
inductive GuardId where
  | upvarGuard
  | scopeGuard
  | condGuard
  deriving DecidableEq, Repr

abbrev DropLog := List GuardId

/-- Count occurrences of a specific guard in a drop trace. -/
def countGuard (g : GuardId) : DropLog → Nat
  | [] => 0
  | x :: xs =>
    let rest := countGuard g xs
    if x == g then rest + 1 else rest

/-- Safety predicate: every live resource is dropped at most once. -/
def NoDoubleDrop (log : DropLog) : Prop :=
  countGuard .upvarGuard log ≤ 1 ∧
  countGuard .scopeGuard log ≤ 1 ∧
  countGuard .condGuard  log ≤ 1

/-- Constructive boolean check equivalent to `NoDoubleDrop`. -/
def noDoubleDropB (log : DropLog) : Bool :=
  Nat.ble (countGuard .upvarGuard log) 1 &&
  Nat.ble (countGuard .scopeGuard log) 1 &&
  Nat.ble (countGuard .condGuard  log) 1

private theorem nat_ble_true_iff_le : ∀ (a b : Nat), Nat.ble a b = true ↔ a ≤ b := by
  intro a
  induction a with
  | zero =>
    intro b
    cases b <;> constructor <;> intro _ <;> first | exact Nat.zero_le _ | rfl
  | succ a ih =>
    intro b
    cases b with
    | zero =>
      constructor
      · intro h
        cases h
      · intro h
        exact absurd h (Nat.not_succ_le_zero a)
    | succ b =>
      have h1 := ih b
      constructor
      · intro h
        exact Nat.succ_le_succ (h1.mp h)
      · intro h
        exact h1.mpr (Nat.le_of_succ_le_succ h)

theorem noDoubleDropB_iff (log : DropLog) : noDoubleDropB log = true ↔ NoDoubleDrop log := by
  unfold noDoubleDropB NoDoubleDrop
  cases hU : Nat.ble (countGuard .upvarGuard log) 1 <;>
  cases hS : Nat.ble (countGuard .scopeGuard log) 1 <;>
  cases hC : Nat.ble (countGuard .condGuard  log) 1 <;>
  simp only [Bool.and_true, Bool.and_false]
  · constructor <;> intro h
    · cases h
    · exact absurd ((nat_ble_true_iff_le _ _).mpr h.1) (by rw [hU]; intro x; cases x)
  · constructor <;> intro h
    · cases h
    · exact absurd ((nat_ble_true_iff_le _ _).mpr h.1) (by rw [hU]; intro x; cases x)
  · constructor <;> intro h
    · cases h
    · exact absurd ((nat_ble_true_iff_le _ _).mpr h.1) (by rw [hU]; intro x; cases x)
  · constructor <;> intro h
    · cases h
    · exact absurd ((nat_ble_true_iff_le _ _).mpr h.1) (by rw [hU]; intro x; cases x)
  · constructor <;> intro h
    · cases h
    · exact absurd ((nat_ble_true_iff_le _ _).mpr h.2.1) (by rw [hS]; intro x; cases x)
  · constructor <;> intro h
    · cases h
    · exact absurd ((nat_ble_true_iff_le _ _).mpr h.2.1) (by rw [hS]; intro x; cases x)
  · constructor <;> intro h
    · cases h
    · exact absurd ((nat_ble_true_iff_le _ _).mpr h.2.2) (by rw [hC]; intro x; cases x)
  · constructor
    · intro _
      exact ⟨(nat_ble_true_iff_le _ _).mp hU,
             (nat_ble_true_iff_le _ _).mp hS,
             (nat_ble_true_iff_le _ _).mp hC⟩
    · intro _
      trivial

/-- Inputs supplied at a `poll` / `resume` invocation. -/
inductive PollInput where
  | yieldPending
  | advance (v : Nat)
  | unwindPanic
  deriving DecidableEq, Repr

/-- Explicit panic classifications matching `AssertKind::ResumedAfter*`. -/
inductive PanicReason where
  | bodyUnwind
  | resumedAfterReturn
  | resumedAfterPanic
  deriving DecidableEq, Repr

/-- Observable result of polling a coroutine or observing a memory/pinning fault. -/
inductive PollOutcome where
  | pending
  | ready (ret : Nat)
  | panicked (reason : PanicReason)
  | faultUninitOrAlias
  deriving DecidableEq, Repr

/-- External operations applied to a coroutine instance. -/
inductive CoroAction where
  | poll (inp : PollInput)
  | cancelDrop
  deriving DecidableEq, Repr

/-- Control-flow phases of the source 2-suspend-point coroutine. -/
inductive SrcPhase where
  | unresumed
  | suspended0
  | suspended1
  | returned
  | panicked
  | dropped
  deriving DecidableEq, Repr

/--
  High-level pre-`StateTransform` coroutine state:
  - `pinnedLocal` is borrowed via `selfBorrowLive` across both `.await` points;
  - `earlyDropCond = true` drops `condGuard` after `.await #1` and before `.await #2`
    (synthesizing an `ElaborateDrops` dynamic `bool` drop flag);
  - `tmp0` and `tmp1` have disjoint lifetimes (`suspended0` vs `suspended1`).
-/
structure SrcCoroState where
  phase          : SrcPhase
  upvarVal       : Nat
  earlyDropCond  : Bool
  pinnedLocal    : Nat
  selfBorrowLive : Bool
  liveUpvar      : Bool
  liveScope      : Bool
  liveCond       : Bool
  tmp0           : Nat
  tmp1           : Nat
  dropLog        : DropLog
  deriving DecidableEq, Repr

/-- Initial unresumed source coroutine state. -/
def initSrc (upvarVal : Nat) (earlyDropCond : Bool) : SrcCoroState :=
  { phase          := .unresumed
    upvarVal       := upvarVal
    earlyDropCond  := earlyDropCond
    pinnedLocal    := 0
    selfBorrowLive := false
    liveUpvar      := true
    liveScope      := false
    liveCond       := false
    tmp0           := 0
    tmp1           := 0
    dropLog        := [] }

/-- Append active drops in reverse acquisition order (`cond`, `scope`, `upvar`). -/
def appendActiveDrops (log : DropLog) (liveCond liveScope liveUpvar : Bool) : DropLog :=
  let l1 := if liveCond  then log ++ [.condGuard]  else log
  let l2 := if liveScope then l1  ++ [.scopeGuard] else l1
  if liveUpvar then l2 ++ [.upvarGuard] else l2

/-- Source coroutine `poll` transition semantics. -/
def stepSrcPoll (s : SrcCoroState) (inp : PollInput) : PollOutcome × SrcCoroState :=
  match s.phase with
  | .unresumed =>
    let pinned := s.upvarVal + 10
    match inp with
    | .yieldPending =>
      (.pending,
       { s with
         phase          := .suspended0
         pinnedLocal    := pinned
         selfBorrowLive := true
         liveScope      := true
         liveCond       := true
         tmp0           := pinned + 1 })
    | .advance v0 =>
      let log1 := if s.earlyDropCond then s.dropLog ++ [.condGuard] else s.dropLog
      let condAlive := !s.earlyDropCond
      (.pending,
       { s with
         phase          := .suspended1
         pinnedLocal    := pinned
         selfBorrowLive := true
         liveScope      := true
         liveCond       := condAlive
         tmp0           := 0
         tmp1           := pinned + v0 + 2
         dropLog        := log1 })
    | .unwindPanic =>
      let log' := appendActiveDrops s.dropLog true true s.liveUpvar
      (.panicked .bodyUnwind,
       { s with
         phase          := .panicked
         pinnedLocal    := pinned
         selfBorrowLive := false
         liveUpvar      := false
         liveScope      := false
         liveCond       := false
         tmp0           := 0
         tmp1           := 0
         dropLog        := log' })
  | .suspended0 =>
    if !s.selfBorrowLive then
      (.faultUninitOrAlias, s)
    else
      match inp with
      | .yieldPending =>
        (.pending, s)
      | .advance v0 =>
        let log1 :=
          if s.earlyDropCond && s.liveCond then s.dropLog ++ [.condGuard] else s.dropLog
        let condAlive := if s.earlyDropCond then false else s.liveCond
        (.pending,
         { s with
           phase    := .suspended1
           tmp0     := 0
           tmp1     := s.pinnedLocal + v0 + 2
           liveCond := condAlive
           dropLog  := log1 })
      | .unwindPanic =>
        let log' := appendActiveDrops s.dropLog s.liveCond s.liveScope s.liveUpvar
        (.panicked .bodyUnwind,
         { s with
           phase          := .panicked
           selfBorrowLive := false
           liveUpvar      := false
           liveScope      := false
           liveCond       := false
           tmp0           := 0
           tmp1           := 0
           dropLog        := log' })
  | .suspended1 =>
    if !s.selfBorrowLive then
      (.faultUninitOrAlias, s)
    else
      match inp with
      | .yieldPending =>
        (.pending, s)
      | .advance v1 =>
        let res := s.pinnedLocal + s.tmp1 + v1
        let log' := appendActiveDrops s.dropLog s.liveCond s.liveScope s.liveUpvar
        (.ready res,
         { s with
           phase          := .returned
           selfBorrowLive := false
           liveUpvar      := false
           liveScope      := false
           liveCond       := false
           tmp0           := 0
           tmp1           := 0
           dropLog        := log' })
      | .unwindPanic =>
        let log' := appendActiveDrops s.dropLog s.liveCond s.liveScope s.liveUpvar
        (.panicked .bodyUnwind,
         { s with
           phase          := .panicked
           selfBorrowLive := false
           liveUpvar      := false
           liveScope      := false
           liveCond       := false
           tmp0           := 0
           tmp1           := 0
           dropLog        := log' })
  | .returned => (.panicked .resumedAfterReturn, s)
  | .panicked => (.panicked .resumedAfterPanic, s)
  | .dropped  => (.faultUninitOrAlias, s)

/-- Source coroutine `drop` transition semantics. -/
def stepSrcDrop (s : SrcCoroState) : SrcCoroState :=
  match s.phase with
  | .unresumed =>
    let log' := appendActiveDrops s.dropLog false false s.liveUpvar
    { s with phase := .dropped, liveUpvar := false, dropLog := log' }
  | .suspended0 | .suspended1 =>
    let log' := appendActiveDrops s.dropLog s.liveCond s.liveScope s.liveUpvar
    { s with
      phase          := .dropped
      selfBorrowLive := false
      liveUpvar      := false
      liveScope      := false
      liveCond       := false
      tmp0           := 0
      tmp1           := 0
      dropLog        := log' }
  | .returned | .panicked | .dropped =>
    { s with phase := .dropped }

/-- Execute a finite action list on `SrcCoroState`. -/
def runSrcActions (s : SrcCoroState) : List CoroAction → PollOutcome × SrcCoroState
  | [] => (.pending, s)
  | [act] =>
    match act with
    | .poll inp   => stepSrcPoll s inp
    | .cancelDrop => (.ready 0, stepSrcDrop s)
  | act :: rest =>
    let s' :=
      match act with
      | .poll inp   => (stepSrcPoll s inp).2
      | .cancelDrop => stepSrcDrop s
    runSrcActions s' rest

/-! ### Lowered `StateTransform` Discriminant-Indexed State Machine -/

/-- Address-anchored self-borrow pointer stored in the coroutine prefix (`_s1`). -/
structure SelfRefPtr where
  baseAddr : Nat
  fieldOff : Nat
  deriving DecidableEq, Repr

/--
  Lowered coroutine frame layout matching `rustc_mir_transform::coroutine` +
  `rustc_abi::layout::coroutine`:
  - `discr` is mutated ONLY on exit (`SetDiscriminant`), never upon function entry.
  - `s0_pinnedLocal`, `s1_selfRef`, `s2_scopeLive`, `s3_condDropFlag` sit in the
    overlap-ineligible prefix alongside the upvar slot.
  - `overlapUnionSlot` models the single shared physical union storage reused across
    disjoint variants `Suspend0 (3)` (`tmp0`) and `Suspend1 (4)` (`tmp1`).
-/
structure LoweredFrame where
  frameAddr        : Nat
  discr            : Nat
  upvarSlot        : Option Nat
  earlyDropCfg     : Bool
  s0_pinnedLocal   : Option Nat
  s1_selfRef       : Option SelfRefPtr
  s2_scopeLive     : Bool
  s3_condDropFlag  : Bool
  overlapUnionSlot : Option Nat
  dropLog          : DropLog
  deriving DecidableEq, Repr

/-- Initial lowered state machine at `Unresumed (0)`. -/
def initLowered (addr upvarVal : Nat) (earlyDropCond : Bool) : LoweredFrame :=
  { frameAddr        := addr
    discr            := DISCR_UNRESUMED
    upvarSlot        := some upvarVal
    earlyDropCfg     := earlyDropCond
    s0_pinnedLocal   := none
    s1_selfRef       := none
    s2_scopeLive     := false
    s3_condDropFlag  := false
    overlapUnionSlot := none
    dropLog          := [] }

/-- Dereference pinned self-reference `_s1` checking address stability (`Pin`). -/
def readPinnedSelfRef (f : LoweredFrame) : Option Nat :=
  match f.s1_selfRef, f.s0_pinnedLocal with
  | some ptr, some v =>
    if natBeq ptr.baseAddr f.frameAddr && natBeq ptr.fieldOff 0 then some v else none
  | _, _ => none

/-- Resume helper from `Suspend0 (3)` after loading `pinnedLocal` through `_s1`. -/
def loweredResumeFrom0 (f : LoweredFrame) (inp : PollInput) : PollOutcome × LoweredFrame :=
  match readPinnedSelfRef f, f.overlapUnionSlot with
  | some pinned, some _tmp0 =>
    match inp with
    | .yieldPending =>
      (.pending, f)
    | .advance v0 =>
      -- Move/consume `_tmp0` out of `overlapUnionSlot`, then write `tmp1` into the same slot.
      let log1 :=
        if f.earlyDropCfg && f.s3_condDropFlag then f.dropLog ++ [.condGuard] else f.dropLog
      let flag1 := if f.earlyDropCfg then false else f.s3_condDropFlag
      (.pending,
       { f with
         discr            := DISCR_SUSPEND1
         s3_condDropFlag  := flag1
         overlapUnionSlot := some (pinned + v0 + 2)
         dropLog          := log1 })
    | .unwindPanic =>
      -- `generate_poison_block_and_redirect_unwinds_there`: drop active guards via flags,
      -- then execute `SetDiscriminant(2)` (`Panicked`) before `UnwindResume`.
      let log' := appendActiveDrops f.dropLog f.s3_condDropFlag f.s2_scopeLive f.upvarSlot.isSome
      (.panicked .bodyUnwind,
       { f with
         discr            := DISCR_POISONED
         upvarSlot        := none
         s1_selfRef       := none
         s2_scopeLive     := false
         s3_condDropFlag  := false
         overlapUnionSlot := none
         dropLog          := log' })
  | _, _ => (.faultUninitOrAlias, f)

/-- Resume helper from `Suspend1 (4)` reading `_s1` and overlapped `tmp1`. -/
def loweredResumeFrom1 (f : LoweredFrame) (inp : PollInput) : PollOutcome × LoweredFrame :=
  match readPinnedSelfRef f, f.overlapUnionSlot with
  | some pinned, some tmp1 =>
    match inp with
    | .yieldPending =>
      (.pending, f)
    | .advance v1 =>
      let res := pinned + tmp1 + v1
      let log' := appendActiveDrops f.dropLog f.s3_condDropFlag f.s2_scopeLive f.upvarSlot.isSome
      (.ready res,
       { f with
         discr            := DISCR_RETURNED
         upvarSlot        := none
         s1_selfRef       := none
         s2_scopeLive     := false
         s3_condDropFlag  := false
         overlapUnionSlot := none
         dropLog          := log' })
    | .unwindPanic =>
      let log' := appendActiveDrops f.dropLog f.s3_condDropFlag f.s2_scopeLive f.upvarSlot.isSome
      (.panicked .bodyUnwind,
       { f with
         discr            := DISCR_POISONED
         upvarSlot        := none
         s1_selfRef       := none
         s2_scopeLive     := false
         s3_condDropFlag  := false
         overlapUnionSlot := none
         dropLog          := log' })
  | _, _ => (.faultUninitOrAlias, f)

/-- Lowered `Future::poll` state machine (`create_coroutine_resume_function`). -/
def loweredPoll (f : LoweredFrame) (inp : PollInput) : PollOutcome × LoweredFrame :=
  match f.discr with
  | 0 =>
    match f.upvarSlot with
    | none => (.faultUninitOrAlias, f)
    | some upv =>
      let pinned := upv + 10
      let ptr : SelfRefPtr := { baseAddr := f.frameAddr, fieldOff := 0 }
      match inp with
      | .yieldPending =>
        (.pending,
         { f with
           discr            := DISCR_SUSPEND0
           s0_pinnedLocal   := some pinned
           s1_selfRef       := some ptr
           s2_scopeLive     := true
           s3_condDropFlag  := true
           overlapUnionSlot := some (pinned + 1) })
      | .advance v0 =>
        let log1 := if f.earlyDropCfg then f.dropLog ++ [.condGuard] else f.dropLog
        let flag1 := !f.earlyDropCfg
        (.pending,
         { f with
           discr            := DISCR_SUSPEND1
           s0_pinnedLocal   := some pinned
           s1_selfRef       := some ptr
           s2_scopeLive     := true
           s3_condDropFlag  := flag1
           overlapUnionSlot := some (pinned + v0 + 2)
           dropLog          := log1 })
      | .unwindPanic =>
        let log' := appendActiveDrops f.dropLog true true true
        (.panicked .bodyUnwind,
         { f with
           discr            := DISCR_POISONED
           upvarSlot        := none
           s0_pinnedLocal   := some pinned
           s1_selfRef       := none
           s2_scopeLive     := false
           s3_condDropFlag  := false
           overlapUnionSlot := none
           dropLog          := log' })
  | 1 => (.panicked .resumedAfterReturn, f)
  | 2 => (.panicked .resumedAfterPanic, f)
  | 3 => loweredResumeFrom0 f inp
  | 4 => loweredResumeFrom1 f inp
  | _ => (.faultUninitOrAlias, f)

/--
  Lowered `drop_in_place` glue (`create_coroutine_drop_shim`):
  - `Unresumed (0)` -> `drop_clean` (drops upvars only).
  - `Suspend0 (3)` / `Suspend1 (4)` -> drops live locals using elaborated drop flags.
  - `Returned (1)` / `Panicked (2)` -> default no-op return!
-/
def loweredDropGlue (f : LoweredFrame) : LoweredFrame :=
  match f.discr with
  | 0 =>
    let log' := appendActiveDrops f.dropLog false false f.upvarSlot.isSome
    { f with
      discr     := DISCR_RETURNED
      upvarSlot := none
      dropLog   := log' }
  | 3 =>
    -- `scopeGuard` is unconditionally live at `Suspend0` (discriminant-gated in `drop.rs` without
    -- a boolean drop flag), whereas `condGuard` and upvars use elaborated drop-flag / slot state.
    let log' := appendActiveDrops f.dropLog f.s3_condDropFlag true f.upvarSlot.isSome
    { f with
      discr            := DISCR_RETURNED
      upvarSlot        := none
      s1_selfRef       := none
      s2_scopeLive     := false
      s3_condDropFlag  := false
      overlapUnionSlot := none
      dropLog          := log' }
  | 4 =>
    let log' := appendActiveDrops f.dropLog f.s3_condDropFlag true f.upvarSlot.isSome
    { f with
      discr            := DISCR_RETURNED
      upvarSlot        := none
      s1_selfRef       := none
      s2_scopeLive     := false
      s3_condDropFlag  := false
      overlapUnionSlot := none
      dropLog          := log' }
  | _ =>
    -- `Returned (1)` and `Panicked (2)` fall through to `default_block = Return`.
    { f with discr := DISCR_RETURNED }

/-- Execute a finite action list on `LoweredFrame`. -/
def runLoweredActions (f : LoweredFrame) : List CoroAction → PollOutcome × LoweredFrame
  | [] => (.pending, f)
  | [act] =>
    match act with
    | .poll inp   => loweredPoll f inp
    | .cancelDrop => (.ready 0, loweredDropGlue f)
  | act :: rest =>
    let f' :=
      match act with
      | .poll inp   => (loweredPoll f inp).2
      | .cancelDrop => loweredDropGlue f
    runLoweredActions f' rest

/-! ### Simulation Relation and Soundness Theorems -/

/--
  Lockstep simulation invariant linking `SrcCoroState` and `LoweredFrame` pinned at `addr`.
  Includes constructive resource accounting (`ResourceInv`) inside the phase invariants.
-/
def SimRel (addr : Nat) (src : SrcCoroState) (tgt : LoweredFrame) : Prop :=
  tgt.frameAddr = addr ∧
  tgt.earlyDropCfg = src.earlyDropCond ∧
  tgt.dropLog = src.dropLog ∧
  ((if src.liveUpvar then 1 else 0) + countGuard .upvarGuard src.dropLog ≤ 1 ∧
   (if src.liveScope then 1 else 0) + countGuard .scopeGuard src.dropLog ≤ 1 ∧
   (if src.liveCond  then 1 else 0) + countGuard .condGuard  src.dropLog ≤ 1) ∧
  match src.phase with
  | .unresumed =>
    tgt.discr = DISCR_UNRESUMED ∧
    src.liveUpvar = true ∧
    src.liveScope = false ∧
    src.liveCond = false ∧
    src.selfBorrowLive = false ∧
    tgt.upvarSlot = some src.upvarVal ∧
    tgt.s2_scopeLive = false ∧
    tgt.s3_condDropFlag = false ∧
    tgt.overlapUnionSlot = none ∧
    countGuard .scopeGuard src.dropLog = 0 ∧
    countGuard .condGuard src.dropLog = 0
  | .suspended0 =>
    tgt.discr = DISCR_SUSPEND0 ∧
    src.liveUpvar = true ∧
    src.liveScope = true ∧
    src.selfBorrowLive = true ∧
    tgt.upvarSlot = some src.upvarVal ∧
    tgt.s0_pinnedLocal = some src.pinnedLocal ∧
    tgt.s1_selfRef = some { baseAddr := addr, fieldOff := 0 } ∧
    tgt.s2_scopeLive = true ∧
    tgt.s3_condDropFlag = src.liveCond ∧
    tgt.overlapUnionSlot = some src.tmp0
  | .suspended1 =>
    tgt.discr = DISCR_SUSPEND1 ∧
    src.liveUpvar = true ∧
    src.liveScope = true ∧
    src.selfBorrowLive = true ∧
    tgt.upvarSlot = some src.upvarVal ∧
    tgt.s0_pinnedLocal = some src.pinnedLocal ∧
    tgt.s1_selfRef = some { baseAddr := addr, fieldOff := 0 } ∧
    tgt.s2_scopeLive = true ∧
    tgt.s3_condDropFlag = src.liveCond ∧
    tgt.overlapUnionSlot = some src.tmp1
  | .returned =>
    tgt.discr = DISCR_RETURNED ∧
    src.liveUpvar = false ∧
    src.liveScope = false ∧
    src.liveCond = false ∧
    tgt.upvarSlot = none ∧
    tgt.s2_scopeLive = false ∧
    tgt.s3_condDropFlag = false
  | .panicked =>
    tgt.discr = DISCR_POISONED ∧
    src.liveUpvar = false ∧
    src.liveScope = false ∧
    src.liveCond = false ∧
    tgt.upvarSlot = none ∧
    tgt.s2_scopeLive = false ∧
    tgt.s3_condDropFlag = false
  | .dropped =>
    tgt.discr = DISCR_RETURNED ∧
    src.liveUpvar = false ∧
    src.liveScope = false ∧
    src.liveCond = false ∧
    tgt.upvarSlot = none ∧
    tgt.s2_scopeLive = false ∧
    tgt.s3_condDropFlag = false

private theorem countGuard_append (g : GuardId) (l1 l2 : DropLog) :
    countGuard g (l1 ++ l2) = countGuard g l1 + countGuard g l2 := by
  induction l1 with
  | nil =>
    change countGuard g l2 = 0 + countGuard g l2
    exact (Nat.zero_add _).symm
  | cons x xs ih =>
    cases hx : (x == g)
    · change (if (x == g) then countGuard g (xs ++ l2) + 1 else countGuard g (xs ++ l2)) =
             (if (x == g) then countGuard g xs + 1 else countGuard g xs) + countGuard g l2
      rw [hx]
      exact ih
    · change (if (x == g) then countGuard g (xs ++ l2) + 1 else countGuard g (xs ++ l2)) =
             (if (x == g) then countGuard g xs + 1 else countGuard g xs) + countGuard g l2
      rw [hx]
      simp only [↓reduceIte]
      rw [ih]
      exact (Nat.add_right_comm (countGuard g xs) 1 (countGuard g l2)).symm

private theorem bool_dichotomy (b : Bool) : b = false ∨ b = true := by
  cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem appendActiveDrops_bounds
    (log : DropLog) (bC bS bU lC lS lU : Bool)
    (hU : (if lU then 1 else 0) + countGuard .upvarGuard log ≤ 1)
    (hS : (if lS then 1 else 0) + countGuard .scopeGuard log ≤ 1)
    (hC : (if lC then 1 else 0) + countGuard .condGuard  log ≤ 1)
    (hCok : bC = false ∨ lC = true)
    (hSok : bS = false ∨ lS = true)
    (hUok : bU = false ∨ lU = true) :
    countGuard .upvarGuard (appendActiveDrops log bC bS bU) ≤ 1 ∧
    countGuard .scopeGuard (appendActiveDrops log bC bS bU) ≤ 1 ∧
    countGuard .condGuard  (appendActiveDrops log bC bS bU) ≤ 1 := by
  have c_upv_c : countGuard .upvarGuard [.condGuard] = 0 := rfl
  have c_upv_s : countGuard .upvarGuard [.scopeGuard] = 0 := rfl
  have c_upv_u : countGuard .upvarGuard [.upvarGuard] = 1 := rfl
  have c_scp_c : countGuard .scopeGuard [.condGuard] = 0 := rfl
  have c_scp_s : countGuard .scopeGuard [.scopeGuard] = 1 := rfl
  have c_scp_u : countGuard .scopeGuard [.upvarGuard] = 0 := rfl
  have c_cnd_c : countGuard .condGuard [.condGuard] = 1 := rfl
  have c_cnd_s : countGuard .condGuard [.scopeGuard] = 0 := rfl
  have c_cnd_u : countGuard .condGuard [.upvarGuard] = 0 := rfl
  unfold appendActiveDrops
  cases bC <;> cases bS <;> cases bU <;>
  simp only [↓reduceIte, Bool.false_eq_true, countGuard_append,
             c_upv_c, c_upv_s, c_upv_u, c_scp_c, c_scp_s, c_scp_u, c_cnd_c, c_cnd_s, c_cnd_u,
             Nat.add_zero]
  · exact ⟨Nat.le_trans (Nat.le_add_left _ _) hU,
           Nat.le_trans (Nat.le_add_left _ _) hS,
           Nat.le_trans (Nat.le_add_left _ _) hC⟩
  · refine ⟨?_, Nat.le_trans (Nat.le_add_left _ _) hS, Nat.le_trans (Nat.le_add_left _ _) hC⟩
    rcases hUok with hF | hT
    · cases hF
    · rw [hT] at hU; rw [Nat.add_comm]; exact hU
  · refine ⟨Nat.le_trans (Nat.le_add_left _ _) hU, ?_, Nat.le_trans (Nat.le_add_left _ _) hC⟩
    rcases hSok with hF | hT
    · cases hF
    · rw [hT] at hS; rw [Nat.add_comm]; exact hS
  · refine ⟨?_, ?_, Nat.le_trans (Nat.le_add_left _ _) hC⟩
    · rcases hUok with hF | hT
      · cases hF
      · rw [hT] at hU; rw [Nat.add_comm]; exact hU
    · rcases hSok with hF | hT
      · cases hF
      · rw [hT] at hS; rw [Nat.add_comm]; exact hS
  · refine ⟨Nat.le_trans (Nat.le_add_left _ _) hU, Nat.le_trans (Nat.le_add_left _ _) hS, ?_⟩
    rcases hCok with hF | hT
    · cases hF
    · rw [hT] at hC; rw [Nat.add_comm]; exact hC
  · refine ⟨?_, Nat.le_trans (Nat.le_add_left _ _) hS, ?_⟩
    · rcases hUok with hF | hT
      · cases hF
      · rw [hT] at hU; rw [Nat.add_comm]; exact hU
    · rcases hCok with hF | hT
      · cases hF
      · rw [hT] at hC; rw [Nat.add_comm]; exact hC
  · refine ⟨Nat.le_trans (Nat.le_add_left _ _) hU, ?_, ?_⟩
    · rcases hSok with hF | hT
      · cases hF
      · rw [hT] at hS; rw [Nat.add_comm]; exact hS
    · rcases hCok with hF | hT
      · cases hF
      · rw [hT] at hC; rw [Nat.add_comm]; exact hC
  · refine ⟨?_, ?_, ?_⟩
    · rcases hUok with hF | hT
      · cases hF
      · rw [hT] at hU; rw [Nat.add_comm]; exact hU
    · rcases hSok with hF | hT
      · cases hF
      · rw [hT] at hS; rw [Nat.add_comm]; exact hS
    · rcases hCok with hF | hT
      · cases hF
      · rw [hT] at hC; rw [Nat.add_comm]; exact hC

theorem init_sim (addr upvarVal : Nat) (earlyDrop : Bool) :
    SimRel addr (initSrc upvarVal earlyDrop) (initLowered addr upvarVal earlyDrop) := by
  refine ⟨rfl, rfl, rfl, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact Nat.le_refl 1
  · exact Nat.zero_le 1
  · exact Nat.zero_le 1
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Single-step poll simulation between source coroutine and `StateTransform` frame. -/
theorem poll_step_lockstep_sim
    (addr : Nat) (src : SrcCoroState) (tgt : LoweredFrame) (inp : PollInput)
    (h_not_dropped : src.phase ≠ .dropped)
    (h_sim : SimRel addr src tgt) :
    let (outS, src') := stepSrcPoll src inp
    let (outT, tgt') := loweredPoll tgt inp
    outT = outS ∧ outT ≠ .faultUninitOrAlias ∧ SimRel addr src' tgt' := by
  rcases h_sim with ⟨hAddr, hEarly, hLog, ⟨hIU, hIS, hIC⟩, hPhase⟩
  cases hPh : src.phase
  · -- .unresumed
    rw [hPh] at hPhase
    rcases hPhase with
      ⟨hDiscr, hLiveU, hLiveS, hLiveC, hBorrow, hUpv, hScopeT, hCondT, hUnion, hDropS0, hDropC0⟩
    rw [hLiveU] at hIU
    rw [hLiveS] at hIS
    rw [hLiveC] at hIC
    unfold stepSrcPoll loweredPoll
    rw [hPh, hDiscr, hUpv, hEarly, hLog]
    cases inp with
    | yieldPending =>
      refine ⟨rfl, ?_, ⟨hAddr, rfl, rfl, ⟨?_, ?_, ?_⟩, ?_⟩⟩
      · intro h; cases h
      · simpa [hLiveU] using hIU
      · simp [hDropS0]
      · simp [hDropC0]
      · exact ⟨rfl, hLiveU, rfl, rfl, rfl, rfl, hAddr ▸ rfl, rfl, rfl, rfl⟩
    | advance v0 =>
      cases hEarlyVal : src.earlyDropCond
      · refine ⟨rfl, ?_, ⟨hAddr, rfl, rfl, ⟨?_, ?_, ?_⟩, ?_⟩⟩
        · intro h; cases h
        · simpa [hLiveU] using hIU
        · simp [hDropS0]
        · simp [hDropC0]
        · exact ⟨rfl, hLiveU, rfl, rfl, rfl, rfl, hAddr ▸ rfl, rfl, rfl, rfl⟩
      · have c_cnd_c : countGuard .condGuard [.condGuard] = 1 := rfl
        have c_upv_c : countGuard .upvarGuard [.condGuard] = 0 := rfl
        have c_scp_c : countGuard .scopeGuard [.condGuard] = 0 := rfl
        refine ⟨rfl, ?_, ⟨hAddr, rfl, ?_, ⟨?_, ?_, ?_⟩, ?_⟩⟩
        · intro h; cases h
        · rfl
        · simpa [hLiveU, countGuard_append, c_upv_c] using hIU
        · simp [countGuard_append, c_scp_c, hDropS0]
        · simp [countGuard_append, c_cnd_c, hDropC0]
        · exact ⟨rfl, hLiveU, rfl, rfl, rfl, rfl, hAddr ▸ rfl, rfl, rfl, rfl⟩
    | unwindPanic =>
      have hIU' : (if true = true then 1 else 0) + countGuard .upvarGuard src.dropLog ≤ 1 := hIU
      have hIS' : (if true = true then 1 else 0) + countGuard .scopeGuard src.dropLog ≤ 1 := by
        simp [hDropS0]
      have hIC' : (if true = true then 1 else 0) + countGuard .condGuard src.dropLog ≤ 1 := by
        simp [hDropC0]
      have hB := appendActiveDrops_bounds src.dropLog true true true true true true
        hIU' hIS' hIC' (Or.inr rfl) (Or.inr rfl) (Or.inr rfl)
      rw [hLiveU]
      refine ⟨rfl, ?_, ⟨hAddr, rfl, rfl, ⟨?_, ?_, ?_⟩, ?_⟩⟩
      · intro h; cases h
      · simp [hB.1]
      · simp [hB.2.1]
      · simp [hB.2.2]
      · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · -- .suspended0
    rw [hPh] at hPhase
    rcases hPhase with ⟨hDiscr, hLiveU, hLiveS, hBorrow, hUpv, hPin, hPtr, hScopeT, hCondT, hUnion⟩
    have hEqAddr : natBeq addr addr = true := natBeq_refl addr
    have hEqZero : natBeq 0 0 = true := rfl
    unfold stepSrcPoll loweredPoll loweredResumeFrom0 readPinnedSelfRef
    rw [hPh, hBorrow, hDiscr, hPtr, hPin, hAddr, hUnion, hEarly, hCondT, hScopeT, hUpv, hLog]
    simp only [hEqAddr, hEqZero, Bool.and_self, ↓reduceIte, Bool.not_true, Bool.false_eq_true]
    cases inp with
    | yieldPending =>
      dsimp only
      refine ⟨(by first | rfl | trivial), ?_, ⟨(by first | rfl | exact hAddr), (by first | rfl | exact hEarly), (by first | rfl | exact hLog), ⟨hIU, hIS, hIC⟩, ?_⟩⟩
      · intro h; cases h
      · rw [hPh]
        exact ⟨hDiscr, hLiveU, hLiveS, hBorrow, hUpv, hPin, hPtr, hScopeT, hCondT, hUnion⟩
    | advance v0 =>
      dsimp only
      cases hEarlyVal : src.earlyDropCond
      · simp only [Bool.false_and, ↓reduceIte, Bool.false_eq_true]
        refine ⟨(by first | rfl | trivial), ?_, ⟨rfl, rfl, rfl, ⟨hIU, hIS, hIC⟩, ?_⟩⟩
        · intro h; cases h
        · exact ⟨rfl, hLiveU, hLiveS, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · cases hLC : src.liveCond
        · rw [hLC] at hIC
          simp only [Bool.true_and, ↓reduceIte, Bool.false_eq_true]
          refine ⟨(by first | rfl | trivial), ?_, ⟨rfl, rfl, rfl, ⟨hIU, hIS, hIC⟩, ?_⟩⟩
          · intro h; cases h
          · exact ⟨rfl, hLiveU, hLiveS, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        · rw [hLC] at hIC
          have c_cnd_c : countGuard .condGuard [.condGuard] = 1 := rfl
          have c_upv_c : countGuard .upvarGuard [.condGuard] = 0 := rfl
          have c_scp_c : countGuard .scopeGuard [.condGuard] = 0 := rfl
          simp only [Bool.true_and, ↓reduceIte]
          refine ⟨(by first | rfl | trivial), ?_, ⟨rfl, rfl, rfl, ⟨?_, ?_, ?_⟩, ?_⟩⟩
          · intro h; cases h
          · simpa [countGuard_append, c_upv_c] using hIU
          · simpa [countGuard_append, c_scp_c] using hIS
          · simpa [countGuard_append, c_cnd_c, Nat.add_comm] using hIC
          · exact ⟨rfl, hLiveU, hLiveS, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    | unwindPanic =>
      dsimp only
      have hB := appendActiveDrops_bounds src.dropLog src.liveCond src.liveScope src.liveUpvar
        src.liveCond src.liveScope src.liveUpvar
        hIU hIS hIC (bool_dichotomy _) (bool_dichotomy _) (bool_dichotomy _)
      rw [hLiveU, hLiveS]
      refine ⟨(by first | rfl | trivial), ?_, ⟨rfl, rfl, ?_, ⟨?_, ?_, ?_⟩, ?_⟩⟩
      · intro h; cases h
      · rfl
      · simpa [hLiveU, hLiveS] using hB.1
      · simpa [hLiveU, hLiveS] using hB.2.1
      · simpa [hLiveU, hLiveS] using hB.2.2
      · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · -- .suspended1
    rw [hPh] at hPhase
    rcases hPhase with ⟨hDiscr, hLiveU, hLiveS, hBorrow, hUpv, hPin, hPtr, hScopeT, hCondT, hUnion⟩
    have hEqAddr : natBeq addr addr = true := natBeq_refl addr
    have hEqZero : natBeq 0 0 = true := rfl
    unfold stepSrcPoll loweredPoll loweredResumeFrom1 readPinnedSelfRef
    rw [hPh, hBorrow, hDiscr, hPtr, hPin, hAddr, hUnion, hEarly, hCondT, hScopeT, hUpv, hLog]
    simp only [hEqAddr, hEqZero, Bool.and_self, ↓reduceIte, Bool.not_true, Bool.false_eq_true]
    cases inp with
    | yieldPending =>
      dsimp only
      refine ⟨(by first | rfl | trivial), ?_, ⟨(by first | rfl | exact hAddr), (by first | rfl | exact hEarly), (by first | rfl | exact hLog), ⟨hIU, hIS, hIC⟩, ?_⟩⟩
      · intro h; cases h
      · rw [hPh]
        exact ⟨hDiscr, hLiveU, hLiveS, hBorrow, hUpv, hPin, hPtr, hScopeT, hCondT, hUnion⟩
    | advance v1 =>
      dsimp only
      have hB := appendActiveDrops_bounds src.dropLog src.liveCond src.liveScope src.liveUpvar
        src.liveCond src.liveScope src.liveUpvar
        hIU hIS hIC (bool_dichotomy _) (bool_dichotomy _) (bool_dichotomy _)
      rw [hLiveU, hLiveS]
      refine ⟨(by first | rfl | trivial), ?_, ⟨rfl, rfl, ?_, ⟨?_, ?_, ?_⟩, ?_⟩⟩
      · intro h; cases h
      · rfl
      · simpa [hLiveU, hLiveS] using hB.1
      · simpa [hLiveU, hLiveS] using hB.2.1
      · simpa [hLiveU, hLiveS] using hB.2.2
      · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    | unwindPanic =>
      dsimp only
      have hB := appendActiveDrops_bounds src.dropLog src.liveCond src.liveScope src.liveUpvar
        src.liveCond src.liveScope src.liveUpvar
        hIU hIS hIC (bool_dichotomy _) (bool_dichotomy _) (bool_dichotomy _)
      rw [hLiveU, hLiveS]
      refine ⟨(by first | rfl | trivial), ?_, ⟨rfl, rfl, ?_, ⟨?_, ?_, ?_⟩, ?_⟩⟩
      · intro h; cases h
      · rfl
      · simpa [hLiveU, hLiveS] using hB.1
      · simpa [hLiveU, hLiveS] using hB.2.1
      · simpa [hLiveU, hLiveS] using hB.2.2
      · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · -- .returned
    rw [hPh] at hPhase
    rcases hPhase with ⟨hDiscr, hLiveU, hLiveS, hLiveC, hUpv, hScopeT, hCondT⟩
    unfold stepSrcPoll loweredPoll
    rw [hPh, hDiscr]
    simp only [DISCR_RETURNED]
    refine ⟨(by first | rfl | trivial), ?_, ⟨hAddr, hEarly, hLog, ⟨hIU, hIS, hIC⟩, ?_⟩⟩
    · intro h; cases h
    · rw [hPh]
      exact ⟨hDiscr, hLiveU, hLiveS, hLiveC, hUpv, hScopeT, hCondT⟩
  · -- .panicked
    rw [hPh] at hPhase
    rcases hPhase with ⟨hDiscr, hLiveU, hLiveS, hLiveC, hUpv, hScopeT, hCondT⟩
    unfold stepSrcPoll loweredPoll
    rw [hPh, hDiscr]
    simp only [DISCR_POISONED]
    refine ⟨(by first | rfl | trivial), ?_, ⟨hAddr, hEarly, hLog, ⟨hIU, hIS, hIC⟩, ?_⟩⟩
    · intro h; cases h
    · rw [hPh]
      exact ⟨hDiscr, hLiveU, hLiveS, hLiveC, hUpv, hScopeT, hCondT⟩
  · -- .dropped (contradicts `h_not_dropped`)
    exact absurd hPh h_not_dropped

/-- Single-step cancellation / `drop_in_place` simulation theorem. -/
theorem cancel_drop_lockstep_sim
    (addr : Nat) (src : SrcCoroState) (tgt : LoweredFrame)
    (h_sim : SimRel addr src tgt) :
    let src' := stepSrcDrop src
    let tgt' := loweredDropGlue tgt
    tgt'.dropLog = src'.dropLog ∧ SimRel addr src' tgt' := by
  rcases h_sim with ⟨hAddr, hEarly, hLog, ⟨hIU, hIS, hIC⟩, hPhase⟩
  cases hPh : src.phase
  · -- .unresumed
    rw [hPh] at hPhase
    rcases hPhase with ⟨hDiscr, hLiveU, hLiveS, hLiveC, _, hUpv, hScopeT, hCondT, _, _, _⟩
    have hB := appendActiveDrops_bounds src.dropLog false false src.liveUpvar
      src.liveCond src.liveScope src.liveUpvar
      hIU hIS hIC (Or.inl rfl) (Or.inl rfl) (bool_dichotomy _)
    unfold stepSrcDrop loweredDropGlue
    rw [hPh, hDiscr, hUpv, hLog, hLiveU, hLiveS, hLiveC, hScopeT, hCondT]
    refine ⟨rfl, ⟨hAddr, hEarly, rfl, ⟨?_, ?_, ?_⟩, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩⟩
    · simpa [hLiveU] using hB.1
    · simpa [hLiveU] using hB.2.1
    · simpa [hLiveU] using hB.2.2
  · -- .suspended0
    rw [hPh] at hPhase
    rcases hPhase with ⟨hDiscr, hLiveU, hLiveS, _, hUpv, _, _, _, hCondT, _⟩
    have hB := appendActiveDrops_bounds src.dropLog src.liveCond src.liveScope src.liveUpvar
      src.liveCond src.liveScope src.liveUpvar
      hIU hIS hIC (bool_dichotomy _) (bool_dichotomy _) (bool_dichotomy _)
    unfold stepSrcDrop loweredDropGlue
    rw [hPh, hDiscr, hUpv, hLog, hLiveU, hLiveS, hCondT]
    refine ⟨rfl, ⟨hAddr, hEarly, rfl, ⟨?_, ?_, ?_⟩, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩⟩
    · simpa [hLiveU, hLiveS] using hB.1
    · simpa [hLiveU, hLiveS] using hB.2.1
    · simpa [hLiveU, hLiveS] using hB.2.2
  · -- .suspended1
    rw [hPh] at hPhase
    rcases hPhase with ⟨hDiscr, hLiveU, hLiveS, _, hUpv, _, _, _, hCondT, _⟩
    have hB := appendActiveDrops_bounds src.dropLog src.liveCond src.liveScope src.liveUpvar
      src.liveCond src.liveScope src.liveUpvar
      hIU hIS hIC (bool_dichotomy _) (bool_dichotomy _) (bool_dichotomy _)
    unfold stepSrcDrop loweredDropGlue
    rw [hPh, hDiscr, hUpv, hLog, hLiveU, hLiveS, hCondT]
    refine ⟨rfl, ⟨hAddr, hEarly, rfl, ⟨?_, ?_, ?_⟩, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩⟩
    · simpa [hLiveU, hLiveS] using hB.1
    · simpa [hLiveU, hLiveS] using hB.2.1
    · simpa [hLiveU, hLiveS] using hB.2.2
  · -- .returned
    rw [hPh] at hPhase
    rcases hPhase with ⟨hDiscr, hLiveU, hLiveS, hLiveC, hUpv, hScopeT, hCondT⟩
    unfold stepSrcDrop loweredDropGlue
    rw [hPh, hDiscr]
    exact ⟨hLog, ⟨hAddr, hEarly, hLog, ⟨hIU, hIS, hIC⟩, ⟨rfl, hLiveU, hLiveS, hLiveC, hUpv, hScopeT, hCondT⟩⟩⟩
  · -- .panicked
    rw [hPh] at hPhase
    rcases hPhase with ⟨hDiscr, hLiveU, hLiveS, hLiveC, hUpv, hScopeT, hCondT⟩
    unfold stepSrcDrop loweredDropGlue
    rw [hPh, hDiscr]
    exact ⟨hLog, ⟨hAddr, hEarly, hLog, ⟨hIU, hIS, hIC⟩, ⟨rfl, hLiveU, hLiveS, hLiveC, hUpv, hScopeT, hCondT⟩⟩⟩
  · -- .dropped
    rw [hPh] at hPhase
    rcases hPhase with ⟨hDiscr, hLiveU, hLiveS, hLiveC, hUpv, hScopeT, hCondT⟩
    unfold stepSrcDrop loweredDropGlue
    rw [hPh, hDiscr]
    exact ⟨hLog, ⟨hAddr, hEarly, hLog, ⟨hIU, hIS, hIC⟩, ⟨rfl, hLiveU, hLiveS, hLiveC, hUpv, hScopeT, hCondT⟩⟩⟩

/--
  Safe Rust ownership discipline: `cancelDrop` consumes the pinned coroutine, so
  no `poll` occurs after `cancelDrop` (caller-unwind drops are `cancelDrop` at the end).
-/
def ValidActions : SrcPhase → List CoroAction → Bool
  | _, [] => true
  | ph, act :: rest =>
    match ph, act with
    | .dropped, .poll _ => false
    | .unresumed, .poll .yieldPending => ValidActions .suspended0 rest
    | .unresumed, .poll (.advance _) => ValidActions .suspended1 rest
    | .unresumed, .poll .unwindPanic => ValidActions .panicked rest
    | .suspended0, .poll .yieldPending => ValidActions .suspended0 rest
    | .suspended0, .poll (.advance _) => ValidActions .suspended1 rest
    | .suspended0, .poll .unwindPanic => ValidActions .panicked rest
    | .suspended1, .poll .yieldPending => ValidActions .suspended1 rest
    | .suspended1, .poll (.advance _) => ValidActions .returned rest
    | .suspended1, .poll .unwindPanic => ValidActions .panicked rest
    | .returned, .poll _ => ValidActions .returned rest
    | .panicked, .poll _ => ValidActions .panicked rest
    | _, .cancelDrop => ValidActions .dropped rest

private theorem stepSrcPoll_phase_matches (s : SrcCoroState) (inp : PollInput)
    (hB : s.phase = .suspended0 ∨ s.phase = .suspended1 → s.selfBorrowLive = true) :
    match s.phase, inp with
    | .unresumed, .yieldPending => (stepSrcPoll s inp).2.phase = .suspended0
    | .unresumed, .advance _    => (stepSrcPoll s inp).2.phase = .suspended1
    | .unresumed, .unwindPanic  => (stepSrcPoll s inp).2.phase = .panicked
    | .suspended0, .yieldPending => (stepSrcPoll s inp).2.phase = .suspended0
    | .suspended0, .advance _    => (stepSrcPoll s inp).2.phase = .suspended1
    | .suspended0, .unwindPanic  => (stepSrcPoll s inp).2.phase = .panicked
    | .suspended1, .yieldPending => (stepSrcPoll s inp).2.phase = .suspended1
    | .suspended1, .advance _    => (stepSrcPoll s inp).2.phase = .returned
    | .suspended1, .unwindPanic  => (stepSrcPoll s inp).2.phase = .panicked
    | .returned, _   => (stepSrcPoll s inp).2.phase = .returned
    | .panicked, _   => (stepSrcPoll s inp).2.phase = .panicked
    | .dropped, _    => (stepSrcPoll s inp).2.phase = .dropped := by
  cases hPh : s.phase <;> cases inp <;> unfold stepSrcPoll <;> rw [hPh]
  all_goals first
    | rfl
    | exact hPh
    | (have hb := hB (Or.inl hPh); simp only [hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte] <;> first | rfl | exact hPh)
    | (have hb := hB (Or.inr hPh); simp only [hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte] <;> first | rfl | exact hPh)

private theorem validActions_tail_after_poll
    (s : SrcCoroState) (inp : PollInput) (rest : List CoroAction)
    (hNotDrop : s.phase ≠ .dropped)
    (hBorrow : s.phase = .suspended0 ∨ s.phase = .suspended1 → s.selfBorrowLive = true)
    (hValid : ValidActions s.phase (.poll inp :: rest) = true) :
    ValidActions (stepSrcPoll s inp).2.phase rest = true := by
  have hm := stepSrcPoll_phase_matches s inp hBorrow
  cases hPh : s.phase <;> cases inp
  all_goals
    try exact absurd hPh hNotDrop
    try (rw [hPh] at hValid hm; unfold ValidActions at hValid; rw [hm]; exact hValid)

private theorem simRel_selfBorrow (addr : Nat) (src : SrcCoroState) (tgt : LoweredFrame)
    (h : SimRel addr src tgt) :
    src.phase = .suspended0 ∨ src.phase = .suspended1 → src.selfBorrowLive = true := by
  intro hp
  rcases h with ⟨_, _, _, _, hPh⟩
  rcases hp with h0 | h1
  · rw [h0] at hPh; exact hPh.2.2.2.1
  · rw [h1] at hPh; exact hPh.2.2.2.1

/-- Inductive trace lockstep simulation and `NoDoubleDrop` invariance. -/
theorem execTrace_lockstep_sim
    (addr : Nat) (src : SrcCoroState) (tgt : LoweredFrame) (acts : List CoroAction)
    (h_sim : SimRel addr src tgt)
    (h_valid : ValidActions src.phase acts = true) :
    let (outS, src') := runSrcActions src acts
    let (outT, tgt') := runLoweredActions tgt acts
    outT = outS ∧
    tgt'.dropLog = src'.dropLog ∧
    NoDoubleDrop tgt'.dropLog ∧
    SimRel addr src' tgt' := by
  induction acts generalizing src tgt with
  | nil =>
    rcases h_sim with ⟨hAddr, hEarly, hLog, ⟨hIU, hIS, hIC⟩, hPhase⟩
    have hND : NoDoubleDrop tgt.dropLog := by
      rw [hLog]
      exact ⟨Nat.le_trans (Nat.le_add_left _ _) hIU,
             Nat.le_trans (Nat.le_add_left _ _) hIS,
             Nat.le_trans (Nat.le_add_left _ _) hIC⟩
    exact ⟨rfl, hLog, hND, ⟨hAddr, hEarly, hLog, ⟨hIU, hIS, hIC⟩, hPhase⟩⟩
  | cons act rest ih =>
    cases rest with
    | nil =>
      cases act with
      | poll inp =>
        have hNotDrop : src.phase ≠ .dropped := by
          intro hD
          rw [hD] at h_valid
          cases h_valid
        have hStep := poll_step_lockstep_sim addr src tgt inp hNotDrop h_sim
        dsimp only at hStep
        rcases hStep with ⟨hOut, _, hSim'⟩
        rcases hSim' with ⟨hAddr', hEarly', hLog', ⟨hIU', hIS', hIC'⟩, hPh'⟩
        have hND : NoDoubleDrop (loweredPoll tgt inp).2.dropLog := by
          rw [hLog']
          exact ⟨Nat.le_trans (Nat.le_add_left _ _) hIU',
                 Nat.le_trans (Nat.le_add_left _ _) hIS',
                 Nat.le_trans (Nat.le_add_left _ _) hIC'⟩
        exact ⟨hOut, hLog', hND, ⟨hAddr', hEarly', hLog', ⟨hIU', hIS', hIC'⟩, hPh'⟩⟩
      | cancelDrop =>
        have hDrop := cancel_drop_lockstep_sim addr src tgt h_sim
        dsimp only at hDrop
        rcases hDrop with ⟨hLog', hSim'⟩
        rcases hSim' with ⟨hAddr', hEarly', hLog'', ⟨hIU', hIS', hIC'⟩, hPh'⟩
        have hND : NoDoubleDrop (loweredDropGlue tgt).dropLog := by
          rw [hLog'']
          exact ⟨Nat.le_trans (Nat.le_add_left _ _) hIU',
                 Nat.le_trans (Nat.le_add_left _ _) hIS',
                 Nat.le_trans (Nat.le_add_left _ _) hIC'⟩
        exact ⟨rfl, hLog', hND, ⟨hAddr', hEarly', hLog'', ⟨hIU', hIS', hIC'⟩, hPh'⟩⟩
    | cons act2 rest2 =>
      cases act with
      | poll inp =>
        have hNotDrop : src.phase ≠ .dropped := by
          intro hD
          rw [hD] at h_valid
          cases h_valid
        have hStep := poll_step_lockstep_sim addr src tgt inp hNotDrop h_sim
        dsimp only at hStep
        rcases hStep with ⟨_, _, hSim'⟩
        have hValid' := validActions_tail_after_poll src inp (act2 :: rest2)
          hNotDrop (simRel_selfBorrow addr src tgt h_sim) h_valid
        exact ih (stepSrcPoll src inp).2 (loweredPoll tgt inp).2 hSim' hValid'
      | cancelDrop =>
        have hDrop := cancel_drop_lockstep_sim addr src tgt h_sim
        dsimp only at hDrop
        rcases hDrop with ⟨_, hSim'⟩
        have hValid' : ValidActions (stepSrcDrop src).phase (act2 :: rest2) = true := by
          have hDropPh : (stepSrcDrop src).phase = .dropped := by
            cases hPh : src.phase <;> unfold stepSrcDrop <;> rw [hPh] <;> rfl
          rw [hDropPh]
          cases hPh : src.phase <;> rw [hPh] at h_valid <;> exact h_valid
        exact ih (stepSrcDrop src) (loweredDropGlue tgt) hSim' hValid'

/--
  Direct safety corollary: every reachable lowered state along any valid trace satisfies
  `NoDoubleDrop`, including panic unwind followed by caller `drop_in_place`.
-/
theorem no_double_drop_invariant
    (addr upvarVal : Nat) (earlyDrop : Bool) (acts : List CoroAction)
    (h_valid : ValidActions .unresumed acts = true) :
    NoDoubleDrop (runLoweredActions (initLowered addr upvarVal earlyDrop) acts).2.dropLog := by
  have h := execTrace_lockstep_sim addr (initSrc upvarVal earlyDrop)
    (initLowered addr upvarVal earlyDrop) acts (init_sim addr upvarVal earlyDrop) h_valid
  exact h.2.2.1

/--
  Pinning necessity witness: moving a suspended `!Unpin` self-referential frame from
  `addr` to `addr + 64` invalidates the self-borrow pointer `_s1` on the next poll.
-/
theorem moving_suspended_self_ref_frame_faults (addr upvarVal : Nat) (earlyDrop : Bool) :
    let suspended := (loweredPoll (initLowered addr upvarVal earlyDrop) .yieldPending).2
    let relocated := { suspended with frameAddr := addr + 64 }
    (loweredPoll relocated (.advance 7)).1 = .faultUninitOrAlias := by
  intro suspended relocated
  have hneq : natBeq addr (addr + 64) = false := by
    have hlt : addr ≠ addr + 64 := Nat.ne_of_lt (Nat.lt_add_of_pos_right (by decide : 0 < 64))
    cases h : natBeq addr (addr + 64)
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true h) hlt
  change (loweredPoll relocated (.advance 7)).1 = .faultUninitOrAlias
  have hDiscr : relocated.discr = 3 := rfl
  have hPtr : relocated.s1_selfRef = some { baseAddr := addr, fieldOff := 0 } := rfl
  have hPin : relocated.s0_pinnedLocal = some (upvarVal + 10) := rfl
  have hFaddr : relocated.frameAddr = addr + 64 := rfl
  unfold loweredPoll
  rw [hDiscr]
  dsimp only
  unfold loweredResumeFrom0 readPinnedSelfRef
  rw [hPtr, hPin, hFaddr]
  dsimp only
  rw [hneq]
  rfl

/-! ### Sharpness Counterexample 1 (CE1): `noalias` on `!Unpin` `Pin<&mut Self>` Miscompiles -/

/-- Provenance-tagged pointer modeling LLVM `LangRef.md` `based_on` rules. -/
structure ProvPtr where
  addr : Nat
  prov : Nat
  deriving DecidableEq, Repr

/-- LLVM `based_on` provenance relation across function activations (`prov₁` vs `prov₂`). -/
def basedOn (p argPtr : ProvPtr) : Bool :=
  p.prov = argPtr.prov

/--
  Two-activation self-referential coroutine memory trace:
  - Poll #1 (`prov₁ = 1`): writes `s0 := 15`, stores `s1 := { addr := baseAddr, prov := 1 }`.
  - Poll #2 (`prov₂ = 2`, new `Pin<&mut Self>` arg `selfPtr₂` with fresh provenance `2`):
    1. Reads `r := s1` (`r.prov = 1 ≠ 2`, so `basedOn r selfPtr₂ = false`);
    2. Mutates `*(selfPtr₂.s0) := 99`;
    3. Dereferences `*r` (reading `s0`).
  If `Pin<&mut Self>` is erroneously annotated `noalias` (`noaliasFlag = true`), an
  alias-blind store-load optimizer commutes step (3) before step (2) because
  `basedOn r selfPtr₂ = false` and `*(selfPtr₂.s0)` is modified via `selfPtr₂` — yielding
  stale `15` instead of `99` AND triggering LLVM `noalias` UB (`LangRef.md` L1512-1519).
-/
def runActivation2Mem (selfPtr₂ r : ProvPtr) (noaliasFlag : Bool) : Nat × Bool :=
  let s0Initial := 15
  let s0Updated := 99
  let aliasesSameAddr := (r.addr = selfPtr₂.addr)
  let basedOnArg := basedOn r selfPtr₂
  let noAliasUB := noaliasFlag && aliasesSameAddr && !basedOnArg
  let observedRead :=
    if noaliasFlag && !basedOnArg then
      -- Alias-blind GVN/DSE forwards the pre-store load across the store via `selfPtr₂`.
      s0Initial
    else
      if aliasesSameAddr then s0Updated else s0Initial
  (observedRead, noAliasUB)

/-- True operational execution (`!Unpin` suppresses `noalias`, so `noaliasFlag = false`). -/
def evalResumedPollTrue : Nat × Bool :=
  let selfPtr₂ : ProvPtr := { addr := 4096, prov := 2 }
  let storedSelfRef : ProvPtr := { addr := 4096, prov := 1 }
  runActivation2Mem selfPtr₂ storedSelfRef false

/-- Miscompiled execution when `noalias` is emitted on `!Unpin` `Pin<&mut Self>`. -/
def evalResumedPollNoAliasOpt : Nat × Bool :=
  let selfPtr₂ : ProvPtr := { addr := 4096, prov := 2 }
  let storedSelfRef : ProvPtr := { addr := 4096, prov := 1 }
  runActivation2Mem selfPtr₂ storedSelfRef true

theorem ce1_noalias_on_self_ref_pin_miscompiles :
    evalResumedPollNoAliasOpt.1 = 15 ∧
    evalResumedPollTrue.1 = 99 ∧
    evalResumedPollNoAliasOpt.1 ≠ evalResumedPollTrue.1 ∧
    evalResumedPollNoAliasOpt.2 = true := by
  refine ⟨rfl, rfl, ?_, rfl⟩
  intro h
  cases h

/-! ### Sharpness Counterexample 2 (CE2): Omitting `Panicked (2)` Poison Transition -/

/-- Faulty variant of `loweredResumeFrom0` that omits `SetDiscriminant(DISCR_POISONED)` on unwind. -/
def loweredResumeFrom0MissingPoison (f : LoweredFrame) (inp : PollInput) :
    PollOutcome × LoweredFrame :=
  match readPinnedSelfRef f, f.overlapUnionSlot with
  | some pinned, some _tmp0 =>
    match inp with
    | .yieldPending => (.pending, f)
    | .advance v0 =>
      let log1 :=
        if f.earlyDropCfg && f.s3_condDropFlag then f.dropLog ++ [.condGuard] else f.dropLog
      let flag1 := if f.earlyDropCfg then false else f.s3_condDropFlag
      (.pending,
       { f with
         discr            := DISCR_SUSPEND1
         s3_condDropFlag  := flag1
         overlapUnionSlot := some (pinned + v0 + 2)
         dropLog          := log1 })
    | .unwindPanic =>
      -- BUG: cleanup drops live guards and frees variant payload `overlapUnionSlot := none`,
      -- yet omits `discr := DISCR_POISONED` (leaving `discr = DISCR_SUSPEND0`)!
      let log' := appendActiveDrops f.dropLog f.s3_condDropFlag f.s2_scopeLive f.upvarSlot.isSome
      (.panicked .bodyUnwind,
       { f with
         discr            := f.discr
         upvarSlot        := none
         s1_selfRef       := none
         s2_scopeLive     := false
         s3_condDropFlag  := false
         overlapUnionSlot := none
         dropLog          := log' })
  | _, _ => (.faultUninitOrAlias, f)

/-- Faulty `poll` identical to `loweredPoll` except using `loweredResumeFrom0MissingPoison`. -/
def loweredPollMissingPoison (f : LoweredFrame) (inp : PollInput) :
    PollOutcome × LoweredFrame :=
  match f.discr with
  | 3 => loweredResumeFrom0MissingPoison f inp
  | _ => loweredPoll f inp

/--
  CE2a: Omitting `SetDiscriminant(2)` (`Panicked`) on unwind leaves `discr = DISCR_SUSPEND0`,
  so the caller's automatic stack-unwind `drop_in_place` (`loweredDropGlue`) re-executes the
  `Suspend0` drop path and double-drops `scopeGuard` (`count = 2`, violating `NoDoubleDrop`),
  whereas sound `StateTransform` sets `discr = 2` and makes `loweredDropGlue` a no-op (`count = 1`).
-/
theorem ce2a_missing_poison_double_drops (addr upvarVal : Nat) :
    let f0 := initLowered addr upvarVal false
    let f1 := (loweredPollMissingPoison f0 .yieldPending).2
    let fUnwindBug := (loweredPollMissingPoison f1 .unwindPanic).2
    let fAfterCallerDropBug := loweredDropGlue fUnwindBug
    let fSoundUnwind := (loweredPoll (loweredPoll f0 .yieldPending).2 .unwindPanic).2
    let fSoundAfterDrop := loweredDropGlue fSoundUnwind
    countGuard .scopeGuard fAfterCallerDropBug.dropLog = 2 ∧
    ¬ NoDoubleDrop fAfterCallerDropBug.dropLog ∧
    countGuard .scopeGuard fSoundAfterDrop.dropLog = 1 ∧
    NoDoubleDrop fSoundAfterDrop.dropLog := by
  have hEq : natBeq addr addr = true := natBeq_refl addr
  have hZero : natBeq 0 0 = true := rfl
  intro f0 f1 fUnwindBug fAfterCallerDropBug fSoundUnwind fSoundAfterDrop
  have hf1 : f1 =
      { frameAddr := addr, discr := 3, upvarSlot := some upvarVal, earlyDropCfg := false,
        s0_pinnedLocal := some (upvarVal + 10),
        s1_selfRef := some { baseAddr := addr, fieldOff := 0 }, s2_scopeLive := true,
        s3_condDropFlag := true, overlapUnionSlot := some (upvarVal + 10 + 1), dropLog := [] } := rfl
  have hfUnwindBug : fUnwindBug =
      { frameAddr := addr, discr := 3, upvarSlot := none, earlyDropCfg := false,
        s0_pinnedLocal := some (upvarVal + 10), s1_selfRef := none, s2_scopeLive := false,
        s3_condDropFlag := false, overlapUnionSlot := none,
        dropLog := [.condGuard, .scopeGuard, .upvarGuard] } := by
    change (loweredPollMissingPoison f1 .unwindPanic).2 = _
    rw [hf1]
    unfold loweredPollMissingPoison loweredResumeFrom0MissingPoison readPinnedSelfRef appendActiveDrops
    dsimp
    rw [hEq, hZero]
    simp only [Bool.and_self, ↓reduceIte]
  have hBugLog : fAfterCallerDropBug.dropLog =
      [.condGuard, .scopeGuard, .upvarGuard, .scopeGuard] := by
    change (loweredDropGlue fUnwindBug).dropLog = _
    rw [hfUnwindBug]
    rfl
  have hfSound1 : (loweredPoll f0 .yieldPending).2 =
      { frameAddr := addr, discr := 3, upvarSlot := some upvarVal, earlyDropCfg := false,
        s0_pinnedLocal := some (upvarVal + 10),
        s1_selfRef := some { baseAddr := addr, fieldOff := 0 }, s2_scopeLive := true,
        s3_condDropFlag := true, overlapUnionSlot := some (upvarVal + 10 + 1), dropLog := [] } := rfl
  have hfSoundUnwind : fSoundUnwind =
      { frameAddr := addr, discr := 2, upvarSlot := none, earlyDropCfg := false,
        s0_pinnedLocal := some (upvarVal + 10), s1_selfRef := none, s2_scopeLive := false,
        s3_condDropFlag := false, overlapUnionSlot := none,
        dropLog := [.condGuard, .scopeGuard, .upvarGuard] } := by
    change (loweredPoll (loweredPoll f0 .yieldPending).2 .unwindPanic).2 = _
    rw [hfSound1]
    unfold loweredPoll loweredResumeFrom0 readPinnedSelfRef appendActiveDrops
    dsimp
    rw [hEq, hZero]
    simp only [Bool.and_self, ↓reduceIte]
  have hSoundLog : fSoundAfterDrop.dropLog = [.condGuard, .scopeGuard, .upvarGuard] := by
    change (loweredDropGlue fSoundUnwind).dropLog = _
    rw [hfSoundUnwind]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hBugLog]; rfl
  · intro hND
    rw [hBugLog] at hND
    have hLe : (2 : Nat) ≤ 1 := hND.2.1
    cases hLe with
    | step h2 => cases h2
  · rw [hSoundLog]; rfl
  · rw [hSoundLog]
    exact ⟨Nat.le_refl 1, Nat.le_refl 1, Nat.le_refl 1⟩

/--
  CE2b: Omitting `SetDiscriminant(2)` (`Panicked`) on unwind allows a caught-unwind re-poll to
  re-enter `Suspend0`'s resume block (`discr = 3`) and fault on uninitialized/moved-out
  `overlapUnionSlot = none`, whereas sound `StateTransform` traps with `.panicked .resumedAfterPanic`.
-/
theorem ce2b_missing_poison_repoll_reads_uninit_payload (addr upvarVal : Nat) :
    let f0 := initLowered addr upvarVal false
    let f1 := (loweredPollMissingPoison f0 .yieldPending).2
    let fUnwindBug := (loweredPollMissingPoison f1 .unwindPanic).2
    let repollBug := loweredPollMissingPoison fUnwindBug (.advance 5)
    let fSoundUnwind := (loweredPoll (loweredPoll f0 .yieldPending).2 .unwindPanic).2
    let repollSound := loweredPoll fSoundUnwind (.advance 5)
    repollBug.1 = .faultUninitOrAlias ∧
    repollSound.1 = .panicked .resumedAfterPanic := by
  have hEq : natBeq addr addr = true := natBeq_refl addr
  have hZero : natBeq 0 0 = true := rfl
  intro f0 f1 fUnwindBug repollBug fSoundUnwind repollSound
  have hf1 : f1 =
      { frameAddr := addr, discr := 3, upvarSlot := some upvarVal, earlyDropCfg := false,
        s0_pinnedLocal := some (upvarVal + 10),
        s1_selfRef := some { baseAddr := addr, fieldOff := 0 }, s2_scopeLive := true,
        s3_condDropFlag := true, overlapUnionSlot := some (upvarVal + 10 + 1), dropLog := [] } := rfl
  have hfUnwindBug : fUnwindBug =
      { frameAddr := addr, discr := 3, upvarSlot := none, earlyDropCfg := false,
        s0_pinnedLocal := some (upvarVal + 10), s1_selfRef := none, s2_scopeLive := false,
        s3_condDropFlag := false, overlapUnionSlot := none,
        dropLog := [.condGuard, .scopeGuard, .upvarGuard] } := by
    change (loweredPollMissingPoison f1 .unwindPanic).2 = _
    rw [hf1]
    unfold loweredPollMissingPoison loweredResumeFrom0MissingPoison readPinnedSelfRef appendActiveDrops
    dsimp
    rw [hEq, hZero]
    simp only [Bool.and_self, ↓reduceIte]
  have hfSound1 : (loweredPoll f0 .yieldPending).2 =
      { frameAddr := addr, discr := 3, upvarSlot := some upvarVal, earlyDropCfg := false,
        s0_pinnedLocal := some (upvarVal + 10),
        s1_selfRef := some { baseAddr := addr, fieldOff := 0 }, s2_scopeLive := true,
        s3_condDropFlag := true, overlapUnionSlot := some (upvarVal + 10 + 1), dropLog := [] } := rfl
  have hfSoundUnwind : fSoundUnwind =
      { frameAddr := addr, discr := 2, upvarSlot := none, earlyDropCfg := false,
        s0_pinnedLocal := some (upvarVal + 10), s1_selfRef := none, s2_scopeLive := false,
        s3_condDropFlag := false, overlapUnionSlot := none,
        dropLog := [.condGuard, .scopeGuard, .upvarGuard] } := by
    change (loweredPoll (loweredPoll f0 .yieldPending).2 .unwindPanic).2 = _
    rw [hfSound1]
    unfold loweredPoll loweredResumeFrom0 readPinnedSelfRef appendActiveDrops
    dsimp
    rw [hEq, hZero]
    simp only [Bool.and_self, ↓reduceIte]
  constructor
  · change (loweredPollMissingPoison fUnwindBug (.advance 5)).1 = .faultUninitOrAlias
    rw [hfUnwindBug]
    rfl
  · change (loweredPoll fSoundUnwind (.advance 5)).1 = .panicked .resumedAfterPanic
    rw [hfSoundUnwind]
    rfl

end CoroutineStateTransformRefinement

#print axioms CoroutineStateTransformRefinement.noDoubleDropB_iff
#print axioms CoroutineStateTransformRefinement.init_sim
#print axioms CoroutineStateTransformRefinement.poll_step_lockstep_sim
#print axioms CoroutineStateTransformRefinement.cancel_drop_lockstep_sim
#print axioms CoroutineStateTransformRefinement.execTrace_lockstep_sim
#print axioms CoroutineStateTransformRefinement.no_double_drop_invariant
#print axioms CoroutineStateTransformRefinement.moving_suspended_self_ref_frame_faults
#print axioms CoroutineStateTransformRefinement.ce1_noalias_on_self_ref_pin_miscompiles
#print axioms CoroutineStateTransformRefinement.ce2a_missing_poison_double_drops
#print axioms CoroutineStateTransformRefinement.ce2b_missing_poison_repoll_reads_uninit_payload
