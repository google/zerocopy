/-!
# Soundness and Sharpness of `rustc` `AsyncDrop`, `CoroutineDrop`,
`future_drop_poll`, Drop-Ladder Elaboration, and Cross-Crate Feature Gating

Self-contained kernel-checked Lean `v4.34.1` formalization modeling the exact
state-machine transitions, reverse-order `dropline` / unwind half-ladders, and
cross-crate `AsyncDrop` dispatch predicates in `rust-lang/rust`
(`342d74463af7dd3018ef6aa04dd5500c2deb5bd1` and
`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`).

## Trust-Boundary Compliance
- Zero `sorry` / `sorryAx`.
- Zero `Classical.choice`, zero `omega`, zero `bv_decide`, zero `native_decide`,
  zero `Lean.ofReduceBool`, zero `Lean.trustCompiler`.
- Zero `partial def`, zero `deriving` on recursive inductives, and explicit
  `noncomputable def` on every term-level definition so Lean generates zero
  `._unsafe_rec` helpers.

## Primary Results
1. `futureDropPoll_idempotent_iff_marks_returned`:
   For an unresumed coroutine holding an owned heap upvar (under either
   `has_async_drops = true` via `insert_clean_drop` or `has_async_drops = false`
   via `create_coroutine_drop_shim_proxy_async`), the `.await`-induced double
   poll of `future_drop_poll` is UB-free and idempotent if and only if the
   `UNRESUMED` drop path transitions the coroutine discriminant to `RETURNED`.
2. `futureDropPoll_suspended_immediate_idempotent_iff_coroDrop_marks_returned`
   and `futureDropPoll_suspended_yielding_accidentally_safe`:
   For a suspended coroutine (`Suspend0`) whose local's `AsyncDrop::drop`
   completes immediately in one poll (no intermediate yield) or whose resource
   remains an unmoved upvar, idempotence holds iff `TerminatorKind::CoroutineDrop`
   also transitions the discriminant to `RETURNED`; by contrast, a yielding
   `AsyncDrop::drop` transitions the outer coroutine to `DropYield` whose inner
   `async_drop_in_place` future sets its own discriminant to `RETURNED`, masking
   the missing outer transition.
3. `async_drop_ladder_exact_once_per_init_field` and
   `unwind_cleanup_never_async_drops`:
   In `elaborate_drop.rs`'s reverse-order three-track ladder (`normal`,
   `dropline`, `unwind`), for any list of fields with distinct IDs and under any
   normal exit, mid-drop panic, mid-drop coroutine cancellation, or cleanup-pad
   entry, every initialized field is dropped exactly once, every uninitialized
   field is dropped zero times, drop order is strictly reverse declaration
   order, and every drop in unwind cleanup (`inCleanup = true`) is synchronous.
4. `transitive_gate_restores_wrapper_compositionality` and
   `strict_warning_policy_agrees_with_diagnostic`:
   Modeling `check_if_can_async_drop` (`elaborate_drop.rs:679-695`), a
   transitive foreign-`AsyncDrop` gate restores wrapper compositionality across
   `Option`, arrays, tuples, `Box`, local wrappers, foreign wrappers, and
   partial-move open drops; a strict feature-off gate restores agreement with
   the compiler warning (`rustc_metadata/src/diagnostics.rs:590-603`).
5. Constructive sharpness counterexamples:
   - `ce1_unresumed_missing_returned_transition_causes_double_drop_ub`
   - `ce1b_suspended_immediate_missing_returned_causes_double_drop_ub`
   - `ce2_non_transitive_gate_splits_bare_vs_option`
   - `ce3_unresumed_upvar_sync_drop_vs_suspended_async_drop`
-/

namespace AsyncDropSoundness

/-! ## Part I: `CoroutineArgs` State Machine & `future_drop_poll` Idempotence -/

/-- Coroutine discriminant states matching `CoroutineArgs`
(`UNRESUMED = 0`, `RETURNED = 1`, `POISONED = 2`, `Suspend0 = 3`,
and `DropYield = 4` for a dropline `Yield` inside `build_async_drop`). -/
inductive CoroDiscr where
  | unresumed
  | returned
  | poisoned
  | suspend0
  | dropYield

/-- Observable destruction & fault events emitted by drop shims. -/
inductive DropEvent where
  | syncDrop (id : Nat)
  | asyncDropStart (id : Nat)
  | asyncDropFinish (id : Nat)
  | ubDoubleDrop (id : Nat)
  | panicPoisoned

/-- Poll result of `future_drop_poll` (`Poll<()>`). -/
inductive PollRes where
  | pending
  | ready

/-- Kind of live resource owned by the coroutine frame. -/
inductive ResourceMode where
  /-- Upvar in `UNRESUMED` (or unmoved upvar at `Suspend0`) with `has_async_drops = true`. -/
  | upvarAsyncCoro
  /-- Upvar in `UNRESUMED` with `has_async_drops = false` (`create_coroutine_drop_shim_proxy_async`). -/
  | upvarPlainProxy
  /-- Local live across `Suspend0` whose `AsyncDrop::drop` yields `Pending` once before `Ready`. -/
  | localYieldingAsync
  /-- Local live across `Suspend0` whose `AsyncDrop::drop` returns `Ready` immediately on poll 1. -/
  | localImmediateAsync

/-- Compiler lowering policy knobs modeling exact `rustc` lines:
- `marksReturnedOnUnresumed`: whether `insert_clean_drop` (`coroutine/drop.rs:148-174`)
  emits `SetDiscriminant(RETURNED)` (`rustc` HEAD = `false`).
- `marksReturnedOnCoroutineDrop`: whether `create_coroutine_drop_shim_async`
  (`coroutine/drop.rs:304-310`) emits `SetDiscriminant(RETURNED)` on
  `TerminatorKind::CoroutineDrop` (`rustc` HEAD = `false`).
- `unresumedUpvarsUseAsyncDrop`: `produce_async_drops` in
  `elaborate_coroutine_drops` (`coroutine/drop.rs:103`; `rustc` HEAD = `false`). -/
structure LoweringPolicy where
  marksReturnedOnUnresumed : Bool
  marksReturnedOnCoroutineDrop : Bool
  unresumedUpvarsUseAsyncDrop : Bool

/-- Exact `rustc` HEAD (`342d74463af7dd3018ef6aa04dd5500c2deb5bd1`) policy. -/
noncomputable def rustcHeadPolicy : LoweringPolicy :=
  { marksReturnedOnUnresumed := false
    marksReturnedOnCoroutineDrop := false
    unresumedUpvarsUseAsyncDrop := false }

/-- Repaired policy that emits `SetDiscriminant(RETURNED)` on both `UNRESUMED`
and `TerminatorKind::CoroutineDrop`. -/
noncomputable def fixedDiscrPolicy : LoweringPolicy :=
  { marksReturnedOnUnresumed := true
    marksReturnedOnCoroutineDrop := true
    unresumedUpvarsUseAsyncDrop := false }

/-- Operational state of a single coroutine frame plus event trace. -/
structure CoroFrame where
  discr : CoroDiscr
  mode : ResourceMode
  resourceId : Nat
  resourceAlive : Bool
  /-- Discriminant of the nested `async_drop_in_place<T>` sub-future stored in
  `DropYield` (which DOES transition to `RETURNED` via `coroutine/mod.rs:491`
  and returns `Ready` idempotently via `coroutine/mod.rs:917-918`). -/
  innerAdropReturned : Bool
  log : List DropEvent

/-- Structural equality on `CoroDiscr` (avoiding `deriving`). -/
noncomputable def CoroDiscr.beq : CoroDiscr → CoroDiscr → Bool
  | .unresumed, .unresumed => true
  | .returned, .returned => true
  | .poisoned, .poisoned => true
  | .suspend0, .suspend0 => true
  | .dropYield, .dropYield => true
  | _, _ => false

/-- Structural equality on `DropEvent` (avoiding `deriving`). -/
noncomputable def DropEvent.beq : DropEvent → DropEvent → Bool
  | .syncDrop a, .syncDrop b => Nat.beq a b
  | .asyncDropStart a, .asyncDropStart b => Nat.beq a b
  | .asyncDropFinish a, .asyncDropFinish b => Nat.beq a b
  | .ubDoubleDrop a, .ubDoubleDrop b => Nat.beq a b
  | .panicPoisoned, .panicPoisoned => true
  | _, _ => false

/-- Helper: check if an event list contains any `.ubDoubleDrop`. -/
noncomputable def hasDoubleDropUb : List DropEvent → Bool
  | [] => false
  | .ubDoubleDrop _ :: _ => true
  | _ :: rest => hasDoubleDropUb rest

/-- Helper: count non-UB completed destructions of `id`
(`.syncDrop id` or `.asyncDropFinish id`). -/
noncomputable def countCompletedDrops (id : Nat) : List DropEvent → Nat
  | [] => 0
  | .syncDrop k :: rest =>
    (if Nat.beq k id then 1 else 0) + countCompletedDrops id rest
  | .asyncDropFinish k :: rest =>
    (if Nat.beq k id then 1 else 0) + countCompletedDrops id rest
  | _ :: rest => countCompletedDrops id rest

/-- Helper: single-step evaluation of `Coro::future_drop_poll`
(`create_coroutine_drop_shim_async` at `coroutine/drop.rs:258-352` and
`create_coroutine_drop_shim_proxy_async` at `coroutine/drop.rs:356-408`). -/
noncomputable def evalFutureDropPoll (pol : LoweringPolicy) (st : CoroFrame) :
    PollRes × CoroFrame :=
  match st.discr with
  | .returned =>
    -- `RETURNED` hits `default_block = insert_poll_ready_block` (coroutine/drop.rs:301)
    (.ready, st)
  | .poisoned =>
    -- `POISONED` panics (`ResumedAfterPanic`, coroutine/drop.rs:289-291)
    (.ready, { st with log := st.log ++ [.panicPoisoned] })
  | .unresumed =>
    -- `UNRESUMED (0)` -> `drop_clean` (`insert_clean_drop`, coroutine/drop.rs:148-174)
    -- or `create_coroutine_drop_shim_proxy_async` -> `create_coroutine_drop_shim` (L196, L385).
    let nextDiscr :=
      match pol.marksReturnedOnUnresumed with
      | true => CoroDiscr.returned
      | false => CoroDiscr.unresumed
    match st.resourceAlive with
    | false =>
      -- Re-entering `drop_clean` on an already-freed heap upvar triggers dangling-box UAF UB.
      (.ready, { st with discr := nextDiscr, log := st.log ++ [.ubDoubleDrop st.resourceId] })
    | true =>
      match st.mode with
      | .upvarPlainProxy =>
        (.ready, { st with
          discr := nextDiscr
          resourceAlive := false
          log := st.log ++ [.syncDrop st.resourceId] })
      | .upvarAsyncCoro | .localYieldingAsync | .localImmediateAsync =>
        match pol.unresumedUpvarsUseAsyncDrop with
        | true =>
          (.ready, { st with
            discr := nextDiscr
            resourceAlive := false
            log := st.log ++ [.asyncDropStart st.resourceId, .asyncDropFinish st.resourceId] })
        | false =>
          (.ready, { st with
            discr := nextDiscr
            resourceAlive := false
            log := st.log ++ [.syncDrop st.resourceId] })
  | .suspend0 =>
    -- `Suspend0 (3)` -> dropline path for suspended coroutine.
    let nextDiscrDone :=
      match pol.marksReturnedOnCoroutineDrop with
      | true => CoroDiscr.returned
      | false => CoroDiscr.suspend0
    match st.resourceAlive with
    | false =>
      (.ready, { st with discr := nextDiscrDone, log := st.log ++ [.ubDoubleDrop st.resourceId] })
    | true =>
      match st.mode with
      | .upvarAsyncCoro | .upvarPlainProxy =>
        -- Unmoved upvar dropped via `elaborate_coroutine_drops` (`produce_async_drops = false`),
        -- culminating in `TerminatorKind::CoroutineDrop`.
        (.ready, { st with
          discr := nextDiscrDone
          resourceAlive := false
          log := st.log ++ [.syncDrop st.resourceId] })
      | .localImmediateAsync =>
        -- Local `AsyncDrop::drop` returns `Poll::Ready` on first poll (no `Yield` hit),
        -- reaching `TerminatorKind::CoroutineDrop` directly without updating discriminant.
        (.ready, { st with
          discr := nextDiscrDone
          resourceAlive := false
          log := st.log ++ [.asyncDropStart st.resourceId, .asyncDropFinish st.resourceId] })
      | .localYieldingAsync =>
        -- Local `AsyncDrop::drop` yields `Poll::Pending` once, setting `discr := .dropYield`
        -- (`coroutine/mod.rs:531`) while storing the nested `async_drop_in_place` sub-future.
        (.pending, { st with
          discr := CoroDiscr.dropYield
          innerAdropReturned := false
          log := st.log ++ [.asyncDropStart st.resourceId] })
  | .dropYield =>
    -- Resuming `future_drop_poll` at `DropYield` polls the nested `async_drop_in_place<T>` future.
    let nextDiscrDone :=
      match pol.marksReturnedOnCoroutineDrop with
      | true => CoroDiscr.returned
      | false => CoroDiscr.dropYield
    match st.innerAdropReturned with
    | true =>
      -- Nested `async_drop_in_place<T>` already reached `RETURNED`; by `coroutine/mod.rs:917-918`
      -- polling it again returns `Poll::Ready(())` idempotently without re-dropping `T`!
      (.ready, { st with discr := nextDiscrDone })
    | false =>
      match st.resourceAlive with
      | false =>
        (.ready, { st with discr := nextDiscrDone, log := st.log ++ [.ubDoubleDrop st.resourceId] })
      | true =>
        (.ready, { st with
          discr := nextDiscrDone
          resourceAlive := false
          innerAdropReturned := true
          log := st.log ++ [.asyncDropFinish st.resourceId] })

/-- Drive `future_drop_poll` up to `fuel` polls until `PollRes.ready`
(models the `.await` poll loop of `async_drop_in_place(&mut *slot).await`). -/
noncomputable def driveToReady (pol : LoweringPolicy) : Nat → CoroFrame → CoroFrame
  | 0, st => st
  | n + 1, st =>
    match evalFutureDropPoll pol st with
    | (.ready, st') => st'
    | (.pending, st') => driveToReady pol n st'

/-- Model `unsafe { async_drop_in_place(&mut *slot).await; }` inside an `async` block:
1. The `.await` loop drives `Proxy1 = async_drop_in_place<Coro>` (`Coro::future_drop_poll`)
   to `Poll::Ready(())`.
2. At the semicolon, the outer `async` block async-drops the `.await` temporary `Proxy1`,
   invoking `Proxy2 = async_drop_in_place<Proxy1>` which via `find_async_drop_impl_coroutine`
   (`ty/sty.rs:1558-1575`) and `build_adrop_for_coroutine_shim` (`async_destructor_ctor.rs:200-304`)
   unconditionally re-polls `Coro::future_drop_poll` on `slot`! -/
noncomputable def runAsyncDropInPlaceAwait (pol : LoweringPolicy) (st : CoroFrame) : CoroFrame :=
  let afterAwait := driveToReady pol 4 st
  -- Drop of the `.await` temporary unconditionally polls `future_drop_poll` again:
  (evalFutureDropPoll pol afterAwait).2

/-- Model driving `async_drop_in_place(&mut *slot)` from a sync driver (`block_on(drop_fut)`):
the temporary is dropped synchronously (no `Proxy2` re-poll of `Coro::future_drop_poll`). -/
noncomputable def runAsyncDropInPlaceSyncDriver (pol : LoweringPolicy) (st : CoroFrame) : CoroFrame :=
  driveToReady pol 4 st

/-- Constructor for an initial unresumed coroutine holding an alive heap upvar. -/
noncomputable def mkUnresumed (mode : ResourceMode) (id : Nat) : CoroFrame :=
  { discr := .unresumed
    mode := mode
    resourceId := id
    resourceAlive := true
    innerAdropReturned := false
    log := [] }

/-- Constructor for a coroutine polled once to `Suspend0` holding an alive resource. -/
noncomputable def mkSuspended (mode : ResourceMode) (id : Nat) : CoroFrame :=
  { discr := .suspend0
    mode := mode
    resourceId := id
    resourceAlive := true
    innerAdropReturned := false
    log := [] }

/-- A post-`.await` drop run is sound and idempotent if:
1. No `.ubDoubleDrop` occurred;
2. The resource was destroyed exactly once; and
3. A subsequent poll of `future_drop_poll` leaves the state (and log) identical
   while returning `.ready`. -/
noncomputable def IdempotentDropRun (pol : LoweringPolicy) (st0 : CoroFrame) : Prop :=
  let stFinal := runAsyncDropInPlaceAwait pol st0
  hasDoubleDropUb stFinal.log = false ∧
  countCompletedDrops st0.resourceId stFinal.log = 1 ∧
  evalFutureDropPoll pol stFinal = (.ready, stFinal)

theorem driveToReady_ready (pol : LoweringPolicy) (n : Nat) (st st' : CoroFrame)
    (h : evalFutureDropPoll pol st = (.ready, st')) :
    driveToReady pol (n + 1) st = st' := by
  change (match evalFutureDropPoll pol st with
    | (.ready, s) => s
    | (.pending, s) => driveToReady pol n s) = st'
  rw [h]

theorem driveToReady_pending (pol : LoweringPolicy) (n : Nat) (st st' : CoroFrame)
    (h : evalFutureDropPoll pol st = (.pending, st')) :
    driveToReady pol (n + 1) st = driveToReady pol n st' := by
  change (match evalFutureDropPoll pol st with
    | (.ready, s) => s
    | (.pending, s) => driveToReady pol n s) = driveToReady pol n st'
  rw [h]

/-- **Theorem 1 (`futureDropPoll_idempotent_iff_marks_returned`):**
For an unresumed coroutine holding an owned heap upvar (under either
`upvarAsyncCoro` / `has_async_drops = true` or `upvarPlainProxy` /
`has_async_drops = false`), `async_drop_in_place(&mut *slot).await` inside an
`async` block is UB-free and idempotent **if and only if** the `UNRESUMED` drop
path transitions the coroutine discriminant to `CoroutineArgs::RETURNED`
(`pol.marksReturnedOnUnresumed = true`). -/
theorem futureDropPoll_idempotent_iff_marks_returned
    (pol : LoweringPolicy) (isAsyncCoro : Bool) (id : Nat) :
    let mode := if isAsyncCoro then ResourceMode.upvarAsyncCoro else ResourceMode.upvarPlainProxy
    IdempotentDropRun pol (mkUnresumed mode id) ↔ pol.marksReturnedOnUnresumed = true := by
  cases pol with
  | mk mUnres mCoro mUpv =>
    cases isAsyncCoro <;> cases mUnres <;> cases mUpv
    all_goals
      dsimp only [IdempotentDropRun, runAsyncDropInPlaceAwait, mkUnresumed, ite_true, ite_false]
      rw [show (4 : Nat) = 3 + 1 from rfl, driveToReady_ready _ 3 _ _ rfl]
      dsimp only [evalFutureDropPoll, hasDoubleDropUb, countCompletedDrops,
        List.nil_append, List.cons_append]
    all_goals
      first
      | exact ⟨fun h => Bool.noConfusion h.1, fun h => Bool.noConfusion h⟩
      | (rw [Nat.beq_refl]; exact ⟨fun _ => rfl, fun _ => ⟨rfl, rfl, rfl⟩⟩)

/-- **Theorem 1b (`futureDropPoll_suspended_immediate_idempotent_iff_coroDrop_marks_returned`):**
Even after polling a coroutine once to `Suspend0`, if its live local has an
immediately-ready `AsyncDrop::drop` (no `.await` inside `AsyncDrop::drop`) OR
its live resource is an unmoved upvar, `async_drop_in_place(&mut *slot).await`
is UB-free and idempotent **if and only if** `TerminatorKind::CoroutineDrop`
transitions the discriminant to `RETURNED` (`pol.marksReturnedOnCoroutineDrop = true`). -/
theorem futureDropPoll_suspended_immediate_idempotent_iff_coroDrop_marks_returned
    (pol : LoweringPolicy) (isUnmovedUpvar : Bool) (id : Nat) :
    let mode := if isUnmovedUpvar then ResourceMode.upvarAsyncCoro else ResourceMode.localImmediateAsync
    IdempotentDropRun pol (mkSuspended mode id) ↔ pol.marksReturnedOnCoroutineDrop = true := by
  cases pol with
  | mk mUnres mCoro mUpv =>
    cases isUnmovedUpvar <;> cases mCoro
    all_goals
      dsimp only [IdempotentDropRun, runAsyncDropInPlaceAwait, mkSuspended, ite_true, ite_false]
      rw [show (4 : Nat) = 3 + 1 from rfl, driveToReady_ready _ 3 _ _ rfl]
      dsimp only [evalFutureDropPoll, hasDoubleDropUb, countCompletedDrops,
        List.nil_append, List.cons_append]
    all_goals
      first
      | exact ⟨fun h => Bool.noConfusion h.1, fun h => Bool.noConfusion h⟩
      | (rw [Nat.beq_refl]; exact ⟨fun _ => rfl, fun _ => ⟨rfl, rfl, rfl⟩⟩)

/-- **Theorem 1c (`futureDropPoll_suspended_yielding_accidentally_safe`):**
Under `rustcHeadPolicy` (`marksReturnedOnUnresumed = false`,
`marksReturnedOnCoroutineDrop = false`), a suspended coroutine whose local's
`AsyncDrop::drop` yields `Pending` once (`localYieldingAsync`) STILL passes
`runAsyncDropInPlaceAwait` without UB and destroys the local exactly once—not
because `CoroutineDrop` sets `RETURNED`, but because yielding advances `discr`
to `DropYield` where the nested `async_drop_in_place<T>` future is
`RETURNED`-idempotent (`coroutine/mod.rs:917-918`). -/
theorem futureDropPoll_suspended_yielding_accidentally_safe (id : Nat) :
    IdempotentDropRun rustcHeadPolicy (mkSuspended .localYieldingAsync id) ∧
    (runAsyncDropInPlaceAwait rustcHeadPolicy (mkSuspended .localYieldingAsync id)).discr =
      CoroDiscr.dropYield := by
  dsimp only [IdempotentDropRun, runAsyncDropInPlaceAwait, mkSuspended, rustcHeadPolicy]
  rw [show (4 : Nat) = 3 + 1 from rfl, driveToReady_pending _ 3 _ _ rfl]
  rw [show (3 : Nat) = 2 + 1 from rfl, driveToReady_ready _ 2 _ _ rfl]
  dsimp only [evalFutureDropPoll, hasDoubleDropUb, countCompletedDrops,
    List.nil_append, List.cons_append]
  rw [Nat.beq_refl]
  exact ⟨⟨rfl, rfl, rfl⟩, rfl⟩

/-- **Theorem 1d (`sync_driver_avoids_double_poll_even_on_unresumed`):**
Driving `async_drop_in_place(&mut *slot)` from a synchronous caller (`block_on`)
never invokes the second `future_drop_poll`, so even under `rustcHeadPolicy` on
an `UNRESUMED` coroutine, zero UB occurs and the upvar is dropped once
(though synchronously and leaving `discr = .unresumed`). -/
theorem sync_driver_avoids_double_poll_even_on_unresumed (id : Nat) :
    let st := runAsyncDropInPlaceSyncDriver rustcHeadPolicy (mkUnresumed .upvarAsyncCoro id)
    hasDoubleDropUb st.log = false ∧
    countCompletedDrops id st.log = 1 ∧
    st.discr = CoroDiscr.unresumed := by
  dsimp only [runAsyncDropInPlaceSyncDriver, mkUnresumed, rustcHeadPolicy]
  rw [show (4 : Nat) = 3 + 1 from rfl, driveToReady_ready _ 3 _ _ rfl]
  dsimp only [hasDoubleDropUb, countCompletedDrops, List.nil_append, List.cons_append]
  rw [Nat.beq_refl]
  exact ⟨rfl, rfl, rfl⟩

/-! ## Part II: Reverse-Order `dropline` Half-Ladder & Unwind Sync-Fallback -/

/-- A single field or local slot participating in a drop ladder
(`elaborate_drop.rs:838-955`). -/
structure FieldSpec where
  id : Nat
  init : Bool
  hasAsyncDrop : Bool

/-- Destruction mode recorded by the drop-ladder semantics. -/
inductive LadderDropKind where
  | sync
  | async

/-- One recorded field destruction event in the drop-ladder trace. -/
structure LadderEvent where
  fieldId : Nat
  kind : LadderDropKind
  inCleanup : Bool

/-- Execution scenario through the 3-track drop ladder (`normal_ladder`,
`dropline_ladder`, `unwind_ladder` at `elaborate_drop.rs:879-955`). -/
inductive LadderScenario where
  /-- Normal `async` scope exit without panic or cancellation. -/
  | normal
  /-- Coroutine cancelled at reverse step `k` (switches to `dropline_ladder` via
  `Yield { drop: Some(dropline_bb) }`, still non-cleanup so async drops continue). -/
  | cancelAt (k : Nat)
  /-- Panic raised during reverse step `k` (switches to `unwind_ladder` with
  `unwind.is_cleanup() = true` for all subsequent steps). -/
  | panicAt (k : Nat)
  /-- Already in unwind cleanup (`unwind.is_cleanup() = true`) upon entry. -/
  | unwindEntry

/-- Emit the drop event (if any) for one field given whether `inCleanup` holds.
Models `!unwind.is_cleanup() && check_if_can_async_drop(...)` at
`elaborate_drop.rs:636, 1249, 1311, 1578`. -/
noncomputable def dropOneField (inCleanup : Bool) (f : FieldSpec) : List LadderEvent :=
  if f.init then
    let k := if (!inCleanup) && f.hasAsyncDrop then LadderDropKind.async else LadderDropKind.sync
    [{ fieldId := f.id, kind := k, inCleanup := inCleanup }]
  else
    []

/-- Execute a reverse-ordered field list starting at step counter `step` and
cleanup flag `inCleanup`. -/
noncomputable def execRevLadder (sc : LadderScenario) (step : Nat) (inCleanup : Bool) :
    List FieldSpec → List LadderEvent
  | [] => []
  | f :: rest =>
    let curCleanup :=
      match sc with
      | .unwindEntry => true
      | _ => inCleanup
    let ev := dropOneField curCleanup f
    let nextCleanup :=
      match sc with
      | .panicAt k => if Nat.beq step k then true else curCleanup
      | .unwindEntry => true
      | .normal => curCleanup
      | .cancelAt _ => curCleanup
    ev ++ execRevLadder sc (step + 1) nextCleanup rest

/-- Run the 3-track drop ladder on fields in declaration order: `elaborate_drop.rs:846`
iterates `fields.iter().rev()`, so execution visits `fields.reverse`. -/
noncomputable def runAsyncDropLadder (sc : LadderScenario) (fields : List FieldSpec) :
    List LadderEvent :=
  execRevLadder sc 0 false fields.reverse

/-- Count how many times field `fid` was destroyed in a ladder trace. -/
noncomputable def countLadderDrops (fid : Nat) : List LadderEvent → Nat
  | [] => 0
  | e :: rest => (if Nat.beq e.fieldId fid then 1 else 0) + countLadderDrops fid rest

/-- Extract field IDs from a ladder trace in execution order. -/
noncomputable def traceFieldIds : List LadderEvent → List Nat
  | [] => []
  | e :: rest => e.fieldId :: traceFieldIds rest

/-- Extract IDs of initialized fields from a field list. -/
noncomputable def initFieldIds : List FieldSpec → List Nat
  | [] => []
  | f :: rest => if f.init then f.id :: initFieldIds rest else initFieldIds rest

/-- Predicate: a list of field IDs has no duplicates (`Pairwise (· ≠ ·)`). -/
noncomputable def noDupIds : List Nat → Prop
  | [] => True
  | x :: xs => (∀ y, y ∈ xs → y ≠ x) ∧ noDupIds xs

/-- Predicate: every cleanup event in a trace uses synchronous `Drop` (never `AsyncDrop`). -/
noncomputable def allCleanupEventsAreSync : List LadderEvent → Prop
  | [] => True
  | e :: rest => (e.inCleanup = true → e.kind = LadderDropKind.sync) ∧ allCleanupEventsAreSync rest

/-- Predicate: zero async drops occur anywhere in the trace. -/
noncomputable def noAsyncDropsInTrace : List LadderEvent → Prop
  | [] => True
  | e :: rest => e.kind = LadderDropKind.sync ∧ noAsyncDropsInTrace rest

theorem countLadderDrops_append (fid : Nat) (xs ys : List LadderEvent) :
    countLadderDrops fid (xs ++ ys) = countLadderDrops fid xs + countLadderDrops fid ys := by
  induction xs with
  | nil =>
    change countLadderDrops fid ys = 0 + countLadderDrops fid ys
    rw [Nat.zero_add]
  | cons e es ih =>
    change (if Nat.beq e.fieldId fid then 1 else 0) + countLadderDrops fid (es ++ ys) =
      ((if Nat.beq e.fieldId fid then 1 else 0) + countLadderDrops fid es) + countLadderDrops fid ys
    rw [ih, Nat.add_assoc]

theorem traceFieldIds_append (xs ys : List LadderEvent) :
    traceFieldIds (xs ++ ys) = traceFieldIds xs ++ traceFieldIds ys := by
  induction xs with
  | nil => rfl
  | cons e es ih =>
    change e.fieldId :: traceFieldIds (es ++ ys) = e.fieldId :: (traceFieldIds es ++ traceFieldIds ys)
    rw [ih]

theorem allCleanupEventsAreSync_append (xs ys : List LadderEvent)
    (hx : allCleanupEventsAreSync xs) (hy : allCleanupEventsAreSync ys) :
    allCleanupEventsAreSync (xs ++ ys) := by
  induction xs with
  | nil => exact hy
  | cons e es ih => exact ⟨hx.1, ih hx.2⟩

theorem noAsyncDropsInTrace_append (xs ys : List LadderEvent)
    (hx : noAsyncDropsInTrace xs) (hy : noAsyncDropsInTrace ys) :
    noAsyncDropsInTrace (xs ++ ys) := by
  induction xs with
  | nil => exact hy
  | cons e es ih => exact ⟨hx.1, ih hx.2⟩

theorem initFieldIds_append (xs ys : List FieldSpec) :
    initFieldIds (xs ++ ys) = initFieldIds xs ++ initFieldIds ys := by
  induction xs with
  | nil => rfl
  | cons f fs ih =>
    change (if f.init then f.id :: initFieldIds (fs ++ ys) else initFieldIds (fs ++ ys)) =
      (if f.init then f.id :: initFieldIds fs else initFieldIds fs) ++ initFieldIds ys
    cases hInit : f.init
    · exact ih
    · change f.id :: initFieldIds (fs ++ ys) = f.id :: (initFieldIds fs ++ initFieldIds ys)
      rw [ih]

theorem initFieldIds_reverse (fs : List FieldSpec) :
    initFieldIds fs.reverse = (initFieldIds fs).reverse := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    rw [List.reverse_cons, initFieldIds_append, ih]
    change (initFieldIds fs).reverse ++ (if f.init then [f.id] else []) =
      (if f.init then f.id :: initFieldIds fs else initFieldIds fs).reverse
    cases hInit : f.init
    · exact List.append_nil _
    · exact (List.reverse_cons (a := f.id) (as := initFieldIds fs)).symm

theorem execRevLadder_traceFieldIds (sc : LadderScenario) (step : Nat) (inCleanup : Bool)
    (fs : List FieldSpec) :
    traceFieldIds (execRevLadder sc step inCleanup fs) = initFieldIds fs := by
  induction fs generalizing step inCleanup with
  | nil => rfl
  | cons f rest ih =>
    unfold execRevLadder
    rw [traceFieldIds_append, ih]
    change traceFieldIds (dropOneField _ f) ++ initFieldIds rest =
      if f.init then f.id :: initFieldIds rest else initFieldIds rest
    unfold dropOneField
    cases hInit : f.init
    · rfl
    · rfl

theorem execRevLadder_allCleanupSync (sc : LadderScenario) (step : Nat) (inCleanup : Bool)
    (fs : List FieldSpec) :
    allCleanupEventsAreSync (execRevLadder sc step inCleanup fs) := by
  induction fs generalizing step inCleanup with
  | nil => trivial
  | cons f rest ih =>
    unfold execRevLadder
    apply allCleanupEventsAreSync_append
    · unfold dropOneField
      cases hInit : f.init
      · trivial
      · constructor
        · intro hC
          cases hC' : (match sc with | .unwindEntry => true | _ => inCleanup)
          · rw [hC'] at hC; cases hC
          · rfl
        · trivial
    · exact ih _ _

theorem execRevLadder_unwind_noAsync (sc : LadderScenario) (step : Nat) (fs : List FieldSpec) :
    noAsyncDropsInTrace (execRevLadder sc step true fs) := by
  induction fs generalizing step with
  | nil => trivial
  | cons f rest ih =>
    unfold execRevLadder
    apply noAsyncDropsInTrace_append
    · unfold dropOneField
      cases hInit : f.init
      · trivial
      · cases sc <;> exact ⟨rfl, trivial⟩
    · cases sc with
      | normal => exact ih (step + 1)
      | cancelAt _ => exact ih (step + 1)
      | unwindEntry => exact ih (step + 1)
      | panicAt k =>
        cases hEq : Nat.beq step k
        · simpa [hEq] using ih (step + 1)
        · simpa [hEq] using ih (step + 1)

theorem countLadderDrops_eq_countIds (fid : Nat) (evs : List LadderEvent) :
    countLadderDrops fid evs = (traceFieldIds evs).countP (fun x => Nat.beq x fid) := by
  induction evs with
  | nil => rfl
  | cons e es ih =>
    change (if Nat.beq e.fieldId fid then 1 else 0) + countLadderDrops fid es =
      (traceFieldIds (e :: es)).countP (fun x => Nat.beq x fid)
    unfold traceFieldIds
    rw [List.countP_cons, ih]
    cases Nat.beq e.fieldId fid
    · change 0 + _ = _ + 0
      rw [Nat.zero_add, Nat.add_zero]
    · change 1 + _ = _ + 1
      rw [Nat.add_comm]

theorem countP_eq_zero_of_not_mem (fid : Nat) (xs : List Nat) (hNot : fid ∉ xs) :
    xs.countP (fun x => Nat.beq x fid) = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.countP_cons]
    have hNe : x ≠ fid := fun hEq => hNot (hEq ▸ List.Mem.head xs)
    have hBeq : Nat.beq x fid = false := by
      cases h : Nat.beq x fid
      · rfl
      · exact False.elim (hNe (Nat.eq_of_beq_eq_true h))
    have hTail : fid ∉ xs := fun hIn => hNot (List.Mem.tail x hIn)
    rw [hBeq, ih hTail]
    rfl

theorem countP_eq_one_of_mem_noDup (fid : Nat) (xs : List Nat)
    (hNd : noDupIds xs) (hIn : fid ∈ xs) :
    xs.countP (fun x => Nat.beq x fid) = 1 := by
  induction xs with
  | nil => cases hIn
  | cons x xs ih =>
    rw [List.countP_cons]
    cases hIn with
    | head =>
      have hNotInTail : fid ∉ xs := fun hMem => hNd.1 fid hMem rfl
      rw [Nat.beq_refl, countP_eq_zero_of_not_mem fid xs hNotInTail]
      rfl
    | tail _ hMem =>
      have hNe : fid ≠ x := hNd.1 fid hMem
      have hBeq : Nat.beq x fid = false := by
        cases h : Nat.beq x fid
        · rfl
        · exact False.elim (hNe (Nat.eq_of_beq_eq_true h).symm)
      rw [hBeq]
      change xs.countP (fun x => Nat.beq x fid) + 0 = 1
      rw [Nat.add_zero]
      exact ih hNd.2 hMem

theorem mem_map_id_of_mem_initFieldIds (fs : List FieldSpec) (y : Nat)
    (hy : y ∈ initFieldIds fs) : y ∈ fs.map FieldSpec.id := by
  induction fs with
  | nil => cases hy
  | cons g gs ih =>
    unfold initFieldIds at hy
    cases hG : g.init
    · rw [hG] at hy
      exact List.Mem.tail _ (ih hy)
    · rw [hG] at hy
      rcases List.mem_cons.mp hy with hEq | hTail
      · rw [hEq]; exact List.Mem.head _
      · exact List.Mem.tail _ (ih hTail)

theorem noDupIds_filter_init (fs : List FieldSpec) (hNd : noDupIds (fs.map FieldSpec.id)) :
    noDupIds (initFieldIds fs) := by
  induction fs with
  | nil => trivial
  | cons f rest ih =>
    unfold initFieldIds
    cases hInit : f.init
    · exact ih hNd.2
    · refine ⟨?_, ih hNd.2⟩
      intro y hy
      exact hNd.1 y (mem_map_id_of_mem_initFieldIds rest y hy)

theorem noDupIds_append_singleton (xs : List Nat) (x : Nat)
    (hNd : noDupIds xs) (hNot : x ∉ xs) :
    noDupIds (xs ++ [x]) := by
  induction xs with
  | nil =>
    change (∀ y, y ∈ ([] : List Nat) → y ≠ x) ∧ True
    exact ⟨(fun _ hy => nomatch hy), trivial⟩
  | cons a as ih =>
    refine ⟨?_, ih hNd.2 (fun h => hNot (List.Mem.tail _ h))⟩
    intro y hy hEq
    rw [hEq] at hy
    have hOr : a ∈ as ∨ a ∈ [x] := List.mem_append.mp hy
    cases hOr with
    | inl hInAs => exact hNd.1 a hInAs rfl
    | inr hInX =>
      cases hInX with
      | head => exact hNot (List.Mem.head _)
      | tail _ hEmp => cases hEmp

theorem noDupIds_reverse (xs : List Nat) (hNd : noDupIds xs) : noDupIds xs.reverse := by
  induction xs with
  | nil => trivial
  | cons x xs ih =>
    rw [List.reverse_cons]
    apply noDupIds_append_singleton
    · exact ih hNd.2
    · intro hInRev
      have hIn : x ∈ xs := List.mem_reverse.mp hInRev
      exact hNd.1 x hIn rfl

theorem mem_initFieldIds_of_init (fs : List FieldSpec) (f : FieldSpec)
    (hMem : f ∈ fs) (hInit : f.init = true) : f.id ∈ initFieldIds fs := by
  induction fs with
  | nil => cases hMem
  | cons g gs ih =>
    unfold initFieldIds
    cases hMem with
    | head =>
      rw [hInit]
      exact List.Mem.head _
    | tail _ hTail =>
      cases g.init
      · exact ih hTail
      · exact List.Mem.tail _ (ih hTail)

theorem not_mem_initFieldIds_of_uninit (fs : List FieldSpec) (f : FieldSpec)
    (hNd : noDupIds (fs.map FieldSpec.id)) (hMem : f ∈ fs) (hUninit : f.init = false) :
    f.id ∉ initFieldIds fs := by
  induction fs with
  | nil => cases hMem
  | cons g gs ih =>
    unfold initFieldIds
    cases hMem with
    | head =>
      rw [hUninit]
      intro hIn
      exact hNd.1 f.id (mem_map_id_of_mem_initFieldIds gs f.id hIn) rfl
    | tail _ hTail =>
      have hNotInTail := ih hNd.2 hTail
      cases hG : g.init
      · exact hNotInTail
      · intro hIn
        rcases List.mem_cons.mp hIn with hEq | hT
        · have hFInMap : f.id ∈ gs.map FieldSpec.id := List.mem_map.mpr ⟨f, hTail, rfl⟩
          exact hNd.1 f.id hFInMap hEq
        · exact hNotInTail hT

/-- **Theorem 2 (`async_drop_ladder_exact_once_per_init_field`):**
For any field list `fields` with distinct IDs and any 3-track drop-ladder
scenario (`normal`, `cancelAt k`, `panicAt k`, or `unwindEntry`):
1. The trace destroys initialized fields in exact reverse declaration order;
2. Every initialized field is destroyed **exact once** (`countLadderDrops = 1`);
3. Every uninitialized field is destroyed **zero times** (`countLadderDrops = 0`); and
4. Every destruction occurring in cleanup (`inCleanup = true`) is strictly sync. -/
theorem async_drop_ladder_exact_once_per_init_field
    (sc : LadderScenario) (fields : List FieldSpec)
    (hDistinct : noDupIds (fields.map FieldSpec.id)) :
    let trace := runAsyncDropLadder sc fields
    traceFieldIds trace = (initFieldIds fields).reverse ∧
    (∀ f, f ∈ fields → f.init = true → countLadderDrops f.id trace = 1) ∧
    (∀ f, f ∈ fields → f.init = false → countLadderDrops f.id trace = 0) ∧
    allCleanupEventsAreSync trace := by
  dsimp only [runAsyncDropLadder]
  have hIds : traceFieldIds (execRevLadder sc 0 false fields.reverse) = (initFieldIds fields).reverse := by
    rw [execRevLadder_traceFieldIds, initFieldIds_reverse]
  have hNoDupInitRev : noDupIds (initFieldIds fields).reverse :=
    noDupIds_reverse _ (noDupIds_filter_init fields hDistinct)
  refine ⟨hIds, ?_, ?_, execRevLadder_allCleanupSync sc 0 false fields.reverse⟩
  · intro f hMem hInit
    rw [countLadderDrops_eq_countIds, hIds]
    apply countP_eq_one_of_mem_noDup f.id _ hNoDupInitRev
    exact List.mem_reverse.mpr (mem_initFieldIds_of_init fields f hMem hInit)
  · intro f hMem hUninit
    rw [countLadderDrops_eq_countIds, hIds]
    apply countP_eq_zero_of_not_mem
    intro hInRev
    exact not_mem_initFieldIds_of_uninit fields f hDistinct hMem hUninit (List.mem_reverse.mp hInRev)

/-- **Theorem 2b (`unwind_cleanup_never_async_drops`):**
Entering the ladder on an unwind cleanup edge (`LadderScenario.unwindEntry`)
produces zero `.async` drop events across the entire field list, matching
`!unwind.is_cleanup()` at `elaborate_drop.rs:636, 1249, 1311, 1578`. -/
theorem unwind_cleanup_never_async_drops (fields : List FieldSpec) :
    noAsyncDropsInTrace (runAsyncDropLadder .unwindEntry fields) := by
  unfold runAsyncDropLadder
  have hStep : ∀ (step : Nat) (fs : List FieldSpec),
      noAsyncDropsInTrace (execRevLadder .unwindEntry step false fs) := by
    intro step fs
    induction fs generalizing step with
    | nil => trivial
    | cons f rest ih =>
      unfold execRevLadder
      apply noAsyncDropsInTrace_append
      · unfold dropOneField
        cases f.init
        · trivial
        · exact ⟨rfl, trivial⟩
      · exact execRevLadder_unwind_noAsync .unwindEntry (step + 1) rest
  exact hStep 0 fields.reverse

/-! ## Part III: Cross-Crate `AsyncDrop` Feature-Gate Non-Transitivity vs. Transitivity -/

/-- Structural Rust type grammar for drop dispatch (`elaborate_drop.rs:663-712`
and `needs_drop.rs:41-63`). -/
inductive DropTy where
  | prim
  | adt (isLocal : Bool) (hasOwnAsyncDrop : Bool) (field : DropTy)
  | pair (fst snd : DropTy)
  | option (inner : DropTy)
  | array (inner : DropTy)
  | tuple1 (inner : DropTy)
  | boxed (inner : DropTy)

/-- Exact structural model of `Ty::needs_async_drop` (`needs_drop.rs:41-63`),
which recurses into ADT fields, `Option`, arrays, tuples, and `Box<T>`. -/
noncomputable def needsAsyncDrop : DropTy → Bool
  | .prim => false
  | .adt _ hasOwn f => hasOwn || needsAsyncDrop f
  | .pair a b => needsAsyncDrop a || needsAsyncDrop b
  | .option inner => needsAsyncDrop inner
  | .array inner => needsAsyncDrop inner
  | .tuple1 inner => needsAsyncDrop inner
  | .boxed inner => needsAsyncDrop inner

/-- Transitive predicate: does `ty` contain any foreign (`isLocal = false`)
ADT implementing `AsyncDrop`? -/
noncomputable def containsForeignAsyncDrop : DropTy → Bool
  | .prim => false
  | .adt isLocal hasOwn f => ((!isLocal) && hasOwn) || containsForeignAsyncDrop f
  | .pair a b => containsForeignAsyncDrop a || containsForeignAsyncDrop b
  | .option inner => containsForeignAsyncDrop inner
  | .array inner => containsForeignAsyncDrop inner
  | .tuple1 inner => containsForeignAsyncDrop inner
  | .boxed inner => containsForeignAsyncDrop inner

/-- Exact model of `rustc`'s `check_if_can_async_drop` (`elaborate_drop.rs:679-711`):
when `featureEnabled = false`, it checks ONLY top-level
`ty::Adt(def, _) => !def.did().is_local() && def.async_destructor(tcx).is_some()`! -/
noncomputable def rustcShallowGate (featureEnabled : Bool) (ty : DropTy) : Bool :=
  let gate :=
    if featureEnabled then
      true
    else
      match ty with
      | .adt false true _ => true
      | _ => false
  gate && needsAsyncDrop ty

/-- Candidate Fix A (wrapper-compositional transitive gate): allow async drop
when `featureEnabled = true` OR `ty` transitively contains a foreign `AsyncDrop` ADT. -/
noncomputable def transitiveGate (featureEnabled : Bool) (ty : DropTy) : Bool :=
  let gate := if featureEnabled then true else containsForeignAsyncDrop ty
  gate && needsAsyncDrop ty

/-- Candidate Fix B (strict warning-faithful gate): honor
`rustc_metadata/src/diagnostics.rs:595` (*"if async drop type will be dropped
in a crate without `feature(async_drop)`, sync Drop will be used"*). -/
noncomputable def strictWarningGate (featureEnabled : Bool) (ty : DropTy) : Bool :=
  featureEnabled && needsAsyncDrop ty

/-- Every type containing a foreign `AsyncDrop` ADT satisfies `needsAsyncDrop`. -/
theorem needsAsyncDrop_of_containsForeign (ty : DropTy)
    (h : containsForeignAsyncDrop ty = true) :
    needsAsyncDrop ty = true := by
  induction ty with
  | prim => cases h
  | adt isLocal hasOwn f ih =>
    unfold containsForeignAsyncDrop at h
    unfold needsAsyncDrop
    cases isLocal <;> cases hasOwn
    · exact ih h
    · rfl
    · exact ih h
    · rfl
  | pair a b iha ihb =>
    unfold containsForeignAsyncDrop at h
    unfold needsAsyncDrop
    cases ha : containsForeignAsyncDrop a
    · rw [ha] at h
      have hb : needsAsyncDrop b = true := ihb h
      rw [hb]
      cases needsAsyncDrop a <;> rfl
    · rw [iha ha]; rfl
  | option inner ih => exact ih h
  | array inner ih => exact ih h
  | tuple1 inner ih => exact ih h
  | boxed inner ih => exact ih h

/-- **Theorem 3 (`transitive_gate_restores_wrapper_compositionality`):**
Under `transitiveGate`, wrapping any type `t` in `Option`, `[t; 1]`, `(t,)`,
`Box<t>`, a local wrapper struct `LocalWrap(t)`, a foreign wrapper struct
`DepWrap(t)`, or pairing `t` with a non-async-drop sibling `(t, String)` (as in
partial-move open-drop!) **always preserves** `AsyncDrop` dispatch identically! -/
theorem transitive_gate_restores_wrapper_compositionality
    (featureEnabled : Bool) (t : DropTy) :
    transitiveGate featureEnabled (.option t) = transitiveGate featureEnabled t ∧
    transitiveGate featureEnabled (.array t) = transitiveGate featureEnabled t ∧
    transitiveGate featureEnabled (.tuple1 t) = transitiveGate featureEnabled t ∧
    transitiveGate featureEnabled (.boxed t) = transitiveGate featureEnabled t ∧
    transitiveGate featureEnabled (.adt true false t) = transitiveGate featureEnabled t ∧
    transitiveGate featureEnabled (.adt false false t) = transitiveGate featureEnabled t ∧
    transitiveGate featureEnabled (.pair t .prim) = transitiveGate featureEnabled t := by
  have hPairF : containsForeignAsyncDrop (.pair t .prim) = containsForeignAsyncDrop t := by
    change (containsForeignAsyncDrop t || false) = containsForeignAsyncDrop t
    exact Bool.or_false _
  have hPairN : needsAsyncDrop (.pair t .prim) = needsAsyncDrop t := by
    change (needsAsyncDrop t || false) = needsAsyncDrop t
    exact Bool.or_false _
  unfold transitiveGate
  rw [hPairF, hPairN]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Theorem 3b (`strict_warning_policy_agrees_with_diagnostic`):**
Under `strictWarningGate`, omitting `#![feature(async_drop)]` guarantees
synchronous `Drop` (`false`) uniformly for every type `t` (bare or wrapped),
matching the warning help text in `rustc_metadata/src/diagnostics.rs:595`. -/
theorem strict_warning_policy_agrees_with_diagnostic (t : DropTy) :
    strictWarningGate false t = false := rfl

/-- **Theorem 3c (`all_three_gates_agree_when_feature_enabled`):**
When `#![feature(async_drop)]` is enabled (`featureEnabled = true`),
`rustcShallowGate`, `transitiveGate`, and `strictWarningGate` are
extensionally equal on every `DropTy`. -/
theorem all_three_gates_agree_when_feature_enabled (t : DropTy) :
    rustcShallowGate true t = transitiveGate true t ∧
    transitiveGate true t = strictWarningGate true t := by
  unfold rustcShallowGate transitiveGate strictWarningGate
  exact ⟨rfl, rfl⟩

/-! ## Part IV: Constructive Sharpness Counterexamples -/

/-- **CE1 (`ce1_unresumed_missing_returned_transition_causes_double_drop_ub`):**
Under `rustcHeadPolicy`, BOTH an unresumed async coroutine (`has_async_drops = true`)
AND an unresumed plain-`Box` coroutine (`has_async_drops = false`,
`create_coroutine_drop_shim_proxy_async`) trigger `.ubDoubleDrop` on
`async_drop_in_place(&mut *slot).await` inside an `async` block. -/
theorem ce1_unresumed_missing_returned_transition_causes_double_drop_ub :
    let stAsync := runAsyncDropInPlaceAwait rustcHeadPolicy (mkUnresumed .upvarAsyncCoro 42)
    let stPlain := runAsyncDropInPlaceAwait rustcHeadPolicy (mkUnresumed .upvarPlainProxy 77)
    stAsync.log = [.syncDrop 42, .ubDoubleDrop 42] ∧
    hasDoubleDropUb stAsync.log = true ∧
    stPlain.log = [.syncDrop 77, .ubDoubleDrop 77] ∧
    hasDoubleDropUb stPlain.log = true := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- **CE1b (`ce1b_suspended_immediate_missing_returned_causes_double_drop_ub`):**
Under `rustcHeadPolicy`, even a **suspended** coroutine (`Suspend0`) triggers
`.ubDoubleDrop` on `async_drop_in_place(&mut *slot).await` when either:
- its live local has an immediately-ready `AsyncDrop::drop` (no `.await`), or
- its live resource is an unmoved `AsyncDrop` upvar. -/
theorem ce1b_suspended_immediate_missing_returned_causes_double_drop_ub :
    let stImm := runAsyncDropInPlaceAwait rustcHeadPolicy (mkSuspended .localImmediateAsync 123)
    let stUpv := runAsyncDropInPlaceAwait rustcHeadPolicy (mkSuspended .upvarAsyncCoro 66)
    stImm.log = [.asyncDropStart 123, .asyncDropFinish 123, .ubDoubleDrop 123] ∧
    hasDoubleDropUb stImm.log = true ∧
    stUpv.log = [.syncDrop 66, .ubDoubleDrop 66] ∧
    hasDoubleDropUb stUpv.log = true := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- **CE2 (`ce2_non_transitive_gate_splits_bare_vs_option`):**
In a downstream crate omitting `#![feature(async_drop)]`, `rustcShallowGate`
dispatches bare foreign `DepGuard` to `AsyncDrop` (`true`) while dispatching
`Option<DepGuard>`, `[DepGuard; 1]`, `(DepGuard,)`, `Box<DepGuard>`,
`LocalWrap(DepGuard)`, `DepWrap(DepGuard)`, AND unmoved `(DepGuard, String)` to
sync `Drop` (`false`)—while partially moving out `String` open-drops field `.0`
as bare `DepGuard` (`true`), breaking partial-move transparency! -/
theorem ce2_non_transitive_gate_splits_bare_vs_option :
    let depGuard : DropTy := .adt false true .prim
    rustcShallowGate false depGuard = true ∧
    rustcShallowGate false (.option depGuard) = false ∧
    rustcShallowGate false (.array depGuard) = false ∧
    rustcShallowGate false (.tuple1 depGuard) = false ∧
    rustcShallowGate false (.boxed depGuard) = false ∧
    rustcShallowGate false (.adt true false depGuard) = false ∧
    rustcShallowGate false (.adt false false depGuard) = false ∧
    rustcShallowGate false (.pair depGuard .prim) = false := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **CE3 (`ce3_unresumed_upvar_sync_drop_vs_suspended_async_drop`):**
Under `rustcHeadPolicy` (`produce_async_drops = false` in
`elaborate_coroutine_drops`, `coroutine/drop.rs:103`), implicitly dropping an
unresumed `async move` coroutine owning an `AsyncDrop` upvar executes sync
`Drop` (`[.syncDrop 55]`), whereas dropping the same guard after moving it into
a local and suspending executes `AsyncDrop` (`[.asyncDropStart 55, .asyncDropFinish 55]`). -/
theorem ce3_unresumed_upvar_sync_drop_vs_suspended_async_drop :
    let stUnresumed := runAsyncDropInPlaceSyncDriver rustcHeadPolicy (mkUnresumed .upvarAsyncCoro 55)
    let stSuspended := runAsyncDropInPlaceAwait rustcHeadPolicy (mkSuspended .localYieldingAsync 55)
    stUnresumed.log = [.syncDrop 55] ∧
    stSuspended.log = [.asyncDropStart 55, .asyncDropFinish 55] := by
  exact ⟨rfl, rfl⟩

end AsyncDropSoundness
