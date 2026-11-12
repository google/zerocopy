-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Small-Step Unwind Landing Pads, Byte-Fragment Transmutation, and Open Intrinsic Dispatch

This standalone Lean 4 (`v4.34.1`) mechanization accompanies the reference
report on `rustc` drop elaboration, unwind landing pads
(`UnwindAction::Cleanup`), multi-field reference projections, byte-fragment
transmutation, and table-driven intrinsic dispatch in `Runtime(PostCleanup)`
MIR.

The file is organized into three self-contained parts:

1. **Part 1 (`UnwindAndDropModel`)**:
   - Contrasts a fail-closed boolean unwind model (`hasCleanup : Bool` stepping
     to `.failed` whenever `hasCleanup || !s.stack.isEmpty`) with a small-step
     operational model of `rustc`'s `Runtime(PostCleanup)` unwind state machine
     (`UnwindAction`, `Terminator.drop`, `Terminator.unwindResume`,
     `Terminator.unwindTerminate`, and inter-procedural stack unwinding).
   - Proves that `assert_with_drop_cleanup`, `conditional_drop_flag_unwind`,
     `open_drop_partial_move`, multi-frame cross-call unwinding, and
     `extern "C"` ABI unwind termination all execute their drop glue in exact
     accordance with `ElaborateDrops` and `AbortUnwindingCalls` rather than
     collapsing to `.failed`.
   - Models the `#[may_dangle]` vs. `StorageDead` ordering seam (`StorageDead`
     of a borrowed local preceding `Drop` of a guard holding `&'a T`) and proves
     both why eager deep reference validation falsely rejects `#[may_dangle]`
     destructors and why lazy dereference-point validation (or explicit
     `MaybeDangling` wrapping) accepts them while still rejecting wild loads.

2. **Part 2 (`ProjectionAndFragmentModel`)**:
   - Proves concrete counterexamples against scalar `fieldDepth : Nat` reference
     projections (`&pair.1` fails), untyped right-nested `fieldCons` aggregates
     (a 1-field struct wrapping a 2-tuple is rejected as ill-typed), and
     two-stage `peelTransparent` + `extractTransmuteBits` transmutation
     (`#[repr(transparent)] struct TransparentWithPhantom<T>(PhantomData<u64>, (), T)`
     fails both stages).
   - Mechanizes path-projected references (`proj : List PlaceElem`), typed
     aggregate field lists (`MirVal.adt id (fields : List MirVal)`), and a
     single-pass symbolic byte-fragment representation (`Fragment.bits`,
     `Fragment.symBytes`, `Fragment.uninit`) with `encodeFragments` and
     `decodeFragments`.
   - Proves that the single-pass byte-fragment codec handles generic
     `#[repr(transparent)]` wrappers with arbitrary 1-ZST (`PhantomData`, `()`)
     sibling fields, mixed symbolic/concrete `#[repr(C)]` structs, endian-aware
     scalar splitting/coalescing (`u64 <-> (u32, u32)`), and fail-closed
     rejection of uninitialized padding bytes (`Fragment.uninit`) when decoding
     into types that require initialized bytes.

3. **Part 3 (`OpenIntrinsicModel`)**:
   - Formalizes a uniform `Terminator.callIntrinsic` construct parameterized by
     an open `IntrinsicOp` table (`sizeOf`, `alignOf`, `offsetOf`,
     `transmuteCopy`, `atomicLoad`, `bswap`, `ctlz`, `overflowingAdd`) operating
     over standard `MirTy.adt` and `MirTy.ref` types without dedicated
     per-intrinsic `MirTy`, `MirVal`, or `Terminator` constructors.
   - Proves a single parametric frame/statement-index invariance theorem
     (`evalTerminator_stmtIdx_invariant`) that covers all current and future
     `IntrinsicOp` entries in one case rather than scaling linearly with the
     number of modeled intrinsics.
-/

namespace UnwindFragmentsAndIntrinsics

/-!
## Part 1: Small-Step Unwind Landing Pads, Drop Elaboration, and `#[may_dangle]`
-/

namespace UnwindAndDropModel

abbrev BlockId := Nat
abbrev LocalId := Nat
abbrev FnId := Nat

/-- `rustc_middle::mir::UnwindTerminateReason` in `Runtime(PostCleanup)` MIR. -/
inductive UnwindTerminateReason where
  | abi
  | inCleanup
  deriving DecidableEq, Repr

/-- `rustc_middle::mir::UnwindAction` on unwindable MIR terminators. -/
inductive UnwindAction where
  | continue_
  | unreachable
  | terminate (reason : UnwindTerminateReason)
  | cleanup (bb : BlockId)
  deriving DecidableEq, Repr

/-- Terminal outcome of a whole-program execution trace. -/
inductive TerminalOutcome where
  | normalReturn (retVal : Nat)
  | cleanUnwind
  | cleanAbort (reason : UnwindTerminateReason)
  deriving DecidableEq, Repr

/-!
### 1A. The Fail-Closed `hasCleanup : Bool` Workaround and Its False-UB Seam

When a MIR model collapses `UnwindAction` into `hasCleanup : Bool`
(`!matches!(unwind, UnwindAction::Continue)`) and steps to `.failed` whenever
`hasCleanup || !s.stack.isEmpty` holds on a `panic` or failed `assert`, any
function that has a local with drop glue (so `ElaborateDrops` emits
`UnwindAction::Cleanup(bb)`) or any helper called from a parent stack frame is
treated as undefined behavior (`.failed`) when an assertion fails or a panic
occurs.
-/

inductive BrittleTerminator where
  | return_
  | panic (hasCleanup : Bool)
  | assert (cond : Bool) (target : BlockId) (hasCleanup : Bool)
  deriving DecidableEq, Repr

structure BrittleState where
  stackDepth : Nat
  deriving DecidableEq, Repr

inductive BrittleExecResult where
  | running (nextBb : BlockId)
  | terminated (outcome : TerminalOutcome)
  | failed
  deriving DecidableEq, Repr

def evalBrittleTerminator (s : BrittleState) (t : BrittleTerminator) : BrittleExecResult :=
  match t with
  | .return_ => .terminated (.normalReturn 0)
  | .panic hasCleanup =>
    if hasCleanup || s.stackDepth > 0 then .failed
    else .terminated .cleanUnwind
  | .assert cond target hasCleanup =>
    if cond then .running target
    else if hasCleanup || s.stackDepth > 0 then .failed
    else .terminated .cleanUnwind

/--
Counterexample 1A: Under the `hasCleanup : Bool` model, a root-frame assertion
failure in a function with a local drop guard (`hasCleanup = true`) steps to
`.failed` (indistinguishable from undefined behavior), and a helper assertion
failure without cleanup (`hasCleanup = false`) called at `stackDepth = 1` also
steps to `.failed`.
-/
theorem brittle_model_treats_cleanup_and_callee_unwind_as_failed :
    evalBrittleTerminator { stackDepth := 0 } (.assert false 3 true) = .failed ∧
    evalBrittleTerminator { stackDepth := 1 } (.assert false 3 false) = .failed := by
  decide

/-!
### 1B. Small-Step `Runtime(PostCleanup)` Unwind & Drop State Machine

We now model the exact control-flow primitives emitted by `ElaborateDrops`,
`AbortUnwindingCalls`, and `RemoveNoopLandingPads`:
- `UnwindAction.cleanup bb` transfers control to basic block `bb` in the current
  frame;
- `Terminator.drop localId target unwind dropEffect dropPanics` models static and
  elaborated drop glue, appending `dropEffect` to the observable drop trace (or
  triggering a secondary unwind along `unwind` if the destructor itself panics);
- `Terminator.unwindResume` pops the caller frame from `s.stack` and dispatches
  the caller's `unwindAction` (or finishes in `.terminated .cleanUnwind` when the
  root frame's stack is empty);
- `Terminator.unwindTerminate reason` halts immediately in
  `.terminated (.cleanAbort reason)`.
-/

inductive Stmt where
  | assignNat (dst : LocalId) (val : Nat)
  | assignBool (dst : LocalId) (val : Bool)
  | moveLocal (dst : LocalId) (src : LocalId)
  | storageLive (loc : LocalId)
  | storageDead (loc : LocalId)
  deriving DecidableEq, Repr

inductive Terminator where
  | goto (target : BlockId)
  | switchBool (scrutinee : LocalId) (falseTarget : BlockId) (trueTarget : BlockId)
  | return_
  | panic (unwind : UnwindAction)
  | assert (cond : Bool) (target : BlockId) (unwind : UnwindAction)
  | drop (loc : LocalId) (target : BlockId) (unwind : UnwindAction)
      (effectId : Nat) (dropPanics : Bool := false)
  | call (callee : FnId) (argVal : Nat) (dst : LocalId)
      (target : Option BlockId) (unwind : UnwindAction)
  | unwindResume
  | unwindTerminate (reason : UnwindTerminateReason)
  deriving DecidableEq, Repr

structure BasicBlock where
  isCleanup : Bool := false
  stmts : List Stmt := []
  terminator : Terminator
  deriving DecidableEq, Repr

structure FnBody where
  blocks : List BasicBlock
  deriving DecidableEq, Repr

structure CallFrame where
  fnId : FnId
  returnTarget : Option BlockId
  unwindAction : UnwindAction
  returnDst : LocalId
  savedNatLocals : List (LocalId × Nat)
  savedBoolLocals : List (LocalId × Bool)
  deriving DecidableEq, Repr

structure MachineState where
  fnId : FnId
  bb : BlockId
  natLocals : List (LocalId × Nat) := []
  boolLocals : List (LocalId × Bool) := []
  stack : List CallFrame := []
  dropLog : List Nat := []
  deriving DecidableEq, Repr

inductive StepResult where
  | running (next : MachineState)
  | terminated (outcome : TerminalOutcome) (dropLog : List Nat)
  | failed
  deriving DecidableEq, Repr

def lookupNat (env : List (LocalId × Nat)) (k : LocalId) : Nat :=
  match env with
  | [] => 0
  | (k', v) :: rest => if k == k' then v else lookupNat rest k

def updateNat (env : List (LocalId × Nat)) (k : LocalId) (v : Nat) : List (LocalId × Nat) :=
  (k, v) :: env.filter (fun p => p.1 != k)

def lookupBool (env : List (LocalId × Bool)) (k : LocalId) : Bool :=
  match env with
  | [] => false
  | (k', v) :: rest => if k == k' then v else lookupBool rest k

def updateBool (env : List (LocalId × Bool)) (k : LocalId) (v : Bool) : List (LocalId × Bool) :=
  (k, v) :: env.filter (fun p => p.1 != k)

def execStmt (s : MachineState) (st : Stmt) : MachineState :=
  match st with
  | .assignNat dst v => { s with natLocals := updateNat s.natLocals dst v }
  | .assignBool dst b => { s with boolLocals := updateBool s.boolLocals dst b }
  | .moveLocal dst src =>
    let v := lookupNat s.natLocals src
    { s with natLocals := updateNat s.natLocals dst v }
  | .storageLive _ => s
  | .storageDead _ => s

def execStmts (s : MachineState) (stmts : List Stmt) : MachineState :=
  stmts.foldl execStmt s

/--
Small-step unwind initiation (`initiateUnwindStack` / `initiateUnwind`),
structurally recursive on the call stack `stack : List CallFrame`:
- `.cleanup bb` jumps to the cleanup landing-pad block `bb` in the current frame;
- `.terminate reason` halts in `.terminated (.cleanAbort reason)`;
- `.unreachable` steps to `.failed` (reached an uninhabited unwind edge);
- `.continue_` pops the current frame from `stack` and dispatches the caller's
  `unwindAction` (or finishes in `.terminated .cleanUnwind` at the root frame).
-/
def initiateUnwindStack (stack : List CallFrame) (dropLog : List Nat)
    (fnId : FnId) (natLocals : List (LocalId × Nat))
    (boolLocals : List (LocalId × Bool)) (act : UnwindAction) : StepResult :=
  match act with
  | .cleanup bb =>
    .running {
      fnId := fnId
      bb := bb
      natLocals := natLocals
      boolLocals := boolLocals
      stack := stack
      dropLog := dropLog
    }
  | .terminate reason => .terminated (.cleanAbort reason) dropLog
  | .unreachable => .failed
  | .continue_ =>
    match stack with
    | [] => .terminated .cleanUnwind dropLog
    | frame :: rest =>
      initiateUnwindStack rest dropLog frame.fnId frame.savedNatLocals
        frame.savedBoolLocals frame.unwindAction

def initiateUnwind (s : MachineState) (act : UnwindAction) : StepResult :=
  initiateUnwindStack s.stack s.dropLog s.fnId s.natLocals s.boolLocals act

/--
Universal Unwind-Initiation Lemma 1: For any machine state `s` (regardless of
stack depth), `UnwindAction.cleanup bb` transitions directly to basic block `bb`
in the active frame without failing closed.
-/
theorem initiateUnwind_cleanup (s : MachineState) (bb : BlockId) :
    initiateUnwind s (.cleanup bb) = .running { s with bb := bb } := by
  cases s with
  | mk _ _ _ _ stack _ =>
    cases stack <;> rfl

/--
Universal Unwind-Initiation Lemma 2: When `s.stack = frame :: rest`,
`UnwindAction.continue_` (or `Terminator.unwindResume`) pops `frame` and
dispatches `frame.unwindAction` in the restored caller state.
-/
theorem initiateUnwind_continue_pop (s : MachineState) (frame : CallFrame)
    (rest : List CallFrame) (h : s.stack = frame :: rest) :
    initiateUnwind s .continue_ =
      initiateUnwindStack rest s.dropLog frame.fnId frame.savedNatLocals
        frame.savedBoolLocals frame.unwindAction := by
  unfold initiateUnwind
  rw [h]
  rfl

def stepBlock (prog : FnId → Option FnBody) (s : MachineState) : StepResult :=
  match prog s.fnId with
  | none => .failed
  | some body =>
    match body.blocks[s.bb]? with
    | none => .failed
    | some blk =>
      let s1 := execStmts s blk.stmts
      match blk.terminator with
      | .goto target => .running { s1 with bb := target }
      | .switchBool scrut falseTgt trueTgt =>
        let b := lookupBool s1.boolLocals scrut
        .running { s1 with bb := if b then trueTgt else falseTgt }
      | .return_ =>
        let retVal := lookupNat s1.natLocals 0
        match s1.stack with
        | [] => .terminated (.normalReturn retVal) s1.dropLog
        | frame :: rest =>
          match frame.returnTarget with
          | none => .failed
          | some retBb =>
            .running {
              fnId := frame.fnId
              bb := retBb
              natLocals := updateNat frame.savedNatLocals frame.returnDst retVal
              boolLocals := frame.savedBoolLocals
              stack := rest
              dropLog := s1.dropLog
            }
      | .panic unwind => initiateUnwind s1 unwind
      | .assert cond target unwind =>
        if cond then .running { s1 with bb := target }
        else initiateUnwind s1 unwind
      | .drop _ target unwind effectId dropPanics =>
        let s2 := { s1 with dropLog := s1.dropLog ++ [effectId] }
        if dropPanics then initiateUnwind s2 unwind
        else .running { s2 with bb := target }
      | .call callee argVal dst target unwind =>
        let frame : CallFrame := {
          fnId := s1.fnId
          returnTarget := target
          unwindAction := unwind
          returnDst := dst
          savedNatLocals := s1.natLocals
          savedBoolLocals := s1.boolLocals
        }
        .running {
          fnId := callee
          bb := 0
          natLocals := [(1, argVal)]
          boolLocals := []
          stack := frame :: s1.stack
          dropLog := s1.dropLog
        }
      | .unwindResume => initiateUnwind s1 .continue_
      | .unwindTerminate reason => .terminated (.cleanAbort reason) s1.dropLog

def runSteps (prog : FnId → Option FnBody) (s : MachineState) : Nat → StepResult
  | 0 => .running s
  | fuel + 1 =>
    match stepBlock prog s with
    | .running s' => runSteps prog s' fuel
    | res => res

/--
`Runtime(PostCleanup)` CFG for `assert_with_drop_cleanup(x)` (matching `probe_bin.mir`
lines 50–114):
- `bb0`: initializes `_2 = TrackedGuard(10)`, checks `x != 0`, branches to `bb1` or `bb2`.
- `bb1`: sets `_0 = 10 + x`, branches to `bb3`.
- `bb2`: `panic -> cleanup bb5`.
- `bb3`: `drop(_2) -> [return: bb4, unwind: bb6]`.
- `bb4`: `return`.
- `bb5 (cleanup)`: `drop(_2) -> [return: bb6, unwind terminate(cleanup)]`.
- `bb6 (cleanup)`: `resume`.
-/
def assertWithDropCleanupBody (xNonZero : Bool) (dropPanicsInCleanup : Bool := false) : FnBody :=
  { blocks := [
      -- bb0
      { stmts := [.assignNat 2 10, .assignBool 4 xNonZero]
        terminator := .switchBool 4 2 1 },
      -- bb1
      { stmts := [.assignNat 0 11]
        terminator := .goto 3 },
      -- bb2
      { stmts := []
        terminator := .panic (.cleanup 5) },
      -- bb3
      { stmts := []
        terminator := .drop 2 4 (.cleanup 6) 10 false },
      -- bb4
      { stmts := []
        terminator := .return_ },
      -- bb5 (cleanup)
      { isCleanup := true
        stmts := []
        terminator := .drop 2 6 (.terminate .inCleanup) 10 dropPanicsInCleanup },
      -- bb6 (cleanup)
      { isCleanup := true
        stmts := []
        terminator := .unwindResume }
    ] }

/--
Theorem 1B.1: When `x == 0`, `assert_with_drop_cleanup` panics at `bb2`, jumps
to cleanup landing pad `bb5`, runs `TrackedGuard::drop` (recording effect `10`),
executes `resume` at `bb6`, and terminates cleanly in `.terminated .cleanUnwind [10]`
rather than `.failed`.
-/
theorem assert_with_drop_cleanup_unwinds_and_runs_drop :
    runSteps (fun _ => some (assertWithDropCleanupBody false false))
      { fnId := 0, bb := 0 } 10
    = .terminated .cleanUnwind [10] := by
  decide

/--
Theorem 1B.2: If the destructor inside cleanup block `bb5` itself panics
(`dropPanicsInCleanup = true`), the `UnwindAction.terminate .inCleanup` guard
emitted by `ElaborateDrops` halts immediately in
`.terminated (.cleanAbort .inCleanup) [10]`.
-/
theorem double_panic_in_cleanup_aborts_with_inCleanup :
    runSteps (fun _ => some (assertWithDropCleanupBody false true))
      { fnId := 0, bb := 0 } 10
    = .terminated (.cleanAbort .inCleanup) [10] := by
  decide

/--
`Runtime(PostCleanup)` CFG for `conditional_drop_flag_unwind(cond)` (matching
`probe_bin.mir` lines 169–249) together with `may_unwind_callee` (`fnId = 1`):
- Drop flag `_9` is set to `true` when `_3` is initialized in `bb0`.
- When `cond = true` (`bb1`), `_9` is cleared to `false` before `std::mem::drop`
  consumes `_3` (effect `20`).
- `bb4` calls `may_unwind_callee` (`fnId = 1`) with `unwind: cleanup bb10`.
- `may_unwind_callee` panics with `UnwindAction.continue_`, which pops the frame
  and enters caller cleanup block `bb10`.
- `bb10 (cleanup)` switches on drop flag `_9`: if `_9 == true`, `bb9` drops `_3`
  (effect `20`, without redundant `_9 = false` reset) and proceeds to `bb7`
  (`resume`); if `_9 == false`, `bb10` skips `bb9` and jumps straight to `bb7`
  (`resume`).
-/
def conditionalDropFlagProg (cond : Bool) (calleeUnwinds : Bool) : FnId → Option FnBody
  | 0 => some {
      blocks := [
        -- bb0
        { stmts := [.assignBool 9 false, .assignBool 9 true, .assignBool 5 cond]
          terminator := .switchBool 5 3 1 },
        -- bb1 (cond == true: early drop clears _9 := false and drops _3)
        { stmts := [.assignBool 9 false]
          terminator := .drop 3 2 (.cleanup 10) 20 false },
        -- bb2
        { stmts := []
          terminator := .goto 4 },
        -- bb3 (cond == false: _3 stays live, _9 stays true)
        { stmts := []
          terminator := .goto 4 },
        -- bb4 (calls may_unwind_callee)
        { stmts := []
          terminator := .call 1 99 0 (some 5) (.cleanup 10) },
        -- bb5 (normal return from callee: test drop flag _9)
        { stmts := []
          terminator := .switchBool 9 6 8 },
        -- bb6 (normal return exit: clears _9 := false and returns)
        { stmts := [.assignBool 9 false]
          terminator := .return_ },
        -- bb7 (cleanup): resume
        { isCleanup := true
          stmts := []
          terminator := .unwindResume },
        -- bb8 (normal drop of _3 when _9 == true)
        { stmts := []
          terminator := .drop 3 6 (.cleanup 7) 20 false },
        -- bb9 (cleanup drop of _3 when _9 == true; no _9 := false reset in cleanup!)
        { isCleanup := true
          stmts := []
          terminator := .drop 3 7 (.terminate .inCleanup) 20 false },
        -- bb10 (cleanup landing pad: test drop flag _9)
        { isCleanup := true
          stmts := []
          terminator := .switchBool 9 7 9 }
      ]
    }
  | 1 => some {
      blocks := [
        -- bb0 of may_unwind_callee
        { stmts := [.assignNat 0 42]
          terminator := if calleeUnwinds then .panic .continue_ else .return_ }
      ]
    }
  | _ => none

/--
Theorem 1B.3: Across all four combinations of `(cond, calleeUnwinds)` in
`conditional_drop_flag_unwind`, `_3` (drop effect `20`) is dropped **exactly
once** (`dropLog = [20]`), and unwinding from the callee (`fnId = 1`) propagates
through the caller's `bb10 (cleanup)` drop-flag test to `.terminated .cleanUnwind`.
-/
theorem conditional_drop_flag_drops_once_on_all_paths :
    runSteps (conditionalDropFlagProg true true) { fnId := 0, bb := 0 } 20
      = .terminated .cleanUnwind [20] ∧
    runSteps (conditionalDropFlagProg false true) { fnId := 0, bb := 0 } 20
      = .terminated .cleanUnwind [20] ∧
    runSteps (conditionalDropFlagProg true false) { fnId := 0, bb := 0 } 20
      = .terminated (.normalReturn 42) [20] ∧
    runSteps (conditionalDropFlagProg false false) { fnId := 0, bb := 0 } 20
      = .terminated (.normalReturn 42) [20] := by
  decide

/--
`Runtime(PostCleanup)` CFG for `open_drop_partial_move(cond, calleeUnwinds)`
(matching `probe_bin.mir` lines 251–358):
- `GuardPair(_3.0, _3.1)` has field `0` (effect `1`) conditionally moved &
  dropped in `bb1` (clearing drop flag `_12 := false`), while field `1`
  (effect `2`) stays initialized on both branches.
- If dropping `_3.0` on the normal return path (`bb10`) itself panics
  (`firstFieldDropPanics = true`), its `unwind: bb8` edge jumps into the cleanup
  half-ladder (`bb8`) to drop `_3.1` before `resume` (`bb7`)!
-/
def openDropHalfLadderProg (cond : Bool) (calleeUnwinds : Bool)
    (firstFieldDropPanics : Bool := false) : FnId → Option FnBody
  | 0 => some {
      blocks := [
        -- bb0: _12 := true
        { stmts := [.assignBool 12 true, .assignBool 7 cond]
          terminator := .switchBool 7 3 1 },
        -- bb1: _12 := false; move & drop _3.0 (effect 1)
        { stmts := [.assignBool 12 false]
          terminator := .drop 8 2 (.cleanup 13) 1 false },
        -- bb2
        { stmts := [], terminator := .goto 4 },
        -- bb3
        { stmts := [], terminator := .goto 4 },
        -- bb4: call may_unwind_callee
        { stmts := []
          terminator := .call 1 99 0 (some 5) (.cleanup 13) },
        -- bb5: normal half-ladder entry tests _12
        { stmts := []
          terminator := .switchBool 12 9 10 },
        -- bb6: normal return
        { stmts := [.assignBool 12 false]
          terminator := .return_ },
        -- bb7 (cleanup): resume
        { isCleanup := true, stmts := [], terminator := .unwindResume },
        -- bb8 (cleanup): drop _3.1 (effect 2) if normal drop of _3.0 panicked
        { isCleanup := true
          stmts := []
          terminator := .drop 31 7 (.terminate .inCleanup) 2 false },
        -- bb9 (normal): drop _3.1 (effect 2)
        { stmts := []
          terminator := .drop 31 6 (.cleanup 7) 2 false },
        -- bb10 (normal): drop _3.0 (effect 1), unwinds to bb8 on panic
        { stmts := []
          terminator := .drop 30 9 (.cleanup 8) 1 firstFieldDropPanics },
        -- bb11 (cleanup): drop _3.1 (effect 2)
        { isCleanup := true
          stmts := []
          terminator := .drop 31 7 (.terminate .inCleanup) 2 false },
        -- bb12 (cleanup): drop _3.0 (effect 1) -> bb11
        { isCleanup := true
          stmts := []
          terminator := .drop 30 11 (.terminate .inCleanup) 1 false },
        -- bb13 (cleanup): cleanup half-ladder entry tests _12
        { isCleanup := true
          stmts := []
          terminator := .switchBool 12 11 12 }
      ]
    }
  | 1 => some {
      blocks := [
        { stmts := [.assignNat 0 77]
          terminator := if calleeUnwinds then .panic .continue_ else .return_ }
      ]
    }
  | _ => none

/--
Theorem 1B.4: In `open_drop_partial_move`, both field `0` (effect `1`) and field
`1` (effect `2`) are dropped in order `[1, 2]` whether:
1. `cond = true` (field `0` dropped early, callee unwinds, cleanup ladder drops
   only field `1`),
2. `cond = false` (callee unwinds, cleanup ladder drops field `0` then field `1`),
3. `cond = false` (callee returns normally, normal drop of field `0` in `bb10`
   panics, and the cross-edge `bb10 -> bb8` drops field `1` before `resume`).
-/
theorem open_drop_half_ladder_preserves_exact_field_drops :
    runSteps (openDropHalfLadderProg true true false) { fnId := 0, bb := 0 } 20
      = .terminated .cleanUnwind [1, 2] ∧
    runSteps (openDropHalfLadderProg false true false) { fnId := 0, bb := 0 } 20
      = .terminated .cleanUnwind [1, 2] ∧
    runSteps (openDropHalfLadderProg false false true) { fnId := 0, bb := 0 } 20
      = .terminated .cleanUnwind [1, 2] := by
  decide

/--
Theorem 1B.5 (`extern "C"` ABI boundary): When `AbortUnwindingCalls` rewrites
`bb6`'s `resume` into `terminate(abi)` (`UnwindTerminateReason.abi`), an
unwinding panic in `extern_c_cleanup_then_terminate` still executes local drop
glue (`[10]`) in `bb5 (cleanup)` before halting in `.terminated (.cleanAbort .abi)`.
-/
def externCCleanupBody : FnBody :=
  { blocks := [
      { stmts := [.assignNat 2 30], terminator := .panic (.cleanup 1) },
      { isCleanup := true, stmts := [], terminator := .drop 2 2 (.terminate .inCleanup) 30 false },
      { isCleanup := true, stmts := [], terminator := .unwindTerminate .abi }
    ] }

theorem extern_c_runs_cleanup_drop_before_abi_terminate :
    runSteps (fun _ => some externCCleanupBody) { fnId := 0, bb := 0 } 10
      = .terminated (.cleanAbort .abi) [30] := by
  decide

/-!
### 1C. The `#[may_dangle]` vs. `StorageDead` Operational Seam

In `may_dangle_storage_dead_order` (`probe_bin.mir` lines 360–416), `rustc`'s
borrow checker (`add_drop_live_facts_for` using `destructor_constraints`) omits
region liveness constraints for `#[may_dangle] 'a` at `drop(_2)`. Consequently,
in `Runtime(PostCleanup)` MIR:
1. `_4` (`scoped_val`) is allocated with generation `1`;
2. `_2` (`EyepatchGuard(&scoped_val)`) stores a reference to `(_4, gen := 1)`;
3. `StorageDead(_4)` increments `_4`'s generation to `2` (deallocating `_4`);
4. `drop(_2)` invokes `<EyepatchGuard as Drop>::drop(&mut _2)` while `_2.0`
   points to dead generation `1`!

We compare two reference-validity disciplines on `Drop` entry:
- **Eager deep reference validity (`checkDeepRefValid`)**: requires every nested
  `RefVal` reachable inside the dropped value (even behind `&mut Self` or inside
  an uninspected field) to point to a live local generation at `Drop` entry.
- **Dereference-point reference validity (`checkDerefValid`)**: allows a live
  outer `&mut Self` reference whose pointee contains a dangling inner reference
  unless the destructor body actually *dereferences* or *retags by shared/mutable
  ref* that inner reference.
-/

inductive GuardPayloadVal where
  | scalar (n : Nat)
  | ref (targetLocal : LocalId) (gen : Nat)
  | maybeDangling (inner : GuardPayloadVal)
  deriving DecidableEq, Repr

structure GenEnv where
  liveGen : LocalId → Option Nat

def isRefLive (env : GenEnv) (loc : LocalId) (gen : Nat) : Bool :=
  env.liveGen loc == some gen

/-- Eager deep validity checks every `ref` field inside the guard on `Drop` entry. -/
def checkDeepRefValid (env : GenEnv) : GuardPayloadVal → Bool
  | .scalar _ => true
  | .ref loc gen => isRefLive env loc gen
  | .maybeDangling _ => true

/--
Dereference-point validity: entering `Drop::drop(_1: &mut Guard)` checks that the
guard's own storage (`guardLoc`) is live, and checks inner references only when a
statement inside `Drop::drop` projects and dereferences them (`derefInner = true`).
-/
def evalDropGuard (eagerDeepCheck : Bool) (env : GenEnv)
    (guardLoc : LocalId) (guardGen : Nat) (payload : GuardPayloadVal)
    (derefInner : Bool) : Bool :=
  if !isRefLive env guardLoc guardGen then false
  else if eagerDeepCheck && !checkDeepRefValid env payload then false
  else if derefInner then checkDeepRefValid env payload
  else true

/--
After `StorageDead(_4)` (line 402 of `probe_bin.mir`), `_2` (`guardLoc = 2`) is
still live at generation `1`, whereas `_4` (`scoped_val`, `targetLocal = 4`) is
dead (`liveGen 4 = none`).
-/
def postStorageDeadEnv : GenEnv :=
  { liveGen := fun loc => if loc == 2 then some 1 else none }

/--
Theorem 1C.1: At `drop(_2)` after `StorageDead(_4)`:
1. Eager deep reference validation (`eagerDeepCheck = true`) falsely rejects
   `EyepatchGuard(&scoped_val)` (`evalDropGuard = false`) even when `Drop::drop`
   never dereferences `(*_1).0` (`derefInner = false`).
2. Dereference-point validation (`eagerDeepCheck = false`) accepts
   `EyepatchGuard::drop` when `(*_1).0` is not dereferenced (`derefInner = false`),
   still rejects wild dereferences of `(*_1).0` (`derefInner = true`), and
   accepts `MaybeDangling` wrappers under both models.
-/
theorem may_dangle_after_storage_dead_characterization :
    evalDropGuard true postStorageDeadEnv 2 1 (.ref 4 1) false = false ∧
    evalDropGuard false postStorageDeadEnv 2 1 (.ref 4 1) false = true ∧
    evalDropGuard false postStorageDeadEnv 2 1 (.ref 4 1) true = false ∧
    evalDropGuard true postStorageDeadEnv 2 1 (.maybeDangling (.ref 4 1)) false = true := by
  decide

end UnwindAndDropModel

/-!
## Part 2: Path-Projected References, Typed Aggregates, and Single-Pass Byte-Fragment Transmutation
-/

namespace ProjectionAndFragmentModel

abbrev AdtId := Nat
abbrev LocalId := Nat

/-!
### 2A. Counterexamples to Scalar `fieldDepth : Nat` and Untyped `fieldCons`

We first formalize the brittle representations and prove the three concrete
failure modes:
1. Scalar `fieldDepth : Nat` can only peel `.field 0` projections (`&pair.1` fails).
2. Untyped right-nested `fieldCons` (`packFields`) represents a 1-field ADT by its
   unwrapped single field value `.adt id v`, so when that single field is itself a
   2-tuple represented as `.fieldCons a b`, `validFields [tupleTy] (.fieldCons a b)`
   hits the `[f], .fieldCons _ _ => false` branch and rejects a well-typed value!
3. Two-stage `evalTransmuteVal` (`peelTransparent` + `extractTransmuteBits`) fails
   on `#[repr(transparent)] struct TransparentWithPhantom<T>(PhantomData<u64>, (), T)`
   because Stage 1 requires `fields.length == 1` (rejecting sibling 1-ZST fields)
   and Stage 2 requires concrete scalar bits (rejecting generic `T = .param 0`).
-/

inductive BrittleVal where
  | int (w : Nat) (n : Nat)
  | param (idx : Nat)
  | ref (loc : LocalId) (fieldDepth : Nat)
  | adt (id : AdtId) (payload : BrittleVal)
  | fieldCons (head : BrittleVal) (tail : BrittleVal)
  | unit
  deriving DecidableEq, Repr

def evalBrittleRefProj (v : BrittleVal) (fieldIdx : Nat) : Option BrittleVal :=
  match v with
  | .ref loc depth =>
    if fieldIdx == 0 then some (.ref loc (depth + 1)) else none
  | _ => none

def packBrittleFields : List BrittleVal → BrittleVal
  | [] => .unit
  | [v] => v
  | v :: vs => .fieldCons v (packBrittleFields vs)

def checkBrittleSingleFieldAdt (v : BrittleVal) : Bool :=
  match v with
  | .fieldCons _ _ => false
  | _ => true

/--
Counterexample 2A.1: Scalar `fieldDepth : Nat` cannot project `&pair.1`
(`evalBrittleRefProj (.ref 1 0) 1 = none`), and packing a 1-field struct whose
sole field is a 2-tuple `packBrittleFields [.int 8 10, .int 8 20]` produces a
`.fieldCons` node that `checkBrittleSingleFieldAdt` rejects as a multi-field
list!
-/
theorem brittle_fieldDepth_and_fieldCons_counterexamples :
    evalBrittleRefProj (.ref 1 0) 1 = none ∧
    checkBrittleSingleFieldAdt (packBrittleFields [packBrittleFields [.int 8 10, .int 8 20]]) = false := by
  decide

/-!
### 2B. Path-Projected References (`List PlaceElem`) and Typed Aggregate Field Lists

Replacing `fieldDepth : Nat` with `proj : List PlaceElem` and `MirVal.fieldCons`
with `fields : List MirVal` eliminates both representation seams.
-/

inductive PlaceElem where
  | deref
  | field (idx : Nat)
  deriving DecidableEq, Repr

inductive MirVal where
  | int (byteWidth : Nat) (bits : Nat)
  | symParam (paramIdx : Nat) (byteWidth : Nat)
  | uninitBytes (byteWidth : Nat)
  | ref (loc : LocalId) (proj : List PlaceElem)
  | adt (id : AdtId) (fields : List MirVal)
  | tuple (fields : List MirVal)

/-- Projecting `&(*r).fieldIdx` appends `.field fieldIdx` to the reference path. -/
def evalRefFieldProj (v : MirVal) (fieldIdx : Nat) : Option MirVal :=
  match v with
  | .ref loc path => some (.ref loc (path ++ [.field fieldIdx]))
  | _ => none

/-- Resolving a path of `.field idx` projections through nested aggregates. -/
def resolveFieldPath (v : MirVal) : List PlaceElem → Option MirVal
  | [] => some v
  | .field idx :: rest =>
    match v with
    | .adt _ fields | .tuple fields =>
      match fields[idx]? with
      | some fVal => resolveFieldPath fVal rest
      | none => none
    | _ => none
  | .deref :: _ => none

/--
Theorem 2B.1: With `proj : List PlaceElem` and `fields : List MirVal`, borrowing
`&pair.1` on `TwoUsize(100, 200)` and dereferencing `*_2` resolves to
`MirVal.int 8 200`, and a 1-field struct wrapping a 2-tuple resolves both `.0`
and `.0.1` unambiguously.
-/
theorem path_projected_ref_resolves_second_field_and_nested_tuple :
    let twoUsize := MirVal.adt 1 [.int 8 100, .int 8 200]
    let refSecond := evalRefFieldProj (.ref 1 []) 1
    let wrappedTuple := MirVal.adt 2 [.tuple [.int 8 10, .int 8 20]]
    (refSecond = some (.ref 1 [.field 1])) ∧
    (resolveFieldPath twoUsize [.field 1] = some (.int 8 200)) ∧
    (resolveFieldPath wrappedTuple [.field 0, .field 1] = some (.int 8 20)) :=
  ⟨rfl, rfl, rfl⟩

/-!
### 2C. Single-Pass Symbolic Byte-Fragment Transmutation (`Fragment`)

Instead of a two-stage `peelTransparent` + `extractTransmuteBits` fallback, we
represent the byte layout of any value as a flat `List Fragment`, where each
`Fragment` is a single byte (or contiguous slice):
- `Fragment.byte (b : Nat)`: a concrete initialized byte (`0 ≤ b < 256`);
- `Fragment.symByte (paramIdx : Nat) (byteOffset : Nat)`: byte `byteOffset` of
  symbolic type parameter `paramIdx`;
- `Fragment.uninit`: an uninitialized byte (such as inter-field or trailing
  struct padding).

Why per-byte fragments? Because a list of byte-level fragments has:
1. Canonical length `fragments.length = byteSize(T)`;
2. Zero-size erasure: any 1-ZST field (`PhantomData<u64>`, `()`, `[u8; 0]`)
   encodes to `[] : List Fragment`, so `#[repr(transparent)]` wrappers with
   arbitrary leading or trailing 1-ZST fields have the **exact same** fragment
   list as their single non-ZST payload without needing a separate
   `peelTransparent` pass!
3. Mixed symbolic + concrete support: a `#[repr(C)]` struct containing both a
   generic parameter `T` and concrete integer fields encodes to
   `symBytes(T) ++ intBytes(u32)` and decodes cleanly into any layout-compatible
   target type.
4. Endian-aware scalar splitting and coalescing: a little-endian `u64` encodes to
   8 `Fragment.byte` elements that decode into `(u32, u32)` (and vice versa).
5. Sound padding handling: padding bytes encode to `Fragment.uninit`, which
   cannot be decoded into `MirTy.int` or `MirTy.symParam` (failing closed on UB
   padding reads), while decoding into target padding (`MirTy.padding n`) consumes
   any `n` fragments.
-/

inductive Fragment where
  | byte (b : Nat)
  | symByte (paramIdx : Nat) (byteOffset : Nat)
  | uninit
  deriving DecidableEq, Repr

inductive MirTy where
  | int (byteWidth : Nat)
  | symParam (paramIdx : Nat) (byteWidth : Nat)
  | padding (byteWidth : Nat)
  | zst (id : AdtId)
  | adt (id : AdtId) (fields : List MirTy)
  | tuple (fields : List MirTy)

mutual
def tyByteSize : MirTy → Nat
  | .int w => w
  | .symParam _ w => w
  | .padding w => w
  | .zst _ => 0
  | .adt _ fields => fieldListByteSize fields
  | .tuple fields => fieldListByteSize fields

def fieldListByteSize : List MirTy → Nat
  | [] => 0
  | f :: fs => tyByteSize f + fieldListByteSize fs
end

/-- Encode a `w`-byte little-endian integer into `w` `Fragment.byte` elements. -/
def encodeIntLE : Nat → Nat → List Fragment
  | 0, _ => []
  | w + 1, n => .byte (n % 256) :: encodeIntLE w (n / 256)

/-- Decode `w` `Fragment.byte` elements into a little-endian integer. -/
def decodeIntLE : List Fragment → Option Nat
  | [] => some 0
  | .byte b :: rest =>
    match decodeIntLE rest with
    | some hi => some (b + 256 * hi)
    | none => none
  | _ :: _ => none

/-- Generate `w` symbolic byte fragments for type parameter `paramIdx`. -/
def makeSymBytes (paramIdx : Nat) (w : Nat) : List Fragment :=
  (List.range w).map (fun i => .symByte paramIdx i)

/-- Check that `frags` is the intact `w`-byte sequence for `paramIdx`. -/
def checkSymBytes (paramIdx : Nat) (w : Nat) (frags : List Fragment) : Bool :=
  frags == makeSymBytes paramIdx w

mutual
def encodeFragments (ty : MirTy) (v : MirVal) : Option (List Fragment) :=
  match ty, v with
  | .int w, .int w' n =>
    if w == w' then some (encodeIntLE w n) else none
  | .symParam idx w, .symParam idx' w' =>
    if idx == idx' && w == w' then some (makeSymBytes idx w) else none
  | .padding w, .uninitBytes w' =>
    if w == w' then some (List.replicate w .uninit) else none
  | .zst id, .adt id' [] =>
    if id == id' then some [] else none
  | .adt id fTys, .adt id' fVals =>
    if id == id' then encodeFieldFragments fTys fVals else none
  | .tuple fTys, .tuple fVals =>
    encodeFieldFragments fTys fVals
  | _, _ => none

def encodeFieldFragments : List MirTy → List MirVal → Option (List Fragment)
  | [], [] => some []
  | fTy :: fTys, fVal :: fVals =>
    match encodeFragments fTy fVal, encodeFieldFragments fTys fVals with
    | some h, some t => some (h ++ t)
    | _, _ => none
  | _, _ => none
end

mutual
def decodeFragments (ty : MirTy) (frags : List Fragment) : Option (MirVal × List Fragment) :=
  match ty with
  | .int w =>
    if frags.length < w then none
    else
      let (chunk, rest) := frags.splitAt w
      match decodeIntLE chunk with
      | some n => some (.int w n, rest)
      | none => none
  | .symParam idx w =>
    if frags.length < w then none
    else
      let (chunk, rest) := frags.splitAt w
      if checkSymBytes idx w chunk then some (.symParam idx w, rest)
      else none
  | .padding w =>
    if frags.length < w then none
    else
      let (_, rest) := frags.splitAt w
      some (.uninitBytes w, rest)
  | .zst id => some (.adt id [], frags)
  | .adt id fTys =>
    match decodeFieldFragments fTys frags with
    | some (vals, rest) => some (.adt id vals, rest)
    | none => none
  | .tuple fTys =>
    match decodeFieldFragments fTys frags with
    | some (vals, rest) => some (.tuple vals, rest)
    | none => none

def decodeFieldFragments : List MirTy → List Fragment → Option (List MirVal × List Fragment)
  | [], frags => some ([], frags)
  | fTy :: fTys, frags =>
    match decodeFragments fTy frags with
    | some (v, rest1) =>
      match decodeFieldFragments fTys rest1 with
      | some (vs, rest2) => some (v :: vs, rest2)
      | none => none
    | none => none
end

/--
Single-pass operational rule for `transmute` and `transmute_copy`:
1. Check `tyByteSize srcTy == tyByteSize dstTy`;
2. Encode `srcVal` at `srcTy` into `frags : List Fragment`;
3. Decode `frags` at `dstTy` and require `rest.isEmpty`.
-/
def evalTransmuteUnified (srcTy dstTy : MirTy) (srcVal : MirVal) : Option MirVal :=
  if tyByteSize srcTy != tyByteSize dstTy then none
  else
    match encodeFragments srcTy srcVal with
    | none => none
    | some frags =>
      match decodeFragments dstTy frags with
      | some (dstVal, []) => some dstVal
      | _ => none

/--
Theorem 2C.0 (Universal 0-Sized Tuple Field Erasure):
Prepending a 0-sized unit tuple field (`.tuple []`, `.tuple []`) to any field
type list `fTys` and value list `fVals` leaves `encodeFieldFragments` and
`fieldListByteSize` identically unchanged.
-/
theorem unit_tuple_field_erasure (fTys : List MirTy) (fVals : List MirVal) :
    fieldListByteSize (.tuple [] :: fTys) = fieldListByteSize fTys ∧
    encodeFieldFragments (.tuple [] :: fTys) (.tuple [] :: fVals) =
      encodeFieldFragments fTys fVals := by
  constructor
  · simp [fieldListByteSize, tyByteSize]
  · simp [encodeFieldFragments, encodeFragments]
    cases encodeFieldFragments fTys fVals <;> rfl

/--
`TransparentWithPhantom<T>(PhantomData<u64>, (), T)` where `T` is generic
parameter `0` of byte width `8`:
- Field 0: `PhantomData<u64>` (`.zst 90`)
- Field 1: `()` (`.tuple []`)
- Field 2: `T` (`.symParam 0 8`)
-/
def transparentWithPhantomTy : MirTy :=
  .adt 10 [.zst 90, .tuple [], .symParam 0 8]

def transparentWithPhantomVal : MirVal :=
  .adt 10 [.adt 90 [], .tuple [], .symParam 0 8]

/--
Theorem 2C.1: The single-pass `evalTransmuteUnified` rule round-trips
`TransparentWithPhantom<T> <-> T` for symbolic `T` without any special-case
`peelTransparent` pass, because the 1-ZST sibling fields (`PhantomData<u64>` and
`()`) encode to `[] : List Fragment`.
-/
theorem unified_transmute_handles_transparent_with_phantom_zsts :
    evalTransmuteUnified transparentWithPhantomTy (.symParam 0 8) transparentWithPhantomVal
      = some (.symParam 0 8) ∧
    evalTransmuteUnified (.symParam 0 8) transparentWithPhantomTy (.symParam 0 8)
      = some transparentWithPhantomVal :=
  ⟨rfl, rfl⟩

/--
Theorem 2C.2: `evalTransmuteUnified` handles `#[repr(C)]` structs that mix a
symbolic generic parameter `T` (`.symParam 0 8`) and a concrete scalar (`u32`,
`.int 4`) when transmuted into a layout-compatible pair `(T, (u16, u16))`.
-/
theorem unified_transmute_handles_mixed_symbolic_and_concrete_repr_c :
    let srcTy := MirTy.adt 20 [.symParam 0 8, .int 4]
    let dstTy := MirTy.tuple [.symParam 0 8, .tuple [.int 2, .int 2]]
    let srcVal := MirVal.adt 20 [.symParam 0 8, .int 4 0x00020001]
    evalTransmuteUnified srcTy dstTy srcVal
      = some (.tuple [.symParam 0 8, .tuple [.int 2 1, .int 2 2]]) :=
  rfl

/--
Theorem 2C.3: `evalTransmuteUnified` rejects transmuting uninitialized padding
bytes (`MirTy.padding 4`) into an initialized scalar (`MirTy.int 4`), preventing
unsound fabrication of initialized values from padding, while allowing
initialized scalar bytes to be transmuted into padding (`MirTy.padding 4`).
-/
theorem unified_transmute_rejects_uninit_padding_to_int :
    evalTransmuteUnified (.padding 4) (.int 4) (.uninitBytes 4) = none ∧
    evalTransmuteUnified (.int 4) (.padding 4) (.int 4 0x12345678) = some (.uninitBytes 4) :=
  ⟨rfl, rfl⟩

end ProjectionAndFragmentModel

/-!
## Part 3: Open / Table-Driven Intrinsic Dispatch vs. Hardcoded AST Constructors
-/

namespace OpenIntrinsicModel

open ProjectionAndFragmentModel

abbrev BlockId := Nat
abbrev LocalId := Nat

/--
Open enumeration of compiler intrinsics and well-known library primitives.
Adding a new entry to `IntrinsicOp` and `evalIntrinsic` adds zero constructors to
`MirTy`, `MirVal`, or `Terminator`.
-/
inductive IntrinsicOp where
  | sizeOf
  | alignOf
  | offsetOf (fieldIdx : Nat)
  | transmuteCopy
  | atomicLoad
  | bswap
  | ctlz
  | overflowingAdd
  deriving DecidableEq, Repr

/-- Standard `core::sync::atomic::Ordering` ADT ID (`AdtId = 500`). -/
def orderingAdtId : AdtId := 500

/-- Standard `core::sync::atomic::Atomic<usize>` ADT ID (`AdtId = 501`). -/
def atomicUsizeAdtId : AdtId := 501

mutual
def tyAlign : MirTy → Nat
  | .int w => if w == 0 then 1 else w
  | .symParam _ w => if w == 0 then 1 else w
  | .padding _ => 1
  | .zst _ => 1
  | .adt _ fields => fieldListAlign fields
  | .tuple fields => fieldListAlign fields

def fieldListAlign : List MirTy → Nat
  | [] => 1
  | f :: fs => Nat.max (tyAlign f) (fieldListAlign fs)
end

def fieldByteOffset : List MirTy → Nat → Option Nat
  | _, 0 => some 0
  | f :: fs, idx + 1 =>
    match fieldByteOffset fs idx with
    | some off => some (tyByteSize f + off)
    | none => none
  | [], _ + 1 => none

/--
Pure operational semantics for `IntrinsicOp`.
Notice that:
- `sizeOf`, `alignOf`, and `offsetOf` query `tyByteSize`, `tyAlign`, and
  `fieldByteOffset` on `typeArgs`;
- `transmuteCopy` reads the pointee of `&src` and invokes `evalTransmuteUnified`;
- `atomicLoad` takes a standard `MirVal.ref loc path` pointing to an
  `Atomic<usize>` ADT (`.adt atomicUsizeAdtId [.int 8 v]`) and a standard
  `Ordering` enum value (`.adt orderingAdtId [.int 1 discr]`), without needing
  `MirTy.refAtomicUsize` or `MirTy.atomicOrdering` in `MirTy`!
-/
def evalIntrinsic (lookupLocal : LocalId → Option MirVal)
    (op : IntrinsicOp) (typeArgs : List MirTy) (args : List MirVal) : Option MirVal :=
  match op, typeArgs, args with
  | .sizeOf, [ty], [] => some (.int 8 (tyByteSize ty))
  | .alignOf, [ty], [] => some (.int 8 (tyAlign ty))
  | .offsetOf idx, [.adt _ fields], [] =>
    match fieldByteOffset fields idx with
    | some off => some (.int 8 off)
    | none => none
  | .transmuteCopy, [srcTy, dstTy], [.ref loc path] =>
    match lookupLocal loc with
    | some rootVal =>
      match resolveFieldPath rootVal path with
      | some srcVal => evalTransmuteUnified srcTy dstTy srcVal
      | none => none
    | none => none
  | .atomicLoad, [], [.ref loc path, .adt ordId [.int 1 _discr]] =>
    if ordId != orderingAdtId then none
    else
      match lookupLocal loc with
      | some rootVal =>
        match resolveFieldPath rootVal path with
        | some (.adt atomId [.int 8 v]) =>
          if atomId == atomicUsizeAdtId then some (.int 8 v) else none
        | _ => none
      | none => none
  | .bswap, [], [.int 2 n] =>
    let lo := n % 256
    let hi := (n / 256) % 256
    some (.int 2 (lo * 256 + hi))
  | .ctlz, [], [.int 1 n] =>
    let lz :=
      if n >= 128 then 0
      else if n >= 64 then 1
      else if n >= 32 then 2
      else if n >= 16 then 3
      else if n >= 8 then 4
      else if n >= 4 then 5
      else if n >= 2 then 6
      else if n >= 1 then 7
      else 8
    some (.int 4 lz)
  | .overflowingAdd, [], [.int w a, .int w' b] =>
    if w != w' then none
    else
      let modulus := 2 ^ (8 * w)
      let sum := a + b
      some (.tuple [.int w (sum % modulus), .int 1 (if sum >= modulus then 1 else 0)])
  | _, _, _ => none

/--
A compact `Terminator` grammar where all intrinsics and layout/atomic primitives
share a single `.callIntrinsic` constructor.
-/
inductive ExtensibleTerminator where
  | goto (target : BlockId)
  | return_
  | callIntrinsic (op : IntrinsicOp) (typeArgs : List MirTy)
      (args : List MirVal) (dst : LocalId) (target : BlockId)

structure FrameState where
  bb : BlockId
  stmtIdx : Nat
  locals : List (LocalId × MirVal)

def lookupLocalVal (locals : List (LocalId × MirVal)) (k : LocalId) : Option MirVal :=
  match locals with
  | [] => none
  | (k', v) :: rest => if k == k' then some v else lookupLocalVal rest k

def writeLocalVal (locals : List (LocalId × MirVal)) (k : LocalId) (v : MirVal) :
    List (LocalId × MirVal) :=
  (k, v) :: locals.filter (fun p => p.1 != k)

def evalExtensibleTerminator (s : FrameState) (t : ExtensibleTerminator) : Option FrameState :=
  match t with
  | .goto target => some { s with bb := target, stmtIdx := 0 }
  | .return_ => some { s with stmtIdx := 0 }
  | .callIntrinsic op typeArgs args dst target =>
    match evalIntrinsic (lookupLocalVal s.locals) op typeArgs args with
    | some res =>
      some { s with bb := target, stmtIdx := 0, locals := writeLocalVal s.locals dst res }
    | none => none

/--
Theorem 3.1 (Single-Case `stmtIdx` Lowering Invariance):
In a closed-AST design where each intrinsic (`callLayout`, `callTransmuteCopy`,
`callAtomicLoad`, ...) is a separate `Terminator` constructor, every lowering
lemma (`evalMirTerminator_with_stmtIdx_normal`, `evalMirTerminator_eq_of_nocall`,
`validStep_with_stmtIdx`, etc.) requires a separate proof case per intrinsic.

With `ExtensibleTerminator.callIntrinsic`, the `stmtIdx`-invariance theorem is
proved **once** for all `IntrinsicOp` variants simultaneously—adding new variants
to `IntrinsicOp` or `evalIntrinsic` requires zero changes to the theorem or its
proof!
-/
theorem evalTerminator_stmtIdx_invariant
    (s : FrameState) (idx1 idx2 : Nat) (t : ExtensibleTerminator) :
    evalExtensibleTerminator { s with stmtIdx := idx1 } t =
    evalExtensibleTerminator { s with stmtIdx := idx2 } t := by
  cases t <;> rfl

/--
Theorem 3.2: End-to-end gallery check confirming that `sizeOf`, `alignOf`,
`offsetOf`, `transmuteCopy`, `atomicLoad` (via standard `MirVal.ref` and
`MirVal.adt`), `bswap`, `ctlz`, and `overflowingAdd` all execute through the
single `ExtensibleTerminator.callIntrinsic` rule.
-/
theorem intrinsic_gallery_executes_uniformly :
    let initLocals : List (LocalId × MirVal) := [
      (1, .adt atomicUsizeAdtId [.int 8 55]),
      (2, transparentWithPhantomVal)
    ]
    let lookup := lookupLocalVal initLocals
    let relaxedOrd := MirVal.adt orderingAdtId [.int 1 0]
    (evalIntrinsic lookup .sizeOf [transparentWithPhantomTy] [] = some (.int 8 8)) ∧
    (evalIntrinsic lookup .alignOf [transparentWithPhantomTy] [] = some (.int 8 8)) ∧
    (evalIntrinsic lookup (.offsetOf 2) [transparentWithPhantomTy] [] = some (.int 8 0)) ∧
    (evalIntrinsic lookup .transmuteCopy [transparentWithPhantomTy, .symParam 0 8] [.ref 2 []]
      = some (.symParam 0 8)) ∧
    (evalIntrinsic lookup .atomicLoad [] [.ref 1 [], relaxedOrd] = some (.int 8 55)) ∧
    (evalIntrinsic lookup .bswap [] [.int 2 0x1234] = some (.int 2 0x3412)) ∧
    (evalIntrinsic lookup .ctlz [] [.int 1 0x08] = some (.int 4 4)) ∧
    (evalIntrinsic lookup .overflowingAdd [] [.int 1 250, .int 1 10]
      = some (.tuple [.int 1 4, .int 1 1])) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end OpenIntrinsicModel

end UnwindFragmentsAndIntrinsics
