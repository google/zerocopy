-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Trusted.MirAst
import Trusted.MirSemantics

namespace VrustcFormal.F1_13

open Trusted.MirAst Trusted.MirSemantics

/-!
# Two-Phase Stack Unwinding, `BasicBlock.cleanup`, `TerminatorKind.unwindResume`, `AbortUnwindingCalls`, and Unwind-Aware `MIR Inline` Reduction Directly Into `Trusted.MirSemantics` (`VrustcFormal.F1_13`)

This module closes the final remaining executable constructs in Anneal's
unmodified `mirProfileVersion = 1` `Trusted.MirAst` (`TerminatorKind.unwindResume`,
`BasicBlock.cleanup`, `UnwindAction.{continue_, unreachable, terminate, cleanup}`
on both `TerminatorKind.assert` and `TerminatorKind.call`, and
`TerminalOut.unwound`), grounded directly in unmodified `Trusted.MirAst` and
`Trusted.MirSemantics` (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`,
zero surrogate AST or `Val` types), vendored `lean-miri`
(`proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`,
`Miri/Interpreter/ControlFlow.lean:42-204`, `Stack.lean:19-423`), upstream
`compiler/rustc_mir_transform/src/abort_unwinding_calls.rs:1-148`, and live
`zerocopy 0.8.48` (`4,665` MIR bodies) `AbortUnwindingCalls` census
(`panic=unwind`: `-33` cleanup bodies / `-90` cleanup BBs; `panic=abort`:
`-1,953` cleanup bodies -> `0 / 4,460` fn-like bodies retaining cleanup pads).

1. **Part I — Unified Interprocedural, `Assert`, and Two-Phase Unwinding
   Operational Semantics (`M_unwind`) Directly Over `Trusted.MirAst.Program`:**
   - Reuses unmodified `Trusted.MirSemantics.{Val, LocalSlot, CallerMemory,
     Query, Out, FaultKind, FrameState, evalStatement, evalPrimitiveOperand,
     evalOperandToSlot, writePlace, initLocalsLoop, checkArgsMatch,
     hasStorageAnnotation, storageAnnotationsInBounds, isSupportedScalarOrUnitTy,
     BodyStaticAdmitted, ValidEntryArgs, entryProgForBody}`.
   - Extends `TerminalOut` with `UnwindOut.{returned, unwound, aborted}` and
     models multi-frame unwinding (`dispatchUnwindStack` over `List CallContUnw`):
     * `BasicBlock.cleanup` enforcement matching `ControlFlow.lean:74`
       (`.return_` in `cleanup = true` and `.unwindResume` in `cleanup = false`
       both fault `.fault .unsupported`);
     * `UnwindAction.cleanup padBb` jumps into `padBb` requiring
       `padBb.cleanup == true` (else `.fault .unsupported`), without writing the
       interrupted call's `dst` place;
     * `UnwindAction.continue_` propagates unwinding across caller frames until
       either a cleanup pad, `.unreachable` (`.fault .undefined`,
       `ControlFlow.lean:47`), `.terminate` (`.done (.aborted callerMem)`), or
       top-of-stack (`.done (.unwound callerMem)`).
     * Returning normally from a diverging call (`target = none`) faults
       `.fault .undefined` (`ControlFlow.lean:110`).

2. **Part II — Decidable Certified Unwind-Elimination & Lowering Passes Over
   Unmodified `Trusted.MirAst.Program`:**
   - `UnwindOptStep.inlineWithUnwind`: unwind-aware `MIR Inline` splicing a
     non-self-recursive callee (including unwinding callees with cleanup pads
     and `.unwindResume`) into ANY `callerUnwind` action (`.cleanup`,
     `.continue_`, `.unreachable`, or `.terminate` via always-failing
     `.assert` encoding) with shared `unwindExitBlock` `StorageDead` cleanup.
   - `UnwindOptStep.dischargeTrivialAssert`: replaces constant-satisfied
     `TerminatorKind.assert` with `TerminatorKind.goto`.
   - `UnwindOptStep.abortUnwindingCalls`: mechanizes
     `abort_unwinding_calls.rs:69-137` under a sound inductive interprocedural
     `checkNoUnwindSummary` certificate, tightening proven non-unwinding
     `call`/`assert` unwind actions to `.unreachable` while preserving full
     bidirectional semantic equivalence (`↔`).
   - `UnwindOptStep.pruneDeadCleanupBlocks`: mechanizes
     `abort_unwinding_calls.rs:140` (`remove_dead_blocks`) with an explicit
     `hasStorageAnnotation` preservation guard preventing silent `DeadLocal`
     UB erasure (`CE5`).
   - Also models `-C panic=abort` ABI enforcement (`checkPanicAbortEntryTransform`),
     proving exact `.unwound -> .aborted` outcome refinement while keeping all
     `.returned`, `.fault`, and `DivergesUnw` behaviors identical.

3. **Part III — Six Core Target Theorems (frozen `sorry` placeholders):**
   - `unwind_conservative_extension_exact`
   - `unwindOptStep_sound_bidirectional_iff`
   - `panicAbortEntryTransform_refines_unwound_to_aborted`
   - `unwindOptTrace_sound_bidirectional_iff`
   - `unwindOptTrace_reduces_to_trusted_mir`
   - `unwindOptTrace_then_optPipeline_vc_transport`

4. **Part IV — Deterministic Adequacy, Ten Sharpness Counterexamples
   (`CE1`--`CE10`), and Universal $2^{32}$ Multi-Pass Unwind-Reduction Witness
   (`0` `sorry`, strictly `[propext]`):**
   - Verifies every unwind, cleanup, abort, `hasStorageAnnotation`, and inlining
     boundary constructively, and verifies a 2-body unwinding-capable program
     reducing via `inlineWithUnwind -> dischargeTrivialAssert ->
     abortUnwindingCalls -> pruneDeadCleanupBlocks` to unmodified
     `Trusted.MirSemantics`.
-/

/-! ## Part I: Operational Semantics `M_unwind` Over Unmodified `Trusted.MirAst.Program` -/

/-- Structural boolean equality without `Decidable` instances. -/
noncomputable def boolEq : Bool → Bool → Bool
  | true, true => true
  | false, false => true
  | _, _ => false

/-- Pairwise boolean relation over two lists of equal length. -/
noncomputable def listRel {α β : Type} (r : α → β → Bool) :
    List α → List β → Bool
  | [], [] => true
  | x :: xs, y :: ys => r x y && listRel r xs ys
  | _, _ => false

/-- Structural equality on `ProjectionElem`. -/
noncomputable def projElemEq : ProjectionElem → ProjectionElem → Bool
  | .deref, .deref => true
  | .field idx₁ ty₁, .field idx₂ ty₂ => Nat.beq idx₁ idx₂ && MirTy.beq ty₁ ty₂
  | .unsupported, .unsupported => true
  | _, _ => false

/-- Structural equality on `Place`. -/
noncomputable def placeEq (p₁ p₂ : Place) : Bool :=
  Nat.beq p₁.localId p₂.localId && listRel projElemEq p₁.projection p₂.projection

/-- Structural equality on `ConstLit`. -/
noncomputable def constLitEq : ConstLit → ConstLit → Bool
  | .scalar b₁, .scalar b₂ => b₁ == b₂
  | .zeroSized, .zeroSized => true
  | _, _ => false

/-- Structural equality on `ConstOperand`. -/
noncomputable def constOpEq (c₁ c₂ : ConstOperand) : Bool :=
  MirTy.beq c₁.ty c₂.ty && constLitEq c₁.lit c₂.lit

/-- Structural equality on `BinOp`. -/
noncomputable def binOpEq : BinOp → BinOp → Bool
  | .add, .add | .addUnchecked, .addUnchecked | .addWithOverflow, .addWithOverflow
  | .sub, .sub | .subUnchecked, .subUnchecked | .subWithOverflow, .subWithOverflow
  | .mul, .mul | .mulUnchecked, .mulUnchecked | .mulWithOverflow, .mulWithOverflow
  | .div, .div | .rem, .rem
  | .bitXor, .bitXor | .bitAnd, .bitAnd | .bitOr, .bitOr
  | .shl, .shl | .shlUnchecked, .shlUnchecked
  | .shr, .shr | .shrUnchecked, .shrUnchecked
  | .eq, .eq | .lt, .lt | .le, .le | .ne, .ne | .ge, .ge | .gt, .gt
  | .offset, .offset => true
  | _, _ => false

/-- Structural equality on `UnOp`. -/
noncomputable def unOpEq : UnOp → UnOp → Bool
  | .not, .not | .neg, .neg | .ptrMetadata, .ptrMetadata => true
  | _, _ => false

/-- Structural equality on `Operand`. -/
noncomputable def operandEq : Operand → Operand → Bool
  | .copy p₁, .copy p₂ => placeEq p₁ p₂
  | .move p₁, .move p₂ => placeEq p₁ p₂
  | .constant c₁, .constant c₂ => constOpEq c₁ c₂
  | _, _ => false

/-- Structural equality on `Rvalue`. -/
noncomputable def rvalueEq : Rvalue → Rvalue → Bool
  | .use o₁, .use o₂ => operandEq o₁ o₂
  | .binaryOp op₁ l₁ r₁, .binaryOp op₂ l₂ r₂ =>
    binOpEq op₁ op₂ && operandEq l₁ l₂ && operandEq r₁ r₂
  | .unaryOp op₁ o₁, .unaryOp op₂ o₂ => unOpEq op₁ op₂ && operandEq o₁ o₂
  | .discriminant p₁, .discriminant p₂ => placeEq p₁ p₂
  | .ref m₁ p₁, .ref m₂ p₂ => Mutability.beq m₁ m₂ && placeEq p₁ p₂
  | .addressOf m₁ p₁, .addressOf m₂ p₂ => Mutability.beq m₁ m₂ && placeEq p₁ p₂
  | .aggregateTuple fs₁, .aggregateTuple fs₂ => listRel operandEq fs₁ fs₂
  | .unsupported, .unsupported => true
  | _, _ => false

/-- Structural equality on `StatementKind`. -/
noncomputable def stmtEq : StatementKind → StatementKind → Bool
  | .assign d₁ rv₁, .assign d₂ rv₂ => placeEq d₁ d₂ && rvalueEq rv₁ rv₂
  | .storageLive i₁, .storageLive i₂ => Nat.beq i₁ i₂
  | .storageDead i₁, .storageDead i₂ => Nat.beq i₁ i₂
  | .nop, .nop => true
  | .unsupported, .unsupported => true
  | _, _ => false

/-- Structural equality on `SwitchTargets`. -/
noncomputable def switchTargetsEq (t₁ t₂ : SwitchTargets) : Bool :=
  Nat.beq t₁.otherwise t₂.otherwise &&
    listRel (fun a b => (a.1 == b.1) && Nat.beq a.2 b.2) t₁.branches t₂.branches

/-- Structural equality on `UnwindAction`. -/
noncomputable def unwindActionEq : UnwindAction → UnwindAction → Bool
  | .continue_, .continue_ | .unreachable, .unreachable
  | .terminate, .terminate => true
  | .cleanup b₁, .cleanup b₂ => Nat.beq b₁ b₂
  | _, _ => false

/-- Structural equality on `AssertKind`. -/
noncomputable def assertKindEq : AssertKind → AssertKind → Bool
  | .overflow o₁, .overflow o₂ => binOpEq o₁ o₂
  | .overflowNeg, .overflowNeg | .divByZero, .divByZero | .remByZero, .remByZero
  | .boundsCheck, .boundsCheck | .misalignedPtrDeref, .misalignedPtrDeref
  | .nullPtrDeref, .nullPtrDeref | .unsupported, .unsupported => true
  | _, _ => false

/-- Structural equality on `Option BasicBlockId`. -/
noncomputable def optBbEq : Option BasicBlockId → Option BasicBlockId → Bool
  | none, none => true
  | some a, some b => Nat.beq a b
  | _, _ => false

/-- Structural equality on `TerminatorKind`. -/
noncomputable def termEq : TerminatorKind → TerminatorKind → Bool
  | .goto t₁, .goto t₂ => Nat.beq t₁ t₂
  | .switchInt d₁ ts₁, .switchInt d₂ ts₂ => operandEq d₁ d₂ && switchTargetsEq ts₁ ts₂
  | .return_, .return_ | .unreachable, .unreachable
  | .unwindResume, .unwindResume | .unsupported, .unsupported => true
  | .assert c₁ e₁ m₁ t₁ u₁, .assert c₂ e₂ m₂ t₂ u₂ =>
    operandEq c₁ c₂ && boolEq e₁ e₂ && assertKindEq m₁ m₂ &&
      Nat.beq t₁ t₂ && unwindActionEq u₁ u₂
  | .call fn₁ as₁ d₁ t₁ u₁, .call fn₂ as₂ d₂ t₂ u₂ =>
    Nat.beq fn₁ fn₂ && listRel operandEq as₁ as₂ && placeEq d₁ d₂ &&
      optBbEq t₁ t₂ && unwindActionEq u₁ u₂
  | _, _ => false

/-- Structural equality on `BasicBlock`. -/
noncomputable def bbEq (b₁ b₂ : BasicBlock) : Bool :=
  listRel stmtEq b₁.statements b₂.statements &&
    termEq b₁.terminator b₂.terminator &&
    boolEq b₁.cleanup b₂.cleanup

/-- Structural equality on `Body`. -/
noncomputable def bodyEq (b₁ b₂ : Body) : Bool :=
  listRel MirTy.beq b₁.locals b₂.locals &&
    Nat.beq b₁.argumentCount b₂.argumentCount &&
    listRel bbEq b₁.basicBlocks b₂.basicBlocks &&
    boolEq b₁.isUnsafe b₂.isUnsafe &&
    stringBeq b₁.identity b₂.identity

/-- Structural equality on `VerificationScope`. -/
noncomputable def scopeEq : VerificationScope → VerificationScope → Bool
  | .crate, .crate => true
  | .unit, .unit => true
  | _, _ => false

/-- Structural equality on `Program`. -/
noncomputable def programEq (p₁ p₂ : Program) : Bool :=
  listRel bodyEq p₁.bodies p₂.bodies &&
    Nat.beq p₁.entryDefId p₂.entryDefId &&
    Nat.beq p₁.pointerWidthBits p₂.pointerWidthBits &&
    Nat.beq p₁.mirProfileVersion p₂.mirProfileVersion &&
    scopeEq p₁.scope p₂.scope

/-- Observable terminal outcome in `M_unwind`: extends unmodified
`Trusted.MirSemantics.TerminalOut` (`returned`, `unwound`) with explicit
process termination (`aborted`, matching `UnwindAction.terminate` /
`UnwindTerminateReason::{Abi, InCleanup}`). -/
inductive UnwindOut where
  | returned (out : Out)
  | unwound (callerMem : CallerMemory := ⟨[]⟩)
  | aborted (callerMem : CallerMemory := ⟨[]⟩)

/-- Canonical embedding of `Trusted.MirSemantics.TerminalOut` into `UnwindOut`. -/
noncomputable def embedTerminalOut : TerminalOut → UnwindOut
  | .returned out => .returned out
  | .unwound mem => .unwound mem

/-- Partial projection of `UnwindOut` back into `Trusted.MirSemantics.TerminalOut`. -/
noncomputable def projectUnwindOut? : UnwindOut → Option TerminalOut
  | .returned out => some (.returned out)
  | .unwound mem => some (.unwound mem)
  | .aborted _ => none

/-- Suspended caller continuation waiting for a direct `TerminatorKind.call` to
either return normally (writing `_0` into `dst` and jumping to `target`) or
unwind (dispatching `unwind : UnwindAction`). -/
structure CallContUnw where
  callerFrame : FrameState
  dst : Place
  target : Option BasicBlockId
  unwind : UnwindAction

/-- Running machine state of `M_unwind`: active execution frame, suspended
caller continuation stack (head is immediate caller), and caller memory. -/
structure UnwindState where
  active : FrameState
  callStack : List CallContUnw := []
  callerMem : CallerMemory := ⟨[]⟩

/-- Embed a single-frame `Trusted.MirSemantics.State` into `UnwindState`. -/
noncomputable def embedStateUnw? (s : State) : Option UnwindState :=
  match s.frames with
  | [f] => some { active := f, callStack := [], callerMem := s.callerMem }
  | _ => none

/-- Project a single-frame `UnwindState` back to `Trusted.MirSemantics.State`. -/
noncomputable def projectStateUnw? (s : UnwindState) : Option State :=
  match s.callStack with
  | [] => some { frames := [s.active], callerMem := s.callerMem }
  | _ :: _ => none

/-- Project a single-frame `StepResult UnwindState UnwindOut` back to
`Trusted.MirSemantics.StepResult State TerminalOut`. -/
noncomputable def projectStepResultUnw? :
    StepResult UnwindState UnwindOut → Option (StepResult State TerminalOut)
  | .step s =>
    match projectStateUnw? s with
    | some s' => some (.step s')
    | none => none
  | .done out =>
    match projectUnwindOut? out with
    | some out' => some (.done out')
    | none => none
  | .fault k => some (.fault k)

/-- Initial machine state in `M_unwind`: reuses unmodified
`Trusted.MirSemantics.initState` verbatim so entry-body validation,
`hasStorageAnnotation`, and argument type checks match 1-for-1. -/
noncomputable def initStateUnw (p : Program) (q : Query) :
    Except FaultKind UnwindState :=
  match initState p q with
  | .error k => .error k
  | .ok s₀ =>
    match embedStateUnw? s₀ with
    | some u₀ => .ok u₀
    | none => .error .unsupported

/-- Sequential left-to-right argument evaluation for `TerminatorKind.call`,
reusing unmodified `Trusted.MirSemantics.evalOperandToSlot` so `Operand.move`
deinitialization and uninit/dead fault ordering match `rustc_const_eval`. -/
noncomputable def evalCallArgsUnw (bodyLocals : List MirTy)
    (locals : List LocalSlot) :
    List Operand → Except FaultKind (List Val × List LocalSlot)
  | [] => .ok ([], locals)
  | op :: rest =>
    match evalOperandToSlot bodyLocals locals op with
    | .error k => .error k
    | .ok (_, none, _) => .error .undefined
    | .ok (_, some v, locals₁) =>
      match evalCallArgsUnw bodyLocals locals₁ rest with
      | .error k => .error k
      | .ok (vs, locals₂) => .ok (v :: vs, locals₂)

/-- Initialize a callee's stack frame from validated evaluated call arguments
(reusing unmodified `Trusted.MirSemantics.initLocalsLoop`). -/
noncomputable def initCalleeFrameUnw (calleeDefId : DefId) (callee : Body)
    (argVals : List Val) : Except FaultKind FrameState :=
  if callee.basicBlocks.isEmpty then
    .error .unsupported
  else if !Nat.blt callee.argumentCount callee.locals.length then
    .error .unsupported
  else if !storageAnnotationsInBounds callee then
    .error .unsupported
  else if !callee.locals.all isSupportedScalarOrUnitTy then
    .error .unsupported
  else
    let paramTys := (callee.locals.drop 1).take callee.argumentCount
    if !checkArgsMatch argVals paramTys then
      .error .unsupported
    else
      .ok {
        defId := calleeDefId
        blockIdx := 0
        stmtIdx := 0
        locals := initLocalsLoop callee argVals 0 callee.locals
      }

/-- Jump to `padBb` inside `frame`, enforcing `bb.cleanup == true`
(`ControlFlow.lean:42-75` — landing pads entered via `UnwindAction.cleanup`
must be cleanup blocks). -/
noncomputable def enterCleanupBlockUnw (p : Program) (frame : FrameState)
    (rest : List CallContUnw) (mem : CallerMemory) (padBb : BasicBlockId) :
    StepResult UnwindState UnwindOut :=
  match Trusted.MirSemantics.getElem? p.bodies frame.defId with
  | none => .fault .unsupported
  | some body =>
    match Trusted.MirSemantics.getElem? body.basicBlocks padBb with
    | none => .fault .unsupported
    | some bb =>
      if !bb.cleanup then
        .fault .unsupported
      else
        .step {
          active := { frame with blockIdx := padBb, stmtIdx := 0 }
          callStack := rest
          callerMem := mem
        }

/-- Structural two-phase unwind propagation across `callStack`:
- `[]` (top-of-stack): exits cleanly with `.done (.unwound mem)`;
- `cont :: rest`: pops the callee without writing `cont.dst` and dispatches
  `cont.unwind` (`.cleanup padBb` enters `padBb` requiring `cleanup = true`;
  `.continue_` continues unwinding `rest`; `.unreachable` faults `.undefined`
  per `ControlFlow.lean:47`; `.terminate` terminates with `.done (.aborted mem)`). -/
noncomputable def dispatchUnwindStack (p : Program) (mem : CallerMemory) :
    List CallContUnw → StepResult UnwindState UnwindOut
  | [] => .done (.unwound mem)
  | cont :: rest =>
    match cont.unwind with
    | .cleanup padBb => enterCleanupBlockUnw p cont.callerFrame rest mem padBb
    | .continue_ => dispatchUnwindStack p mem rest
    | .unreachable => .fault .undefined
    | .terminate => .done (.aborted mem)

/-- Dispatch a local `UnwindAction` triggered inside `frame` (by a failing
`TerminatorKind.assert`):
- `.cleanup padBb`: jumps to cleanup block `padBb` in `frame` (`cleanup = true`);
- `.continue_`: unwinds out of `frame` across `callStack`;
- `.unreachable`: faults `.fault .undefined` (UB);
- `.terminate`: terminates with `.done (.aborted mem)`. -/
noncomputable def dispatchLocalUnwind (p : Program) (frame : FrameState)
    (callStack : List CallContUnw) (mem : CallerMemory) :
    UnwindAction → StepResult UnwindState UnwindOut
  | .cleanup padBb => enterCleanupBlockUnw p frame callStack mem padBb
  | .continue_ => dispatchUnwindStack p mem callStack
  | .unreachable => .fault .undefined
  | .terminate => .done (.aborted mem)

/-- Return normally from `callee` with value `retVal` to caller continuation
`cont` (`ControlFlow.lean:87-110`): requires unprojected `cont.dst`, writes
`retVal` via unmodified `Trusted.MirSemantics.writePlace`, and resumes at
`cont.target` (faulting `.undefined` if `cont.target = none`, i.e., returning
from a diverging `-> !` call). -/
noncomputable def returnToCallerUnw (p : Program) (retVal : Val)
    (cont : CallContUnw) (rest : List CallContUnw) (mem : CallerMemory) :
    StepResult UnwindState UnwindOut :=
  match Trusted.MirSemantics.getElem? p.bodies cont.callerFrame.defId with
  | none => .fault .unsupported
  | some callerBody =>
    if !cont.dst.projection.isEmpty then
      .fault .unsupported
    else
      match Trusted.MirSemantics.getElem? callerBody.locals cont.dst.localId with
      | none => .fault .unsupported
      | some dstTy =>
        match writePlace cont.callerFrame.locals cont.dst.localId dstTy retVal with
        | .error k => .fault k
        | .ok localsAfterWrite =>
          match cont.target with
          | none => .fault .undefined
          | some nextBb =>
            .step {
              active := {
                cont.callerFrame with
                blockIdx := nextBb
                stmtIdx := 0
                locals := localsAfterWrite
              }
              callStack := rest
              callerMem := mem
            }

/-- Single-step terminator evaluator in `M_unwind`, extending unmodified
`Trusted.MirSemantics.evalTerminator` with `TerminatorKind.unwindResume`,
`TerminatorKind.assert`, and `TerminatorKind.call` (both normal return and
unwinding). -/
noncomputable def evalTerminatorUnw (p : Program) (body : Body)
    (bb : BasicBlock) (frame : FrameState) (callStack : List CallContUnw)
    (mem : CallerMemory) : StepResult UnwindState UnwindOut :=
  match bb.terminator with
  | .goto target =>
    .step {
      active := { frame with blockIdx := target, stmtIdx := 0 }
      callStack
      callerMem := mem
    }
  | .return_ =>
    if bb.cleanup then
      .fault .unsupported
    else
      match Trusted.MirSemantics.getElem? frame.locals 0 with
      | some (.live (some retVal)) =>
        match callStack with
        | [] => .done (.returned ⟨retVal, mem⟩)
        | cont :: rest => returnToCallerUnw p retVal cont rest mem
      | some (.live none) | some .dead => .fault .undefined
      | none => .fault .unsupported
  | .unreachable =>
    .fault .undefined
  | .switchInt discr targets =>
    match evalPrimitiveOperand body.locals frame.locals discr with
    | .error k => .fault k
    | .ok (discrVal, localsAfterDiscr) =>
      let targetRes : Except FaultKind BasicBlockId :=
        match discrVal with
        | .scalar sv =>
          evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches
        | .bool b =>
          evalBoolSwitchBranches b targets.otherwise targets.branches
        | _ => .error .unsupported
      match targetRes with
      | .error k => .fault k
      | .ok target =>
        .step {
          active := {
            frame with
            blockIdx := target
            stmtIdx := 0
            locals := localsAfterDiscr
          }
          callStack
          callerMem := mem
        }
  | .unwindResume =>
    if !bb.cleanup then
      .fault .unsupported
    else
      dispatchUnwindStack p mem callStack
  | .assert cond expected _msg target unwind =>
    match evalPrimitiveOperand body.locals frame.locals cond with
    | .error k => .fault k
    | .ok (.bool b, localsAfterCond) =>
      let frame' := { frame with locals := localsAfterCond }
      if boolEq b expected then
        .step {
          active := { frame' with blockIdx := target, stmtIdx := 0 }
          callStack
          callerMem := mem
        }
      else
        dispatchLocalUnwind p frame' callStack mem unwind
    | .ok (_, _) => .fault .unsupported
  | .call calleeDefId args dst target unwind =>
    match evalCallArgsUnw body.locals frame.locals args with
    | .error k => .fault k
    | .ok (argVals, localsAfterArgs) =>
      match Trusted.MirSemantics.getElem? p.bodies calleeDefId with
      | none => .fault .unsupported
      | some calleeBody =>
        match initCalleeFrameUnw calleeDefId calleeBody argVals with
        | .error k => .fault k
        | .ok calleeFrame =>
          let cont : CallContUnw := {
            callerFrame := { frame with locals := localsAfterArgs }
            dst
            target
            unwind
          }
          .step {
            active := calleeFrame
            callStack := cont :: callStack
            callerMem := mem
          }
  | .unsupported => .fault .unsupported

/-- Total single-step evaluator of `M_unwind` over unmodified `Program`:
delegates statement execution directly to unmodified
`Trusted.MirSemantics.evalStatement`. -/
noncomputable def evalStepUnw (p : Program) (_c : Choice) (s : UnwindState) :
    StepResult UnwindState UnwindOut :=
  match Trusted.MirSemantics.getElem? p.bodies s.active.defId with
  | none => .fault .unsupported
  | some body =>
    match Trusted.MirSemantics.getElem? body.basicBlocks s.active.blockIdx with
    | none => .fault .unsupported
    | some bb =>
      match Trusted.MirSemantics.getElem? bb.statements s.active.stmtIdx with
      | some stmt =>
        match evalStatement body s.active s.callerMem stmt with
        | .fault k => .fault k
        | .done out => .done (embedTerminalOut out)
        | .step st' =>
          match st'.frames with
          | [f'] =>
            .step {
              active := f'
              callStack := s.callStack
              callerMem := st'.callerMem
            }
          | _ => .fault .unsupported
      | none =>
        if Nat.beq s.active.stmtIdx bb.statements.length then
          evalTerminatorUnw p body bb s.active s.callStack s.callerMem
        else
          .fault .unsupported

/-- Admissible demonic choice in `M_unwind` (deterministic: `c = 0`). -/
noncomputable def ValidChoiceUnw (_p : Program) (_s : UnwindState)
    (c : Choice) : Prop :=
  c = 0

/-- Small-step transition relation of `M_unwind`. -/
noncomputable def StepUnw (p : Program) (s : UnwindState)
    (res : StepResult UnwindState UnwindOut) : Prop :=
  ∃ c : Choice, ValidChoiceUnw p s c ∧ evalStepUnw p c s = res

/-- Finite-step reachability in `M_unwind`. -/
inductive ReachesUnw (p : Program) : UnwindState → UnwindState → Prop where
  | refl (s : UnwindState) : ReachesUnw p s s
  | tail {s₁ s₂ s₃ : UnwindState} :
      ReachesUnw p s₁ s₂ →
      StepUnw p s₂ (.step s₃) →
      ReachesUnw p s₁ s₃

/-- Outcome reachability from `(p, q)` in `M_unwind`. -/
noncomputable def ReachesResultUnw (p : Program) (q : Query)
    (res : StepResult UnwindState UnwindOut) : Prop :=
  match initStateUnw p q with
  | .error k => res = .fault k
  | .ok s₀ => ∃ s : UnwindState, ReachesUnw p s₀ s ∧ StepUnw p s res

/-- All-prefix well-formedness in `M_unwind` (no reachable `.fault`). -/
noncomputable def WellFormedUnw (p : Program) (q : Query) : Prop :=
  (∃ s₀ : UnwindState, initStateUnw p q = .ok s₀ ∧
    ∀ s : UnwindState, ReachesUnw p s₀ s → ∃ c : Choice, ValidChoiceUnw p s c) ∧
  (∀ k : FaultKind, ¬ ReachesResultUnw p q (.fault k))

/-- Observable terminal outcome in `M_unwind`. -/
noncomputable def BehaviorUnw (p : Program) (q : Query) (out : UnwindOut) :
    Prop :=
  ReachesResultUnw p q (.done out)

/-- Constructive divergence (`0` `Classical.choice`) in `M_unwind`. -/
noncomputable def DivergesUnw (p : Program) (q : Query) : Prop :=
  ∃ s₀ : UnwindState,
    initStateUnw p q = .ok s₀ ∧
    ∃ trace : Nat → UnwindState,
      trace 0 = s₀ ∧
      ∀ n : Nat, StepUnw p (trace n) (.step (trace (n + 1)))

/-- Partial-correctness postcondition satisfaction in `M_unwind`. -/
noncomputable def SatisfiesPostUnw (p : Program) (q : Query)
    (post : UnwindOut → Prop) : Prop :=
  WellFormedUnw p q ∧ ∀ out : UnwindOut, BehaviorUnw p q out → post out

/-- Lift a `TerminalOut → Prop` postcondition to `UnwindOut → Prop`
(rejecting `.aborted` unless explicitly permitted by a custom postcondition). -/
noncomputable def liftTerminalPost (post : TerminalOut → Prop) :
    UnwindOut → Prop
  | .returned out => post (.returned out)
  | .unwound mem => post (.unwound mem)
  | .aborted _ => False

/-- Per-body verification judgment in `M_unwind`, matching unmodified
`Trusted.MirSemantics.BodyVerified` verbatim! -/
noncomputable def BodyVerifiedUnw (p : Program) (defId : DefId) (body : Body)
    (safetyPre : List Val → Prop) : Prop :=
  Trusted.MirSemantics.getElem? p.bodies defId = some body ∧
  BodyStaticAdmitted p body = true ∧
  ∀ args : List Val,
    ValidEntryArgs body args →
    (body.isUnsafe = true → safetyPre args) →
    WellFormedUnw (entryProgForBody p defId) { args := args }

/-- Program-wide verification judgment in `M_unwind`, matching unmodified
`Trusted.MirSemantics.ProgramVerified` verbatim! -/
noncomputable def ProgramVerifiedUnw (p : Program) (specs : Specs) : Prop :=
  Nat.beq p.pointerWidthBits 64 = true ∧
  Nat.beq p.mirProfileVersion 1 = true ∧
  !p.bodies.isEmpty = true ∧
  Nat.blt p.entryDefId p.bodies.length = true ∧
  bodiesHaveUniqueIdentities p.bodies = true ∧
  (∀ (defId : DefId) (body : Body),
    Trusted.MirSemantics.getElem? p.bodies defId = some body →
    BodyVerifiedUnw p defId body (specs.safety body.identity)) ∧
  specs.property p

/-- Whole-crate theorem in `M_unwind`, matching unmodified
`Trusted.MirSemantics.CrateTheorem` verbatim! -/
noncomputable def CrateTheoremUnw (c : Crate) : Prop :=
  c.program.scope = .crate ∧ ProgramVerifiedUnw c.program c.specs

/-- Per-item proof-unit theorem in `M_unwind`, matching unmodified
`Trusted.MirSemantics.UnitTheorem` verbatim! -/
noncomputable def UnitTheoremUnw (c : Crate) : Prop :=
  c.program.scope = .unit ∧ ProgramVerifiedUnw c.program c.specs

/-- Full bidirectional semantic equivalence between two programs in `M_unwind`
across all queries, fault kinds, terminal outcomes, divergence, and
postconditions. -/
noncomputable def FullSemanticEquivUnw (p₁ p₂ : Program) : Prop :=
  (∀ q : Query, WellFormedUnw p₁ q ↔ WellFormedUnw p₂ q) ∧
  (∀ q : Query, ∀ out : UnwindOut,
    BehaviorUnw p₁ q out ↔ BehaviorUnw p₂ q out) ∧
  (∀ q : Query, ∀ k : FaultKind,
    ReachesResultUnw p₁ q (.fault k) ↔ ReachesResultUnw p₂ q (.fault k)) ∧
  (∀ q : Query, DivergesUnw p₁ q ↔ DivergesUnw p₂ q) ∧
  (∀ q : Query, ∀ post : UnwindOut → Prop,
    SatisfiesPostUnw p₁ q post ↔ SatisfiesPostUnw p₂ q post)

/-- Program-wide full equivalence across every entry body `defId`, preserving
program metadata, body count, identities, `isUnsafe`, and static admissibility. -/
noncomputable def ProgramEquivUnw (p₁ p₂ : Program) : Prop :=
  p₁.bodies.length = p₂.bodies.length ∧
  p₁.entryDefId = p₂.entryDefId ∧
  p₁.pointerWidthBits = p₂.pointerWidthBits ∧
  p₁.mirProfileVersion = p₂.mirProfileVersion ∧
  p₁.scope = p₂.scope ∧
  bodiesHaveUniqueIdentities p₁.bodies = bodiesHaveUniqueIdentities p₂.bodies ∧
  FullSemanticEquivUnw p₁ p₂ ∧
  (∀ defId : DefId,
    match Trusted.MirSemantics.getElem? p₁.bodies defId,
          Trusted.MirSemantics.getElem? p₂.bodies defId with
    | some b₁, some b₂ =>
      b₁.identity = b₂.identity ∧
      b₁.isUnsafe = b₂.isUnsafe ∧
      BodyStaticAdmitted p₁ b₁ = BodyStaticAdmitted p₂ b₂ ∧
      (∀ args : List Val, ValidEntryArgs b₁ args ↔ ValidEntryArgs b₂ args) ∧
      FullSemanticEquivUnw (entryProgForBody p₁ defId)
        (entryProgForBody p₂ defId)
    | none, none => True
    | _, _ => False)

/-- Extensionality requirement on `Specs.property` for transporting
`CrateTheoremUnw` / `UnitTheoremUnw` across semantically equivalent programs. -/
noncomputable def SpecsPropertyUnwInvariant (specs : Specs) : Prop :=
  ∀ p₁ p₂ : Program, ProgramEquivUnw p₁ p₂ → (specs.property p₁ ↔ specs.property p₂)

/-- Whether a terminator belongs to unmodified `Trusted.MirSemantics`'s
intraprocedural base fragment (no `.unwindResume`, `.assert`, or `.call`). -/
noncomputable def isBaseMirTerm : TerminatorKind → Bool
  | .goto _ | .switchInt _ _ | .return_ | .unreachable | .unsupported => true
  | .unwindResume | .assert _ _ _ _ _ | .call _ _ _ _ _ => false

/-- Whether a `Body` contains zero `.unwindResume`, `.assert`, or `.call`
terminators (so `M_unwind` coincides 1-for-1 with `Trusted.MirSemantics`). -/
noncomputable def isBaseMirBody (body : Body) : Bool :=
  body.basicBlocks.all (fun bb => isBaseMirTerm bb.terminator)

/-- Whether every body in `p` lies in `Trusted.MirSemantics`'s base fragment. -/
noncomputable def isBaseMirProgram (p : Program) : Bool :=
  p.bodies.all isBaseMirBody

/-! ## Part II: Decidable Certified Unwind-Elimination, `AbortUnwindingCalls`, & Unwind-Aware `MIR Inline` Checkers -/

/-- Check whether `cond : Operand` is a boolean constant equal to `expected`. -/
noncomputable def assertConstSatisfied (cond : Operand) (expected : Bool) :
    Bool :=
  match cond with
  | .constant c =>
    match evalConstLit c.ty c.lit with
    | .ok (.bool b) => boolEq b expected
    | _ => false
  | _ => false

/-- Check whether `TerminatorKind` can directly trigger an unwind in a body
given a boolean table `noUnwindFlags` of bodies certified never to unwind. -/
noncomputable def termCannotUnwind (noUnwindFlags : List Bool) :
    TerminatorKind → Bool
  | .goto _ | .switchInt _ _ | .return_ | .unreachable | .unsupported => true
  | .unwindResume => false
  | .assert cond expected _ _ unwind =>
    assertConstSatisfied cond expected ||
      match unwind with
      | .terminate | .unreachable => true
      | .continue_ | .cleanup _ => false
  | .call calleeId _ _ _ unwind =>
    (match Trusted.MirSemantics.getElem? noUnwindFlags calleeId with
     | some true => true
     | _ => false) ||
      match unwind with
      | .terminate | .unreachable => true
      | .continue_ | .cleanup _ => false

/-- Verify that `noUnwindFlags` is a sound inductive interprocedural
`CannotUnwind` summary for `p`:
1. `noUnwindFlags.length == p.bodies.length`, and
2. For every body `defId` with `noUnwindFlags[defId] = true`, every basic block
   has `termCannotUnwind noUnwindFlags bb.terminator = true` (notice that a
   body whose calls/asserts only target `noUnwindFlags = true` callees or
   `.terminate`/`.unreachable` unwind actions and contains no `.unwindResume`
   can NEVER unwind out of its frame — even under arbitrary loops or mutual
   recursion). -/
noncomputable def checkNoUnwindSummaryLoop (p : Program)
    (noUnwindFlags : List Bool) : Nat → List Bool → Bool
  | _, [] => true
  | idx, flag :: rest =>
    (if !flag then true
     else
       match Trusted.MirSemantics.getElem? p.bodies idx with
       | none => false
       | some body =>
         body.basicBlocks.all (fun bb =>
           termCannotUnwind noUnwindFlags bb.terminator)) &&
    checkNoUnwindSummaryLoop p noUnwindFlags (idx + 1) rest

/-- Top-level decidable verifier for an inductive `CannotUnwind` summary. -/
noncomputable def checkNoUnwindSummary (p : Program)
    (noUnwindFlags : List Bool) : Bool :=
  Nat.beq noUnwindFlags.length p.bodies.length &&
    checkNoUnwindSummaryLoop p noUnwindFlags 0 noUnwindFlags

/-- Tighten a single terminator under `AbortUnwindingCalls`
(`compiler/rustc_mir_transform/src/abort_unwinding_calls.rs:118-124`):
- Any `.call calleeId ... unwind` whose callee is certified `noUnwind` has its
  unwind action tightened to `.unreachable`;
- Any `.assert cond expected msg target unwind` whose `cond` is a constant
  equal to `expected` has its unwind action tightened to `.unreachable`. -/
noncomputable def rewriteTermAbortUnw (noUnwindFlags : List Bool)
    (bb : BasicBlock) : BasicBlock :=
  let term' :=
    match bb.terminator with
    | .call calleeId args dst target unwind =>
      match Trusted.MirSemantics.getElem? noUnwindFlags calleeId with
      | some true => .call calleeId args dst target .unreachable
      | _ => .call calleeId args dst target unwind
    | .assert cond expected msg target unwind =>
      if assertConstSatisfied cond expected then
        .assert cond expected msg target .unreachable
      else
        .assert cond expected msg target unwind
    | other => other
  { bb with terminator := term' }

/-- Apply `AbortUnwindingCalls` terminator tightening to every body in `p`. -/
noncomputable def applyAbortUnwindingCalls (p : Program)
    (noUnwindFlags : List Bool) : Option Program :=
  if !checkNoUnwindSummary p noUnwindFlags then
    none
  else
    let bodies' :=
      p.bodies.map (fun body =>
        { body with
          basicBlocks := body.basicBlocks.map (rewriteTermAbortUnw noUnwindFlags) })
    some { p with bodies := bodies' }

/-- Decidable checker for `AbortUnwindingCalls` terminator tightening. -/
noncomputable def checkAbortUnwindingCalls (pSrc : Program)
    (noUnwindFlags : List Bool) (pTgt : Program) : Bool :=
  match applyAbortUnwindingCalls pSrc noUnwindFlags with
  | none => false
  | some pOut => programEq pOut pTgt

/-- Always-failing `.assert` terminator encoding `UnwindTerminate` cleanly
inside unmodified `Trusted.MirAst` (steps directly to `.done (.aborted mem)`). -/
noncomputable def mkTerminateTerm : TerminatorKind :=
  .assert (.constant { ty := .bool, lit := .scalar (BitVec.ofNat 128 0) })
    true .overflowNeg 0 .terminate

/-- Rewrite a single block in the entry body for `-C panic=abort` ABI enforcement. -/
noncomputable def rewriteBbPanicAbort (bb : BasicBlock) : BasicBlock :=
  let term' :=
    match bb.terminator with
    | .unwindResume =>
      if bb.cleanup then mkTerminateTerm else .unwindResume
    | .assert cond expected msg target .continue_ =>
      .assert cond expected msg target .terminate
    | .call calleeId args dst target .continue_ =>
      .call calleeId args dst target .terminate
    | other => other
  { bb with terminator := term' }

/-- Apply `-C panic=abort` ABI transformation to the entry body of `p`.
Requires that no body in `p` recursively calls `p.entryDefId`, so the
transformed entry body only runs as the bottommost stack frame (`callStack = []`). -/
noncomputable def bodyCallsDefId (targetDef : DefId) (body : Body) : Bool :=
  body.basicBlocks.any (fun bb =>
    match bb.terminator with
    | .call fn _ _ _ _ => Nat.beq fn targetDef
    | _ => false)

noncomputable def applyPanicAbortEntryTransform (p : Program) : Option Program :=
  if p.bodies.any (bodyCallsDefId p.entryDefId) then
    none
  else
    match Trusted.MirSemantics.getElem? p.bodies p.entryDefId with
    | none => none
    | some entryBody =>
      let entryBody' := {
        entryBody with
        basicBlocks := entryBody.basicBlocks.map rewriteBbPanicAbort
      }
      match setElem? p.bodies p.entryDefId entryBody' with
      | none => none
      | some bodies' => some { p with bodies := bodies' }

/-- Decidable checker for `-C panic=abort` ABI transformation on entry body. -/
noncomputable def checkPanicAbortEntryTransform (pSrc pTgt : Program) : Bool :=
  match applyPanicAbortEntryTransform pSrc with
  | none => false
  | some pOut => programEq pOut pTgt

/-- Apply trivial-assert elimination on `(defId, bbIdx)`: replaces a
constant-satisfied `.assert` with `.goto target`. -/
noncomputable def applyDischargeTrivialAssert (p : Program) (defId : DefId)
    (bbIdx : BasicBlockId) : Option Program :=
  match Trusted.MirSemantics.getElem? p.bodies defId with
  | none => none
  | some body =>
    match Trusted.MirSemantics.getElem? body.basicBlocks bbIdx with
    | none => none
    | some bb =>
      match bb.terminator with
      | .assert cond expected _ target _ =>
        if !assertConstSatisfied cond expected then
          none
        else
          let bb' := { bb with terminator := .goto target }
          match setElem? body.basicBlocks bbIdx bb' with
          | none => none
          | some bbs' =>
            let body' := { body with basicBlocks := bbs' }
            match setElem? p.bodies defId body' with
            | none => none
            | some bodies' => some { p with bodies := bodies' }
      | _ => none

/-- Decidable checker for trivial-assert elimination. -/
noncomputable def checkDischargeTrivialAssert (pSrc : Program) (defId : DefId)
    (bbIdx : BasicBlockId) (pTgt : Program) : Bool :=
  match applyDischargeTrivialAssert pSrc defId bbIdx with
  | none => false
  | some pOut => programEq pOut pTgt

/-- Look up the new compacted index of `oldBb` inside a sorted `keepBlocks` list. -/
noncomputable def findNewBbIdx (oldBb : BasicBlockId) :
    Nat → List BasicBlockId → Option BasicBlockId
  | _, [] => none
  | idx, k :: ks =>
    if Nat.beq k oldBb then some idx
    else findNewBbIdx oldBb (idx + 1) ks

/-- Check whether `keepBlocks` is strictly increasing and bounded by `nBlocks`. -/
noncomputable def isStrictSortedBounded (nBlocks : Nat) :
    Option Nat → List BasicBlockId → Bool
  | _, [] => true
  | none, k :: ks => Nat.blt k nBlocks && isStrictSortedBounded nBlocks (some k) ks
  | some prev, k :: ks =>
    Nat.blt prev k && Nat.blt k nBlocks && isStrictSortedBounded nBlocks (some k) ks

/-- Remap an `UnwindAction` through `keepBlocks` (only `.cleanup b` needs a
valid compacted target). -/
noncomputable def remapUnwindAction (keepBlocks : List BasicBlockId) :
    UnwindAction → Option UnwindAction
  | .continue_ => some .continue_
  | .unreachable => some .unreachable
  | .terminate => some .terminate
  | .cleanup b =>
    match findNewBbIdx b 0 keepBlocks with
    | some b' => some (.cleanup b')
    | none => none

/-- Remap a list of `(BitVec 128 × BasicBlockId)` switch branches. -/
noncomputable def remapSwitchBranches (keepBlocks : List BasicBlockId) :
    List (BitVec 128 × BasicBlockId) → Option (List (BitVec 128 × BasicBlockId))
  | [] => some []
  | (v, b) :: rest =>
    match findNewBbIdx b 0 keepBlocks, remapSwitchBranches keepBlocks rest with
    | some b', some rest' => some ((v, b') :: rest')
    | _, _ => none

/-- Remap a `TerminatorKind` through `keepBlocks`; returns `none` if ANY
reachable normal or `.cleanup` target is missing from `keepBlocks`. -/
noncomputable def remapTerminator (keepBlocks : List BasicBlockId) :
    TerminatorKind → Option TerminatorKind
  | .goto t =>
    match findNewBbIdx t 0 keepBlocks with
    | some t' => some (.goto t')
    | none => none
  | .switchInt discr ts =>
    match findNewBbIdx ts.otherwise 0 keepBlocks,
          remapSwitchBranches keepBlocks ts.branches with
    | some oth', some brs' =>
      some (.switchInt discr { branches := brs', otherwise := oth' })
    | _, _ => none
  | .return_ => some .return_
  | .unreachable => some .unreachable
  | .unwindResume => some .unwindResume
  | .unsupported => some .unsupported
  | .assert cond exp msg t u =>
    match findNewBbIdx t 0 keepBlocks, remapUnwindAction keepBlocks u with
    | some t', some u' => some (.assert cond exp msg t' u')
    | _, _ => none
  | .call fn args dst tOpt u =>
    let tOpt' : Option (Option BasicBlockId) :=
      match tOpt with
      | none => some none
      | some t =>
        match findNewBbIdx t 0 keepBlocks with
        | some t' => some (some t')
        | none => none
    match tOpt', remapUnwindAction keepBlocks u with
    | some tRes, some u' => some (.call fn args dst tRes u')
    | _, _ => none

/-- Build the compacted basic-block list for `keepBlocks`. -/
noncomputable def compactKeepBlocks (origBbs : List BasicBlock)
    (allKeep : List BasicBlockId) : List BasicBlockId → Option (List BasicBlock)
  | [] => some []
  | k :: ks =>
    match Trusted.MirSemantics.getElem? origBbs k with
    | none => none
    | some bb =>
      match remapTerminator allKeep bb.terminator,
            compactKeepBlocks origBbs allKeep ks with
      | some term', some rest' =>
        some ({ bb with terminator := term' } :: rest')
      | _, _ => none

/-- Check that `hasStorageAnnotation b₁ loc == hasStorageAnnotation b₂ loc` for
every local `loc < n` (`CE5` guard preventing silent `DeadLocal` UB erasure
when pruning unreachable cleanup pads). -/
noncomputable def allLocalsStorageAnnotEq (b₁ b₂ : Body) : Nat → Bool
  | 0 => true
  | n + 1 =>
    boolEq (hasStorageAnnotation b₁ n) (hasStorageAnnotation b₂ n) &&
      allLocalsStorageAnnotEq b₁ b₂ n

/-- Apply `hasStorageAnnotation`-preserving dead-block / dead-cleanup-pad
pruning (`abort_unwinding_calls.rs:140` guarded by `allLocalsStorageAnnotEq`). -/
noncomputable def applyPruneDeadCleanupBlocks (p : Program) (defId : DefId)
    (keepBlocks : List BasicBlockId) : Option Program :=
  match Trusted.MirSemantics.getElem? p.bodies defId with
  | none => none
  | some body =>
    if !isStrictSortedBounded body.basicBlocks.length none keepBlocks then
      none
    else
      match keepBlocks with
      | 0 :: _ =>
        match compactKeepBlocks body.basicBlocks keepBlocks keepBlocks with
        | none => none
        | some bbs' =>
          let body' := { body with basicBlocks := bbs' }
          if !boolEq (storageAnnotationsInBounds body)
                (storageAnnotationsInBounds body') ||
              !allLocalsStorageAnnotEq body body' body.locals.length then
            none
          else
            match setElem? p.bodies defId body' with
            | none => none
            | some bodies' => some { p with bodies := bodies' }
      | _ => none

/-- Decidable checker for `hasStorageAnnotation`-preserving dead-block pruning. -/
noncomputable def checkPruneDeadCleanupBlocks (pSrc : Program) (defId : DefId)
    (keepBlocks : List BasicBlockId) (pTgt : Program) : Bool :=
  match applyPruneDeadCleanupBlocks pSrc defId keepBlocks with
  | none => false
  | some pOut => programEq pOut pTgt

/-! ### Unwind-Aware `MIR Inline` Splicing (`compiler/rustc_mir_transform/src/inline.rs`) -/

/-- Specification of a single unwind-aware call site to inline. -/
structure UnwindInlineSite where
  callerDefId : DefId
  callBlock : BasicBlockId
  calleeDefId : DefId

/-- Shift a `Place`'s local index by `locOff`. -/
noncomputable def shiftPlaceUnw (locOff : Nat) (pl : Place) : Place :=
  { pl with localId := pl.localId + locOff }

/-- Shift an `Operand`'s local references by `locOff`. -/
noncomputable def shiftOperandUnw (locOff : Nat) : Operand → Operand
  | .copy pl => .copy (shiftPlaceUnw locOff pl)
  | .move pl => .move (shiftPlaceUnw locOff pl)
  | .constant c => .constant c

/-- Shift an `Rvalue`'s local references by `locOff`. -/
noncomputable def shiftRvalueUnw (locOff : Nat) : Rvalue → Rvalue
  | .use op => .use (shiftOperandUnw locOff op)
  | .binaryOp op l r => .binaryOp op (shiftOperandUnw locOff l) (shiftOperandUnw locOff r)
  | .unaryOp op o => .unaryOp op (shiftOperandUnw locOff o)
  | .discriminant pl => .discriminant (shiftPlaceUnw locOff pl)
  | .ref m pl => .ref m (shiftPlaceUnw locOff pl)
  | .addressOf m pl => .addressOf m (shiftPlaceUnw locOff pl)
  | .aggregateTuple fs => .aggregateTuple (fs.map (shiftOperandUnw locOff))
  | .unsupported => .unsupported

/-- Shift a `StatementKind`'s local references by `locOff`. -/
noncomputable def shiftStmtUnw (locOff : Nat) : StatementKind → StatementKind
  | .assign dst rv => .assign (shiftPlaceUnw locOff dst) (shiftRvalueUnw locOff rv)
  | .storageLive id => .storageLive (id + locOff)
  | .storageDead id => .storageDead (id + locOff)
  | .nop => .nop
  | .unsupported => .unsupported

/-- Shift an `UnwindAction` inside an inlined callee:
- `.cleanup b` shifts to `.cleanup (b + bbOff)`;
- `.continue_` redirects to `.cleanup unwindExitBb`;
- `.unreachable` and `.terminate` remain unchanged. -/
noncomputable def shiftCalleeUnwindAction (bbOff : Nat)
    (unwindExitBb : BasicBlockId) : UnwindAction → UnwindAction
  | .cleanup b => .cleanup (b + bbOff)
  | .continue_ => .cleanup unwindExitBb
  | .unreachable => .unreachable
  | .terminate => .terminate

/-- Shift a callee terminator when splicing into `caller`. -/
noncomputable def shiftCalleeTerminator (locOff bbOff : Nat)
    (normalExitBb unwindExitBb : BasicBlockId) (isCleanup : Bool) :
    TerminatorKind → TerminatorKind
  | .goto t => .goto (t + bbOff)
  | .switchInt discr ts =>
    .switchInt (shiftOperandUnw locOff discr)
      {
        branches := ts.branches.map (fun br => (br.1, br.2 + bbOff))
        otherwise := ts.otherwise + bbOff
      }
  | .return_ =>
    if isCleanup then .return_ else .goto normalExitBb
  | .unreachable => .unreachable
  | .unwindResume =>
    if isCleanup then .goto unwindExitBb else .unwindResume
  | .assert cond exp msg t u =>
    .assert (shiftOperandUnw locOff cond) exp msg (t + bbOff)
      (shiftCalleeUnwindAction bbOff unwindExitBb u)
  | .call fn args dst tOpt u =>
    .call fn (args.map (shiftOperandUnw locOff)) (shiftPlaceUnw locOff dst)
      (match tOpt with | none => none | some t => some (t + bbOff))
      (shiftCalleeUnwindAction bbOff unwindExitBb u)
  | .unsupported => .unsupported

/-- Shift a single callee `BasicBlock` during unwind-aware inlining. -/
noncomputable def shiftCalleeBlock (locOff bbOff : Nat)
    (normalExitBb unwindExitBb : BasicBlockId) (bb : BasicBlock) : BasicBlock :=
  {
    statements := bb.statements.map (shiftStmtUnw locOff)
    terminator := shiftCalleeTerminator locOff bbOff normalExitBb unwindExitBb
      bb.cleanup bb.terminator
    cleanup := bb.cleanup
  }

/-- Emit `StorageLive (locOff + i)` for every `i < n` that starts live at
callee entry (`i <= argumentCount` or `!hasStorageAnnotation callee i`),
matching `Trusted.MirSemantics.initLocalsLoop` verbatim. -/
noncomputable def mkCalleeEntryStorageLive (callee : Body) (locOff : Nat) :
    Nat → Nat → List StatementKind
  | _, 0 => []
  | i, rem + 1 =>
    let rest := mkCalleeEntryStorageLive callee locOff (i + 1) rem
    if Nat.ble i callee.argumentCount || !hasStorageAnnotation callee i then
      .storageLive (locOff + i) :: rest
    else
      rest

/-- Emit `StorageDead (base + i)` for every `i < n`. -/
noncomputable def mkAllStorageDead (base : Nat) : Nat → List StatementKind
  | 0 => []
  | n + 1 => .storageDead (base + n) :: mkAllStorageDead base n

/-- Emit sequential argument-binding assignments `_(locOff + 1 + idx) = arg`. -/
noncomputable def mkArgBindStmts (locOff : Nat) :
    Nat → List Operand → List StatementKind
  | _, [] => []
  | idx, op :: ops =>
    .assign { localId := locOff + 1 + idx, projection := [] } (.use op) ::
      mkArgBindStmts locOff (idx + 1) ops

noncomputable def placeLocalLt (n : Nat) (pl : Place) : Bool :=
  Nat.blt pl.localId n

noncomputable def operandLocalsLt (n : Nat) : Operand → Bool
  | .copy pl | .move pl => placeLocalLt n pl
  | .constant _ => true

noncomputable def rvalueLocalsLt (n : Nat) : Rvalue → Bool
  | .use op => operandLocalsLt n op
  | .binaryOp _ l r => operandLocalsLt n l && operandLocalsLt n r
  | .unaryOp _ o => operandLocalsLt n o
  | .discriminant pl | .ref _ pl | .addressOf _ pl => placeLocalLt n pl
  | .aggregateTuple fs => fs.all (operandLocalsLt n)
  | .unsupported => true

noncomputable def stmtLocalsLtAndNoDead0 (n : Nat) : StatementKind → Bool
  | .assign dst rv => placeLocalLt n dst && rvalueLocalsLt n rv
  | .storageLive id => Nat.blt id n
  | .storageDead id => !Nat.beq id 0 && Nat.blt id n
  | .nop | .unsupported => true

noncomputable def unwindActionBlocksLt (nBbs : Nat) (bbs : List BasicBlock) :
    UnwindAction → Bool
  | .continue_ | .unreachable | .terminate => true
  | .cleanup b =>
    Nat.blt b nBbs &&
      match Trusted.MirSemantics.getElem? bbs b with
      | some pad => pad.cleanup
      | none => false

noncomputable def termWellScoped (nLocs nBbs : Nat) (bbs : List BasicBlock) :
    TerminatorKind → Bool
  | .goto t => Nat.blt t nBbs
  | .switchInt d ts =>
    operandLocalsLt nLocs d && Nat.blt ts.otherwise nBbs &&
      ts.branches.all (fun br => Nat.blt br.2 nBbs)
  | .return_ | .unreachable | .unwindResume | .unsupported => true
  | .assert c _ _ t u =>
    operandLocalsLt nLocs c && Nat.blt t nBbs &&
      unwindActionBlocksLt nBbs bbs u
  | .call _ args dst tOpt u =>
    args.all (operandLocalsLt nLocs) && placeLocalLt nLocs dst &&
      (match tOpt with | none => true | some t => Nat.blt t nBbs) &&
      unwindActionBlocksLt nBbs bbs u

/-- Check that `callee` is statically admissible for unwind-aware inlining. -/
noncomputable def calleeUnwindInlineAdmitted (callee : Body) : Bool :=
  !callee.basicBlocks.isEmpty &&
    Nat.blt callee.argumentCount callee.locals.length &&
    storageAnnotationsInBounds callee &&
    callee.locals.all isSupportedScalarOrUnitTy &&
    callee.basicBlocks.all (fun bb =>
      bb.statements.all (stmtLocalsLtAndNoDead0 callee.locals.length) &&
      termWellScoped callee.locals.length callee.basicBlocks.length
        callee.basicBlocks bb.terminator)

noncomputable def callerStmtLocalsLt (n : Nat) : StatementKind → Bool
  | .assign dst rv => placeLocalLt n dst && rvalueLocalsLt n rv
  | .storageLive id | .storageDead id => Nat.blt id n
  | .nop | .unsupported => true

noncomputable def unwindActionBlocksOnlyLt (nBbs : Nat) : UnwindAction → Bool
  | .continue_ | .unreachable | .terminate => true
  | .cleanup b => Nat.blt b nBbs

noncomputable def callerTermInBounds (nLocs nBbs : Nat) :
    TerminatorKind → Bool
  | .goto t => Nat.blt t nBbs
  | .switchInt d ts =>
    operandLocalsLt nLocs d && Nat.blt ts.otherwise nBbs &&
      ts.branches.all (fun br => Nat.blt br.2 nBbs)
  | .return_ | .unreachable | .unwindResume | .unsupported => true
  | .assert c _ _ t u =>
    operandLocalsLt nLocs c && Nat.blt t nBbs &&
      unwindActionBlocksOnlyLt nBbs u
  | .call _ args dst tOpt u =>
    args.all (operandLocalsLt nLocs) && placeLocalLt nLocs dst &&
      (match tOpt with | none => true | some t => Nat.blt t nBbs) &&
      unwindActionBlocksOnlyLt nBbs u

/-- Check that `caller` is statically well-scoped so appending callee locals
and basic blocks cannot turn an out-of-bounds local or block fault in `caller`
into an in-bounds access to the spliced callee (`CE11`). -/
noncomputable def callerUnwindInlineAdmitted (caller : Body) : Bool :=
  Nat.blt caller.argumentCount caller.locals.length &&
    storageAnnotationsInBounds caller &&
    caller.basicBlocks.all (fun bb =>
      bb.statements.all (callerStmtLocalsLt caller.locals.length) &&
      callerTermInBounds caller.locals.length caller.basicBlocks.length
        bb.terminator)

/-- Check that a caller's `dst` place is unprojected with local index
`< caller.locals.length` and declared type matching `callee.locals[0]`. -/
noncomputable def callDstCompatible (caller callee : Body) (dst : Place) :
    Bool :=
  dst.projection.isEmpty &&
    match Trusted.MirSemantics.getElem? caller.locals dst.localId,
          Trusted.MirSemantics.getElem? callee.locals 0 with
    | some dstTy, some retTy => MirTy.beq dstTy retTy
    | _, _ => false

noncomputable def operandTy? (bodyLocals : List MirTy) :
    Operand → Option MirTy
  | .copy pl | .move pl =>
    if pl.projection.isEmpty then
      Trusted.MirSemantics.getElem? bodyLocals pl.localId
    else
      none
  | .constant c => some c.ty

noncomputable def callArgsTyMatch (callerLocals : List MirTy) :
    List Operand → List MirTy → Bool
  | [], [] => true
  | op :: ops, ty :: tys =>
    match operandTy? callerLocals op with
    | some opTy => MirTy.beq opTy ty && callArgsTyMatch callerLocals ops tys
    | none => false
  | _, _ => false

/-- Terminator emitted at the end of `unwindExitBlock` (`cleanup = true`)
corresponding to `callerUnwind`. -/
noncomputable def callerUnwindToExitTerm : UnwindAction → TerminatorKind
  | .cleanup padBb => .goto padBb
  | .continue_ => .unwindResume
  | .unreachable => .unreachable
  | .terminate => mkTerminateTerm

/-- Apply unwind-aware `MIR Inline` splicing at `site` (`UnwindInlineSite`). -/
noncomputable def applyInlineWithUnwind (p : Program)
    (site : UnwindInlineSite) : Option Program :=
  if Nat.beq site.callerDefId site.calleeDefId then
    none
  else
    match Trusted.MirSemantics.getElem? p.bodies site.callerDefId,
          Trusted.MirSemantics.getElem? p.bodies site.calleeDefId with
    | some caller, some callee =>
      if !calleeUnwindInlineAdmitted callee ||
          !callerUnwindInlineAdmitted caller then
        none
      else
        match Trusted.MirSemantics.getElem? caller.basicBlocks site.callBlock with
        | none => none
        | some callBb =>
          if callBb.cleanup then
            none
          else
            match callBb.terminator with
            | .call cDef args dst target callerUnwind =>
              let paramTys := (callee.locals.drop 1).take callee.argumentCount
              let targetOk : Bool :=
                match target with
                | none => true
                | some tBb =>
                  match Trusted.MirSemantics.getElem? caller.basicBlocks tBb with
                  | some tData => !tData.cleanup
                  | none => false
              let unwindOk : Bool :=
                match callerUnwind with
                | .continue_ | .unreachable | .terminate => true
                | .cleanup pBb =>
                  match Trusted.MirSemantics.getElem? caller.basicBlocks pBb with
                  | some pData => pData.cleanup
                  | none => false
              if !Nat.beq cDef site.calleeDefId ||
                  !callDstCompatible caller callee dst ||
                  !callArgsTyMatch caller.locals args paramTys ||
                  !targetOk || !unwindOk then
                none
              else
                let locOff := caller.locals.length
                let bbOff := caller.basicBlocks.length
                let normalExitBb := bbOff + callee.basicBlocks.length
                let unwindExitBb := normalExitBb + 1
                let entryLives :=
                  mkCalleeEntryStorageLive callee locOff 0 callee.locals.length
                let argBinds := mkArgBindStmts locOff 0 args
                let callBb' : BasicBlock := {
                  statements := callBb.statements ++ entryLives ++ argBinds
                  terminator := .goto bbOff
                  cleanup := false
                }
                let shiftedCalleeBbs :=
                  callee.basicBlocks.map
                    (shiftCalleeBlock locOff bbOff normalExitBb unwindExitBb)
                let deads := mkAllStorageDead locOff callee.locals.length
                let normalExitBlock : BasicBlock := {
                  statements :=
                    (.assign dst (.use (.move { localId := locOff, projection := [] }))) ::
                      deads
                  terminator :=
                    match target with
                    | some tBb => .goto tBb
                    | none => .unreachable
                  cleanup := false
                }
                let unwindExitBlock : BasicBlock := {
                  statements := deads
                  terminator := callerUnwindToExitTerm callerUnwind
                  cleanup := true
                }
                match setElem? caller.basicBlocks site.callBlock callBb' with
                | none => none
                | some callerBbsUpdated =>
                  let caller' : Body := {
                    caller with
                    locals := caller.locals ++ callee.locals
                    basicBlocks :=
                      callerBbsUpdated ++ shiftedCalleeBbs ++
                        [normalExitBlock, unwindExitBlock]
                  }
                  match setElem? p.bodies site.callerDefId caller' with
                  | none => none
                  | some bodies' => some { p with bodies := bodies' }
            | _ => none
    | _, _ => none

/-- Decidable checker for single-site unwind-aware MIR inlining. -/
noncomputable def checkInlineWithUnwind (pSrc : Program)
    (site : UnwindInlineSite) (pTgt : Program) : Bool :=
  match applyInlineWithUnwind pSrc site with
  | none => false
  | some pOut => programEq pOut pTgt

/-- Single certified unwind-lowering / optimization step. -/
inductive UnwindOptStep where
  | inlineWithUnwind (site : UnwindInlineSite)
  | dischargeTrivialAssert (defId : DefId) (bbIdx : BasicBlockId)
  | abortUnwindingCalls (noUnwindFlags : List Bool)
  | pruneDeadCleanupBlocks (defId : DefId) (keepBlocks : List BasicBlockId)

/-- Apply one certified `UnwindOptStep`. -/
noncomputable def applyUnwindOptStep (p : Program) :
    UnwindOptStep → Option Program
  | .inlineWithUnwind site => applyInlineWithUnwind p site
  | .dischargeTrivialAssert defId bbIdx => applyDischargeTrivialAssert p defId bbIdx
  | .abortUnwindingCalls flags => applyAbortUnwindingCalls p flags
  | .pruneDeadCleanupBlocks defId keep => applyPruneDeadCleanupBlocks p defId keep

/-- Check one certified `UnwindOptStep`. -/
noncomputable def checkUnwindOptStep (pSrc : Program) (step : UnwindOptStep)
    (pTgt : Program) : Bool :=
  match applyUnwindOptStep pSrc step with
  | none => false
  | some pOut => programEq pOut pTgt

/-- Finite trace of certified unwind-lowering steps. -/
abbrev UnwindOptTrace := List UnwindOptStep

/-- Check a finite trace of certified `UnwindOptStep`s from `pSrc` to `pTgt`. -/
noncomputable def checkUnwindOptTrace :
    Program → UnwindOptTrace → Program → Bool
  | pSrc, [], pTgt => programEq pSrc pTgt
  | pSrc, step :: rest, pTgt =>
    match applyUnwindOptStep pSrc step with
    | none => false
    | some pMid => checkUnwindOptTrace pMid rest pTgt

/-- Post-lowering intraprocedural equivalence over unmodified
`Trusted.MirSemantics` (matching `F1-5`..`F1-12` for vertical composition). -/
noncomputable def FullSemanticEquivBase (p₁ p₂ : Program) : Prop :=
  (∀ q : Query, WellFormed p₁ q ↔ WellFormed p₂ q) ∧
  (∀ q : Query, ∀ out : TerminalOut, Behavior p₁ q out ↔ Behavior p₂ q out) ∧
  (∀ q : Query, ∀ k : FaultKind,
    ReachesResult p₁ q (.fault k) ↔ ReachesResult p₂ q (.fault k)) ∧
  (∀ q : Query, Diverges p₁ q ↔ Diverges p₂ q) ∧
  (∀ q : Query, ∀ post : TerminalOut → Prop,
    SatisfiesPost p₁ q post ↔ SatisfiesPost p₂ q post)

/-! ### Slice: F1_13_Common.lean -/

-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.




/-! ### Boolean, Nat, List, & Structural Equality Reflection Lemmas -/

private theorem bool_and_true {a b : Bool} (h : (a && b) = true) :
    a = true ∧ b = true := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | cases h

private theorem bool_and_intro {a b : Bool} (ha : a = true) (hb : b = true) :
    (a && b) = true := by
  rw [ha, hb]; rfl

private theorem bool_or_true {a b : Bool} (h : (a || b) = true) :
    a = true ∨ b = true := by
  cases a <;> cases b <;> first | exact Or.inl rfl | exact Or.inr rfl | cases h

private theorem bool_not_true {a : Bool} (h : (!a) = true) : a = false := by
  cases a <;> first | rfl | cases h

private theorem bool_not_false {a : Bool} (h : (!a) = false) : a = true := by
  cases a <;> first | rfl | cases h

private theorem boolEq_eq {a b : Bool} (h : boolEq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

private theorem boolEq_refl (a : Bool) : boolEq a a = true := by
  cases a <;> rfl

private theorem if_bool_true {α : Type} {c : Bool} {t e : α} (h : c = true) :
    (if c then t else e) = t := by
  rw [h]; rfl

private theorem if_bool_false {α : Type} {c : Bool} {t e : α} (h : c = false) :
    (if c then t else e) = e := by
  rw [h]; rfl

private theorem nat_beq_eq : ∀ {a b : Nat}, Nat.beq a b = true → a = b
  | 0, 0, _ => rfl
  | 0, _ + 1, h => by cases h
  | _ + 1, 0, h => by cases h
  | a + 1, b + 1, h => congrArg Nat.succ (nat_beq_eq h)

private theorem nat_beq_refl : ∀ (a : Nat), Nat.beq a a = true
  | 0 => rfl
  | a + 1 => nat_beq_refl a

private theorem nat_ne_of_beq_false {a b : Nat} (h : Nat.beq a b = false) : a ≠ b := by
  intro heq
  subst heq
  rw [nat_beq_refl] at h
  cases h

private theorem nat_beq_false_of_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b with
  | false => rfl
  | true => exact False.elim (h (nat_beq_eq hb))

private theorem nat_blt_lt : ∀ {a b : Nat}, Nat.blt a b = true → a < b
  | 0, 0, h => by cases h
  | 0, _ + 1, _ => Nat.zero_lt_succ _
  | _ + 1, 0, h => by cases h
  | a + 1, b + 1, h => Nat.succ_lt_succ (nat_blt_lt h)

private theorem nat_lt_blt : ∀ {a b : Nat}, a < b → Nat.blt a b = true
  | 0, 0, h => False.elim (Nat.not_lt_zero 0 h)
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, h => False.elim (Nat.not_lt_zero _ h)
  | a + 1, b + 1, h => @nat_lt_blt a b (Nat.lt_of_succ_lt_succ h)

private theorem nat_ble_le : ∀ {a b : Nat}, Nat.ble a b = true → a ≤ b
  | 0, _, _ => Nat.zero_le _
  | _ + 1, 0, h => by cases h
  | a + 1, b + 1, h => Nat.succ_le_succ (nat_ble_le h)

private theorem nat_le_ble : ∀ {a b : Nat}, a ≤ b → Nat.ble a b = true
  | 0, _, _ => rfl
  | _ + 1, 0, h => False.elim (Nat.not_succ_le_zero _ h)
  | a + 1, b + 1, h => @nat_le_ble a b (Nat.le_of_succ_le_succ h)

private theorem nat_gt_ble_false {a b : Nat} (h : b < a) : Nat.ble a b = false := by
  cases hb : Nat.ble a b with
  | false => rfl
  | true => exact False.elim (Nat.not_le_of_gt h (nat_ble_le hb))

private theorem uint8_beq_eq {a b : UInt8} (h : (a == b) = true) : a = b :=
  eq_of_beq h

private theorem uint8_list_beq_eq : ∀ {a b : List UInt8}, List.beq a b = true → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | x :: xs, y :: ys, h => by
    dsimp [List.beq] at h
    let ⟨hxy, hrest⟩ := bool_and_true h
    rw [uint8_beq_eq hxy, uint8_list_beq_eq hrest]

private theorem stringBeq_eq {a b : String} (h : stringBeq a b = true) : a = b := by
  unfold stringBeq at h
  have hL : a.toByteArray.data.toList = b.toByteArray.data.toList :=
    uint8_list_beq_eq h
  cases a with
  | ofByteArray ba _ =>
    cases b with
    | ofByteArray bb _ =>
      cases ba with
      | mk da =>
        cases bb with
        | mk db =>
          cases da with
          | mk la =>
            cases db with
            | mk lb =>
              dsimp at hL
              subst hL
              rfl

private theorem intWidth_beq_eq {a b : IntWidth} (h : IntWidth.beq a b = true) :
    a = b := by
  cases a <;> cases b <;> first | rfl | cases h

private theorem mutability_beq_eq {a b : Mutability} (h : Mutability.beq a b = true) :
    a = b := by
  cases a <;> cases b <;> first | rfl | cases h

private theorem natListBeq_eq : ∀ {a b : List Nat}, natListBeq a b = true → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | x :: xs, y :: ys, h => by
    dsimp [natListBeq] at h
    let ⟨h1, h2⟩ := bool_and_true h
    rw [nat_beq_eq h1, natListBeq_eq h2]

private theorem enumTagRepr_beq_eq {a b : EnumTagRepr}
    (h : EnumTagRepr.beq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h | (
    dsimp [EnumTagRepr.beq] at h
    let ⟨h1, h2⟩ := bool_and_true h
    rw [intWidth_beq_eq h1, eq_of_beq h2])

private theorem enumTy_beq_eq {a b : EnumTy} (h : EnumTy.beq a b = true) : a = b := by
  cases a with
  | mk id1 w1 s1 tr1 ds1 =>
    cases b with
    | mk id2 w2 s2 tr2 ds2 =>
      dsimp [EnumTy.beq] at h
      let ⟨h1234, h5⟩ := bool_and_true h
      let ⟨h123, h4⟩ := bool_and_true h1234
      let ⟨h12, h3⟩ := bool_and_true h123
      let ⟨h1, h2⟩ := bool_and_true h12
      rw [nat_beq_eq h1, intWidth_beq_eq h2, eq_of_beq h3,
          enumTagRepr_beq_eq h4, natListBeq_eq h5]

mutual
  private theorem mirTy_beq_eq : ∀ {a b : MirTy}, MirTy.beq a b = true → a = b
    | .bool, .bool, _ => rfl
    | .int w1 s1, .int w2 s2, h => by
      dsimp [MirTy.beq] at h
      let ⟨h1, h2⟩ := bool_and_true h
      rw [intWidth_beq_eq h1, eq_of_beq h2]
    | .unit, .unit, _ => rfl
    | .never, .never, _ => rfl
    | .enum e1, .enum e2, h => congrArg MirTy.enum (enumTy_beq_eq h)
    | .tuple fs1, .tuple fs2, h =>
      congrArg MirTy.tuple (mirTy_beqList_eq h)
    | .ref m1 p1, .ref m2 p2, h => by
      dsimp [MirTy.beq] at h
      let ⟨h1, h2⟩ := bool_and_true h
      rw [mutability_beq_eq h1, mirTy_beq_eq h2]
    | .rawPtr m1 p1, .rawPtr m2 p2, h => by
      dsimp [MirTy.beq] at h
      let ⟨h1, h2⟩ := bool_and_true h
      rw [mutability_beq_eq h1, mirTy_beq_eq h2]
    | .unsupported, .unsupported, _ => rfl
    | .bool, .int _ _, h | .bool, .unit, h | .bool, .never, h
    | .bool, .enum _, h | .bool, .tuple _, h | .bool, .ref _ _, h
    | .bool, .rawPtr _ _, h | .bool, .unsupported, h
    | .int _ _, .bool, h | .int _ _, .unit, h | .int _ _, .never, h
    | .int _ _, .enum _, h | .int _ _, .tuple _, h | .int _ _, .ref _ _, h
    | .int _ _, .rawPtr _ _, h | .int _ _, .unsupported, h
    | .unit, .bool, h | .unit, .int _ _, h | .unit, .never, h
    | .unit, .enum _, h | .unit, .tuple _, h | .unit, .ref _ _, h
    | .unit, .rawPtr _ _, h | .unit, .unsupported, h
    | .never, .bool, h | .never, .int _ _, h | .never, .unit, h
    | .never, .enum _, h | .never, .tuple _, h | .never, .ref _ _, h
    | .never, .rawPtr _ _, h | .never, .unsupported, h
    | .enum _, .bool, h | .enum _, .int _ _, h | .enum _, .unit, h
    | .enum _, .never, h | .enum _, .tuple _, h | .enum _, .ref _ _, h
    | .enum _, .rawPtr _ _, h | .enum _, .unsupported, h
    | .tuple _, .bool, h | .tuple _, .int _ _, h | .tuple _, .unit, h
    | .tuple _, .never, h | .tuple _, .enum _, h | .tuple _, .ref _ _, h
    | .tuple _, .rawPtr _ _, h | .tuple _, .unsupported, h
    | .ref _ _, .bool, h | .ref _ _, .int _ _, h | .ref _ _, .unit, h
    | .ref _ _, .never, h | .ref _ _, .enum _, h | .ref _ _, .tuple _, h
    | .ref _ _, .rawPtr _ _, h | .ref _ _, .unsupported, h
    | .rawPtr _ _, .bool, h | .rawPtr _ _, .int _ _, h | .rawPtr _ _, .unit, h
    | .rawPtr _ _, .never, h | .rawPtr _ _, .enum _, h | .rawPtr _ _, .tuple _, h
    | .rawPtr _ _, .ref _ _, h | .rawPtr _ _, .unsupported, h
    | .unsupported, .bool, h | .unsupported, .int _ _, h
    | .unsupported, .unit, h | .unsupported, .never, h
    | .unsupported, .enum _, h | .unsupported, .tuple _, h
    | .unsupported, .ref _ _, h | .unsupported, .rawPtr _ _, h => by cases h

  private theorem mirTy_beqList_eq :
      ∀ {a b : List MirTy}, MirTy.beqList a b = true → a = b
    | [], [], _ => rfl
    | [], _ :: _, h => by cases h
    | _ :: _, [], h => by cases h
    | x :: xs, y :: ys, h => by
      dsimp [MirTy.beqList] at h
      let ⟨h1, h2⟩ := bool_and_true h
      rw [mirTy_beq_eq h1, mirTy_beqList_eq h2]
end

private theorem listRel_eq {α : Type} {r : α → α → Bool}
    (hr : ∀ {a b}, r a b = true → a = b) :
    ∀ {xs ys : List α}, listRel r xs ys = true → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | x :: xs, y :: ys, h => by
    dsimp [listRel] at h
    let ⟨h1, h2⟩ := bool_and_true h
    rw [hr h1, listRel_eq hr h2]

private theorem projElemEq_eq {a b : ProjectionElem} (h : projElemEq a b = true) :
    a = b := by
  cases a <;> cases b <;> first | rfl | cases h | (
    dsimp [projElemEq] at h
    let ⟨h1, h2⟩ := bool_and_true h
    rw [nat_beq_eq h1, mirTy_beq_eq h2])

private theorem placeEq_eq {a b : Place} (h : placeEq a b = true) : a = b := by
  cases a with
  | mk i1 p1 =>
    cases b with
    | mk i2 p2 =>
      dsimp [placeEq] at h
      let ⟨h1, h2⟩ := bool_and_true h
      rw [nat_beq_eq h1, listRel_eq projElemEq_eq h2]

private theorem constLitEq_eq {a b : ConstLit} (h : constLitEq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h | (
    dsimp [constLitEq] at h
    rw [eq_of_beq h])

private theorem constOpEq_eq {a b : ConstOperand} (h : constOpEq a b = true) :
    a = b := by
  cases a with
  | mk t1 l1 =>
    cases b with
    | mk t2 l2 =>
      dsimp [constOpEq] at h
      let ⟨h1, h2⟩ := bool_and_true h
      rw [mirTy_beq_eq h1, constLitEq_eq h2]

private theorem binOpEq_eq {a b : BinOp} (h : binOpEq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

private theorem unOpEq_eq {a b : UnOp} (h : unOpEq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

private theorem operandEq_eq {a b : Operand} (h : operandEq a b = true) : a = b := by
  cases a <;> cases b <;> (first
    | cases h
    | exact congrArg Operand.copy (placeEq_eq h)
    | exact congrArg Operand.move (placeEq_eq h)
    | exact congrArg Operand.constant (constOpEq_eq h))

private theorem rvalueEq_eq {a b : Rvalue} (h : rvalueEq a b = true) : a = b := by
  cases a <;> cases b <;> (first
    | rfl
    | cases h
    | exact congrArg Rvalue.use (operandEq_eq h)
    | (dsimp [rvalueEq] at h
       let ⟨h12, h3⟩ := bool_and_true h
       let ⟨h1, h2⟩ := bool_and_true h12
       rw [binOpEq_eq h1, operandEq_eq h2, operandEq_eq h3])
    | (dsimp [rvalueEq] at h
       let ⟨h1, h2⟩ := bool_and_true h
       rw [unOpEq_eq h1, operandEq_eq h2])
    | exact congrArg Rvalue.discriminant (placeEq_eq h)
    | (dsimp [rvalueEq] at h
       let ⟨h1, h2⟩ := bool_and_true h
       rw [mutability_beq_eq h1, placeEq_eq h2])
    | (dsimp [rvalueEq] at h
       let ⟨h1, h2⟩ := bool_and_true h
       rw [mutability_beq_eq h1, placeEq_eq h2])
    | exact congrArg Rvalue.aggregateTuple (listRel_eq operandEq_eq h))

private theorem stmtEq_eq {a b : StatementKind} (h : stmtEq a b = true) : a = b := by
  cases a <;> cases b <;> (first
    | rfl
    | cases h
    | (dsimp [stmtEq] at h
       let ⟨h1, h2⟩ := bool_and_true h
       rw [placeEq_eq h1, rvalueEq_eq h2])
    | exact congrArg StatementKind.storageLive (nat_beq_eq h)
    | exact congrArg StatementKind.storageDead (nat_beq_eq h))

private theorem switchTargetsEq_eq {a b : SwitchTargets}
    (h : switchTargetsEq a b = true) : a = b := by
  cases a with
  | mk br1 o1 =>
    cases b with
    | mk br2 o2 =>
      dsimp [switchTargetsEq] at h
      let ⟨hO, hB⟩ := bool_and_true h
      have hBrEq : br1 = br2 :=
        listRel_eq (fun {p q} hpq => by
          cases p; cases q
          dsimp at hpq
          let ⟨hp1, hp2⟩ := bool_and_true hpq
          rw [eq_of_beq hp1, nat_beq_eq hp2]) hB
      rw [nat_beq_eq hO, hBrEq]

private theorem unwindActionEq_eq {a b : UnwindAction} (h : unwindActionEq a b = true) :
    a = b := by
  cases a <;> cases b <;> (first
    | rfl
    | cases h
    | exact congrArg UnwindAction.cleanup (nat_beq_eq h))

private theorem assertKindEq_eq {a b : AssertKind} (h : assertKindEq a b = true) :
    a = b := by
  cases a <;> cases b <;> (first
    | rfl
    | cases h
    | exact congrArg AssertKind.overflow (binOpEq_eq h))

private theorem optBbEq_eq {a b : Option BasicBlockId} (h : optBbEq a b = true) :
    a = b := by
  cases a <;> cases b <;> (first
    | rfl
    | cases h
    | exact congrArg Option.some (nat_beq_eq h))

private theorem termEq_eq {a b : TerminatorKind} (h : termEq a b = true) : a = b := by
  cases a <;> cases b <;> (first
    | rfl
    | cases h
    | exact congrArg TerminatorKind.goto (nat_beq_eq h)
    | (dsimp [termEq] at h
       let ⟨h1, h2⟩ := bool_and_true h
       rw [operandEq_eq h1, switchTargetsEq_eq h2])
    | (dsimp [termEq] at h
       let ⟨h1234, h5⟩ := bool_and_true h
       let ⟨h123, h4⟩ := bool_and_true h1234
       let ⟨h12, h3⟩ := bool_and_true h123
       let ⟨h1, h2⟩ := bool_and_true h12
       rw [operandEq_eq h1, boolEq_eq h2, assertKindEq_eq h3,
           nat_beq_eq h4, unwindActionEq_eq h5])
    | (dsimp [termEq] at h
       let ⟨h1234, h5⟩ := bool_and_true h
       let ⟨h123, h4⟩ := bool_and_true h1234
       let ⟨h12, h3⟩ := bool_and_true h123
       let ⟨h1, h2⟩ := bool_and_true h12
       rw [nat_beq_eq h1, listRel_eq operandEq_eq h2, placeEq_eq h3,
           optBbEq_eq h4, unwindActionEq_eq h5]))

private theorem bbEq_eq {a b : BasicBlock} (h : bbEq a b = true) : a = b := by
  cases a with
  | mk s1 t1 c1 =>
    cases b with
    | mk s2 t2 c2 =>
      dsimp [bbEq] at h
      let ⟨h12, h3⟩ := bool_and_true h
      let ⟨h1, h2⟩ := bool_and_true h12
      rw [listRel_eq stmtEq_eq h1, termEq_eq h2, boolEq_eq h3]

private theorem bodyEq_eq {a b : Body} (h : bodyEq a b = true) : a = b := by
  cases a with
  | mk ac1 l1 bb1 u1 id1 =>
    cases b with
    | mk ac2 l2 bb2 u2 id2 =>
      dsimp [bodyEq] at h
      let ⟨h1234, h5⟩ := bool_and_true h
      let ⟨h123, h4⟩ := bool_and_true h1234
      let ⟨h12, h3⟩ := bool_and_true h123
      let ⟨h1, h2⟩ := bool_and_true h12
      rw [listRel_eq mirTy_beq_eq h1, nat_beq_eq h2, listRel_eq bbEq_eq h3,
          boolEq_eq h4, stringBeq_eq h5]

private theorem scopeEq_eq {a b : VerificationScope} (h : scopeEq a b = true) :
    a = b := by
  cases a <;> cases b <;> first | rfl | cases h

private theorem programEq_eq {a b : Program} (h : programEq a b = true) : a = b := by
  cases a with
  | mk bs1 e1 pw1 v1 sc1 =>
    cases b with
    | mk bs2 e2 pw2 v2 sc2 =>
      dsimp [programEq] at h
      let ⟨h1234, h5⟩ := bool_and_true h
      let ⟨h123, h4⟩ := bool_and_true h1234
      let ⟨h12, h3⟩ := bool_and_true h123
      let ⟨h1, h2⟩ := bool_and_true h12
      rw [listRel_eq bodyEq_eq h1, nat_beq_eq h2, nat_beq_eq h3,
          nat_beq_eq h4, scopeEq_eq h5]

/-! ### List Indexing, `setElem?`, `List.all`, `List.any`, & `List.map` Lemmas -/

private theorem getElem?_some_lt {α : Type} :
    ∀ {xs : List α} {i : Nat} {x : α},
      Trusted.MirSemantics.getElem? xs i = some x → i < xs.length
  | [], _, _, h => by cases h
  | _ :: _, 0, _, _ => Nat.zero_lt_succ _
  | _ :: _, _ + 1, _, h => Nat.succ_lt_succ (getElem?_some_lt h)

private theorem getElem?_none_ge {α : Type} :
    ∀ {xs : List α} {i : Nat},
      Trusted.MirSemantics.getElem? xs i = none → xs.length ≤ i
  | [], _, _ => Nat.zero_le _
  | _ :: _, 0, h => by cases h
  | _ :: _, _ + 1, h => Nat.succ_le_succ (getElem?_none_ge h)

private theorem getElem?_none_of_ge {α : Type} :
    ∀ {xs : List α} {i : Nat},
      xs.length ≤ i → Trusted.MirSemantics.getElem? xs i = none
  | [], _, _ => rfl
  | _ :: _, 0, h => False.elim (Nat.not_succ_le_zero _ h)
  | _ :: xs, i + 1, h => @getElem?_none_of_ge α xs i (Nat.le_of_succ_le_succ h)

private theorem getElem?_some_of_lt {α : Type} :
    ∀ (xs : List α) (i : Nat),
      i < xs.length → ∃ x, Trusted.MirSemantics.getElem? xs i = some x
  | [], _, h => False.elim (Nat.not_lt_zero _ h)
  | x :: _, 0, _ => ⟨x, rfl⟩
  | _ :: xs, i + 1, h => getElem?_some_of_lt xs i (Nat.lt_of_succ_lt_succ h)

private theorem getElem?_map {α β : Type} (f : α → β) :
    ∀ (xs : List α) (i : Nat),
      Trusted.MirSemantics.getElem? (xs.map f) i =
        match Trusted.MirSemantics.getElem? xs i with
        | some x => some (f x)
        | none => none
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: xs, i + 1 => getElem?_map f xs i

private theorem getElem?_append_left {α : Type} :
    ∀ {xs ys : List α} {i : Nat},
      i < xs.length →
      Trusted.MirSemantics.getElem? (xs ++ ys) i =
        Trusted.MirSemantics.getElem? xs i
  | [], _, _, h => False.elim (Nat.not_lt_zero _ h)
  | _ :: _, _, 0, _ => rfl
  | _ :: xs, ys, i + 1, h =>
    @getElem?_append_left α xs ys i (Nat.lt_of_succ_lt_succ h)

private theorem getElem?_append_right {α : Type} :
    ∀ (xs ys : List α) (j : Nat),
      Trusted.MirSemantics.getElem? (xs ++ ys) (xs.length + j) =
        Trusted.MirSemantics.getElem? ys j
  | [], _, j => by dsimp [List.length]; rw [Nat.zero_add]
  | _ :: xs, ys, j => by
    dsimp [List.length]
    rw [Nat.succ_add]
    exact getElem?_append_right xs ys j

private theorem getElem?_append_right_comm {α : Type} (xs ys : List α) (j : Nat) :
    Trusted.MirSemantics.getElem? (xs ++ ys) (j + xs.length) =
      Trusted.MirSemantics.getElem? ys j := by
  rw [Nat.add_comm]
  exact getElem?_append_right xs ys j

private theorem setElem?_length {α : Type} :
    ∀ {xs xs' : List α} {i : Nat} {v : α},
      setElem? xs i v = some xs' → xs'.length = xs.length
  | [], _, _, _, h => by cases h
  | _ :: _, _, 0, _, h => by injection h with heq; rw [← heq]; rfl
  | _ :: xs, _, i + 1, v, h => by
    dsimp [setElem?] at h
    cases hs : setElem? xs i v with
    | none => rw [hs] at h; cases h
    | some rest =>
      rw [hs] at h
      injection h with heq
      rw [← heq]
      exact congrArg Nat.succ (setElem?_length hs)

private theorem setElem?_getElem?_same {α : Type} :
    ∀ {xs xs' : List α} {i : Nat} {v : α},
      setElem? xs i v = some xs' →
      Trusted.MirSemantics.getElem? xs' i = some v
  | [], _, _, _, h => by cases h
  | _ :: _, _, 0, _, h => by injection h with heq; rw [← heq]; rfl
  | _ :: xs, _, i + 1, v, h => by
    dsimp [setElem?] at h
    cases hs : setElem? xs i v with
    | none => rw [hs] at h; cases h
    | some rest =>
      rw [hs] at h
      injection h with heq
      rw [← heq]
      exact @setElem?_getElem?_same α xs rest i v hs

private theorem setElem?_getElem?_ne {α : Type} :
    ∀ {xs xs' : List α} {i j : Nat} {v : α},
      setElem? xs i v = some xs' →
      j ≠ i →
      Trusted.MirSemantics.getElem? xs' j = Trusted.MirSemantics.getElem? xs j
  | [], _, _, _, _, h, _ => by cases h
  | _ :: _, _, 0, 0, _, _, hne => False.elim (hne rfl)
  | _ :: _, _, 0, _ + 1, _, h, _ => by injection h with heq; rw [← heq]; rfl
  | _ :: xs, _, i + 1, 0, v, h, _ => by
    dsimp [setElem?] at h
    cases hs : setElem? xs i v with
    | none => rw [hs] at h; cases h
    | some rest => rw [hs] at h; injection h with heq; rw [← heq]; rfl
  | _ :: xs, _, i + 1, j + 1, v, h, hne => by
    dsimp [setElem?] at h
    cases hs : setElem? xs i v with
    | none => rw [hs] at h; cases h
    | some rest =>
      rw [hs] at h
      injection h with heq
      rw [← heq]
      exact @setElem?_getElem?_ne α xs rest i j v hs (fun eq => hne (congrArg Nat.succ eq))

private theorem setElem?_some_of_lt {α : Type} :
    ∀ (xs : List α) (i : Nat) (v : α),
      i < xs.length → ∃ xs', setElem? xs i v = some xs'
  | [], _, _, h => False.elim (Nat.not_lt_zero _ h)
  | _ :: xs, 0, v, _ => ⟨v :: xs, rfl⟩
  | x :: xs, i + 1, v, h => by
    let ⟨rest, hr⟩ := setElem?_some_of_lt xs i v (Nat.lt_of_succ_lt_succ h)
    exact ⟨x :: rest, by dsimp [setElem?]; rw [hr]⟩

private theorem list_all_getElem? {α : Type} {p : α → Bool} :
    ∀ {xs : List α} {i : Nat} {x : α},
      xs.all p = true → Trusted.MirSemantics.getElem? xs i = some x → p x = true
  | [], _, _, _, hg => by cases hg
  | _ :: _, 0, _, ha, hg => by
    injection hg with heq; subst heq
    dsimp [List.all] at ha
    exact (bool_and_true ha).1
  | _ :: _, _ + 1, _, ha, hg => by
    dsimp [List.all] at ha
    exact list_all_getElem? (bool_and_true ha).2 hg

private theorem list_all_of_getElem? {α : Type} {p : α → Bool} :
    ∀ {xs : List α},
      (∀ i x, Trusted.MirSemantics.getElem? xs i = some x → p x = true) →
      xs.all p = true
  | [], _ => rfl
  | x :: xs, h => by
    dsimp [List.all]
    exact bool_and_intro (h 0 x rfl)
      (list_all_of_getElem? (fun i y hy => h (i + 1) y hy))

private theorem list_any_false_getElem? {α : Type} {p : α → Bool} :
    ∀ {xs : List α} {i : Nat} {x : α},
      xs.any p = false → Trusted.MirSemantics.getElem? xs i = some x → p x = false
  | [], _, _, _, hg => by cases hg
  | _ :: _, 0, _, ha, hg => by
    injection hg with heq; subst heq
    dsimp [List.any] at ha
    cases hpx : p _ with
    | false => rfl
    | true => rw [hpx] at ha; cases ha
  | x :: xs, i + 1, y, ha, hg => by
    dsimp [List.any] at ha
    cases hpx : p x with
    | true => rw [hpx] at ha; cases ha
    | false =>
      rw [hpx] at ha
      exact list_any_false_getElem? ha hg

private theorem list_all_append {α : Type} (p : α → Bool) :
    ∀ (xs ys : List α), (xs ++ ys).all p = (xs.all p && ys.all p)
  | [], ys => by dsimp [List.all]; cases ys.all p <;> rfl
  | x :: xs, ys => by
    dsimp [List.all]
    rw [list_all_append p xs ys]
    cases p x <;> cases xs.all p <;> cases ys.all p <;> rfl

private theorem list_all_map {α β : Type} (f : α → β) (p : β → Bool) :
    ∀ (xs : List α), (xs.map f).all p = xs.all (fun x => p (f x))
  | [] => rfl
  | x :: xs => by dsimp [List.map, List.all]; rw [list_all_map f p xs]

/-! ### Constructive Deterministic Outcomes -> Full Equivalence & Stuttering Simulation Combinator (`0` `Classical.choice`) -/

private theorem reachesUnw_trans {p : Program} {s₁ s₂ s₃ : UnwindState}
    (h12 : ReachesUnw p s₁ s₂) (h23 : ReachesUnw p s₂ s₃) :
    ReachesUnw p s₁ s₃ := by
  induction h23 with
  | refl => exact h12
  | tail _ hSt ih => exact ReachesUnw.tail ih hSt

private theorem c_reachesUnw_head_det {p : Program} {s₁ s₂ s₃ : UnwindState}
    (hStep : evalStepUnw p 0 s₁ = .step s₂)
    (hRest : ReachesUnw p s₂ s₃) :
    ReachesUnw p s₁ s₃ :=
  reachesUnw_trans (ReachesUnw.tail (ReachesUnw.refl s₁) ⟨0, rfl, hStep⟩) hRest

/-- Step `s` once in `p`, staying at `s` if terminal or faulting. -/
private noncomputable def stepOrSelfUnw (p : Program) (s : UnwindState) : UnwindState :=
  match evalStepUnw p 0 s with
  | .step s' => s'
  | _ => s

/-- Deterministic `n`-step iterator in `M_unwind`. -/
private noncomputable def iterUnw (p : Program) (s₀ : UnwindState) : Nat → UnwindState
  | 0 => s₀
  | n + 1 => stepOrSelfUnw p (iterUnw p s₀ n)

/-- Step-counted reachability in `M_unwind`. -/
private inductive ReachesNUnw (p : Program) :
    Nat → UnwindState → UnwindState → Prop where
  | zero (s : UnwindState) : ReachesNUnw p 0 s s
  | succ {n : Nat} {s₁ s₂ s₃ : UnwindState} :
      evalStepUnw p 0 s₁ = .step s₂ →
      ReachesNUnw p n s₂ s₃ →
      ReachesNUnw p (n + 1) s₁ s₃

/-- Positive-step reachability (`≥ 1` step) in `M_unwind`. -/
private noncomputable def ReachesPlusUnw (p : Program) (s₁ s₂ : UnwindState) : Prop :=
  ∃ n : Nat, ReachesNUnw p (n + 1) s₁ s₂

private theorem reachesNUnw_to_reachesUnw {p : Program} :
    ∀ {n : Nat} {s₁ s₂ : UnwindState},
      ReachesNUnw p n s₁ s₂ → ReachesUnw p s₁ s₂
  | 0, s, _, .zero _ => ReachesUnw.refl s
  | _ + 1, _, _, .succ hStep hRest =>
    c_reachesUnw_head_det hStep (reachesNUnw_to_reachesUnw hRest)

private theorem reachesNUnw_trans {p : Program} :
    ∀ {n m : Nat} {s₁ s₂ s₃ : UnwindState},
      ReachesNUnw p n s₁ s₂ →
      ReachesNUnw p m s₂ s₃ →
      ReachesNUnw p (n + m) s₁ s₃
  | 0, _, _, _, _, .zero _, h2 => by rw [Nat.zero_add]; exact h2
  | n + 1, m, _, _, _, .succ hStep h1, h2 => by
    rw [Nat.succ_add]
    exact ReachesNUnw.succ hStep (reachesNUnw_trans h1 h2)

private theorem reachesUnw_to_reachesNUnw {p : Program} {s₁ s₂ : UnwindState}
    (h : ReachesUnw p s₁ s₂) : ∃ n, ReachesNUnw p n s₁ s₂ := by
  induction h with
  | refl => exact ⟨0, ReachesNUnw.zero _⟩
  | tail _ hStep ih =>
    let ⟨n, hn⟩ := ih
    let ⟨c, hc, hEv⟩ := hStep
    cases hc
    exact ⟨n + 1, reachesNUnw_trans hn (ReachesNUnw.succ hEv (ReachesNUnw.zero _))⟩

/-- Determinism of `ReachesNUnw` prefix alignment: if `s` reaches `s₁` in `d`
steps and reaches terminal/faulting `t` in `m` steps, then `d ≤ m` and `s₁`
reaches `t` in `m - d` steps. -/
private theorem reachesNUnw_det_split {p : Program} {t : UnwindState}
    (hNoStepT : ∀ s', evalStepUnw p 0 t ≠ .step s') :
    ∀ {d m : Nat} {s s₁ : UnwindState},
      ReachesNUnw p d s s₁ →
      ReachesNUnw p m s t →
      d ≤ m ∧ ReachesNUnw p (m - d) s₁ t
  | 0, m, _, _, .zero _, hM => ⟨Nat.zero_le m, hM⟩
  | d + 1, 0, s, s₁, .succ hStep _, .zero _ =>
    False.elim (hNoStepT _ hStep)
  | d + 1, m + 1, s, s₁, .succ hStepD hD, .succ hStepM hM => by
    rw [hStepD] at hStepM
    injection hStepM with hEq
    subst hEq
    let ⟨hLe, hRem⟩ := reachesNUnw_det_split hNoStepT hD hM
    rw [Nat.succ_sub_succ]
    exact ⟨Nat.succ_le_succ hLe, hRem⟩

/-- Determinism of terminal/fault outcomes from the same start state in `M_unwind`. -/
private theorem reachesNUnw_terminal_unique {p : Program} {s t₁ t₂ : UnwindState}
    {r₁ r₂ : StepResult UnwindState UnwindOut}
    (hNoStep1 : ∀ s', r₁ ≠ .step s')
    (hNoStep2 : ∀ s', r₂ ≠ .step s')
    (h1 : ∃ n₁, ReachesNUnw p n₁ s t₁)
    (hEv1 : evalStepUnw p 0 t₁ = r₁)
    (h2 : ∃ n₂, ReachesNUnw p n₂ s t₂)
    (hEv2 : evalStepUnw p 0 t₂ = r₂) :
    r₁ = r₂ := by
  let ⟨n₁, hn₁⟩ := h1
  let ⟨n₂, hn₂⟩ := h2
  have hNS1 : ∀ s', evalStepUnw p 0 t₁ ≠ .step s' := fun s' h => hNoStep1 s' (hEv1.symm.trans h)
  have hNS2 : ∀ s', evalStepUnw p 0 t₂ ≠ .step s' := fun s' h => hNoStep2 s' (hEv2.symm.trans h)
  let ⟨hLe1, hRem1⟩ := reachesNUnw_det_split hNS2 hn₁ hn₂
  let ⟨hLe2, _⟩ := reachesNUnw_det_split hNS1 hn₂ hn₁
  have hEqN : n₂ - n₁ = 0 := by
    have hEq : n₁ = n₂ := Nat.le_antisymm hLe1 hLe2
    rw [hEq, Nat.sub_self]
  rw [hEqN] at hRem1
  cases hRem1
  exact hEv1.symm.trans hEv2

/-- Determinism: if `tr` is an infinite trace from `s₀`, every `ReachesNUnw p n s₀ s`
equals `tr n` and steps further (hence never reaches any terminal or fault). -/
private theorem reachesNUnw_eq_trace {p : Program} {s₀ : UnwindState}
    {tr : Nat → UnwindState} (h0 : tr 0 = s₀)
    (hTr : ∀ n, StepUnw p (tr n) (.step (tr (n + 1)))) :
    ∀ {n : Nat} {s : UnwindState}, ReachesNUnw p n s₀ s → s = tr n
  | 0, _, .zero _ => h0.symm
  | n + 1, s, .succ hStep hRest => by
    have hAt0 : evalStepUnw p 0 s₀ = .step (tr 1) := by
      let ⟨c, hc, hEv⟩ := hTr 0
      cases hc
      rw [h0] at hEv
      exact hEv
    rw [hAt0] at hStep
    injection hStep with hEq1
    subst hEq1
    exact reachesNUnw_eq_trace (tr := fun k => tr (k + 1)) rfl
      (fun k => hTr (k + 1)) hRest

private theorem divergesUnw_iff_no_terminal_or_fault (p : Program) (q : Query) :
    DivergesUnw p q ↔
      (∃ s₀, initStateUnw p q = .ok s₀) ∧
      (∀ k : FaultKind, ¬ ReachesResultUnw p q (.fault k)) ∧
      (∀ out : UnwindOut, ¬ BehaviorUnw p q out) := by
  constructor
  · intro ⟨s₀, hInit, tr, h0, hTr⟩
    refine ⟨⟨s₀, hInit⟩, ?_, ?_⟩
    · intro k hF
      unfold ReachesResultUnw at hF
      rw [hInit] at hF
      let ⟨s, hR, ⟨c, hc, hEv⟩⟩ := hF
      cases hc
      let ⟨n, hn⟩ := reachesUnw_to_reachesNUnw hR
      have hsEq := reachesNUnw_eq_trace h0 hTr hn
      subst hsEq
      let ⟨c', hc', hEv'⟩ := hTr n
      cases hc'
      rw [hEv'] at hEv
      cases hEv
    · intro out hB
      unfold BehaviorUnw ReachesResultUnw at hB
      rw [hInit] at hB
      let ⟨s, hR, ⟨c, hc, hEv⟩⟩ := hB
      cases hc
      let ⟨n, hn⟩ := reachesUnw_to_reachesNUnw hR
      have hsEq := reachesNUnw_eq_trace h0 hTr hn
      subst hsEq
      let ⟨c', hc', hEv'⟩ := hTr n
      cases hc'
      rw [hEv'] at hEv
      cases hEv
  · intro ⟨⟨s₀, hInit⟩, hNoF, hNoB⟩
    have hIter : ∀ n, ReachesUnw p s₀ (iterUnw p s₀ n) ∧
        StepUnw p (iterUnw p s₀ n) (.step (iterUnw p s₀ (n + 1))) := by
      intro n
      induction n with
      | zero =>
        refine ⟨ReachesUnw.refl s₀, ?_⟩
        dsimp [iterUnw, stepOrSelfUnw]
        cases hEv : evalStepUnw p 0 s₀ with
        | fault k =>
          exact False.elim (hNoF k (by
            unfold ReachesResultUnw; rw [hInit]
            exact ⟨s₀, ReachesUnw.refl s₀, ⟨0, rfl, hEv⟩⟩))
        | done out =>
          exact False.elim (hNoB out (by
            unfold BehaviorUnw ReachesResultUnw; rw [hInit]
            exact ⟨s₀, ReachesUnw.refl s₀, ⟨0, rfl, hEv⟩⟩))
        | step s₁ => exact ⟨0, rfl, hEv⟩
      | succ k ih =>
        have hRNext : ReachesUnw p s₀ (iterUnw p s₀ (k + 1)) :=
          ReachesUnw.tail ih.1 ih.2
        refine ⟨hRNext, ?_⟩
        cases hEv : evalStepUnw p 0 (iterUnw p s₀ (k + 1)) with
        | fault fk =>
          exact False.elim (hNoF fk (by
            unfold ReachesResultUnw; rw [hInit]
            exact ⟨_, hRNext, ⟨0, rfl, hEv⟩⟩))
        | done out =>
          exact False.elim (hNoB out (by
            unfold BehaviorUnw ReachesResultUnw; rw [hInit]
            exact ⟨_, hRNext, ⟨0, rfl, hEv⟩⟩))
        | step s' =>
          have hNextEq : iterUnw p s₀ (k + 1 + 1) = s' := by
            change stepOrSelfUnw p (iterUnw p s₀ (k + 1)) = s'
            unfold stepOrSelfUnw
            rw [hEv]
          rw [hNextEq]
          exact ⟨0, rfl, hEv⟩
    exact ⟨s₀, hInit, iterUnw p s₀, rfl, fun n => (hIter n).2⟩

/-- In `M_unwind`, `WellFormedUnw p q` holds iff no `.fault k` is reachable
(since `ValidChoiceUnw p s 0` holds unconditionally for all states `s`). -/
private theorem wellFormedUnw_iff_no_fault (p : Program) (q : Query) :
    WellFormedUnw p q ↔ ∀ k : FaultKind, ¬ ReachesResultUnw p q (.fault k) := by
  constructor
  · intro hWf; exact hWf.2
  · intro hNoF
    refine ⟨?_, hNoF⟩
    cases hInit : initStateUnw p q with
    | error k =>
      exact False.elim (hNoF k (by unfold ReachesResultUnw; rw [hInit]))
    | ok s₀ =>
      exact ⟨s₀, rfl, fun _ _ => ⟨0, rfl⟩⟩

/-- Universal equivalence builder from finite fault + behavior equivalence
(automatically derives `WellFormedUnw`, constructive `DivergesUnw`, and
`SatisfiesPostUnw` with `0` `Classical.choice`!). -/
private theorem fullSemanticEquivUnw_of_outcomes {p₁ p₂ : Program}
    (hFault : ∀ q k,
      ReachesResultUnw p₁ q (.fault k) ↔ ReachesResultUnw p₂ q (.fault k))
    (hBeh : ∀ q out, BehaviorUnw p₁ q out ↔ BehaviorUnw p₂ q out) :
    FullSemanticEquivUnw p₁ p₂ := by
  have hWf : ∀ q, WellFormedUnw p₁ q ↔ WellFormedUnw p₂ q := by
    intro q
    rw [wellFormedUnw_iff_no_fault, wellFormedUnw_iff_no_fault]
    exact ⟨fun h k hf2 => h k ((hFault q k).mpr hf2),
           fun h k hf1 => h k ((hFault q k).mp hf1)⟩
  have hDiv : ∀ q, DivergesUnw p₁ q ↔ DivergesUnw p₂ q := by
    intro q
    rw [divergesUnw_iff_no_terminal_or_fault, divergesUnw_iff_no_terminal_or_fault]
    constructor
    · intro ⟨_, hNoF1, hNoB1⟩
      have hNoF2 : ∀ k, ¬ ReachesResultUnw p₂ q (.fault k) :=
        fun k hf2 => hNoF1 k ((hFault q k).mpr hf2)
      have hInit2 : ∃ s₀, initStateUnw p₂ q = .ok s₀ := by
        cases hI : initStateUnw p₂ q with
        | error k => exact False.elim (hNoF2 k (by unfold ReachesResultUnw; rw [hI]))
        | ok s₀ => exact ⟨s₀, rfl⟩
      exact ⟨hInit2, hNoF2, fun out hb2 => hNoB1 out ((hBeh q out).mpr hb2)⟩
    · intro ⟨_, hNoF2, hNoB2⟩
      have hNoF1 : ∀ k, ¬ ReachesResultUnw p₁ q (.fault k) :=
        fun k hf1 => hNoF2 k ((hFault q k).mp hf1)
      have hInit1 : ∃ s₀, initStateUnw p₁ q = .ok s₀ := by
        cases hI : initStateUnw p₁ q with
        | error k => exact False.elim (hNoF1 k (by unfold ReachesResultUnw; rw [hI]))
        | ok s₀ => exact ⟨s₀, rfl⟩
      exact ⟨hInit1, hNoF1, fun out hb1 => hNoB2 out ((hBeh q out).mp hb1)⟩
  have hPost : ∀ q post, SatisfiesPostUnw p₁ q post ↔ SatisfiesPostUnw p₂ q post := by
    intro q post
    unfold SatisfiesPostUnw
    constructor
    · intro ⟨hw1, hp1⟩
      exact ⟨(hWf q).mp hw1, fun out hb2 => hp1 out ((hBeh q out).mpr hb2)⟩
    · intro ⟨hw2, hp2⟩
      exact ⟨(hWf q).mpr hw2, fun out hb1 => hp2 out ((hBeh q out).mp hb1)⟩
  exact ⟨hWf, hBeh, hFault, hDiv, hPost⟩

/-- Forward stuttering simulation along `ReachesUnw`. -/
private theorem fwd_stutter_sim_reaches {p₁ p₂ : Program}
    (R : UnwindState → UnwindState → Prop)
    (hStep : ∀ s₁ s₂ s₁', R s₁ s₂ →
      evalStepUnw p₁ 0 s₁ = .step s₁' →
      ∃ s₂', ReachesPlusUnw p₂ s₂ s₂' ∧ R s₁' s₂') :
    ∀ {s₁ t₁ s₂ : UnwindState},
      ReachesUnw p₁ s₁ t₁ → R s₁ s₂ →
      ∃ t₂, ReachesUnw p₂ s₂ t₂ ∧ R t₁ t₂ := by
  intro s₁ t₁ s₂ hR hRel
  induction hR with
  | refl => exact ⟨s₂, ReachesUnw.refl s₂, hRel⟩
  | tail _ hSt ih =>
    let ⟨mid₂, hR2, hRelMid⟩ := ih
    let ⟨c, hc, hEv⟩ := hSt
    cases hc
    let ⟨t₂, ⟨d, hd⟩, hRelT⟩ := hStep _ mid₂ _ hRelMid hEv
    exact ⟨t₂, reachesUnw_trans hR2 (reachesNUnw_to_reachesUnw hd), hRelT⟩

/-- Constructive reverse terminal/fault reflection from a ONE-WAY forward
stuttering simulation (`0` `Classical.choice`!). -/
private theorem fwd_stutter_sim_reflect_terminal {p₁ p₂ : Program}
    (R : UnwindState → UnwindState → Prop)
    (hStep : ∀ s₁ s₂ s₁', R s₁ s₂ →
      evalStepUnw p₁ 0 s₁ = .step s₁' →
      ∃ s₂', ReachesPlusUnw p₂ s₂ s₂' ∧ R s₁' s₂')
    (hDone : ∀ s₁ s₂ out, R s₁ s₂ →
      evalStepUnw p₁ 0 s₁ = .done out →
      ∃ s₂', ReachesUnw p₂ s₂ s₂' ∧ evalStepUnw p₂ 0 s₂' = .done out)
    (hFault : ∀ s₁ s₂ k, R s₁ s₂ →
      evalStepUnw p₁ 0 s₁ = .fault k →
      ∃ s₂', ReachesUnw p₂ s₂ s₂' ∧ evalStepUnw p₂ 0 s₂' = .fault k)
    {t₂ : UnwindState} {r : StepResult UnwindState UnwindOut}
    (hNoStepR : ∀ x, r ≠ .step x)
    (hEvT2 : evalStepUnw p₂ 0 t₂ = r) :
    ∀ (n m : Nat), m ≤ n →
      ∀ {s₁ s₂ : UnwindState},
        R s₁ s₂ →
        ReachesNUnw p₂ m s₂ t₂ →
        ∃ t₁, ReachesUnw p₁ s₁ t₁ ∧ evalStepUnw p₁ 0 t₁ = r := by
  intro n
  induction n with
  | zero =>
    intro m hm s₁ s₂ hRel hRm
    have hM0 : m = 0 := Nat.le_zero.mp hm
    subst hM0
    cases hEv1 : evalStepUnw p₁ 0 s₁ with
    | done out' =>
      let ⟨t₂', hR2', hEv2'⟩ := hDone s₁ s₂ out' hRel hEv1
      have hEq := reachesNUnw_terminal_unique
        (fun x h => by cases h) hNoStepR
        (reachesUnw_to_reachesNUnw hR2') hEv2' ⟨0, hRm⟩ hEvT2
      exact ⟨s₁, ReachesUnw.refl s₁, hEv1.trans hEq⟩
    | fault k' =>
      let ⟨t₂', hR2', hEv2'⟩ := hFault s₁ s₂ k' hRel hEv1
      have hEq := reachesNUnw_terminal_unique
        (fun x h => by cases h) hNoStepR
        (reachesUnw_to_reachesNUnw hR2') hEv2' ⟨0, hRm⟩ hEvT2
      exact ⟨s₁, ReachesUnw.refl s₁, hEv1.trans hEq⟩
    | step s₁' =>
      let ⟨s₂', ⟨d, hd⟩, _⟩ := hStep s₁ s₂ s₁' hRel hEv1
      have hNST2 : ∀ x, evalStepUnw p₂ 0 t₂ ≠ .step x :=
        fun x h => hNoStepR x (hEvT2.symm.trans h)
      let ⟨hLe, _⟩ := reachesNUnw_det_split hNST2 hd hRm
      exact False.elim (Nat.not_succ_le_zero d hLe)
  | succ n ih =>
    intro m hm s₁ s₂ hRel hRm
    cases hEv1 : evalStepUnw p₁ 0 s₁ with
    | done out' =>
      let ⟨t₂', hR2', hEv2'⟩ := hDone s₁ s₂ out' hRel hEv1
      have hEq := reachesNUnw_terminal_unique
        (fun x h => by cases h) hNoStepR
        (reachesUnw_to_reachesNUnw hR2') hEv2' ⟨m, hRm⟩ hEvT2
      exact ⟨s₁, ReachesUnw.refl s₁, hEv1.trans hEq⟩
    | fault k' =>
      let ⟨t₂', hR2', hEv2'⟩ := hFault s₁ s₂ k' hRel hEv1
      have hEq := reachesNUnw_terminal_unique
        (fun x h => by cases h) hNoStepR
        (reachesUnw_to_reachesNUnw hR2') hEv2' ⟨m, hRm⟩ hEvT2
      exact ⟨s₁, ReachesUnw.refl s₁, hEv1.trans hEq⟩
    | step s₁' =>
      let ⟨s₂', ⟨d, hd⟩, hRel'⟩ := hStep s₁ s₂ s₁' hRel hEv1
      have hNST2 : ∀ x, evalStepUnw p₂ 0 t₂ ≠ .step x :=
        fun x h => hNoStepR x (hEvT2.symm.trans h)
      let ⟨_, hRem⟩ := reachesNUnw_det_split hNST2 hd hRm
      have hSubLe : m - (d + 1) ≤ n := by
        have h1 : m ≤ n + (d + 1) :=
          Nat.le_trans hm (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le d)) n)
        exact Nat.sub_le_of_le_add h1
      let ⟨t₁, hR1', hEvT1⟩ := ih (m - (d + 1)) hSubLe hRel' hRem
      exact ⟨t₁, c_reachesUnw_head_det hEv1 hR1', hEvT1⟩

/-- Master constructive forward stuttering simulation combinator: a single
one-way forward stuttering simulation (`1` step -> `≥ 1` steps, `.done`/`.fault` ->
`≥ 0` steps + matching `.done`/`.fault`) yields FULL bidirectional
`FullSemanticEquivUnw p₁ p₂` with `0` `Classical.choice`! -/
private theorem fullSemanticEquivUnw_of_fwd_stutter_sim {p₁ p₂ : Program}
    (R : UnwindState → UnwindState → Prop)
    (hInitErr : ∀ q k, initStateUnw p₁ q = .error k ↔ initStateUnw p₂ q = .error k)
    (hInitOk : ∀ q s₁ s₂,
      initStateUnw p₁ q = .ok s₁ → initStateUnw p₂ q = .ok s₂ → R s₁ s₂)
    (hStep : ∀ s₁ s₂ s₁', R s₁ s₂ →
      evalStepUnw p₁ 0 s₁ = .step s₁' →
      ∃ s₂', ReachesPlusUnw p₂ s₂ s₂' ∧ R s₁' s₂')
    (hDone : ∀ s₁ s₂ out, R s₁ s₂ →
      evalStepUnw p₁ 0 s₁ = .done out →
      ∃ s₂', ReachesUnw p₂ s₂ s₂' ∧ evalStepUnw p₂ 0 s₂' = .done out)
    (hFault : ∀ s₁ s₂ k, R s₁ s₂ →
      evalStepUnw p₁ 0 s₁ = .fault k →
      ∃ s₂', ReachesUnw p₂ s₂ s₂' ∧ evalStepUnw p₂ 0 s₂' = .fault k) :
    FullSemanticEquivUnw p₁ p₂ := by
  have hRes : ∀ q (r : StepResult UnwindState UnwindOut),
      (∀ x, r ≠ .step x) →
      (ReachesResultUnw p₁ q r ↔ ReachesResultUnw p₂ q r) := by
    intro q r hNoStep
    unfold ReachesResultUnw
    cases hI1 : initStateUnw p₁ q with
    | error k₁ =>
      have hI2 : initStateUnw p₂ q = .error k₁ := (hInitErr q k₁).mp hI1
      rw [hI2]
    | ok s₁ =>
      cases hI2 : initStateUnw p₂ q with
      | error k₂ =>
        have hI1' : initStateUnw p₁ q = .error k₂ := (hInitErr q k₂).mpr hI2
        rw [hI1] at hI1'
        cases hI1'
      | ok s₂ =>
        have hRel0 : R s₁ s₂ := hInitOk q s₁ s₂ hI1 hI2
        constructor
        · intro ⟨t₁, hR1, ⟨c, hc, hEv1⟩⟩
          cases hc
          let ⟨t₂, hR2, hRelT⟩ := fwd_stutter_sim_reaches R hStep hR1 hRel0
          cases r with
          | step x => exact False.elim (hNoStep x rfl)
          | done out =>
            let ⟨t₂', hR2', hEv2'⟩ := hDone t₁ t₂ out hRelT hEv1
            exact ⟨t₂', reachesUnw_trans hR2 hR2', ⟨0, rfl, hEv2'⟩⟩
          | fault k =>
            let ⟨t₂', hR2', hEv2'⟩ := hFault t₁ t₂ k hRelT hEv1
            exact ⟨t₂', reachesUnw_trans hR2 hR2', ⟨0, rfl, hEv2'⟩⟩
        · intro ⟨t₂, hR2, ⟨c, hc, hEv2⟩⟩
          cases hc
          let ⟨n, hn⟩ := reachesUnw_to_reachesNUnw hR2
          let ⟨t₁, hR1, hEv1⟩ :=
            fwd_stutter_sim_reflect_terminal R hStep hDone hFault
              hNoStep hEv2 n n (Nat.le_refl n) hRel0 hn
          exact ⟨t₁, hR1, ⟨0, rfl, hEv1⟩⟩
  exact fullSemanticEquivUnw_of_outcomes
    (fun q k => hRes q (.fault k) (fun _ h => by cases h))
    (fun q out => hRes q (.done out) (fun _ h => by cases h))

/-- Specialization of `fullSemanticEquivUnw_of_fwd_stutter_sim` to a 1-to-1
lockstep simulation (for `AbortUnwindingCalls`, `DischargeTrivialAssert`,
`PruneDeadCleanupBlocks`, etc.). -/
private theorem fullSemanticEquivUnw_of_lockstep {p₁ p₂ : Program}
    (R : UnwindState → UnwindState → Prop)
    (hInitErr : ∀ q k, initStateUnw p₁ q = .error k ↔ initStateUnw p₂ q = .error k)
    (hInitOk : ∀ q s₁ s₂,
      initStateUnw p₁ q = .ok s₁ → initStateUnw p₂ q = .ok s₂ → R s₁ s₂)
    (hStep : ∀ s₁ s₂ s₁', R s₁ s₂ →
      evalStepUnw p₁ 0 s₁ = .step s₁' →
      ∃ s₂', evalStepUnw p₂ 0 s₂ = .step s₂' ∧ R s₁' s₂')
    (hDone : ∀ s₁ s₂ out, R s₁ s₂ →
      evalStepUnw p₁ 0 s₁ = .done out →
      evalStepUnw p₂ 0 s₂ = .done out)
    (hFault : ∀ s₁ s₂ k, R s₁ s₂ →
      evalStepUnw p₁ 0 s₁ = .fault k →
      evalStepUnw p₂ 0 s₂ = .fault k) :
    FullSemanticEquivUnw p₁ p₂ :=
  fullSemanticEquivUnw_of_fwd_stutter_sim R hInitErr hInitOk
    (fun s₁ s₂ s₁' hRel hEv =>
      let ⟨s₂', hEv2, hRel'⟩ := hStep s₁ s₂ s₁' hRel hEv
      ⟨s₂', ⟨0, ReachesNUnw.succ hEv2 (ReachesNUnw.zero s₂')⟩, hRel'⟩)
    (fun s₁ s₂ out hRel hEv =>
      ⟨s₂, ReachesUnw.refl s₂, hDone s₁ s₂ out hRel hEv⟩)
    (fun s₁ s₂ k hRel hEv =>
      ⟨s₂, ReachesUnw.refl s₂, hFault s₁ s₂ k hRel hEv⟩)

private theorem fullSemanticEquivUnw_refl (p : Program) : FullSemanticEquivUnw p p :=
  ⟨fun _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl,
   fun _ => Iff.rfl, fun _ _ => Iff.rfl⟩

private theorem fullSemanticEquivUnw_trans {p₁ p₂ p₃ : Program}
    (h12 : FullSemanticEquivUnw p₁ p₂)
    (h23 : FullSemanticEquivUnw p₂ p₃) :
    FullSemanticEquivUnw p₁ p₃ :=
  ⟨fun q => (h12.1 q).trans (h23.1 q),
   fun q out => (h12.2.1 q out).trans (h23.2.1 q out),
   fun q k => (h12.2.2.1 q k).trans (h23.2.2.1 q k),
   fun q => (h12.2.2.2.1 q).trans (h23.2.2.2.1 q),
   fun q post => (h12.2.2.2.2 q post).trans (h23.2.2.2.2 q post)⟩

private theorem programEquivUnw_refl (p : Program) : ProgramEquivUnw p p := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, fullSemanticEquivUnw_refl p, ?_⟩
  intro defId
  cases Trusted.MirSemantics.getElem? p.bodies defId with
  | none => exact True.intro
  | some b =>
    exact ⟨rfl, rfl, rfl, fun _ => Iff.rfl,
      fullSemanticEquivUnw_refl (entryProgForBody p defId)⟩

private theorem programEquivUnw_trans {p₁ p₂ p₃ : Program}
    (h12 : ProgramEquivUnw p₁ p₂)
    (h23 : ProgramEquivUnw p₂ p₃) :
    ProgramEquivUnw p₁ p₃ := by
  let ⟨hLen12, hEnt12, hPw12, hVer12, hSc12, hUniq12, hSem12, hBod12⟩ := h12
  let ⟨hLen23, hEnt23, hPw23, hVer23, hSc23, hUniq23, hSem23, hBod23⟩ := h23
  refine ⟨hLen12.trans hLen23, hEnt12.trans hEnt23, hPw12.trans hPw23,
    hVer12.trans hVer23, hSc12.trans hSc23, hUniq12.trans hUniq23,
    fullSemanticEquivUnw_trans hSem12 hSem23, ?_⟩
  intro defId
  have hB12 := hBod12 defId
  have hB23 := hBod23 defId
  cases h1 : Trusted.MirSemantics.getElem? p₁.bodies defId with
  | none =>
    rw [h1] at hB12
    cases h2 : Trusted.MirSemantics.getElem? p₂.bodies defId with
    | some b₂ => rw [h2] at hB12; exact False.elim hB12
    | none =>
      rw [h2] at hB23
      cases h3 : Trusted.MirSemantics.getElem? p₃.bodies defId with
      | some b₃ => rw [h3] at hB23; exact False.elim hB23
      | none => exact True.intro
  | some b₁ =>
    rw [h1] at hB12
    cases h2 : Trusted.MirSemantics.getElem? p₂.bodies defId with
    | none => rw [h2] at hB12; exact False.elim hB12
    | some b₂ =>
      rw [h2] at hB12 hB23
      cases h3 : Trusted.MirSemantics.getElem? p₃.bodies defId with
      | none => rw [h3] at hB23; exact False.elim hB23
      | some b₃ =>
        rw [h3] at hB23
        let ⟨hId12, hUn12, hAd12, hAr12, hSe12⟩ := hB12
        let ⟨hId23, hUn23, hAd23, hAr23, hSe23⟩ := hB23
        exact ⟨hId12.trans hId23, hUn12.trans hUn23, hAd12.trans hAd23,
          fun args => (hAr12 args).trans (hAr23 args),
          fullSemanticEquivUnw_trans hSe12 hSe23⟩

/-! ### Slice: Slice1_ConservativeExt_And_PanicAbort.lean -/

-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.




/-! ### Part A: Theorem 1 (`unwind_conservative_extension_exact_slice1`) -/

private theorem initState_single_frame {p : Program} {q : Query} {s₀ : State}
    (h : initState p q = .ok s₀) :
    ∃ f : FrameState, s₀ = { frames := [f], callerMem := q.callerMem } := by
  unfold initState at h
  cases h1 : (!Nat.beq p.pointerWidthBits 64 || !Nat.beq p.mirProfileVersion 1) <;>
    rw [h1] at h
  · dsimp at h
    cases h2 : (!q.callerMem.allocations.isEmpty) <;> rw [h2] at h
    · dsimp at h
      cases h3 : Trusted.MirSemantics.getElem? p.bodies p.entryDefId with
      | none => rw [h3] at h; cases h
      | some body =>
        rw [h3] at h; dsimp at h
        cases h4 : body.basicBlocks.isEmpty <;> rw [h4] at h
        · dsimp at h
          cases h5 : (!Nat.blt body.argumentCount body.locals.length) <;> rw [h5] at h
          · dsimp at h
            cases h6 : (!storageAnnotationsInBounds body) <;> rw [h6] at h
            · dsimp at h
              cases h7 : (!body.locals.all isSupportedScalarOrUnitTy) <;> rw [h7] at h
              · dsimp at h
                cases h8 : (!checkArgsMatch q.args ((body.locals.drop 1).take body.argumentCount)) <;>
                  rw [h8] at h
                · dsimp at h
                  injection h with hEq
                  exact ⟨_, hEq.symm⟩
                · cases h
              · cases h
            · cases h
          · cases h
        · cases h
    · cases h
  · cases h

private theorem initStateUnw_ok_iff (p : Program) (q : Query) (u₀ : UnwindState) :
    initStateUnw p q = .ok u₀ ↔
      u₀.callStack = [] ∧
      initState p q = .ok { frames := [u₀.active], callerMem := u₀.callerMem } := by
  unfold initStateUnw
  cases hI : initState p q with
  | error k =>
    constructor
    · intro h; cases h
    · intro ⟨_, h⟩; cases h
  | ok s₀ =>
    let ⟨f, hsEq⟩ := initState_single_frame hI
    subst hsEq
    dsimp [embedStateUnw?]
    constructor
    · intro h
      injection h with huEq
      subst huEq
      exact ⟨rfl, rfl⟩
    · intro ⟨hCs, hEq⟩
      injection hEq with hStEq
      cases u₀ with
      | mk act cs mem =>
        dsimp at hCs hStEq
        subst hCs
        injection hStEq with hFrEq hMemEq
        injection hFrEq with hActEq
        subst hActEq
        subst hMemEq
        rfl

private theorem initStateUnw_error_iff (p : Program) (q : Query) (k : FaultKind) :
    initStateUnw p q = .error k ↔ initState p q = .error k := by
  unfold initStateUnw
  cases hI : initState p q with
  | error k' =>
    dsimp
    constructor <;> (intro h; injection h with he; rw [he])
  | ok s₀ =>
    let ⟨f, hsEq⟩ := initState_single_frame hI
    subst hsEq
    dsimp [embedStateUnw?]
    constructor <;> intro h <;> cases h

private theorem evalStatement_outcomes (body : Body) (frame : FrameState)
    (mem : CallerMemory) (stmt : StatementKind) :
    (∀ out, evalStatement body frame mem stmt ≠ .done out) ∧
    (∀ st', evalStatement body frame mem stmt = .step st' →
      ∃ f', st'.frames = [f'] ∧ f'.defId = frame.defId) := by
  cases stmt with
  | nop =>
    refine ⟨fun _ h => (by cases h), fun st' h => ?_⟩
    dsimp [evalStatement] at h
    injection h with hEq; subst hEq; exact ⟨_, rfl, rfl⟩
  | unsupported =>
    exact ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩
  | storageLive lid =>
    dsimp [evalStatement]
    cases Trusted.MirSemantics.getElem? body.locals lid with
    | none => exact ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩
    | some ty =>
      dsimp
      cases setElem? frame.locals lid (liveUninitSlot ty) with
      | none => exact ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩
      | some locs' =>
        dsimp
        refine ⟨fun _ h => (by cases h), fun st' h => ?_⟩
        injection h with hEq; subst hEq; exact ⟨_, rfl, rfl⟩
  | storageDead lid =>
    dsimp [evalStatement]
    cases Nat.beq lid 0 with
    | true => exact ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩
    | false =>
      dsimp
      cases setElem? frame.locals lid .dead with
      | none => exact ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩
      | some locs' =>
        dsimp
        refine ⟨fun _ h => (by cases h), fun st' h => ?_⟩
        injection h with hEq; subst hEq; exact ⟨_, rfl, rfl⟩
  | assign dst rv =>
    dsimp [evalStatement]
    cases !dst.projection.isEmpty with
    | true => exact ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩
    | false =>
      dsimp
      cases Trusted.MirSemantics.getElem? body.locals dst.localId with
      | none => exact ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩
      | some dstTy =>
        dsimp
        cases evalRvalue body.locals frame.locals dstTy rv with
        | error _ => exact ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩
        | ok pair =>
          dsimp
          cases writePlace pair.2 dst.localId dstTy pair.1 with
          | error _ => exact ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩
          | ok locs' =>
            dsimp
            refine ⟨fun _ h => (by cases h), fun st' h => ?_⟩
            injection h with hEq; subst hEq; exact ⟨_, rfl, rfl⟩

/-- Helper for equal fault outcomes in `evalStepUnw_base_corresp`. -/
private theorem base_step_corresp_fault (k₀ : FaultKind) :
    (∀ u' : UnwindState, (StepResult.fault k₀ : StepResult UnwindState UnwindOut) = .step u' →
      u'.callStack = [] ∧
      (StepResult.fault k₀ : StepResult State TerminalOut) = .step ⟨[u'.active], u'.callerMem⟩) ∧
    (∀ s' : State, (StepResult.fault k₀ : StepResult State TerminalOut) = .step s' →
      ∃ f' m', s' = ⟨[f'], m'⟩ ∧
        (StepResult.fault k₀ : StepResult UnwindState UnwindOut) = .step ⟨f', [], m'⟩) ∧
    (∀ out : TerminalOut,
      (StepResult.fault k₀ : StepResult UnwindState UnwindOut) = .done (embedTerminalOut out) ↔
      (StepResult.fault k₀ : StepResult State TerminalOut) = .done out) ∧
    (∀ m : CallerMemory,
      (StepResult.fault k₀ : StepResult UnwindState UnwindOut) ≠ .done (.aborted m)) ∧
    (∀ k : FaultKind,
      (StepResult.fault k₀ : StepResult UnwindState UnwindOut) = .fault k ↔
      (StepResult.fault k₀ : StepResult State TerminalOut) = .fault k) :=
  ⟨fun _ h => (by cases h),
   fun _ h => (by cases h),
   fun _ => ⟨fun h => (by cases h), fun h => (by cases h)⟩,
   fun _ h => (by cases h),
   fun _ => ⟨fun h => by injection h with he; rw [he],
             fun h => by injection h with he; rw [he]⟩⟩

/-- Helper for equal single-frame step outcomes in `evalStepUnw_base_corresp`. -/
private theorem base_step_corresp_step (f' : FrameState) (m' : CallerMemory) :
    (∀ u' : UnwindState,
      (StepResult.step ⟨f', [], m'⟩ : StepResult UnwindState UnwindOut) = .step u' →
      u'.callStack = [] ∧
      (StepResult.step ⟨[f'], m'⟩ : StepResult State TerminalOut) = .step ⟨[u'.active], u'.callerMem⟩) ∧
    (∀ s' : State,
      (StepResult.step ⟨[f'], m'⟩ : StepResult State TerminalOut) = .step s' →
      ∃ f₂ m₂, s' = ⟨[f₂], m₂⟩ ∧
        (StepResult.step ⟨f', [], m'⟩ : StepResult UnwindState UnwindOut) = .step ⟨f₂, [], m₂⟩) ∧
    (∀ out : TerminalOut,
      (StepResult.step ⟨f', [], m'⟩ : StepResult UnwindState UnwindOut) = .done (embedTerminalOut out) ↔
      (StepResult.step ⟨[f'], m'⟩ : StepResult State TerminalOut) = .done out) ∧
    (∀ m : CallerMemory,
      (StepResult.step ⟨f', [], m'⟩ : StepResult UnwindState UnwindOut) ≠ .done (.aborted m)) ∧
    (∀ k : FaultKind,
      (StepResult.step ⟨f', [], m'⟩ : StepResult UnwindState UnwindOut) = .fault k ↔
      (StepResult.step ⟨[f'], m'⟩ : StepResult State TerminalOut) = .fault k) :=
  ⟨fun u' hu' => by injection hu' with he; subst he; exact ⟨rfl, rfl⟩,
   fun s' hs' => by injection hs' with he; subst he; exact ⟨f', m', rfl, rfl⟩,
   fun _ => ⟨fun h => (by cases h), fun h => (by cases h)⟩,
   fun _ h => (by cases h),
   fun _ => ⟨fun h => (by cases h), fun h => (by cases h)⟩⟩

/-- Exact single-step correspondence between `evalStepUnw` and unmodified
`Trusted.MirSemantics.evalStep` on any `isBaseMirProgram p = true` program
and single-frame state (`callStack = []`). -/
private theorem evalStepUnw_base_corresp {p : Program}
    (hBase : isBaseMirProgram p = true)
    (f : FrameState) (mem : CallerMemory) :
    (∀ u', evalStepUnw p 0 ⟨f, [], mem⟩ = .step u' →
      u'.callStack = [] ∧
      evalStep p 0 ⟨[f], mem⟩ = .step ⟨[u'.active], u'.callerMem⟩) ∧
    (∀ s', evalStep p 0 ⟨[f], mem⟩ = .step s' →
      ∃ f' m', s' = ⟨[f'], m'⟩ ∧
        evalStepUnw p 0 ⟨f, [], mem⟩ = .step ⟨f', [], m'⟩) ∧
    (∀ out, evalStepUnw p 0 ⟨f, [], mem⟩ = .done (embedTerminalOut out) ↔
      evalStep p 0 ⟨[f], mem⟩ = .done out) ∧
    (∀ m, evalStepUnw p 0 ⟨f, [], mem⟩ ≠ .done (.aborted m)) ∧
    (∀ k, evalStepUnw p 0 ⟨f, [], mem⟩ = .fault k ↔
      evalStep p 0 ⟨[f], mem⟩ = .fault k) := by
  unfold evalStepUnw evalStep
  dsimp
  cases hBod : Trusted.MirSemantics.getElem? p.bodies f.defId with
  | none => exact base_step_corresp_fault .unsupported
  | some body =>
    dsimp
    have hBaseBody : isBaseMirBody body = true := list_all_getElem? hBase hBod
    cases hBb : Trusted.MirSemantics.getElem? body.basicBlocks f.blockIdx with
    | none => exact base_step_corresp_fault .unsupported
    | some bb =>
      dsimp
      have hBaseTerm : isBaseMirTerm bb.terminator = true :=
        list_all_getElem? (p := fun b : BasicBlock => isBaseMirTerm b.terminator) hBaseBody hBb
      cases hSt : Trusted.MirSemantics.getElem? bb.statements f.stmtIdx with
      | some stmt =>
        dsimp
        let ⟨hNoDone, hSingle⟩ := evalStatement_outcomes body f mem stmt
        cases hEv : evalStatement body f mem stmt with
        | fault fk => exact base_step_corresp_fault fk
        | done out => exact False.elim (hNoDone out hEv)
        | step st' =>
          let ⟨f', hf', _⟩ := hSingle st' hEv
          cases st' with
          | mk frs m' =>
            dsimp at hf'
            subst hf'
            exact base_step_corresp_step f' m'
      | none =>
        dsimp
        cases hEqLen : Nat.beq f.stmtIdx bb.statements.length with
        | false => exact base_step_corresp_fault .unsupported
        | true =>
          dsimp [evalTerminatorUnw, evalTerminator, jumpToBlock]
          cases hTerm : bb.terminator with
          | unwindResume => rw [hTerm] at hBaseTerm; cases hBaseTerm
          | assert _ _ _ _ _ => rw [hTerm] at hBaseTerm; cases hBaseTerm
          | call _ _ _ _ _ => rw [hTerm] at hBaseTerm; cases hBaseTerm
          | goto target =>
            exact base_step_corresp_step { f with blockIdx := target, stmtIdx := 0 } mem
          | unreachable => exact base_step_corresp_fault .undefined
          | unsupported => exact base_step_corresp_fault .unsupported
          | return_ =>
            cases bb.cleanup with
            | true => exact base_step_corresp_fault .unsupported
            | false =>
              dsimp
              cases Trusted.MirSemantics.getElem? f.locals 0 with
              | none => exact base_step_corresp_fault .unsupported
              | some slot =>
                cases slot with
                | dead => exact base_step_corresp_fault .undefined
                | live optVal =>
                  cases optVal with
                  | none => exact base_step_corresp_fault .undefined
                  | some retVal =>
                    refine ⟨fun _ h => (by cases h), fun _ h => (by cases h), ?_, ?_, ?_⟩
                    · intro out
                      cases out with
                      | returned o =>
                        dsimp [embedTerminalOut]
                        constructor <;> intro h <;> injection h with h1 <;>
                          injection h1 with h2 <;> subst h2 <;> rfl
                      | unwound m =>
                        dsimp [embedTerminalOut]
                        exact ⟨fun h => (by cases h), fun h => (by cases h)⟩
                    · intro _ h; cases h
                    · intro _; exact ⟨fun h => (by cases h), fun h => (by cases h)⟩
          | switchInt discr targets =>
            dsimp
            cases evalPrimitiveOperand body.locals f.locals discr with
            | error fk => exact base_step_corresp_fault fk
            | ok pair =>
              dsimp
              cases pair with
              | mk dVal locAfter =>
                dsimp
                cases dVal with
                | scalar sv =>
                  dsimp
                  cases evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches with
                  | error fk => exact base_step_corresp_fault fk
                  | ok tgt =>
                    exact base_step_corresp_step
                      { f with blockIdx := tgt, stmtIdx := 0, locals := locAfter } mem
                | bool b =>
                  dsimp
                  cases evalBoolSwitchBranches b targets.otherwise targets.branches with
                  | error fk => exact base_step_corresp_fault fk
                  | ok tgt =>
                    exact base_step_corresp_step
                      { f with blockIdx := tgt, stmtIdx := 0, locals := locAfter } mem
                | unit | ptr _ | enumVal _ _ | tuple _ | bytes _ =>
                  exact base_step_corresp_fault .unsupported

private theorem reachesUnw_to_reaches_base_clean {p : Program}
    (hBase : isBaseMirProgram p = true) :
    ∀ {u₀ u : UnwindState},
      u₀.callStack = [] →
      ReachesUnw p u₀ u →
      u.callStack = [] ∧
      Reaches p ⟨[u₀.active], u₀.callerMem⟩ ⟨[u.active], u.callerMem⟩ := by
  intro u₀ u hCs0 hR
  induction hR with
  | refl => exact ⟨hCs0, Reaches.refl _⟩
  | @tail s₂ s₃ _ hSt ih =>
    let ⟨hCs2, hR2⟩ := ih
    let ⟨c, hc, hEv⟩ := hSt
    cases hc
    cases s₂ with
    | mk f2 cs2 m2 =>
      dsimp at hCs2 hR2
      subst hCs2
      let ⟨hCs3, hEvBase⟩ := (evalStepUnw_base_corresp hBase f2 m2).1 s₃ hEv
      exact ⟨hCs3, Reaches.tail hR2 ⟨0, rfl, hEvBase⟩⟩

private theorem reaches_to_reachesUnw_base {p : Program}
    (hBase : isBaseMirProgram p = true) {f₀ : FrameState} {m₀ : CallerMemory}
    {s : State} (hR : Reaches p ⟨[f₀], m₀⟩ s) :
    ∃ f m, s = ⟨[f], m⟩ ∧ ReachesUnw p ⟨f₀, [], m₀⟩ ⟨f, [], m⟩ := by
  induction hR with
  | refl => exact ⟨f₀, m₀, rfl, ReachesUnw.refl _⟩
  | @tail s₂ s₃ _ hSt ih =>
    let ⟨f2, m2, hs2Eq, hR2⟩ := ih
    subst hs2Eq
    let ⟨c, hc, hEv⟩ := hSt
    cases hc
    let ⟨f3, m3, hs3Eq, hEvUnw⟩ := (evalStepUnw_base_corresp hBase f2 m2).2.1 s₃ hEv
    exact ⟨f3, m3, hs3Eq, ReachesUnw.tail hR2 ⟨0, rfl, hEvUnw⟩⟩

private theorem base_program_outcomes_iff {p : Program}
    (hBase : isBaseMirProgram p = true) :
    (∀ q : Query, WellFormedUnw p q ↔ WellFormed p q) ∧
    (∀ q : Query, ∀ out : TerminalOut,
      BehaviorUnw p q (embedTerminalOut out) ↔ Behavior p q out) ∧
    (∀ q : Query, ∀ mem : CallerMemory, ¬ BehaviorUnw p q (.aborted mem)) ∧
    (∀ q : Query, ∀ k : FaultKind,
      ReachesResultUnw p q (.fault k) ↔ ReachesResult p q (.fault k)) ∧
    (∀ q : Query, DivergesUnw p q ↔ Diverges p q) ∧
    (∀ q : Query, ∀ post : TerminalOut → Prop,
      SatisfiesPostUnw p q (liftTerminalPost post) ↔ SatisfiesPost p q post) := by
  have hFault : ∀ q k,
      ReachesResultUnw p q (.fault k) ↔ ReachesResult p q (.fault k) := by
    intro q k
    unfold ReachesResultUnw ReachesResult
    cases hI : initState p q with
    | error k₀ =>
      have hIu := (initStateUnw_error_iff p q k₀).mpr hI
      rw [hIu]
      dsimp
      constructor <;> (intro h; injection h with he; rw [he])
    | ok s₀ =>
      let ⟨f₀, hsEq⟩ := initState_single_frame hI
      subst hsEq
      have hIu : initStateUnw p q = .ok ⟨f₀, [], q.callerMem⟩ :=
        (initStateUnw_ok_iff p q ⟨f₀, [], q.callerMem⟩).mpr ⟨rfl, hI⟩
      rw [hIu]
      constructor
      · intro ⟨u, hRu, ⟨c, hc, hEv⟩⟩
        cases hc
        let ⟨hCsu, hRb⟩ := reachesUnw_to_reaches_base_clean hBase rfl hRu
        cases u with
        | mk fu csu mu =>
          dsimp at hCsu hRb
          subst hCsu
          have hEvB := ((evalStepUnw_base_corresp hBase fu mu).2.2.2.2 k).mp hEv
          exact ⟨⟨[fu], mu⟩, hRb, ⟨0, rfl, hEvB⟩⟩
      · intro ⟨s, hRb, ⟨c, hc, hEv⟩⟩
        cases hc
        let ⟨fs, ms, hsEq2, hRu⟩ := reaches_to_reachesUnw_base hBase hRb
        subst hsEq2
        have hEvU := ((evalStepUnw_base_corresp hBase fs ms).2.2.2.2 k).mpr hEv
        exact ⟨⟨fs, [], ms⟩, hRu, ⟨0, rfl, hEvU⟩⟩
  have hBeh : ∀ q out,
      BehaviorUnw p q (embedTerminalOut out) ↔ Behavior p q out := by
    intro q out
    unfold BehaviorUnw Behavior ReachesResultUnw ReachesResult
    cases hI : initState p q with
    | error k₀ =>
      have hIu := (initStateUnw_error_iff p q k₀).mpr hI
      rw [hIu]
      exact ⟨fun h => (by cases h), fun h => (by cases h)⟩
    | ok s₀ =>
      let ⟨f₀, hsEq⟩ := initState_single_frame hI
      subst hsEq
      have hIu : initStateUnw p q = .ok ⟨f₀, [], q.callerMem⟩ :=
        (initStateUnw_ok_iff p q ⟨f₀, [], q.callerMem⟩).mpr ⟨rfl, hI⟩
      rw [hIu]
      constructor
      · intro ⟨u, hRu, ⟨c, hc, hEv⟩⟩
        cases hc
        let ⟨hCsu, hRb⟩ := reachesUnw_to_reaches_base_clean hBase rfl hRu
        cases u with
        | mk fu csu mu =>
          dsimp at hCsu hRb
          subst hCsu
          have hEvB := ((evalStepUnw_base_corresp hBase fu mu).2.2.1 out).mp hEv
          exact ⟨⟨[fu], mu⟩, hRb, ⟨0, rfl, hEvB⟩⟩
      · intro ⟨s, hRb, ⟨c, hc, hEv⟩⟩
        cases hc
        let ⟨fs, ms, hsEq2, hRu⟩ := reaches_to_reachesUnw_base hBase hRb
        subst hsEq2
        have hEvU := ((evalStepUnw_base_corresp hBase fs ms).2.2.1 out).mpr hEv
        exact ⟨⟨fs, [], ms⟩, hRu, ⟨0, rfl, hEvU⟩⟩
  have hNoAbort : ∀ q mem, ¬ BehaviorUnw p q (.aborted mem) := by
    intro q mem hB
    unfold BehaviorUnw ReachesResultUnw at hB
    cases hI : initStateUnw p q with
    | error k₀ => rw [hI] at hB; cases hB
    | ok u₀ =>
      rw [hI] at hB
      let ⟨hCs0, _⟩ := (initStateUnw_ok_iff p q u₀).mp hI
      let ⟨u, hRu, ⟨c, hc, hEv⟩⟩ := hB
      cases hc
      let ⟨hCsu, _⟩ := reachesUnw_to_reaches_base_clean hBase hCs0 hRu
      cases u with
      | mk fu csu mu =>
        dsimp at hCsu
        subst hCsu
        exact (evalStepUnw_base_corresp hBase fu mu).2.2.2.1 mem hEv
  have hWf : ∀ q, WellFormedUnw p q ↔ WellFormed p q := by
    intro q
    rw [wellFormedUnw_iff_no_fault]
    unfold WellFormed
    constructor
    · intro hNoF
      have hNoFB : ∀ k, ¬ ReachesResult p q (.fault k) :=
        fun k hfk => hNoF k ((hFault q k).mpr hfk)
      refine ⟨?_, hNoFB⟩
      cases hI : initState p q with
      | error k => exact False.elim (hNoFB k (by unfold ReachesResult; rw [hI]))
      | ok s₀ => exact ⟨s₀, rfl, fun _ _ => ⟨0, rfl⟩⟩
    · intro ⟨_, hNoFB⟩ k hfu
      exact hNoFB k ((hFault q k).mp hfu)
  have hDiv : ∀ q, DivergesUnw p q ↔ Diverges p q := by
    intro q
    constructor
    · intro ⟨u₀, hIu, tr, h0, hTr⟩
      let ⟨hCs0, hIb⟩ := (initStateUnw_ok_iff p q u₀).mp hIu
      have hTrCs : ∀ n, (tr n).callStack = [] ∧
          Step p ⟨[(tr n).active], (tr n).callerMem⟩
            (.step ⟨[(tr (n + 1)).active], (tr (n + 1)).callerMem⟩) := by
        intro n
        have hCsN : (tr n).callStack = [] := by
          induction n with
          | zero => rw [h0]; exact hCs0
          | succ k ihk =>
            let ⟨c, hc, hEv⟩ := hTr k
            cases hc
            cases hTk : tr k with
            | mk fk csk mk' =>
              rw [hTk] at ihk hEv
              dsimp at ihk
              subst ihk
              exact ((evalStepUnw_base_corresp hBase fk mk').1 (tr (k + 1)) hEv).1
        refine ⟨hCsN, ?_⟩
        let ⟨c, hc, hEv⟩ := hTr n
        cases hc
        cases hTn : tr n with
        | mk fn csn mn =>
          rw [hTn] at hCsN hEv
          dsimp at hCsN
          subst hCsN
          exact ⟨0, rfl, ((evalStepUnw_base_corresp hBase fn mn).1 (tr (n + 1)) hEv).2⟩
      exact ⟨⟨[u₀.active], u₀.callerMem⟩, hIb,
        fun n => ⟨[(tr n).active], (tr n).callerMem⟩,
        by dsimp; rw [h0], fun n => (hTrCs n).2⟩
    · intro ⟨s₀, hIb, tr, h0, hTr⟩
      let ⟨f₀, hsEq⟩ := initState_single_frame hIb
      subst hsEq
      have hIu : initStateUnw p q = .ok ⟨f₀, [], q.callerMem⟩ :=
        (initStateUnw_ok_iff p q ⟨f₀, [], q.callerMem⟩).mpr ⟨rfl, hIb⟩
      have hTrSingle : ∀ n, ∃ f m, tr n = ⟨[f], m⟩ := by
        intro n
        induction n with
        | zero => rw [h0]; exact ⟨f₀, q.callerMem, rfl⟩
        | succ k ihk =>
          let ⟨fk, mk', hTk⟩ := ihk
          let ⟨c, hc, hEv⟩ := hTr k
          cases hc
          rw [hTk] at hEv
          let ⟨f', m', hEq', _⟩ := (evalStepUnw_base_corresp hBase fk mk').2.1 (tr (k + 1)) hEv
          exact ⟨f', m', hEq'⟩
      let liftS : State → UnwindState := fun st =>
        match st.frames with
        | [f] => ⟨f, [], st.callerMem⟩
        | _ => ⟨f₀, [], q.callerMem⟩
      refine ⟨⟨f₀, [], q.callerMem⟩, hIu, fun n => liftS (tr n), ?_, ?_⟩
      · dsimp [liftS]; rw [h0]
      · intro n
        let ⟨fn, mn, hTn⟩ := hTrSingle n
        let ⟨fn1, mn1, hTn1⟩ := hTrSingle (n + 1)
        let ⟨c, hc, hEv⟩ := hTr n
        cases hc
        rw [hTn, hTn1] at hEv
        let ⟨f', m', hEq', hEvU⟩ := (evalStepUnw_base_corresp hBase fn mn).2.1 ⟨[fn1], mn1⟩ hEv
        injection hEq' with hFrEq hMEq
        injection hFrEq with hFEq
        subst hFEq
        subst hMEq
        dsimp [liftS]
        rw [hTn, hTn1]
        exact ⟨0, rfl, hEvU⟩
  have hPost : ∀ q post,
      SatisfiesPostUnw p q (liftTerminalPost post) ↔ SatisfiesPost p q post := by
    intro q post
    unfold SatisfiesPostUnw SatisfiesPost
    constructor
    · intro ⟨hWu, hPu⟩
      refine ⟨(hWf q).mp hWu, fun out hBo => ?_⟩
      have hBu := (hBeh q out).mpr hBo
      have hLp := hPu (embedTerminalOut out) hBu
      cases out <;> exact hLp
    · intro ⟨hWb, hPb⟩
      refine ⟨(hWf q).mpr hWb, fun out hBu => ?_⟩
      cases out with
      | returned o => exact hPb (.returned o) ((hBeh q (.returned o)).mp hBu)
      | unwound m => exact hPb (.unwound m) ((hBeh q (.unwound m)).mp hBu)
      | aborted m => exact False.elim (hNoAbort q m hBu)
  exact ⟨hWf, hBeh, hNoAbort, hFault, hDiv, hPost⟩

private theorem unwind_conservative_extension_exact_slice1 (p : Program) :
    (∀ s : State, ∀ u : UnwindState,
      embedStateUnw? s = some u → projectStateUnw? u = some s) ∧
    (isBaseMirProgram p = true →
      (∀ q : Query, WellFormedUnw p q ↔ WellFormed p q) ∧
      (∀ q : Query, ∀ out : TerminalOut,
        BehaviorUnw p q (embedTerminalOut out) ↔ Behavior p q out) ∧
      (∀ q : Query, ∀ mem : CallerMemory, ¬ BehaviorUnw p q (.aborted mem)) ∧
      (∀ q : Query, ∀ k : FaultKind,
        ReachesResultUnw p q (.fault k) ↔ ReachesResult p q (.fault k)) ∧
      (∀ q : Query, DivergesUnw p q ↔ Diverges p q) ∧
      (∀ q : Query, ∀ post : TerminalOut → Prop,
        SatisfiesPostUnw p q (liftTerminalPost post) ↔ SatisfiesPost p q post) ∧
      (∀ c : Crate, c.program = p →
        (CrateTheoremUnw c ↔ CrateTheorem c) ∧
        (UnitTheoremUnw c ↔ UnitTheorem c))) := by
  constructor
  · intro s u hEmb
    cases s with
    | mk frs mem =>
      dsimp [embedStateUnw?] at hEmb
      cases frs with
      | nil => cases hEmb
      | cons f rest =>
        cases rest with
        | cons _ _ => cases hEmb
        | nil =>
          injection hEmb with hEq
          subst hEq
          rfl
  · intro hBase
    let ⟨hWf, hBeh, hNoAbort, hFault, hDiv, hPost⟩ := base_program_outcomes_iff hBase
    refine ⟨hWf, hBeh, hNoAbort, hFault, hDiv, hPost, ?_⟩
    intro c hcEq
    subst hcEq
    have hPv : ProgramVerifiedUnw c.program c.specs ↔ ProgramVerified c.program c.specs := by
      unfold ProgramVerifiedUnw ProgramVerified
      have hBv :
          (∀ defId body, Trusted.MirSemantics.getElem? c.program.bodies defId = some body →
            BodyVerifiedUnw c.program defId body (c.specs.safety body.identity)) ↔
          (∀ defId body, Trusted.MirSemantics.getElem? c.program.bodies defId = some body →
            BodyVerified c.program defId body (c.specs.safety body.identity)) := by
        constructor <;> intro hAll defId body hGet
        · let ⟨hg, hadm, hargs⟩ := hAll defId body hGet
          refine ⟨hg, hadm, fun args hva huns => ?_⟩
          have hBaseE : isBaseMirProgram (entryProgForBody c.program defId) = true := hBase
          exact ((base_program_outcomes_iff hBaseE).1 { args := args }).mp (hargs args hva huns)
        · let ⟨hg, hadm, hargs⟩ := hAll defId body hGet
          refine ⟨hg, hadm, fun args hva huns => ?_⟩
          have hBaseE : isBaseMirProgram (entryProgForBody c.program defId) = true := hBase
          exact ((base_program_outcomes_iff hBaseE).1 { args := args }).mpr (hargs args hva huns)
      constructor
      · intro ⟨h1, h2, h3, h4, h5, h6, h7⟩
        exact ⟨h1, h2, h3, h4, h5, hBv.mp h6, h7⟩
      · intro ⟨h1, h2, h3, h4, h5, h6, h7⟩
        exact ⟨h1, h2, h3, h4, h5, hBv.mpr h6, h7⟩
    unfold CrateTheoremUnw CrateTheorem UnitTheoremUnw UnitTheorem
    exact ⟨⟨fun ⟨h1, h2⟩ => ⟨h1, hPv.mp h2⟩, fun ⟨h1, h2⟩ => ⟨h1, hPv.mpr h2⟩⟩,
           ⟨fun ⟨h1, h2⟩ => ⟨h1, hPv.mp h2⟩, fun ⟨h1, h2⟩ => ⟨h1, hPv.mpr h2⟩⟩⟩

/-! ### Part B: Theorem 3 (`panicAbortEntryTransform_refines_unwound_to_aborted_slice1`) -/

private theorem list_any_map {α β : Type} (f : α → β) (p : β → Bool) :
    ∀ (xs : List α), (xs.map f).any p = xs.any (fun x => p (f x))
  | [] => rfl
  | x :: xs => by dsimp [List.map, List.any]; rw [list_any_map f p xs]

private theorem map_rewriteBbPanicAbort_hasStorage (body : Body) (lid : LocalId) :
    hasStorageAnnotation
      { body with basicBlocks := body.basicBlocks.map rewriteBbPanicAbort } lid =
    hasStorageAnnotation body lid := by
  unfold hasStorageAnnotation
  dsimp
  rw [list_any_map]
  rfl

private theorem map_rewriteBbPanicAbort_storageInBounds (body : Body) :
    storageAnnotationsInBounds
      { body with basicBlocks := body.basicBlocks.map rewriteBbPanicAbort } =
    storageAnnotationsInBounds body := by
  unfold storageAnnotationsInBounds
  dsimp
  rw [list_all_map]
  rfl

private theorem map_rewriteBbPanicAbort_initLocalsLoop (body : Body) (args : List Val) :
    ∀ (idx : Nat) (rem : List MirTy),
      initLocalsLoop
        { body with basicBlocks := body.basicBlocks.map rewriteBbPanicAbort }
        args idx rem =
      initLocalsLoop body args idx rem
  | _, [] => rfl
  | idx, ty :: rest => by
    dsimp [initLocalsLoop]
    rw [map_rewriteBbPanicAbort_hasStorage]
    rw [map_rewriteBbPanicAbort_initLocalsLoop body args (idx + 1) rest]

private theorem initCalleeFrameUnw_defId {calleeDefId : DefId} {callee : Body}
    {argVals : List Val} {cFrame : FrameState}
    (h : initCalleeFrameUnw calleeDefId callee argVals = .ok cFrame) :
    cFrame.defId = calleeDefId := by
  unfold initCalleeFrameUnw at h
  cases h1 : callee.basicBlocks.isEmpty <;> rw [h1] at h
  · dsimp at h
    cases h2 : (!Nat.blt callee.argumentCount callee.locals.length) <;> rw [h2] at h
    · dsimp at h
      cases h3 : (!storageAnnotationsInBounds callee) <;> rw [h3] at h
      · dsimp at h
        cases h4 : (!callee.locals.all isSupportedScalarOrUnitTy) <;> rw [h4] at h
        · dsimp at h
          cases h5 : (!checkArgsMatch argVals ((callee.locals.drop 1).take callee.argumentCount)) <;>
            rw [h5] at h
          · dsimp at h
            injection h with hEq; rw [← hEq]
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

/-- Stack relation for `-C panic=abort`: non-bottom frames are identical and
never belong to `entryDefId`; the bottom frame belongs to `entryDefId`, shares
`(callerFrame, dst, target)`, and replaces `.continue_` with `.terminate` while
forbidding `.continue_` in `pTgt`. -/
private inductive PanicAbortStackRel (entryDef : DefId) :
    List CallContUnw → List CallContUnw → Prop where
  | nil : PanicAbortStackRel entryDef [] []
  | bottom (c₁ c₂ : CallContUnw) :
      c₁.callerFrame = c₂.callerFrame →
      c₁.callerFrame.defId = entryDef →
      c₁.dst = c₂.dst →
      c₁.target = c₂.target →
      c₂.unwind ≠ .continue_ →
      (c₁.unwind = c₂.unwind ∨ (c₁.unwind = .continue_ ∧ c₂.unwind = .terminate)) →
      PanicAbortStackRel entryDef [c₁] [c₂]
  | upper (c : CallContUnw) (r₁ r₂ : List CallContUnw) :
      c.callerFrame.defId ≠ entryDef →
      r₁ ≠ [] →
      PanicAbortStackRel entryDef r₁ r₂ →
      PanicAbortStackRel entryDef (c :: r₁) (c :: r₂)

/-- State relation for `-C panic=abort` entry transformation. -/
private noncomputable def PanicAbortStateRel (entryDef : DefId)
    (s₁ s₂ : UnwindState) : Prop :=
  s₁.active = s₂.active ∧
  s₁.callerMem = s₂.callerMem ∧
  PanicAbortStackRel entryDef s₁.callStack s₂.callStack ∧
  (s₁.callStack = [] → s₁.active.defId = entryDef) ∧
  (s₁.callStack ≠ [] → s₁.active.defId ≠ entryDef)

/-- Exact 1-to-1 outcome refinement predicate between `r₁` (in `pSrc`) and `r₂`
(in `pTgt`) under `-C panic=abort`. -/
private noncomputable def PanicAbortResRel (entryDef : DefId)
    (r₁ r₂ : StepResult UnwindState UnwindOut) : Prop :=
  match r₁, r₂ with
  | .step s₁', .step s₂' => PanicAbortStateRel entryDef s₁' s₂'
  | .done (.returned o₁), .done (.returned o₂) => o₁ = o₂
  | .done (.unwound m₁), .done (.aborted m₂) => m₁ = m₂
  | .done (.aborted m₁), .done (.aborted m₂) => m₁ = m₂
  | .fault k₁, .fault k₂ => k₁ = k₂
  | _, _ => False

private theorem panicAbort_entry_body_eq {pSrc pTgt : Program} {entryBody : Body}
    (hSet : setElem? pSrc.bodies pSrc.entryDefId
      { entryBody with basicBlocks := entryBody.basicBlocks.map rewriteBbPanicAbort } =
      some pTgt.bodies) :
    Trusted.MirSemantics.getElem? pTgt.bodies pSrc.entryDefId =
      some { entryBody with basicBlocks := entryBody.basicBlocks.map rewriteBbPanicAbort } :=
  setElem?_getElem?_same hSet

private theorem panicAbort_enterCleanup_entry {pSrc pTgt : Program} {entryBody : Body}
    (hGetEnt : Trusted.MirSemantics.getElem? pSrc.bodies pSrc.entryDefId = some entryBody)
    (hSet : setElem? pSrc.bodies pSrc.entryDefId
      { entryBody with basicBlocks := entryBody.basicBlocks.map rewriteBbPanicAbort } =
      some pTgt.bodies)
    (frame : FrameState) (hFrameEnt : frame.defId = pSrc.entryDefId)
    (mem : CallerMemory) (padBb : BasicBlockId) :
    enterCleanupBlockUnw pTgt frame [] mem padBb =
      enterCleanupBlockUnw pSrc frame [] mem padBb := by
  unfold enterCleanupBlockUnw
  rw [hFrameEnt, hGetEnt, panicAbort_entry_body_eq hSet]
  dsimp
  rw [getElem?_map]
  cases Trusted.MirSemantics.getElem? entryBody.basicBlocks padBb with
  | none => rfl
  | some bb => rfl

private theorem panicAbort_enterCleanup_nonEntry {pSrc pTgt : Program} {entryBody : Body}
    (hSet : setElem? pSrc.bodies pSrc.entryDefId
      { entryBody with basicBlocks := entryBody.basicBlocks.map rewriteBbPanicAbort } =
      some pTgt.bodies)
    (frame : FrameState) (hFrameNe : frame.defId ≠ pSrc.entryDefId)
    (r₁ r₂ : List CallContUnw) (hR1Ne : r₁ ≠ [])
    (hStack : PanicAbortStackRel pSrc.entryDefId r₁ r₂)
    (mem : CallerMemory) (padBb : BasicBlockId) :
    PanicAbortResRel pSrc.entryDefId
      (enterCleanupBlockUnw pSrc frame r₁ mem padBb)
      (enterCleanupBlockUnw pTgt frame r₂ mem padBb) := by
  unfold enterCleanupBlockUnw
  rw [setElem?_getElem?_ne hSet hFrameNe]
  cases Trusted.MirSemantics.getElem? pSrc.bodies frame.defId with
  | none => exact rfl
  | some body =>
    dsimp
    cases Trusted.MirSemantics.getElem? body.basicBlocks padBb with
    | none => exact rfl
    | some bb =>
      dsimp
      cases !bb.cleanup with
      | true => exact rfl
      | false =>
        dsimp [PanicAbortResRel, PanicAbortStateRel]
        exact ⟨rfl, rfl, hStack,
          fun hNil => False.elim (hR1Ne hNil),
          fun _ => hFrameNe⟩

private theorem panicAbort_enterCleanup_entry_rel {pSrc pTgt : Program} {entryBody : Body}
    (hGetEnt : Trusted.MirSemantics.getElem? pSrc.bodies pSrc.entryDefId = some entryBody)
    (hSet : setElem? pSrc.bodies pSrc.entryDefId
      { entryBody with basicBlocks := entryBody.basicBlocks.map rewriteBbPanicAbort } =
      some pTgt.bodies)
    (frame : FrameState) (hFrameEnt : frame.defId = pSrc.entryDefId)
    (mem : CallerMemory) (padBb : BasicBlockId) :
    PanicAbortResRel pSrc.entryDefId
      (enterCleanupBlockUnw pSrc frame [] mem padBb)
      (enterCleanupBlockUnw pTgt frame [] mem padBb) := by
  rw [panicAbort_enterCleanup_entry hGetEnt hSet frame hFrameEnt mem padBb]
  unfold enterCleanupBlockUnw
  rw [hFrameEnt, hGetEnt]
  dsimp
  cases Trusted.MirSemantics.getElem? entryBody.basicBlocks padBb with
  | none => exact rfl
  | some bb =>
    dsimp
    cases !bb.cleanup with
    | true => exact rfl
    | false =>
      dsimp [PanicAbortResRel, PanicAbortStateRel]
      exact ⟨rfl, rfl, PanicAbortStackRel.nil,
        fun _ => rfl,
        fun hNe => False.elim (hNe rfl)⟩

private theorem panicAbort_dispatchUnwindStack {pSrc pTgt : Program} {entryBody : Body}
    (hGetEnt : Trusted.MirSemantics.getElem? pSrc.bodies pSrc.entryDefId = some entryBody)
    (hSet : setElem? pSrc.bodies pSrc.entryDefId
      { entryBody with basicBlocks := entryBody.basicBlocks.map rewriteBbPanicAbort } =
      some pTgt.bodies)
    (mem : CallerMemory) :
    ∀ {cs₁ cs₂ : List CallContUnw},
      cs₁ ≠ [] →
      PanicAbortStackRel pSrc.entryDefId cs₁ cs₂ →
      PanicAbortResRel pSrc.entryDefId
        (dispatchUnwindStack pSrc mem cs₁)
        (dispatchUnwindStack pTgt mem cs₂) := by
  intro cs₁ cs₂ hNe hRel
  induction hRel with
  | nil => exact False.elim (hNe rfl)
  | bottom c₁ c₂ hCf hEnt hDst hTgt hNeCont hUnw =>
    dsimp [dispatchUnwindStack]
    cases hUnw with
    | inr hPair =>
      let ⟨hU1, hU2⟩ := hPair
      rw [hU1, hU2]
      exact rfl
    | inl hEqU =>
      rw [hEqU]
      cases hU2 : c₂.unwind with
      | continue_ => exact False.elim (hNeCont hU2)
      | unreachable => exact rfl
      | terminate => exact rfl
      | cleanup padBb =>
        rw [hCf]
        exact panicAbort_enterCleanup_entry_rel hGetEnt hSet c₂.callerFrame
          (by rw [← hCf]; exact hEnt) mem padBb
  | upper c r₁ r₂ hNeEnt hR1Ne hSub ih =>
    dsimp [dispatchUnwindStack]
    cases c.unwind with
    | cleanup padBb =>
      exact panicAbort_enterCleanup_nonEntry hSet c.callerFrame hNeEnt r₁ r₂ hR1Ne hSub mem padBb
    | continue_ =>
      exact ih hR1Ne
    | unreachable => exact rfl
    | terminate => exact rfl

private theorem panicAbort_returnToCaller {pSrc pTgt : Program} {entryBody : Body}
    (hGetEnt : Trusted.MirSemantics.getElem? pSrc.bodies pSrc.entryDefId = some entryBody)
    (hSet : setElem? pSrc.bodies pSrc.entryDefId
      { entryBody with basicBlocks := entryBody.basicBlocks.map rewriteBbPanicAbort } =
      some pTgt.bodies)
    (retVal : Val) (mem : CallerMemory) :
    ∀ {c₁ c₂ : CallContUnw} {r₁ r₂ : List CallContUnw},
      PanicAbortStackRel pSrc.entryDefId (c₁ :: r₁) (c₂ :: r₂) →
      PanicAbortResRel pSrc.entryDefId
        (returnToCallerUnw pSrc retVal c₁ r₁ mem)
        (returnToCallerUnw pTgt retVal c₂ r₂ mem) := by
  intro c₁ c₂ r₁ r₂ hRel
  cases hRel with
  | bottom _ _ hCf hEnt hDst hTgt _ _ =>
    unfold returnToCallerUnw
    rw [← hCf, hEnt, ← hDst, ← hTgt, hGetEnt, panicAbort_entry_body_eq hSet]
    dsimp
    cases !c₁.dst.projection.isEmpty with
    | true => exact rfl
    | false =>
      dsimp
      cases Trusted.MirSemantics.getElem? entryBody.locals c₁.dst.localId with
      | none => exact rfl
      | some dstTy =>
        dsimp
        cases writePlace c₁.callerFrame.locals c₁.dst.localId dstTy retVal with
        | error _ => exact rfl
        | ok locs' =>
          dsimp
          cases c₁.target with
          | none => exact rfl
          | some nextBb =>
            dsimp [PanicAbortResRel, PanicAbortStateRel]
            exact ⟨rfl, rfl, PanicAbortStackRel.nil,
              fun _ => hEnt, fun hNe => False.elim (hNe rfl)⟩
  | upper _ _ _ hNeEnt hR1Ne hSub =>
    unfold returnToCallerUnw
    rw [setElem?_getElem?_ne hSet hNeEnt]
    cases Trusted.MirSemantics.getElem? pSrc.bodies c₁.callerFrame.defId with
    | none => exact rfl
    | some callerBody =>
      dsimp
      cases !c₁.dst.projection.isEmpty with
      | true => exact rfl
      | false =>
        dsimp
        cases Trusted.MirSemantics.getElem? callerBody.locals c₁.dst.localId with
        | none => exact rfl
        | some dstTy =>
          dsimp
          cases writePlace c₁.callerFrame.locals c₁.dst.localId dstTy retVal with
          | error _ => exact rfl
          | ok locs' =>
            dsimp
            cases c₁.target with
            | none => exact rfl
            | some nextBb =>
              dsimp [PanicAbortResRel, PanicAbortStateRel]
              exact ⟨rfl, rfl, hSub,
                fun hNil => False.elim (hR1Ne hNil),
                fun _ => hNeEnt⟩

private theorem bodyCallsDefId_false_call_ne {targetDef : DefId} {body : Body}
    {bb : BasicBlock} {bi : BasicBlockId}
    {fn : DefId} {args : List Operand} {dst : Place}
    {tgt : Option BasicBlockId} {unw : UnwindAction}
    (hNoCall : bodyCallsDefId targetDef body = false)
    (hBb : Trusted.MirSemantics.getElem? body.basicBlocks bi = some bb)
    (hTerm : bb.terminator = .call fn args dst tgt unw) :
    fn ≠ targetDef := by
  have hFalse := list_any_false_getElem? hNoCall hBb
  rw [hTerm] at hFalse
  exact nat_ne_of_beq_false hFalse

/-- Helper: single step when `callStack` is non-empty (both `bottom` and `upper`). -/
private theorem panicAbort_step_nonEmpty {pSrc pTgt : Program} {entryBody : Body}
    (hNoRec : pSrc.bodies.any (bodyCallsDefId pSrc.entryDefId) = false)
    (hGetEnt : Trusted.MirSemantics.getElem? pSrc.bodies pSrc.entryDefId = some entryBody)
    (hSet : setElem? pSrc.bodies pSrc.entryDefId
      { entryBody with basicBlocks := entryBody.basicBlocks.map rewriteBbPanicAbort } =
      some pTgt.bodies)
    (f₁ : FrameState) (m₁ : CallerMemory)
    (c₁ c₂ : CallContUnw) (r₁ r₂ : List CallContUnw)
    (hDefNe : f₁.defId ≠ pSrc.entryDefId)
    (hStack : PanicAbortStackRel pSrc.entryDefId (c₁ :: r₁) (c₂ :: r₂)) :
    PanicAbortResRel pSrc.entryDefId
      (evalStepUnw pSrc 0 ⟨f₁, c₁ :: r₁, m₁⟩)
      (evalStepUnw pTgt 0 ⟨f₁, c₂ :: r₂, m₁⟩) := by
  unfold evalStepUnw
  dsimp
  rw [setElem?_getElem?_ne hSet hDefNe]
  cases hBod : Trusted.MirSemantics.getElem? pSrc.bodies f₁.defId with
  | none => exact rfl
  | some body =>
    dsimp
    cases hBb : Trusted.MirSemantics.getElem? body.basicBlocks f₁.blockIdx with
    | none => exact rfl
    | some bb =>
      dsimp
      cases Trusted.MirSemantics.getElem? bb.statements f₁.stmtIdx with
      | some stmt =>
        dsimp
        let ⟨hNoDone, hSingle⟩ := evalStatement_outcomes body f₁ m₁ stmt
        cases hEv : evalStatement body f₁ m₁ stmt with
        | fault _ => exact rfl
        | done out => exact False.elim (hNoDone out hEv)
        | step st' =>
          dsimp
          let ⟨f', hf', hDefEq⟩ := hSingle st' hEv
          cases st' with
          | mk frs m' =>
            dsimp at hf'
            subst hf'
            dsimp [PanicAbortResRel, PanicAbortStateRel]
            exact ⟨rfl, rfl, hStack, fun h => (by cases h),
              fun _ => by rw [hDefEq]; exact hDefNe⟩
      | none =>
        dsimp
        cases Nat.beq f₁.stmtIdx bb.statements.length with
        | false => exact rfl
        | true =>
          dsimp [evalTerminatorUnw]
          cases hTerm : bb.terminator with
          | goto tgt =>
            dsimp [PanicAbortResRel, PanicAbortStateRel]
            exact ⟨rfl, rfl, hStack, fun h => (by cases h), fun _ => hDefNe⟩
          | unreachable => exact rfl
          | unsupported => exact rfl
          | return_ =>
            cases bb.cleanup with
            | true => exact rfl
            | false =>
              dsimp
              cases Trusted.MirSemantics.getElem? f₁.locals 0 with
              | none => exact rfl
              | some sl =>
                cases sl with
                | dead => exact rfl
                | live ov =>
                  cases ov with
                  | none => exact rfl
                  | some rv =>
                    exact panicAbort_returnToCaller hGetEnt hSet rv m₁ hStack
          | switchInt discr targets =>
            dsimp
            cases evalPrimitiveOperand body.locals f₁.locals discr with
            | error _ => exact rfl
            | ok pair =>
              cases pair with
              | mk dv la =>
                cases dv with
                | scalar sv =>
                  dsimp
                  cases evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches with
                  | error _ => exact rfl
                  | ok tgt =>
                    dsimp [PanicAbortResRel, PanicAbortStateRel]
                    exact ⟨rfl, rfl, hStack, fun h => (by cases h), fun _ => hDefNe⟩
                | bool b =>
                  dsimp
                  cases evalBoolSwitchBranches b targets.otherwise targets.branches with
                  | error _ => exact rfl
                  | ok tgt =>
                    dsimp [PanicAbortResRel, PanicAbortStateRel]
                    exact ⟨rfl, rfl, hStack, fun h => (by cases h), fun _ => hDefNe⟩
                | unit | ptr _ | enumVal _ _ | tuple _ | bytes _ => exact rfl
          | unwindResume =>
            dsimp
            cases !bb.cleanup with
            | true => exact rfl
            | false =>
              dsimp
              exact panicAbort_dispatchUnwindStack hGetEnt hSet m₁
                (fun h => (by cases h)) hStack
          | assert cond expected msg tgt unw =>
            dsimp
            cases evalPrimitiveOperand body.locals f₁.locals cond with
            | error _ => exact rfl
            | ok pair =>
              cases pair with
              | mk v la =>
                cases v with
                | bool b =>
                  dsimp
                  cases boolEq b expected with
                  | true =>
                    dsimp [PanicAbortResRel, PanicAbortStateRel]
                    exact ⟨rfl, rfl, hStack, fun h => (by cases h), fun _ => hDefNe⟩
                  | false =>
                    dsimp [dispatchLocalUnwind]
                    cases unw with
                    | cleanup padBb =>
                      exact panicAbort_enterCleanup_nonEntry hSet
                        { f₁ with locals := la } hDefNe (c₁ :: r₁) (c₂ :: r₂)
                        (fun h => (by cases h)) hStack m₁ padBb
                    | continue_ =>
                      exact panicAbort_dispatchUnwindStack hGetEnt hSet m₁
                        (fun h => (by cases h)) hStack
                    | unreachable => exact rfl
                    | terminate => exact rfl
                | scalar _ | unit | ptr _ | enumVal _ _ | tuple _ | bytes _ =>
                  exact rfl
          | call calleeId args dst tgt unw =>
            dsimp
            have hNoCallB : bodyCallsDefId pSrc.entryDefId body = false :=
              list_any_false_getElem? hNoRec hBod
            have hCalleeNe : calleeId ≠ pSrc.entryDefId :=
              bodyCallsDefId_false_call_ne hNoCallB hBb hTerm
            have hCalleeBod :
                Trusted.MirSemantics.getElem? pTgt.bodies calleeId =
                  Trusted.MirSemantics.getElem? pSrc.bodies calleeId :=
              setElem?_getElem?_ne hSet hCalleeNe
            cases evalCallArgsUnw body.locals f₁.locals args with
            | error _ => exact rfl
            | ok pair =>
              dsimp
              rw [hCalleeBod]
              cases Trusted.MirSemantics.getElem? pSrc.bodies calleeId with
              | none => exact rfl
              | some cBody =>
                dsimp
                cases hInitC : initCalleeFrameUnw calleeId cBody pair.1 with
                | error _ => exact rfl
                | ok cFrame =>
                  have hCDef := initCalleeFrameUnw_defId hInitC
                  dsimp [PanicAbortResRel, PanicAbortStateRel]
                  refine ⟨rfl, rfl,
                    PanicAbortStackRel.upper _ _ _ hDefNe (fun h => (by cases h)) hStack,
                    fun h => (by cases h),
                    fun _ => by rw [hCDef]; exact hCalleeNe⟩

private theorem panicAbort_step_rel {pSrc pTgt : Program} {entryBody : Body}
    (hNoRec : pSrc.bodies.any (bodyCallsDefId pSrc.entryDefId) = false)
    (hGetEnt : Trusted.MirSemantics.getElem? pSrc.bodies pSrc.entryDefId = some entryBody)
    (hSet : setElem? pSrc.bodies pSrc.entryDefId
      { entryBody with basicBlocks := entryBody.basicBlocks.map rewriteBbPanicAbort } =
      some pTgt.bodies)
    {s₁ s₂ : UnwindState}
    (hRel : PanicAbortStateRel pSrc.entryDefId s₁ s₂) :
    PanicAbortResRel pSrc.entryDefId
      (evalStepUnw pSrc 0 s₁) (evalStepUnw pTgt 0 s₂) := by
  let ⟨hActEq, hMemEq, hStackRel, hNilEnt, hConsNe⟩ := hRel
  cases s₁ with
  | mk f₁ cs₁ m₁ =>
    cases s₂ with
    | mk f₂ cs₂ m₂ =>
      dsimp at hActEq hMemEq hStackRel hNilEnt hConsNe
      subst hActEq
      subst hMemEq
      cases hStackRel with
      | bottom c₁ c₂ hCf hEnt hDst hTgt hNeCont hUnw =>
        exact panicAbort_step_nonEmpty hNoRec hGetEnt hSet f₁ m₁ c₁ c₂ [] []
          (hConsNe (fun h => (by cases h)))
          (PanicAbortStackRel.bottom c₁ c₂ hCf hEnt hDst hTgt hNeCont hUnw)
      | upper c r₁ r₂ hNeEnt hR1Ne hSub =>
        exact panicAbort_step_nonEmpty hNoRec hGetEnt hSet f₁ m₁ c c r₁ r₂
          (hConsNe (fun h => (by cases h)))
          (PanicAbortStackRel.upper c r₁ r₂ hNeEnt hR1Ne hSub)
      | nil =>
        have hDefEnt : f₁.defId = pSrc.entryDefId := hNilEnt rfl
        unfold evalStepUnw
        dsimp
        rw [hDefEnt, hGetEnt, panicAbort_entry_body_eq hSet]
        dsimp
        rw [getElem?_map]
        cases hBb : Trusted.MirSemantics.getElem? entryBody.basicBlocks f₁.blockIdx with
        | none => exact rfl
        | some bb =>
          dsimp [rewriteBbPanicAbort]
          cases hSt : Trusted.MirSemantics.getElem? bb.statements f₁.stmtIdx with
          | some stmt =>
            dsimp
            let ⟨hNoDone, hSingle⟩ := evalStatement_outcomes entryBody f₁ m₁ stmt
            have hEvStEq :
                evalStatement
                  { entryBody with basicBlocks := entryBody.basicBlocks.map rewriteBbPanicAbort }
                  f₁ m₁ stmt =
                evalStatement entryBody f₁ m₁ stmt := by
              cases stmt <;> rfl
            rw [hEvStEq]
            cases hEv : evalStatement entryBody f₁ m₁ stmt with
            | fault _ => exact rfl
            | done out => exact False.elim (hNoDone out hEv)
            | step st' =>
              dsimp
              let ⟨f', hf', hDefEq⟩ := hSingle st' hEv
              cases st' with
              | mk frs m' =>
                dsimp at hf'
                subst hf'
                dsimp [PanicAbortResRel, PanicAbortStateRel]
                exact ⟨rfl, rfl, PanicAbortStackRel.nil,
                  fun _ => hDefEq.trans hDefEnt,
                  fun h => False.elim (h rfl)⟩
          | none =>
            dsimp
            cases Nat.beq f₁.stmtIdx bb.statements.length with
            | false => exact rfl
            | true =>
              dsimp [evalTerminatorUnw]
              cases hTerm : bb.terminator with
              | goto tgt =>
                dsimp [PanicAbortResRel, PanicAbortStateRel]
                exact ⟨rfl, rfl, PanicAbortStackRel.nil,
                  fun _ => hDefEnt, fun h => False.elim (h rfl)⟩
              | unreachable => exact rfl
              | unsupported => exact rfl
              | return_ =>
                dsimp
                cases bb.cleanup with
                | true => exact rfl
                | false =>
                  dsimp
                  cases Trusted.MirSemantics.getElem? f₁.locals 0 with
                  | none => exact rfl
                  | some sl =>
                    cases sl with
                    | dead => exact rfl
                    | live ov =>
                      cases ov with
                      | none => exact rfl
                      | some rv => exact rfl
              | switchInt discr targets =>
                dsimp
                cases evalPrimitiveOperand entryBody.locals f₁.locals discr with
                | error _ => exact rfl
                | ok pair =>
                  cases pair with
                  | mk dv la =>
                    cases dv with
                    | scalar sv =>
                      dsimp
                      cases evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches with
                      | error _ => exact rfl
                      | ok tgt =>
                        dsimp [PanicAbortResRel, PanicAbortStateRel]
                        exact ⟨rfl, rfl, PanicAbortStackRel.nil,
                          fun _ => hDefEnt, fun h => False.elim (h rfl)⟩
                    | bool b =>
                      dsimp
                      cases evalBoolSwitchBranches b targets.otherwise targets.branches with
                      | error _ => exact rfl
                      | ok tgt =>
                        dsimp [PanicAbortResRel, PanicAbortStateRel]
                        exact ⟨rfl, rfl, PanicAbortStackRel.nil,
                          fun _ => hDefEnt, fun h => False.elim (h rfl)⟩
                    | unit | ptr _ | enumVal _ _ | tuple _ | bytes _ => exact rfl
              | unwindResume =>
                dsimp
                cases bb.cleanup with
                | false => exact rfl
                | true => exact rfl
              | assert cond expected msg tgt unw =>
                have hEvalCase :
                    ∀ (u₂ : UnwindAction),
                      (u₂ = unw ∧ unw ≠ .continue_) ∨ (unw = .continue_ ∧ u₂ = .terminate) →
                      PanicAbortResRel pSrc.entryDefId
                        (match evalPrimitiveOperand entryBody.locals f₁.locals cond with
                        | .error k => .fault k
                        | .ok (.bool b, la) =>
                          if boolEq b expected then
                            .step ⟨{ f₁ with blockIdx := tgt, stmtIdx := 0, locals := la }, [], m₁⟩
                          else
                            dispatchLocalUnwind pSrc { f₁ with locals := la } [] m₁ unw
                        | .ok (_, _) => .fault .unsupported)
                        (match evalPrimitiveOperand entryBody.locals f₁.locals cond with
                        | .error k => .fault k
                        | .ok (.bool b, la) =>
                          if boolEq b expected then
                            .step ⟨{ f₁ with blockIdx := tgt, stmtIdx := 0, locals := la }, [], m₁⟩
                          else
                            dispatchLocalUnwind pTgt { f₁ with locals := la } [] m₁ u₂
                        | .ok (_, _) => .fault .unsupported) := by
                  intro u₂ hU
                  cases evalPrimitiveOperand entryBody.locals f₁.locals cond with
                  | error _ => exact rfl
                  | ok pair =>
                    cases pair with
                    | mk v la =>
                      cases v with
                      | bool b =>
                        dsimp
                        cases boolEq b expected with
                        | true =>
                          dsimp [PanicAbortResRel, PanicAbortStateRel]
                          exact ⟨rfl, rfl, PanicAbortStackRel.nil,
                            fun _ => hDefEnt, fun h => False.elim (h rfl)⟩
                        | false =>
                          dsimp
                          cases hU with
                          | inr hp =>
                            let ⟨h1, h2⟩ := hp
                            rw [h1, h2]; exact rfl
                          | inl hp =>
                            let ⟨hEq, hNeC⟩ := hp
                            rw [hEq]
                            cases unw with
                            | continue_ => exact False.elim (hNeC rfl)
                            | unreachable => exact rfl
                            | terminate => exact rfl
                            | cleanup padBb =>
                              exact panicAbort_enterCleanup_entry_rel hGetEnt hSet
                                { f₁ with locals := la } hDefEnt m₁ padBb
                      | scalar _ | unit | ptr _ | enumVal _ _ | tuple _ | bytes _ =>
                        exact rfl
                cases unw with
                | continue_ => dsimp; exact hEvalCase .terminate (Or.inr ⟨rfl, rfl⟩)
                | cleanup padBb => dsimp; exact hEvalCase (.cleanup padBb) (Or.inl ⟨rfl, fun h => (by cases h)⟩)
                | unreachable => dsimp; exact hEvalCase .unreachable (Or.inl ⟨rfl, fun h => (by cases h)⟩)
                | terminate => dsimp; exact hEvalCase .terminate (Or.inl ⟨rfl, fun h => (by cases h)⟩)
              | call calleeId args dst tgt unw =>
                have hNoCallEnt : bodyCallsDefId pSrc.entryDefId entryBody = false :=
                  list_any_false_getElem? hNoRec hGetEnt
                have hCalleeNe : calleeId ≠ pSrc.entryDefId :=
                  bodyCallsDefId_false_call_ne hNoCallEnt hBb hTerm
                have hCalleeBod :
                    Trusted.MirSemantics.getElem? pTgt.bodies calleeId =
                      Trusted.MirSemantics.getElem? pSrc.bodies calleeId :=
                  setElem?_getElem?_ne hSet hCalleeNe
                have hCallCase :
                    ∀ (u₂ : UnwindAction),
                      u₂ ≠ .continue_ →
                      (unw = u₂ ∨ (unw = .continue_ ∧ u₂ = .terminate)) →
                      PanicAbortResRel pSrc.entryDefId
                        (match evalCallArgsUnw entryBody.locals f₁.locals args with
                        | .error k => .fault k
                        | .ok (av, la) =>
                          match Trusted.MirSemantics.getElem? pSrc.bodies calleeId with
                          | none => .fault .unsupported
                          | some cb =>
                            match initCalleeFrameUnw calleeId cb av with
                            | .error k => .fault k
                            | .ok cf =>
                              .step ⟨cf, [{ callerFrame := { f₁ with locals := la }, dst, target := tgt, unwind := unw }], m₁⟩)
                        (match evalCallArgsUnw entryBody.locals f₁.locals args with
                        | .error k => .fault k
                        | .ok (av, la) =>
                          match Trusted.MirSemantics.getElem? pTgt.bodies calleeId with
                          | none => .fault .unsupported
                          | some cb =>
                            match initCalleeFrameUnw calleeId cb av with
                            | .error k => .fault k
                            | .ok cf =>
                              .step ⟨cf, [{ callerFrame := { f₁ with locals := la }, dst, target := tgt, unwind := u₂ }], m₁⟩) := by
                  intro u₂ hNeC hU
                  cases evalCallArgsUnw entryBody.locals f₁.locals args with
                  | error _ => exact rfl
                  | ok pair =>
                    dsimp
                    rw [hCalleeBod]
                    cases Trusted.MirSemantics.getElem? pSrc.bodies calleeId with
                    | none => exact rfl
                    | some cb =>
                      dsimp
                      cases hInitC : initCalleeFrameUnw calleeId cb pair.1 with
                      | error _ => exact rfl
                      | ok cf =>
                        have hCDef := initCalleeFrameUnw_defId hInitC
                        dsimp [PanicAbortResRel, PanicAbortStateRel]
                        refine ⟨rfl, rfl,
                          PanicAbortStackRel.bottom _ _ rfl hDefEnt rfl rfl hNeC hU,
                          fun h => (by cases h),
                          fun _ => by rw [hCDef]; exact hCalleeNe⟩
                cases unw with
                | continue_ => dsimp; exact hCallCase .terminate (fun h => (by cases h)) (Or.inr ⟨rfl, rfl⟩)
                | cleanup padBb => dsimp; exact hCallCase (.cleanup padBb) (fun h => (by cases h)) (Or.inl rfl)
                | unreachable => dsimp; exact hCallCase .unreachable (fun h => (by cases h)) (Or.inl rfl)
                | terminate => dsimp; exact hCallCase .terminate (fun h => (by cases h)) (Or.inl rfl)

private theorem panicAbort_initStateUnw_eq {pSrc pTgt : Program} {entryBody : Body}
    (hEntEq : pTgt.entryDefId = pSrc.entryDefId)
    (hPwEq : pTgt.pointerWidthBits = pSrc.pointerWidthBits)
    (hVerEq : pTgt.mirProfileVersion = pSrc.mirProfileVersion)
    (hGetEnt : Trusted.MirSemantics.getElem? pSrc.bodies pSrc.entryDefId = some entryBody)
    (hSet : setElem? pSrc.bodies pSrc.entryDefId
      { entryBody with basicBlocks := entryBody.basicBlocks.map rewriteBbPanicAbort } =
      some pTgt.bodies)
    (q : Query) :
    initStateUnw pTgt q = initStateUnw pSrc q := by
  unfold initStateUnw
  have hBase : initState pTgt q = initState pSrc q := by
    unfold initState
    rw [hPwEq, hVerEq, hEntEq, hGetEnt, panicAbort_entry_body_eq hSet]
    dsimp
    have hEmp : (entryBody.basicBlocks.map rewriteBbPanicAbort).isEmpty =
        entryBody.basicBlocks.isEmpty := by
      cases entryBody.basicBlocks <;> rfl
    rw [hEmp, map_rewriteBbPanicAbort_storageInBounds,
        map_rewriteBbPanicAbort_initLocalsLoop]
  rw [hBase]

private theorem initStateUnw_entryDefId {p : Program} {q : Query} {u₀ : UnwindState}
    (h : initStateUnw p q = .ok u₀) :
    u₀.callStack = [] ∧ u₀.active.defId = p.entryDefId := by
  let ⟨hCs, hBase⟩ := (initStateUnw_ok_iff p q u₀).mp h
  refine ⟨hCs, ?_⟩
  unfold initState at hBase
  cases h1 : (!Nat.beq p.pointerWidthBits 64 || !Nat.beq p.mirProfileVersion 1) <;>
    rw [h1] at hBase
  · dsimp at hBase
    cases h2 : (!q.callerMem.allocations.isEmpty) <;> rw [h2] at hBase
    · dsimp at hBase
      cases h3 : Trusted.MirSemantics.getElem? p.bodies p.entryDefId with
      | none => rw [h3] at hBase; cases hBase
      | some body =>
        rw [h3] at hBase; dsimp at hBase
        cases h4 : body.basicBlocks.isEmpty <;> rw [h4] at hBase
        · dsimp at hBase
          cases h5 : (!Nat.blt body.argumentCount body.locals.length) <;> rw [h5] at hBase
          · dsimp at hBase
            cases h6 : (!storageAnnotationsInBounds body) <;> rw [h6] at hBase
            · dsimp at hBase
              cases h7 : (!body.locals.all isSupportedScalarOrUnitTy) <;> rw [h7] at hBase
              · dsimp at hBase
                cases h8 : (!checkArgsMatch q.args ((body.locals.drop 1).take body.argumentCount)) <;>
                  rw [h8] at hBase
                · dsimp at hBase
                  injection hBase with hEq1
                  injection hEq1 with hEq2
                  injection hEq2 with hEq3
                  rw [← hEq3]
                · cases hBase
              · cases hBase
            · cases hBase
          · cases hBase
        · cases hBase
    · cases hBase
  · cases hBase

private theorem panicAbortEntryTransform_refines_unwound_to_aborted_slice1
    (pSrc pTgt : Program)
    (hAbort : checkPanicAbortEntryTransform pSrc pTgt = true) :
    (∀ q : Query, WellFormedUnw pSrc q ↔ WellFormedUnw pTgt q) ∧
    (∀ q : Query, ∀ out : Out,
      BehaviorUnw pSrc q (.returned out) ↔ BehaviorUnw pTgt q (.returned out)) ∧
    (∀ q : Query, ∀ mem : CallerMemory,
      (BehaviorUnw pSrc q (.unwound mem) ∨ BehaviorUnw pSrc q (.aborted mem)) ↔
        BehaviorUnw pTgt q (.aborted mem)) ∧
    (∀ q : Query, ∀ mem : CallerMemory, ¬ BehaviorUnw pTgt q (.unwound mem)) ∧
    (∀ q : Query, ∀ k : FaultKind,
      ReachesResultUnw pSrc q (.fault k) ↔ ReachesResultUnw pTgt q (.fault k)) ∧
    (∀ q : Query, DivergesUnw pSrc q ↔ DivergesUnw pTgt q) := by
  unfold checkPanicAbortEntryTransform applyPanicAbortEntryTransform at hAbort
  cases hNoRec : pSrc.bodies.any (bodyCallsDefId pSrc.entryDefId) with
  | true => rw [hNoRec] at hAbort; cases hAbort
  | false =>
    rw [hNoRec] at hAbort; dsimp at hAbort
    cases hGetEnt : Trusted.MirSemantics.getElem? pSrc.bodies pSrc.entryDefId with
    | none => rw [hGetEnt] at hAbort; cases hAbort
    | some entryBody =>
      rw [hGetEnt] at hAbort; dsimp at hAbort
      cases hSet : setElem? pSrc.bodies pSrc.entryDefId
          { entryBody with basicBlocks := entryBody.basicBlocks.map rewriteBbPanicAbort } with
      | none => rw [hSet] at hAbort; cases hAbort
      | some bodies' =>
        rw [hSet] at hAbort; dsimp at hAbort
        have hPOut : ({ pSrc with bodies := bodies' } : Program) = pTgt :=
          programEq_eq hAbort
        subst hPOut
        have hInitEq : ∀ q, initStateUnw { pSrc with bodies := bodies' } q = initStateUnw pSrc q :=
          panicAbort_initStateUnw_eq rfl rfl rfl hGetEnt hSet
        have hStepRel : ∀ s₁ s₂, PanicAbortStateRel pSrc.entryDefId s₁ s₂ →
            PanicAbortResRel pSrc.entryDefId
              (evalStepUnw pSrc 0 s₁) (evalStepUnw { pSrc with bodies := bodies' } 0 s₂) :=
          fun _ _ hR => panicAbort_step_rel hNoRec hGetEnt hSet hR
        have hFwdReaches : ∀ {s₁ t₁ s₂ : UnwindState},
            ReachesUnw pSrc s₁ t₁ → PanicAbortStateRel pSrc.entryDefId s₁ s₂ →
            ∃ t₂, ReachesUnw { pSrc with bodies := bodies' } s₂ t₂ ∧
              PanicAbortStateRel pSrc.entryDefId t₁ t₂ := by
          intro s₁ t₁ s₂ hR hRel0
          induction hR with
          | refl => exact ⟨s₂, ReachesUnw.refl s₂, hRel0⟩
          | @tail m₁ n₁ _ hSt ih =>
            let ⟨m₂, hRm2, hRelM⟩ := ih
            let ⟨c, hc, hEv1⟩ := hSt
            cases hc
            have hSR := hStepRel m₁ m₂ hRelM
            rw [hEv1] at hSR
            cases hEv2 : evalStepUnw { pSrc with bodies := bodies' } 0 m₂ with
            | step n₂ =>
              rw [hEv2] at hSR
              exact ⟨n₂, ReachesUnw.tail hRm2 ⟨0, rfl, hEv2⟩, hSR⟩
            | done _ => rw [hEv2] at hSR; exact False.elim hSR
            | fault _ => rw [hEv2] at hSR; exact False.elim hSR
        have hBwdReaches : ∀ {s₁ s₂ t₂ : UnwindState},
            ReachesUnw { pSrc with bodies := bodies' } s₂ t₂ →
            PanicAbortStateRel pSrc.entryDefId s₁ s₂ →
            ∃ t₁, ReachesUnw pSrc s₁ t₁ ∧
              PanicAbortStateRel pSrc.entryDefId t₁ t₂ := by
          intro s₁ s₂ t₂ hR hRel0
          induction hR with
          | refl => exact ⟨s₁, ReachesUnw.refl s₁, hRel0⟩
          | @tail m₂ n₂ _ hSt ih =>
            let ⟨m₁, hRm1, hRelM⟩ := ih
            let ⟨c, hc, hEv2⟩ := hSt
            cases hc
            have hSR := hStepRel m₁ m₂ hRelM
            rw [hEv2] at hSR
            cases hEv1 : evalStepUnw pSrc 0 m₁ with
            | step n₁ =>
              rw [hEv1] at hSR
              exact ⟨n₁, ReachesUnw.tail hRm1 ⟨0, rfl, hEv1⟩, hSR⟩
            | done o => cases o <;> (rw [hEv1] at hSR; exact False.elim hSR)
            | fault _ => rw [hEv1] at hSR; exact False.elim hSR
        have hInitRel : ∀ q s₀, initStateUnw pSrc q = .ok s₀ →
            PanicAbortStateRel pSrc.entryDefId s₀ s₀ := by
          intro q s₀ hI
          let ⟨hCs, hDef⟩ := initStateUnw_entryDefId hI
          refine ⟨rfl, rfl, ?_, fun _ => hDef, fun hNe => False.elim (hNe hCs)⟩
          rw [hCs]; exact PanicAbortStackRel.nil
        have hFault : ∀ q k,
            ReachesResultUnw pSrc q (.fault k) ↔
              ReachesResultUnw { pSrc with bodies := bodies' } q (.fault k) := by
          intro q k
          unfold ReachesResultUnw
          rw [hInitEq q]
          cases hI : initStateUnw pSrc q with
          | error k₀ => exact Iff.rfl
          | ok s₀ =>
            have hRel0 := hInitRel q s₀ hI
            constructor
            · intro ⟨t₁, hR1, ⟨c, hc, hEv1⟩⟩
              cases hc
              let ⟨t₂, hR2, hRelT⟩ := hFwdReaches hR1 hRel0
              have hSR := hStepRel t₁ t₂ hRelT
              rw [hEv1] at hSR
              cases hEv2 : evalStepUnw { pSrc with bodies := bodies' } 0 t₂ with
              | fault k₂ =>
                rw [hEv2] at hSR; dsimp [PanicAbortResRel] at hSR; subst hSR
                exact ⟨t₂, hR2, ⟨0, rfl, hEv2⟩⟩
              | step _ => rw [hEv2] at hSR; exact False.elim hSR
              | done _ => rw [hEv2] at hSR; exact False.elim hSR
            · intro ⟨t₂, hR2, ⟨c, hc, hEv2⟩⟩
              cases hc
              let ⟨t₁, hR1, hRelT⟩ := hBwdReaches hR2 hRel0
              have hSR := hStepRel t₁ t₂ hRelT
              rw [hEv2] at hSR
              cases hEv1 : evalStepUnw pSrc 0 t₁ with
              | fault k₁ =>
                rw [hEv1] at hSR; dsimp [PanicAbortResRel] at hSR; subst hSR
                exact ⟨t₁, hR1, ⟨0, rfl, hEv1⟩⟩
              | step _ => rw [hEv1] at hSR; exact False.elim hSR
              | done o => cases o <;> (rw [hEv1] at hSR; exact False.elim hSR)
        have hRet : ∀ q out,
            BehaviorUnw pSrc q (.returned out) ↔
              BehaviorUnw { pSrc with bodies := bodies' } q (.returned out) := by
          intro q out
          unfold BehaviorUnw ReachesResultUnw
          rw [hInitEq q]
          cases hI : initStateUnw pSrc q with
          | error k₀ => exact Iff.rfl
          | ok s₀ =>
            have hRel0 := hInitRel q s₀ hI
            constructor
            · intro ⟨t₁, hR1, ⟨c, hc, hEv1⟩⟩
              cases hc
              let ⟨t₂, hR2, hRelT⟩ := hFwdReaches hR1 hRel0
              have hSR := hStepRel t₁ t₂ hRelT
              rw [hEv1] at hSR
              cases hEv2 : evalStepUnw { pSrc with bodies := bodies' } 0 t₂ with
              | done o₂ =>
                rw [hEv2] at hSR
                cases o₂ with
                | returned out₂ =>
                  dsimp [PanicAbortResRel] at hSR; subst hSR
                  exact ⟨t₂, hR2, ⟨0, rfl, hEv2⟩⟩
                | unwound _ => exact False.elim hSR
                | aborted _ => exact False.elim hSR
              | step _ => rw [hEv2] at hSR; exact False.elim hSR
              | fault _ => rw [hEv2] at hSR; exact False.elim hSR
            · intro ⟨t₂, hR2, ⟨c, hc, hEv2⟩⟩
              cases hc
              let ⟨t₁, hR1, hRelT⟩ := hBwdReaches hR2 hRel0
              have hSR := hStepRel t₁ t₂ hRelT
              rw [hEv2] at hSR
              cases hEv1 : evalStepUnw pSrc 0 t₁ with
              | done o₁ =>
                rw [hEv1] at hSR
                cases o₁ with
                | returned out₁ =>
                  dsimp [PanicAbortResRel] at hSR; subst hSR
                  exact ⟨t₁, hR1, ⟨0, rfl, hEv1⟩⟩
                | unwound _ => exact False.elim hSR
                | aborted _ => exact False.elim hSR
              | step _ => rw [hEv1] at hSR; exact False.elim hSR
              | fault _ => rw [hEv1] at hSR; exact False.elim hSR
        have hAbortBeh : ∀ q mem,
            (BehaviorUnw pSrc q (.unwound mem) ∨ BehaviorUnw pSrc q (.aborted mem)) ↔
              BehaviorUnw { pSrc with bodies := bodies' } q (.aborted mem) := by
          intro q mem
          unfold BehaviorUnw ReachesResultUnw
          rw [hInitEq q]
          cases hI : initStateUnw pSrc q with
          | error k₀ =>
            constructor
            · intro h; cases h with
              | inl h1 => cases h1
              | inr h2 => cases h2
            · intro h; cases h
          | ok s₀ =>
            have hRel0 := hInitRel q s₀ hI
            constructor
            · intro hOr
              cases hOr with
              | inl hU =>
                let ⟨t₁, hR1, ⟨c, hc, hEv1⟩⟩ := hU
                cases hc
                let ⟨t₂, hR2, hRelT⟩ := hFwdReaches hR1 hRel0
                have hSR := hStepRel t₁ t₂ hRelT
                rw [hEv1] at hSR
                cases hEv2 : evalStepUnw { pSrc with bodies := bodies' } 0 t₂ with
                | done o₂ =>
                  rw [hEv2] at hSR
                  cases o₂ with
                  | aborted m₂ =>
                    dsimp [PanicAbortResRel] at hSR; subst hSR
                    exact ⟨t₂, hR2, ⟨0, rfl, hEv2⟩⟩
                  | returned _ => exact False.elim hSR
                  | unwound _ => exact False.elim hSR
                | step _ => rw [hEv2] at hSR; exact False.elim hSR
                | fault _ => rw [hEv2] at hSR; exact False.elim hSR
              | inr hA =>
                let ⟨t₁, hR1, ⟨c, hc, hEv1⟩⟩ := hA
                cases hc
                let ⟨t₂, hR2, hRelT⟩ := hFwdReaches hR1 hRel0
                have hSR := hStepRel t₁ t₂ hRelT
                rw [hEv1] at hSR
                cases hEv2 : evalStepUnw { pSrc with bodies := bodies' } 0 t₂ with
                | done o₂ =>
                  rw [hEv2] at hSR
                  cases o₂ with
                  | aborted m₂ =>
                    dsimp [PanicAbortResRel] at hSR; subst hSR
                    exact ⟨t₂, hR2, ⟨0, rfl, hEv2⟩⟩
                  | returned _ => exact False.elim hSR
                  | unwound _ => exact False.elim hSR
                | step _ => rw [hEv2] at hSR; exact False.elim hSR
                | fault _ => rw [hEv2] at hSR; exact False.elim hSR
            · intro ⟨t₂, hR2, ⟨c, hc, hEv2⟩⟩
              cases hc
              let ⟨t₁, hR1, hRelT⟩ := hBwdReaches hR2 hRel0
              have hSR := hStepRel t₁ t₂ hRelT
              rw [hEv2] at hSR
              cases hEv1 : evalStepUnw pSrc 0 t₁ with
              | done o₁ =>
                rw [hEv1] at hSR
                cases o₁ with
                | unwound m₁ =>
                  dsimp [PanicAbortResRel] at hSR; subst hSR
                  exact Or.inl ⟨t₁, hR1, ⟨0, rfl, hEv1⟩⟩
                | aborted m₁ =>
                  dsimp [PanicAbortResRel] at hSR; subst hSR
                  exact Or.inr ⟨t₁, hR1, ⟨0, rfl, hEv1⟩⟩
                | returned _ => exact False.elim hSR
              | step _ => rw [hEv1] at hSR; exact False.elim hSR
              | fault _ => rw [hEv1] at hSR; exact False.elim hSR
        have hNoUnw : ∀ q mem,
            ¬ BehaviorUnw { pSrc with bodies := bodies' } q (.unwound mem) := by
          intro q mem hB
          unfold BehaviorUnw ReachesResultUnw at hB
          rw [hInitEq q] at hB
          cases hI : initStateUnw pSrc q with
          | error k₀ => rw [hI] at hB; cases hB
          | ok s₀ =>
            rw [hI] at hB
            have hRel0 := hInitRel q s₀ hI
            let ⟨t₂, hR2, ⟨c, hc, hEv2⟩⟩ := hB
            cases hc
            let ⟨t₁, _, hRelT⟩ := hBwdReaches hR2 hRel0
            have hSR := hStepRel t₁ t₂ hRelT
            rw [hEv2] at hSR
            cases hEv1 : evalStepUnw pSrc 0 t₁ with
            | step _ => rw [hEv1] at hSR; exact False.elim hSR
            | fault _ => rw [hEv1] at hSR; exact False.elim hSR
            | done o₁ => cases o₁ <;> (rw [hEv1] at hSR; exact False.elim hSR)
        have hWf : ∀ q,
            WellFormedUnw pSrc q ↔ WellFormedUnw { pSrc with bodies := bodies' } q := by
          intro q
          rw [wellFormedUnw_iff_no_fault, wellFormedUnw_iff_no_fault]
          exact ⟨fun h k hf => h k ((hFault q k).mpr hf),
                 fun h k hf => h k ((hFault q k).mp hf)⟩
        have hDiv : ∀ q,
            DivergesUnw pSrc q ↔ DivergesUnw { pSrc with bodies := bodies' } q := by
          intro q
          rw [divergesUnw_iff_no_terminal_or_fault, divergesUnw_iff_no_terminal_or_fault]
          rw [hInitEq q]
          constructor
          · intro ⟨hIn, hNoF1, hNoB1⟩
            refine ⟨hIn, fun k hf => hNoF1 k ((hFault q k).mpr hf), fun out hb => ?_⟩
            cases out with
            | returned o => exact hNoB1 (.returned o) ((hRet q o).mpr hb)
            | unwound m => exact hNoUnw q m hb
            | aborted m =>
              cases (hAbortBeh q m).mpr hb with
              | inl hu => exact hNoB1 (.unwound m) hu
              | inr ha => exact hNoB1 (.aborted m) ha
          · intro ⟨hIn, hNoF2, hNoB2⟩
            refine ⟨hIn, fun k hf => hNoF2 k ((hFault q k).mp hf), fun out hb => ?_⟩
            cases out with
            | returned o => exact hNoB2 (.returned o) ((hRet q o).mp hb)
            | unwound m => exact hNoB2 (.aborted m) ((hAbortBeh q m).mp (Or.inl hb))
            | aborted m => exact hNoB2 (.aborted m) ((hAbortBeh q m).mp (Or.inr hb))
        exact ⟨hWf, hRet, hAbortBeh, hNoUnw, hFault, hDiv⟩

/-! ### Slice: Slice2_Abort_Assert_And_Prune.lean -/

-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.




/-! ### Shared Metadata & `assertConstSatisfied` Helpers -/

private theorem map_identity_setElem? {bs bs' : List Body} {i : Nat} {b b' : Body}
    (hGet : Trusted.MirSemantics.getElem? bs i = some b)
    (hSet : setElem? bs i b' = some bs')
    (hId : b'.identity = b.identity) :
    bs'.map (fun x => x.identity) = bs.map (fun x => x.identity) := by
  induction bs generalizing bs' i with
  | nil => cases hSet
  | cons x xs ih =>
    cases i with
    | zero =>
      dsimp [Trusted.MirSemantics.getElem?] at hGet
      injection hGet with hx; subst hx
      dsimp [setElem?] at hSet
      injection hSet with hbs; subst hbs
      dsimp [List.map]
      rw [hId]
    | succ k =>
      dsimp [Trusted.MirSemantics.getElem?] at hGet
      dsimp [setElem?] at hSet
      cases hs : setElem? xs k b' with
      | none => rw [hs] at hSet; cases hSet
      | some rest =>
        rw [hs] at hSet
        injection hSet with hbs; subst hbs
        dsimp [List.map]
        rw [ih hGet hs]

private theorem bodiesHaveUniqueIdentities_of_map_eq {bs₁ bs₂ : List Body}
    (hMap : bs₁.map (fun b => b.identity) = bs₂.map (fun b => b.identity)) :
    bodiesHaveUniqueIdentities bs₁ = bodiesHaveUniqueIdentities bs₂ := by
  unfold bodiesHaveUniqueIdentities
  have hAll : bs₁.all (fun b => !stringBeq b.identity "") =
      bs₂.all (fun b => !stringBeq b.identity "") := by
    have h1 := (list_all_map (fun b : Body => b.identity) (fun s => !stringBeq s "") bs₁).symm
    have h2 := (list_all_map (fun b : Body => b.identity) (fun s => !stringBeq s "") bs₂).symm
    rw [h1, h2, hMap]
  rw [hAll, hMap]

private theorem list_length_map {α β : Type} (f : α → β) :
    ∀ (xs : List α), (xs.map f).length = xs.length
  | [] => rfl
  | _ :: xs => congrArg Nat.succ (list_length_map f xs)

private theorem evalConstLit_bool_ty {ty : MirTy} {lit : ConstLit} {b : Bool}
    (h : evalConstLit ty lit = .ok (.bool b)) : ty = .bool := by
  cases ty with
  | bool => rfl
  | int w s =>
    cases lit with
    | scalar bits =>
      dsimp [evalConstLit] at h
      cases h1 : (truncateBits w bits != bits) <;> rw [h1] at h <;> cases h
    | zeroSized => cases h
  | unit =>
    cases lit <;> (dsimp [evalConstLit] at h; cases h)
  | enum e =>
    cases lit with
    | zeroSized =>
      dsimp [evalConstLit] at h
      cases h1 : isZstEnumTy e <;> rw [h1] at h <;> cases h
    | scalar bits =>
      dsimp [evalConstLit] at h
      cases htr : e.tagRepr with
      | zeroSized => rw [htr] at h; cases h
      | scalar tagW tagS =>
        rw [htr] at h; dsimp at h
        cases h1 : (!enumAdmitted e || truncateBits tagW bits != bits) <;> rw [h1] at h
        · dsimp at h
          cases h2 : findDiscrVariant? (tagBitsToDiscrBits tagW tagS e.discrWidth bits) e.discriminants <;>
            rw [h2] at h <;> cases h
        · cases h
  | never | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
    cases lit <;> (dsimp [evalConstLit] at h; cases h)

private theorem assertConstSatisfied_eval {bodyLocals : List MirTy}
    {locals : List LocalSlot} {cond : Operand} {expected : Bool}
    (hSat : assertConstSatisfied cond expected = true) :
    ∃ b : Bool,
      evalPrimitiveOperand bodyLocals locals cond = .ok (.bool b, locals) ∧
      boolEq b expected = true := by
  unfold assertConstSatisfied at hSat
  cases cond with
  | copy _ => cases hSat
  | move _ => cases hSat
  | constant c =>
    dsimp at hSat
    cases hEv : evalConstLit c.ty c.lit with
    | error _ => rw [hEv] at hSat; cases hSat
    | ok v =>
      rw [hEv] at hSat
      cases v with
      | bool b =>
        dsimp at hSat
        have hTy : c.ty = .bool := evalConstLit_bool_ty hEv
        refine ⟨b, ?_, hSat⟩
        dsimp [evalPrimitiveOperand, evalOperandToSlot]
        rw [hEv]
        dsimp
        rw [hTy]
        rfl
      | scalar _ | unit | ptr _ | enumVal _ _ | tuple _ | bytes _ => cases hSat

private theorem setElem?_isEmpty {α : Type} {xs xs' : List α} {i : Nat} {v : α}
    (hSet : setElem? xs i v = some xs') :
    xs'.isEmpty = xs.isEmpty := by
  cases xs with
  | nil => cases hSet
  | cons x rest =>
    cases i with
    | zero =>
      dsimp [setElem?] at hSet
      injection hSet with hEq; subst hEq; rfl
    | succ k =>
      dsimp [setElem?] at hSet
      cases hs : setElem? rest k v with
      | none => rw [hs] at hSet; cases hSet
      | some r =>
        rw [hs] at hSet
        injection hSet with hEq; subst hEq; rfl

private theorem setElem?_bb_same_stmts_hasStorage {bbs bbs' : List BasicBlock}
    {i : Nat} {bb bb' : BasicBlock}
    (hGet : Trusted.MirSemantics.getElem? bbs i = some bb)
    (hSet : setElem? bbs i bb' = some bbs')
    (hStmts : bb'.statements = bb.statements) (lid : LocalId) :
    bbs'.any (fun b => b.statements.any (stmtHasStorageMarker lid)) =
      bbs.any (fun b => b.statements.any (stmtHasStorageMarker lid)) := by
  induction bbs generalizing bbs' i with
  | nil => cases hSet
  | cons x xs ih =>
    cases i with
    | zero =>
      dsimp [Trusted.MirSemantics.getElem?] at hGet
      injection hGet with hx; subst hx
      dsimp [setElem?] at hSet
      injection hSet with hb; subst hb
      dsimp [List.any]
      rw [hStmts]
    | succ k =>
      dsimp [Trusted.MirSemantics.getElem?] at hGet
      dsimp [setElem?] at hSet
      cases hs : setElem? xs k bb' with
      | none => rw [hs] at hSet; cases hSet
      | some rest =>
        rw [hs] at hSet
        injection hSet with hb; subst hb
        dsimp [List.any]
        rw [ih hGet hs]

private theorem setElem?_bb_same_stmts_storageInBounds {bbs bbs' : List BasicBlock}
    {i : Nat} {bb bb' : BasicBlock} {nLocs : Nat}
    (hGet : Trusted.MirSemantics.getElem? bbs i = some bb)
    (hSet : setElem? bbs i bb' = some bbs')
    (hStmts : bb'.statements = bb.statements) :
    bbs'.all (fun b => b.statements.all (fun stmt =>
      match stmt with
      | .storageLive id | .storageDead id => Nat.blt id nLocs
      | _ => true)) =
    bbs.all (fun b => b.statements.all (fun stmt =>
      match stmt with
      | .storageLive id | .storageDead id => Nat.blt id nLocs
      | _ => true)) := by
  induction bbs generalizing bbs' i with
  | nil => cases hSet
  | cons x xs ih =>
    cases i with
    | zero =>
      dsimp [Trusted.MirSemantics.getElem?] at hGet
      injection hGet with hx; subst hx
      dsimp [setElem?] at hSet
      injection hSet with hb; subst hb
      dsimp [List.all]
      rw [hStmts]
    | succ k =>
      dsimp [Trusted.MirSemantics.getElem?] at hGet
      dsimp [setElem?] at hSet
      cases hs : setElem? xs k bb' with
      | none => rw [hs] at hSet; cases hSet
      | some rest =>
        rw [hs] at hSet
        injection hSet with hb; subst hb
        dsimp [List.all]
        rw [ih hGet hs]

private theorem initLocalsLoop_congr_hasStorage {b₁ b₂ : Body} (args : List Val)
    (hArgEq : b₁.argumentCount = b₂.argumentCount)
    (hHas : ∀ loc, loc < b₁.locals.length →
      hasStorageAnnotation b₁ loc = hasStorageAnnotation b₂ loc) :
    ∀ (idx : Nat) (rem : List MirTy),
      idx + rem.length ≤ b₁.locals.length →
      initLocalsLoop b₁ args idx rem = initLocalsLoop b₂ args idx rem
  | _, [], _ => rfl
  | idx, ty :: rest, hLe => by
    dsimp [initLocalsLoop]
    have hLt : idx < b₁.locals.length := by
      dsimp [List.length] at hLe
      exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (Nat.zero_lt_succ rest.length)) hLe
    rw [hArgEq, hHas idx hLt]
    have hLe2 : (idx + 1) + rest.length ≤ b₁.locals.length := by
      dsimp [List.length] at hLe
      rw [Nat.add_right_comm, Nat.add_assoc]
      exact hLe
    rw [initLocalsLoop_congr_hasStorage args hArgEq hHas (idx + 1) rest hLe2]

private theorem initState_congr_body {p₁ p₂ : Program} {b₁ b₂ : Body}
    (hPw : p₁.pointerWidthBits = p₂.pointerWidthBits)
    (hVer : p₁.mirProfileVersion = p₂.mirProfileVersion)
    (hGet1 : Trusted.MirSemantics.getElem? p₁.bodies p₁.entryDefId = some b₁)
    (hGet2 : Trusted.MirSemantics.getElem? p₂.bodies p₂.entryDefId = some b₂)
    (hEnt : p₁.entryDefId = p₂.entryDefId)
    (hEmp : b₁.basicBlocks.isEmpty = b₂.basicBlocks.isEmpty)
    (hArgCnt : b₁.argumentCount = b₂.argumentCount)
    (hLocs : b₁.locals = b₂.locals)
    (hStorB : storageAnnotationsInBounds b₁ = storageAnnotationsInBounds b₂)
    (hHas : ∀ loc, loc < b₁.locals.length →
      hasStorageAnnotation b₁ loc = hasStorageAnnotation b₂ loc)
    (q : Query) :
    initState p₁ q = initState p₂ q := by
  unfold initState
  rw [hPw, hVer, hGet1, hGet2]
  dsimp
  rw [hEnt, hEmp, hArgCnt, hLocs, hStorB]
  have hLoop : initLocalsLoop b₁ q.args 0 b₂.locals = initLocalsLoop b₂ q.args 0 b₂.locals := by
    rw [← hLocs]
    exact @initLocalsLoop_congr_hasStorage b₁ b₂ q.args hArgCnt hHas 0 b₁.locals
      (by rw [Nat.zero_add]; exact Nat.le_refl _)
  rw [hLoop]

/-! ### Part 1: `.dischargeTrivialAssert` Soundness (`dischargeTrivialAssert_sound_slice2`) -/

private theorem dischargeTrivialAssert_evalStep_eq {p : Program}
    {defId : DefId} {bbIdx : BasicBlockId}
    {body : Body} {bb : BasicBlock} {cond : Operand} {expected : Bool}
    {msg : AssertKind} {target : BasicBlockId} {unwind : UnwindAction}
    {bbs' : List BasicBlock} {bodies' : List Body}
    (hGetB : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (hGetBb : Trusted.MirSemantics.getElem? body.basicBlocks bbIdx = some bb)
    (hTerm : bb.terminator = .assert cond expected msg target unwind)
    (hSat : assertConstSatisfied cond expected = true)
    (hSetBb : setElem? body.basicBlocks bbIdx { bb with terminator := .goto target } = some bbs')
    (hSetB : setElem? p.bodies defId { body with basicBlocks := bbs' } = some bodies')
    (ent : DefId) (s : UnwindState) :
    evalStepUnw { p with bodies := bodies', entryDefId := ent } 0 s =
      evalStepUnw { p with entryDefId := ent } 0 s := by
  let p1 : Program := { p with entryDefId := ent }
  let p2 : Program := { p with bodies := bodies', entryDefId := ent }
  have hEnterEq : ∀ frame rest mem padBb,
      enterCleanupBlockUnw p2 frame rest mem padBb =
        enterCleanupBlockUnw p1 frame rest mem padBb := by
    intro frame rest mem padBb
    unfold enterCleanupBlockUnw
    dsimp [p1, p2]
    cases hEqD : Nat.beq frame.defId defId with
    | false =>
      rw [setElem?_getElem?_ne hSetB (nat_ne_of_beq_false hEqD)]
    | true =>
      have hD := nat_beq_eq hEqD
      rw [hD, hGetB, setElem?_getElem?_same hSetB]
      dsimp
      cases hEqBb : Nat.beq padBb bbIdx with
      | false =>
        rw [setElem?_getElem?_ne hSetBb (nat_ne_of_beq_false hEqBb)]
      | true =>
        have hB := nat_beq_eq hEqBb
        rw [hB, hGetBb, setElem?_getElem?_same hSetBb]
  have hDispStack : ∀ mem cs,
      dispatchUnwindStack p2 mem cs = dispatchUnwindStack p1 mem cs := by
    intro mem cs
    induction cs with
    | nil => rfl
    | cons c rest ih =>
      dsimp [dispatchUnwindStack]
      cases c.unwind with
      | cleanup padBb => exact hEnterEq c.callerFrame rest mem padBb
      | continue_ => exact ih
      | unreachable => rfl
      | terminate => rfl
  have hRetEq : ∀ retVal cont rest mem,
      returnToCallerUnw p2 retVal cont rest mem =
        returnToCallerUnw p1 retVal cont rest mem := by
    intro retVal cont rest mem
    unfold returnToCallerUnw
    dsimp [p1, p2]
    cases hEqD : Nat.beq cont.callerFrame.defId defId with
    | false =>
      rw [setElem?_getElem?_ne hSetB (nat_ne_of_beq_false hEqD)]
    | true =>
      have hD := nat_beq_eq hEqD
      rw [hD, hGetB, setElem?_getElem?_same hSetB]
  have hInitCalleeBody : ∀ av,
      initCalleeFrameUnw defId { body with basicBlocks := bbs' } av =
        initCalleeFrameUnw defId body av := by
    intro av
    unfold initCalleeFrameUnw
    dsimp
    have hEmp := setElem?_isEmpty hSetBb
    have hSb : storageAnnotationsInBounds { body with basicBlocks := bbs' } =
        storageAnnotationsInBounds body :=
      setElem?_bb_same_stmts_storageInBounds hGetBb hSetBb rfl
    have hHas : ∀ loc, loc < body.locals.length →
        hasStorageAnnotation { body with basicBlocks := bbs' } loc =
          hasStorageAnnotation body loc :=
      fun loc _ => setElem?_bb_same_stmts_hasStorage hGetBb hSetBb rfl loc
    have hLoop : initLocalsLoop { body with basicBlocks := bbs' } av 0 body.locals =
        initLocalsLoop body av 0 body.locals :=
      @initLocalsLoop_congr_hasStorage { body with basicBlocks := bbs' } body av rfl hHas
        0 body.locals (by rw [Nat.zero_add]; exact Nat.le_refl _)
    rw [hEmp, hSb, hLoop]
  have hTermShared : ∀ (b : Body) (blk : BasicBlock) (f : FrameState) (cs : List CallContUnw) (m : CallerMemory),
      evalTerminatorUnw p2 b blk f cs m = evalTerminatorUnw p1 b blk f cs m := by
    intro b blk f cs m
    unfold evalTerminatorUnw
    cases blk.terminator with
    | goto _ | unreachable | unsupported | switchInt _ _ => rfl
    | return_ =>
      cases blk.cleanup with
      | true => rfl
      | false =>
        dsimp
        cases Trusted.MirSemantics.getElem? f.locals 0 with
        | none => rfl
        | some sl =>
          cases sl with
          | dead => rfl
          | live ov =>
            cases ov with
            | none => rfl
            | some rv =>
              cases cs with
              | nil => rfl
              | cons c rest => exact hRetEq rv c rest m
    | unwindResume =>
      cases !blk.cleanup with
      | true => rfl
      | false => exact hDispStack m cs
    | assert c e _ t u =>
      dsimp
      cases evalPrimitiveOperand b.locals f.locals c with
      | error _ => rfl
      | ok pair =>
        cases pair with
        | mk v la =>
          cases v with
          | bool bv =>
            dsimp
            cases boolEq bv e with
            | true => rfl
            | false =>
              dsimp [dispatchLocalUnwind]
              cases u with
              | cleanup padBb => exact hEnterEq { f with locals := la } cs m padBb
              | continue_ => exact hDispStack m cs
              | unreachable => rfl
              | terminate => rfl
          | scalar _ | unit | ptr _ | enumVal _ _ | tuple _ | bytes _ => rfl
    | call cDef args dst tgt u =>
      dsimp
      cases evalCallArgsUnw b.locals f.locals args with
      | error _ => rfl
      | ok pair =>
        dsimp [p1, p2]
        cases hEqD : Nat.beq cDef defId with
        | false =>
          rw [setElem?_getElem?_ne hSetB (nat_ne_of_beq_false hEqD)]
        | true =>
          have hD := nat_beq_eq hEqD
          rw [hD, hGetB, setElem?_getElem?_same hSetB]
          dsimp
          rw [hInitCalleeBody pair.1]
  change evalStepUnw p2 0 s = evalStepUnw p1 0 s
  unfold evalStepUnw
  dsimp [p1, p2]
  cases hEqD : Nat.beq s.active.defId defId with
  | false =>
    rw [setElem?_getElem?_ne hSetB (nat_ne_of_beq_false hEqD)]
    cases Trusted.MirSemantics.getElem? p.bodies s.active.defId with
    | none => rfl
    | some b =>
      dsimp
      cases Trusted.MirSemantics.getElem? b.basicBlocks s.active.blockIdx with
      | none => rfl
      | some blk =>
        dsimp
        cases Trusted.MirSemantics.getElem? blk.statements s.active.stmtIdx with
        | some _ => rfl
        | none =>
          dsimp
          cases Nat.beq s.active.stmtIdx blk.statements.length with
          | false => rfl
          | true => exact hTermShared b blk s.active s.callStack s.callerMem
  | true =>
    have hD := nat_beq_eq hEqD
    rw [hD, hGetB, setElem?_getElem?_same hSetB]
    dsimp
    cases hEqBb : Nat.beq s.active.blockIdx bbIdx with
    | false =>
      rw [setElem?_getElem?_ne hSetBb (nat_ne_of_beq_false hEqBb)]
      cases Trusted.MirSemantics.getElem? body.basicBlocks s.active.blockIdx with
      | none => rfl
      | some blk =>
        dsimp
        cases Trusted.MirSemantics.getElem? blk.statements s.active.stmtIdx with
        | some stmt =>
          dsimp
          have hStEq : evalStatement { body with basicBlocks := bbs' } s.active s.callerMem stmt =
              evalStatement body s.active s.callerMem stmt := by cases stmt <;> rfl
          rw [hStEq]
        | none =>
          dsimp
          cases Nat.beq s.active.stmtIdx blk.statements.length with
          | false => rfl
          | true =>
            dsimp
            have hTm1 : evalTerminatorUnw p2 { body with basicBlocks := bbs' } blk s.active s.callStack s.callerMem =
                evalTerminatorUnw p2 body blk s.active s.callStack s.callerMem := by
              unfold evalTerminatorUnw
              cases blk.terminator <;> rfl
            rw [hTm1]
            exact hTermShared body blk s.active s.callStack s.callerMem
    | true =>
      have hB := nat_beq_eq hEqBb
      rw [hB, hGetBb, setElem?_getElem?_same hSetBb]
      dsimp
      cases Trusted.MirSemantics.getElem? bb.statements s.active.stmtIdx with
      | some stmt =>
        dsimp
        have hStEq : evalStatement { body with basicBlocks := bbs' } s.active s.callerMem stmt =
            evalStatement body s.active s.callerMem stmt := by cases stmt <;> rfl
        rw [hStEq]
      | none =>
        dsimp
        cases Nat.beq s.active.stmtIdx bb.statements.length with
        | false => rfl
        | true =>
          dsimp [evalTerminatorUnw]
          rw [hTerm]
          dsimp
          let ⟨bVal, hEvalC, hBoolEq⟩ :=
            assertConstSatisfied_eval (bodyLocals := body.locals) (locals := s.active.locals) hSat
          rw [hEvalC]
          dsimp
          rw [hBoolEq]
          rfl

private theorem dischargeTrivialAssert_sound_slice2 (pSrc pTgt : Program)
    (defId : DefId) (bbIdx : BasicBlockId)
    (hCheck : checkDischargeTrivialAssert pSrc defId bbIdx pTgt = true) :
    ProgramEquivUnw pSrc pTgt := by
  unfold checkDischargeTrivialAssert applyDischargeTrivialAssert at hCheck
  cases hGetB : Trusted.MirSemantics.getElem? pSrc.bodies defId with
  | none => rw [hGetB] at hCheck; cases hCheck
  | some body =>
    rw [hGetB] at hCheck; dsimp at hCheck
    cases hGetBb : Trusted.MirSemantics.getElem? body.basicBlocks bbIdx with
    | none => rw [hGetBb] at hCheck; cases hCheck
    | some bb =>
      rw [hGetBb] at hCheck; dsimp at hCheck
      cases hTerm : bb.terminator with
      | goto _ | switchInt _ _ | return_ | unreachable | unwindResume
      | call _ _ _ _ _ | unsupported => rw [hTerm] at hCheck; cases hCheck
      | assert cond expected msg target unwind =>
        rw [hTerm] at hCheck; dsimp at hCheck
        cases hSat : assertConstSatisfied cond expected with
        | false => rw [hSat] at hCheck; cases hCheck
        | true =>
          rw [hSat] at hCheck; dsimp at hCheck
          cases hSetBb : setElem? body.basicBlocks bbIdx { bb with terminator := .goto target } with
          | none => rw [hSetBb] at hCheck; cases hCheck
          | some bbs' =>
            rw [hSetBb] at hCheck; dsimp at hCheck
            cases hSetB : setElem? pSrc.bodies defId { body with basicBlocks := bbs' } with
            | none => rw [hSetB] at hCheck; cases hCheck
            | some bodies' =>
              rw [hSetB] at hCheck; dsimp at hCheck
              have hPOut : ({ pSrc with bodies := bodies' } : Program) = pTgt :=
                programEq_eq hCheck
              subst hPOut
              have hLen : pSrc.bodies.length = bodies'.length :=
                (setElem?_length hSetB).symm
              have hUniq : bodiesHaveUniqueIdentities pSrc.bodies =
                  bodiesHaveUniqueIdentities bodies' :=
                (bodiesHaveUniqueIdentities_of_map_eq
                  (map_identity_setElem? hGetB hSetB rfl)).symm
              have hEmp : bbs'.isEmpty = body.basicBlocks.isEmpty := setElem?_isEmpty hSetBb
              have hSb : storageAnnotationsInBounds { body with basicBlocks := bbs' } =
                  storageAnnotationsInBounds body :=
                setElem?_bb_same_stmts_storageInBounds hGetBb hSetBb rfl
              have hSemEntry : ∀ ent : DefId,
                  FullSemanticEquivUnw { pSrc with entryDefId := ent }
                    { pSrc with bodies := bodies', entryDefId := ent } := by
                intro ent
                have hInitEq : ∀ q, initStateUnw { pSrc with bodies := bodies', entryDefId := ent } q =
                    initStateUnw { pSrc with entryDefId := ent } q := by
                  intro q
                  unfold initStateUnw
                  cases hEqD : Nat.beq ent defId with
                  | false =>
                    have hBase : initState { pSrc with bodies := bodies', entryDefId := ent } q =
                        initState { pSrc with entryDefId := ent } q := by
                      unfold initState
                      dsimp
                      rw [setElem?_getElem?_ne hSetB (nat_ne_of_beq_false hEqD)]
                    rw [hBase]
                  | true =>
                    have hD := nat_beq_eq hEqD
                    have hBase : initState { pSrc with bodies := bodies', entryDefId := ent } q =
                        initState { pSrc with entryDefId := ent } q :=
                      @initState_congr_body { pSrc with bodies := bodies', entryDefId := ent }
                        { pSrc with entryDefId := ent }
                        { body with basicBlocks := bbs' } body
                        rfl rfl
                        (by rw [hD]; exact setElem?_getElem?_same hSetB)
                        (by rw [hD]; exact hGetB)
                        rfl hEmp rfl rfl hSb
                        (fun loc _ => setElem?_bb_same_stmts_hasStorage hGetBb hSetBb rfl loc) q
                    rw [hBase]
                exact fullSemanticEquivUnw_of_lockstep (fun s₁ s₂ => s₁ = s₂)
                  (fun q k => by rw [hInitEq q])
                  (fun q s₁ s₂ h1 h2 => by
                    rw [hInitEq q] at h2; rw [h1] at h2; injection h2)
                  (fun s₁ s₂ s₁' hEq hSt => by
                    subst hEq
                    exact ⟨s₁', (dischargeTrivialAssert_evalStep_eq hGetB hGetBb hTerm hSat hSetBb hSetB ent s₁).trans hSt, rfl⟩)
                  (fun s₁ s₂ out hEq hD => by
                    subst hEq
                    exact (dischargeTrivialAssert_evalStep_eq hGetB hGetBb hTerm hSat hSetBb hSetB ent s₁).trans hD)
                  (fun s₁ s₂ k hEq hF => by
                    subst hEq
                    exact (dischargeTrivialAssert_evalStep_eq hGetB hGetBb hTerm hSat hSetBb hSetB ent s₁).trans hF)
              refine ⟨hLen, rfl, rfl, rfl, rfl, hUniq, hSemEntry pSrc.entryDefId, ?_⟩
              intro d
              cases hEqD : Nat.beq d defId with
              | false =>
                rw [setElem?_getElem?_ne hSetB (nat_ne_of_beq_false hEqD)]
                cases Trusted.MirSemantics.getElem? pSrc.bodies d with
                | none => exact True.intro
                | some b =>
                  exact ⟨rfl, rfl, rfl, fun _ => Iff.rfl, hSemEntry d⟩
              | true =>
                have hD := nat_beq_eq hEqD
                rw [hD, hGetB, setElem?_getElem?_same hSetB]
                refine ⟨rfl, rfl, ?_, fun _ => Iff.rfl, hSemEntry defId⟩
                unfold BodyStaticAdmitted
                dsimp
                rw [hEmp, hSb]

/-! ### Part 2: `.abortUnwindingCalls` Soundness (`abortUnwindingCalls_sound_slice2`) -/

private noncomputable def isFlagTrue (flags : List Bool) (d : DefId) : Bool :=
  match Trusted.MirSemantics.getElem? flags d with
  | some true => true
  | _ => false

private theorem checkNoUnwindSummaryLoop_sound (p : Program) (flags : List Bool) :
    ∀ (idx : Nat) (rem : List Bool) (k : Nat),
      checkNoUnwindSummaryLoop p flags idx rem = true →
      Trusted.MirSemantics.getElem? rem k = some true →
      ∃ body,
        Trusted.MirSemantics.getElem? p.bodies (idx + k) = some body ∧
        body.basicBlocks.all (fun bb => termCannotUnwind flags bb.terminator) = true
  | _, [], _, _, hGet => by cases hGet
  | idx, flag :: rest, 0, hLoop, hGet => by
    dsimp [Trusted.MirSemantics.getElem?] at hGet
    injection hGet with hf; subst hf
    dsimp [checkNoUnwindSummaryLoop] at hLoop
    let ⟨hCur, _⟩ := bool_and_true hLoop
    cases hBod : Trusted.MirSemantics.getElem? p.bodies idx with
    | none => rw [hBod] at hCur; cases hCur
    | some body =>
      rw [hBod] at hCur
      exact ⟨body, rfl, hCur⟩
  | idx, flag :: rest, k + 1, hLoop, hGet => by
    dsimp [Trusted.MirSemantics.getElem?] at hGet
    dsimp [checkNoUnwindSummaryLoop] at hLoop
    let ⟨_, hRest⟩ := bool_and_true hLoop
    have hRes := checkNoUnwindSummaryLoop_sound p flags (idx + 1) rest k hRest hGet
    rw [Nat.add_right_comm] at hRes
    exact hRes

private theorem checkNoUnwindSummary_sound {p : Program} {flags : List Bool}
    (hSum : checkNoUnwindSummary p flags = true) {d : DefId}
    (hFlag : isFlagTrue flags d = true) :
    ∃ body,
      Trusted.MirSemantics.getElem? p.bodies d = some body ∧
      body.basicBlocks.all (fun bb => termCannotUnwind flags bb.terminator) = true := by
  unfold checkNoUnwindSummary at hSum
  let ⟨_, hLoop⟩ := bool_and_true hSum
  unfold isFlagTrue at hFlag
  cases hG : Trusted.MirSemantics.getElem? flags d with
  | none => rw [hG] at hFlag; cases hFlag
  | some b =>
    rw [hG] at hFlag
    cases b with
    | false => cases hFlag
    | true =>
      have hRes := checkNoUnwindSummaryLoop_sound p flags 0 flags d hLoop hG
      rw [Nat.zero_add] at hRes
      exact hRes

private noncomputable def rewriteBodyAbortUnw (flags : List Bool) (body : Body) : Body :=
  { body with basicBlocks := body.basicBlocks.map (rewriteTermAbortUnw flags) }

private theorem rewriteBodyAbortUnw_hasStorage (flags : List Bool) (body : Body) (lid : LocalId) :
    hasStorageAnnotation (rewriteBodyAbortUnw flags body) lid =
      hasStorageAnnotation body lid := by
  unfold hasStorageAnnotation rewriteBodyAbortUnw
  dsimp
  rw [list_any_map]
  rfl

private theorem rewriteBodyAbortUnw_storageInBounds (flags : List Bool) (body : Body) :
    storageAnnotationsInBounds (rewriteBodyAbortUnw flags body) =
      storageAnnotationsInBounds body := by
  unfold storageAnnotationsInBounds rewriteBodyAbortUnw
  dsimp
  rw [list_all_map]
  rfl

private theorem rewriteBodyAbortUnw_isEmpty (flags : List Bool) (body : Body) :
    (rewriteBodyAbortUnw flags body).basicBlocks.isEmpty = body.basicBlocks.isEmpty := by
  unfold rewriteBodyAbortUnw
  dsimp
  cases body.basicBlocks <;> rfl

private theorem rewriteBodyAbortUnw_initCallee (flags : List Bool) (d : DefId)
    (body : Body) (av : List Val) :
    initCalleeFrameUnw d (rewriteBodyAbortUnw flags body) av =
      initCalleeFrameUnw d body av := by
  unfold initCalleeFrameUnw
  rw [rewriteBodyAbortUnw_isEmpty, rewriteBodyAbortUnw_storageInBounds]
  have hLoop : initLocalsLoop (rewriteBodyAbortUnw flags body) av 0 (rewriteBodyAbortUnw flags body).locals =
      initLocalsLoop body av 0 body.locals :=
    @initLocalsLoop_congr_hasStorage (rewriteBodyAbortUnw flags body) body av rfl
      (fun loc _ => rewriteBodyAbortUnw_hasStorage flags body loc)
      0 body.locals (by rw [Nat.zero_add]; exact Nat.le_refl _)
  rw [hLoop]
  rfl

/-- Inductive interprocedural firewall stack relation for `AbortUnwindingCalls`. -/
private inductive AbortUnwStackRel (flags : List Bool) :
    Bool → List CallContUnw → List CallContUnw → Prop where
  | nil (activeNoUnw : Bool) : AbortUnwStackRel flags activeNoUnw [] []
  | consEq (activeNoUnw : Bool) (c : CallContUnw) (r₁ r₂ : List CallContUnw) :
      (isFlagTrue flags c.callerFrame.defId = true →
        c.unwind = .terminate ∨ c.unwind = .unreachable) →
      AbortUnwStackRel flags (isFlagTrue flags c.callerFrame.defId) r₁ r₂ →
      AbortUnwStackRel flags activeNoUnw (c :: r₁) (c :: r₂)
  | consTightened (c₁ c₂ : CallContUnw) (r₁ r₂ : List CallContUnw) :
      c₁.callerFrame = c₂.callerFrame →
      c₁.dst = c₂.dst →
      c₁.target = c₂.target →
      c₂.unwind = .unreachable →
      AbortUnwStackRel flags (isFlagTrue flags c₁.callerFrame.defId) r₁ r₂ →
      AbortUnwStackRel flags true (c₁ :: r₁) (c₂ :: r₂)

private noncomputable def AbortUnwStateRel (flags : List Bool)
    (s₁ s₂ : UnwindState) : Prop :=
  s₁.active = s₂.active ∧
  s₁.callerMem = s₂.callerMem ∧
  AbortUnwStackRel flags (isFlagTrue flags s₁.active.defId) s₁.callStack s₂.callStack

private theorem abortUnw_enterCleanup_eq (p : Program) (flags : List Bool)
    (ent : DefId) (frame : FrameState) (r₁ r₂ : List CallContUnw)
    (mem : CallerMemory) (padBb : BasicBlockId)
    (hStack : AbortUnwStackRel flags (isFlagTrue flags frame.defId) r₁ r₂) :
    match enterCleanupBlockUnw { p with entryDefId := ent } frame r₁ mem padBb,
          enterCleanupBlockUnw { p with bodies := p.bodies.map (rewriteBodyAbortUnw flags), entryDefId := ent } frame r₂ mem padBb with
    | .step s₁', .step s₂' => AbortUnwStateRel flags s₁' s₂'
    | .done o₁, .done o₂ => o₁ = o₂
    | .fault k₁, .fault k₂ => k₁ = k₂
    | _, _ => False := by
  unfold enterCleanupBlockUnw
  dsimp
  rw [getElem?_map]
  cases Trusted.MirSemantics.getElem? p.bodies frame.defId with
  | none => exact rfl
  | some body =>
    dsimp [rewriteBodyAbortUnw]
    rw [getElem?_map]
    cases Trusted.MirSemantics.getElem? body.basicBlocks padBb with
    | none => exact rfl
    | some bb =>
      dsimp [rewriteTermAbortUnw]
      cases !bb.cleanup with
      | true => exact rfl
      | false =>
        dsimp [AbortUnwStateRel]
        exact ⟨rfl, rfl, hStack⟩

private theorem abortUnw_dispatchUnwindStack_aux (p : Program) (flags : List Bool)
    (ent : DefId) (mem : CallerMemory) :
    ∀ {b : Bool} {cs₁ cs₂ : List CallContUnw},
      AbortUnwStackRel flags b cs₁ cs₂ →
      b = false →
      match dispatchUnwindStack { p with entryDefId := ent } mem cs₁,
            dispatchUnwindStack { p with bodies := p.bodies.map (rewriteBodyAbortUnw flags), entryDefId := ent } mem cs₂ with
      | .step s₁', .step s₂' => AbortUnwStateRel flags s₁' s₂'
      | .done o₁, .done o₂ => o₁ = o₂
      | .fault k₁, .fault k₂ => k₁ = k₂
      | _, _ => False := by
  intro b cs₁ cs₂ hRel hB
  induction hRel with
  | nil _ => exact rfl
  | consTightened _ _ _ _ _ _ _ _ _ => cases hB
  | consEq _ c r₁ r₂ hFire hSub ih =>
    dsimp [dispatchUnwindStack]
    cases hU : c.unwind with
    | terminate => exact rfl
    | unreachable => exact rfl
    | cleanup padBb =>
      exact abortUnw_enterCleanup_eq p flags ent c.callerFrame r₁ r₂ mem padBb hSub
    | continue_ =>
      have hCallerFalse : isFlagTrue flags c.callerFrame.defId = false := by
        cases hf : isFlagTrue flags c.callerFrame.defId with
        | false => rfl
        | true =>
          cases hFire hf with
          | inl ht => rw [hU] at ht; cases ht
          | inr hu => rw [hU] at hu; cases hu
      exact ih hCallerFalse

private theorem abortUnw_dispatchUnwindStack (p : Program) (flags : List Bool)
    (ent : DefId) (mem : CallerMemory) {cs₁ cs₂ : List CallContUnw}
    (hRel : AbortUnwStackRel flags false cs₁ cs₂) :
    match dispatchUnwindStack { p with entryDefId := ent } mem cs₁,
          dispatchUnwindStack { p with bodies := p.bodies.map (rewriteBodyAbortUnw flags), entryDefId := ent } mem cs₂ with
    | .step s₁', .step s₂' => AbortUnwStateRel flags s₁' s₂'
    | .done o₁, .done o₂ => o₁ = o₂
    | .fault k₁, .fault k₂ => k₁ = k₂
    | _, _ => False :=
  abortUnw_dispatchUnwindStack_aux p flags ent mem hRel rfl

private theorem abortUnw_returnToCaller (p : Program) (flags : List Bool)
    (ent : DefId) (retVal : Val) (mem : CallerMemory)
    {b : Bool} {c₁ c₂ : CallContUnw} {r₁ r₂ : List CallContUnw}
    (hRel : AbortUnwStackRel flags b (c₁ :: r₁) (c₂ :: r₂)) :
    match returnToCallerUnw { p with entryDefId := ent } retVal c₁ r₁ mem,
          returnToCallerUnw { p with bodies := p.bodies.map (rewriteBodyAbortUnw flags), entryDefId := ent } retVal c₂ r₂ mem with
    | .step s₁', .step s₂' => AbortUnwStateRel flags s₁' s₂'
    | .done o₁, .done o₂ => o₁ = o₂
    | .fault k₁, .fault k₂ => k₁ = k₂
    | _, _ => False := by
  have hCommon :
      c₁.callerFrame = c₂.callerFrame →
      c₁.dst = c₂.dst →
      c₁.target = c₂.target →
      AbortUnwStackRel flags (isFlagTrue flags c₁.callerFrame.defId) r₁ r₂ →
      match returnToCallerUnw { p with entryDefId := ent } retVal c₁ r₁ mem,
            returnToCallerUnw { p with bodies := p.bodies.map (rewriteBodyAbortUnw flags), entryDefId := ent } retVal c₂ r₂ mem with
      | .step s₁', .step s₂' => AbortUnwStateRel flags s₁' s₂'
      | .done o₁, .done o₂ => o₁ = o₂
      | .fault k₁, .fault k₂ => k₁ = k₂
      | _, _ => False := by
    intro hCf hDst hTgt hSub
    unfold returnToCallerUnw
    dsimp
    rw [← hCf, ← hDst, ← hTgt, getElem?_map]
    cases Trusted.MirSemantics.getElem? p.bodies c₁.callerFrame.defId with
    | none => exact rfl
    | some callerBody =>
      dsimp [rewriteBodyAbortUnw]
      cases !c₁.dst.projection.isEmpty with
      | true => exact rfl
      | false =>
        dsimp
        cases Trusted.MirSemantics.getElem? callerBody.locals c₁.dst.localId with
        | none => exact rfl
        | some dstTy =>
          dsimp
          cases writePlace c₁.callerFrame.locals c₁.dst.localId dstTy retVal with
          | error _ => exact rfl
          | ok locs' =>
            dsimp
            cases c₁.target with
            | none => exact rfl
            | some nextBb =>
              dsimp [AbortUnwStateRel]
              exact ⟨rfl, rfl, hSub⟩
  cases hRel with
  | consEq _ _ _ _ _ hSub => exact hCommon rfl rfl rfl hSub
  | consTightened _ _ _ _ hCf hDst hTgt _ hSub => exact hCommon hCf hDst hTgt hSub

private theorem abortUnw_step_rel {p : Program} {flags : List Bool}
    (hSum : checkNoUnwindSummary p flags = true)
    (ent : DefId) {s₁ s₂ : UnwindState}
    (hRel : AbortUnwStateRel flags s₁ s₂) :
    match evalStepUnw { p with entryDefId := ent } 0 s₁,
          evalStepUnw { p with bodies := p.bodies.map (rewriteBodyAbortUnw flags), entryDefId := ent } 0 s₂ with
    | .step s₁', .step s₂' => AbortUnwStateRel flags s₁' s₂'
    | .done o₁, .done o₂ => o₁ = o₂
    | .fault k₁, .fault k₂ => k₁ = k₂
    | _, _ => False := by
  let ⟨hAct, hMem, hStack⟩ := hRel
  cases s₁ with
  | mk f₁ cs₁ m₁ =>
    cases s₂ with
    | mk f₂ cs₂ m₂ =>
      dsimp at hAct hMem hStack
      subst hAct
      subst hMem
      unfold evalStepUnw
      dsimp
      rw [getElem?_map]
      cases hBod : Trusted.MirSemantics.getElem? p.bodies f₁.defId with
      | none => exact rfl
      | some body =>
        dsimp [rewriteBodyAbortUnw]
        rw [getElem?_map]
        cases hBb : Trusted.MirSemantics.getElem? body.basicBlocks f₁.blockIdx with
        | none => exact rfl
        | some bb =>
          dsimp [rewriteTermAbortUnw]
          cases Trusted.MirSemantics.getElem? bb.statements f₁.stmtIdx with
          | some stmt =>
            dsimp
            have hEvStEq :
                evalStatement
                  { body with basicBlocks := body.basicBlocks.map (rewriteTermAbortUnw flags) }
                  f₁ m₁ stmt =
                  evalStatement body f₁ m₁ stmt := by cases stmt <;> rfl
            rw [hEvStEq]
            let ⟨hNoDone, hSingle⟩ := evalStatement_outcomes body f₁ m₁ stmt
            cases hEv : evalStatement body f₁ m₁ stmt with
            | fault _ => exact rfl
            | done out => exact False.elim (hNoDone out hEv)
            | step st' =>
              dsimp
              let ⟨f', hf', hDefEq⟩ := hSingle st' hEv
              cases st' with
              | mk frs m' =>
                dsimp at hf'
                subst hf'
                dsimp [AbortUnwStateRel]
                refine ⟨rfl, rfl, ?_⟩
                rw [hDefEq]
                exact hStack
          | none =>
            dsimp
            cases Nat.beq f₁.stmtIdx bb.statements.length with
            | false => exact rfl
            | true =>
              dsimp [evalTerminatorUnw]
              cases hTerm : bb.terminator with
              | goto tgt =>
                dsimp [AbortUnwStateRel]
                exact ⟨rfl, rfl, hStack⟩
              | unreachable => exact rfl
              | unsupported => exact rfl
              | return_ =>
                dsimp
                cases bb.cleanup with
                | true => exact rfl
                | false =>
                  dsimp
                  cases Trusted.MirSemantics.getElem? f₁.locals 0 with
                  | none => exact rfl
                  | some sl =>
                    cases sl with
                    | dead => exact rfl
                    | live ov =>
                      cases ov with
                      | none => exact rfl
                      | some rv =>
                        cases hFl : isFlagTrue flags f₁.defId with
                        | false =>
                          rw [hFl] at hStack
                          cases hStack with
                          | nil _ => exact rfl
                          | consEq _ c r₁ r₂ hF hSub =>
                            exact abortUnw_returnToCaller p flags ent rv m₁
                              (AbortUnwStackRel.consEq false c r₁ r₂ hF hSub)
                        | true =>
                          rw [hFl] at hStack
                          cases hStack with
                          | nil _ => exact rfl
                          | consEq _ c r₁ r₂ hF hSub =>
                            exact abortUnw_returnToCaller p flags ent rv m₁
                              (AbortUnwStackRel.consEq true c r₁ r₂ hF hSub)
                          | consTightened c₁ c₂ r₁ r₂ hCf hDst hTgt hU hSub =>
                            exact abortUnw_returnToCaller p flags ent rv m₁
                              (AbortUnwStackRel.consTightened c₁ c₂ r₁ r₂ hCf hDst hTgt hU hSub)
              | switchInt discr targets =>
                dsimp
                cases evalPrimitiveOperand body.locals f₁.locals discr with
                | error _ => exact rfl
                | ok pair =>
                  cases pair with
                  | mk dv la =>
                    cases dv with
                    | scalar sv =>
                      dsimp
                      cases evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches with
                      | error _ => exact rfl
                      | ok tgt =>
                        dsimp [AbortUnwStateRel]
                        exact ⟨rfl, rfl, hStack⟩
                    | bool b =>
                      dsimp
                      cases evalBoolSwitchBranches b targets.otherwise targets.branches with
                      | error _ => exact rfl
                      | ok tgt =>
                        dsimp [AbortUnwStateRel]
                        exact ⟨rfl, rfl, hStack⟩
                    | unit | ptr _ | enumVal _ _ | tuple _ | bytes _ => exact rfl
              | unwindResume =>
                dsimp
                cases !bb.cleanup with
                | true => exact rfl
                | false =>
                  dsimp
                  cases hFl : isFlagTrue flags f₁.defId with
                  | true =>
                    let ⟨body2, hBod2, hAll⟩ := checkNoUnwindSummary_sound hSum hFl
                    rw [hBod] at hBod2; injection hBod2 with hBEq; subst hBEq
                    have hNoU := list_all_getElem? (p := fun b : BasicBlock => termCannotUnwind flags b.terminator) hAll hBb
                    rw [hTerm] at hNoU
                    cases hNoU
                  | false =>
                    rw [hFl] at hStack
                    exact abortUnw_dispatchUnwindStack p flags ent m₁ hStack
              | assert cond expected msg tgt unw =>
                dsimp
                cases hSat : assertConstSatisfied cond expected with
                | true =>
                  dsimp
                  let ⟨bVal, hEvalC, hBoolEq⟩ :=
                    assertConstSatisfied_eval (bodyLocals := body.locals) (locals := f₁.locals) hSat
                  rw [hEvalC]
                  dsimp
                  rw [hBoolEq]
                  dsimp [AbortUnwStateRel]
                  exact ⟨rfl, rfl, hStack⟩
                | false =>
                  dsimp
                  cases evalPrimitiveOperand body.locals f₁.locals cond with
                  | error _ => exact rfl
                  | ok pair =>
                    cases pair with
                    | mk v la =>
                      cases v with
                      | bool b =>
                        dsimp
                        cases boolEq b expected with
                        | true =>
                          dsimp [AbortUnwStateRel]
                          exact ⟨rfl, rfl, hStack⟩
                        | false =>
                          dsimp [dispatchLocalUnwind]
                          cases hU : unw with
                          | cleanup padBb =>
                            exact abortUnw_enterCleanup_eq p flags ent
                              { f₁ with locals := la } cs₁ cs₂ m₁ padBb hStack
                          | terminate => exact rfl
                          | unreachable => exact rfl
                          | continue_ =>
                            cases hFl : isFlagTrue flags f₁.defId with
                            | false =>
                              rw [hFl] at hStack
                              exact abortUnw_dispatchUnwindStack p flags ent m₁ hStack
                            | true =>
                              let ⟨body2, hBod2, hAll⟩ := checkNoUnwindSummary_sound hSum hFl
                              rw [hBod] at hBod2; injection hBod2 with hBEq; subst hBEq
                              have hNoU := list_all_getElem? (p := fun b : BasicBlock => termCannotUnwind flags b.terminator) hAll hBb
                              rw [hTerm, hU] at hNoU
                              dsimp [termCannotUnwind] at hNoU
                              rw [hSat] at hNoU
                              cases hNoU
                      | scalar _ | unit | ptr _ | enumVal _ _ | tuple _ | bytes _ => exact rfl
              | call calleeId args dst tgt unw =>
                dsimp
                have hCallCommon :
                    ∀ (u₂ : UnwindAction),
                      ((isFlagTrue flags calleeId = true ∧ u₂ = .unreachable) ∨
                       (isFlagTrue flags calleeId = false ∧ u₂ = unw)) →
                      match
                        ((match evalCallArgsUnw body.locals f₁.locals args with
                          | .error k => .fault k
                          | .ok (av, la) =>
                            match Trusted.MirSemantics.getElem? p.bodies calleeId with
                            | none => .fault .unsupported
                            | some cb =>
                              match initCalleeFrameUnw calleeId cb av with
                              | .error k => .fault k
                              | .ok cf =>
                                .step ⟨cf, { callerFrame := { f₁ with locals := la }, dst, target := tgt, unwind := unw } :: cs₁, m₁⟩) : StepResult UnwindState UnwindOut),
                        ((match evalCallArgsUnw body.locals f₁.locals args with
                          | .error k => .fault k
                          | .ok (av, la) =>
                            match Trusted.MirSemantics.getElem? (p.bodies.map (rewriteBodyAbortUnw flags)) calleeId with
                            | none => .fault .unsupported
                            | some cb =>
                              match initCalleeFrameUnw calleeId cb av with
                              | .error k => .fault k
                              | .ok cf =>
                                .step ⟨cf, { callerFrame := { f₁ with locals := la }, dst, target := tgt, unwind := u₂ } :: cs₂, m₁⟩) : StepResult UnwindState UnwindOut) with
                      | .step s₁', .step s₂' => AbortUnwStateRel flags s₁' s₂'
                      | .done o₁, .done o₂ => o₁ = o₂
                      | .fault k₁, .fault k₂ => k₁ = k₂
                      | _, _ => False := by
                  intro u₂ hMode
                  cases evalCallArgsUnw body.locals f₁.locals args with
                  | error _ => exact rfl
                  | ok pair =>
                    dsimp
                    rw [getElem?_map]
                    cases Trusted.MirSemantics.getElem? p.bodies calleeId with
                    | none => exact rfl
                    | some cb =>
                      dsimp
                      rw [rewriteBodyAbortUnw_initCallee]
                      cases hInitC : initCalleeFrameUnw calleeId cb pair.1 with
                      | error _ => exact rfl
                      | ok cf =>
                        have hCDef := initCalleeFrameUnw_defId hInitC
                        dsimp [AbortUnwStateRel]
                        refine ⟨rfl, rfl, ?_⟩
                        rw [hCDef]
                        cases hMode with
                        | inl hT =>
                          let ⟨hCalTrue, hU2⟩ := hT
                          rw [hCalTrue]
                          exact AbortUnwStackRel.consTightened _ _ cs₁ cs₂ rfl rfl rfl hU2 hStack
                        | inr hF =>
                          let ⟨hCalFalse, hU2⟩ := hF
                          subst hU2
                          refine AbortUnwStackRel.consEq _ _ cs₁ cs₂ ?_ hStack
                          intro hCallerTrue
                          let ⟨body2, hBod2, hAll⟩ := checkNoUnwindSummary_sound hSum hCallerTrue
                          rw [hBod] at hBod2; injection hBod2 with hBEq; subst hBEq
                          have hNoU := list_all_getElem? (p := fun b : BasicBlock => termCannotUnwind flags b.terminator) hAll hBb
                          rw [hTerm] at hNoU
                          dsimp [termCannotUnwind] at hNoU
                          unfold isFlagTrue at hCalFalse
                          cases hGFl : Trusted.MirSemantics.getElem? flags calleeId with
                          | none =>
                            rw [hGFl] at hNoU; dsimp at hNoU
                            cases u₂ with
                            | terminate => exact Or.inl rfl
                            | unreachable => exact Or.inr rfl
                            | continue_ => cases hNoU
                            | cleanup _ => cases hNoU
                          | some flb =>
                            rw [hGFl] at hCalFalse hNoU
                            cases flb with
                            | true => cases hCalFalse
                            | false =>
                              dsimp at hNoU
                              cases u₂ with
                              | terminate => exact Or.inl rfl
                              | unreachable => exact Or.inr rfl
                              | continue_ => cases hNoU
                              | cleanup _ => cases hNoU
                cases hGFl : Trusted.MirSemantics.getElem? flags calleeId with
                | none =>
                  dsimp
                  exact hCallCommon unw (Or.inr ⟨by unfold isFlagTrue; rw [hGFl], rfl⟩)
                | some flb =>
                  cases flb with
                  | false =>
                    dsimp
                    exact hCallCommon unw (Or.inr ⟨by unfold isFlagTrue; rw [hGFl], rfl⟩)
                  | true =>
                    dsimp
                    exact hCallCommon .unreachable (Or.inl ⟨by unfold isFlagTrue; rw [hGFl], rfl⟩)

private theorem abortUnwindingCalls_sound_slice2 (pSrc pTgt : Program)
    (noUnwindFlags : List Bool)
    (hCheck : checkAbortUnwindingCalls pSrc noUnwindFlags pTgt = true) :
    ProgramEquivUnw pSrc pTgt := by
  unfold checkAbortUnwindingCalls applyAbortUnwindingCalls at hCheck
  cases hSum : checkNoUnwindSummary pSrc noUnwindFlags with
  | false => rw [hSum] at hCheck; cases hCheck
  | true =>
    rw [hSum] at hCheck; dsimp at hCheck
    have hPOut :
        ({ pSrc with bodies := pSrc.bodies.map (rewriteBodyAbortUnw noUnwindFlags) } : Program) =
          pTgt :=
      programEq_eq hCheck
    subst hPOut
    have hMapId :
        (pSrc.bodies.map (rewriteBodyAbortUnw noUnwindFlags)).map (fun b => b.identity) =
          pSrc.bodies.map (fun b => b.identity) := by
      induction pSrc.bodies with
      | nil => rfl
      | cons b bs ih => dsimp [List.map, rewriteBodyAbortUnw]; rw [ih]
    have hSemEntry : ∀ ent : DefId,
        FullSemanticEquivUnw { pSrc with entryDefId := ent }
          { pSrc with bodies := pSrc.bodies.map (rewriteBodyAbortUnw noUnwindFlags), entryDefId := ent } := by
      intro ent
      have hInitEq : ∀ q,
          initStateUnw { pSrc with bodies := pSrc.bodies.map (rewriteBodyAbortUnw noUnwindFlags), entryDefId := ent } q =
            initStateUnw { pSrc with entryDefId := ent } q := by
        intro q
        unfold initStateUnw
        have hBase : initState { pSrc with bodies := pSrc.bodies.map (rewriteBodyAbortUnw noUnwindFlags), entryDefId := ent } q =
            initState { pSrc with entryDefId := ent } q := by
          cases hGet : Trusted.MirSemantics.getElem? pSrc.bodies ent with
          | none =>
            unfold initState; dsimp; rw [getElem?_map, hGet]
          | some body =>
            exact @initState_congr_body
              { pSrc with bodies := pSrc.bodies.map (rewriteBodyAbortUnw noUnwindFlags), entryDefId := ent }
              { pSrc with entryDefId := ent }
              (rewriteBodyAbortUnw noUnwindFlags body) body rfl rfl
              (by rw [getElem?_map, hGet])
              hGet
              rfl
              (rewriteBodyAbortUnw_isEmpty noUnwindFlags body)
              rfl rfl
              (rewriteBodyAbortUnw_storageInBounds noUnwindFlags body)
              (fun loc _ => rewriteBodyAbortUnw_hasStorage noUnwindFlags body loc) q
        rw [hBase]
      exact fullSemanticEquivUnw_of_lockstep (AbortUnwStateRel noUnwindFlags)
        (fun q k => by rw [hInitEq q])
        (fun q s₁ s₂ h1 h2 => by
          rw [hInitEq q] at h2; rw [h1] at h2; injection h2 with hEq; subst hEq
          let ⟨hCs, _⟩ := initStateUnw_entryDefId h1
          refine ⟨rfl, rfl, ?_⟩
          rw [hCs]
          exact AbortUnwStackRel.nil _)
        (fun s₁ s₂ s₁' hRel hSt => by
          have hSR := abortUnw_step_rel hSum ent hRel
          rw [hSt] at hSR
          cases hEv2 : evalStepUnw { pSrc with bodies := pSrc.bodies.map (rewriteBodyAbortUnw noUnwindFlags), entryDefId := ent } 0 s₂ with
          | step s₂' => rw [hEv2] at hSR; exact ⟨s₂', rfl, hSR⟩
          | done _ => rw [hEv2] at hSR; exact False.elim hSR
          | fault _ => rw [hEv2] at hSR; exact False.elim hSR)
        (fun s₁ s₂ out hRel hD => by
          have hSR := abortUnw_step_rel hSum ent hRel
          rw [hD] at hSR
          cases hEv2 : evalStepUnw { pSrc with bodies := pSrc.bodies.map (rewriteBodyAbortUnw noUnwindFlags), entryDefId := ent } 0 s₂ with
          | done o₂ => rw [hEv2] at hSR; dsimp at hSR; rw [← hSR]
          | step _ => rw [hEv2] at hSR; exact False.elim hSR
          | fault _ => rw [hEv2] at hSR; exact False.elim hSR)
        (fun s₁ s₂ k hRel hF => by
          have hSR := abortUnw_step_rel hSum ent hRel
          rw [hF] at hSR
          cases hEv2 : evalStepUnw { pSrc with bodies := pSrc.bodies.map (rewriteBodyAbortUnw noUnwindFlags), entryDefId := ent } 0 s₂ with
          | fault k₂ => rw [hEv2] at hSR; dsimp at hSR; rw [← hSR]
          | step _ => rw [hEv2] at hSR; exact False.elim hSR
          | done _ => rw [hEv2] at hSR; exact False.elim hSR)
    refine ⟨(list_length_map (rewriteBodyAbortUnw noUnwindFlags) pSrc.bodies).symm, rfl, rfl, rfl, rfl,
      (bodiesHaveUniqueIdentities_of_map_eq hMapId).symm,
      hSemEntry pSrc.entryDefId, ?_⟩
    intro d
    rw [getElem?_map]
    cases Trusted.MirSemantics.getElem? pSrc.bodies d with
    | none => exact True.intro
    | some b =>
      refine ⟨rfl, rfl, ?_, fun _ => Iff.rfl, hSemEntry d⟩
      unfold BodyStaticAdmitted
      rw [rewriteBodyAbortUnw_isEmpty, rewriteBodyAbortUnw_storageInBounds]
      rfl

/-! ### Part 3: `.pruneDeadCleanupBlocks` Soundness (`pruneDeadCleanupBlocks_sound_slice2`) -/

private theorem allLocalsStorageAnnotEq_sound (b₁ b₂ : Body) :
    ∀ (n loc : Nat),
      allLocalsStorageAnnotEq b₁ b₂ n = true →
      loc < n →
      hasStorageAnnotation b₁ loc = hasStorageAnnotation b₂ loc
  | 0, _, _, hLt => False.elim (Nat.not_lt_zero _ hLt)
  | n + 1, loc, hAll, hLt => by
    dsimp [allLocalsStorageAnnotEq] at hAll
    let ⟨hCur, hRest⟩ := bool_and_true hAll
    cases hEq : Nat.beq loc n with
    | true =>
      rw [nat_beq_eq hEq]
      exact boolEq_eq hCur
    | false =>
      have hNe : loc ≠ n := nat_ne_of_beq_false hEq
      have hLe : loc ≤ n := Nat.le_of_lt_succ hLt
      exact allLocalsStorageAnnotEq_sound b₁ b₂ n loc hRest (Nat.lt_of_le_of_ne hLe hNe)

private theorem findNewBbIdx_add_base (oldBb : BasicBlockId) :
    ∀ (base : Nat) (ks : List BasicBlockId) (j : Nat),
      findNewBbIdx oldBb 0 ks = some j ↔
      findNewBbIdx oldBb base ks = some (base + j)
  | _, [], _ => ⟨fun h => (by cases h), fun h => (by cases h)⟩
  | base, k :: ks, j => by
    dsimp [findNewBbIdx]
    cases Nat.beq k oldBb with
    | true =>
      dsimp
      constructor
      · intro h; injection h with hj; subst hj; rw [Nat.add_zero]
      · intro h; injection h with hj
        have hJ0 : j = 0 := Nat.add_left_cancel (by rw [Nat.add_zero]; exact hj.symm)
        rw [hJ0]
    | false =>
      dsimp
      cases j with
      | zero =>
        constructor
        · intro h
          have hGe : ∀ (b : Nat) (xs : List BasicBlockId) (r : Nat),
              findNewBbIdx oldBb b xs = some r → b ≤ r := by
            intro b xs
            induction xs generalizing b with
            | nil => intro _ h1; cases h1
            | cons x xs ih =>
              intro r h1
              dsimp [findNewBbIdx] at h1
              cases hx : Nat.beq x oldBb with
              | true =>
                rw [hx] at h1; dsimp at h1; injection h1 with hr; subst hr
                exact Nat.le_refl b
              | false =>
                rw [hx] at h1; dsimp at h1
                exact Nat.le_of_succ_le (ih (b + 1) r h1)
          exact False.elim (Nat.not_succ_le_zero 0 (hGe 1 ks 0 h))
        · intro h
          have hGe : ∀ (b : Nat) (xs : List BasicBlockId) (r : Nat),
              findNewBbIdx oldBb b xs = some r → b ≤ r := by
            intro b xs
            induction xs generalizing b with
            | nil => intro _ h1; cases h1
            | cons x xs ih =>
              intro r h1
              dsimp [findNewBbIdx] at h1
              cases hx : Nat.beq x oldBb with
              | true =>
                rw [hx] at h1; dsimp at h1; injection h1 with hr; subst hr
                exact Nat.le_refl b
              | false =>
                rw [hx] at h1; dsimp at h1
                exact Nat.le_of_succ_le (ih (b + 1) r h1)
          rw [Nat.add_zero] at h
          exact False.elim (Nat.not_succ_le_self base (hGe (base + 1) ks base h))
      | succ j' =>
        have h1 := findNewBbIdx_add_base oldBb 1 ks j'
        have h2 := findNewBbIdx_add_base oldBb (base + 1) ks j'
        have hEq1 : 1 + j' = j' + 1 := Nat.add_comm 1 j'
        have hEq2 : base + 1 + j' = base + (j' + 1) := by
          rw [Nat.add_assoc, Nat.add_comm 1 j']
        rw [hEq1] at h1
        rw [hEq2] at h2
        exact h1.symm.trans h2

private theorem compactKeepBlocks_lookup {origBbs bbs' : List BasicBlock}
    {allKeep : List BasicBlockId} :
    ∀ {ks : List BasicBlockId} {oldBb newBb : BasicBlockId},
      compactKeepBlocks origBbs allKeep ks = some bbs' →
      findNewBbIdx oldBb 0 ks = some newBb →
      ∃ bb term',
        Trusted.MirSemantics.getElem? origBbs oldBb = some bb ∧
        remapTerminator allKeep bb.terminator = some term' ∧
        Trusted.MirSemantics.getElem? bbs' newBb = some { bb with terminator := term' } := by
  intro ks
  induction ks generalizing bbs' with
  | nil => intro _ _ _ hF; cases hF
  | cons k rest ih =>
    intro oldBb newBb hComp hF
    dsimp [compactKeepBlocks] at hComp
    cases hGet : Trusted.MirSemantics.getElem? origBbs k with
    | none => rw [hGet] at hComp; cases hComp
    | some bb =>
      rw [hGet] at hComp; dsimp at hComp
      cases hRemap : remapTerminator allKeep bb.terminator with
      | none => rw [hRemap] at hComp; cases hComp
      | some term' =>
        rw [hRemap] at hComp
        cases hRest : compactKeepBlocks origBbs allKeep rest with
        | none => rw [hRest] at hComp; cases hComp
        | some restBbs =>
          rw [hRest] at hComp; dsimp at hComp
          injection hComp with hBbsEq
          subst hBbsEq
          dsimp [findNewBbIdx] at hF
          cases hEq : Nat.beq k oldBb with
          | true =>
            rw [hEq] at hF; dsimp at hF
            injection hF with hNew0; subst hNew0
            have hK := nat_beq_eq hEq; subst hK
            exact ⟨bb, term', hGet, hRemap, rfl⟩
          | false =>
            rw [hEq] at hF; dsimp at hF
            cases newBb with
            | zero =>
              have hGe : ∀ (b : Nat) (xs : List BasicBlockId) (r : Nat),
                  findNewBbIdx oldBb b xs = some r → b ≤ r := by
                intro b xs
                induction xs generalizing b with
                | nil => intro _ h1; cases h1
                | cons x xs ih2 =>
                  intro r h1
                  dsimp [findNewBbIdx] at h1
                  cases hx : Nat.beq x oldBb with
                  | true => rw [hx] at h1; dsimp at h1; injection h1 with hr; subst hr; exact Nat.le_refl b
                  | false => rw [hx] at h1; dsimp at h1; exact Nat.le_of_succ_le (ih2 (b + 1) r h1)
              exact False.elim (Nat.not_succ_le_zero 0 (hGe 1 rest 0 hF))
            | succ j =>
              have hF0 : findNewBbIdx oldBb 0 rest = some j :=
                (findNewBbIdx_add_base oldBb 1 rest j).mpr (by rw [Nat.add_comm]; exact hF)
              exact ih (bbs' := restBbs) hRest hF0

private theorem evalSwitchBranches_remap (keepBlocks : List BasicBlockId)
    (w : IntWidth) (bits : BitVec 128) {oth oth' : BasicBlockId}
    (hOth : findNewBbIdx oth 0 keepBlocks = some oth') :
    ∀ {brs brs' : List (BitVec 128 × BasicBlockId)},
      remapSwitchBranches keepBlocks brs = some brs' →
      match evalSwitchBranches w bits oth brs, evalSwitchBranches w bits oth' brs' with
      | .ok t₁, .ok t₂ => findNewBbIdx t₁ 0 keepBlocks = some t₂
      | .error k₁, .error k₂ => k₁ = k₂
      | _, _ => False
  | [], brs', hR => by
    dsimp [remapSwitchBranches] at hR
    injection hR with hEq; subst hEq
    dsimp [evalSwitchBranches]
    exact hOth
  | (v, b) :: rest, brs', hR => by
    dsimp [remapSwitchBranches] at hR
    cases hFb : findNewBbIdx b 0 keepBlocks with
    | none => rw [hFb] at hR; cases hR
    | some b' =>
      rw [hFb] at hR
      cases hRest : remapSwitchBranches keepBlocks rest with
      | none => rw [hRest] at hR; cases hR
      | some rest' =>
        rw [hRest] at hR
        injection hR with hEq; subst hEq
        dsimp [evalSwitchBranches]
        cases truncateBits w v != v with
        | true => exact rfl
        | false =>
          dsimp
          cases truncateBits w bits == truncateBits w v with
          | true => exact hFb
          | false => exact evalSwitchBranches_remap keepBlocks w bits hOth hRest

private theorem evalBoolSwitchBranches_remap (keepBlocks : List BasicBlockId)
    (bVal : Bool) {oth oth' : BasicBlockId}
    (hOth : findNewBbIdx oth 0 keepBlocks = some oth') :
    ∀ {brs brs' : List (BitVec 128 × BasicBlockId)},
      remapSwitchBranches keepBlocks brs = some brs' →
      match evalBoolSwitchBranches bVal oth brs, evalBoolSwitchBranches bVal oth' brs' with
      | .ok t₁, .ok t₂ => findNewBbIdx t₁ 0 keepBlocks = some t₂
      | .error k₁, .error k₂ => k₁ = k₂
      | _, _ => False
  | [], brs', hR => by
    dsimp [remapSwitchBranches] at hR
    injection hR with hEq; subst hEq
    dsimp [evalBoolSwitchBranches]
    exact hOth
  | (v, b) :: rest, brs', hR => by
    dsimp [remapSwitchBranches] at hR
    cases hFb : findNewBbIdx b 0 keepBlocks with
    | none => rw [hFb] at hR; cases hR
    | some b' =>
      rw [hFb] at hR
      cases hRest : remapSwitchBranches keepBlocks rest with
      | none => rw [hRest] at hR; cases hR
      | some rest' =>
        rw [hRest] at hR
        injection hR with hEq; subst hEq
        dsimp [evalBoolSwitchBranches]
        cases evalConstLit .bool (.scalar v) with
        | error _ => exact rfl
        | ok val =>
          cases val with
          | bool cb =>
            cases cb with
            | false =>
              dsimp
              cases !bVal with
              | true => exact hFb
              | false => exact evalBoolSwitchBranches_remap keepBlocks bVal hOth hRest
            | true =>
              dsimp
              cases bVal with
              | true => exact hFb
              | false => exact evalBoolSwitchBranches_remap keepBlocks false hOth hRest
          | scalar _ | unit | ptr _ | enumVal _ _ | tuple _ | bytes _ => exact rfl

/-- Frame relation for `PruneDeadCleanupBlocks` on `defId`. -/
private noncomputable def PruneFrameRel (defId : DefId) (keepBlocks : List BasicBlockId)
    (f₁ f₂ : FrameState) : Prop :=
  f₁.defId = f₂.defId ∧
  f₁.stmtIdx = f₂.stmtIdx ∧
  f₁.locals = f₂.locals ∧
  (f₁.defId ≠ defId → f₁.blockIdx = f₂.blockIdx) ∧
  (f₁.defId = defId → findNewBbIdx f₁.blockIdx 0 keepBlocks = some f₂.blockIdx)

private noncomputable def PruneContRel (defId : DefId) (keepBlocks : List BasicBlockId)
    (c₁ c₂ : CallContUnw) : Prop :=
  PruneFrameRel defId keepBlocks c₁.callerFrame c₂.callerFrame ∧
  c₁.dst = c₂.dst ∧
  (c₁.callerFrame.defId ≠ defId → c₁.target = c₂.target ∧ c₁.unwind = c₂.unwind) ∧
  (c₁.callerFrame.defId = defId →
    ((c₁.target = none ∧ c₂.target = none) ∨
      ∃ t₁ t₂, c₁.target = some t₁ ∧ c₂.target = some t₂ ∧
        findNewBbIdx t₁ 0 keepBlocks = some t₂) ∧
    remapUnwindAction keepBlocks c₁.unwind = some c₂.unwind)

private inductive PruneStackRel (defId : DefId) (keepBlocks : List BasicBlockId) :
    List CallContUnw → List CallContUnw → Prop where
  | nil : PruneStackRel defId keepBlocks [] []
  | cons {c₁ c₂ : CallContUnw} {r₁ r₂ : List CallContUnw} :
      PruneContRel defId keepBlocks c₁ c₂ →
      PruneStackRel defId keepBlocks r₁ r₂ →
      PruneStackRel defId keepBlocks (c₁ :: r₁) (c₂ :: r₂)

private noncomputable def PruneStateRel (defId : DefId) (keepBlocks : List BasicBlockId)
    (s₁ s₂ : UnwindState) : Prop :=
  PruneFrameRel defId keepBlocks s₁.active s₂.active ∧
  s₁.callerMem = s₂.callerMem ∧
  PruneStackRel defId keepBlocks s₁.callStack s₂.callStack

private theorem prune_enterCleanup {p : Program} {defId : DefId}
    {keepBlocks : List BasicBlockId} {body : Body}
    {bbs' : List BasicBlock} {bodies' : List Body}
    (hGetB : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (hComp : compactKeepBlocks body.basicBlocks keepBlocks keepBlocks = some bbs')
    (hSetB : setElem? p.bodies defId { body with basicBlocks := bbs' } = some bodies')
    (ent : DefId) {f₁ f₂ : FrameState} {r₁ r₂ : List CallContUnw}
    (mem : CallerMemory) (pad₁ pad₂ : BasicBlockId)
    (hFr : PruneFrameRel defId keepBlocks f₁ f₂)
    (hSt : PruneStackRel defId keepBlocks r₁ r₂)
    (hPadNe : f₁.defId ≠ defId → pad₁ = pad₂)
    (hPadEq : f₁.defId = defId → findNewBbIdx pad₁ 0 keepBlocks = some pad₂) :
    match enterCleanupBlockUnw { p with entryDefId := ent } f₁ r₁ mem pad₁,
          enterCleanupBlockUnw { p with bodies := bodies', entryDefId := ent } f₂ r₂ mem pad₂ with
    | .step s₁', .step s₂' => PruneStateRel defId keepBlocks s₁' s₂'
    | .done o₁, .done o₂ => o₁ = o₂
    | .fault k₁, .fault k₂ => k₁ = k₂
    | _, _ => False := by
  let ⟨hDef, _, hLocs, _, _⟩ := hFr
  unfold enterCleanupBlockUnw
  dsimp
  rw [← hDef]
  cases hEqD : Nat.beq f₁.defId defId with
  | false =>
    have hNe := nat_ne_of_beq_false hEqD
    rw [setElem?_getElem?_ne hSetB hNe, ← hPadNe hNe]
    cases Trusted.MirSemantics.getElem? p.bodies f₁.defId with
    | none => exact rfl
    | some b =>
      dsimp
      cases Trusted.MirSemantics.getElem? b.basicBlocks pad₁ with
      | none => exact rfl
      | some bb =>
        dsimp
        cases !bb.cleanup with
        | true => exact rfl
        | false =>
          dsimp [PruneStateRel, PruneFrameRel]
          exact ⟨⟨rfl, rfl, hLocs, fun _ => rfl, fun h => False.elim (hNe h)⟩, rfl, hSt⟩
  | true =>
    have hD := nat_beq_eq hEqD
    rw [hD, hGetB, setElem?_getElem?_same hSetB]
    dsimp
    have hFind := hPadEq hD
    let ⟨bb, term', hGetBb, _, hGetBb'⟩ := compactKeepBlocks_lookup hComp hFind
    rw [hGetBb, hGetBb']
    dsimp
    cases !bb.cleanup with
    | true => exact rfl
    | false =>
      dsimp [PruneStateRel, PruneFrameRel]
      exact ⟨⟨rfl, rfl, hLocs, fun h => False.elim (h rfl), fun _ => hFind⟩, rfl, hSt⟩

private theorem prune_dispatchUnwindStack {p : Program} {defId : DefId}
    {keepBlocks : List BasicBlockId} {body : Body}
    {bbs' : List BasicBlock} {bodies' : List Body}
    (hGetB : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (hComp : compactKeepBlocks body.basicBlocks keepBlocks keepBlocks = some bbs')
    (hSetB : setElem? p.bodies defId { body with basicBlocks := bbs' } = some bodies')
    (ent : DefId) (mem : CallerMemory) :
    ∀ {cs₁ cs₂ : List CallContUnw},
      PruneStackRel defId keepBlocks cs₁ cs₂ →
      match dispatchUnwindStack { p with entryDefId := ent } mem cs₁,
            dispatchUnwindStack { p with bodies := bodies', entryDefId := ent } mem cs₂ with
      | .step s₁', .step s₂' => PruneStateRel defId keepBlocks s₁' s₂'
      | .done o₁, .done o₂ => o₁ = o₂
      | .fault k₁, .fault k₂ => k₁ = k₂
      | _, _ => False := by
  intro cs₁ cs₂ hRel
  induction hRel with
  | nil => exact rfl
  | @cons c₁ c₂ r₁ r₂ hCont hSub ih =>
    let ⟨hFr, _, hNeC, hEqC⟩ := hCont
    dsimp [dispatchUnwindStack]
    cases hEqD : Nat.beq c₁.callerFrame.defId defId with
    | false =>
      have hNe := nat_ne_of_beq_false hEqD
      let ⟨_, hUnwEq⟩ := hNeC hNe
      rw [← hUnwEq]
      cases c₁.unwind with
      | continue_ => exact ih
      | unreachable => exact rfl
      | terminate => exact rfl
      | cleanup padBb =>
        exact prune_enterCleanup hGetB hComp hSetB ent mem padBb padBb hFr hSub
          (fun _ => rfl) (fun h => False.elim (hNe h))
    | true =>
      have hD := nat_beq_eq hEqD
      let ⟨_, hRemapU⟩ := hEqC hD
      cases hU1 : c₁.unwind with
      | continue_ =>
        rw [hU1] at hRemapU; dsimp [remapUnwindAction] at hRemapU
        injection hRemapU with hU2; rw [← hU2]; exact ih
      | unreachable =>
        rw [hU1] at hRemapU; dsimp [remapUnwindAction] at hRemapU
        injection hRemapU with hU2; rw [← hU2]
      | terminate =>
        rw [hU1] at hRemapU; dsimp [remapUnwindAction] at hRemapU
        injection hRemapU with hU2; rw [← hU2]
      | cleanup pad₁ =>
        rw [hU1] at hRemapU; dsimp [remapUnwindAction] at hRemapU
        cases hF : findNewBbIdx pad₁ 0 keepBlocks with
        | none => rw [hF] at hRemapU; cases hRemapU
        | some pad₂ =>
          rw [hF] at hRemapU; dsimp at hRemapU
          injection hRemapU with hU2; rw [← hU2]
          exact prune_enterCleanup hGetB hComp hSetB ent mem pad₁ pad₂ hFr hSub
            (fun h => False.elim (h hD)) (fun _ => hF)

private theorem prune_returnToCaller {p : Program} {defId : DefId}
    {keepBlocks : List BasicBlockId} {body : Body}
    {bbs' : List BasicBlock} {bodies' : List Body}
    (hGetB : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (hSetB : setElem? p.bodies defId { body with basicBlocks := bbs' } = some bodies')
    (ent : DefId) (retVal : Val) (mem : CallerMemory)
    {c₁ c₂ : CallContUnw} {r₁ r₂ : List CallContUnw}
    (hCont : PruneContRel defId keepBlocks c₁ c₂)
    (hSub : PruneStackRel defId keepBlocks r₁ r₂) :
    match returnToCallerUnw { p with entryDefId := ent } retVal c₁ r₁ mem,
          returnToCallerUnw { p with bodies := bodies', entryDefId := ent } retVal c₂ r₂ mem with
    | .step s₁', .step s₂' => PruneStateRel defId keepBlocks s₁' s₂'
    | .done o₁, .done o₂ => o₁ = o₂
    | .fault k₁, .fault k₂ => k₁ = k₂
    | _, _ => False := by
  let ⟨⟨hDef, _, hLocs, _, _⟩, hDst, hNeC, hEqC⟩ := hCont
  unfold returnToCallerUnw
  dsimp
  rw [← hDef, ← hDst, ← hLocs]
  cases hEqD : Nat.beq c₁.callerFrame.defId defId with
  | false =>
    have hNe := nat_ne_of_beq_false hEqD
    let ⟨hTgtEq, _⟩ := hNeC hNe
    rw [setElem?_getElem?_ne hSetB hNe, ← hTgtEq]
    cases Trusted.MirSemantics.getElem? p.bodies c₁.callerFrame.defId with
    | none => exact rfl
    | some cb =>
      dsimp
      cases !c₁.dst.projection.isEmpty with
      | true => exact rfl
      | false =>
        dsimp
        cases Trusted.MirSemantics.getElem? cb.locals c₁.dst.localId with
        | none => exact rfl
        | some dstTy =>
          dsimp
          cases writePlace c₁.callerFrame.locals c₁.dst.localId dstTy retVal with
          | error _ => exact rfl
          | ok locs' =>
            dsimp
            cases c₁.target with
            | none => exact rfl
            | some nextBb =>
              dsimp [PruneStateRel, PruneFrameRel]
              exact ⟨⟨rfl, rfl, rfl, fun _ => rfl, fun h => False.elim (hNe h)⟩, rfl, hSub⟩
  | true =>
    have hD := nat_beq_eq hEqD
    let ⟨hTgtRel, _⟩ := hEqC hD
    rw [hD, hGetB, setElem?_getElem?_same hSetB]
    dsimp
    cases !c₁.dst.projection.isEmpty with
    | true => exact rfl
    | false =>
      dsimp
      cases Trusted.MirSemantics.getElem? body.locals c₁.dst.localId with
      | none => exact rfl
      | some dstTy =>
        dsimp
        cases writePlace c₁.callerFrame.locals c₁.dst.localId dstTy retVal with
        | error _ => exact rfl
        | ok locs' =>
          dsimp
          cases hTgtRel with
          | inl hN =>
            let ⟨hN1, hN2⟩ := hN
            rw [hN1, hN2]
          | inr hS =>
            let ⟨t₁, t₂, hT1, hT2, hF⟩ := hS
            rw [hT1, hT2]
            dsimp [PruneStateRel, PruneFrameRel]
            exact ⟨⟨rfl, rfl, rfl, fun h => False.elim (h rfl), fun _ => hF⟩, rfl, hSub⟩

private theorem prune_step_rel {p : Program} {defId : DefId}
    {keepTail : List BasicBlockId} {body : Body}
    {bbs' : List BasicBlock} {bodies' : List Body}
    (hGetB : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (hBound : isStrictSortedBounded body.basicBlocks.length none (0 :: keepTail) = true)
    (hComp : compactKeepBlocks body.basicBlocks (0 :: keepTail) (0 :: keepTail) = some bbs')
    (hSb : storageAnnotationsInBounds body = storageAnnotationsInBounds { body with basicBlocks := bbs' })
    (hAllHas : allLocalsStorageAnnotEq body { body with basicBlocks := bbs' } body.locals.length = true)
    (hSetB : setElem? p.bodies defId { body with basicBlocks := bbs' } = some bodies')
    (ent : DefId) {s₁ s₂ : UnwindState}
    (hRel : PruneStateRel defId (0 :: keepTail) s₁ s₂) :
    match evalStepUnw { p with entryDefId := ent } 0 s₁,
          evalStepUnw { p with bodies := bodies', entryDefId := ent } 0 s₂ with
    | .step s₁', .step s₂' => PruneStateRel defId (0 :: keepTail) s₁' s₂'
    | .done o₁, .done o₂ => o₁ = o₂
    | .fault k₁, .fault k₂ => k₁ = k₂
    | _, _ => False := by
  let keepBlocks := 0 :: keepTail
  have hBbsNonEmpty : bbs'.isEmpty = body.basicBlocks.isEmpty := by
    have h0Lt : 0 < body.basicBlocks.length := by
      dsimp [isStrictSortedBounded] at hBound
      exact nat_blt_lt (bool_and_true hBound).1
    cases hOrig : body.basicBlocks with
    | nil => rw [hOrig] at h0Lt; exact False.elim (Nat.not_lt_zero 0 h0Lt)
    | cons _ _ =>
      have hC := hComp
      dsimp [compactKeepBlocks] at hC
      rw [hOrig] at hC
      dsimp [Trusted.MirSemantics.getElem?] at hC
      cases hRm : remapTerminator (0 :: keepTail) _ with
      | none => rw [hRm] at hC; cases hC
      | some _ =>
        rw [hRm] at hC
        cases hCr : compactKeepBlocks _ _ keepTail with
        | none => rw [hCr] at hC; cases hC
        | some _ =>
          rw [hCr] at hC
          injection hC with hEq; rw [← hEq]; rfl
  have hInitCalleeEq : ∀ av,
      initCalleeFrameUnw defId { body with basicBlocks := bbs' } av =
        initCalleeFrameUnw defId body av := by
    intro av
    unfold initCalleeFrameUnw
    dsimp
    rw [hBbsNonEmpty, ← hSb]
    have hLoop : initLocalsLoop { body with basicBlocks := bbs' } av 0 body.locals =
        initLocalsLoop body av 0 body.locals :=
      @initLocalsLoop_congr_hasStorage { body with basicBlocks := bbs' } body av rfl
        (fun loc hLt => (allLocalsStorageAnnotEq_sound body { body with basicBlocks := bbs' }
          body.locals.length loc hAllHas hLt).symm)
        0 body.locals (by rw [Nat.zero_add]; exact Nat.le_refl _)
    rw [hLoop]
  have hInitFrameRel : ∀ cDef cf, cf.defId = cDef → cf.blockIdx = 0 →
      PruneFrameRel defId keepBlocks cf cf := by
    intro cDef cf hCd hCb
    refine ⟨rfl, rfl, rfl, fun _ => rfl, fun hEq => ?_⟩
    rw [hCb]; rfl
  let ⟨⟨hDef, hStmt, hLocs, hBbNe, hBbEq⟩, hMem, hStack⟩ := hRel
  cases s₁ with
  | mk f₁ cs₁ m₁ =>
    cases s₂ with
    | mk f₂ cs₂ m₂ =>
      dsimp at hDef hStmt hLocs hBbNe hBbEq hMem hStack
      subst hMem
      unfold evalStepUnw
      dsimp
      rw [← hDef, ← hStmt]
      cases hEqD : Nat.beq f₁.defId defId with
      | false =>
        have hNe := nat_ne_of_beq_false hEqD
        rw [setElem?_getElem?_ne hSetB hNe, ← hBbNe hNe]
        cases Trusted.MirSemantics.getElem? p.bodies f₁.defId with
        | none => exact rfl
        | some b =>
          dsimp
          cases Trusted.MirSemantics.getElem? b.basicBlocks f₁.blockIdx with
          | none => exact rfl
          | some bb =>
            dsimp
            cases Trusted.MirSemantics.getElem? bb.statements f₁.stmtIdx with
            | some stmt =>
              dsimp
              have hFeq : f₂ = f₁ := by
                cases f₁; cases f₂; dsimp at hDef hStmt hLocs hBbNe
                have hBi := hBbNe hNe
                subst hDef; subst hStmt; subst hLocs; subst hBi; rfl
              rw [hFeq]
              let ⟨hNoDone, hSingle⟩ := evalStatement_outcomes b f₁ m₁ stmt
              cases hEv : evalStatement b f₁ m₁ stmt with
              | fault _ => exact rfl
              | done out => exact False.elim (hNoDone out hEv)
              | step st' =>
                dsimp
                let ⟨f', hf', hDef'⟩ := hSingle st' hEv
                cases st' with
                | mk frs m' =>
                  dsimp at hf'; subst hf'
                  dsimp [PruneStateRel, PruneFrameRel]
                  exact ⟨⟨rfl, rfl, rfl, fun _ => rfl, fun h => False.elim (hNe (hDef'.symm.trans h))⟩, rfl, hStack⟩
            | none =>
              dsimp
              cases Nat.beq f₁.stmtIdx bb.statements.length with
              | false => exact rfl
              | true =>
                have hFeq : f₂ = f₁ := by
                  cases f₁; cases f₂; dsimp at hDef hStmt hLocs hBbNe
                  have hBi := hBbNe hNe
                  subst hDef; subst hStmt; subst hLocs; subst hBi; rfl
                rw [hFeq]
                dsimp [evalTerminatorUnw]
                cases bb.terminator with
                | goto tgt =>
                  dsimp [PruneStateRel, PruneFrameRel]
                  exact ⟨⟨rfl, rfl, rfl, fun _ => rfl, fun h => False.elim (hNe h)⟩, rfl, hStack⟩
                | unreachable => exact rfl
                | unsupported => exact rfl
                | return_ =>
                  dsimp
                  cases bb.cleanup with
                  | true => exact rfl
                  | false =>
                    dsimp
                    cases Trusted.MirSemantics.getElem? f₁.locals 0 with
                    | none => exact rfl
                    | some sl =>
                      cases sl with
                      | dead => exact rfl
                      | live ov =>
                        cases ov with
                        | none => exact rfl
                        | some rv =>
                          cases hStack with
                          | nil => exact rfl
                          | cons hCont hSub =>
                            exact prune_returnToCaller hGetB hSetB ent rv m₁ hCont hSub
                | switchInt discr targets =>
                  dsimp
                  cases evalPrimitiveOperand b.locals f₁.locals discr with
                  | error _ => exact rfl
                  | ok pair =>
                    cases pair with
                    | mk dv la =>
                      cases dv with
                      | scalar sv =>
                        dsimp
                        cases evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches with
                        | error _ => exact rfl
                        | ok tgt =>
                          dsimp [PruneStateRel, PruneFrameRel]
                          exact ⟨⟨rfl, rfl, rfl, fun _ => rfl, fun h => False.elim (hNe h)⟩, rfl, hStack⟩
                      | bool bv =>
                        dsimp
                        cases evalBoolSwitchBranches bv targets.otherwise targets.branches with
                        | error _ => exact rfl
                        | ok tgt =>
                          dsimp [PruneStateRel, PruneFrameRel]
                          exact ⟨⟨rfl, rfl, rfl, fun _ => rfl, fun h => False.elim (hNe h)⟩, rfl, hStack⟩
                      | unit | ptr _ | enumVal _ _ | tuple _ | bytes _ => exact rfl
                | unwindResume =>
                  dsimp
                  cases !bb.cleanup with
                  | true => exact rfl
                  | false =>
                    dsimp
                    exact prune_dispatchUnwindStack hGetB hComp hSetB ent m₁ hStack
                | assert cond expected msg tgt unw =>
                  dsimp
                  cases evalPrimitiveOperand b.locals f₁.locals cond with
                  | error _ => exact rfl
                  | ok pair =>
                    cases pair with
                    | mk v la =>
                      cases v with
                      | bool bv =>
                        dsimp
                        cases boolEq bv expected with
                        | true =>
                          dsimp [PruneStateRel, PruneFrameRel]
                          exact ⟨⟨rfl, rfl, rfl, fun _ => rfl, fun h => False.elim (hNe h)⟩, rfl, hStack⟩
                        | false =>
                          dsimp [dispatchLocalUnwind]
                          cases unw with
                          | cleanup padBb =>
                            exact prune_enterCleanup hGetB hComp hSetB ent m₁ padBb padBb
                              ⟨rfl, rfl, rfl, fun _ => rfl, fun h => False.elim (hNe h)⟩ hStack
                              (fun _ => rfl) (fun h => False.elim (hNe h))
                          | continue_ =>
                            exact prune_dispatchUnwindStack hGetB hComp hSetB ent m₁ hStack
                          | unreachable => exact rfl
                          | terminate => exact rfl
                      | scalar _ | unit | ptr _ | enumVal _ _ | tuple _ | bytes _ => exact rfl
                | call cDef args dst tgt unw =>
                  dsimp
                  cases evalCallArgsUnw b.locals f₁.locals args with
                  | error _ => exact rfl
                  | ok pair =>
                    dsimp
                    cases hEqC : Nat.beq cDef defId with
                    | false =>
                      rw [setElem?_getElem?_ne hSetB (nat_ne_of_beq_false hEqC)]
                      cases Trusted.MirSemantics.getElem? p.bodies cDef with
                      | none => exact rfl
                      | some cb =>
                        dsimp
                        cases hIC : initCalleeFrameUnw cDef cb pair.1 with
                        | error _ => exact rfl
                        | ok cf =>
                          have hCd := initCalleeFrameUnw_defId hIC
                          have hCb : cf.blockIdx = 0 := by
                            unfold initCalleeFrameUnw at hIC
                            cases h1 : cb.basicBlocks.isEmpty <;> rw [h1] at hIC
                            · dsimp at hIC
                              cases h2 : (!Nat.blt cb.argumentCount cb.locals.length) <;> rw [h2] at hIC
                              · dsimp at hIC
                                cases h3 : (!storageAnnotationsInBounds cb) <;> rw [h3] at hIC
                                · dsimp at hIC
                                  cases h4 : (!cb.locals.all isSupportedScalarOrUnitTy) <;> rw [h4] at hIC
                                  · dsimp at hIC
                                    cases h5 : (!checkArgsMatch pair.1 ((cb.locals.drop 1).take cb.argumentCount)) <;> rw [h5] at hIC
                                    · dsimp at hIC; injection hIC with he; rw [← he]
                                    · cases hIC
                                  · cases hIC
                                · cases hIC
                              · cases hIC
                            · cases hIC
                          dsimp [PruneStateRel]
                          refine ⟨hInitFrameRel cDef cf hCd hCb, rfl, PruneStackRel.cons ?_ hStack⟩
                          exact ⟨⟨rfl, rfl, rfl, fun _ => rfl, fun h => False.elim (hNe h)⟩,
                            rfl, fun _ => ⟨rfl, rfl⟩, fun h => False.elim (hNe h)⟩
                    | true =>
                      have hC := nat_beq_eq hEqC
                      rw [hC, hGetB, setElem?_getElem?_same hSetB]
                      dsimp
                      rw [hInitCalleeEq pair.1]
                      cases hIC : initCalleeFrameUnw defId body pair.1 with
                      | error _ => exact rfl
                      | ok cf =>
                        have hCd := initCalleeFrameUnw_defId hIC
                        have hCb : cf.blockIdx = 0 := by
                          unfold initCalleeFrameUnw at hIC
                          cases h1 : body.basicBlocks.isEmpty <;> rw [h1] at hIC
                          · dsimp at hIC
                            cases h2 : (!Nat.blt body.argumentCount body.locals.length) <;> rw [h2] at hIC
                            · dsimp at hIC
                              cases h3 : (!storageAnnotationsInBounds body) <;> rw [h3] at hIC
                              · dsimp at hIC
                                cases h4 : (!body.locals.all isSupportedScalarOrUnitTy) <;> rw [h4] at hIC
                                · dsimp at hIC
                                  cases h5 : (!checkArgsMatch pair.1 ((body.locals.drop 1).take body.argumentCount)) <;> rw [h5] at hIC
                                  · dsimp at hIC; injection hIC with he; rw [← he]
                                  · cases hIC
                                · cases hIC
                              · cases hIC
                            · cases hIC
                          · cases hIC
                        dsimp [PruneStateRel]
                        refine ⟨hInitFrameRel defId cf hCd hCb, rfl, PruneStackRel.cons ?_ hStack⟩
                        exact ⟨⟨rfl, rfl, rfl, fun _ => rfl, fun h => False.elim (hNe h)⟩,
                          rfl, fun _ => ⟨rfl, rfl⟩, fun h => False.elim (hNe h)⟩
      | true =>
        have hD := nat_beq_eq hEqD
        have hFind := hBbEq hD
        rw [hD, hGetB, setElem?_getElem?_same hSetB]
        dsimp
        let ⟨bb, term', hGetBb, hRemap, hGetBb'⟩ := compactKeepBlocks_lookup hComp hFind
        rw [hGetBb, hGetBb']
        dsimp
        cases Trusted.MirSemantics.getElem? bb.statements f₁.stmtIdx with
        | some stmt =>
          dsimp
          have hEvStEq :
              evalStatement { body with basicBlocks := bbs' } f₂ m₁ stmt =
                match evalStatement body f₁ m₁ stmt with
                | .fault k => .fault k
                | .done out => .done out
                | .step st' =>
                  match st'.frames with
                  | [f'] => .step ⟨[{ f' with blockIdx := f₂.blockIdx }], st'.callerMem⟩
                  | _ => .fault .unsupported := by
            cases stmt with
            | nop =>
              dsimp [evalStatement]
              cases f₁; cases f₂; dsimp at hDef hStmt hLocs
              subst hDef; subst hStmt; subst hLocs; rfl
            | unsupported => rfl
            | storageLive lid =>
              dsimp [evalStatement]
              rw [← hLocs]
              cases Trusted.MirSemantics.getElem? body.locals lid with
              | none => rfl
              | some ty =>
                dsimp
                cases setElem? f₁.locals lid (liveUninitSlot ty) with
                | none => rfl
                | some locs' =>
                  dsimp
                  cases f₁; cases f₂; dsimp at hDef hStmt hLocs
                  subst hDef; subst hStmt; subst hLocs; rfl
            | storageDead lid =>
              dsimp [evalStatement]
              rw [← hLocs]
              cases Nat.beq lid 0 with
              | true => rfl
              | false =>
                dsimp
                cases setElem? f₁.locals lid .dead with
                | none => rfl
                | some locs' =>
                  dsimp
                  cases f₁; cases f₂; dsimp at hDef hStmt hLocs
                  subst hDef; subst hStmt; subst hLocs; rfl
            | assign dst rv =>
              dsimp [evalStatement]
              rw [← hLocs]
              cases !dst.projection.isEmpty with
              | true => rfl
              | false =>
                dsimp
                cases Trusted.MirSemantics.getElem? body.locals dst.localId with
                | none => rfl
                | some dstTy =>
                  dsimp
                  cases evalRvalue body.locals f₁.locals dstTy rv with
                  | error _ => rfl
                  | ok pair =>
                    dsimp
                    cases writePlace pair.2 dst.localId dstTy pair.1 with
                    | error _ => rfl
                    | ok locs' =>
                      dsimp
                      cases f₁; cases f₂; dsimp at hDef hStmt hLocs
                      subst hDef; subst hStmt; subst hLocs; rfl
          rw [hEvStEq]
          let ⟨hNoDone, hSingle⟩ := evalStatement_outcomes body f₁ m₁ stmt
          cases hEv : evalStatement body f₁ m₁ stmt with
          | fault _ => exact rfl
          | done out => exact False.elim (hNoDone out hEv)
          | step st' =>
            dsimp
            let ⟨f', hf', hDef'⟩ := hSingle st' hEv
            cases st' with
            | mk frs m' =>
              dsimp at hf'; subst hf'
              dsimp [PruneStateRel, PruneFrameRel]
              have hBb' : f'.blockIdx = f₁.blockIdx := by
                cases stmt with
                | nop => dsimp [evalStatement] at hEv; injection hEv with h1; injection h1 with h2; injection h2 with h3; rw [← h3]
                | unsupported => cases hEv
                | storageLive lid =>
                  dsimp [evalStatement] at hEv
                  cases h1 : Trusted.MirSemantics.getElem? body.locals lid with
                  | none => rw [h1] at hEv; cases hEv
                  | some ty =>
                    rw [h1] at hEv; dsimp at hEv
                    cases h2 : setElem? f₁.locals lid (liveUninitSlot ty) with
                    | none => rw [h2] at hEv; cases hEv
                    | some ls => rw [h2] at hEv; injection hEv with ha; injection ha with hb; injection hb with hc; rw [← hc]
                | storageDead lid =>
                  dsimp [evalStatement] at hEv
                  cases h1 : Nat.beq lid 0 with
                  | true => rw [h1] at hEv; cases hEv
                  | false =>
                    rw [h1] at hEv; dsimp at hEv
                    cases h2 : setElem? f₁.locals lid .dead with
                    | none => rw [h2] at hEv; cases hEv
                    | some ls => rw [h2] at hEv; injection hEv with ha; injection ha with hb; injection hb with hc; rw [← hc]
                | assign dst rv =>
                  dsimp [evalStatement] at hEv
                  cases h1 : !dst.projection.isEmpty with
                  | true => rw [h1] at hEv; cases hEv
                  | false =>
                    rw [h1] at hEv; dsimp at hEv
                    cases h2 : Trusted.MirSemantics.getElem? body.locals dst.localId with
                    | none => rw [h2] at hEv; cases hEv
                    | some dt =>
                      rw [h2] at hEv; dsimp at hEv
                      cases h3 : evalRvalue body.locals f₁.locals dt rv with
                      | error _ => rw [h3] at hEv; cases hEv
                      | ok pr =>
                        rw [h3] at hEv; dsimp at hEv
                        cases h4 : writePlace pr.2 dst.localId dt pr.1 with
                        | error _ => rw [h4] at hEv; cases hEv
                        | ok ls => rw [h4] at hEv; injection hEv with ha; injection ha with hb; injection hb with hc; rw [← hc]
              refine ⟨⟨rfl, rfl, rfl, fun h => False.elim (h (hDef'.trans hD)), fun _ => ?_⟩, rfl, hStack⟩
              rw [hBb']
              exact hFind
        | none =>
          dsimp
          cases Nat.beq f₁.stmtIdx bb.statements.length with
          | false => exact rfl
          | true =>
            dsimp [evalTerminatorUnw]
            rw [← hLocs]
            cases hTerm : bb.terminator with
            | goto t₁ =>
              rw [hTerm] at hRemap; dsimp [remapTerminator] at hRemap
              cases hFt : findNewBbIdx t₁ 0 keepBlocks with
              | none => rw [hFt] at hRemap; cases hRemap
              | some t₂ =>
                rw [hFt] at hRemap; injection hRemap with hT'; rw [← hT']
                dsimp [PruneStateRel, PruneFrameRel]
                exact ⟨⟨hDef, rfl, rfl, fun h => False.elim (h hD), fun _ => hFt⟩, rfl, hStack⟩
            | unreachable =>
              rw [hTerm] at hRemap; dsimp [remapTerminator] at hRemap
              injection hRemap with hT'; rw [← hT']
            | unsupported =>
              rw [hTerm] at hRemap; dsimp [remapTerminator] at hRemap
              injection hRemap with hT'; rw [← hT']
            | return_ =>
              rw [hTerm] at hRemap; dsimp [remapTerminator] at hRemap
              injection hRemap with hT'; rw [← hT']
              dsimp
              cases bb.cleanup with
              | true => exact rfl
              | false =>
                dsimp
                cases Trusted.MirSemantics.getElem? f₁.locals 0 with
                | none => exact rfl
                | some sl =>
                  cases sl with
                  | dead => exact rfl
                  | live ov =>
                    cases ov with
                    | none => exact rfl
                    | some rv =>
                      cases hStack with
                      | nil => exact rfl
                      | cons hCont hSub =>
                        exact prune_returnToCaller hGetB hSetB ent rv m₁ hCont hSub
            | unwindResume =>
              rw [hTerm] at hRemap; dsimp [remapTerminator] at hRemap
              injection hRemap with hT'; rw [← hT']
              dsimp
              cases !bb.cleanup with
              | true => exact rfl
              | false =>
                dsimp
                exact prune_dispatchUnwindStack hGetB hComp hSetB ent m₁ hStack
            | switchInt discr targets =>
              rw [hTerm] at hRemap; dsimp [remapTerminator] at hRemap
              cases hFo : findNewBbIdx targets.otherwise 0 keepBlocks with
              | none => rw [hFo] at hRemap; cases hRemap
              | some oth' =>
                rw [hFo] at hRemap
                cases hFb : remapSwitchBranches keepBlocks targets.branches with
                | none => rw [hFb] at hRemap; cases hRemap
                | some brs' =>
                  rw [hFb] at hRemap; injection hRemap with hT'; rw [← hT']
                  dsimp
                  cases evalPrimitiveOperand body.locals f₁.locals discr with
                  | error _ => exact rfl
                  | ok pair =>
                    cases pair with
                    | mk dv la =>
                      cases dv with
                      | scalar sv =>
                        dsimp
                        have hSw := evalSwitchBranches_remap keepBlocks sv.width sv.bits hFo hFb
                        cases hE1 : evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches with
                        | error k₁ =>
                          rw [hE1] at hSw
                          cases hE2 : evalSwitchBranches sv.width sv.bits oth' brs' with
                          | error k₂ => rw [hE2] at hSw; dsimp at hSw; exact hSw
                          | ok _ => rw [hE2] at hSw; exact False.elim hSw
                        | ok t₁ =>
                          rw [hE1] at hSw
                          cases hE2 : evalSwitchBranches sv.width sv.bits oth' brs' with
                          | error _ => rw [hE2] at hSw; exact False.elim hSw
                          | ok t₂ =>
                            rw [hE2] at hSw; dsimp at hSw
                            dsimp [PruneStateRel, PruneFrameRel]
                            exact ⟨⟨hDef, rfl, rfl, fun h => False.elim (h hD), fun _ => hSw⟩, rfl, hStack⟩
                      | bool bv =>
                        dsimp
                        have hSw := evalBoolSwitchBranches_remap keepBlocks bv hFo hFb
                        cases hE1 : evalBoolSwitchBranches bv targets.otherwise targets.branches with
                        | error k₁ =>
                          rw [hE1] at hSw
                          cases hE2 : evalBoolSwitchBranches bv oth' brs' with
                          | error k₂ => rw [hE2] at hSw; dsimp at hSw; exact hSw
                          | ok _ => rw [hE2] at hSw; exact False.elim hSw
                        | ok t₁ =>
                          rw [hE1] at hSw
                          cases hE2 : evalBoolSwitchBranches bv oth' brs' with
                          | error _ => rw [hE2] at hSw; exact False.elim hSw
                          | ok t₂ =>
                            rw [hE2] at hSw; dsimp at hSw
                            dsimp [PruneStateRel, PruneFrameRel]
                            exact ⟨⟨hDef, rfl, rfl, fun h => False.elim (h hD), fun _ => hSw⟩, rfl, hStack⟩
                      | unit | ptr _ | enumVal _ _ | tuple _ | bytes _ => exact rfl
            | assert cond expected msg t₁ u₁ =>
              rw [hTerm] at hRemap; dsimp [remapTerminator] at hRemap
              cases hFt : findNewBbIdx t₁ 0 keepBlocks with
              | none => rw [hFt] at hRemap; cases hRemap
              | some t₂ =>
                rw [hFt] at hRemap
                cases hFu : remapUnwindAction keepBlocks u₁ with
                | none => rw [hFu] at hRemap; cases hRemap
                | some u₂ =>
                  rw [hFu] at hRemap; injection hRemap with hT'; rw [← hT']
                  dsimp
                  cases evalPrimitiveOperand body.locals f₁.locals cond with
                  | error _ => exact rfl
                  | ok pair =>
                    cases pair with
                    | mk v la =>
                      cases v with
                      | bool bv =>
                        dsimp
                        cases boolEq bv expected with
                        | true =>
                          dsimp [PruneStateRel, PruneFrameRel]
                          exact ⟨⟨hDef, rfl, rfl, fun h => False.elim (h hD), fun _ => hFt⟩, rfl, hStack⟩
                        | false =>
                          dsimp [dispatchLocalUnwind]
                          cases hU1 : u₁ with
                          | continue_ =>
                            rw [hU1] at hFu; dsimp [remapUnwindAction] at hFu
                            injection hFu with hU2; rw [← hU2]
                            exact prune_dispatchUnwindStack hGetB hComp hSetB ent m₁ hStack
                          | unreachable =>
                            rw [hU1] at hFu; dsimp [remapUnwindAction] at hFu
                            injection hFu with hU2; rw [← hU2]
                          | terminate =>
                            rw [hU1] at hFu; dsimp [remapUnwindAction] at hFu
                            injection hFu with hU2; rw [← hU2]
                          | cleanup pad₁ =>
                            rw [hU1] at hFu; dsimp [remapUnwindAction] at hFu
                            cases hFp : findNewBbIdx pad₁ 0 keepBlocks with
                            | none => rw [hFp] at hFu; cases hFu
                            | some pad₂ =>
                              rw [hFp] at hFu; injection hFu with hU2; rw [← hU2]
                              exact prune_enterCleanup hGetB hComp hSetB ent m₁ pad₁ pad₂
                                ⟨hDef, hStmt, rfl, fun h => False.elim (h hD), fun _ => hFind⟩
                                hStack (fun h => False.elim (h hD)) (fun _ => hFp)
                      | scalar _ | unit | ptr _ | enumVal _ _ | tuple _ | bytes _ => exact rfl
            | call cDef args dst tOpt₁ u₁ =>
              rw [hTerm] at hRemap; dsimp [remapTerminator] at hRemap
              cases hFu : remapUnwindAction keepBlocks u₁ with
              | none =>
                rw [hFu] at hRemap
                cases tOpt₁ with
                | none => cases hRemap
                | some t =>
                  dsimp at hRemap
                  cases hFt : findNewBbIdx t 0 (0 :: keepTail) <;> (rw [hFt] at hRemap; cases hRemap)
              | some u₂ =>
                have hCallGoal : ∀ tOpt₂,
                    ((tOpt₁ = none ∧ tOpt₂ = none) ∨
                      ∃ t₁ t₂, tOpt₁ = some t₁ ∧ tOpt₂ = some t₂ ∧ findNewBbIdx t₁ 0 keepBlocks = some t₂) →
                    term' = .call cDef args dst tOpt₂ u₂ →
                    match
                      ((match evalCallArgsUnw body.locals f₁.locals args with
                        | .error k => .fault k
                        | .ok (av, la) =>
                          match Trusted.MirSemantics.getElem? p.bodies cDef with
                          | none => .fault .unsupported
                          | some cb =>
                            match initCalleeFrameUnw cDef cb av with
                            | .error k => .fault k
                            | .ok cf =>
                              .step ⟨cf, { callerFrame := { f₁ with locals := la }, dst, target := tOpt₁, unwind := u₁ } :: cs₁, m₁⟩) : StepResult UnwindState UnwindOut),
                      ((match evalCallArgsUnw body.locals f₁.locals args with
                        | .error k => .fault k
                        | .ok (av, la) =>
                          match Trusted.MirSemantics.getElem? bodies' cDef with
                          | none => .fault .unsupported
                          | some cb =>
                            match initCalleeFrameUnw cDef cb av with
                            | .error k => .fault k
                            | .ok cf =>
                              .step ⟨cf, { callerFrame := { f₂ with locals := la }, dst, target := tOpt₂, unwind := u₂ } :: cs₂, m₁⟩) : StepResult UnwindState UnwindOut) with
                    | .step s₁', .step s₂' => PruneStateRel defId keepBlocks s₁' s₂'
                    | .done o₁, .done o₂ => o₁ = o₂
                    | .fault k₁, .fault k₂ => k₁ = k₂
                    | _, _ => False := by
                  intro tOpt₂ hTgtRel _
                  cases evalCallArgsUnw body.locals f₁.locals args with
                  | error _ => exact rfl
                  | ok pair =>
                    dsimp
                    cases hEqC : Nat.beq cDef defId with
                    | false =>
                      rw [setElem?_getElem?_ne hSetB (nat_ne_of_beq_false hEqC)]
                      cases Trusted.MirSemantics.getElem? p.bodies cDef with
                      | none => exact rfl
                      | some cb =>
                        dsimp
                        cases hIC : initCalleeFrameUnw cDef cb pair.1 with
                        | error _ => exact rfl
                        | ok cf =>
                          have hCd := initCalleeFrameUnw_defId hIC
                          have hCb : cf.blockIdx = 0 := by
                            unfold initCalleeFrameUnw at hIC
                            cases h1 : cb.basicBlocks.isEmpty <;> rw [h1] at hIC
                            · dsimp at hIC
                              cases h2 : (!Nat.blt cb.argumentCount cb.locals.length) <;> rw [h2] at hIC
                              · dsimp at hIC
                                cases h3 : (!storageAnnotationsInBounds cb) <;> rw [h3] at hIC
                                · dsimp at hIC
                                  cases h4 : (!cb.locals.all isSupportedScalarOrUnitTy) <;> rw [h4] at hIC
                                  · dsimp at hIC
                                    cases h5 : (!checkArgsMatch pair.1 ((cb.locals.drop 1).take cb.argumentCount)) <;> rw [h5] at hIC
                                    · dsimp at hIC; injection hIC with he; rw [← he]
                                    · cases hIC
                                  · cases hIC
                                · cases hIC
                              · cases hIC
                            · cases hIC
                          dsimp [PruneStateRel]
                          refine ⟨hInitFrameRel cDef cf hCd hCb, rfl, PruneStackRel.cons ?_ hStack⟩
                          exact ⟨⟨hDef, hStmt, rfl, fun h => False.elim (h hD), fun _ => hFind⟩,
                            rfl, fun h => False.elim (h hD), fun _ => ⟨hTgtRel, hFu⟩⟩
                    | true =>
                      have hC := nat_beq_eq hEqC
                      rw [hC, hGetB, setElem?_getElem?_same hSetB]
                      dsimp
                      rw [hInitCalleeEq pair.1]
                      cases hIC : initCalleeFrameUnw defId body pair.1 with
                      | error _ => exact rfl
                      | ok cf =>
                        have hCd := initCalleeFrameUnw_defId hIC
                        have hCb : cf.blockIdx = 0 := by
                          unfold initCalleeFrameUnw at hIC
                          cases h1 : body.basicBlocks.isEmpty <;> rw [h1] at hIC
                          · dsimp at hIC
                            cases h2 : (!Nat.blt body.argumentCount body.locals.length) <;> rw [h2] at hIC
                            · dsimp at hIC
                              cases h3 : (!storageAnnotationsInBounds body) <;> rw [h3] at hIC
                              · dsimp at hIC
                                cases h4 : (!body.locals.all isSupportedScalarOrUnitTy) <;> rw [h4] at hIC
                                · dsimp at hIC
                                  cases h5 : (!checkArgsMatch pair.1 ((body.locals.drop 1).take body.argumentCount)) <;> rw [h5] at hIC
                                  · dsimp at hIC; injection hIC with he; rw [← he]
                                  · cases hIC
                                · cases hIC
                              · cases hIC
                            · cases hIC
                          · cases hIC
                        dsimp [PruneStateRel]
                        refine ⟨hInitFrameRel defId cf hCd hCb, rfl, PruneStackRel.cons ?_ hStack⟩
                        exact ⟨⟨hDef, hStmt, rfl, fun h => False.elim (h hD), fun _ => hFind⟩,
                          rfl, fun h => False.elim (h hD), fun _ => ⟨hTgtRel, hFu⟩⟩
                cases hTO : tOpt₁ with
                | none =>
                  rw [hTO, hFu] at hRemap; dsimp at hRemap
                  injection hRemap with hT'
                  rw [← hT']
                  dsimp
                  have hG := hCallGoal none (Or.inl ⟨hTO, rfl⟩) hT'.symm
                  rw [hTO] at hG
                  exact hG
                | some t₁ =>
                  rw [hTO, hFu] at hRemap; dsimp at hRemap
                  cases hFt : findNewBbIdx t₁ 0 keepBlocks with
                  | none => rw [hFt] at hRemap; cases hRemap
                  | some t₂ =>
                    rw [hFt] at hRemap; dsimp at hRemap
                    injection hRemap with hT'
                    rw [← hT']
                    dsimp
                    have hG := hCallGoal (some t₂) (Or.inr ⟨t₁, t₂, hTO, rfl, hFt⟩) hT'.symm
                    rw [hTO] at hG
                    exact hG

private theorem pruneDeadCleanupBlocks_sound_slice2 (pSrc pTgt : Program)
    (defId : DefId) (keepBlocks : List BasicBlockId)
    (hCheck : checkPruneDeadCleanupBlocks pSrc defId keepBlocks pTgt = true) :
    ProgramEquivUnw pSrc pTgt := by
  unfold checkPruneDeadCleanupBlocks applyPruneDeadCleanupBlocks at hCheck
  cases hGetB : Trusted.MirSemantics.getElem? pSrc.bodies defId with
  | none => rw [hGetB] at hCheck; cases hCheck
  | some body =>
    rw [hGetB] at hCheck; dsimp at hCheck
    cases hBound : isStrictSortedBounded body.basicBlocks.length none keepBlocks with
    | false => rw [hBound] at hCheck; cases hCheck
    | true =>
      rw [hBound] at hCheck; dsimp at hCheck
      cases keepBlocks with
      | nil => cases hCheck
      | cons k0 keepTail =>
        cases k0 with
        | succ _ => cases hCheck
        | zero =>
          dsimp at hCheck
          cases hComp : compactKeepBlocks body.basicBlocks (0 :: keepTail) (0 :: keepTail) with
          | none => rw [hComp] at hCheck; cases hCheck
          | some bbs' =>
            rw [hComp] at hCheck; dsimp at hCheck
            cases hSb : boolEq (storageAnnotationsInBounds body) (storageAnnotationsInBounds { body with basicBlocks := bbs' }) with
            | false => rw [hSb] at hCheck; cases hCheck
            | true =>
              rw [hSb] at hCheck
              cases hAllHas : allLocalsStorageAnnotEq body { body with basicBlocks := bbs' } body.locals.length with
              | false => rw [hAllHas] at hCheck; cases hCheck
              | true =>
                rw [hAllHas] at hCheck; dsimp at hCheck
                cases hSetB : setElem? pSrc.bodies defId { body with basicBlocks := bbs' } with
                | none => rw [hSetB] at hCheck; cases hCheck
                | some bodies' =>
                  rw [hSetB] at hCheck; dsimp at hCheck
                  have hPOut : ({ pSrc with bodies := bodies' } : Program) = pTgt :=
                    programEq_eq hCheck
                  subst hPOut
                  have hSbEq : storageAnnotationsInBounds body =
                      storageAnnotationsInBounds { body with basicBlocks := bbs' } :=
                    boolEq_eq hSb
                  have hBbsNonEmpty : bbs'.isEmpty = body.basicBlocks.isEmpty := by
                    have h0Lt : 0 < body.basicBlocks.length := by
                      dsimp [isStrictSortedBounded] at hBound
                      exact nat_blt_lt (bool_and_true hBound).1
                    cases hOrig : body.basicBlocks with
                    | nil => rw [hOrig] at h0Lt; exact False.elim (Nat.not_lt_zero 0 h0Lt)
                    | cons _ _ =>
                      have hC := hComp
                      dsimp [compactKeepBlocks] at hC
                      rw [hOrig] at hC
                      dsimp [Trusted.MirSemantics.getElem?] at hC
                      cases hRm : remapTerminator (0 :: keepTail) _ with
                      | none => rw [hRm] at hC; cases hC
                      | some _ =>
                        rw [hRm] at hC
                        cases hCr : compactKeepBlocks _ _ keepTail with
                        | none => rw [hCr] at hC; cases hC
                        | some _ => rw [hCr] at hC; injection hC with hEq; rw [← hEq]; rfl
                  have hSemEntry : ∀ ent : DefId,
                      FullSemanticEquivUnw { pSrc with entryDefId := ent }
                        { pSrc with bodies := bodies', entryDefId := ent } := by
                    intro ent
                    have hInitEq : ∀ q,
                        initStateUnw { pSrc with bodies := bodies', entryDefId := ent } q =
                          initStateUnw { pSrc with entryDefId := ent } q := by
                      intro q
                      unfold initStateUnw
                      cases hEqD : Nat.beq ent defId with
                      | false =>
                        have hBase : initState { pSrc with bodies := bodies', entryDefId := ent } q =
                            initState { pSrc with entryDefId := ent } q := by
                          unfold initState; dsimp
                          rw [setElem?_getElem?_ne hSetB (nat_ne_of_beq_false hEqD)]
                        rw [hBase]
                      | true =>
                        have hD := nat_beq_eq hEqD
                        have hBase : initState { pSrc with bodies := bodies', entryDefId := ent } q =
                            initState { pSrc with entryDefId := ent } q :=
                          @initState_congr_body
                            { pSrc with bodies := bodies', entryDefId := ent }
                            { pSrc with entryDefId := ent }
                            { body with basicBlocks := bbs' } body rfl rfl
                            (by rw [hD]; exact setElem?_getElem?_same hSetB)
                            (by rw [hD]; exact hGetB)
                            rfl hBbsNonEmpty rfl rfl hSbEq.symm
                            (fun loc hLt => (allLocalsStorageAnnotEq_sound body { body with basicBlocks := bbs' }
                              body.locals.length loc hAllHas hLt).symm) q
                        rw [hBase]
                    exact fullSemanticEquivUnw_of_lockstep (PruneStateRel defId (0 :: keepTail))
                      (fun q k => by rw [hInitEq q])
                      (fun q s₁ s₂ h1 h2 => by
                        rw [hInitEq q] at h2; rw [h1] at h2; injection h2 with hEq; subst hEq
                        let ⟨hCs, _⟩ := initStateUnw_entryDefId h1
                        have hBb0 : s₁.active.blockIdx = 0 := by
                          let ⟨_, hBase⟩ := (initStateUnw_ok_iff _ q s₁).mp h1
                          unfold initState at hBase
                          cases h1' : (!Nat.beq pSrc.pointerWidthBits 64 || !Nat.beq pSrc.mirProfileVersion 1) <;> rw [h1'] at hBase
                          · dsimp at hBase
                            cases h2' : (!q.callerMem.allocations.isEmpty) <;> rw [h2'] at hBase
                            · dsimp at hBase
                              cases h3' : Trusted.MirSemantics.getElem? pSrc.bodies ent with
                              | none => rw [h3'] at hBase; cases hBase
                              | some b0 =>
                                rw [h3'] at hBase; dsimp at hBase
                                cases h4' : b0.basicBlocks.isEmpty <;> rw [h4'] at hBase
                                · dsimp at hBase
                                  cases h5' : (!Nat.blt b0.argumentCount b0.locals.length) <;> rw [h5'] at hBase
                                  · dsimp at hBase
                                    cases h6' : (!storageAnnotationsInBounds b0) <;> rw [h6'] at hBase
                                    · dsimp at hBase
                                      cases h7' : (!b0.locals.all isSupportedScalarOrUnitTy) <;> rw [h7'] at hBase
                                      · dsimp at hBase
                                        cases h8' : (!checkArgsMatch q.args ((b0.locals.drop 1).take b0.argumentCount)) <;> rw [h8'] at hBase
                                        · dsimp at hBase
                                          injection hBase with ha; injection ha with hb; injection hb with hc
                                          rw [← hc]
                                        · cases hBase
                                      · cases hBase
                                    · cases hBase
                                  · cases hBase
                                · cases hBase
                            · cases hBase
                          · cases hBase
                        refine ⟨⟨rfl, rfl, rfl, fun _ => rfl, fun _ => by rw [hBb0]; rfl⟩, rfl, ?_⟩
                        rw [hCs]; exact PruneStackRel.nil)
                      (fun s₁ s₂ s₁' hRel hSt => by
                        have hSR := prune_step_rel hGetB hBound hComp hSbEq hAllHas hSetB ent hRel
                        rw [hSt] at hSR
                        cases hEv2 : evalStepUnw { pSrc with bodies := bodies', entryDefId := ent } 0 s₂ with
                        | step s₂' => rw [hEv2] at hSR; exact ⟨s₂', rfl, hSR⟩
                        | done _ => rw [hEv2] at hSR; exact False.elim hSR
                        | fault _ => rw [hEv2] at hSR; exact False.elim hSR)
                      (fun s₁ s₂ out hRel hD => by
                        have hSR := prune_step_rel hGetB hBound hComp hSbEq hAllHas hSetB ent hRel
                        rw [hD] at hSR
                        cases hEv2 : evalStepUnw { pSrc with bodies := bodies', entryDefId := ent } 0 s₂ with
                        | done o₂ => rw [hEv2] at hSR; dsimp at hSR; rw [← hSR]
                        | step _ => rw [hEv2] at hSR; exact False.elim hSR
                        | fault _ => rw [hEv2] at hSR; exact False.elim hSR)
                      (fun s₁ s₂ k hRel hF => by
                        have hSR := prune_step_rel hGetB hBound hComp hSbEq hAllHas hSetB ent hRel
                        rw [hF] at hSR
                        cases hEv2 : evalStepUnw { pSrc with bodies := bodies', entryDefId := ent } 0 s₂ with
                        | fault k₂ => rw [hEv2] at hSR; dsimp at hSR; rw [← hSR]
                        | step _ => rw [hEv2] at hSR; exact False.elim hSR
                        | done _ => rw [hEv2] at hSR; exact False.elim hSR)
                  refine ⟨(setElem?_length hSetB).symm, rfl, rfl, rfl, rfl,
                    (bodiesHaveUniqueIdentities_of_map_eq (map_identity_setElem? hGetB hSetB rfl)).symm,
                    hSemEntry pSrc.entryDefId, ?_⟩
                  intro d
                  cases hEqD : Nat.beq d defId with
                  | false =>
                    rw [setElem?_getElem?_ne hSetB (nat_ne_of_beq_false hEqD)]
                    cases Trusted.MirSemantics.getElem? pSrc.bodies d with
                    | none => exact True.intro
                    | some b => exact ⟨rfl, rfl, rfl, fun _ => Iff.rfl, hSemEntry d⟩
                  | true =>
                    have hD := nat_beq_eq hEqD
                    rw [hD, hGetB, setElem?_getElem?_same hSetB]
                    refine ⟨rfl, rfl, ?_, fun _ => Iff.rfl, hSemEntry defId⟩
                    unfold BodyStaticAdmitted
                    dsimp
                    rw [hBbsNonEmpty, ← hSbEq]

/-! ### Slice: Slice3a_InlineHelpers.lean -/

-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.




/-! ### Part 1: List, `replicateDead`, `setElem?` Append, & Prefix/Suffix Helpers -/

private noncomputable def replicateDead : Nat → List LocalSlot
  | 0 => []
  | n + 1 => .dead :: replicateDead n

private theorem replicateDead_length : ∀ n, (replicateDead n).length = n
  | 0 => rfl
  | n + 1 => congrArg Nat.succ (replicateDead_length n)

private theorem getElem?_replicateDead :
    ∀ {n i : Nat}, i < n →
      Trusted.MirSemantics.getElem? (replicateDead n) i = some .dead
  | 0, _, h => False.elim (Nat.not_lt_zero _ h)
  | _ + 1, 0, _ => rfl
  | n + 1, i + 1, h => @getElem?_replicateDead n i (Nat.lt_of_succ_lt_succ h)

private theorem list_length_append {α : Type} :
    ∀ (xs ys : List α), (xs ++ ys).length = xs.length + ys.length
  | [], _ => by dsimp [List.length]; rw [Nat.zero_add]
  | _ :: xs, ys => by
    dsimp [List.length]
    rw [list_length_append xs ys, Nat.succ_add]

private theorem list_any_append {α : Type} (p : α → Bool) :
    ∀ (xs ys : List α), (xs ++ ys).any p = (xs.any p || ys.any p)
  | [], ys => by dsimp [List.any]; cases ys.any p <;> rfl
  | x :: xs, ys => by
    dsimp [List.any]
    rw [list_any_append p xs ys]
    cases p x <;> cases xs.any p <;> cases ys.any p <;> rfl

private theorem setElem?_append_left {α : Type} :
    ∀ {xs : List α} (ys : List α) {i : Nat} (v : α),
      i < xs.length →
      setElem? (xs ++ ys) i v =
        match setElem? xs i v with
        | some xs' => some (xs' ++ ys)
        | none => none
  | [], _, _, _, h => False.elim (Nat.not_lt_zero _ h)
  | _ :: _, _, 0, _, _ => rfl
  | x :: xs, ys, i + 1, v, h => by
    dsimp [setElem?]
    rw [@setElem?_append_left α xs ys i v (Nat.lt_of_succ_lt_succ h)]
    cases setElem? xs i v <;> rfl

private theorem setElem?_append_right {α : Type} :
    ∀ (xs ys : List α) (j : Nat) (v : α),
      setElem? (xs ++ ys) (xs.length + j) v =
        match setElem? ys j v with
        | some ys' => some (xs ++ ys')
        | none => none
  | [], ys, j, v => by
    dsimp [List.length]; rw [Nat.zero_add]
    cases setElem? ys j v <;> rfl
  | x :: xs, ys, j, v => by
    dsimp [List.length]; rw [Nat.succ_add]
    dsimp [setElem?]
    rw [setElem?_append_right xs ys j v]
    cases setElem? ys j v <;> rfl

private theorem setElem?_append_right_comm {α : Type} (xs ys : List α) (j : Nat) (v : α) :
    setElem? (xs ++ ys) (j + xs.length) v =
      match setElem? ys j v with
      | some ys' => some (xs ++ ys')
      | none => none := by
  rw [Nat.add_comm]
  exact setElem?_append_right xs ys j v

private theorem list_drop_append_left {α : Type} :
    ∀ (n : Nat) (xs ys : List α),
      n ≤ xs.length →
      (xs ++ ys).drop n = xs.drop n ++ ys
  | 0, _, _, _ => rfl
  | _ + 1, [], _, h => False.elim (Nat.not_succ_le_zero _ h)
  | n + 1, _ :: xs, ys, h =>
    list_drop_append_left n xs ys (Nat.le_of_succ_le_succ h)

private theorem list_take_append_left {α : Type} :
    ∀ (n : Nat) (xs ys : List α),
      n ≤ xs.length →
      (xs ++ ys).take n = xs.take n
  | 0, _, _, _ => rfl
  | _ + 1, [], _, h => False.elim (Nat.not_succ_le_zero _ h)
  | n + 1, x :: xs, ys, h => by
    dsimp [List.take]
    rw [list_take_append_left n xs ys (Nat.le_of_succ_le_succ h)]

private theorem list_length_drop {α : Type} :
    ∀ (n : Nat) (xs : List α), (xs.drop n).length = xs.length - n
  | 0, _ => rfl
  | n + 1, [] => by dsimp [List.drop, List.length]; exact (Nat.zero_sub (n + 1)).symm
  | n + 1, _ :: xs => by
    dsimp [List.drop, List.length]
    rw [Nat.succ_sub_succ]
    exact list_length_drop n xs

private theorem list_length_take {α : Type} :
    ∀ (n : Nat) (xs : List α), n ≤ xs.length → (xs.take n).length = n
  | 0, _, _ => rfl
  | _ + 1, [], h => False.elim (Nat.not_succ_le_zero _ h)
  | n + 1, _ :: xs, h => by
    dsimp [List.take, List.length]
    exact congrArg Nat.succ (list_length_take n xs (Nat.le_of_succ_le_succ h))

private theorem list_getElem?_drop {α : Type} :
    ∀ (n : Nat) (xs : List α) (i : Nat),
      Trusted.MirSemantics.getElem? (xs.drop n) i =
        Trusted.MirSemantics.getElem? xs (n + i)
  | 0, _, i => by dsimp [List.drop]; rw [Nat.zero_add]
  | _ + 1, [], _ => rfl
  | n + 1, _ :: xs, i => by
    dsimp [List.drop]; rw [Nat.succ_add]
    exact list_getElem?_drop n xs i

private theorem list_getElem?_take_lt {α : Type} :
    ∀ {n i : Nat} (xs : List α),
      i < n →
      Trusted.MirSemantics.getElem? (xs.take n) i =
        Trusted.MirSemantics.getElem? xs i
  | 0, _, _, h => False.elim (Nat.not_lt_zero _ h)
  | _ + 1, _, [], _ => rfl
  | _ + 1, 0, _ :: _, _ => rfl
  | n + 1, i + 1, _ :: xs, h =>
    @list_getElem?_take_lt α n i xs (Nat.lt_of_succ_lt_succ h)

private theorem paramTys_append_eq (caller callee : Body)
    (hArgLt : caller.argumentCount < caller.locals.length) :
    ((caller.locals ++ callee.locals).drop 1).take caller.argumentCount =
      (caller.locals.drop 1).take caller.argumentCount := by
  have h1Le : 1 ≤ caller.locals.length :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) hArgLt
  rw [list_drop_append_left 1 caller.locals callee.locals h1Le]
  have hArgLeDrop : caller.argumentCount ≤ (caller.locals.drop 1).length := by
    rw [list_length_drop]
    exact Nat.le_sub_of_add_le hArgLt
  exact list_take_append_left caller.argumentCount (caller.locals.drop 1) callee.locals hArgLeDrop

private theorem initLocalsLoop_length (body : Body) (args : List Val) :
    ∀ (idx : Nat) (rem : List MirTy),
      (initLocalsLoop body args idx rem).length = rem.length
  | _, [] => rfl
  | idx, _ :: rest =>
    congrArg Nat.succ (initLocalsLoop_length body args (idx + 1) rest)

private theorem initLocalsLoop_append (body : Body) (args : List Val) :
    ∀ (idx : Nat) (xs ys : List MirTy),
      initLocalsLoop body args idx (xs ++ ys) =
        initLocalsLoop body args idx xs ++
          initLocalsLoop body args (idx + xs.length) ys
  | idx, [], ys => by dsimp [List.length, initLocalsLoop]
  | idx, x :: xs, ys => by
    dsimp [List.length, initLocalsLoop]
    rw [initLocalsLoop_append body args (idx + 1) xs ys]
    have hEq : idx + 1 + xs.length = idx + (xs.length + 1) := by
      rw [Nat.add_assoc, Nat.add_comm 1 xs.length]
    rw [hEq]

/-! ### Part 2: `FrameWellTyped` & `FrameStmtInBounds` Reachable Invariants -/

private theorem enumTy_beq_refl (e : EnumTy) : EnumTy.beq e e = true := by
  cases e with
  | mk id w s tr ds =>
    unfold EnumTy.beq
    have h1 : Nat.beq id id = true := nat_beq_refl id
    have h2 : IntWidth.beq w w = true := by cases w <;> rfl
    have h3 : (s == s) = true := by cases s <;> rfl
    have h4 : EnumTagRepr.beq tr tr = true := by
      cases tr with
      | zeroSized => rfl
      | scalar tw ts =>
        dsimp [EnumTagRepr.beq]
        have ha : IntWidth.beq tw tw = true := by cases tw <;> rfl
        have hb : (ts == ts) = true := by cases ts <;> rfl
        rw [ha, hb]; rfl
    have h5 : natListBeq ds ds = true := by
      induction ds with
      | nil => rfl
      | cons d rest ih =>
        dsimp [natListBeq]; rw [nat_beq_refl d, ih]; rfl
    rw [h1, h2, h3, h4, h5]; rfl

mutual
  private theorem mirTy_beq_refl : ∀ (t : MirTy), MirTy.beq t t = true
    | .bool | .unit | .never | .unsupported => rfl
    | .int w s => by
      dsimp [MirTy.beq]
      have h1 : IntWidth.beq w w = true := by cases w <;> rfl
      have h2 : (s == s) = true := by cases s <;> rfl
      rw [h1, h2]; rfl
    | .enum e => enumTy_beq_refl e
    | .ref m p => by
      dsimp [MirTy.beq]
      have h1 : Mutability.beq m m = true := by cases m <;> rfl
      rw [h1, mirTy_beq_refl p]; rfl
    | .rawPtr m p => by
      dsimp [MirTy.beq]
      have h1 : Mutability.beq m m = true := by cases m <;> rfl
      rw [h1, mirTy_beq_refl p]; rfl
    | .tuple fs => mirTy_beqList_refl fs

  private theorem mirTy_beqList_refl : ∀ (fs : List MirTy), MirTy.beqList fs fs = true
    | [] => rfl
    | x :: xs => by
      dsimp [MirTy.beqList]
      rw [mirTy_beq_refl x, mirTy_beqList_refl xs]; rfl
end

private theorem enumAdmitted_nonEmpty {e : EnumTy} (h : enumAdmitted e = true) :
    Nat.blt 0 e.discriminants.length = true := by
  unfold enumAdmitted at h
  let ⟨h1234, _⟩ := bool_and_true h
  let ⟨h123, _⟩ := bool_and_true h1234
  let ⟨h12, _⟩ := bool_and_true h123
  let ⟨hNe, _⟩ := bool_and_true h12
  cases hd : e.discriminants with
  | nil => rw [hd] at hNe; cases hNe
  | cons _ _ => rfl

private theorem findDiscrVariantAux_lt (discrBits : BitVec 128) :
    ∀ (idx : Nat) (ds : List Nat) (v : Nat),
      findDiscrVariantAux idx discrBits ds = some v →
      v < idx + ds.length
  | _, [], _, h => by cases h
  | idx, d :: ds, v, h => by
    dsimp [findDiscrVariantAux] at h
    cases hc : (BitVec.ofNat 128 d == discrBits) with
    | true =>
      rw [hc] at h; dsimp at h; injection h with hv; subst hv
      dsimp [List.length]
      exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ ds.length)
    | false =>
      rw [hc] at h; dsimp at h
      have hLt := findDiscrVariantAux_lt discrBits (idx + 1) ds v h
      have hEq : idx + 1 + ds.length = idx + (ds.length + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 ds.length]
      rw [hEq] at hLt
      exact hLt

private theorem checkVal_liveUninitSlot {ty : MirTy} {v : Val}
    (h : liveUninitSlot ty = .live (some v)) : checkVal v ty = true := by
  cases ty with
  | unit =>
    dsimp [liveUninitSlot] at h
    injection h with h1; injection h1 with hv; subst hv; rfl
  | enum ety =>
    dsimp [liveUninitSlot] at h
    cases hz : isZstEnumTy ety with
    | false => rw [hz] at h; cases h
    | true =>
      rw [hz] at h; dsimp at h
      injection h with h1; injection h1 with hv; subst hv
      have hAdm : enumAdmitted ety = true := by
        unfold isZstEnumTy at hz
        cases htr : ety.tagRepr with
        | scalar _ _ => rw [htr] at hz; cases hz
        | zeroSized => rw [htr] at hz; exact hz
      unfold checkVal Val.ty?
      dsimp
      rw [hAdm, enumAdmitted_nonEmpty hAdm]
      dsimp
      exact enumTy_beq_refl ety
  | bool | int _ _ | never | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
    dsimp [liveUninitSlot] at h; cases h

private theorem evalConstLit_checkVal {ty : MirTy} {lit : ConstLit} {v : Val}
    (h : evalConstLit ty lit = .ok v) : checkVal v ty = true := by
  cases ty with
  | int w s =>
    cases lit with
    | zeroSized => cases h
    | scalar bits =>
      dsimp [evalConstLit] at h
      cases hc : (truncateBits w bits != bits) <;> rw [hc] at h
      · dsimp at h
        injection h with hv; subst hv
        have hEqB : truncateBits w bits = bits := by
          have hBeq : (truncateBits w bits == bits) = true := by
            unfold bne at hc
            exact bool_not_false hc
          exact eq_of_beq hBeq
        have hWf : ScalarVal.wf { width := w, signed := s, bits := bits } = true := by
          unfold ScalarVal.wf
          unfold bne at hc
          exact bool_not_false hc
        unfold checkVal Val.ty?
        dsimp
        rw [hEqB, hWf]
        dsimp [MirTy.beq]
        have h1 : IntWidth.beq w w = true := by cases w <;> rfl
        have h2 : (s == s) = true := by cases s <;> rfl
        rw [h1, h2]; rfl
      · cases h
  | bool =>
    cases lit with
    | zeroSized => cases h
    | scalar bits =>
      dsimp [evalConstLit] at h
      cases hc : (truncateBits .i8 bits != bits) <;> rw [hc] at h
      · dsimp at h
        cases h0 : (UInt8.ofNat (truncateBits .i8 bits).toNat == 0) <;> rw [h0] at h
        · dsimp at h
          cases h1 : (UInt8.ofNat (truncateBits .i8 bits).toNat == 1) <;> rw [h1] at h
          · cases h
          · dsimp at h; injection h with hv; subst hv; rfl
        · dsimp at h; injection h with hv; subst hv; rfl
      · cases h
  | unit =>
    cases lit with
    | scalar _ => cases h
    | zeroSized =>
      dsimp [evalConstLit] at h; injection h with hv; subst hv; rfl
  | enum e =>
    cases lit with
    | zeroSized =>
      dsimp [evalConstLit] at h
      cases hz : isZstEnumTy e <;> rw [hz] at h
      · cases h
      · dsimp at h; injection h with hv; subst hv
        have hAdm : enumAdmitted e = true := by
          unfold isZstEnumTy at hz
          cases htr : e.tagRepr with
          | scalar _ _ => rw [htr] at hz; cases hz
          | zeroSized => rw [htr] at hz; exact hz
        unfold checkVal Val.ty?; dsimp
        rw [hAdm, enumAdmitted_nonEmpty hAdm]; dsimp
        exact enumTy_beq_refl e
    | scalar bits =>
      dsimp [evalConstLit] at h
      cases htr : e.tagRepr with
      | zeroSized => rw [htr] at h; cases h
      | scalar tagW tagS =>
        rw [htr] at h; dsimp at h
        cases hc : (!enumAdmitted e || truncateBits tagW bits != bits) <;> rw [hc] at h
        · dsimp at h
          have hAdm : enumAdmitted e = true := by
            cases ha : enumAdmitted e with
            | true => rfl
            | false => rw [ha] at hc; cases hc
          cases hf : findDiscrVariant? (tagBitsToDiscrBits tagW tagS e.discrWidth bits) e.discriminants with
          | none => rw [hf] at h; cases h
          | some idx =>
            rw [hf] at h; dsimp at h
            injection h with hv; subst hv
            have hIdxLt : idx < e.discriminants.length := by
              have hL := findDiscrVariantAux_lt _ 0 e.discriminants idx hf
              rw [Nat.zero_add] at hL; exact hL
            unfold checkVal Val.ty?; dsimp
            rw [hAdm, nat_lt_blt hIdxLt]; dsimp
            exact enumTy_beq_refl e
        · cases h
  | never | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
    cases lit <;> (dsimp [evalConstLit] at h; cases h)

/-- Reachable frame invariant: locals match body length, every live initialized
slot satisfies `checkVal`, and `stmtIdx ≤ bb.statements.length` whenever `blockIdx`
is in bounds. -/
private noncomputable def FrameWf (p : Program) (f : FrameState) : Prop :=
  ∀ body, Trusted.MirSemantics.getElem? p.bodies f.defId = some body →
    f.locals.length = body.locals.length ∧
    (∀ i ty v,
      Trusted.MirSemantics.getElem? body.locals i = some ty →
      Trusted.MirSemantics.getElem? f.locals i = some (.live (some v)) →
      checkVal v ty = true) ∧
    (∀ bb, Trusted.MirSemantics.getElem? body.basicBlocks f.blockIdx = some bb →
      f.stmtIdx ≤ bb.statements.length)

private theorem checkArgsMatch_getElem? :
    ∀ {args : List Val} {tys : List MirTy} {i : Nat} {v : Val} {ty : MirTy},
      checkArgsMatch args tys = true →
      Trusted.MirSemantics.getElem? args i = some v →
      Trusted.MirSemantics.getElem? tys i = some ty →
      checkVal v ty = true
  | [], [], _, _, _, _, ha, _ => by cases ha
  | [], _ :: _, _, _, _, h, _, _ => by cases h
  | _ :: _, [], _, _, _, h, _, _ => by cases h
  | a :: as, t :: ts, 0, v, ty, h, ha, ht => by
    dsimp [Trusted.MirSemantics.getElem?] at ha ht
    injection ha with hv; subst hv
    injection ht with hty; subst hty
    dsimp [checkArgsMatch] at h
    exact (bool_and_true h).1
  | _ :: as, _ :: ts, i + 1, v, ty, h, ha, ht => by
    dsimp [checkArgsMatch] at h
    exact checkArgsMatch_getElem? (bool_and_true h).2 ha ht

private theorem initLocalsLoop_wf (body : Body) (args : List Val)
    (hMatch : checkArgsMatch args ((body.locals.drop 1).take body.argumentCount) = true) :
    ∀ (idx : Nat) (rem : List MirTy) (k : Nat) (ty : MirTy) (v : Val),
      (∀ j t, Trusted.MirSemantics.getElem? rem j = some t →
        Trusted.MirSemantics.getElem? body.locals (idx + j) = some t) →
      Trusted.MirSemantics.getElem? rem k = some ty →
      Trusted.MirSemantics.getElem? (initLocalsLoop body args idx rem) k = some (.live (some v)) →
      checkVal v ty = true
  | _, [], _, _, _, _, ht, _ => by cases ht
  | idx, t0 :: rest, 0, ty, v, hAlign, ht, hs => by
    dsimp [Trusted.MirSemantics.getElem?] at ht hs
    injection ht with heq; subst heq
    dsimp [initLocalsLoop] at hs
    injection hs with hSlot
    cases h0 : Nat.beq idx 0 with
    | true =>
      rw [h0] at hSlot; dsimp at hSlot
      exact checkVal_liveUninitSlot hSlot
    | false =>
      rw [h0] at hSlot; dsimp at hSlot
      cases hLe : Nat.ble idx body.argumentCount with
      | true =>
        rw [hLe] at hSlot; dsimp at hSlot
        cases hGa : Trusted.MirSemantics.getElem? args (idx - 1) with
        | none => rw [hGa] at hSlot; cases hSlot
        | some av =>
          rw [hGa] at hSlot; dsimp at hSlot
          injection hSlot with hLive; injection hLive with hAv; subst hAv
          have hPos : 0 < idx := Nat.pos_of_ne_zero (nat_ne_of_beq_false h0)
          have hSubLt : idx - 1 < body.argumentCount := by
            cases idx with
            | zero => exact False.elim (Nat.not_lt_zero 0 hPos)
            | succ m => exact nat_ble_le hLe
          have hTyInParam :
              Trusted.MirSemantics.getElem? ((body.locals.drop 1).take body.argumentCount) (idx - 1) =
                some t0 := by
            rw [list_getElem?_take_lt _ hSubLt, list_getElem?_drop]
            have hEqIdx : 1 + (idx - 1) = idx := by
              rw [Nat.add_comm]; exact Nat.sub_add_cancel hPos
            rw [hEqIdx]
            have h0A := hAlign 0 t0 rfl
            rw [Nat.add_zero] at h0A
            exact h0A
          exact checkArgsMatch_getElem? hMatch hGa hTyInParam
      | false =>
        rw [hLe] at hSlot; dsimp at hSlot
        cases hHas : hasStorageAnnotation body idx with
        | true => rw [hHas] at hSlot; cases hSlot
        | false =>
          rw [hHas] at hSlot; dsimp at hSlot
          exact checkVal_liveUninitSlot hSlot
  | idx, _ :: rest, k + 1, ty, v, hAlign, ht, hs => by
    dsimp [Trusted.MirSemantics.getElem?] at ht hs
    exact initLocalsLoop_wf body args hMatch (idx + 1) rest k ty v
      (fun j t hj => by
        have hA := hAlign (j + 1) t hj
        have hEq : idx + (j + 1) = idx + 1 + j := by
          rw [Nat.add_assoc, Nat.add_comm 1 j]
        rw [← hEq]
        exact hA) ht hs

private theorem initCalleeFrameUnw_wf {p : Program} {d : DefId} {cb : Body}
    {av : List Val} {cf : FrameState}
    (hGet : Trusted.MirSemantics.getElem? p.bodies d = some cb)
    (hInit : initCalleeFrameUnw d cb av = .ok cf) :
    FrameWf p cf ∧ cf.defId = d ∧ cf.blockIdx = 0 ∧ cf.stmtIdx = 0 := by
  unfold initCalleeFrameUnw at hInit
  cases h1 : cb.basicBlocks.isEmpty <;> rw [h1] at hInit
  · dsimp at hInit
    cases h2 : (!Nat.blt cb.argumentCount cb.locals.length) <;> rw [h2] at hInit
    · dsimp at hInit
      cases h3 : (!storageAnnotationsInBounds cb) <;> rw [h3] at hInit
      · dsimp at hInit
        cases h4 : (!cb.locals.all isSupportedScalarOrUnitTy) <;> rw [h4] at hInit
        · dsimp at hInit
          cases h5 : (!checkArgsMatch av ((cb.locals.drop 1).take cb.argumentCount)) <;>
            rw [h5] at hInit
          · dsimp at hInit
            injection hInit with hCf; subst hCf
            have hMatch : checkArgsMatch av ((cb.locals.drop 1).take cb.argumentCount) = true :=
              bool_not_false h5
            refine ⟨?_, rfl, rfl, rfl⟩
            intro body hBod
            rw [hGet] at hBod; injection hBod with hBeq; subst hBeq
            refine ⟨initLocalsLoop_length cb av 0 cb.locals, ?_, fun _ _ => Nat.zero_le _⟩
            intro i ty v hTy hSl
            exact initLocalsLoop_wf cb av hMatch 0 cb.locals i ty v
              (fun j t hj => by rw [Nat.zero_add]; exact hj) hTy hSl
          · cases hInit
        · cases hInit
      · cases hInit
    · cases hInit
  · cases hInit

private theorem initStateUnw_wf {p : Program} {q : Query} {u₀ : UnwindState}
    (h : initStateUnw p q = .ok u₀) :
    FrameWf p u₀.active ∧ u₀.callStack = [] ∧ u₀.active.defId = p.entryDefId ∧
      u₀.active.blockIdx = 0 ∧ u₀.active.stmtIdx = 0 := by
  let ⟨hCs, hBase⟩ := (initStateUnw_ok_iff p q u₀).mp h
  unfold initState at hBase
  cases h1 : (!Nat.beq p.pointerWidthBits 64 || !Nat.beq p.mirProfileVersion 1) <;> rw [h1] at hBase
  · dsimp at hBase
    cases h2 : (!q.callerMem.allocations.isEmpty) <;> rw [h2] at hBase
    · dsimp at hBase
      cases h3 : Trusted.MirSemantics.getElem? p.bodies p.entryDefId with
      | none => rw [h3] at hBase; cases hBase
      | some body =>
        rw [h3] at hBase; dsimp at hBase
        cases h4 : body.basicBlocks.isEmpty <;> rw [h4] at hBase
        · dsimp at hBase
          cases h5 : (!Nat.blt body.argumentCount body.locals.length) <;> rw [h5] at hBase
          · dsimp at hBase
            cases h6 : (!storageAnnotationsInBounds body) <;> rw [h6] at hBase
            · dsimp at hBase
              cases h7 : (!body.locals.all isSupportedScalarOrUnitTy) <;> rw [h7] at hBase
              · dsimp at hBase
                cases h8 : (!checkArgsMatch q.args ((body.locals.drop 1).take body.argumentCount)) <;>
                  rw [h8] at hBase
                · dsimp at hBase
                  injection hBase with hStEq
                  injection hStEq with hFrEq _
                  injection hFrEq with hActEq
                  have hMatch : checkArgsMatch q.args ((body.locals.drop 1).take body.argumentCount) = true :=
                    bool_not_false h8
                  rw [← hActEq]
                  refine ⟨?_, hCs, rfl, rfl, rfl⟩
                  intro b2 hB2
                  rw [h3] at hB2; injection hB2 with hBeq; subst hBeq
                  refine ⟨initLocalsLoop_length body q.args 0 body.locals, ?_, fun _ _ => Nat.zero_le _⟩
                  intro i ty v hTy hSl
                  exact initLocalsLoop_wf body q.args hMatch 0 body.locals i ty v
                    (fun j t hj => by rw [Nat.zero_add]; exact hj) hTy hSl
                · cases hBase
              · cases hBase
            · cases hBase
          · cases hBase
        · cases hBase
    · cases hBase
  · cases hBase

private theorem evalOperandToSlot_wf {bodyLocals : List MirTy}
    {locals locs' : List LocalSlot} {op : Operand}
    {opTy : MirTy} {optVal : Option Val}
    (hLen : locals.length = bodyLocals.length)
    (hWt : ∀ i ty v,
      Trusted.MirSemantics.getElem? bodyLocals i = some ty →
      Trusted.MirSemantics.getElem? locals i = some (.live (some v)) →
      checkVal v ty = true)
    (hEv : evalOperandToSlot bodyLocals locals op = .ok (opTy, optVal, locs')) :
    locs'.length = bodyLocals.length ∧
    (∀ v, optVal = some v → checkVal v opTy = true) ∧
    (∀ i ty v,
      Trusted.MirSemantics.getElem? bodyLocals i = some ty →
      Trusted.MirSemantics.getElem? locs' i = some (.live (some v)) →
      checkVal v ty = true) := by
  cases op with
  | constant c =>
    dsimp [evalOperandToSlot] at hEv
    cases hc : evalConstLit c.ty c.lit with
    | error _ => rw [hc] at hEv; cases hEv
    | ok v =>
      rw [hc] at hEv; dsimp at hEv
      injection hEv with hTup
      injection hTup with hTyEq hRest
      injection hRest with hOptEq hLocEq
      subst hTyEq; subst hOptEq; subst hLocEq
      refine ⟨hLen, ?_, hWt⟩
      intro v2 hv2; injection hv2 with heq; subst heq
      exact evalConstLit_checkVal hc
  | copy pl =>
    dsimp [evalOperandToSlot] at hEv
    cases hp : (!pl.projection.isEmpty) <;> rw [hp] at hEv
    · dsimp at hEv
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals pl.localId with
      | none => rw [hTy] at hEv; cases hEv
      | some ty =>
        rw [hTy] at hEv
        cases hSl : Trusted.MirSemantics.getElem? locals pl.localId with
        | none => rw [hSl] at hEv; cases hEv
        | some sl =>
          rw [hSl] at hEv
          cases sl with
          | dead => cases hEv
          | live ov =>
            dsimp at hEv
            injection hEv with hTup
            injection hTup with hTyEq hRest
            injection hRest with hOptEq hLocEq
            subst hTyEq; subst hOptEq; subst hLocEq
            refine ⟨hLen, ?_, hWt⟩
            intro v hv; subst hv
            exact hWt pl.localId ty v hTy hSl
    · cases hEv
  | move pl =>
    dsimp [evalOperandToSlot] at hEv
    cases hp : (!pl.projection.isEmpty) <;> rw [hp] at hEv
    · dsimp at hEv
      cases hTy : Trusted.MirSemantics.getElem? bodyLocals pl.localId with
      | none => rw [hTy] at hEv; cases hEv
      | some ty =>
        rw [hTy] at hEv
        cases hSl : Trusted.MirSemantics.getElem? locals pl.localId with
        | none => rw [hSl] at hEv; cases hEv
        | some sl =>
          rw [hSl] at hEv
          cases sl with
          | dead => cases hEv
          | live ov =>
            dsimp at hEv
            cases hSet : setElem? locals pl.localId (liveUninitSlot ty) with
            | none => rw [hSet] at hEv; cases hEv
            | some l' =>
              rw [hSet] at hEv; dsimp at hEv
              injection hEv with hTup
              injection hTup with hTyEq hRest
              injection hRest with hOptEq hLocEq
              subst hTyEq; subst hOptEq; subst hLocEq
              refine ⟨(setElem?_length hSet).trans hLen, ?_, ?_⟩
              · intro v hv; subst hv; exact hWt pl.localId ty v hTy hSl
              · intro i ti vi hTi hSli
                cases hEqI : Nat.beq i pl.localId with
                | true =>
                  have hi := nat_beq_eq hEqI; subst hi
                  rw [hTy] at hTi; injection hTi with hte; subst hte
                  rw [setElem?_getElem?_same hSet] at hSli
                  injection hSli with hSlot
                  exact checkVal_liveUninitSlot hSlot
                | false =>
                  rw [setElem?_getElem?_ne hSet (nat_ne_of_beq_false hEqI)] at hSli
                  exact hWt i ti vi hTi hSli
    · cases hEv

private theorem evalPrimitiveOperand_wf {bodyLocals : List MirTy}
    {locals locs' : List LocalSlot} {op : Operand} {v : Val}
    (hLen : locals.length = bodyLocals.length)
    (hWt : ∀ i ty vi,
      Trusted.MirSemantics.getElem? bodyLocals i = some ty →
      Trusted.MirSemantics.getElem? locals i = some (.live (some vi)) →
      checkVal vi ty = true)
    (hEv : evalPrimitiveOperand bodyLocals locals op = .ok (v, locs')) :
    locs'.length = bodyLocals.length ∧
    (∀ i ty vi,
      Trusted.MirSemantics.getElem? bodyLocals i = some ty →
      Trusted.MirSemantics.getElem? locs' i = some (.live (some vi)) →
      checkVal vi ty = true) := by
  unfold evalPrimitiveOperand at hEv
  cases hOp : evalOperandToSlot bodyLocals locals op with
  | error _ => rw [hOp] at hEv; cases hEv
  | ok tup =>
    rw [hOp] at hEv; dsimp at hEv
    let ⟨hL, _, hW⟩ := evalOperandToSlot_wf hLen hWt hOp
    cases hp : (!isPrimitiveReadableTy tup.1) <;> rw [hp] at hEv
    · dsimp at hEv
      cases hOv : tup.2.1 with
      | none => rw [hOv] at hEv; cases hEv
      | some val =>
        rw [hOv] at hEv; dsimp at hEv
        injection hEv with hPair; injection hPair with _ hLocEq
        subst hLocEq
        exact ⟨hL, hW⟩
    · cases hEv

private theorem evalCallArgsUnw_wf {bodyLocals : List MirTy} :
    ∀ {args : List Operand} {locals locs' : List LocalSlot} {vs : List Val},
      locals.length = bodyLocals.length →
      (∀ i ty vi,
        Trusted.MirSemantics.getElem? bodyLocals i = some ty →
        Trusted.MirSemantics.getElem? locals i = some (.live (some vi)) →
        checkVal vi ty = true) →
      evalCallArgsUnw bodyLocals locals args = .ok (vs, locs') →
      locs'.length = bodyLocals.length ∧
      (∀ i ty vi,
        Trusted.MirSemantics.getElem? bodyLocals i = some ty →
        Trusted.MirSemantics.getElem? locs' i = some (.live (some vi)) →
        checkVal vi ty = true)
  | [], locals, locs', _, hLen, hWt, hEv => by
    dsimp [evalCallArgsUnw] at hEv
    injection hEv with hp; injection hp with _ hl; subst hl
    exact ⟨hLen, hWt⟩
  | op :: rest, locals, locs', vs, hLen, hWt, hEv => by
    dsimp [evalCallArgsUnw] at hEv
    cases hOp : evalOperandToSlot bodyLocals locals op with
    | error _ => rw [hOp] at hEv; cases hEv
    | ok tup =>
      cases tup with
      | mk ty pr1 =>
        cases pr1 with
        | mk ov locs1 =>
          rw [hOp] at hEv
          let ⟨hL1, _, hW1⟩ := evalOperandToSlot_wf hLen hWt hOp
          cases ov with
          | none => cases hEv
          | some v =>
            dsimp at hEv
            cases hRest : evalCallArgsUnw bodyLocals locs1 rest with
            | error _ => rw [hRest] at hEv; cases hEv
            | ok pr =>
              rw [hRest] at hEv; dsimp at hEv
              injection hEv with hp; injection hp with _ hl; subst hl
              exact evalCallArgsUnw_wf hL1 hW1 hRest

private theorem writePlace_wf {bodyLocals : List MirTy}
    {locals locs' : List LocalSlot} {lid : LocalId} {dstTy : MirTy} {val : Val}
    (hLen : locals.length = bodyLocals.length)
    (hWt : ∀ i ty vi,
      Trusted.MirSemantics.getElem? bodyLocals i = some ty →
      Trusted.MirSemantics.getElem? locals i = some (.live (some vi)) →
      checkVal vi ty = true)
    (hTyLid : Trusted.MirSemantics.getElem? bodyLocals lid = some dstTy)
    (hWr : writePlace locals lid dstTy val = .ok locs') :
    locs'.length = bodyLocals.length ∧
    (∀ i ty vi,
      Trusted.MirSemantics.getElem? bodyLocals i = some ty →
      Trusted.MirSemantics.getElem? locs' i = some (.live (some vi)) →
      checkVal vi ty = true) := by
  unfold writePlace at hWr
  cases hCv : (!checkVal val dstTy) <;> rw [hCv] at hWr
  · dsimp at hWr
    have hValOk : checkVal val dstTy = true := bool_not_false hCv
    cases hSl : Trusted.MirSemantics.getElem? locals lid with
    | none => rw [hSl] at hWr; cases hWr
    | some sl =>
      rw [hSl] at hWr
      cases sl with
      | dead => cases hWr
      | live _ =>
        dsimp at hWr
        cases hSet : setElem? locals lid (.live (some val)) with
        | none => rw [hSet] at hWr; cases hWr
        | some ls =>
          rw [hSet] at hWr; injection hWr with heq; subst heq
          refine ⟨(setElem?_length hSet).trans hLen, ?_⟩
          intro i ti vi hTi hSli
          cases hEqI : Nat.beq i lid with
          | true =>
            have hi := nat_beq_eq hEqI; subst hi
            rw [hTyLid] at hTi; injection hTi with hte; subst hte
            rw [setElem?_getElem?_same hSet] at hSli
            injection hSli with hL; injection hL with hL2; injection hL2 with hV; subst hV
            exact hValOk
          | false =>
            rw [setElem?_getElem?_ne hSet (nat_ne_of_beq_false hEqI)] at hSli
            exact hWt i ti vi hTi hSli
  · cases hWr

private theorem evalRvalue_wf {bodyLocals : List MirTy}
    {locals locs' : List LocalSlot} {dstTy : MirTy} {rv : Rvalue} {v : Val}
    (hLen : locals.length = bodyLocals.length)
    (hWt : ∀ i ty vi,
      Trusted.MirSemantics.getElem? bodyLocals i = some ty →
      Trusted.MirSemantics.getElem? locals i = some (.live (some vi)) →
      checkVal vi ty = true)
    (hEv : evalRvalue bodyLocals locals dstTy rv = .ok (v, locs')) :
    locs'.length = bodyLocals.length ∧
    (∀ i ty vi,
      Trusted.MirSemantics.getElem? bodyLocals i = some ty →
      Trusted.MirSemantics.getElem? locs' i = some (.live (some vi)) →
      checkVal vi ty = true) := by
  cases rv with
  | unsupported | ref _ _ | addressOf _ _ | aggregateTuple _ => cases hEv
  | discriminant pl =>
    dsimp [evalRvalue] at hEv
    cases hp : (!pl.projection.isEmpty) <;> rw [hp] at hEv
    · dsimp at hEv
      cases h1 : Trusted.MirSemantics.getElem? bodyLocals pl.localId with
      | none => rw [h1] at hEv; cases hEv
      | some ty =>
        rw [h1] at hEv
        cases ty with
        | bool | int _ _ | unit | never | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases hEv
        | enum ety =>
          cases h2 : Trusted.MirSemantics.getElem? locals pl.localId with
          | none => rw [h2] at hEv; cases hEv
          | some sl =>
            rw [h2] at hEv; dsimp at hEv
            cases hadm : (!enumAdmitted ety) <;> rw [hadm] at hEv
            · dsimp at hEv
              cases htr : ety.tagRepr <;> rw [htr] at hEv
              · cases sl with
                | dead => cases hEv
                | live ov =>
                  cases ov with
                  | none =>
                    dsimp at hEv
                    cases hd : Trusted.MirSemantics.getElem? ety.discriminants 0 with
                    | none => rw [hd] at hEv; cases hEv
                    | some disc =>
                      rw [hd] at hEv; injection hEv with hp2; injection hp2 with _ hl; subst hl
                      exact ⟨hLen, hWt⟩
                  | some val =>
                    cases val with
                    | enumVal ety' vi =>
                      dsimp at hEv
                      cases hc : (EnumTy.beq ety ety' && Nat.beq vi 0) <;> rw [hc] at hEv
                      · cases hEv
                      · dsimp at hEv
                        cases hd : Trusted.MirSemantics.getElem? ety.discriminants 0 with
                        | none => rw [hd] at hEv; cases hEv
                        | some disc =>
                          rw [hd] at hEv; injection hEv with hp2; injection hp2 with _ hl; subst hl
                          exact ⟨hLen, hWt⟩
                    | scalar _ | bool _ | unit | ptr _ | tuple _ | bytes _ => cases hEv
              · cases sl with
                | dead => cases hEv
                | live ov =>
                  cases ov with
                  | none => cases hEv
                  | some val =>
                    cases val with
                    | enumVal ety' vi =>
                      dsimp at hEv
                      cases hc : (EnumTy.beq ety ety' && Nat.blt vi ety.discriminants.length) <;> rw [hc] at hEv
                      · cases hEv
                      · dsimp at hEv
                        cases hd : Trusted.MirSemantics.getElem? ety.discriminants vi with
                        | none => rw [hd] at hEv; cases hEv
                        | some disc =>
                          rw [hd] at hEv; injection hEv with hp2; injection hp2 with _ hl; subst hl
                          exact ⟨hLen, hWt⟩
                    | scalar _ | bool _ | unit | ptr _ | tuple _ | bytes _ => cases hEv
            · cases hEv
    · cases hEv
  | use op =>
    dsimp [evalRvalue] at hEv
    cases hOp : evalOperandToSlot bodyLocals locals op with
    | error _ => rw [hOp] at hEv; cases hEv
    | ok tup =>
      rw [hOp] at hEv; dsimp at hEv
      let ⟨hL, _, hW⟩ := evalOperandToSlot_wf hLen hWt hOp
      cases hb : (!MirTy.beq tup.1 dstTy) <;> rw [hb] at hEv
      · dsimp at hEv
        cases hov : tup.2.1 with
        | none => rw [hov] at hEv; cases hEv
        | some val =>
          rw [hov] at hEv; injection hEv with hp2; injection hp2 with _ hl; subst hl
          exact ⟨hL, hW⟩
      · cases hEv
  | binaryOp op lhs rhs =>
    dsimp [evalRvalue] at hEv
    cases h1 : evalPrimitiveOperand bodyLocals locals lhs with
    | error _ => rw [h1] at hEv; cases hEv
    | ok p1 =>
      rw [h1] at hEv; dsimp at hEv
      let ⟨hL1, hW1⟩ := evalPrimitiveOperand_wf hLen hWt h1
      cases h2 : evalPrimitiveOperand bodyLocals p1.2 rhs with
      | error _ => rw [h2] at hEv; cases hEv
      | ok p2 =>
        rw [h2] at hEv; dsimp at hEv
        let ⟨hL2, hW2⟩ := evalPrimitiveOperand_wf hL1 hW1 h2
        cases h3 : evalBinOp op p1.1 p2.1 with
        | error _ => rw [h3] at hEv; cases hEv
        | ok res =>
          rw [h3] at hEv; injection hEv with hp2; injection hp2 with _ hl; subst hl
          exact ⟨hL2, hW2⟩
  | unaryOp op o =>
    dsimp [evalRvalue] at hEv
    cases h1 : evalPrimitiveOperand bodyLocals locals o with
    | error _ => rw [h1] at hEv; cases hEv
    | ok p1 =>
      rw [h1] at hEv; dsimp at hEv
      let ⟨hL1, hW1⟩ := evalPrimitiveOperand_wf hLen hWt h1
      cases h2 : evalUnOp op p1.1 with
      | error _ => rw [h2] at hEv; cases hEv
      | ok res =>
        rw [h2] at hEv; injection hEv with hp2; injection hp2 with _ hl; subst hl
        exact ⟨hL1, hW1⟩

private theorem evalStatement_wf {p : Program} {body : Body} {bb : BasicBlock}
    {f f' : FrameState} {mem m' : CallerMemory} {stmt : StatementKind}
    (hBod : Trusted.MirSemantics.getElem? p.bodies f.defId = some body)
    (hBb : Trusted.MirSemantics.getElem? body.basicBlocks f.blockIdx = some bb)
    (hSt : Trusted.MirSemantics.getElem? bb.statements f.stmtIdx = some stmt)
    (hWf : FrameWf p f)
    (hEv : evalStatement body f mem stmt = .step ⟨[f'], m'⟩) :
    FrameWf p f' ∧ f'.defId = f.defId ∧ f'.blockIdx = f.blockIdx ∧
      f'.stmtIdx = f.stmtIdx + 1 := by
  let ⟨hLen, hWt, _⟩ := hWf body hBod
  have hStmtLt : f.stmtIdx < bb.statements.length := getElem?_some_lt hSt
  cases stmt with
  | nop =>
    dsimp [evalStatement] at hEv
    injection hEv with h1; injection h1 with h2 _; injection h2 with h3; subst h3
    refine ⟨?_, rfl, rfl, rfl⟩
    intro b2 hb2; rw [hBod] at hb2; injection hb2 with he; subst he
    refine ⟨hLen, hWt, fun bb2 hbb2 => ?_⟩
    rw [hBb] at hbb2; injection hbb2 with hbe; subst hbe
    exact hStmtLt
  | unsupported => cases hEv
  | storageLive lid =>
    dsimp [evalStatement] at hEv
    cases hTy : Trusted.MirSemantics.getElem? body.locals lid with
    | none => rw [hTy] at hEv; cases hEv
    | some ty =>
      rw [hTy] at hEv; dsimp at hEv
      cases hSet : setElem? f.locals lid (liveUninitSlot ty) with
      | none => rw [hSet] at hEv; cases hEv
      | some ls =>
        rw [hSet] at hEv; injection hEv with h1; injection h1 with h2 _; injection h2 with h3; subst h3
        refine ⟨?_, rfl, rfl, rfl⟩
        intro b2 hb2; rw [hBod] at hb2; injection hb2 with he; subst he
        refine ⟨(setElem?_length hSet).trans hLen, ?_, fun bb2 hbb2 => ?_⟩
        · intro i ti vi hTi hSli
          cases hEqI : Nat.beq i lid with
          | true =>
            have hi := nat_beq_eq hEqI; subst hi
            rw [hTy] at hTi; injection hTi with hte; subst hte
            rw [setElem?_getElem?_same hSet] at hSli
            injection hSli with hSlot
            exact checkVal_liveUninitSlot hSlot
          | false =>
            rw [setElem?_getElem?_ne hSet (nat_ne_of_beq_false hEqI)] at hSli
            exact hWt i ti vi hTi hSli
        · rw [hBb] at hbb2; injection hbb2 with hbe; subst hbe; exact hStmtLt
  | storageDead lid =>
    dsimp [evalStatement] at hEv
    cases h0 : Nat.beq lid 0 with
    | true => rw [h0] at hEv; cases hEv
    | false =>
      rw [h0] at hEv; dsimp at hEv
      cases hSet : setElem? f.locals lid .dead with
      | none => rw [hSet] at hEv; cases hEv
      | some ls =>
        rw [hSet] at hEv; injection hEv with h1; injection h1 with h2 _; injection h2 with h3; subst h3
        refine ⟨?_, rfl, rfl, rfl⟩
        intro b2 hb2; rw [hBod] at hb2; injection hb2 with he; subst he
        refine ⟨(setElem?_length hSet).trans hLen, ?_, fun bb2 hbb2 => ?_⟩
        · intro i ti vi hTi hSli
          cases hEqI : Nat.beq i lid with
          | true =>
            have hi := nat_beq_eq hEqI; subst hi
            rw [setElem?_getElem?_same hSet] at hSli; cases hSli
          | false =>
            rw [setElem?_getElem?_ne hSet (nat_ne_of_beq_false hEqI)] at hSli
            exact hWt i ti vi hTi hSli
        · rw [hBb] at hbb2; injection hbb2 with hbe; subst hbe; exact hStmtLt
  | assign dst rv =>
    dsimp [evalStatement] at hEv
    cases hp : (!dst.projection.isEmpty) <;> rw [hp] at hEv
    · dsimp at hEv
      cases hTy : Trusted.MirSemantics.getElem? body.locals dst.localId with
      | none => rw [hTy] at hEv; cases hEv
      | some dstTy =>
        rw [hTy] at hEv; dsimp at hEv
        cases hRv : evalRvalue body.locals f.locals dstTy rv with
        | error _ => rw [hRv] at hEv; cases hEv
        | ok pr =>
          rw [hRv] at hEv; dsimp at hEv
          let ⟨hL1, hW1⟩ := evalRvalue_wf hLen hWt hRv
          cases hWr : writePlace pr.2 dst.localId dstTy pr.1 with
          | error _ => rw [hWr] at hEv; cases hEv
          | ok ls =>
            rw [hWr] at hEv; injection hEv with h1; injection h1 with h2 _; injection h2 with h3; subst h3
            let ⟨hL2, hW2⟩ := writePlace_wf hL1 hW1 hTy hWr
            refine ⟨?_, rfl, rfl, rfl⟩
            intro b2 hb2; rw [hBod] at hb2; injection hb2 with he; subst he
            refine ⟨hL2, hW2, fun bb2 hbb2 => ?_⟩
            rw [hBb] at hbb2; injection hbb2 with hbe; subst hbe; exact hStmtLt
    · cases hEv

/-! ### Part 3: Caller/Callee Local-Slice Isolation Lemmas -/

private theorem evalOperandToSlot_prefix {cLocs eLocs : List MirTy}
    {cSlots sSlots : List LocalSlot} {op : Operand}
    (hLenC : cSlots.length = cLocs.length)
    (hLt : operandLocalsLt cLocs.length op = true) :
    evalOperandToSlot (cLocs ++ eLocs) (cSlots ++ sSlots) op =
      match evalOperandToSlot cLocs cSlots op with
      | .error k => .error k
      | .ok (ty, ov, cSlots') => .ok (ty, ov, cSlots' ++ sSlots) := by
  cases op with
  | constant c =>
    dsimp [evalOperandToSlot]
    cases evalConstLit c.ty c.lit <;> rfl
  | copy pl =>
    dsimp [operandLocalsLt, placeLocalLt] at hLt
    have hIdLt : pl.localId < cLocs.length := nat_blt_lt hLt
    have hIdLtS : pl.localId < cSlots.length := by rw [hLenC]; exact hIdLt
    dsimp [evalOperandToSlot]
    rw [getElem?_append_left hIdLt, getElem?_append_left hIdLtS]
    cases !pl.projection.isEmpty with
    | true => rfl
    | false =>
      dsimp
      cases Trusted.MirSemantics.getElem? cLocs pl.localId with
      | none => rfl
      | some ty =>
        cases Trusted.MirSemantics.getElem? cSlots pl.localId with
        | none => rfl
        | some sl => cases sl <;> rfl
  | move pl =>
    dsimp [operandLocalsLt, placeLocalLt] at hLt
    have hIdLt : pl.localId < cLocs.length := nat_blt_lt hLt
    have hIdLtS : pl.localId < cSlots.length := by rw [hLenC]; exact hIdLt
    dsimp [evalOperandToSlot]
    rw [getElem?_append_left hIdLt, getElem?_append_left hIdLtS]
    cases !pl.projection.isEmpty with
    | true => rfl
    | false =>
      dsimp
      cases Trusted.MirSemantics.getElem? cLocs pl.localId with
      | none => rfl
      | some ty =>
        cases Trusted.MirSemantics.getElem? cSlots pl.localId with
        | none => rfl
        | some sl =>
          cases sl with
          | dead => rfl
          | live ov =>
            dsimp
            rw [setElem?_append_left sSlots (liveUninitSlot ty) hIdLtS]
            cases setElem? cSlots pl.localId (liveUninitSlot ty) <;> rfl

private theorem evalOperandToSlot_suffix {cLocs eLocs : List MirTy}
    {cSlots eSlots : List LocalSlot} {op : Operand}
    (hLenC : cSlots.length = cLocs.length) :
    evalOperandToSlot (cLocs ++ eLocs) (cSlots ++ eSlots) (shiftOperandUnw cLocs.length op) =
      match evalOperandToSlot eLocs eSlots op with
      | .error k => .error k
      | .ok (ty, ov, eSlots') => .ok (ty, ov, cSlots ++ eSlots') := by
  cases op with
  | constant c =>
    dsimp [shiftOperandUnw, evalOperandToSlot]
    cases evalConstLit c.ty c.lit <;> rfl
  | copy pl =>
    dsimp [shiftOperandUnw, shiftPlaceUnw, evalOperandToSlot]
    rw [getElem?_append_right_comm cLocs eLocs pl.localId]
    have hR : Trusted.MirSemantics.getElem? (cSlots ++ eSlots) (pl.localId + cLocs.length) =
        Trusted.MirSemantics.getElem? eSlots pl.localId := by
      rw [← hLenC]; exact getElem?_append_right_comm cSlots eSlots pl.localId
    rw [hR]
    cases !pl.projection.isEmpty with
    | true => rfl
    | false =>
      dsimp
      cases Trusted.MirSemantics.getElem? eLocs pl.localId with
      | none => rfl
      | some ty =>
        cases Trusted.MirSemantics.getElem? eSlots pl.localId with
        | none => rfl
        | some sl => cases sl <;> rfl
  | move pl =>
    dsimp [shiftOperandUnw, shiftPlaceUnw, evalOperandToSlot]
    rw [getElem?_append_right_comm cLocs eLocs pl.localId]
    have hR : Trusted.MirSemantics.getElem? (cSlots ++ eSlots) (pl.localId + cLocs.length) =
        Trusted.MirSemantics.getElem? eSlots pl.localId := by
      rw [← hLenC]; exact getElem?_append_right_comm cSlots eSlots pl.localId
    rw [hR]
    cases !pl.projection.isEmpty with
    | true => rfl
    | false =>
      dsimp
      cases Trusted.MirSemantics.getElem? eLocs pl.localId with
      | none => rfl
      | some ty =>
        cases Trusted.MirSemantics.getElem? eSlots pl.localId with
        | none => rfl
        | some sl =>
          cases sl with
          | dead => rfl
          | live ov =>
            dsimp
            rw [← hLenC, setElem?_append_right_comm cSlots eSlots pl.localId (liveUninitSlot ty)]
            cases setElem? eSlots pl.localId (liveUninitSlot ty) <;> rfl

private theorem evalPrimitiveOperand_prefix {cLocs eLocs : List MirTy}
    {cSlots sSlots : List LocalSlot} {op : Operand}
    (hLenC : cSlots.length = cLocs.length)
    (hLt : operandLocalsLt cLocs.length op = true) :
    evalPrimitiveOperand (cLocs ++ eLocs) (cSlots ++ sSlots) op =
      match evalPrimitiveOperand cLocs cSlots op with
      | .error k => .error k
      | .ok (v, cSlots') => .ok (v, cSlots' ++ sSlots) := by
  unfold evalPrimitiveOperand
  rw [evalOperandToSlot_prefix hLenC hLt]
  cases evalOperandToSlot cLocs cSlots op with
  | error _ => rfl
  | ok tup =>
    dsimp
    cases !isPrimitiveReadableTy tup.1 with
    | true => rfl
    | false =>
      dsimp
      cases tup.2.1 <;> rfl

private theorem evalPrimitiveOperand_suffix {cLocs eLocs : List MirTy}
    {cSlots eSlots : List LocalSlot} {op : Operand}
    (hLenC : cSlots.length = cLocs.length) :
    evalPrimitiveOperand (cLocs ++ eLocs) (cSlots ++ eSlots) (shiftOperandUnw cLocs.length op) =
      match evalPrimitiveOperand eLocs eSlots op with
      | .error k => .error k
      | .ok (v, eSlots') => .ok (v, cSlots ++ eSlots') := by
  unfold evalPrimitiveOperand
  rw [evalOperandToSlot_suffix hLenC]
  cases evalOperandToSlot eLocs eSlots op with
  | error _ => rfl
  | ok tup =>
    dsimp
    cases !isPrimitiveReadableTy tup.1 with
    | true => rfl
    | false =>
      dsimp
      cases tup.2.1 <;> rfl

private theorem evalOperandToSlot_len {bodyLocals : List MirTy}
    {locals locs' : List LocalSlot} {op : Operand}
    {ty : MirTy} {ov : Option Val}
    (hEv : evalOperandToSlot bodyLocals locals op = .ok (ty, ov, locs')) :
    locs'.length = locals.length := by
  cases op with
  | constant c =>
    dsimp [evalOperandToSlot] at hEv
    cases hc : evalConstLit c.ty c.lit with
    | error _ => rw [hc] at hEv; cases hEv
    | ok _ =>
      rw [hc] at hEv; dsimp at hEv
      injection hEv with ht; injection ht with _ hr; injection hr with _ hl; rw [← hl]
  | copy pl =>
    dsimp [evalOperandToSlot] at hEv
    cases hp : (!pl.projection.isEmpty) <;> rw [hp] at hEv
    · dsimp at hEv
      cases h1 : Trusted.MirSemantics.getElem? bodyLocals pl.localId with
      | none => rw [h1] at hEv; cases hEv
      | some _ =>
        rw [h1] at hEv
        cases h2 : Trusted.MirSemantics.getElem? locals pl.localId with
        | none => rw [h2] at hEv; cases hEv
        | some sl =>
          rw [h2] at hEv
          cases sl with
          | dead => cases hEv
          | live _ =>
            dsimp at hEv
            injection hEv with ht; injection ht with _ hr; injection hr with _ hl; rw [← hl]
    · cases hEv
  | move pl =>
    dsimp [evalOperandToSlot] at hEv
    cases hp : (!pl.projection.isEmpty) <;> rw [hp] at hEv
    · dsimp at hEv
      cases h1 : Trusted.MirSemantics.getElem? bodyLocals pl.localId with
      | none => rw [h1] at hEv; cases hEv
      | some t =>
        rw [h1] at hEv
        cases h2 : Trusted.MirSemantics.getElem? locals pl.localId with
        | none => rw [h2] at hEv; cases hEv
        | some sl =>
          rw [h2] at hEv
          cases sl with
          | dead => cases hEv
          | live _ =>
            dsimp at hEv
            cases h3 : setElem? locals pl.localId (liveUninitSlot t) with
            | none => rw [h3] at hEv; cases hEv
            | some ls =>
              rw [h3] at hEv; dsimp at hEv
              injection hEv with ht; injection ht with _ hr; injection hr with _ hl
              rw [← hl]; exact setElem?_length h3
    · cases hEv

private theorem evalCallArgsUnw_prefix {cLocs eLocs : List MirTy} :
    ∀ {args : List Operand} {cSlots sSlots : List LocalSlot},
      cSlots.length = cLocs.length →
      args.all (operandLocalsLt cLocs.length) = true →
      evalCallArgsUnw (cLocs ++ eLocs) (cSlots ++ sSlots) args =
        match evalCallArgsUnw cLocs cSlots args with
        | .error k => .error k
        | .ok (vs, cSlots') => .ok (vs, cSlots' ++ sSlots)
  | [], _, _, _, _ => rfl
  | op :: rest, cSlots, sSlots, hLenC, hAll => by
    dsimp [List.all] at hAll
    let ⟨hOpLt, hRestLt⟩ := bool_and_true hAll
    dsimp [evalCallArgsUnw]
    rw [evalOperandToSlot_prefix hLenC hOpLt]
    cases hOp : evalOperandToSlot cLocs cSlots op with
    | error _ => rfl
    | ok tup =>
      cases tup with
      | mk oTy rest1 =>
        cases rest1 with
        | mk ov cSlots1 =>
          dsimp
          cases ov with
          | none => rfl
          | some v =>
            dsimp
            have hLen1 : cSlots1.length = cLocs.length :=
              (evalOperandToSlot_len hOp).trans hLenC
            rw [evalCallArgsUnw_prefix hLen1 hRestLt]
            cases evalCallArgsUnw cLocs cSlots1 rest <;> rfl

private theorem evalCallArgsUnw_suffix {cLocs eLocs : List MirTy} :
    ∀ {args : List Operand} {cSlots eSlots : List LocalSlot},
      cSlots.length = cLocs.length →
      evalCallArgsUnw (cLocs ++ eLocs) (cSlots ++ eSlots) (args.map (shiftOperandUnw cLocs.length)) =
        match evalCallArgsUnw eLocs eSlots args with
        | .error k => .error k
        | .ok (vs, eSlots') => .ok (vs, cSlots ++ eSlots')
  | [], _, _, _ => rfl
  | op :: rest, cSlots, eSlots, hLenC => by
    dsimp [List.map, evalCallArgsUnw]
    rw [evalOperandToSlot_suffix hLenC]
    cases evalOperandToSlot eLocs eSlots op with
    | error _ => rfl
    | ok tup =>
      cases tup with
      | mk oTy rest1 =>
        cases rest1 with
        | mk ov eSlots1 =>
          dsimp
          cases ov with
          | none => rfl
          | some v =>
            dsimp
            rw [evalCallArgsUnw_suffix hLenC]
            cases evalCallArgsUnw eLocs eSlots1 rest <;> rfl

private theorem writePlace_prefix {cSlots sSlots : List LocalSlot} {lid : LocalId}
    {dstTy : MirTy} {val : Val}
    (hLt : lid < cSlots.length) :
    writePlace (cSlots ++ sSlots) lid dstTy val =
      match writePlace cSlots lid dstTy val with
      | .error k => .error k
      | .ok cSlots' => .ok (cSlots' ++ sSlots) := by
  unfold writePlace
  rw [getElem?_append_left hLt]
  cases !checkVal val dstTy with
  | true => rfl
  | false =>
    dsimp
    cases Trusted.MirSemantics.getElem? cSlots lid with
    | none => rfl
    | some sl =>
      cases sl with
      | dead => rfl
      | live _ =>
        dsimp
        rw [setElem?_append_left sSlots (.live (some val)) hLt]
        cases setElem? cSlots lid (.live (some val)) <;> rfl

private theorem writePlace_suffix {cSlots eSlots : List LocalSlot} {lid : LocalId}
    {dstTy : MirTy} {val : Val} :
    writePlace (cSlots ++ eSlots) (lid + cSlots.length) dstTy val =
      match writePlace eSlots lid dstTy val with
      | .error k => .error k
      | .ok eSlots' => .ok (cSlots ++ eSlots') := by
  unfold writePlace
  rw [getElem?_append_right_comm cSlots eSlots lid]
  cases !checkVal val dstTy with
  | true => rfl
  | false =>
    dsimp
    cases Trusted.MirSemantics.getElem? eSlots lid with
    | none => rfl
    | some sl =>
      cases sl with
      | dead => rfl
      | live _ =>
        dsimp
        rw [setElem?_append_right_comm cSlots eSlots lid (.live (some val))]
        cases setElem? eSlots lid (.live (some val)) <;> rfl

private theorem evalRvalue_prefix {cLocs eLocs : List MirTy}
    {cSlots sSlots : List LocalSlot} {dstTy : MirTy} {rv : Rvalue}
    (hLenC : cSlots.length = cLocs.length)
    (hLt : rvalueLocalsLt cLocs.length rv = true) :
    evalRvalue (cLocs ++ eLocs) (cSlots ++ sSlots) dstTy rv =
      match evalRvalue cLocs cSlots dstTy rv with
      | .error k => .error k
      | .ok (v, cSlots') => .ok (v, cSlots' ++ sSlots) := by
  cases rv with
  | unsupported | ref _ _ | addressOf _ _ | aggregateTuple _ => rfl
  | use op =>
    dsimp [evalRvalue]
    rw [evalOperandToSlot_prefix hLenC hLt]
    cases evalOperandToSlot cLocs cSlots op with
    | error _ => rfl
    | ok tup =>
      dsimp
      cases !MirTy.beq tup.1 dstTy with
      | true => rfl
      | false =>
        dsimp
        cases tup.2.1 <;> rfl
  | unaryOp op o =>
    dsimp [evalRvalue]
    rw [evalPrimitiveOperand_prefix hLenC hLt]
    cases evalPrimitiveOperand cLocs cSlots o with
    | error _ => rfl
    | ok p1 =>
      dsimp
      cases evalUnOp op p1.1 <;> rfl
  | binaryOp op lhs rhs =>
    dsimp [rvalueLocalsLt] at hLt
    let ⟨hL, hR⟩ := bool_and_true hLt
    dsimp [evalRvalue]
    rw [evalPrimitiveOperand_prefix hLenC hL]
    cases h1 : evalPrimitiveOperand cLocs cSlots lhs with
    | error _ => rfl
    | ok p1 =>
      dsimp
      have hLen1 : p1.2.length = cLocs.length := by
        unfold evalPrimitiveOperand at h1
        cases hOp : evalOperandToSlot cLocs cSlots lhs with
        | error _ => rw [hOp] at h1; cases h1
        | ok tup =>
          rw [hOp] at h1; dsimp at h1
          cases hp : (!isPrimitiveReadableTy tup.1) <;> rw [hp] at h1
          · dsimp at h1
            cases hov : tup.2.1 with
            | none => rw [hov] at h1; cases h1
            | some _ =>
              rw [hov] at h1; dsimp at h1
              injection h1 with hp2; subst hp2
              exact (evalOperandToSlot_len hOp).trans hLenC
          · cases h1
      rw [evalPrimitiveOperand_prefix hLen1 hR]
      cases evalPrimitiveOperand cLocs p1.2 rhs with
      | error _ => rfl
      | ok p2 =>
        dsimp
        cases evalBinOp op p1.1 p2.1 <;> rfl
  | discriminant pl =>
    dsimp [rvalueLocalsLt, placeLocalLt] at hLt
    have hIdLt : pl.localId < cLocs.length := nat_blt_lt hLt
    have hIdLtS : pl.localId < cSlots.length := by rw [hLenC]; exact hIdLt
    dsimp [evalRvalue]
    rw [getElem?_append_left hIdLt, getElem?_append_left hIdLtS]
    cases !pl.projection.isEmpty with
    | true => rfl
    | false =>
      dsimp
      cases Trusted.MirSemantics.getElem? cLocs pl.localId with
      | none => rfl
      | some ty =>
        cases ty with
        | bool | int _ _ | unit | never | tuple _ | ref _ _ | rawPtr _ _ | unsupported => rfl
        | enum ety =>
          cases Trusted.MirSemantics.getElem? cSlots pl.localId with
          | none => rfl
          | some sl =>
            dsimp
            cases !enumAdmitted ety with
            | true => rfl
            | false =>
              dsimp
              cases ety.tagRepr with
              | zeroSized =>
                cases sl with
                | dead => rfl
                | live ov =>
                  cases ov with
                  | none =>
                    cases Trusted.MirSemantics.getElem? ety.discriminants 0 <;> rfl
                  | some val =>
                    cases val with
                    | enumVal ety' vi =>
                      dsimp
                      cases EnumTy.beq ety ety' && Nat.beq vi 0 with
                      | false => rfl
                      | true => cases Trusted.MirSemantics.getElem? ety.discriminants 0 <;> rfl
                    | scalar _ | bool _ | unit | ptr _ | tuple _ | bytes _ => rfl
              | scalar tw ts =>
                cases sl with
                | dead => rfl
                | live ov =>
                  cases ov with
                  | none => rfl
                  | some val =>
                    cases val with
                    | enumVal ety' vi =>
                      dsimp
                      cases EnumTy.beq ety ety' && Nat.blt vi ety.discriminants.length with
                      | false => rfl
                      | true => cases Trusted.MirSemantics.getElem? ety.discriminants vi <;> rfl
                    | scalar _ | bool _ | unit | ptr _ | tuple _ | bytes _ => rfl

private theorem evalRvalue_suffix {cLocs eLocs : List MirTy}
    {cSlots eSlots : List LocalSlot} {dstTy : MirTy} {rv : Rvalue}
    (hLenC : cSlots.length = cLocs.length) :
    evalRvalue (cLocs ++ eLocs) (cSlots ++ eSlots) dstTy (shiftRvalueUnw cLocs.length rv) =
      match evalRvalue eLocs eSlots dstTy rv with
      | .error k => .error k
      | .ok (v, eSlots') => .ok (v, cSlots ++ eSlots') := by
  cases rv with
  | unsupported | ref _ _ | addressOf _ _ | aggregateTuple _ => rfl
  | use op =>
    dsimp [shiftRvalueUnw, evalRvalue]
    rw [evalOperandToSlot_suffix hLenC]
    cases evalOperandToSlot eLocs eSlots op with
    | error _ => rfl
    | ok tup =>
      dsimp
      cases !MirTy.beq tup.1 dstTy with
      | true => rfl
      | false =>
        dsimp
        cases tup.2.1 <;> rfl
  | unaryOp op o =>
    dsimp [shiftRvalueUnw, evalRvalue]
    rw [evalPrimitiveOperand_suffix hLenC]
    cases evalPrimitiveOperand eLocs eSlots o with
    | error _ => rfl
    | ok p1 =>
      dsimp
      cases evalUnOp op p1.1 <;> rfl
  | binaryOp op lhs rhs =>
    dsimp [shiftRvalueUnw, evalRvalue]
    rw [evalPrimitiveOperand_suffix hLenC]
    cases evalPrimitiveOperand eLocs eSlots lhs with
    | error _ => rfl
    | ok p1 =>
      dsimp
      rw [evalPrimitiveOperand_suffix hLenC]
      cases evalPrimitiveOperand eLocs p1.2 rhs with
      | error _ => rfl
      | ok p2 =>
        dsimp
        cases evalBinOp op p1.1 p2.1 <;> rfl
  | discriminant pl =>
    dsimp [shiftRvalueUnw, shiftPlaceUnw, evalRvalue]
    rw [getElem?_append_right_comm cLocs eLocs pl.localId]
    have hR : Trusted.MirSemantics.getElem? (cSlots ++ eSlots) (pl.localId + cLocs.length) =
        Trusted.MirSemantics.getElem? eSlots pl.localId := by
      rw [← hLenC]; exact getElem?_append_right_comm cSlots eSlots pl.localId
    rw [hR]
    cases !pl.projection.isEmpty with
    | true => rfl
    | false =>
      dsimp
      cases Trusted.MirSemantics.getElem? eLocs pl.localId with
      | none => rfl
      | some ty =>
        cases ty with
        | bool | int _ _ | unit | never | tuple _ | ref _ _ | rawPtr _ _ | unsupported => rfl
        | enum ety =>
          cases Trusted.MirSemantics.getElem? eSlots pl.localId with
          | none => rfl
          | some sl =>
            dsimp
            cases !enumAdmitted ety with
            | true => rfl
            | false =>
              dsimp
              cases ety.tagRepr with
              | zeroSized =>
                cases sl with
                | dead => rfl
                | live ov =>
                  cases ov with
                  | none =>
                    cases Trusted.MirSemantics.getElem? ety.discriminants 0 <;> rfl
                  | some val =>
                    cases val with
                    | enumVal ety' vi =>
                      dsimp
                      cases EnumTy.beq ety ety' && Nat.beq vi 0 with
                      | false => rfl
                      | true => cases Trusted.MirSemantics.getElem? ety.discriminants 0 <;> rfl
                    | scalar _ | bool _ | unit | ptr _ | tuple _ | bytes _ => rfl
              | scalar tw ts =>
                cases sl with
                | dead => rfl
                | live ov =>
                  cases ov with
                  | none => rfl
                  | some val =>
                    cases val with
                    | enumVal ety' vi =>
                      dsimp
                      cases EnumTy.beq ety ety' && Nat.blt vi ety.discriminants.length with
                      | false => rfl
                      | true => cases Trusted.MirSemantics.getElem? ety.discriminants vi <;> rfl
                    | scalar _ | bool _ | unit | ptr _ | tuple _ | bytes _ => rfl

/-! ### Slice: Slice3b_InlineGadgets.lean -/

-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.





/-! ### Part 1: Statement Prefix/Suffix Isolation -/

private theorem evalPrimitiveOperand_len {bodyLocals : List MirTy}
    {locals locs' : List LocalSlot} {op : Operand} {v : Val}
    (h : evalPrimitiveOperand bodyLocals locals op = .ok (v, locs')) :
    locs'.length = locals.length := by
  unfold evalPrimitiveOperand at h
  cases hOp : evalOperandToSlot bodyLocals locals op with
  | error _ => rw [hOp] at h; cases h
  | ok tup =>
    cases tup with
    | mk ty pr1 =>
      cases pr1 with
      | mk ov locs1 =>
        rw [hOp] at h; dsimp at h
        cases hp : (!isPrimitiveReadableTy ty) <;> rw [hp] at h
        · dsimp at h
          cases ov with
          | none => cases h
          | some _ =>
            dsimp at h; injection h with h1; injection h1 with _ hl; subst hl
            exact evalOperandToSlot_len hOp
        · cases h

private theorem evalRvalue_len {bodyLocals : List MirTy}
    {locals locs' : List LocalSlot} {dstTy : MirTy} {rv : Rvalue} {v : Val}
    (h : evalRvalue bodyLocals locals dstTy rv = .ok (v, locs')) :
    locs'.length = locals.length := by
  cases rv with
  | use op =>
    dsimp [evalRvalue] at h
    cases hOp : evalOperandToSlot bodyLocals locals op with
    | error _ => rw [hOp] at h; cases h
    | ok tup =>
      cases tup with
      | mk ty pr1 =>
        cases pr1 with
        | mk ov locs1 =>
          rw [hOp] at h; dsimp at h
          cases hb : (!MirTy.beq ty dstTy) <;> rw [hb] at h
          · dsimp at h
            cases ov with
            | none => cases h
            | some _ =>
              injection h with h1; injection h1 with _ hl; subst hl
              exact evalOperandToSlot_len hOp
          · cases h
  | unaryOp uop op =>
    dsimp [evalRvalue] at h
    cases h1 : evalPrimitiveOperand bodyLocals locals op with
    | error _ => rw [h1] at h; cases h
    | ok p1 =>
      cases p1 with
      | mk v1 locs1 =>
        rw [h1] at h; dsimp at h
        cases hu : evalUnOp uop v1 with
        | error _ => rw [hu] at h; cases h
        | ok _ =>
          rw [hu] at h; dsimp at h
          injection h with h2; injection h2 with _ hl; subst hl
          exact evalPrimitiveOperand_len h1
  | binaryOp bop lhs rhs =>
    dsimp [evalRvalue] at h
    cases h1 : evalPrimitiveOperand bodyLocals locals lhs with
    | error _ => rw [h1] at h; cases h
    | ok p1 =>
      cases p1 with
      | mk v1 locs1 =>
        rw [h1] at h; dsimp at h
        cases h2 : evalPrimitiveOperand bodyLocals locs1 rhs with
        | error _ => rw [h2] at h; cases h
        | ok p2 =>
          cases p2 with
          | mk v2 locs2 =>
            rw [h2] at h; dsimp at h
            cases hb : evalBinOp bop v1 v2 with
            | error _ => rw [hb] at h; cases h
            | ok _ =>
              rw [hb] at h; dsimp at h
              injection h with h3; injection h3 with _ hl; subst hl
              exact (evalPrimitiveOperand_len h2).trans (evalPrimitiveOperand_len h1)
  | discriminant pl =>
    dsimp [evalRvalue] at h
    cases hp : (!pl.projection.isEmpty) <;> rw [hp] at h
    · dsimp at h
      cases ht : Trusted.MirSemantics.getElem? bodyLocals pl.localId with
      | none => rw [ht] at h; cases h
      | some ty =>
        rw [ht] at h
        cases ty with
        | bool | int _ _ | unit | never | tuple _ | ref _ _ | rawPtr _ _ | unsupported => cases h
        | enum ety =>
          cases hs : Trusted.MirSemantics.getElem? locals pl.localId with
          | none => rw [hs] at h; cases h
          | some sl =>
            rw [hs] at h; dsimp at h
            cases ha : (!enumAdmitted ety) <;> rw [ha] at h
            · dsimp at h
              cases hr : ety.tagRepr <;> rw [hr] at h
              · cases sl with
                | dead => cases h
                | live ov =>
                  cases ov with
                  | none =>
                    cases hd : Trusted.MirSemantics.getElem? ety.discriminants 0 <;> rw [hd] at h
                    · cases h
                    · dsimp at h; injection h with h1; injection h1 with _ hl; subst hl; rfl
                  | some val =>
                    cases val with
                    | enumVal ety' vi =>
                      dsimp at h
                      cases hc : (EnumTy.beq ety ety' && Nat.beq vi 0) <;> rw [hc] at h
                      · cases h
                      · dsimp at h
                        cases hd : Trusted.MirSemantics.getElem? ety.discriminants 0 <;> rw [hd] at h
                        · cases h
                        · dsimp at h; injection h with h1; injection h1 with _ hl; subst hl; rfl
                    | scalar _ | bool _ | unit | ptr _ | tuple _ | bytes _ => cases h
              · cases sl with
                | dead => cases h
                | live ov =>
                  cases ov with
                  | none => cases h
                  | some val =>
                    cases val with
                    | enumVal ety' vi =>
                      dsimp at h
                      cases hc : (EnumTy.beq ety ety' && Nat.blt vi ety.discriminants.length) <;> rw [hc] at h
                      · cases h
                      · dsimp at h
                        cases hd : Trusted.MirSemantics.getElem? ety.discriminants vi <;> rw [hd] at h
                        · cases h
                        · dsimp at h; injection h with h1; injection h1 with _ hl; subst hl; rfl
                    | scalar _ | bool _ | unit | ptr _ | tuple _ | bytes _ => cases h
            · cases h
    · cases h
  | ref _ _ | addressOf _ _ | aggregateTuple _ | unsupported => cases h

private theorem evalStatement_prefix {caller caller' : Body} {f : FrameState}
    {cSlots sSlots : List LocalSlot} {mem : CallerMemory} {stmt : StatementKind}
    (hLocs : caller'.locals = caller.locals ++ calleeLocs)
    (hLenC : cSlots.length = caller.locals.length)
    (hLt : callerStmtLocalsLt caller.locals.length stmt = true) :
    evalStatement caller' { f with locals := cSlots ++ sSlots } mem stmt =
      match evalStatement caller { f with locals := cSlots } mem stmt with
      | .fault k => .fault k
      | .done out => .done out
      | .step st' =>
        match st'.frames with
        | [f'] =>
          .step { frames := [{ f' with locals := f'.locals ++ sSlots }],
                  callerMem := st'.callerMem }
        | _ => .fault .unsupported := by
  cases stmt with
  | nop => rfl
  | unsupported => rfl
  | storageLive id =>
    dsimp [callerStmtLocalsLt] at hLt
    have hIdLt : id < caller.locals.length := nat_blt_lt hLt
    have hIdLtS : id < cSlots.length := by rw [hLenC]; exact hIdLt
    dsimp [evalStatement]
    rw [hLocs, getElem?_append_left hIdLt]
    cases Trusted.MirSemantics.getElem? caller.locals id with
    | none => rfl
    | some ty =>
      dsimp
      rw [setElem?_append_left sSlots (liveUninitSlot ty) hIdLtS]
      cases setElem? cSlots id (liveUninitSlot ty) <;> rfl
  | storageDead id =>
    dsimp [callerStmtLocalsLt] at hLt
    have hIdLt : id < caller.locals.length := nat_blt_lt hLt
    have hIdLtS : id < cSlots.length := by rw [hLenC]; exact hIdLt
    dsimp [evalStatement]
    cases Nat.beq id 0 with
    | true => rfl
    | false =>
      dsimp
      rw [setElem?_append_left sSlots .dead hIdLtS]
      cases setElem? cSlots id .dead <;> rfl
  | assign dst rv =>
    dsimp [callerStmtLocalsLt, placeLocalLt] at hLt
    let ⟨hDst, hRv⟩ := bool_and_true hLt
    have hIdLt : dst.localId < caller.locals.length := nat_blt_lt hDst
    dsimp [evalStatement]
    rw [hLocs]
    cases !dst.projection.isEmpty with
    | true => rfl
    | false =>
      dsimp
      rw [getElem?_append_left hIdLt]
      cases Trusted.MirSemantics.getElem? caller.locals dst.localId with
      | none => rfl
      | some dstTy =>
        dsimp
        rw [evalRvalue_prefix hLenC hRv]
        cases hEv : evalRvalue caller.locals cSlots dstTy rv with
        | error _ => rfl
        | ok pr =>
          dsimp
          have hLenPr : pr.2.length = caller.locals.length :=
            (evalRvalue_len hEv).trans hLenC
          have hIdLtPr : dst.localId < pr.2.length := by rw [hLenPr]; exact hIdLt
          rw [writePlace_prefix hIdLtPr]
          cases writePlace pr.2 dst.localId dstTy pr.1 <;> rfl

private theorem evalStatement_suffix {callerLocs calleeLocs : List MirTy}
    {caller' callee : Body} {f : FrameState}
    {cSlots eSlots : List LocalSlot} {mem : CallerMemory} {stmt : StatementKind}
    (hLocs' : caller'.locals = callerLocs ++ calleeLocs)
    (hCalleeLocs : callee.locals = calleeLocs)
    (hLenC : cSlots.length = callerLocs.length)
    (hPosC : 0 < callerLocs.length)
    (hAd : stmtLocalsLtAndNoDead0 calleeLocs.length stmt = true) :
    evalStatement caller' { f with locals := cSlots ++ eSlots } mem
        (shiftStmtUnw callerLocs.length stmt) =
      match evalStatement callee { f with locals := eSlots } mem stmt with
      | .fault k => .fault k
      | .done out => .done out
      | .step st' =>
        match st'.frames with
        | [f'] =>
          .step { frames := [{ f' with locals := cSlots ++ f'.locals }],
                  callerMem := st'.callerMem }
        | _ => .fault .unsupported := by
  cases stmt with
  | nop => rfl
  | unsupported => rfl
  | storageLive id =>
    dsimp [shiftStmtUnw, evalStatement]
    rw [hLocs', hCalleeLocs, getElem?_append_right_comm callerLocs calleeLocs id]
    cases Trusted.MirSemantics.getElem? calleeLocs id with
    | none => rfl
    | some ty =>
      dsimp
      rw [← hLenC, setElem?_append_right_comm cSlots eSlots id (liveUninitSlot ty)]
      cases setElem? eSlots id (liveUninitSlot ty) <;> rfl
  | storageDead id =>
    dsimp [stmtLocalsLtAndNoDead0] at hAd
    let ⟨hNe0, _⟩ := bool_and_true hAd
    have hIdNe0 : Nat.beq id 0 = false := bool_not_true hNe0
    have hShiftNe0 : Nat.beq (id + callerLocs.length) 0 = false := by
      have hGt : 0 < id + callerLocs.length := Nat.lt_of_lt_of_le hPosC (Nat.le_add_left _ _)
      exact nat_beq_false_of_ne (Nat.ne_of_gt hGt)
    dsimp [shiftStmtUnw, evalStatement]
    rw [hIdNe0, hShiftNe0]
    dsimp
    rw [← hLenC, setElem?_append_right_comm cSlots eSlots id .dead]
    cases setElem? eSlots id .dead <;> rfl
  | assign dst rv =>
    dsimp [shiftStmtUnw, shiftPlaceUnw, evalStatement]
    rw [hLocs', hCalleeLocs]
    cases !dst.projection.isEmpty with
    | true => rfl
    | false =>
      dsimp
      rw [getElem?_append_right_comm callerLocs calleeLocs dst.localId]
      cases Trusted.MirSemantics.getElem? calleeLocs dst.localId with
      | none => rfl
      | some dstTy =>
        dsimp
        rw [evalRvalue_suffix hLenC]
        cases evalRvalue calleeLocs eSlots dstTy rv with
        | error _ => rfl
        | ok pr =>
          dsimp
          rw [← hLenC, writePlace_suffix]
          cases writePlace pr.2 dst.localId dstTy pr.1 <;> rfl

/-! ### Part 2: Operand Type Agreement & `callArgsTyMatch` -/

private theorem operandTy?_eq_evalOperandToSlot {bodyLocals : List MirTy}
    {locals : List LocalSlot} {op : Operand} {opTy srcTy : MirTy}
    {ov : Option Val} {locals' : List LocalSlot}
    (hTy : operandTy? bodyLocals op = some opTy)
    (hEv : evalOperandToSlot bodyLocals locals op = .ok (srcTy, ov, locals')) :
    srcTy = opTy := by
  cases op with
  | constant c =>
    dsimp [operandTy?] at hTy
    injection hTy with h1
    dsimp [evalOperandToSlot] at hEv
    cases hc : evalConstLit c.ty c.lit with
    | error _ => rw [hc] at hEv; cases hEv
    | ok v =>
      rw [hc] at hEv; dsimp at hEv
      injection hEv with hp; injection hp with h2 _
      rw [← h2, h1]
  | copy pl =>
    dsimp [operandTy?] at hTy
    dsimp [evalOperandToSlot] at hEv
    cases hp : pl.projection.isEmpty with
    | false => rw [hp] at hTy; cases hTy
    | true =>
      rw [hp] at hTy hEv; dsimp at hTy hEv
      rw [hTy] at hEv
      cases hS : Trusted.MirSemantics.getElem? locals pl.localId with
      | none => rw [hS] at hEv; cases hEv
      | some sl =>
        rw [hS] at hEv
        cases sl with
        | dead => cases hEv
        | live _ =>
          injection hEv with hp2; injection hp2 with h2 _
          exact h2.symm
  | move pl =>
    dsimp [operandTy?] at hTy
    dsimp [evalOperandToSlot] at hEv
    cases hp : pl.projection.isEmpty with
    | false => rw [hp] at hTy; cases hTy
    | true =>
      rw [hp] at hTy hEv; dsimp at hTy hEv
      rw [hTy] at hEv
      cases hS : Trusted.MirSemantics.getElem? locals pl.localId with
      | none => rw [hS] at hEv; cases hEv
      | some sl =>
        rw [hS] at hEv
        cases sl with
        | dead => cases hEv
        | live _ =>
          dsimp at hEv
          cases hSet : setElem? locals pl.localId (liveUninitSlot opTy) with
          | none => rw [hSet] at hEv; cases hEv
          | some _ =>
            rw [hSet] at hEv; dsimp at hEv
            injection hEv with hp2; injection hp2 with h2 _
            exact h2.symm

private theorem callArgsTyMatch_checkArgsMatch {callerLocals : List MirTy} :
    ∀ {args : List Operand} {paramTys : List MirTy}
      {cSlots cSlots' : List LocalSlot} {vs : List Val},
      callArgsTyMatch callerLocals args paramTys = true →
      cSlots.length = callerLocals.length →
      (∀ (i : Nat) (ty : MirTy) (vi : Val),
        Trusted.MirSemantics.getElem? callerLocals i = some ty →
        Trusted.MirSemantics.getElem? cSlots i = some (.live (some vi)) →
        checkVal vi ty = true) →
      evalCallArgsUnw callerLocals cSlots args = .ok (vs, cSlots') →
      checkArgsMatch vs paramTys = true
  | [], [], _, _, _, _, _, _, hEv => by
    dsimp [evalCallArgsUnw] at hEv
    injection hEv with hp; injection hp with hv _; subst hv; rfl
  | [], _ :: _, _, _, _, hMatch, _, _, _ => by cases hMatch
  | _ :: _, [], _, _, _, hMatch, _, _, _ => by cases hMatch
  | op :: ops, ty :: tys, cSlots, cSlots', vs, hMatch, hLen, hWt, hEv => by
    dsimp [callArgsTyMatch] at hMatch
    cases hOpTy : operandTy? callerLocals op with
    | none => rw [hOpTy] at hMatch; cases hMatch
    | some opTy =>
      rw [hOpTy] at hMatch; dsimp at hMatch
      let ⟨hBeq, hRestM⟩ := bool_and_true hMatch
      have hTyEq : opTy = ty := mirTy_beq_eq hBeq
      dsimp [evalCallArgsUnw] at hEv
      cases hOp : evalOperandToSlot callerLocals cSlots op with
      | error _ => rw [hOp] at hEv; cases hEv
      | ok tup =>
        cases tup with
        | mk srcTy pr1 =>
          cases pr1 with
          | mk ov locs1 =>
            rw [hOp] at hEv
            let ⟨hL1, hValTy, hW1⟩ := evalOperandToSlot_wf hLen hWt hOp
            have hSrcEq : srcTy = opTy := operandTy?_eq_evalOperandToSlot hOpTy hOp
            cases ov with
            | none => cases hEv
            | some v =>
              dsimp at hEv
              cases hRest : evalCallArgsUnw callerLocals locs1 ops with
              | error _ => rw [hRest] at hEv; cases hEv
              | ok pr =>
                rw [hRest] at hEv; dsimp at hEv
                injection hEv with hp; injection hp with hv _; subst hv
                dsimp [checkArgsMatch]
                have hCv : checkVal v ty = true := by
                  rw [← hTyEq, ← hSrcEq]; exact hValTy v rfl
                have hCr : checkArgsMatch pr.1 tys = true :=
                  callArgsTyMatch_checkArgsMatch hRestM hL1 hW1 hRest
                rw [hCv, hCr]; rfl

/-! ### Part 3: Unpacked `InlineUnwCtx` & Static Preservation Lemmas -/

private noncomputable def inlineNormalExitTerm : Option BasicBlockId → TerminatorKind
  | some tBb => .goto tBb
  | none => .unreachable

private structure InlineUnwCtx (pSrc pTgt : Program) (site : UnwindInlineSite) where
  caller : Body
  callee : Body
  callBb : BasicBlock
  args : List Operand
  dst : Place
  target : Option BasicBlockId
  callerUnwind : UnwindAction
  callerBbsUpdated : List BasicBlock
  bodies' : List Body
  hNe : site.callerDefId ≠ site.calleeDefId
  hCaller : Trusted.MirSemantics.getElem? pSrc.bodies site.callerDefId = some caller
  hCallee : Trusted.MirSemantics.getElem? pSrc.bodies site.calleeDefId = some callee
  hCalleeAdm : calleeUnwindInlineAdmitted callee = true
  hCallerAdm : callerUnwindInlineAdmitted caller = true
  hCallBb : Trusted.MirSemantics.getElem? caller.basicBlocks site.callBlock = some callBb
  hNotClean : callBb.cleanup = false
  hTerm : callBb.terminator = .call site.calleeDefId args dst target callerUnwind
  hDstCompat : callDstCompatible caller callee dst = true
  hArgsMatch : callArgsTyMatch caller.locals args
      ((callee.locals.drop 1).take callee.argumentCount) = true
  hTargetOk : ∀ (tBb : BasicBlockId), target = some tBb →
      ∃ tData : BasicBlock,
        Trusted.MirSemantics.getElem? caller.basicBlocks tBb = some tData ∧
        tData.cleanup = false
  hUnwindOk : ∀ (pBb : BasicBlockId), callerUnwind = .cleanup pBb →
      ∃ pData : BasicBlock,
        Trusted.MirSemantics.getElem? caller.basicBlocks pBb = some pData ∧
        pData.cleanup = true
  hSetBb : setElem? caller.basicBlocks site.callBlock {
      statements := callBb.statements ++
        mkCalleeEntryStorageLive callee caller.locals.length 0 callee.locals.length ++
        mkArgBindStmts caller.locals.length 0 args
      terminator := .goto caller.basicBlocks.length
      cleanup := false
    } = some callerBbsUpdated
  hSetBody : setElem? pSrc.bodies site.callerDefId {
      caller with
      locals := caller.locals ++ callee.locals
      basicBlocks := callerBbsUpdated ++
        callee.basicBlocks.map (shiftCalleeBlock caller.locals.length
          caller.basicBlocks.length
          (caller.basicBlocks.length + callee.basicBlocks.length)
          (caller.basicBlocks.length + callee.basicBlocks.length + 1)) ++
        [{
          statements :=
            (.assign dst (.use (.move { localId := caller.locals.length, projection := [] }))) ::
              mkAllStorageDead caller.locals.length callee.locals.length
          terminator := inlineNormalExitTerm target
          cleanup := false
        }, {
          statements := mkAllStorageDead caller.locals.length callee.locals.length
          terminator := callerUnwindToExitTerm callerUnwind
          cleanup := true
        }]
    } = some bodies'
  hPtgt : pTgt = { pSrc with bodies := bodies' }

namespace InlineUnwCtx

private noncomputable def locOff {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) : Nat :=
  ctx.caller.locals.length

private noncomputable def bbOff {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) : Nat :=
  ctx.caller.basicBlocks.length

private noncomputable def normalExitBb {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) : BasicBlockId :=
  ctx.bbOff + ctx.callee.basicBlocks.length

private noncomputable def unwindExitBb {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) : BasicBlockId :=
  ctx.normalExitBb + 1

private noncomputable def entryLives {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) : List StatementKind :=
  mkCalleeEntryStorageLive ctx.callee ctx.locOff 0 ctx.callee.locals.length

private noncomputable def argBinds {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) : List StatementKind :=
  mkArgBindStmts ctx.locOff 0 ctx.args

private noncomputable def deads {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) : List StatementKind :=
  mkAllStorageDead ctx.locOff ctx.callee.locals.length

private noncomputable def callBb' {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) : BasicBlock := {
  statements := ctx.callBb.statements ++ ctx.entryLives ++ ctx.argBinds
  terminator := .goto ctx.bbOff
  cleanup := false
}

private noncomputable def shiftedCalleeBbs {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) : List BasicBlock :=
  ctx.callee.basicBlocks.map
    (shiftCalleeBlock ctx.locOff ctx.bbOff ctx.normalExitBb ctx.unwindExitBb)

private noncomputable def normalExitBlock {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) : BasicBlock := {
  statements :=
    (.assign ctx.dst (.use (.move { localId := ctx.locOff, projection := [] }))) ::
      ctx.deads
  terminator := inlineNormalExitTerm ctx.target
  cleanup := false
}

private noncomputable def unwindExitBlock {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) : BasicBlock := {
  statements := ctx.deads
  terminator := callerUnwindToExitTerm ctx.callerUnwind
  cleanup := true
}

private noncomputable def caller' {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) : Body := {
  ctx.caller with
  locals := ctx.caller.locals ++ ctx.callee.locals
  basicBlocks := ctx.callerBbsUpdated ++ ctx.shiftedCalleeBbs ++
    [ctx.normalExitBlock, ctx.unwindExitBlock]
}

end InlineUnwCtx

private theorem unpack_setBody_some {pSrc pTgt : Program} {defId : DefId} {b : Body}
    (h : (match setElem? pSrc.bodies defId b with
          | none => none
          | some bodies' => some { pSrc with bodies := bodies' }) = some pTgt) :
    ∃ bodies', setElem? pSrc.bodies defId b = some bodies' ∧
      pTgt = { pSrc with bodies := bodies' } := by
  cases hS : setElem? pSrc.bodies defId b with
  | none => rw [hS] at h; cases h
  | some bodies' =>
    rw [hS] at h; injection h with hP
    exact ⟨bodies', rfl, hP.symm⟩

private theorem unpack_applyInlineWithUnwind {pSrc pTgt : Program} {site : UnwindInlineSite}
    (h : applyInlineWithUnwind pSrc site = some pTgt) :
    Nonempty (InlineUnwCtx pSrc pTgt site) := by
  unfold applyInlineWithUnwind at h
  cases hEq : Nat.beq site.callerDefId site.calleeDefId with
  | true => rw [hEq] at h; cases h
  | false =>
    rw [hEq] at h; dsimp at h
    cases hC : Trusted.MirSemantics.getElem? pSrc.bodies site.callerDefId with
    | none => rw [hC] at h; cases h
    | some caller =>
      rw [hC] at h
      cases hE : Trusted.MirSemantics.getElem? pSrc.bodies site.calleeDefId with
      | none => rw [hE] at h; cases h
      | some callee =>
        rw [hE] at h; dsimp at h
        cases hEa : calleeUnwindInlineAdmitted callee with
        | false => rw [hEa] at h; cases h
        | true =>
          rw [hEa] at h
          cases hCa : callerUnwindInlineAdmitted caller with
          | false => rw [hCa] at h; cases h
          | true =>
            rw [hCa] at h; dsimp at h
            cases hBb : Trusted.MirSemantics.getElem? caller.basicBlocks site.callBlock with
            | none => rw [hBb] at h; cases h
            | some callBb =>
              rw [hBb] at h; dsimp at h
              cases hCl : callBb.cleanup with
              | true => rw [hCl] at h; cases h
              | false =>
                rw [hCl] at h; dsimp at h
                cases hTm : callBb.terminator with
                | goto _ | switchInt _ _ | return_ | unreachable
                | unwindResume | assert _ _ _ _ _ | unsupported =>
                  rw [hTm] at h; cases h
                | call cDef args dst target callerUnwind =>
                  rw [hTm] at h; dsimp at h
                  cases hCd : Nat.beq cDef site.calleeDefId with
                  | false => rw [hCd] at h; cases h
                  | true =>
                    rw [hCd] at h
                    have hCdEq : cDef = site.calleeDefId := nat_beq_eq hCd
                    subst hCdEq
                    cases hDst : callDstCompatible caller callee dst with
                    | false => rw [hDst] at h; cases h
                    | true =>
                      rw [hDst] at h
                      cases hArg : callArgsTyMatch caller.locals args
                          ((callee.locals.drop 1).take callee.argumentCount) with
                      | false => rw [hArg] at h; cases h
                      | true =>
                        rw [hArg] at h
                        have hIfSplit : ∀ {α : Type} {a b : Bool} {v : Option α} {x : α},
                            (if ((!true || !true || !true || !a) || !b) = true then none else v) =
                              some x →
                            a = true ∧ b = true ∧ v = some x := by
                          intro α a b v x h0
                          cases a with
                          | false => cases h0
                          | true =>
                            cases b with
                            | false => cases h0
                            | true => exact ⟨rfl, rfl, h0⟩
                        let ⟨hTargetOk, hUnwindOk, hElse⟩ := hIfSplit h
                        cases hSetBb : setElem? caller.basicBlocks site.callBlock {
                          statements := callBb.statements ++
                            mkCalleeEntryStorageLive callee caller.locals.length 0
                              callee.locals.length ++
                            mkArgBindStmts caller.locals.length 0 args
                          terminator := .goto caller.basicBlocks.length
                          cleanup := false
                        } with
                        | none => rw [hSetBb] at hElse; cases hElse
                        | some callerBbsUpdated =>
                          rw [hSetBb] at hElse; dsimp at hElse
                          let ⟨bodies', hSetB, hP⟩ := unpack_setBody_some hElse
                          have hTargetOk' : ∀ (tBb : BasicBlockId), target = some tBb →
                              ∃ tData : BasicBlock,
                                Trusted.MirSemantics.getElem? caller.basicBlocks tBb = some tData ∧
                                tData.cleanup = false := by
                            intro tBb ht
                            subst ht; dsimp at hTargetOk
                            cases hG : Trusted.MirSemantics.getElem? caller.basicBlocks tBb with
                            | none => rw [hG] at hTargetOk; cases hTargetOk
                            | some tData =>
                              rw [hG] at hTargetOk
                              exact ⟨tData, rfl, bool_not_true hTargetOk⟩
                          have hUnwindOk' : ∀ (pBb : BasicBlockId), callerUnwind = .cleanup pBb →
                              ∃ pData : BasicBlock,
                                Trusted.MirSemantics.getElem? caller.basicBlocks pBb = some pData ∧
                                pData.cleanup = true := by
                            intro pBb hp
                            subst hp; dsimp at hUnwindOk
                            cases hG : Trusted.MirSemantics.getElem? caller.basicBlocks pBb with
                            | none => rw [hG] at hUnwindOk; cases hUnwindOk
                            | some pData =>
                              rw [hG] at hUnwindOk
                              exact ⟨pData, rfl, hUnwindOk⟩
                          have hSetB' : setElem? pSrc.bodies site.callerDefId {
                            caller with
                            locals := caller.locals ++ callee.locals
                            basicBlocks := callerBbsUpdated ++
                              callee.basicBlocks.map (shiftCalleeBlock caller.locals.length
                                caller.basicBlocks.length
                                (caller.basicBlocks.length + callee.basicBlocks.length)
                                (caller.basicBlocks.length + callee.basicBlocks.length + 1)) ++
                              [{
                                statements :=
                                  (.assign dst (.use (.move ⟨caller.locals.length, []⟩))) ::
                                    mkAllStorageDead caller.locals.length callee.locals.length
                                terminator := inlineNormalExitTerm target
                                cleanup := false
                              }, {
                                statements := mkAllStorageDead caller.locals.length
                                  callee.locals.length
                                terminator := callerUnwindToExitTerm callerUnwind
                                cleanup := true
                              }]
                          } = some bodies' := by
                            cases target <;> exact hSetB
                          exact ⟨{
                            caller := caller
                            callee := callee
                            callBb := callBb
                            args := args
                            dst := dst
                            target := target
                            callerUnwind := callerUnwind
                            callerBbsUpdated := callerBbsUpdated
                            bodies' := bodies'
                            hNe := nat_ne_of_beq_false hEq
                            hCaller := hC
                            hCallee := hE
                            hCalleeAdm := hEa
                            hCallerAdm := hCa
                            hCallBb := hBb
                            hNotClean := hCl
                            hTerm := hTm
                            hDstCompat := hDst
                            hArgsMatch := hArg
                            hTargetOk := hTargetOk'
                            hUnwindOk := hUnwindOk'
                            hSetBb := hSetBb
                            hSetBody := hSetB'
                            hPtgt := hP
                          }⟩

/-! #### Basic Static Projections on `InlineUnwCtx` -/

private theorem list_any_false_of_all {α : Type} {p : α → Bool} :
    ∀ {xs : List α}, xs.all (fun x => !p x) = true → xs.any p = false
  | [], _ => rfl
  | x :: xs, h => by
    dsimp [List.all] at h
    let ⟨h1, h2⟩ := bool_and_true h
    dsimp [List.any]
    rw [bool_not_true h1]
    exact list_any_false_of_all h2

private theorem ctx_caller_argLt {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) :
    ctx.caller.argumentCount < ctx.locOff := by
  have h := ctx.hCallerAdm
  unfold callerUnwindInlineAdmitted at h
  let ⟨h12, _⟩ := bool_and_true h
  let ⟨h1, _⟩ := bool_and_true h12
  exact nat_blt_lt h1

private theorem ctx_locOff_pos {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) :
    0 < ctx.locOff :=
  Nat.lt_of_le_of_lt (Nat.zero_le _) (ctx_caller_argLt ctx)

private theorem ctx_caller_storageInBounds {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) :
    storageAnnotationsInBounds ctx.caller = true := by
  have h := ctx.hCallerAdm
  unfold callerUnwindInlineAdmitted at h
  let ⟨h12, _⟩ := bool_and_true h
  let ⟨_, h2⟩ := bool_and_true h12
  exact h2

private theorem ctx_caller_bbs_all {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) :
    ctx.caller.basicBlocks.all (fun bb =>
      bb.statements.all (callerStmtLocalsLt ctx.locOff) &&
      callerTermInBounds ctx.locOff ctx.bbOff bb.terminator) = true := by
  have h := ctx.hCallerAdm
  unfold callerUnwindInlineAdmitted at h
  let ⟨_, h3⟩ := bool_and_true h
  exact h3

private theorem ctx_callee_nonEmpty {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) :
    ctx.callee.basicBlocks.isEmpty = false := by
  have h := ctx.hCalleeAdm
  unfold calleeUnwindInlineAdmitted at h
  let ⟨h1234, _⟩ := bool_and_true h
  let ⟨h123, _⟩ := bool_and_true h1234
  let ⟨h12, _⟩ := bool_and_true h123
  let ⟨h1, _⟩ := bool_and_true h12
  exact bool_not_true h1

private theorem ctx_callee_argLt {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) :
    ctx.callee.argumentCount < ctx.callee.locals.length := by
  have h := ctx.hCalleeAdm
  unfold calleeUnwindInlineAdmitted at h
  let ⟨h1234, _⟩ := bool_and_true h
  let ⟨h123, _⟩ := bool_and_true h1234
  let ⟨h12, _⟩ := bool_and_true h123
  let ⟨_, h2⟩ := bool_and_true h12
  exact nat_blt_lt h2

private theorem ctx_callee_storageInBounds {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) :
    storageAnnotationsInBounds ctx.callee = true := by
  have h := ctx.hCalleeAdm
  unfold calleeUnwindInlineAdmitted at h
  let ⟨h1234, _⟩ := bool_and_true h
  let ⟨h123, _⟩ := bool_and_true h1234
  let ⟨_, h3⟩ := bool_and_true h123
  exact h3

private theorem ctx_callee_locals_supported {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) :
    ctx.callee.locals.all isSupportedScalarOrUnitTy = true := by
  have h := ctx.hCalleeAdm
  unfold calleeUnwindInlineAdmitted at h
  let ⟨h1234, _⟩ := bool_and_true h
  let ⟨_, h4⟩ := bool_and_true h1234
  exact h4

private theorem ctx_callee_bbs_all {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) :
    ctx.callee.basicBlocks.all (fun bb =>
      bb.statements.all (stmtLocalsLtAndNoDead0 ctx.callee.locals.length) &&
      termWellScoped ctx.callee.locals.length ctx.callee.basicBlocks.length
        ctx.callee.basicBlocks bb.terminator) = true := by
  have h := ctx.hCalleeAdm
  unfold calleeUnwindInlineAdmitted at h
  let ⟨_, h5⟩ := bool_and_true h
  exact h5

private theorem ctx_bodies_length {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) :
    pTgt.bodies.length = pSrc.bodies.length := by
  rw [ctx.hPtgt]
  exact setElem?_length ctx.hSetBody

private theorem ctx_bodies_lookup_eq {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) :
    Trusted.MirSemantics.getElem? pTgt.bodies site.callerDefId = some ctx.caller' := by
  have hB : pTgt.bodies = ctx.bodies' := congrArg Program.bodies ctx.hPtgt
  rw [hB]
  exact setElem?_getElem?_same ctx.hSetBody

private theorem ctx_bodies_lookup_ne {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) {d : DefId} (hNe : d ≠ site.callerDefId) :
    Trusted.MirSemantics.getElem? pTgt.bodies d =
      Trusted.MirSemantics.getElem? pSrc.bodies d := by
  have hB : pTgt.bodies = ctx.bodies' := congrArg Program.bodies ctx.hPtgt
  rw [hB]
  exact setElem?_getElem?_ne ctx.hSetBody hNe

private theorem ctx_callerBbsUpdated_len {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) :
    ctx.callerBbsUpdated.length = ctx.bbOff :=
  setElem?_length ctx.hSetBb

private theorem ctx_caller'_bb_lookup_ne {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) {b : BasicBlockId}
    (hLt : b < ctx.bbOff) (hNe : b ≠ site.callBlock) :
    Trusted.MirSemantics.getElem? ctx.caller'.basicBlocks b =
      Trusted.MirSemantics.getElem? ctx.caller.basicBlocks b := by
  dsimp [InlineUnwCtx.caller']
  have hLt1 : b < ctx.callerBbsUpdated.length := by
    rw [ctx_callerBbsUpdated_len ctx]; exact hLt
  have hLt2 : b < (ctx.callerBbsUpdated ++ ctx.shiftedCalleeBbs).length := by
    rw [list_length_append]; exact Nat.lt_of_lt_of_le hLt1 (Nat.le_add_right _ _)
  rw [getElem?_append_left hLt2, getElem?_append_left hLt1]
  exact setElem?_getElem?_ne ctx.hSetBb hNe

private theorem ctx_caller'_bb_lookup_call {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) :
    Trusted.MirSemantics.getElem? ctx.caller'.basicBlocks site.callBlock =
      some ctx.callBb' := by
  dsimp [InlineUnwCtx.caller']
  have hLt0 : site.callBlock < ctx.bbOff := getElem?_some_lt ctx.hCallBb
  have hLt1 : site.callBlock < ctx.callerBbsUpdated.length := by
    rw [ctx_callerBbsUpdated_len ctx]; exact hLt0
  have hLt2 : site.callBlock < (ctx.callerBbsUpdated ++ ctx.shiftedCalleeBbs).length := by
    rw [list_length_append]; exact Nat.lt_of_lt_of_le hLt1 (Nat.le_add_right _ _)
  rw [getElem?_append_left hLt2, getElem?_append_left hLt1]
  exact setElem?_getElem?_same ctx.hSetBb

private theorem ctx_caller'_bb_lookup_callee {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) {b : BasicBlockId}
    (hLt : b < ctx.callee.basicBlocks.length) :
    Trusted.MirSemantics.getElem? ctx.caller'.basicBlocks (b + ctx.bbOff) =
      match Trusted.MirSemantics.getElem? ctx.callee.basicBlocks b with
      | some bb =>
        some (shiftCalleeBlock ctx.locOff ctx.bbOff ctx.normalExitBb ctx.unwindExitBb bb)
      | none => none := by
  dsimp [InlineUnwCtx.caller']
  have hLenU : ctx.callerBbsUpdated.length = ctx.bbOff := ctx_callerBbsUpdated_len ctx
  have hLenS : ctx.shiftedCalleeBbs.length = ctx.callee.basicBlocks.length :=
    list_length_map _ _
  have hLt2 : b + ctx.bbOff < (ctx.callerBbsUpdated ++ ctx.shiftedCalleeBbs).length := by
    rw [list_length_append, hLenU, hLenS, Nat.add_comm]
    exact Nat.add_lt_add_left hLt ctx.bbOff
  rw [getElem?_append_left hLt2]
  have hEq : Trusted.MirSemantics.getElem? (ctx.callerBbsUpdated ++ ctx.shiftedCalleeBbs)
      (b + ctx.bbOff) = Trusted.MirSemantics.getElem? ctx.shiftedCalleeBbs b := by
    rw [← hLenU]
    exact getElem?_append_right_comm ctx.callerBbsUpdated ctx.shiftedCalleeBbs b
  rw [hEq]
  dsimp [InlineUnwCtx.shiftedCalleeBbs]
  rw [getElem?_map]
  cases Trusted.MirSemantics.getElem? ctx.callee.basicBlocks b <;> rfl

private theorem ctx_caller'_bb_lookup_normalExit {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) :
    Trusted.MirSemantics.getElem? ctx.caller'.basicBlocks ctx.normalExitBb =
      some ctx.normalExitBlock := by
  dsimp [InlineUnwCtx.caller', InlineUnwCtx.normalExitBb]
  have hLen : (ctx.callerBbsUpdated ++ ctx.shiftedCalleeBbs).length =
      ctx.bbOff + ctx.callee.basicBlocks.length := by
    rw [list_length_append, ctx_callerBbsUpdated_len ctx]
    dsimp [InlineUnwCtx.shiftedCalleeBbs]
    rw [list_length_map]
  have hEq : ctx.bbOff + ctx.callee.basicBlocks.length =
      (ctx.callerBbsUpdated ++ ctx.shiftedCalleeBbs).length + 0 := by
    rw [hLen, Nat.add_zero]
  rw [hEq, getElem?_append_right]
  rfl

private theorem ctx_caller'_bb_lookup_unwindExit {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) :
    Trusted.MirSemantics.getElem? ctx.caller'.basicBlocks ctx.unwindExitBb =
      some ctx.unwindExitBlock := by
  dsimp [InlineUnwCtx.caller', InlineUnwCtx.unwindExitBb, InlineUnwCtx.normalExitBb]
  have hLen : (ctx.callerBbsUpdated ++ ctx.shiftedCalleeBbs).length =
      ctx.bbOff + ctx.callee.basicBlocks.length := by
    rw [list_length_append, ctx_callerBbsUpdated_len ctx]
    dsimp [InlineUnwCtx.shiftedCalleeBbs]
    rw [list_length_map]
  rw [← hLen, getElem?_append_right]
  rfl

/-! #### Storage Annotations & `initLocalsLoop` Agreement for `caller'` -/

private theorem mkCalleeEntryStorageLive_inBounds (callee : Body) (locOff : Nat) :
    ∀ (i rem : Nat),
      i + rem ≤ callee.locals.length →
      (mkCalleeEntryStorageLive callee locOff i rem).all (fun stmt =>
        match stmt with
        | .storageLive id | .storageDead id =>
          Nat.blt id (locOff + callee.locals.length)
        | _ => true) = true
  | _, 0, _ => rfl
  | i, rem + 1, hLe => by
    dsimp [mkCalleeEntryStorageLive]
    have hNext : i + 1 + rem ≤ callee.locals.length := by
      have hEq : i + 1 + rem = i + (rem + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 rem]
      rw [hEq]; exact hLe
    have hIh := mkCalleeEntryStorageLive_inBounds callee locOff (i + 1) rem hNext
    cases (Nat.ble i callee.argumentCount || !hasStorageAnnotation callee i) with
    | false => exact hIh
    | true =>
      dsimp [List.all]
      have hILt : i < callee.locals.length :=
        Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_succ_self i)
          (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le rem)) i)) hLe
      have hLt : locOff + i < locOff + callee.locals.length :=
        Nat.add_lt_add_left hILt locOff
      rw [nat_lt_blt hLt, hIh]; rfl

private theorem mkCalleeEntryStorageLive_noLow (callee : Body) (locOff : Nat) (x : Nat)
    (hx : x < locOff) :
    ∀ (i rem : Nat),
      (mkCalleeEntryStorageLive callee locOff i rem).any (stmtHasStorageMarker x) = false
  | _, 0 => rfl
  | i, rem + 1 => by
    dsimp [mkCalleeEntryStorageLive]
    have hIh := mkCalleeEntryStorageLive_noLow callee locOff x hx (i + 1) rem
    cases (Nat.ble i callee.argumentCount || !hasStorageAnnotation callee i) with
    | false => exact hIh
    | true =>
      dsimp [List.any, stmtHasStorageMarker]
      have hNe : Nat.beq (locOff + i) x = false :=
        nat_beq_false_of_ne (Nat.ne_of_gt (Nat.lt_of_lt_of_le hx (Nat.le_add_right _ _)))
      rw [hNe]; exact hIh

private theorem mkArgBindStmts_noStorage (locOff : Nat) :
    ∀ (idx : Nat) (ops : List Operand),
      (mkArgBindStmts locOff idx ops).all (fun stmt =>
        match stmt with
        | .storageLive _ | .storageDead _ => false
        | _ => true) = true
  | _, [] => rfl
  | idx, _ :: ops => mkArgBindStmts_noStorage locOff (idx + 1) ops

private theorem mkArgBindStmts_any_marker_false (locOff x : Nat) :
    ∀ (idx : Nat) (ops : List Operand),
      (mkArgBindStmts locOff idx ops).any (stmtHasStorageMarker x) = false
  | _, [] => rfl
  | idx, _ :: ops => mkArgBindStmts_any_marker_false locOff x (idx + 1) ops

private theorem mkAllStorageDead_inBounds (locOff total : Nat) :
    ∀ (n : Nat), n ≤ total →
      (mkAllStorageDead locOff n).all (fun stmt =>
        match stmt with
        | .storageLive id | .storageDead id => Nat.blt id (locOff + total)
        | _ => true) = true
  | 0, _ => rfl
  | n + 1, hLe => by
    dsimp [mkAllStorageDead, List.all]
    have hLt : locOff + n < locOff + total :=
      Nat.add_lt_add_left (Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hLe) locOff
    have hIh := mkAllStorageDead_inBounds locOff total n (Nat.le_of_succ_le hLe)
    rw [nat_lt_blt hLt, hIh]; rfl

private theorem mkAllStorageDead_noLow (locOff x : Nat) (hx : x < locOff) :
    ∀ (n : Nat),
      (mkAllStorageDead locOff n).any (stmtHasStorageMarker x) = false
  | 0 => rfl
  | n + 1 => by
    dsimp [mkAllStorageDead, List.any, stmtHasStorageMarker]
    have hNe : Nat.beq (locOff + n) x = false :=
      nat_beq_false_of_ne (Nat.ne_of_gt (Nat.lt_of_lt_of_le hx (Nat.le_add_right _ _)))
    rw [hNe]
    exact mkAllStorageDead_noLow locOff x hx n

private theorem mkAllStorageDead_has (locOff : Nat) :
    ∀ (n j : Nat), j < n →
      (mkAllStorageDead locOff n).any (stmtHasStorageMarker (locOff + j)) = true
  | 0, _, h => False.elim (Nat.not_lt_zero _ h)
  | n + 1, j, h => by
    dsimp [mkAllStorageDead, List.any, stmtHasStorageMarker]
    cases hEq : Nat.beq (locOff + n) (locOff + j) with
    | true => rfl
    | false =>
      have hNe : j ≠ n := by
        intro hjn; subst hjn; rw [nat_beq_refl] at hEq; cases hEq
      have hLt : j < n := Nat.lt_of_le_of_ne (Nat.le_of_succ_le_succ h) hNe
      exact mkAllStorageDead_has locOff n j hLt

private theorem ctx_caller'_storageInBounds {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) :
    storageAnnotationsInBounds ctx.caller' = true := by
  unfold storageAnnotationsInBounds
  dsimp [InlineUnwCtx.caller']
  rw [list_length_append]
  have hCheckCaller : ∀ (bb : BasicBlock),
      bb.statements.all (callerStmtLocalsLt ctx.locOff) = true →
      ∀ (j : Nat) (st : StatementKind),
        Trusted.MirSemantics.getElem? bb.statements j = some st →
        (match st with
         | .storageLive id | .storageDead id =>
           Nat.blt id (ctx.caller.locals.length + ctx.callee.locals.length)
         | _ => true) = true := by
    intro bb hAll j st hSt
    have h1 := list_all_getElem? hAll hSt
    cases st with
    | assign _ _ | nop | unsupported => rfl
    | storageLive id =>
      dsimp [callerStmtLocalsLt] at h1
      exact nat_lt_blt (Nat.lt_of_lt_of_le (nat_blt_lt h1) (Nat.le_add_right _ _))
    | storageDead id =>
      dsimp [callerStmtLocalsLt] at h1
      exact nat_lt_blt (Nat.lt_of_lt_of_le (nat_blt_lt h1) (Nat.le_add_right _ _))
  rw [list_all_append, list_all_append]
  apply bool_and_intro
  · apply bool_and_intro
    · apply list_all_of_getElem?
      intro i bb hBb
      cases hEq : Nat.beq i site.callBlock with
      | true =>
        have hi : i = site.callBlock := nat_beq_eq hEq
        subst hi
        rw [setElem?_getElem?_same ctx.hSetBb] at hBb
        injection hBb with hB; subst hB
        dsimp [InlineUnwCtx.callBb']
        rw [list_all_append, list_all_append]
        apply bool_and_intro
        · apply bool_and_intro
          · apply list_all_of_getElem?
            have hOrig := list_all_getElem? (ctx_caller_bbs_all ctx) ctx.hCallBb
            let ⟨hOrigS, _⟩ := bool_and_true hOrig
            exact hCheckCaller ctx.callBb hOrigS
          · apply list_all_of_getElem?
            intro j st hSt
            have hM := list_all_getElem?
              (mkCalleeEntryStorageLive_inBounds ctx.callee ctx.locOff 0
                ctx.callee.locals.length (by rw [Nat.zero_add]; exact Nat.le_refl _)) hSt
            cases st with
            | assign _ _ | nop | unsupported => rfl
            | storageLive id => exact hM
            | storageDead id => exact hM
        · apply list_all_of_getElem?
          intro j st hSt
          have hNo := list_all_getElem? (mkArgBindStmts_noStorage ctx.locOff 0 ctx.args) hSt
          cases st with
          | storageLive _ | storageDead _ => cases hNo
          | assign _ _ | nop | unsupported => rfl
      | false =>
        have hNe : i ≠ site.callBlock := nat_ne_of_beq_false hEq
        rw [setElem?_getElem?_ne ctx.hSetBb hNe] at hBb
        have hOrig := list_all_getElem? (ctx_caller_bbs_all ctx) hBb
        let ⟨hOrigS, _⟩ := bool_and_true hOrig
        apply list_all_of_getElem?
        exact hCheckCaller bb hOrigS
    · dsimp [InlineUnwCtx.shiftedCalleeBbs]
      rw [list_all_map]
      apply list_all_of_getElem?
      intro i bb hBb
      dsimp [shiftCalleeBlock]
      rw [list_all_map]
      have hCb := list_all_getElem? (ctx_callee_bbs_all ctx) hBb
      let ⟨hCbS, _⟩ := bool_and_true hCb
      apply list_all_of_getElem?
      intro j st hSt
      have h1 := list_all_getElem? hCbS hSt
      cases st with
      | assign _ _ | nop | unsupported => rfl
      | storageLive id =>
        dsimp [stmtLocalsLtAndNoDead0] at h1
        dsimp [shiftStmtUnw, InlineUnwCtx.locOff]
        have hLt : id + ctx.caller.locals.length <
            ctx.caller.locals.length + ctx.callee.locals.length := by
          rw [Nat.add_comm]; exact Nat.add_lt_add_left (nat_blt_lt h1) _
        exact nat_lt_blt hLt
      | storageDead id =>
        dsimp [stmtLocalsLtAndNoDead0] at h1
        let ⟨_, hIdLt⟩ := bool_and_true h1
        dsimp [shiftStmtUnw, InlineUnwCtx.locOff]
        have hLt : id + ctx.caller.locals.length <
            ctx.caller.locals.length + ctx.callee.locals.length := by
          rw [Nat.add_comm]; exact Nat.add_lt_add_left (nat_blt_lt hIdLt) _
        exact nat_lt_blt hLt
  · have hD : ctx.deads.all (fun stmt =>
        match stmt with
        | .storageLive id | .storageDead id =>
          Nat.blt id (ctx.caller.locals.length + ctx.callee.locals.length)
        | _ => true) = true := by
      apply list_all_of_getElem?
      intro j st hSt
      have hM := list_all_getElem?
        (mkAllStorageDead_inBounds ctx.locOff ctx.callee.locals.length
          ctx.callee.locals.length (Nat.le_refl _)) hSt
      cases st with
      | assign _ _ | nop | unsupported => rfl
      | storageLive id => exact hM
      | storageDead id => exact hM
    dsimp [List.all, InlineUnwCtx.normalExitBlock, InlineUnwCtx.unwindExitBlock]
    apply bool_and_intro
    · apply bool_and_intro
      · rfl
      · apply list_all_of_getElem?
        intro j st hSt
        have hM := list_all_getElem? hD hSt
        cases st with
        | assign _ _ | nop | unsupported => rfl
        | storageLive id => exact hM
        | storageDead id => exact hM
    · apply bool_and_intro
      · apply list_all_of_getElem?
        intro j st hSt
        have hM := list_all_getElem? hD hSt
        cases st with
        | assign _ _ | nop | unsupported => rfl
        | storageLive id => exact hM
        | storageDead id => exact hM
      · rfl

private theorem list_any_setElem?_eq {α : Type} (p : α → Bool) :
    ∀ {xs ys : List α} {i : Nat} {v : α} {orig : α},
      Trusted.MirSemantics.getElem? xs i = some orig →
      setElem? xs i v = some ys →
      p v = p orig →
      ys.any p = xs.any p
  | [], _, _, _, _, hGet, _, _ => by cases hGet
  | x :: xs, ys, 0, v, orig, hGet, hSet, hEq => by
    dsimp [Trusted.MirSemantics.getElem?] at hGet
    injection hGet with hx; subst hx
    dsimp [setElem?] at hSet
    injection hSet with hy; subst hy
    dsimp [List.any]
    rw [hEq]
  | x :: xs, ys, i + 1, v, orig, hGet, hSet, hEq => by
    dsimp [Trusted.MirSemantics.getElem?] at hGet
    dsimp [setElem?] at hSet
    cases hS : setElem? xs i v with
    | none => rw [hS] at hSet; cases hSet
    | some xs' =>
      rw [hS] at hSet; dsimp at hSet
      injection hSet with hy; subst hy
      dsimp [List.any]
      cases p x with
      | true => rfl
      | false => exact list_any_setElem?_eq p hGet hS hEq

private theorem ctx_caller'_hasStorageAnnot_prefix {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) {x : Nat} (hx : x < ctx.locOff) :
    hasStorageAnnotation ctx.caller' x = hasStorageAnnotation ctx.caller x := by
  unfold hasStorageAnnotation
  dsimp [InlineUnwCtx.caller']
  rw [list_any_append, list_any_append]
  have hUpd : ctx.callerBbsUpdated.any (fun bb =>
      bb.statements.any (stmtHasStorageMarker x)) =
      ctx.caller.basicBlocks.any (fun bb =>
        bb.statements.any (stmtHasStorageMarker x)) := by
    apply list_any_setElem?_eq (fun bb => bb.statements.any (stmtHasStorageMarker x))
      ctx.hCallBb ctx.hSetBb
    dsimp
    rw [list_any_append, list_any_append]
    have hLow1 := mkCalleeEntryStorageLive_noLow ctx.callee ctx.locOff x hx 0 ctx.callee.locals.length
    have hLow2 := mkArgBindStmts_any_marker_false ctx.locOff x 0 ctx.args
    dsimp [InlineUnwCtx.locOff] at hLow1 hLow2
    rw [hLow1, hLow2]
    cases ctx.callBb.statements.any (stmtHasStorageMarker x) <;> rfl
  have hShifted : ctx.shiftedCalleeBbs.any (fun bb =>
      bb.statements.any (stmtHasStorageMarker x)) = false := by
    dsimp [InlineUnwCtx.shiftedCalleeBbs]
    rw [list_any_map]
    apply list_any_false_of_all
    apply list_all_of_getElem?
    intro i bb _
    dsimp [shiftCalleeBlock]
    rw [list_any_map]
    have hF : bb.statements.any (fun s => stmtHasStorageMarker x (shiftStmtUnw ctx.locOff s)) = false := by
      apply list_any_false_of_all
      apply list_all_of_getElem?
      intro j st _
      cases st with
      | assign _ _ | nop | unsupported => rfl
      | storageLive id =>
        dsimp [shiftStmtUnw, stmtHasStorageMarker]
        have hNe : Nat.beq (id + ctx.locOff) x = false :=
          nat_beq_false_of_ne (Nat.ne_of_gt (Nat.lt_of_lt_of_le hx (Nat.le_add_left _ _)))
        rw [hNe]; rfl
      | storageDead id =>
        dsimp [shiftStmtUnw, stmtHasStorageMarker]
        have hNe : Nat.beq (id + ctx.locOff) x = false :=
          nat_beq_false_of_ne (Nat.ne_of_gt (Nat.lt_of_lt_of_le hx (Nat.le_add_left _ _)))
        rw [hNe]; rfl
    rw [hF]; rfl
  have hExits : ([ctx.normalExitBlock, ctx.unwindExitBlock] : List BasicBlock).any (fun bb =>
      bb.statements.any (stmtHasStorageMarker x)) = false := by
    dsimp [List.any, InlineUnwCtx.normalExitBlock, InlineUnwCtx.unwindExitBlock,
           InlineUnwCtx.deads, stmtHasStorageMarker]
    rw [mkAllStorageDead_noLow ctx.locOff x hx ctx.callee.locals.length]
    rfl
  rw [hUpd, hShifted, hExits]
  cases ctx.caller.basicBlocks.any (fun bb => bb.statements.any (stmtHasStorageMarker x)) <;> rfl

private theorem ctx_caller'_hasStorageAnnot_suffix {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) {j : Nat} (hj : j < ctx.callee.locals.length) :
    hasStorageAnnotation ctx.caller' (ctx.locOff + j) = true := by
  unfold hasStorageAnnotation
  dsimp [InlineUnwCtx.caller']
  rw [list_any_append]
  have hExits : ([ctx.normalExitBlock, ctx.unwindExitBlock] : List BasicBlock).any (fun bb =>
      bb.statements.any (stmtHasStorageMarker (ctx.locOff + j))) = true := by
    dsimp [List.any, InlineUnwCtx.normalExitBlock, InlineUnwCtx.deads, stmtHasStorageMarker]
    rw [mkAllStorageDead_has ctx.locOff ctx.callee.locals.length j hj]
    rfl
  rw [hExits]
  cases (ctx.callerBbsUpdated ++ ctx.shiftedCalleeBbs).any
      (fun bb => bb.statements.any (stmtHasStorageMarker (ctx.locOff + j))) <;> rfl

private theorem ctx_caller'_initLocalsLoop_prefix {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) (argVals : List Val) :
    ∀ (idx : Nat) (xs : List MirTy),
      idx + xs.length ≤ ctx.locOff →
      initLocalsLoop ctx.caller' argVals idx xs =
        initLocalsLoop ctx.caller argVals idx xs
  | _, [], _ => rfl
  | idx, ty :: rest, hLe => by
    dsimp [initLocalsLoop]
    have hIdxLt : idx < ctx.locOff :=
      Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_succ_self idx)
        (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le rest.length)) idx)) hLe
    have hNext : idx + 1 + rest.length ≤ ctx.locOff := by
      have hEq : idx + 1 + rest.length = idx + (rest.length + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 rest.length]
      rw [hEq]; exact hLe
    have hAnn : hasStorageAnnotation ctx.caller' idx = hasStorageAnnotation ctx.caller idx :=
      ctx_caller'_hasStorageAnnot_prefix ctx hIdxLt
    have hIh := ctx_caller'_initLocalsLoop_prefix ctx argVals (idx + 1) rest hNext
    have hArgEq : ctx.caller'.argumentCount = ctx.caller.argumentCount := rfl
    rw [hArgEq, hAnn, hIh]

private theorem ctx_caller'_initLocalsLoop_suffix {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) (argVals : List Val) :
    ∀ (j : Nat) (xs : List MirTy),
      j + xs.length ≤ ctx.callee.locals.length →
      initLocalsLoop ctx.caller' argVals (ctx.locOff + j) xs =
        replicateDead xs.length
  | _, [], _ => rfl
  | j, ty :: rest, hLe => by
    dsimp [initLocalsLoop, replicateDead]
    have hPos : 0 < ctx.locOff + j :=
      Nat.lt_of_lt_of_le (ctx_locOff_pos ctx) (Nat.le_add_right _ _)
    have hNe0 : Nat.beq (ctx.locOff + j) 0 = false :=
      nat_beq_false_of_ne (Nat.ne_of_gt hPos)
    have hGtArg : ctx.caller.argumentCount < ctx.locOff + j :=
      Nat.lt_of_lt_of_le (ctx_caller_argLt ctx) (Nat.le_add_right _ _)
    have hBle : Nat.ble (ctx.locOff + j) ctx.caller'.argumentCount = false :=
      nat_gt_ble_false hGtArg
    have hJLt : j < ctx.callee.locals.length :=
      Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_succ_self j)
        (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le rest.length)) j)) hLe
    have hAnn : hasStorageAnnotation ctx.caller' (ctx.locOff + j) = true :=
      ctx_caller'_hasStorageAnnot_suffix ctx hJLt
    rw [hNe0, hBle, hAnn]
    dsimp
    have hNext : j + 1 + rest.length ≤ ctx.callee.locals.length := by
      have hEq : j + 1 + rest.length = j + (rest.length + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 rest.length]
      rw [hEq]; exact hLe
    have hAdd : ctx.locOff + j + 1 = ctx.locOff + (j + 1) := Nat.add_assoc _ _ _
    rw [hAdd, ctx_caller'_initLocalsLoop_suffix ctx argVals (j + 1) rest hNext]

private theorem ctx_caller'_initLocalsLoop {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) (argVals : List Val) :
    initLocalsLoop ctx.caller' argVals 0 ctx.caller'.locals =
      initLocalsLoop ctx.caller argVals 0 ctx.caller.locals ++
        replicateDead ctx.callee.locals.length := by
  have hLocs : ctx.caller'.locals = ctx.caller.locals ++ ctx.callee.locals := rfl
  rw [hLocs, initLocalsLoop_append]
  rw [ctx_caller'_initLocalsLoop_prefix ctx argVals 0 ctx.caller.locals
        (by rw [Nat.zero_add]; exact Nat.le_refl _)]
  have h0 : 0 + ctx.caller.locals.length = ctx.locOff + 0 := by
    rw [Nat.zero_add, Nat.add_zero]; rfl
  rw [h0, ctx_caller'_initLocalsLoop_suffix ctx argVals 0 ctx.callee.locals
        (by rw [Nat.zero_add]; exact Nat.le_refl _)]

private theorem ctx_caller'_paramTys {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) :
    (ctx.caller'.locals.drop 1).take ctx.caller'.argumentCount =
      (ctx.caller.locals.drop 1).take ctx.caller.argumentCount := by
  dsimp [InlineUnwCtx.caller']
  exact paramTys_append_eq ctx.caller ctx.callee (ctx_caller_argLt ctx)

private theorem ctx_caller'_locals_supported {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) :
    ctx.caller'.locals.all isSupportedScalarOrUnitTy =
      ctx.caller.locals.all isSupportedScalarOrUnitTy := by
  dsimp [InlineUnwCtx.caller']
  rw [list_all_append, ctx_callee_locals_supported ctx]
  cases ctx.caller.locals.all isSupportedScalarOrUnitTy <;> rfl

private theorem ctx_caller_bbs_nonEmpty {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) :
    ctx.caller.basicBlocks.isEmpty = false := by
  have hLt := getElem?_some_lt ctx.hCallBb
  cases hB : ctx.caller.basicBlocks with
  | nil => rw [hB] at hLt; exact False.elim (Nat.not_lt_zero _ hLt)
  | cons _ _ => rfl

private theorem ctx_caller'_bbs_nonEmpty {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) :
    ctx.caller'.basicBlocks.isEmpty = false := by
  have hLen : 0 < ctx.callerBbsUpdated.length := by
    rw [ctx_callerBbsUpdated_len ctx]
    exact Nat.lt_of_le_of_lt (Nat.zero_le _) (getElem?_some_lt ctx.hCallBb)
  dsimp [InlineUnwCtx.caller']
  cases hU : ctx.callerBbsUpdated with
  | nil => rw [hU] at hLen; exact False.elim (Nat.not_lt_zero _ hLen)
  | cons _ _ => rfl

private theorem ctx_caller'_bodyStaticAdmitted {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) :
    BodyStaticAdmitted pTgt ctx.caller' = BodyStaticAdmitted pSrc ctx.caller := by
  unfold BodyStaticAdmitted
  have hPw : pTgt.pointerWidthBits = pSrc.pointerWidthBits := by
    have h := congrArg Program.pointerWidthBits ctx.hPtgt; exact h
  have hPv : pTgt.mirProfileVersion = pSrc.mirProfileVersion := by
    have h := congrArg Program.mirProfileVersion ctx.hPtgt; exact h
  have hId : ctx.caller'.identity = ctx.caller.identity := rfl
  have hBbs1 := ctx_caller_bbs_nonEmpty ctx
  have hBbs2 := ctx_caller'_bbs_nonEmpty ctx
  have hArg1 : Nat.blt ctx.caller.argumentCount ctx.caller.locals.length = true :=
    nat_lt_blt (ctx_caller_argLt ctx)
  have hArg2 : Nat.blt ctx.caller'.argumentCount ctx.caller'.locals.length = true := by
    dsimp [InlineUnwCtx.caller']
    rw [list_length_append]
    exact nat_lt_blt (Nat.lt_of_lt_of_le (ctx_caller_argLt ctx) (Nat.le_add_right _ _))
  have hSt1 := ctx_caller_storageInBounds ctx
  have hSt2 := ctx_caller'_storageInBounds ctx
  have hSup := ctx_caller'_locals_supported ctx
  rw [hPw, hPv, hId, hBbs1, hBbs2, hArg1, hArg2, hSt1, hSt2, hSup]

/-! ### Part 4: Multi-Step Gadget 1 — `entryLives` (`mkCalleeEntryStorageLive`) -/

private noncomputable def calleeAfterEntryLives (callee : Body) :
    Nat → List MirTy → List LocalSlot
  | _, [] => []
  | idx, ty :: rest =>
    let sl :=
      if Nat.ble idx callee.argumentCount || !hasStorageAnnotation callee idx then
        liveUninitSlot ty
      else
        .dead
    sl :: calleeAfterEntryLives callee (idx + 1) rest

private theorem calleeAfterEntryLives_length (callee : Body) :
    ∀ (idx : Nat) (xs : List MirTy),
      (calleeAfterEntryLives callee idx xs).length = xs.length
  | _, [] => rfl
  | idx, _ :: rest => congrArg Nat.succ (calleeAfterEntryLives_length callee (idx + 1) rest)

private theorem calleeAfterEntryLives_getElem? (callee : Body) :
    ∀ (idx : Nat) (xs : List MirTy) (k : Nat),
      Trusted.MirSemantics.getElem? (calleeAfterEntryLives callee idx xs) k =
        match Trusted.MirSemantics.getElem? xs k with
        | none => none
        | some ty =>
          some (if Nat.ble (idx + k) callee.argumentCount ||
                   !hasStorageAnnotation callee (idx + k) then
                  liveUninitSlot ty
                else
                  .dead)
  | _, [], _ => rfl
  | idx, ty :: rest, 0 => rfl
  | idx, ty :: rest, k + 1 => by
    dsimp [calleeAfterEntryLives, Trusted.MirSemantics.getElem?]
    rw [calleeAfterEntryLives_getElem? callee (idx + 1) rest k]
    have hEq : idx + 1 + k = idx + (k + 1) := by
      rw [Nat.add_assoc, Nat.add_comm 1 k]
    rw [hEq]

private theorem step_storageLive_in_block {p : Program} {body : Body} {bb : BasicBlock}
    {defId : DefId} {bbIdx stmtIdx locId : Nat}
    {locals locals' : List LocalSlot} {ty : MirTy}
    {stack : List CallContUnw} {mem : CallerMemory}
    (hBody : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (hBb : Trusted.MirSemantics.getElem? body.basicBlocks bbIdx = some bb)
    (hStmt : Trusted.MirSemantics.getElem? bb.statements stmtIdx = some (.storageLive locId))
    (hTy : Trusted.MirSemantics.getElem? body.locals locId = some ty)
    (hSet : setElem? locals locId (liveUninitSlot ty) = some locals') :
    StepUnw p
      { active := { defId := defId, blockIdx := bbIdx, stmtIdx := stmtIdx, locals := locals },
        callStack := stack, callerMem := mem }
      (.step { active := { defId := defId, blockIdx := bbIdx, stmtIdx := stmtIdx + 1,
                           locals := locals' },
               callStack := stack, callerMem := mem }) := by
  refine ⟨0, rfl, ?_⟩
  unfold evalStepUnw
  rw [hBody]; dsimp
  rw [hBb]; dsimp
  rw [hStmt]; dsimp [evalStatement]
  rw [hTy]; dsimp
  rw [hSet]

private theorem step_storageDead_in_block {p : Program} {body : Body} {bb : BasicBlock}
    {defId : DefId} {bbIdx stmtIdx locId : Nat}
    {locals locals' : List LocalSlot}
    {stack : List CallContUnw} {mem : CallerMemory}
    (hBody : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (hBb : Trusted.MirSemantics.getElem? body.basicBlocks bbIdx = some bb)
    (hStmt : Trusted.MirSemantics.getElem? bb.statements stmtIdx = some (.storageDead locId))
    (hPos : 0 < locId)
    (hSet : setElem? locals locId .dead = some locals') :
    StepUnw p
      { active := { defId := defId, blockIdx := bbIdx, stmtIdx := stmtIdx, locals := locals },
        callStack := stack, callerMem := mem }
      (.step { active := { defId := defId, blockIdx := bbIdx, stmtIdx := stmtIdx + 1,
                           locals := locals' },
               callStack := stack, callerMem := mem }) := by
  refine ⟨0, rfl, ?_⟩
  unfold evalStepUnw
  rw [hBody]; dsimp
  rw [hBb]; dsimp
  rw [hStmt]; dsimp [evalStatement]
  rw [nat_beq_false_of_ne (Nat.ne_of_gt hPos)]
  dsimp
  rw [hSet]

private theorem run_entryLives_loop {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site)
    (cSlots : List LocalSlot) (hLenC : cSlots.length = ctx.locOff)
    (stack : List CallContUnw) (mem : CallerMemory) :
    ∀ (rem i stmtOff : Nat) (preSlots : List LocalSlot),
      i + rem = ctx.callee.locals.length →
      preSlots.length = i →
      (∀ (k : Nat), k < (mkCalleeEntryStorageLive ctx.callee ctx.locOff i rem).length →
        Trusted.MirSemantics.getElem? ctx.callBb'.statements (stmtOff + k) =
          Trusted.MirSemantics.getElem?
            (mkCalleeEntryStorageLive ctx.callee ctx.locOff i rem) k) →
      ReachesUnw pTgt
        { active := { defId := site.callerDefId, blockIdx := site.callBlock,
                      stmtIdx := stmtOff,
                      locals := cSlots ++ (preSlots ++ replicateDead rem) },
          callStack := stack, callerMem := mem }
        { active := { defId := site.callerDefId, blockIdx := site.callBlock,
                      stmtIdx := stmtOff +
                        (mkCalleeEntryStorageLive ctx.callee ctx.locOff i rem).length,
                      locals := cSlots ++ (preSlots ++
                        calleeAfterEntryLives ctx.callee i (ctx.callee.locals.drop i)) },
          callStack := stack, callerMem := mem }
  | 0, i, stmtOff, preSlots, hSum, _, _ => by
    have hGe : ctx.callee.locals.length ≤ i := by
      rw [← hSum, Nat.add_zero]; exact Nat.le_refl _
    have hDrop : ctx.callee.locals.drop i = [] := by
      have hL : (ctx.callee.locals.drop i).length = 0 := by
        rw [list_length_drop]; exact Nat.sub_eq_zero_of_le hGe
      cases hd : ctx.callee.locals.drop i with
      | nil => rfl
      | cons _ _ => rw [hd] at hL; cases hL
    dsimp [mkCalleeEntryStorageLive, replicateDead]
    rw [hDrop]
    exact ReachesUnw.refl _
  | rem + 1, i, stmtOff, preSlots, hSum, hPreLen, hSlice => by
    have hILt : i < ctx.callee.locals.length := by
      rw [← hSum]
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self i)
        (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le rem)) i)
    let ⟨ty, hTy⟩ := getElem?_some_of_lt ctx.callee.locals i hILt
    have hDrop : ctx.callee.locals.drop i = ty :: ctx.callee.locals.drop (i + 1) := by
      have hSplit : ∀ (n : Nat) (xs : List MirTy) (t : MirTy),
          Trusted.MirSemantics.getElem? xs n = some t →
          xs.drop n = t :: xs.drop (n + 1) := by
        intro n
        induction n with
        | zero =>
          intro xs t ht
          cases xs with
          | nil => cases ht
          | cons y ys =>
            dsimp [Trusted.MirSemantics.getElem?] at ht
            injection ht with h; subst h; rfl
        | succ n ih =>
          intro xs t ht
          cases xs with
          | nil => cases ht
          | cons y ys =>
            dsimp [Trusted.MirSemantics.getElem?] at ht
            dsimp [List.drop]
            exact ih ys t ht
      exact hSplit i ctx.callee.locals ty hTy
    have hNextSum : i + 1 + rem = ctx.callee.locals.length := by
      have hEq : i + 1 + rem = i + (rem + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 rem]
      rw [hEq]; exact hSum
    dsimp [mkCalleeEntryStorageLive]
    dsimp [mkCalleeEntryStorageLive] at hSlice
    cases hCond : (Nat.ble i ctx.callee.argumentCount ||
        !hasStorageAnnotation ctx.callee i) with
    | false =>
      rw [hCond] at hSlice
      dsimp at hSlice
      rw [hDrop]
      dsimp [calleeAfterEntryLives]
      rw [hCond]; dsimp
      have hPre1 : (preSlots ++ [LocalSlot.dead]).length = i + 1 := by
        rw [list_length_append, hPreLen]; rfl
      have hReassoc1 : preSlots ++ replicateDead (rem + 1) =
          (preSlots ++ [LocalSlot.dead]) ++ replicateDead rem := by
        dsimp [replicateDead]
        rw [List.append_assoc]; rfl
      have hReassoc2 : preSlots ++ (LocalSlot.dead :: calleeAfterEntryLives ctx.callee (i + 1)
          (ctx.callee.locals.drop (i + 1))) =
          (preSlots ++ [LocalSlot.dead]) ++ calleeAfterEntryLives ctx.callee (i + 1)
            (ctx.callee.locals.drop (i + 1)) := by
        rw [List.append_assoc]; rfl
      rw [hReassoc1, hReassoc2]
      exact run_entryLives_loop ctx cSlots hLenC stack mem rem (i + 1) stmtOff
        (preSlots ++ [LocalSlot.dead]) hNextSum hPre1 hSlice
    | true =>
      rw [hCond] at hSlice
      dsimp at hSlice
      rw [hDrop]
      dsimp [calleeAfterEntryLives]
      rw [hCond]; dsimp
      have hStmt0 : Trusted.MirSemantics.getElem? ctx.callBb'.statements stmtOff =
          some (.storageLive (ctx.locOff + i)) := by
        have h0 := hSlice 0 (Nat.zero_lt_succ _)
        rw [Nat.add_zero] at h0; exact h0
      have hTy' : Trusted.MirSemantics.getElem? ctx.caller'.locals (ctx.locOff + i) =
          some ty := by
        dsimp [InlineUnwCtx.caller', InlineUnwCtx.locOff]
        rw [getElem?_append_right]
        exact hTy
      have hSet : setElem? (cSlots ++ (preSlots ++ replicateDead (rem + 1)))
          (ctx.locOff + i) (liveUninitSlot ty) =
          some (cSlots ++ ((preSlots ++ [liveUninitSlot ty]) ++ replicateDead rem)) := by
        rw [← hLenC, setElem?_append_right cSlots (preSlots ++ replicateDead (rem + 1)) i
              (liveUninitSlot ty)]
        have h2 : setElem? (preSlots ++ replicateDead (rem + 1)) i (liveUninitSlot ty) =
            some ((preSlots ++ [liveUninitSlot ty]) ++ replicateDead rem) := by
          have h3 : i = preSlots.length + 0 := by rw [hPreLen, Nat.add_zero]
          rw [h3, setElem?_append_right]
          dsimp [replicateDead, setElem?]
          rw [List.append_assoc]; rfl
        rw [h2]
      have hStep : StepUnw pTgt
          { active := { defId := site.callerDefId, blockIdx := site.callBlock,
                        stmtIdx := stmtOff,
                        locals := cSlots ++ (preSlots ++ replicateDead (rem + 1)) },
            callStack := stack, callerMem := mem }
          (.step { active := { defId := site.callerDefId, blockIdx := site.callBlock,
                               stmtIdx := stmtOff + 1,
                               locals := cSlots ++
                                 ((preSlots ++ [liveUninitSlot ty]) ++ replicateDead rem) },
                   callStack := stack, callerMem := mem }) :=
        step_storageLive_in_block (ctx_bodies_lookup_eq ctx)
          (ctx_caller'_bb_lookup_call ctx) hStmt0 hTy' hSet
      have hPre1 : (preSlots ++ [liveUninitSlot ty]).length = i + 1 := by
        rw [list_length_append, hPreLen]; rfl
      have hSlice1 : ∀ (k : Nat),
          k < (mkCalleeEntryStorageLive ctx.callee ctx.locOff (i + 1) rem).length →
          Trusted.MirSemantics.getElem? ctx.callBb'.statements (stmtOff + 1 + k) =
            Trusted.MirSemantics.getElem?
              (mkCalleeEntryStorageLive ctx.callee ctx.locOff (i + 1) rem) k := by
        intro k hk
        have hEq : stmtOff + 1 + k = stmtOff + (k + 1) := by
          rw [Nat.add_assoc, Nat.add_comm 1 k]
        rw [hEq]
        exact hSlice (k + 1) (Nat.succ_lt_succ hk)
      have hRest := run_entryLives_loop ctx cSlots hLenC stack mem rem (i + 1) (stmtOff + 1)
        (preSlots ++ [liveUninitSlot ty]) hNextSum hPre1 hSlice1
      have hAdd : stmtOff + 1 +
          (mkCalleeEntryStorageLive ctx.callee ctx.locOff (i + 1) rem).length =
          stmtOff +
          ((.storageLive (ctx.locOff + i) ::
            mkCalleeEntryStorageLive ctx.callee ctx.locOff (i + 1) rem).length) := by
        dsimp [List.length]
        rw [Nat.add_assoc, Nat.add_comm 1 _]
      have hReassoc : preSlots ++ (liveUninitSlot ty :: calleeAfterEntryLives ctx.callee (i + 1)
          (ctx.callee.locals.drop (i + 1))) =
          (preSlots ++ [liveUninitSlot ty]) ++ calleeAfterEntryLives ctx.callee (i + 1)
            (ctx.callee.locals.drop (i + 1)) := by
        rw [List.append_assoc]; rfl
      rw [hAdd] at hRest
      rw [hReassoc]
      exact reachesUnw_trans
        (ReachesUnw.tail (ReachesUnw.refl _) hStep)
        hRest

private theorem ctx_entryLives_pos {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) :
    0 < ctx.entryLives.length := by
  have hLen : 0 < ctx.callee.locals.length :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) (ctx_callee_argLt ctx)
  cases hN : ctx.callee.locals.length with
  | zero => rw [hN] at hLen; exact False.elim (Nat.not_lt_zero _ hLen)
  | succ rem =>
    dsimp [InlineUnwCtx.entryLives]
    rw [hN]
    dsimp [mkCalleeEntryStorageLive]
    exact Nat.zero_lt_succ _

private theorem run_entryLives {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site)
    (cSlots : List LocalSlot) (hLenC : cSlots.length = ctx.locOff)
    (stack : List CallContUnw) (mem : CallerMemory) :
    ReachesPlusUnw pTgt
      { active := { defId := site.callerDefId, blockIdx := site.callBlock,
                    stmtIdx := ctx.callBb.statements.length,
                    locals := cSlots ++ replicateDead ctx.callee.locals.length },
        callStack := stack, callerMem := mem }
      { active := { defId := site.callerDefId, blockIdx := site.callBlock,
                    stmtIdx := ctx.callBb.statements.length + ctx.entryLives.length,
                    locals := cSlots ++
                      calleeAfterEntryLives ctx.callee 0 ctx.callee.locals },
        callStack := stack, callerMem := mem } := by
  have hSlice : ∀ (k : Nat), k < ctx.entryLives.length →
      Trusted.MirSemantics.getElem? ctx.callBb'.statements
        (ctx.callBb.statements.length + k) =
      Trusted.MirSemantics.getElem? ctx.entryLives k := by
    intro k hk
    dsimp [InlineUnwCtx.callBb']
    have hLt : ctx.callBb.statements.length + k <
        (ctx.callBb.statements ++ ctx.entryLives).length := by
      rw [list_length_append]
      exact Nat.add_lt_add_left hk _
    rw [getElem?_append_left hLt, getElem?_append_right]
  have hReach := run_entryLives_loop ctx cSlots hLenC stack mem
    ctx.callee.locals.length 0 ctx.callBb.statements.length []
    (Nat.zero_add _) rfl hSlice
  dsimp [List.append, List.drop] at hReach
  have hNe :
      (⟨⟨site.callerDefId, site.callBlock, ctx.callBb.statements.length,
          cSlots ++ replicateDead ctx.callee.locals.length⟩, stack, mem⟩ : UnwindState) ≠
      ⟨⟨site.callerDefId, site.callBlock,
          ctx.callBb.statements.length + ctx.entryLives.length,
          cSlots ++ calleeAfterEntryLives ctx.callee 0 ctx.callee.locals⟩, stack, mem⟩ := by
    intro hEq
    have hIdx : ctx.callBb.statements.length =
        ctx.callBb.statements.length + ctx.entryLives.length := by
      injection hEq with hAct _ _
      injection hAct with _ _ hSt _
    have hZ : ctx.entryLives.length = 0 := by
      have h1 : ctx.callBb.statements.length + 0 =
          ctx.callBb.statements.length + ctx.entryLives.length := by
        rw [Nat.add_zero]; exact hIdx
      exact (Nat.add_left_cancel h1).symm
    have hPos := ctx_entryLives_pos ctx
    rw [hZ] at hPos
    exact Nat.not_lt_zero _ hPos
  let ⟨n, hn⟩ := reachesUnw_to_reachesNUnw hReach
  have hZeroEq : ∀ {s1 s2 : UnwindState}, ReachesNUnw pTgt 0 s1 s2 → s1 = s2 := by
    intro s1 s2 hz; cases hz; rfl
  cases n with
  | zero =>
    exact False.elim (hNe (hZeroEq hn))
  | succ m =>
    exact ⟨m, hn⟩

/-! ### Part 5: Multi-Step Gadget 2 — `argBinds` (`mkArgBindStmts`) -/

private noncomputable def overwriteArgs :
    List LocalSlot → Nat → List Val → List LocalSlot
  | slots, _, [] => slots
  | slots, idx, v :: vs =>
    match setElem? slots idx (.live (some v)) with
    | some slots' => overwriteArgs slots' (idx + 1) vs
    | none => slots

private theorem overwriteArgs_length :
    ∀ (slots : List LocalSlot) (idx : Nat) (vs : List Val),
      (overwriteArgs slots idx vs).length = slots.length
  | _, _, [] => rfl
  | slots, idx, v :: vs => by
    dsimp [overwriteArgs]
    cases hS : setElem? slots idx (.live (some v)) with
    | none => rfl
    | some slots' =>
      rw [overwriteArgs_length slots' (idx + 1) vs]
      exact setElem?_length hS

private theorem overwriteArgs_getElem?_lt :
    ∀ (slots : List LocalSlot) (idx : Nat) (vs : List Val) (k : Nat),
      k < idx →
      Trusted.MirSemantics.getElem? (overwriteArgs slots idx vs) k =
        Trusted.MirSemantics.getElem? slots k
  | _, _, [], _, _ => rfl
  | slots, idx, v :: vs, k, hLt => by
    dsimp [overwriteArgs]
    cases hS : setElem? slots idx (.live (some v)) with
    | none => rfl
    | some slots' =>
      rw [overwriteArgs_getElem?_lt slots' (idx + 1) vs k (Nat.lt_succ_of_lt hLt)]
      exact setElem?_getElem?_ne hS (Nat.ne_of_lt hLt)

private theorem overwriteArgs_getElem?_ge :
    ∀ (slots : List LocalSlot) (idx : Nat) (vs : List Val) (k : Nat),
      idx + vs.length ≤ k →
      Trusted.MirSemantics.getElem? (overwriteArgs slots idx vs) k =
        Trusted.MirSemantics.getElem? slots k
  | _, _, [], _, _ => rfl
  | slots, idx, v :: vs, k, hGe => by
    dsimp [overwriteArgs]
    cases hS : setElem? slots idx (.live (some v)) with
    | none => rfl
    | some slots' =>
      have hGe1 : idx + 1 + vs.length ≤ k := by
        have hEq : idx + 1 + vs.length = idx + (vs.length + 1) := by
          rw [Nat.add_assoc, Nat.add_comm 1 vs.length]
        rw [hEq]; exact hGe
      rw [overwriteArgs_getElem?_ge slots' (idx + 1) vs k hGe1]
      have hNe : k ≠ idx := Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_succ_self idx)
        (Nat.le_trans (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le vs.length)) idx) hGe))
      exact setElem?_getElem?_ne hS hNe

private theorem overwriteArgs_getElem?_mid :
    ∀ (slots : List LocalSlot) (idx : Nat) (vs : List Val) (d : Nat) (v : Val),
      idx + vs.length ≤ slots.length →
      Trusted.MirSemantics.getElem? vs d = some v →
      Trusted.MirSemantics.getElem? (overwriteArgs slots idx vs) (idx + d) =
        some (.live (some v))
  | _, _, [], _, _, _, hGet => by cases hGet
  | slots, idx, w :: ws, 0, v, hLe, hGet => by
    dsimp [Trusted.MirSemantics.getElem?] at hGet
    injection hGet with hv; subst hv
    have hLt : idx < slots.length :=
      Nat.lt_of_lt_of_le (Nat.lt_succ_self idx)
        (Nat.le_trans (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le ws.length)) idx) hLe)
    let ⟨slots', hSet⟩ := setElem?_some_of_lt slots idx (LocalSlot.live (some w)) hLt
    dsimp [overwriteArgs]
    rw [hSet, Nat.add_zero]
    rw [overwriteArgs_getElem?_lt slots' (idx + 1) ws idx (Nat.lt_succ_self idx)]
    exact setElem?_getElem?_same hSet
  | slots, idx, w :: ws, d + 1, v, hLe, hGet => by
    dsimp [Trusted.MirSemantics.getElem?] at hGet
    have hLt : idx < slots.length :=
      Nat.lt_of_lt_of_le (Nat.lt_succ_self idx)
        (Nat.le_trans (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le ws.length)) idx) hLe)
    let ⟨slots', hSet⟩ := setElem?_some_of_lt slots idx (LocalSlot.live (some w)) hLt
    dsimp [overwriteArgs]
    rw [hSet]
    have hLe1 : idx + 1 + ws.length ≤ slots'.length := by
      rw [setElem?_length hSet]
      have hEq : idx + 1 + ws.length = idx + (ws.length + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 ws.length]
      rw [hEq]; exact hLe
    have hEq : idx + (d + 1) = idx + 1 + d := by
      rw [Nat.add_assoc, Nat.add_comm 1 d]
    rw [hEq]
    exact overwriteArgs_getElem?_mid slots' (idx + 1) ws d v hLe1 hGet

private theorem list_eq_of_getElem? {α : Type} :
    ∀ {xs ys : List α},
      xs.length = ys.length →
      (∀ k : Nat, Trusted.MirSemantics.getElem? xs k = Trusted.MirSemantics.getElem? ys k) →
      xs = ys
  | [], [], _, _ => rfl
  | [], _ :: _, hLen, _ => by cases hLen
  | _ :: _, [], hLen, _ => by cases hLen
  | x :: xs, y :: ys, hLen, hGet => by
    have h0 := hGet 0
    dsimp [Trusted.MirSemantics.getElem?] at h0
    injection h0 with hxy; subst hxy
    have hTail : xs = ys :=
      list_eq_of_getElem? (Nat.succ.inj hLen) (fun k => hGet (k + 1))
    rw [hTail]

private theorem initLocalsLoop_getElem? (body : Body) (args : List Val) :
    ∀ (idx : Nat) (xs : List MirTy) (k : Nat),
      Trusted.MirSemantics.getElem? (initLocalsLoop body args idx xs) k =
        match Trusted.MirSemantics.getElem? xs k with
        | none => none
        | some ty =>
          some (if Nat.beq (idx + k) 0 then
                  liveUninitSlot ty
                else if Nat.ble (idx + k) body.argumentCount then
                  match Trusted.MirSemantics.getElem? args ((idx + k) - 1) with
                  | some v => .live (some v)
                  | none => .dead
                else if hasStorageAnnotation body (idx + k) then
                  .dead
                else
                  liveUninitSlot ty)
  | _, [], _ => rfl
  | idx, ty :: rest, 0 => rfl
  | idx, ty :: rest, k + 1 => by
    dsimp [initLocalsLoop, Trusted.MirSemantics.getElem?]
    rw [initLocalsLoop_getElem? body args (idx + 1) rest k]
    have hEq : idx + 1 + k = idx + (k + 1) := by
      rw [Nat.add_assoc, Nat.add_comm 1 k]
    cases Trusted.MirSemantics.getElem? rest k with
    | none => rfl
    | some ty' =>
      dsimp
      have hNe0 : Nat.beq (idx + (k + 1)) 0 = false :=
        nat_beq_false_of_ne (Nat.ne_of_gt
          (Nat.lt_of_le_of_lt (Nat.zero_le idx) (Nat.lt_add_of_pos_right (Nat.zero_lt_succ k))))
      have hSub : idx + (k + 1) - 1 = idx + k := by
        rw [← Nat.add_assoc, Nat.add_sub_cancel]
      rw [hEq, hNe0, hSub]; rfl

private theorem overwriteArgs_calleeAfterEntryLives_eq_initLocalsLoop (callee : Body)
    (vs : List Val)
    (hArgLt : callee.argumentCount < callee.locals.length)
    (hVsLen : vs.length = callee.argumentCount) :
    overwriteArgs (calleeAfterEntryLives callee 0 callee.locals) 1 vs =
      initLocalsLoop callee vs 0 callee.locals := by
  apply list_eq_of_getElem?
  · rw [overwriteArgs_length, calleeAfterEntryLives_length, initLocalsLoop_length]
  · intro k
    cases k with
    | zero =>
      rw [overwriteArgs_getElem?_lt _ 1 vs 0 (Nat.zero_lt_succ 0)]
      rw [calleeAfterEntryLives_getElem?, initLocalsLoop_getElem?]
      rw [Nat.zero_add]
      cases Trusted.MirSemantics.getElem? callee.locals 0 with
      | none => rfl
      | some ty => rfl
    | succ d =>
      cases hLe : Nat.ble (d + 1) callee.argumentCount with
      | true =>
        have hD1Le : d + 1 ≤ callee.argumentCount := nat_ble_le hLe
        have hDLt : d < vs.length := by
          rw [hVsLen]; exact Nat.lt_of_succ_le hD1Le
        let ⟨v, hv⟩ := getElem?_some_of_lt vs d hDLt
        have h1Len : 1 + vs.length ≤ (calleeAfterEntryLives callee 0 callee.locals).length := by
          rw [calleeAfterEntryLives_length, hVsLen, Nat.add_comm]
          exact hArgLt
        have hEq1 : d + 1 = 1 + d := Nat.add_comm d 1
        rw [hEq1, overwriteArgs_getElem?_mid _ 1 vs d v h1Len hv]
        rw [← hEq1, initLocalsLoop_getElem?, Nat.zero_add]
        have hKLt : d + 1 < callee.locals.length := Nat.lt_of_le_of_lt hD1Le hArgLt
        let ⟨ty, hTy⟩ := getElem?_some_of_lt callee.locals (d + 1) hKLt
        rw [hTy]; dsimp
        rw [hLe]; dsimp
        rw [hv]
      | false =>
        have hGt : callee.argumentCount < d + 1 := by
          cases Nat.lt_or_ge callee.argumentCount (d + 1) with
          | inl h => exact h
          | inr h => rw [nat_le_ble h] at hLe; cases hLe
        have hGe : 1 + vs.length ≤ d + 1 := by
          rw [hVsLen, Nat.add_comm]; exact hGt
        rw [overwriteArgs_getElem?_ge _ 1 vs (d + 1) hGe]
        rw [calleeAfterEntryLives_getElem?, initLocalsLoop_getElem?, Nat.zero_add]
        cases Trusted.MirSemantics.getElem? callee.locals (d + 1) with
        | none => rfl
        | some ty =>
          dsimp
          rw [hLe]; dsimp
          cases hasStorageAnnotation callee (d + 1) <;> rfl

private theorem run_argBinds_loop {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site)
    (stack : List CallContUnw) (mem : CallerMemory) :
    ∀ (ops : List Operand) (pTys : List MirTy) (idx stmtOff : Nat)
      (cSlots eSlots : List LocalSlot),
      cSlots.length = ctx.locOff →
      eSlots.length = ctx.callee.locals.length →
      (∀ (i : Nat) (ty : MirTy) (vi : Val),
        Trusted.MirSemantics.getElem? ctx.caller.locals i = some ty →
        Trusted.MirSemantics.getElem? cSlots i = some (.live (some vi)) →
        checkVal vi ty = true) →
      ops.all (operandLocalsLt ctx.locOff) = true →
      callArgsTyMatch ctx.caller.locals ops pTys = true →
      (∀ (k : Nat) (t : MirTy),
        Trusted.MirSemantics.getElem? pTys k = some t →
        Trusted.MirSemantics.getElem? ctx.callee.locals (1 + idx + k) = some t) →
      (∀ (k : Nat), k < ops.length →
        ∃ ov : Option Val,
          Trusted.MirSemantics.getElem? eSlots (1 + idx + k) = some (.live ov)) →
      (∀ (k : Nat), k < ops.length →
        Trusted.MirSemantics.getElem? ctx.callBb'.statements (stmtOff + k) =
          Trusted.MirSemantics.getElem? (mkArgBindStmts ctx.locOff idx ops) k) →
      match evalCallArgsUnw ctx.caller.locals cSlots ops with
      | .error fk =>
        ∃ s' : UnwindState,
          ReachesUnw pTgt
            { active := { defId := site.callerDefId, blockIdx := site.callBlock,
                          stmtIdx := stmtOff, locals := cSlots ++ eSlots },
              callStack := stack, callerMem := mem } s' ∧
          StepUnw pTgt s' (.fault fk)
      | .ok (vs, cSlots') =>
        ReachesUnw pTgt
          { active := { defId := site.callerDefId, blockIdx := site.callBlock,
                        stmtIdx := stmtOff, locals := cSlots ++ eSlots },
            callStack := stack, callerMem := mem }
          { active := { defId := site.callerDefId, blockIdx := site.callBlock,
                        stmtIdx := stmtOff + ops.length,
                        locals := cSlots' ++ overwriteArgs eSlots (1 + idx) vs },
            callStack := stack, callerMem := mem }
  | [], [], idx, stmtOff, cSlots, eSlots, _, _, _, _, _, _, _, _ => by
    dsimp [evalCallArgsUnw, overwriteArgs, List.length]
    exact ReachesUnw.refl _
  | [], _ :: _, _, _, _, _, _, _, _, _, hMatch, _, _, _ => by cases hMatch
  | _ :: _, [], _, _, _, _, _, _, _, _, hMatch, _, _, _ => by cases hMatch
  | op :: ops, ty :: pTys, idx, stmtOff, cSlots, eSlots,
      hLenC, hLenE, hWt, hOpsLt, hMatch, hPTy, hLive, hSlice => by
    dsimp [List.all] at hOpsLt
    let ⟨hOpLt, hOpsLt'⟩ := bool_and_true hOpsLt
    dsimp [callArgsTyMatch] at hMatch
    cases hOpTy : operandTy? ctx.caller.locals op with
    | none => rw [hOpTy] at hMatch; cases hMatch
    | some opTy =>
      rw [hOpTy] at hMatch; dsimp at hMatch
      let ⟨hBeq, hMatch'⟩ := bool_and_true hMatch
      have hTyEq : opTy = ty := mirTy_beq_eq hBeq
      have hDstTy : Trusted.MirSemantics.getElem? ctx.callee.locals (1 + idx) = some ty := by
        have h0 := hPTy 0 ty rfl
        rw [Nat.add_zero] at h0; exact h0
      have hDstTy' : Trusted.MirSemantics.getElem? ctx.caller'.locals (ctx.locOff + 1 + idx) =
          some ty := by
        dsimp [InlineUnwCtx.caller', InlineUnwCtx.locOff]
        rw [Nat.add_assoc, getElem?_append_right]
        exact hDstTy
      have hStmt0 : Trusted.MirSemantics.getElem? ctx.callBb'.statements stmtOff =
          some (.assign { localId := ctx.locOff + 1 + idx, projection := [] } (.use op)) := by
        have h0 := hSlice 0 (Nat.zero_lt_succ _)
        rw [Nat.add_zero] at h0; exact h0
      dsimp [evalCallArgsUnw]
      cases hOp : evalOperandToSlot ctx.caller.locals cSlots op with
      | error fk =>
        dsimp
        refine ⟨_, ReachesUnw.refl _, ⟨0, rfl, ?_⟩⟩
        unfold evalStepUnw
        rw [ctx_bodies_lookup_eq ctx]; dsimp
        rw [ctx_caller'_bb_lookup_call ctx]; dsimp
        rw [hStmt0]; dsimp [evalStatement]
        rw [hDstTy']; dsimp [evalRvalue, InlineUnwCtx.caller']
        rw [evalOperandToSlot_prefix hLenC hOpLt, hOp]
      | ok tup =>
        cases tup with
        | mk srcTy pr1 =>
          cases pr1 with
          | mk ov locs1 =>
            let ⟨hL1, hValTy, hW1⟩ := evalOperandToSlot_wf hLenC hWt hOp
            have hSrcEq : srcTy = ty :=
              (operandTy?_eq_evalOperandToSlot hOpTy hOp).trans hTyEq
            have hSrcBeq : MirTy.beq srcTy ty = true := by
              rw [hSrcEq]; exact mirTy_beq_refl ty
            cases ov with
            | none =>
              dsimp
              refine ⟨_, ReachesUnw.refl _, ⟨0, rfl, ?_⟩⟩
              unfold evalStepUnw
              rw [ctx_bodies_lookup_eq ctx]; dsimp
              rw [ctx_caller'_bb_lookup_call ctx]; dsimp
              rw [hStmt0]; dsimp [evalStatement]
              rw [hDstTy']; dsimp [evalRvalue, InlineUnwCtx.caller']
              rw [evalOperandToSlot_prefix hLenC hOpLt, hOp]
              dsimp
              rw [hSrcBeq]; rfl
            | some v =>
              dsimp
              have hCv : checkVal v ty = true := by
                rw [← hSrcEq]; exact hValTy v rfl
              let ⟨ov0, hLive0⟩ := hLive 0 (Nat.zero_lt_succ _)
              rw [Nat.add_zero] at hLive0
              have hSlotLt : 1 + idx < eSlots.length := getElem?_some_lt hLive0
              let ⟨eSlots1, hSetE⟩ := setElem?_some_of_lt eSlots (1 + idx) (LocalSlot.live (some v)) hSlotLt
              have hWrE : writePlace eSlots (1 + idx) ty v = .ok eSlots1 := by
                unfold writePlace
                rw [hCv]; dsimp
                rw [hLive0, hSetE]
              have hStep : StepUnw pTgt
                  { active := { defId := site.callerDefId, blockIdx := site.callBlock,
                                stmtIdx := stmtOff, locals := cSlots ++ eSlots },
                    callStack := stack, callerMem := mem }
                  (.step { active := { defId := site.callerDefId, blockIdx := site.callBlock,
                                       stmtIdx := stmtOff + 1, locals := locs1 ++ eSlots1 },
                           callStack := stack, callerMem := mem }) := by
                refine ⟨0, rfl, ?_⟩
                unfold evalStepUnw
                rw [ctx_bodies_lookup_eq ctx]; dsimp
                rw [ctx_caller'_bb_lookup_call ctx]; dsimp
                rw [hStmt0]; dsimp [evalStatement]
                rw [hDstTy']; dsimp [evalRvalue, InlineUnwCtx.caller']
                rw [evalOperandToSlot_prefix hLenC hOpLt, hOp]
                dsimp
                rw [hSrcBeq]
                dsimp
                have hWr : writePlace (locs1 ++ eSlots) (ctx.locOff + 1 + idx) ty v =
                    .ok (locs1 ++ eSlots1) := by
                  have hComm : ctx.locOff + 1 + idx = (1 + idx) + ctx.locOff := by
                    rw [Nat.add_assoc, Nat.add_comm]
                  rw [hComm]
                  dsimp [InlineUnwCtx.locOff]
                  rw [← hL1, writePlace_suffix, hWrE]
                rw [hWr]
              have hLenE1 : eSlots1.length = ctx.callee.locals.length :=
                (setElem?_length hSetE).trans hLenE
              have hPTy1 : ∀ (k : Nat) (t : MirTy),
                  Trusted.MirSemantics.getElem? pTys k = some t →
                  Trusted.MirSemantics.getElem? ctx.callee.locals (1 + (idx + 1) + k) =
                    some t := by
                intro k t ht
                have hEq : 1 + (idx + 1) + k = 1 + idx + (k + 1) := by
                  rw [← Nat.add_assoc 1 idx 1, Nat.add_assoc (1 + idx) 1 k, Nat.add_comm 1 k]
                rw [hEq]
                exact hPTy (k + 1) t ht
              have hLive1 : ∀ (k : Nat), k < ops.length →
                  ∃ ov : Option Val,
                    Trusted.MirSemantics.getElem? eSlots1 (1 + (idx + 1) + k) =
                      some (.live ov) := by
                intro k hk
                have hEq : 1 + (idx + 1) + k = 1 + idx + (k + 1) := by
                  rw [← Nat.add_assoc 1 idx 1, Nat.add_assoc (1 + idx) 1 k, Nat.add_comm 1 k]
                rw [hEq]
                have hNe : 1 + idx + (k + 1) ≠ 1 + idx :=
                  Nat.ne_of_gt (Nat.lt_add_of_pos_right (Nat.zero_lt_succ k))
                rw [setElem?_getElem?_ne hSetE hNe]
                exact hLive (k + 1) (Nat.succ_lt_succ hk)
              have hSlice1 : ∀ (k : Nat), k < ops.length →
                  Trusted.MirSemantics.getElem? ctx.callBb'.statements (stmtOff + 1 + k) =
                    Trusted.MirSemantics.getElem? (mkArgBindStmts ctx.locOff (idx + 1) ops) k := by
                intro k hk
                have hEq : stmtOff + 1 + k = stmtOff + (k + 1) := by
                  rw [Nat.add_assoc, Nat.add_comm 1 k]
                rw [hEq]
                exact hSlice (k + 1) (Nat.succ_lt_succ hk)
              have hIh := run_argBinds_loop ctx stack mem ops pTys (idx + 1) (stmtOff + 1)
                locs1 eSlots1 hL1 hLenE1 hW1 hOpsLt' hMatch' hPTy1 hLive1 hSlice1
              cases hRest : evalCallArgsUnw ctx.caller.locals locs1 ops with
              | error fk =>
                rw [hRest] at hIh
                dsimp at hIh
                let ⟨s', hRs', hSt'⟩ := hIh
                exact ⟨s', reachesUnw_trans (ReachesUnw.tail (ReachesUnw.refl _) hStep) hRs', hSt'⟩
              | ok pr =>
                rw [hRest] at hIh
                dsimp at hIh
                dsimp [overwriteArgs]
                rw [hSetE]
                have hAdd1 : 1 + idx + 1 = 1 + (idx + 1) := (Nat.add_assoc 1 idx 1).symm
                have hAdd2 : stmtOff + 1 + ops.length = stmtOff + (ops.length + 1) := by
                  rw [Nat.add_assoc, Nat.add_comm 1 ops.length]
                rw [hAdd1]
                rw [hAdd2] at hIh
                exact reachesUnw_trans (ReachesUnw.tail (ReachesUnw.refl _) hStep) hIh

private theorem callArgsTyMatch_length {callerLocals : List MirTy} :
    ∀ {ops : List Operand} {tys : List MirTy},
      callArgsTyMatch callerLocals ops tys = true →
      ops.length = tys.length
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | op :: ops, _ :: tys, h => by
    dsimp [callArgsTyMatch] at h
    cases hTy : operandTy? callerLocals op with
    | none => rw [hTy] at h; cases h
    | some _ =>
      rw [hTy] at h; dsimp at h
      let ⟨_, hRest⟩ := bool_and_true h
      exact congrArg Nat.succ (callArgsTyMatch_length hRest)

private theorem list_getElem?_take {α : Type} :
    ∀ (n : Nat) (xs : List α) (k : Nat),
      k < n →
      Trusted.MirSemantics.getElem? (xs.take n) k =
        Trusted.MirSemantics.getElem? xs k
  | 0, _, _, hk => False.elim (Nat.not_lt_zero _ hk)
  | _ + 1, [], _, _ => rfl
  | _ + 1, _ :: _, 0, _ => rfl
  | n + 1, _ :: xs, k + 1, hk =>
    list_getElem?_take n xs k (Nat.lt_of_succ_lt_succ hk)

private theorem list_getElem?_take_none {α : Type} :
    ∀ (n : Nat) (xs : List α) (k : Nat),
      n ≤ k →
      Trusted.MirSemantics.getElem? (xs.take n) k = none
  | 0, _, _, _ => rfl
  | _ + 1, [], _, _ => rfl
  | _ + 1, _ :: _, 0, h => False.elim (Nat.not_succ_le_zero _ h)
  | n + 1, _ :: xs, k + 1, h =>
    list_getElem?_take_none n xs k (Nat.le_of_succ_le_succ h)

private theorem run_argBinds {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site)
    (cSlots : List LocalSlot) (hLenC : cSlots.length = ctx.locOff)
    (hWt : ∀ (i : Nat) (ty : MirTy) (vi : Val),
      Trusted.MirSemantics.getElem? ctx.caller.locals i = some ty →
      Trusted.MirSemantics.getElem? cSlots i = some (.live (some vi)) →
      checkVal vi ty = true)
    (stack : List CallContUnw) (mem : CallerMemory) :
    match evalCallArgsUnw ctx.caller.locals cSlots ctx.args with
    | .error fk =>
      ∃ s' : UnwindState,
        ReachesUnw pTgt
          { active := { defId := site.callerDefId, blockIdx := site.callBlock,
                        stmtIdx := ctx.callBb.statements.length + ctx.entryLives.length,
                        locals := cSlots ++
                          calleeAfterEntryLives ctx.callee 0 ctx.callee.locals },
            callStack := stack, callerMem := mem } s' ∧
        StepUnw pTgt s' (.fault fk)
    | .ok (vs, cSlots') =>
      ReachesUnw pTgt
        { active := { defId := site.callerDefId, blockIdx := site.callBlock,
                      stmtIdx := ctx.callBb.statements.length + ctx.entryLives.length,
                      locals := cSlots ++
                        calleeAfterEntryLives ctx.callee 0 ctx.callee.locals },
          callStack := stack, callerMem := mem }
        { active := { defId := site.callerDefId, blockIdx := site.callBlock,
                      stmtIdx := ctx.callBb.statements.length + ctx.entryLives.length +
                        ctx.args.length,
                      locals := cSlots' ++
                        initLocalsLoop ctx.callee vs 0 ctx.callee.locals },
          callStack := stack, callerMem := mem } := by
  have hOpsLt : ctx.args.all (operandLocalsLt ctx.locOff) = true := by
    have hBb := list_all_getElem? (ctx_caller_bbs_all ctx) ctx.hCallBb
    let ⟨_, hTm⟩ := bool_and_true hBb
    rw [ctx.hTerm] at hTm
    dsimp [callerTermInBounds] at hTm
    let ⟨h123, _⟩ := bool_and_true hTm
    let ⟨h12, _⟩ := bool_and_true h123
    let ⟨h1, _⟩ := bool_and_true h12
    exact h1
  have hPTysLen : ((ctx.callee.locals.drop 1).take ctx.callee.argumentCount).length =
      ctx.callee.argumentCount := by
    apply list_length_take
    rw [list_length_drop]
    have h := ctx_callee_argLt ctx
    exact Nat.le_sub_of_add_le h
  have hArgsLen : ctx.args.length = ctx.callee.argumentCount :=
    (callArgsTyMatch_length ctx.hArgsMatch).trans hPTysLen
  have hPTy : ∀ (k : Nat) (t : MirTy),
      Trusted.MirSemantics.getElem?
        ((ctx.callee.locals.drop 1).take ctx.callee.argumentCount) k = some t →
      Trusted.MirSemantics.getElem? ctx.callee.locals (1 + 0 + k) = some t := by
    intro k t ht
    have hkLt : k < ctx.callee.argumentCount := by
      have h := getElem?_some_lt ht
      rw [hPTysLen] at h; exact h
    rw [list_getElem?_take _ _ k hkLt, list_getElem?_drop] at ht
    rw [Nat.add_zero]
    exact ht
  have hLive : ∀ (k : Nat), k < ctx.args.length →
      ∃ ov : Option Val,
        Trusted.MirSemantics.getElem?
          (calleeAfterEntryLives ctx.callee 0 ctx.callee.locals) (1 + 0 + k) =
          some (.live ov) := by
    intro k hk
    rw [Nat.add_zero, calleeAfterEntryLives_getElem?, Nat.zero_add]
    have hKLe : 1 + k ≤ ctx.callee.argumentCount := by
      rw [Nat.add_comm]; rw [hArgsLen] at hk; exact hk
    have hKLt : 1 + k < ctx.callee.locals.length :=
      Nat.lt_of_le_of_lt hKLe (ctx_callee_argLt ctx)
    let ⟨ty, hTy⟩ := getElem?_some_of_lt ctx.callee.locals (1 + k) hKLt
    rw [hTy]; dsimp
    rw [nat_le_ble hKLe]; dsimp
    cases ty with
    | unit => exact ⟨some .unit, rfl⟩
    | enum ety =>
      dsimp [liveUninitSlot]
      cases isZstEnumTy ety with
      | true => exact ⟨some (.enumVal ety 0), rfl⟩
      | false => exact ⟨none, rfl⟩
    | bool | int _ _ | never | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
      exact ⟨none, rfl⟩
  have hSlice : ∀ (k : Nat), k < ctx.args.length →
      Trusted.MirSemantics.getElem? ctx.callBb'.statements
        (ctx.callBb.statements.length + ctx.entryLives.length + k) =
      Trusted.MirSemantics.getElem? (mkArgBindStmts ctx.locOff 0 ctx.args) k := by
    intro k hk
    dsimp [InlineUnwCtx.callBb', InlineUnwCtx.argBinds]
    have hLen : (ctx.callBb.statements ++ ctx.entryLives).length =
        ctx.callBb.statements.length + ctx.entryLives.length :=
      list_length_append _ _
    rw [← hLen, getElem?_append_right]
  have hRun := run_argBinds_loop ctx stack mem ctx.args
    ((ctx.callee.locals.drop 1).take ctx.callee.argumentCount) 0
    (ctx.callBb.statements.length + ctx.entryLives.length)
    cSlots (calleeAfterEntryLives ctx.callee 0 ctx.callee.locals)
    hLenC (calleeAfterEntryLives_length _ _ _) hWt hOpsLt ctx.hArgsMatch
    hPTy hLive hSlice
  cases hEv : evalCallArgsUnw ctx.caller.locals cSlots ctx.args with
  | error fk => rw [hEv] at hRun; exact hRun
  | ok pr =>
    rw [hEv] at hRun
    dsimp at hRun
    have hVsLen : pr.1.length = ctx.callee.argumentCount := by
      have hEvalLen : ∀ {ops : List Operand} {locs locs' : List LocalSlot} {vs : List Val},
          evalCallArgsUnw ctx.caller.locals locs ops = .ok (vs, locs') →
          vs.length = ops.length := by
        intro ops
        induction ops with
        | nil =>
          intro locs locs' vs h
          dsimp [evalCallArgsUnw] at h
          injection h with hp; injection hp with hv _; subst hv; rfl
        | cons op rest ih =>
          intro locs locs' vs h
          dsimp [evalCallArgsUnw] at h
          cases h1 : evalOperandToSlot ctx.caller.locals locs op with
          | error _ => rw [h1] at h; cases h
          | ok tup =>
            cases tup with
            | mk _ pr1 =>
              cases pr1 with
              | mk ov locs1 =>
                rw [h1] at h
                cases ov with
                | none => cases h
                | some v =>
                  dsimp at h
                  cases h2 : evalCallArgsUnw ctx.caller.locals locs1 rest with
                  | error _ => rw [h2] at h; cases h
                  | ok pr2 =>
                    rw [h2] at h; dsimp at h
                    injection h with hp; injection hp with hv _; subst hv
                    exact congrArg Nat.succ (ih h2)
      exact (hEvalLen hEv).trans hArgsLen
    rw [overwriteArgs_calleeAfterEntryLives_eq_initLocalsLoop ctx.callee pr.1
          (ctx_callee_argLt ctx) hVsLen] at hRun
    exact hRun

/-! ### Part 6: Multi-Step Gadget 3 — `deads` (`mkAllStorageDead`) -/

private theorem mkAllStorageDead_length (base : Nat) :
    ∀ (n : Nat), (mkAllStorageDead base n).length = n
  | 0 => rfl
  | n + 1 => congrArg Nat.succ (mkAllStorageDead_length base n)

private theorem run_deads_loop {p : Program} {body : Body} {bb : BasicBlock}
    {defId : DefId} {bbIdx base : Nat}
    (hBody : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (hBb : Trusted.MirSemantics.getElem? body.basicBlocks bbIdx = some bb)
    (hPos : 0 < base)
    (cSlots : List LocalSlot) (hLenC : cSlots.length = base)
    (stack : List CallContUnw) (mem : CallerMemory) :
    ∀ (n stmtOff : Nat) (eSlots tailSlots : List LocalSlot),
      eSlots.length = n →
      (∀ (k : Nat), k < n →
        Trusted.MirSemantics.getElem? bb.statements (stmtOff + k) =
          Trusted.MirSemantics.getElem? (mkAllStorageDead base n) k) →
      ReachesUnw p
        { active := { defId := defId, blockIdx := bbIdx, stmtIdx := stmtOff,
                      locals := cSlots ++ (eSlots ++ tailSlots) },
          callStack := stack, callerMem := mem }
        { active := { defId := defId, blockIdx := bbIdx, stmtIdx := stmtOff + n,
                      locals := cSlots ++ (replicateDead n ++ tailSlots) },
          callStack := stack, callerMem := mem }
  | 0, stmtOff, eSlots, tailSlots, hLenE, _ => by
    cases eSlots with
    | cons _ _ => cases hLenE
    | nil =>
      dsimp [replicateDead]
      exact ReachesUnw.refl _
  | n + 1, stmtOff, eSlots, tailSlots, hLenE, hSlice => by
    have hSplit : ∀ {α : Type} (m : Nat) (xs : List α) (h : xs.length = m + 1),
        ∃ (ys : List α) (z : α), ys.length = m ∧ xs = ys ++ [z] := by
      intro α m
      induction m with
      | zero =>
        intro xs h
        cases xs with
        | nil => cases h
        | cons a rest =>
          cases rest with
          | cons _ _ => cases h
          | nil => exact ⟨[], a, rfl, rfl⟩
      | succ m ih =>
        intro xs h
        cases xs with
        | nil => cases h
        | cons a rest =>
          let ⟨ys, z, hyl, hEq⟩ := ih rest (Nat.succ.inj h)
          exact ⟨a :: ys, z, congrArg Nat.succ hyl, congrArg (a :: ·) hEq⟩
    let ⟨ys, z, hyl, hEqE⟩ := hSplit n eSlots hLenE
    subst hEqE
    have hStmt0 : Trusted.MirSemantics.getElem? bb.statements stmtOff =
        some (.storageDead (base + n)) := by
      have h0 := hSlice 0 (Nat.zero_lt_succ n)
      rw [Nat.add_zero] at h0; exact h0
    have hLocPos : 0 < base + n := Nat.lt_of_lt_of_le hPos (Nat.le_add_right _ _)
    have hSet : setElem? (cSlots ++ ((ys ++ [z]) ++ tailSlots)) (base + n) .dead =
        some (cSlots ++ (ys ++ (.dead :: tailSlots))) := by
      rw [← hLenC, setElem?_append_right cSlots ((ys ++ [z]) ++ tailSlots) n .dead]
      rw [List.append_assoc]
      have hN : n = ys.length + 0 := by rw [hyl, Nat.add_zero]
      rw [hN, setElem?_append_right ys ([z] ++ tailSlots) 0 .dead]
      rfl
    have hStep : StepUnw p
        { active := { defId := defId, blockIdx := bbIdx, stmtIdx := stmtOff,
                      locals := cSlots ++ ((ys ++ [z]) ++ tailSlots) },
          callStack := stack, callerMem := mem }
        (.step { active := { defId := defId, blockIdx := bbIdx, stmtIdx := stmtOff + 1,
                             locals := cSlots ++ (ys ++ (.dead :: tailSlots)) },
                 callStack := stack, callerMem := mem }) :=
      step_storageDead_in_block hBody hBb hStmt0 hLocPos hSet
    have hSlice1 : ∀ (k : Nat), k < n →
        Trusted.MirSemantics.getElem? bb.statements (stmtOff + 1 + k) =
          Trusted.MirSemantics.getElem? (mkAllStorageDead base n) k := by
      intro k hk
      have hEq : stmtOff + 1 + k = stmtOff + (k + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 k]
      rw [hEq]
      exact hSlice (k + 1) (Nat.succ_lt_succ hk)
    have hRest := run_deads_loop hBody hBb hPos cSlots hLenC stack mem
      n (stmtOff + 1) ys (.dead :: tailSlots) hyl hSlice1
    have hAdd : stmtOff + 1 + n = stmtOff + (n + 1) := by
      rw [Nat.add_assoc, Nat.add_comm 1 n]
    have hRep : replicateDead n ++ (.dead :: tailSlots) =
        replicateDead (n + 1) ++ tailSlots := by
      have hRepComm : ∀ (m : Nat), replicateDead m ++ [.dead] = .dead :: replicateDead m := by
        intro m
        induction m with
        | zero => rfl
        | succ m ih =>
          dsimp [replicateDead, List.append]
          rw [ih]
      have h1 : replicateDead n ++ (.dead :: tailSlots) =
          (replicateDead n ++ [.dead]) ++ tailSlots := by
        rw [List.append_assoc]; rfl
      rw [h1, hRepComm n]; rfl
    rw [hAdd, hRep] at hRest
    exact reachesUnw_trans (ReachesUnw.tail (ReachesUnw.refl _) hStep) hRest

private theorem run_deads_normalExit {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site)
    (cSlots eSlots : List LocalSlot)
    (hLenC : cSlots.length = ctx.locOff)
    (hLenE : eSlots.length = ctx.callee.locals.length)
    (stack : List CallContUnw) (mem : CallerMemory) :
    ReachesUnw pTgt
      { active := { defId := site.callerDefId, blockIdx := ctx.normalExitBb,
                    stmtIdx := 1, locals := cSlots ++ eSlots },
        callStack := stack, callerMem := mem }
      { active := { defId := site.callerDefId, blockIdx := ctx.normalExitBb,
                    stmtIdx := ctx.normalExitBlock.statements.length,
                    locals := cSlots ++ replicateDead ctx.callee.locals.length },
        callStack := stack, callerMem := mem } := by
  have hSlice : ∀ (k : Nat), k < ctx.callee.locals.length →
      Trusted.MirSemantics.getElem? ctx.normalExitBlock.statements (1 + k) =
        Trusted.MirSemantics.getElem? (mkAllStorageDead ctx.locOff ctx.callee.locals.length) k := by
    intro k _
    have hEq : 1 + k = k + 1 := Nat.add_comm 1 k
    rw [hEq]; rfl
  have hRun := run_deads_loop (ctx_bodies_lookup_eq ctx)
    (ctx_caller'_bb_lookup_normalExit ctx) (ctx_locOff_pos ctx)
    cSlots hLenC stack mem ctx.callee.locals.length 1 eSlots [] hLenE hSlice
  have hLenSt : ctx.normalExitBlock.statements.length = 1 + ctx.callee.locals.length := by
    dsimp [InlineUnwCtx.normalExitBlock, InlineUnwCtx.deads, List.length]
    rw [mkAllStorageDead_length, Nat.add_comm]
  rw [List.append_nil, List.append_nil, ← hLenSt] at hRun
  exact hRun

private theorem run_deads_unwindExit {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site)
    (cSlots eSlots : List LocalSlot)
    (hLenC : cSlots.length = ctx.locOff)
    (hLenE : eSlots.length = ctx.callee.locals.length)
    (stack : List CallContUnw) (mem : CallerMemory) :
    ReachesUnw pTgt
      { active := { defId := site.callerDefId, blockIdx := ctx.unwindExitBb,
                    stmtIdx := 0, locals := cSlots ++ eSlots },
        callStack := stack, callerMem := mem }
      { active := { defId := site.callerDefId, blockIdx := ctx.unwindExitBb,
                    stmtIdx := ctx.unwindExitBlock.statements.length,
                    locals := cSlots ++ replicateDead ctx.callee.locals.length },
        callStack := stack, callerMem := mem } := by
  have hSlice : ∀ (k : Nat), k < ctx.callee.locals.length →
      Trusted.MirSemantics.getElem? ctx.unwindExitBlock.statements (0 + k) =
        Trusted.MirSemantics.getElem? (mkAllStorageDead ctx.locOff ctx.callee.locals.length) k := by
    intro k _
    rw [Nat.zero_add]; rfl
  have hRun := run_deads_loop (ctx_bodies_lookup_eq ctx)
    (ctx_caller'_bb_lookup_unwindExit ctx) (ctx_locOff_pos ctx)
    cSlots hLenC stack mem ctx.callee.locals.length 0 eSlots [] hLenE hSlice
  have hLenSt : ctx.unwindExitBlock.statements.length = 0 + ctx.callee.locals.length := by
    dsimp [InlineUnwCtx.unwindExitBlock, InlineUnwCtx.deads]
    rw [mkAllStorageDead_length, Nat.zero_add]
  rw [List.append_nil, List.append_nil, ← hLenSt] at hRun
  exact hRun

/-! ### Slice: Slice3c_InlineStep.lean -/

-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.





/-! ### Part 1: Switch-Branch Shifting & Bounds Helpers -/

private theorem evalSwitchBranches_shift (w : IntWidth) (bits : BitVec 128)
    (bbOff : Nat) (oth : BasicBlockId) :
    ∀ (brs : List (BitVec 128 × BasicBlockId)),
      evalSwitchBranches w bits (oth + bbOff)
        (brs.map (fun br => (br.1, br.2 + bbOff))) =
        match evalSwitchBranches w bits oth brs with
        | .error k => .error k
        | .ok t => .ok (t + bbOff)
  | [] => rfl
  | (c, t) :: rest => by
    dsimp [List.map, evalSwitchBranches]
    cases (truncateBits w c != c) with
    | true => rfl
    | false =>
      dsimp
      cases (truncateBits w bits == truncateBits w c) with
      | true => rfl
      | false => exact evalSwitchBranches_shift w bits bbOff oth rest

private theorem evalBoolSwitchBranches_shift (b : Bool) (bbOff : Nat) (oth : BasicBlockId) :
    ∀ (brs : List (BitVec 128 × BasicBlockId)),
      evalBoolSwitchBranches b (oth + bbOff)
        (brs.map (fun br => (br.1, br.2 + bbOff))) =
        match evalBoolSwitchBranches b oth brs with
        | .error k => .error k
        | .ok t => .ok (t + bbOff)
  | [] => rfl
  | (c, t) :: rest => by
    dsimp [List.map, evalBoolSwitchBranches]
    cases evalConstLit .bool (.scalar c) with
    | error _ => rfl
    | ok v =>
      cases v with
      | bool cv =>
        cases cv with
        | false =>
          cases (!b) with
          | true => rfl
          | false => exact evalBoolSwitchBranches_shift b bbOff oth rest
        | true =>
          cases b with
          | true => rfl
          | false => exact evalBoolSwitchBranches_shift false bbOff oth rest
      | scalar _ | unit | ptr _ | enumVal _ _ | tuple _ | bytes _ => rfl

private theorem evalSwitchBranches_lt {w : IntWidth} {bits : BitVec 128}
    {n oth : Nat} :
    ∀ {brs : List (BitVec 128 × BasicBlockId)} {t : BasicBlockId},
      oth < n →
      brs.all (fun br => Nat.blt br.2 n) = true →
      evalSwitchBranches w bits oth brs = .ok t →
      t < n
  | [], _, hOth, _, hEv => by
    dsimp [evalSwitchBranches] at hEv
    injection hEv with ht; subst ht; exact hOth
  | (c, b) :: rest, t, hOth, hAll, hEv => by
    dsimp [List.all] at hAll
    let ⟨hB, hRest⟩ := bool_and_true hAll
    dsimp [evalSwitchBranches] at hEv
    cases h1 : (truncateBits w c != c) <;> rw [h1] at hEv
    · dsimp at hEv
      cases h2 : (truncateBits w bits == truncateBits w c) <;> rw [h2] at hEv
      · dsimp at hEv
        exact evalSwitchBranches_lt hOth hRest hEv
      · dsimp at hEv; injection hEv with ht; subst ht; exact nat_blt_lt hB
    · cases hEv

private theorem evalBoolSwitchBranches_lt {b : Bool} {n oth : Nat} :
    ∀ {brs : List (BitVec 128 × BasicBlockId)} {t : BasicBlockId},
      oth < n →
      brs.all (fun br => Nat.blt br.2 n) = true →
      evalBoolSwitchBranches b oth brs = .ok t →
      t < n
  | [], _, hOth, _, hEv => by
    dsimp [evalBoolSwitchBranches] at hEv
    injection hEv with ht; subst ht; exact hOth
  | (c, tgt) :: rest, t, hOth, hAll, hEv => by
    dsimp [List.all] at hAll
    let ⟨hB, hRest⟩ := bool_and_true hAll
    dsimp [evalBoolSwitchBranches] at hEv
    cases hc : evalConstLit .bool (.scalar c) with
    | error _ => rw [hc] at hEv; cases hEv
    | ok v =>
      rw [hc] at hEv
      cases v with
      | bool cv =>
        cases cv with
        | false =>
          dsimp at hEv
          cases hb : (!b) <;> rw [hb] at hEv
          · dsimp at hEv; exact evalBoolSwitchBranches_lt hOth hRest hEv
          · dsimp at hEv; injection hEv with ht; subst ht; exact nat_blt_lt hB
        | true =>
          dsimp at hEv
          cases b with
          | false => dsimp at hEv; exact evalBoolSwitchBranches_lt hOth hRest hEv
          | true => dsimp at hEv; injection hEv with ht; subst ht; exact nat_blt_lt hB
      | scalar _ | unit | ptr _ | enumVal _ _ | tuple _ | bytes _ => cases hEv

private theorem frameWf_reset_block {p : Program} {f : FrameState} {bbIdx : BasicBlockId}
    {locals' : List LocalSlot}
    (hWf : ∀ body : Body,
      Trusted.MirSemantics.getElem? p.bodies f.defId = some body →
      locals'.length = body.locals.length ∧
      (∀ i ty v,
        Trusted.MirSemantics.getElem? body.locals i = some ty →
        Trusted.MirSemantics.getElem? locals' i = some (.live (some v)) →
        checkVal v ty = true)) :
    FrameWf p { f with blockIdx := bbIdx, stmtIdx := 0, locals := locals' } := by
  intro body hBod
  let ⟨hL, hW⟩ := hWf body hBod
  exact ⟨hL, hW, fun _ _ => Nat.zero_le _⟩

private theorem frameWf_same_locals_block {p : Program} {f : FrameState} {bbIdx : BasicBlockId}
    (hWf : FrameWf p f) :
    FrameWf p { f with blockIdx := bbIdx, stmtIdx := 0 } := by
  intro body hBod
  let ⟨hL, hW, _⟩ := hWf body hBod
  exact ⟨hL, hW, fun _ _ => Nat.zero_le _⟩

private theorem frameWf_update_locals_same_loc {p : Program} {body : Body}
    {f : FrameState} {locals' : List LocalSlot}
    (hBod : Trusted.MirSemantics.getElem? p.bodies f.defId = some body)
    (hWf : FrameWf p f)
    (hLen : locals'.length = body.locals.length)
    (hWt : ∀ i ty v,
      Trusted.MirSemantics.getElem? body.locals i = some ty →
      Trusted.MirSemantics.getElem? locals' i = some (.live (some v)) →
      checkVal v ty = true) :
    FrameWf p { f with locals := locals' } := by
  intro b2 hb2
  rw [hBod] at hb2; injection hb2 with hEq; subst hEq
  let ⟨_, _, hSt⟩ := hWf body hBod
  exact ⟨hLen, hWt, hSt⟩

private theorem frameWf_update_locals_reset {p : Program} {body : Body}
    {f : FrameState} {bbIdx : BasicBlockId} {locals' : List LocalSlot}
    (hBod : Trusted.MirSemantics.getElem? p.bodies f.defId = some body)
    (hLen : locals'.length = body.locals.length)
    (hWt : ∀ i ty v,
      Trusted.MirSemantics.getElem? body.locals i = some ty →
      Trusted.MirSemantics.getElem? locals' i = some (.live (some v)) →
      checkVal v ty = true) :
    FrameWf p { f with blockIdx := bbIdx, stmtIdx := 0, locals := locals' } := by
  intro b2 hb2
  rw [hBod] at hb2; injection hb2 with hEq; subst hEq
  exact ⟨hLen, hWt, fun _ _ => Nat.zero_le _⟩

/-! ### Part 2: Fused-Frame Simulation Relations (`InlNormalFrameRel`, `InlStackRel`, `InlStateRel`) -/

private inductive InlNormalFrameRel {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) : FrameState → FrameState → Prop where
  | other {f : FrameState} :
      f.defId ≠ site.callerDefId →
      InlNormalFrameRel ctx f f
  | caller {f : FrameState} :
      f.defId = site.callerDefId →
      f.blockIdx < ctx.bbOff →
      FrameWf pSrc f →
      InlNormalFrameRel ctx f
        { f with locals := f.locals ++ replicateDead ctx.callee.locals.length }

private inductive InlStackRel {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) :
    List CallContUnw → List CallContUnw → Prop where
  | nil : InlStackRel ctx [] []
  | consSingle {cont₁ cont₂ : CallContUnw} {rest₁ rest₂ : List CallContUnw} :
      InlNormalFrameRel ctx cont₁.callerFrame cont₂.callerFrame →
      cont₂.dst = cont₁.dst →
      cont₂.target = cont₁.target →
      cont₂.unwind = cont₁.unwind →
      (cont₁.callerFrame.defId = site.callerDefId →
        cont₁.dst.localId < ctx.locOff ∧
        (∀ tBb, cont₁.target = some tBb → tBb < ctx.bbOff) ∧
        (∀ pBb, cont₁.unwind = .cleanup pBb → pBb < ctx.bbOff)) →
      InlStackRel ctx rest₁ rest₂ →
      InlStackRel ctx (cont₁ :: rest₁) (cont₂ :: rest₂)
  | consFused {eCont cCont : CallContUnw} {rest₁ rest₂ : List CallContUnw} :
      cCont.callerFrame.defId = site.callerDefId →
      FrameWf pSrc cCont.callerFrame →
      cCont.dst = ctx.dst →
      cCont.target = ctx.target →
      cCont.unwind = ctx.callerUnwind →
      eCont.callerFrame.defId = site.calleeDefId →
      eCont.callerFrame.blockIdx < ctx.callee.basicBlocks.length →
      FrameWf pSrc eCont.callerFrame →
      eCont.dst.localId < ctx.callee.locals.length →
      (∀ tBb, eCont.target = some tBb → tBb < ctx.callee.basicBlocks.length) →
      unwindActionBlocksLt ctx.callee.basicBlocks.length ctx.callee.basicBlocks eCont.unwind = true →
      InlStackRel ctx rest₁ rest₂ →
      InlStackRel ctx (eCont :: cCont :: rest₁)
        ({ callerFrame := {
             defId := site.callerDefId
             blockIdx := eCont.callerFrame.blockIdx + ctx.bbOff
             stmtIdx := eCont.callerFrame.stmtIdx
             locals := cCont.callerFrame.locals ++ eCont.callerFrame.locals
           }
           dst := shiftPlaceUnw ctx.locOff eCont.dst
           target := match eCont.target with | none => none | some t => some (t + ctx.bbOff)
           unwind := shiftCalleeUnwindAction ctx.bbOff ctx.unwindExitBb eCont.unwind } :: rest₂)

private inductive InlStateRel {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) : UnwindState → UnwindState → Prop where
  | unfused {f₁ f₂ : FrameState} {stack₁ stack₂ : List CallContUnw}
      {mem : CallerMemory} :
      InlNormalFrameRel ctx f₁ f₂ →
      InlStackRel ctx stack₁ stack₂ →
      InlStateRel ctx
        { active := f₁, callStack := stack₁, callerMem := mem }
        { active := f₂, callStack := stack₂, callerMem := mem }
  | fused {eFrame : FrameState} {cCont : CallContUnw}
      {rest₁ rest₂ : List CallContUnw} {mem : CallerMemory} :
      eFrame.defId = site.calleeDefId →
      eFrame.blockIdx < ctx.callee.basicBlocks.length →
      FrameWf pSrc eFrame →
      cCont.callerFrame.defId = site.callerDefId →
      FrameWf pSrc cCont.callerFrame →
      cCont.dst = ctx.dst →
      cCont.target = ctx.target →
      cCont.unwind = ctx.callerUnwind →
      InlStackRel ctx rest₁ rest₂ →
      InlStateRel ctx
        { active := eFrame, callStack := cCont :: rest₁, callerMem := mem }
        { active := {
            defId := site.callerDefId
            blockIdx := eFrame.blockIdx + ctx.bbOff
            stmtIdx := eFrame.stmtIdx
            locals := cCont.callerFrame.locals ++ eFrame.locals
          }
          callStack := rest₂
          callerMem := mem }

/-! ### Part 3: `SimOutcome` Combinators & `initCalleeFrameUnw` Agreement -/

private noncomputable def SimOutcome {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) (s₂ : UnwindState) :
    StepResult UnwindState UnwindOut → Prop
  | .step s₁' => ∃ s₂', ReachesPlusUnw pTgt s₂ s₂' ∧ InlStateRel ctx s₁' s₂'
  | .done out => ∃ s₂', ReachesUnw pTgt s₂ s₂' ∧ evalStepUnw pTgt 0 s₂' = .done out
  | .fault k => ∃ s₂', ReachesUnw pTgt s₂ s₂' ∧ evalStepUnw pTgt 0 s₂' = .fault k

private theorem reachesPlusUnw_of_step {p : Program} {s₁ s₂ : UnwindState}
    (h : evalStepUnw p 0 s₁ = .step s₂) :
    ReachesPlusUnw p s₁ s₂ :=
  ⟨0, ReachesNUnw.succ h (ReachesNUnw.zero s₂)⟩

private theorem reachesPlusUnw_of_step_reaches {p : Program} {s₁ s₂ s₃ : UnwindState}
    (hStep : evalStepUnw p 0 s₁ = .step s₂)
    (hReach : ReachesUnw p s₂ s₃) :
    ReachesPlusUnw p s₁ s₃ := by
  let ⟨n, hn⟩ := reachesUnw_to_reachesNUnw hReach
  exact ⟨n, ReachesNUnw.succ hStep hn⟩

private theorem reachesPlusUnw_of_reachesPlus_reaches {p : Program} {s₁ s₂ s₃ : UnwindState}
    (h1 : ReachesPlusUnw p s₁ s₂)
    (h2 : ReachesUnw p s₂ s₃) :
    ReachesPlusUnw p s₁ s₃ := by
  let ⟨m, hm⟩ := h1
  let ⟨n, hn⟩ := reachesUnw_to_reachesNUnw h2
  have hT := reachesNUnw_trans hm hn
  have hAdd : m + 1 + n = m + n + 1 := by
    rw [Nat.add_assoc, Nat.add_comm 1 n, ← Nat.add_assoc]
  rw [hAdd] at hT
  exact ⟨m + n, hT⟩

private theorem simOutcome_step_one {pSrc pTgt : Program} {site : UnwindInlineSite}
    {ctx : InlineUnwCtx pSrc pTgt site} {s₂ s₂' s₁' : UnwindState}
    (hEv : evalStepUnw pTgt 0 s₂ = .step s₂')
    (hRel : InlStateRel ctx s₁' s₂') :
    SimOutcome ctx s₂ (.step s₁') :=
  ⟨s₂', reachesPlusUnw_of_step hEv, hRel⟩

private theorem simOutcome_done_zero {pSrc pTgt : Program} {site : UnwindInlineSite}
    {ctx : InlineUnwCtx pSrc pTgt site} {s₂ : UnwindState} {out : UnwindOut}
    (hEv : evalStepUnw pTgt 0 s₂ = .done out) :
    SimOutcome ctx s₂ (.done out) :=
  ⟨s₂, ReachesUnw.refl s₂, hEv⟩

private theorem simOutcome_fault_zero {pSrc pTgt : Program} {site : UnwindInlineSite}
    {ctx : InlineUnwCtx pSrc pTgt site} {s₂ : UnwindState} {k : FaultKind}
    (hEv : evalStepUnw pTgt 0 s₂ = .fault k) :
    SimOutcome ctx s₂ (.fault k) :=
  ⟨s₂, ReachesUnw.refl s₂, hEv⟩

private theorem simOutcome_prepend_step {pSrc pTgt : Program} {site : UnwindInlineSite}
    {ctx : InlineUnwCtx pSrc pTgt site} {s₂ s₂' : UnwindState}
    {res : StepResult UnwindState UnwindOut}
    (hStep : evalStepUnw pTgt 0 s₂ = .step s₂')
    (hOut : SimOutcome ctx s₂' res) :
    SimOutcome ctx s₂ res := by
  cases res with
  | step s₁' =>
    let ⟨t₂, hPlus, hRel⟩ := hOut
    let ⟨m, hm⟩ := hPlus
    exact ⟨t₂, reachesPlusUnw_of_step_reaches hStep (reachesNUnw_to_reachesUnw hm), hRel⟩
  | done out =>
    let ⟨t₂, hR, hEv⟩ := hOut
    exact ⟨t₂, c_reachesUnw_head_det hStep hR, hEv⟩
  | fault k =>
    let ⟨t₂, hR, hEv⟩ := hOut
    exact ⟨t₂, c_reachesUnw_head_det hStep hR, hEv⟩

private theorem simOutcome_prepend_reaches {pSrc pTgt : Program} {site : UnwindInlineSite}
    {ctx : InlineUnwCtx pSrc pTgt site} {s₂ s₂' : UnwindState}
    {res : StepResult UnwindState UnwindOut}
    (hReach : ReachesUnw pTgt s₂ s₂')
    (hOut : SimOutcome ctx s₂' res) :
    SimOutcome ctx s₂ res := by
  cases res with
  | step s₁' =>
    let ⟨t₂, hPlus, hRel⟩ := hOut
    let ⟨n, hn⟩ := reachesUnw_to_reachesNUnw hReach
    let ⟨m, hm⟩ := hPlus
    have hT := reachesNUnw_trans hn hm
    have hEq : n + (m + 1) = n + m + 1 := (Nat.add_assoc n m 1).symm
    rw [hEq] at hT
    exact ⟨t₂, ⟨n + m, hT⟩, hRel⟩
  | done out =>
    let ⟨t₂, hR, hEv⟩ := hOut
    exact ⟨t₂, reachesUnw_trans hReach hR, hEv⟩
  | fault k =>
    let ⟨t₂, hR, hEv⟩ := hOut
    exact ⟨t₂, reachesUnw_trans hReach hR, hEv⟩

private theorem inl_initCalleeFrame_caller {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) (av : List Val) :
    initCalleeFrameUnw site.callerDefId ctx.caller' av =
      match initCalleeFrameUnw site.callerDefId ctx.caller av with
      | .error k => .error k
      | .ok cf => .ok { cf with locals := cf.locals ++ replicateDead ctx.callee.locals.length } := by
  unfold initCalleeFrameUnw
  have hNe1 := ctx_caller_bbs_nonEmpty ctx
  have hNe2 := ctx_caller'_bbs_nonEmpty ctx
  have hArg1 : Nat.blt ctx.caller.argumentCount ctx.caller.locals.length = true :=
    nat_lt_blt (ctx_caller_argLt ctx)
  have hArg2 : Nat.blt ctx.caller'.argumentCount ctx.caller'.locals.length = true := by
    dsimp [InlineUnwCtx.caller']
    rw [list_length_append]
    exact nat_lt_blt (Nat.lt_of_lt_of_le (ctx_caller_argLt ctx) (Nat.le_add_right _ _))
  have hSt1 := ctx_caller_storageInBounds ctx
  have hSt2 := ctx_caller'_storageInBounds ctx
  have hSup := ctx_caller'_locals_supported ctx
  have hP := ctx_caller'_paramTys ctx
  have hInit := ctx_caller'_initLocalsLoop ctx av
  rw [hNe1, hNe2, hArg1, hArg2, hSt1, hSt2, hSup, hP, hInit]
  dsimp
  cases ctx.caller.locals.all isSupportedScalarOrUnitTy with
  | false => rfl
  | true =>
    dsimp
    cases checkArgsMatch av ((ctx.caller.locals.drop 1).take ctx.caller.argumentCount) <;> rfl

private theorem inl_initCalleeFrame_any {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) (calleeId : DefId) (av : List Val) :
    match Trusted.MirSemantics.getElem? pSrc.bodies calleeId with
    | none => Trusted.MirSemantics.getElem? pTgt.bodies calleeId = none
    | some cb₁ =>
      ∃ cb₂ : Body,
        Trusted.MirSemantics.getElem? pTgt.bodies calleeId = some cb₂ ∧
        match initCalleeFrameUnw calleeId cb₁ av with
        | .error k => initCalleeFrameUnw calleeId cb₂ av = .error k
        | .ok cf₁ =>
          ∃ cf₂ : FrameState,
            initCalleeFrameUnw calleeId cb₂ av = .ok cf₂ ∧
            InlNormalFrameRel ctx cf₁ cf₂ := by
  cases hEq : Nat.beq calleeId site.callerDefId with
  | true =>
    have hId : calleeId = site.callerDefId := nat_beq_eq hEq
    subst hId
    rw [ctx.hCaller]
    refine ⟨ctx.caller', ctx_bodies_lookup_eq ctx, ?_⟩
    rw [inl_initCalleeFrame_caller ctx av]
    cases hInit : initCalleeFrameUnw site.callerDefId ctx.caller av with
    | error k => rfl
    | ok cf₁ =>
      dsimp
      let ⟨hWf, hDef, hBb, _⟩ := initCalleeFrameUnw_wf ctx.hCaller hInit
      have hBbLt : cf₁.blockIdx < ctx.bbOff := by
        rw [hBb]
        exact Nat.lt_of_le_of_lt (Nat.zero_le _) (getElem?_some_lt ctx.hCallBb)
      exact ⟨{ cf₁ with locals := cf₁.locals ++ replicateDead ctx.callee.locals.length },
             rfl, InlNormalFrameRel.caller hDef hBbLt hWf⟩
  | false =>
    have hNe : calleeId ≠ site.callerDefId := nat_ne_of_beq_false hEq
    rw [ctx_bodies_lookup_ne ctx hNe]
    cases hGet : Trusted.MirSemantics.getElem? pSrc.bodies calleeId with
    | none => rfl
    | some cb =>
      refine ⟨cb, rfl, ?_⟩
      cases hInit : initCalleeFrameUnw calleeId cb av with
      | error k => rfl
      | ok cf₁ =>
        let ⟨_, hDef, _, _⟩ := initCalleeFrameUnw_wf hGet hInit
        have hDefNe : cf₁.defId ≠ site.callerDefId := by rw [hDef]; exact hNe
        exact ⟨cf₁, rfl, InlNormalFrameRel.other hDefNe⟩

/-! ### Part 4: Unwind-Exit Block, Inductive `dispatchUnwindStack`, & `returnToCallerUnw` -/

private theorem inl_mkTerminateTerm_step {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site)
    (cSlots : List LocalSlot) (stack : List CallContUnw) (mem : CallerMemory)
    (hUnw : ctx.callerUnwind = .terminate) :
    evalStepUnw pTgt 0
      { active := { defId := site.callerDefId, blockIdx := ctx.unwindExitBb,
                    stmtIdx := ctx.unwindExitBlock.statements.length,
                    locals := cSlots ++ replicateDead ctx.callee.locals.length },
        callStack := stack, callerMem := mem } =
      .done (.aborted mem) := by
  unfold evalStepUnw
  rw [ctx_bodies_lookup_eq ctx]; dsimp
  rw [ctx_caller'_bb_lookup_unwindExit ctx]; dsimp
  rw [getElem?_none_of_ge (Nat.le_refl _)]; dsimp
  rw [nat_beq_refl]; dsimp
  unfold evalTerminatorUnw
  dsimp [InlineUnwCtx.unwindExitBlock]
  rw [hUnw]
  rfl

private theorem inl_exit_unwindExitBlock {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site)
    {cCont : CallContUnw} {eSlots : List LocalSlot}
    {rest₁ rest₂ : List CallContUnw} {mem : CallerMemory}
    (hCDef : cCont.callerFrame.defId = site.callerDefId)
    (hCWf : FrameWf pSrc cCont.callerFrame)
    (hCUnw : cCont.unwind = ctx.callerUnwind)
    (hLenE : eSlots.length = ctx.callee.locals.length)
    (hRest : InlStackRel ctx rest₁ rest₂)
    (hRec : ∀ (s₂ : UnwindState),
      evalStepUnw pTgt 0 s₂ = dispatchUnwindStack pTgt mem rest₂ →
      SimOutcome ctx s₂ (dispatchUnwindStack pSrc mem rest₁))
    {s₂ : UnwindState}
    (hStep0 : evalStepUnw pTgt 0 s₂ = .step {
      active := { defId := site.callerDefId, blockIdx := ctx.unwindExitBb,
                  stmtIdx := 0, locals := cCont.callerFrame.locals ++ eSlots },
      callStack := rest₂, callerMem := mem }) :
    SimOutcome ctx s₂ (dispatchUnwindStack pSrc mem (cCont :: rest₁)) := by
  have hCFBod : Trusted.MirSemantics.getElem? pSrc.bodies cCont.callerFrame.defId = some ctx.caller := by
    rw [hCDef]; exact ctx.hCaller
  let ⟨hLenC, _, _⟩ := hCWf ctx.caller hCFBod
  have hDeads := run_deads_unwindExit ctx cCont.callerFrame.locals eSlots hLenC hLenE rest₂ mem
  let sEnd : UnwindState := {
    active := { defId := site.callerDefId, blockIdx := ctx.unwindExitBb,
                stmtIdx := ctx.unwindExitBlock.statements.length,
                locals := cCont.callerFrame.locals ++ replicateDead ctx.callee.locals.length },
    callStack := rest₂, callerMem := mem
  }
  apply simOutcome_prepend_step hStep0
  apply simOutcome_prepend_reaches hDeads
  dsimp [dispatchUnwindStack]
  rw [hCUnw]
  cases hU : ctx.callerUnwind with
  | cleanup pBb =>
    let ⟨pData, hPData, hPClean⟩ := ctx.hUnwindOk pBb hU
    have hPBbLt : pBb < ctx.bbOff := getElem?_some_lt hPData
    dsimp [enterCleanupBlockUnw]
    rw [hCFBod]; dsimp; rw [hPData]; dsimp; rw [hPClean]; dsimp
    have hGoto : evalStepUnw pTgt 0 sEnd = .step {
        active := { defId := site.callerDefId, blockIdx := pBb, stmtIdx := 0,
                    locals := cCont.callerFrame.locals ++ replicateDead ctx.callee.locals.length },
        callStack := rest₂, callerMem := mem } := by
      unfold evalStepUnw
      rw [ctx_bodies_lookup_eq ctx]; dsimp
      rw [ctx_caller'_bb_lookup_unwindExit ctx]; dsimp
      rw [getElem?_none_of_ge (Nat.le_refl _)]; dsimp
      rw [nat_beq_refl]; dsimp
      unfold evalTerminatorUnw
      dsimp [InlineUnwCtx.unwindExitBlock]
      rw [hU]; rfl
    apply simOutcome_step_one hGoto
    have hEqF : { defId := site.callerDefId, blockIdx := pBb, stmtIdx := 0,
                  locals := cCont.callerFrame.locals ++ replicateDead ctx.callee.locals.length } =
        { ({ cCont.callerFrame with blockIdx := pBb, stmtIdx := 0 }) with
          locals := ({ cCont.callerFrame with blockIdx := pBb, stmtIdx := 0 }).locals ++
            replicateDead ctx.callee.locals.length } := by
      dsimp; rw [hCDef]
    rw [hEqF]
    exact InlStateRel.unfused
      (InlNormalFrameRel.caller hCDef hPBbLt (frameWf_same_locals_block hCWf))
      hRest
  | unreachable =>
    apply simOutcome_fault_zero
    unfold evalStepUnw
    rw [ctx_bodies_lookup_eq ctx]; dsimp
    rw [ctx_caller'_bb_lookup_unwindExit ctx]; dsimp
    rw [getElem?_none_of_ge (Nat.le_refl _)]; dsimp
    rw [nat_beq_refl]; dsimp
    unfold evalTerminatorUnw
    dsimp [InlineUnwCtx.unwindExitBlock]
    rw [hU]; rfl
  | terminate =>
    exact simOutcome_done_zero (inl_mkTerminateTerm_step ctx cCont.callerFrame.locals rest₂ mem hU)
  | continue_ =>
    apply hRec sEnd
    unfold evalStepUnw
    rw [ctx_bodies_lookup_eq ctx]; dsimp
    rw [ctx_caller'_bb_lookup_unwindExit ctx]; dsimp
    rw [getElem?_none_of_ge (Nat.le_refl _)]; dsimp
    rw [nat_beq_refl]; dsimp
    unfold evalTerminatorUnw
    dsimp [InlineUnwCtx.unwindExitBlock]
    rw [hU]; rfl

private theorem inl_enterCleanupBlock_normal {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site)
    {f₁ f₂ : FrameState} {rest₁ rest₂ : List CallContUnw} {mem : CallerMemory}
    {pBb : BasicBlockId}
    (hFr : InlNormalFrameRel ctx f₁ f₂)
    (hPBbLt : f₁.defId = site.callerDefId → pBb < ctx.bbOff)
    (hRest : InlStackRel ctx rest₁ rest₂)
    {s₂ : UnwindState}
    (hEv : evalStepUnw pTgt 0 s₂ = enterCleanupBlockUnw pTgt f₂ rest₂ mem pBb) :
    SimOutcome ctx s₂ (enterCleanupBlockUnw pSrc f₁ rest₁ mem pBb) := by
  cases hFr with
  | other hNe =>
    unfold enterCleanupBlockUnw
    unfold enterCleanupBlockUnw at hEv
    rw [ctx_bodies_lookup_ne ctx hNe] at hEv
    cases hBod : Trusted.MirSemantics.getElem? pSrc.bodies f₁.defId with
    | none => dsimp; rw [hBod] at hEv; exact simOutcome_fault_zero hEv
    | some body =>
      dsimp; rw [hBod] at hEv; dsimp at hEv
      cases hBb : Trusted.MirSemantics.getElem? body.basicBlocks pBb with
      | none => dsimp; rw [hBb] at hEv; exact simOutcome_fault_zero hEv
      | some bb =>
        dsimp; rw [hBb] at hEv; dsimp at hEv
        cases hCl : bb.cleanup with
        | false => dsimp; rw [hCl] at hEv; exact simOutcome_fault_zero hEv
        | true =>
          dsimp; rw [hCl] at hEv; dsimp at hEv
          exact simOutcome_step_one hEv
            (InlStateRel.unfused (InlNormalFrameRel.other hNe) hRest)
  | caller hDef _ hWf =>
    have hLt := hPBbLt hDef
    unfold enterCleanupBlockUnw
    unfold enterCleanupBlockUnw at hEv
    rw [hDef] at hEv
    rw [ctx_bodies_lookup_eq ctx] at hEv; dsimp at hEv
    have hCFBod : Trusted.MirSemantics.getElem? pSrc.bodies f₁.defId = some ctx.caller := by
      rw [hDef]; exact ctx.hCaller
    rw [hCFBod]; dsimp
    cases hEqCall : Nat.beq pBb site.callBlock with
    | true =>
      have hp : pBb = site.callBlock := nat_beq_eq hEqCall
      subst hp
      rw [ctx.hCallBb]; dsimp; rw [ctx.hNotClean]; dsimp
      rw [ctx_caller'_bb_lookup_call ctx] at hEv; dsimp at hEv
      exact simOutcome_fault_zero hEv
    | false =>
      have hNeCall : pBb ≠ site.callBlock := nat_ne_of_beq_false hEqCall
      rw [ctx_caller'_bb_lookup_ne ctx hLt hNeCall] at hEv
      cases hBb : Trusted.MirSemantics.getElem? ctx.caller.basicBlocks pBb with
      | none => dsimp; rw [hBb] at hEv; exact simOutcome_fault_zero hEv
      | some bb =>
        dsimp; rw [hBb] at hEv; dsimp at hEv
        cases hCl : bb.cleanup with
        | false => dsimp; rw [hCl] at hEv; exact simOutcome_fault_zero hEv
        | true =>
          dsimp; rw [hCl] at hEv; dsimp at hEv
          rw [← hDef] at hEv
          exact simOutcome_step_one hEv
            (InlStateRel.unfused
              (InlNormalFrameRel.caller (f := { f₁ with blockIdx := pBb, stmtIdx := 0 })
                hDef hLt (frameWf_same_locals_block hWf))
              hRest)

private theorem inl_dispatchUnwindStack {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) {stack₁ stack₂ : List CallContUnw}
    (hStack : InlStackRel ctx stack₁ stack₂) (mem : CallerMemory) :
    ∀ (s₂ : UnwindState),
      evalStepUnw pTgt 0 s₂ = dispatchUnwindStack pTgt mem stack₂ →
      SimOutcome ctx s₂ (dispatchUnwindStack pSrc mem stack₁) := by
  induction hStack with
  | nil =>
    intro s₂ hEv
    dsimp [dispatchUnwindStack] at hEv
    dsimp [dispatchUnwindStack]
    exact simOutcome_done_zero hEv
  | @consSingle cont₁ cont₂ rest₁ rest₂ hFr hDst hTgt hUnw hBounds hRest ih =>
    intro s₂ hEv
    dsimp [dispatchUnwindStack] at hEv
    dsimp [dispatchUnwindStack]
    rw [hUnw] at hEv
    cases hU : cont₁.unwind with
    | continue_ =>
      dsimp; rw [hU] at hEv
      exact ih s₂ hEv
    | unreachable =>
      dsimp; rw [hU] at hEv
      exact simOutcome_fault_zero hEv
    | terminate =>
      dsimp; rw [hU] at hEv
      exact simOutcome_done_zero hEv
    | cleanup pBb =>
      dsimp; rw [hU] at hEv
      exact inl_enterCleanupBlock_normal ctx hFr
        (fun hDef => (hBounds hDef).2.2 pBb hU) hRest hEv
  | @consFused eCont cCont rest₁ rest₂ hCDef hCWf hCDst hCTgt hCUnw
      hEDef hEBbLt hEWf hEDstLt hETgtLt hEUnwOk hRest ih =>
    intro s₂ hEv
    dsimp [dispatchUnwindStack] at hEv
    dsimp [dispatchUnwindStack]
    cases hEU : eCont.unwind with
    | unreachable =>
      dsimp; rw [hEU] at hEv; dsimp [shiftCalleeUnwindAction] at hEv
      exact simOutcome_fault_zero hEv
    | terminate =>
      dsimp; rw [hEU] at hEv; dsimp [shiftCalleeUnwindAction] at hEv
      exact simOutcome_done_zero hEv
    | cleanup pBb =>
      dsimp; rw [hEU] at hEv; dsimp [shiftCalleeUnwindAction] at hEv
      rw [hEU] at hEUnwOk; dsimp [unwindActionBlocksLt] at hEUnwOk
      let ⟨hPBbBlt, hPCleanM⟩ := bool_and_true hEUnwOk
      have hPBbLt : pBb < ctx.callee.basicBlocks.length := nat_blt_lt hPBbBlt
      let ⟨pBbData, hPBbGet⟩ := getElem?_some_of_lt ctx.callee.basicBlocks pBb hPBbLt
      rw [hPBbGet] at hPCleanM; dsimp at hPCleanM
      have hEBod : Trusted.MirSemantics.getElem? pSrc.bodies eCont.callerFrame.defId =
          some ctx.callee := by
        rw [hEDef]; exact ctx.hCallee
      dsimp [enterCleanupBlockUnw]
      rw [hEBod]; dsimp; rw [hPBbGet]; dsimp; rw [hPCleanM]; dsimp
      dsimp [enterCleanupBlockUnw] at hEv
      rw [ctx_bodies_lookup_eq ctx] at hEv; dsimp at hEv
      rw [ctx_caller'_bb_lookup_callee ctx hPBbLt, hPBbGet] at hEv; dsimp [shiftCalleeBlock] at hEv
      rw [hPCleanM] at hEv; dsimp at hEv
      exact simOutcome_step_one hEv
        (InlStateRel.fused hEDef hPBbLt (frameWf_same_locals_block hEWf)
          hCDef hCWf hCDst hCTgt hCUnw hRest)
    | continue_ =>
      dsimp; rw [hEU] at hEv; dsimp [shiftCalleeUnwindAction, enterCleanupBlockUnw] at hEv
      rw [ctx_bodies_lookup_eq ctx] at hEv; dsimp at hEv
      rw [ctx_caller'_bb_lookup_unwindExit ctx] at hEv
      dsimp [InlineUnwCtx.unwindExitBlock] at hEv
      have hEBod : Trusted.MirSemantics.getElem? pSrc.bodies eCont.callerFrame.defId =
          some ctx.callee := by
        rw [hEDef]; exact ctx.hCallee
      let ⟨hLenE, _, _⟩ := hEWf ctx.callee hEBod
      exact inl_exit_unwindExitBlock ctx hCDef hCWf hCUnw hLenE hRest ih hEv

private theorem inl_returnToCaller {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) (retVal : Val)
    {stack₁ stack₂ : List CallContUnw}
    (hStack : InlStackRel ctx stack₁ stack₂)
    {cont₁ cont₂ : CallContUnw} {rest₁ rest₂ : List CallContUnw}
    (hS1 : stack₁ = cont₁ :: rest₁) (hS2 : stack₂ = cont₂ :: rest₂)
    (mem : CallerMemory) {s₂ : UnwindState}
    (hEv : evalStepUnw pTgt 0 s₂ = returnToCallerUnw pTgt retVal cont₂ rest₂ mem) :
    SimOutcome ctx s₂ (returnToCallerUnw pSrc retVal cont₁ rest₁ mem) := by
  cases hStack with
  | nil => cases hS1
  | @consSingle c1 c2 r1 r2 hFr hDst hTgt hUnw hBounds hRest =>
    injection hS1 with h1 h1r; subst h1; subst h1r
    injection hS2 with h2 h2r; subst h2; subst h2r
    cases c1 with
    | mk cf1 d1 t1 u1 =>
      cases c2 with
      | mk cf2 d2 t2 u2 =>
        dsimp at hFr hDst hTgt hUnw hBounds
        cases hFr with
        | other hNe =>
          unfold returnToCallerUnw
          unfold returnToCallerUnw at hEv
          dsimp; dsimp at hEv
          rw [ctx_bodies_lookup_ne ctx hNe, hDst, hTgt] at hEv
          cases hBod : Trusted.MirSemantics.getElem? pSrc.bodies cf1.defId with
          | none => dsimp; rw [hBod] at hEv; exact simOutcome_fault_zero hEv
          | some body =>
            dsimp; rw [hBod] at hEv; dsimp at hEv
            cases hProj : (!d1.projection.isEmpty) with
            | true => dsimp; rw [hProj] at hEv; exact simOutcome_fault_zero hEv
            | false =>
              dsimp; rw [hProj] at hEv; dsimp at hEv
              cases hTy : Trusted.MirSemantics.getElem? body.locals d1.localId with
              | none => dsimp; rw [hTy] at hEv; exact simOutcome_fault_zero hEv
              | some dstTy =>
                dsimp; rw [hTy] at hEv; dsimp at hEv
                cases hWr : writePlace cf1.locals d1.localId dstTy retVal with
                | error k => dsimp; rw [hWr] at hEv; exact simOutcome_fault_zero hEv
                | ok locs' =>
                  dsimp; rw [hWr] at hEv; dsimp at hEv
                  cases hT : t1 with
                  | none => dsimp; rw [hT] at hEv; exact simOutcome_fault_zero hEv
                  | some nextBb =>
                    dsimp; rw [hT] at hEv; dsimp at hEv
                    exact simOutcome_step_one hEv
                      (InlStateRel.unfused (InlNormalFrameRel.other hNe) hRest)
        | caller hDef _ hWf =>
          let ⟨hDstLt, hTgtLt, _⟩ := hBounds hDef
          have hCBod : Trusted.MirSemantics.getElem? pSrc.bodies cf1.defId =
              some ctx.caller := by
            rw [hDef]; exact ctx.hCaller
          let ⟨hLenC, hWtC, _⟩ := hWf ctx.caller hCBod
          have hDstLtS : d1.localId < cf1.locals.length := by
            rw [hLenC]; exact hDstLt
          unfold returnToCallerUnw
          unfold returnToCallerUnw at hEv
          dsimp; dsimp at hEv
          rw [hCBod]; dsimp
          rw [hDef, hDst, hTgt] at hEv
          rw [ctx_bodies_lookup_eq ctx] at hEv; dsimp at hEv
          cases hProj : (!d1.projection.isEmpty) with
          | true => dsimp; rw [hProj] at hEv; exact simOutcome_fault_zero hEv
          | false =>
            dsimp; rw [hProj] at hEv; dsimp at hEv
            dsimp [InlineUnwCtx.caller'] at hEv
            rw [getElem?_append_left hDstLt] at hEv
            cases hTy : Trusted.MirSemantics.getElem? ctx.caller.locals d1.localId with
            | none => dsimp; rw [hTy] at hEv; exact simOutcome_fault_zero hEv
            | some dstTy =>
              dsimp; rw [hTy] at hEv; dsimp at hEv
              rw [writePlace_prefix hDstLtS] at hEv
              cases hWr : writePlace cf1.locals d1.localId dstTy retVal with
              | error k => dsimp; rw [hWr] at hEv; exact simOutcome_fault_zero hEv
              | ok locs' =>
                dsimp; rw [hWr] at hEv; dsimp at hEv
                let ⟨hL', hW'⟩ := writePlace_wf hLenC hWtC hTy hWr
                cases hT : t1 with
                | none => dsimp; rw [hT] at hEv; exact simOutcome_fault_zero hEv
                | some nextBb =>
                  dsimp; rw [hT] at hEv; dsimp at hEv
                  rw [← hDef] at hEv
                  have hNextLt := hTgtLt nextBb hT
                  exact simOutcome_step_one hEv
                    (InlStateRel.unfused
                      (InlNormalFrameRel.caller
                        (f := { cf1 with blockIdx := nextBb, stmtIdx := 0, locals := locs' })
                        hDef hNextLt (frameWf_update_locals_reset hCBod hL' hW'))
                      hRest)
  | @consFused eCont cCont rest₁' rest₂' hCDef hCWf hCDst hCTgt hCUnw
      hEDef hEBbLt hEWf hEDstLt hETgtLt hEUnwOk hRest =>
    injection hS1 with h1 h1r; subst h1; subst h1r
    injection hS2 with h2 h2r; subst h2; subst h2r
    have hCBod : Trusted.MirSemantics.getElem? pSrc.bodies cCont.callerFrame.defId =
        some ctx.caller := by
      rw [hCDef]; exact ctx.hCaller
    have hEBod : Trusted.MirSemantics.getElem? pSrc.bodies eCont.callerFrame.defId =
        some ctx.callee := by
      rw [hEDef]; exact ctx.hCallee
    let ⟨hLenC, _, _⟩ := hCWf ctx.caller hCBod
    let ⟨hLenE, hWtE, _⟩ := hEWf ctx.callee hEBod
    unfold returnToCallerUnw
    unfold returnToCallerUnw at hEv
    rw [hEBod]; dsimp
    rw [ctx_bodies_lookup_eq ctx] at hEv; dsimp at hEv
    have hShiftProj : (shiftPlaceUnw ctx.locOff eCont.dst).projection = eCont.dst.projection := rfl
    rw [hShiftProj] at hEv
    cases hProj : (!eCont.dst.projection.isEmpty) with
    | true => dsimp; rw [hProj] at hEv; exact simOutcome_fault_zero hEv
    | false =>
      dsimp; rw [hProj] at hEv; dsimp at hEv
      dsimp [shiftPlaceUnw, InlineUnwCtx.caller', InlineUnwCtx.locOff] at hEv
      rw [getElem?_append_right_comm ctx.caller.locals ctx.callee.locals eCont.dst.localId] at hEv
      cases hTy : Trusted.MirSemantics.getElem? ctx.callee.locals eCont.dst.localId with
      | none => dsimp; rw [hTy] at hEv; exact simOutcome_fault_zero hEv
      | some dstTy =>
        dsimp; rw [hTy] at hEv; dsimp at hEv
        rw [← hLenC, writePlace_suffix] at hEv
        cases hWr : writePlace eCont.callerFrame.locals eCont.dst.localId dstTy retVal with
        | error k => dsimp; rw [hWr] at hEv; exact simOutcome_fault_zero hEv
        | ok eLocs' =>
          dsimp; rw [hWr] at hEv; dsimp at hEv
          let ⟨hLE', hWE'⟩ := writePlace_wf hLenE hWtE hTy hWr
          cases hT : eCont.target with
          | none => dsimp; rw [hT] at hEv; exact simOutcome_fault_zero hEv
          | some nextBb =>
            dsimp; rw [hT] at hEv; dsimp at hEv
            have hNextLt := hETgtLt nextBb hT
            exact simOutcome_step_one hEv
              (InlStateRel.fused hEDef hNextLt
                (frameWf_update_locals_reset hEBod hLE' hWE')
                hCDef hCWf hCDst hCTgt hCUnw hRest)

/-! ### Part 5: Main Forward Stuttering Step Simulation (`inl_step_fwd`) -/

private theorem inl_step_unfused_other {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site)
    {f : FrameState} {stack₁ stack₂ : List CallContUnw} {mem : CallerMemory}
    (hNe : f.defId ≠ site.callerDefId)
    (hStack : InlStackRel ctx stack₁ stack₂) :
    SimOutcome ctx
      { active := f, callStack := stack₂, callerMem := mem }
      (evalStepUnw pSrc 0 { active := f, callStack := stack₁, callerMem := mem }) := by
  let s₂ : UnwindState := { active := f, callStack := stack₂, callerMem := mem }
  have hEv0 : evalStepUnw pTgt 0 s₂ =
      match Trusted.MirSemantics.getElem? pSrc.bodies f.defId with
      | none => .fault .unsupported
      | some body =>
        match Trusted.MirSemantics.getElem? body.basicBlocks f.blockIdx with
        | none => .fault .unsupported
        | some bb =>
          match Trusted.MirSemantics.getElem? bb.statements f.stmtIdx with
          | some stmt =>
            match evalStatement body f mem stmt with
            | .fault k => .fault k
            | .done out => .done (embedTerminalOut out)
            | .step st' =>
              match st'.frames with
              | [f'] => .step { active := f', callStack := stack₂, callerMem := st'.callerMem }
              | _ => .fault .unsupported
          | none =>
            if Nat.beq f.stmtIdx bb.statements.length then
              evalTerminatorUnw pTgt body bb f stack₂ mem
            else
              .fault .unsupported := by
    unfold evalStepUnw
    dsimp [s₂]
    rw [ctx_bodies_lookup_ne ctx hNe]
  unfold evalStepUnw
  cases hBod : Trusted.MirSemantics.getElem? pSrc.bodies f.defId with
  | none =>
    dsimp; rw [hBod] at hEv0
    exact simOutcome_fault_zero hEv0
  | some body =>
    dsimp; rw [hBod] at hEv0; dsimp at hEv0
    cases hBb : Trusted.MirSemantics.getElem? body.basicBlocks f.blockIdx with
    | none =>
      dsimp; rw [hBb] at hEv0
      exact simOutcome_fault_zero hEv0
    | some bb =>
      dsimp; rw [hBb] at hEv0; dsimp at hEv0
      cases hSt : Trusted.MirSemantics.getElem? bb.statements f.stmtIdx with
      | some stmt =>
        dsimp; rw [hSt] at hEv0; dsimp at hEv0
        cases hEval : evalStatement body f mem stmt with
        | fault k => dsimp; rw [hEval] at hEv0; dsimp at hEv0; exact simOutcome_fault_zero hEv0
        | done out => dsimp; rw [hEval] at hEv0; dsimp at hEv0; exact simOutcome_done_zero hEv0
        | step st' =>
          dsimp; rw [hEval] at hEv0; dsimp at hEv0
          cases hFrs : st'.frames with
          | nil => dsimp; rw [hFrs] at hEv0; dsimp at hEv0; exact simOutcome_fault_zero hEv0
          | cons f' restF =>
            cases restF with
            | cons _ _ => dsimp; rw [hFrs] at hEv0; dsimp at hEv0; exact simOutcome_fault_zero hEv0
            | nil =>
              dsimp; rw [hFrs] at hEv0; dsimp at hEv0
              have hF'Def : f'.defId = f.defId := by
                cases stmt with
                | nop =>
                  dsimp [evalStatement] at hEval
                  injection hEval with h1; rw [← h1] at hFrs
                  dsimp at hFrs; injection hFrs with h2; subst h2; rfl
                | unsupported => cases hEval
                | storageLive id =>
                  dsimp [evalStatement] at hEval
                  cases ht : Trusted.MirSemantics.getElem? body.locals id with
                  | none => rw [ht] at hEval; cases hEval
                  | some ty =>
                    rw [ht] at hEval; dsimp at hEval
                    cases hs : setElem? f.locals id (liveUninitSlot ty) with
                    | none => rw [hs] at hEval; cases hEval
                    | some _ =>
                      rw [hs] at hEval; injection hEval with h1; rw [← h1] at hFrs
                      dsimp at hFrs; injection hFrs with h2; subst h2; rfl
                | storageDead id =>
                  dsimp [evalStatement] at hEval
                  cases hb : Nat.beq id 0 <;> rw [hb] at hEval
                  · dsimp at hEval
                    cases hs : setElem? f.locals id .dead with
                    | none => rw [hs] at hEval; cases hEval
                    | some _ =>
                      rw [hs] at hEval; injection hEval with h1; rw [← h1] at hFrs
                      dsimp at hFrs; injection hFrs with h2; subst h2; rfl
                  · cases hEval
                | assign dst rv =>
                  dsimp [evalStatement] at hEval
                  cases hp : (!dst.projection.isEmpty) <;> rw [hp] at hEval
                  · dsimp at hEval
                    cases ht : Trusted.MirSemantics.getElem? body.locals dst.localId with
                    | none => rw [ht] at hEval; cases hEval
                    | some dstTy =>
                      rw [ht] at hEval; dsimp at hEval
                      cases hr : evalRvalue body.locals f.locals dstTy rv with
                      | error _ => rw [hr] at hEval; cases hEval
                      | ok pr =>
                        rw [hr] at hEval; dsimp at hEval
                        cases hw : writePlace pr.2 dst.localId dstTy pr.1 with
                        | error _ => rw [hw] at hEval; cases hEval
                        | ok _ =>
                          rw [hw] at hEval; injection hEval with h1; rw [← h1] at hFrs
                          dsimp at hFrs; injection hFrs with h2; subst h2; rfl
                  · cases hEval
              have hF'Ne : f'.defId ≠ site.callerDefId := by rw [hF'Def]; exact hNe
              exact simOutcome_step_one hEv0
                (InlStateRel.unfused (InlNormalFrameRel.other hF'Ne) hStack)
      | none =>
        dsimp; rw [hSt] at hEv0; dsimp at hEv0
        cases hEqLen : Nat.beq f.stmtIdx bb.statements.length with
        | false => dsimp; rw [hEqLen] at hEv0; dsimp at hEv0; exact simOutcome_fault_zero hEv0
        | true =>
          dsimp; rw [hEqLen] at hEv0; dsimp at hEv0
          unfold evalTerminatorUnw
          unfold evalTerminatorUnw at hEv0
          cases hTm : bb.terminator with
          | goto t =>
            dsimp; rw [hTm] at hEv0; dsimp at hEv0
            exact simOutcome_step_one hEv0
              (InlStateRel.unfused (InlNormalFrameRel.other hNe) hStack)
          | unreachable =>
            dsimp; rw [hTm] at hEv0; exact simOutcome_fault_zero hEv0
          | unsupported =>
            dsimp; rw [hTm] at hEv0; exact simOutcome_fault_zero hEv0
          | return_ =>
            dsimp; rw [hTm] at hEv0; dsimp at hEv0
            cases hCl : bb.cleanup with
            | true => dsimp; rw [hCl] at hEv0; dsimp at hEv0; exact simOutcome_fault_zero hEv0
            | false =>
              dsimp; rw [hCl] at hEv0; dsimp at hEv0
              cases hRet : Trusted.MirSemantics.getElem? f.locals 0 with
              | none => dsimp; rw [hRet] at hEv0; dsimp at hEv0; exact simOutcome_fault_zero hEv0
              | some sl =>
                rw [hRet] at hEv0
                cases sl with
                | dead => exact simOutcome_fault_zero hEv0
                | live ov =>
                  cases ov with
                  | none => exact simOutcome_fault_zero hEv0
                  | some retVal =>
                    cases hStack with
                    | nil => exact simOutcome_done_zero hEv0
                    | @consSingle c1 c2 r1 r2 hF hD hT hU hB hR =>
                      exact inl_returnToCaller ctx retVal
                        (InlStackRel.consSingle hF hD hT hU hB hR) rfl rfl mem hEv0
                    | @consFused eC cC r1 r2 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 =>
                      exact inl_returnToCaller ctx retVal
                        (InlStackRel.consFused h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12) rfl rfl mem hEv0
          | switchInt discr ts =>
            dsimp; rw [hTm] at hEv0; dsimp at hEv0
            cases hOp : evalPrimitiveOperand body.locals f.locals discr with
            | error k => dsimp; rw [hOp] at hEv0; dsimp at hEv0; exact simOutcome_fault_zero hEv0
            | ok pr =>
              dsimp; rw [hOp] at hEv0; dsimp at hEv0
              cases hv : pr.1 with
              | scalar sv =>
                dsimp; rw [hv] at hEv0; dsimp at hEv0
                cases hTr : evalSwitchBranches sv.width sv.bits ts.otherwise ts.branches with
                | error k => dsimp; rw [hTr] at hEv0; dsimp at hEv0; exact simOutcome_fault_zero hEv0
                | ok tgt =>
                  dsimp; rw [hTr] at hEv0; dsimp at hEv0
                  exact simOutcome_step_one hEv0
                    (InlStateRel.unfused (InlNormalFrameRel.other hNe) hStack)
              | bool b =>
                dsimp; rw [hv] at hEv0; dsimp at hEv0
                cases hTr : evalBoolSwitchBranches b ts.otherwise ts.branches with
                | error k => dsimp; rw [hTr] at hEv0; dsimp at hEv0; exact simOutcome_fault_zero hEv0
                | ok tgt =>
                  dsimp; rw [hTr] at hEv0; dsimp at hEv0
                  exact simOutcome_step_one hEv0
                    (InlStateRel.unfused (InlNormalFrameRel.other hNe) hStack)
              | unit | ptr _ | enumVal _ _ | tuple _ | bytes _ =>
                dsimp; rw [hv] at hEv0; dsimp at hEv0; exact simOutcome_fault_zero hEv0
          | unwindResume =>
            dsimp; rw [hTm] at hEv0; dsimp at hEv0
            cases hCl : bb.cleanup with
            | false => dsimp; rw [hCl] at hEv0; dsimp at hEv0; exact simOutcome_fault_zero hEv0
            | true =>
              dsimp; rw [hCl] at hEv0; dsimp at hEv0
              exact inl_dispatchUnwindStack ctx hStack mem s₂ hEv0
          | assert cond exp msg t u =>
            dsimp; rw [hTm] at hEv0; dsimp at hEv0
            cases hOp : evalPrimitiveOperand body.locals f.locals cond with
            | error k => dsimp; rw [hOp] at hEv0; dsimp at hEv0; exact simOutcome_fault_zero hEv0
            | ok pr =>
              cases pr with
              | mk pv pl =>
                rw [hOp] at hEv0
                cases pv with
                | scalar _ | unit | ptr _ | enumVal _ _ | tuple _ | bytes _ =>
                  exact simOutcome_fault_zero hEv0
                | bool b =>
                  dsimp; dsimp at hEv0
                  cases hb : boolEq b exp with
                  | true =>
                    dsimp; rw [hb] at hEv0; dsimp at hEv0
                    exact simOutcome_step_one hEv0
                      (InlStateRel.unfused (InlNormalFrameRel.other hNe) hStack)
                  | false =>
                    dsimp; rw [hb] at hEv0; dsimp at hEv0
                    dsimp [dispatchLocalUnwind]
                    dsimp [dispatchLocalUnwind] at hEv0
                    cases u with
                    | unreachable => exact simOutcome_fault_zero hEv0
                    | terminate => exact simOutcome_done_zero hEv0
                    | continue_ => exact inl_dispatchUnwindStack ctx hStack mem s₂ hEv0
                    | cleanup pBb =>
                      exact inl_enterCleanupBlock_normal ctx
                        (InlNormalFrameRel.other (f := { f with locals := pl }) hNe)
                        (fun hDef => False.elim (hNe hDef)) hStack hEv0
          | call calleeId args dst tgt u =>
            dsimp; rw [hTm] at hEv0; dsimp at hEv0
            cases hArgs : evalCallArgsUnw body.locals f.locals args with
            | error k => dsimp; rw [hArgs] at hEv0; dsimp at hEv0; exact simOutcome_fault_zero hEv0
            | ok pr =>
              dsimp; rw [hArgs] at hEv0; dsimp at hEv0
              have hCall := inl_initCalleeFrame_any ctx calleeId pr.1
              cases hCb : Trusted.MirSemantics.getElem? pSrc.bodies calleeId with
              | none =>
                dsimp; rw [hCb] at hCall; rw [hCall] at hEv0
                exact simOutcome_fault_zero hEv0
              | some cb₁ =>
                dsimp; rw [hCb] at hCall
                let ⟨cb₂, hCb₂, hInit⟩ := hCall
                rw [hCb₂] at hEv0; dsimp at hEv0
                cases hI1 : initCalleeFrameUnw calleeId cb₁ pr.1 with
                | error k =>
                  dsimp; rw [hI1] at hInit; rw [hInit] at hEv0
                  exact simOutcome_fault_zero hEv0
                | ok cf₁ =>
                  dsimp; rw [hI1] at hInit
                  let ⟨cf₂, hI2, hCfRel⟩ := hInit
                  rw [hI2] at hEv0; dsimp at hEv0
                  exact simOutcome_step_one hEv0
                    (InlStateRel.unfused hCfRel
                      (InlStackRel.consSingle
                        (InlNormalFrameRel.other (f := { f with locals := pr.2 }) hNe)
                        rfl rfl rfl (fun hDef => False.elim (hNe hDef)) hStack))

private theorem inl_step_unfused_caller {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site)
    {f : FrameState} {stack₁ stack₂ : List CallContUnw} {mem : CallerMemory}
    (hDef : f.defId = site.callerDefId)
    (hBbLt : f.blockIdx < ctx.bbOff)
    (hWf : FrameWf pSrc f)
    (hStack : InlStackRel ctx stack₁ stack₂) :
    SimOutcome ctx
      { active := { f with locals := f.locals ++ replicateDead ctx.callee.locals.length },
        callStack := stack₂, callerMem := mem }
      (evalStepUnw pSrc 0 { active := f, callStack := stack₁, callerMem := mem }) := by
  have hCBod : Trusted.MirSemantics.getElem? pSrc.bodies f.defId = some ctx.caller := by
    rw [hDef]; exact ctx.hCaller
  let ⟨hLenC, hWtC, hStmtLe⟩ := hWf ctx.caller hCBod
  let ⟨bb, hBb⟩ := getElem?_some_of_lt ctx.caller.basicBlocks f.blockIdx hBbLt
  have hBbAd := list_all_getElem? (ctx_caller_bbs_all ctx) hBb
  let ⟨hStmtsLt, hTermBounds⟩ := bool_and_true hBbAd
  let s₂ : UnwindState := {
    active := { f with locals := f.locals ++ replicateDead ctx.callee.locals.length },
    callStack := stack₂, callerMem := mem
  }
  have hLe : f.stmtIdx ≤ bb.statements.length := hStmtLe bb hBb
  -- Split between executing an in-bounds statement of `bb` vs executing `bb.terminator`
  cases hSt : Trusted.MirSemantics.getElem? bb.statements f.stmtIdx with
  | some stmt =>
    have hStmtLt : f.stmtIdx < bb.statements.length := getElem?_some_lt hSt
    have hSLt : callerStmtLocalsLt ctx.locOff stmt = true := list_all_getElem? hStmtsLt hSt
    have hStTgt : ∃ bb₂ : BasicBlock,
        Trusted.MirSemantics.getElem? ctx.caller'.basicBlocks f.blockIdx = some bb₂ ∧
        Trusted.MirSemantics.getElem? bb₂.statements f.stmtIdx = some stmt := by
      cases hEqC : Nat.beq f.blockIdx site.callBlock with
      | true =>
        have hEqB : f.blockIdx = site.callBlock := nat_beq_eq hEqC
        rw [hEqB, ctx.hCallBb] at hBb; injection hBb with hBeq; subst hBeq
        refine ⟨ctx.callBb', ?_, ?_⟩
        · rw [hEqB]; exact ctx_caller'_bb_lookup_call ctx
        dsimp [InlineUnwCtx.callBb']
        have hLt1 : f.stmtIdx < (ctx.callBb.statements ++ ctx.entryLives).length := by
          rw [list_length_append]
          exact Nat.lt_of_lt_of_le hStmtLt (Nat.le_add_right _ _)
        rw [getElem?_append_left hLt1, getElem?_append_left hStmtLt]
        exact hSt
      | false =>
        have hNeC : f.blockIdx ≠ site.callBlock := nat_ne_of_beq_false hEqC
        refine ⟨bb, ?_, hSt⟩
        rw [ctx_caller'_bb_lookup_ne ctx hBbLt hNeC]; exact hBb
    let ⟨bb₂, hBb₂, hSt₂⟩ := hStTgt
    have hEv2 : evalStepUnw pTgt 0 s₂ =
        match evalStatement ctx.caller' { f with locals := f.locals ++ replicateDead ctx.callee.locals.length } mem stmt with
        | .fault k => .fault k
        | .done out => .done (embedTerminalOut out)
        | .step st' =>
          match st'.frames with
          | [f'] => .step { active := f', callStack := stack₂, callerMem := st'.callerMem }
          | _ => .fault .unsupported := by
      unfold evalStepUnw
      dsimp [s₂]; rw [hDef, ctx_bodies_lookup_eq ctx]; dsimp
      rw [hBb₂]; dsimp; rw [hSt₂]
    rw [evalStatement_prefix (rfl : ctx.caller'.locals = ctx.caller.locals ++ ctx.callee.locals)
          hLenC hSLt] at hEv2
    unfold evalStepUnw
    rw [hCBod]; dsimp; rw [hBb]; dsimp; rw [hSt]; dsimp
    cases hEv1 : evalStatement ctx.caller f mem stmt with
    | fault k => dsimp; rw [hEv1] at hEv2; dsimp at hEv2; exact simOutcome_fault_zero hEv2
    | done out => dsimp; rw [hEv1] at hEv2; dsimp at hEv2; exact simOutcome_done_zero hEv2
    | step st' =>
      dsimp; rw [hEv1] at hEv2; dsimp at hEv2
      cases hFrs : st'.frames with
      | nil => dsimp; rw [hFrs] at hEv2; dsimp at hEv2; exact simOutcome_fault_zero hEv2
      | cons f' restF =>
        cases restF with
        | cons _ _ => dsimp; rw [hFrs] at hEv2; dsimp at hEv2; exact simOutcome_fault_zero hEv2
        | nil =>
          dsimp; rw [hFrs] at hEv2; dsimp at hEv2
          have hEv1' : evalStatement ctx.caller f mem stmt = .step ⟨[f'], st'.callerMem⟩ := by
            rw [hEv1]; cases st' with | mk frs cm => dsimp at hFrs; subst hFrs; rfl
          let ⟨hWf', hDef', hBb', _⟩ := evalStatement_wf hCBod hBb hSt hWf hEv1'
          have hDef1 : f'.defId = site.callerDefId := hDef'.trans hDef
          have hBb1 : f'.blockIdx < ctx.bbOff := by rw [hBb']; exact hBbLt
          exact simOutcome_step_one hEv2
            (InlStateRel.unfused (InlNormalFrameRel.caller hDef1 hBb1 hWf') hStack)
  | none =>
    have hGe : bb.statements.length ≤ f.stmtIdx := getElem?_none_ge hSt
    have hEqIdx : f.stmtIdx = bb.statements.length := Nat.le_antisymm hLe hGe
    have hEqLenB : Nat.beq f.stmtIdx bb.statements.length = true := by
      rw [hEqIdx]; exact nat_beq_refl _
    unfold evalStepUnw
    rw [hCBod]; dsimp; rw [hBb]; dsimp; rw [hSt]; dsimp
    rw [hEqLenB]; dsimp
    -- Now split on whether `f.blockIdx = site.callBlock` (the inlined site!) or not
    cases hEqC : Nat.beq f.blockIdx site.callBlock with
    | true =>
      -- THE INLINED CALL SITE!
      have hEqB : f.blockIdx = site.callBlock := nat_beq_eq hEqC
      rw [hEqB, ctx.hCallBb] at hBb
      injection hBb with hBbEq; subst hBbEq
      unfold evalTerminatorUnw
      rw [ctx.hTerm]; dsimp
      have hS2Eq : s₂ = {
          active := { defId := site.callerDefId, blockIdx := site.callBlock,
                      stmtIdx := ctx.callBb.statements.length,
                      locals := f.locals ++ replicateDead ctx.callee.locals.length },
          callStack := stack₂, callerMem := mem } := by
        dsimp [s₂]
        cases f with
        | mk d b st l =>
          dsimp at hDef hEqB hEqIdx; subst hDef; subst hEqB; subst hEqIdx; rfl
      change SimOutcome ctx s₂ _
      rw [hS2Eq]
      have hEntry := run_entryLives ctx f.locals hLenC stack₂ mem
      have hArgRun := run_argBinds ctx f.locals hLenC hWtC stack₂ mem
      cases hArgs : evalCallArgsUnw ctx.caller.locals f.locals ctx.args with
      | error fk =>
        rw [hArgs] at hArgRun
        let ⟨s', hRs', ⟨c, hc, hEvF⟩⟩ := hArgRun
        cases hc
        let ⟨m, hm⟩ := hEntry
        exact ⟨s', reachesUnw_trans (reachesNUnw_to_reachesUnw hm) hRs', hEvF⟩
      | ok pr =>
        rw [hArgs] at hArgRun; dsimp at hArgRun
        rw [ctx.hCallee]; dsimp
        let ⟨hLA, hWA⟩ := evalCallArgsUnw_wf hLenC hWtC hArgs
        have hMatch : checkArgsMatch pr.1 ((ctx.callee.locals.drop 1).take ctx.callee.argumentCount) = true :=
          callArgsTyMatch_checkArgsMatch ctx.hArgsMatch hLenC hWtC hArgs
        have hInitCallee : initCalleeFrameUnw site.calleeDefId ctx.callee pr.1 =
            .ok { defId := site.calleeDefId, blockIdx := 0, stmtIdx := 0,
                  locals := initLocalsLoop ctx.callee pr.1 0 ctx.callee.locals } := by
          unfold initCalleeFrameUnw
          rw [ctx_callee_nonEmpty ctx, nat_lt_blt (ctx_callee_argLt ctx),
              ctx_callee_storageInBounds ctx, ctx_callee_locals_supported ctx]
          dsimp
          rw [hMatch]; rfl
        rw [hInitCallee]; dsimp
        let ⟨hWfE, _, _, _⟩ := initCalleeFrameUnw_wf ctx.hCallee hInitCallee
        have hCallBb'Len : ctx.callBb'.statements.length =
            ctx.callBb.statements.length + ctx.entryLives.length + ctx.args.length := by
          dsimp [InlineUnwCtx.callBb', InlineUnwCtx.argBinds]
          rw [list_length_append, list_length_append]
          have hArgBindsLen : ∀ (idx : Nat) (ops : List Operand),
              (mkArgBindStmts ctx.locOff idx ops).length = ops.length := by
            intro idx ops
            induction ops generalizing idx with
            | nil => rfl
            | cons _ rest ih => exact congrArg Nat.succ (ih (idx + 1))
          rw [hArgBindsLen]
        have hGoto : evalStepUnw pTgt 0
            { active := { defId := site.callerDefId, blockIdx := site.callBlock,
                          stmtIdx := ctx.callBb.statements.length + ctx.entryLives.length + ctx.args.length,
                          locals := pr.2 ++ initLocalsLoop ctx.callee pr.1 0 ctx.callee.locals },
              callStack := stack₂, callerMem := mem } =
            .step { active := { defId := site.callerDefId, blockIdx := 0 + ctx.bbOff,
                                stmtIdx := 0,
                                locals := pr.2 ++ initLocalsLoop ctx.callee pr.1 0 ctx.callee.locals },
                    callStack := stack₂, callerMem := mem } := by
          unfold evalStepUnw
          rw [ctx_bodies_lookup_eq ctx]; dsimp
          rw [ctx_caller'_bb_lookup_call ctx]; dsimp
          rw [← hCallBb'Len, getElem?_none_of_ge (Nat.le_refl _)]; dsimp
          rw [nat_beq_refl]; dsimp
          unfold evalTerminatorUnw
          dsimp [InlineUnwCtx.callBb']
          rw [Nat.zero_add]
        have hAllReach : ReachesPlusUnw pTgt
            { active := { defId := site.callerDefId, blockIdx := site.callBlock,
                          stmtIdx := ctx.callBb.statements.length,
                          locals := f.locals ++ replicateDead ctx.callee.locals.length },
              callStack := stack₂, callerMem := mem }
            { active := { defId := site.callerDefId, blockIdx := 0 + ctx.bbOff,
                          stmtIdx := 0,
                          locals := pr.2 ++ initLocalsLoop ctx.callee pr.1 0 ctx.callee.locals },
              callStack := stack₂, callerMem := mem } :=
          reachesPlusUnw_of_reachesPlus_reaches
            (reachesPlusUnw_of_reachesPlus_reaches hEntry hArgRun)
            (ReachesUnw.tail (ReachesUnw.refl _) ⟨0, rfl, hGoto⟩)
        have hCalleePos : 0 < ctx.callee.basicBlocks.length := by
          have hNe := ctx_callee_nonEmpty ctx
          cases hB : ctx.callee.basicBlocks with
          | nil => rw [hB] at hNe; cases hNe
          | cons _ _ => exact Nat.zero_lt_succ _
        exact ⟨_, hAllReach,
          InlStateRel.fused rfl hCalleePos hWfE hDef
            (frameWf_update_locals_same_loc hCBod hWf hLA hWA)
            rfl rfl rfl hStack⟩
    | false =>
      -- NON-INLINED CALLER BLOCK TERMINATOR
      have hNeC : f.blockIdx ≠ site.callBlock := nat_ne_of_beq_false hEqC
      have hEv2 : evalStepUnw pTgt 0 s₂ =
          evalTerminatorUnw pTgt ctx.caller' bb
            { f with locals := f.locals ++ replicateDead ctx.callee.locals.length }
            stack₂ mem := by
        unfold evalStepUnw
        dsimp [s₂]; rw [hDef, ctx_bodies_lookup_eq ctx]; dsimp
        rw [ctx_caller'_bb_lookup_ne ctx hBbLt hNeC, hBb]; dsimp
        rw [hSt]; dsimp; rw [hEqLenB]; rfl
      unfold evalTerminatorUnw
      unfold evalTerminatorUnw at hEv2
      cases hTm : bb.terminator with
      | unreachable => dsimp; rw [hTm] at hEv2; dsimp at hEv2; exact simOutcome_fault_zero hEv2
      | unsupported => dsimp; rw [hTm] at hEv2; dsimp at hEv2; exact simOutcome_fault_zero hEv2
      | goto t =>
        dsimp; rw [hTm] at hEv2 hTermBounds; dsimp at hEv2
        have hTLt : t < ctx.bbOff := nat_blt_lt hTermBounds
        exact simOutcome_step_one hEv2
          (InlStateRel.unfused
            (InlNormalFrameRel.caller hDef hTLt (frameWf_same_locals_block hWf))
            hStack)
      | return_ =>
        dsimp; rw [hTm] at hEv2; dsimp at hEv2
        cases hCl : bb.cleanup with
        | true => dsimp; rw [hCl] at hEv2; dsimp at hEv2; exact simOutcome_fault_zero hEv2
        | false =>
          dsimp; rw [hCl] at hEv2; dsimp at hEv2
          have h0Lt : 0 < f.locals.length := by rw [hLenC]; exact ctx_locOff_pos ctx
          rw [getElem?_append_left h0Lt] at hEv2
          cases hRet : Trusted.MirSemantics.getElem? f.locals 0 with
          | none => dsimp; rw [hRet] at hEv2; dsimp at hEv2; exact simOutcome_fault_zero hEv2
          | some sl =>
            rw [hRet] at hEv2
            cases sl with
            | dead => exact simOutcome_fault_zero hEv2
            | live ov =>
              cases ov with
              | none => exact simOutcome_fault_zero hEv2
              | some retVal =>
                cases hStack with
                | nil => exact simOutcome_done_zero hEv2
                | @consSingle c1 c2 r1 r2 hF hD hT hU hB hR =>
                  exact inl_returnToCaller ctx retVal
                    (InlStackRel.consSingle hF hD hT hU hB hR) rfl rfl mem hEv2
                | @consFused eC cC r1 r2 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 =>
                  exact inl_returnToCaller ctx retVal
                    (InlStackRel.consFused h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12) rfl rfl mem hEv2
      | switchInt discr ts =>
        dsimp; rw [hTm] at hEv2 hTermBounds; dsimp at hEv2
        dsimp [callerTermInBounds] at hTermBounds
        let ⟨h12, hBrsLt⟩ := bool_and_true hTermBounds
        let ⟨hDiscrLt, hOthBlt⟩ := bool_and_true h12
        dsimp [InlineUnwCtx.caller'] at hEv2
        rw [evalPrimitiveOperand_prefix hLenC hDiscrLt] at hEv2
        cases hOp : evalPrimitiveOperand ctx.caller.locals f.locals discr with
        | error k => dsimp; rw [hOp] at hEv2; dsimp at hEv2; exact simOutcome_fault_zero hEv2
        | ok pr =>
          dsimp; rw [hOp] at hEv2; dsimp at hEv2
          let ⟨hLP, hWP⟩ := evalPrimitiveOperand_wf hLenC hWtC hOp
          cases hV : pr.1 with
          | scalar sv =>
            dsimp; rw [hV] at hEv2; dsimp at hEv2
            cases hTr : evalSwitchBranches sv.width sv.bits ts.otherwise ts.branches with
            | error k => dsimp; rw [hTr] at hEv2; dsimp at hEv2; exact simOutcome_fault_zero hEv2
            | ok tgt =>
              dsimp; rw [hTr] at hEv2; dsimp at hEv2
              have hTgtLt : tgt < ctx.bbOff :=
                evalSwitchBranches_lt (nat_blt_lt hOthBlt) hBrsLt hTr
              exact simOutcome_step_one hEv2
                (InlStateRel.unfused
                  (InlNormalFrameRel.caller
                    (f := { f with blockIdx := tgt, stmtIdx := 0, locals := pr.2 })
                    hDef hTgtLt (frameWf_update_locals_reset hCBod hLP hWP))
                  hStack)
          | bool b =>
            dsimp; rw [hV] at hEv2; dsimp at hEv2
            cases hTr : evalBoolSwitchBranches b ts.otherwise ts.branches with
            | error k => dsimp; rw [hTr] at hEv2; dsimp at hEv2; exact simOutcome_fault_zero hEv2
            | ok tgt =>
              dsimp; rw [hTr] at hEv2; dsimp at hEv2
              have hTgtLt : tgt < ctx.bbOff :=
                evalBoolSwitchBranches_lt (nat_blt_lt hOthBlt) hBrsLt hTr
              exact simOutcome_step_one hEv2
                (InlStateRel.unfused
                  (InlNormalFrameRel.caller
                    (f := { f with blockIdx := tgt, stmtIdx := 0, locals := pr.2 })
                    hDef hTgtLt (frameWf_update_locals_reset hCBod hLP hWP))
                  hStack)
          | unit | ptr _ | enumVal _ _ | tuple _ | bytes _ =>
            dsimp; rw [hV] at hEv2; dsimp at hEv2; exact simOutcome_fault_zero hEv2
      | unwindResume =>
        dsimp; rw [hTm] at hEv2; dsimp at hEv2
        cases hCl : bb.cleanup with
        | false => dsimp; rw [hCl] at hEv2; dsimp at hEv2; exact simOutcome_fault_zero hEv2
        | true =>
          dsimp; rw [hCl] at hEv2; dsimp at hEv2
          exact inl_dispatchUnwindStack ctx hStack mem s₂ hEv2
      | assert cond exp msg t u =>
        dsimp; rw [hTm] at hEv2 hTermBounds; dsimp at hEv2
        dsimp [callerTermInBounds] at hTermBounds
        let ⟨h12, hULt⟩ := bool_and_true hTermBounds
        let ⟨hCondLt, hTBlt⟩ := bool_and_true h12
        dsimp [InlineUnwCtx.caller'] at hEv2
        rw [evalPrimitiveOperand_prefix hLenC hCondLt] at hEv2
        cases hOp : evalPrimitiveOperand ctx.caller.locals f.locals cond with
        | error k => dsimp; rw [hOp] at hEv2; dsimp at hEv2; exact simOutcome_fault_zero hEv2
        | ok pr =>
          let ⟨hLP, hWP⟩ := evalPrimitiveOperand_wf hLenC hWtC hOp
          cases pr with
          | mk pv pl =>
            rw [hOp] at hEv2
            dsimp at hLP hWP
            cases pv with
            | scalar _ | unit | ptr _ | enumVal _ _ | tuple _ | bytes _ =>
              exact simOutcome_fault_zero hEv2
            | bool b =>
              dsimp; dsimp at hEv2
              cases hb : boolEq b exp with
              | true =>
                dsimp; rw [hb] at hEv2; dsimp at hEv2
                exact simOutcome_step_one hEv2
                  (InlStateRel.unfused
                    (InlNormalFrameRel.caller
                      (f := { f with blockIdx := t, stmtIdx := 0, locals := pl })
                      hDef (nat_blt_lt hTBlt)
                      (frameWf_update_locals_reset hCBod hLP hWP))
                    hStack)
              | false =>
                dsimp; rw [hb] at hEv2; dsimp at hEv2
                dsimp [dispatchLocalUnwind]
                dsimp [dispatchLocalUnwind] at hEv2
                cases u with
                | unreachable => exact simOutcome_fault_zero hEv2
                | terminate => exact simOutcome_done_zero hEv2
                | continue_ => exact inl_dispatchUnwindStack ctx hStack mem s₂ hEv2
                | cleanup pBb =>
                  dsimp [unwindActionBlocksOnlyLt] at hULt
                  exact inl_enterCleanupBlock_normal ctx
                    (InlNormalFrameRel.caller (f := { f with locals := pl }) hDef hBbLt
                      (frameWf_update_locals_same_loc hCBod hWf hLP hWP))
                    (fun _ => nat_blt_lt hULt) hStack hEv2
      | call calleeId args dst tgt u =>
        dsimp; rw [hTm] at hEv2 hTermBounds; dsimp at hEv2
        dsimp [callerTermInBounds] at hTermBounds
        let ⟨h123, hULt⟩ := bool_and_true hTermBounds
        let ⟨h12, hTgtLt⟩ := bool_and_true h123
        let ⟨hArgsLt, hDstLt⟩ := bool_and_true h12
        dsimp [InlineUnwCtx.caller'] at hEv2
        rw [evalCallArgsUnw_prefix hLenC hArgsLt] at hEv2
        cases hArgs : evalCallArgsUnw ctx.caller.locals f.locals args with
        | error k => dsimp; rw [hArgs] at hEv2; dsimp at hEv2; exact simOutcome_fault_zero hEv2
        | ok pr =>
          dsimp; rw [hArgs] at hEv2; dsimp at hEv2
          let ⟨hLA, hWA⟩ := evalCallArgsUnw_wf hLenC hWtC hArgs
          have hCall := inl_initCalleeFrame_any ctx calleeId pr.1
          cases hCb : Trusted.MirSemantics.getElem? pSrc.bodies calleeId with
          | none =>
            dsimp; rw [hCb] at hCall; rw [hCall] at hEv2
            exact simOutcome_fault_zero hEv2
          | some cb₁ =>
            dsimp; rw [hCb] at hCall
            let ⟨cb₂, hCb₂, hInit⟩ := hCall
            rw [hCb₂] at hEv2; dsimp at hEv2
            cases hI1 : initCalleeFrameUnw calleeId cb₁ pr.1 with
            | error k =>
              dsimp; rw [hI1] at hInit; rw [hInit] at hEv2
              exact simOutcome_fault_zero hEv2
            | ok cf₁ =>
              dsimp; rw [hI1] at hInit
              let ⟨cf₂, hI2, hCfRel⟩ := hInit
              rw [hI2] at hEv2; dsimp at hEv2
              have hContBounds : f.defId = site.callerDefId →
                  dst.localId < ctx.locOff ∧
                  (∀ tBb, tgt = some tBb → tBb < ctx.bbOff) ∧
                  (∀ pBb, u = .cleanup pBb → pBb < ctx.bbOff) := by
                intro _
                refine ⟨nat_blt_lt hDstLt, ?_, ?_⟩
                · intro tBb ht; rw [ht] at hTgtLt; exact nat_blt_lt hTgtLt
                · intro pBb hp; rw [hp] at hULt; exact nat_blt_lt hULt
              exact simOutcome_step_one hEv2
                (InlStateRel.unfused hCfRel
                  (InlStackRel.consSingle
                    (InlNormalFrameRel.caller (f := { f with locals := pr.2 }) hDef hBbLt
                      (frameWf_update_locals_same_loc hCBod hWf hLA hWA))
                    rfl rfl rfl hContBounds hStack))

private theorem inl_step_fused {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site)
    {eFrame : FrameState} {cCont : CallContUnw}
    {rest₁ rest₂ : List CallContUnw} {mem : CallerMemory}
    (hEDef : eFrame.defId = site.calleeDefId)
    (hEBbLt : eFrame.blockIdx < ctx.callee.basicBlocks.length)
    (hEWf : FrameWf pSrc eFrame)
    (hCDef : cCont.callerFrame.defId = site.callerDefId)
    (hCWf : FrameWf pSrc cCont.callerFrame)
    (hCDst : cCont.dst = ctx.dst)
    (hCTgt : cCont.target = ctx.target)
    (hCUnw : cCont.unwind = ctx.callerUnwind)
    (hRest : InlStackRel ctx rest₁ rest₂) :
    SimOutcome ctx
      { active := {
          defId := site.callerDefId
          blockIdx := eFrame.blockIdx + ctx.bbOff
          stmtIdx := eFrame.stmtIdx
          locals := cCont.callerFrame.locals ++ eFrame.locals
        }
        callStack := rest₂
        callerMem := mem }
      (evalStepUnw pSrc 0 { active := eFrame, callStack := cCont :: rest₁, callerMem := mem }) := by
  have hEBod : Trusted.MirSemantics.getElem? pSrc.bodies eFrame.defId = some ctx.callee := by
    rw [hEDef]; exact ctx.hCallee
  have hCBod : Trusted.MirSemantics.getElem? pSrc.bodies cCont.callerFrame.defId = some ctx.caller := by
    rw [hCDef]; exact ctx.hCaller
  let ⟨hLenE, hWtE, hStmtLeE⟩ := hEWf ctx.callee hEBod
  let ⟨hLenC, hWtC, _⟩ := hCWf ctx.caller hCBod
  let ⟨bb, hBb⟩ := getElem?_some_of_lt ctx.callee.basicBlocks eFrame.blockIdx hEBbLt
  have hBbAd := list_all_getElem? (ctx_callee_bbs_all ctx) hBb
  let ⟨hStmtsAd, hTermAd⟩ := bool_and_true hBbAd
  let f₂ : FrameState := {
    defId := site.callerDefId
    blockIdx := eFrame.blockIdx + ctx.bbOff
    stmtIdx := eFrame.stmtIdx
    locals := cCont.callerFrame.locals ++ eFrame.locals
  }
  let s₂ : UnwindState := { active := f₂, callStack := rest₂, callerMem := mem }
  have hBb₂ : Trusted.MirSemantics.getElem? ctx.caller'.basicBlocks (eFrame.blockIdx + ctx.bbOff) =
      some (shiftCalleeBlock ctx.locOff ctx.bbOff ctx.normalExitBb ctx.unwindExitBb bb) := by
    rw [ctx_caller'_bb_lookup_callee ctx hEBbLt, hBb]
  cases hSt : Trusted.MirSemantics.getElem? bb.statements eFrame.stmtIdx with
  | some stmt =>
    have hSAd : stmtLocalsLtAndNoDead0 ctx.callee.locals.length stmt = true :=
      list_all_getElem? hStmtsAd hSt
    have hSt₂ : Trusted.MirSemantics.getElem?
        (shiftCalleeBlock ctx.locOff ctx.bbOff ctx.normalExitBb ctx.unwindExitBb bb).statements
        eFrame.stmtIdx = some (shiftStmtUnw ctx.locOff stmt) := by
      dsimp [shiftCalleeBlock]
      rw [getElem?_map, hSt]
    have hEv2 : evalStepUnw pTgt 0 s₂ =
        match evalStatement ctx.caller' f₂ mem (shiftStmtUnw ctx.locOff stmt) with
        | .fault k => .fault k
        | .done out => .done (embedTerminalOut out)
        | .step st' =>
          match st'.frames with
          | [f'] => .step { active := f', callStack := rest₂, callerMem := st'.callerMem }
          | _ => .fault .unsupported := by
      unfold evalStepUnw
      dsimp [s₂, f₂]
      rw [ctx_bodies_lookup_eq ctx]; dsimp
      rw [hBb₂]; dsimp; rw [hSt₂]
    have hF2Eq : f₂ = { ({ defId := site.callerDefId, blockIdx := eFrame.blockIdx + ctx.bbOff,
                           stmtIdx := eFrame.stmtIdx, locals := eFrame.locals } : FrameState) with
                        locals := cCont.callerFrame.locals ++ eFrame.locals } := rfl
    have hEvSuff := evalStatement_suffix
      (rfl : ctx.caller'.locals = ctx.caller.locals ++ ctx.callee.locals)
      (rfl : ctx.callee.locals = ctx.callee.locals)
      hLenC (ctx_locOff_pos ctx) hSAd
      (f := { defId := site.callerDefId, blockIdx := eFrame.blockIdx + ctx.bbOff,
              stmtIdx := eFrame.stmtIdx, locals := eFrame.locals })
      (cSlots := cCont.callerFrame.locals) (eSlots := eFrame.locals) (mem := mem)
    -- Relate `evalStatement ctx.callee { defId := ..., blockIdx := ..., stmtIdx := eFrame.stmtIdx, locals := eFrame.locals }` to `evalStatement ctx.callee eFrame`
    have hSameEval : ∀ (g : FrameState), g.stmtIdx = eFrame.stmtIdx → g.locals = eFrame.locals →
        evalStatement ctx.callee g mem stmt =
          match evalStatement ctx.callee eFrame mem stmt with
          | .fault k => .fault k
          | .done out => .done out
          | .step st' =>
            match st'.frames with
            | [f'] => .step { frames := [{ g with stmtIdx := f'.stmtIdx, locals := f'.locals }],
                              callerMem := st'.callerMem }
            | _ => .fault .unsupported := by
      intro g hSi hLoc
      cases stmt with
      | nop => dsimp [evalStatement]; rw [hSi, hLoc]
      | unsupported => rfl
      | storageLive id =>
        dsimp [evalStatement]; rw [hLoc]
        cases Trusted.MirSemantics.getElem? ctx.callee.locals id with
        | none => rfl
        | some ty =>
          dsimp
          cases setElem? eFrame.locals id (liveUninitSlot ty) with
          | none => rfl
          | some _ => dsimp; rw [hSi]
      | storageDead id =>
        dsimp [evalStatement]; rw [hLoc]
        cases Nat.beq id 0 with
        | true => rfl
        | false =>
          dsimp
          cases setElem? eFrame.locals id .dead with
          | none => rfl
          | some _ => dsimp; rw [hSi]
      | assign dst rv =>
        dsimp [evalStatement]; rw [hLoc]
        cases !dst.projection.isEmpty with
        | true => rfl
        | false =>
          dsimp
          cases Trusted.MirSemantics.getElem? ctx.callee.locals dst.localId with
          | none => rfl
          | some dstTy =>
            dsimp
            cases evalRvalue ctx.callee.locals eFrame.locals dstTy rv with
            | error _ => rfl
            | ok pr =>
              dsimp
              cases writePlace pr.2 dst.localId dstTy pr.1 with
              | error _ => rfl
              | ok _ => dsimp; rw [hSi]
    dsimp [InlineUnwCtx.locOff] at hEv2
    rw [hF2Eq] at hEv2
    rw [hEvSuff] at hEv2
    dsimp at hEv2
    rw [hSameEval { defId := site.callerDefId, blockIdx := eFrame.blockIdx + ctx.bbOff,
                    stmtIdx := eFrame.stmtIdx, locals := eFrame.locals } rfl rfl] at hEv2
    unfold evalStepUnw
    rw [hEBod]; dsimp; rw [hBb]; dsimp; rw [hSt]; dsimp
    cases hEv1 : evalStatement ctx.callee eFrame mem stmt with
    | fault k => dsimp; rw [hEv1] at hEv2; dsimp at hEv2; exact simOutcome_fault_zero hEv2
    | done out => dsimp; rw [hEv1] at hEv2; dsimp at hEv2; exact simOutcome_done_zero hEv2
    | step st' =>
      dsimp; rw [hEv1] at hEv2; dsimp at hEv2
      cases hFrs : st'.frames with
      | nil => dsimp; rw [hFrs] at hEv2; dsimp at hEv2; exact simOutcome_fault_zero hEv2
      | cons e' restF =>
        cases restF with
        | cons _ _ => dsimp; rw [hFrs] at hEv2; dsimp at hEv2; exact simOutcome_fault_zero hEv2
        | nil =>
          dsimp; rw [hFrs] at hEv2; dsimp at hEv2
          have hEv1' : evalStatement ctx.callee eFrame mem stmt = .step ⟨[e'], st'.callerMem⟩ := by
            rw [hEv1]; cases st' with | mk frs cm => dsimp at hFrs; subst hFrs; rfl
          let ⟨hWfE', hDefE', hBbE', _⟩ := evalStatement_wf hEBod hBb hSt hEWf hEv1'
          have hDef1 : e'.defId = site.calleeDefId := hDefE'.trans hEDef
          have hBb1 : e'.blockIdx < ctx.callee.basicBlocks.length := by rw [hBbE']; exact hEBbLt
          rw [← hBbE'] at hEv2
          exact simOutcome_step_one hEv2
            (InlStateRel.fused hDef1 hBb1 hWfE' hCDef hCWf hCDst hCTgt hCUnw hRest)
  | none =>
    have hGe : bb.statements.length ≤ eFrame.stmtIdx := getElem?_none_ge hSt
    have hEqIdx : eFrame.stmtIdx = bb.statements.length := Nat.le_antisymm (hStmtLeE bb hBb) hGe
    have hEqLenE : Nat.beq eFrame.stmtIdx bb.statements.length = true := by
      rw [hEqIdx]; exact nat_beq_refl _
    unfold evalStepUnw
    rw [hEBod]; dsimp; rw [hBb]; dsimp; rw [hSt]; dsimp
    rw [hEqLenE]; dsimp
    have hEv2 : evalStepUnw pTgt 0 s₂ =
        evalTerminatorUnw pTgt ctx.caller'
          (shiftCalleeBlock ctx.locOff ctx.bbOff ctx.normalExitBb ctx.unwindExitBb bb)
          f₂ rest₂ mem := by
      unfold evalStepUnw
      dsimp [s₂, f₂]
      rw [ctx_bodies_lookup_eq ctx]; dsimp
      rw [hBb₂]; dsimp
      have hNone₂ : Trusted.MirSemantics.getElem?
          (shiftCalleeBlock ctx.locOff ctx.bbOff ctx.normalExitBb ctx.unwindExitBb bb).statements
          eFrame.stmtIdx = none := by
        dsimp [shiftCalleeBlock]
        rw [getElem?_map, hSt]
      have hLen₂ : (shiftCalleeBlock ctx.locOff ctx.bbOff ctx.normalExitBb ctx.unwindExitBb bb).statements.length =
          bb.statements.length := list_length_map _ _
      rw [hNone₂]; dsimp; rw [hLen₂, hEqLenE]; rfl
    cases bb with
    | mk bbStmts bbTerm bbClean =>
      dsimp at hBbAd hStmtsAd hTermAd hSt hGe hEqIdx hEqLenE
      unfold evalTerminatorUnw
      unfold evalTerminatorUnw at hEv2
      dsimp [shiftCalleeBlock]
      dsimp [shiftCalleeBlock] at hEv2
      cases hTm : bbTerm with
      | unreachable => dsimp; rw [hTm] at hEv2; exact simOutcome_fault_zero hEv2
      | unsupported => dsimp; rw [hTm] at hEv2; exact simOutcome_fault_zero hEv2
      | goto t =>
        dsimp; rw [hTm] at hEv2 hTermAd; dsimp [shiftCalleeTerminator] at hEv2
        have hTLt : t < ctx.callee.basicBlocks.length := nat_blt_lt hTermAd
        exact simOutcome_step_one hEv2
          (InlStateRel.fused hEDef hTLt (frameWf_same_locals_block hEWf)
            hCDef hCWf hCDst hCTgt hCUnw hRest)
      | return_ =>
        dsimp; rw [hTm] at hEv2
        cases bbClean with
        | true =>
          dsimp; dsimp [shiftCalleeTerminator] at hEv2
          exact simOutcome_fault_zero hEv2
        | false =>
          -- NORMAL RETURN FROM INLINED CALLEE via `normalExitBlock`!
          dsimp; dsimp [shiftCalleeTerminator] at hEv2
          -- Step 1: `.goto ctx.normalExitBb`
          let sNorm0 : UnwindState := {
            active := { defId := site.callerDefId, blockIdx := ctx.normalExitBb,
                        stmtIdx := 0, locals := cCont.callerFrame.locals ++ eFrame.locals },
            callStack := rest₂, callerMem := mem
          }
          apply simOutcome_prepend_step hEv2
          -- Unpack `callDstCompatible`
          have hDstC := ctx.hDstCompat
          unfold callDstCompatible at hDstC
          let ⟨hDstProj, hDstTyM⟩ := bool_and_true hDstC
          cases hDstTyGet : Trusted.MirSemantics.getElem? ctx.caller.locals ctx.dst.localId with
          | none => rw [hDstTyGet] at hDstTyM; cases hDstTyM
          | some dstTy =>
            rw [hDstTyGet] at hDstTyM
            cases hRetTyGet : Trusted.MirSemantics.getElem? ctx.callee.locals 0 with
            | none => rw [hRetTyGet] at hDstTyM; cases hDstTyM
            | some retTy =>
              rw [hRetTyGet] at hDstTyM
              have hTyEq : dstTy = retTy := mirTy_beq_eq hDstTyM
              have hDstLt : ctx.dst.localId < ctx.locOff := getElem?_some_lt hDstTyGet
              have hDstLtS : ctx.dst.localId < cCont.callerFrame.locals.length := by
                rw [hLenC]; exact hDstLt
              have hDstTy' : Trusted.MirSemantics.getElem? ctx.caller'.locals ctx.dst.localId =
                  some dstTy := by
                dsimp [InlineUnwCtx.caller']
                rw [getElem?_append_left hDstLt]; exact hDstTyGet
              have hRetTy' : Trusted.MirSemantics.getElem? ctx.caller'.locals ctx.locOff =
                  some retTy := by
                dsimp [InlineUnwCtx.caller', InlineUnwCtx.locOff]
                have h0 : ctx.caller.locals.length = ctx.caller.locals.length + 0 := (Nat.add_zero _).symm
                rw [h0, getElem?_append_right]; exact hRetTyGet
              have hRetSlot : Trusted.MirSemantics.getElem?
                  (cCont.callerFrame.locals ++ eFrame.locals) ctx.locOff =
                  Trusted.MirSemantics.getElem? eFrame.locals 0 := by
                dsimp [InlineUnwCtx.locOff]
                rw [← hLenC]
                have h0 : cCont.callerFrame.locals.length = cCont.callerFrame.locals.length + 0 :=
                  (Nat.add_zero _).symm
                rw [h0, getElem?_append_right]
              have hEvStmt0 : evalStepUnw pTgt 0 sNorm0 =
                  match evalRvalue ctx.caller'.locals (cCont.callerFrame.locals ++ eFrame.locals)
                      dstTy (.use (.move ⟨ctx.locOff, []⟩)) with
                  | .error k => .fault k
                  | .ok (val, locsAfterRval) =>
                    match writePlace locsAfterRval ctx.dst.localId dstTy val with
                    | .error k => .fault k
                    | .ok locsAfterWrite =>
                      .step { active := { defId := site.callerDefId, blockIdx := ctx.normalExitBb,
                                          stmtIdx := 1, locals := locsAfterWrite },
                              callStack := rest₂, callerMem := mem } := by
                unfold evalStepUnw
                dsimp [sNorm0]
                rw [ctx_bodies_lookup_eq ctx]; dsimp
                rw [ctx_caller'_bb_lookup_normalExit ctx]
                dsimp [InlineUnwCtx.normalExitBlock, Trusted.MirSemantics.getElem?, evalStatement]
                rw [hDstProj]; dsimp; rw [hDstTy']; dsimp
                cases evalRvalue ctx.caller'.locals (cCont.callerFrame.locals ++ eFrame.locals)
                    dstTy (.use (.move ⟨ctx.locOff, []⟩)) with
                | error _ => rfl
                | ok pr =>
                  cases pr with
                  | mk v ls =>
                    dsimp
                    cases writePlace ls ctx.dst.localId dstTy v <;> rfl
              -- Evaluate `eFrame.locals[0]`
              have h0LtE : 0 < eFrame.locals.length := by
                rw [hLenE]; exact getElem?_some_lt hRetTyGet
              let ⟨sl0, hSl0⟩ := getElem?_some_of_lt eFrame.locals 0 h0LtE
              rw [hSl0]
              dsimp [evalRvalue, evalOperandToSlot] at hEvStmt0
              rw [hRetTy', hRetSlot, hSl0] at hEvStmt0
              cases sl0 with
              | dead => exact simOutcome_fault_zero hEvStmt0
              | live ov0 =>
                dsimp at hEvStmt0
                let ⟨eLocs1, hSetE0⟩ := setElem?_some_of_lt eFrame.locals 0 (liveUninitSlot retTy) h0LtE
                have hSetApp : setElem? (cCont.callerFrame.locals ++ eFrame.locals) ctx.locOff
                    (liveUninitSlot retTy) = some (cCont.callerFrame.locals ++ eLocs1) := by
                  dsimp [InlineUnwCtx.locOff]
                  rw [← hLenC]
                  have h0 : cCont.callerFrame.locals.length = cCont.callerFrame.locals.length + 0 :=
                    (Nat.add_zero _).symm
                  rw [h0, setElem?_append_right, hSetE0]
                rw [hSetApp] at hEvStmt0; dsimp at hEvStmt0
                have hBeqR : MirTy.beq retTy dstTy = true := by
                  rw [hTyEq]; exact mirTy_beq_refl retTy
                rw [hBeqR] at hEvStmt0; dsimp at hEvStmt0
                cases ov0 with
                | none => exact simOutcome_fault_zero hEvStmt0
                | some retVal =>
                  dsimp at hEvStmt0
                  dsimp [returnToCallerUnw]
                  rw [hCBod, hCDst, hCTgt, hDstProj]; dsimp; rw [hDstTyGet]; dsimp
                  rw [writePlace_prefix hDstLtS] at hEvStmt0
                  cases hWr : writePlace cCont.callerFrame.locals ctx.dst.localId dstTy retVal with
                  | error k => rw [hWr] at hEvStmt0; exact simOutcome_fault_zero hEvStmt0
                  | ok cLocs' =>
                    dsimp; rw [hWr] at hEvStmt0; dsimp at hEvStmt0
                    let ⟨hLC', hWC'⟩ := writePlace_wf hLenC hWtC hDstTyGet hWr
                    have hLE1 : eLocs1.length = ctx.callee.locals.length :=
                      (setElem?_length hSetE0).trans hLenE
                    apply simOutcome_prepend_step hEvStmt0
                    have hDeads := run_deads_normalExit ctx cLocs' eLocs1 hLC' hLE1 rest₂ mem
                    apply simOutcome_prepend_reaches hDeads
                    cases hTgtCase : ctx.target with
                    | none =>
                      apply simOutcome_fault_zero
                      unfold evalStepUnw
                      rw [ctx_bodies_lookup_eq ctx]; dsimp
                      rw [ctx_caller'_bb_lookup_normalExit ctx]; dsimp
                      rw [getElem?_none_of_ge (Nat.le_refl _)]; dsimp
                      rw [nat_beq_refl]; dsimp
                      unfold evalTerminatorUnw
                      dsimp [InlineUnwCtx.normalExitBlock]
                      rw [hTgtCase]; rfl
                    | some nextBb =>
                      let ⟨tData, hTData, _⟩ := ctx.hTargetOk nextBb hTgtCase
                      have hNextLt : nextBb < ctx.bbOff := getElem?_some_lt hTData
                      have hGoto : evalStepUnw pTgt 0
                          { active := { defId := site.callerDefId, blockIdx := ctx.normalExitBb,
                                        stmtIdx := ctx.normalExitBlock.statements.length,
                                        locals := cLocs' ++ replicateDead ctx.callee.locals.length },
                            callStack := rest₂, callerMem := mem } =
                          .step { active := { defId := site.callerDefId, blockIdx := nextBb,
                                              stmtIdx := 0,
                                              locals := cLocs' ++ replicateDead ctx.callee.locals.length },
                                  callStack := rest₂, callerMem := mem } := by
                        unfold evalStepUnw
                        rw [ctx_bodies_lookup_eq ctx]; dsimp
                        rw [ctx_caller'_bb_lookup_normalExit ctx]; dsimp
                        rw [getElem?_none_of_ge (Nat.le_refl _)]; dsimp
                        rw [nat_beq_refl]; dsimp
                        unfold evalTerminatorUnw
                        dsimp [InlineUnwCtx.normalExitBlock]
                        rw [hTgtCase]; rfl
                      apply simOutcome_step_one hGoto
                      have hEqF : { defId := site.callerDefId, blockIdx := nextBb, stmtIdx := 0,
                                    locals := cLocs' ++ replicateDead ctx.callee.locals.length } =
                          { ({ cCont.callerFrame with blockIdx := nextBb, stmtIdx := 0, locals := cLocs' }) with
                            locals := ({ cCont.callerFrame with blockIdx := nextBb, stmtIdx := 0, locals := cLocs' }).locals ++
                              replicateDead ctx.callee.locals.length } := by
                        dsimp; rw [hCDef]
                      rw [hEqF]
                      exact InlStateRel.unfused
                        (InlNormalFrameRel.caller hCDef hNextLt
                          (frameWf_update_locals_reset hCBod hLC' hWC'))
                        hRest
      | unwindResume =>
        dsimp; rw [hTm] at hEv2
        cases bbClean with
        | false =>
          dsimp; dsimp [shiftCalleeTerminator] at hEv2
          exact simOutcome_fault_zero hEv2
        | true =>
          dsimp; dsimp [shiftCalleeTerminator] at hEv2
          exact inl_exit_unwindExitBlock ctx hCDef hCWf hCUnw hLenE hRest
            (inl_dispatchUnwindStack ctx hRest mem) hEv2
      | switchInt discr ts =>
        dsimp; rw [hTm] at hEv2 hTermAd; dsimp [shiftCalleeTerminator] at hEv2
        dsimp [termWellScoped] at hTermAd
        let ⟨h12, hBrsLt⟩ := bool_and_true hTermAd
        let ⟨_, hOthBlt⟩ := bool_and_true h12
        dsimp [InlineUnwCtx.caller', InlineUnwCtx.locOff] at hEv2
        rw [evalPrimitiveOperand_suffix hLenC] at hEv2
        cases hOp : evalPrimitiveOperand ctx.callee.locals eFrame.locals discr with
        | error k => dsimp; rw [hOp] at hEv2; dsimp at hEv2; exact simOutcome_fault_zero hEv2
        | ok pr =>
          dsimp; rw [hOp] at hEv2; dsimp at hEv2
          let ⟨hLP, hWP⟩ := evalPrimitiveOperand_wf hLenE hWtE hOp
          cases hV : pr.1 with
          | scalar sv =>
            dsimp; rw [hV] at hEv2; dsimp at hEv2
            rw [evalSwitchBranches_shift] at hEv2
            cases hTr : evalSwitchBranches sv.width sv.bits ts.otherwise ts.branches with
            | error k => dsimp; rw [hTr] at hEv2; dsimp at hEv2; exact simOutcome_fault_zero hEv2
            | ok tgt =>
              dsimp; rw [hTr] at hEv2; dsimp at hEv2
              have hTgtLt : tgt < ctx.callee.basicBlocks.length :=
                evalSwitchBranches_lt (nat_blt_lt hOthBlt) hBrsLt hTr
              exact simOutcome_step_one hEv2
                (InlStateRel.fused hEDef hTgtLt
                  (frameWf_update_locals_reset hEBod hLP hWP)
                  hCDef hCWf hCDst hCTgt hCUnw hRest)
          | bool b =>
            dsimp; rw [hV] at hEv2; dsimp at hEv2
            rw [evalBoolSwitchBranches_shift] at hEv2
            cases hTr : evalBoolSwitchBranches b ts.otherwise ts.branches with
            | error k => dsimp; rw [hTr] at hEv2; dsimp at hEv2; exact simOutcome_fault_zero hEv2
            | ok tgt =>
              dsimp; rw [hTr] at hEv2; dsimp at hEv2
              have hTgtLt : tgt < ctx.callee.basicBlocks.length :=
                evalBoolSwitchBranches_lt (nat_blt_lt hOthBlt) hBrsLt hTr
              exact simOutcome_step_one hEv2
                (InlStateRel.fused hEDef hTgtLt
                  (frameWf_update_locals_reset hEBod hLP hWP)
                  hCDef hCWf hCDst hCTgt hCUnw hRest)
          | unit | ptr _ | enumVal _ _ | tuple _ | bytes _ =>
            dsimp; rw [hV] at hEv2; dsimp at hEv2; exact simOutcome_fault_zero hEv2
      | assert cond exp msg t u =>
        dsimp; rw [hTm] at hEv2 hTermAd; dsimp [shiftCalleeTerminator] at hEv2
        dsimp [termWellScoped] at hTermAd
        let ⟨h12, hUAd⟩ := bool_and_true hTermAd
        let ⟨_, hTBlt⟩ := bool_and_true h12
        dsimp [InlineUnwCtx.caller', InlineUnwCtx.locOff] at hEv2
        rw [evalPrimitiveOperand_suffix hLenC] at hEv2
        cases hOp : evalPrimitiveOperand ctx.callee.locals eFrame.locals cond with
        | error k => dsimp; rw [hOp] at hEv2; dsimp at hEv2; exact simOutcome_fault_zero hEv2
        | ok pr =>
          let ⟨hLP, hWP⟩ := evalPrimitiveOperand_wf hLenE hWtE hOp
          cases pr with
          | mk pv pl =>
            rw [hOp] at hEv2
            dsimp at hLP hWP
            cases pv with
            | scalar _ | unit | ptr _ | enumVal _ _ | tuple _ | bytes _ =>
              exact simOutcome_fault_zero hEv2
            | bool b =>
              dsimp; dsimp at hEv2
              cases hb : boolEq b exp with
              | true =>
                dsimp; rw [hb] at hEv2; dsimp at hEv2
                exact simOutcome_step_one hEv2
                  (InlStateRel.fused hEDef (nat_blt_lt hTBlt)
                    (frameWf_update_locals_reset hEBod hLP hWP)
                    hCDef hCWf hCDst hCTgt hCUnw hRest)
              | false =>
                dsimp; rw [hb] at hEv2; dsimp at hEv2
                dsimp [dispatchLocalUnwind]
                dsimp [dispatchLocalUnwind] at hEv2
                cases u with
                | unreachable =>
                  dsimp [shiftCalleeUnwindAction] at hEv2
                  exact simOutcome_fault_zero hEv2
                | terminate =>
                  dsimp [shiftCalleeUnwindAction] at hEv2
                  exact simOutcome_done_zero hEv2
                | continue_ =>
                  dsimp [shiftCalleeUnwindAction, enterCleanupBlockUnw] at hEv2
                  rw [ctx_bodies_lookup_eq ctx] at hEv2; dsimp at hEv2
                  rw [ctx_caller'_bb_lookup_unwindExit ctx] at hEv2
                  dsimp [InlineUnwCtx.unwindExitBlock] at hEv2
                  exact inl_exit_unwindExitBlock ctx hCDef hCWf hCUnw hLP hRest
                    (inl_dispatchUnwindStack ctx hRest mem) hEv2
                | cleanup pBb =>
                  dsimp [unwindActionBlocksLt] at hUAd
                  let ⟨hPBbBlt, hPCleanM⟩ := bool_and_true hUAd
                  have hPBbLt : pBb < ctx.callee.basicBlocks.length := nat_blt_lt hPBbBlt
                  let ⟨pData, hPData⟩ := getElem?_some_of_lt ctx.callee.basicBlocks pBb hPBbLt
                  rw [hPData] at hPCleanM; dsimp at hPCleanM
                  dsimp [enterCleanupBlockUnw]
                  rw [hEBod]; dsimp; rw [hPData]; dsimp; rw [hPCleanM]; dsimp
                  dsimp [shiftCalleeUnwindAction, enterCleanupBlockUnw] at hEv2
                  rw [ctx_bodies_lookup_eq ctx] at hEv2; dsimp at hEv2
                  rw [ctx_caller'_bb_lookup_callee ctx hPBbLt, hPData] at hEv2
                  dsimp [shiftCalleeBlock] at hEv2
                  rw [hPCleanM] at hEv2; dsimp at hEv2
                  exact simOutcome_step_one hEv2
                    (InlStateRel.fused hEDef hPBbLt
                      (frameWf_update_locals_reset hEBod hLP hWP)
                      hCDef hCWf hCDst hCTgt hCUnw hRest)
      | call calleeId args dst tgt u =>
        dsimp; rw [hTm] at hEv2 hTermAd; dsimp [shiftCalleeTerminator] at hEv2
        dsimp [termWellScoped] at hTermAd
        let ⟨h123, hUAd⟩ := bool_and_true hTermAd
        let ⟨h12, hTgtAd⟩ := bool_and_true h123
        let ⟨_, hDstAd⟩ := bool_and_true h12
        dsimp [placeLocalLt] at hDstAd
        dsimp [InlineUnwCtx.caller', InlineUnwCtx.locOff] at hEv2
        rw [evalCallArgsUnw_suffix hLenC] at hEv2
        cases hArgs : evalCallArgsUnw ctx.callee.locals eFrame.locals args with
        | error k => dsimp; rw [hArgs] at hEv2; dsimp at hEv2; exact simOutcome_fault_zero hEv2
        | ok pr =>
          dsimp; rw [hArgs] at hEv2; dsimp at hEv2
          let ⟨hLA, hWA⟩ := evalCallArgsUnw_wf hLenE hWtE hArgs
          have hCall := inl_initCalleeFrame_any ctx calleeId pr.1
          cases hCb : Trusted.MirSemantics.getElem? pSrc.bodies calleeId with
          | none =>
            dsimp; rw [hCb] at hCall; rw [hCall] at hEv2
            exact simOutcome_fault_zero hEv2
          | some cb₁ =>
            dsimp; rw [hCb] at hCall
            let ⟨cb₂, hCb₂, hInit⟩ := hCall
            rw [hCb₂] at hEv2; dsimp at hEv2
            cases hI1 : initCalleeFrameUnw calleeId cb₁ pr.1 with
            | error k =>
              dsimp; rw [hI1] at hInit; rw [hInit] at hEv2
              exact simOutcome_fault_zero hEv2
            | ok cf₁ =>
              dsimp; rw [hI1] at hInit
              let ⟨cf₂, hI2, hCfRel⟩ := hInit
              rw [hI2] at hEv2; dsimp at hEv2
              have hETgtLt : ∀ tBb, tgt = some tBb → tBb < ctx.callee.basicBlocks.length := by
                intro tBb ht; rw [ht] at hTgtAd; exact nat_blt_lt hTgtAd
              exact simOutcome_step_one hEv2
                (InlStateRel.unfused hCfRel
                  (InlStackRel.consFused
                    (eCont := { callerFrame := { eFrame with locals := pr.2 },
                                dst := dst, target := tgt, unwind := u })
                    hCDef hCWf hCDst hCTgt hCUnw
                    hEDef hEBbLt (frameWf_update_locals_same_loc hEBod hEWf hLA hWA)
                    (nat_blt_lt hDstAd) hETgtLt hUAd hRest))

private theorem inl_step_fwd {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) {s₁ s₂ : UnwindState}
    (hRel : InlStateRel ctx s₁ s₂) :
    SimOutcome ctx s₂ (evalStepUnw pSrc 0 s₁) := by
  cases hRel with
  | unfused hFr hStack =>
    cases hFr with
    | other hNe => exact inl_step_unfused_other ctx hNe hStack
    | caller hDef hBbLt hWf => exact inl_step_unfused_caller ctx hDef hBbLt hWf hStack
  | fused hEDef hEBbLt hEWf hCDef hCWf hCDst hCTgt hCUnw hRest =>
    exact inl_step_fused ctx hEDef hEBbLt hEWf hCDef hCWf hCDst hCTgt hCUnw hRest

/-! ### Part 6: Top-Level `inlineWithUnwind` Soundness (`ProgramEquivUnw`) -/

private theorem entryProgForBody_enterCleanupBlockUnw (p : Program) (d : DefId)
    (f : FrameState) (stack : List CallContUnw) (mem : CallerMemory) (padBb : BasicBlockId) :
    enterCleanupBlockUnw (entryProgForBody p d) f stack mem padBb =
      enterCleanupBlockUnw p f stack mem padBb := rfl

private theorem entryProgForBody_dispatchUnwindStack (p : Program) (d : DefId) (mem : CallerMemory) :
    ∀ (stack : List CallContUnw),
      dispatchUnwindStack (entryProgForBody p d) mem stack = dispatchUnwindStack p mem stack
  | [] => rfl
  | cont :: rest => by
    unfold dispatchUnwindStack
    cases cont.unwind with
    | continue_ => exact entryProgForBody_dispatchUnwindStack p d mem rest
    | cleanup _ | terminate | unreachable => rfl

private theorem entryProgForBody_dispatchLocalUnwind (p : Program) (d : DefId)
    (f : FrameState) (stack : List CallContUnw) (mem : CallerMemory) (u : UnwindAction) :
    dispatchLocalUnwind (entryProgForBody p d) f stack mem u =
      dispatchLocalUnwind p f stack mem u := by
  unfold dispatchLocalUnwind
  cases u with
  | continue_ => exact entryProgForBody_dispatchUnwindStack p d mem stack
  | cleanup _ | terminate | unreachable => rfl

private theorem entryProgForBody_returnToCallerUnw (p : Program) (d : DefId)
    (retVal : Val) (cont : CallContUnw) (rest : List CallContUnw) (mem : CallerMemory) :
    returnToCallerUnw (entryProgForBody p d) retVal cont rest mem =
      returnToCallerUnw p retVal cont rest mem := rfl

private theorem entryProgForBody_evalTerminatorUnw (p : Program) (d : DefId)
    (body : Body) (bb : BasicBlock) (f : FrameState)
    (stack : List CallContUnw) (mem : CallerMemory) :
    evalTerminatorUnw (entryProgForBody p d) body bb f stack mem =
      evalTerminatorUnw p body bb f stack mem := by
  unfold evalTerminatorUnw
  cases bb.terminator with
  | goto _ | unreachable | unsupported | switchInt _ _ | call _ _ _ _ _ => rfl
  | return_ =>
    cases bb.cleanup with
    | true => rfl
    | false =>
      dsimp
      cases Trusted.MirSemantics.getElem? f.locals 0 with
      | none => rfl
      | some sl =>
        cases sl with
        | dead => rfl
        | live ov =>
          cases ov with
          | none => rfl
          | some rv =>
            cases stack with
            | nil => rfl
            | cons cont rest => exact entryProgForBody_returnToCallerUnw p d rv cont rest mem
  | unwindResume =>
    cases bb.cleanup with
    | false => rfl
    | true => exact entryProgForBody_dispatchUnwindStack p d mem stack
  | assert cond exp _msg target u =>
    dsimp
    cases evalPrimitiveOperand body.locals f.locals cond with
    | error _ => rfl
    | ok pr =>
      cases pr with
      | mk pv pl =>
        cases pv with
        | scalar _ | unit | ptr _ | enumVal _ _ | tuple _ | bytes _ => rfl
        | bool b =>
          dsimp
          cases boolEq b exp with
          | true => rfl
          | false => exact entryProgForBody_dispatchLocalUnwind p d _ stack mem u

private theorem entryProgForBody_evalStepUnw (p : Program) (d : DefId) (c : Choice) (s : UnwindState) :
    evalStepUnw (entryProgForBody p d) c s = evalStepUnw p c s := by
  unfold evalStepUnw
  have hBod : (entryProgForBody p d).bodies = p.bodies := rfl
  rw [hBod]
  cases Trusted.MirSemantics.getElem? p.bodies s.active.defId with
  | none => rfl
  | some body =>
    dsimp
    cases Trusted.MirSemantics.getElem? body.basicBlocks s.active.blockIdx with
    | none => rfl
    | some bb =>
      dsimp
      cases Trusted.MirSemantics.getElem? bb.statements s.active.stmtIdx with
      | some _ => rfl
      | none =>
        dsimp
        cases Nat.beq s.active.stmtIdx bb.statements.length with
        | false => rfl
        | true => dsimp; exact entryProgForBody_evalTerminatorUnw p d body bb s.active s.callStack s.callerMem

private theorem entryProgForBody_reachesUnw {p : Program} {d : DefId} {s₁ s₂ : UnwindState}
    (h : ReachesUnw p s₁ s₂) : ReachesUnw (entryProgForBody p d) s₁ s₂ := by
  induction h with
  | refl => exact ReachesUnw.refl _
  | tail _ hStep ih =>
    let ⟨c, hc, hEv⟩ := hStep
    have hStep' : StepUnw (entryProgForBody p d) _ (.step _) :=
      ⟨c, hc, (entryProgForBody_evalStepUnw p d c _).trans hEv⟩
    exact ReachesUnw.tail ih hStep'

private theorem entryProgForBody_reachesPlusUnw {p : Program} {d : DefId} {s₁ s₂ : UnwindState}
    (h : ReachesPlusUnw p s₁ s₂) : ReachesPlusUnw (entryProgForBody p d) s₁ s₂ := by
  let ⟨n, hn⟩ := h
  have hConv : ∀ {k : Nat} {a b : UnwindState},
      ReachesNUnw p k a b → ReachesNUnw (entryProgForBody p d) k a b := by
    intro k a b hN
    induction hN with
    | zero x => exact ReachesNUnw.zero x
    | succ hSt _ ih =>
      exact ReachesNUnw.succ ((entryProgForBody_evalStepUnw p d 0 _).trans hSt) ih
  exact ⟨n, hConv hn⟩

private theorem inl_initStateUnw_caller {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) (q : Query) :
    initStateUnw (entryProgForBody pTgt site.callerDefId) q =
      match initStateUnw (entryProgForBody pSrc site.callerDefId) q with
      | .error k => .error k
      | .ok u => .ok {
          active := { u.active with
                      locals := u.active.locals ++ replicateDead ctx.callee.locals.length },
          callStack := u.callStack,
          callerMem := u.callerMem
        } := by
  unfold initStateUnw initState entryProgForBody
  have hPw : pTgt.pointerWidthBits = pSrc.pointerWidthBits := by
    have h := congrArg Program.pointerWidthBits ctx.hPtgt; exact h
  have hPv : pTgt.mirProfileVersion = pSrc.mirProfileVersion := by
    have h := congrArg Program.mirProfileVersion ctx.hPtgt; exact h
  rw [hPw, hPv]
  cases (!Nat.beq pSrc.pointerWidthBits 64 || !Nat.beq pSrc.mirProfileVersion 1) with
  | true => rfl
  | false =>
    dsimp
    cases (!q.callerMem.allocations.isEmpty) with
    | true => rfl
    | false =>
      dsimp
      rw [ctx.hCaller, ctx_bodies_lookup_eq ctx]; dsimp
      have hNe1 := ctx_caller_bbs_nonEmpty ctx
      have hNe2 := ctx_caller'_bbs_nonEmpty ctx
      have hArg1 : Nat.blt ctx.caller.argumentCount ctx.caller.locals.length = true :=
        nat_lt_blt (ctx_caller_argLt ctx)
      have hArg2 : Nat.blt ctx.caller'.argumentCount ctx.caller'.locals.length = true := by
        dsimp [InlineUnwCtx.caller']
        rw [list_length_append]
        exact nat_lt_blt (Nat.lt_of_lt_of_le (ctx_caller_argLt ctx) (Nat.le_add_right _ _))
      have hSt1 := ctx_caller_storageInBounds ctx
      have hSt2 := ctx_caller'_storageInBounds ctx
      have hSup := ctx_caller'_locals_supported ctx
      have hP := ctx_caller'_paramTys ctx
      have hInit := ctx_caller'_initLocalsLoop ctx q.args
      rw [hNe1, hNe2, hArg1, hArg2, hSt1, hSt2, hSup, hP, hInit]
      dsimp
      cases ctx.caller.locals.all isSupportedScalarOrUnitTy with
      | false => rfl
      | true =>
        dsimp
        cases checkArgsMatch q.args ((ctx.caller.locals.drop 1).take ctx.caller.argumentCount) <;> rfl

private theorem inl_entry_fullSemanticEquiv {pSrc pTgt : Program} {site : UnwindInlineSite}
    (ctx : InlineUnwCtx pSrc pTgt site) (defId : DefId) :
    FullSemanticEquivUnw (entryProgForBody pSrc defId) (entryProgForBody pTgt defId) := by
  apply fullSemanticEquivUnw_of_fwd_stutter_sim (InlStateRel ctx)
  · intro q k
    cases hEq : Nat.beq defId site.callerDefId with
    | true =>
      have hd : defId = site.callerDefId := nat_beq_eq hEq
      subst hd
      rw [inl_initStateUnw_caller ctx q]
      cases initStateUnw (entryProgForBody pSrc site.callerDefId) q with
      | error k1 =>
        constructor <;> (intro h; injection h with he; subst he; rfl)
      | ok _ =>
        constructor <;> (intro h; cases h)
    | false =>
      have hNe : defId ≠ site.callerDefId := nat_ne_of_beq_false hEq
      have hSame : initStateUnw (entryProgForBody pTgt defId) q =
          initStateUnw (entryProgForBody pSrc defId) q := by
        unfold initStateUnw initState entryProgForBody
        have hPw : pTgt.pointerWidthBits = pSrc.pointerWidthBits := by
          have h := congrArg Program.pointerWidthBits ctx.hPtgt; exact h
        have hPv : pTgt.mirProfileVersion = pSrc.mirProfileVersion := by
          have h := congrArg Program.mirProfileVersion ctx.hPtgt; exact h
        rw [hPw, hPv, ctx_bodies_lookup_ne ctx hNe]
      rw [hSame]
  · intro q s₁ s₂ hI1 hI2
    cases hEq : Nat.beq defId site.callerDefId with
    | true =>
      have hd : defId = site.callerDefId := nat_beq_eq hEq
      subst hd
      rw [inl_initStateUnw_caller ctx q, hI1] at hI2
      injection hI2 with hs; subst hs
      let ⟨hWf, hCs, hDef, hBb, _⟩ := initStateUnw_wf hI1
      have hWfP : FrameWf pSrc s₁.active := hWf
      have hDef' : s₁.active.defId = site.callerDefId := hDef
      have hBbLt : s₁.active.blockIdx < ctx.bbOff := by
        rw [hBb]; exact Nat.lt_of_le_of_lt (Nat.zero_le _) (getElem?_some_lt ctx.hCallBb)
      cases s₁ with
      | mk act cs cm =>
        dsimp at hCs hWfP hDef' hBbLt; subst hCs
        exact InlStateRel.unfused (InlNormalFrameRel.caller hDef' hBbLt hWfP) InlStackRel.nil
    | false =>
      have hNe : defId ≠ site.callerDefId := nat_ne_of_beq_false hEq
      have hSame : initStateUnw (entryProgForBody pTgt defId) q =
          initStateUnw (entryProgForBody pSrc defId) q := by
        unfold initStateUnw initState entryProgForBody
        have hPw : pTgt.pointerWidthBits = pSrc.pointerWidthBits := by
          have h := congrArg Program.pointerWidthBits ctx.hPtgt; exact h
        have hPv : pTgt.mirProfileVersion = pSrc.mirProfileVersion := by
          have h := congrArg Program.mirProfileVersion ctx.hPtgt; exact h
        rw [hPw, hPv, ctx_bodies_lookup_ne ctx hNe]
      rw [hSame, hI1] at hI2; injection hI2 with hs; subst hs
      let ⟨_, hCs, hDef, _, _⟩ := initStateUnw_wf hI1
      have hDefNe : s₁.active.defId ≠ site.callerDefId := by rw [hDef]; exact hNe
      cases s₁ with
      | mk act cs cm =>
        dsimp at hCs hDefNe; subst hCs
        exact InlStateRel.unfused (InlNormalFrameRel.other hDefNe) InlStackRel.nil
  · intro s₁ s₂ s₁' hRel hStep
    have hOut := inl_step_fwd ctx hRel
    rw [entryProgForBody_evalStepUnw] at hStep
    rw [hStep] at hOut
    let ⟨s₂', hPlus, hRel'⟩ := hOut
    exact ⟨s₂', entryProgForBody_reachesPlusUnw hPlus, hRel'⟩
  · intro s₁ s₂ out hRel hDone
    have hOut := inl_step_fwd ctx hRel
    rw [entryProgForBody_evalStepUnw] at hDone
    rw [hDone] at hOut
    let ⟨s₂', hR, hEv⟩ := hOut
    exact ⟨s₂', entryProgForBody_reachesUnw hR,
           (entryProgForBody_evalStepUnw pTgt defId 0 s₂').trans hEv⟩
  · intro s₁ s₂ k hRel hFault
    have hOut := inl_step_fwd ctx hRel
    rw [entryProgForBody_evalStepUnw] at hFault
    rw [hFault] at hOut
    let ⟨s₂', hR, hEv⟩ := hOut
    exact ⟨s₂', entryProgForBody_reachesUnw hR,
           (entryProgForBody_evalStepUnw pTgt defId 0 s₂').trans hEv⟩

private theorem inlineWithUnwind_sound_slice3 {pSrc pTgt : Program}
    {site : UnwindInlineSite}
    (h : applyInlineWithUnwind pSrc site = some pTgt) :
    ProgramEquivUnw pSrc pTgt := by
  let ⟨ctx⟩ := unpack_applyInlineWithUnwind h
  have hScope : pSrc.scope = pTgt.scope := by
    have h1 := congrArg Program.scope ctx.hPtgt; exact h1.symm
  have hPw : pSrc.pointerWidthBits = pTgt.pointerWidthBits := by
    have h1 := congrArg Program.pointerWidthBits ctx.hPtgt; exact h1.symm
  have hPv : pSrc.mirProfileVersion = pTgt.mirProfileVersion := by
    have h1 := congrArg Program.mirProfileVersion ctx.hPtgt; exact h1.symm
  have hEnt : pSrc.entryDefId = pTgt.entryDefId := by
    have h1 := congrArg Program.entryDefId ctx.hPtgt; exact h1.symm
  have hLen : pSrc.bodies.length = pTgt.bodies.length := (ctx_bodies_length ctx).symm
  have hIds : pSrc.bodies.map (fun b => b.identity) = pTgt.bodies.map (fun b => b.identity) := by
    apply list_eq_of_getElem?
    · rw [list_length_map, list_length_map, hLen]
    · intro i
      rw [getElem?_map, getElem?_map]
      cases hEq : Nat.beq i site.callerDefId with
      | true =>
        have hi : i = site.callerDefId := nat_beq_eq hEq; subst hi
        rw [ctx.hCaller, ctx_bodies_lookup_eq ctx]; rfl
      | false =>
        rw [ctx_bodies_lookup_ne ctx (nat_ne_of_beq_false hEq)]
  have hUniq : bodiesHaveUniqueIdentities pSrc.bodies = bodiesHaveUniqueIdentities pTgt.bodies := by
    unfold bodiesHaveUniqueIdentities
    rw [hIds]
    have hAll : pSrc.bodies.all (fun b => !stringBeq b.identity "") =
        pTgt.bodies.all (fun b => !stringBeq b.identity "") := by
      have hMapAll : ∀ (bs : List Body),
          bs.all (fun b => !stringBeq b.identity "") =
            (bs.map (fun b => b.identity)).all (fun s => !stringBeq s "") := by
        intro bs
        induction bs with
        | nil => rfl
        | cons b rest ih => dsimp [List.all, List.map]; rw [ih]
      rw [hMapAll, hMapAll, hIds]
    rw [hAll]
  have hFull : FullSemanticEquivUnw pSrc pTgt := by
    have hEq1 : entryProgForBody pSrc pSrc.entryDefId = pSrc := by
      cases pSrc; rfl
    have hEq2 : entryProgForBody pTgt pSrc.entryDefId = pTgt := by
      rw [hEnt]; cases pTgt; rfl
    have hF := inl_entry_fullSemanticEquiv ctx pSrc.entryDefId
    rw [hEq1, hEq2] at hF
    exact hF
  refine ⟨hLen, hEnt, hPw, hPv, hScope, hUniq, hFull, ?_⟩
  intro defId
  cases hEq : Nat.beq defId site.callerDefId with
  | true =>
    have hd : defId = site.callerDefId := nat_beq_eq hEq; subst hd
    rw [ctx.hCaller, ctx_bodies_lookup_eq ctx]
    refine ⟨rfl, rfl, (ctx_caller'_bodyStaticAdmitted ctx).symm, ?_,
            inl_entry_fullSemanticEquiv ctx site.callerDefId⟩
    intro args
    unfold ValidEntryArgs
    rw [ctx_caller'_paramTys ctx]
  | false =>
    have hNe : defId ≠ site.callerDefId := nat_ne_of_beq_false hEq
    rw [ctx_bodies_lookup_ne ctx hNe]
    cases Trusted.MirSemantics.getElem? pSrc.bodies defId with
    | none => exact True.intro
    | some b =>
      have hAdm : BodyStaticAdmitted pSrc b = BodyStaticAdmitted pTgt b := by
        unfold BodyStaticAdmitted
        rw [hPw, hPv]
      exact ⟨rfl, rfl, hAdm, fun _ => Iff.rfl, inl_entry_fullSemanticEquiv ctx defId⟩

/-! ### Slice: Slice4_TraceAndVc.lean -/

-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.




/-! ### Part 1: Structural Reflexivity of `programEq` -/

private theorem listRel_refl {α : Type} {r : α → α → Bool}
    (hr : ∀ x : α, r x x = true) : ∀ xs : List α, listRel r xs xs = true
  | [] => rfl
  | x :: xs => by
    dsimp [listRel]
    rw [hr x, listRel_refl hr xs]; rfl

private theorem projElemEq_refl : ∀ (e : ProjectionElem), projElemEq e e = true
  | .deref | .unsupported => rfl
  | .field idx ty => by
    dsimp [projElemEq]
    rw [nat_beq_refl idx, mirTy_beq_refl ty]; rfl

private theorem placeEq_refl (p : Place) : placeEq p p = true := by
  unfold placeEq
  rw [nat_beq_refl p.localId, listRel_refl projElemEq_refl p.projection]; rfl

private theorem constLitEq_refl : ∀ (c : ConstLit), constLitEq c c = true
  | .zeroSized => rfl
  | .scalar b => beq_self_eq_true b

private theorem constOpEq_refl (c : ConstOperand) : constOpEq c c = true := by
  unfold constOpEq
  rw [mirTy_beq_refl c.ty, constLitEq_refl c.lit]; rfl

private theorem binOpEq_refl (op : BinOp) : binOpEq op op = true := by
  cases op <;> rfl

private theorem unOpEq_refl (op : UnOp) : unOpEq op op = true := by
  cases op <;> rfl

private theorem operandEq_refl : ∀ (o : Operand), operandEq o o = true
  | .copy p | .move p => placeEq_refl p
  | .constant c => constOpEq_refl c

private theorem rvalueEq_refl : ∀ (rv : Rvalue), rvalueEq rv rv = true
  | .use o => operandEq_refl o
  | .binaryOp op l r => by
    dsimp [rvalueEq]
    rw [binOpEq_refl op, operandEq_refl l, operandEq_refl r]; rfl
  | .unaryOp op o => by
    dsimp [rvalueEq]
    rw [unOpEq_refl op, operandEq_refl o]; rfl
  | .discriminant p => placeEq_refl p
  | .ref m p | .addressOf m p => by
    dsimp [rvalueEq]
    have hm : Mutability.beq m m = true := by cases m <;> rfl
    rw [hm, placeEq_refl p]; rfl
  | .aggregateTuple fs => listRel_refl operandEq_refl fs
  | .unsupported => rfl

private theorem stmtEq_refl : ∀ (s : StatementKind), stmtEq s s = true
  | .assign d rv => by
    dsimp [stmtEq]; rw [placeEq_refl d, rvalueEq_refl rv]; rfl
  | .storageLive i | .storageDead i => nat_beq_refl i
  | .nop | .unsupported => rfl

private theorem switchTargetsEq_refl (t : SwitchTargets) : switchTargetsEq t t = true := by
  unfold switchTargetsEq
  rw [nat_beq_refl t.otherwise]
  have hBr : ∀ (br : BitVec 128 × BasicBlockId),
      ((br.1 == br.1) && Nat.beq br.2 br.2) = true := by
    intro br
    rw [beq_self_eq_true br.1, nat_beq_refl br.2]; rfl
  rw [listRel_refl hBr t.branches]; rfl

private theorem unwindActionEq_refl : ∀ (u : UnwindAction), unwindActionEq u u = true
  | .continue_ | .unreachable | .terminate => rfl
  | .cleanup b => nat_beq_refl b

private theorem assertKindEq_refl : ∀ (m : AssertKind), assertKindEq m m = true
  | .overflow o => binOpEq_refl o
  | .overflowNeg | .divByZero | .remByZero | .boundsCheck
  | .misalignedPtrDeref | .nullPtrDeref | .unsupported => rfl

private theorem optBbEq_refl : ∀ (o : Option BasicBlockId), optBbEq o o = true
  | none => rfl
  | some b => nat_beq_refl b

private theorem termEq_refl : ∀ (t : TerminatorKind), termEq t t = true
  | .goto b => nat_beq_refl b
  | .switchInt d ts => by
    dsimp [termEq]; rw [operandEq_refl d, switchTargetsEq_refl ts]; rfl
  | .return_ | .unreachable | .unwindResume | .unsupported => rfl
  | .assert c e m t u => by
    dsimp [termEq]
    rw [operandEq_refl c, boolEq_refl e, assertKindEq_refl m,
        nat_beq_refl t, unwindActionEq_refl u]; rfl
  | .call fn as_ d t u => by
    dsimp [termEq]
    rw [nat_beq_refl fn, listRel_refl operandEq_refl as_,
        placeEq_refl d, optBbEq_refl t, unwindActionEq_refl u]; rfl

private theorem bbEq_refl (b : BasicBlock) : bbEq b b = true := by
  unfold bbEq
  rw [listRel_refl stmtEq_refl b.statements,
      termEq_refl b.terminator, boolEq_refl b.cleanup]; rfl

private theorem uint8_list_beq_refl : ∀ (xs : List UInt8), List.beq xs xs = true
  | [] => rfl
  | x :: xs => by
    dsimp [List.beq]
    rw [beq_self_eq_true x, uint8_list_beq_refl xs]; rfl

private theorem stringBeq_refl (s : String) : stringBeq s s = true :=
  uint8_list_beq_refl s.toByteArray.data.toList

private theorem bodyEq_refl (b : Body) : bodyEq b b = true := by
  unfold bodyEq
  rw [listRel_refl mirTy_beq_refl b.locals,
      nat_beq_refl b.argumentCount,
      listRel_refl bbEq_refl b.basicBlocks,
      boolEq_refl b.isUnsafe,
      stringBeq_refl b.identity]; rfl

private theorem scopeEq_refl (s : VerificationScope) : scopeEq s s = true := by
  cases s <;> rfl

private theorem programEq_refl (p : Program) : programEq p p = true := by
  unfold programEq
  rw [listRel_refl bodyEq_refl p.bodies,
      nat_beq_refl p.entryDefId,
      nat_beq_refl p.pointerWidthBits,
      nat_beq_refl p.mirProfileVersion,
      scopeEq_refl p.scope]; rfl

/-! ### Part 2: Step & Finite-Trace Soundness (`Theorems 2 & 4`) -/

private theorem unwindOptStep_sound_bidirectional_iff_slice4
    (pSrc : Program) (step : UnwindOptStep) (pTgt : Program)
    (hStep : checkUnwindOptStep pSrc step pTgt = true) :
    ProgramEquivUnw pSrc pTgt := by
  cases step with
  | inlineWithUnwind site =>
    unfold checkUnwindOptStep applyUnwindOptStep at hStep
    dsimp at hStep
    cases hApp : applyInlineWithUnwind pSrc site with
    | none => rw [hApp] at hStep; cases hStep
    | some pOut =>
      rw [hApp] at hStep
      have hEq : pOut = pTgt := programEq_eq hStep
      subst hEq
      exact inlineWithUnwind_sound_slice3 hApp
  | dischargeTrivialAssert defId bbIdx =>
    exact dischargeTrivialAssert_sound_slice2 pSrc pTgt defId bbIdx hStep
  | abortUnwindingCalls flags =>
    exact abortUnwindingCalls_sound_slice2 pSrc pTgt flags hStep
  | pruneDeadCleanupBlocks defId keep =>
    exact pruneDeadCleanupBlocks_sound_slice2 pSrc pTgt defId keep hStep

private theorem unwindOptTrace_sound_bidirectional_iff_slice4
    (pSrc : Program) (trace : UnwindOptTrace) (pTgt : Program)
    (hTrace : checkUnwindOptTrace pSrc trace pTgt = true) :
    ProgramEquivUnw pSrc pTgt := by
  induction trace generalizing pSrc with
  | nil =>
    dsimp [checkUnwindOptTrace] at hTrace
    have hEq : pSrc = pTgt := programEq_eq hTrace
    subst hEq
    exact programEquivUnw_refl pSrc
  | cons step rest ih =>
    dsimp [checkUnwindOptTrace] at hTrace
    cases hApp : applyUnwindOptStep pSrc step with
    | none => rw [hApp] at hTrace; cases hTrace
    | some pMid =>
      rw [hApp] at hTrace
      have hChk : checkUnwindOptStep pSrc step pMid = true := by
        unfold checkUnwindOptStep
        rw [hApp]
        exact programEq_refl pMid
      exact programEquivUnw_trans
        (unwindOptStep_sound_bidirectional_iff_slice4 pSrc step pMid hChk)
        (ih pMid hTrace)

/-! ### Part 3: `CrateTheoremUnw` / `UnitTheoremUnw` Transport & `Trusted.MirSemantics` Reduction (`Theorems 5 & 6`) -/

private theorem programEquivUnw_symm {p₁ p₂ : Program} (h : ProgramEquivUnw p₁ p₂) :
    ProgramEquivUnw p₂ p₁ := by
  let ⟨hLen, hEnt, hPw, hPv, hScope, hUniq, hFull, hBodies⟩ := h
  have symmFull : ∀ {a b : Program}, FullSemanticEquivUnw a b → FullSemanticEquivUnw b a := by
    intro a b hf
    let ⟨hw, hb, hr, hd, hs⟩ := hf
    exact ⟨fun q => (hw q).symm,
           fun q o => (hb q o).symm,
           fun q k => (hr q k).symm,
           fun q => (hd q).symm,
           fun q p => (hs q p).symm⟩
  refine ⟨hLen.symm, hEnt.symm, hPw.symm, hPv.symm, hScope.symm, hUniq.symm, symmFull hFull, ?_⟩
  intro defId
  have hB := hBodies defId
  cases h1 : Trusted.MirSemantics.getElem? p₁.bodies defId with
  | none =>
    rw [h1] at hB
    cases h2 : Trusted.MirSemantics.getElem? p₂.bodies defId with
    | none => exact True.intro
    | some _ => rw [h2] at hB; exact False.elim hB
  | some b₁ =>
    rw [h1] at hB
    cases h2 : Trusted.MirSemantics.getElem? p₂.bodies defId with
    | none => rw [h2] at hB; exact False.elim hB
    | some b₂ =>
      rw [h2] at hB
      let ⟨hId, hUns, hAdm, hArgs, hEF⟩ := hB
      exact ⟨hId.symm, hUns.symm, hAdm.symm, fun args => (hArgs args).symm, symmFull hEF⟩

private theorem programEquivUnw_programVerified_imp {p₁ p₂ : Program} {specs : Specs}
    (hEq : ProgramEquivUnw p₁ p₂)
    (hPropImp : specs.property p₁ → specs.property p₂)
    (hV1 : ProgramVerifiedUnw p₁ specs) :
    ProgramVerifiedUnw p₂ specs := by
  let ⟨hLen, hEnt, hPw, hPv, _, hUniq, _, hBodies⟩ := hEq
  let ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hV1
  have hIsEmpty : p₁.bodies.isEmpty = p₂.bodies.isEmpty := by
    cases hb1 : p₁.bodies with
    | nil =>
      rw [hb1] at hLen
      cases hb2 : p₂.bodies with
      | nil => rfl
      | cons _ _ => rw [hb2] at hLen; cases hLen
    | cons _ _ =>
      rw [hb1] at hLen
      cases hb2 : p₂.bodies with
      | nil => rw [hb2] at hLen; cases hLen
      | cons _ _ => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hPropImp h7⟩
  · rw [← hPw]; exact h1
  · rw [← hPv]; exact h2
  · rw [← hIsEmpty]; exact h3
  · rw [← hEnt, ← hLen]; exact h4
  · rw [← hUniq]; exact h5
  · intro defId b₂ hGet2
    have hB := hBodies defId
    cases hGet1 : Trusted.MirSemantics.getElem? p₁.bodies defId with
    | none => rw [hGet1, hGet2] at hB; exact False.elim hB
    | some b₁ =>
      rw [hGet1, hGet2] at hB
      let ⟨hId, hUns, hAdm, hArgs, hEF⟩ := hB
      let ⟨_, hAdm1, hWf1⟩ := h6 defId b₁ hGet1
      refine ⟨hGet2, ?_, ?_⟩
      · rw [← hAdm]; exact hAdm1
      · intro args hVal2 hPre2
        have hVal1 : ValidEntryArgs b₁ args := (hArgs args).mpr hVal2
        have hPre1 : b₁.isUnsafe = true → specs.safety b₁.identity args := by
          intro hU1
          rw [hId]
          apply hPre2
          rw [← hUns]; exact hU1
        exact (hEF.1 { args := args }).mp (hWf1 args hVal1 hPre1)

private theorem programEquivUnw_programVerified_iff {p₁ p₂ : Program} {specs : Specs}
    (hEq : ProgramEquivUnw p₁ p₂)
    (hSpec : SpecsPropertyUnwInvariant specs) :
    ProgramVerifiedUnw p₁ specs ↔ ProgramVerifiedUnw p₂ specs :=
  ⟨programEquivUnw_programVerified_imp hEq (hSpec p₁ p₂ hEq).mp,
   programEquivUnw_programVerified_imp (programEquivUnw_symm hEq) (hSpec p₁ p₂ hEq).mpr⟩

private theorem unwindOptTrace_reduces_to_trusted_mir_slice4
    (pSrc : Program) (trace : UnwindOptTrace) (pFlat : Program)
    (specs : Specs)
    (hTrace : checkUnwindOptTrace pSrc trace pFlat = true)
    (hBase : isBaseMirProgram pFlat = true)
    (hSpec : SpecsPropertyUnwInvariant specs) :
    (∀ q : Query, WellFormedUnw pSrc q ↔ WellFormed pFlat q) ∧
    (∀ q : Query, ∀ out : TerminalOut,
      BehaviorUnw pSrc q (embedTerminalOut out) ↔ Behavior pFlat q out) ∧
    (∀ q : Query, ∀ k : FaultKind,
      ReachesResultUnw pSrc q (.fault k) ↔ ReachesResult pFlat q (.fault k)) ∧
    (∀ q : Query, DivergesUnw pSrc q ↔ Diverges pFlat q) ∧
    (∀ q : Query, ∀ post : TerminalOut → Prop,
      SatisfiesPostUnw pSrc q (liftTerminalPost post) ↔
        SatisfiesPost pFlat q post) ∧
    (CrateTheoremUnw ⟨pSrc, specs⟩ ↔ CrateTheorem ⟨pFlat, specs⟩) ∧
    (UnitTheoremUnw ⟨pSrc, specs⟩ ↔ UnitTheorem ⟨pFlat, specs⟩) := by
  have hEq := unwindOptTrace_sound_bidirectional_iff_slice4 pSrc trace pFlat hTrace
  have hCE := (unwind_conservative_extension_exact_slice1 pFlat).2 hBase
  let ⟨hWfCE, hBehCE, _, hFltCE, hDivCE, hPostCE, hCrateUnitCE⟩ := hCE
  let ⟨hCrateCE, hUnitCE⟩ := hCrateUnitCE ⟨pFlat, specs⟩ rfl
  have hFull := hEq.2.2.2.2.2.2.1
  have hScope := hEq.2.2.2.2.1
  have hPV := programEquivUnw_programVerified_iff hEq hSpec
  have hCrateEq : CrateTheoremUnw ⟨pSrc, specs⟩ ↔ CrateTheoremUnw ⟨pFlat, specs⟩ := by
    unfold CrateTheoremUnw; dsimp
    rw [hScope]
    exact ⟨fun ⟨hs, hp⟩ => ⟨hs, hPV.mp hp⟩, fun ⟨hs, hp⟩ => ⟨hs, hPV.mpr hp⟩⟩
  have hUnitEq : UnitTheoremUnw ⟨pSrc, specs⟩ ↔ UnitTheoremUnw ⟨pFlat, specs⟩ := by
    unfold UnitTheoremUnw; dsimp
    rw [hScope]
    exact ⟨fun ⟨hs, hp⟩ => ⟨hs, hPV.mp hp⟩, fun ⟨hs, hp⟩ => ⟨hs, hPV.mpr hp⟩⟩
  exact ⟨
    fun q => (hFull.1 q).trans (hWfCE q),
    fun q out => (hFull.2.1 q (embedTerminalOut out)).trans (hBehCE q out),
    fun q k => (hFull.2.2.1 q k).trans (hFltCE q k),
    fun q => (hFull.2.2.2.1 q).trans (hDivCE q),
    fun q post => (hFull.2.2.2.2 q (liftTerminalPost post)).trans (hPostCE q post),
    hCrateEq.trans hCrateCE,
    hUnitEq.trans hUnitCE
  ⟩

private theorem unwindOptTrace_then_optPipeline_vc_transport_slice4
    (pSrc : Program) (trace : UnwindOptTrace) (pFlat pOpt : Program)
    (hTrace : checkUnwindOptTrace pSrc trace pFlat = true)
    (hBase : isBaseMirProgram pFlat = true)
    (hPostOpt : FullSemanticEquivBase pFlat pOpt) :
    (∀ q : Query, WellFormedUnw pSrc q ↔ WellFormed pOpt q) ∧
    (∀ q : Query, ∀ out : TerminalOut,
      BehaviorUnw pSrc q (embedTerminalOut out) ↔ Behavior pOpt q out) ∧
    (∀ q : Query, ∀ k : FaultKind,
      ReachesResultUnw pSrc q (.fault k) ↔ ReachesResult pOpt q (.fault k)) ∧
    (∀ q : Query, DivergesUnw pSrc q ↔ Diverges pOpt q) ∧
    (∀ q : Query, ∀ post : TerminalOut → Prop,
      SatisfiesPostUnw pSrc q (liftTerminalPost post) ↔
        SatisfiesPost pOpt q post) := by
  have hEq := unwindOptTrace_sound_bidirectional_iff_slice4 pSrc trace pFlat hTrace
  have hCE := (unwind_conservative_extension_exact_slice1 pFlat).2 hBase
  let ⟨hWfCE, hBehCE, _, hFltCE, hDivCE, hPostCE, _⟩ := hCE
  let ⟨hWfOpt, hBehOpt, hFltOpt, hDivOpt, hPostOpt'⟩ := hPostOpt
  have hFull := hEq.2.2.2.2.2.2.1
  exact ⟨
    fun q => ((hFull.1 q).trans (hWfCE q)).trans (hWfOpt q),
    fun q out => ((hFull.2.1 q (embedTerminalOut out)).trans (hBehCE q out)).trans (hBehOpt q out),
    fun q k => ((hFull.2.2.1 q k).trans (hFltCE q k)).trans (hFltOpt q k),
    fun q => ((hFull.2.2.2.1 q).trans (hDivCE q)).trans (hDivOpt q),
    fun q post => ((hFull.2.2.2.2 q (liftTerminalPost post)).trans (hPostCE q post)).trans (hPostOpt' q post)
  ⟩

/-! ## Part III: Core Target Theorems (Frozen Statement Signatures) -/

/-- **Theorem 1 (`unwind_conservative_extension_exact`):**
`M_unwind` is an exact conservative extension of unmodified
`Trusted.MirSemantics`:
1. Single-frame state embedding and projection round-trip exactly;
2. On every `isBaseMirProgram p = true` program, `WellFormedUnw`, `BehaviorUnw`
   (including unreachability of `.aborted`), `ReachesResultUnw (.fault k)`,
   `DivergesUnw`, `SatisfiesPostUnw`, `ProgramVerifiedUnw`, `CrateTheoremUnw`,
   and `UnitTheoremUnw` coincide bidirectionally (`↔`) with unmodified
   `Trusted.MirSemantics`. -/
theorem unwind_conservative_extension_exact (p : Program) :
    (∀ s : State, ∀ u : UnwindState,
      embedStateUnw? s = some u → projectStateUnw? u = some s) ∧
    (isBaseMirProgram p = true →
      (∀ q : Query, WellFormedUnw p q ↔ WellFormed p q) ∧
      (∀ q : Query, ∀ out : TerminalOut,
        BehaviorUnw p q (embedTerminalOut out) ↔ Behavior p q out) ∧
      (∀ q : Query, ∀ mem : CallerMemory, ¬ BehaviorUnw p q (.aborted mem)) ∧
      (∀ q : Query, ∀ k : FaultKind,
        ReachesResultUnw p q (.fault k) ↔ ReachesResult p q (.fault k)) ∧
      (∀ q : Query, DivergesUnw p q ↔ Diverges p q) ∧
      (∀ q : Query, ∀ post : TerminalOut → Prop,
        SatisfiesPostUnw p q (liftTerminalPost post) ↔ SatisfiesPost p q post) ∧
      (∀ c : Crate, c.program = p →
        (CrateTheoremUnw c ↔ CrateTheorem c) ∧
        (UnitTheoremUnw c ↔ UnitTheorem c))) := by
  exact unwind_conservative_extension_exact_slice1 p

/-- **Theorem 2 (`unwindOptStep_sound_bidirectional_iff`):**
Every accepted `UnwindOptStep` (`.inlineWithUnwind`, `.dischargeTrivialAssert`,
`.abortUnwindingCalls`, or `.pruneDeadCleanupBlocks`) preserves full
program-wide bidirectional semantic equivalence (`ProgramEquivUnw`, including
all entry bodies, all terminal outcomes `.returned`/`.unwound`/`.aborted`,
exact fault kinds `.undefined` vs. `.unsupported`, and constructive
`DivergesUnw`). -/
theorem unwindOptStep_sound_bidirectional_iff
    (pSrc : Program) (step : UnwindOptStep) (pTgt : Program)
    (hStep : checkUnwindOptStep pSrc step pTgt = true) :
    ProgramEquivUnw pSrc pTgt := by
  exact unwindOptStep_sound_bidirectional_iff_slice4 pSrc step pTgt hStep

/-- **Theorem 3 (`panicAbortEntryTransform_refines_unwound_to_aborted`):**
Applying `-C panic=abort` ABI enforcement (`checkPanicAbortEntryTransform`) to
the entry body preserves `WellFormedUnw`, all `.returned` outputs, all exact
`.fault` kinds, and `DivergesUnw` bidirectionally (`↔`), while converting every
top-level `.unwound mem` outcome cleanly into `.aborted mem` (and leaving
`pTgt` with zero reachable `.unwound` outcomes). -/
theorem panicAbortEntryTransform_refines_unwound_to_aborted
    (pSrc pTgt : Program)
    (hAbort : checkPanicAbortEntryTransform pSrc pTgt = true) :
    (∀ q : Query, WellFormedUnw pSrc q ↔ WellFormedUnw pTgt q) ∧
    (∀ q : Query, ∀ out : Out,
      BehaviorUnw pSrc q (.returned out) ↔ BehaviorUnw pTgt q (.returned out)) ∧
    (∀ q : Query, ∀ mem : CallerMemory,
      (BehaviorUnw pSrc q (.unwound mem) ∨ BehaviorUnw pSrc q (.aborted mem)) ↔
        BehaviorUnw pTgt q (.aborted mem)) ∧
    (∀ q : Query, ∀ mem : CallerMemory, ¬ BehaviorUnw pTgt q (.unwound mem)) ∧
    (∀ q : Query, ∀ k : FaultKind,
      ReachesResultUnw pSrc q (.fault k) ↔ ReachesResultUnw pTgt q (.fault k)) ∧
    (∀ q : Query, DivergesUnw pSrc q ↔ DivergesUnw pTgt q) := by
  exact panicAbortEntryTransform_refines_unwound_to_aborted_slice1 pSrc pTgt hAbort

/-- **Theorem 4 (`unwindOptTrace_sound_bidirectional_iff`):**
Arbitrary finite traces of certified `UnwindOptStep`s compose transitively to
preserve `ProgramEquivUnw pSrc pTgt`. -/
theorem unwindOptTrace_sound_bidirectional_iff
    (pSrc : Program) (trace : UnwindOptTrace) (pTgt : Program)
    (hTrace : checkUnwindOptTrace pSrc trace pTgt = true) :
    ProgramEquivUnw pSrc pTgt := by
  exact unwindOptTrace_sound_bidirectional_iff_slice4 pSrc trace pTgt hTrace

/-- **Theorem 5 (`unwindOptTrace_reduces_to_trusted_mir`):**
Whenever a finite certified unwind-lowering trace `checkUnwindOptTrace pSrc trace pFlat = true`
terminates in a base-MIR program `isBaseMirProgram pFlat = true`, verification
of `pSrc` in `M_unwind` reduces bidirectionally (`↔`) directly onto Anneal's
unmodified `Trusted.MirSemantics` (`WellFormed`, `Behavior`, `ReachesResult`,
`Diverges`, `SatisfiesPost`, `CrateTheorem`, and `UnitTheorem` under
`SpecsPropertyUnwInvariant`). -/
theorem unwindOptTrace_reduces_to_trusted_mir
    (pSrc : Program) (trace : UnwindOptTrace) (pFlat : Program)
    (specs : Specs)
    (hTrace : checkUnwindOptTrace pSrc trace pFlat = true)
    (hBase : isBaseMirProgram pFlat = true)
    (hSpec : SpecsPropertyUnwInvariant specs) :
    (∀ q : Query, WellFormedUnw pSrc q ↔ WellFormed pFlat q) ∧
    (∀ q : Query, ∀ out : TerminalOut,
      BehaviorUnw pSrc q (embedTerminalOut out) ↔ Behavior pFlat q out) ∧
    (∀ q : Query, ∀ k : FaultKind,
      ReachesResultUnw pSrc q (.fault k) ↔ ReachesResult pFlat q (.fault k)) ∧
    (∀ q : Query, DivergesUnw pSrc q ↔ Diverges pFlat q) ∧
    (∀ q : Query, ∀ post : TerminalOut → Prop,
      SatisfiesPostUnw pSrc q (liftTerminalPost post) ↔
        SatisfiesPost pFlat q post) ∧
    (CrateTheoremUnw ⟨pSrc, specs⟩ ↔ CrateTheorem ⟨pFlat, specs⟩) ∧
    (UnitTheoremUnw ⟨pSrc, specs⟩ ↔ UnitTheorem ⟨pFlat, specs⟩) := by
  exact unwindOptTrace_reduces_to_trusted_mir_slice4 pSrc trace pFlat specs hTrace hBase hSpec

/-- **Theorem 6 (`unwindOptTrace_then_optPipeline_vc_transport`):**
Vertical composition: any certified `UnwindOptTrace` lowering `pSrc` to a
base-MIR `pFlat` followed by any certified post-lowering intraprocedural
equivalence `FullSemanticEquivBase` (e.g., `F1-5`..`F1-9`) transports `M_unwind`
verification obligations on `pSrc` directly onto unmodified
`Trusted.MirSemantics` on `pOpt`. -/
theorem unwindOptTrace_then_optPipeline_vc_transport
    (pSrc : Program) (trace : UnwindOptTrace) (pFlat pOpt : Program)
    (hTrace : checkUnwindOptTrace pSrc trace pFlat = true)
    (hBase : isBaseMirProgram pFlat = true)
    (hPostOpt : FullSemanticEquivBase pFlat pOpt) :
    (∀ q : Query, WellFormedUnw pSrc q ↔ WellFormed pOpt q) ∧
    (∀ q : Query, ∀ out : TerminalOut,
      BehaviorUnw pSrc q (embedTerminalOut out) ↔ Behavior pOpt q out) ∧
    (∀ q : Query, ∀ k : FaultKind,
      ReachesResultUnw pSrc q (.fault k) ↔ ReachesResult pOpt q (.fault k)) ∧
    (∀ q : Query, DivergesUnw pSrc q ↔ Diverges pOpt q) ∧
    (∀ q : Query, ∀ post : TerminalOut → Prop,
      SatisfiesPostUnw pSrc q (liftTerminalPost post) ↔
        SatisfiesPost pOpt q post) := by
  exact unwindOptTrace_then_optPipeline_vc_transport_slice4 pSrc trace pFlat pOpt hTrace hBase hPostOpt

/-! ## Part IV: Bounded-Fuel Adequacy, Ten Sharpness Counterexamples (`CE1`--`CE10`), & Multi-Pass Unwind-Reduction Witness (`0` `sorry`) -/

/-- Bounded-fuel executor for `M_unwind`. -/
noncomputable def execFuelUnw (p : Program) :
    Nat → UnwindState → Option (StepResult UnwindState UnwindOut)
  | 0, _ => none
  | fuel + 1, s =>
    match evalStepUnw p 0 s with
    | .step s' => execFuelUnw p fuel s'
    | .done out => some (.done out)
    | .fault k => some (.fault k)

/-- Bounded-fuel execution from `(p, q)` in `M_unwind`. -/
noncomputable def execUnw (p : Program) (q : Query) (fuel : Nat) :
    Option (StepResult UnwindState UnwindOut) :=
  match initStateUnw p q with
  | .error k => some (.fault k)
  | .ok s₀ => execFuelUnw p fuel s₀

/-- Helper: `ReachesUnw` head prepend. -/
theorem reachesUnw_head {p : Program} {s₁ s₂ s₃ : UnwindState}
    (hStep : StepUnw p s₁ (.step s₂)) (hRest : ReachesUnw p s₂ s₃) :
    ReachesUnw p s₁ s₃ := by
  induction hRest with
  | refl => exact ReachesUnw.tail (ReachesUnw.refl s₁) hStep
  | tail _ hLast ih => exact ReachesUnw.tail ih hLast

/-- Determinism of `evalStepUnw` -> `ReachesUnw` head step. -/
theorem reachesUnw_head_det {p : Program} {s₁ s₂ s₃ : UnwindState}
    (hStep : evalStepUnw p 0 s₁ = .step s₂) (hRest : ReachesUnw p s₂ s₃) :
    ReachesUnw p s₁ s₃ :=
  reachesUnw_head ⟨0, rfl, hStep⟩ hRest

/-- Soundness of `execFuelUnw` with respect to `ReachesUnw` and `StepUnw`. -/
theorem execFuelUnw_sound (p : Program) :
    ∀ (fuel : Nat) (s₀ : UnwindState) (res : StepResult UnwindState UnwindOut),
      execFuelUnw p fuel s₀ = some res →
      ∃ s : UnwindState, ReachesUnw p s₀ s ∧ StepUnw p s res
  | 0, _, _, h => by cases h
  | fuel + 1, s₀, res, h => by
    unfold execFuelUnw at h
    cases hEv : evalStepUnw p 0 s₀ with
    | step s₁ =>
      rw [hEv] at h
      let ⟨s, hR, hS⟩ := execFuelUnw_sound p fuel s₁ res h
      exact ⟨s, reachesUnw_head_det hEv hR, hS⟩
    | done out =>
      rw [hEv] at h
      injection h with hEq
      subst hEq
      exact ⟨s₀, ReachesUnw.refl s₀, ⟨0, rfl, hEv⟩⟩
    | fault k =>
      rw [hEv] at h
      injection h with hEq
      subst hEq
      exact ⟨s₀, ReachesUnw.refl s₀, ⟨0, rfl, hEv⟩⟩

/-- Soundness of `execUnw` with respect to `ReachesResultUnw`. -/
theorem execUnw_sound {p : Program} {q : Query} {fuel : Nat}
    {res : StepResult UnwindState UnwindOut}
    (h : execUnw p q fuel = some res) :
    ReachesResultUnw p q res := by
  unfold execUnw at h
  unfold ReachesResultUnw
  cases hInit : initStateUnw p q with
  | error k =>
    rw [hInit] at h
    injection h with hEq
    exact hEq.symm
  | ok s₀ =>
    rw [hInit] at h
    exact execFuelUnw_sound p fuel s₀ res h

/-- Determinism of `evalStepUnw` implies any `execFuelUnw = some (.done out)`
rules out all faults and forces every reached terminal outcome to equal `out`. -/
theorem execFuelUnw_done_det (p : Program) :
    ∀ (fuel : Nat) (s₀ : UnwindState) (out : UnwindOut),
      execFuelUnw p fuel s₀ = some (.done out) →
      (∀ s : UnwindState, ReachesUnw p s₀ s →
        ∀ k : FaultKind, ¬ StepUnw p s (.fault k)) ∧
      (∀ s : UnwindState, ReachesUnw p s₀ s →
        ∀ out' : UnwindOut, StepUnw p s (.done out') → out' = out)
  | 0, _, _, h => by cases h
  | fuel + 1, s₀, out, h => by
    unfold execFuelUnw at h
    cases hEv : evalStepUnw p 0 s₀ with
    | fault _ => rw [hEv] at h; cases h
    | done out₀ =>
      rw [hEv] at h
      injection h with hEq
      injection hEq with hOutEq
      subst hOutEq
      have hOnly0 : ∀ s, ReachesUnw p s₀ s → s = s₀ := by
        intro s hR
        induction hR with
        | refl => rfl
        | tail _ hStep ih =>
          subst ih
          let ⟨c, hc, hStepEq⟩ := hStep
          cases hc
          rw [hEv] at hStepEq
          cases hStepEq
      refine ⟨?_, ?_⟩
      · intro s hR k hF
        have hEq := hOnly0 s hR
        subst hEq
        let ⟨c, hc, hFEq⟩ := hF
        cases hc
        rw [hEv] at hFEq
        cases hFEq
      · intro s hR out' hD
        have hEq := hOnly0 s hR
        subst hEq
        let ⟨c, hc, hDEq⟩ := hD
        cases hc
        rw [hEv] at hDEq
        injection hDEq with hO
        exact hO.symm
    | step s₁ =>
      rw [hEv] at h
      let ⟨ihNoF, ihDet⟩ := execFuelUnw_done_det p fuel s₁ out h
      have hStepFrom0 : ∀ s, ReachesUnw p s₀ s → s = s₀ ∨ ReachesUnw p s₁ s := by
        intro s hR
        induction hR with
        | refl => exact Or.inl rfl
        | tail _ hSt ih =>
          cases ih with
          | inl hEq0 =>
            subst hEq0
            let ⟨c, hc, hStEq⟩ := hSt
            cases hc
            rw [hEv] at hStEq
            injection hStEq with hEq1
            subst hEq1
            exact Or.inr (ReachesUnw.refl s₁)
          | inr hR1 =>
            exact Or.inr (ReachesUnw.tail hR1 hSt)
      refine ⟨?_, ?_⟩
      · intro s hR k hF
        cases hStepFrom0 s hR with
        | inl hEq0 =>
          subst hEq0
          let ⟨c, hc, hFEq⟩ := hF
          cases hc
          rw [hEv] at hFEq
          cases hFEq
        | inr hR1 => exact ihNoF s hR1 k hF
      · intro s hR out' hD
        cases hStepFrom0 s hR with
        | inl hEq0 =>
          subst hEq0
          let ⟨c, hc, hDEq⟩ := hD
          cases hc
          rw [hEv] at hDEq
          cases hDEq
        | inr hR1 => exact ihDet s hR1 out' hD

/-- Positive adequacy canary for `M_unwind`. -/
theorem positiveCanaryUnw_of_exec {p : Program} {q : Query} {fuel : Nat}
    {out : UnwindOut} (h : execUnw p q fuel = some (.done out)) :
    WellFormedUnw p q ∧ BehaviorUnw p q out ∧
      (∀ out' : UnwindOut, BehaviorUnw p q out' → out' = out) := by
  have hBeh : BehaviorUnw p q out := execUnw_sound h
  unfold execUnw at h
  cases hInit : initStateUnw p q with
  | error _ => rw [hInit] at h; cases h
  | ok s₀ =>
    rw [hInit] at h
    let ⟨hNoF, hDet⟩ := execFuelUnw_done_det p fuel s₀ out h
    refine ⟨⟨⟨s₀, hInit, fun _ _ => ⟨0, rfl⟩⟩, ?_⟩, hBeh, ?_⟩
    · intro k hF
      unfold ReachesResultUnw at hF
      rw [hInit] at hF
      let ⟨s, hR, hS⟩ := hF
      exact hNoF s hR k hS
    · intro out' hB'
      unfold BehaviorUnw ReachesResultUnw at hB'
      rw [hInit] at hB'
      let ⟨s, hR, hS⟩ := hB'
      exact hDet s hR out' hS

/-- Negative adequacy canary for `M_unwind`. -/
theorem negativeCanaryUnw_of_exec {p : Program} {q : Query} {fuel : Nat}
    {k : FaultKind} (h : execUnw p q fuel = some (.fault k)) :
    ReachesResultUnw p q (.fault k) ∧ ¬ WellFormedUnw p q := by
  have hF : ReachesResultUnw p q (.fault k) := execUnw_sound h
  exact ⟨hF, fun hWf => hWf.2 k hF⟩

/-- Helper scalar constant builders for Part IV counterexamples. -/
noncomputable def u32Const (n : Nat) : Operand :=
  .constant { ty := .int .i32 false, lit := .scalar (BitVec.ofNat 128 n) }

noncomputable def boolConst (b : Bool) : Operand :=
  .constant { ty := .bool, lit := .scalar (BitVec.ofNat 128 (if b then 1 else 0)) }

noncomputable def emptyQuery : Query := { args := [], callerMem := ⟨[]⟩ }

/-- **CE1:** Executing `TerminatorKind.return_` inside a `cleanup = true` basic
block faults `.fault .unsupported` (`ControlFlow.lean:74`). -/
noncomputable def progCe1ReturnInCleanup : Program where
  bodies := [{
    locals := [.int .i32 false]
    argumentCount := 0
    basicBlocks := [{
      statements := [.assign { localId := 0, projection := [] } (.use (u32Const 7))]
      terminator := .return_
      cleanup := true
    }]
  }]
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1

theorem ce1_return_in_cleanup_faults_unsupported :
    ReachesResultUnw progCe1ReturnInCleanup emptyQuery (.fault .unsupported) ∧
    ¬ WellFormedUnw progCe1ReturnInCleanup emptyQuery :=
  negativeCanaryUnw_of_exec (fuel := 4) (by rfl)

/-- **CE2:** Executing `TerminatorKind.unwindResume` inside a `cleanup = false`
basic block faults `.fault .unsupported` (`ControlFlow.lean:74`). -/
noncomputable def progCe2UnwindResumeInNormalBlock : Program where
  bodies := [{
    locals := [.int .i32 false]
    argumentCount := 0
    basicBlocks := [{
      statements := []
      terminator := .unwindResume
      cleanup := false
    }]
  }]
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1

theorem ce2_unwind_resume_in_normal_block_faults_unsupported :
    ReachesResultUnw progCe2UnwindResumeInNormalBlock emptyQuery (.fault .unsupported) ∧
    ¬ WellFormedUnw progCe2UnwindResumeInNormalBlock emptyQuery :=
  negativeCanaryUnw_of_exec (fuel := 3) (by rfl)

/-- **CE3:** Unwinding out of a callee across `UnwindAction.unreachable` faults
`.fault .undefined` (UB, `ControlFlow.lean:47`), AND `checkNoUnwindSummary`
rejects certifying the genuinely unwinding callee as `noUnwind`. -/
noncomputable def bodyUnwindingCallee : Body where
  locals := [.int .i32 false]
  argumentCount := 0
  basicBlocks := [
    { statements := []
      terminator := .assert (boolConst false) true .overflowNeg 1 (.cleanup 2)
      cleanup := false },
    { statements := [.assign { localId := 0, projection := [] } (.use (u32Const 1))]
      terminator := .return_
      cleanup := false },
    { statements := []
      terminator := .unwindResume
      cleanup := true }
  ]

noncomputable def progCe3UnwindAcrossUnreachable : Program where
  bodies := [
    { locals := [.int .i32 false]
      argumentCount := 0
      basicBlocks := [
        { statements := []
          terminator := .call 1 [] { localId := 0, projection := [] } (some 1) .unreachable
          cleanup := false },
        { statements := []
          terminator := .return_
          cleanup := false }
      ] },
    bodyUnwindingCallee
  ]
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1

theorem ce3_unwind_across_unreachable_is_ub_and_summary_rejected :
    ReachesResultUnw progCe3UnwindAcrossUnreachable emptyQuery (.fault .undefined) ∧
    ¬ WellFormedUnw progCe3UnwindAcrossUnreachable emptyQuery ∧
    checkNoUnwindSummary progCe3UnwindAcrossUnreachable [false, true] = false := by
  exact ⟨(negativeCanaryUnw_of_exec (fuel := 8) (by rfl)).1,
    (negativeCanaryUnw_of_exec (fuel := 8) (by rfl)).2, rfl⟩

/-- **CE4:** Double-panic / `UnwindAction.terminate` inside a cleanup pad
transitions cleanly to `.aborted` (distinct from `.unwound` and `.fault`). -/
noncomputable def progCe4DoublePanicTerminate : Program where
  bodies := [{
    locals := [.int .i32 false]
    argumentCount := 0
    basicBlocks := [
      { statements := []
        terminator := .assert (boolConst false) true .overflowNeg 1 (.cleanup 2)
        cleanup := false },
      { statements := [.assign { localId := 0, projection := [] } (.use (u32Const 0))]
        terminator := .return_
        cleanup := false },
      { statements := []
        terminator := .assert (boolConst false) true .overflowNeg 2 .terminate
        cleanup := true }
    ]
  }]
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1

theorem ce4_double_panic_terminate_produces_aborted_distinct_from_unwound :
    WellFormedUnw progCe4DoublePanicTerminate emptyQuery ∧
    BehaviorUnw progCe4DoublePanicTerminate emptyQuery (.aborted ⟨[]⟩) ∧
    ¬ BehaviorUnw progCe4DoublePanicTerminate emptyQuery (.unwound ⟨[]⟩) := by
  let ⟨hWf, hBeh, hDet⟩ :=
    positiveCanaryUnw_of_exec (p := progCe4DoublePanicTerminate)
      (q := emptyQuery) (fuel := 6) (out := .aborted ⟨[]⟩) (by rfl)
  exact ⟨hWf, hBeh, fun hUnw => by cases hDet (.unwound ⟨[]⟩) hUnw⟩

/-- **CE5 (Live `abort_unwinding_calls.rs:140` `hasStorageAnnotation` UB-Erasure
Sharpness):**
When an unreachable `cleanup = true` block holds the SOLE `StorageDead 1`
annotation for local `_1`, local `_1` starts `.dead` in `progCe5Src` (causing
writing `_1 = 9` in `bb0` to fault `.fault .undefined`), whereas naive
`remove_dead_blocks` dropping `bb1` flips `hasStorageAnnotation body 1` from
`true` to `false` so `progCe5NaiveDrop` returns `9` cleanly. Our certified
`checkPruneDeadCleanupBlocks` catches the `hasStorageAnnotation` flip and
rejects the unsound pruning (`= false`). -/
noncomputable def progCe5Src : Program where
  bodies := [{
    locals := [.int .i32 false, .int .i32 false]
    argumentCount := 0
    basicBlocks := [
      { statements := [
          .assign { localId := 1, projection := [] } (.use (u32Const 9)),
          .assign { localId := 0, projection := [] }
            (.use (.copy { localId := 1, projection := [] }))
        ]
        terminator := .return_
        cleanup := false },
      { statements := [.storageDead 1]
        terminator := .unwindResume
        cleanup := true }
    ]
  }]
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1

noncomputable def progCe5NaiveDrop : Program where
  bodies := [{
    locals := [.int .i32 false, .int .i32 false]
    argumentCount := 0
    basicBlocks := [
      { statements := [
          .assign { localId := 1, projection := [] } (.use (u32Const 9)),
          .assign { localId := 0, projection := [] }
            (.use (.copy { localId := 1, projection := [] }))
        ]
        terminator := .return_
        cleanup := false }
    ]
  }]
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1

theorem ce5_dead_cleanup_storage_annotation_flip_erases_ub_and_rejected :
    ReachesResultUnw progCe5Src emptyQuery (.fault .undefined) ∧
    BehaviorUnw progCe5NaiveDrop emptyQuery
      (.returned ⟨.scalar ⟨.i32, false, BitVec.ofNat 128 9⟩, ⟨[]⟩⟩) ∧
    checkPruneDeadCleanupBlocks progCe5Src 0 [0] progCe5NaiveDrop = false := by
  exact ⟨(negativeCanaryUnw_of_exec (fuel := 6) (by rfl)).1,
    (positiveCanaryUnw_of_exec (fuel := 6) (by rfl)).2.1, rfl⟩

/-- **CE6:** When a callee unwinds into a caller's `.cleanup padBb`, the
interrupted call's destination place `dst` (`_1`) is NOT written — so reading
`_1` inside `padBb` faults `.fault .undefined` (UB), whereas a clean cleanup pad
finishes `.done (.unwound ⟨[]⟩)`. -/
noncomputable def progCe6CleanupReadsUnwrittenDst : Program where
  bodies := [
    { locals := [.int .i32 false, .int .i32 false]
      argumentCount := 0
      basicBlocks := [
        { statements := []
          terminator := .call 1 [] { localId := 1, projection := [] } (some 1) (.cleanup 2)
          cleanup := false },
        { statements := [
            .assign { localId := 0, projection := [] }
              (.use (.copy { localId := 1, projection := [] }))
          ]
          terminator := .return_
          cleanup := false },
        { statements := [
            .assign { localId := 0, projection := [] }
              (.use (.copy { localId := 1, projection := [] }))
          ]
          terminator := .unwindResume
          cleanup := true }
      ] },
    bodyUnwindingCallee
  ]
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1

noncomputable def progCe6CleanupClean : Program where
  bodies := [
    { locals := [.int .i32 false, .int .i32 false]
      argumentCount := 0
      basicBlocks := [
        { statements := []
          terminator := .call 1 [] { localId := 1, projection := [] } (some 1) (.cleanup 2)
          cleanup := false },
        { statements := [
            .assign { localId := 0, projection := [] }
              (.use (.copy { localId := 1, projection := [] }))
          ]
          terminator := .return_
          cleanup := false },
        { statements := [.nop]
          terminator := .unwindResume
          cleanup := true }
      ] },
    bodyUnwindingCallee
  ]
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1

theorem ce6_unwind_does_not_write_call_dst :
    ReachesResultUnw progCe6CleanupReadsUnwrittenDst emptyQuery (.fault .undefined) ∧
    WellFormedUnw progCe6CleanupClean emptyQuery ∧
    BehaviorUnw progCe6CleanupClean emptyQuery (.unwound ⟨[]⟩) := by
  exact ⟨(negativeCanaryUnw_of_exec (fuel := 10) (by rfl)).1,
    (positiveCanaryUnw_of_exec (fuel := 10) (by rfl)).1,
    (positiveCanaryUnw_of_exec (fuel := 10) (by rfl)).2.1⟩

/-- **CE7:** Unwind-aware `MIR Inline` (`applyInlineWithUnwind`) accepts
inlining a genuinely unwinding callee (`bodyUnwindingCallee`) into a caller
with `.cleanup 2`, and the inlined program preserves `.done (.unwound ⟨[]⟩)`. -/
noncomputable def siteCe7 : UnwindInlineSite :=
  { callerDefId := 0, callBlock := 0, calleeDefId := 1 }

noncomputable def progCe7Inlined : Program :=
  match applyInlineWithUnwind progCe6CleanupClean siteCe7 with
  | some p => p
  | none => progCe6CleanupClean

theorem ce7_inline_unwinding_callee_preserves_unwound :
    checkInlineWithUnwind progCe6CleanupClean siteCe7 progCe7Inlined = true ∧
    WellFormedUnw progCe7Inlined emptyQuery ∧
    BehaviorUnw progCe7Inlined emptyQuery (.unwound ⟨[]⟩) := by
  exact ⟨rfl,
    (positiveCanaryUnw_of_exec (fuel := 16) (by rfl)).1,
    (positiveCanaryUnw_of_exec (fuel := 16) (by rfl)).2.1⟩

/-- **CE8:** Returning normally from a diverging call (`target = none`) faults
`.fault .undefined` (UB, `ControlFlow.lean:110`). -/
noncomputable def progCe8ReturnFromDivergingCall : Program where
  bodies := [
    { locals := [.int .i32 false]
      argumentCount := 0
      basicBlocks := [
        { statements := []
          terminator := .call 1 [] { localId := 0, projection := [] } none .continue_
          cleanup := false }
      ] },
    { locals := [.int .i32 false]
      argumentCount := 0
      basicBlocks := [
        { statements := [.assign { localId := 0, projection := [] } (.use (u32Const 42))]
          terminator := .return_
          cleanup := false }
      ] }
  ]
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1

theorem ce8_return_from_diverging_call_faults_ub :
    ReachesResultUnw progCe8ReturnFromDivergingCall emptyQuery (.fault .undefined) ∧
    ¬ WellFormedUnw progCe8ReturnFromDivergingCall emptyQuery :=
  negativeCanaryUnw_of_exec (fuel := 8) (by rfl)

/-- **CE9:** `TerminatorKind.assert` with `expected = false` succeeds on
`false`, and non-boolean `cond` fails closed to `.fault .unsupported`. -/
noncomputable def progCe9AssertFalseExpectedOk : Program where
  bodies := [{
    locals := [.int .i32 false]
    argumentCount := 0
    basicBlocks := [
      { statements := []
        terminator := .assert (boolConst false) false .overflowNeg 1 .continue_
        cleanup := false },
      { statements := [.assign { localId := 0, projection := [] } (.use (u32Const 55))]
        terminator := .return_
        cleanup := false }
    ]
  }]
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1

noncomputable def progCe9AssertNonBoolFaults : Program where
  bodies := [{
    locals := [.int .i32 false]
    argumentCount := 0
    basicBlocks := [
      { statements := []
        terminator := .assert (u32Const 1) true .overflowNeg 0 .continue_
        cleanup := false }
    ]
  }]
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1

theorem ce9_assert_polarity_and_non_bool_fail_closed :
    BehaviorUnw progCe9AssertFalseExpectedOk emptyQuery
      (.returned ⟨.scalar ⟨.i32, false, BitVec.ofNat 128 55⟩, ⟨[]⟩⟩) ∧
    ReachesResultUnw progCe9AssertNonBoolFaults emptyQuery (.fault .unsupported) := by
  exact ⟨(positiveCanaryUnw_of_exec (fuel := 6) (by rfl)).2.1,
    (negativeCanaryUnw_of_exec (fuel := 4) (by rfl)).1⟩

/-- **CE10 (End-to-End Multi-Pass Witness & `-C panic=abort` Refinement Witness):**
A 2-body program (`entry(x: u32) -> u32` calling `inc_wrap(y: u32) -> u32` with
a `cleanup = true` landing pad + `.unwindResume` and a satisfied
`assert(true == true)` inside `inc_wrap`) lowers via
`inlineWithUnwind -> dischargeTrivialAssert -> abortUnwindingCalls ->
pruneDeadCleanupBlocks` into a 100% base-MIR `progWitnessFlat`
(`isBaseMirProgram = true`), AND `-C panic=abort` on `progCe6CleanupClean`
converts `.unwound` cleanly into `.aborted`. -/
noncomputable def progWitnessSrc : Program where
  bodies := [
    { locals := [.int .i32 false, .int .i32 false]
      argumentCount := 1
      basicBlocks := [
        { statements := []
          terminator := .call 1 [.copy { localId := 1, projection := [] }]
            { localId := 0, projection := [] } (some 1) (.cleanup 2)
          cleanup := false },
        { statements := []
          terminator := .return_
          cleanup := false },
        { statements := [.nop]
          terminator := .unwindResume
          cleanup := true }
      ]
      identity := "witness::entry" },
    { locals := [.int .i32 false, .int .i32 false]
      argumentCount := 1
      basicBlocks := [
        { statements := []
          terminator := .assert (boolConst true) true .overflowNeg 1 .continue_
          cleanup := false },
        { statements := [
            .assign { localId := 0, projection := [] }
              (.binaryOp .add (.copy { localId := 1, projection := [] })
                (u32Const 1))
          ]
          terminator := .return_
          cleanup := false }
      ]
      identity := "witness::inc_wrap" }
  ]
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1
  scope := .crate

noncomputable def witnessTrace : UnwindOptTrace := [
  .dischargeTrivialAssert 1 0,
  .abortUnwindingCalls [false, true],
  .pruneDeadCleanupBlocks 0 [0, 1],
  .inlineWithUnwind { callerDefId := 0, callBlock := 0, calleeDefId := 1 },
  .pruneDeadCleanupBlocks 0 [0, 1, 2, 3, 4]
]

noncomputable def applyTraceOpt :
    Program → UnwindOptTrace → Option Program
  | p, [] => some p
  | p, s :: rest =>
    match applyUnwindOptStep p s with
    | none => none
    | some p' => applyTraceOpt p' rest

noncomputable def progWitnessFlat : Program :=
  match applyTraceOpt progWitnessSrc witnessTrace with
  | some p => p
  | none => progWitnessSrc

noncomputable def progCe6PanicAbort : Program :=
  match applyPanicAbortEntryTransform progCe6CleanupClean with
  | some p => p
  | none => progCe6CleanupClean

theorem ce10_witness_unwind_trace_and_panic_abort_refinement :
    checkUnwindOptTrace progWitnessSrc witnessTrace progWitnessFlat = true ∧
    isBaseMirProgram progWitnessFlat = true ∧
    checkPanicAbortEntryTransform progCe6CleanupClean progCe6PanicAbort = true ∧
    BehaviorUnw progCe6PanicAbort emptyQuery (.aborted ⟨[]⟩) := by
  exact ⟨rfl, rfl, rfl, (positiveCanaryUnw_of_exec (fuel := 10) (by rfl)).2.1⟩


/-- **CE11:** Out-of-bounds caller `.goto` targeting `bbOff` (which would
silently land in the spliced callee entry block after appending callee blocks)
is rejected by `applyInlineWithUnwind` via `callerUnwindInlineAdmitted`. -/
noncomputable def progCe11CallerOobGoto : Program where
  bodies := [
    { locals := [.int .i32 false]
      argumentCount := 0
      basicBlocks := [
        { statements := [], terminator := .goto 2, cleanup := false },
        { statements := []
          terminator := .call 1 [] { localId := 0, projection := [] } (some 0) .continue_
          cleanup := false }
      ] },
    { locals := [.int .i32 false]
      argumentCount := 0
      basicBlocks := [
        { statements := [.assign { localId := 0, projection := [] } (.use (u32Const 99))]
          terminator := .return_
          cleanup := false }
      ] }
  ]
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1

theorem ce11_caller_oob_goto_rejected_by_inline_checker :
    applyInlineWithUnwind progCe11CallerOobGoto
      { callerDefId := 0, callBlock := 1, calleeDefId := 1 } = none ∧
    ReachesResultUnw progCe11CallerOobGoto emptyQuery (.fault .unsupported) := by
  exact ⟨rfl, (negativeCanaryUnw_of_exec (fuel := 4) (by rfl)).1⟩

end VrustcFormal.F1_13
