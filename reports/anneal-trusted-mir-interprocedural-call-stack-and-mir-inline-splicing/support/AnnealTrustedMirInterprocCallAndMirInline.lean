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

namespace VrustcFormal.F1_10

open Trusted.MirAst Trusted.MirSemantics

/-!
# Interprocedural Call-Stack Semantics & Certified MIR Inlining Splicing (`VrustcFormal.F1_10`)

This module closes the single largest expressiveness cliff in Anneal's
`Trusted.MirSemantics` (`TerminatorKind.call -> .fault .unsupported` at
`Trusted/MirSemantics.lean:1568`), grounded directly in unmodified
`Trusted.MirAst` and `Trusted.MirSemantics` (zero surrogate MIR AST types),
upstream `rustc_const_eval::interpret` (`rust-lang/rust` commits
`8144389c895da997dbdecaa635e41d6a50be6ffd` and
`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`), upstream
`rustc_mir_transform::inline::Integrator` (`compiler/rustc_mir_transform/src/inline.rs:864-1355`),
and empirical study `E3-13` (Package #57: `44.5%`--`45.7%` `Call` terminator
elimination and `56.7% -> 71.2%` call-free `zerocopy` bodies across `4,302`
monomorphized MIR bodies):

1. **Part I — Interprocedural Call-Stack Operational Semantics Directly Over
   `Trusted.MirAst.Program`:**
   - Extends `Trusted.MirSemantics` conservatively with an explicit caller
     continuation stack (`CallContinuation`, `InterprocState`) and
     `evalStepInterproc` delegating every statement and non-call/non-return
     terminator directly to `Trusted.MirSemantics.evalStatement` and
     `Trusted.MirSemantics.evalTerminator`.
   - Evaluates direct `TerminatorKind.call` arguments sequentially left-to-right
     via `evalOperandToSlot` (preserving `Operand.move` deinitialization and
     fault ordering), pushes the caller continuation, initializes the callee
     frame via `Trusted.MirSemantics.initLocalsLoop`, and on `TerminatorKind.return_`
     pops the continuation, writes `_0` into `cont.dst` via `writePlace`, and
     resumes at `cont.target` (or faults `.undefined` when `target = none`).
   - Defines `WellFormedInterproc`, `BehaviorInterproc`,
     `ReachesResultInterproc`, `DivergesInterproc`, `SatisfiesPostInterproc`,
     `BodyVerifiedInterproc`, `ProgramVerifiedInterproc`,
     `CrateTheoremInterproc`, `UnitTheoremInterproc`, and
     `FullSemanticEquivInterproc`.

2. **Part II — Decidable Certified MIR Inlining Splicing Checker (`InlineSite`,
   `InlineTrace`, `checkMirInlineCallSite`, `checkMirInlineTrace`):**
   - Mechanizes `rustc_mir_transform::inline::Integrator` over unmodified
     `Trusted.MirAst.Program`: checks non-self-recursive call-site admissibility
     (`callerDefId ≠ calleeDefId`, caller/callee local and basic-block bounds,
     `calleeCallAdmitted`, return-type compatibility, no callee `StorageDead 0`),
     appends shifted callee locals and basic blocks, splices entry `StorageLive`
     and sequential argument-binding assignments into `callBlock`, rewrites
     non-cleanup callee `.return_` terminators to `.goto exitBlock`, and emits
     return-value transfer plus `StorageDead` cleanup across all shifted callee
     locals in `exitBlock` (preserving `hasStorageAnnotation` on caller locals
     and guaranteeing clean frame reset across loop re-entry and mutual
     recursion).

3. **Part III — Five Core Target Theorems (`sorry` placeholders frozen for
   Stage 3 proof):**
   - `interproc_conservative_extension_exact`: exact single-frame agreement and
     full call-free equivalence with unmodified `Trusted.MirSemantics`.
   - `mirInlineCallSite_sound_bidirectional_iff`: single-site bidirectional
     interprocedural equivalence (`↔`).
   - `mirInlineTrace_sound_bidirectional_iff`: arbitrary finite trace
     composition (`↔`).
   - `mirInlineTrace_reduces_interproc_to_intraproc_trusted`: reduction of
     multi-function `CrateTheoremInterproc` / `UnitTheoremInterproc` into
     unmodified intraprocedural `Trusted.MirSemantics.CrateTheorem` /
     `UnitTheorem` once all calls are eliminated.
   - `mirInline_then_postInline_vc_transport`: composition of MIR inlining with
     arbitrary post-inline intraprocedural optimization equivalence
     (`F1-5`..`F1-9`).

4. **Part IV — Deterministic Adequacy, Six Sharpness Counterexamples
   (`CE1`--`CE6`), and Multi-Hop Loop Inlining Witness (`0` `sorry`, strictly
   `[propext]`):**
   - Proves bounded-fuel adequacy for both unmodified `Trusted.MirSemantics` and
     `evalStepInterproc`, six constructive sharpness counterexamples validating
     every checker guard and fault-ordering rule (including 4-frame recursive
     execution `rec(3) = 3`), and a concrete 3-function 2-hop loop witness
     (`main -> helper_a -> helper_b` invoked twice in a loop) bridging
     `evalStepInterproc` directly into unmodified `Trusted.MirSemantics`.
-/

/-! ## Part I: Interprocedural Call-Stack Operational Semantics Over `Trusted.MirAst.Program` -/

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
noncomputable def optBlockEq : Option BasicBlockId → Option BasicBlockId → Bool
  | none, none => true
  | some b₁, some b₂ => Nat.beq b₁ b₂
  | _, _ => false

/-- Structural equality on `TerminatorKind`. -/
noncomputable def terminatorEq : TerminatorKind → TerminatorKind → Bool
  | .goto t₁, .goto t₂ => Nat.beq t₁ t₂
  | .switchInt d₁ ts₁, .switchInt d₂ ts₂ =>
    operandEq d₁ d₂ && switchTargetsEq ts₁ ts₂
  | .return_, .return_ => true
  | .unreachable, .unreachable => true
  | .unwindResume, .unwindResume => true
  | .assert c₁ e₁ m₁ t₁ u₁, .assert c₂ e₂ m₂ t₂ u₂ =>
    operandEq c₁ c₂ && (e₁ == e₂) && assertKindEq m₁ m₂ &&
      Nat.beq t₁ t₂ && unwindActionEq u₁ u₂
  | .call f₁ as₁ d₁ t₁ u₁, .call f₂ as₂ d₂ t₂ u₂ =>
    Nat.beq f₁ f₂ && listRel operandEq as₁ as₂ && placeEq d₁ d₂ &&
      optBlockEq t₁ t₂ && unwindActionEq u₁ u₂
  | .unsupported, .unsupported => true
  | _, _ => false

/-- Structural equality on `BasicBlock`. -/
noncomputable def blockEq (b₁ b₂ : BasicBlock) : Bool :=
  (b₁.cleanup == b₂.cleanup) &&
    listRel stmtEq b₁.statements b₂.statements &&
    terminatorEq b₁.terminator b₂.terminator

/-- Structural equality on `VerificationScope`. -/
noncomputable def scopeEq : VerificationScope → VerificationScope → Bool
  | .unit, .unit | .crate, .crate => true
  | _, _ => false

/-- Shared body-metadata equality (`argumentCount`, `locals`, `isUnsafe`,
`identity`). -/
noncomputable def bodyHeaderEq (b₁ b₂ : Body) : Bool :=
  Nat.beq b₁.argumentCount b₂.argumentCount &&
    MirTy.beqList b₁.locals b₂.locals &&
    (b₁.isUnsafe == b₂.isUnsafe) &&
    stringBeq b₁.identity b₂.identity

/-- Structural equality on `Body`. -/
noncomputable def bodyEq (b₁ b₂ : Body) : Bool :=
  bodyHeaderEq b₁ b₂ && listRel blockEq b₁.basicBlocks b₂.basicBlocks

/-- Shared program-header equality (`pointerWidthBits`, `mirProfileVersion`,
`entryDefId`, `scope`). -/
noncomputable def programHeaderEq (p₁ p₂ : Program) : Bool :=
  Nat.beq p₁.pointerWidthBits p₂.pointerWidthBits &&
    Nat.beq p₁.mirProfileVersion p₂.mirProfileVersion &&
    Nat.beq p₁.entryDefId p₂.entryDefId &&
    scopeEq p₁.scope p₂.scope

/-- Structural equality on `Program`. -/
noncomputable def programEq (p₁ p₂ : Program) : Bool :=
  programHeaderEq p₁ p₂ && listRel bodyEq p₁.bodies p₂.bodies

/-- Metadata compatibility between two programs sharing the same crate/unit
packaging (`pointerWidthBits`, `mirProfileVersion`, `entryDefId`, `scope`,
body count, and per-body `identity` strings), preserved by every certified MIR
optimization pass (`F1-5`--`F1-9`) and by MIR inlining. -/
noncomputable def ProgramMetadataCompat (p₁ p₂ : Program) : Bool :=
  programHeaderEq p₁ p₂ &&
    listRel (fun b₁ b₂ => stringBeq b₁.identity b₂.identity) p₁.bodies p₂.bodies

/-! ### Interprocedural Call-Stack Machine Over `Trusted.MirAst.Program` -/

/-- Suspended caller continuation frame pushed on `TerminatorKind.call`,
recording the caller's post-argument-evaluation `FrameState`, destination
`Place`, optional normal return `BasicBlockId`, and `UnwindAction`. -/
structure CallContinuation where
  callerFrame : FrameState
  dst : Place
  target : Option BasicBlockId
  unwind : UnwindAction

/-- Interprocedural machine state directly over unmodified
`Trusted.MirSemantics.{FrameState, CallerMemory}`: currently executing frame
`cur`, suspended caller stack `stack` (head is the immediate caller), and
caller-visible memory `callerMem`. -/
structure InterprocState where
  cur : FrameState
  stack : List CallContinuation
  callerMem : CallerMemory := ⟨[]⟩

/-- Exact embedding of a single-frame intraprocedural `Trusted.MirSemantics.State`
into `InterprocState` (`none` whenever `s.frames` is not a singleton). -/
noncomputable def embedState (s : State) : Option InterprocState :=
  match s.frames with
  | [frame] => some { cur := frame, stack := [], callerMem := s.callerMem }
  | _ => none

/-- Exact projection of a top-level (`stack = []`) `InterprocState` back to
`Trusted.MirSemantics.State`. -/
noncomputable def projectTopState (s : InterprocState) : State :=
  { frames := [s.cur], callerMem := s.callerMem }

/-- Lift a single-frame `Trusted.MirSemantics` transition into `InterprocState`
while preserving the suspended caller stack `stack`. -/
noncomputable def liftSingleFrameStep (stack : List CallContinuation) :
    StepResult State TerminalOut → StepResult InterprocState TerminalOut
  | .step s' =>
    match s'.frames with
    | [frame'] =>
      .step { cur := frame', stack := stack, callerMem := s'.callerMem }
    | _ => .fault .unsupported
  | .done out => .done out
  | .fault k => .fault k

/-- Static admissibility of a callee body at `TerminatorKind.call`, matching the
per-body static checks of `Trusted.MirSemantics.initState`. -/
noncomputable def calleeCallAdmitted (body : Body) : Bool :=
  !body.basicBlocks.isEmpty &&
    Nat.blt body.argumentCount body.locals.length &&
    storageAnnotationsInBounds body &&
    body.locals.all isSupportedScalarOrUnitTy

/-- Evaluate function-call arguments sequentially left-to-right against the
callee's declared parameter types `paramTys`, matching both
`rustc_const_eval::interpret` left-to-right argument evaluation and the spliced
`.assign ⟨localBase + 1 + i, []⟩ (.use arg_i)` sequence emitted by MIR inlining:
each argument `arg_i` is resolved via `Trusted.MirSemantics.evalOperandToSlot`
(deinitializing moved non-ZST caller locals in order), checked for exact static
type equality `srcTy == paramTy_i`, checked for initialization (`some v`), and
validated via `Trusted.MirSemantics.checkVal v paramTy_i`. -/
noncomputable def evalCallArgs (callerBodyLocals : List MirTy)
    (callerLocals : List LocalSlot) :
    List Operand → List MirTy → Except FaultKind (List Val × List LocalSlot)
  | [], [] => .ok ([], callerLocals)
  | arg :: restArgs, paramTy :: restTys =>
    match evalOperandToSlot callerBodyLocals callerLocals arg with
    | .error k => .error k
    | .ok (srcTy, optVal, locals₁) =>
      if !(MirTy.beq srcTy paramTy) then
        .error .unsupported
      else
        match optVal with
        | none => .error .undefined
        | some v =>
          if !checkVal v paramTy then
            .error .unsupported
          else
            match evalCallArgs callerBodyLocals locals₁ restArgs restTys with
            | .error k => .error k
            | .ok (vs, localsFinal) => .ok (v :: vs, localsFinal)
  | _, _ => .error .unsupported

/-- Evaluate `TerminatorKind.call` in `evalStepInterproc`: validates non-cleanup
block, unprojected in-bounds destination, statically admitted callee body,
matching arity and return type, evaluates arguments left-to-right via
`evalCallArgs`, initializes the callee frame via
`Trusted.MirSemantics.initLocalsLoop`, and pushes the caller continuation onto
`stack`. Destination liveness (`DeadLocal`) is checked when the callee returns
and writes to `dst`, matching `rustc_const_eval::interpret` (`step.rs` /
`call.rs`) and `Trusted.MirSemantics.evalStatement`. -/
noncomputable def evalCallTerminator (p : Program) (callerBody : Body)
    (bb : BasicBlock) (frame : FrameState) (stack : List CallContinuation)
    (callerMem : CallerMemory) (calleeDefId : DefId) (args : List Operand)
    (dst : Place) (target : Option BasicBlockId) (unwind : UnwindAction) :
    StepResult InterprocState TerminalOut :=
  if bb.cleanup || !dst.projection.isEmpty then
    .fault .unsupported
  else
    match Trusted.MirSemantics.getElem? callerBody.locals dst.localId,
        Trusted.MirSemantics.getElem? p.bodies calleeDefId with
    | some dstTy, some calleeBody =>
      if !calleeCallAdmitted calleeBody ||
          !Nat.beq args.length calleeBody.argumentCount then
        .fault .unsupported
      else
        match Trusted.MirSemantics.getElem? calleeBody.locals 0 with
        | none => .fault .unsupported
        | some calleeRetTy =>
          if !MirTy.beq calleeRetTy dstTy then
            .fault .unsupported
          else
            let paramTys :=
              (calleeBody.locals.drop 1).take calleeBody.argumentCount
            match evalCallArgs callerBody.locals frame.locals args paramTys with
            | .error k => .fault k
            | .ok (argVals, callerLocalsAfterArgs) =>
              let calleeLocals :=
                initLocalsLoop calleeBody argVals 0 calleeBody.locals
              let calleeFrame : FrameState := {
                defId := calleeDefId
                blockIdx := 0
                stmtIdx := 0
                locals := calleeLocals
              }
              let cont : CallContinuation := {
                callerFrame := { frame with locals := callerLocalsAfterArgs }
                dst := dst
                target := target
                unwind := unwind
              }
              .step {
                cur := calleeFrame
                stack := cont :: stack
                callerMem := callerMem
              }
    | _, _ => .fault .unsupported

/-- Evaluate `TerminatorKind.return_` in `evalStepInterproc`:
- On an empty call stack (`stack = []`), matches `Trusted.MirSemantics.evalTerminator`
  identically (returning `.done (.returned ⟨retVal, callerMem⟩)`).
- On a non-empty stack (`cont :: rest`), validates caller body, unprojected
  `cont.dst`, and return-type compatibility, reads `_0`, writes `retVal` into
  `cont.dst` via `Trusted.MirSemantics.writePlace` (checking `checkVal` and
  destination liveness), and resumes `cont.callerFrame` at `(retBb, 0)` when
  `cont.target = some retBb` (or faults `.undefined` when `cont.target = none`,
  matching `rustc_const_eval`'s `return_to_block` on a diverging call). -/
noncomputable def evalReturnTerminator (p : Program) (body : Body)
    (bb : BasicBlock) (frame : FrameState) (stack : List CallContinuation)
    (callerMem : CallerMemory) :
    StepResult InterprocState TerminalOut :=
  if bb.cleanup then
    .fault .unsupported
  else
    match stack with
    | [] =>
      match Trusted.MirSemantics.getElem? frame.locals 0 with
      | some (.live (some retVal)) =>
        .done (.returned ⟨retVal, callerMem⟩)
      | some (.live none) | some .dead => .fault .undefined
      | none => .fault .unsupported
    | cont :: rest =>
      if !cont.dst.projection.isEmpty then
        .fault .unsupported
      else
        match Trusted.MirSemantics.getElem? p.bodies cont.callerFrame.defId with
        | none => .fault .unsupported
        | some callerBody =>
          match Trusted.MirSemantics.getElem? callerBody.locals cont.dst.localId,
              Trusted.MirSemantics.getElem? body.locals 0 with
          | some dstTy, some calleeRetTy =>
            if !MirTy.beq calleeRetTy dstTy then
              .fault .unsupported
            else
              match Trusted.MirSemantics.getElem? frame.locals 0 with
              | some (.live (some retVal)) =>
                match writePlace cont.callerFrame.locals cont.dst.localId
                    dstTy retVal with
                | .error k => .fault k
                | .ok callerLocals' =>
                  match cont.target with
                  | some retBb =>
                    .step {
                      cur := {
                        cont.callerFrame with
                        blockIdx := retBb
                        stmtIdx := 0
                        locals := callerLocals'
                      }
                      stack := rest
                      callerMem := callerMem
                    }
                  | none => .fault .undefined
              | some (.live none) | some .dead => .fault .undefined
              | none => .fault .unsupported
          | _, _ => .fault .unsupported

/-- Total single-step interprocedural evaluator directly over unmodified
`Trusted.MirAst.Program`: delegates every statement to
`Trusted.MirSemantics.evalStatement` and every non-`.call`/non-`.return_`
terminator directly to `Trusted.MirSemantics.evalTerminator`. -/
noncomputable def evalStepInterproc (p : Program) (_c : Choice)
    (s : InterprocState) : StepResult InterprocState TerminalOut :=
  match Trusted.MirSemantics.getElem? p.bodies s.cur.defId with
  | none => .fault .unsupported
  | some body =>
    match Trusted.MirSemantics.getElem? body.basicBlocks s.cur.blockIdx with
    | none => .fault .unsupported
    | some bb =>
      match Trusted.MirSemantics.getElem? bb.statements s.cur.stmtIdx with
      | some stmt =>
        liftSingleFrameStep s.stack (evalStatement body s.cur s.callerMem stmt)
      | none =>
        if Nat.beq s.cur.stmtIdx bb.statements.length then
          match bb.terminator with
          | .return_ =>
            evalReturnTerminator p body bb s.cur s.stack s.callerMem
          | .call calleeDefId args dst target unwind =>
            evalCallTerminator p body bb s.cur s.stack s.callerMem
              calleeDefId args dst target unwind
          | _ =>
            liftSingleFrameStep s.stack
              (evalTerminator body bb s.cur s.callerMem)
        else
          .fault .unsupported

/-- Entry initialization for `evalStepInterproc`, delegating directly to
`Trusted.MirSemantics.initState`. -/
noncomputable def initStateInterproc (p : Program) (q : Query) :
    Except FaultKind InterprocState :=
  match initState p q with
  | .error k => .error k
  | .ok s₀ =>
    match embedState s₀ with
    | some is₀ => .ok is₀
    | none => .error .unsupported

/-- Admissible demonic choice predicate for `evalStepInterproc`. -/
noncomputable def ValidChoiceInterproc (_p : Program) (_s : InterprocState)
    (c : Choice) : Prop :=
  c = 0

/-- Relational small-step interprocedural transition. -/
noncomputable def StepInterproc (p : Program) (s : InterprocState)
    (res : StepResult InterprocState TerminalOut) : Prop :=
  ∃ c : Choice, ValidChoiceInterproc p s c ∧ evalStepInterproc p c s = res

/-- Finite-step interprocedural state reachability. -/
inductive ReachesInterproc (p : Program) :
    InterprocState → InterprocState → Prop where
  | refl (s : InterprocState) : ReachesInterproc p s s
  | tail {s₁ s₂ s₃ : InterprocState} :
      ReachesInterproc p s₁ s₂ →
      StepInterproc p s₂ (.step s₃) →
      ReachesInterproc p s₁ s₃

/-- Outcome `res` is reached from `(p, q)` under `evalStepInterproc`. -/
noncomputable def ReachesResultInterproc (p : Program) (q : Query)
    (res : StepResult InterprocState TerminalOut) : Prop :=
  match initStateInterproc p q with
  | .error k => res = .fault k
  | .ok s₀ => ∃ s : InterprocState, ReachesInterproc p s₀ s ∧ StepInterproc p s res

/-- All-prefix interprocedural well-formedness (no `.fault .undefined` or
`.fault .unsupported` along any reachable execution prefix). -/
noncomputable def WellFormedInterproc (p : Program) (q : Query) : Prop :=
  (∃ s₀ : InterprocState, initStateInterproc p q = .ok s₀ ∧
    ∀ s : InterprocState, ReachesInterproc p s₀ s →
      ∃ c : Choice, ValidChoiceInterproc p s c) ∧
  (∀ k : FaultKind, ¬ ReachesResultInterproc p q (.fault k))

/-- Observable terminal behavior of `(p, q)` under `evalStepInterproc`. -/
noncomputable def BehaviorInterproc (p : Program) (q : Query)
    (out : TerminalOut) : Prop :=
  ReachesResultInterproc p q (.done out)

/-- Constructive interprocedural divergence: existence of an infinite coherent
trace `trace : Nat → InterprocState` from `initStateInterproc p q = .ok s₀`. -/
noncomputable def DivergesInterproc (p : Program) (q : Query) : Prop :=
  ∃ s₀ : InterprocState,
    initStateInterproc p q = .ok s₀ ∧
    ∃ trace : Nat → InterprocState,
      trace 0 = s₀ ∧
      ∀ n : Nat, StepInterproc p (trace n) (.step (trace (n + 1)))

/-- Interprocedural partial-correctness contract satisfaction. -/
noncomputable def SatisfiesPostInterproc (p : Program) (q : Query)
    (post : TerminalOut → Prop) : Prop :=
  WellFormedInterproc p q ∧
  ∀ out : TerminalOut, BehaviorInterproc p q out → post out

/-- Interprocedural per-body verification judgment mirroring
`Trusted.MirSemantics.BodyVerified`. -/
noncomputable def BodyVerifiedInterproc (p : Program) (defId : DefId)
    (body : Body) (safetyPre : List Val → Prop) : Prop :=
  Trusted.MirSemantics.getElem? p.bodies defId = some body ∧
  BodyStaticAdmitted p body = true ∧
  ∀ args : List Val,
    ValidEntryArgs body args →
    (body.isUnsafe = true → safetyPre args) →
    WellFormedInterproc (entryProgForBody p defId) { args := args }

/-- Interprocedural program verification judgment mirroring
`Trusted.MirSemantics.ProgramVerified`. -/
noncomputable def ProgramVerifiedInterproc (p : Program) (specs : Specs) :
    Prop :=
  Nat.beq p.pointerWidthBits 64 = true ∧
  Nat.beq p.mirProfileVersion 1 = true ∧
  !p.bodies.isEmpty = true ∧
  Nat.blt p.entryDefId p.bodies.length = true ∧
  bodiesHaveUniqueIdentities p.bodies = true ∧
  (∀ (defId : DefId) (body : Body),
    Trusted.MirSemantics.getElem? p.bodies defId = some body →
    BodyVerifiedInterproc p defId body (specs.safety body.identity)) ∧
  specs.property p

/-- Interprocedural whole-crate verification obligation mirroring
`Trusted.MirSemantics.CrateTheorem`. -/
noncomputable def CrateTheoremInterproc (c : Crate) : Prop :=
  c.program.scope = .crate ∧ ProgramVerifiedInterproc c.program c.specs

/-- Interprocedural proof-unit verification obligation mirroring
`Trusted.MirSemantics.UnitTheorem`. -/
noncomputable def UnitTheoremInterproc (c : Crate) : Prop :=
  c.program.scope = .unit ∧ ProgramVerifiedInterproc c.program c.specs

/-- Bundled intraprocedural bidirectional semantic equivalence on unmodified
`Trusted.MirSemantics` (matching `F1_9.FullSemanticEquiv` for post-inline
pipeline composition). -/
noncomputable def FullSemanticEquiv (pSrc pTgt : Program) : Prop :=
  (∀ q : Query,
    (WellFormed pTgt q ↔ WellFormed pSrc q) ∧
    (∀ out : TerminalOut, Behavior pTgt q out ↔ Behavior pSrc q out) ∧
    (∀ k : FaultKind,
      ReachesResult pTgt q (.fault k) ↔ ReachesResult pSrc q (.fault k)) ∧
    (Diverges pTgt q ↔ Diverges pSrc q)) ∧
  (∀ (q : Query) (post : TerminalOut → Prop),
    SatisfiesPost pTgt q post ↔ SatisfiesPost pSrc q post) ∧
  (∀ (defId : DefId) (bSrc bTgt : Body) (safetyPre : List Val → Prop),
    Trusted.MirSemantics.getElem? pSrc.bodies defId = some bSrc →
    Trusted.MirSemantics.getElem? pTgt.bodies defId = some bTgt →
    (BodyVerified pTgt defId bTgt safetyPre ↔
      BodyVerified pSrc defId bSrc safetyPre))

/-- Bundled interprocedural bidirectional semantic equivalence across all
judgments (`WellFormedInterproc`, `BehaviorInterproc`,
`ReachesResultInterproc (.fault k)`, `DivergesInterproc`,
`SatisfiesPostInterproc`, and `BodyVerifiedInterproc`). -/
noncomputable def FullSemanticEquivInterproc (pSrc pTgt : Program) : Prop :=
  (∀ q : Query,
    (WellFormedInterproc pTgt q ↔ WellFormedInterproc pSrc q) ∧
    (∀ out : TerminalOut,
      BehaviorInterproc pTgt q out ↔ BehaviorInterproc pSrc q out) ∧
    (∀ k : FaultKind,
      ReachesResultInterproc pTgt q (.fault k) ↔
        ReachesResultInterproc pSrc q (.fault k)) ∧
    (DivergesInterproc pTgt q ↔ DivergesInterproc pSrc q)) ∧
  (∀ (q : Query) (post : TerminalOut → Prop),
    SatisfiesPostInterproc pTgt q post ↔ SatisfiesPostInterproc pSrc q post) ∧
  (∀ (defId : DefId) (bSrc bTgt : Body) (safetyPre : List Val → Prop),
    Trusted.MirSemantics.getElem? pSrc.bodies defId = some bSrc →
    Trusted.MirSemantics.getElem? pTgt.bodies defId = some bTgt →
    (BodyVerifiedInterproc pTgt defId bTgt safetyPre ↔
      BodyVerifiedInterproc pSrc defId bSrc safetyPre))

/-- Select body `u` of `p` as a `.unit`-scoped proof-unit subject. -/
noncomputable def unitProgForDef (p : Program) (u : DefId) : Program :=
  { p with entryDefId := u, scope := .unit }

/-- Semantic invariance of `specs.property` across interprocedurally equivalent
programs (`FullSemanticEquivInterproc`), automatically satisfied by
`property := fun _ => True` and by any behavioral contract over
`WellFormedInterproc`, `BehaviorInterproc`, or `DivergesInterproc` (and, on
call-free programs, any intraprocedural contract over `Trusted.MirSemantics`). -/
noncomputable def SpecsPropertyInvariant (specs : Specs) : Prop :=
  ∀ p₁ p₂ : Program, FullSemanticEquivInterproc p₁ p₂ →
    (specs.property p₁ ↔ specs.property p₂)

/-- Whether terminator `t` is not `TerminatorKind.call`. -/
noncomputable def isNonCallTerminator : TerminatorKind → Bool
  | .call _ _ _ _ _ => false
  | _ => true

/-- Whether basic block `bb` contains no `TerminatorKind.call`. -/
noncomputable def blockIsCallFree (bb : BasicBlock) : Bool :=
  isNonCallTerminator bb.terminator

/-- Whether body `b` contains no `TerminatorKind.call` in any basic block. -/
noncomputable def bodyIsCallFree (b : Body) : Bool :=
  b.basicBlocks.all blockIsCallFree

/-- Whether every body in `p.bodies` is free of `TerminatorKind.call`. -/
noncomputable def isCallFreeProgram (p : Program) : Bool :=
  p.bodies.all bodyIsCallFree

/-- Whether the active instruction of a single-frame `State` in `p` is not a
`TerminatorKind.call` terminator. -/
noncomputable def stepIsNotCall (p : Program) (s : State) : Bool :=
  match s.frames with
  | [frame] =>
    match Trusted.MirSemantics.getElem? p.bodies frame.defId with
    | none => true
    | some body =>
      match Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx with
      | none => true
      | some bb =>
        match Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx with
        | some _ => true
        | none =>
          if Nat.beq frame.stmtIdx bb.statements.length then
            isNonCallTerminator bb.terminator
          else
            true
  | _ => true

/-! ## Part II: Decidable Certified MIR Inlining Splicing Checker (`InlineSite` & `InlineTrace`) -/

/-! ### Local-Index, Block-Index, and Callee-Storage Hygiene Predicates -/

/-- Check that every `LocalId` referenced by `opnd` is `< bound`. -/
noncomputable def operandLocalsLt (bound : Nat) : Operand → Bool
  | .copy p | .move p => Nat.blt p.localId bound
  | .constant _ => true

/-- Check that every `LocalId` referenced by `rv` is `< bound`. -/
noncomputable def rvalueLocalsLt (bound : Nat) : Rvalue → Bool
  | .use o | .unaryOp _ o => operandLocalsLt bound o
  | .binaryOp _ l r => operandLocalsLt bound l && operandLocalsLt bound r
  | .discriminant p | .ref _ p | .addressOf _ p => Nat.blt p.localId bound
  | .aggregateTuple fs => fs.all (operandLocalsLt bound)
  | .unsupported => true

/-- Check that every `LocalId` referenced by `stmt` is `< bound`. -/
noncomputable def stmtLocalsLt (bound : Nat) : StatementKind → Bool
  | .assign dst rv => Nat.blt dst.localId bound && rvalueLocalsLt bound rv
  | .storageLive id | .storageDead id => Nat.blt id bound
  | .nop | .unsupported => true

/-- Check that every `LocalId` referenced by `term` is `< bound`. -/
noncomputable def terminatorLocalsLt (bound : Nat) : TerminatorKind → Bool
  | .goto _ | .return_ | .unreachable | .unwindResume | .unsupported => true
  | .switchInt d _ => operandLocalsLt bound d
  | .assert c _ _ _ _ => operandLocalsLt bound c
  | .call _ args dst _ _ =>
    args.all (operandLocalsLt bound) && Nat.blt dst.localId bound

/-- Check that every statement and terminator in `b` references only in-bounds
locals `< b.locals.length` (preventing out-of-bounds caller locals from
aliasing newly appended callee slots). -/
noncomputable def bodyAllLocalsInBounds (b : Body) : Bool :=
  let bound := b.locals.length
  b.basicBlocks.all (fun bb =>
    bb.statements.all (stmtLocalsLt bound) &&
      terminatorLocalsLt bound bb.terminator)

/-- Check that any cleanup target in `u` is `< bound`. -/
noncomputable def unwindBlocksLt (bound : Nat) : UnwindAction → Bool
  | .continue_ | .unreachable | .terminate => true
  | .cleanup b => Nat.blt b bound

/-- Check that every `BasicBlockId` referenced by `term` is `< bound`. -/
noncomputable def terminatorBlocksLt (bound : Nat) : TerminatorKind → Bool
  | .goto t => Nat.blt t bound
  | .switchInt _ ts =>
    Nat.blt ts.otherwise bound &&
      ts.branches.all (fun br => Nat.blt br.2 bound)
  | .return_ | .unreachable | .unwindResume | .unsupported => true
  | .assert _ _ _ t u => Nat.blt t bound && unwindBlocksLt bound u
  | .call _ _ _ tgt u =>
    (match tgt with | none => true | some b => Nat.blt b bound) &&
      unwindBlocksLt bound u

/-- Check that every basic block target in `b` is strictly `< b.basicBlocks.length`
(preventing out-of-bounds caller or callee block jumps from aliasing newly
spliced callee blocks or `exitBlock`). -/
noncomputable def bodyAllBlocksInBounds (b : Body) : Bool :=
  let bound := b.basicBlocks.length
  b.basicBlocks.all (fun bb => terminatorBlocksLt bound bb.terminator)

/-- Check that `b` contains no `StatementKind.storageDead 0`, which faults with
`.unsupported` on `_0` in `Trusted.MirSemantics.evalStatement` but would shift
to `localBase + 0 > 0` after inlining. -/
noncomputable def bodyHasNoStorageDeadZero (b : Body) : Bool :=
  b.basicBlocks.all (fun bb =>
    bb.statements.all (fun stmt =>
      match stmt with
      | .storageDead id => !Nat.beq id 0
      | _ => true))

/-! ### `Integrator` Relocation & Splicing Transformations (`inline.rs:864-1355`) -/

/-- Shift a callee `Place` by `localBase`. -/
noncomputable def shiftPlace (localBase : Nat) (p : Place) : Place :=
  { localId := localBase + p.localId, projection := p.projection }

/-- Shift all local indices inside a callee `Operand` by `localBase`. -/
noncomputable def shiftOperand (localBase : Nat) : Operand → Operand
  | .copy p => .copy (shiftPlace localBase p)
  | .move p => .move (shiftPlace localBase p)
  | .constant c => .constant c

/-- Shift all local indices inside a callee `Rvalue` by `localBase`. -/
noncomputable def shiftRvalue (localBase : Nat) : Rvalue → Rvalue
  | .use o => .use (shiftOperand localBase o)
  | .binaryOp op l r =>
    .binaryOp op (shiftOperand localBase l) (shiftOperand localBase r)
  | .unaryOp op o => .unaryOp op (shiftOperand localBase o)
  | .discriminant p => .discriminant (shiftPlace localBase p)
  | .ref m p => .ref m (shiftPlace localBase p)
  | .addressOf m p => .addressOf m (shiftPlace localBase p)
  | .aggregateTuple fs => .aggregateTuple (fs.map (shiftOperand localBase))
  | .unsupported => .unsupported

/-- Shift all local indices inside a callee `StatementKind` by `localBase`. -/
noncomputable def shiftStmt (localBase : Nat) : StatementKind → StatementKind
  | .assign dst rv =>
    .assign (shiftPlace localBase dst) (shiftRvalue localBase rv)
  | .storageLive id => .storageLive (localBase + id)
  | .storageDead id => .storageDead (localBase + id)
  | .nop => .nop
  | .unsupported => .unsupported

/-- Shift all branch targets of a callee `SwitchTargets` by `blockBase`. -/
noncomputable def shiftSwitchTargets (blockBase : Nat)
    (ts : SwitchTargets) : SwitchTargets :=
  {
    branches := ts.branches.map (fun br => (br.1, blockBase + br.2))
    otherwise := blockBase + ts.otherwise
  }

/-- Map a callee `UnwindAction` into the caller CFG, matching
`Integrator::map_unwind` (`inline.rs:1220-1236`). -/
noncomputable def mapInlinedUnwind (blockBase : Nat)
    (callUnwind : UnwindAction) (inCleanup : Bool) :
    UnwindAction → UnwindAction
  | .continue_ => if inCleanup then .continue_ else callUnwind
  | .unreachable => .unreachable
  | .terminate => .terminate
  | .cleanup b => .cleanup (blockBase + b)

/-- Shift locals and basic blocks in a callee `TerminatorKind`, rewriting
non-cleanup `.return_` to `.goto exitBlock` while preserving cleanup `.return_`
(so cleanup `.return_` continues to fault `.unsupported` identically). -/
noncomputable def shiftCalleeTerminator (localBase blockBase exitBlock : Nat)
    (callUnwind : UnwindAction) (inCleanup : Bool) :
    TerminatorKind → TerminatorKind
  | .goto t => .goto (blockBase + t)
  | .switchInt d ts =>
    .switchInt (shiftOperand localBase d) (shiftSwitchTargets blockBase ts)
  | .return_ => if inCleanup then .return_ else .goto exitBlock
  | .unreachable => .unreachable
  | .unwindResume => .unwindResume
  | .assert c e m t u =>
    .assert (shiftOperand localBase c) e m (blockBase + t)
      (mapInlinedUnwind blockBase callUnwind inCleanup u)
  | .call f cArgs cDst cTarget cUnwind =>
    .call f (cArgs.map (shiftOperand localBase)) (shiftPlace localBase cDst)
      (cTarget.map (fun b => blockBase + b))
      (mapInlinedUnwind blockBase callUnwind inCleanup cUnwind)
  | .unsupported => .unsupported

/-- Shift an entire callee `BasicBlock` into caller local/block coordinates. -/
noncomputable def shiftCalleeBlock (localBase blockBase exitBlock : Nat)
    (callUnwind : UnwindAction) (bb : BasicBlock) : BasicBlock :=
  {
    statements := bb.statements.map (shiftStmt localBase)
    terminator :=
      shiftCalleeTerminator localBase blockBase exitBlock callUnwind bb.cleanup
        bb.terminator
    cleanup := bb.cleanup
  }

/-- Emit `StatementKind.storageLive (localBase + j)` for every callee local
that starts live at callee entry (`_0`, `_1 .. _argumentCount`, and every
var/temp `j > argumentCount` lacking a storage annotation in `callee`). -/
noncomputable def mkPrologueStorageLives (callee : Body) (localBase : Nat) :
    Nat → List MirTy → List StatementKind
  | _, [] => []
  | idx, _ :: rest =>
    let restStmts := mkPrologueStorageLives callee localBase (idx + 1) rest
    if Nat.beq idx 0 || Nat.ble idx callee.argumentCount ||
        !hasStorageAnnotation callee idx then
      .storageLive (localBase + idx) :: restStmts
    else
      restStmts

/-- Emit sequential left-to-right argument-binding assignments
`.assign ⟨localBase + 1 + i, []⟩ (.use arg_i)` matching `evalCallArgs`. -/
noncomputable def mkArgAssignStmts (localBase : Nat) :
    Nat → List Operand → List StatementKind
  | _, [] => []
  | idx, arg :: rest =>
    .assign ⟨localBase + 1 + idx, []⟩ (.use arg) ::
      mkArgAssignStmts localBase (idx + 1) rest

/-- Emit `StatementKind.storageDead (localBase + j)` for every callee local
`0 ≤ j < count`, resetting all shifted callee slots to `.dead` at `exitBlock`
(guaranteeing `hasStorageAnnotation` on all shifted slots and clean loop
re-entry). -/
noncomputable def mkEpilogueStorageDeads (localBase : Nat) :
    Nat → Nat → List StatementKind
  | _, 0 => []
  | idx, count + 1 =>
    .storageDead (localBase + idx) ::
      mkEpilogueStorageDeads localBase (idx + 1) count

/-- Single direct call-site inlining descriptor (`callerDefId ≠ calleeDefId` at
`callBlock`). -/
structure InlineSite where
  callerDefId : DefId
  calleeDefId : DefId
  callBlock : BasicBlockId

/-- Arbitrary finite sequence of MIR call-site inlining steps. -/
abbrev InlineTrace := List InlineSite

/-- Deterministically splice `site.calleeDefId` into `site.callerDefId` at
`site.callBlock`, failing closed (`none`) whenever any structural, typing,
acyclicity, or storage-hygiene guard is violated. -/
noncomputable def applyMirInlineCallSite (site : InlineSite)
    (pSrc : Program) : Option Program :=
  if Nat.beq site.callerDefId site.calleeDefId then
    none
  else
    match Trusted.MirSemantics.getElem? pSrc.bodies site.callerDefId,
        Trusted.MirSemantics.getElem? pSrc.bodies site.calleeDefId with
    | some callerSrc, some calleeSrc =>
      if !Nat.blt callerSrc.argumentCount callerSrc.locals.length ||
          !bodyAllLocalsInBounds callerSrc ||
          !bodyAllBlocksInBounds callerSrc ||
          !calleeCallAdmitted calleeSrc ||
          !bodyAllLocalsInBounds calleeSrc ||
          !bodyAllBlocksInBounds calleeSrc ||
          !bodyHasNoStorageDeadZero calleeSrc then
        none
      else
        match Trusted.MirSemantics.getElem? callerSrc.basicBlocks
            site.callBlock with
        | none => none
        | some callBb =>
          if callBb.cleanup then
            none
          else
            match callBb.terminator with
            | .call f args dst (some retBb) unwind =>
              if !Nat.beq f site.calleeDefId ||
                  !dst.projection.isEmpty ||
                  !Nat.blt dst.localId callerSrc.locals.length ||
                  !Nat.beq args.length calleeSrc.argumentCount then
                none
              else
                match Trusted.MirSemantics.getElem? callerSrc.locals dst.localId,
                    Trusted.MirSemantics.getElem? calleeSrc.locals 0 with
                | some dstTy, some calleeRetTy =>
                  if !MirTy.beq calleeRetTy dstTy then
                    none
                  else
                    let localBase := callerSrc.locals.length
                    let blockBase := callerSrc.basicBlocks.length
                    let exitBlock := blockBase + calleeSrc.basicBlocks.length
                    let prologueLiveStmts :=
                      mkPrologueStorageLives calleeSrc localBase 0
                        calleeSrc.locals
                    let argAssignStmts := mkArgAssignStmts localBase 0 args
                    let callBbTgt : BasicBlock := {
                      statements :=
                        callBb.statements ++ prologueLiveStmts ++ argAssignStmts
                      terminator := .goto blockBase
                      cleanup := false
                    }
                    let epilogueDeadStmts :=
                      mkEpilogueStorageDeads localBase 0 calleeSrc.locals.length
                    let exitBb : BasicBlock := {
                      statements :=
                        (.assign dst (.use (.move ⟨localBase, []⟩))) ::
                          epilogueDeadStmts
                      terminator := .goto retBb
                      cleanup := false
                    }
                    let shiftedCalleeBlocks :=
                      calleeSrc.basicBlocks.map
                        (shiftCalleeBlock localBase blockBase exitBlock unwind)
                    match setElem? callerSrc.basicBlocks site.callBlock
                        callBbTgt with
                    | none => none
                    | some callerBbsUpdated =>
                      let callerTgt : Body := {
                        callerSrc with
                        locals := callerSrc.locals ++ calleeSrc.locals
                        basicBlocks :=
                          callerBbsUpdated ++ shiftedCalleeBlocks ++ [exitBb]
                      }
                      match setElem? pSrc.bodies site.callerDefId callerTgt with
                      | none => none
                      | some bodiesTgt =>
                        some { pSrc with bodies := bodiesTgt }
                | _, _ => none
            | _ => none
    | _, _ => none

/-- Decidable single-site MIR inlining validator checking
`pSrc --[site]--> pTgt`. -/
noncomputable def checkMirInlineCallSite (site : InlineSite)
    (pSrc pTgt : Program) : Bool :=
  match applyMirInlineCallSite site pSrc with
  | some pOut => programEq pOut pTgt
  | none => false

/-- Deterministically execute an arbitrary finite `InlineTrace` on `pSrc`. -/
noncomputable def applyMirInlineTrace : InlineTrace → Program → Option Program
  | [], p => some p
  | site :: rest, p =>
    match applyMirInlineCallSite site p with
    | some pMid => applyMirInlineTrace rest pMid
    | none => none

/-- Decidable arbitrary-length multi-hop MIR inlining validator checking
`pSrc --[inlineTrace]*--> pTgt`. -/
noncomputable def checkMirInlineTrace (inlineTrace : InlineTrace)
    (pSrc pTgt : Program) : Bool :=
  match applyMirInlineTrace inlineTrace pSrc with
  | some pOut => programEq pOut pTgt
  | none => false

/-! ### Stage 4 Private Helpers — Slice A: Reflection, Lists, & AST Equality -/

private theorem if_bool_true {α : Type} {c : Bool} {t e : α} (h : c = true) :
    (if c then t else e) = t := by
  rw [h]; rfl

private theorem if_bool_false {α : Type} {c : Bool} {t e : α} (h : c = false) :
    (if c then t else e) = e := by
  rw [h]; rfl

private theorem bool_and_true {a b : Bool} (h : (a && b) = true) :
    a = true ∧ b = true := by
  cases a with
  | false => cases h
  | true =>
    cases b with
    | false => cases h
    | true => exact ⟨rfl, rfl⟩

private theorem bool_and_intro {a b : Bool} (ha : a = true) (hb : b = true) :
    (a && b) = true := by
  rw [ha, hb]; rfl

private theorem bool_or_true {a b : Bool} (h : (a || b) = true) :
    a = true ∨ b = true := by
  cases a with
  | true => exact Or.inl rfl
  | false =>
    cases b with
    | true => exact Or.inr rfl
    | false => cases h

private theorem bool_or_false {a b : Bool} (h : (a || b) = false) :
    a = false ∧ b = false := by
  cases a with
  | true => cases h
  | false =>
    cases b with
    | true => cases h
    | false => exact ⟨rfl, rfl⟩

private theorem bool_not_true {a : Bool} (h : (!a) = true) : a = false := by
  cases a with
  | false => rfl
  | true => cases h

private theorem bool_not_false {a : Bool} (h : (!a) = false) : a = true := by
  cases a with
  | true => rfl
  | false => cases h

private theorem bool_beq_eq {a b : Bool} (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

private theorem bool_beq_refl (a : Bool) : (a == a) = true := by
  cases a <;> rfl

private theorem nat_beq_refl (n : Nat) : Nat.beq n n = true := by
  induction n with
  | zero => rfl
  | succ _ ih => exact ih

private theorem nat_beq_eq {a b : Nat} (h : Nat.beq a b = true) : a = b := by
  induction a generalizing b with
  | zero =>
    cases b with
    | zero => rfl
    | succ _ => cases h
  | succ _ ih =>
    cases b with
    | zero => cases h
    | succ _ => rw [ih h]

private theorem nat_beq_of_eq {a b : Nat} (h : a = b) : Nat.beq a b = true := by
  subst h; exact nat_beq_refl a

private theorem nat_beq_false_of_ne {a b : Nat} (h : a ≠ b) :
    Nat.beq a b = false := by
  cases hEq : Nat.beq a b with
  | false => rfl
  | true => exact False.elim (h (nat_beq_eq hEq))

private theorem nat_ne_of_beq_false {a b : Nat} (h : Nat.beq a b = false) : a ≠ b := by
  intro hEq
  rw [hEq, nat_beq_refl] at h
  cases h

private theorem nat_ble_le {a b : Nat} (h : Nat.ble a b = true) : a ≤ b := by
  induction a generalizing b with
  | zero => exact Nat.zero_le b
  | succ _ ih =>
    cases b with
    | zero => cases h
    | succ _ => exact Nat.succ_le_succ (ih h)

private theorem nat_le_ble {a b : Nat} (h : a ≤ b) : Nat.ble a b = true := by
  induction a generalizing b with
  | zero => rfl
  | succ k ih =>
    cases b with
    | zero => exact False.elim (Nat.not_succ_le_zero k h)
    | succ _ => exact ih (Nat.le_of_succ_le_succ h)

private theorem nat_ble_false_gt {a b : Nat} (h : Nat.ble a b = false) : b < a := by
  cases Nat.lt_or_ge b a with
  | inl hlt => exact hlt
  | inr hle =>
    rw [nat_le_ble hle] at h
    cases h

private theorem nat_gt_ble_false {a b : Nat} (h : b < a) : Nat.ble a b = false := by
  cases hB : Nat.ble a b with
  | false => rfl
  | true => exact False.elim (Nat.not_lt_of_ge (nat_ble_le hB) h)

private theorem nat_blt_lt {a b : Nat} (h : Nat.blt a b = true) : a < b :=
  nat_ble_le h

private theorem nat_lt_blt {a b : Nat} (h : a < b) : Nat.blt a b = true :=
  nat_le_ble h

private theorem nat_blt_false_ge {a b : Nat} (h : Nat.blt a b = false) : b ≤ a := by
  cases Nat.lt_or_ge a b with
  | inl hlt =>
    rw [nat_lt_blt hlt] at h
    cases h
  | inr hge => exact hge

private theorem nat_ge_blt_false {a b : Nat} (h : b ≤ a) : Nat.blt a b = false := by
  cases hB : Nat.blt a b with
  | false => rfl
  | true => exact False.elim (Nat.not_lt_of_ge h (nat_blt_lt hB))

private theorem nat_add_ne_zero_left {a b : Nat} (h : 0 < a) : a + b ≠ 0 := by
  intro hEq
  cases a with
  | zero => exact Nat.not_lt_zero 0 h
  | succ k =>
    rw [Nat.succ_add] at hEq
    cases hEq

private theorem nat_lt_add_right {a b : Nat} (c : Nat) (h : a < b) : a < b + c :=
  Nat.lt_of_lt_of_le h (Nat.le_add_right b c)

private theorem nat_add_lt_add_left_of_lt {a b : Nat} (c : Nat) (h : a < b) :
    c + a < c + b :=
  Nat.add_lt_add_left h c

private theorem nat_lt_of_add_lt_add_left {a b c : Nat} (h : c + a < c + b) :
    a < b := by
  induction c with
  | zero =>
    rw [Nat.zero_add, Nat.zero_add] at h
    exact h
  | succ _ ih =>
    rw [Nat.succ_add, Nat.succ_add] at h
    exact ih (Nat.lt_of_succ_lt_succ h)

private theorem nat_ne_add_left_of_lt {l base j : Nat} (h : l < base) :
    base + j ≠ l := by
  intro hEq
  exact Nat.not_lt_of_ge (Nat.le_add_right base j) (hEq ▸ h)

private theorem nat_beq_add_left_of_lt {l base j : Nat} (h : l < base) :
    Nat.beq (base + j) l = false :=
  nat_beq_false_of_ne (nat_ne_add_left_of_lt h)

private theorem nat_add_sub_cancel_left (a b : Nat) : (a + b) - a = b := by
  rw [Nat.add_comm]
  exact Nat.add_sub_cancel b a

private theorem nat_sub_add_cancel_of_le {a b : Nat} (h : a ≤ b) :
    a + (b - a) = b := by
  rw [Nat.add_comm]
  exact Nat.sub_add_cancel h

private theorem bitvec_beq_eq {n : Nat} {a b : BitVec n}
    (h : (a == b) = true) : a = b :=
  eq_of_beq h

private theorem uint8_beq_eq {a b : UInt8} (h : (a == b) = true) : a = b :=
  eq_of_beq h

private theorem uint8_list_beq_eq {xs ys : List UInt8}
    (h : List.beq xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases h
  | cons x xs ih =>
    cases ys with
    | nil => cases h
    | cons y ys =>
      let ⟨h1, h2⟩ := bool_and_true h
      rw [uint8_beq_eq h1, ih h2]

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

private theorem intWidth_beq_eq {a b : IntWidth}
    (h : IntWidth.beq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

private theorem intWidth_beq_refl (a : IntWidth) : IntWidth.beq a a = true := by
  cases a <;> rfl

private theorem mutability_beq_eq {a b : Mutability}
    (h : Mutability.beq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

private theorem mutability_beq_refl (a : Mutability) : Mutability.beq a a = true := by
  cases a <;> rfl

private theorem natListBeq_eq {a b : List Nat}
    (h : natListBeq a b = true) : a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons _ _ => cases h
  | cons _ _ ih =>
    cases b with
    | nil => cases h
    | cons _ _ =>
      let ⟨h1, h2⟩ := bool_and_true h
      rw [nat_beq_eq h1, ih h2]

private theorem natListBeq_refl (a : List Nat) : natListBeq a a = true := by
  induction a with
  | nil => rfl
  | cons x _ ih =>
    dsimp [natListBeq]
    rw [nat_beq_refl x, ih]
    rfl

private theorem enumTagRepr_beq_eq {a b : EnumTagRepr}
    (h : EnumTagRepr.beq a b = true) : a = b := by
  cases a with
  | zeroSized =>
    cases b with
    | zeroSized => rfl
    | scalar _ _ => cases h
  | scalar _ _ =>
    cases b with
    | zeroSized => cases h
    | scalar _ _ =>
      let ⟨h1, h2⟩ := bool_and_true h
      rw [intWidth_beq_eq h1, bool_beq_eq h2]

private theorem enumTagRepr_beq_refl (a : EnumTagRepr) :
    EnumTagRepr.beq a a = true := by
  cases a with
  | zeroSized => rfl
  | scalar w s =>
    dsimp [EnumTagRepr.beq]
    rw [intWidth_beq_refl w]
    cases s <;> rfl

private theorem enumTy_beq_eq {a b : EnumTy}
    (h : EnumTy.beq a b = true) : a = b := by
  cases a with
  | mk _ _ _ _ _ =>
    cases b with
    | mk _ _ _ _ _ =>
      dsimp [EnumTy.beq] at h
      let ⟨h1234, h5⟩ := bool_and_true h
      let ⟨h123, h4⟩ := bool_and_true h1234
      let ⟨h12, h3⟩ := bool_and_true h123
      let ⟨h1, h2⟩ := bool_and_true h12
      rw [nat_beq_eq h1, intWidth_beq_eq h2, bool_beq_eq h3,
          enumTagRepr_beq_eq h4, natListBeq_eq h5]

private theorem enumTy_beq_refl (a : EnumTy) : EnumTy.beq a a = true := by
  cases a with
  | mk id w s tr ds =>
    unfold EnumTy.beq
    rw [nat_beq_refl id, intWidth_beq_refl w, enumTagRepr_beq_refl tr,
        natListBeq_refl ds]
    cases s <;> rfl

mutual
  private theorem mirTy_beq_eq : ∀ {a b : MirTy}, MirTy.beq a b = true → a = b
    | .bool, .bool, _ => rfl
    | .int _ _, .int _ _, h => by
      let ⟨h1, h2⟩ := bool_and_true h
      rw [intWidth_beq_eq h1, bool_beq_eq h2]
    | .unit, .unit, _ => rfl
    | .never, .never, _ => rfl
    | .enum _, .enum _, h => by rw [enumTy_beq_eq h]
    | .tuple _, .tuple _, h => by rw [mirTy_beqList_eq h]
    | .ref _ _, .ref _ _, h => by
      let ⟨h1, h2⟩ := bool_and_true h
      rw [mutability_beq_eq h1, mirTy_beq_eq h2]
    | .rawPtr _ _, .rawPtr _ _, h => by
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
    | .unsupported, .bool, h | .unsupported, .int _ _, h | .unsupported, .unit, h
    | .unsupported, .never, h | .unsupported, .enum _, h | .unsupported, .tuple _, h
    | .unsupported, .ref _ _, h | .unsupported, .rawPtr _ _, h =>
      by cases h

  private theorem mirTy_beqList_eq :
      ∀ {a b : List MirTy}, MirTy.beqList a b = true → a = b
    | [], [], _ => rfl
    | _ :: _, _ :: _, h => by
      let ⟨h1, h2⟩ := bool_and_true h
      rw [mirTy_beq_eq h1, mirTy_beqList_eq h2]
    | [], _ :: _, h | _ :: _, [], h => by cases h
end

mutual
  private theorem mirTy_beq_refl : ∀ (t : MirTy), MirTy.beq t t = true
    | .bool => rfl
    | .int w s => by
      change (IntWidth.beq w w && (s == s)) = true
      rw [intWidth_beq_refl w, bool_beq_refl s]
      rfl
    | .unit => rfl
    | .never => rfl
    | .enum ety => enumTy_beq_refl ety
    | .tuple fs => mirTy_beqList_refl fs
    | .ref m p => by
      change (Mutability.beq m m && MirTy.beq p p) = true
      rw [mutability_beq_refl m, mirTy_beq_refl p]
      rfl
    | .rawPtr m p => by
      change (Mutability.beq m m && MirTy.beq p p) = true
      rw [mutability_beq_refl m, mirTy_beq_refl p]
      rfl
    | .unsupported => rfl

  private theorem mirTy_beqList_refl : ∀ (fs : List MirTy), MirTy.beqList fs fs = true
    | [] => rfl
    | x :: xs => by
      change (MirTy.beq x x && MirTy.beqList xs xs) = true
      rw [mirTy_beq_refl x, mirTy_beqList_refl xs]
      rfl
end

private theorem listRel_length {α β : Type} {r : α → β → Bool}
    {xs : List α} {ys : List β} (h : listRel r xs ys = true) :
    xs.length = ys.length := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases h
  | cons _ _ ih =>
    cases ys with
    | nil => cases h
    | cons _ _ =>
      let ⟨_, h2⟩ := bool_and_true h
      dsimp [List.length]
      rw [ih h2]

private theorem listRel_eq {α : Type} {r : α → α → Bool}
    (hEq : ∀ x y, r x y = true → x = y) {xs ys : List α}
    (hRel : listRel r xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases hRel
  | cons x _ ih =>
    cases ys with
    | nil => cases hRel
    | cons y _ =>
      let ⟨h1, h2⟩ := bool_and_true hRel
      rw [hEq x y h1, ih h2]

private theorem listRel_getElem?_left {α β : Type} {r : α → β → Bool}
    {xs : List α} {ys : List β} {i : Nat} {x : α}
    (hRel : listRel r xs ys = true)
    (hGet : Trusted.MirSemantics.getElem? xs i = some x) :
    ∃ y, Trusted.MirSemantics.getElem? ys i = some y ∧ r x y = true := by
  induction xs generalizing ys i with
  | nil => cases hGet
  | cons a _ ih =>
    cases ys with
    | nil => cases hRel
    | cons b _ =>
      let ⟨hab, hTail⟩ := bool_and_true hRel
      cases i with
      | zero =>
        injection hGet with hxa
        subst hxa
        exact ⟨b, rfl, hab⟩
      | succ _ =>
        dsimp [Trusted.MirSemantics.getElem?]
        exact ih hTail hGet

private theorem listRel_getElem?_right {α β : Type} {r : α → β → Bool}
    {xs : List α} {ys : List β} {i : Nat} {y : β}
    (hRel : listRel r xs ys = true)
    (hGet : Trusted.MirSemantics.getElem? ys i = some y) :
    ∃ x, Trusted.MirSemantics.getElem? xs i = some x ∧ r x y = true := by
  induction xs generalizing ys i with
  | nil =>
    cases ys with
    | nil => cases hGet
    | cons _ _ => cases hRel
  | cons a _ ih =>
    cases ys with
    | nil => cases hRel
    | cons b _ =>
      let ⟨hab, hTail⟩ := bool_and_true hRel
      cases i with
      | zero =>
        injection hGet with hyb
        subst hyb
        exact ⟨a, rfl, hab⟩
      | succ _ =>
        dsimp [Trusted.MirSemantics.getElem?]
        exact ih hTail hGet

private theorem list_map_eq_of_rel {α β γ : Type} {r : α → β → Bool}
    {f : α → γ} {g : β → γ} {xs : List α} {ys : List β}
    (hRel : listRel r xs ys = true)
    (hFG : ∀ a b, r a b = true → f a = g b) :
    xs.map f = ys.map g := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases hRel
  | cons a _ ih =>
    cases ys with
    | nil => cases hRel
    | cons b _ =>
      let ⟨hab, hTail⟩ := bool_and_true hRel
      dsimp [List.map]
      rw [hFG a b hab, ih hTail]

private theorem projElemEq_eq {a b : ProjectionElem}
    (h : projElemEq a b = true) : a = b := by
  cases a with
  | deref => cases b <;> first | rfl | cases h
  | field _ _ =>
    cases b with
    | field _ _ =>
      let ⟨h1, h2⟩ := bool_and_true h
      rw [nat_beq_eq h1, mirTy_beq_eq h2]
    | _ => cases h
  | unsupported => cases b <;> first | rfl | cases h

private theorem placeEq_eq {a b : Place} (h : placeEq a b = true) : a = b := by
  cases a with
  | mk _ _ =>
    cases b with
    | mk _ _ =>
      dsimp [placeEq] at h
      let ⟨h1, h2⟩ := bool_and_true h
      rw [nat_beq_eq h1, listRel_eq (fun _ _ => projElemEq_eq) h2]

private theorem constLitEq_eq {a b : ConstLit}
    (h : constLitEq a b = true) : a = b := by
  cases a with
  | scalar _ =>
    cases b with
    | scalar _ => rw [bitvec_beq_eq h]
    | zeroSized => cases h
  | zeroSized =>
    cases b with
    | scalar _ => cases h
    | zeroSized => rfl

private theorem constOpEq_eq {a b : ConstOperand}
    (h : constOpEq a b = true) : a = b := by
  cases a with
  | mk _ _ =>
    cases b with
    | mk _ _ =>
      dsimp [constOpEq] at h
      let ⟨h1, h2⟩ := bool_and_true h
      rw [mirTy_beq_eq h1, constLitEq_eq h2]

private theorem binOpEq_eq {a b : BinOp} (h : binOpEq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

private theorem unOpEq_eq {a b : UnOp} (h : unOpEq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

private theorem operandEq_eq {a b : Operand}
    (h : operandEq a b = true) : a = b := by
  cases a with
  | copy _ =>
    cases b with
    | copy _ => rw [placeEq_eq h]
    | _ => cases h
  | move _ =>
    cases b with
    | move _ => rw [placeEq_eq h]
    | _ => cases h
  | constant _ =>
    cases b with
    | constant _ => rw [constOpEq_eq h]
    | _ => cases h

private theorem rvalueEq_eq {a b : Rvalue}
    (h : rvalueEq a b = true) : a = b := by
  cases a with
  | use _ =>
    cases b with
    | use _ => rw [operandEq_eq h]
    | _ => cases h
  | binaryOp _ _ _ =>
    cases b with
    | binaryOp _ _ _ =>
      let ⟨h12, h3⟩ := bool_and_true h
      let ⟨h1, h2⟩ := bool_and_true h12
      rw [binOpEq_eq h1, operandEq_eq h2, operandEq_eq h3]
    | _ => cases h
  | unaryOp _ _ =>
    cases b with
    | unaryOp _ _ =>
      let ⟨h1, h2⟩ := bool_and_true h
      rw [unOpEq_eq h1, operandEq_eq h2]
    | _ => cases h
  | discriminant _ =>
    cases b with
    | discriminant _ => rw [placeEq_eq h]
    | _ => cases h
  | ref _ _ =>
    cases b with
    | ref _ _ =>
      let ⟨h1, h2⟩ := bool_and_true h
      rw [mutability_beq_eq h1, placeEq_eq h2]
    | _ => cases h
  | addressOf _ _ =>
    cases b with
    | addressOf _ _ =>
      let ⟨h1, h2⟩ := bool_and_true h
      rw [mutability_beq_eq h1, placeEq_eq h2]
    | _ => cases h
  | aggregateTuple _ =>
    cases b with
    | aggregateTuple _ =>
      rw [listRel_eq (fun _ _ => operandEq_eq) h]
    | _ => cases h
  | unsupported =>
    cases b <;> first | rfl | cases h

private theorem stmtEq_eq {a b : StatementKind}
    (h : stmtEq a b = true) : a = b := by
  cases a with
  | assign _ _ =>
    cases b with
    | assign _ _ =>
      let ⟨h1, h2⟩ := bool_and_true h
      rw [placeEq_eq h1, rvalueEq_eq h2]
    | _ => cases h
  | storageLive _ =>
    cases b with
    | storageLive _ => rw [nat_beq_eq h]
    | _ => cases h
  | storageDead _ =>
    cases b with
    | storageDead _ => rw [nat_beq_eq h]
    | _ => cases h
  | nop => cases b <;> first | rfl | cases h
  | unsupported => cases b <;> first | rfl | cases h

private theorem switchTargetsEq_eq {a b : SwitchTargets}
    (h : switchTargetsEq a b = true) : a = b := by
  cases a with
  | mk bs1 ow1 =>
    cases b with
    | mk bs2 ow2 =>
      dsimp [switchTargetsEq] at h
      let ⟨h1, h2⟩ := bool_and_true h
      have hOw : ow1 = ow2 := nat_beq_eq h1
      have hBs : bs1 = bs2 := listRel_eq (fun x y hxy => by
        cases x with
        | mk _ _ =>
          cases y with
          | mk _ _ =>
            dsimp at hxy
            let ⟨hv, ht⟩ := bool_and_true hxy
            rw [bitvec_beq_eq hv, nat_beq_eq ht]) h2
      rw [hOw, hBs]

private theorem unwindActionEq_eq {a b : UnwindAction}
    (h : unwindActionEq a b = true) : a = b := by
  cases a with
  | cleanup _ =>
    cases b with
    | cleanup _ => rw [nat_beq_eq h]
    | _ => cases h
  | continue_ => cases b <;> first | rfl | cases h
  | unreachable => cases b <;> first | rfl | cases h
  | terminate => cases b <;> first | rfl | cases h

private theorem assertKindEq_eq {a b : AssertKind}
    (h : assertKindEq a b = true) : a = b := by
  cases a with
  | overflow _ =>
    cases b with
    | overflow _ => rw [binOpEq_eq h]
    | _ => cases h
  | overflowNeg => cases b <;> first | rfl | cases h
  | divByZero => cases b <;> first | rfl | cases h
  | remByZero => cases b <;> first | rfl | cases h
  | boundsCheck => cases b <;> first | rfl | cases h
  | misalignedPtrDeref => cases b <;> first | rfl | cases h
  | nullPtrDeref => cases b <;> first | rfl | cases h
  | unsupported => cases b <;> first | rfl | cases h

private theorem optBlockEq_eq {a b : Option BasicBlockId}
    (h : optBlockEq a b = true) : a = b := by
  cases a with
  | none => cases b <;> first | rfl | cases h
  | some _ =>
    cases b with
    | some _ => rw [nat_beq_eq h]
    | none => cases h

private theorem terminatorEq_eq {a b : TerminatorKind}
    (h : terminatorEq a b = true) : a = b := by
  cases a with
  | goto _ =>
    cases b with
    | goto _ => rw [nat_beq_eq h]
    | _ => cases h
  | switchInt _ _ =>
    cases b with
    | switchInt _ _ =>
      let ⟨h1, h2⟩ := bool_and_true h
      rw [operandEq_eq h1, switchTargetsEq_eq h2]
    | _ => cases h
  | return_ => cases b <;> first | rfl | cases h
  | unreachable => cases b <;> first | rfl | cases h
  | unwindResume => cases b <;> first | rfl | cases h
  | assert _ _ _ _ _ =>
    cases b with
    | assert _ _ _ _ _ =>
      let ⟨h1234, h5⟩ := bool_and_true h
      let ⟨h123, h4⟩ := bool_and_true h1234
      let ⟨h12, h3⟩ := bool_and_true h123
      let ⟨h1, h2⟩ := bool_and_true h12
      rw [operandEq_eq h1, bool_beq_eq h2, assertKindEq_eq h3,
          nat_beq_eq h4, unwindActionEq_eq h5]
    | _ => cases h
  | call _ _ _ _ _ =>
    cases b with
    | call _ _ _ _ _ =>
      let ⟨h1234, h5⟩ := bool_and_true h
      let ⟨h123, h4⟩ := bool_and_true h1234
      let ⟨h12, h3⟩ := bool_and_true h123
      let ⟨h1, h2⟩ := bool_and_true h12
      rw [nat_beq_eq h1, listRel_eq (fun _ _ => operandEq_eq) h2,
          placeEq_eq h3, optBlockEq_eq h4, unwindActionEq_eq h5]
    | _ => cases h
  | unsupported => cases b <;> first | rfl | cases h

private theorem blockEq_eq {a b : BasicBlock} (h : blockEq a b = true) : a = b := by
  cases a with
  | mk _ _ _ =>
    cases b with
    | mk _ _ _ =>
      dsimp [blockEq] at h
      let ⟨h12, h3⟩ := bool_and_true h
      let ⟨h1, h2⟩ := bool_and_true h12
      rw [bool_beq_eq h1, listRel_eq (fun _ _ => stmtEq_eq) h2,
          terminatorEq_eq h3]

private theorem scopeEq_eq {a b : VerificationScope}
    (h : scopeEq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

private theorem bodyHeaderEq_elim {b₁ b₂ : Body}
    (h : bodyHeaderEq b₁ b₂ = true) :
    b₁.argumentCount = b₂.argumentCount ∧
    b₁.locals = b₂.locals ∧
    b₁.isUnsafe = b₂.isUnsafe ∧
    b₁.identity = b₂.identity := by
  unfold bodyHeaderEq at h
  let ⟨h123, hId⟩ := bool_and_true h
  let ⟨h12, hUns⟩ := bool_and_true h123
  let ⟨hArg, hLoc⟩ := bool_and_true h12
  exact ⟨nat_beq_eq hArg, mirTy_beqList_eq hLoc, bool_beq_eq hUns,
         stringBeq_eq hId⟩

private theorem bodyEq_eq {b₁ b₂ : Body} (h : bodyEq b₁ b₂ = true) : b₁ = b₂ := by
  cases b₁ with
  | mk _ _ _ _ _ =>
    cases b₂ with
    | mk _ _ _ _ _ =>
      unfold bodyEq at h
      let ⟨hHdr, hBbs⟩ := bool_and_true h
      let ⟨hArg, hLoc, hUns, hId⟩ := bodyHeaderEq_elim hHdr
      have hB := listRel_eq (fun _ _ => blockEq_eq) hBbs
      dsimp at hArg hLoc hUns hId hB
      rw [hArg, hLoc, hUns, hId, hB]

private theorem programHeaderEq_elim {p₁ p₂ : Program}
    (h : programHeaderEq p₁ p₂ = true) :
    p₁.pointerWidthBits = p₂.pointerWidthBits ∧
    p₁.mirProfileVersion = p₂.mirProfileVersion ∧
    p₁.entryDefId = p₂.entryDefId ∧
    p₁.scope = p₂.scope := by
  unfold programHeaderEq at h
  let ⟨h123, hSc⟩ := bool_and_true h
  let ⟨h12, hEnt⟩ := bool_and_true h123
  let ⟨hPw, hVer⟩ := bool_and_true h12
  exact ⟨nat_beq_eq hPw, nat_beq_eq hVer, nat_beq_eq hEnt, scopeEq_eq hSc⟩

private theorem programEq_eq {p₁ p₂ : Program} (h : programEq p₁ p₂ = true) :
    p₁ = p₂ := by
  cases p₁ with
  | mk _ _ _ _ _ =>
    cases p₂ with
    | mk _ _ _ _ _ =>
      unfold programEq at h
      let ⟨hHdr, hBods⟩ := bool_and_true h
      let ⟨hPw, hVer, hEnt, hSc⟩ := programHeaderEq_elim hHdr
      have hB := listRel_eq (fun _ _ => bodyEq_eq) hBods
      dsimp at hPw hVer hEnt hSc hB
      rw [hPw, hVer, hEnt, hSc, hB]

/-! ### List, `getElem?`, `setElem?`, Append, Map, Replicate, &
`initLocalsLoop` Helpers -/

private theorem getElem?_some_lt {α : Type} {xs : List α} {i : Nat} {x : α}
    (h : Trusted.MirSemantics.getElem? xs i = some x) : i < xs.length := by
  induction xs generalizing i with
  | nil => cases h
  | cons _ xs ih =>
    cases i with
    | zero => exact Nat.zero_lt_succ xs.length
    | succ _ => exact Nat.succ_lt_succ (ih h)

private theorem getElem?_none_of_ge {α : Type} {xs : List α} {i : Nat}
    (h : xs.length ≤ i) : Trusted.MirSemantics.getElem? xs i = none := by
  induction xs generalizing i with
  | nil => rfl
  | cons _ xs ih =>
    cases i with
    | zero => exact False.elim (Nat.not_succ_le_zero xs.length h)
    | succ _ => exact ih (Nat.le_of_succ_le_succ h)

private theorem getElem?_some_of_lt {α : Type} (xs : List α) (i : Nat)
    (h : i < xs.length) :
    ∃ x, Trusted.MirSemantics.getElem? xs i = some x := by
  induction xs generalizing i with
  | nil => exact False.elim (Nat.not_lt_zero i h)
  | cons a _ ih =>
    cases i with
    | zero => exact ⟨a, rfl⟩
    | succ k => exact ih k (Nat.lt_of_succ_lt_succ h)

private theorem getElem?_none_ge {α : Type} {xs : List α} {i : Nat}
    (h : Trusted.MirSemantics.getElem? xs i = none) : xs.length ≤ i := by
  cases Nat.lt_or_ge i xs.length with
  | inl hlt =>
    let ⟨_, hx⟩ := getElem?_some_of_lt xs i hlt
    rw [h] at hx
    cases hx
  | inr hge => exact hge

private theorem list_eq_of_getElem?_eq {α : Type} {xs ys : List α}
    (hLen : xs.length = ys.length)
    (hAt : ∀ i, Trusted.MirSemantics.getElem? xs i =
      Trusted.MirSemantics.getElem? ys i) :
    xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases hLen
  | cons _ _ ih =>
    cases ys with
    | nil => cases hLen
    | cons _ _ =>
      have h0 := hAt 0
      dsimp [Trusted.MirSemantics.getElem?] at h0
      injection h0 with hxy
      subst hxy
      rw [ih (Nat.succ.inj hLen) (fun i => hAt (i + 1))]

private theorem setElem?_length {α : Type} {xs xs' : List α} {i : Nat} {v : α}
    (h : setElem? xs i v = some xs') : xs'.length = xs.length := by
  induction xs generalizing xs' i with
  | nil => cases h
  | cons _ _ ih =>
    cases i with
    | zero =>
      injection h with hEq; subst hEq; rfl
    | succ k =>
      dsimp [setElem?] at h
      cases hSub : setElem? _ k v with
      | none => rw [hSub] at h; cases h
      | some _ =>
        rw [hSub] at h
        injection h with hEq; subst hEq
        dsimp [List.length]
        rw [ih hSub]

private theorem setElem?_getElem?_same {α : Type} {xs xs' : List α} {i : Nat} {v : α}
    (h : setElem? xs i v = some xs') :
    Trusted.MirSemantics.getElem? xs' i = some v := by
  induction xs generalizing xs' i with
  | nil => cases h
  | cons _ _ ih =>
    cases i with
    | zero =>
      injection h with hEq; subst hEq; rfl
    | succ k =>
      dsimp [setElem?] at h
      cases hSub : setElem? _ k v with
      | none => rw [hSub] at h; cases h
      | some _ =>
        rw [hSub] at h
        injection h with hEq; subst hEq
        dsimp [Trusted.MirSemantics.getElem?]
        exact ih hSub

private theorem setElem?_getElem?_ne {α : Type} {xs xs' : List α} {i j : Nat} {v : α}
    (h : setElem? xs i v = some xs') (hNe : j ≠ i) :
    Trusted.MirSemantics.getElem? xs' j =
      Trusted.MirSemantics.getElem? xs j := by
  induction xs generalizing xs' i j with
  | nil => cases h
  | cons _ _ ih =>
    cases i with
    | zero =>
      injection h with hEq; subst hEq
      cases j with
      | zero => exact False.elim (hNe rfl)
      | succ _ => rfl
    | succ k =>
      dsimp [setElem?] at h
      cases hSub : setElem? _ k v with
      | none => rw [hSub] at h; cases h
      | some _ =>
        rw [hSub] at h
        injection h with hEq; subst hEq
        cases j with
        | zero => rfl
        | succ _ => exact ih hSub (fun hEq => hNe (by rw [hEq]))

private theorem setElem?_some_of_lt {α : Type} (xs : List α) (i : Nat) (v : α)
    (h : i < xs.length) : ∃ xs', setElem? xs i v = some xs' := by
  induction xs generalizing i with
  | nil => exact False.elim (Nat.not_lt_zero i h)
  | cons a _ ih =>
    cases i with
    | zero => exact ⟨v :: _, rfl⟩
    | succ k =>
      let ⟨sub, hSub⟩ := ih k (Nat.lt_of_succ_lt_succ h)
      exact ⟨a :: sub, by dsimp [setElem?]; rw [hSub]⟩

private theorem setElem?_none_of_ge {α : Type} (xs : List α) (i : Nat) (v : α)
    (h : xs.length ≤ i) : setElem? xs i v = none := by
  induction xs generalizing i with
  | nil => rfl
  | cons _ _ ih =>
    cases i with
    | zero => exact False.elim (Nat.not_succ_le_zero _ h)
    | succ k =>
      dsimp [setElem?]
      rw [ih k (Nat.le_of_succ_le_succ h)]

private theorem list_append_length {α : Type} (xs ys : List α) :
    (xs ++ ys).length = xs.length + ys.length := by
  induction xs with
  | nil => dsimp [List.length]; rw [Nat.zero_add]
  | cons _ rest ih =>
    dsimp [List.length]
    rw [ih, Nat.succ_add]

private theorem getElem?_append_left {α : Type} (xs ys : List α) (i : Nat)
    (h : i < xs.length) :
    Trusted.MirSemantics.getElem? (xs ++ ys) i =
      Trusted.MirSemantics.getElem? xs i := by
  induction xs generalizing i with
  | nil => exact False.elim (Nat.not_lt_zero i h)
  | cons _ _ ih =>
    cases i with
    | zero => rfl
    | succ k => exact ih k (Nat.lt_of_succ_lt_succ h)

private theorem getElem?_append_right_add {α : Type} (xs ys : List α) (j : Nat) :
    Trusted.MirSemantics.getElem? (xs ++ ys) (xs.length + j) =
      Trusted.MirSemantics.getElem? ys j := by
  induction xs with
  | nil =>
    dsimp [List.length]
    rw [Nat.zero_add]
  | cons _ rest ih =>
    dsimp [List.length]
    rw [Nat.succ_add]
    exact ih

private theorem getElem?_append_right {α : Type} (xs ys : List α) (i : Nat)
    (h : xs.length ≤ i) :
    Trusted.MirSemantics.getElem? (xs ++ ys) i =
      Trusted.MirSemantics.getElem? ys (i - xs.length) := by
  have hEq := nat_sub_add_cancel_of_le h
  rw [← hEq]
  have hSub := nat_add_sub_cancel_left xs.length (i - xs.length)
  rw [hSub]
  exact getElem?_append_right_add xs ys (i - xs.length)

private theorem setElem?_append_left {α : Type} (xs ys : List α) (i : Nat) (v : α)
    (h : i < xs.length) :
    setElem? (xs ++ ys) i v = (setElem? xs i v).map (fun xs' => xs' ++ ys) := by
  induction xs generalizing i with
  | nil => exact False.elim (Nat.not_lt_zero i h)
  | cons a rest ih =>
    cases i with
    | zero => rfl
    | succ k =>
      dsimp [setElem?]
      rw [ih k (Nat.lt_of_succ_lt_succ h)]
      cases setElem? rest k v <;> rfl

private theorem setElem?_append_right_add {α : Type} (xs ys : List α) (j : Nat)
    (v : α) :
    setElem? (xs ++ ys) (xs.length + j) v =
      (setElem? ys j v).map (fun ys' => xs ++ ys') := by
  induction xs with
  | nil =>
    dsimp [List.length]
    rw [Nat.zero_add]
    cases setElem? ys j v <;> rfl
  | cons a rest ih =>
    dsimp [List.length]
    rw [Nat.succ_add]
    dsimp [setElem?]
    rw [ih]
    cases setElem? ys j v <;> rfl

private theorem list_replicate_length {α : Type} (n : Nat) (x : α) :
    (List.replicate n x).length = n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    dsimp [List.replicate, List.length]
    rw [ih]

private theorem getElem?_replicate_lt {α : Type} (n : Nat) (x : α) (i : Nat)
    (h : i < n) :
    Trusted.MirSemantics.getElem? (List.replicate n x) i = some x := by
  induction n generalizing i with
  | zero => exact False.elim (Nat.not_lt_zero i h)
  | succ k ih =>
    cases i with
    | zero => rfl
    | succ m => exact ih m (Nat.lt_of_succ_lt_succ h)

private theorem map_length_eq {α β : Type} (f : α → β) (xs : List α) :
    (xs.map f).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons _ _ ih =>
    dsimp [List.map, List.length]
    rw [ih]

private theorem getElem?_map {α β : Type} (f : α → β) (xs : List α) (i : Nat) :
    Trusted.MirSemantics.getElem? (xs.map f) i =
      (Trusted.MirSemantics.getElem? xs i).map f := by
  induction xs generalizing i with
  | nil => rfl
  | cons _ _ ih =>
    cases i with
    | zero => rfl
    | succ k => exact ih k

private theorem map_setElem? {α β : Type} (f : α → β) {xs xs' : List α} {i : Nat}
    {v : α} (h : setElem? xs i v = some xs') :
    setElem? (xs.map f) i (f v) = some (xs'.map f) := by
  induction xs generalizing xs' i with
  | nil => cases h
  | cons a rest ih =>
    cases i with
    | zero =>
      injection h with hEq; subst hEq; rfl
    | succ k =>
      dsimp [setElem?] at h
      cases hSub : setElem? rest k v with
      | none => rw [hSub] at h; cases h
      | some sub =>
        rw [hSub] at h
        injection h with hEq; subst hEq
        dsimp [List.map, setElem?]
        rw [ih hSub]

private theorem list_all_getElem? {α : Type} {p : α → Bool} {xs : List α}
    {i : Nat} {x : α} (hAll : xs.all p = true)
    (hGet : Trusted.MirSemantics.getElem? xs i = some x) : p x = true := by
  induction xs generalizing i with
  | nil => cases hGet
  | cons a rest ih =>
    let ⟨ha, hRest⟩ := bool_and_true hAll
    cases i with
    | zero =>
      injection hGet with hEq; subst hEq; exact ha
    | succ k => exact ih hRest hGet

private theorem list_all_of_forall_getElem? {α : Type} {p : α → Bool} {xs : List α}
    (h : ∀ i x, Trusted.MirSemantics.getElem? xs i = some x → p x = true) :
    xs.all p = true := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    have ha : p a = true := h 0 a rfl
    have hRest : rest.all p = true :=
      ih (fun i x hG => h (i + 1) x hG)
    exact bool_and_intro ha hRest

private theorem list_all_append {α : Type} (p : α → Bool) (xs ys : List α) :
    (xs ++ ys).all p = (xs.all p && ys.all p) := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    dsimp [List.all]
    cases p a with
    | false => rfl
    | true => exact ih

private theorem list_all_map {α β : Type} (p : β → Bool) (f : α → β) (xs : List α) :
    (xs.map f).all p = xs.all (fun a => p (f a)) := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    dsimp [List.map, List.all]
    cases p (f a) with
    | false => rfl
    | true => exact ih

private theorem list_any_append {α : Type} (p : α → Bool) (xs ys : List α) :
    (xs ++ ys).any p = (xs.any p || ys.any p) := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    dsimp [List.any]
    cases p a with
    | true => rfl
    | false => exact ih

private theorem list_any_map {α β : Type} (p : β → Bool) (f : α → β) (xs : List α) :
    (xs.map f).any p = xs.any (fun a => p (f a)) := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    dsimp [List.map, List.any]
    cases p (f a) with
    | true => rfl
    | false => exact ih

private theorem list_any_false_of_forall_getElem? {α : Type} {p : α → Bool}
    {xs : List α}
    (h : ∀ i x, Trusted.MirSemantics.getElem? xs i = some x → p x = false) :
    xs.any p = false := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    have ha : p a = false := h 0 a rfl
    have hRest : rest.any p = false := ih (fun i x hG => h (i + 1) x hG)
    dsimp [List.any]
    rw [ha, hRest]
    rfl

private theorem list_any_true_of_getElem? {α : Type} {p : α → Bool} {xs : List α}
    {i : Nat} {x : α} (hGet : Trusted.MirSemantics.getElem? xs i = some x)
    (hP : p x = true) : xs.any p = true := by
  induction xs generalizing i with
  | nil => cases hGet
  | cons a rest ih =>
    cases i with
    | zero =>
      injection hGet with hEq; subst hEq
      dsimp [List.any]
      rw [hP]
      rfl
    | succ k =>
      dsimp [List.any]
      rw [ih hGet]
      cases p a <;> rfl

private theorem list_any_eq_of_getElem? {α : Type} {p : α → Bool} {xs ys : List α}
    (hLen : xs.length = ys.length)
    (hAt : ∀ i x y,
      Trusted.MirSemantics.getElem? xs i = some x →
      Trusted.MirSemantics.getElem? ys i = some y →
      p x = p y) :
    xs.any p = ys.any p := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases hLen
  | cons a rest ih =>
    cases ys with
    | nil => cases hLen
    | cons b rest' =>
      have hHead : p a = p b := hAt 0 a b rfl rfl
      have hTail : rest.any p = rest'.any p :=
        ih (Nat.succ.inj hLen) (fun i x y hx hy => hAt (i + 1) x y hx hy)
      dsimp [List.any]
      rw [hHead, hTail]

private theorem list_isEmpty_eq_of_length {α β : Type} {xs : List α} {ys : List β}
    (h : xs.length = ys.length) : xs.isEmpty = ys.isEmpty := by
  cases xs with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases h
  | cons _ _ =>
    cases ys with
    | nil => cases h
    | cons _ _ => rfl

private theorem list_isEmpty_false_of_pos {α : Type} {xs : List α}
    (h : 0 < xs.length) : xs.isEmpty = false := by
  cases xs with
  | nil => exact False.elim (Nat.not_lt_zero 0 h)
  | cons _ _ => rfl

private theorem list_pos_of_isEmpty_false {α : Type} {xs : List α}
    (h : xs.isEmpty = false) : 0 < xs.length := by
  cases xs with
  | nil => cases h
  | cons _ rest => exact Nat.zero_lt_succ rest.length

private theorem list_eq_nil_of_isEmpty {α : Type} {xs : List α}
    (h : xs.isEmpty = true) : xs = [] := by
  cases xs with
  | nil => rfl
  | cons _ _ => cases h

private theorem take_append_of_le_length {α : Type} (xs ys : List α) (n : Nat)
    (h : n ≤ xs.length) : (xs ++ ys).take n = xs.take n := by
  induction xs generalizing n with
  | nil =>
    cases n with
    | zero => rfl
    | succ k => exact False.elim (Nat.not_succ_le_zero k h)
  | cons a rest ih =>
    cases n with
    | zero => rfl
    | succ k =>
      dsimp [List.take]
      rw [ih k (Nat.le_of_succ_le_succ h)]

private theorem drop_append_of_le_length {α : Type} (xs ys : List α) (n : Nat)
    (h : n ≤ xs.length) : (xs ++ ys).drop n = xs.drop n ++ ys := by
  induction xs generalizing n with
  | nil =>
    cases n with
    | zero => rfl
    | succ k => exact False.elim (Nat.not_succ_le_zero k h)
  | cons a rest ih =>
    cases n with
    | zero => rfl
    | succ k => exact ih k (Nat.le_of_succ_le_succ h)

private theorem drop_length_eq {α : Type} (xs : List α) (n : Nat) :
    (xs.drop n).length = xs.length - n := by
  induction xs generalizing n with
  | nil =>
    cases n with
    | zero => rfl
    | succ _ =>
      dsimp [List.drop, List.length]
      rw [Nat.zero_sub]
  | cons _ rest ih =>
    cases n with
    | zero => rfl
    | succ k =>
      dsimp [List.drop, List.length]
      rw [Nat.succ_sub_succ]
      exact ih k

private theorem take_drop1_append_left {α : Type} (xs ys : List α) (n : Nat)
    (h : n < xs.length) :
    ((xs ++ ys).drop 1).take n = (xs.drop 1).take n := by
  have h1 : 1 ≤ xs.length := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le n) h)
  rw [drop_append_of_le_length xs ys 1 h1]
  have hLe : n ≤ (xs.drop 1).length := by
    rw [drop_length_eq]
    cases xs with
    | nil => exact False.elim (Nat.not_lt_zero n h)
    | cons _ rest =>
      dsimp [List.length] at h
      dsimp [List.length]
      exact Nat.le_of_lt_succ h
  exact take_append_of_le_length (xs.drop 1) ys n hLe

private theorem getElem?_take_drop1 {α : Type} (xs : List α) (n i : Nat)
    (hi : i < n) :
    Trusted.MirSemantics.getElem? ((xs.drop 1).take n) i =
      Trusted.MirSemantics.getElem? xs (i + 1) := by
  cases xs with
  | nil =>
    dsimp [List.drop, List.take]
    cases n with
    | zero => exact False.elim (Nat.not_lt_zero i hi)
    | succ _ => rfl
  | cons _ ys =>
    dsimp [List.drop, Trusted.MirSemantics.getElem?]
    induction ys generalizing n i with
    | nil =>
      cases n with
      | zero => exact False.elim (Nat.not_lt_zero i hi)
      | succ _ => rfl
    | cons _ _ ih =>
      cases n with
      | zero => exact False.elim (Nat.not_lt_zero i hi)
      | succ m =>
        cases i with
        | zero => rfl
        | succ k => exact ih m k (Nat.lt_of_succ_lt_succ hi)

private theorem initLocalsLoop_length (body : Body) (args : List Val)
    (base : Nat) (tys : List MirTy) :
    (initLocalsLoop body args base tys).length = tys.length := by
  induction tys generalizing base with
  | nil => rfl
  | cons _ _ ih =>
    dsimp [initLocalsLoop, List.length]
    rw [ih (base + 1)]

private theorem initLocalsLoop_getElem? (body : Body) (args : List Val)
    (base : Nat) (tys : List MirTy) (i : Nat) (ty : MirTy)
    (hTy : Trusted.MirSemantics.getElem? tys i = some ty) :
    Trusted.MirSemantics.getElem? (initLocalsLoop body args base tys) i =
      some (if Nat.beq (base + i) 0 then
              liveUninitSlot ty
            else if Nat.ble (base + i) body.argumentCount then
              match Trusted.MirSemantics.getElem? args ((base + i) - 1) with
              | some v => .live (some v)
              | none => .dead
            else if hasStorageAnnotation body (base + i) then
              .dead
            else
              liveUninitSlot ty) := by
  induction tys generalizing base i with
  | nil => cases hTy
  | cons _ _ ih =>
    cases i with
    | zero =>
      injection hTy with hEq; subst hEq; rfl
    | succ k =>
      have hAdd : base + 1 + k = base + (k + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 k]
      have hRec := ih (base + 1) k hTy
      rw [hAdd] at hRec
      exact hRec

private theorem initLocalsLoop_append (body : Body) (args : List Val)
    (base : Nat) (xs ys : List MirTy) :
    initLocalsLoop body args base (xs ++ ys) =
      initLocalsLoop body args base xs ++
        initLocalsLoop body args (base + xs.length) ys := by
  induction xs generalizing base with
  | nil =>
    dsimp [initLocalsLoop, List.length]
  | cons _ rest ih =>
    dsimp [initLocalsLoop, List.length]
    rw [ih (base + 1)]
    have hEq : base + 1 + rest.length = base + (rest.length + 1) := by
      rw [Nat.add_assoc, Nat.add_comm 1 rest.length]
    rw [hEq]

private theorem bodiesHaveUniqueIdentities_eq_of_map_id {bs₁ bs₂ : List Body}
    (hIds : bs₁.map (fun b => b.identity) = bs₂.map (fun b => b.identity)) :
    bodiesHaveUniqueIdentities bs₁ = bodiesHaveUniqueIdentities bs₂ := by
  unfold bodiesHaveUniqueIdentities
  have hAll : bs₁.all (fun b => !stringBeq b.identity "") =
      bs₂.all (fun b => !stringBeq b.identity "") := by
    have h1 := list_all_map (fun s => !stringBeq s "") (fun b : Body => b.identity) bs₁
    have h2 := list_all_map (fun s => !stringBeq s "") (fun b : Body => b.identity) bs₂
    rw [← h1, ← h2, hIds]
  rw [hAll, hIds]

private theorem step_iff_evalStep {p : Program} {s : State}
    {res : StepResult State TerminalOut} :
    Step p s res ↔ evalStep p 0 s = res := by
  constructor
  · intro ⟨c, hc, hEval⟩
    have hc0 : c = 0 := hc
    subst hc0
    exact hEval
  · intro h
    exact ⟨0, rfl, h⟩

private theorem stepInterproc_iff_evalStepInterproc {p : Program} {s : InterprocState}
    {res : StepResult InterprocState TerminalOut} :
    StepInterproc p s res ↔ evalStepInterproc p 0 s = res := by
  constructor
  · intro ⟨c, hc, hEval⟩
    have hc0 : c = 0 := hc
    subst hc0
    exact hEval
  · intro h
    exact ⟨0, rfl, h⟩

private theorem reaches_head_priv {p : Program} {s₁ s₂ s₃ : State}
    (hFirst : Step p s₁ (.step s₂)) (hRest : Reaches p s₂ s₃) :
    Reaches p s₁ s₃ := by
  induction hRest with
  | refl => exact Reaches.tail (Reaches.refl s₁) hFirst
  | tail _ hLast ih => exact Reaches.tail ih hLast

private theorem reachesInterproc_head_priv {p : Program}
    {s₁ s₂ s₃ : InterprocState}
    (hFirst : StepInterproc p s₁ (.step s₂))
    (hRest : ReachesInterproc p s₂ s₃) :
    ReachesInterproc p s₁ s₃ := by
  induction hRest with
  | refl => exact ReachesInterproc.tail (ReachesInterproc.refl s₁) hFirst
  | tail _ hLast ih => exact ReachesInterproc.tail ih hLast

/-! ### Stage 4 Private Helpers — Slice B: Conservative Extension (Theorem 1) -/

private theorem evalStepInterproc_eq_liftSingleFrameStep
    (p : Program) (c : Choice) (s : State) (is : InterprocState)
    (hEmb : embedState s = some is) (hNotCall : stepIsNotCall p s = true) :
    evalStepInterproc p c is = liftSingleFrameStep [] (evalStep p c s) := by
  cases s with
  | mk frames callerMem =>
    unfold embedState at hEmb
    dsimp at hEmb
    cases frames with
    | nil => cases hEmb
    | cons frame rest =>
      cases rest with
      | cons _ _ => cases hEmb
      | nil =>
        injection hEmb with hIsEq
        subst hIsEq
        unfold stepIsNotCall at hNotCall
        dsimp at hNotCall
        unfold evalStepInterproc evalStep
        dsimp
        cases hBody : Trusted.MirSemantics.getElem? p.bodies frame.defId with
        | none => rfl
        | some body =>
          dsimp
          rw [hBody] at hNotCall
          dsimp at hNotCall
          cases hBb : Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx with
          | none => rfl
          | some bb =>
            dsimp
            rw [hBb] at hNotCall
            dsimp at hNotCall
            cases hStmt : Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx with
            | some stmt => rfl
            | none =>
              dsimp
              rw [hStmt] at hNotCall
              dsimp at hNotCall
              cases hLen : Nat.beq frame.stmtIdx bb.statements.length with
              | false => rfl
              | true =>
                dsimp
                rw [hLen] at hNotCall
                dsimp at hNotCall
                cases hTerm : bb.terminator with
                | call _ _ _ _ _ =>
                  rw [hTerm] at hNotCall
                  cases hNotCall
                | return_ =>
                  unfold evalReturnTerminator evalTerminator
                  rw [hTerm]
                  dsimp
                  cases bb.cleanup with
                  | true => rfl
                  | false =>
                    dsimp
                    cases Trusted.MirSemantics.getElem? frame.locals 0 with
                    | none => rfl
                    | some slot =>
                      cases slot with
                      | dead => rfl
                      | live optVal =>
                        cases optVal with
                        | none => rfl
                        | some _ => rfl
                | goto _ => rfl
                | switchInt _ _ => rfl
                | unreachable => rfl
                | unwindResume => rfl
                | assert _ _ _ _ _ => rfl
                | unsupported => rfl

private theorem evalStatement_single_frame {body : Body} {frame : FrameState}
    {mem : CallerMemory} {stmt : StatementKind} {s' : State}
    (h : evalStatement body frame mem stmt = .step s') :
    ∃ frame', s'.frames = [frame'] := by
  cases stmt with
  | nop =>
    dsimp [evalStatement] at h
    injection h with hEq; subst hEq
    exact ⟨{ frame with stmtIdx := frame.stmtIdx + 1 }, rfl⟩
  | unsupported =>
    dsimp [evalStatement] at h; cases h
  | storageLive localId =>
    dsimp [evalStatement] at h
    cases hTy : Trusted.MirSemantics.getElem? body.locals localId with
    | none => rw [hTy] at h; cases h
    | some ty =>
      rw [hTy] at h; dsimp at h
      cases hSet : setElem? frame.locals localId (liveUninitSlot ty) with
      | none => rw [hSet] at h; cases h
      | some locals' =>
        rw [hSet] at h; dsimp at h
        injection h with hEq; subst hEq
        exact ⟨{ frame with stmtIdx := frame.stmtIdx + 1, locals := locals' }, rfl⟩
  | storageDead localId =>
    dsimp [evalStatement] at h
    cases hZ : Nat.beq localId 0 with
    | true => rw [hZ] at h; cases h
    | false =>
      rw [hZ] at h; dsimp at h
      cases hSet : setElem? frame.locals localId .dead with
      | none => rw [hSet] at h; cases h
      | some locals' =>
        rw [hSet] at h; dsimp at h
        injection h with hEq; subst hEq
        exact ⟨{ frame with stmtIdx := frame.stmtIdx + 1, locals := locals' }, rfl⟩
  | assign dst rv =>
    dsimp [evalStatement] at h
    cases hProj : dst.projection.isEmpty with
    | false => rw [hProj] at h; cases h
    | true =>
      rw [hProj] at h; dsimp at h
      cases hTy : Trusted.MirSemantics.getElem? body.locals dst.localId with
      | none => rw [hTy] at h; cases h
      | some dstTy =>
        rw [hTy] at h; dsimp at h
        cases hRv : evalRvalue body.locals frame.locals dstTy rv with
        | error _ => rw [hRv] at h; cases h
        | ok pair =>
          rw [hRv] at h; dsimp at h
          cases pair with
          | mk val localsAfterRval =>
            dsimp at h
            cases hW : writePlace localsAfterRval dst.localId dstTy val with
            | error _ => rw [hW] at h; cases h
            | ok localsAfterWrite =>
              rw [hW] at h; dsimp at h
              injection h with hEq; subst hEq
              exact ⟨_, rfl⟩

private theorem evalTerminator_single_frame {body : Body} {bb : BasicBlock}
    {frame : FrameState} {mem : CallerMemory} {s' : State}
    (h : evalTerminator body bb frame mem = .step s') :
    ∃ frame', s'.frames = [frame'] := by
  unfold evalTerminator at h
  cases hTerm : bb.terminator with
  | goto target =>
    rw [hTerm] at h; dsimp [jumpToBlock] at h
    injection h with hEq; subst hEq
    exact ⟨_, rfl⟩
  | return_ =>
    rw [hTerm] at h; dsimp at h
    cases hCl : bb.cleanup with
    | true => rw [hCl] at h; cases h
    | false =>
      rw [hCl] at h; dsimp at h
      cases h0 : Trusted.MirSemantics.getElem? frame.locals 0 with
      | none => rw [h0] at h; cases h
      | some slot =>
        rw [h0] at h
        cases slot with
        | dead => cases h
        | live optVal => cases optVal <;> cases h
  | unreachable => rw [hTerm] at h; cases h
  | unwindResume => rw [hTerm] at h; cases h
  | assert _ _ _ _ _ => rw [hTerm] at h; cases h
  | call _ _ _ _ _ => rw [hTerm] at h; cases h
  | unsupported => rw [hTerm] at h; cases h
  | switchInt discr targets =>
    rw [hTerm] at h; dsimp at h
    cases hOp : evalPrimitiveOperand body.locals frame.locals discr with
    | error _ => rw [hOp] at h; cases h
    | ok pair =>
      rw [hOp] at h; dsimp at h
      cases pair with
      | mk discrVal localsAfter =>
        dsimp at h
        cases discrVal with
        | scalar sv =>
          dsimp at h
          cases hTgt : evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches with
          | error _ => rw [hTgt] at h; cases h
          | ok target =>
            rw [hTgt] at h; dsimp [jumpToBlock] at h
            injection h with hEq; subst hEq
            exact ⟨_, rfl⟩
        | bool b =>
          dsimp at h
          cases hTgt : evalBoolSwitchBranches b targets.otherwise targets.branches with
          | error _ => rw [hTgt] at h; cases h
          | ok target =>
            rw [hTgt] at h; dsimp [jumpToBlock] at h
            injection h with hEq; subst hEq
            exact ⟨_, rfl⟩
        | ptr _ => cases h
        | unit => cases h
        | enumVal _ _ => cases h
        | tuple _ => cases h
        | bytes _ => cases h

private theorem evalStep_single_frame {p : Program} {c : Choice} {s s' : State}
    (h : evalStep p c s = .step s') : ∃ frame', s'.frames = [frame'] := by
  unfold evalStep at h
  cases hFr : s.frames with
  | nil => rw [hFr] at h; cases h
  | cons frame rest =>
    rw [hFr] at h
    cases rest with
    | cons _ _ => cases h
    | nil =>
      dsimp at h
      cases hBody : Trusted.MirSemantics.getElem? p.bodies frame.defId with
      | none => rw [hBody] at h; cases h
      | some body =>
        rw [hBody] at h; dsimp at h
        cases hBb : Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx with
        | none => rw [hBb] at h; cases h
        | some bb =>
          rw [hBb] at h; dsimp at h
          cases hStmt : Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx with
          | some stmt =>
            rw [hStmt] at h; dsimp at h
            exact evalStatement_single_frame h
          | none =>
            rw [hStmt] at h; dsimp at h
            cases hLen : Nat.beq frame.stmtIdx bb.statements.length with
            | false => rw [hLen] at h; cases h
            | true =>
              rw [hLen] at h; dsimp at h
              exact evalTerminator_single_frame h

private theorem initState_single_frame {p : Program} {q : Query} {s₀ : State}
    (h : initState p q = .ok s₀) : ∃ frame₀, s₀.frames = [frame₀] := by
  unfold initState at h
  cases hHdr : (!Nat.beq p.pointerWidthBits 64 || !Nat.beq p.mirProfileVersion 1) with
  | true => rw [hHdr] at h; cases h
  | false =>
    rw [hHdr] at h; dsimp at h
    cases hMem : (!q.callerMem.allocations.isEmpty) with
    | true => rw [hMem] at h; cases h
    | false =>
      rw [hMem] at h; dsimp at h
      cases hBody : Trusted.MirSemantics.getElem? p.bodies p.entryDefId with
      | none => rw [hBody] at h; cases h
      | some body =>
        rw [hBody] at h; dsimp at h
        cases hEmpty : body.basicBlocks.isEmpty with
        | true => rw [hEmpty] at h; cases h
        | false =>
          rw [hEmpty] at h; dsimp at h
          cases hArg : (!Nat.blt body.argumentCount body.locals.length) with
          | true => rw [hArg] at h; cases h
          | false =>
            rw [hArg] at h; dsimp at h
            cases hSt : (!storageAnnotationsInBounds body) with
            | true => rw [hSt] at h; cases h
            | false =>
              rw [hSt] at h; dsimp at h
              cases hTy : (!body.locals.all isSupportedScalarOrUnitTy) with
              | true => rw [hTy] at h; cases h
              | false =>
                rw [hTy] at h; dsimp at h
                cases hArgs : (!checkArgsMatch q.args
                    ((body.locals.drop 1).take body.argumentCount)) with
                | true => rw [hArgs] at h; cases h
                | false =>
                  rw [hArgs] at h; dsimp at h
                  injection h with hEq; subst hEq
                  exact ⟨_, rfl⟩

private theorem stepIsNotCall_of_callFree {p : Program}
    (hCf : isCallFreeProgram p = true) (s : State) :
    stepIsNotCall p s = true := by
  unfold stepIsNotCall
  cases s.frames with
  | nil => rfl
  | cons frame rest =>
    cases rest with
    | cons _ _ => rfl
    | nil =>
      dsimp
      cases hBody : Trusted.MirSemantics.getElem? p.bodies frame.defId with
      | none => rfl
      | some body =>
        dsimp
        cases hBb : Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx with
        | none => rfl
        | some bb =>
          dsimp
          cases Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx with
          | some _ => rfl
          | none =>
            dsimp
            cases Nat.beq frame.stmtIdx bb.statements.length with
            | false => rfl
            | true =>
              dsimp
              have hBodyCf : bodyIsCallFree body = true :=
                list_all_getElem? hCf hBody
              have hBbCf : blockIsCallFree bb = true :=
                list_all_getElem? hBodyCf hBb
              exact hBbCf

private noncomputable def iterInterprocState (p : Program) (s₀ : InterprocState) :
    Nat → InterprocState
  | 0 => s₀
  | n + 1 =>
    match evalStepInterproc p 0 (iterInterprocState p s₀ n) with
    | .step s' => s'
    | .done _ => iterInterprocState p s₀ n
    | .fault _ => iterInterprocState p s₀ n

private theorem callFree_evalStep_top {p : Program} (hCf : isCallFreeProgram p = true)
    (is : InterprocState) (hStack : is.stack = []) :
    evalStepInterproc p 0 is =
      liftSingleFrameStep [] (evalStep p 0 (projectTopState is)) := by
  have hEmb : embedState (projectTopState is) = some is := by
    cases is with
    | mk cur stack mem =>
      dsimp at hStack
      subst hStack
      rfl
  exact evalStepInterproc_eq_liftSingleFrameStep p 0 (projectTopState is) is
    hEmb (stepIsNotCall_of_callFree hCf (projectTopState is))

private theorem callFree_query_iff {p : Program} (hCf : isCallFreeProgram p = true)
    (q : Query) :
    (WellFormedInterproc p q ↔ WellFormed p q) ∧
    (∀ out : TerminalOut, BehaviorInterproc p q out ↔ Behavior p q out) ∧
    (∀ k : FaultKind,
      ReachesResultInterproc p q (.fault k) ↔ ReachesResult p q (.fault k)) ∧
    (DivergesInterproc p q ↔ Diverges p q) := by
  cases hInit : initState p q with
  | error kErr =>
    have hInitI : initStateInterproc p q = .error kErr := by
      unfold initStateInterproc; rw [hInit]
    refine ⟨?_, ?_, ?_, ?_⟩
    · constructor
      · intro hW; let ⟨⟨_, hOk, _⟩, _⟩ := hW; rw [hInitI] at hOk; cases hOk
      · intro hW; let ⟨⟨_, hOk, _⟩, _⟩ := hW; rw [hInit] at hOk; cases hOk
    · intro out; unfold BehaviorInterproc Behavior ReachesResultInterproc ReachesResult
      rw [hInitI, hInit]
      constructor <;> intro h <;> cases h
    · intro k; unfold ReachesResultInterproc ReachesResult
      rw [hInitI, hInit]
      constructor
      · intro h; injection h with hEq; subst hEq; rfl
      · intro h; injection h with hEq; subst hEq; rfl
    · constructor
      · intro hD; let ⟨_, hOk, _⟩ := hD; rw [hInitI] at hOk; cases hOk
      · intro hD; let ⟨_, hOk, _⟩ := hD; rw [hInit] at hOk; cases hOk
  | ok s₀ =>
    let ⟨frame₀, hFr₀⟩ := initState_single_frame hInit
    let is₀ : InterprocState :=
      { cur := frame₀, stack := [], callerMem := s₀.callerMem }
    have hEmb₀ : embedState s₀ = some is₀ := by
      unfold embedState; rw [hFr₀]
    have hProj₀ : projectTopState is₀ = s₀ := by
      cases s₀ with
      | mk frs mem =>
        dsimp at hFr₀
        subst hFr₀
        rfl
    have hInitI : initStateInterproc p q = .ok is₀ := by
      unfold initStateInterproc; rw [hInit]; dsimp; rw [hEmb₀]
    have hStepFwd : ∀ is is', is.stack = [] →
        evalStepInterproc p 0 is = .step is' →
        is'.stack = [] ∧ evalStep p 0 (projectTopState is) = .step (projectTopState is') := by
      intro is is' hSt hEvI
      rw [callFree_evalStep_top hCf is hSt] at hEvI
      cases hEv : evalStep p 0 (projectTopState is) with
      | done _ => rw [hEv] at hEvI; cases hEvI
      | fault _ => rw [hEv] at hEvI; cases hEvI
      | step s' =>
        rw [hEv] at hEvI
        let ⟨f', hFr'⟩ := evalStep_single_frame hEv
        dsimp [liftSingleFrameStep] at hEvI
        rw [hFr'] at hEvI
        dsimp at hEvI
        injection hEvI with hEq
        subst hEq
        refine ⟨rfl, ?_⟩
        cases s' with
        | mk frs mem =>
          dsimp at hFr'
          subst hFr'
          rfl
    have hStepBwd : ∀ is s', is.stack = [] →
        evalStep p 0 (projectTopState is) = .step s' →
        ∃ is', is'.stack = [] ∧ projectTopState is' = s' ∧
          evalStepInterproc p 0 is = .step is' := by
      intro is s' hSt hEv
      let ⟨f', hFr'⟩ := evalStep_single_frame hEv
      let is' : InterprocState :=
        { cur := f', stack := [], callerMem := s'.callerMem }
      have hProj' : projectTopState is' = s' := by
        cases s' with
        | mk frs mem =>
          dsimp at hFr'
          subst hFr'
          rfl
      refine ⟨is', rfl, hProj', ?_⟩
      rw [callFree_evalStep_top hCf is hSt, hEv]
      dsimp [liftSingleFrameStep]
      rw [hFr']
    have hReachFwd : ∀ is, ReachesInterproc p is₀ is →
        is.stack = [] ∧ Reaches p s₀ (projectTopState is) := by
      intro is hR
      induction hR with
      | refl => rw [hProj₀]; exact ⟨rfl, Reaches.refl s₀⟩
      | tail _ hSt ih =>
        let ⟨hStack, hRs⟩ := ih
        let ⟨hStack', hEv⟩ :=
          hStepFwd _ _ hStack (stepInterproc_iff_evalStepInterproc.mp hSt)
        exact ⟨hStack', Reaches.tail hRs (step_iff_evalStep.mpr hEv)⟩
    have hReachBwd : ∀ s, Reaches p s₀ s →
        ∃ is, is.stack = [] ∧ projectTopState is = s ∧ ReachesInterproc p is₀ is := by
      intro s hR
      induction hR with
      | refl => exact ⟨is₀, rfl, hProj₀, ReachesInterproc.refl is₀⟩
      | @tail _ s₃ _ hSt ih =>
        let ⟨is, hStack, hProj, hRi⟩ := ih
        have hEv : evalStep p 0 (projectTopState is) = .step s₃ := by
          rw [hProj]; exact step_iff_evalStep.mp hSt
        let ⟨is', hStack', hProj', hEvI⟩ := hStepBwd is s₃ hStack hEv
        exact ⟨is', hStack', hProj',
          ReachesInterproc.tail hRi (stepInterproc_iff_evalStepInterproc.mpr hEvI)⟩
    have hDoneIff : ∀ out,
        BehaviorInterproc p q out ↔ Behavior p q out := by
      intro out
      unfold BehaviorInterproc Behavior ReachesResultInterproc ReachesResult
      rw [hInitI, hInit]
      constructor
      · intro ⟨is, hRi, hStI⟩
        let ⟨hStack, hRs⟩ := hReachFwd is hRi
        have hEvI := stepInterproc_iff_evalStepInterproc.mp hStI
        rw [callFree_evalStep_top hCf is hStack] at hEvI
        cases hEv : evalStep p 0 (projectTopState is) with
        | step s' =>
          rw [hEv] at hEvI
          let ⟨f', hFr'⟩ := evalStep_single_frame hEv
          dsimp [liftSingleFrameStep] at hEvI
          rw [hFr'] at hEvI
          cases hEvI
        | fault _ => rw [hEv] at hEvI; cases hEvI
        | done out' =>
          rw [hEv] at hEvI
          injection hEvI with hEq; subst hEq
          exact ⟨projectTopState is, hRs, step_iff_evalStep.mpr hEv⟩
      · intro ⟨s, hRs, hSt⟩
        let ⟨is, hStack, hProj, hRi⟩ := hReachBwd s hRs
        have hEv : evalStep p 0 (projectTopState is) = .done out := by
          rw [hProj]; exact step_iff_evalStep.mp hSt
        have hEvI : evalStepInterproc p 0 is = .done out := by
          rw [callFree_evalStep_top hCf is hStack, hEv]; rfl
        exact ⟨is, hRi, stepInterproc_iff_evalStepInterproc.mpr hEvI⟩
    have hFaultIff : ∀ k,
        ReachesResultInterproc p q (.fault k) ↔ ReachesResult p q (.fault k) := by
      intro k
      unfold ReachesResultInterproc ReachesResult
      rw [hInitI, hInit]
      constructor
      · intro ⟨is, hRi, hStI⟩
        let ⟨hStack, hRs⟩ := hReachFwd is hRi
        have hEvI := stepInterproc_iff_evalStepInterproc.mp hStI
        rw [callFree_evalStep_top hCf is hStack] at hEvI
        cases hEv : evalStep p 0 (projectTopState is) with
        | step s' =>
          rw [hEv] at hEvI
          let ⟨f', hFr'⟩ := evalStep_single_frame hEv
          dsimp [liftSingleFrameStep] at hEvI
          rw [hFr'] at hEvI
          cases hEvI
        | done _ => rw [hEv] at hEvI; cases hEvI
        | fault k' =>
          rw [hEv] at hEvI
          injection hEvI with hEq; subst hEq
          exact ⟨projectTopState is, hRs, step_iff_evalStep.mpr hEv⟩
      · intro ⟨s, hRs, hSt⟩
        let ⟨is, hStack, hProj, hRi⟩ := hReachBwd s hRs
        have hEv : evalStep p 0 (projectTopState is) = .fault k := by
          rw [hProj]; exact step_iff_evalStep.mp hSt
        have hEvI : evalStepInterproc p 0 is = .fault k := by
          rw [callFree_evalStep_top hCf is hStack, hEv]; rfl
        exact ⟨is, hRi, stepInterproc_iff_evalStepInterproc.mpr hEvI⟩
    refine ⟨?_, hDoneIff, hFaultIff, ?_⟩
    · constructor
      · intro hW
        exact ⟨⟨s₀, hInit, fun _ _ => ⟨0, rfl⟩⟩,
          fun k hF => hW.2 k ((hFaultIff k).mpr hF)⟩
      · intro hW
        exact ⟨⟨is₀, hInitI, fun _ _ => ⟨0, rfl⟩⟩,
          fun k hF => hW.2 k ((hFaultIff k).mp hF)⟩
    · constructor
      · intro ⟨is₀', hOkI, tr, h0, hSt⟩
        rw [hInitI] at hOkI; injection hOkI with hEq; subst hEq
        have hTrStack : ∀ n, (tr n).stack = [] := by
          intro n
          induction n with
          | zero => rw [h0]
          | succ m ih =>
            exact (hStepFwd (tr m) (tr (m + 1)) ih
              (stepInterproc_iff_evalStepInterproc.mp (hSt m))).1
        refine ⟨s₀, hInit, fun n => projectTopState (tr n), ?_, fun n => ?_⟩
        · dsimp; rw [h0, hProj₀]
        · exact step_iff_evalStep.mpr
            (hStepFwd (tr n) (tr (n + 1)) (hTrStack n)
              (stepInterproc_iff_evalStepInterproc.mp (hSt n))).2
      · intro ⟨s₀', hOk, tr, h0, hSt⟩
        rw [hInit] at hOk; injection hOk with hEq; subst hEq
        have hInv : ∀ n, (iterInterprocState p is₀ n).stack = [] ∧
            projectTopState (iterInterprocState p is₀ n) = tr n := by
          intro n
          induction n with
          | zero => rw [h0]; exact ⟨rfl, hProj₀⟩
          | succ m ih =>
            let ⟨hStack, hProj⟩ := ih
            have hEv : evalStep p 0 (projectTopState (iterInterprocState p is₀ m)) =
                .step (tr (m + 1)) := by
              rw [hProj]; exact step_iff_evalStep.mp (hSt m)
            let ⟨is', hStack', hProj', hEvI⟩ := hStepBwd _ _ hStack hEv
            dsimp [iterInterprocState]
            rw [hEvI]
            exact ⟨hStack', hProj'⟩
        refine ⟨is₀, hInitI, iterInterprocState p is₀, rfl, fun n => ?_⟩
        let ⟨hStack, hProj⟩ := hInv n
        have hEv : evalStep p 0 (projectTopState (iterInterprocState p is₀ n)) =
            .step (tr (n + 1)) := by
          rw [hProj]; exact step_iff_evalStep.mp (hSt n)
        let ⟨is', _, _, hEvI⟩ := hStepBwd _ _ hStack hEv
        apply stepInterproc_iff_evalStepInterproc.mpr
        dsimp [iterInterprocState]
        rw [hEvI]

private theorem callFree_satisfiesPost_iff {p : Program}
    (hCf : isCallFreeProgram p = true) (q : Query) (post : TerminalOut → Prop) :
    SatisfiesPostInterproc p q post ↔ SatisfiesPost p q post := by
  let ⟨hWf, hBeh, _, _⟩ := callFree_query_iff hCf q
  unfold SatisfiesPostInterproc SatisfiesPost
  constructor
  · intro ⟨hW, hP⟩
    exact ⟨hWf.mp hW, fun out hB => hP out ((hBeh out).mpr hB)⟩
  · intro ⟨hW, hP⟩
    exact ⟨hWf.mpr hW, fun out hB => hP out ((hBeh out).mp hB)⟩

private theorem callFree_bodyVerified_iff {p : Program}
    (hCf : isCallFreeProgram p = true) (defId : DefId) (body : Body)
    (safetyPre : List Val → Prop) :
    BodyVerifiedInterproc p defId body safetyPre ↔
      BodyVerified p defId body safetyPre := by
  unfold BodyVerifiedInterproc BodyVerified
  have hCfE : isCallFreeProgram (entryProgForBody p defId) = true := hCf
  constructor
  · intro ⟨hGet, hAdm, hArgs⟩
    refine ⟨hGet, hAdm, fun args hV hS => ?_⟩
    exact (callFree_query_iff hCfE { args := args }).1.mp (hArgs args hV hS)
  · intro ⟨hGet, hAdm, hArgs⟩
    refine ⟨hGet, hAdm, fun args hV hS => ?_⟩
    exact (callFree_query_iff hCfE { args := args }).1.mpr (hArgs args hV hS)

private theorem callFree_programVerified_iff {p : Program}
    (hCf : isCallFreeProgram p = true) (specs : Specs) :
    ProgramVerifiedInterproc p specs ↔ ProgramVerified p specs := by
  unfold ProgramVerifiedInterproc ProgramVerified
  constructor
  · intro ⟨h1, h2, h3, h4, h5, hBods, hProp⟩
    refine ⟨h1, h2, h3, h4, h5, fun defId body hGet => ?_, hProp⟩
    exact (callFree_bodyVerified_iff hCf defId body (specs.safety body.identity)).mp
      (hBods defId body hGet)
  · intro ⟨h1, h2, h3, h4, h5, hBods, hProp⟩
    refine ⟨h1, h2, h3, h4, h5, fun defId body hGet => ?_, hProp⟩
    exact (callFree_bodyVerified_iff hCf defId body (specs.safety body.identity)).mpr
      (hBods defId body hGet)

private theorem interproc_conservative_extension_exact_priv
    (p : Program) :
    (∀ (c : Choice) (s : State) (is : InterprocState),
      embedState s = some is →
      stepIsNotCall p s = true →
      evalStepInterproc p c is = liftSingleFrameStep [] (evalStep p c s)) ∧
    (isCallFreeProgram p = true →
      (∀ q : Query,
        (WellFormedInterproc p q ↔ WellFormed p q) ∧
        (∀ out : TerminalOut,
          BehaviorInterproc p q out ↔ Behavior p q out) ∧
        (∀ k : FaultKind,
          ReachesResultInterproc p q (.fault k) ↔
            ReachesResult p q (.fault k)) ∧
        (DivergesInterproc p q ↔ Diverges p q)) ∧
      (∀ (q : Query) (post : TerminalOut → Prop),
        SatisfiesPostInterproc p q post ↔ SatisfiesPost p q post) ∧
      (∀ (defId : DefId) (body : Body) (safetyPre : List Val → Prop),
        BodyVerifiedInterproc p defId body safetyPre ↔
          BodyVerified p defId body safetyPre) ∧
      (∀ specs : Specs,
        (CrateTheoremInterproc ⟨p, specs⟩ ↔ CrateTheorem ⟨p, specs⟩) ∧
        (UnitTheoremInterproc ⟨p, specs⟩ ↔ UnitTheorem ⟨p, specs⟩))) := by
  refine ⟨fun c s is hEmb hNC =>
    evalStepInterproc_eq_liftSingleFrameStep p c s is hEmb hNC, ?_⟩
  intro hCf
  refine ⟨fun q => callFree_query_iff hCf q,
    fun q post => callFree_satisfiesPost_iff hCf q post,
    fun defId body safetyPre => callFree_bodyVerified_iff hCf defId body safetyPre,
    fun specs => ?_⟩
  have hPv := callFree_programVerified_iff hCf specs
  unfold CrateTheoremInterproc CrateTheorem UnitTheoremInterproc UnitTheorem
  dsimp
  constructor
  · constructor
    · intro ⟨hSc, hP⟩; exact ⟨hSc, hPv.mp hP⟩
    · intro ⟨hSc, hP⟩; exact ⟨hSc, hPv.mpr hP⟩
  · constructor
    · intro ⟨hSc, hP⟩; exact ⟨hSc, hPv.mp hP⟩
    · intro ⟨hSc, hP⟩; exact ⟨hSc, hPv.mpr hP⟩

/-! ### Stage 4 Private Helpers — Slice C1: Forward-Expansion Simulation,
`InlineWitness`, & Locality/Shift Commutation -/

private inductive StepsN (p : Program) :
    Nat → InterprocState → InterprocState → Prop where
  | zero (s : InterprocState) : StepsN p 0 s s
  | succ {n : Nat} {s₁ s₂ s₃ : InterprocState} :
      evalStepInterproc p 0 s₁ = .step s₂ →
      StepsN p n s₂ s₃ →
      StepsN p (n + 1) s₁ s₃

private theorem stepsN_one {p : Program} {s₁ s₂ : InterprocState}
    (h : evalStepInterproc p 0 s₁ = .step s₂) : StepsN p 1 s₁ s₂ :=
  StepsN.succ h (StepsN.zero s₂)

private theorem stepsN_trans {p : Program} {m n : Nat}
    {s₁ s₂ s₃ : InterprocState}
    (h1 : StepsN p m s₁ s₂) (h2 : StepsN p n s₂ s₃) :
    StepsN p (m + n) s₁ s₃ := by
  induction h1 with
  | zero _ =>
    rw [Nat.zero_add]
    exact h2
  | succ hStep _ ih =>
    rw [Nat.succ_add]
    exact StepsN.succ hStep (ih h2)

private theorem stepsN_to_reaches {p : Program} {n : Nat}
    {s₁ s₂ : InterprocState} (h : StepsN p n s₁ s₂) :
    ReachesInterproc p s₁ s₂ := by
  induction h with
  | zero s => exact ReachesInterproc.refl s
  | succ hStep _ ih =>
    exact reachesInterproc_head_priv
      (stepInterproc_iff_evalStepInterproc.mpr hStep) ih

private theorem reaches_to_stepsN {p : Program} {s₁ s₂ : InterprocState}
    (h : ReachesInterproc p s₁ s₂) :
    ∃ n, StepsN p n s₁ s₂ := by
  induction h with
  | refl => exact ⟨0, StepsN.zero s₁⟩
  | tail _ hSt ih =>
    let ⟨n, hn⟩ := ih
    exact ⟨n + 1, stepsN_trans hn
      (stepsN_one (stepInterproc_iff_evalStepInterproc.mp hSt))⟩

private theorem stepsN_det_le {p : Program} {m n : Nat}
    {s t₁ t₂ : InterprocState}
    (hLe : m ≤ n) (h1 : StepsN p m s t₁) (h2 : StepsN p n s t₂) :
    StepsN p (n - m) t₁ t₂ := by
  induction h1 generalizing n with
  | zero _ =>
    rw [Nat.sub_zero]
    exact h2
  | succ hStep1 _ ih =>
    cases h2 with
    | zero _ => exact False.elim (Nat.not_succ_le_zero _ hLe)
    | succ hStep2 hRest2 =>
      rw [hStep1] at hStep2
      injection hStep2 with hEq
      subst hEq
      rw [Nat.succ_sub_succ]
      exact ih (Nat.le_of_succ_le_succ hLe) hRest2

private theorem stepsN_det_eq {p : Program} {n : Nat}
    {s t₁ t₂ : InterprocState}
    (h1 : StepsN p n s t₁) (h2 : StepsN p n s t₂) : t₁ = t₂ := by
  have h0 := stepsN_det_le (Nat.le_refl n) h1 h2
  rw [Nat.sub_self] at h0
  cases h0
  rfl

private theorem stepsN_succ_step_exists {p : Program} {k : Nat}
    {s₁ s₂ : InterprocState} (h : StepsN p (k + 1) s₁ s₂) :
    ∃ sMid, evalStepInterproc p 0 s₁ = .step sMid ∧ StepsN p k sMid s₂ := by
  cases h with
  | succ hStep hRest => exact ⟨_, hStep, hRest⟩

private theorem stepsN_terminal_unique {p : Program} {m n : Nat}
    {s t₁ t₂ : InterprocState} {res₁ res₂ : StepResult InterprocState TerminalOut}
    (hNot1 : match res₁ with | .step _ => False | _ => True)
    (hNot2 : match res₂ with | .step _ => False | _ => True)
    (h1 : StepsN p m s t₁) (hEv1 : evalStepInterproc p 0 t₁ = res₁)
    (h2 : StepsN p n s t₂) (hEv2 : evalStepInterproc p 0 t₂ = res₂) :
    res₁ = res₂ := by
  cases Nat.lt_or_ge m n with
  | inl hLt =>
    have hDiff := stepsN_det_le (Nat.le_of_lt hLt) h1 h2
    have hPos : 0 < n - m := Nat.sub_pos_of_lt hLt
    cases hEqD : n - m with
    | zero => rw [hEqD] at hPos; exact False.elim (Nat.not_lt_zero 0 hPos)
    | succ k =>
      rw [hEqD] at hDiff
      let ⟨sMid, hSt, _⟩ := stepsN_succ_step_exists hDiff
      rw [hEv1] at hSt
      subst hSt
      exact False.elim hNot1
  | inr hGe =>
    cases Nat.lt_or_ge n m with
    | inl hLt =>
      have hDiff := stepsN_det_le (Nat.le_of_lt hLt) h2 h1
      have hPos : 0 < m - n := Nat.sub_pos_of_lt hLt
      cases hEqD : m - n with
      | zero => rw [hEqD] at hPos; exact False.elim (Nat.not_lt_zero 0 hPos)
      | succ k =>
        rw [hEqD] at hDiff
        let ⟨sMid, hSt, _⟩ := stepsN_succ_step_exists hDiff
        rw [hEv2] at hSt
        subst hSt
        exact False.elim hNot2
    | inr hGe2 =>
      have hMn : m = n := Nat.le_antisymm hGe2 hGe
      subst hMn
      have hT : t₁ = t₂ := stepsN_det_eq h1 h2
      subst hT
      rw [← hEv1, hEv2]

private theorem trace_to_stepsN {p : Program} {s₀ : InterprocState}
    {tr : Nat → InterprocState}
    (h0 : tr 0 = s₀)
    (hSt : ∀ n, StepInterproc p (tr n) (.step (tr (n + 1)))) :
    ∀ n, StepsN p n s₀ (tr n) := by
  intro n
  induction n with
  | zero => rw [h0]; exact StepsN.zero s₀
  | succ k ih =>
    exact stepsN_trans ih
      (stepsN_one (stepInterproc_iff_evalStepInterproc.mp (hSt k)))

private theorem stepsN_iter_prefix {p : Program} {s₀ t : InterprocState}
    {n : Nat} (h : StepsN p n s₀ t) :
    ∀ k, k ≤ n →
      StepsN p k s₀ (iterInterprocState p s₀ k) ∧
      (k < n →
        evalStepInterproc p 0 (iterInterprocState p s₀ k) =
          .step (iterInterprocState p s₀ (k + 1))) := by
  intro k hLe
  induction k with
  | zero =>
    refine ⟨StepsN.zero s₀, fun hLt => ?_⟩
    cases n with
    | zero => exact False.elim (Nat.not_lt_zero 0 hLt)
    | succ m =>
      let ⟨sMid, hStep, _⟩ := stepsN_succ_step_exists h
      dsimp [iterInterprocState]
      rw [hStep]
  | succ j ih =>
    let ⟨hStepsJ, hNextJ⟩ := ih (Nat.le_of_succ_le hLe)
    have hStepJ : evalStepInterproc p 0 (iterInterprocState p s₀ j) =
        .step (iterInterprocState p s₀ (j + 1)) :=
      hNextJ (Nat.lt_of_succ_le hLe)
    have hStepsSucc : StepsN p (j + 1) s₀ (iterInterprocState p s₀ (j + 1)) :=
      stepsN_trans hStepsJ (stepsN_one hStepJ)
    refine ⟨hStepsSucc, fun hLt => ?_⟩
    have hRem := stepsN_det_le hLe hStepsSucc h
    have hPos : 0 < n - (j + 1) := Nat.sub_pos_of_lt hLt
    cases hEqD : n - (j + 1) with
    | zero => rw [hEqD] at hPos; exact False.elim (Nat.not_lt_zero 0 hPos)
    | succ r =>
      rw [hEqD] at hRem
      let ⟨sMid, hStep, _⟩ := stepsN_succ_step_exists hRem
      have hNext : iterInterprocState p s₀ (j + 2) = sMid := by
        change (match evalStepInterproc p 0 (iterInterprocState p s₀ (j + 1)) with
          | .step s' => s'
          | .done _ => iterInterprocState p s₀ (j + 1)
          | .fault _ => iterInterprocState p s₀ (j + 1)) = sMid
        rw [hStep]
      rw [hNext]
      exact hStep

private theorem stepsN_terminal_not_trace {p : Program} {s₀ t : InterprocState}
    {n : Nat} {res : StepResult InterprocState TerminalOut}
    {tr : Nat → InterprocState}
    (hNotStep : match res with | .step _ => False | _ => True)
    (hSteps : StepsN p n s₀ t)
    (hEv : evalStepInterproc p 0 t = res)
    (h0 : tr 0 = s₀)
    (hSt : ∀ k, StepInterproc p (tr k) (.step (tr (k + 1)))) : False := by
  have hTrN := trace_to_stepsN h0 hSt n
  have hEq := stepsN_det_eq hSteps hTrN
  subst hEq
  have hStepN := stepInterproc_iff_evalStepInterproc.mp (hSt n)
  rw [hEv] at hStepN
  subst hStepN
  exact hNotStep

private theorem forward_expansion_sim_query_iff
    {pSrc pTgt : Program} {q : Query}
    {R : InterprocState → InterprocState → Prop}
    (hInitErr : ∀ k, initStateInterproc pSrc q = .error k ↔
      initStateInterproc pTgt q = .error k)
    (hInitOk : ∀ s₀, initStateInterproc pSrc q = .ok s₀ →
      ∃ t₀, initStateInterproc pTgt q = .ok t₀ ∧ R s₀ t₀)
    (hStepSim : ∀ s t, R s t →
      (∀ s', evalStepInterproc pSrc 0 s = .step s' →
        ∃ d t', StepsN pTgt (d + 1) t t' ∧ R s' t') ∧
      (∀ out, evalStepInterproc pSrc 0 s = .done out →
        ∃ d t', StepsN pTgt d t t' ∧ evalStepInterproc pTgt 0 t' = .done out) ∧
      (∀ fk, evalStepInterproc pSrc 0 s = .fault fk →
        ∃ d t', StepsN pTgt d t t' ∧ evalStepInterproc pTgt 0 t' = .fault fk)) :
    (WellFormedInterproc pTgt q ↔ WellFormedInterproc pSrc q) ∧
    (∀ out : TerminalOut,
      BehaviorInterproc pTgt q out ↔ BehaviorInterproc pSrc q out) ∧
    (∀ k : FaultKind,
      ReachesResultInterproc pTgt q (.fault k) ↔
        ReachesResultInterproc pSrc q (.fault k)) ∧
    (DivergesInterproc pTgt q ↔ DivergesInterproc pSrc q) := by
  cases hInitS : initStateInterproc pSrc q with
  | error kErr =>
    have hInitT : initStateInterproc pTgt q = .error kErr :=
      (hInitErr kErr).mp hInitS
    refine ⟨?_, ?_, ?_, ?_⟩
    · constructor
      · intro hW; let ⟨⟨_, hOk, _⟩, _⟩ := hW; rw [hInitT] at hOk; cases hOk
      · intro hW; let ⟨⟨_, hOk, _⟩, _⟩ := hW; rw [hInitS] at hOk; cases hOk
    · intro out; unfold BehaviorInterproc ReachesResultInterproc
      rw [hInitT, hInitS]
    · intro k; unfold ReachesResultInterproc
      rw [hInitT, hInitS]
    · constructor
      · intro hD; let ⟨_, hOk, _⟩ := hD; rw [hInitT] at hOk; cases hOk
      · intro hD; let ⟨_, hOk, _⟩ := hD; rw [hInitS] at hOk; cases hOk
  | ok s₀ =>
    let ⟨t₀, hInitT, hR0⟩ := hInitOk s₀ hInitS
    have hFwdStepsGen : ∀ k s s', StepsN pSrc k s s' →
        ∀ t, R s t → ∃ m t', k ≤ m ∧ StepsN pTgt m t t' ∧ R s' t' := by
      intro k s s' hS
      induction hS with
      | zero sA =>
        intro t hR
        exact ⟨0, t, Nat.le_refl 0, StepsN.zero t, hR⟩
      | succ hEv _ ih =>
        intro t hR
        let ⟨d, tMid, hMid, hRMid⟩ := (hStepSim _ t hR).1 _ hEv
        let ⟨m, tEnd, hLe, hRest, hREnd⟩ := ih tMid hRMid
        refine ⟨(d + 1) + m, tEnd, ?_, stepsN_trans hMid hRest, hREnd⟩
        rw [Nat.add_comm (d + 1) m]
        exact Nat.succ_le_succ (Nat.le_trans hLe (Nat.le_add_right m d))
    have hFwdSteps : ∀ k s, StepsN pSrc k s₀ s →
        ∃ m t, k ≤ m ∧ StepsN pTgt m t₀ t ∧ R s t :=
      fun k s hS => hFwdStepsGen k s₀ s hS t₀ hR0
    have hBwdTerm : ∀ n, ∀ m, m ≤ n →
        ∀ s t tEnd res,
          (match res with | .step _ => False | _ => True) →
          R s t →
          StepsN pTgt m t tEnd →
          evalStepInterproc pTgt 0 tEnd = res →
          ∃ sEnd, ReachesInterproc pSrc s sEnd ∧
            evalStepInterproc pSrc 0 sEnd = res := by
      intro n
      induction n with
      | zero =>
        intro m hLe s t tEnd res hNotStep hR hStepsT hEvT
        have hm0 : m = 0 := Nat.le_zero.mp hLe
        subst hm0
        cases hStepsT
        cases hEvS : evalStepInterproc pSrc 0 s with
        | done out =>
          let ⟨d, t', hSt', hEv'⟩ := (hStepSim s t hR).2.1 out hEvS
          have hResEq := stepsN_terminal_unique hNotStep True.intro
            (StepsN.zero t) hEvT hSt' hEv'
          rw [hResEq]
          exact ⟨s, ReachesInterproc.refl s, hEvS⟩
        | fault fk =>
          let ⟨d, t', hSt', hEv'⟩ := (hStepSim s t hR).2.2 fk hEvS
          have hResEq := stepsN_terminal_unique hNotStep True.intro
            (StepsN.zero t) hEvT hSt' hEv'
          rw [hResEq]
          exact ⟨s, ReachesInterproc.refl s, hEvS⟩
        | step s' =>
          let ⟨d, t', hSt', _⟩ := (hStepSim s t hR).1 s' hEvS
          let ⟨_, hStep0, _⟩ := stepsN_succ_step_exists hSt'
          rw [hEvT] at hStep0
          subst hStep0
          exact False.elim hNotStep
      | succ k ih =>
        intro m hLe s t tEnd res hNotStep hR hStepsT hEvT
        cases hEvS : evalStepInterproc pSrc 0 s with
        | done out =>
          let ⟨d, t', hSt', hEv'⟩ := (hStepSim s t hR).2.1 out hEvS
          have hResEq := stepsN_terminal_unique hNotStep True.intro
            hStepsT hEvT hSt' hEv'
          rw [hResEq]
          exact ⟨s, ReachesInterproc.refl s, hEvS⟩
        | fault fk =>
          let ⟨d, t', hSt', hEv'⟩ := (hStepSim s t hR).2.2 fk hEvS
          have hResEq := stepsN_terminal_unique hNotStep True.intro
            hStepsT hEvT hSt' hEv'
          rw [hResEq]
          exact ⟨s, ReachesInterproc.refl s, hEvS⟩
        | step s' =>
          let ⟨d, t', hSt', hR'⟩ := (hStepSim s t hR).1 s' hEvS
          cases Nat.lt_or_ge m (d + 1) with
          | inl hLt =>
            have hDiff := stepsN_det_le (Nat.le_of_lt hLt) hStepsT hSt'
            have hPos : 0 < (d + 1) - m := Nat.sub_pos_of_lt hLt
            cases hEqD : (d + 1) - m with
            | zero => rw [hEqD] at hPos; exact False.elim (Nat.not_lt_zero 0 hPos)
            | succ r =>
              rw [hEqD] at hDiff
              let ⟨_, hStepEnd, _⟩ := stepsN_succ_step_exists hDiff
              rw [hEvT] at hStepEnd
              subst hStepEnd
              exact False.elim hNotStep
          | inr hGe =>
            have hRem := stepsN_det_le hGe hSt' hStepsT
            have hLeK : m - (d + 1) ≤ k := by
              have h1 : m - (d + 1) ≤ m - 1 :=
                Nat.sub_le_sub_left (Nat.succ_le_succ (Nat.zero_le d)) m
              have h2 : m - 1 ≤ k := by
                have h3 := Nat.sub_le_sub_right hLe 1
                rw [Nat.add_sub_cancel] at h3
                exact h3
              exact Nat.le_trans h1 h2
            let ⟨sEnd, hReach', hEvEnd⟩ :=
              ih (m - (d + 1)) hLeK s' t' tEnd res hNotStep hR' hRem hEvT
            exact ⟨sEnd,
              reachesInterproc_head_priv
                (stepInterproc_iff_evalStepInterproc.mpr hEvS) hReach',
              hEvEnd⟩
    have hTermIff : ∀ res,
        (match res with | .step _ => False | _ => True) →
        (ReachesResultInterproc pTgt q res ↔
          ReachesResultInterproc pSrc q res) := by
      intro res hNotStep
      unfold ReachesResultInterproc
      rw [hInitT, hInitS]
      constructor
      · intro ⟨tEnd, hRt, hStT⟩
        let ⟨m, hStepsT⟩ := reaches_to_stepsN hRt
        let ⟨sEnd, hRs, hEvS⟩ := hBwdTerm m m (Nat.le_refl m) s₀ t₀ tEnd res
          hNotStep hR0 hStepsT (stepInterproc_iff_evalStepInterproc.mp hStT)
        exact ⟨sEnd, hRs, stepInterproc_iff_evalStepInterproc.mpr hEvS⟩
      · intro ⟨sEnd, hRs, hStS⟩
        let ⟨k, hStepsS⟩ := reaches_to_stepsN hRs
        let ⟨m, tMid, _, hStepsT, hRMid⟩ := hFwdSteps k sEnd hStepsS
        have hEvS := stepInterproc_iff_evalStepInterproc.mp hStS
        cases res with
        | step _ => exact False.elim hNotStep
        | done out =>
          let ⟨d, tEnd, hTail, hEvT⟩ := (hStepSim sEnd tMid hRMid).2.1 out hEvS
          exact ⟨tEnd, stepsN_to_reaches (stepsN_trans hStepsT hTail),
            stepInterproc_iff_evalStepInterproc.mpr hEvT⟩
        | fault fk =>
          let ⟨d, tEnd, hTail, hEvT⟩ := (hStepSim sEnd tMid hRMid).2.2 fk hEvS
          exact ⟨tEnd, stepsN_to_reaches (stepsN_trans hStepsT hTail),
            stepInterproc_iff_evalStepInterproc.mpr hEvT⟩
    have hDoneIff : ∀ out,
        BehaviorInterproc pTgt q out ↔ BehaviorInterproc pSrc q out :=
      fun out => hTermIff (.done out) True.intro
    have hFaultIff : ∀ k,
        ReachesResultInterproc pTgt q (.fault k) ↔
          ReachesResultInterproc pSrc q (.fault k) :=
      fun k => hTermIff (.fault k) True.intro
    refine ⟨?_, hDoneIff, hFaultIff, ?_⟩
    · constructor
      · intro hW
        exact ⟨⟨s₀, hInitS, fun _ _ => ⟨0, rfl⟩⟩,
          fun k hF => hW.2 k ((hFaultIff k).mpr hF)⟩
      · intro hW
        exact ⟨⟨t₀, hInitT, fun _ _ => ⟨0, rfl⟩⟩,
          fun k hF => hW.2 k ((hFaultIff k).mp hF)⟩
    · constructor
      · intro ⟨t₀', hOkT, trT, h0T, hStT⟩
        rw [hInitT] at hOkT; injection hOkT with hEqT; subst hEqT
        have hNoTermT : ∀ s t m, StepsN pTgt m t₀ t → R s t →
            ∃ s', evalStepInterproc pSrc 0 s = .step s' := by
          intro s t m hStepsT hR
          cases hEvS : evalStepInterproc pSrc 0 s with
          | step s' => exact ⟨s', rfl⟩
          | done out =>
            let ⟨d, tEnd, hTail, hEvT⟩ := (hStepSim s t hR).2.1 out hEvS
            exact False.elim (stepsN_terminal_not_trace True.intro
              (stepsN_trans hStepsT hTail) hEvT h0T hStT)
          | fault fk =>
            let ⟨d, tEnd, hTail, hEvT⟩ := (hStepSim s t hR).2.2 fk hEvS
            exact False.elim (stepsN_terminal_not_trace True.intro
              (stepsN_trans hStepsT hTail) hEvT h0T hStT)
        have hInv : ∀ k, ∃ m t, StepsN pTgt m t₀ t ∧
            R (iterInterprocState pSrc s₀ k) t := by
          intro k
          induction k with
          | zero => exact ⟨0, t₀, StepsN.zero t₀, hR0⟩
          | succ j ih =>
            let ⟨m, t, hStepsT, hR⟩ := ih
            let ⟨s', hEvS⟩ := hNoTermT _ t m hStepsT hR
            let ⟨d, t', hTail, hR'⟩ := (hStepSim _ t hR).1 s' hEvS
            dsimp [iterInterprocState]
            rw [hEvS]
            exact ⟨m + (d + 1), t', stepsN_trans hStepsT hTail, hR'⟩
        refine ⟨s₀, hInitS, iterInterprocState pSrc s₀, rfl, fun k => ?_⟩
        let ⟨m, t, hStepsT, hR⟩ := hInv k
        let ⟨s', hEvS⟩ := hNoTermT _ t m hStepsT hR
        apply stepInterproc_iff_evalStepInterproc.mpr
        dsimp [iterInterprocState]
        rw [hEvS]
      · intro ⟨s₀', hOkS, trS, h0S, hStS⟩
        rw [hInitS] at hOkS; injection hOkS with hEqS; subst hEqS
        refine ⟨t₀, hInitT, iterInterprocState pTgt t₀, rfl, fun m => ?_⟩
        have hStepsS := trace_to_stepsN h0S hStS (m + 1)
        let ⟨M, tM, hLeM, hStepsT, _⟩ := hFwdSteps (m + 1) (trS (m + 1)) hStepsS
        exact stepInterproc_iff_evalStepInterproc.mpr
          ((stepsN_iter_prefix hStepsT m (Nat.le_of_succ_le hLeM)).2
            (Nat.lt_of_succ_le hLeM))

/-! ### Unpacked `InlineWitness` and Static Structural Lemmas -/

private structure InlineWitness (site : InlineSite) (pSrc pTgt : Program) where
  hNe : site.callerDefId ≠ site.calleeDefId
  callerSrc : Body
  calleeSrc : Body
  hGetCallerSrc : Trusted.MirSemantics.getElem? pSrc.bodies site.callerDefId = some callerSrc
  hGetCalleeSrc : Trusted.MirSemantics.getElem? pSrc.bodies site.calleeDefId = some calleeSrc
  hCallerArgLt : callerSrc.argumentCount < callerSrc.locals.length
  hCallerLocBounds : bodyAllLocalsInBounds callerSrc = true
  hCallerBlkBounds : bodyAllBlocksInBounds callerSrc = true
  hCalleeAdmitted : calleeCallAdmitted calleeSrc = true
  hCalleeLocBounds : bodyAllLocalsInBounds calleeSrc = true
  hCalleeBlkBounds : bodyAllBlocksInBounds calleeSrc = true
  hCalleeNoSD0 : bodyHasNoStorageDeadZero calleeSrc = true
  callBb : BasicBlock
  hGetCallBb : Trusted.MirSemantics.getElem? callerSrc.basicBlocks site.callBlock = some callBb
  hCallBbNotCleanup : callBb.cleanup = false
  args : List Operand
  dst : Place
  retBb : BasicBlockId
  unwind : UnwindAction
  hCallTerm : callBb.terminator = .call site.calleeDefId args dst (some retBb) unwind
  hDstUnproj : dst.projection.isEmpty = true
  hDstLt : dst.localId < callerSrc.locals.length
  hArgsLen : args.length = calleeSrc.argumentCount
  dstTy : MirTy
  calleeRetTy : MirTy
  hGetDstTy : Trusted.MirSemantics.getElem? callerSrc.locals dst.localId = some dstTy
  hGetCalleeRetTy : Trusted.MirSemantics.getElem? calleeSrc.locals 0 = some calleeRetTy
  hRetTyEq : calleeRetTy = dstTy
  callerBbsUpdated : List BasicBlock
  hSetCallerBbs : setElem? callerSrc.basicBlocks site.callBlock
    {
      statements := callBb.statements ++
        mkPrologueStorageLives calleeSrc callerSrc.locals.length 0 calleeSrc.locals ++
        mkArgAssignStmts callerSrc.locals.length 0 args
      terminator := .goto callerSrc.basicBlocks.length
      cleanup := false
    } = some callerBbsUpdated
  bodiesTgt : List Body
  hSetBodies : setElem? pSrc.bodies site.callerDefId
    {
      callerSrc with
      locals := callerSrc.locals ++ calleeSrc.locals
      basicBlocks := callerBbsUpdated ++
        calleeSrc.basicBlocks.map
          (shiftCalleeBlock callerSrc.locals.length callerSrc.basicBlocks.length
            (callerSrc.basicBlocks.length + calleeSrc.basicBlocks.length) unwind) ++
        [{
          statements := (.assign dst (.use (.move ⟨callerSrc.locals.length, []⟩))) ::
            mkEpilogueStorageDeads callerSrc.locals.length 0 calleeSrc.locals.length
          terminator := .goto retBb
          cleanup := false
        }]
    } = some bodiesTgt
  hPTgt : pTgt = { pSrc with bodies := bodiesTgt }

private noncomputable def InlineWitness.localBase {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt) : Nat := w.callerSrc.locals.length

private noncomputable def InlineWitness.blockBase {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt) : Nat := w.callerSrc.basicBlocks.length

private noncomputable def InlineWitness.exitBlock {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt) : Nat :=
  w.blockBase + w.calleeSrc.basicBlocks.length

private noncomputable def InlineWitness.prologueLiveStmts {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt) : List StatementKind :=
  mkPrologueStorageLives w.calleeSrc w.localBase 0 w.calleeSrc.locals

private noncomputable def InlineWitness.argAssignStmts {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt) : List StatementKind :=
  mkArgAssignStmts w.localBase 0 w.args

private noncomputable def InlineWitness.callBbTgt {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt) : BasicBlock := {
  statements := w.callBb.statements ++ w.prologueLiveStmts ++ w.argAssignStmts
  terminator := .goto w.blockBase
  cleanup := false
}

private noncomputable def InlineWitness.epilogueDeadStmts {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt) : List StatementKind :=
  mkEpilogueStorageDeads w.localBase 0 w.calleeSrc.locals.length

private noncomputable def InlineWitness.exitBb {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt) : BasicBlock := {
  statements := (.assign w.dst (.use (.move ⟨w.localBase, []⟩))) :: w.epilogueDeadStmts
  terminator := .goto w.retBb
  cleanup := false
}

private noncomputable def InlineWitness.shiftedCalleeBlocks {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt) : List BasicBlock :=
  w.calleeSrc.basicBlocks.map
    (shiftCalleeBlock w.localBase w.blockBase w.exitBlock w.unwind)

private noncomputable def InlineWitness.callerTgt {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt) : Body := {
  w.callerSrc with
  locals := w.callerSrc.locals ++ w.calleeSrc.locals
  basicBlocks := w.callerBbsUpdated ++ w.shiftedCalleeBlocks ++ [w.exitBb]
}

private theorem extract_inlineWitness {site : InlineSite} {pSrc pTgt : Program}
    (hApply : applyMirInlineCallSite site pSrc = some pTgt) :
    Nonempty (InlineWitness site pSrc pTgt) := by
  unfold applyMirInlineCallSite at hApply
  cases hSame : Nat.beq site.callerDefId site.calleeDefId with
  | true => rw [hSame] at hApply; cases hApply
  | false =>
    rw [hSame] at hApply; dsimp at hApply
    have hNe : site.callerDefId ≠ site.calleeDefId := nat_ne_of_beq_false hSame
    cases hC : Trusted.MirSemantics.getElem? pSrc.bodies site.callerDefId with
    | none => rw [hC] at hApply; cases hApply
    | some callerSrc =>
      rw [hC] at hApply
      cases hE : Trusted.MirSemantics.getElem? pSrc.bodies site.calleeDefId with
      | none => rw [hE] at hApply; cases hApply
      | some calleeSrc =>
        rw [hE] at hApply; dsimp at hApply
        cases hG : (!Nat.blt callerSrc.argumentCount callerSrc.locals.length ||
            !bodyAllLocalsInBounds callerSrc ||
            !bodyAllBlocksInBounds callerSrc ||
            !calleeCallAdmitted calleeSrc ||
            !bodyAllLocalsInBounds calleeSrc ||
            !bodyAllBlocksInBounds calleeSrc ||
            !bodyHasNoStorageDeadZero calleeSrc) with
        | true => rw [hG] at hApply; cases hApply
        | false =>
          rw [hG] at hApply; dsimp at hApply
          let ⟨hG1, hNoSD0⟩ := bool_or_false hG
          let ⟨hG2, hCalleeBlk⟩ := bool_or_false hG1
          let ⟨hG3, hCalleeLoc⟩ := bool_or_false hG2
          let ⟨hG4, hCalleeAdm⟩ := bool_or_false hG3
          let ⟨hG5, hCallerBlk⟩ := bool_or_false hG4
          let ⟨hCallerArg, hCallerLoc⟩ := bool_or_false hG5
          cases hBb : Trusted.MirSemantics.getElem? callerSrc.basicBlocks site.callBlock with
          | none => rw [hBb] at hApply; cases hApply
          | some callBb =>
            rw [hBb] at hApply; dsimp at hApply
            cases hCl : callBb.cleanup with
            | true => rw [hCl] at hApply; cases hApply
            | false =>
              rw [hCl] at hApply; dsimp at hApply
              cases hTerm : callBb.terminator with
              | goto _ => rw [hTerm] at hApply; cases hApply
              | switchInt _ _ => rw [hTerm] at hApply; cases hApply
              | return_ => rw [hTerm] at hApply; cases hApply
              | unreachable => rw [hTerm] at hApply; cases hApply
              | unwindResume => rw [hTerm] at hApply; cases hApply
              | assert _ _ _ _ _ => rw [hTerm] at hApply; cases hApply
              | unsupported => rw [hTerm] at hApply; cases hApply
              | call f args dst target unwind =>
                rw [hTerm] at hApply
                cases target with
                | none => cases hApply
                | some retBb =>
                  dsimp at hApply
                  cases hC2 : (!Nat.beq f site.calleeDefId ||
                      !dst.projection.isEmpty ||
                      !Nat.blt dst.localId callerSrc.locals.length ||
                      !Nat.beq args.length calleeSrc.argumentCount) with
                  | true => rw [hC2] at hApply; cases hApply
                  | false =>
                    rw [hC2] at hApply; dsimp at hApply
                    let ⟨hC21, hALen⟩ := bool_or_false hC2
                    let ⟨hC22, hDLt⟩ := bool_or_false hC21
                    let ⟨hFEq, hDProj⟩ := bool_or_false hC22
                    have hfEq : f = site.calleeDefId := nat_beq_eq (bool_not_false hFEq)
                    subst hfEq
                    cases hDTy : Trusted.MirSemantics.getElem? callerSrc.locals dst.localId with
                    | none => rw [hDTy] at hApply; cases hApply
                    | some dstTy =>
                      rw [hDTy] at hApply
                      cases hRTy : Trusted.MirSemantics.getElem? calleeSrc.locals 0 with
                      | none => rw [hRTy] at hApply; cases hApply
                      | some calleeRetTy =>
                        rw [hRTy] at hApply; dsimp at hApply
                        cases hTyEq : (!MirTy.beq calleeRetTy dstTy) with
                        | true => rw [hTyEq] at hApply; cases hApply
                        | false =>
                          rw [hTyEq] at hApply; dsimp at hApply
                          cases hSetBbs : setElem? callerSrc.basicBlocks site.callBlock
                              {
                                statements := callBb.statements ++
                                  mkPrologueStorageLives calleeSrc callerSrc.locals.length 0
                                    calleeSrc.locals ++
                                  mkArgAssignStmts callerSrc.locals.length 0 args
                                terminator := .goto callerSrc.basicBlocks.length
                                cleanup := false
                              } with
                          | none => rw [hSetBbs] at hApply; cases hApply
                          | some callerBbsUpdated =>
                            rw [hSetBbs] at hApply; dsimp at hApply
                            cases hSetBods : setElem? pSrc.bodies site.callerDefId
                                {
                                  callerSrc with
                                  locals := callerSrc.locals ++ calleeSrc.locals
                                  basicBlocks := callerBbsUpdated ++
                                    calleeSrc.basicBlocks.map
                                      (shiftCalleeBlock callerSrc.locals.length
                                        callerSrc.basicBlocks.length
                                        (callerSrc.basicBlocks.length +
                                          calleeSrc.basicBlocks.length) unwind) ++
                                    [{
                                      statements :=
                                        (.assign dst (.use (.move ⟨callerSrc.locals.length, []⟩))) ::
                                          mkEpilogueStorageDeads callerSrc.locals.length 0
                                            calleeSrc.locals.length
                                      terminator := .goto retBb
                                      cleanup := false
                                    }]
                                } with
                            | none => rw [hSetBods] at hApply; cases hApply
                            | some bodiesTgt =>
                              rw [hSetBods] at hApply; dsimp at hApply
                              injection hApply with hPEq
                              exact ⟨{
                                hNe := hNe
                                callerSrc := callerSrc
                                calleeSrc := calleeSrc
                                hGetCallerSrc := hC
                                hGetCalleeSrc := hE
                                hCallerArgLt := nat_blt_lt (bool_not_false hCallerArg)
                                hCallerLocBounds := bool_not_false hCallerLoc
                                hCallerBlkBounds := bool_not_false hCallerBlk
                                hCalleeAdmitted := bool_not_false hCalleeAdm
                                hCalleeLocBounds := bool_not_false hCalleeLoc
                                hCalleeBlkBounds := bool_not_false hCalleeBlk
                                hCalleeNoSD0 := bool_not_false hNoSD0
                                callBb := callBb
                                hGetCallBb := hBb
                                hCallBbNotCleanup := hCl
                                args := args
                                dst := dst
                                retBb := retBb
                                unwind := unwind
                                hCallTerm := hTerm
                                hDstUnproj := bool_not_false hDProj
                                hDstLt := nat_blt_lt (bool_not_false hDLt)
                                hArgsLen := nat_beq_eq (bool_not_false hALen)
                                dstTy := dstTy
                                calleeRetTy := calleeRetTy
                                hGetDstTy := hDTy
                                hGetCalleeRetTy := hRTy
                                hRetTyEq := mirTy_beq_eq (bool_not_false hTyEq)
                                callerBbsUpdated := callerBbsUpdated
                                hSetCallerBbs := hSetBbs
                                bodiesTgt := bodiesTgt
                                hSetBodies := hSetBods
                                hPTgt := hPEq.symm
                              }⟩

private theorem w_localBase_pos {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt) : 0 < w.localBase :=
  Nat.lt_of_le_of_lt (Nat.zero_le _) w.hCallerArgLt

private theorem w_blockBase_pos {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt) : 0 < w.blockBase :=
  Nat.lt_of_le_of_lt (Nat.zero_le _) (getElem?_some_lt w.hGetCallBb)

private theorem w_callee_admitted_parts {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt) :
    w.calleeSrc.basicBlocks.isEmpty = false ∧
    w.calleeSrc.argumentCount < w.calleeSrc.locals.length ∧
    storageAnnotationsInBounds w.calleeSrc = true ∧
    w.calleeSrc.locals.all isSupportedScalarOrUnitTy = true := by
  have h := w.hCalleeAdmitted
  unfold calleeCallAdmitted at h
  let ⟨h123, h4⟩ := bool_and_true h
  let ⟨h12, h3⟩ := bool_and_true h123
  let ⟨h1, h2⟩ := bool_and_true h12
  exact ⟨bool_not_true h1, nat_blt_lt h2, h3, h4⟩

private theorem w_callee_blocks_pos {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt) : 0 < w.calleeSrc.basicBlocks.length :=
  list_pos_of_isEmpty_false (w_callee_admitted_parts w).1

private theorem w_callee_locals_pos {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt) : 0 < w.calleeSrc.locals.length :=
  Nat.lt_of_le_of_lt (Nat.zero_le _) (w_callee_admitted_parts w).2.1

private theorem w_retBb_lt {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt) : w.retBb < w.blockBase := by
  have hBb := list_all_getElem? w.hCallerBlkBounds w.hGetCallBb
  rw [w.hCallTerm] at hBb
  dsimp [terminatorBlocksLt] at hBb
  exact nat_blt_lt (bool_and_true hBb).1

private theorem w_args_locals_lt {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt) :
    w.args.all (operandLocalsLt w.localBase) = true := by
  have hBb := list_all_getElem? w.hCallerLocBounds w.hGetCallBb
  have hTerm := (bool_and_true hBb).2
  rw [w.hCallTerm] at hTerm
  dsimp [terminatorLocalsLt] at hTerm
  exact (bool_and_true hTerm).1

private theorem w_bodies_getElem?_caller {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt) :
    Trusted.MirSemantics.getElem? pTgt.bodies site.callerDefId = some w.callerTgt := by
  have hBods : pTgt.bodies = w.bodiesTgt := congrArg Program.bodies w.hPTgt
  rw [hBods]
  exact setElem?_getElem?_same w.hSetBodies

private theorem w_bodies_getElem?_ne {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt) {d : DefId} (hNe : d ≠ site.callerDefId) :
    Trusted.MirSemantics.getElem? pTgt.bodies d =
      Trusted.MirSemantics.getElem? pSrc.bodies d := by
  have hBods : pTgt.bodies = w.bodiesTgt := congrArg Program.bodies w.hPTgt
  rw [hBods]
  exact setElem?_getElem?_ne w.hSetBodies hNe

private theorem w_bodies_getElem?_callee {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt) :
    Trusted.MirSemantics.getElem? pTgt.bodies site.calleeDefId = some w.calleeSrc := by
  rw [w_bodies_getElem?_ne w (fun h => w.hNe h.symm)]
  exact w.hGetCalleeSrc

private theorem w_callerBbsUpdated_length {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt) :
    w.callerBbsUpdated.length = w.blockBase :=
  setElem?_length w.hSetCallerBbs

private theorem w_callerTgt_blocks_getElem?_callBlock {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt) :
    Trusted.MirSemantics.getElem? w.callerTgt.basicBlocks site.callBlock =
      some w.callBbTgt := by
  have hLt : site.callBlock < w.callerBbsUpdated.length := by
    rw [w_callerBbsUpdated_length w]
    exact getElem?_some_lt w.hGetCallBb
  have hLt12 : site.callBlock < (w.callerBbsUpdated ++ w.shiftedCalleeBlocks).length := by
    rw [list_append_length]
    exact nat_lt_add_right _ hLt
  dsimp [InlineWitness.callerTgt]
  rw [getElem?_append_left (w.callerBbsUpdated ++ w.shiftedCalleeBlocks) [w.exitBb] _ hLt12]
  rw [getElem?_append_left w.callerBbsUpdated w.shiftedCalleeBlocks _ hLt]
  exact setElem?_getElem?_same w.hSetCallerBbs

private theorem w_callerTgt_blocks_getElem?_lt_ne {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt) {b : BasicBlockId}
    (hLt : b < w.blockBase) (hNe : b ≠ site.callBlock) :
    Trusted.MirSemantics.getElem? w.callerTgt.basicBlocks b =
      Trusted.MirSemantics.getElem? w.callerSrc.basicBlocks b := by
  have hLtU : b < w.callerBbsUpdated.length := by
    rw [w_callerBbsUpdated_length w]; exact hLt
  have hLt12 : b < (w.callerBbsUpdated ++ w.shiftedCalleeBlocks).length := by
    rw [list_append_length]
    exact nat_lt_add_right _ hLtU
  dsimp [InlineWitness.callerTgt]
  rw [getElem?_append_left (w.callerBbsUpdated ++ w.shiftedCalleeBlocks) [w.exitBb] _ hLt12]
  rw [getElem?_append_left w.callerBbsUpdated w.shiftedCalleeBlocks _ hLtU]
  exact setElem?_getElem?_ne w.hSetCallerBbs hNe

private theorem w_callerTgt_blocks_getElem?_callee {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt) {cb : BasicBlockId}
    (hLt : cb < w.calleeSrc.basicBlocks.length) :
    Trusted.MirSemantics.getElem? w.callerTgt.basicBlocks (w.blockBase + cb) =
      (Trusted.MirSemantics.getElem? w.calleeSrc.basicBlocks cb).map
        (shiftCalleeBlock w.localBase w.blockBase w.exitBlock w.unwind) := by
  have hLen1 : (w.callerBbsUpdated ++ w.shiftedCalleeBlocks).length =
      w.blockBase + w.calleeSrc.basicBlocks.length := by
    rw [list_append_length, w_callerBbsUpdated_length w,
        InlineWitness.shiftedCalleeBlocks, map_length_eq]
  have hLtAll : w.blockBase + cb < (w.callerBbsUpdated ++ w.shiftedCalleeBlocks).length := by
    rw [hLen1]
    exact nat_add_lt_add_left_of_lt w.blockBase hLt
  dsimp [InlineWitness.callerTgt]
  rw [getElem?_append_left _ _ _ hLtAll]
  rw [← w_callerBbsUpdated_length w]
  rw [getElem?_append_right_add]
  dsimp [InlineWitness.shiftedCalleeBlocks]
  rw [getElem?_map, w_callerBbsUpdated_length w]

private theorem w_callerTgt_blocks_getElem?_exit {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt) :
    Trusted.MirSemantics.getElem? w.callerTgt.basicBlocks w.exitBlock =
      some w.exitBb := by
  have hLen1 : (w.callerBbsUpdated ++ w.shiftedCalleeBlocks).length = w.exitBlock := by
    rw [list_append_length, w_callerBbsUpdated_length w,
        InlineWitness.shiftedCalleeBlocks, map_length_eq]
    rfl
  dsimp [InlineWitness.callerTgt]
  have hAdd0 : w.exitBlock = (w.callerBbsUpdated ++ w.shiftedCalleeBlocks).length + 0 := by
    rw [hLen1, Nat.add_zero]
  rw [hAdd0]
  rw [getElem?_append_right_add]
  rfl

private theorem mkPrologueStorageLives_all_marker_false (callee : Body) (localBase : Nat)
    (l : LocalId) (hLt : l < localBase) (start : Nat) (tys : List MirTy) :
    (mkPrologueStorageLives callee localBase start tys).any
      (stmtHasStorageMarker l) = false := by
  induction tys generalizing start with
  | nil => rfl
  | cons _ rest ih =>
    dsimp [mkPrologueStorageLives]
    cases (Nat.beq start 0 || Nat.ble start callee.argumentCount ||
        !hasStorageAnnotation callee start) with
    | false => exact ih (start + 1)
    | true =>
      dsimp [List.any, stmtHasStorageMarker]
      rw [nat_beq_add_left_of_lt hLt, ih (start + 1)]
      rfl

private theorem mkArgAssignStmts_all_marker_false (localBase : Nat) (l : LocalId)
    (start : Nat) (args : List Operand) :
    (mkArgAssignStmts localBase start args).any (stmtHasStorageMarker l) = false := by
  induction args generalizing start with
  | nil => rfl
  | cons _ rest ih =>
    dsimp [mkArgAssignStmts, List.any, stmtHasStorageMarker]
    exact ih (start + 1)

private theorem mkEpilogueStorageDeads_all_marker_false (localBase : Nat)
    (l : LocalId) (hLt : l < localBase) (start count : Nat) :
    (mkEpilogueStorageDeads localBase start count).any
      (stmtHasStorageMarker l) = false := by
  induction count generalizing start with
  | zero => rfl
  | succ k ih =>
    dsimp [mkEpilogueStorageDeads, List.any, stmtHasStorageMarker]
    rw [nat_beq_add_left_of_lt hLt, ih (start + 1)]
    rfl

private theorem mkEpilogueStorageDeads_length (localBase start count : Nat) :
    (mkEpilogueStorageDeads localBase start count).length = count := by
  induction count generalizing start with
  | zero => rfl
  | succ k ih =>
    dsimp [mkEpilogueStorageDeads, List.length]
    rw [ih (start + 1)]

private theorem mkEpilogueStorageDeads_getElem? (localBase start count j : Nat)
    (hLt : j < count) :
    Trusted.MirSemantics.getElem?
      (mkEpilogueStorageDeads localBase start count) j =
      some (.storageDead (localBase + (start + j))) := by
  induction count generalizing start j with
  | zero => exact False.elim (Nat.not_lt_zero j hLt)
  | succ k ih =>
    cases j with
    | zero =>
      dsimp [mkEpilogueStorageDeads, Trusted.MirSemantics.getElem?]
    | succ m =>
      dsimp [mkEpilogueStorageDeads, Trusted.MirSemantics.getElem?]
      rw [ih (start + 1) m (Nat.lt_of_succ_lt_succ hLt)]
      have hAdd : start + 1 + m = start + (m + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 m]
      rw [hAdd]

private theorem shiftStmt_marker_false_of_lt (localBase l : Nat) (hLt : l < localBase)
    (stmt : StatementKind) :
    stmtHasStorageMarker l (shiftStmt localBase stmt) = false := by
  cases stmt with
  | assign _ _ => rfl
  | nop => rfl
  | unsupported => rfl
  | storageLive id =>
    dsimp [shiftStmt, stmtHasStorageMarker]
    exact nat_beq_add_left_of_lt hLt
  | storageDead id =>
    dsimp [shiftStmt, stmtHasStorageMarker]
    exact nat_beq_add_left_of_lt hLt

private theorem w_hasStorageAnnotation_lt {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt) {l : LocalId} (hLt : l < w.localBase) :
    hasStorageAnnotation w.callerTgt l = hasStorageAnnotation w.callerSrc l := by
  unfold hasStorageAnnotation
  dsimp [InlineWitness.callerTgt]
  rw [list_any_append, list_any_append]
  have hShiftedFalse : w.shiftedCalleeBlocks.any
      (fun bb => bb.statements.any (stmtHasStorageMarker l)) = false := by
    dsimp [InlineWitness.shiftedCalleeBlocks]
    rw [list_any_map]
    apply list_any_false_of_forall_getElem?
    intro i bb _
    dsimp [shiftCalleeBlock]
    rw [list_any_map]
    apply list_any_false_of_forall_getElem?
    intro j st _
    exact shiftStmt_marker_false_of_lt w.localBase l hLt st
  have hExitFalse : [w.exitBb].any
      (fun bb => bb.statements.any (stmtHasStorageMarker l)) = false := by
    dsimp [List.any, InlineWitness.exitBb, stmtHasStorageMarker,
           InlineWitness.epilogueDeadStmts]
    rw [mkEpilogueStorageDeads_all_marker_false w.localBase l hLt 0
          w.calleeSrc.locals.length]
    rfl
  rw [hShiftedFalse, hExitFalse]
  have hUpdatedEq : w.callerBbsUpdated.any
      (fun bb => bb.statements.any (stmtHasStorageMarker l)) =
      w.callerSrc.basicBlocks.any
        (fun bb => bb.statements.any (stmtHasStorageMarker l)) := by
    apply list_any_eq_of_getElem? (w_callerBbsUpdated_length w)
    intro i bU bS hU hS
    cases hEq : Nat.beq i site.callBlock with
    | false =>
      have hNe := nat_ne_of_beq_false hEq
      rw [setElem?_getElem?_ne w.hSetCallerBbs hNe, hS] at hU
      injection hU with hB; rw [hB]
    | true =>
      have hI := nat_beq_eq hEq
      subst hI
      rw [setElem?_getElem?_same w.hSetCallerBbs] at hU
      rw [w.hGetCallBb] at hS
      injection hU with hBU; injection hS with hBS
      subst hBU; subst hBS
      dsimp
      rw [list_any_append, list_any_append]
      have hProF := mkPrologueStorageLives_all_marker_false w.calleeSrc
        w.callerSrc.locals.length l hLt 0 w.calleeSrc.locals
      have hArgF := mkArgAssignStmts_all_marker_false w.callerSrc.locals.length
        l 0 w.args
      rw [hProF, hArgF]
      cases w.callBb.statements.any (stmtHasStorageMarker l) <;> rfl
  rw [hUpdatedEq]
  cases w.callerSrc.basicBlocks.any
      (fun bb => bb.statements.any (stmtHasStorageMarker l)) <;> rfl

private theorem w_hasStorageAnnotation_shifted {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt) {j : Nat}
    (hLt : j < w.calleeSrc.locals.length) :
    hasStorageAnnotation w.callerTgt (w.localBase + j) = true := by
  unfold hasStorageAnnotation
  have hGetExit := w_callerTgt_blocks_getElem?_exit w
  apply list_any_true_of_getElem? hGetExit
  dsimp [InlineWitness.exitBb, List.any, stmtHasStorageMarker,
         InlineWitness.epilogueDeadStmts]
  have hGetDead := mkEpilogueStorageDeads_getElem? w.localBase 0
    w.calleeSrc.locals.length j hLt
  rw [Nat.zero_add] at hGetDead
  have hAnyDead : (mkEpilogueStorageDeads w.localBase 0 w.calleeSrc.locals.length).any
      (stmtHasStorageMarker (w.localBase + j)) = true :=
    list_any_true_of_getElem? hGetDead (nat_beq_refl (w.localBase + j))
  rw [hAnyDead]
  rfl

private theorem storageAnnotationsInBounds_of_bodyAllLocalsInBounds {b : Body}
    (h : bodyAllLocalsInBounds b = true) :
    storageAnnotationsInBounds b = true := by
  unfold storageAnnotationsInBounds
  apply list_all_of_forall_getElem?
  intro i bb hBb
  have hBbEntry := list_all_getElem? h hBb
  have hBbAll := (bool_and_true hBbEntry).1
  apply list_all_of_forall_getElem?
  intro j stmt hSt
  have hSLt := list_all_getElem? hBbAll hSt
  cases stmt with
  | storageLive _ => exact hSLt
  | storageDead _ => exact hSLt
  | assign _ _ => rfl
  | nop => rfl
  | unsupported => rfl

private theorem mkPrologueStorageLives_in_bounds (callee : Body) (localBase : Nat)
    (start : Nat) (tys : List MirTy)
    (hSum : start + tys.length = callee.locals.length) :
    (mkPrologueStorageLives callee localBase start tys).all (fun stmt =>
      match stmt with
      | .storageLive id | .storageDead id =>
        Nat.blt id (localBase + callee.locals.length)
      | _ => true) = true := by
  induction tys generalizing start with
  | nil => rfl
  | cons _ rest ih =>
    dsimp [List.length] at hSum
    have hStartLt : start < callee.locals.length := by
      rw [← hSum]
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self start)
        (by rw [Nat.add_succ]; exact Nat.succ_le_succ (Nat.le_add_right start rest.length))
    have hSumNext : (start + 1) + rest.length = callee.locals.length := by
      rw [Nat.add_assoc, Nat.add_comm 1 rest.length, ← Nat.add_assoc]
      exact hSum
    dsimp [mkPrologueStorageLives]
    cases (Nat.beq start 0 || Nat.ble start callee.argumentCount ||
        !hasStorageAnnotation callee start) with
    | false => exact ih (start + 1) hSumNext
    | true =>
      dsimp [List.all]
      exact bool_and_intro
        (nat_lt_blt (nat_add_lt_add_left_of_lt localBase hStartLt))
        (ih (start + 1) hSumNext)

private theorem mkArgAssignStmts_storage_in_bounds (localBase bound start : Nat)
    (args : List Operand) :
    (mkArgAssignStmts localBase start args).all (fun stmt =>
      match stmt with
      | .storageLive id | .storageDead id => Nat.blt id bound
      | _ => true) = true := by
  induction args generalizing start with
  | nil => rfl
  | cons _ rest ih =>
    dsimp [mkArgAssignStmts, List.all]
    exact ih (start + 1)

private theorem mkEpilogueStorageDeads_in_bounds (localBase bound start count : Nat)
    (hSum : start + count ≤ bound) :
    (mkEpilogueStorageDeads localBase start count).all (fun stmt =>
      match stmt with
      | .storageLive id | .storageDead id => Nat.blt id (localBase + bound)
      | _ => true) = true := by
  induction count generalizing start with
  | zero => rfl
  | succ k ih =>
    have hStartLt : start < bound :=
      Nat.lt_of_lt_of_le (Nat.lt_succ_self start)
        (Nat.le_trans (by rw [Nat.add_succ]; exact Nat.succ_le_succ (Nat.le_add_right start k)) hSum)
    have hSumNext : (start + 1) + k ≤ bound := by
      rw [Nat.add_assoc, Nat.add_comm 1 k, ← Nat.add_assoc]
      exact hSum
    dsimp [mkEpilogueStorageDeads, List.all]
    exact bool_and_intro
      (nat_lt_blt (nat_add_lt_add_left_of_lt localBase hStartLt))
      (ih (start + 1) hSumNext)

private theorem w_storageAnnotationsInBounds_callerTgt {site : InlineSite}
    {pSrc pTgt : Program} (w : InlineWitness site pSrc pTgt) :
    storageAnnotationsInBounds w.callerTgt = true := by
  unfold storageAnnotationsInBounds
  have hLenLoc : w.callerTgt.locals.length =
      w.localBase + w.calleeSrc.locals.length :=
    list_append_length w.callerSrc.locals w.calleeSrc.locals
  dsimp [InlineWitness.callerTgt]
  rw [list_append_length]
  rw [list_all_append, list_all_append]
  have hUpd : w.callerBbsUpdated.all (fun bb =>
      bb.statements.all (fun stmt =>
        match stmt with
        | .storageLive id | .storageDead id =>
          Nat.blt id (w.localBase + w.calleeSrc.locals.length)
        | _ => true)) = true := by
    apply list_all_of_forall_getElem?
    intro i bb hGet
    cases hEq : Nat.beq i site.callBlock with
    | false =>
      have hNe := nat_ne_of_beq_false hEq
      rw [setElem?_getElem?_ne w.hSetCallerBbs hNe] at hGet
      have hBbEntry := list_all_getElem? w.hCallerLocBounds hGet
      have hBbSt := (bool_and_true hBbEntry).1
      apply list_all_of_forall_getElem?
      intro j stmt hSt
      have hSLt := list_all_getElem? hBbSt hSt
      cases stmt with
      | storageLive id =>
        exact nat_lt_blt (nat_lt_add_right _ (nat_blt_lt hSLt))
      | storageDead id =>
        exact nat_lt_blt (nat_lt_add_right _ (nat_blt_lt hSLt))
      | assign _ _ => rfl
      | nop => rfl
      | unsupported => rfl
    | true =>
      have hI := nat_beq_eq hEq; subst hI
      rw [setElem?_getElem?_same w.hSetCallerBbs] at hGet
      injection hGet with hEqB; subst hEqB
      dsimp
      rw [list_all_append, list_all_append]
      have hCallSt : w.callBb.statements.all (fun stmt =>
          match stmt with
          | .storageLive id | .storageDead id =>
            Nat.blt id (w.localBase + w.calleeSrc.locals.length)
          | _ => true) = true := by
        have hBbEntry := list_all_getElem? w.hCallerLocBounds w.hGetCallBb
        have hBbSt := (bool_and_true hBbEntry).1
        apply list_all_of_forall_getElem?
        intro j stmt hSt
        have hSLt := list_all_getElem? hBbSt hSt
        cases stmt with
        | storageLive id =>
          exact nat_lt_blt (nat_lt_add_right _ (nat_blt_lt hSLt))
        | storageDead id =>
          exact nat_lt_blt (nat_lt_add_right _ (nat_blt_lt hSLt))
        | assign _ _ => rfl
        | nop => rfl
        | unsupported => rfl
      have hPro := mkPrologueStorageLives_in_bounds w.calleeSrc w.localBase 0
        w.calleeSrc.locals (Nat.zero_add _)
      have hArg := mkArgAssignStmts_storage_in_bounds w.localBase
        (w.localBase + w.calleeSrc.locals.length) 0 w.args
      exact bool_and_intro (bool_and_intro hCallSt hPro) hArg
  have hShifted : w.shiftedCalleeBlocks.all (fun bb =>
      bb.statements.all (fun stmt =>
        match stmt with
        | .storageLive id | .storageDead id =>
          Nat.blt id (w.localBase + w.calleeSrc.locals.length)
        | _ => true)) = true := by
    dsimp [InlineWitness.shiftedCalleeBlocks]
    rw [list_all_map]
    apply list_all_of_forall_getElem?
    intro i bb hGet
    dsimp [shiftCalleeBlock]
    rw [list_all_map]
    have hBbEntry := list_all_getElem? w.hCalleeLocBounds hGet
    have hBbSt := (bool_and_true hBbEntry).1
    apply list_all_of_forall_getElem?
    intro j stmt hSt
    have hSLt := list_all_getElem? hBbSt hSt
    cases stmt with
    | storageLive id =>
      dsimp [shiftStmt]
      exact nat_lt_blt (nat_add_lt_add_left_of_lt w.localBase (nat_blt_lt hSLt))
    | storageDead id =>
      dsimp [shiftStmt]
      exact nat_lt_blt (nat_add_lt_add_left_of_lt w.localBase (nat_blt_lt hSLt))
    | assign _ _ => rfl
    | nop => rfl
    | unsupported => rfl
  have hExit : [w.exitBb].all (fun bb =>
      bb.statements.all (fun stmt =>
        match stmt with
        | .storageLive id | .storageDead id =>
          Nat.blt id (w.localBase + w.calleeSrc.locals.length)
        | _ => true)) = true := by
    dsimp [List.all, InlineWitness.exitBb, InlineWitness.epilogueDeadStmts]
    have hEpi := mkEpilogueStorageDeads_in_bounds w.localBase
      w.calleeSrc.locals.length 0 w.calleeSrc.locals.length
      (by rw [Nat.zero_add]; exact Nat.le_refl _)
    rw [hEpi]
    rfl
  exact bool_and_intro (bool_and_intro hUpd hShifted) hExit

private theorem w_initLocalsLoop_callerTgt {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt) (args : List Val) :
    initLocalsLoop w.callerTgt args 0 w.callerTgt.locals =
      initLocalsLoop w.callerSrc args 0 w.callerSrc.locals ++
        List.replicate w.calleeSrc.locals.length .dead := by
  have hLocEq : w.callerTgt.locals = w.callerSrc.locals ++ w.calleeSrc.locals := rfl
  rw [hLocEq, initLocalsLoop_append]
  have hPref : initLocalsLoop w.callerTgt args 0 w.callerSrc.locals =
      initLocalsLoop w.callerSrc args 0 w.callerSrc.locals := by
    apply list_eq_of_getElem?_eq
    · rw [initLocalsLoop_length, initLocalsLoop_length]
    · intro i
      cases hTy : Trusted.MirSemantics.getElem? w.callerSrc.locals i with
      | none =>
        have hGe := getElem?_none_ge hTy
        rw [getElem?_none_of_ge (by rw [initLocalsLoop_length]; exact hGe)]
        rw [getElem?_none_of_ge (by rw [initLocalsLoop_length]; exact hGe)]
      | some ty =>
        have hLt : i < w.localBase := getElem?_some_lt hTy
        rw [initLocalsLoop_getElem? w.callerTgt args 0 w.callerSrc.locals i ty hTy]
        rw [initLocalsLoop_getElem? w.callerSrc args 0 w.callerSrc.locals i ty hTy]
        rw [Nat.zero_add]
        rw [w_hasStorageAnnotation_lt w hLt]
        rfl
  have hSuff : initLocalsLoop w.callerTgt args (0 + w.callerSrc.locals.length)
      w.calleeSrc.locals = List.replicate w.calleeSrc.locals.length .dead := by
    rw [Nat.zero_add]
    change initLocalsLoop w.callerTgt args w.localBase w.calleeSrc.locals =
      List.replicate w.calleeSrc.locals.length .dead
    apply list_eq_of_getElem?_eq
    · rw [initLocalsLoop_length, list_replicate_length]
    · intro j
      cases hTy : Trusted.MirSemantics.getElem? w.calleeSrc.locals j with
      | none =>
        have hGe := getElem?_none_ge hTy
        rw [getElem?_none_of_ge (by rw [initLocalsLoop_length]; exact hGe)]
        rw [getElem?_none_of_ge (by rw [list_replicate_length]; exact hGe)]
      | some ty =>
        have hLt : j < w.calleeSrc.locals.length := getElem?_some_lt hTy
        rw [initLocalsLoop_getElem? w.callerTgt args w.localBase w.calleeSrc.locals j ty hTy]
        rw [getElem?_replicate_lt _ _ _ hLt]
        have hNe0 : Nat.beq (w.localBase + j) 0 = false :=
          nat_beq_false_of_ne (nat_add_ne_zero_left (w_localBase_pos w))
        have hGtArg : Nat.ble (w.localBase + j) w.callerTgt.argumentCount = false :=
          nat_gt_ble_false (Nat.lt_of_lt_of_le w.hCallerArgLt (Nat.le_add_right _ _))
        have hHasSt : hasStorageAnnotation w.callerTgt (w.localBase + j) = true :=
          w_hasStorageAnnotation_shifted w hLt
        rw [hNe0, hGtArg, hHasSt]
        rfl
  rw [hPref, hSuff]

private theorem w_callerTgt_supported_tys {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt) :
    w.callerTgt.locals.all isSupportedScalarOrUnitTy =
      w.callerSrc.locals.all isSupportedScalarOrUnitTy := by
  dsimp [InlineWitness.callerTgt]
  rw [list_all_append, (w_callee_admitted_parts w).2.2.2]
  cases w.callerSrc.locals.all isSupportedScalarOrUnitTy <;> rfl

private theorem w_callerTgt_basicBlocks_nonEmpty {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt) :
    w.callerTgt.basicBlocks.isEmpty = false ∧
    w.callerSrc.basicBlocks.isEmpty = false := by
  have hSrc := list_isEmpty_false_of_pos (w_blockBase_pos w)
  have hPosTgt : 0 < w.callerTgt.basicBlocks.length := by
    dsimp [InlineWitness.callerTgt]
    rw [list_append_length, list_append_length, w_callerBbsUpdated_length w]
    exact nat_lt_add_right _ (nat_lt_add_right _ (w_blockBase_pos w))
  exact ⟨list_isEmpty_false_of_pos hPosTgt, hSrc⟩

private theorem w_callerTgt_argLt {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt) :
    Nat.blt w.callerTgt.argumentCount w.callerTgt.locals.length = true ∧
    Nat.blt w.callerSrc.argumentCount w.callerSrc.locals.length = true := by
  have hSrc := nat_lt_blt w.hCallerArgLt
  have hTgt : w.callerTgt.argumentCount < w.callerTgt.locals.length := by
    dsimp [InlineWitness.callerTgt]
    rw [list_append_length]
    exact nat_lt_add_right _ w.hCallerArgLt
  exact ⟨nat_lt_blt hTgt, hSrc⟩

private theorem w_calleeCallAdmitted_callerTgt {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt) :
    calleeCallAdmitted w.callerTgt = calleeCallAdmitted w.callerSrc := by
  unfold calleeCallAdmitted
  let ⟨hE1, hE2⟩ := w_callerTgt_basicBlocks_nonEmpty w
  let ⟨hA1, hA2⟩ := w_callerTgt_argLt w
  have hStS := storageAnnotationsInBounds_of_bodyAllLocalsInBounds w.hCallerLocBounds
  have hStT := w_storageAnnotationsInBounds_callerTgt w
  rw [hE1, hE2, hA1, hA2, hStT, hStS, w_callerTgt_supported_tys w]

private theorem w_bodyStaticAdmitted_callerTgt {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt) :
    BodyStaticAdmitted pTgt w.callerTgt = BodyStaticAdmitted pSrc w.callerSrc := by
  have hPw : pTgt.pointerWidthBits = pSrc.pointerWidthBits := by
    rw [w.hPTgt]
  have hVer : pTgt.mirProfileVersion = pSrc.mirProfileVersion := by
    rw [w.hPTgt]
  unfold BodyStaticAdmitted
  let ⟨hE1, hE2⟩ := w_callerTgt_basicBlocks_nonEmpty w
  let ⟨hA1, hA2⟩ := w_callerTgt_argLt w
  have hStS := storageAnnotationsInBounds_of_bodyAllLocalsInBounds w.hCallerLocBounds
  have hStT := w_storageAnnotationsInBounds_callerTgt w
  have hSup := w_callerTgt_supported_tys w
  have hId : w.callerTgt.identity = w.callerSrc.identity := rfl
  rw [hPw, hVer, hId, hE1, hE2, hA1, hA2, hStT, hStS, hSup]

private theorem w_callerTgt_paramTys {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt) :
    (w.callerTgt.locals.drop 1).take w.callerTgt.argumentCount =
      (w.callerSrc.locals.drop 1).take w.callerSrc.argumentCount :=
  take_drop1_append_left w.callerSrc.locals w.calleeSrc.locals
    w.callerSrc.argumentCount w.hCallerArgLt

private theorem w_apply_entryProg {site : InlineSite} {pSrc pTgt : Program}
    (hApply : applyMirInlineCallSite site pSrc = some pTgt) (defId : DefId) :
    applyMirInlineCallSite site (entryProgForBody pSrc defId) =
      some (entryProgForBody pTgt defId) := by
  let ⟨w⟩ := extract_inlineWitness hApply
  have hEq : applyMirInlineCallSite site (entryProgForBody pSrc defId) =
      match applyMirInlineCallSite site pSrc with
      | some pOut => some (entryProgForBody pOut defId)
      | none => none := by
    unfold applyMirInlineCallSite entryProgForBody
    dsimp
    cases Nat.beq site.callerDefId site.calleeDefId with
    | true => rfl
    | false =>
      dsimp
      cases Trusted.MirSemantics.getElem? pSrc.bodies site.callerDefId with
      | none => rfl
      | some callerSrc =>
        cases Trusted.MirSemantics.getElem? pSrc.bodies site.calleeDefId with
        | none => rfl
        | some calleeSrc =>
          dsimp
          cases (!Nat.blt callerSrc.argumentCount callerSrc.locals.length ||
              !bodyAllLocalsInBounds callerSrc ||
              !bodyAllBlocksInBounds callerSrc ||
              !calleeCallAdmitted calleeSrc ||
              !bodyAllLocalsInBounds calleeSrc ||
              !bodyAllBlocksInBounds calleeSrc ||
              !bodyHasNoStorageDeadZero calleeSrc) with
          | true => rfl
          | false =>
            dsimp
            cases Trusted.MirSemantics.getElem? callerSrc.basicBlocks site.callBlock with
            | none => rfl
            | some callBb =>
              dsimp
              cases callBb.cleanup with
              | true => rfl
              | false =>
                dsimp
                cases callBb.terminator with
                | call f args dst target unwind =>
                  cases target with
                  | none => rfl
                  | some retBb =>
                    dsimp
                    cases (!Nat.beq f site.calleeDefId ||
                        !dst.projection.isEmpty ||
                        !Nat.blt dst.localId callerSrc.locals.length ||
                        !Nat.beq args.length calleeSrc.argumentCount) with
                    | true => rfl
                    | false =>
                      dsimp
                      cases Trusted.MirSemantics.getElem? callerSrc.locals dst.localId with
                      | none => rfl
                      | some dstTy =>
                        cases Trusted.MirSemantics.getElem? calleeSrc.locals 0 with
                        | none => rfl
                        | some calleeRetTy =>
                          dsimp
                          cases (!MirTy.beq calleeRetTy dstTy) with
                          | true => rfl
                          | false =>
                            dsimp
                            cases setElem? callerSrc.basicBlocks site.callBlock _ with
                            | none => rfl
                            | some callerBbsUpdated =>
                              dsimp
                              cases setElem? pSrc.bodies site.callerDefId _ with
                              | none => rfl
                              | some bodiesTgt => rfl
                | _ => rfl
  rw [hEq, hApply]

private theorem w_apply_unitProg {site : InlineSite} {pSrc pTgt : Program}
    (hApply : applyMirInlineCallSite site pSrc = some pTgt) (u : DefId) :
    applyMirInlineCallSite site (unitProgForDef pSrc u) =
      some (unitProgForDef pTgt u) := by
  have hEq : applyMirInlineCallSite site (unitProgForDef pSrc u) =
      match applyMirInlineCallSite site pSrc with
      | some pOut => some (unitProgForDef pOut u)
      | none => none := by
    unfold applyMirInlineCallSite unitProgForDef
    dsimp
    cases Nat.beq site.callerDefId site.calleeDefId with
    | true => rfl
    | false =>
      dsimp
      cases Trusted.MirSemantics.getElem? pSrc.bodies site.callerDefId with
      | none => rfl
      | some callerSrc =>
        cases Trusted.MirSemantics.getElem? pSrc.bodies site.calleeDefId with
        | none => rfl
        | some calleeSrc =>
          dsimp
          cases (!Nat.blt callerSrc.argumentCount callerSrc.locals.length ||
              !bodyAllLocalsInBounds callerSrc ||
              !bodyAllBlocksInBounds callerSrc ||
              !calleeCallAdmitted calleeSrc ||
              !bodyAllLocalsInBounds calleeSrc ||
              !bodyAllBlocksInBounds calleeSrc ||
              !bodyHasNoStorageDeadZero calleeSrc) with
          | true => rfl
          | false =>
            dsimp
            cases Trusted.MirSemantics.getElem? callerSrc.basicBlocks site.callBlock with
            | none => rfl
            | some callBb =>
              dsimp
              cases callBb.cleanup with
              | true => rfl
              | false =>
                dsimp
                cases callBb.terminator with
                | call f args dst target unwind =>
                  cases target with
                  | none => rfl
                  | some retBb =>
                    dsimp
                    cases (!Nat.beq f site.calleeDefId ||
                        !dst.projection.isEmpty ||
                        !Nat.blt dst.localId callerSrc.locals.length ||
                        !Nat.beq args.length calleeSrc.argumentCount) with
                    | true => rfl
                    | false =>
                      dsimp
                      cases Trusted.MirSemantics.getElem? callerSrc.locals dst.localId with
                      | none => rfl
                      | some dstTy =>
                        cases Trusted.MirSemantics.getElem? calleeSrc.locals 0 with
                        | none => rfl
                        | some calleeRetTy =>
                          dsimp
                          cases (!MirTy.beq calleeRetTy dstTy) with
                          | true => rfl
                          | false =>
                            dsimp
                            cases setElem? callerSrc.basicBlocks site.callBlock _ with
                            | none => rfl
                            | some callerBbsUpdated =>
                              dsimp
                              cases setElem? pSrc.bodies site.callerDefId _ with
                              | none => rfl
                              | some bodiesTgt => rfl
                | _ => rfl
  rw [hEq, hApply]

private theorem w_metadata {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt) :
    pTgt.pointerWidthBits = pSrc.pointerWidthBits ∧
    pTgt.mirProfileVersion = pSrc.mirProfileVersion ∧
    pTgt.entryDefId = pSrc.entryDefId ∧
    pTgt.scope = pSrc.scope ∧
    pTgt.bodies.length = pSrc.bodies.length ∧
    pTgt.bodies.map (fun b => b.identity) =
      pSrc.bodies.map (fun b => b.identity) := by
  have hLen : pTgt.bodies.length = pSrc.bodies.length := by
    rw [w.hPTgt]
    exact setElem?_length w.hSetBodies
  have hIds : pTgt.bodies.map (fun b => b.identity) =
      pSrc.bodies.map (fun b => b.identity) := by
    apply list_eq_of_getElem?_eq
    · rw [map_length_eq, map_length_eq, hLen]
    · intro i
      rw [getElem?_map, getElem?_map]
      cases hEq : Nat.beq i site.callerDefId with
      | false =>
        rw [w_bodies_getElem?_ne w (nat_ne_of_beq_false hEq)]
      | true =>
        have hI := nat_beq_eq hEq; subst hI
        rw [w_bodies_getElem?_caller w, w.hGetCallerSrc]
        rfl
  rw [w.hPTgt]
  exact ⟨rfl, rfl, rfl, rfl, by rw [← w.hPTgt]; exact hLen,
         by rw [← w.hPTgt]; exact hIds⟩

/-! ### Length Preservation, Switch Bounds, Prefix Locality, & Shift
Commutation -/

private theorem evalOperandToSlot_length {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot} {opnd : Operand} {ty : MirTy}
    {optVal : Option Val}
    (h : evalOperandToSlot bodyLocals locals opnd = .ok (ty, optVal, locals')) :
    locals'.length = locals.length := by
  cases opnd with
  | copy p =>
    dsimp [evalOperandToSlot] at h
    cases hPr : p.projection.isEmpty with
    | false => rw [hPr] at h; cases h
    | true =>
      rw [hPr] at h; dsimp at h
      cases hT : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [hT] at h; cases h
      | some _ =>
        rw [hT] at h
        cases hS : Trusted.MirSemantics.getElem? locals p.localId with
        | none => rw [hS] at h; cases h
        | some sl =>
          rw [hS] at h
          cases sl with
          | dead => cases h
          | live _ =>
            injection h with hEq; injection hEq with _ hEq2; injection hEq2 with _ hL
            rw [hL]
  | move p =>
    dsimp [evalOperandToSlot] at h
    cases hPr : p.projection.isEmpty with
    | false => rw [hPr] at h; cases h
    | true =>
      rw [hPr] at h; dsimp at h
      cases hT : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [hT] at h; cases h
      | some ty0 =>
        rw [hT] at h
        cases hS : Trusted.MirSemantics.getElem? locals p.localId with
        | none => rw [hS] at h; cases h
        | some sl =>
          rw [hS] at h
          cases sl with
          | dead => cases h
          | live _ =>
            dsimp at h
            cases hSet : setElem? locals p.localId (liveUninitSlot ty0) with
            | none => rw [hSet] at h; cases h
            | some locs' =>
              rw [hSet] at h; dsimp at h
              injection h with hEq; injection hEq with _ hEq2; injection hEq2 with _ hL
              subst hL
              exact setElem?_length hSet
  | constant c =>
    dsimp [evalOperandToSlot] at h
    cases hC : evalConstLit c.ty c.lit with
    | error _ => rw [hC] at h; cases h
    | ok _ =>
      rw [hC] at h; dsimp at h
      injection h with hEq; injection hEq with _ hEq2; injection hEq2 with _ hL
      rw [hL]

private theorem evalPrimitiveOperand_length {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot} {opnd : Operand} {v : Val}
    (h : evalPrimitiveOperand bodyLocals locals opnd = .ok (v, locals')) :
    locals'.length = locals.length := by
  unfold evalPrimitiveOperand at h
  cases hOp : evalOperandToSlot bodyLocals locals opnd with
  | error _ => rw [hOp] at h; cases h
  | ok triple =>
    rw [hOp] at h; dsimp at h
    cases triple with
    | mk ty rest =>
      cases rest with
      | mk optVal locs1 =>
        dsimp at h
        cases hPr : (!isPrimitiveReadableTy ty) with
        | true => rw [hPr] at h; cases h
        | false =>
          rw [hPr] at h; dsimp at h
          cases optVal with
          | none => cases h
          | some _ =>
            injection h with hEq; injection hEq with _ hL; subst hL
            exact evalOperandToSlot_length hOp

private theorem evalRvalue_length {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot} {dstTy : MirTy} {rv : Rvalue} {v : Val}
    (h : evalRvalue bodyLocals locals dstTy rv = .ok (v, locals')) :
    locals'.length = locals.length := by
  cases rv with
  | use opnd =>
    dsimp [evalRvalue] at h
    cases hOp : evalOperandToSlot bodyLocals locals opnd with
    | error _ => rw [hOp] at h; cases h
    | ok triple =>
      rw [hOp] at h; dsimp at h
      cases triple with
      | mk srcTy rest =>
        cases rest with
        | mk optVal locs1 =>
          dsimp at h
          cases hTy : (!MirTy.beq srcTy dstTy) with
          | true => rw [hTy] at h; cases h
          | false =>
            rw [hTy] at h; dsimp at h
            cases optVal with
            | none => cases h
            | some _ =>
              injection h with hEq; injection hEq with _ hL; subst hL
              exact evalOperandToSlot_length hOp
  | binaryOp op l r =>
    dsimp [evalRvalue] at h
    cases hL : evalPrimitiveOperand bodyLocals locals l with
    | error _ => rw [hL] at h; cases h
    | ok p1 =>
      rw [hL] at h; dsimp at h
      cases p1 with
      | mk lv locs1 =>
        dsimp at h
        cases hR : evalPrimitiveOperand bodyLocals locs1 r with
        | error _ => rw [hR] at h; cases h
        | ok p2 =>
          rw [hR] at h; dsimp at h
          cases p2 with
          | mk rv2 locs2 =>
            dsimp at h
            cases hB : evalBinOp op lv rv2 with
            | error _ => rw [hB] at h; cases h
            | ok _ =>
              rw [hB] at h; dsimp at h
              injection h with hEq; injection hEq with _ hLoc; subst hLoc
              exact (evalPrimitiveOperand_length hR).trans
                (evalPrimitiveOperand_length hL)
  | unaryOp op opnd =>
    dsimp [evalRvalue] at h
    cases hOp : evalPrimitiveOperand bodyLocals locals opnd with
    | error _ => rw [hOp] at h; cases h
    | ok p1 =>
      rw [hOp] at h; dsimp at h
      cases p1 with
      | mk uv locs1 =>
        dsimp at h
        cases hU : evalUnOp op uv with
        | error _ => rw [hU] at h; cases h
        | ok _ =>
          rw [hU] at h; dsimp at h
          injection h with hEq; injection hEq with _ hLoc; subst hLoc
          exact evalPrimitiveOperand_length hOp
  | discriminant p =>
    dsimp [evalRvalue] at h
    cases hPr : p.projection.isEmpty with
    | false => rw [hPr] at h; cases h
    | true =>
      rw [hPr] at h; dsimp at h
      cases hT : Trusted.MirSemantics.getElem? bodyLocals p.localId with
      | none => rw [hT] at h; cases h
      | some ty =>
        rw [hT] at h
        cases ty with
        | enum ety =>
          cases hS : Trusted.MirSemantics.getElem? locals p.localId with
          | none => rw [hS] at h; cases h
          | some slot =>
            rw [hS] at h; dsimp at h
            cases hAdm : (!enumAdmitted ety) with
            | true => rw [hAdm] at h; cases h
            | false =>
              rw [hAdm] at h; dsimp at h
              cases hTag : ety.tagRepr with
              | zeroSized =>
                rw [hTag] at h
                cases slot with
                | dead => cases h
                | live optV =>
                  cases optV with
                  | none =>
                    dsimp at h
                    cases hD : Trusted.MirSemantics.getElem? ety.discriminants 0 with
                    | none => rw [hD] at h; cases h
                    | some _ =>
                      rw [hD] at h; dsimp at h
                      injection h with hEq; injection hEq with _ hL; rw [hL]
                  | some val =>
                    cases val with
                    | enumVal ety' v' =>
                      dsimp at h
                      cases hC : (EnumTy.beq ety ety' && Nat.beq v' 0) with
                      | false => rw [hC] at h; cases h
                      | true =>
                        rw [hC] at h; dsimp at h
                        cases hD : Trusted.MirSemantics.getElem? ety.discriminants 0 with
                        | none => rw [hD] at h; cases h
                        | some _ =>
                          rw [hD] at h; dsimp at h
                          injection h with hEq; injection hEq with _ hL; rw [hL]
                    | _ => cases h
              | scalar _ _ =>
                rw [hTag] at h
                cases slot with
                | dead => cases h
                | live optV =>
                  cases optV with
                  | none => cases h
                  | some val =>
                    cases val with
                    | enumVal ety' v' =>
                      dsimp at h
                      cases hC : (EnumTy.beq ety ety' &&
                          Nat.blt v' ety.discriminants.length) with
                      | false => rw [hC] at h; cases h
                      | true =>
                        rw [hC] at h; dsimp at h
                        cases hD : Trusted.MirSemantics.getElem? ety.discriminants v' with
                        | none => rw [hD] at h; cases h
                        | some _ =>
                          rw [hD] at h; dsimp at h
                          injection h with hEq; injection hEq with _ hL; rw [hL]
                    | _ => cases h
        | _ => cases h
  | ref _ _ => cases h
  | addressOf _ _ => cases h
  | aggregateTuple _ => cases h
  | unsupported => cases h

private theorem writePlace_length {locals locals' : List LocalSlot}
    {dstLocalId : LocalId} {dstTy : MirTy} {val : Val}
    (h : writePlace locals dstLocalId dstTy val = .ok locals') :
    locals'.length = locals.length := by
  unfold writePlace at h
  cases hC : (!checkVal val dstTy) with
  | true => rw [hC] at h; cases h
  | false =>
    rw [hC] at h; dsimp at h
    cases hG : Trusted.MirSemantics.getElem? locals dstLocalId with
    | none => rw [hG] at h; cases h
    | some sl =>
      rw [hG] at h
      cases sl with
      | dead => cases h
      | live _ =>
        cases hSet : setElem? locals dstLocalId (.live (some val)) with
        | none => rw [hSet] at h; cases h
        | some locs' =>
          rw [hSet] at h; dsimp at h
          injection h with hEq; subst hEq
          exact setElem?_length hSet

private theorem evalCallArgs_length {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot} {args : List Operand}
    {paramTys : List MirTy} {vs : List Val}
    (h : evalCallArgs bodyLocals locals args paramTys = .ok (vs, locals')) :
    vs.length = args.length ∧ locals'.length = locals.length := by
  induction args generalizing paramTys locals vs locals' with
  | nil =>
    cases paramTys with
    | cons _ _ => cases h
    | nil =>
      dsimp [evalCallArgs] at h
      injection h with hEq; injection hEq with hV hL
      rw [← hV, ← hL]; exact ⟨rfl, rfl⟩
  | cons arg restArgs ih =>
    cases paramTys with
    | nil => cases h
    | cons paramTy restTys =>
      dsimp [evalCallArgs] at h
      cases hOp : evalOperandToSlot bodyLocals locals arg with
      | error _ => rw [hOp] at h; cases h
      | ok triple =>
        rw [hOp] at h; dsimp at h
        cases triple with
        | mk srcTy rest =>
          cases rest with
          | mk optVal locs1 =>
            dsimp at h
            cases hTy : (!MirTy.beq srcTy paramTy) with
            | true => rw [hTy] at h; cases h
            | false =>
              rw [hTy] at h; dsimp at h
              cases optVal with
              | none => cases h
              | some v =>
                dsimp at h
                cases hCv : (!checkVal v paramTy) with
                | true => rw [hCv] at h; cases h
                | false =>
                  rw [hCv] at h; dsimp at h
                  cases hRec : evalCallArgs bodyLocals locs1 restArgs restTys with
                  | error _ => rw [hRec] at h; cases h
                  | ok pair =>
                    rw [hRec] at h; dsimp at h
                    cases pair with
                    | mk vsRest locsFinal =>
                      dsimp at h
                      injection h with hEq; injection hEq with hV hL
                      subst hV; subst hL
                      let ⟨hLenV, hLenL⟩ := ih hRec
                      exact ⟨by dsimp [List.length]; rw [hLenV],
                        hLenL.trans (evalOperandToSlot_length hOp)⟩

private theorem evalSwitchBranches_lt {w : IntWidth} {discrBits : BitVec 128}
    {otherwise bound target : Nat} {branches : List (BitVec 128 × BasicBlockId)}
    (hOw : otherwise < bound)
    (hBrs : branches.all (fun br => Nat.blt br.2 bound) = true)
    (hRes : evalSwitchBranches w discrBits otherwise branches = .ok target) :
    target < bound := by
  induction branches with
  | nil =>
    dsimp [evalSwitchBranches] at hRes
    injection hRes with hEq; rw [← hEq]; exact hOw
  | cons br rest ih =>
    let ⟨hBr, hRest⟩ := bool_and_true hBrs
    dsimp [evalSwitchBranches] at hRes
    cases hOf : (truncateBits w br.1 != br.1) with
    | true => rw [hOf] at hRes; cases hRes
    | false =>
      rw [hOf] at hRes; dsimp at hRes
      cases hEq : (truncateBits w discrBits == truncateBits w br.1) with
      | true =>
        rw [hEq] at hRes; dsimp at hRes
        injection hRes with hT; rw [← hT]
        exact nat_blt_lt hBr
      | false =>
        rw [hEq] at hRes; dsimp at hRes
        exact ih hRest hRes

private theorem evalBoolSwitchBranches_lt {discr : Bool}
    {otherwise bound target : Nat} {branches : List (BitVec 128 × BasicBlockId)}
    (hOw : otherwise < bound)
    (hBrs : branches.all (fun br => Nat.blt br.2 bound) = true)
    (hRes : evalBoolSwitchBranches discr otherwise branches = .ok target) :
    target < bound := by
  induction branches with
  | nil =>
    dsimp [evalBoolSwitchBranches] at hRes
    injection hRes with hEq; rw [← hEq]; exact hOw
  | cons br rest ih =>
    let ⟨hBr, hRest⟩ := bool_and_true hBrs
    dsimp [evalBoolSwitchBranches] at hRes
    cases hC : evalConstLit .bool (.scalar br.1) with
    | error _ => rw [hC] at hRes; cases hRes
    | ok val =>
      rw [hC] at hRes
      cases val with
      | bool b =>
        cases b with
        | false =>
          dsimp at hRes
          cases hD : (!discr) with
          | true =>
            rw [hD] at hRes; dsimp at hRes
            injection hRes with hT; rw [← hT]; exact nat_blt_lt hBr
          | false =>
            rw [hD] at hRes; dsimp at hRes
            exact ih hRest hRes
        | true =>
          dsimp at hRes
          cases discr with
          | true =>
            dsimp at hRes
            injection hRes with hT; rw [← hT]; exact nat_blt_lt hBr
          | false =>
            dsimp at hRes
            exact ih hRest hRes
      | _ => cases hRes

private theorem evalSwitchBranches_shift (blockBase : Nat) (w : IntWidth)
    (discrBits : BitVec 128) (otherwise : BasicBlockId)
    (branches : List (BitVec 128 × BasicBlockId)) :
    evalSwitchBranches w discrBits (blockBase + otherwise)
      (branches.map (fun br => (br.1, blockBase + br.2))) =
      match evalSwitchBranches w discrBits otherwise branches with
      | .error k => .error k
      | .ok t => .ok (blockBase + t) := by
  induction branches with
  | nil => rfl
  | cons br rest ih =>
    dsimp [List.map, evalSwitchBranches]
    cases (truncateBits w br.1 != br.1) with
    | true => rfl
    | false =>
      dsimp
      cases (truncateBits w discrBits == truncateBits w br.1) with
      | true => rfl
      | false => exact ih

private theorem evalBoolSwitchBranches_shift (blockBase : Nat) (discr : Bool)
    (otherwise : BasicBlockId)
    (branches : List (BitVec 128 × BasicBlockId)) :
    evalBoolSwitchBranches discr (blockBase + otherwise)
      (branches.map (fun br => (br.1, blockBase + br.2))) =
      match evalBoolSwitchBranches discr otherwise branches with
      | .error k => .error k
      | .ok t => .ok (blockBase + t) := by
  induction branches with
  | nil => rfl
  | cons br rest ih =>
    dsimp [List.map, evalBoolSwitchBranches]
    cases evalConstLit .bool (.scalar br.1) with
    | error _ => rfl
    | ok val =>
      cases val with
      | bool b =>
        cases b with
        | false =>
          dsimp
          cases (!discr) with
          | true => rfl
          | false => exact ih
        | true =>
          dsimp
          cases discr with
          | true => rfl
          | false => exact ih
      | _ => rfl

/-! ### Prefix-Locality Commutation (`locals = callerLocs ++ suffix`) -/

private theorem evalOperandToSlot_append_left
    {bodyLocs extraTys : List MirTy} {locs suffix : List LocalSlot}
    {opnd : Operand}
    (hLen : locs.length = bodyLocs.length)
    (hLt : operandLocalsLt bodyLocs.length opnd = true) :
    evalOperandToSlot (bodyLocs ++ extraTys) (locs ++ suffix) opnd =
      match evalOperandToSlot bodyLocs locs opnd with
      | .error k => .error k
      | .ok (ty, optVal, locs') => .ok (ty, optVal, locs' ++ suffix) := by
  cases opnd with
  | copy p =>
    have hPLt : p.localId < bodyLocs.length := nat_blt_lt hLt
    have hPLtL : p.localId < locs.length := by rw [hLen]; exact hPLt
    dsimp [evalOperandToSlot]
    cases p.projection.isEmpty with
    | false => rfl
    | true =>
      dsimp
      rw [getElem?_append_left bodyLocs extraTys p.localId hPLt]
      rw [getElem?_append_left locs suffix p.localId hPLtL]
      cases Trusted.MirSemantics.getElem? bodyLocs p.localId with
      | none => rfl
      | some ty =>
        cases Trusted.MirSemantics.getElem? locs p.localId with
        | none => rfl
        | some sl => cases sl <;> rfl
  | move p =>
    have hPLt : p.localId < bodyLocs.length := nat_blt_lt hLt
    have hPLtL : p.localId < locs.length := by rw [hLen]; exact hPLt
    dsimp [evalOperandToSlot]
    cases p.projection.isEmpty with
    | false => rfl
    | true =>
      dsimp
      rw [getElem?_append_left bodyLocs extraTys p.localId hPLt]
      rw [getElem?_append_left locs suffix p.localId hPLtL]
      cases Trusted.MirSemantics.getElem? bodyLocs p.localId with
      | none => rfl
      | some ty =>
        cases Trusted.MirSemantics.getElem? locs p.localId with
        | none => rfl
        | some sl =>
          cases sl with
          | dead => rfl
          | live optVal =>
            dsimp
            rw [setElem?_append_left locs suffix p.localId (liveUninitSlot ty) hPLtL]
            cases setElem? locs p.localId (liveUninitSlot ty) <;> rfl
  | constant c =>
    dsimp [evalOperandToSlot]
    cases evalConstLit c.ty c.lit <;> rfl

private theorem evalPrimitiveOperand_append_left
    {bodyLocs extraTys : List MirTy} {locs suffix : List LocalSlot}
    {opnd : Operand}
    (hLen : locs.length = bodyLocs.length)
    (hLt : operandLocalsLt bodyLocs.length opnd = true) :
    evalPrimitiveOperand (bodyLocs ++ extraTys) (locs ++ suffix) opnd =
      match evalPrimitiveOperand bodyLocs locs opnd with
      | .error k => .error k
      | .ok (v, locs') => .ok (v, locs' ++ suffix) := by
  unfold evalPrimitiveOperand
  rw [evalOperandToSlot_append_left hLen hLt]
  cases evalOperandToSlot bodyLocs locs opnd with
  | error _ => rfl
  | ok triple =>
    cases triple with
    | mk ty rest =>
      cases rest with
      | mk optVal locs1 =>
        dsimp
        cases (!isPrimitiveReadableTy ty) with
        | true => rfl
        | false =>
          dsimp
          cases optVal <;> rfl

private theorem evalRvalue_append_left
    {bodyLocs extraTys : List MirTy} {locs suffix : List LocalSlot}
    {dstTy : MirTy} {rv : Rvalue}
    (hLen : locs.length = bodyLocs.length)
    (hLt : rvalueLocalsLt bodyLocs.length rv = true) :
    evalRvalue (bodyLocs ++ extraTys) (locs ++ suffix) dstTy rv =
      match evalRvalue bodyLocs locs dstTy rv with
      | .error k => .error k
      | .ok (v, locs') => .ok (v, locs' ++ suffix) := by
  cases rv with
  | use opnd =>
    dsimp [evalRvalue]
    rw [evalOperandToSlot_append_left hLen hLt]
    cases evalOperandToSlot bodyLocs locs opnd with
    | error _ => rfl
    | ok triple =>
      cases triple with
      | mk srcTy rest =>
        cases rest with
        | mk optVal locs1 =>
          dsimp
          cases (!MirTy.beq srcTy dstTy) with
          | true => rfl
          | false =>
            dsimp
            cases optVal <;> rfl
  | binaryOp op l r =>
    let ⟨hL, hR⟩ := bool_and_true hLt
    dsimp [evalRvalue]
    rw [evalPrimitiveOperand_append_left hLen hL]
    cases hEvL : evalPrimitiveOperand bodyLocs locs l with
    | error _ => rfl
    | ok p1 =>
      cases p1 with
      | mk lv locs1 =>
        dsimp
        have hLen1 : locs1.length = bodyLocs.length :=
          (evalPrimitiveOperand_length hEvL).trans hLen
        rw [evalPrimitiveOperand_append_left hLen1 hR]
        cases evalPrimitiveOperand bodyLocs locs1 r with
        | error _ => rfl
        | ok p2 =>
          cases p2 with
          | mk rv2 locs2 =>
            dsimp
            cases evalBinOp op lv rv2 <;> rfl
  | unaryOp op opnd =>
    dsimp [evalRvalue]
    rw [evalPrimitiveOperand_append_left hLen hLt]
    cases evalPrimitiveOperand bodyLocs locs opnd with
    | error _ => rfl
    | ok p1 =>
      cases p1 with
      | mk uv locs1 =>
        dsimp
        cases evalUnOp op uv <;> rfl
  | discriminant p =>
    have hPLt : p.localId < bodyLocs.length := nat_blt_lt hLt
    have hPLtL : p.localId < locs.length := by rw [hLen]; exact hPLt
    dsimp [evalRvalue]
    cases p.projection.isEmpty with
    | false => rfl
    | true =>
      dsimp
      rw [getElem?_append_left bodyLocs extraTys p.localId hPLt]
      rw [getElem?_append_left locs suffix p.localId hPLtL]
      cases Trusted.MirSemantics.getElem? bodyLocs p.localId with
      | none => rfl
      | some ty =>
        cases ty with
        | enum ety =>
          cases Trusted.MirSemantics.getElem? locs p.localId with
          | none => rfl
          | some sl =>
            dsimp
            cases (!enumAdmitted ety) with
            | true => rfl
            | false =>
              dsimp
              cases ety.tagRepr with
              | zeroSized =>
                cases sl with
                | dead => rfl
                | live optV =>
                  cases optV with
                  | none =>
                    dsimp
                    cases Trusted.MirSemantics.getElem? ety.discriminants 0 <;> rfl
                  | some val =>
                    cases val with
                    | enumVal ety' v' =>
                      dsimp
                      cases (EnumTy.beq ety ety' && Nat.beq v' 0) with
                      | false => rfl
                      | true =>
                        dsimp
                        cases Trusted.MirSemantics.getElem? ety.discriminants 0 <;> rfl
                    | _ => rfl
              | scalar _ _ =>
                cases sl with
                | dead => rfl
                | live optV =>
                  cases optV with
                  | none => rfl
                  | some val =>
                    cases val with
                    | enumVal ety' v' =>
                      dsimp
                      cases (EnumTy.beq ety ety' &&
                          Nat.blt v' ety.discriminants.length) with
                      | false => rfl
                      | true =>
                        dsimp
                        cases Trusted.MirSemantics.getElem? ety.discriminants v' <;> rfl
                    | _ => rfl
        | _ => rfl
  | ref _ _ => rfl
  | addressOf _ _ => rfl
  | aggregateTuple _ => rfl
  | unsupported => rfl

private theorem writePlace_append_left
    {locs suffix : List LocalSlot} {dstLocalId : LocalId} {dstTy : MirTy}
    {val : Val} (hLt : dstLocalId < locs.length) :
    writePlace (locs ++ suffix) dstLocalId dstTy val =
      match writePlace locs dstLocalId dstTy val with
      | .error k => .error k
      | .ok locs' => .ok (locs' ++ suffix) := by
  unfold writePlace
  cases (!checkVal val dstTy) with
  | true => rfl
  | false =>
    dsimp
    rw [getElem?_append_left locs suffix dstLocalId hLt]
    cases Trusted.MirSemantics.getElem? locs dstLocalId with
    | none => rfl
    | some sl =>
      cases sl with
      | dead => rfl
      | live _ =>
        dsimp
        rw [setElem?_append_left locs suffix dstLocalId (.live (some val)) hLt]
        cases setElem? locs dstLocalId (.live (some val)) <;> rfl

private theorem evalCallArgs_append_left
    {bodyLocs extraTys : List MirTy} {locs suffix : List LocalSlot}
    {args : List Operand} {paramTys : List MirTy}
    (hLen : locs.length = bodyLocs.length)
    (hArgsLt : args.all (operandLocalsLt bodyLocs.length) = true) :
    evalCallArgs (bodyLocs ++ extraTys) (locs ++ suffix) args paramTys =
      match evalCallArgs bodyLocs locs args paramTys with
      | .error k => .error k
      | .ok (vs, locs') => .ok (vs, locs' ++ suffix) := by
  induction args generalizing paramTys locs with
  | nil =>
    cases paramTys <;> rfl
  | cons arg restArgs ih =>
    cases paramTys with
    | nil => rfl
    | cons paramTy restTys =>
      let ⟨hArgLt, hRestLt⟩ := bool_and_true hArgsLt
      dsimp [evalCallArgs]
      rw [evalOperandToSlot_append_left hLen hArgLt]
      cases hOp : evalOperandToSlot bodyLocs locs arg with
      | error _ => rfl
      | ok triple =>
        cases triple with
        | mk srcTy rest =>
          cases rest with
          | mk optVal locs1 =>
            dsimp
            cases (!MirTy.beq srcTy paramTy) with
            | true => rfl
            | false =>
              dsimp
              cases optVal with
              | none => rfl
              | some v =>
                dsimp
                cases (!checkVal v paramTy) with
                | true => rfl
                | false =>
                  dsimp
                  have hLen1 : locs1.length = bodyLocs.length :=
                    (evalOperandToSlot_length hOp).trans hLen
                  rw [ih hLen1 hRestLt]
                  cases evalCallArgs bodyLocs locs1 restArgs restTys with
                  | error _ => rfl
                  | ok pair =>
                    cases pair with
                    | mk _ _ => rfl

/-! ### Shift-Right Commutation (`locals = outerLocs ++ calleeLocs`, shifted
by `localBase`) -/

private theorem evalOperandToSlot_shift_right
    {outerTys calleeTys : List MirTy} {outerLocs calleeLocs : List LocalSlot}
    {opnd : Operand} (hLen : outerLocs.length = outerTys.length) :
    evalOperandToSlot (outerTys ++ calleeTys) (outerLocs ++ calleeLocs)
      (shiftOperand outerTys.length opnd) =
      match evalOperandToSlot calleeTys calleeLocs opnd with
      | .error k => .error k
      | .ok (ty, optVal, calleeLocs') => .ok (ty, optVal, outerLocs ++ calleeLocs') := by
  cases opnd with
  | copy p =>
    dsimp [shiftOperand, shiftPlace, evalOperandToSlot]
    cases p.projection.isEmpty with
    | false => rfl
    | true =>
      dsimp
      rw [getElem?_append_right_add outerTys calleeTys p.localId]
      rw [← hLen, getElem?_append_right_add outerLocs calleeLocs p.localId]
      cases Trusted.MirSemantics.getElem? calleeTys p.localId with
      | none => rfl
      | some _ =>
        cases Trusted.MirSemantics.getElem? calleeLocs p.localId with
        | none => rfl
        | some sl => cases sl <;> rfl
  | move p =>
    dsimp [shiftOperand, shiftPlace, evalOperandToSlot]
    cases p.projection.isEmpty with
    | false => rfl
    | true =>
      dsimp
      rw [getElem?_append_right_add outerTys calleeTys p.localId]
      rw [← hLen, getElem?_append_right_add outerLocs calleeLocs p.localId]
      cases Trusted.MirSemantics.getElem? calleeTys p.localId with
      | none => rfl
      | some ty =>
        cases Trusted.MirSemantics.getElem? calleeLocs p.localId with
        | none => rfl
        | some sl =>
          cases sl with
          | dead => rfl
          | live _ =>
            dsimp
            rw [setElem?_append_right_add outerLocs calleeLocs p.localId (liveUninitSlot ty)]
            cases setElem? calleeLocs p.localId (liveUninitSlot ty) <;> rfl
  | constant c =>
    dsimp [shiftOperand, evalOperandToSlot]
    cases evalConstLit c.ty c.lit <;> rfl

private theorem evalPrimitiveOperand_shift_right
    {outerTys calleeTys : List MirTy} {outerLocs calleeLocs : List LocalSlot}
    {opnd : Operand} (hLen : outerLocs.length = outerTys.length) :
    evalPrimitiveOperand (outerTys ++ calleeTys) (outerLocs ++ calleeLocs)
      (shiftOperand outerTys.length opnd) =
      match evalPrimitiveOperand calleeTys calleeLocs opnd with
      | .error k => .error k
      | .ok (v, calleeLocs') => .ok (v, outerLocs ++ calleeLocs') := by
  unfold evalPrimitiveOperand
  rw [evalOperandToSlot_shift_right hLen]
  cases evalOperandToSlot calleeTys calleeLocs opnd with
  | error _ => rfl
  | ok triple =>
    cases triple with
    | mk ty rest =>
      cases rest with
      | mk optVal locs1 =>
        dsimp
        cases (!isPrimitiveReadableTy ty) with
        | true => rfl
        | false =>
          dsimp
          cases optVal <;> rfl

private theorem evalRvalue_shift_right
    {outerTys calleeTys : List MirTy} {outerLocs calleeLocs : List LocalSlot}
    {dstTy : MirTy} {rv : Rvalue} (hLen : outerLocs.length = outerTys.length) :
    evalRvalue (outerTys ++ calleeTys) (outerLocs ++ calleeLocs) dstTy
      (shiftRvalue outerTys.length rv) =
      match evalRvalue calleeTys calleeLocs dstTy rv with
      | .error k => .error k
      | .ok (v, calleeLocs') => .ok (v, outerLocs ++ calleeLocs') := by
  cases rv with
  | use opnd =>
    dsimp [shiftRvalue, evalRvalue]
    rw [evalOperandToSlot_shift_right hLen]
    cases evalOperandToSlot calleeTys calleeLocs opnd with
    | error _ => rfl
    | ok triple =>
      cases triple with
      | mk srcTy rest =>
        cases rest with
        | mk optVal locs1 =>
          dsimp
          cases (!MirTy.beq srcTy dstTy) with
          | true => rfl
          | false =>
            dsimp
            cases optVal <;> rfl
  | binaryOp op l r =>
    dsimp [shiftRvalue, evalRvalue]
    rw [evalPrimitiveOperand_shift_right hLen]
    cases evalPrimitiveOperand calleeTys calleeLocs l with
    | error _ => rfl
    | ok p1 =>
      cases p1 with
      | mk lv locs1 =>
        dsimp
        rw [evalPrimitiveOperand_shift_right hLen]
        cases evalPrimitiveOperand calleeTys locs1 r with
        | error _ => rfl
        | ok p2 =>
          cases p2 with
          | mk rv2 locs2 =>
            dsimp
            cases evalBinOp op lv rv2 <;> rfl
  | unaryOp op opnd =>
    dsimp [shiftRvalue, evalRvalue]
    rw [evalPrimitiveOperand_shift_right hLen]
    cases evalPrimitiveOperand calleeTys calleeLocs opnd with
    | error _ => rfl
    | ok p1 =>
      cases p1 with
      | mk uv locs1 =>
        dsimp
        cases evalUnOp op uv <;> rfl
  | discriminant p =>
    dsimp [shiftRvalue, shiftPlace, evalRvalue]
    cases p.projection.isEmpty with
    | false => rfl
    | true =>
      dsimp
      rw [getElem?_append_right_add outerTys calleeTys p.localId]
      rw [← hLen, getElem?_append_right_add outerLocs calleeLocs p.localId]
      cases Trusted.MirSemantics.getElem? calleeTys p.localId with
      | none => rfl
      | some ty =>
        cases ty with
        | enum ety =>
          cases Trusted.MirSemantics.getElem? calleeLocs p.localId with
          | none => rfl
          | some sl =>
            dsimp
            cases (!enumAdmitted ety) with
            | true => rfl
            | false =>
              dsimp
              cases ety.tagRepr with
              | zeroSized =>
                cases sl with
                | dead => rfl
                | live optV =>
                  cases optV with
                  | none =>
                    dsimp
                    cases Trusted.MirSemantics.getElem? ety.discriminants 0 <;> rfl
                  | some val =>
                    cases val with
                    | enumVal ety' v' =>
                      dsimp
                      cases (EnumTy.beq ety ety' && Nat.beq v' 0) with
                      | false => rfl
                      | true =>
                        dsimp
                        cases Trusted.MirSemantics.getElem? ety.discriminants 0 <;> rfl
                    | _ => rfl
              | scalar _ _ =>
                cases sl with
                | dead => rfl
                | live optV =>
                  cases optV with
                  | none => rfl
                  | some val =>
                    cases val with
                    | enumVal ety' v' =>
                      dsimp
                      cases (EnumTy.beq ety ety' &&
                          Nat.blt v' ety.discriminants.length) with
                      | false => rfl
                      | true =>
                        dsimp
                        cases Trusted.MirSemantics.getElem? ety.discriminants v' <;> rfl
                    | _ => rfl
        | _ => rfl
  | ref _ _ => rfl
  | addressOf _ _ => rfl
  | aggregateTuple _ => rfl
  | unsupported => rfl

private theorem writePlace_shift_right
    {outerLocs calleeLocs : List LocalSlot} {dstLocalId : LocalId}
    {dstTy : MirTy} {val : Val} :
    writePlace (outerLocs ++ calleeLocs) (outerLocs.length + dstLocalId) dstTy val =
      match writePlace calleeLocs dstLocalId dstTy val with
      | .error k => .error k
      | .ok calleeLocs' => .ok (outerLocs ++ calleeLocs') := by
  unfold writePlace
  cases (!checkVal val dstTy) with
  | true => rfl
  | false =>
    dsimp
    rw [getElem?_append_right_add outerLocs calleeLocs dstLocalId]
    cases Trusted.MirSemantics.getElem? calleeLocs dstLocalId with
    | none => rfl
    | some sl =>
      cases sl with
      | dead => rfl
      | live _ =>
        dsimp
        rw [setElem?_append_right_add outerLocs calleeLocs dstLocalId (.live (some val))]
        cases setElem? calleeLocs dstLocalId (.live (some val)) <;> rfl

private theorem evalCallArgs_shift_right
    {outerTys calleeTys : List MirTy} {outerLocs calleeLocs : List LocalSlot}
    {args : List Operand} {paramTys : List MirTy}
    (hLen : outerLocs.length = outerTys.length) :
    evalCallArgs (outerTys ++ calleeTys) (outerLocs ++ calleeLocs)
      (args.map (shiftOperand outerTys.length)) paramTys =
      match evalCallArgs calleeTys calleeLocs args paramTys with
      | .error k => .error k
      | .ok (vs, calleeLocs') => .ok (vs, outerLocs ++ calleeLocs') := by
  induction args generalizing paramTys calleeLocs with
  | nil =>
    cases paramTys <;> rfl
  | cons arg restArgs ih =>
    cases paramTys with
    | nil => rfl
    | cons paramTy restTys =>
      dsimp [List.map, evalCallArgs]
      rw [evalOperandToSlot_shift_right hLen]
      cases evalOperandToSlot calleeTys calleeLocs arg with
      | error _ => rfl
      | ok triple =>
        cases triple with
        | mk srcTy rest =>
          cases rest with
          | mk optVal locs1 =>
            dsimp
            cases (!MirTy.beq srcTy paramTy) with
            | true => rfl
            | false =>
              dsimp
              cases optVal with
              | none => rfl
              | some v =>
                dsimp
                cases (!checkVal v paramTy) with
                | true => rfl
                | false =>
                  dsimp
                  rw [ih]
                  cases evalCallArgs calleeTys locs1 restArgs restTys with
                  | error _ => rfl
                  | ok pair =>
                    cases pair with
                    | mk _ _ => rfl

/-! ### Stage 4 Private Helpers — Slice C2: Prologue/Epilogue Execution,
`SimState`, & Theorem 2 -/

private theorem drop_eq_nil_le {α : Type} {xs : List α} {n : Nat}
    (h : xs.drop n = []) : xs.length ≤ n := by
  have hLen : (xs.drop n).length = 0 := by rw [h]; rfl
  rw [drop_length_eq] at hLen
  exact Nat.le_of_sub_eq_zero hLen

private theorem getElem?_of_drop_eq_cons {α : Type} {xs rest : List α} {n : Nat} {x : α}
    (h : xs.drop n = x :: rest) :
    Trusted.MirSemantics.getElem? xs n = some x ∧ xs.drop (n + 1) = rest := by
  induction xs generalizing n with
  | nil => cases n <;> cases h
  | cons a xs ih =>
    cases n with
    | zero =>
      injection h with h1 h2
      subst h1; subst h2
      exact ⟨rfl, rfl⟩
    | succ _ => exact ih h

private theorem liveUninitSlot_is_live (ty : MirTy) :
    ∃ optVal, liveUninitSlot ty = .live optVal := by
  cases ty with
  | unit => exact ⟨some .unit, rfl⟩
  | enum ety =>
    dsimp [liveUninitSlot]
    cases isZstEnumTy ety with
    | true => exact ⟨some (.enumVal ety 0), rfl⟩
    | false => exact ⟨none, rfl⟩
  | bool => exact ⟨none, rfl⟩
  | int _ _ => exact ⟨none, rfl⟩
  | never => exact ⟨none, rfl⟩
  | tuple _ => exact ⟨none, rfl⟩
  | ref _ _ => exact ⟨none, rfl⟩
  | rawPtr _ _ => exact ⟨none, rfl⟩
  | unsupported => exact ⟨none, rfl⟩

private theorem mkArgAssignStmts_length (localBase start : Nat) (args : List Operand) :
    (mkArgAssignStmts localBase start args).length = args.length := by
  induction args generalizing start with
  | nil => rfl
  | cons _ rest ih =>
    dsimp [mkArgAssignStmts, List.length]
    rw [ih (start + 1)]

private theorem take_drop_length_eq {α : Type} (xs : List α) (n : Nat)
    (h : n < xs.length) : ((xs.drop 1).take n).length = n := by
  have hLe : n ≤ (xs.drop 1).length := by
    rw [drop_length_eq]
    cases xs with
    | nil => exact False.elim (Nat.not_lt_zero n h)
    | cons _ rest =>
      dsimp [List.length] at h
      dsimp [List.length]
      exact Nat.le_of_lt_succ h
  have hAux : ∀ (ys : List α) (m : Nat), m ≤ ys.length → (ys.take m).length = m := by
    intro ys
    induction ys with
    | nil =>
      intro m hm
      cases m with
      | zero => rfl
      | succ k => exact False.elim (Nat.not_succ_le_zero k hm)
    | cons _ _ ihr =>
      intro m hm
      cases m with
      | zero => rfl
      | succ k =>
        dsimp [List.take, List.length]
        rw [ihr k (Nat.le_of_succ_le_succ hm)]
  exact hAux (xs.drop 1) n hLe

/-! #### Prologue `StorageLive` Multi-Step Execution -/

private noncomputable def prologueSlotOf (callee : Body) (idx : Nat) (ty : MirTy) :
    LocalSlot :=
  if Nat.beq idx 0 || Nat.ble idx callee.argumentCount ||
      !hasStorageAnnotation callee idx then
    liveUninitSlot ty
  else
    .dead

private theorem exec_prologue_aux {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt)
    (callerLocs : List LocalSlot) (hCLen : callerLocs.length = w.localBase)
    (stackT : List CallContinuation) (mem : CallerMemory)
    (tys : List MirTy) (start baseStmt : Nat) (calleeSlots : List LocalSlot)
    (hDrop : w.calleeSrc.locals.drop start = tys)
    (hStmts : ∀ k stmt,
      Trusted.MirSemantics.getElem?
        (mkPrologueStorageLives w.calleeSrc w.localBase start tys) k = some stmt →
      Trusted.MirSemantics.getElem? w.callBbTgt.statements (baseStmt + k) = some stmt)
    (hELen : calleeSlots.length = w.calleeSrc.locals.length)
    (hPref : ∀ j ty, j < start →
      Trusted.MirSemantics.getElem? w.calleeSrc.locals j = some ty →
      Trusted.MirSemantics.getElem? calleeSlots j =
        some (prologueSlotOf w.calleeSrc j ty))
    (hSuff : ∀ j, start ≤ j → j < w.calleeSrc.locals.length →
      Trusted.MirSemantics.getElem? calleeSlots j = some .dead) :
    ∃ calleeSlotsEnd,
      calleeSlotsEnd.length = w.calleeSrc.locals.length ∧
      (∀ j ty, Trusted.MirSemantics.getElem? w.calleeSrc.locals j = some ty →
        Trusted.MirSemantics.getElem? calleeSlotsEnd j =
          some (prologueSlotOf w.calleeSrc j ty)) ∧
      StepsN pTgt (mkPrologueStorageLives w.calleeSrc w.localBase start tys).length
        { cur := { defId := site.callerDefId, blockIdx := site.callBlock,
                   stmtIdx := baseStmt, locals := callerLocs ++ calleeSlots }
          stack := stackT, callerMem := mem }
        { cur := { defId := site.callerDefId, blockIdx := site.callBlock,
                   stmtIdx := baseStmt +
                     (mkPrologueStorageLives w.calleeSrc w.localBase start tys).length
                   locals := callerLocs ++ calleeSlotsEnd }
          stack := stackT, callerMem := mem } := by
  induction tys generalizing start baseStmt calleeSlots with
  | nil =>
    have hGe : w.calleeSrc.locals.length ≤ start := drop_eq_nil_le hDrop
    refine ⟨calleeSlots, hELen, fun j ty hTy => ?_, ?_⟩
    · exact hPref j ty (Nat.lt_of_lt_of_le (getElem?_some_lt hTy) hGe) hTy
    · dsimp [mkPrologueStorageLives, List.length]
      exact StepsN.zero _
  | cons ty rest ih =>
    let ⟨hTyStart, hDropNext⟩ := getElem?_of_drop_eq_cons hDrop
    have hStartLt : start < w.calleeSrc.locals.length := getElem?_some_lt hTyStart
    dsimp [mkPrologueStorageLives] at hStmts
    dsimp [mkPrologueStorageLives]
    cases hCond : (Nat.beq start 0 || Nat.ble start w.calleeSrc.argumentCount ||
        !hasStorageAnnotation w.calleeSrc start) with
    | false =>
      rw [hCond] at hStmts
      dsimp at hStmts
      dsimp
      have hPrefNext : ∀ j ty', j < start + 1 →
          Trusted.MirSemantics.getElem? w.calleeSrc.locals j = some ty' →
          Trusted.MirSemantics.getElem? calleeSlots j =
            some (prologueSlotOf w.calleeSrc j ty') := by
        intro j ty' hJLt hJTy
        cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hJLt) with
        | inl hLt => exact hPref j ty' hLt hJTy
        | inr hEq =>
          subst hEq
          rw [hTyStart] at hJTy; injection hJTy with hTyEq; subst hTyEq
          rw [hSuff j (Nat.le_refl j) hStartLt]
          unfold prologueSlotOf
          rw [hCond]
          rfl
      have hSuffNext : ∀ j, start + 1 ≤ j → j < w.calleeSrc.locals.length →
          Trusted.MirSemantics.getElem? calleeSlots j = some .dead :=
        fun j hGe hLt => hSuff j (Nat.le_of_succ_le hGe) hLt
      exact ih (start + 1) baseStmt calleeSlots hDropNext hStmts hELen hPrefNext hSuffNext
    | true =>
      rw [hCond] at hStmts
      dsimp at hStmts
      dsimp
      have hStmt0 : Trusted.MirSemantics.getElem? w.callBbTgt.statements baseStmt =
          some (.storageLive (w.localBase + start)) := by
        have h0 := hStmts 0 (.storageLive (w.localBase + start)) rfl
        rw [Nat.add_zero] at h0
        exact h0
      have hStartLtSlots : start < calleeSlots.length := by rw [hELen]; exact hStartLt
      let ⟨calleeSlots', hSetCallee⟩ :=
        setElem?_some_of_lt calleeSlots start (liveUninitSlot ty) hStartLtSlots
      have hSetFull : setElem? (callerLocs ++ calleeSlots) (w.localBase + start)
          (liveUninitSlot ty) = some (callerLocs ++ calleeSlots') := by
        rw [← hCLen, setElem?_append_right_add callerLocs calleeSlots start (liveUninitSlot ty)]
        rw [hSetCallee]; rfl
      have hGetTy : Trusted.MirSemantics.getElem? w.callerTgt.locals (w.localBase + start) =
          some ty := by
        have hLocEq : w.callerTgt.locals = w.callerSrc.locals ++ w.calleeSrc.locals := rfl
        rw [hLocEq]
        change Trusted.MirSemantics.getElem? (w.callerSrc.locals ++ w.calleeSrc.locals)
          (w.callerSrc.locals.length + start) = some ty
        rw [getElem?_append_right_add]
        exact hTyStart
      have hStep1 : evalStepInterproc pTgt 0
          { cur := { defId := site.callerDefId, blockIdx := site.callBlock,
                     stmtIdx := baseStmt, locals := callerLocs ++ calleeSlots }
            stack := stackT, callerMem := mem } =
          .step { cur := { defId := site.callerDefId, blockIdx := site.callBlock,
                           stmtIdx := baseStmt + 1, locals := callerLocs ++ calleeSlots' }
                  stack := stackT, callerMem := mem } := by
        unfold evalStepInterproc
        dsimp
        rw [w_bodies_getElem?_caller w]
        dsimp
        rw [w_callerTgt_blocks_getElem?_callBlock w]
        dsimp
        rw [hStmt0]
        dsimp [evalStatement, liftSingleFrameStep]
        rw [hGetTy]
        dsimp
        rw [hSetFull]
      have hELen' : calleeSlots'.length = w.calleeSrc.locals.length :=
        (setElem?_length hSetCallee).trans hELen
      have hStmtsNext : ∀ k stmt,
          Trusted.MirSemantics.getElem?
            (mkPrologueStorageLives w.calleeSrc w.localBase (start + 1) rest) k = some stmt →
          Trusted.MirSemantics.getElem? w.callBbTgt.statements ((baseStmt + 1) + k) = some stmt := by
        intro k stmt hK
        have hAdd : (baseStmt + 1) + k = baseStmt + (k + 1) := by
          rw [Nat.add_assoc, Nat.add_comm 1 k]
        rw [hAdd]
        exact hStmts (k + 1) stmt hK
      have hPrefNext : ∀ j ty', j < start + 1 →
          Trusted.MirSemantics.getElem? w.calleeSrc.locals j = some ty' →
          Trusted.MirSemantics.getElem? calleeSlots' j =
            some (prologueSlotOf w.calleeSrc j ty') := by
        intro j ty' hJLt hJTy
        cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hJLt) with
        | inl hLt =>
          rw [setElem?_getElem?_ne hSetCallee (Nat.ne_of_lt hLt)]
          exact hPref j ty' hLt hJTy
        | inr hEq =>
          subst hEq
          rw [hTyStart] at hJTy; injection hJTy with hTyEq; subst hTyEq
          rw [setElem?_getElem?_same hSetCallee]
          unfold prologueSlotOf
          rw [hCond]
          rfl
      have hSuffNext : ∀ j, start + 1 ≤ j → j < w.calleeSrc.locals.length →
          Trusted.MirSemantics.getElem? calleeSlots' j = some .dead := by
        intro j hGe hLt
        have hNe : j ≠ start := Nat.ne_of_gt (Nat.lt_of_succ_le hGe)
        rw [setElem?_getElem?_ne hSetCallee hNe]
        exact hSuff j (Nat.le_of_succ_le hGe) hLt
      let ⟨calleeSlotsEnd, hEndLen, hEndAt, hRestSteps⟩ :=
        ih (start + 1) (baseStmt + 1) calleeSlots' hDropNext hStmtsNext hELen' hPrefNext hSuffNext
      refine ⟨calleeSlotsEnd, hEndLen, hEndAt, ?_⟩
      have hAddStmt : baseStmt + ((mkPrologueStorageLives w.calleeSrc w.localBase (start + 1) rest).length + 1) =
          (baseStmt + 1) + (mkPrologueStorageLives w.calleeSrc w.localBase (start + 1) rest).length := by
        rw [Nat.add_assoc, Nat.add_comm 1]
      rw [hAddStmt]
      exact StepsN.succ hStep1 hRestSteps

/-! #### Argument-Binding Assignments Multi-Step Execution -/

private theorem exec_argAssign_aux {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt)
    (stackT : List CallContinuation) (mem : CallerMemory)
    (remArgs : List Operand) (remParamTys : List MirTy)
    (start baseStmt : Nat)
    (callerLocs calleeSlots : List LocalSlot)
    (hLenEq : remArgs.length = remParamTys.length)
    (hBound : start + remArgs.length ≤ w.calleeSrc.argumentCount)
    (hArgsLt : remArgs.all (operandLocalsLt w.localBase) = true)
    (hParamTys : ∀ k ty, Trusted.MirSemantics.getElem? remParamTys k = some ty →
      Trusted.MirSemantics.getElem? w.calleeSrc.locals (1 + start + k) = some ty)
    (hStmts : ∀ k stmt,
      Trusted.MirSemantics.getElem? (mkArgAssignStmts w.localBase start remArgs) k = some stmt →
      Trusted.MirSemantics.getElem? w.callBbTgt.statements (baseStmt + k) = some stmt)
    (hCLen : callerLocs.length = w.localBase)
    (hELen : calleeSlots.length = w.calleeSrc.locals.length)
    (hLive : ∀ k, k < remArgs.length →
      ∃ optV, Trusted.MirSemantics.getElem? calleeSlots (1 + start + k) = some (.live optV)) :
    (∀ fk, evalCallArgs w.callerSrc.locals callerLocs remArgs remParamTys = .error fk →
      ∃ d tEnd,
        StepsN pTgt d
          { cur := { defId := site.callerDefId, blockIdx := site.callBlock,
                     stmtIdx := baseStmt, locals := callerLocs ++ calleeSlots }
            stack := stackT, callerMem := mem }
          tEnd ∧
        evalStepInterproc pTgt 0 tEnd = .fault fk) ∧
    (∀ vs callerLocsFinal,
      evalCallArgs w.callerSrc.locals callerLocs remArgs remParamTys = .ok (vs, callerLocsFinal) →
      ∃ calleeSlotsFinal,
        calleeSlotsFinal.length = w.calleeSrc.locals.length ∧
        (∀ j, j < 1 + start →
          Trusted.MirSemantics.getElem? calleeSlotsFinal j =
            Trusted.MirSemantics.getElem? calleeSlots j) ∧
        (∀ j, 1 + start + remArgs.length ≤ j →
          Trusted.MirSemantics.getElem? calleeSlotsFinal j =
            Trusted.MirSemantics.getElem? calleeSlots j) ∧
        (∀ k v, Trusted.MirSemantics.getElem? vs k = some v →
          Trusted.MirSemantics.getElem? calleeSlotsFinal (1 + start + k) =
            some (.live (some v))) ∧
        StepsN pTgt remArgs.length
          { cur := { defId := site.callerDefId, blockIdx := site.callBlock,
                     stmtIdx := baseStmt, locals := callerLocs ++ calleeSlots }
            stack := stackT, callerMem := mem }
          { cur := { defId := site.callerDefId, blockIdx := site.callBlock,
                     stmtIdx := baseStmt + remArgs.length,
                     locals := callerLocsFinal ++ calleeSlotsFinal }
            stack := stackT, callerMem := mem }) := by
  induction remArgs generalizing remParamTys start baseStmt callerLocs calleeSlots with
  | nil =>
    cases remParamTys with
    | cons _ _ => cases hLenEq
    | nil =>
      constructor
      · intro fk hErr; cases hErr
      · intro vs callerLocsFinal hOk
        dsimp [evalCallArgs] at hOk
        injection hOk with hPair; injection hPair with hV hL
        subst hV; subst hL
        refine ⟨calleeSlots, hELen, fun _ _ => rfl, fun _ _ => rfl,
          fun _ _ hG => (by cases hG), ?_⟩
        dsimp [List.length]
        exact StepsN.zero _
  | cons arg restArgs ih =>
    cases remParamTys with
    | nil => cases hLenEq
    | cons paramTy restTys =>
      have hRestLenEq : restArgs.length = restTys.length := Nat.succ.inj hLenEq
      let ⟨hArgLt, hRestArgsLt⟩ := bool_and_true hArgsLt
      have hParamTy0 : Trusted.MirSemantics.getElem? w.calleeSrc.locals (1 + start) = some paramTy := by
        have h0 := hParamTys 0 paramTy rfl
        rw [Nat.add_zero] at h0
        exact h0
      have hDstIdxEq : w.localBase + 1 + start = w.localBase + (1 + start) :=
        Nat.add_assoc w.localBase 1 start
      have hGetDstTy : Trusted.MirSemantics.getElem? w.callerTgt.locals (w.localBase + 1 + start) =
          some paramTy := by
        rw [hDstIdxEq]
        have hLocEq : w.callerTgt.locals = w.callerSrc.locals ++ w.calleeSrc.locals := rfl
        rw [hLocEq]
        change Trusted.MirSemantics.getElem? (w.callerSrc.locals ++ w.calleeSrc.locals)
          (w.callerSrc.locals.length + (1 + start)) = some paramTy
        rw [getElem?_append_right_add]
        exact hParamTy0
      have hStmt0 : Trusted.MirSemantics.getElem? w.callBbTgt.statements baseStmt =
          some (.assign ⟨w.localBase + 1 + start, []⟩ (.use arg)) := by
        have h0 := hStmts 0 (.assign ⟨w.localBase + 1 + start, []⟩ (.use arg)) rfl
        rw [Nat.add_zero] at h0
        exact h0
      have hEvalOpEq : evalOperandToSlot w.callerTgt.locals (callerLocs ++ calleeSlots) arg =
          match evalOperandToSlot w.callerSrc.locals callerLocs arg with
          | .error k => .error k
          | .ok (ty, optVal, locs') => .ok (ty, optVal, locs' ++ calleeSlots) :=
        evalOperandToSlot_append_left hCLen hArgLt
      have hStartSlotLt : 1 + start < calleeSlots.length := by
        rw [hELen]
        exact getElem?_some_lt hParamTy0
      have hLive0 : ∃ optV, Trusted.MirSemantics.getElem? calleeSlots (1 + start) = some (.live optV) := by
        have h0 := hLive 0 (Nat.zero_lt_succ restArgs.length)
        rw [Nat.add_zero] at h0
        exact h0
      cases hOp : evalOperandToSlot w.callerSrc.locals callerLocs arg with
      | error fk0 =>
        have hStepFault : evalStepInterproc pTgt 0
            { cur := { defId := site.callerDefId, blockIdx := site.callBlock,
                       stmtIdx := baseStmt, locals := callerLocs ++ calleeSlots }
              stack := stackT, callerMem := mem } = .fault fk0 := by
          unfold evalStepInterproc; dsimp
          rw [w_bodies_getElem?_caller w]; dsimp
          rw [w_callerTgt_blocks_getElem?_callBlock w]; dsimp
          rw [hStmt0]; dsimp [evalStatement, liftSingleFrameStep]
          rw [hGetDstTy]; dsimp [evalRvalue]
          rw [hEvalOpEq, hOp]
        constructor
        · intro fk hErr
          dsimp [evalCallArgs] at hErr; rw [hOp] at hErr
          injection hErr with hFk; subst hFk
          exact ⟨0, _, StepsN.zero _, hStepFault⟩
        · intro vs callerLocsFinal hOk
          dsimp [evalCallArgs] at hOk; rw [hOp] at hOk; cases hOk
      | ok triple =>
        cases triple with
        | mk srcTy rest =>
          cases rest with
          | mk optVal locs1 =>
            have hCLen1 : locs1.length = w.localBase :=
              (evalOperandToSlot_length hOp).trans hCLen
            cases hTyBad : (!MirTy.beq srcTy paramTy) with
            | true =>
              have hStepFault : evalStepInterproc pTgt 0
                  { cur := { defId := site.callerDefId, blockIdx := site.callBlock,
                             stmtIdx := baseStmt, locals := callerLocs ++ calleeSlots }
                    stack := stackT, callerMem := mem } = .fault .unsupported := by
                unfold evalStepInterproc; dsimp
                rw [w_bodies_getElem?_caller w]; dsimp
                rw [w_callerTgt_blocks_getElem?_callBlock w]; dsimp
                rw [hStmt0]; dsimp [evalStatement, liftSingleFrameStep]
                rw [hGetDstTy]; dsimp [evalRvalue]
                rw [hEvalOpEq, hOp]; dsimp; rw [hTyBad]; rfl
              constructor
              · intro fk hErr
                dsimp [evalCallArgs] at hErr; rw [hOp] at hErr; dsimp at hErr
                rw [hTyBad] at hErr; injection hErr with hFk; subst hFk
                exact ⟨0, _, StepsN.zero _, hStepFault⟩
              · intro vs callerLocsFinal hOk
                dsimp [evalCallArgs] at hOk; rw [hOp] at hOk; dsimp at hOk
                rw [hTyBad] at hOk; cases hOk
            | false =>
              cases optVal with
              | none =>
                have hStepFault : evalStepInterproc pTgt 0
                    { cur := { defId := site.callerDefId, blockIdx := site.callBlock,
                               stmtIdx := baseStmt, locals := callerLocs ++ calleeSlots }
                      stack := stackT, callerMem := mem } = .fault .undefined := by
                  unfold evalStepInterproc; dsimp
                  rw [w_bodies_getElem?_caller w]; dsimp
                  rw [w_callerTgt_blocks_getElem?_callBlock w]; dsimp
                  rw [hStmt0]; dsimp [evalStatement, liftSingleFrameStep]
                  rw [hGetDstTy]; dsimp [evalRvalue]
                  rw [hEvalOpEq, hOp]; dsimp; rw [hTyBad]; rfl
                constructor
                · intro fk hErr
                  dsimp [evalCallArgs] at hErr; rw [hOp] at hErr; dsimp at hErr
                  rw [hTyBad] at hErr; injection hErr with hFk; subst hFk
                  exact ⟨0, _, StepsN.zero _, hStepFault⟩
                · intro vs callerLocsFinal hOk
                  dsimp [evalCallArgs] at hOk; rw [hOp] at hOk; dsimp at hOk
                  rw [hTyBad] at hOk; cases hOk
              | some v =>
                cases hCvBad : (!checkVal v paramTy) with
                | true =>
                  have hStepFault : evalStepInterproc pTgt 0
                      { cur := { defId := site.callerDefId, blockIdx := site.callBlock,
                                 stmtIdx := baseStmt, locals := callerLocs ++ calleeSlots }
                        stack := stackT, callerMem := mem } = .fault .unsupported := by
                    unfold evalStepInterproc; dsimp
                    rw [w_bodies_getElem?_caller w]; dsimp
                    rw [w_callerTgt_blocks_getElem?_callBlock w]; dsimp
                    rw [hStmt0]; dsimp [evalStatement, liftSingleFrameStep]
                    rw [hGetDstTy]; dsimp [evalRvalue]
                    rw [hEvalOpEq, hOp]; dsimp; rw [hTyBad]; dsimp [writePlace]
                    rw [hCvBad]; rfl
                  constructor
                  · intro fk hErr
                    dsimp [evalCallArgs] at hErr; rw [hOp] at hErr; dsimp at hErr
                    rw [hTyBad] at hErr; dsimp at hErr; rw [hCvBad] at hErr
                    injection hErr with hFk; subst hFk
                    exact ⟨0, _, StepsN.zero _, hStepFault⟩
                  · intro vs callerLocsFinal hOk
                    dsimp [evalCallArgs] at hOk; rw [hOp] at hOk; dsimp at hOk
                    rw [hTyBad] at hOk; dsimp at hOk; rw [hCvBad] at hOk; cases hOk
                | false =>
                  let ⟨optV0, hLiveSlot0⟩ := hLive0
                  let ⟨calleeSlots1, hSetCallee1⟩ :=
                    setElem?_some_of_lt calleeSlots (1 + start) (.live (some v)) hStartSlotLt
                  have hWrite1 : writePlace (locs1 ++ calleeSlots) (w.localBase + 1 + start)
                      paramTy v = .ok (locs1 ++ calleeSlots1) := by
                    rw [hDstIdxEq, ← hCLen1, writePlace_shift_right]
                    unfold writePlace
                    rw [hCvBad]; dsimp
                    rw [hLiveSlot0]; dsimp
                    rw [hSetCallee1]
                  have hStep1 : evalStepInterproc pTgt 0
                      { cur := { defId := site.callerDefId, blockIdx := site.callBlock,
                                 stmtIdx := baseStmt, locals := callerLocs ++ calleeSlots }
                        stack := stackT, callerMem := mem } =
                      .step { cur := { defId := site.callerDefId, blockIdx := site.callBlock,
                                       stmtIdx := baseStmt + 1, locals := locs1 ++ calleeSlots1 }
                              stack := stackT, callerMem := mem } := by
                    unfold evalStepInterproc; dsimp
                    rw [w_bodies_getElem?_caller w]; dsimp
                    rw [w_callerTgt_blocks_getElem?_callBlock w]; dsimp
                    rw [hStmt0]; dsimp [evalStatement, liftSingleFrameStep]
                    rw [hGetDstTy]; dsimp [evalRvalue]
                    rw [hEvalOpEq, hOp]; dsimp; rw [hTyBad]; dsimp
                    rw [hWrite1]
                  have hBoundNext : (start + 1) + restArgs.length ≤ w.calleeSrc.argumentCount := by
                    have hEq : (start + 1) + restArgs.length = start + (restArgs.length + 1) := by
                      rw [Nat.add_assoc, Nat.add_comm 1 restArgs.length]
                    rw [hEq]; exact hBound
                  have hParamTysNext : ∀ k ty,
                      Trusted.MirSemantics.getElem? restTys k = some ty →
                      Trusted.MirSemantics.getElem? w.calleeSrc.locals (1 + (start + 1) + k) =
                        some ty := by
                    intro k ty hK
                    have hEq : 1 + (start + 1) + k = 1 + start + (k + 1) := by
                      rw [← Nat.add_assoc 1 start 1, Nat.add_assoc (1 + start) 1 k, Nat.add_comm 1 k]
                    rw [hEq]
                    exact hParamTys (k + 1) ty hK
                  have hStmtsNext : ∀ k stmt,
                      Trusted.MirSemantics.getElem?
                        (mkArgAssignStmts w.localBase (start + 1) restArgs) k = some stmt →
                      Trusted.MirSemantics.getElem? w.callBbTgt.statements ((baseStmt + 1) + k) =
                        some stmt := by
                    intro k stmt hK
                    have hAdd : (baseStmt + 1) + k = baseStmt + (k + 1) := by
                      rw [Nat.add_assoc, Nat.add_comm 1 k]
                    rw [hAdd]
                    exact hStmts (k + 1) stmt hK
                  have hELen1 : calleeSlots1.length = w.calleeSrc.locals.length :=
                    (setElem?_length hSetCallee1).trans hELen
                  have hLiveNext : ∀ k, k < restArgs.length →
                      ∃ optV, Trusted.MirSemantics.getElem? calleeSlots1
                        (1 + (start + 1) + k) = some (.live optV) := by
                    intro k hKLt
                    have hEq : 1 + (start + 1) + k = 1 + start + (k + 1) := by
                      rw [← Nat.add_assoc 1 start 1, Nat.add_assoc (1 + start) 1 k, Nat.add_comm 1 k]
                    have hNe : 1 + (start + 1) + k ≠ 1 + start := by
                      rw [hEq]
                      exact Nat.ne_of_gt (Nat.lt_add_of_pos_right (Nat.zero_lt_succ k))
                    rw [setElem?_getElem?_ne hSetCallee1 hNe, hEq]
                    exact hLive (k + 1) (Nat.succ_lt_succ hKLt)
                  let ⟨ihErr, ihOk⟩ := ih restTys (start + 1) (baseStmt + 1) locs1 calleeSlots1
                    hRestLenEq hBoundNext hRestArgsLt hParamTysNext hStmtsNext hCLen1 hELen1 hLiveNext
                  constructor
                  · intro fk hErr
                    dsimp [evalCallArgs] at hErr; rw [hOp] at hErr; dsimp at hErr
                    rw [hTyBad] at hErr; dsimp at hErr; rw [hCvBad] at hErr; dsimp at hErr
                    cases hRec : evalCallArgs w.callerSrc.locals locs1 restArgs restTys with
                    | ok pair =>
                      rw [hRec] at hErr; cases pair; cases hErr
                    | error fk' =>
                      rw [hRec] at hErr; injection hErr with hFk; subst hFk
                      let ⟨d, tEnd, hRestSteps, hFaultEnd⟩ := ihErr fk' hRec
                      exact ⟨d + 1, tEnd, StepsN.succ hStep1 hRestSteps, hFaultEnd⟩
                  · intro vs callerLocsFinal hOk
                    dsimp [evalCallArgs] at hOk; rw [hOp] at hOk; dsimp at hOk
                    rw [hTyBad] at hOk; dsimp at hOk; rw [hCvBad] at hOk; dsimp at hOk
                    cases hRec : evalCallArgs w.callerSrc.locals locs1 restArgs restTys with
                    | error _ => rw [hRec] at hOk; cases hOk
                    | ok pair =>
                      rw [hRec] at hOk; dsimp at hOk
                      cases pair with
                      | mk vsRest locsFinal =>
                        dsimp at hOk
                        injection hOk with hP; injection hP with hV hL
                        subst hV; subst hL
                        let ⟨calleeSlotsFinal, hEndLen, hEndPref, hEndSuff, hEndVs, hRestSteps⟩ :=
                          ihOk vsRest locsFinal hRec
                        refine ⟨calleeSlotsFinal, hEndLen, ?_, ?_, ?_, ?_⟩
                        · intro j hJLt
                          have hJLt1 : j < 1 + (start + 1) :=
                            Nat.lt_trans hJLt (by rw [← Nat.add_assoc]; exact Nat.lt_succ_self _)
                          rw [hEndPref j hJLt1]
                          rw [setElem?_getElem?_ne hSetCallee1 (Nat.ne_of_lt hJLt)]
                        · intro j hJGe
                          have hGe1 : 1 + (start + 1) + restArgs.length ≤ j := by
                            have hEq : 1 + (start + 1) + restArgs.length =
                                1 + start + (restArgs.length + 1) := by
                              rw [← Nat.add_assoc 1 start 1, Nat.add_assoc (1 + start) 1,
                                  Nat.add_comm 1 restArgs.length]
                            rw [hEq]; exact hJGe
                          have hNe : j ≠ 1 + start := by
                            apply Nat.ne_of_gt
                            exact Nat.lt_of_lt_of_le
                              (Nat.lt_add_of_pos_right (Nat.zero_lt_succ restArgs.length)) hJGe
                          rw [hEndSuff j hGe1]
                          rw [setElem?_getElem?_ne hSetCallee1 hNe]
                        · intro k v' hGetV
                          cases k with
                          | zero =>
                            injection hGetV with hEqV; subst hEqV
                            rw [Nat.add_zero]
                            have hLt1 : 1 + start < 1 + (start + 1) := by
                              rw [← Nat.add_assoc]; exact Nat.lt_succ_self _
                            rw [hEndPref (1 + start) hLt1]
                            exact setElem?_getElem?_same hSetCallee1
                          | succ m =>
                            have hEq : 1 + start + (m + 1) = 1 + (start + 1) + m := by
                              rw [← Nat.add_assoc 1 start 1, Nat.add_assoc (1 + start) 1 m,
                                  Nat.add_comm 1 m]
                            rw [hEq]
                            exact hEndVs m v' hGetV
                        · dsimp [List.length]
                          have hAddS : baseStmt + (restArgs.length + 1) =
                              (baseStmt + 1) + restArgs.length := by
                            rw [Nat.add_assoc, Nat.add_comm 1 restArgs.length]
                          rw [hAddS]
                          exact StepsN.succ hStep1 hRestSteps

private theorem exec_inlined_call_entry {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt)
    (callerLocs : List LocalSlot) (hCLen : callerLocs.length = w.localBase)
    (stackT : List CallContinuation) (mem : CallerMemory) :
    let paramTys := (w.calleeSrc.locals.drop 1).take w.calleeSrc.argumentCount
    let sStart : InterprocState := {
      cur := {
        defId := site.callerDefId
        blockIdx := site.callBlock
        stmtIdx := w.callBb.statements.length
        locals := callerLocs ++ List.replicate w.calleeSrc.locals.length .dead
      }
      stack := stackT
      callerMem := mem
    }
    (∀ fk, evalCallArgs w.callerSrc.locals callerLocs w.args paramTys = .error fk →
      ∃ d tEnd, StepsN pTgt d sStart tEnd ∧ evalStepInterproc pTgt 0 tEnd = .fault fk) ∧
    (∀ argVals callerLocsAfter,
      evalCallArgs w.callerSrc.locals callerLocs w.args paramTys =
        .ok (argVals, callerLocsAfter) →
      ∃ d, StepsN pTgt (d + 1) sStart
        {
          cur := {
            defId := site.callerDefId
            blockIdx := w.blockBase + 0
            stmtIdx := 0
            locals := callerLocsAfter ++
              initLocalsLoop w.calleeSrc argVals 0 w.calleeSrc.locals
          }
          stack := stackT
          callerMem := mem
        }) := by
  intro paramTys sStart
  have hProStmts : ∀ k stmt,
      Trusted.MirSemantics.getElem? w.prologueLiveStmts k = some stmt →
      Trusted.MirSemantics.getElem? w.callBbTgt.statements
        (w.callBb.statements.length + k) = some stmt := by
    intro k stmt hK
    have hKLt : k < w.prologueLiveStmts.length := getElem?_some_lt hK
    have hLt12 : w.callBb.statements.length + k <
        (w.callBb.statements ++ w.prologueLiveStmts).length := by
      rw [list_append_length]
      exact nat_add_lt_add_left_of_lt _ hKLt
    dsimp [InlineWitness.callBbTgt]
    rw [getElem?_append_left (w.callBb.statements ++ w.prologueLiveStmts) w.argAssignStmts _ hLt12]
    rw [getElem?_append_right_add]
    exact hK
  let ⟨calleePro, hProLen, hProAt, hProSteps⟩ :=
    exec_prologue_aux w callerLocs hCLen stackT mem w.calleeSrc.locals 0
      w.callBb.statements.length (List.replicate w.calleeSrc.locals.length .dead)
      rfl hProStmts (list_replicate_length _ _)
      (fun j _ hLt => False.elim (Nat.not_lt_zero j hLt))
      (fun j _ hLt => getElem?_replicate_lt _ _ _ hLt)
  have hArgBase : (w.callBb.statements ++ w.prologueLiveStmts).length =
      w.callBb.statements.length + w.prologueLiveStmts.length :=
    list_append_length _ _
  have hArgStmts : ∀ k stmt,
      Trusted.MirSemantics.getElem? (mkArgAssignStmts w.localBase 0 w.args) k = some stmt →
      Trusted.MirSemantics.getElem? w.callBbTgt.statements
        ((w.callBb.statements.length + w.prologueLiveStmts.length) + k) = some stmt := by
    intro k stmt hK
    dsimp [InlineWitness.callBbTgt]
    rw [← hArgBase, getElem?_append_right_add]
    exact hK
  have hParamLen : w.args.length = paramTys.length := by
    rw [w.hArgsLen]
    exact (take_drop_length_eq w.calleeSrc.locals w.calleeSrc.argumentCount
      (w_callee_admitted_parts w).2.1).symm
  have hBound0 : 0 + w.args.length ≤ w.calleeSrc.argumentCount := by
    rw [Nat.zero_add, w.hArgsLen]; exact Nat.le_refl _
  have hParamAt : ∀ k ty, Trusted.MirSemantics.getElem? paramTys k = some ty →
      Trusted.MirSemantics.getElem? w.calleeSrc.locals (1 + 0 + k) = some ty := by
    intro k ty hK
    have hKLt : k < w.calleeSrc.argumentCount := by
      have h1 := getElem?_some_lt hK
      rw [take_drop_length_eq w.calleeSrc.locals w.calleeSrc.argumentCount
        (w_callee_admitted_parts w).2.1] at h1
      exact h1
    have hTake := getElem?_take_drop1 w.calleeSrc.locals w.calleeSrc.argumentCount k hKLt
    rw [Nat.add_zero, Nat.add_comm 1 k, ← hTake]
    exact hK
  have hLivePro : ∀ k, k < w.args.length →
      ∃ optV, Trusted.MirSemantics.getElem? calleePro (1 + 0 + k) = some (.live optV) := by
    intro k hKLt
    have hKArg : k < w.calleeSrc.argumentCount := by rw [← w.hArgsLen]; exact hKLt
    have hK1Le : k + 1 ≤ w.calleeSrc.argumentCount := Nat.succ_le_of_lt hKArg
    have hK1Lt : k + 1 < w.calleeSrc.locals.length :=
      Nat.lt_of_le_of_lt hK1Le (w_callee_admitted_parts w).2.1
    let ⟨ty, hTy⟩ := getElem?_some_of_lt w.calleeSrc.locals (k + 1) hK1Lt
    have hIdx : 1 + 0 + k = k + 1 := by rw [Nat.add_zero, Nat.add_comm]
    rw [hIdx, hProAt (k + 1) ty hTy]
    unfold prologueSlotOf
    rw [nat_le_ble hK1Le]
    cases Nat.beq (k + 1) 0 <;>
      (dsimp; let ⟨ov, hOv⟩ := liveUninitSlot_is_live ty; exact ⟨ov, by rw [hOv]⟩)
  let ⟨hArgErr, hArgOk⟩ := exec_argAssign_aux w stackT mem w.args paramTys 0
    (w.callBb.statements.length + w.prologueLiveStmts.length)
    callerLocs calleePro hParamLen hBound0 (w_args_locals_lt w)
    hParamAt hArgStmts hCLen hProLen hLivePro
  constructor
  · intro fk hErr
    let ⟨d, tEnd, hArgSteps, hFaultEnd⟩ := hArgErr fk hErr
    exact ⟨w.prologueLiveStmts.length + d, tEnd,
      stepsN_trans hProSteps hArgSteps, hFaultEnd⟩
  · intro argVals callerLocsAfter hOk
    let ⟨calleeFinal, hFinLen, hFinPref, hFinSuff, hFinVs, hArgSteps⟩ :=
      hArgOk argVals callerLocsAfter hOk
    let ⟨hArgValsLen, _⟩ := evalCallArgs_length hOk
    have hCalleeEq : calleeFinal = initLocalsLoop w.calleeSrc argVals 0 w.calleeSrc.locals := by
      apply list_eq_of_getElem?_eq
      · rw [hFinLen, initLocalsLoop_length]
      · intro j
        cases hTy : Trusted.MirSemantics.getElem? w.calleeSrc.locals j with
        | none =>
          have hGe := getElem?_none_ge hTy
          rw [getElem?_none_of_ge (by rw [hFinLen]; exact hGe)]
          rw [getElem?_none_of_ge (by rw [initLocalsLoop_length]; exact hGe)]
        | some ty =>
          rw [initLocalsLoop_getElem? w.calleeSrc argVals 0 w.calleeSrc.locals j ty hTy]
          rw [Nat.zero_add]
          cases j with
          | zero =>
            rw [hFinPref 0 (Nat.zero_lt_succ 0)]
            rw [hProAt 0 ty hTy]
            rfl
          | succ m =>
            cases Nat.lt_or_ge m w.calleeSrc.argumentCount with
            | inl hMLt =>
              have hMLtVals : m < argVals.length := by
                rw [hArgValsLen, w.hArgsLen]; exact hMLt
              let ⟨v, hGetV⟩ := getElem?_some_of_lt argVals m hMLtVals
              have hLeArg : m + 1 ≤ w.calleeSrc.argumentCount := Nat.succ_le_of_lt hMLt
              have hIdx : m + 1 = 1 + 0 + m := by rw [Nat.add_zero, Nat.add_comm]
              rw [hIdx, hFinVs m v hGetV, ← hIdx]
              have hNe0 : Nat.beq (m + 1) 0 = false := rfl
              rw [hNe0, nat_le_ble hLeArg]
              dsimp
              rw [hGetV]
            | inr hMGe =>
              have hGeFin : 1 + 0 + w.args.length ≤ m + 1 := by
                rw [Nat.add_zero, w.hArgsLen, Nat.add_comm 1]
                exact Nat.succ_le_succ hMGe
              rw [hFinSuff (m + 1) hGeFin, hProAt (m + 1) ty hTy]
              have hNe0 : Nat.beq (m + 1) 0 = false := rfl
              have hGtArg : Nat.ble (m + 1) w.calleeSrc.argumentCount = false :=
                nat_gt_ble_false (Nat.lt_succ_of_le hMGe)
              unfold prologueSlotOf
              rw [hNe0, hGtArg]
              dsimp
              cases hasStorageAnnotation w.calleeSrc (m + 1) <;> rfl
    have hEndStmtLen : (w.callBb.statements.length + w.prologueLiveStmts.length) +
        w.args.length = w.callBbTgt.statements.length := by
      dsimp [InlineWitness.callBbTgt]
      rw [list_append_length, list_append_length, InlineWitness.argAssignStmts,
          mkArgAssignStmts_length]
    have hGotoStep : evalStepInterproc pTgt 0
        { cur := { defId := site.callerDefId, blockIdx := site.callBlock,
                   stmtIdx := (w.callBb.statements.length + w.prologueLiveStmts.length) +
                     w.args.length,
                   locals := callerLocsAfter ++ calleeFinal }
          stack := stackT, callerMem := mem } =
        .step { cur := { defId := site.callerDefId, blockIdx := w.blockBase + 0,
                         stmtIdx := 0,
                         locals := callerLocsAfter ++
                           initLocalsLoop w.calleeSrc argVals 0 w.calleeSrc.locals }
                stack := stackT, callerMem := mem } := by
      unfold evalStepInterproc; dsimp
      rw [w_bodies_getElem?_caller w]; dsimp
      rw [w_callerTgt_blocks_getElem?_callBlock w]; dsimp
      rw [hEndStmtLen]
      rw [getElem?_none_of_ge (Nat.le_refl _)]
      rw [nat_beq_refl]
      dsimp [InlineWitness.callBbTgt, evalTerminator, jumpToBlock, liftSingleFrameStep]
      rw [hCalleeEq]
    refine ⟨w.prologueLiveStmts.length + w.args.length, ?_⟩
    exact stepsN_trans (stepsN_trans hProSteps hArgSteps) (stepsN_one hGotoStep)

/-! #### Epilogue Return Transfer & `StorageDead` Multi-Step Execution -/

private theorem exec_epilogue_deads_aux {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt)
    (callerLocs : List LocalSlot) (hCLen : callerLocs.length = w.localBase)
    (stackT : List CallContinuation) (mem : CallerMemory)
    (count start : Nat) (calleeSlots : List LocalSlot)
    (hSum : start + count = w.calleeSrc.locals.length)
    (hELen : calleeSlots.length = w.calleeSrc.locals.length)
    (hPrefDead : ∀ j, j < start →
      Trusted.MirSemantics.getElem? calleeSlots j = some .dead) :
    StepsN pTgt count
      { cur := { defId := site.callerDefId, blockIdx := w.exitBlock,
                 stmtIdx := 1 + start, locals := callerLocs ++ calleeSlots }
        stack := stackT, callerMem := mem }
      { cur := { defId := site.callerDefId, blockIdx := w.exitBlock,
                 stmtIdx := 1 + w.calleeSrc.locals.length,
                 locals := callerLocs ++ List.replicate w.calleeSrc.locals.length .dead }
        stack := stackT, callerMem := mem } := by
  induction count generalizing start calleeSlots with
  | zero =>
    rw [Nat.add_zero] at hSum
    have hEqDead : calleeSlots = List.replicate w.calleeSrc.locals.length .dead := by
      apply list_eq_of_getElem?_eq
      · rw [hELen, list_replicate_length]
      · intro j
        cases Nat.lt_or_ge j w.calleeSrc.locals.length with
        | inl hLt =>
          rw [hPrefDead j (by rw [hSum]; exact hLt), getElem?_replicate_lt _ _ _ hLt]
        | inr hGe =>
          rw [getElem?_none_of_ge (by rw [hELen]; exact hGe)]
          rw [getElem?_none_of_ge (by rw [list_replicate_length]; exact hGe)]
    rw [hSum, hEqDead]
    exact StepsN.zero _
  | succ k ih =>
    have hStartLt : start < w.calleeSrc.locals.length := by
      rw [← hSum]
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self start)
        (by rw [Nat.add_succ]; exact Nat.succ_le_succ (Nat.le_add_right start k))
    have hStartLtSlots : start < calleeSlots.length := by rw [hELen]; exact hStartLt
    let ⟨calleeSlots', hSetC⟩ := setElem?_some_of_lt calleeSlots start .dead hStartLtSlots
    have hStmt : Trusted.MirSemantics.getElem? w.exitBb.statements (1 + start) =
        some (.storageDead (w.localBase + start)) := by
      have hIdx : 1 + start = start + 1 := Nat.add_comm 1 start
      rw [hIdx]
      dsimp [InlineWitness.exitBb, Trusted.MirSemantics.getElem?,
             InlineWitness.epilogueDeadStmts]
      have hG := mkEpilogueStorageDeads_getElem? w.localBase 0 w.calleeSrc.locals.length
        start hStartLt
      rw [Nat.zero_add] at hG
      exact hG
    have hNe0 : Nat.beq (w.localBase + start) 0 = false :=
      nat_beq_false_of_ne (nat_add_ne_zero_left (w_localBase_pos w))
    have hSetFull : setElem? (callerLocs ++ calleeSlots) (w.localBase + start) .dead =
        some (callerLocs ++ calleeSlots') := by
      rw [← hCLen, setElem?_append_right_add callerLocs calleeSlots start .dead, hSetC]
      rfl
    have hStep1 : evalStepInterproc pTgt 0
        { cur := { defId := site.callerDefId, blockIdx := w.exitBlock,
                   stmtIdx := 1 + start, locals := callerLocs ++ calleeSlots }
          stack := stackT, callerMem := mem } =
        .step { cur := { defId := site.callerDefId, blockIdx := w.exitBlock,
                         stmtIdx := 1 + (start + 1), locals := callerLocs ++ calleeSlots' }
                stack := stackT, callerMem := mem } := by
      unfold evalStepInterproc; dsimp
      rw [w_bodies_getElem?_caller w]; dsimp
      rw [w_callerTgt_blocks_getElem?_exit w]; dsimp
      rw [hStmt]; dsimp [evalStatement, liftSingleFrameStep]
      rw [hNe0]; dsimp
      rw [hSetFull]; rfl
    have hSumNext : (start + 1) + k = w.calleeSrc.locals.length := by
      rw [Nat.add_assoc, Nat.add_comm 1 k, ← Nat.add_assoc]; exact hSum
    have hELen' : calleeSlots'.length = w.calleeSrc.locals.length :=
      (setElem?_length hSetC).trans hELen
    have hPrefNext : ∀ j, j < start + 1 →
        Trusted.MirSemantics.getElem? calleeSlots' j = some .dead := by
      intro j hJLt
      cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hJLt) with
      | inl hLt =>
        rw [setElem?_getElem?_ne hSetC (Nat.ne_of_lt hLt)]
        exact hPrefDead j hLt
      | inr hEq =>
        subst hEq
        exact setElem?_getElem?_same hSetC
    exact StepsN.succ hStep1 (ih (start + 1) calleeSlots' hSumNext hELen' hPrefNext)

private theorem exec_inlined_return_epilogue {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt)
    (outerLocs calleeLocs : List LocalSlot)
    (hOLen : outerLocs.length = w.localBase)
    (hELen : calleeLocs.length = w.calleeSrc.locals.length)
    (cb : BasicBlockId) (cbb : BasicBlock)
    (hGetCbb : Trusted.MirSemantics.getElem? w.calleeSrc.basicBlocks cb = some cbb)
    (hNotCleanup : cbb.cleanup = false)
    (hTerm : cbb.terminator = .return_)
    (stackT : List CallContinuation) (mem : CallerMemory) :
    let sStart : InterprocState := {
      cur := {
        defId := site.callerDefId
        blockIdx := w.blockBase + cb
        stmtIdx := cbb.statements.length
        locals := outerLocs ++ calleeLocs
      }
      stack := stackT
      callerMem := mem
    }
    match Trusted.MirSemantics.getElem? calleeLocs 0 with
    | some (.live (some retVal)) =>
      match writePlace outerLocs w.dst.localId w.dstTy retVal with
      | .error fk =>
        ∃ d tEnd, StepsN pTgt d sStart tEnd ∧ evalStepInterproc pTgt 0 tEnd = .fault fk
      | .ok outerLocs' =>
        ∃ d, StepsN pTgt (d + 1) sStart
          {
            cur := {
              defId := site.callerDefId
              blockIdx := w.retBb
              stmtIdx := 0
              locals := outerLocs' ++ List.replicate w.calleeSrc.locals.length .dead
            }
            stack := stackT
            callerMem := mem
          }
    | some (.live none) | some .dead =>
      ∃ d tEnd, StepsN pTgt d sStart tEnd ∧ evalStepInterproc pTgt 0 tEnd = .fault .undefined
    | none => True := by
  intro sStart
  have hCbLt : cb < w.calleeSrc.basicBlocks.length := getElem?_some_lt hGetCbb
  have hGetShifted : Trusted.MirSemantics.getElem? w.callerTgt.basicBlocks (w.blockBase + cb) =
      some (shiftCalleeBlock w.localBase w.blockBase w.exitBlock w.unwind cbb) := by
    rw [w_callerTgt_blocks_getElem?_callee w hCbLt, hGetCbb]; rfl
  have hShiftedLen : (shiftCalleeBlock w.localBase w.blockBase w.exitBlock w.unwind cbb).statements.length =
      cbb.statements.length := map_length_eq _ _
  have hStepGotoExit : evalStepInterproc pTgt 0 sStart =
      .step {
        cur := {
          defId := site.callerDefId
          blockIdx := w.exitBlock
          stmtIdx := 0
          locals := outerLocs ++ calleeLocs
        }
        stack := stackT
        callerMem := mem
      } := by
    unfold evalStepInterproc; dsimp [sStart]
    rw [w_bodies_getElem?_caller w]; dsimp
    rw [hGetShifted]; dsimp
    rw [getElem?_none_of_ge (by rw [hShiftedLen]; exact Nat.le_refl _)]
    rw [hShiftedLen, nat_beq_refl]
    dsimp [shiftCalleeBlock]
    rw [hTerm, hNotCleanup]
    dsimp [shiftCalleeTerminator, evalTerminator, jumpToBlock, liftSingleFrameStep]
  have hGetDstTyTgt : Trusted.MirSemantics.getElem? w.callerTgt.locals w.dst.localId =
      some w.dstTy := by
    have hLocEq : w.callerTgt.locals = w.callerSrc.locals ++ w.calleeSrc.locals := rfl
    rw [hLocEq, getElem?_append_left _ _ _ w.hDstLt]
    exact w.hGetDstTy
  have hGetRetTyTgt : Trusted.MirSemantics.getElem? w.callerTgt.locals w.localBase =
      some w.calleeRetTy := by
    have hLocEq : w.callerTgt.locals = w.callerSrc.locals ++ w.calleeSrc.locals := rfl
    rw [hLocEq]
    change Trusted.MirSemantics.getElem? (w.callerSrc.locals ++ w.calleeSrc.locals)
      (w.callerSrc.locals.length + 0) = some w.calleeRetTy
    rw [getElem?_append_right_add]
    exact w.hGetCalleeRetTy
  have hGetSlot0 : Trusted.MirSemantics.getElem? (outerLocs ++ calleeLocs) w.localBase =
      Trusted.MirSemantics.getElem? calleeLocs 0 := by
    have hAdd0 : w.localBase = outerLocs.length + 0 := by rw [hOLen, Nat.add_zero]
    rw [hAdd0, getElem?_append_right_add]
  have hTyBeq : MirTy.beq w.calleeRetTy w.dstTy = true := by
    rw [w.hRetTyEq]; exact mirTy_beq_refl w.dstTy
  cases hSlot0 : Trusted.MirSemantics.getElem? calleeLocs 0 with
  | none => exact True.intro
  | some sl =>
    cases sl with
    | dead =>
      dsimp
      refine ⟨1, _, stepsN_one hStepGotoExit, ?_⟩
      unfold evalStepInterproc; dsimp
      rw [w_bodies_getElem?_caller w]; dsimp
      rw [w_callerTgt_blocks_getElem?_exit w]
      dsimp [InlineWitness.exitBb, Trusted.MirSemantics.getElem?, evalStatement, liftSingleFrameStep]
      rw [w.hDstUnproj]; dsimp
      rw [hGetDstTyTgt]; dsimp [evalRvalue, evalOperandToSlot]
      rw [hGetRetTyTgt, hGetSlot0, hSlot0]
    | live optV =>
      cases optV with
      | none =>
        dsimp
        let ⟨calleeLocs1, hSet0⟩ :=
          setElem?_some_of_lt calleeLocs 0 (liveUninitSlot w.calleeRetTy)
            (getElem?_some_lt hSlot0)
        have hSetFull : setElem? (outerLocs ++ calleeLocs) w.localBase
            (liveUninitSlot w.calleeRetTy) = some (outerLocs ++ calleeLocs1) := by
          have hAdd0 : w.localBase = outerLocs.length + 0 := by rw [hOLen, Nat.add_zero]
          rw [hAdd0, setElem?_append_right_add, hSet0]; rfl
        refine ⟨1, _, stepsN_one hStepGotoExit, ?_⟩
        unfold evalStepInterproc; dsimp
        rw [w_bodies_getElem?_caller w]; dsimp
        rw [w_callerTgt_blocks_getElem?_exit w]
        dsimp [InlineWitness.exitBb, Trusted.MirSemantics.getElem?, evalStatement, liftSingleFrameStep]
        rw [w.hDstUnproj]; dsimp
        rw [hGetDstTyTgt]; dsimp [evalRvalue, evalOperandToSlot]
        rw [hGetRetTyTgt, hGetSlot0, hSlot0]; dsimp
        rw [hSetFull]; dsimp
        rw [hTyBeq]; rfl
      | some retVal =>
        dsimp
        let ⟨calleeLocs1, hSet0⟩ :=
          setElem?_some_of_lt calleeLocs 0 (liveUninitSlot w.calleeRetTy)
            (getElem?_some_lt hSlot0)
        have hSetFull : setElem? (outerLocs ++ calleeLocs) w.localBase
            (liveUninitSlot w.calleeRetTy) = some (outerLocs ++ calleeLocs1) := by
          have hAdd0 : w.localBase = outerLocs.length + 0 := by rw [hOLen, Nat.add_zero]
          rw [hAdd0, setElem?_append_right_add, hSet0]; rfl
        have hDstLtOuter : w.dst.localId < outerLocs.length := by
          rw [hOLen]; exact w.hDstLt
        have hWriteEq := writePlace_append_left (suffix := calleeLocs1) (dstTy := w.dstTy)
          (val := retVal) hDstLtOuter
        cases hWr : writePlace outerLocs w.dst.localId w.dstTy retVal with
        | error fk =>
          dsimp
          refine ⟨1, _, stepsN_one hStepGotoExit, ?_⟩
          unfold evalStepInterproc; dsimp
          rw [w_bodies_getElem?_caller w]; dsimp
          rw [w_callerTgt_blocks_getElem?_exit w]
          dsimp [InlineWitness.exitBb, Trusted.MirSemantics.getElem?, evalStatement, liftSingleFrameStep]
          rw [w.hDstUnproj]; dsimp
          rw [hGetDstTyTgt]; dsimp [evalRvalue, evalOperandToSlot]
          rw [hGetRetTyTgt, hGetSlot0, hSlot0]; dsimp
          rw [hSetFull]; dsimp
          rw [hTyBeq]; dsimp
          rw [hWriteEq, hWr]
        | ok outerLocs' =>
          dsimp
          have hOLen' : outerLocs'.length = w.localBase :=
            (writePlace_length hWr).trans hOLen
          have hELen1 : calleeLocs1.length = w.calleeSrc.locals.length :=
            (setElem?_length hSet0).trans hELen
          have hStepAssign : evalStepInterproc pTgt 0
              { cur := { defId := site.callerDefId, blockIdx := w.exitBlock,
                         stmtIdx := 0, locals := outerLocs ++ calleeLocs }
                stack := stackT, callerMem := mem } =
              .step { cur := { defId := site.callerDefId, blockIdx := w.exitBlock,
                               stmtIdx := 1 + 0, locals := outerLocs' ++ calleeLocs1 }
                      stack := stackT, callerMem := mem } := by
            unfold evalStepInterproc; dsimp
            rw [w_bodies_getElem?_caller w]; dsimp
            rw [w_callerTgt_blocks_getElem?_exit w]
            dsimp [InlineWitness.exitBb, Trusted.MirSemantics.getElem?, evalStatement, liftSingleFrameStep]
            rw [w.hDstUnproj]; dsimp
            rw [hGetDstTyTgt]; dsimp [evalRvalue, evalOperandToSlot]
            rw [hGetRetTyTgt, hGetSlot0, hSlot0]; dsimp
            rw [hSetFull]; dsimp
            rw [hTyBeq]; dsimp
            rw [hWriteEq, hWr]
          have hDeads := exec_epilogue_deads_aux w outerLocs' hOLen' stackT mem
            w.calleeSrc.locals.length 0 calleeLocs1 (Nat.zero_add _) hELen1
            (fun j hLt => False.elim (Nat.not_lt_zero j hLt))
          have hExitLen : w.exitBb.statements.length = 1 + w.calleeSrc.locals.length := by
            dsimp [InlineWitness.exitBb, List.length, InlineWitness.epilogueDeadStmts]
            rw [mkEpilogueStorageDeads_length, Nat.add_comm]
          have hStepGotoRet : evalStepInterproc pTgt 0
              { cur := { defId := site.callerDefId, blockIdx := w.exitBlock,
                         stmtIdx := 1 + w.calleeSrc.locals.length,
                         locals := outerLocs' ++
                           List.replicate w.calleeSrc.locals.length .dead }
                stack := stackT, callerMem := mem } =
              .step { cur := { defId := site.callerDefId, blockIdx := w.retBb,
                               stmtIdx := 0,
                               locals := outerLocs' ++
                                 List.replicate w.calleeSrc.locals.length .dead }
                      stack := stackT, callerMem := mem } := by
            unfold evalStepInterproc; dsimp
            rw [w_bodies_getElem?_caller w]; dsimp
            rw [w_callerTgt_blocks_getElem?_exit w]; dsimp
            rw [← hExitLen, getElem?_none_of_ge (Nat.le_refl _), nat_beq_refl]
            rfl
          refine ⟨1 + w.calleeSrc.locals.length + 1, ?_⟩
          have hTot := stepsN_trans
            (stepsN_trans (stepsN_one hStepGotoExit) (stepsN_one hStepAssign))
            (stepsN_trans hDeads (stepsN_one hStepGotoRet))
          have hCountEq : (1 + 1) + (w.calleeSrc.locals.length + 1) =
              1 + w.calleeSrc.locals.length + 1 + 1 := by
            rw [Nat.add_assoc 1 1, Nat.add_comm 1 (w.calleeSrc.locals.length + 1),
                ← Nat.add_assoc 1 (w.calleeSrc.locals.length + 1) 1,
                ← Nat.add_assoc 1 w.calleeSrc.locals.length 1]
          rw [hCountEq] at hTot
          exact hTot

/-! #### Stack & Machine State Simulation Relation (`SimStack` & `SimState`) -/

private inductive SimStack {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt) :
    List CallContinuation → List CallContinuation → Prop where
  | nil : SimStack w [] []
  | nonCaller (cont : CallContinuation) (restS restT : List CallContinuation) :
      cont.callerFrame.defId ≠ site.callerDefId →
      SimStack w restS restT →
      SimStack w (cont :: restS) (cont :: restT)
  | outerCaller (cont : CallContinuation) (restS restT : List CallContinuation) :
      cont.callerFrame.defId = site.callerDefId →
      cont.callerFrame.locals.length = w.localBase →
      cont.dst.localId < w.localBase →
      (∀ b, cont.target = some b → b < w.blockBase) →
      SimStack w restS restT →
      SimStack w (cont :: restS)
        ({ cont with
           callerFrame := {
             cont.callerFrame with
             locals := cont.callerFrame.locals ++
               List.replicate w.calleeSrc.locals.length .dead
           } } :: restT)
  | splicedCallee (contInner contOuter : CallContinuation)
      (restS restT : List CallContinuation)
      (bbTgt stmtTgt : Nat) (uTgt : UnwindAction) :
      contInner.callerFrame.defId = site.calleeDefId →
      contInner.callerFrame.locals.length = w.calleeSrc.locals.length →
      (∀ b, contInner.target = some b → b < w.calleeSrc.basicBlocks.length) →
      contOuter.callerFrame.defId = site.callerDefId →
      contOuter.callerFrame.locals.length = w.localBase →
      contOuter.dst = w.dst →
      contOuter.target = some w.retBb →
      SimStack w restS restT →
      SimStack w (contInner :: contOuter :: restS)
        ({
          callerFrame := {
            defId := site.callerDefId
            blockIdx := bbTgt
            stmtIdx := stmtTgt
            locals := contOuter.callerFrame.locals ++ contInner.callerFrame.locals
          }
          dst := shiftPlace w.localBase contInner.dst
          target := contInner.target.map (fun b => w.blockBase + b)
          unwind := uTgt
        } :: restT)

private inductive SimState {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt) :
    InterprocState → InterprocState → Prop where
  | nonCaller (frame : FrameState) (stackS stackT : List CallContinuation)
      (mem : CallerMemory) :
      frame.defId ≠ site.callerDefId →
      SimStack w stackS stackT →
      SimState w
        { cur := frame, stack := stackS, callerMem := mem }
        { cur := frame, stack := stackT, callerMem := mem }
  | outerCaller (frame : FrameState) (stackS stackT : List CallContinuation)
      (mem : CallerMemory) :
      frame.defId = site.callerDefId →
      frame.locals.length = w.localBase →
      frame.blockIdx < w.blockBase →
      (∀ bb, Trusted.MirSemantics.getElem? w.callerSrc.basicBlocks frame.blockIdx = some bb →
        frame.stmtIdx ≤ bb.statements.length) →
      SimStack w stackS stackT →
      SimState w
        { cur := frame, stack := stackS, callerMem := mem }
        { cur := { frame with
            locals := frame.locals ++ List.replicate w.calleeSrc.locals.length .dead }
          stack := stackT, callerMem := mem }
  | inlinedCallee (calleeFrame : FrameState) (contOuter : CallContinuation)
      (restS stackT : List CallContinuation) (mem : CallerMemory) :
      calleeFrame.defId = site.calleeDefId →
      calleeFrame.locals.length = w.calleeSrc.locals.length →
      calleeFrame.blockIdx < w.calleeSrc.basicBlocks.length →
      (∀ cbb, Trusted.MirSemantics.getElem? w.calleeSrc.basicBlocks calleeFrame.blockIdx =
          some cbb →
        calleeFrame.stmtIdx ≤ cbb.statements.length) →
      contOuter.callerFrame.defId = site.callerDefId →
      contOuter.callerFrame.locals.length = w.localBase →
      contOuter.dst = w.dst →
      contOuter.target = some w.retBb →
      SimStack w restS stackT →
      SimState w
        { cur := calleeFrame, stack := contOuter :: restS, callerMem := mem }
        { cur := {
            defId := site.callerDefId
            blockIdx := w.blockBase + calleeFrame.blockIdx
            stmtIdx := calleeFrame.stmtIdx
            locals := contOuter.callerFrame.locals ++ calleeFrame.locals
          }
          stack := stackT, callerMem := mem }

/-! #### Shared Return-Stack & Call-Callee Transition Simulation Lemmas -/

private theorem sim_fault_same {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt) (fk0 : FaultKind) :
    (∀ s', (.fault fk0 : StepResult InterprocState TerminalOut) = .step s' →
      ∃ t', (.fault fk0 : StepResult InterprocState TerminalOut) = .step t' ∧ SimState w s' t') ∧
    (∀ out, (.fault fk0 : StepResult InterprocState TerminalOut) = .done out →
      (.fault fk0 : StepResult InterprocState TerminalOut) = .done out) ∧
    (∀ fk, (.fault fk0 : StepResult InterprocState TerminalOut) = .fault fk →
      (.fault fk0 : StepResult InterprocState TerminalOut) = .fault fk) :=
  ⟨fun _ h => (by cases h), fun _ h => (by cases h), fun _ h => h⟩

private theorem sim_return_step {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt)
    {bodySrc bodyTgt : Body} {bbSrc bbTgt : BasicBlock}
    {frameSrc frameTgt : FrameState}
    {stackS stackT : List CallContinuation} {mem : CallerMemory}
    (hCl : bbSrc.cleanup = bbTgt.cleanup)
    (hRetTy0 : Trusted.MirSemantics.getElem? bodySrc.locals 0 =
      Trusted.MirSemantics.getElem? bodyTgt.locals 0)
    (hRetSlot0 : Trusted.MirSemantics.getElem? frameSrc.locals 0 =
      Trusted.MirSemantics.getElem? frameTgt.locals 0)
    (hStack : SimStack w stackS stackT) :
    let resS := evalReturnTerminator pSrc bodySrc bbSrc frameSrc stackS mem
    let resT := evalReturnTerminator pTgt bodyTgt bbTgt frameTgt stackT mem
    (∀ s', resS = .step s' → ∃ t', resT = .step t' ∧ SimState w s' t') ∧
    (∀ out, resS = .done out → resT = .done out) ∧
    (∀ fk, resS = .fault fk → resT = .fault fk) := by
  intro resS resT
  have hUnf : ∀ (a : StepResult InterprocState TerminalOut)
      (b : StepResult InterprocState TerminalOut),
      a = b → (match a with | .step _ => False | _ => True) →
      (∀ s', a = .step s' → ∃ t', b = .step t' ∧ SimState w s' t') ∧
      (∀ out, a = .done out → b = .done out) ∧
      (∀ fk, a = .fault fk → b = .fault fk) := by
    intro a b hEq hNS
    subst hEq
    cases a with
    | step _ => exact False.elim hNS
    | done _ => exact ⟨fun _ h => (by cases h), fun _ h => h, fun _ h => (by cases h)⟩
    | fault fk => exact sim_fault_same w fk
  cases hClVal : bbSrc.cleanup with
  | true =>
    have hClT : bbTgt.cleanup = true := by rw [← hCl, hClVal]
    apply hUnf resS resT
    · unfold resS resT evalReturnTerminator; rw [hClVal, hClT]; rfl
    · unfold resS evalReturnTerminator; rw [hClVal]; exact True.intro
  | false =>
    have hClT : bbTgt.cleanup = false := by rw [← hCl, hClVal]
    cases hStack with
    | nil =>
      apply hUnf resS resT
      · unfold resS resT evalReturnTerminator
        rw [hClVal, hClT]; dsimp; rw [hRetSlot0]
      · unfold resS evalReturnTerminator
        rw [hClVal]; dsimp
        cases Trusted.MirSemantics.getElem? frameSrc.locals 0 with
        | none => exact True.intro
        | some sl => cases sl with
          | dead => exact True.intro
          | live ov => cases ov <;> exact True.intro
    | nonCaller cont restS restT hNe hRest =>
      unfold resS resT evalReturnTerminator
      rw [hClVal, hClT]; dsimp
      cases hProj : (!cont.dst.projection.isEmpty) with
      | true => exact sim_fault_same w .unsupported
      | false =>
        dsimp
        rw [w_bodies_getElem?_ne w hNe]
        cases Trusted.MirSemantics.getElem? pSrc.bodies cont.callerFrame.defId with
        | none => exact sim_fault_same w .unsupported
        | some callerBody =>
          dsimp
          rw [← hRetTy0]
          cases Trusted.MirSemantics.getElem? callerBody.locals cont.dst.localId with
          | none => exact sim_fault_same w .unsupported
          | some dstTy =>
            cases Trusted.MirSemantics.getElem? bodySrc.locals 0 with
            | none => exact sim_fault_same w .unsupported
            | some calleeRetTy =>
              dsimp
              cases (!MirTy.beq calleeRetTy dstTy) with
              | true => exact sim_fault_same w .unsupported
              | false =>
                dsimp
                rw [← hRetSlot0]
                cases Trusted.MirSemantics.getElem? frameSrc.locals 0 with
                | none => exact sim_fault_same w .unsupported
                | some sl =>
                  cases sl with
                  | dead => exact sim_fault_same w .undefined
                  | live ov =>
                    cases ov with
                    | none => exact sim_fault_same w .undefined
                    | some retVal =>
                      dsimp
                      cases writePlace cont.callerFrame.locals cont.dst.localId dstTy retVal with
                      | error fk => exact sim_fault_same w fk
                      | ok callerLocs' =>
                        dsimp
                        cases cont.target with
                        | none => exact sim_fault_same w .undefined
                        | some retBb =>
                          dsimp
                          refine ⟨fun s' hSt => ?_, fun _ h => (by cases h), fun _ h => (by cases h)⟩
                          injection hSt with hEq; subst hEq
                          exact ⟨_, rfl, SimState.nonCaller _ restS restT mem hNe hRest⟩
    | outerCaller cont restS restT hDef hCLen hDstLt hTgtLt hRest =>
      unfold resS resT evalReturnTerminator
      rw [hClVal, hClT]; dsimp
      cases hProj : (!cont.dst.projection.isEmpty) with
      | true => exact sim_fault_same w .unsupported
      | false =>
        dsimp
        rw [hDef, w.hGetCallerSrc, w_bodies_getElem?_caller w]
        dsimp
        have hLocEq : w.callerTgt.locals = w.callerSrc.locals ++ w.calleeSrc.locals := rfl
        rw [hLocEq, getElem?_append_left _ _ _ hDstLt, ← hRetTy0]
        cases Trusted.MirSemantics.getElem? w.callerSrc.locals cont.dst.localId with
        | none => exact sim_fault_same w .unsupported
        | some dstTy =>
          cases Trusted.MirSemantics.getElem? bodySrc.locals 0 with
          | none => exact sim_fault_same w .unsupported
          | some calleeRetTy =>
            dsimp
            cases (!MirTy.beq calleeRetTy dstTy) with
            | true => exact sim_fault_same w .unsupported
            | false =>
              dsimp
              rw [← hRetSlot0]
              cases Trusted.MirSemantics.getElem? frameSrc.locals 0 with
              | none => exact sim_fault_same w .unsupported
              | some sl =>
                cases sl with
                | dead => exact sim_fault_same w .undefined
                | live ov =>
                  cases ov with
                  | none => exact sim_fault_same w .undefined
                  | some retVal =>
                    dsimp
                    have hDstLtC : cont.dst.localId < cont.callerFrame.locals.length := by
                      rw [hCLen]; exact hDstLt
                    rw [writePlace_append_left hDstLtC]
                    cases hWr : writePlace cont.callerFrame.locals cont.dst.localId dstTy retVal with
                    | error fk => exact sim_fault_same w fk
                    | ok callerLocs' =>
                      dsimp
                      cases hTgt : cont.target with
                      | none => exact sim_fault_same w .undefined
                      | some retBb =>
                        dsimp
                        refine ⟨fun s' hSt => ?_, fun _ h => (by cases h), fun _ h => (by cases h)⟩
                        injection hSt with hEq; subst hEq
                        exact ⟨_, rfl, SimState.outerCaller _ restS restT mem rfl
                          ((writePlace_length hWr).trans hCLen)
                          (hTgtLt retBb hTgt)
                          (fun _ _ => Nat.zero_le _) hRest⟩
    | splicedCallee contInner contOuter restS restT bbTgt stmtTgt uTgt
        hInDef hInLen hInTgtLt hOutDef hOutLen hOutDst hOutTgt hRest =>
      unfold resS resT evalReturnTerminator
      rw [hClVal, hClT]; dsimp [shiftPlace]
      cases hProj : (!contInner.dst.projection.isEmpty) with
      | true => exact sim_fault_same w .unsupported
      | false =>
        dsimp
        rw [hInDef, w.hGetCalleeSrc, w_bodies_getElem?_caller w]
        dsimp
        have hLocEq : w.callerTgt.locals = w.callerSrc.locals ++ w.calleeSrc.locals := rfl
        have hGetDst : Trusted.MirSemantics.getElem? w.callerTgt.locals
            (w.localBase + contInner.dst.localId) =
            Trusted.MirSemantics.getElem? w.calleeSrc.locals contInner.dst.localId := by
          rw [hLocEq]
          change Trusted.MirSemantics.getElem? (w.callerSrc.locals ++ w.calleeSrc.locals)
            (w.callerSrc.locals.length + contInner.dst.localId) = _
          rw [getElem?_append_right_add]
        rw [hGetDst, ← hRetTy0]
        cases Trusted.MirSemantics.getElem? w.calleeSrc.locals contInner.dst.localId with
        | none => exact sim_fault_same w .unsupported
        | some dstTy =>
          cases Trusted.MirSemantics.getElem? bodySrc.locals 0 with
          | none => exact sim_fault_same w .unsupported
          | some calleeRetTy =>
            dsimp
            cases (!MirTy.beq calleeRetTy dstTy) with
            | true => exact sim_fault_same w .unsupported
            | false =>
              dsimp
              rw [← hRetSlot0]
              cases Trusted.MirSemantics.getElem? frameSrc.locals 0 with
              | none => exact sim_fault_same w .unsupported
              | some sl =>
                cases sl with
                | dead => exact sim_fault_same w .undefined
                | live ov =>
                  cases ov with
                  | none => exact sim_fault_same w .undefined
                  | some retVal =>
                    dsimp
                    rw [← hOutLen, writePlace_shift_right]
                    cases hWr : writePlace contInner.callerFrame.locals contInner.dst.localId
                        dstTy retVal with
                    | error fk => exact sim_fault_same w fk
                    | ok innerLocs' =>
                      dsimp
                      cases hTgt : contInner.target with
                      | none => exact sim_fault_same w .undefined
                      | some retBb =>
                        dsimp [Option.map]
                        refine ⟨fun s' hSt => ?_, fun _ h => (by cases h), fun _ h => (by cases h)⟩
                        injection hSt with hEq; subst hEq
                        exact ⟨_, rfl, SimState.inlinedCallee _ contOuter restS restT mem
                          rfl ((writePlace_length hWr).trans hInLen)
                          (hInTgtLt retBb hTgt)
                          (fun _ _ => Nat.zero_le _)
                          hOutDef hOutLen hOutDst hOutTgt hRest⟩

private theorem sim_call_entry_general {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt)
    {callerBodySrc callerBodyTgt : Body} {bbSrc bbTgt : BasicBlock}
    {frameSrc frameTgt : FrameState}
    {stackS stackT : List CallContinuation} {mem : CallerMemory}
    {calleeDefId : DefId} {argsSrc argsTgt : List Operand}
    {dstSrc dstTgt : Place} {targetSrc targetTgt : Option BasicBlockId}
    {unwindSrc unwindTgt : UnwindAction}
    (hCl : bbSrc.cleanup = bbTgt.cleanup)
    (hProj : dstSrc.projection.isEmpty = dstTgt.projection.isEmpty)
    (hDstTy : Trusted.MirSemantics.getElem? callerBodySrc.locals dstSrc.localId =
      Trusted.MirSemantics.getElem? callerBodyTgt.locals dstTgt.localId)
    (hCallArgs : ∀ paramTys,
      (∀ fk, evalCallArgs callerBodySrc.locals frameSrc.locals argsSrc paramTys = .error fk →
        evalCallArgs callerBodyTgt.locals frameTgt.locals argsTgt paramTys = .error fk) ∧
      (∀ argVals locsS,
        evalCallArgs callerBodySrc.locals frameSrc.locals argsSrc paramTys = .ok (argVals, locsS) →
        ∃ locsT,
          evalCallArgs callerBodyTgt.locals frameTgt.locals argsTgt paramTys = .ok (argVals, locsT) ∧
          SimStack w
            ({ callerFrame := { frameSrc with locals := locsS }, dst := dstSrc,
               target := targetSrc, unwind := unwindSrc } :: stackS)
            ({ callerFrame := { frameTgt with locals := locsT }, dst := dstTgt,
               target := targetTgt, unwind := unwindTgt } :: stackT)))
    (hArgsLen : argsSrc.length = argsTgt.length) :
    let resS := evalCallTerminator pSrc callerBodySrc bbSrc frameSrc stackS mem
      calleeDefId argsSrc dstSrc targetSrc unwindSrc
    let resT := evalCallTerminator pTgt callerBodyTgt bbTgt frameTgt stackT mem
      calleeDefId argsTgt dstTgt targetTgt unwindTgt
    (∀ s', resS = .step s' → ∃ t', resT = .step t' ∧ SimState w s' t') ∧
    (∀ out, resS = .done out → resT = .done out) ∧
    (∀ fk, resS = .fault fk → resT = .fault fk) := by
  intro resS resT
  unfold resS resT evalCallTerminator
  rw [← hCl, ← hProj]
  cases (bbSrc.cleanup || !dstSrc.projection.isEmpty) with
  | true => exact sim_fault_same w .unsupported
  | false =>
    dsimp
    rw [← hDstTy]
    cases Trusted.MirSemantics.getElem? callerBodySrc.locals dstSrc.localId with
    | none => exact sim_fault_same w .unsupported
    | some dstTy =>
      cases hIsCaller : Nat.beq calleeDefId site.callerDefId with
      | false =>
        have hNe := nat_ne_of_beq_false hIsCaller
        rw [w_bodies_getElem?_ne w hNe]
        cases Trusted.MirSemantics.getElem? pSrc.bodies calleeDefId with
        | none => exact sim_fault_same w .unsupported
        | some calleeBody =>
          dsimp
          rw [← hArgsLen]
          cases (!calleeCallAdmitted calleeBody ||
              !Nat.beq argsSrc.length calleeBody.argumentCount) with
          | true => exact sim_fault_same w .unsupported
          | false =>
            dsimp
            cases Trusted.MirSemantics.getElem? calleeBody.locals 0 with
            | none => exact sim_fault_same w .unsupported
            | some calleeRetTy =>
              dsimp
              cases (!MirTy.beq calleeRetTy dstTy) with
              | true => exact sim_fault_same w .unsupported
              | false =>
                dsimp
                let paramTys := (calleeBody.locals.drop 1).take calleeBody.argumentCount
                cases hEvA : evalCallArgs callerBodySrc.locals frameSrc.locals argsSrc paramTys with
                | error fk =>
                  have hEvAT := (hCallArgs paramTys).1 fk hEvA
                  rw [hEvAT]
                  exact sim_fault_same w fk
                | ok pair =>
                  cases pair with
                  | mk argVals locsS =>
                    let ⟨locsT, hEvAT, hSimSt⟩ := (hCallArgs paramTys).2 argVals locsS hEvA
                    rw [hEvAT]; dsimp
                    refine ⟨fun s' hSt => ?_, fun _ h => (by cases h), fun _ h => (by cases h)⟩
                    injection hSt with hEq; subst hEq
                    exact ⟨_, rfl, SimState.nonCaller _ _ _ mem hNe hSimSt⟩
      | true =>
        have hEqId := nat_beq_eq hIsCaller
        subst hEqId
        rw [w.hGetCallerSrc, w_bodies_getElem?_caller w]
        dsimp
        rw [w_calleeCallAdmitted_callerTgt w, ← hArgsLen]
        have hArgCnt : w.callerTgt.argumentCount = w.callerSrc.argumentCount := rfl
        rw [hArgCnt]
        cases (!calleeCallAdmitted w.callerSrc ||
            !Nat.beq argsSrc.length w.callerSrc.argumentCount) with
        | true => exact sim_fault_same w .unsupported
        | false =>
          dsimp
          have hLoc0 : Trusted.MirSemantics.getElem? w.callerTgt.locals 0 =
              Trusted.MirSemantics.getElem? w.callerSrc.locals 0 := by
            have hLocEq : w.callerTgt.locals = w.callerSrc.locals ++ w.calleeSrc.locals := rfl
            rw [hLocEq, getElem?_append_left _ _ _ (w_localBase_pos w)]
          rw [hLoc0]
          cases Trusted.MirSemantics.getElem? w.callerSrc.locals 0 with
          | none => exact sim_fault_same w .unsupported
          | some calleeRetTy =>
            dsimp
            cases (!MirTy.beq calleeRetTy dstTy) with
            | true => exact sim_fault_same w .unsupported
            | false =>
              dsimp
              have hParamEq : (w.callerTgt.locals.drop 1).take w.callerSrc.argumentCount =
                  (w.callerSrc.locals.drop 1).take w.callerSrc.argumentCount :=
                w_callerTgt_paramTys w
              rw [hParamEq]
              let paramTys := (w.callerSrc.locals.drop 1).take w.callerSrc.argumentCount
              cases hEvA : evalCallArgs callerBodySrc.locals frameSrc.locals argsSrc paramTys with
              | error fk =>
                have hEvAT := (hCallArgs paramTys).1 fk hEvA
                rw [hEvAT]
                exact sim_fault_same w fk
              | ok pair =>
                cases pair with
                | mk argVals locsS =>
                  let ⟨locsT, hEvAT, hSimSt⟩ := (hCallArgs paramTys).2 argVals locsS hEvA
                  rw [hEvAT]; dsimp
                  rw [w_initLocalsLoop_callerTgt w argVals]
                  refine ⟨fun s' hSt => ?_, fun _ h => (by cases h), fun _ h => (by cases h)⟩
                  injection hSt with hEq; subst hEq
                  exact ⟨_, rfl, SimState.outerCaller _ _ _ mem rfl
                    (initLocalsLoop_length _ _ _ _)
                    (w_blockBase_pos w)
                    (fun _ _ => Nat.zero_le _) hSimSt⟩

/-! #### `evalStatement` & `evalTerminator` Shape, Prefix-Locality, &
Shift-Right Lemmas -/

private theorem evalStatement_step_shape {body : Body} {frame : FrameState}
    {mem : CallerMemory} {stmt : StatementKind} {s' : State}
    (h : evalStatement body frame mem stmt = .step s') :
    ∃ locs',
      s' = { frames := [{ frame with stmtIdx := frame.stmtIdx + 1, locals := locs' }],
             callerMem := mem } ∧
      locs'.length = frame.locals.length := by
  cases stmt with
  | nop =>
    dsimp [evalStatement] at h; injection h with hEq; subst hEq
    exact ⟨frame.locals, rfl, rfl⟩
  | unsupported => dsimp [evalStatement] at h; cases h
  | storageLive id =>
    dsimp [evalStatement] at h
    cases hT : Trusted.MirSemantics.getElem? body.locals id with
    | none => rw [hT] at h; cases h
    | some ty =>
      rw [hT] at h; dsimp at h
      cases hS : setElem? frame.locals id (liveUninitSlot ty) with
      | none => rw [hS] at h; cases h
      | some locs' =>
        rw [hS] at h; dsimp at h
        injection h with hEq; subst hEq
        exact ⟨locs', rfl, setElem?_length hS⟩
  | storageDead id =>
    dsimp [evalStatement] at h
    cases hZ : Nat.beq id 0 with
    | true => rw [hZ] at h; cases h
    | false =>
      rw [hZ] at h; dsimp at h
      cases hS : setElem? frame.locals id .dead with
      | none => rw [hS] at h; cases h
      | some locs' =>
        rw [hS] at h; dsimp at h
        injection h with hEq; subst hEq
        exact ⟨locs', rfl, setElem?_length hS⟩
  | assign dst rv =>
    dsimp [evalStatement] at h
    cases hP : dst.projection.isEmpty with
    | false => rw [hP] at h; cases h
    | true =>
      rw [hP] at h; dsimp at h
      cases hT : Trusted.MirSemantics.getElem? body.locals dst.localId with
      | none => rw [hT] at h; cases h
      | some dstTy =>
        rw [hT] at h; dsimp at h
        cases hR : evalRvalue body.locals frame.locals dstTy rv with
        | error _ => rw [hR] at h; cases h
        | ok pair =>
          rw [hR] at h; dsimp at h
          cases pair with
          | mk v locs1 =>
            dsimp at h
            cases hW : writePlace locs1 dst.localId dstTy v with
            | error _ => rw [hW] at h; cases h
            | ok locs2 =>
              rw [hW] at h; dsimp at h
              injection h with hEq; subst hEq
              exact ⟨locs2, rfl, (writePlace_length hW).trans (evalRvalue_length hR)⟩

private theorem evalTerminator_step_shape {body : Body} {bb : BasicBlock}
    {frame : FrameState} {mem : CallerMemory} {s' : State}
    (h : evalTerminator body bb frame mem = .step s') :
    ∃ tgt locs',
      s' = { frames := [{ frame with blockIdx := tgt, stmtIdx := 0, locals := locs' }],
             callerMem := mem } ∧
      locs'.length = frame.locals.length ∧
      (∀ bound, terminatorBlocksLt bound bb.terminator = true → tgt < bound) := by
  unfold evalTerminator at h
  cases hTerm : bb.terminator with
  | goto target =>
    rw [hTerm] at h; dsimp [jumpToBlock] at h
    injection h with hEq; subst hEq
    exact ⟨target, frame.locals, rfl, rfl, fun _ hB => nat_blt_lt hB⟩
  | return_ =>
    rw [hTerm] at h; dsimp at h
    cases hCl : bb.cleanup with
    | true => rw [hCl] at h; cases h
    | false =>
      rw [hCl] at h; dsimp at h
      cases h0 : Trusted.MirSemantics.getElem? frame.locals 0 with
      | none => rw [h0] at h; cases h
      | some sl =>
        rw [h0] at h
        cases sl with
        | dead => cases h
        | live ov => cases ov <;> cases h
  | unreachable => rw [hTerm] at h; cases h
  | unwindResume => rw [hTerm] at h; cases h
  | assert _ _ _ _ _ => rw [hTerm] at h; cases h
  | call _ _ _ _ _ => rw [hTerm] at h; cases h
  | unsupported => rw [hTerm] at h; cases h
  | switchInt discr targets =>
    rw [hTerm] at h; dsimp at h
    cases hOp : evalPrimitiveOperand body.locals frame.locals discr with
    | error _ => rw [hOp] at h; cases h
    | ok pair =>
      rw [hOp] at h; dsimp at h
      cases pair with
      | mk discrVal locs1 =>
        dsimp at h
        cases discrVal with
        | scalar sv =>
          dsimp at h
          cases hSw : evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches with
          | error _ => rw [hSw] at h; cases h
          | ok tgt =>
            rw [hSw] at h; dsimp [jumpToBlock] at h
            injection h with hEq; subst hEq
            refine ⟨tgt, locs1, rfl, evalPrimitiveOperand_length hOp, fun bound hB => ?_⟩
            let ⟨hOw, hBrs⟩ := bool_and_true hB
            exact evalSwitchBranches_lt (nat_blt_lt hOw) hBrs hSw
        | bool b =>
          dsimp at h
          cases hSw : evalBoolSwitchBranches b targets.otherwise targets.branches with
          | error _ => rw [hSw] at h; cases h
          | ok tgt =>
            rw [hSw] at h; dsimp [jumpToBlock] at h
            injection h with hEq; subst hEq
            refine ⟨tgt, locs1, rfl, evalPrimitiveOperand_length hOp, fun bound hB => ?_⟩
            let ⟨hOw, hBrs⟩ := bool_and_true hB
            exact evalBoolSwitchBranches_lt (nat_blt_lt hOw) hBrs hSw
        | ptr _ => cases h
        | unit => cases h
        | enumVal _ _ => cases h
        | tuple _ => cases h
        | bytes _ => cases h

private theorem evalStatement_append_left
    {bodySrc bodyTgt : Body} {frame : FrameState}
    {suffix : List LocalSlot} {extraTys : List MirTy}
    {mem : CallerMemory} {stmt : StatementKind}
    (hLocsEq : bodyTgt.locals = bodySrc.locals ++ extraTys)
    (hLen : frame.locals.length = bodySrc.locals.length)
    (hLt : stmtLocalsLt bodySrc.locals.length stmt = true) :
    evalStatement bodyTgt { frame with locals := frame.locals ++ suffix } mem stmt =
      match evalStatement bodySrc frame mem stmt with
      | .step s' =>
        match s'.frames with
        | [f'] => .step { frames := [{ f' with locals := f'.locals ++ suffix }],
                          callerMem := s'.callerMem }
        | _ => .fault .unsupported
      | .done out => .done out
      | .fault fk => .fault fk := by
  cases stmt with
  | nop => rfl
  | unsupported => rfl
  | storageLive id =>
    have hIdLt : id < bodySrc.locals.length := nat_blt_lt hLt
    have hIdLtL : id < frame.locals.length := by rw [hLen]; exact hIdLt
    dsimp [evalStatement]
    rw [hLocsEq, getElem?_append_left _ _ _ hIdLt]
    cases Trusted.MirSemantics.getElem? bodySrc.locals id with
    | none => rfl
    | some ty =>
      dsimp
      rw [setElem?_append_left _ _ _ _ hIdLtL]
      cases setElem? frame.locals id (liveUninitSlot ty) <;> rfl
  | storageDead id =>
    have hIdLt : id < bodySrc.locals.length := nat_blt_lt hLt
    have hIdLtL : id < frame.locals.length := by rw [hLen]; exact hIdLt
    dsimp [evalStatement]
    cases Nat.beq id 0 with
    | true => rfl
    | false =>
      dsimp
      rw [setElem?_append_left _ _ _ _ hIdLtL]
      cases setElem? frame.locals id .dead <;> rfl
  | assign dst rv =>
    let ⟨hDstB, hRvLt⟩ := bool_and_true hLt
    have hDstLt : dst.localId < bodySrc.locals.length := nat_blt_lt hDstB
    dsimp [evalStatement]
    cases dst.projection.isEmpty with
    | false => rfl
    | true =>
      dsimp
      rw [hLocsEq, getElem?_append_left _ _ _ hDstLt]
      cases Trusted.MirSemantics.getElem? bodySrc.locals dst.localId with
      | none => rfl
      | some dstTy =>
        dsimp
        rw [evalRvalue_append_left hLen hRvLt]
        cases hRv : evalRvalue bodySrc.locals frame.locals dstTy rv with
        | error _ => rfl
        | ok pair =>
          cases pair with
          | mk v locs1 =>
            dsimp
            have hDstLt1 : dst.localId < locs1.length := by
              rw [evalRvalue_length hRv, hLen]; exact hDstLt
            rw [writePlace_append_left hDstLt1]
            cases writePlace locs1 dst.localId dstTy v <;> rfl

private theorem evalStatement_shift_right
    {calleeBody bodyTgt : Body} {outerTys : List MirTy}
    {outerLocs : List LocalSlot} {calleeFrame : FrameState}
    {defTgt bbTgt : Nat} {mem : CallerMemory} {stmt : StatementKind}
    (hLocsEq : bodyTgt.locals = outerTys ++ calleeBody.locals)
    (hOLen : outerLocs.length = outerTys.length)
    (hPos : 0 < outerTys.length)
    (hNoSD0 : match stmt with | .storageDead id => !Nat.beq id 0 | _ => true) :
    evalStatement bodyTgt
      { defId := defTgt, blockIdx := bbTgt, stmtIdx := calleeFrame.stmtIdx,
        locals := outerLocs ++ calleeFrame.locals }
      mem (shiftStmt outerTys.length stmt) =
      match evalStatement calleeBody calleeFrame mem stmt with
      | .step s' =>
        match s'.frames with
        | [f'] => .step { frames := [{ defId := defTgt, blockIdx := bbTgt,
                                       stmtIdx := f'.stmtIdx,
                                       locals := outerLocs ++ f'.locals }],
                          callerMem := s'.callerMem }
        | _ => .fault .unsupported
      | .done out => .done out
      | .fault fk => .fault fk := by
  cases stmt with
  | nop => rfl
  | unsupported => rfl
  | storageLive id =>
    dsimp [shiftStmt, evalStatement]
    rw [hLocsEq, getElem?_append_right_add]
    cases Trusted.MirSemantics.getElem? calleeBody.locals id with
    | none => rfl
    | some ty =>
      dsimp
      rw [← hOLen, setElem?_append_right_add]
      cases setElem? calleeFrame.locals id (liveUninitSlot ty) <;> rfl
  | storageDead id =>
    have hIdNe0 : Nat.beq id 0 = false := bool_not_true hNoSD0
    have hShNe0 : Nat.beq (outerTys.length + id) 0 = false :=
      nat_beq_false_of_ne (nat_add_ne_zero_left hPos)
    dsimp [shiftStmt, evalStatement]
    rw [hIdNe0, hShNe0]; dsimp
    rw [← hOLen, setElem?_append_right_add]
    cases setElem? calleeFrame.locals id .dead <;> rfl
  | assign dst rv =>
    dsimp [shiftStmt, shiftPlace, evalStatement]
    cases dst.projection.isEmpty with
    | false => rfl
    | true =>
      dsimp
      rw [hLocsEq, getElem?_append_right_add]
      cases Trusted.MirSemantics.getElem? calleeBody.locals dst.localId with
      | none => rfl
      | some dstTy =>
        dsimp
        rw [evalRvalue_shift_right hOLen]
        cases evalRvalue calleeBody.locals calleeFrame.locals dstTy rv with
        | error _ => rfl
        | ok pair =>
          cases pair with
          | mk v locs1 =>
            dsimp
            rw [← hOLen, writePlace_shift_right]
            cases writePlace locs1 dst.localId dstTy v <;> rfl

private theorem evalTerminator_nonCall_nonReturn_append_left
    {bodySrc bodyTgt : Body} {bb : BasicBlock} {frame : FrameState}
    {suffix : List LocalSlot} {extraTys : List MirTy} {mem : CallerMemory}
    (hLocsEq : bodyTgt.locals = bodySrc.locals ++ extraTys)
    (hLen : frame.locals.length = bodySrc.locals.length)
    (hLt : terminatorLocalsLt bodySrc.locals.length bb.terminator = true)
    (hNotRet : bb.terminator ≠ .return_) :
    evalTerminator bodyTgt bb { frame with locals := frame.locals ++ suffix } mem =
      match evalTerminator bodySrc bb frame mem with
      | .step s' =>
        match s'.frames with
        | [f'] => .step { frames := [{ f' with locals := f'.locals ++ suffix }],
                          callerMem := s'.callerMem }
        | _ => .fault .unsupported
      | .done out => .done out
      | .fault fk => .fault fk := by
  unfold evalTerminator
  cases hTerm : bb.terminator with
  | goto _ => rfl
  | unreachable => rfl
  | unwindResume => rfl
  | assert _ _ _ _ _ => rfl
  | call _ _ _ _ _ => rfl
  | unsupported => rfl
  | return_ => exact False.elim (hNotRet hTerm)
  | switchInt discr targets =>
    rw [hTerm] at hLt
    dsimp [terminatorLocalsLt] at hLt
    dsimp
    rw [hLocsEq, evalPrimitiveOperand_append_left hLen hLt]
    cases evalPrimitiveOperand bodySrc.locals frame.locals discr with
    | error _ => rfl
    | ok pair =>
      cases pair with
      | mk discrVal locs1 =>
        dsimp
        cases discrVal with
        | scalar sv =>
          dsimp
          cases evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches <;> rfl
        | bool b =>
          dsimp
          cases evalBoolSwitchBranches b targets.otherwise targets.branches <;> rfl
        | ptr _ => rfl
        | unit => rfl
        | enumVal _ _ => rfl
        | tuple _ => rfl
        | bytes _ => rfl

private theorem evalTerminator_nonCall_nonReturn_shift_right
    {calleeBody bodyTgt : Body} {outerTys : List MirTy}
    {outerLocs : List LocalSlot} {cbb : BasicBlock} {calleeFrame : FrameState}
    {defTgt blockBase exitBlock : Nat} {unwind : UnwindAction}
    {mem : CallerMemory}
    (hLocsEq : bodyTgt.locals = outerTys ++ calleeBody.locals)
    (hOLen : outerLocs.length = outerTys.length)
    (hNotRet : cbb.terminator ≠ .return_)
    (hNotCall : isNonCallTerminator cbb.terminator = true) :
    evalTerminator bodyTgt
      (shiftCalleeBlock outerTys.length blockBase exitBlock unwind cbb)
      { defId := defTgt, blockIdx := blockBase + calleeFrame.blockIdx,
        stmtIdx := calleeFrame.stmtIdx, locals := outerLocs ++ calleeFrame.locals }
      mem =
      match evalTerminator calleeBody cbb calleeFrame mem with
      | .step s' =>
        match s'.frames with
        | [f'] => .step { frames := [{ defId := defTgt,
                                       blockIdx := blockBase + f'.blockIdx,
                                       stmtIdx := f'.stmtIdx,
                                       locals := outerLocs ++ f'.locals }],
                          callerMem := s'.callerMem }
        | _ => .fault .unsupported
      | .done out => .done out
      | .fault fk => .fault fk := by
  unfold evalTerminator
  dsimp [shiftCalleeBlock]
  cases hTerm : cbb.terminator with
  | goto _ => rfl
  | unreachable => rfl
  | unwindResume => rfl
  | assert _ _ _ _ _ => rfl
  | unsupported => rfl
  | return_ => exact False.elim (hNotRet hTerm)
  | call _ _ _ _ _ => rw [hTerm] at hNotCall; cases hNotCall
  | switchInt discr targets =>
    dsimp [shiftCalleeTerminator, shiftSwitchTargets]
    rw [hLocsEq, evalPrimitiveOperand_shift_right hOLen]
    cases evalPrimitiveOperand calleeBody.locals calleeFrame.locals discr with
    | error _ => rfl
    | ok pair =>
      cases pair with
      | mk discrVal locs1 =>
        dsimp
        cases discrVal with
        | scalar sv =>
          dsimp
          rw [evalSwitchBranches_shift]
          cases evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches <;> rfl
        | bool b =>
          dsimp
          rw [evalBoolSwitchBranches_shift]
          cases evalBoolSwitchBranches b targets.otherwise targets.branches <;> rfl
        | ptr _ => rfl
        | unit => rfl
        | enumVal _ _ => rfl
        | tuple _ => rfl
        | bytes _ => rfl

/-! ### Stage 4 Private Helpers — Slice C3: `step_sim`,
`initStateInterproc_sim`, & Theorem 2 -/

private theorem lift_one_step_sim {site : InlineSite} {pSrc pTgt : Program}
    {w : InlineWitness site pSrc pTgt} {s t : InterprocState}
    (h1 : (∀ s', evalStepInterproc pSrc 0 s = .step s' →
            ∃ t', evalStepInterproc pTgt 0 t = .step t' ∧ SimState w s' t') ∧
          (∀ out, evalStepInterproc pSrc 0 s = .done out →
            evalStepInterproc pTgt 0 t = .done out) ∧
          (∀ fk, evalStepInterproc pSrc 0 s = .fault fk →
            evalStepInterproc pTgt 0 t = .fault fk)) :
    (∀ s', evalStepInterproc pSrc 0 s = .step s' →
      ∃ d t', StepsN pTgt (d + 1) t t' ∧ SimState w s' t') ∧
    (∀ out, evalStepInterproc pSrc 0 s = .done out →
      ∃ d t', StepsN pTgt d t t' ∧ evalStepInterproc pTgt 0 t' = .done out) ∧
    (∀ fk, evalStepInterproc pSrc 0 s = .fault fk →
      ∃ d t', StepsN pTgt d t t' ∧ evalStepInterproc pTgt 0 t' = .fault fk) := by
  let ⟨hS, hD, hF⟩ := h1
  exact ⟨
    fun s' h => let ⟨t', hT, hR⟩ := hS s' h; ⟨0, t', stepsN_one hT, hR⟩,
    fun out h => ⟨0, t, StepsN.zero t, hD out h⟩,
    fun fk h => ⟨0, t, StepsN.zero t, hF fk h⟩
  ⟩

private theorem step_sim_nonCaller {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt)
    (frame : FrameState) (stackS stackT : List CallContinuation)
    (mem : CallerMemory) (hNe : frame.defId ≠ site.callerDefId)
    (hStack : SimStack w stackS stackT) :
    let s := { cur := frame, stack := stackS, callerMem := mem : InterprocState }
    let t := { cur := frame, stack := stackT, callerMem := mem : InterprocState }
    (∀ s', evalStepInterproc pSrc 0 s = .step s' →
      ∃ d t', StepsN pTgt (d + 1) t t' ∧ SimState w s' t') ∧
    (∀ out, evalStepInterproc pSrc 0 s = .done out →
      ∃ d t', StepsN pTgt d t t' ∧ evalStepInterproc pTgt 0 t' = .done out) ∧
    (∀ fk, evalStepInterproc pSrc 0 s = .fault fk →
      ∃ d t', StepsN pTgt d t t' ∧ evalStepInterproc pTgt 0 t' = .fault fk) := by
  intro s t
  apply lift_one_step_sim
  unfold evalStepInterproc; dsimp [s, t]
  rw [w_bodies_getElem?_ne w hNe]
  cases Trusted.MirSemantics.getElem? pSrc.bodies frame.defId with
  | none => exact sim_fault_same w .unsupported
  | some body =>
    dsimp
    cases Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx with
    | none => exact sim_fault_same w .unsupported
    | some bb =>
      dsimp
      cases Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx with
      | some stmt =>
        dsimp
        cases hEv : evalStatement body frame mem stmt with
        | done out =>
          exact ⟨fun _ h => (by cases h), fun _ h => h, fun _ h => (by cases h)⟩
        | fault fk => exact sim_fault_same w fk
        | step sSt =>
          let ⟨locs', hShape, _⟩ := evalStatement_step_shape hEv
          rw [hShape]; dsimp [liftSingleFrameStep]
          refine ⟨fun s' hSt => ?_, fun _ h => (by cases h), fun _ h => (by cases h)⟩
          injection hSt with hEq; subst hEq
          exact ⟨_, rfl, SimState.nonCaller _ stackS stackT mem hNe hStack⟩
      | none =>
        dsimp
        cases Nat.beq frame.stmtIdx bb.statements.length with
        | false => exact sim_fault_same w .unsupported
        | true =>
          dsimp
          cases hTerm : bb.terminator with
          | return_ =>
            exact sim_return_step w rfl rfl rfl hStack
          | call calleeDefId args dst target unwind =>
            exact sim_call_entry_general w rfl rfl rfl
              (fun _ => ⟨fun _ h => h, fun _ locsS h =>
                ⟨locsS, h, SimStack.nonCaller _ stackS stackT hNe hStack⟩⟩) rfl
          | goto _ | switchInt _ _ | unreachable | unwindResume
          | assert _ _ _ _ _ | unsupported =>
            cases hEv : evalTerminator body bb frame mem with
            | done out =>
              exact ⟨fun _ h => (by cases h), fun _ h => h, fun _ h => (by cases h)⟩
            | fault fk => exact sim_fault_same w fk
            | step sSt =>
              let ⟨tgt, locs', hShape, _, _⟩ := evalTerminator_step_shape hEv
              rw [hShape]; dsimp [liftSingleFrameStep]
              refine ⟨fun s' hSt => ?_, fun _ h => (by cases h), fun _ h => (by cases h)⟩
              injection hSt with hEq; subst hEq
              exact ⟨_, rfl, SimState.nonCaller _ stackS stackT mem hNe hStack⟩

private theorem step_sim_outerCaller {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt)
    (frame : FrameState) (stackS stackT : List CallContinuation)
    (mem : CallerMemory)
    (hDef : frame.defId = site.callerDefId)
    (hCLen : frame.locals.length = w.localBase)
    (hBlkLt : frame.blockIdx < w.blockBase)
    (hStmtLe : ∀ bb,
      Trusted.MirSemantics.getElem? w.callerSrc.basicBlocks frame.blockIdx = some bb →
      frame.stmtIdx ≤ bb.statements.length)
    (hStack : SimStack w stackS stackT) :
    let deadSuff := List.replicate w.calleeSrc.locals.length .dead
    let s := { cur := frame, stack := stackS, callerMem := mem : InterprocState }
    let t := { cur := { frame with locals := frame.locals ++ deadSuff },
               stack := stackT, callerMem := mem : InterprocState }
    (∀ s', evalStepInterproc pSrc 0 s = .step s' →
      ∃ d t', StepsN pTgt (d + 1) t t' ∧ SimState w s' t') ∧
    (∀ out, evalStepInterproc pSrc 0 s = .done out →
      ∃ d t', StepsN pTgt d t t' ∧ evalStepInterproc pTgt 0 t' = .done out) ∧
    (∀ fk, evalStepInterproc pSrc 0 s = .fault fk →
      ∃ d t', StepsN pTgt d t t' ∧ evalStepInterproc pTgt 0 t' = .fault fk) := by
  cases frame with
  | mk df blk st locs =>
    dsimp at hDef hCLen hBlkLt hStmtLe
    subst hDef
    let frame : FrameState := { defId := site.callerDefId, blockIdx := blk, stmtIdx := st, locals := locs }
    intro deadSuff s t
    let ⟨bb, hGetBb⟩ := getElem?_some_of_lt w.callerSrc.basicBlocks blk hBlkLt
    have hBbEntry := list_all_getElem? w.hCallerLocBounds hGetBb
    let ⟨hBbStmtsLt, hBbTermLt⟩ := bool_and_true hBbEntry
    have hBbTermBlkLt := list_all_getElem? w.hCallerBlkBounds hGetBb
    cases hIsCall : Nat.beq blk site.callBlock with
    | false =>
      have hNeCall : blk ≠ site.callBlock := nat_ne_of_beq_false hIsCall
      have hGetBbTgt : Trusted.MirSemantics.getElem? w.callerTgt.basicBlocks blk =
          some bb := by
        rw [w_callerTgt_blocks_getElem?_lt_ne w hBlkLt hNeCall]; exact hGetBb
      apply lift_one_step_sim
      unfold evalStepInterproc; dsimp [s, t]
      rw [w.hGetCallerSrc, w_bodies_getElem?_caller w]; dsimp
      rw [hGetBb, hGetBbTgt]; dsimp
      cases hGetSt : Trusted.MirSemantics.getElem? bb.statements st with
      | some stmt =>
        dsimp
        have hSLt : stmtLocalsLt w.callerSrc.locals.length stmt = true :=
          list_all_getElem? hBbStmtsLt hGetSt
        have hEvEq := evalStatement_append_left (bodyTgt := w.callerTgt)
          (frame := frame) (suffix := deadSuff) (extraTys := w.calleeSrc.locals) (mem := mem)
          rfl hCLen hSLt
        dsimp [frame] at hEvEq
        rw [hEvEq]
        cases hEv : evalStatement w.callerSrc frame mem stmt with
        | done out =>
          exact ⟨fun _ h => (by cases h), fun _ h => h, fun _ h => (by cases h)⟩
        | fault fk => exact sim_fault_same w fk
        | step sSt =>
          let ⟨locs', hShape, hLen'⟩ := evalStatement_step_shape hEv
          rw [hShape]; dsimp [liftSingleFrameStep, frame]
          refine ⟨fun s' hSt => ?_, fun _ h => (by cases h), fun _ h => (by cases h)⟩
          injection hSt with hEq; subst hEq
          refine ⟨_, rfl, SimState.outerCaller _ stackS stackT mem rfl
            (hLen'.trans hCLen) hBlkLt ?_ hStack⟩
          intro bb' hBb'
          rw [hGetBb] at hBb'; injection hBb' with hEqB; subst hEqB
          exact Nat.succ_le_of_lt (getElem?_some_lt hGetSt)
      | none =>
        dsimp
        cases Nat.beq st bb.statements.length with
        | false => exact sim_fault_same w .unsupported
        | true =>
          dsimp
          cases hTerm : bb.terminator with
          | return_ =>
            have hRetTy0 : Trusted.MirSemantics.getElem? w.callerSrc.locals 0 =
                Trusted.MirSemantics.getElem? w.callerTgt.locals 0 := by
              have hLocEq : w.callerTgt.locals = w.callerSrc.locals ++ w.calleeSrc.locals := rfl
              rw [hLocEq, getElem?_append_left _ _ _ (w_localBase_pos w)]
            have hRetSl0 : Trusted.MirSemantics.getElem? locs 0 =
                Trusted.MirSemantics.getElem? (locs ++ deadSuff) 0 := by
              rw [getElem?_append_left _ _ _ (by rw [hCLen]; exact w_localBase_pos w)]
            exact sim_return_step w rfl hRetTy0 hRetSl0 hStack
          | call calleeDefId args dst target unwind =>
            rw [hTerm] at hBbTermLt hBbTermBlkLt
            dsimp [terminatorLocalsLt] at hBbTermLt
            let ⟨hArgsLt, hDstLtB⟩ := bool_and_true hBbTermLt
            have hDstLt : dst.localId < w.localBase := nat_blt_lt hDstLtB
            dsimp [terminatorBlocksLt] at hBbTermBlkLt
            have hTgtB := (bool_and_true hBbTermBlkLt).1
            have hTgtLt : ∀ b, target = some b → b < w.blockBase := by
              intro b hB; rw [hB] at hTgtB; exact nat_blt_lt hTgtB
            have hDstTyEq : Trusted.MirSemantics.getElem? w.callerSrc.locals dst.localId =
                Trusted.MirSemantics.getElem? w.callerTgt.locals dst.localId := by
              have hLocEq : w.callerTgt.locals = w.callerSrc.locals ++ w.calleeSrc.locals := rfl
              rw [hLocEq, getElem?_append_left _ _ _ hDstLt]
            refine sim_call_entry_general w rfl rfl hDstTyEq ?_ rfl
            intro paramTys
            have hCallEq : evalCallArgs w.callerTgt.locals (locs ++ deadSuff) args paramTys =
                match evalCallArgs w.callerSrc.locals locs args paramTys with
                | .error k => .error k
                | .ok (vs, locs') => .ok (vs, locs' ++ deadSuff) :=
              evalCallArgs_append_left hCLen hArgsLt
            constructor
            · intro fk hErr; rw [hCallEq, hErr]
            · intro argVals locsS hOk
              rw [hCallEq, hOk]
              let ⟨_, hLenS⟩ := evalCallArgs_length hOk
              exact ⟨locsS ++ deadSuff, rfl,
                SimStack.outerCaller _ stackS stackT rfl (hLenS.trans hCLen)
                  hDstLt hTgtLt hStack⟩
          | goto _ | switchInt _ _ | unreachable | unwindResume
          | assert _ _ _ _ _ | unsupported =>
            have hNotRet : bb.terminator ≠ .return_ := by rw [hTerm]; intro h; cases h
            have hEvEq := evalTerminator_nonCall_nonReturn_append_left
              (bodyTgt := w.callerTgt) (bb := bb) (frame := frame)
              (suffix := deadSuff) (extraTys := w.calleeSrc.locals) (mem := mem)
              rfl hCLen hBbTermLt hNotRet
            dsimp [frame] at hEvEq
            rw [hEvEq]
            cases hEv : evalTerminator w.callerSrc bb frame mem with
            | done out =>
              exact ⟨fun _ h => (by cases h), fun _ h => h, fun _ h => (by cases h)⟩
            | fault fk => exact sim_fault_same w fk
            | step sSt =>
              let ⟨tgt, locs', hShape, hLen', hTgtBound⟩ := evalTerminator_step_shape hEv
              rw [hShape]; dsimp [liftSingleFrameStep, frame]
              refine ⟨fun s' hSt => ?_, fun _ h => (by cases h), fun _ h => (by cases h)⟩
              injection hSt with hEq; subst hEq
              have hTgtLt : tgt < w.blockBase := hTgtBound w.blockBase hBbTermBlkLt
              exact ⟨_, rfl, SimState.outerCaller _ stackS stackT mem rfl
                (hLen'.trans hCLen) hTgtLt (fun _ _ => Nat.zero_le _) hStack⟩
    | true =>
      have hEqCall : blk = site.callBlock := nat_beq_eq hIsCall
      subst hEqCall
      have hBbEq : bb = w.callBb := by
        rw [w.hGetCallBb] at hGetBb
        injection hGetBb with hEq; exact hEq.symm
      subst hBbEq
      have hLeCall : st ≤ w.callBb.statements.length := hStmtLe w.callBb hGetBb
      cases Nat.lt_or_eq_of_le hLeCall with
      | inl hStmtLt =>
        let ⟨stmt, hGetSt⟩ := getElem?_some_of_lt w.callBb.statements st hStmtLt
        have hGetStTgt : Trusted.MirSemantics.getElem? w.callBbTgt.statements st =
            some stmt := by
          have hLt12 : st < (w.callBb.statements ++ w.prologueLiveStmts).length := by
            rw [list_append_length]; exact nat_lt_add_right _ hStmtLt
          dsimp [InlineWitness.callBbTgt]
          rw [getElem?_append_left (w.callBb.statements ++ w.prologueLiveStmts) w.argAssignStmts _ hLt12]
          rw [getElem?_append_left w.callBb.statements w.prologueLiveStmts _ hStmtLt]
          exact hGetSt
        apply lift_one_step_sim
        unfold evalStepInterproc; dsimp [s, t]
        rw [w.hGetCallerSrc, w_bodies_getElem?_caller w]; dsimp
        rw [w.hGetCallBb, w_callerTgt_blocks_getElem?_callBlock w]; dsimp
        rw [hGetSt, hGetStTgt]; dsimp
        have hSLt : stmtLocalsLt w.callerSrc.locals.length stmt = true :=
          list_all_getElem? hBbStmtsLt hGetSt
        have hEvEq := evalStatement_append_left (bodyTgt := w.callerTgt)
          (frame := frame) (suffix := deadSuff) (extraTys := w.calleeSrc.locals) (mem := mem)
          rfl hCLen hSLt
        dsimp [frame] at hEvEq
        rw [hEvEq]
        cases hEv : evalStatement w.callerSrc frame mem stmt with
        | done out =>
          exact ⟨fun _ h => (by cases h), fun _ h => h, fun _ h => (by cases h)⟩
        | fault fk => exact sim_fault_same w fk
        | step sSt =>
          let ⟨locs', hShape, hLen'⟩ := evalStatement_step_shape hEv
          rw [hShape]; dsimp [liftSingleFrameStep, frame]
          refine ⟨fun s' hSt => ?_, fun _ h => (by cases h), fun _ h => (by cases h)⟩
          injection hSt with hEq; subst hEq
          refine ⟨_, rfl, SimState.outerCaller _ stackS stackT mem rfl
            (hLen'.trans hCLen) hBlkLt ?_ hStack⟩
          intro bb' hBb'
          rw [hGetBb] at hBb'; injection hBb' with hEqB; subst hEqB
          exact Nat.succ_le_of_lt hStmtLt
      | inr hStmtEq =>
        subst hStmtEq
        have hSrcEval : evalStepInterproc pSrc 0 s =
            let paramTys := (w.calleeSrc.locals.drop 1).take w.calleeSrc.argumentCount
            match evalCallArgs w.callerSrc.locals locs w.args paramTys with
            | .error k => .fault k
            | .ok (argVals, callerLocsAfter) =>
              .step {
                cur := {
                  defId := site.calleeDefId
                  blockIdx := 0
                  stmtIdx := 0
                  locals := initLocalsLoop w.calleeSrc argVals 0 w.calleeSrc.locals
                }
                stack := {
                  callerFrame := { frame with locals := callerLocsAfter }
                  dst := w.dst
                  target := some w.retBb
                  unwind := w.unwind
                } :: stackS
                callerMem := mem
              } := by
          unfold evalStepInterproc; dsimp [s, frame]
          rw [w.hGetCallerSrc]; dsimp
          rw [w.hGetCallBb]; dsimp
          rw [getElem?_none_of_ge (Nat.le_refl _), nat_beq_refl]; dsimp
          rw [w.hCallTerm]; dsimp [evalCallTerminator]
          rw [w.hCallBbNotCleanup, w.hDstUnproj]; dsimp
          rw [w.hGetDstTy, w.hGetCalleeSrc]; dsimp
          rw [w.hCalleeAdmitted, w.hArgsLen, nat_beq_refl]; dsimp
          rw [w.hGetCalleeRetTy]; dsimp
          have hTyBeq : MirTy.beq w.calleeRetTy w.dstTy = true := by
            rw [w.hRetTyEq]; exact mirTy_beq_refl w.dstTy
          rw [hTyBeq]; rfl
        let ⟨hEntryErr, hEntryOk⟩ := exec_inlined_call_entry w locs hCLen stackT mem
        rw [hSrcEval]
        dsimp
        cases hArgs : evalCallArgs w.callerSrc.locals locs w.args
            ((w.calleeSrc.locals.drop 1).take w.calleeSrc.argumentCount) with
        | error fk0 =>
          dsimp
          refine ⟨fun _ h => (by cases h), fun _ h => (by cases h), fun fk h => ?_⟩
          injection h with hEq; subst hEq
          exact hEntryErr fk0 hArgs
        | ok pair =>
          cases pair with
          | mk argVals callerLocsAfter =>
            dsimp
            refine ⟨fun s' hSt => ?_, fun _ h => (by cases h), fun _ h => (by cases h)⟩
            injection hSt with hEq; subst hEq
            let ⟨d, hSteps⟩ := hEntryOk argVals callerLocsAfter hArgs
            let ⟨_, hAfterLen⟩ := evalCallArgs_length hArgs
            exact ⟨d, _, hSteps,
              SimState.inlinedCallee _ _ stackS stackT mem rfl
                (initLocalsLoop_length _ _ _ _)
                (w_callee_blocks_pos w)
                (fun _ _ => Nat.zero_le _)
                rfl (hAfterLen.trans hCLen) rfl rfl hStack⟩

private theorem step_sim_inlinedCallee {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt)
    (calleeFrame : FrameState) (contOuter : CallContinuation)
    (restS stackT : List CallContinuation) (mem : CallerMemory)
    (hInDef : calleeFrame.defId = site.calleeDefId)
    (hInLen : calleeFrame.locals.length = w.calleeSrc.locals.length)
    (hCbLt : calleeFrame.blockIdx < w.calleeSrc.basicBlocks.length)
    (_hStmtLe : ∀ cbb,
      Trusted.MirSemantics.getElem? w.calleeSrc.basicBlocks calleeFrame.blockIdx = some cbb →
      calleeFrame.stmtIdx ≤ cbb.statements.length)
    (hOutDef : contOuter.callerFrame.defId = site.callerDefId)
    (hOutLen : contOuter.callerFrame.locals.length = w.localBase)
    (hOutDst : contOuter.dst = w.dst)
    (hOutTgt : contOuter.target = some w.retBb)
    (hStack : SimStack w restS stackT) :
    let s := { cur := calleeFrame, stack := contOuter :: restS,
               callerMem := mem : InterprocState }
    let t := { cur := {
                 defId := site.callerDefId
                 blockIdx := w.blockBase + calleeFrame.blockIdx
                 stmtIdx := calleeFrame.stmtIdx
                 locals := contOuter.callerFrame.locals ++ calleeFrame.locals
               }, stack := stackT, callerMem := mem : InterprocState }
    (∀ s', evalStepInterproc pSrc 0 s = .step s' →
      ∃ d t', StepsN pTgt (d + 1) t t' ∧ SimState w s' t') ∧
    (∀ out, evalStepInterproc pSrc 0 s = .done out →
      ∃ d t', StepsN pTgt d t t' ∧ evalStepInterproc pTgt 0 t' = .done out) ∧
    (∀ fk, evalStepInterproc pSrc 0 s = .fault fk →
      ∃ d t', StepsN pTgt d t t' ∧ evalStepInterproc pTgt 0 t' = .fault fk) := by
  intro s t
  let ⟨cbb, hGetCbb⟩ :=
    getElem?_some_of_lt w.calleeSrc.basicBlocks calleeFrame.blockIdx hCbLt
  have hGetCbbTgt : Trusted.MirSemantics.getElem? w.callerTgt.basicBlocks
      (w.blockBase + calleeFrame.blockIdx) =
      some (shiftCalleeBlock w.localBase w.blockBase w.exitBlock w.unwind cbb) := by
    rw [w_callerTgt_blocks_getElem?_callee w hCbLt, hGetCbb]; rfl
  have hShLen : (shiftCalleeBlock w.localBase w.blockBase w.exitBlock w.unwind cbb).statements.length =
      cbb.statements.length := map_length_eq _ _
  have hCbbTermBlkLt := list_all_getElem? w.hCalleeBlkBounds hGetCbb
  cases hGetSt : Trusted.MirSemantics.getElem? cbb.statements calleeFrame.stmtIdx with
  | some stmt =>
    have hGetStTgt : Trusted.MirSemantics.getElem?
        (shiftCalleeBlock w.localBase w.blockBase w.exitBlock w.unwind cbb).statements
        calleeFrame.stmtIdx = some (shiftStmt w.localBase stmt) := by
      dsimp [shiftCalleeBlock]; rw [getElem?_map, hGetSt]; rfl
    have hNoSD0_bool : (fun x : StatementKind =>
        match x with | .storageDead id => !Nat.beq id 0 | _ => true) stmt = true := by
      have hZ := w.hCalleeNoSD0
      unfold bodyHasNoStorageDeadZero at hZ
      have hBbNo := list_all_getElem? hZ hGetCbb
      have hRes := list_all_getElem? hBbNo hGetSt
      exact hRes
    have hNoSD0 : match stmt with | .storageDead id => (!Nat.beq id 0) = true | _ => true = true := by
      cases stmt with
      | storageDead id => exact hNoSD0_bool
      | nop | storageLive _ | assign _ _ | unsupported => rfl
    apply lift_one_step_sim
    unfold evalStepInterproc; dsimp [s, t]
    rw [hInDef, w.hGetCalleeSrc, w_bodies_getElem?_caller w]; dsimp
    rw [hGetCbb, hGetCbbTgt]; dsimp
    rw [hGetSt, hGetStTgt]; dsimp
    have hEvEq := evalStatement_shift_right (calleeBody := w.calleeSrc)
      (bodyTgt := w.callerTgt) (outerTys := w.callerSrc.locals)
      (outerLocs := contOuter.callerFrame.locals) (calleeFrame := calleeFrame)
      (defTgt := site.callerDefId) (bbTgt := w.blockBase + calleeFrame.blockIdx)
      (mem := mem) (stmt := stmt) rfl hOutLen (w_localBase_pos w) hNoSD0
    dsimp [InlineWitness.localBase]
    rw [hEvEq]
    cases hEv : evalStatement w.calleeSrc calleeFrame mem stmt with
    | done out =>
      exact ⟨fun _ h => (by cases h), fun _ h => h, fun _ h => (by cases h)⟩
    | fault fk => exact sim_fault_same w fk
    | step sSt =>
      let ⟨locs', hShape, hLen'⟩ := evalStatement_step_shape hEv
      rw [hShape]; dsimp [liftSingleFrameStep]
      refine ⟨fun s' hSt => ?_, fun _ h => (by cases h), fun _ h => (by cases h)⟩
      injection hSt with hEq; subst hEq
      refine ⟨_, rfl, SimState.inlinedCallee _ contOuter restS stackT mem hInDef
        (hLen'.trans hInLen) hCbLt ?_ hOutDef hOutLen hOutDst hOutTgt hStack⟩
      intro cbb' hCbb'
      rw [hGetCbb] at hCbb'; injection hCbb' with hEqB; subst hEqB
      exact Nat.succ_le_of_lt (getElem?_some_lt hGetSt)
  | none =>
    have hGetStTgt : Trusted.MirSemantics.getElem?
        (shiftCalleeBlock w.localBase w.blockBase w.exitBlock w.unwind cbb).statements
        calleeFrame.stmtIdx = none := by
      dsimp [shiftCalleeBlock]; rw [getElem?_map, hGetSt]; rfl
    cases hLenEq : Nat.beq calleeFrame.stmtIdx cbb.statements.length with
    | false =>
      apply lift_one_step_sim
      unfold evalStepInterproc; dsimp [s, t]
      rw [hInDef, w.hGetCalleeSrc, w_bodies_getElem?_caller w]; dsimp
      rw [hGetCbb, hGetCbbTgt]; dsimp
      rw [hGetSt, hGetStTgt, hShLen, hLenEq]
      exact sim_fault_same w .unsupported
    | true =>
      have hStmtEqLen : calleeFrame.stmtIdx = cbb.statements.length := nat_beq_eq hLenEq
      cases hTerm : cbb.terminator with
      | return_ =>
        cases hCl : cbb.cleanup with
        | true =>
          apply lift_one_step_sim
          unfold evalStepInterproc; dsimp [s, t]
          rw [hInDef, w.hGetCalleeSrc, w_bodies_getElem?_caller w]; dsimp
          rw [hGetCbb, hGetCbbTgt]; dsimp
          rw [hGetSt, hGetStTgt, hShLen, hLenEq]; dsimp
          dsimp [shiftCalleeBlock, shiftCalleeTerminator]
          rw [hTerm]; dsimp
          rw [hCl]; dsimp [evalReturnTerminator]
          rw [hCl]; dsimp
          exact sim_fault_same w .unsupported
        | false =>
          have hSrcRet : evalStepInterproc pSrc 0 s =
              match Trusted.MirSemantics.getElem? calleeFrame.locals 0 with
              | some (.live (some retVal)) =>
                match writePlace contOuter.callerFrame.locals w.dst.localId w.dstTy retVal with
                | .error k => .fault k
                | .ok outerLocs' =>
                  .step {
                    cur := {
                      contOuter.callerFrame with
                      blockIdx := w.retBb
                      stmtIdx := 0
                      locals := outerLocs'
                    }
                    stack := restS
                    callerMem := mem
                  }
              | some (.live none) | some .dead => .fault .undefined
              | none => .fault .unsupported := by
            unfold evalStepInterproc; dsimp [s]
            rw [hInDef, w.hGetCalleeSrc]; dsimp
            rw [hGetCbb]; dsimp
            rw [hGetSt, hLenEq]; dsimp
            rw [hTerm]; dsimp [evalReturnTerminator]
            rw [hCl, hOutDst, w.hDstUnproj]; dsimp
            rw [hOutDef, w.hGetCallerSrc]; dsimp
            rw [w.hGetDstTy, w.hGetCalleeRetTy]; dsimp
            have hTyBeq : MirTy.beq w.calleeRetTy w.dstTy = true := by
              rw [w.hRetTyEq]; exact mirTy_beq_refl w.dstTy
            rw [hTyBeq]; dsimp
            cases Trusted.MirSemantics.getElem? calleeFrame.locals 0 with
            | none => rfl
            | some sl =>
              cases sl with
              | dead => rfl
              | live ov =>
                cases ov with
                | none => rfl
                | some retVal =>
                  dsimp
                  cases writePlace contOuter.callerFrame.locals w.dst.localId w.dstTy retVal with
                  | error _ => rfl
                  | ok _ => dsimp; rw [hOutTgt]
          have hEpi := exec_inlined_return_epilogue w contOuter.callerFrame.locals
            calleeFrame.locals hOutLen hInLen calleeFrame.blockIdx cbb hGetCbb hCl hTerm
            stackT mem
          have hTgtEq : t = {
              cur := {
                defId := site.callerDefId
                blockIdx := w.blockBase + calleeFrame.blockIdx
                stmtIdx := cbb.statements.length
                locals := contOuter.callerFrame.locals ++ calleeFrame.locals
              }
              stack := stackT
              callerMem := mem
            } := by
            dsimp [t]; rw [hStmtEqLen]
          rw [hSrcRet, hTgtEq]
          cases hSl0 : Trusted.MirSemantics.getElem? calleeFrame.locals 0 with
          | none =>
            have hGe0 := getElem?_none_ge hSl0
            rw [hInLen] at hGe0
            exact False.elim (Nat.not_lt_of_ge hGe0 (w_callee_locals_pos w))
          | some sl =>
            rw [hSl0] at hEpi
            cases sl with
            | dead =>
              dsimp at hEpi; dsimp
              refine ⟨fun _ h => (by cases h), fun _ h => (by cases h), fun fk h => ?_⟩
              injection h with hEq; subst hEq; exact hEpi
            | live ov =>
              cases ov with
              | none =>
                dsimp at hEpi; dsimp
                refine ⟨fun _ h => (by cases h), fun _ h => (by cases h), fun fk h => ?_⟩
                injection h with hEq; subst hEq; exact hEpi
              | some retVal =>
                dsimp at hEpi; dsimp
                cases hWr : writePlace contOuter.callerFrame.locals w.dst.localId w.dstTy retVal with
                | error fk0 =>
                  rw [hWr] at hEpi; dsimp at hEpi; dsimp
                  refine ⟨fun _ h => (by cases h), fun _ h => (by cases h), fun fk h => ?_⟩
                  injection h with hEq; subst hEq; exact hEpi
                | ok outerLocs' =>
                  rw [hWr] at hEpi; dsimp at hEpi; dsimp
                  let ⟨d, hSteps⟩ := hEpi
                  refine ⟨fun s' hSt => ?_, fun _ h => (by cases h), fun _ h => (by cases h)⟩
                  injection hSt with hEq; subst hEq
                  have hFrameEq : ({
                      cur := {
                        defId := site.callerDefId
                        blockIdx := w.retBb
                        stmtIdx := 0
                        locals := outerLocs' ++ List.replicate w.calleeSrc.locals.length .dead
                      }
                      stack := stackT
                      callerMem := mem
                    } : InterprocState) = {
                      cur := {
                        { contOuter.callerFrame with
                          blockIdx := w.retBb, stmtIdx := 0, locals := outerLocs' } with
                        locals := outerLocs' ++ List.replicate w.calleeSrc.locals.length .dead
                      }
                      stack := stackT
                      callerMem := mem
                    } := by
                    cases contOuter with
                    | mk cf _ _ _ =>
                      cases cf with
                      | mk df _ _ _ =>
                        dsimp at hOutDef
                        rw [hOutDef]
                  rw [hFrameEq] at hSteps
                  exact ⟨d, _, hSteps,
                    SimState.outerCaller _ restS stackT mem hOutDef
                      ((writePlace_length hWr).trans hOutLen)
                      (w_retBb_lt w) (fun _ _ => Nat.zero_le _) hStack⟩
      | call f cArgs cDst cTarget cUnwind =>
        rw [hTerm] at hCbbTermBlkLt
        dsimp [terminatorBlocksLt] at hCbbTermBlkLt
        have hCTgtB := (bool_and_true hCbbTermBlkLt).1
        have hCTgtLt : ∀ b, cTarget = some b → b < w.calleeSrc.basicBlocks.length := by
          intro b hB; rw [hB] at hCTgtB; exact nat_blt_lt hCTgtB
        apply lift_one_step_sim
        unfold evalStepInterproc; dsimp [s, t]
        rw [hInDef, w.hGetCalleeSrc, w_bodies_getElem?_caller w]; dsimp
        rw [hGetCbb, hGetCbbTgt]; dsimp
        rw [hGetSt, hGetStTgt, hShLen, hLenEq]; dsimp
        dsimp [shiftCalleeBlock, shiftCalleeTerminator]
        rw [hTerm]; dsimp
        have hDstTyEq : Trusted.MirSemantics.getElem? w.calleeSrc.locals cDst.localId =
            Trusted.MirSemantics.getElem? w.callerTgt.locals (shiftPlace w.localBase cDst).localId := by
          have hLocEq : w.callerTgt.locals = w.callerSrc.locals ++ w.calleeSrc.locals := rfl
          rw [hLocEq]
          change Trusted.MirSemantics.getElem? w.calleeSrc.locals cDst.localId =
            Trusted.MirSemantics.getElem? (w.callerSrc.locals ++ w.calleeSrc.locals)
              (w.callerSrc.locals.length + cDst.localId)
          rw [getElem?_append_right_add]
        have hArgsLenEq : cArgs.length = (cArgs.map (shiftOperand w.localBase)).length :=
          (map_length_eq _ _).symm
        refine sim_call_entry_general w rfl rfl hDstTyEq ?_ hArgsLenEq
        intro paramTys
        have hCallEq := evalCallArgs_shift_right (outerTys := w.callerSrc.locals)
          (calleeTys := w.calleeSrc.locals) (outerLocs := contOuter.callerFrame.locals)
          (calleeLocs := calleeFrame.locals) (args := cArgs) (paramTys := paramTys) hOutLen
        constructor
        · intro fk hErr
          dsimp [InlineWitness.callerTgt, InlineWitness.localBase]
          rw [hCallEq, hErr]
        · intro argVals locsS hOk
          dsimp [InlineWitness.callerTgt, InlineWitness.localBase]
          rw [hCallEq, hOk]
          let ⟨_, hLenS⟩ := evalCallArgs_length hOk
          exact ⟨contOuter.callerFrame.locals ++ locsS, rfl,
            SimStack.splicedCallee _ contOuter restS stackT
              (w.blockBase + calleeFrame.blockIdx) calleeFrame.stmtIdx
              (mapInlinedUnwind w.blockBase w.unwind cbb.cleanup cUnwind)
              hInDef (hLenS.trans hInLen) hCTgtLt
              hOutDef hOutLen hOutDst hOutTgt hStack⟩
      | goto _ | switchInt _ _ | unreachable | unwindResume
      | assert _ _ _ _ _ | unsupported =>
        have hNotRet : cbb.terminator ≠ .return_ := by rw [hTerm]; intro h; cases h
        have hNotCall : isNonCallTerminator cbb.terminator = true := by rw [hTerm]; rfl
        apply lift_one_step_sim
        unfold evalStepInterproc; dsimp [s, t]
        rw [hInDef, w.hGetCalleeSrc, w_bodies_getElem?_caller w]; dsimp
        rw [hGetCbb, hGetCbbTgt]; dsimp
        rw [hGetSt, hGetStTgt, hShLen, hLenEq]; dsimp
        dsimp [shiftCalleeBlock, shiftCalleeTerminator]
        rw [hTerm]; dsimp
        have hEvEq := evalTerminator_nonCall_nonReturn_shift_right
          (calleeBody := w.calleeSrc) (bodyTgt := w.callerTgt)
          (outerTys := w.callerSrc.locals) (outerLocs := contOuter.callerFrame.locals)
          (cbb := cbb) (calleeFrame := calleeFrame) (defTgt := site.callerDefId)
          (blockBase := w.blockBase) (exitBlock := w.exitBlock) (unwind := w.unwind)
          (mem := mem) rfl hOutLen hNotRet hNotCall
        dsimp [shiftCalleeBlock] at hEvEq
        rw [hTerm] at hEvEq
        dsimp [shiftCalleeTerminator] at hEvEq
        dsimp [InlineWitness.localBase]
        rw [hEvEq]
        cases hEv : evalTerminator w.calleeSrc cbb calleeFrame mem with
        | done out =>
          exact ⟨fun _ h => (by cases h), fun _ h => h, fun _ h => (by cases h)⟩
        | fault fk => exact sim_fault_same w fk
        | step sSt =>
          let ⟨tgt, locs', hShape, hLen', hTgtBound⟩ := evalTerminator_step_shape hEv
          rw [hShape]; dsimp [liftSingleFrameStep]
          refine ⟨fun s' hSt => ?_, fun _ h => (by cases h), fun _ h => (by cases h)⟩
          injection hSt with hEq; subst hEq
          have hTgtLt : tgt < w.calleeSrc.basicBlocks.length :=
            hTgtBound w.calleeSrc.basicBlocks.length hCbbTermBlkLt
          exact ⟨_, rfl, SimState.inlinedCallee _ contOuter restS stackT mem
            hInDef (hLen'.trans hInLen) hTgtLt (fun _ _ => Nat.zero_le _)
            hOutDef hOutLen hOutDst hOutTgt hStack⟩

private theorem step_sim_all {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt) (s t : InterprocState)
    (hSim : SimState w s t) :
    (∀ s', evalStepInterproc pSrc 0 s = .step s' →
      ∃ d t', StepsN pTgt (d + 1) t t' ∧ SimState w s' t') ∧
    (∀ out, evalStepInterproc pSrc 0 s = .done out →
      ∃ d t', StepsN pTgt d t t' ∧ evalStepInterproc pTgt 0 t' = .done out) ∧
    (∀ fk, evalStepInterproc pSrc 0 s = .fault fk →
      ∃ d t', StepsN pTgt d t t' ∧ evalStepInterproc pTgt 0 t' = .fault fk) := by
  cases hSim with
  | nonCaller frame stackS stackT mem hNe hStack =>
    exact step_sim_nonCaller w frame stackS stackT mem hNe hStack
  | outerCaller frame stackS stackT mem hDef hCLen hBlkLt hStmtLe hStack =>
    exact step_sim_outerCaller w frame stackS stackT mem hDef hCLen hBlkLt hStmtLe hStack
  | inlinedCallee calleeFrame contOuter restS stackT mem hInDef hInLen hCbLt hStmtLe
      hOutDef hOutLen hOutDst hOutTgt hStack =>
    exact step_sim_inlinedCallee w calleeFrame contOuter restS stackT mem hInDef hInLen
      hCbLt hStmtLe hOutDef hOutLen hOutDst hOutTgt hStack

/-! #### `initStateInterproc` Simulation & Theorem 2 -/

private theorem initStateInterproc_sim {site : InlineSite} {pSrc pTgt : Program}
    (w : InlineWitness site pSrc pTgt) (q : Query) :
    (∀ k, initStateInterproc pSrc q = .error k ↔ initStateInterproc pTgt q = .error k) ∧
    (∀ s₀, initStateInterproc pSrc q = .ok s₀ →
      ∃ t₀, initStateInterproc pTgt q = .ok t₀ ∧ SimState w s₀ t₀) := by
  have hPw : pTgt.pointerWidthBits = pSrc.pointerWidthBits := by rw [w.hPTgt]
  have hVer : pTgt.mirProfileVersion = pSrc.mirProfileVersion := by rw [w.hPTgt]
  have hEnt : pTgt.entryDefId = pSrc.entryDefId := by rw [w.hPTgt]
  cases hIsCaller : Nat.beq pSrc.entryDefId site.callerDefId with
  | false =>
    have hNe : pSrc.entryDefId ≠ site.callerDefId := nat_ne_of_beq_false hIsCaller
    have hInitEq : initState pTgt q = initState pSrc q := by
      unfold initState
      rw [hPw, hVer, hEnt, w_bodies_getElem?_ne w hNe]
    have hInitIEq : initStateInterproc pTgt q = initStateInterproc pSrc q := by
      unfold initStateInterproc; rw [hInitEq]
    constructor
    · intro k; rw [hInitIEq]
    · intro s₀ hOk
      rw [hInitIEq]
      refine ⟨s₀, hOk, ?_⟩
      unfold initStateInterproc at hOk
      cases hInit : initState pSrc q with
      | error _ => rw [hInit] at hOk; cases hOk
      | ok st₀ =>
        rw [hInit] at hOk; dsimp at hOk
        have hDefEq : ∃ fr₀, st₀.frames = [fr₀] ∧ fr₀.defId = pSrc.entryDefId := by
          unfold initState at hInit
          cases h1 : (!Nat.beq pSrc.pointerWidthBits 64 || !Nat.beq pSrc.mirProfileVersion 1) with
          | true => rw [h1] at hInit; cases hInit
          | false =>
            rw [h1] at hInit; dsimp at hInit
            cases h2 : (!q.callerMem.allocations.isEmpty) with
            | true => rw [h2] at hInit; cases hInit
            | false =>
              rw [h2] at hInit; dsimp at hInit
              cases h3 : Trusted.MirSemantics.getElem? pSrc.bodies pSrc.entryDefId with
              | none => rw [h3] at hInit; cases hInit
              | some body =>
                rw [h3] at hInit; dsimp at hInit
                cases h4 : body.basicBlocks.isEmpty with
                | true => rw [h4] at hInit; cases hInit
                | false =>
                  rw [h4] at hInit; dsimp at hInit
                  cases h5 : (!Nat.blt body.argumentCount body.locals.length) with
                  | true => rw [h5] at hInit; cases hInit
                  | false =>
                    rw [h5] at hInit; dsimp at hInit
                    cases h6 : (!storageAnnotationsInBounds body) with
                    | true => rw [h6] at hInit; cases hInit
                    | false =>
                      rw [h6] at hInit; dsimp at hInit
                      cases h7 : (!body.locals.all isSupportedScalarOrUnitTy) with
                      | true => rw [h7] at hInit; cases hInit
                      | false =>
                        rw [h7] at hInit; dsimp at hInit
                        cases h8 : (!checkArgsMatch q.args ((body.locals.drop 1).take body.argumentCount)) with
                        | true => rw [h8] at hInit; cases hInit
                        | false =>
                          rw [h8] at hInit; dsimp at hInit
                          injection hInit with hEq; subst hEq
                          exact ⟨_, rfl, rfl⟩
        let ⟨fr₀, hFr₀, hFrDef⟩ := hDefEq
        unfold embedState at hOk
        rw [hFr₀] at hOk; dsimp at hOk
        injection hOk with hS0; subst hS0
        exact SimState.nonCaller fr₀ [] [] st₀.callerMem (by rw [hFrDef]; exact hNe) SimStack.nil
  | true =>
    have hEqEnt : pSrc.entryDefId = site.callerDefId := nat_beq_eq hIsCaller
    have hEntT : pTgt.entryDefId = site.callerDefId := hEnt.trans hEqEnt
    unfold initStateInterproc initState
    rw [hPw, hVer, hEntT, hEqEnt]
    cases (!Nat.beq pSrc.pointerWidthBits 64 || !Nat.beq pSrc.mirProfileVersion 1) with
    | true => exact ⟨fun _ => Iff.rfl, fun _ h => (by cases h)⟩
    | false =>
      dsimp
      cases (!q.callerMem.allocations.isEmpty) with
      | true => exact ⟨fun _ => Iff.rfl, fun _ h => (by cases h)⟩
      | false =>
        dsimp
        rw [w.hGetCallerSrc, w_bodies_getElem?_caller w]; dsimp
        let ⟨hE1, hE2⟩ := w_callerTgt_basicBlocks_nonEmpty w
        let ⟨hA1, hA2⟩ := w_callerTgt_argLt w
        have hStS := storageAnnotationsInBounds_of_bodyAllLocalsInBounds w.hCallerLocBounds
        have hStT := w_storageAnnotationsInBounds_callerTgt w
        rw [hE1, hE2, hA1, hA2, hStT, hStS, w_callerTgt_supported_tys w]
        dsimp
        cases (!w.callerSrc.locals.all isSupportedScalarOrUnitTy) with
        | true => exact ⟨fun _ => Iff.rfl, fun _ h => (by cases h)⟩
        | false =>
          dsimp
          rw [w_callerTgt_paramTys w]
          cases (!checkArgsMatch q.args
              ((w.callerSrc.locals.drop 1).take w.callerSrc.argumentCount)) with
          | true => exact ⟨fun _ => Iff.rfl, fun _ h => (by cases h)⟩
          | false =>
            dsimp [embedState]
            rw [w_initLocalsLoop_callerTgt w q.args]
            constructor
            · intro _; exact ⟨fun h => (by cases h), fun h => (by cases h)⟩
            · intro s₀ hOk
              injection hOk with hEq; subst hEq
              exact ⟨_, rfl,
                SimState.outerCaller _ [] [] q.callerMem rfl
                  (initLocalsLoop_length _ _ _ _)
                  (w_blockBase_pos w)
                  (fun _ _ => Nat.zero_le _) SimStack.nil⟩

private theorem mirInlineCallSite_apply_query_iff {site : InlineSite} {pSrc pTgt : Program}
    (hApply : applyMirInlineCallSite site pSrc = some pTgt) (q : Query) :
    (WellFormedInterproc pTgt q ↔ WellFormedInterproc pSrc q) ∧
    (∀ out : TerminalOut,
      BehaviorInterproc pTgt q out ↔ BehaviorInterproc pSrc q out) ∧
    (∀ k : FaultKind,
      ReachesResultInterproc pTgt q (.fault k) ↔
        ReachesResultInterproc pSrc q (.fault k)) ∧
    (DivergesInterproc pTgt q ↔ DivergesInterproc pSrc q) := by
  let ⟨w⟩ := extract_inlineWitness hApply
  let ⟨hInitErr, hInitOk⟩ := initStateInterproc_sim w q
  exact forward_expansion_sim_query_iff hInitErr hInitOk (step_sim_all w)

private theorem mirInlineCallSite_apply_sound {site : InlineSite} {pSrc pTgt : Program}
    (hApply : applyMirInlineCallSite site pSrc = some pTgt) :
    FullSemanticEquivInterproc pSrc pTgt := by
  let ⟨w⟩ := extract_inlineWitness hApply
  have hQ : ∀ q : Query,
      (WellFormedInterproc pTgt q ↔ WellFormedInterproc pSrc q) ∧
      (∀ out : TerminalOut,
        BehaviorInterproc pTgt q out ↔ BehaviorInterproc pSrc q out) ∧
      (∀ k : FaultKind,
        ReachesResultInterproc pTgt q (.fault k) ↔
          ReachesResultInterproc pSrc q (.fault k)) ∧
      (DivergesInterproc pTgt q ↔ DivergesInterproc pSrc q) :=
    fun q => mirInlineCallSite_apply_query_iff hApply q
  refine ⟨hQ, ?_, ?_⟩
  · intro q post
    let ⟨hWf, hBeh, _, _⟩ := hQ q
    unfold SatisfiesPostInterproc
    constructor
    · intro ⟨hW, hP⟩
      exact ⟨hWf.mp hW, fun out hB => hP out ((hBeh out).mpr hB)⟩
    · intro ⟨hW, hP⟩
      exact ⟨hWf.mpr hW, fun out hB => hP out ((hBeh out).mp hB)⟩
  · intro defId bSrc bTgt safetyPre hGetS hGetT
    have hEntryApply := w_apply_entryProg hApply defId
    have hWfEntry : ∀ args : List Val,
        WellFormedInterproc (entryProgForBody pTgt defId) { args := args } ↔
          WellFormedInterproc (entryProgForBody pSrc defId) { args := args } :=
      fun args => (mirInlineCallSite_apply_query_iff hEntryApply { args := args }).1
    cases hIsCaller : Nat.beq defId site.callerDefId with
    | false =>
      have hNe := nat_ne_of_beq_false hIsCaller
      rw [w_bodies_getElem?_ne w hNe, hGetS] at hGetT
      injection hGetT with hBEq; subst hBEq
      have hAdmEq : BodyStaticAdmitted pTgt bSrc = BodyStaticAdmitted pSrc bSrc := by
        have hPw : pTgt.pointerWidthBits = pSrc.pointerWidthBits := by rw [w.hPTgt]
        have hVer : pTgt.mirProfileVersion = pSrc.mirProfileVersion := by rw [w.hPTgt]
        unfold BodyStaticAdmitted; rw [hPw, hVer]
      unfold BodyVerifiedInterproc
      constructor
      · intro ⟨_, hAdm, hArgs⟩
        refine ⟨hGetS, by rw [← hAdmEq]; exact hAdm, fun args hV hS => ?_⟩
        exact (hWfEntry args).mp (hArgs args hV hS)
      · intro ⟨_, hAdm, hArgs⟩
        refine ⟨by rw [w_bodies_getElem?_ne w hNe]; exact hGetS,
          by rw [hAdmEq]; exact hAdm, fun args hV hS => ?_⟩
        exact (hWfEntry args).mpr (hArgs args hV hS)
    | true =>
      have hEqId := nat_beq_eq hIsCaller; subst hEqId
      rw [w.hGetCallerSrc] at hGetS; injection hGetS with hBS; subst hBS
      rw [w_bodies_getElem?_caller w] at hGetT; injection hGetT with hBT; subst hBT
      have hAdmEq := w_bodyStaticAdmitted_callerTgt w
      have hValidEq : ∀ args : List Val,
          ValidEntryArgs w.callerTgt args ↔ ValidEntryArgs w.callerSrc args := by
        intro args; unfold ValidEntryArgs; rw [w_callerTgt_paramTys w]
      have hUnsafeEq : w.callerTgt.isUnsafe = w.callerSrc.isUnsafe := rfl
      unfold BodyVerifiedInterproc
      constructor
      · intro ⟨_, hAdm, hArgs⟩
        refine ⟨w.hGetCallerSrc, by rw [← hAdmEq]; exact hAdm, fun args hV hS => ?_⟩
        exact (hWfEntry args).mp
          (hArgs args ((hValidEq args).mpr hV) (by rw [hUnsafeEq]; exact hS))
      · intro ⟨_, hAdm, hArgs⟩
        refine ⟨w_bodies_getElem?_caller w, by rw [hAdmEq]; exact hAdm, fun args hV hS => ?_⟩
        exact (hWfEntry args).mpr
          (hArgs args ((hValidEq args).mp hV) (by rw [← hUnsafeEq]; exact hS))

private theorem mirInlineCallSite_sound_bidirectional_iff_priv
    (site : InlineSite) (pSrc pTgt : Program)
    (hSite : checkMirInlineCallSite site pSrc pTgt = true) :
    FullSemanticEquivInterproc pSrc pTgt := by
  unfold checkMirInlineCallSite at hSite
  cases hApp : applyMirInlineCallSite site pSrc with
  | none => rw [hApp] at hSite; cases hSite
  | some pOut =>
    rw [hApp] at hSite
    have hEq : pOut = pTgt := programEq_eq hSite
    subst hEq
    exact mirInlineCallSite_apply_sound hApp

/-! ### Stage 4 Private Helpers — Slice D: Theorems 3, 4, & 5 -/

private abbrev ProgramMetaEq (p₁ p₂ : Program) : Prop :=
  p₂.pointerWidthBits = p₁.pointerWidthBits ∧
  p₂.mirProfileVersion = p₁.mirProfileVersion ∧
  p₂.entryDefId = p₁.entryDefId ∧
  p₂.scope = p₁.scope ∧
  p₂.bodies.length = p₁.bodies.length ∧
  p₂.bodies.map (fun b => b.identity) = p₁.bodies.map (fun b => b.identity)

private theorem programMetaEq_refl (p : Program) : ProgramMetaEq p p :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem programMetaEq_trans {p₁ p₂ p₃ : Program}
    (h12 : ProgramMetaEq p₁ p₂) (h23 : ProgramMetaEq p₂ p₃) :
    ProgramMetaEq p₁ p₃ :=
  ⟨h23.1.trans h12.1,
   h23.2.1.trans h12.2.1,
   h23.2.2.1.trans h12.2.2.1,
   h23.2.2.2.1.trans h12.2.2.2.1,
   h23.2.2.2.2.1.trans h12.2.2.2.2.1,
   h23.2.2.2.2.2.trans h12.2.2.2.2.2⟩

private theorem list_identities_of_rel {xs ys : List Body}
    (h : listRel (fun b₁ b₂ => stringBeq b₁.identity b₂.identity) xs ys = true) :
    ys.length = xs.length ∧
    ys.map (fun b => b.identity) = xs.map (fun b => b.identity) := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact ⟨rfl, rfl⟩
    | cons _ _ => cases h
  | cons x rx ih =>
    cases ys with
    | nil => cases h
    | cons y ry =>
      dsimp [listRel] at h
      let ⟨hId, hRest⟩ := bool_and_true h
      let ⟨hLen, hMap⟩ := ih hRest
      have hIdEq : y.identity = x.identity := (stringBeq_eq hId).symm
      dsimp [List.length, List.map]
      rw [hLen, hIdEq, hMap]
      exact ⟨rfl, rfl⟩

private theorem programMetaEq_of_compat {p₁ p₂ : Program}
    (h : ProgramMetadataCompat p₁ p₂ = true) : ProgramMetaEq p₁ p₂ := by
  unfold ProgramMetadataCompat at h
  let ⟨hHdr, hBodies⟩ := bool_and_true h
  let ⟨hPw, hVer, hEnt, hSc⟩ := programHeaderEq_elim hHdr
  let ⟨hLen, hMap⟩ := list_identities_of_rel hBodies
  exact ⟨hPw.symm, hVer.symm, hEnt.symm, hSc.symm, hLen, hMap⟩

private theorem list_isEmpty_eq_of_length_eq {α : Type} {xs ys : List α}
    (hLen : xs.length = ys.length) : xs.isEmpty = ys.isEmpty := by
  cases xs with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases hLen
  | cons _ _ =>
    cases ys with
    | nil => cases hLen
    | cons _ _ => rfl

private theorem body_identity_eq_of_map_eq {bs₁ bs₂ : List Body} {defId : DefId}
    {b₁ b₂ : Body}
    (hMap : bs₂.map (fun b => b.identity) = bs₁.map (fun b => b.identity))
    (h1 : Trusted.MirSemantics.getElem? bs₁ defId = some b₁)
    (h2 : Trusted.MirSemantics.getElem? bs₂ defId = some b₂) :
    b₂.identity = b₁.identity := by
  have hGet := congrArg (fun xs => Trusted.MirSemantics.getElem? xs defId) hMap
  rw [getElem?_map, getElem?_map, h2, h1] at hGet
  dsimp [Option.map] at hGet
  injection hGet

private theorem fullSemanticEquivInterproc_refl (p : Program) :
    FullSemanticEquivInterproc p p := by
  refine ⟨fun _ => ⟨Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, Iff.rfl⟩,
          fun _ _ => Iff.rfl, ?_⟩
  intro defId b₁ b₂ _ h1 h2
  rw [h1] at h2
  injection h2 with hEq
  subst hEq
  exact Iff.rfl

private theorem fullSemanticEquivInterproc_trans {p₁ p₂ p₃ : Program}
    (hLen12 : p₂.bodies.length = p₁.bodies.length)
    (h12 : FullSemanticEquivInterproc p₁ p₂)
    (h23 : FullSemanticEquivInterproc p₂ p₃) :
    FullSemanticEquivInterproc p₁ p₃ := by
  let ⟨hQ12, hPost12, hBody12⟩ := h12
  let ⟨hQ23, hPost23, hBody23⟩ := h23
  refine ⟨?_, ?_, ?_⟩
  · intro q
    let ⟨hWf12, hBeh12, hF12, hDiv12⟩ := hQ12 q
    let ⟨hWf23, hBeh23, hF23, hDiv23⟩ := hQ23 q
    exact ⟨hWf23.trans hWf12,
           fun out => (hBeh23 out).trans (hBeh12 out),
           fun k => (hF23 k).trans (hF12 k),
           hDiv23.trans hDiv12⟩
  · intro q post
    exact (hPost23 q post).trans (hPost12 q post)
  · intro defId b₁ b₃ safetyPre hGet1 hGet3
    have hLt2 : defId < p₂.bodies.length := by
      rw [hLen12]; exact getElem?_some_lt hGet1
    let ⟨b₂, hGet2⟩ := getElem?_some_of_lt p₂.bodies defId hLt2
    exact (hBody23 defId b₂ b₃ safetyPre hGet2 hGet3).trans
      (hBody12 defId b₁ b₂ safetyPre hGet1 hGet2)

private theorem applyMirInlineTrace_sound_and_meta (inlineTrace : InlineTrace) :
    ∀ {pSrc pOut : Program},
      applyMirInlineTrace inlineTrace pSrc = some pOut →
      FullSemanticEquivInterproc pSrc pOut ∧
      ProgramMetaEq pSrc pOut ∧
      (∀ u : DefId,
        applyMirInlineTrace inlineTrace (unitProgForDef pSrc u) =
          some (unitProgForDef pOut u)) := by
  induction inlineTrace with
  | nil =>
    intro pSrc pOut hApply
    dsimp [applyMirInlineTrace] at hApply
    injection hApply with hEq
    subst hEq
    exact ⟨fullSemanticEquivInterproc_refl pSrc, programMetaEq_refl pSrc,
           fun _ => rfl⟩
  | cons site rest ih =>
    intro pSrc pOut hApply
    dsimp [applyMirInlineTrace] at hApply
    cases hStep : applyMirInlineCallSite site pSrc with
    | none => rw [hStep] at hApply; cases hApply
    | some pMid =>
      rw [hStep] at hApply
      let ⟨w⟩ := extract_inlineWitness hStep
      have hEq1 := mirInlineCallSite_apply_sound hStep
      have hMeta1 : ProgramMetaEq pSrc pMid := w_metadata w
      have hUnit1 := w_apply_unitProg hStep
      let ⟨hEq2, hMeta2, hUnit2⟩ := ih hApply
      refine ⟨fullSemanticEquivInterproc_trans hMeta1.2.2.2.2.1 hEq1 hEq2,
              programMetaEq_trans hMeta1 hMeta2, ?_⟩
      intro u
      dsimp [applyMirInlineTrace]
      rw [hUnit1 u]
      exact hUnit2 u

/-- Private proof of Theorem 3 (`mirInlineTrace_sound_bidirectional_iff`). -/
private theorem mirInlineTrace_sound_bidirectional_iff_priv
    (inlineTrace : InlineTrace) (pSrc pTgt : Program)
    (hTrace : checkMirInlineTrace inlineTrace pSrc pTgt = true) :
    FullSemanticEquivInterproc pSrc pTgt := by
  unfold checkMirInlineTrace at hTrace
  cases hApp : applyMirInlineTrace inlineTrace pSrc with
  | none => rw [hApp] at hTrace; cases hTrace
  | some pOut =>
    rw [hApp] at hTrace
    have hEq : pOut = pTgt := programEq_eq hTrace
    subst hEq
    exact (applyMirInlineTrace_sound_and_meta inlineTrace hApp).1

private theorem programVerifiedInterproc_iff_of_equiv_meta
    {p₁ p₂ : Program} {specs : Specs}
    (hEq : FullSemanticEquivInterproc p₁ p₂)
    (hMeta : ProgramMetaEq p₁ p₂)
    (hSpec : SpecsPropertyInvariant specs) :
    ProgramVerifiedInterproc p₁ specs ↔ ProgramVerifiedInterproc p₂ specs := by
  let ⟨hPw, hVer, hEnt, _, hLen, hIds⟩ := hMeta
  have hEmptyEq : p₂.bodies.isEmpty = p₁.bodies.isEmpty :=
    list_isEmpty_eq_of_length_eq hLen
  have hUniqEq : bodiesHaveUniqueIdentities p₂.bodies =
      bodiesHaveUniqueIdentities p₁.bodies :=
    bodiesHaveUniqueIdentities_eq_of_map_id hIds
  have hPropIff := hSpec p₁ p₂ hEq
  unfold ProgramVerifiedInterproc
  constructor
  · intro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    refine ⟨by rw [hPw]; exact h1,
            by rw [hVer]; exact h2,
            by rw [hEmptyEq]; exact h3,
            by rw [hEnt, hLen]; exact h4,
            by rw [hUniqEq]; exact h5,
            ?_,
            hPropIff.mp h7⟩
    intro defId b₂ hGet2
    have hLt1 : defId < p₁.bodies.length := by
      rw [← hLen]; exact getElem?_some_lt hGet2
    let ⟨b₁, hGet1⟩ := getElem?_some_of_lt p₁.bodies defId hLt1
    have hIdEq : b₂.identity = b₁.identity :=
      body_identity_eq_of_map_eq hIds hGet1 hGet2
    rw [hIdEq]
    exact (hEq.2.2 defId b₁ b₂ (specs.safety b₁.identity) hGet1 hGet2).mpr
      (h6 defId b₁ hGet1)
  · intro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    refine ⟨by rw [← hPw]; exact h1,
            by rw [← hVer]; exact h2,
            by rw [← hEmptyEq]; exact h3,
            by rw [← hEnt, ← hLen]; exact h4,
            by rw [← hUniqEq]; exact h5,
            ?_,
            hPropIff.mpr h7⟩
    intro defId b₁ hGet1
    have hLt2 : defId < p₂.bodies.length := by
      rw [hLen]; exact getElem?_some_lt hGet1
    let ⟨b₂, hGet2⟩ := getElem?_some_of_lt p₂.bodies defId hLt2
    have hIdEq : b₂.identity = b₁.identity :=
      body_identity_eq_of_map_eq hIds hGet1 hGet2
    have hBv2 : BodyVerifiedInterproc p₂ defId b₂ (specs.safety b₁.identity) := by
      rw [← hIdEq]; exact h6 defId b₂ hGet2
    exact (hEq.2.2 defId b₁ b₂ (specs.safety b₁.identity) hGet1 hGet2).mp hBv2

private theorem crate_and_unit_interproc_iff_of_equiv_meta
    {p₁ p₂ : Program} {specs : Specs}
    (hEq : FullSemanticEquivInterproc p₁ p₂)
    (hMeta : ProgramMetaEq p₁ p₂)
    (hSpec : SpecsPropertyInvariant specs) :
    (CrateTheoremInterproc ⟨p₁, specs⟩ ↔ CrateTheoremInterproc ⟨p₂, specs⟩) ∧
    (UnitTheoremInterproc ⟨p₁, specs⟩ ↔ UnitTheoremInterproc ⟨p₂, specs⟩) := by
  have hPv := programVerifiedInterproc_iff_of_equiv_meta hEq hMeta hSpec
  have hSc : p₂.scope = p₁.scope := hMeta.2.2.2.1
  constructor
  · unfold CrateTheoremInterproc; dsimp
    constructor
    · intro ⟨hS, hP⟩; exact ⟨hSc.trans hS, hPv.mp hP⟩
    · intro ⟨hS, hP⟩; exact ⟨hSc.symm.trans hS, hPv.mpr hP⟩
  · unfold UnitTheoremInterproc; dsimp
    constructor
    · intro ⟨hS, hP⟩; exact ⟨hSc.trans hS, hPv.mp hP⟩
    · intro ⟨hS, hP⟩; exact ⟨hSc.symm.trans hS, hPv.mpr hP⟩

/-- Private proof of Theorem 4
(`mirInlineTrace_reduces_interproc_to_intraproc_trusted`). -/
private theorem mirInlineTrace_reduces_interproc_to_intraproc_trusted_priv
    (inlineTrace : InlineTrace) (pSrc pCallFree : Program) (specs : Specs)
    (hTrace : checkMirInlineTrace inlineTrace pSrc pCallFree = true)
    (hCallFree : isCallFreeProgram pCallFree = true)
    (hSpec : SpecsPropertyInvariant specs) :
    (CrateTheoremInterproc ⟨pSrc, specs⟩ ↔ CrateTheorem ⟨pCallFree, specs⟩) ∧
    (UnitTheoremInterproc ⟨pSrc, specs⟩ ↔ UnitTheorem ⟨pCallFree, specs⟩) ∧
    (∀ u : DefId,
      UnitTheoremInterproc ⟨unitProgForDef pSrc u, specs⟩ ↔
        UnitTheorem ⟨unitProgForDef pCallFree u, specs⟩) := by
  unfold checkMirInlineTrace at hTrace
  cases hApp : applyMirInlineTrace inlineTrace pSrc with
  | none => rw [hApp] at hTrace; cases hTrace
  | some pOut =>
    rw [hApp] at hTrace
    have hEqOut : pOut = pCallFree := programEq_eq hTrace
    rw [hEqOut] at hApp
    let ⟨hEq, hMeta, hUnit⟩ := applyMirInlineTrace_sound_and_meta inlineTrace hApp
    let ⟨hCrI, hUnI⟩ := crate_and_unit_interproc_iff_of_equiv_meta hEq hMeta hSpec
    let ⟨hCrCF, hUnCF⟩ :=
      ((interproc_conservative_extension_exact_priv pCallFree).2 hCallFree).2.2.2 specs
    refine ⟨hCrI.trans hCrCF, hUnI.trans hUnCF, ?_⟩
    intro u
    let ⟨hEqU, hMetaU, _⟩ := applyMirInlineTrace_sound_and_meta inlineTrace (hUnit u)
    let ⟨_, hUnIU⟩ := crate_and_unit_interproc_iff_of_equiv_meta hEqU hMetaU hSpec
    have hCallFreeU : isCallFreeProgram (unitProgForDef pCallFree u) = true := hCallFree
    let ⟨_, hUnCFU⟩ :=
      ((interproc_conservative_extension_exact_priv (unitProgForDef pCallFree u)).2
        hCallFreeU).2.2.2 specs
    exact hUnIU.trans hUnCFU

private theorem fullSemanticEquivInterproc_of_callFree_intraproc
    {p₁ p₂ : Program}
    (hCF1 : isCallFreeProgram p₁ = true)
    (hCF2 : isCallFreeProgram p₂ = true)
    (hIntra : FullSemanticEquiv p₁ p₂) :
    FullSemanticEquivInterproc p₁ p₂ := by
  let ⟨hQ1, hPost1, hBody1, _⟩ := (interproc_conservative_extension_exact_priv p₁).2 hCF1
  let ⟨hQ2, hPost2, hBody2, _⟩ := (interproc_conservative_extension_exact_priv p₂).2 hCF2
  let ⟨hQI, hPostI, hBodyI⟩ := hIntra
  refine ⟨?_, ?_, ?_⟩
  · intro q
    let ⟨hWf1, hBeh1, hF1, hDiv1⟩ := hQ1 q
    let ⟨hWf2, hBeh2, hF2, hDiv2⟩ := hQ2 q
    let ⟨hWfI, hBehI, hFI, hDivI⟩ := hQI q
    exact ⟨(hWf2.trans hWfI).trans hWf1.symm,
           fun out => ((hBeh2 out).trans (hBehI out)).trans (hBeh1 out).symm,
           fun k => ((hF2 k).trans (hFI k)).trans (hF1 k).symm,
           (hDiv2.trans hDivI).trans hDiv1.symm⟩
  · intro q post
    exact ((hPost2 q post).trans (hPostI q post)).trans (hPost1 q post).symm
  · intro defId b₁ b₂ safetyPre hGet1 hGet2
    exact ((hBody2 defId b₂ safetyPre).trans
      (hBodyI defId b₁ b₂ safetyPre hGet1 hGet2)).trans
      (hBody1 defId b₁ safetyPre).symm

/-- Private proof of Theorem 5
(`mirInline_then_postInline_vc_transport`). -/
private theorem mirInline_then_postInline_vc_transport_priv
    (inlineTrace : InlineTrace) (pSrc pCallFree pOpt : Program) (specs : Specs)
    (hTrace : checkMirInlineTrace inlineTrace pSrc pCallFree = true)
    (hCallFreeMid : isCallFreeProgram pCallFree = true)
    (hCallFreeOpt : isCallFreeProgram pOpt = true)
    (hMeta : ProgramMetadataCompat pCallFree pOpt = true)
    (hPostOpt : FullSemanticEquiv pCallFree pOpt)
    (hSpec : SpecsPropertyInvariant specs) :
    (CrateTheoremInterproc ⟨pSrc, specs⟩ ↔ CrateTheorem ⟨pOpt, specs⟩) ∧
    (UnitTheoremInterproc ⟨pSrc, specs⟩ ↔ UnitTheorem ⟨pOpt, specs⟩) := by
  unfold checkMirInlineTrace at hTrace
  cases hApp : applyMirInlineTrace inlineTrace pSrc with
  | none => rw [hApp] at hTrace; cases hTrace
  | some pOut =>
    rw [hApp] at hTrace
    have hEqOut : pOut = pCallFree := programEq_eq hTrace
    rw [hEqOut] at hApp
    let ⟨hEq1, hMeta1, _⟩ := applyMirInlineTrace_sound_and_meta inlineTrace hApp
    let ⟨hCr1, hUn1⟩ := crate_and_unit_interproc_iff_of_equiv_meta hEq1 hMeta1 hSpec
    have hEq2 := fullSemanticEquivInterproc_of_callFree_intraproc
      hCallFreeMid hCallFreeOpt hPostOpt
    have hMeta2 := programMetaEq_of_compat hMeta
    let ⟨hCr2, hUn2⟩ := crate_and_unit_interproc_iff_of_equiv_meta hEq2 hMeta2 hSpec
    let ⟨hCrOpt, hUnOpt⟩ :=
      ((interproc_conservative_extension_exact_priv pOpt).2 hCallFreeOpt).2.2.2 specs
    exact ⟨(hCr1.trans hCr2).trans hCrOpt, (hUn1.trans hUn2).trans hUnOpt⟩

/-! ## Part III: Core Target Theorems Directly Over `Trusted.MirSemantics` & Interprocedural MIR Inlining -/

/-- **Theorem 1 (Exact Conservative Extension of `evalStepInterproc` Over
`Trusted.MirSemantics`):**
1. On any `p : Program`, any `c : Choice`, and any single-frame state `s : State`
   with `embedState s = some is` whose active instruction is not a
   `TerminatorKind.call` (`stepIsNotCall p s = true`), `evalStepInterproc p c is`
   matches `liftSingleFrameStep [] (evalStep p c s)` identically.
2. Whenever `isCallFreeProgram p = true`, `WellFormedInterproc`,
   `BehaviorInterproc`, `ReachesResultInterproc (.fault k)`,
   `DivergesInterproc`, `SatisfiesPostInterproc`, `BodyVerifiedInterproc`,
   `CrateTheoremInterproc`, and `UnitTheoremInterproc` are bidirectionally
   equivalent (`↔`) to Anneal's unmodified `Trusted.MirSemantics` judgments. -/
theorem interproc_conservative_extension_exact
    (p : Program) :
    (∀ (c : Choice) (s : State) (is : InterprocState),
      embedState s = some is →
      stepIsNotCall p s = true →
      evalStepInterproc p c is = liftSingleFrameStep [] (evalStep p c s)) ∧
    (isCallFreeProgram p = true →
      (∀ q : Query,
        (WellFormedInterproc p q ↔ WellFormed p q) ∧
        (∀ out : TerminalOut,
          BehaviorInterproc p q out ↔ Behavior p q out) ∧
        (∀ k : FaultKind,
          ReachesResultInterproc p q (.fault k) ↔
            ReachesResult p q (.fault k)) ∧
        (DivergesInterproc p q ↔ Diverges p q)) ∧
      (∀ (q : Query) (post : TerminalOut → Prop),
        SatisfiesPostInterproc p q post ↔ SatisfiesPost p q post) ∧
      (∀ (defId : DefId) (body : Body) (safetyPre : List Val → Prop),
        BodyVerifiedInterproc p defId body safetyPre ↔
          BodyVerified p defId body safetyPre) ∧
      (∀ specs : Specs,
        (CrateTheoremInterproc ⟨p, specs⟩ ↔ CrateTheorem ⟨p, specs⟩) ∧
        (UnitTheoremInterproc ⟨p, specs⟩ ↔ UnitTheorem ⟨p, specs⟩))) := by
  exact interproc_conservative_extension_exact_priv p

/-- **Theorem 2 (Single Call-Site MIR Inlining Bidirectional Soundness):**
For any `site : InlineSite`, `checkMirInlineCallSite site pSrc pTgt = true`
implies `FullSemanticEquivInterproc pSrc pTgt` (`WellFormedInterproc`,
`BehaviorInterproc`, `ReachesResultInterproc (.fault k)`, `DivergesInterproc`,
`SatisfiesPostInterproc`, and `BodyVerifiedInterproc` all `↔`, including under
loop re-entry, nested calls, and mutual recursion). -/
theorem mirInlineCallSite_sound_bidirectional_iff
    (site : InlineSite) (pSrc pTgt : Program)
    (hSite : checkMirInlineCallSite site pSrc pTgt = true) :
    FullSemanticEquivInterproc pSrc pTgt := by
  exact mirInlineCallSite_sound_bidirectional_iff_priv site pSrc pTgt hSite

/-- **Theorem 3 (Arbitrary-Length Multi-Hop MIR Inlining Trace Soundness):**
For any finite `inlineTrace : InlineTrace`, `checkMirInlineTrace inlineTrace
pSrc pTgt = true` implies `FullSemanticEquivInterproc pSrc pTgt` (`↔`). -/
theorem mirInlineTrace_sound_bidirectional_iff
    (inlineTrace : InlineTrace) (pSrc pTgt : Program)
    (hTrace : checkMirInlineTrace inlineTrace pSrc pTgt = true) :
    FullSemanticEquivInterproc pSrc pTgt := by
  exact mirInlineTrace_sound_bidirectional_iff_priv inlineTrace pSrc pTgt hTrace

/-- **Theorem 4 (Interprocedural-to-Intraprocedural Reduction Into Anneal's
Unmodified `CrateTheorem` & `UnitTheorem`):**
Whenever `checkMirInlineTrace inlineTrace pSrc pCallFree = true`,
`isCallFreeProgram pCallFree = true`, and `SpecsPropertyInvariant specs`,
multi-function interprocedural verification of `pSrc` reduces bidirectionally
(`↔`) to Anneal's unmodified intraprocedural `Trusted.MirSemantics.CrateTheorem`
and `UnitTheorem` on `pCallFree` across both whole-crate subjects and arbitrary
per-item proof units `u : DefId`. -/
theorem mirInlineTrace_reduces_interproc_to_intraproc_trusted
    (inlineTrace : InlineTrace) (pSrc pCallFree : Program) (specs : Specs)
    (hTrace : checkMirInlineTrace inlineTrace pSrc pCallFree = true)
    (hCallFree : isCallFreeProgram pCallFree = true)
    (hSpec : SpecsPropertyInvariant specs) :
    (CrateTheoremInterproc ⟨pSrc, specs⟩ ↔ CrateTheorem ⟨pCallFree, specs⟩) ∧
    (UnitTheoremInterproc ⟨pSrc, specs⟩ ↔ UnitTheorem ⟨pCallFree, specs⟩) ∧
    (∀ u : DefId,
      UnitTheoremInterproc ⟨unitProgForDef pSrc u, specs⟩ ↔
        UnitTheorem ⟨unitProgForDef pCallFree u, specs⟩) := by
  exact mirInlineTrace_reduces_interproc_to_intraproc_trusted_priv inlineTrace pSrc pCallFree specs hTrace hCallFree hSpec

/-- **Theorem 5 (Composed MIR Inlining + Post-Inline Optimization VC
Transport):**
Composing a call-eliminating MIR inlining trace (`pSrc --[inlineTrace]-->
pCallFree`) with any post-inline intraprocedural equivalence
`FullSemanticEquiv pCallFree pOpt` (such as the 5-family `MirOptTrace` pipeline
in `F1-5`--`F1-9`) preserving call-freedom and program metadata transports
`CrateTheoremInterproc` and `UnitTheoremInterproc` bidirectionally (`↔`)
directly to unmodified `Trusted.MirSemantics.CrateTheorem` and `UnitTheorem`
on `pOpt`. -/
theorem mirInline_then_postInline_vc_transport
    (inlineTrace : InlineTrace) (pSrc pCallFree pOpt : Program) (specs : Specs)
    (hTrace : checkMirInlineTrace inlineTrace pSrc pCallFree = true)
    (hCallFreeMid : isCallFreeProgram pCallFree = true)
    (hCallFreeOpt : isCallFreeProgram pOpt = true)
    (hMeta : ProgramMetadataCompat pCallFree pOpt = true)
    (hPostOpt : FullSemanticEquiv pCallFree pOpt)
    (hSpec : SpecsPropertyInvariant specs) :
    (CrateTheoremInterproc ⟨pSrc, specs⟩ ↔ CrateTheorem ⟨pOpt, specs⟩) ∧
    (UnitTheoremInterproc ⟨pSrc, specs⟩ ↔ UnitTheorem ⟨pOpt, specs⟩) := by
  exact mirInline_then_postInline_vc_transport_priv inlineTrace pSrc pCallFree pOpt specs hTrace hCallFreeMid hCallFreeOpt hMeta hPostOpt hSpec

/-! ## Part IV: Deterministic Adequacy, Sharpness Counterexamples, & Two-Hop Loop Inlining Witness (`0` `sorry`) -/

/-! ### Deterministic Fuel-Indexed Adequacy for Unmodified `Trusted.MirSemantics` -/

noncomputable def execOutcome (p : Program) (onDone : TerminalOut → Prop)
    (onFault : FaultKind → Prop) : Nat → State → Prop
  | 0, _ => False
  | fuel + 1, s =>
    match evalStep p 0 s with
    | .step s' => execOutcome p onDone onFault fuel s'
    | .done out => onDone out
    | .fault k => onFault k

noncomputable def execReturns (p : Program) (fuel : Nat) (q : Query)
    (expected : Val) : Prop :=
  match initState p q with
  | .error _ => False
  | .ok s₀ =>
    execOutcome p (fun out => out = .returned ⟨expected, ⟨[]⟩⟩)
      (fun _ => False) fuel s₀

noncomputable def execFaults (p : Program) (fuel : Nat) (q : Query)
    (expected : FaultKind) : Prop :=
  match initState p q with
  | .error k => k = expected
  | .ok s₀ =>
    execOutcome p (fun _ => False) (fun k => k = expected) fuel s₀

theorem reaches_head_det {p : Program} {s₁ s₂ s₃ : State}
    (hFirst : Step p s₁ (.step s₂)) (hRest : Reaches p s₂ s₃) :
    Reaches p s₁ s₃ := by
  induction hRest with
  | refl => exact Reaches.tail (Reaches.refl s₁) hFirst
  | tail _ hLast ih => exact Reaches.tail ih hLast

theorem execOutcome_reaches_inv {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {s₁ s₂ : State} {fuel : Nat}
    (hExec : execOutcome p onDone onFault fuel s₁)
    (hReach : Reaches p s₁ s₂) :
    ∃ fuel', execOutcome p onDone onFault fuel' s₂ := by
  induction hReach with
  | refl => exact ⟨fuel, hExec⟩
  | tail _ hStep ih =>
    let ⟨f, hf⟩ := ih
    cases f with
    | zero => exact False.elim hf
    | succ f' =>
      let ⟨c, hc, hEval⟩ := hStep
      have hc0 : c = 0 := hc
      subst hc0
      dsimp [execOutcome] at hf
      rw [hEval] at hf
      exact ⟨f', hf⟩

theorem execOutcome_terminal {p : Program}
    {onDone : TerminalOut → Prop} {onFault : FaultKind → Prop}
    {fuel : Nat} {s : State}
    (hExec : execOutcome p onDone onFault fuel s) :
    ∃ sEnd res, Reaches p s sEnd ∧ Step p sEnd res ∧
      match res with
      | .step _ => False
      | .done out => onDone out
      | .fault k => onFault k := by
  induction fuel generalizing s with
  | zero => exact False.elim hExec
  | succ f ih =>
    dsimp [execOutcome] at hExec
    cases hEval : evalStep p 0 s with
    | step s' =>
      rw [hEval] at hExec
      let ⟨sEnd, res, hR, hT, hPost⟩ := ih hExec
      exact ⟨sEnd, res, reaches_head_det ⟨0, rfl, hEval⟩ hR, hT, hPost⟩
    | done out =>
      rw [hEval] at hExec
      exact ⟨s, .done out, Reaches.refl s, ⟨0, rfl, hEval⟩, hExec⟩
    | fault k =>
      rw [hEval] at hExec
      exact ⟨s, .fault k, Reaches.refl s, ⟨0, rfl, hEval⟩, hExec⟩

theorem positiveCanary_of_execReturns {p : Program} {fuel : Nat}
    {q : Query} {expected : Val}
    (h : execReturns p fuel q expected) :
    PositiveCanaryClaim p q expected := by
  unfold execReturns at h
  cases hInit : initState p q with
  | error _ =>
    rw [hInit] at h
    exact False.elim h
  | ok s₀ =>
    rw [hInit] at h
    refine ⟨⟨⟨s₀, hInit, fun _ _ => ⟨0, rfl⟩⟩, ?_⟩, ?_⟩
    · intro k hFault
      change (match initState p q with
        | .error k' => StepResult.fault k = .fault k'
        | .ok sInit => ∃ s, Reaches p sInit s ∧ Step p s (.fault k)) at hFault
      rw [hInit] at hFault
      let ⟨sF, hReach, c, hc, hEval⟩ := hFault
      have hc0 : c = 0 := hc
      subst hc0
      let ⟨f', hf'⟩ := execOutcome_reaches_inv h hReach
      cases f' with
      | zero => exact hf'
      | succ f'' =>
        dsimp [execOutcome] at hf'
        rw [hEval] at hf'
        exact hf'
    · change (match initState p q with
        | .error k' =>
          (StepResult.done (TerminalOut.returned ⟨expected, ⟨[]⟩⟩) :
            StepResult State TerminalOut) = .fault k'
        | .ok sInit =>
          ∃ s, Reaches p sInit s ∧
            Step p s (.done (.returned ⟨expected, ⟨[]⟩⟩)))
      rw [hInit]
      let ⟨sEnd, res, hR, hStep, hRes⟩ := execOutcome_terminal h
      cases res with
      | step _ => exact False.elim hRes
      | fault _ => exact False.elim hRes
      | done out =>
        subst hRes
        exact ⟨sEnd, hR, hStep⟩

theorem negativeCanary_of_execFaults {p : Program} {fuel : Nat}
    {q : Query} {expectedFault otherFault : FaultKind}
    (hNe : otherFault ≠ expectedFault)
    (h : execFaults p fuel q expectedFault) :
    NegativeCanaryClaim p q expectedFault otherFault := by
  unfold execFaults at h
  cases hInit : initState p q with
  | error k =>
    rw [hInit] at h
    subst h
    refine ⟨?_, ?_, ?_⟩
    · change (match initState p q with
        | .error k' => StepResult.fault k = .fault k'
        | .ok sInit => ∃ s, Reaches p sInit s ∧ Step p s (.fault k))
      rw [hInit]
    · intro hOther
      change (match initState p q with
        | .error k' => StepResult.fault otherFault = .fault k'
        | .ok sInit =>
          ∃ s, Reaches p sInit s ∧ Step p s (.fault otherFault)) at hOther
      rw [hInit] at hOther
      cases hOther
      exact hNe rfl
    · intro hWf
      let ⟨⟨_, hOk, _⟩, _⟩ := hWf
      rw [hInit] at hOk
      cases hOk
  | ok s₀ =>
    rw [hInit] at h
    have hReachExp : ReachesResult p q (.fault expectedFault) := by
      change (match initState p q with
        | .error k' => StepResult.fault expectedFault = .fault k'
        | .ok sInit =>
          ∃ s, Reaches p sInit s ∧ Step p s (.fault expectedFault))
      rw [hInit]
      let ⟨sEnd, res, hR, hStep, hRes⟩ := execOutcome_terminal h
      cases res with
      | step _ => exact False.elim hRes
      | done _ => exact False.elim hRes
      | fault k =>
        subst hRes
        exact ⟨sEnd, hR, hStep⟩
    refine ⟨hReachExp, ?_, ?_⟩
    · intro hOther
      change (match initState p q with
        | .error k' => StepResult.fault otherFault = .fault k'
        | .ok sInit =>
          ∃ s, Reaches p sInit s ∧ Step p s (.fault otherFault)) at hOther
      rw [hInit] at hOther
      let ⟨sF, hReach, c, hc, hEval⟩ := hOther
      have hc0 : c = 0 := hc
      subst hc0
      let ⟨f', hf'⟩ := execOutcome_reaches_inv h hReach
      cases f' with
      | zero => exact hf'
      | succ f'' =>
        dsimp [execOutcome] at hf'
        rw [hEval] at hf'
        exact hNe hf'
    · intro hWf
      exact hWf.2 expectedFault hReachExp

/-! ### Deterministic Fuel-Indexed Adequacy for `evalStepInterproc` (`evalInterprocFuel`) -/

/-- Bounded-fuel deterministic interpreter for `evalStepInterproc`. -/
noncomputable def evalInterprocFuel (p : Program) :
    Nat → InterprocState → StepResult InterprocState TerminalOut
  | 0, s => .step s
  | fuel + 1, s =>
    match evalStepInterproc p 0 s with
    | .step s' => evalInterprocFuel p fuel s'
    | .done out => .done out
    | .fault k => .fault k

/-- Interprocedural positive canary proposition: `(p, q)` is well-formed and
returns `expectedRet` with empty `callerMem`. -/
noncomputable def PositiveCanaryClaimInterproc (p : Program) (q : Query)
    (expectedRet : Val) : Prop :=
  WellFormedInterproc p q ∧
  BehaviorInterproc p q (.returned ⟨expectedRet, ⟨[]⟩⟩)

/-- Interprocedural negative fault canary proposition: `(p, q)` reaches
`.fault expectedFault`, does not reach `.fault otherFault`, and is not
`WellFormedInterproc`. -/
noncomputable def NegativeCanaryClaimInterproc (p : Program) (q : Query)
    (expectedFault otherFault : FaultKind) : Prop :=
  ReachesResultInterproc p q (.fault expectedFault) ∧
  ¬ ReachesResultInterproc p q (.fault otherFault) ∧
  ¬ WellFormedInterproc p q

noncomputable def execReturnsInterproc (p : Program) (fuel : Nat) (q : Query)
    (expected : Val) : Prop :=
  match initStateInterproc p q with
  | .error _ => False
  | .ok s₀ =>
    evalInterprocFuel p fuel s₀ = .done (.returned ⟨expected, ⟨[]⟩⟩)

noncomputable def execFaultsInterproc (p : Program) (fuel : Nat) (q : Query)
    (expected : FaultKind) : Prop :=
  match initStateInterproc p q with
  | .error k => k = expected
  | .ok s₀ => evalInterprocFuel p fuel s₀ = .fault expected

theorem reachesInterproc_head_det {p : Program}
    {s₁ s₂ s₃ : InterprocState}
    (hFirst : StepInterproc p s₁ (.step s₂))
    (hRest : ReachesInterproc p s₂ s₃) :
    ReachesInterproc p s₁ s₃ := by
  induction hRest with
  | refl => exact ReachesInterproc.tail (ReachesInterproc.refl s₁) hFirst
  | tail _ hLast ih => exact ReachesInterproc.tail ih hLast

theorem evalInterprocFuel_reaches_inv {p : Program}
    {res : StepResult InterprocState TerminalOut}
    {s₁ s₂ : InterprocState} {fuel : Nat}
    (hNotStep : match res with | .step _ => False | _ => True)
    (hExec : evalInterprocFuel p fuel s₁ = res)
    (hReach : ReachesInterproc p s₁ s₂) :
    ∃ fuel', evalInterprocFuel p fuel' s₂ = res := by
  induction hReach with
  | refl => exact ⟨fuel, hExec⟩
  | tail _ hStep ih =>
    let ⟨f, hf⟩ := ih
    cases f with
    | zero =>
      dsimp [evalInterprocFuel] at hf
      subst hf
      exact False.elim hNotStep
    | succ f' =>
      let ⟨c, hc, hEval⟩ := hStep
      have hc0 : c = 0 := hc
      subst hc0
      dsimp [evalInterprocFuel] at hf
      rw [hEval] at hf
      exact ⟨f', hf⟩

theorem evalInterprocFuel_terminal {p : Program}
    {res : StepResult InterprocState TerminalOut}
    {fuel : Nat} {s : InterprocState}
    (hNotStep : match res with | .step _ => False | _ => True)
    (hExec : evalInterprocFuel p fuel s = res) :
    ∃ sEnd, ReachesInterproc p s sEnd ∧ StepInterproc p sEnd res := by
  induction fuel generalizing s with
  | zero =>
    dsimp [evalInterprocFuel] at hExec
    subst hExec
    exact False.elim hNotStep
  | succ f ih =>
    dsimp [evalInterprocFuel] at hExec
    cases hEval : evalStepInterproc p 0 s with
    | step s' =>
      rw [hEval] at hExec
      let ⟨sEnd, hR, hT⟩ := ih hExec
      exact ⟨sEnd, reachesInterproc_head_det ⟨0, rfl, hEval⟩ hR, hT⟩
    | done out =>
      rw [hEval] at hExec
      subst hExec
      exact ⟨s, ReachesInterproc.refl s, ⟨0, rfl, hEval⟩⟩
    | fault k =>
      rw [hEval] at hExec
      subst hExec
      exact ⟨s, ReachesInterproc.refl s, ⟨0, rfl, hEval⟩⟩

theorem positiveCanaryInterproc_of_execReturnsInterproc {p : Program}
    {fuel : Nat} {q : Query} {expected : Val}
    (h : execReturnsInterproc p fuel q expected) :
    PositiveCanaryClaimInterproc p q expected := by
  unfold execReturnsInterproc at h
  cases hInit : initStateInterproc p q with
  | error _ =>
    rw [hInit] at h
    exact False.elim h
  | ok s₀ =>
    rw [hInit] at h
    refine ⟨⟨⟨s₀, hInit, fun _ _ => ⟨0, rfl⟩⟩, ?_⟩, ?_⟩
    · intro k hFault
      unfold ReachesResultInterproc at hFault
      rw [hInit] at hFault
      let ⟨sF, hReach, c, hc, hEval⟩ := hFault
      have hc0 : c = 0 := hc
      subst hc0
      let ⟨f', hf'⟩ := evalInterprocFuel_reaches_inv True.intro h hReach
      cases f' with
      | zero =>
        dsimp [evalInterprocFuel] at hf'
        cases hf'
      | succ f'' =>
        dsimp [evalInterprocFuel] at hf'
        rw [hEval] at hf'
        cases hf'
    · unfold BehaviorInterproc ReachesResultInterproc
      rw [hInit]
      exact evalInterprocFuel_terminal True.intro h

theorem negativeCanaryInterproc_of_execFaultsInterproc {p : Program}
    {fuel : Nat} {q : Query} {expectedFault otherFault : FaultKind}
    (hNe : otherFault ≠ expectedFault)
    (h : execFaultsInterproc p fuel q expectedFault) :
    NegativeCanaryClaimInterproc p q expectedFault otherFault := by
  unfold execFaultsInterproc at h
  cases hInit : initStateInterproc p q with
  | error k =>
    rw [hInit] at h
    subst h
    refine ⟨?_, ?_, ?_⟩
    · unfold ReachesResultInterproc; rw [hInit]
    · intro hOther
      unfold ReachesResultInterproc at hOther
      rw [hInit] at hOther
      cases hOther
      exact hNe rfl
    · intro hWf
      let ⟨⟨_, hOk, _⟩, _⟩ := hWf
      rw [hInit] at hOk
      cases hOk
  | ok s₀ =>
    rw [hInit] at h
    have hReachExp : ReachesResultInterproc p q (.fault expectedFault) := by
      unfold ReachesResultInterproc
      rw [hInit]
      exact evalInterprocFuel_terminal True.intro h
    refine ⟨hReachExp, ?_, ?_⟩
    · intro hOther
      unfold ReachesResultInterproc at hOther
      rw [hInit] at hOther
      let ⟨sF, hReach, c, hc, hEval⟩ := hOther
      have hc0 : c = 0 := hc
      subst hc0
      let ⟨f', hf'⟩ := evalInterprocFuel_reaches_inv True.intro h hReach
      cases f' with
      | zero =>
        dsimp [evalInterprocFuel] at hf'
        cases hf'
      | succ f'' =>
        dsimp [evalInterprocFuel] at hf'
        rw [hEval] at hf'
        injection hf' with hEq
        exact hNe hEq
    · intro hWf
      exact hWf.2 expectedFault hReachExp

/-- Chunked fuel-indexed runner for `evalStepInterproc`, bounding kernel
recursion depth on longer concrete executions without `set_option`. -/
noncomputable def evalInterprocChunks (p : Program) (chunk : Nat) :
    Nat → InterprocState → StepResult InterprocState TerminalOut
  | 0, s => .step s
  | n + 1, s =>
    match evalInterprocFuel p chunk s with
    | .step s' => evalInterprocChunks p chunk n s'
    | .done out => .done out
    | .fault k => .fault k

noncomputable def execReturnsInterprocChunks (p : Program) (chunk count : Nat)
    (q : Query) (expected : Val) : Prop :=
  match initStateInterproc p q with
  | .error _ => False
  | .ok s₀ =>
    evalInterprocChunks p chunk count s₀ = .done (.returned ⟨expected, ⟨[]⟩⟩)

theorem evalInterprocFuel_append {p : Program} {f₁ f₂ : Nat}
    {s sMid : InterprocState}
    {res : StepResult InterprocState TerminalOut}
    (h₁ : evalInterprocFuel p f₁ s = .step sMid)
    (h₂ : evalInterprocFuel p f₂ sMid = res) :
    ∃ fTotal, evalInterprocFuel p fTotal s = res := by
  induction f₁ generalizing s with
  | zero =>
    dsimp [evalInterprocFuel] at h₁
    injection h₁ with hEq
    subst hEq
    exact ⟨f₂, h₂⟩
  | succ k ih =>
    dsimp [evalInterprocFuel] at h₁
    cases hEval : evalStepInterproc p 0 s with
    | step s' =>
      rw [hEval] at h₁
      let ⟨ft, hft⟩ := ih h₁
      exact ⟨ft + 1, by dsimp [evalInterprocFuel]; rw [hEval]; exact hft⟩
    | done _ =>
      rw [hEval] at h₁
      cases h₁
    | fault _ =>
      rw [hEval] at h₁
      cases h₁

theorem evalInterprocChunks_to_fuel {p : Program} {chunk n : Nat}
    {s : InterprocState} {res : StepResult InterprocState TerminalOut}
    (hNotStep : match res with | .step _ => False | _ => True)
    (hExec : evalInterprocChunks p chunk n s = res) :
    ∃ fuel, evalInterprocFuel p fuel s = res := by
  induction n generalizing s with
  | zero =>
    dsimp [evalInterprocChunks] at hExec
    subst hExec
    exact False.elim hNotStep
  | succ m ih =>
    dsimp [evalInterprocChunks] at hExec
    cases hChunk : evalInterprocFuel p chunk s with
    | step s' =>
      rw [hChunk] at hExec
      let ⟨ft, hft⟩ := ih hExec
      exact evalInterprocFuel_append hChunk hft
    | done out =>
      rw [hChunk] at hExec
      subst hExec
      exact ⟨chunk, hChunk⟩
    | fault k =>
      rw [hChunk] at hExec
      subst hExec
      exact ⟨chunk, hChunk⟩

theorem positiveCanaryInterproc_of_execReturnsInterprocChunks {p : Program}
    {chunk count : Nat} {q : Query} {expected : Val}
    (h : execReturnsInterprocChunks p chunk count q expected) :
    PositiveCanaryClaimInterproc p q expected := by
  unfold execReturnsInterprocChunks at h
  cases hInit : initStateInterproc p q with
  | error _ =>
    rw [hInit] at h
    exact False.elim h
  | ok s₀ =>
    rw [hInit] at h
    let ⟨fuel, hFuel⟩ := evalInterprocChunks_to_fuel True.intro h
    apply positiveCanaryInterproc_of_execReturnsInterproc (fuel := fuel)
    unfold execReturnsInterproc
    rw [hInit]
    exact hFuel

/-! ### Sharpness Counterexample 1 (`CE1`): Uninitialized Argument UB Must Fire Before Callee Entry -/

noncomputable def ce1CalleeIgnoreArg : Body := {
  argumentCount := 1
  locals := [u32Ty, u32Ty]
  identity := "ce1::ignore_arg"
  basicBlocks := [{
    statements := [
      .assign ⟨0, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 42)⟩))
    ]
    terminator := .return_
  }]
}

noncomputable def progCe1Src : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [
    {
      argumentCount := 0
      locals := [u32Ty, u32Ty]
      identity := "ce1::caller"
      basicBlocks := [
        {
          statements := [.storageLive 1]
          terminator := .call 1 [.copy ⟨1, []⟩] ⟨0, []⟩ (some 1) .continue_
        },
        {
          statements := [.storageDead 1]
          terminator := .return_
        }
      ]
    },
    ce1CalleeIgnoreArg
  ]

/-- Unsound inlining that drops the argument-binding assignment
`_3 = copy _1` because `callee` never reads its parameter. -/
noncomputable def progCe1BadTgt : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [
    {
      argumentCount := 0
      locals := [u32Ty, u32Ty, u32Ty, u32Ty]
      identity := "ce1::caller"
      basicBlocks := [
        {
          statements := [.storageLive 1, .storageLive 2, .storageLive 3]
          terminator := .goto 2
        },
        {
          statements := [.storageDead 1]
          terminator := .return_
        },
        {
          statements := [
            .assign ⟨2, []⟩
              (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 42)⟩))
          ]
          terminator := .goto 3
        },
        {
          statements := [
            .assign ⟨0, []⟩ (.use (.move ⟨2, []⟩)),
            .storageDead 2,
            .storageDead 3
          ]
          terminator := .goto 1
        }
      ]
    },
    ce1CalleeIgnoreArg
  ]

/-- Certified inlining preserving `_3 = copy _1` before entering `callee`. -/
noncomputable def progCe1GoodTgt : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [
    {
      argumentCount := 0
      locals := [u32Ty, u32Ty, u32Ty, u32Ty]
      identity := "ce1::caller"
      basicBlocks := [
        {
          statements := [
            .storageLive 1,
            .storageLive 2,
            .storageLive 3,
            .assign ⟨3, []⟩ (.use (.copy ⟨1, []⟩))
          ]
          terminator := .goto 2
        },
        {
          statements := [.storageDead 1]
          terminator := .return_
        },
        {
          statements := [
            .assign ⟨2, []⟩
              (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 42)⟩))
          ]
          terminator := .goto 3
        },
        {
          statements := [
            .assign ⟨0, []⟩ (.use (.move ⟨2, []⟩)),
            .storageDead 2,
            .storageDead 3
          ]
          terminator := .goto 1
        }
      ]
    },
    ce1CalleeIgnoreArg
  ]

/-- **Sharpness Theorem CE1:** Passing an uninitialized local `_1 : u32` to a
callee that ignores its parameter faults with `.fault .undefined` in `progCe1Src`
before entering the callee. Dropping the argument-binding assignment erases UB
(returning `42_u32` in `progCe1BadTgt`) and is rejected by
`checkMirInlineCallSite`, whereas certified splicing (`progCe1GoodTgt`)
preserves `.fault .undefined` in unmodified `Trusted.MirSemantics`. -/
theorem ce1_uninit_arg_ub_fires_before_callee_entry :
    checkMirInlineCallSite ⟨0, 1, 0⟩ progCe1Src progCe1BadTgt = false ∧
    checkMirInlineCallSite ⟨0, 1, 0⟩ progCe1Src progCe1GoodTgt = true ∧
    NegativeCanaryClaimInterproc progCe1Src queryEmpty .undefined .unsupported ∧
    PositiveCanaryClaim progCe1BadTgt queryEmpty (u32Val 42) ∧
    NegativeCanaryClaim progCe1GoodTgt queryEmpty .undefined .unsupported := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · exact negativeCanaryInterproc_of_execFaultsInterproc (fuel := 6)
      (by intro h; cases h) rfl
  · exact positiveCanary_of_execReturns (fuel := 12) rfl
  · exact negativeCanary_of_execFaults (fuel := 12)
      (by intro h; cases h) rfl

/-! ### Sharpness Counterexample 2 (`CE2`): Unshifted Callee Local Clobbers Caller State -/

noncomputable def ce2CalleeUsesLocal2 : Body := {
  argumentCount := 1
  locals := [u32Ty, u32Ty, u32Ty]
  identity := "ce2::callee"
  basicBlocks := [{
    statements := [
      .assign ⟨2, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 99)⟩)),
      .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨1, []⟩) (.copy ⟨2, []⟩))
    ]
    terminator := .return_
  }]
}

noncomputable def progCe2Src : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [
    {
      argumentCount := 1
      locals := [u32Ty, u32Ty, u32Ty, u32Ty]
      identity := "ce2::caller"
      basicBlocks := [
        {
          statements := [
            .assign ⟨2, []⟩ (.use (.copy ⟨1, []⟩))
          ]
          terminator := .call 1
            [.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 5)⟩]
            ⟨3, []⟩ (some 1) .continue_
        },
        {
          statements := [
            .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨2, []⟩) (.copy ⟨3, []⟩))
          ]
          terminator := .return_
        }
      ]
    },
    ce2CalleeUsesLocal2
  ]

/-- Unsound inlining that fails to shift callee local `_2` by `localBase = 4`,
clobbering caller's `_2` from `10_u32` to `99_u32`. -/
noncomputable def progCe2BadTgt : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [
    {
      argumentCount := 1
      locals := [u32Ty, u32Ty, u32Ty, u32Ty, u32Ty, u32Ty, u32Ty]
      identity := "ce2::caller"
      basicBlocks := [
        {
          statements := [
            .assign ⟨2, []⟩ (.use (.copy ⟨1, []⟩)),
            .storageLive 4,
            .storageLive 5,
            .storageLive 6,
            .assign ⟨5, []⟩
              (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 5)⟩))
          ]
          terminator := .goto 2
        },
        {
          statements := [
            .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨2, []⟩) (.copy ⟨3, []⟩))
          ]
          terminator := .return_
        },
        {
          statements := [
            .assign ⟨2, []⟩
              (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 99)⟩)),
            .assign ⟨4, []⟩ (.binaryOp .add (.copy ⟨5, []⟩) (.copy ⟨2, []⟩))
          ]
          terminator := .goto 3
        },
        {
          statements := [
            .assign ⟨3, []⟩ (.use (.move ⟨4, []⟩)),
            .storageDead 4,
            .storageDead 5,
            .storageDead 6
          ]
          terminator := .goto 1
        }
      ]
    },
    ce2CalleeUsesLocal2
  ]

/-- **Sharpness Theorem CE2:** Failing to shift callee local `_2` by
`localBase = 4` clobbers caller's `_2` (`10 -> 99`), changing the return value
from `114_u32` (`10 + 104`) in `progCe2Src` to `203_u32` (`99 + 104`) in
`progCe2BadTgt`, and is rejected by `checkMirInlineCallSite`. -/
theorem ce2_unshifted_callee_local_clobbers_caller_state :
    checkMirInlineCallSite ⟨0, 1, 0⟩ progCe2Src progCe2BadTgt = false ∧
    PositiveCanaryClaimInterproc progCe2Src { args := [u32Val 10] }
      (u32Val 114) ∧
    PositiveCanaryClaim progCe2BadTgt { args := [u32Val 10] } (u32Val 203) := by
  refine ⟨rfl, ?_, ?_⟩
  · exact positiveCanaryInterproc_of_execReturnsInterproc (fuel := 12) rfl
  · exact positiveCanary_of_execReturns (fuel := 20) rfl

/-! ### Sharpness Counterexample 3 (`CE3`): Omitting Prologue `StorageLive` Causes `DeadLocal` UB -/

noncomputable def ce3CalleeConst77 : Body := {
  argumentCount := 0
  locals := [u32Ty]
  identity := "ce3::const77"
  basicBlocks := [{
    statements := [
      .assign ⟨0, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 77)⟩))
    ]
    terminator := .return_
  }]
}

noncomputable def progCe3Src : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [
    {
      argumentCount := 0
      locals := [u32Ty]
      identity := "ce3::caller"
      basicBlocks := [
        {
          statements := []
          terminator := .call 1 [] ⟨0, []⟩ (some 1) .continue_
        },
        {
          statements := []
          terminator := .return_
        }
      ]
    },
    ce3CalleeConst77
  ]

/-- Unsound inlining that emits `StorageDead 1` in `exitBlock` (making `_1`
start `.dead` in `callerTgt`) while omitting prologue `StorageLive 1`. -/
noncomputable def progCe3BadTgt : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [
    {
      argumentCount := 0
      locals := [u32Ty, u32Ty]
      identity := "ce3::caller"
      basicBlocks := [
        {
          statements := []
          terminator := .goto 2
        },
        {
          statements := []
          terminator := .return_
        },
        {
          statements := [
            .assign ⟨1, []⟩
              (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 77)⟩))
          ]
          terminator := .goto 3
        },
        {
          statements := [
            .assign ⟨0, []⟩ (.use (.move ⟨1, []⟩)),
            .storageDead 1
          ]
          terminator := .goto 1
        }
      ]
    },
    ce3CalleeConst77
  ]

/-- **Sharpness Theorem CE3:** Because `exitBlock` places `StorageDead 1` on
shifted callee slot `_1`, `_1` starts `.dead` at caller entry; omitting the
prologue `StorageLive 1` turns a well-formed `77_u32` return in `progCe3Src`
into `.fault .undefined` (`DeadLocal`) in `progCe3BadTgt` and is rejected by
`checkMirInlineCallSite`. -/
theorem ce3_missing_prologue_storageLive_causes_dead_local_ub :
    checkMirInlineCallSite ⟨0, 1, 0⟩ progCe3Src progCe3BadTgt = false ∧
    PositiveCanaryClaimInterproc progCe3Src queryEmpty (u32Val 77) ∧
    NegativeCanaryClaim progCe3BadTgt queryEmpty .undefined .unsupported := by
  refine ⟨rfl, ?_, ?_⟩
  · exact positiveCanaryInterproc_of_execReturnsInterproc (fuel := 10) rfl
  · exact negativeCanary_of_execFaults (fuel := 10) (by intro h; cases h) rfl

/-! ### Sharpness Counterexample 4 (`CE4`): Self-Recursive Call Executes on Stack Yet Is Rejected by Inliner -/

/-- Self-recursive countdown `fn rec(n: u32) -> u32 { if n == 0 { 0 } else { rec(n - 1) + 1 } }`. -/
noncomputable def progCe4SelfRec : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty, u32Ty, u32Ty]
    identity := "ce4::rec_countdown"
    basicBlocks := [
      {
        statements := []
        terminator := .switchInt (.copy ⟨1, []⟩) {
          branches := [(BitVec.ofNat 128 0, 1)]
          otherwise := 2
        }
      },
      {
        statements := [
          .assign ⟨0, []⟩
            (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 0)⟩))
        ]
        terminator := .return_
      },
      {
        statements := [
          .assign ⟨2, []⟩ (.binaryOp .sub (.copy ⟨1, []⟩)
            (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩))
        ]
        terminator := .call 0 [.move ⟨2, []⟩] ⟨3, []⟩ (some 3) .continue_
      },
      {
        statements := [
          .assign ⟨0, []⟩ (.binaryOp .add (.move ⟨3, []⟩)
            (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩))
        ]
        terminator := .return_
      }
    ]
  }]

/-- **Sharpness Theorem CE4:** Self-recursive `progCe4SelfRec` executes cleanly
across 4 active stack frames under `evalStepInterproc` (`rec(3) = 3_u32`), hits
`.fault .unsupported` in unmodified `Trusted.MirSemantics`, and is rejected by
`applyMirInlineCallSite` / `checkMirInlineCallSite` because
`callerDefId = calleeDefId = 0`. -/
theorem ce4_self_recursive_call_rejected :
    applyMirInlineCallSite ⟨0, 0, 2⟩ progCe4SelfRec = none ∧
    checkMirInlineCallSite ⟨0, 0, 2⟩ progCe4SelfRec progCe4SelfRec = false ∧
    PositiveCanaryClaimInterproc progCe4SelfRec { args := [u32Val 3] }
      (u32Val 3) ∧
    NegativeCanaryClaim progCe4SelfRec { args := [u32Val 3] }
      .unsupported .undefined := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact positiveCanaryInterproc_of_execReturnsInterproc (fuel := 30) rfl
  · exact negativeCanary_of_execFaults (fuel := 10) (by intro h; cases h) rfl

/-! ### Sharpness Counterexample 5 (`CE5`): Dead Destination Faults on Return Write & Callee Fault Precedes Write -/

noncomputable def ce5CalleeRet42 : Body := {
  argumentCount := 0
  locals := [u32Ty]
  identity := "ce5::ret42"
  basicBlocks := [{
    statements := [
      .assign ⟨0, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 42)⟩))
    ]
    terminator := .return_
  }]
}

noncomputable def ce5CalleeUnsupported : Body := {
  argumentCount := 0
  locals := [u32Ty]
  identity := "ce5::unsup"
  basicBlocks := [{
    statements := [.unsupported]
    terminator := .return_
  }]
}

noncomputable def progCe5DeadDstRetSrc : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [
    {
      argumentCount := 0
      locals := [u32Ty, u32Ty]
      identity := "ce5::caller_dead_dst_ret"
      basicBlocks := [
        {
          statements := [.storageLive 1, .storageDead 1]
          terminator := .call 1 [] ⟨1, []⟩ (some 1) .continue_
        },
        {
          statements := [
            .assign ⟨0, []⟩
              (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 0)⟩))
          ]
          terminator := .return_
        }
      ]
    },
    ce5CalleeRet42
  ]

noncomputable def progCe5DeadDstRetTgt : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [
    {
      argumentCount := 0
      locals := [u32Ty, u32Ty, u32Ty]
      identity := "ce5::caller_dead_dst_ret"
      basicBlocks := [
        {
          statements := [.storageLive 1, .storageDead 1, .storageLive 2]
          terminator := .goto 2
        },
        {
          statements := [
            .assign ⟨0, []⟩
              (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 0)⟩))
          ]
          terminator := .return_
        },
        {
          statements := [
            .assign ⟨2, []⟩
              (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 42)⟩))
          ]
          terminator := .goto 3
        },
        {
          statements := [
            .assign ⟨1, []⟩ (.use (.move ⟨2, []⟩)),
            .storageDead 2
          ]
          terminator := .goto 1
        }
      ]
    },
    ce5CalleeRet42
  ]

noncomputable def progCe5DeadDstUnsupSrc : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [
    {
      argumentCount := 0
      locals := [u32Ty, u32Ty]
      identity := "ce5::caller_dead_dst_unsup"
      basicBlocks := [
        {
          statements := [.storageLive 1, .storageDead 1]
          terminator := .call 1 [] ⟨1, []⟩ (some 1) .continue_
        },
        {
          statements := [
            .assign ⟨0, []⟩
              (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 0)⟩))
          ]
          terminator := .return_
        }
      ]
    },
    ce5CalleeUnsupported
  ]

noncomputable def progCe5DeadDstUnsupTgt : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [
    {
      argumentCount := 0
      locals := [u32Ty, u32Ty, u32Ty]
      identity := "ce5::caller_dead_dst_unsup"
      basicBlocks := [
        {
          statements := [.storageLive 1, .storageDead 1, .storageLive 2]
          terminator := .goto 2
        },
        {
          statements := [
            .assign ⟨0, []⟩
              (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 0)⟩))
          ]
          terminator := .return_
        },
        {
          statements := [.unsupported]
          terminator := .goto 3
        },
        {
          statements := [
            .assign ⟨1, []⟩ (.use (.move ⟨2, []⟩)),
            .storageDead 2
          ]
          terminator := .goto 1
        }
      ]
    },
    ce5CalleeUnsupported
  ]

/-- **Sharpness Theorem CE5:** Destination liveness (`DeadLocal`) is checked at
return-write time (matching `rustc_const_eval::interpret`), so:
1. When the callee returns into dead `_1`, both `progCe5DeadDstRetSrc`
   (`evalStepInterproc`) and certified inlined `progCe5DeadDstRetTgt`
   (`Trusted.MirSemantics`) fault with `.fault .undefined`; and
2. When the callee hits `.unsupported` before returning, both
   `progCe5DeadDstUnsupSrc` and certified inlined `progCe5DeadDstUnsupTgt`
   fault with `.fault .unsupported` (and not `.fault .undefined`). -/
theorem ce5_dead_dst_faults_on_return_and_callee_fault_precedes_dst_write :
    checkMirInlineCallSite ⟨0, 1, 0⟩ progCe5DeadDstRetSrc progCe5DeadDstRetTgt =
      true ∧
    checkMirInlineCallSite ⟨0, 1, 0⟩ progCe5DeadDstUnsupSrc
      progCe5DeadDstUnsupTgt = true ∧
    NegativeCanaryClaimInterproc progCe5DeadDstRetSrc queryEmpty
      .undefined .unsupported ∧
    NegativeCanaryClaim progCe5DeadDstRetTgt queryEmpty
      .undefined .unsupported ∧
    NegativeCanaryClaimInterproc progCe5DeadDstUnsupSrc queryEmpty
      .unsupported .undefined ∧
    NegativeCanaryClaim progCe5DeadDstUnsupTgt queryEmpty
      .unsupported .undefined := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
  · exact negativeCanaryInterproc_of_execFaultsInterproc (fuel := 10)
      (by intro h; cases h) rfl
  · exact negativeCanary_of_execFaults (fuel := 12) (by intro h; cases h) rfl
  · exact negativeCanaryInterproc_of_execFaultsInterproc (fuel := 10)
      (by intro h; cases h) rfl
  · exact negativeCanary_of_execFaults (fuel := 12) (by intro h; cases h) rfl

/-! ### Sharpness Counterexample 6 (`CE6`): Callee `StorageDead 0` Must Be Rejected Before Shifting -/

noncomputable def ce6CalleeStorageDead0 : Body := {
  argumentCount := 0
  locals := [u32Ty]
  identity := "ce6::storage_dead_ret_place"
  basicBlocks := [{
    statements := [
      .storageDead 0,
      .storageLive 0,
      .assign ⟨0, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 5)⟩))
    ]
    terminator := .return_
  }]
}

noncomputable def progCe6Src : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [
    {
      argumentCount := 0
      locals := [u32Ty]
      identity := "ce6::caller"
      basicBlocks := [
        {
          statements := []
          terminator := .call 1 [] ⟨0, []⟩ (some 1) .continue_
        },
        {
          statements := []
          terminator := .return_
        }
      ]
    },
    ce6CalleeStorageDead0
  ]

/-- Unsound inlining that shifts `StorageDead 0` in `callee` to `StorageDead 1`
(which no longer triggers `Nat.beq localId 0 -> .fault .unsupported`), turning
`.fault .unsupported` into `5_u32`. -/
noncomputable def progCe6BadTgt : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [
    {
      argumentCount := 0
      locals := [u32Ty, u32Ty]
      identity := "ce6::caller"
      basicBlocks := [
        {
          statements := [.storageLive 1]
          terminator := .goto 2
        },
        {
          statements := []
          terminator := .return_
        },
        {
          statements := [
            .storageDead 1,
            .storageLive 1,
            .assign ⟨1, []⟩
              (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 5)⟩))
          ]
          terminator := .goto 3
        },
        {
          statements := [
            .assign ⟨0, []⟩ (.use (.move ⟨1, []⟩)),
            .storageDead 1
          ]
          terminator := .goto 1
        }
      ]
    },
    ce6CalleeStorageDead0
  ]

/-- **Sharpness Theorem CE6:** Executing `StorageDead 0` inside `callee` faults
with `.fault .unsupported` in `progCe6Src`, whereas shifting it to
`StorageDead 1` in `progCe6BadTgt` bypasses the `localId == 0` guard and
returns `5_u32`; `bodyHasNoStorageDeadZero` rejects the call site. -/
theorem ce6_callee_storageDead_zero_rejected :
    bodyHasNoStorageDeadZero ce6CalleeStorageDead0 = false ∧
    checkMirInlineCallSite ⟨0, 1, 0⟩ progCe6Src progCe6BadTgt = false ∧
    NegativeCanaryClaimInterproc progCe6Src queryEmpty
      .unsupported .undefined ∧
    PositiveCanaryClaim progCe6BadTgt queryEmpty (u32Val 5) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact negativeCanaryInterproc_of_execFaultsInterproc (fuel := 10)
      (by intro h; cases h) rfl
  · exact positiveCanary_of_execReturns (fuel := 14) rfl

/-! ### Constructive Two-Hop Loop Witness (`main -> helper_a -> helper_b` Called Twice in a Loop) -/

/-- Leaf body `fn helper_b(z: u32) -> u32 { _2 = z + z; _0 = move _2; return }`
(using an always-live temp `_2` without storage annotations). -/
noncomputable def witnessHelperB : Body := {
  argumentCount := 1
  locals := [u32Ty, u32Ty, u32Ty]
  identity := "witness::helper_b"
  basicBlocks := [{
    statements := [
      .assign ⟨2, []⟩ (.binaryOp .add (.copy ⟨1, []⟩) (.copy ⟨1, []⟩)),
      .assign ⟨0, []⟩ (.use (.move ⟨2, []⟩))
    ]
    terminator := .return_
  }]
}

/-- Middle body `fn helper_a(a: u32, b: u32) -> u32` calling `helper_b(move _3)`
with a storage-annotated temp `_3`. -/
noncomputable def witnessHelperASrc : Body := {
  argumentCount := 2
  locals := [u32Ty, u32Ty, u32Ty, u32Ty, u32Ty]
  identity := "witness::helper_a"
  basicBlocks := [
    {
      statements := [
        .storageLive 3,
        .assign ⟨3, []⟩ (.binaryOp .add (.copy ⟨1, []⟩) (.copy ⟨2, []⟩))
      ]
      terminator := .call 2 [.move ⟨3, []⟩] ⟨4, []⟩ (some 1) .continue_
    },
    {
      statements := [
        .storageDead 3,
        .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨4, []⟩)
          (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩))
      ]
      terminator := .return_
    }
  ]
}

/-- Entry body `fn main(x: u32) -> u32` invoking `helper_a(x, i)` twice in a
loop (`i = 0, 1`), exercising `exitBlock`'s `StorageDead` reset across loop
re-entry (`x = 10 -> helper_a(10, 0) + helper_a(10, 1) = 21 + 23 = 44`). -/
noncomputable def witnessMainSrc : Body := {
  argumentCount := 1
  locals := [u32Ty, u32Ty, u32Ty, u32Ty, u32Ty, .bool]
  identity := "witness::main"
  basicBlocks := [
    {
      statements := [
        .assign ⟨2, []⟩
          (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 0)⟩)),
        .assign ⟨3, []⟩
          (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 0)⟩))
      ]
      terminator := .goto 1
    },
    {
      statements := [
        .assign ⟨5, []⟩ (.binaryOp .lt (.copy ⟨2, []⟩)
          (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 2)⟩))
      ]
      terminator := .switchInt (.copy ⟨5, []⟩) {
        branches := [(BitVec.ofNat 128 1, 2)]
        otherwise := 4
      }
    },
    {
      statements := []
      terminator := .call 1 [.copy ⟨1, []⟩, .copy ⟨2, []⟩] ⟨4, []⟩ (some 3)
        .continue_
    },
    {
      statements := [
        .assign ⟨3, []⟩ (.binaryOp .add (.copy ⟨3, []⟩) (.copy ⟨4, []⟩)),
        .assign ⟨2, []⟩ (.binaryOp .add (.copy ⟨2, []⟩)
          (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩))
      ]
      terminator := .goto 1
    },
    {
      statements := [
        .assign ⟨0, []⟩ (.use (.copy ⟨3, []⟩))
      ]
      terminator := .return_
    }
  ]
}

/-- Source 3-body crate (`main -> helper_a -> helper_b`). -/
noncomputable def pWitnessSrc : Program where
  scope := .crate
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [witnessMainSrc, witnessHelperASrc, witnessHelperB]

/-- Step 1 result: `helper_b` inlined into `helper_a` at `bb0`. -/
noncomputable def witnessHelperAInlined : Body := {
  argumentCount := 2
  locals := [u32Ty, u32Ty, u32Ty, u32Ty, u32Ty, u32Ty, u32Ty, u32Ty]
  identity := "witness::helper_a"
  basicBlocks := [
    {
      statements := [
        .storageLive 3,
        .assign ⟨3, []⟩ (.binaryOp .add (.copy ⟨1, []⟩) (.copy ⟨2, []⟩)),
        .storageLive 5,
        .storageLive 6,
        .storageLive 7,
        .assign ⟨6, []⟩ (.use (.move ⟨3, []⟩))
      ]
      terminator := .goto 2
    },
    {
      statements := [
        .storageDead 3,
        .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨4, []⟩)
          (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩))
      ]
      terminator := .return_
    },
    {
      statements := [
        .assign ⟨7, []⟩ (.binaryOp .add (.copy ⟨6, []⟩) (.copy ⟨6, []⟩)),
        .assign ⟨5, []⟩ (.use (.move ⟨7, []⟩))
      ]
      terminator := .goto 3
    },
    {
      statements := [
        .assign ⟨4, []⟩ (.use (.move ⟨5, []⟩)),
        .storageDead 5,
        .storageDead 6,
        .storageDead 7
      ]
      terminator := .goto 1
    }
  ]
}

/-- Intermediate crate after Step 1 (`helper_b` inlined into `helper_a`). -/
noncomputable def pWitnessMid : Program where
  scope := .crate
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [witnessMainSrc, witnessHelperAInlined, witnessHelperB]

/-- Step 2 result: fully call-free `main` with `helper_a` (containing
`helper_b`) spliced into `bb2` (note shifted storage-annotated local `6 + 3 = 9`
and `6 + 5..7 = 11..13` omit prologue `StorageLive`, remaining `.dead` until
their inner `StorageLive` statements execute, and all `6..13` reset to `.dead`
in `bb9` before jumping back to `bb3` and looping into `bb2`). -/
noncomputable def witnessMainInlined : Body := {
  argumentCount := 1
  locals := [
    u32Ty, u32Ty, u32Ty, u32Ty, u32Ty, .bool,
    u32Ty, u32Ty, u32Ty, u32Ty, u32Ty, u32Ty, u32Ty, u32Ty
  ]
  identity := "witness::main"
  basicBlocks := [
    {
      statements := [
        .assign ⟨2, []⟩
          (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 0)⟩)),
        .assign ⟨3, []⟩
          (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 0)⟩))
      ]
      terminator := .goto 1
    },
    {
      statements := [
        .assign ⟨5, []⟩ (.binaryOp .lt (.copy ⟨2, []⟩)
          (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 2)⟩))
      ]
      terminator := .switchInt (.copy ⟨5, []⟩) {
        branches := [(BitVec.ofNat 128 1, 2)]
        otherwise := 4
      }
    },
    {
      statements := [
        .storageLive 6,
        .storageLive 7,
        .storageLive 8,
        .storageLive 10,
        .assign ⟨7, []⟩ (.use (.copy ⟨1, []⟩)),
        .assign ⟨8, []⟩ (.use (.copy ⟨2, []⟩))
      ]
      terminator := .goto 5
    },
    {
      statements := [
        .assign ⟨3, []⟩ (.binaryOp .add (.copy ⟨3, []⟩) (.copy ⟨4, []⟩)),
        .assign ⟨2, []⟩ (.binaryOp .add (.copy ⟨2, []⟩)
          (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩))
      ]
      terminator := .goto 1
    },
    {
      statements := [
        .assign ⟨0, []⟩ (.use (.copy ⟨3, []⟩))
      ]
      terminator := .return_
    },
    {
      statements := [
        .storageLive 9,
        .assign ⟨9, []⟩ (.binaryOp .add (.copy ⟨7, []⟩) (.copy ⟨8, []⟩)),
        .storageLive 11,
        .storageLive 12,
        .storageLive 13,
        .assign ⟨12, []⟩ (.use (.move ⟨9, []⟩))
      ]
      terminator := .goto 7
    },
    {
      statements := [
        .storageDead 9,
        .assign ⟨6, []⟩ (.binaryOp .add (.copy ⟨10, []⟩)
          (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩))
      ]
      terminator := .goto 9
    },
    {
      statements := [
        .assign ⟨13, []⟩ (.binaryOp .add (.copy ⟨12, []⟩) (.copy ⟨12, []⟩)),
        .assign ⟨11, []⟩ (.use (.move ⟨13, []⟩))
      ]
      terminator := .goto 8
    },
    {
      statements := [
        .assign ⟨10, []⟩ (.use (.move ⟨11, []⟩)),
        .storageDead 11,
        .storageDead 12,
        .storageDead 13
      ]
      terminator := .goto 6
    },
    {
      statements := [
        .assign ⟨4, []⟩ (.use (.move ⟨6, []⟩)),
        .storageDead 6,
        .storageDead 7,
        .storageDead 8,
        .storageDead 9,
        .storageDead 10,
        .storageDead 11,
        .storageDead 12,
        .storageDead 13
      ]
      terminator := .goto 3
    }
  ]
}

/-- Fully call-free target crate after bottom-up 2-hop inlining. -/
noncomputable def pWitnessCallFree : Program where
  scope := .crate
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [witnessMainInlined, witnessHelperAInlined, witnessHelperB]

noncomputable def witnessTwoHopTrace : InlineTrace := [
  ⟨1, 2, 0⟩,
  ⟨0, 1, 2⟩
]

/-- **Constructive Multi-Hop Loop Witness
(`witness_two_hop_inline_reduces_to_trusted_intraproc`):**
Demonstrates end-to-end non-vacuity on a 3-function crate
`main -> helper_a -> helper_b` where `main` invokes `helper_a` twice inside a
loop:
1. `pWitnessSrc` is not call-free and hits `.fault .unsupported` in unmodified
   `Trusted.MirSemantics`;
2. `checkMirInlineTrace witnessTwoHopTrace pWitnessSrc pWitnessCallFree = true`
   eliminates every `.call` terminator (`isCallFreeProgram pWitnessCallFree = true`,
   `pWitnessSrc ≠ pWitnessCallFree`);
3. `evalStepInterproc` on `pWitnessSrc` (`x = 10`) returns `44_u32` across both
   loop iterations and nested call frames; and
4. Anneal's unmodified intraprocedural `Trusted.MirSemantics.evalStep` (as well
   as `evalStepInterproc`) executes `pWitnessCallFree` (`x = 10`) to the exact
   same `44_u32` (exercising `StorageDead` frame reset on loop re-entry). -/
theorem witness_two_hop_inline_reduces_to_trusted_intraproc :
    isCallFreeProgram pWitnessSrc = false ∧
    isCallFreeProgram pWitnessCallFree = true ∧
    checkMirInlineCallSite ⟨1, 2, 0⟩ pWitnessSrc pWitnessMid = true ∧
    checkMirInlineCallSite ⟨0, 1, 2⟩ pWitnessMid pWitnessCallFree = true ∧
    checkMirInlineTrace witnessTwoHopTrace pWitnessSrc pWitnessCallFree = true ∧
    pWitnessSrc ≠ pWitnessCallFree ∧
    NegativeCanaryClaim pWitnessSrc { args := [u32Val 10] }
      .unsupported .undefined ∧
    PositiveCanaryClaimInterproc pWitnessSrc { args := [u32Val 10] }
      (u32Val 44) ∧
    PositiveCanaryClaim pWitnessCallFree { args := [u32Val 10] } (u32Val 44) ∧
    PositiveCanaryClaimInterproc pWitnessCallFree { args := [u32Val 10] }
      (u32Val 44) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro hEq
    have hCf : isCallFreeProgram pWitnessSrc =
        isCallFreeProgram pWitnessCallFree := by
      rw [hEq]
    cases hCf
  · exact negativeCanary_of_execFaults (fuel := 20) (by intro h; cases h) rfl
  · exact positiveCanaryInterproc_of_execReturnsInterproc (fuel := 45) rfl
  · exact positiveCanary_of_execReturns (fuel := 90) rfl
  · exact positiveCanaryInterproc_of_execReturnsInterprocChunks
      (chunk := 30) (count := 4) rfl

end VrustcFormal.F1_10
