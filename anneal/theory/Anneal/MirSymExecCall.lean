-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Init.Core
public import Init.NotationExtra
public import Init.SimpLemmas
public import Init.Data.Nat.Basic
public import Init.Data.List.Basic
public import Init.Data.BitVec.BasicAux
public import Init.Control.Except
public import Trusted
public import Trusted.MirAst
public import Trusted.MirSemantics
public import Anneal.Framework.StepWp
public import Anneal.MirWp
public import Anneal.MirTotal.Ops
public import Anneal.MirTotal.StepCore
public import Anneal.MirSymExec

public section

namespace Anneal.MirSymExecCall

open Trusted.MirAst Trusted.MirSemantics Anneal.Framework.StepWp Anneal.MirWp
open Anneal.MirTotal Anneal.MirSymExec

/-!
# Multi-Frame MIR Symbolic Executor (`Anneal.MirSymExecCall`)

Extends the single-frame executor of `Anneal.MirSymExec` to whole Profile v1
call stacks (`0` `._unsafe_rec`, `["propext"]`-only axioms), stepping directly
against `Trusted.MirSemantics.evalStep` without the
`bodyHasAnyCall body = false` restriction:

1. **Frames (`SymFrame`, `SymProg`):** a `SymState` per frame plus the frame's
   call-stack metadata (`FrameMeta`: body, sysroot operation, return place,
   and return block). Statements, `goto`, `switchInt`, and the root `return`
   reuse `symStatement` / `symTerminator` through `evalStatement_meta` and
   `evalTerminator_meta`, which carry the metadata through a step.
2. **Calls (`symCall`, `symReturn`):** intra-crate `.call` and `.sysrootCall`
   push a callee frame from symbolic arguments (`symCallArgs`), and a
   non-root `return` writes the callee's `_0` into the caller's destination.
3. **Side conditions (`SymCond`):** an unchecked sysroot operation
   (`unchecked_{add,sub,mul}`) is executed as its wrapping counterpart and
   records that it must not fault. Every soundness theorem assumes the
   recorded conditions (`condsHold`), so callers discharge them from the
   function's `# Safety` precondition instead of losing them.
4. **Bounded runs (`symProgRunSteps`):** a proof checks a run with `rfl` and
   lifts it with `symProgRunSteps_entry_behavior`. Because every intermediate
   state is forced (`forceSymProg`), one `rfl` covers runs of dozens of steps
   under the default `maxHeartbeats`; longer runs can still be checked in
   chunks against explicit checkpoint states composed with
   `symProgRunSteps_trans`.
-/

private theorem if_false_eq {α : Type} {t e : α} :
    (if false = true then t else e) = e := rfl

private theorem if_true_eq {α : Type} {t e : α} :
    (if true = true then t else e) = t := rfl

/-- Call-stack metadata of a frame. -/
structure FrameMeta where
  defId : DefId
  sysrootOp? : Option SysrootNumOp
  retDst? : Option Place
  retTarget? : Option BasicBlockId

/-- Replace the call-stack metadata of `f`. -/
@[expose] noncomputable def FrameMeta.apply (m : FrameMeta) (f : FrameState) :
    FrameState :=
  { f with defId := m.defId, sysrootOp? := m.sysrootOp?, retDst? := m.retDst?,
           retTarget? := m.retTarget? }

/-- Apply `m` to every frame of a stepped state. -/
@[expose] noncomputable def FrameMeta.applyRes (m : FrameMeta) :
    StepResult State TerminalOut → StepResult State TerminalOut
  | .step s => .step { s with frames := s.frames.map m.apply }
  | .done out => .done out
  | .fault k => .fault k

/-- `evalStatement` reads only a frame's locals and statement index, so it
carries any call-stack metadata through. -/
theorem evalStatement_meta (m : FrameMeta) (body : Body) (f : FrameState)
    (mem : MemoryState) (cm : CallerMemory) (stmt : StatementKind) :
    evalStatement body (m.apply f) mem cm stmt =
      m.applyRes (evalStatement body f mem cm stmt) := by
  cases stmt with
  | nop => rfl
  | storageLive x =>
    dsimp only [evalStatement, FrameMeta.apply]
    cases Trusted.MirSemantics.getElem? body.locals x with
    | none => rfl
    | some ty =>
      dsimp only
      cases Trusted.MirSemantics.getElem? f.locals x with
      | none => rfl
      | some old =>
        dsimp only
        cases Trusted.MirSemantics.setElem? f.locals x (liveUninitSlot ty) with
        | none => rfl
        | some l' =>
          dsimp only
          cases deallocateLocal mem old with
          | error k => rfl
          | ok m' => rfl
  | storageDead x =>
    dsimp only [evalStatement, FrameMeta.apply]
    cases Nat.beq x 0 with
    | true => rfl
    | false =>
      cases Trusted.MirSemantics.getElem? f.locals x with
      | none => rfl
      | some old =>
        dsimp only
        cases Trusted.MirSemantics.setElem? f.locals x .dead with
        | none => rfl
        | some l' =>
          dsimp only
          cases deallocateLocal mem old with
          | error k => rfl
          | ok m' => rfl
  | assign dst rv =>
    dsimp only [evalStatement, FrameMeta.apply]
    cases dst.projection.isEmpty with
    | false => rfl
    | true =>
      cases Trusted.MirSemantics.getElem? body.locals dst.localId with
      | none => rfl
      | some ty =>
        dsimp only
        cases evalRvalue body.locals f.locals mem ty rv with
        | error k => rfl
        | ok r =>
          cases r with
          | mk v r_tl =>
            cases r_tl with
            | mk l1 m1 =>
              dsimp only
              cases writePlace l1 m1 dst.localId ty v with
              | error k => rfl
              | ok r2 => cases r2 with | mk l2 m2 => rfl
  | unsupported => rfl


private theorem jump_match_meta (m : FrameMeta) (f : FrameState)
    (mem : MemoryState) (cm : CallerMemory)
    (X : Except FaultKind BasicBlockId) :
    (match X with
      | .error k => (.fault k : StepResult State TerminalOut)
      | .ok t => jumpToBlock (m.apply f) mem cm t) =
      m.applyRes (match X with
        | .error k => .fault k
        | .ok t => jumpToBlock f mem cm t) := by
  cases X <;> rfl

/-- `evalTerminator` carries frame metadata through `goto` and `switchInt`. -/
theorem evalTerminator_meta (m : FrameMeta) (body : Body) (bb : BasicBlock)
    (f : FrameState) (mem : MemoryState) (cm : CallerMemory)
    (ps : PanicStrategy) (hl : Bool) (ps' : PanicStrategy) (hl' : Bool)
    (hNotAssert : ∀ c e msg t u, bb.terminator ≠ .assert c e msg t u)
    (hNotRet : bb.terminator ≠ .return_) :
    evalTerminator body bb (m.apply f) mem cm ps hl =
      m.applyRes (evalTerminator body bb f mem cm ps' hl') := by
  dsimp only [evalTerminator]
  cases hT : bb.terminator with
  | goto t => rfl
  | return_ => exact absurd hT hNotRet
  | assert c e msg t u => exact absurd hT (hNotAssert c e msg t u)
  | switchInt d targets =>
    dsimp only [FrameMeta.apply]
    cases evalPrimitiveOperand body.locals f.locals mem d with
    | error k => rfl
    | ok r =>
      cases r with
      | mk dv r_tl =>
        cases r_tl with
        | mk l1 m1 =>
          dsimp only
          cases dv <;> first
            | rfl
            | exact jump_match_meta m { f with locals := l1 } m1 cm _
  | unreachable => rfl
  | unwindResume => rfl
  | call _ _ _ _ _ => rfl
  | coreCall _ _ _ _ _ => rfl
  | sysrootCall _ _ _ _ _ => rfl
  | callNe _ _ _ _ _ => rfl
  | drop _ _ _ => rfl
  | unsupported => rfl

/-! ## Symbolic call stacks -/

/-- Symbolic frame: the block, statement, and locals of `core` (whose own
`defId` is ignored) plus the frame's call-stack metadata. -/
structure SymFrame where
  core : SymState
  hdr : FrameMeta

/-- Concrete `FrameState` denoted by a `SymFrame` under `env`. -/
@[expose] noncomputable def SymFrame.toFrame (env : SymEnv) (f : SymFrame) :
    FrameState :=
  f.hdr.apply (f.core.toFrame env)

theorem SymFrame.toFrame_eq (env : SymEnv) (f : SymFrame) :
    f.toFrame env = f.hdr.apply (f.core.toFrame env) := rfl

theorem SymFrame.toFrame_locals (env : SymEnv) (f : SymFrame) :
    (f.toFrame env).locals = f.core.slots.map (SymSlot.eval env) := rfl

/-- Side condition recorded by a symbolic step. `ok op a b` states that
`evalBinOp op a b` does not fault, as an unchecked operation requires. -/
inductive SymCond where
  | ok (op : BinOp) (a b : SymScalar)

/-- Whether a side condition holds under `env`. -/
@[expose] noncomputable def SymCond.eval (env : SymEnv) : SymCond → Bool
  | .ok op a b =>
    match evalBinOpComp op (.scalar (a.eval env)) (.scalar (b.eval env)) with
    | .ok _ => true
    | .error _ => false

/-- Whether every side condition in `cs` holds under `env`. -/
@[expose] noncomputable def condsHold (env : SymEnv) (cs : List SymCond) :
    Bool :=
  List.foldr (fun c acc => c.eval env && acc) true cs

/-- Symbolic call stack (innermost frame first) with the side conditions
accumulated so far. -/
structure SymProg where
  frames : List SymFrame
  conds : List SymCond

/-- Concrete `State` denoted by a `SymProg` under `env` (entry memory, empty
caller memory). -/
@[expose] noncomputable def SymProg.toState (env : SymEnv) (s : SymProg) :
    State :=
  { frames := s.frames.map (SymFrame.toFrame env), callerMem := ⟨[]⟩,
    mem := entryMemory }

/-- Result of a multi-frame symbolic step. A root return carries the side
conditions its run accumulated. -/
inductive SymProgRes where
  | step (next : SymProg)
  | ret (val : SymVal) (conds : List SymCond)
  | stuck

/-! ## Statements -/

/-- The wrapping operation that computes an unchecked operation's value when
the unchecked one does not fault, or `none` for wrapping operations. -/
@[expose] noncomputable def sysrootWrapKind? :
    SysrootNumKind → Option SysrootNumKind
  | .uncheckedAdd => some .wrappingAdd
  | .uncheckedSub => some .wrappingSub
  | .uncheckedMul => some .wrappingMul
  | .wrappingAdd => none
  | .wrappingSub => none
  | .wrappingMul => none

/-- The single statement of `sysrootNumBody` for kind `k`. -/
@[expose] noncomputable def sysrootStmt (k : SysrootNumKind) : StatementKind :=
  .assign ⟨0, []⟩
    (.binaryOp (sysrootNumBinOp k) (.copy ⟨1, []⟩) (.copy ⟨2, []⟩))

/-- Side condition of an unchecked sysroot statement: its operation must not
fault on the frame's arguments `_1` and `_2`. -/
@[expose] noncomputable def symSysrootCond (tys : List MirTy) (s : SymState)
    (k : SysrootNumKind) : Option SymCond :=
  match symPrim tys s.slots (.copy ⟨1, []⟩) with
  | none => none
  | some (va, l1) =>
    match symPrim tys l1 (.copy ⟨2, []⟩) with
    | none => none
    | some (vb, _) =>
      match va.asScalar?, vb.asScalar? with
      | some sa, some sb => some (.ok (sysrootNumBinOp k) sa sb)
      | some _, none => none
      | none, _ => none

/-- Symbolic statement of a frame running `body` (sysroot operation `op?`).
An unchecked sysroot statement runs as its wrapping counterpart and records
the side condition that the unchecked operation does not fault. -/
@[expose] noncomputable def symFrameStmt (body : Body)
    (op? : Option SysrootNumOp) (s : SymState) (stmt : StatementKind) :
    Option (SymState × List SymCond) :=
  match op? with
  | none => (symStatement body s stmt).map fun s' => (s', [])
  | some op =>
    match sysrootWrapKind? op.kind with
    | none => (symStatement body s stmt).map fun s' => (s', [])
    | some kW =>
      match symSysrootCond body.locals s op.kind,
          symStatement body s (sysrootStmt kW) with
      | some c, some s' => some (s', [c])
      | some _, none => none
      | none, _ => none

/-! ## Calls and returns -/

/-- Symbolic `evalCallArgs`: evaluate call arguments left to right against
the callee's parameter types, threading moved-local deinitialization. -/
@[expose] noncomputable def symCallArgs (tys : List MirTy) (args : List Operand)
    (paramTys : List MirTy) (ls : List SymSlot) :
    Option (List SymVal × List SymSlot) :=
  List.foldr
    (fun (opnd : Operand)
         (ih : List MirTy → List SymSlot →
           Option (List SymVal × List SymSlot))
         (ps : List MirTy) (ls : List SymSlot) =>
      match ps with
      | [] => none
      | pty :: rest =>
        match symOperand tys ls opnd with
        | some (ty, some v, ls1) =>
          match mirTyEqExact 16 ty pty with
          | some true => (ih rest ls1).map fun r => (v :: r.1, r.2)
          | some false => none
          | none => none
        | some (_, none, _) => none
        | none => none)
    (fun ps ls => match ps with | [] => some ([], ls) | _ :: _ => none)
    args paramTys ls

/-- The static call-site checks of `evalCallTerminatorBy` (with
`tyEq := MirTy.beq`); `true` means the call faults. -/
@[expose] noncomputable def callGuard (callerBody : Body) (bb : BasicBlock)
    (calleeBody : Body) (args : List Operand) (dst : Place)
    (target : Option BasicBlockId) (unwind : UnwindAction) : Bool :=
  !callTargetAdmittedBy MirTy.beq callerBody bb calleeBody args dst target
        unwind ||
      calleeBody.basicBlocks.isEmpty ||
      !storageAnnotationsInBoundsComp calleeBody ||
      !discriminantTypesValidBy MirTy.beq calleeBody ||
      !castTypesValidBy MirTy.beq calleeBody ||
      !assignTypesValidBy MirTy.beq calleeBody ||
      !calleeBody.locals.all isSupportedScalarOrUnitTyComp

/-- Symbolic `evalCallTerminator`: check the call site, evaluate the
arguments, and push the callee frame on top of the updated caller. -/
@[expose] noncomputable def symCall (callerBody : Body) (bb : BasicBlock)
    (f : SymFrame) (callers : List SymFrame) (conds : List SymCond)
    (calleeDefId : DefId) (sysrootOp? : Option SysrootNumOp)
    (calleeBody : Body) (args : List Operand) (dst : Place)
    (target : Option BasicBlockId) (unwind : UnwindAction) : SymProgRes :=
  if callGuard callerBody bb calleeBody args dst target unwind then .stuck
  else
    match symCallArgs callerBody.locals args
        ((calleeBody.locals.drop 1).take calleeBody.argumentCount)
        f.core.slots with
    | none => .stuck
    | some (argVals, ls') =>
      match compGetElem? ls' dst.localId with
      | some (.immediate _) =>
        .step
          { frames :=
              { core := symEntry calleeBody argVals,
                hdr := ⟨calleeDefId, sysrootOp?, some dst, target⟩ } ::
              { f with core := { f.core with slots := ls' } } :: callers,
            conds := conds }
      | some .dead => .stuck
      | none => .stuck

/-- Symbolic `activeFrameBody`. -/
@[expose] noncomputable def symActiveBody (p : Program) (m : FrameMeta) :
    Option Body :=
  match m.sysrootOp? with
  | some op => some (sysrootNumBody op)
  | none => compGetElem? p.bodies m.defId

/-- Symbolic `evalNonRootReturn`: pop the callee, write its `_0` into the
caller's destination, and resume the caller at the return block. -/
@[expose] noncomputable def symReturn (p : Program) (bb : BasicBlock)
    (callee caller : SymFrame) (rest : List SymFrame) (conds : List SymCond) :
    SymProgRes :=
  if bb.cleanup then .stuck
  else
    match compGetElem? callee.core.slots 0 with
    | some (.immediate (some v)) =>
      match callee.hdr.retDst?, callee.hdr.retTarget? with
      | some dst, some tgt =>
        if !dst.projection.isEmpty then .stuck
        else
          match symActiveBody p caller.hdr with
          | none => .stuck
          | some callerBody =>
            match compGetElem? callerBody.locals dst.localId with
            | none => .stuck
            | some dstTy =>
              if symValCheckTy v dstTy then
                match compGetElem? caller.core.slots dst.localId with
                | some (.immediate _) =>
                  match compSetElem? caller.core.slots dst.localId
                      (.immediate (some v)) with
                  | none => .stuck
                  | some ls' =>
                    .step
                      { frames :=
                          { caller with
                            core := { block := tgt, stmt := 0,
                                      slots := ls' } } :: rest,
                        conds := conds }
                | some .dead => .stuck
                | none => .stuck
              else .stuck
      | some _, none => .stuck
      | none, _ => .stuck
    | some (.immediate none) => .stuck
    | some .dead => .stuck
    | none => .stuck

/-! ## Steps -/

/-- Single multi-frame symbolic step, mirroring `evalStep`. -/
@[expose] noncomputable def symProgStep (p : Program) (s : SymProg) :
    SymProgRes :=
  match s.frames with
  | [] => .stuck
  | f :: callers =>
    match symActiveBody p f.hdr with
    | none => .stuck
    | some body =>
      match compGetElem? body.basicBlocks f.core.block with
      | none => .stuck
      | some bb =>
        match compGetElem? bb.statements f.core.stmt with
        | some stmt =>
          match symFrameStmt body f.hdr.sysrootOp? f.core stmt with
          | some (c', cs) =>
            .step { frames := { f with core := c' } :: callers,
                    conds := cs ++ s.conds }
          | none => .stuck
        | none =>
          if Nat.beq f.core.stmt bb.statements.length then
            match bb.terminator with
            | .call callee args dst target unwind =>
              match compGetElem? p.bodies callee with
              | none => .stuck
              | some cb =>
                symCall body bb f callers s.conds callee none cb args dst target
                  unwind
            | .sysrootCall op args dst target unwind =>
              symCall body bb f callers s.conds 0 (some op) (sysrootNumBody op)
                args dst target unwind
            | .return_ =>
              match callers with
              | [] =>
                match symTerminator body bb f.core with
                | .ret v => .ret v s.conds
                | .step _ => .stuck
                | .stuck => .stuck
              | caller :: rest => symReturn p bb f caller rest s.conds
            | .goto _ | .switchInt _ _ =>
              match symTerminator body bb f.core with
              | .step c' =>
                .step { frames := { f with core := c' } :: callers,
                        conds := s.conds }
              | .ret _ => .stuck
              | .stuck => .stuck
            | .assert _ _ _ _ _ | .unreachable | .unwindResume
            | .coreCall _ _ _ _ _ | .callNe _ _ _ _ _ | .drop _ _ _
            | .unsupported => .stuck
          else .stuck

/-! ## Soundness -/

theorem condsHold_append (env : SymEnv) :
    ∀ (a b : List SymCond),
      condsHold env (a ++ b) = (condsHold env a && condsHold env b)
  | [], b => rfl
  | c :: a, b => by
    change (c.eval env && condsHold env (a ++ b)) =
      ((c.eval env && condsHold env a) && condsHold env b)
    rw [condsHold_append env a b]
    cases c.eval env <;> rfl

theorem compGetElem?_map {α β : Type} (f : α → β) :
    ∀ (xs : List α) (n : Nat),
      compGetElem? (xs.map f) n = (compGetElem? xs n).map f
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: tl, n + 1 => compGetElem?_map f tl n

theorem compSetElem?_map {α β : Type} (f : α → β) :
    ∀ (xs : List α) (n : Nat) (v : α),
      compSetElem? (xs.map f) n (f v) = (compSetElem? xs n v).map (List.map f)
  | xs, n, v => by
    rw [compSetElem?_eq, compSetElem?_eq]
    induction xs generalizing n with
    | nil => rfl
    | cons x tl ih =>
      cases n with
      | zero => rfl
      | succ n =>
        change (match Trusted.MirSemantics.setElem? (tl.map f) n (f v) with
          | some tl' => some (f x :: tl')
          | none => none) =
          (match Trusted.MirSemantics.setElem? tl n v with
            | some tl' => some (x :: tl')
            | none => none).map (List.map f)
        rw [ih n]
        cases Trusted.MirSemantics.setElem? tl n v <;> rfl

theorem attachCallers_single (callers : List FrameState) (fr : FrameState)
    (cm : CallerMemory) (mem : MemoryState) :
    attachCallers callers
        (.step { frames := [fr], callerMem := cm, mem := mem }) =
      .step { frames := fr :: callers, callerMem := cm, mem := mem } := by
  cases callers <;> rfl

/-- `return_` reads only the frame's locals. -/
theorem evalTerminator_return_meta (m : FrameMeta) (body : Body)
    (bb : BasicBlock) (f : FrameState) (mem : MemoryState) (cm : CallerMemory)
    (ps ps' : PanicStrategy) (hl hl' : Bool) (hT : bb.terminator = .return_) :
    evalTerminator body bb (m.apply f) mem cm ps hl =
      evalTerminator body bb f mem cm ps' hl' := by
  dsimp only [evalTerminator]
  rw [hT]
  rfl

/-- Shared tail of `evalArithOp` for `+`, `-`, and `*` once the mathematical
result is known; `u` selects the unchecked variant. -/
@[expose] noncomputable def arithTail (u : Bool) (w : IntWidth) (s : Bool)
    (result : Int) : Except FaultKind Val :=
  let hostOverflow : Bool :=
    if s then
      decide (result < Neg.neg (HPow.hPow (2 : Int) 127)) ||
        decide (result ≥ HPow.hPow (2 : Int) 127)
    else
      decide (result < 0) || decide (result ≥ HPow.hPow (2 : Int) 128)
  match truncateScalar w s result with
  | .error k => .error k
  | .ok (val, lossy) =>
    if (hostOverflow || lossy) && u then .error .undefined
    else .ok (.scalar val)

theorem arithTail_unchecked {w : IntWidth} {s : Bool} {result : Int}
    {v : Val} (h : arithTail true w s result = .ok v) :
    arithTail false w s result = .ok v := by
  repeat unfold arithTail at h
  repeat unfold arithTail
  cases hT : truncateScalar w s result with
  | error k => rw [hT] at h; cases h
  | ok r =>
    cases r with
    | mk val lossy =>
      rw [hT] at h
      repeat dsimp only at h
      repeat dsimp only
      cases hb : ((if s then
          decide (result < Neg.neg (HPow.hPow (2 : Int) 127)) ||
            decide (result ≥ HPow.hPow (2 : Int) 127)
        else
          decide (result < 0) || decide (result ≥ HPow.hPow (2 : Int) 128)) ||
          lossy) with
      | true => rw [hb] at h; cases h
      | false => rw [hb] at h; exact h

/-- An unchecked operation and its wrapping counterpart share `arithTail`. -/
theorem evalArithOp_unchecked_tail (k : SysrootNumKind) (kW : SysrootNumKind)
    (hW : sysrootWrapKind? k = some kW) (w : IntWidth) (s : Bool) (l r : Int) :
    ∃ res : Int,
      evalArithOp (sysrootNumBinOp k) w s l r = arithTail true w s res ∧
      evalArithOp (sysrootNumBinOp kW) w s l r = arithTail false w s res := by
  cases k with
  | uncheckedAdd =>
    cases hW; exact ⟨l + r, by cases s <;> rfl, by cases s <;> rfl⟩
  | uncheckedSub =>
    cases hW; exact ⟨l - r, by cases s <;> rfl, by cases s <;> rfl⟩
  | uncheckedMul =>
    cases hW; exact ⟨l * r, by cases s <;> rfl, by cases s <;> rfl⟩
  | wrappingAdd | wrappingSub | wrappingMul => cases hW

private theorem evalBinOp_arith_form (k : SysrootNumKind) (kW : SysrootNumKind)
    (hW : sysrootWrapKind? k = some kW) (x y : ScalarVal) :
    (evalBinOp (sysrootNumBinOp k) (.scalar x) (.scalar y) =
      if (!(IntWidth.beq x.width y.width && (x.signed == y.signed))) = true then
        .error .unsupported
      else evalArithOp (sysrootNumBinOp k) x.width x.signed (decodeScalar x)
        (decodeScalar y)) ∧
    (evalBinOp (sysrootNumBinOp kW) (.scalar x) (.scalar y) =
      if (!(IntWidth.beq x.width y.width && (x.signed == y.signed))) = true then
        .error .unsupported
      else evalArithOp (sysrootNumBinOp kW) x.width x.signed (decodeScalar x)
        (decodeScalar y)) := by
  cases k with
  | uncheckedAdd => cases hW; exact ⟨rfl, rfl⟩
  | uncheckedSub => cases hW; exact ⟨rfl, rfl⟩
  | uncheckedMul => cases hW; exact ⟨rfl, rfl⟩
  | wrappingAdd | wrappingSub | wrappingMul => cases hW

/-- An unchecked sysroot operation that does not fault computes the same value
as its wrapping counterpart. -/
theorem evalBinOp_unchecked_wrap {k kW : SysrootNumKind}
    (hW : sysrootWrapKind? k = some kW) {x y : ScalarVal} {v : Val}
    (h : evalBinOp (sysrootNumBinOp k) (.scalar x) (.scalar y) = .ok v) :
    evalBinOp (sysrootNumBinOp kW) (.scalar x) (.scalar y) = .ok v := by
  let ⟨hU, hWr⟩ := evalBinOp_arith_form k kW hW x y
  rw [hU] at h
  rw [hWr]
  cases hc : (IntWidth.beq x.width y.width && (x.signed == y.signed)) with
  | false => rw [hc] at h; cases h
  | true =>
    rw [hc] at h
    let ⟨res, hA, hB⟩ :=
      evalArithOp_unchecked_tail k kW hW x.width x.signed (decodeScalar x)
        (decodeScalar y)
    change evalArithOp (sysrootNumBinOp k) x.width x.signed (decodeScalar x)
      (decodeScalar y) = .ok v at h
    change evalArithOp (sysrootNumBinOp kW) x.width x.signed (decodeScalar x)
      (decodeScalar y) = .ok v
    rw [hA] at h
    rw [hB]
    exact arithTail_unchecked h

/-- Under its side condition, an unchecked sysroot statement steps exactly as
its wrapping counterpart. -/
theorem sysrootStmt_swap {body : Body} {s : SymState}
    {k kW : SysrootNumKind}
    {c : SymCond} (hW : sysrootWrapKind? k = some kW)
    (hc : symSysrootCond body.locals s k = some c) (env : SymEnv)
    (hcv : c.eval env = true) :
    evalStatement body (s.toFrame env) entryMemory ⟨[]⟩ (sysrootStmt k) =
      evalStatement body (s.toFrame env) entryMemory ⟨[]⟩ (sysrootStmt kW) := by
  unfold symSysrootCond at hc
  cases hA : symPrim body.locals s.slots (.copy ⟨1, []⟩) with
  | none => rw [hA] at hc; cases hc
  | some pa =>
    cases pa with
    | mk va l1 =>
      rw [hA] at hc
      dsimp only at hc
      cases hB : symPrim body.locals l1 (.copy ⟨2, []⟩) with
      | none => rw [hB] at hc; cases hc
      | some pb =>
        cases pb with
        | mk vb l2 =>
          rw [hB] at hc
          dsimp only at hc
          cases hsa : va.asScalar? with
          | none => rw [hsa] at hc; cases hc
          | some sa =>
            cases hsb : vb.asScalar? with
            | none => rw [hsa, hsb] at hc; cases hc
            | some sb =>
              rw [hsa, hsb] at hc
              cases hc
              have hsaE := (symVal_asScalar?_sound hsa env).2
              have hsbE := (symVal_asScalar?_sound hsb env).2
              dsimp only [SymCond.eval] at hcv
              cases hEv : evalBinOpComp (sysrootNumBinOp k)
                  (.scalar (sa.eval env)) (.scalar (sb.eval env)) with
              | error _ => rw [hEv] at hcv; cases hcv
              | ok v =>
                rw [evalBinOpComp_eq] at hEv
                have hEvW := evalBinOp_unchecked_wrap hW hEv
                dsimp only [evalStatement, sysrootStmt, SymState.toFrame]
                cases Trusted.MirSemantics.getElem? body.locals 0 with
                | none => rfl
                | some ty =>
                  dsimp only [evalRvalue]
                  rw [symPrim_sound hA env]
                  dsimp only
                  rw [symPrim_sound hB env]
                  dsimp only
                  rw [hsaE, hsbE, hEv, hEvW]

/-- Soundness of `symFrameStmt`, given its side conditions. `hSys` records
that a sysroot frame runs the statement of its own `sysrootNumBody`. -/
theorem symFrameStmt_sound {body : Body} {op? : Option SysrootNumOp}
    {s s' : SymState} {stmt : StatementKind} {cs : List SymCond}
    (h : symFrameStmt body op? s stmt = some (s', cs))
    (hSys : ∀ op, op? = some op → stmt = sysrootStmt op.kind) (env : SymEnv)
    (hc : condsHold env cs = true) :
    evalStatement body (s.toFrame env) entryMemory ⟨[]⟩ stmt =
      .step (s'.toState env) := by
  cases op? with
  | none =>
    dsimp only [symFrameStmt] at h
    cases hS : symStatement body s stmt with
    | none => rw [hS] at h; cases h
    | some s0 => rw [hS] at h; cases h; exact symStatement_sound hS env
  | some op =>
    dsimp only [symFrameStmt] at h
    cases hk : sysrootWrapKind? op.kind with
    | none =>
      rw [hk] at h
      dsimp only at h
      cases hS : symStatement body s stmt with
      | none => rw [hS] at h; cases h
      | some s0 => rw [hS] at h; cases h; exact symStatement_sound hS env
    | some kW =>
      rw [hk] at h
      dsimp only at h
      cases hC : symSysrootCond body.locals s op.kind with
      | none => rw [hC] at h; cases h
      | some c =>
        cases hS : symStatement body s (sysrootStmt kW) with
        | none => rw [hC, hS] at h; cases h
        | some s0 =>
          rw [hC, hS] at h
          cases h
          have hcv : c.eval env = true := by
            change (c.eval env && true) = true at hc
            cases hce : c.eval env with
            | false => rw [hce] at hc; cases hc
            | true => rfl
          rw [hSys op rfl, sysrootStmt_swap hk hC env hcv]
          exact symStatement_sound hS env

private theorem evalCallArgBy_tail {tys : List MirTy} {ls ls1 : List SymSlot}
    {opnd : Operand} {ty pty : MirTy} {v : SymVal} (env : SymEnv)
    (hO : symOperand tys ls opnd = some (ty, some v, ls1))
    (hTy : MirTy.beq ty pty = true) :
    (match evalOperandToSlotComp tys (ls.map (SymSlot.eval env)) entryMemory
        (fun srcTy => MirTy.beq srcTy pty) opnd with
      | .error k => .error k
      | .ok (srcTy, optVal, locals', mem') =>
        if !MirTy.beq srcTy pty then .error .unsupported
        else
          match optVal with
          | some v => .ok (v, locals', mem')
          | none => .error .undefined :
        Except FaultKind (Val × List LocalSlot × MemoryState)) =
      .ok (v.eval env, ls1.map (SymSlot.eval env), entryMemory) := by
  rw [evalOperandToSlotComp_eq tys _ entryMemory _
    (fun srcTy => MirTy.beq srcTy pty) opnd (fun _ => rfl),
    symOperand_sound hO env]
  dsimp only
  rw [hTy]
  rfl

theorem evalCallArgBy_sym {tys : List MirTy} {ls ls1 : List SymSlot}
    {opnd : Operand} {ty pty : MirTy} {v : SymVal} (env : SymEnv)
    (hasMove : Bool)
    (hO : symOperand tys ls opnd = some (ty, some v, ls1))
    (hTy : MirTy.beq ty pty = true) :
    evalCallArgBy MirTy.beq tys (ls.map (SymSlot.eval env)) entryMemory hasMove
        opnd pty =
      .ok (v.eval env, ls1.map (SymSlot.eval env), entryMemory) := by
  have hTail := evalCallArgBy_tail env hO hTy
  cases opnd with
  | constant c => exact hTail
  | copy place =>
    unfold evalCallArgBy
    dsimp only
    rw [compGetElem?_map]
    cases compGetElem? ls place.localId with
    | none => cases hasMove <;> exact hTail
    | some sl => cases sl <;> cases hasMove <;> exact hTail
  | move place =>
    unfold evalCallArgBy
    dsimp only
    rw [compGetElem?_map]
    cases compGetElem? ls place.localId with
    | none => exact hTail
    | some sl => cases sl <;> exact hTail

private theorem evalCallArgsBy_cons (tys : List MirTy) (hasMove : Bool)
    (opnd : Operand) (rest : List Operand) (pty : MirTy) (prest : List MirTy)
    (ls : List LocalSlot) (mem : MemoryState) :
    evalCallArgsBy MirTy.beq tys hasMove (opnd :: rest) (pty :: prest) ls mem =
      match evalCallArgBy MirTy.beq tys ls mem hasMove opnd pty with
      | .error k => .error k
      | .ok (v, ls₁, m₁) =>
        match evalCallArgsBy MirTy.beq tys hasMove rest prest ls₁ m₁ with
        | .error k => .error k
        | .ok (vs, ls₂, m₂) => .ok (v :: vs, ls₂, m₂) := rfl

/-- Soundness of `symCallArgs`. Symbolic slots are never `.indirect`, so the
result does not depend on `hasMove`. -/
theorem symCallArgs_sound {tys : List MirTy} (env : SymEnv)
    (hasMove : Bool) :
    ∀ {args : List Operand} {ps : List MirTy} {ls ls' : List SymSlot}
      {vs : List SymVal},
      symCallArgs tys args ps ls = some (vs, ls') →
      evalCallArgs tys (ls.map (SymSlot.eval env)) entryMemory hasMove args ps =
        .ok (vs.map (SymVal.eval env), ls'.map (SymSlot.eval env), entryMemory)
  | [], ps, ls, ls', vs, h => by
    cases ps with
    | nil => cases h; rfl
    | cons _ _ => cases h
  | opnd :: rest, ps, ls, ls', vs, h => by
    rw [← evalCallArgsBy_eq MirTy.beq (fun _ _ => rfl)]
    cases ps with
    | nil => cases h
    | cons pty prest =>
      change (match symOperand tys ls opnd with
        | some (ty, some v, ls1) =>
          match mirTyEqExact 16 ty pty with
          | some true => (symCallArgs tys rest prest ls1).map
              fun r => (v :: r.1, r.2)
          | some false => none
          | none => none
        | some (_, none, _) => none
        | none => none) = some (vs, ls') at h
      cases hO : symOperand tys ls opnd with
      | none => rw [hO] at h; cases h
      | some t =>
        cases t with
        | mk ty t_tl =>
          cases t_tl with
          | mk ov ls1 =>
            cases ov with
            | none => rw [hO] at h; cases h
            | some v =>
              rw [hO] at h
              dsimp only at h
              cases hT : mirTyEqExact 16 ty pty with
              | none => rw [hT] at h; cases h
              | some b =>
                cases b with
                | false => rw [hT] at h; cases h
                | true =>
                  rw [hT] at h
                  cases hR : symCallArgs tys rest prest ls1 with
                  | none => rw [hR] at h; cases h
                  | some r =>
                    cases r with
                    | mk vs0 ls2 =>
                      rw [hR] at h
                      cases h
                      have hTy : MirTy.beq ty pty = true :=
                        (mirTyEqExact_eq 16 ty pty true hT).symm
                      have ih := symCallArgs_sound env hasMove hR
                      rw [← evalCallArgsBy_eq MirTy.beq (fun _ _ => rfl)] at ih
                      rw [evalCallArgsBy_cons,
                        evalCallArgBy_sym env hasMove hO hTy]
                      dsimp only
                      rw [ih]
                      rfl

theorem symEntry_locals (body : Body) (args : List SymVal) (env : SymEnv) :
    (symEntry body args).slots.map (SymSlot.eval env) =
      initLocalsLoop body (args.map (SymVal.eval env)) 0 body.locals := by
  have h := congrArg (fun st : State => st.frames.map FrameState.locals)
    (symEntry_toState body args env)
  exact (List.cons.inj h).1

/-- Soundness of `symCall`; a call adds no side conditions. -/
theorem symCall_step {callerBody : Body} {bb : BasicBlock} {f : SymFrame}
    {callers : List SymFrame} {conds : List SymCond} {calleeDefId : DefId}
    {sysOp? : Option SysrootNumOp} {cb : Body} {args : List Operand}
    {dst : Place} {target : Option BasicBlockId} {unwind : UnwindAction}
    {s' : SymProg}
    (h : symCall callerBody bb f callers conds calleeDefId sysOp? cb args dst
      target unwind = .step s') (env : SymEnv) :
    evalCallTerminator callerBody bb (f.toFrame env)
        (callers.map (SymFrame.toFrame env)) entryMemory ⟨[]⟩ calleeDefId sysOp?
        cb args dst target unwind = .step (s'.toState env) ∧
      s'.conds = conds := by
  rw [← evalCallTerminatorBy_eq MirTy.beq (fun _ _ => rfl)]
  unfold symCall at h
  unfold evalCallTerminatorBy
  cases hG : callGuard callerBody bb cb args dst target unwind with
  | true => rw [hG, if_true_eq] at h; cases h
  | false =>
    rw [hG, if_false_eq] at h
    unfold callGuard at hG
    rw [hG, if_false_eq]
    dsimp only
    cases hA : symCallArgs callerBody.locals args
        ((cb.locals.drop 1).take cb.argumentCount) f.core.slots with
    | none => rw [hA] at h; cases h
    | some r =>
      cases r with
      | mk argVals ls' =>
        rw [hA] at h
        dsimp only at h
        rw [evalCallArgsBy_eq MirTy.beq (fun _ _ => rfl)]
        rw [SymFrame.toFrame_locals]
        rw [symCallArgs_sound env _ hA]
        dsimp only
        rw [compGetElem?_map]
        cases hD : compGetElem? ls' dst.localId with
        | none => rw [hD] at h; cases h
        | some sl =>
          cases sl with
          | dead => rw [hD] at h; cases h
          | immediate o =>
            rw [hD] at h
            cases h
            refine ⟨?_, rfl⟩
            dsimp only [Option.map, SymSlot.eval]
            rw [initLocalsLoopComp_eq, ← symEntry_locals cb argVals env]
            rfl

theorem localsHaveIndirect_sym (env : SymEnv) :
    ∀ (ls : List SymSlot),
      localsHaveIndirect (ls.map (SymSlot.eval env)) = false
  | [] => rfl
  | sl :: rest => by
    have ih := localsHaveIndirect_sym env rest
    repeat unfold localsHaveIndirect at ih
    repeat unfold localsHaveIndirect
    cases sl <;> exact ih

theorem activeFrameBody_sym (p : Program) (f : SymFrame) (env : SymEnv) :
    activeFrameBody p (f.toFrame env) = symActiveBody p f.hdr := by
  unfold activeFrameBody symActiveBody
  dsimp only [SymFrame.toFrame, FrameMeta.apply, SymState.toFrame]
  cases f.hdr.sysrootOp? with
  | some op => rfl
  | none => exact (compGetElem?_eq _ _).symm

/-- `writePlace` of a symbolic value into an immediate symbolic slot. -/
theorem writePlace_sym {ls ls' : List SymSlot} {i : LocalId} {ty : MirTy}
    {v : SymVal} {o : Option SymVal} (env : SymEnv)
    (hChk : symValCheckTy v ty = true)
    (hS : compGetElem? ls i = some (.immediate o))
    (hSet : compSetElem? ls i (.immediate (some v)) = some ls') :
    writePlace (ls.map (SymSlot.eval env)) entryMemory i ty (v.eval env) =
      .ok (ls'.map (SymSlot.eval env), entryMemory) := by
  unfold writePlace
  rw [checkVal_of_symValCheckTy hChk env, Bool.not_true, if_false_eq,
    ← compGetElem?_eq, compGetElem?_map, hS]
  dsimp only [Option.map, SymSlot.eval]
  rw [← compSetElem?_eq]
  have hMap := compSetElem?_map (SymSlot.eval env) ls i (.immediate (some v))
  rw [hSet] at hMap
  exact (congrArg (fun r => match r with
    | some locals' => (Except.ok (locals', entryMemory) :
        Except FaultKind (List LocalSlot × MemoryState))
    | none => .error .unsupported) hMap)

/-- Soundness of `symReturn`; a return adds no side conditions. -/
theorem symReturn_step {p : Program} {bb : BasicBlock}
    {callee caller : SymFrame}
    {rest : List SymFrame} {conds : List SymCond} {s' : SymProg}
    (h : symReturn p bb callee caller rest conds = .step s') (calleeBody : Body)
    (env : SymEnv) :
    evalNonRootReturn p calleeBody bb (callee.toFrame env) (caller.toFrame env)
        (rest.map (SymFrame.toFrame env)) entryMemory ⟨[]⟩ =
      .step (s'.toState env) ∧ s'.conds = conds := by
  unfold symReturn at h
  unfold evalNonRootReturn
  rw [SymFrame.toFrame_locals, localsHaveIndirect_sym]
  cases hc : bb.cleanup with
  | true => rw [hc, if_true_eq] at h; cases h
  | false =>
    rw [hc, if_false_eq] at h
    rw [Bool.false_or, if_false_eq]
    dsimp only
    rw [← compGetElem?_eq, compGetElem?_map]
    cases h0 : compGetElem? callee.core.slots 0 with
    | none => rw [h0] at h; cases h
    | some sl =>
      cases sl with
      | dead => rw [h0] at h; cases h
      | immediate o =>
        cases o with
        | none => rw [h0] at h; cases h
        | some v =>
          rw [h0] at h
          repeat dsimp only [Option.map, SymSlot.eval] at h
          repeat dsimp only [Option.map, SymSlot.eval]
          rw [show (callee.toFrame env).retDst? = callee.hdr.retDst? from rfl,
            show (callee.toFrame env).retTarget? = callee.hdr.retTarget?
              from rfl]
          cases hd : callee.hdr.retDst? with
          | none => rw [hd] at h; cases h
          | some dst =>
            cases ht : callee.hdr.retTarget? with
            | none => rw [hd, ht] at h; cases h
            | some tgt =>
              rw [hd, ht] at h
              repeat dsimp only at h
              repeat dsimp only
              cases hp : dst.projection.isEmpty with
              | false => rw [hp] at h; cases h
              | true =>
                rw [hp, Bool.not_true, if_false_eq] at h
                rw [Bool.not_true, if_false_eq, activeFrameBody_sym]
                cases hb : symActiveBody p caller.hdr with
                | none => rw [hb] at h; cases h
                | some callerBody =>
                  rw [hb] at h
                  repeat dsimp only at h
                  repeat dsimp only
                  rw [← compGetElem?_eq]
                  cases hty : compGetElem? callerBody.locals dst.localId with
                  | none => rw [hty] at h; cases h
                  | some dstTy =>
                    rw [hty] at h
                    repeat dsimp only at h
                    repeat dsimp only
                    cases hchk : symValCheckTy v dstTy with
                    | false => rw [hchk, if_false_eq] at h; cases h
                    | true =>
                      rw [hchk, if_true_eq] at h
                      cases hs : compGetElem? caller.core.slots dst.localId with
                      | none => rw [hs] at h; cases h
                      | some cs =>
                        cases cs with
                        | dead => rw [hs] at h; cases h
                        | immediate o2 =>
                          rw [hs] at h
                          dsimp only at h
                          cases hset : compSetElem? caller.core.slots
                              dst.localId (.immediate (some v)) with
                          | none => rw [hset] at h; cases h
                          | some ls' =>
                            rw [hset] at h
                            cases h
                            rw [SymFrame.toFrame_locals,
                              writePlace_sym env hchk hs hset]
                            exact ⟨rfl, rfl⟩

/-- A sysroot frame's only statement is `sysrootStmt`. -/
theorem sysroot_stmt_shape {p : Program} {m : FrameMeta}
    {op : SysrootNumOp}
    {body : Body} {bb : BasicBlock} {b i : Nat} {stmt : StatementKind}
    (hb : symActiveBody p m = some body) (hop : m.sysrootOp? = some op)
    (hbb : compGetElem? body.basicBlocks b = some bb)
    (hst : compGetElem? bb.statements i = some stmt) :
    stmt = sysrootStmt op.kind := by
  unfold symActiveBody at hb
  rw [hop] at hb
  cases hb
  cases b with
  | succ _ => cases hbb
  | zero =>
    cases hbb
    cases i with
    | succ _ => cases hst
    | zero => cases hst; rfl

theorem condsHold_of_append {env : SymEnv} {a b : List SymCond}
    (h : condsHold env (a ++ b) = true) :
    condsHold env a = true ∧ condsHold env b = true := by
  rw [condsHold_append] at h
  cases ha : condsHold env a with
  | false => rw [ha] at h; cases h
  | true => rw [ha] at h; exact ⟨rfl, h⟩

/-- One symbolic step is one concrete `evalStep`, given the accumulated side
conditions. -/
theorem symProgStep_sound {p : Program} {s s' : SymProg}
    (h : symProgStep p s = .step s') (env : SymEnv) :
    (∃ cs, s'.conds = cs ++ s.conds) ∧
      (condsHold env s'.conds = true →
        evalStep p 0 (s.toState env) = .step (s'.toState env)) := by
  unfold symProgStep at h
  unfold SymProg.toState
  cases hF : s.frames with
  | nil => rw [hF] at h; cases h
  | cons f callers =>
    rw [hF] at h
    dsimp only at h
    dsimp only [evalStep, List.map]
    rw [activeFrameBody_sym,
      show (f.toFrame env).blockIdx = f.core.block from rfl,
      show (f.toFrame env).stmtIdx = f.core.stmt from rfl]
    cases hb : symActiveBody p f.hdr with
    | none => rw [hb] at h; cases h
    | some body =>
      rw [hb] at h
      repeat dsimp only at h
      repeat dsimp only
      rw [← compGetElem?_eq]
      cases hbb : compGetElem? body.basicBlocks f.core.block with
      | none => rw [hbb] at h; cases h
      | some bb =>
        rw [hbb] at h
        repeat dsimp only at h
        repeat dsimp only
        rw [← compGetElem?_eq]
        cases hst : compGetElem? bb.statements f.core.stmt with
        | some stmt =>
          rw [hst] at h
          repeat dsimp only at h
          repeat dsimp only
          cases hfs : symFrameStmt body f.hdr.sysrootOp? f.core stmt with
          | none => rw [hfs] at h; cases h
          | some r =>
            cases r with
            | mk c' cs =>
              rw [hfs] at h
              cases h
              refine ⟨⟨cs, rfl⟩, fun hc => ?_⟩
              have hcs := (condsHold_of_append hc).1
              have hSys : ∀ op, f.hdr.sysrootOp? = some op →
                  stmt = sysrootStmt op.kind :=
                fun op hop => sysroot_stmt_shape hb hop hbb hst
              rw [SymFrame.toFrame_eq,
                evalStatement_meta, symFrameStmt_sound hfs hSys env hcs]
              exact attachCallers_single _ _ _ _
        | none =>
          rw [hst] at h
          repeat dsimp only at h
          repeat dsimp only
          cases hlen : Nat.beq f.core.stmt bb.statements.length with
          | false => rw [hlen, if_false_eq] at h; cases h
          | true =>
            rw [hlen, if_true_eq] at h
            rw [if_true_eq]
            cases hT : bb.terminator with
            | call callee args dst target unwind =>
              rw [hT] at h
              repeat dsimp only at h
              repeat dsimp only
              rw [← compGetElem?_eq]
              cases hcb : compGetElem? p.bodies callee with
              | none => rw [hcb] at h; cases h
              | some cb =>
                rw [hcb] at h
                exact ⟨⟨[], (symCall_step h env).2⟩,
                  fun _ => (symCall_step h env).1⟩
            | sysrootCall op args dst target unwind =>
              rw [hT] at h
              exact ⟨⟨[], (symCall_step h env).2⟩,
                fun _ => (symCall_step h env).1⟩
            | return_ =>
              rw [hT] at h
              repeat dsimp only at h
              repeat dsimp only
              cases callers with
              | nil =>
                dsimp only at h
                cases hR : symTerminator body bb f.core with
                | ret v => rw [hR] at h; cases h
                | step _ => rw [hR] at h; cases h
                | stuck => rw [hR] at h; cases h
              | cons caller rest =>
                exact ⟨⟨[], (symReturn_step h body env).2⟩,
                  fun _ => (symReturn_step h body env).1⟩
            | goto t =>
              rw [hT] at h
              repeat dsimp only at h
              repeat dsimp only
              cases hR : symTerminator body bb f.core with
              | step c' =>
                rw [hR] at h
                cases h
                refine ⟨⟨[], rfl⟩, fun _ => ?_⟩
                rw [SymFrame.toFrame_eq,
                  evalTerminator_meta f.hdr body bb (f.core.toFrame env)
                    entryMemory ⟨[]⟩ _ _ .unwind true
                    (fun c e msg t u hA => by rw [hT] at hA; cases hA)
                    (fun hA => by rw [hT] at hA; cases hA),
                  symTerminator_step hR env]
                exact attachCallers_single _ _ _ _
              | ret _ => rw [hR] at h; cases h
              | stuck => rw [hR] at h; cases h
            | switchInt d targets =>
              rw [hT] at h
              repeat dsimp only at h
              repeat dsimp only
              cases hR : symTerminator body bb f.core with
              | step c' =>
                rw [hR] at h
                cases h
                refine ⟨⟨[], rfl⟩, fun _ => ?_⟩
                rw [SymFrame.toFrame_eq,
                  evalTerminator_meta f.hdr body bb (f.core.toFrame env)
                    entryMemory ⟨[]⟩ _ _ .unwind true
                    (fun c e msg t u hA => by rw [hT] at hA; cases hA)
                    (fun hA => by rw [hT] at hA; cases hA),
                  symTerminator_step hR env]
                exact attachCallers_single _ _ _ _
              | ret _ => rw [hR] at h; cases h
              | stuck => rw [hR] at h; cases h
            | assert _ _ _ _ _ => rw [hT] at h; cases h
            | unreachable => rw [hT] at h; cases h
            | unwindResume => rw [hT] at h; cases h
            | coreCall _ _ _ _ _ => rw [hT] at h; cases h
            | callNe _ _ _ _ _ => rw [hT] at h; cases h
            | drop _ _ _ => rw [hT] at h; cases h
            | unsupported => rw [hT] at h; cases h

theorem symCall_ne_ret {callerBody : Body} {bb : BasicBlock} {f : SymFrame}
    {callers : List SymFrame} {conds : List SymCond} {calleeDefId : DefId}
    {sysOp? : Option SysrootNumOp} {cb : Body} {args : List Operand}
    {dst : Place} {target : Option BasicBlockId} {unwind : UnwindAction}
    {v : SymVal} {cs : List SymCond} :
    symCall callerBody bb f callers conds calleeDefId sysOp? cb args dst target
      unwind ≠ .ret v cs := by
  intro h
  unfold symCall at h
  cases hG : callGuard callerBody bb cb args dst target unwind with
  | true => rw [hG, if_true_eq] at h; cases h
  | false =>
    rw [hG, if_false_eq] at h
    cases hA : symCallArgs callerBody.locals args
        ((cb.locals.drop 1).take cb.argumentCount) f.core.slots with
    | none => rw [hA] at h; cases h
    | some r =>
      cases r with
      | mk argVals ls' =>
        rw [hA] at h
        dsimp only at h
        cases hD : compGetElem? ls' dst.localId with
        | none => rw [hD] at h; cases h
        | some sl => cases sl <;> (rw [hD] at h; cases h)

theorem symReturn_ne_ret {p : Program} {bb : BasicBlock}
    {callee caller : SymFrame} {rest : List SymFrame} {conds : List SymCond}
    {v : SymVal} {cs : List SymCond} :
    symReturn p bb callee caller rest conds ≠ .ret v cs := by
  intro h
  unfold symReturn at h
  cases hc : bb.cleanup with
  | true => rw [hc, if_true_eq] at h; cases h
  | false =>
    rw [hc, if_false_eq] at h
    cases h0 : compGetElem? callee.core.slots 0 with
    | none => rw [h0] at h; cases h
    | some sl =>
      cases sl with
      | dead => rw [h0] at h; cases h
      | immediate o =>
        cases o with
        | none => rw [h0] at h; cases h
        | some w =>
          rw [h0] at h
          dsimp only at h
          cases hd : callee.hdr.retDst? with
          | none => rw [hd] at h; cases h
          | some dst =>
            cases ht : callee.hdr.retTarget? with
            | none => rw [hd, ht] at h; cases h
            | some tgt =>
              rw [hd, ht] at h
              dsimp only at h
              cases hp : dst.projection.isEmpty with
              | false => rw [hp] at h; cases h
              | true =>
                rw [hp, Bool.not_true, if_false_eq] at h
                cases hb : symActiveBody p caller.hdr with
                | none => rw [hb] at h; cases h
                | some callerBody =>
                  rw [hb] at h
                  dsimp only at h
                  cases hty : compGetElem? callerBody.locals dst.localId with
                  | none => rw [hty] at h; cases h
                  | some dstTy =>
                    rw [hty] at h
                    dsimp only at h
                    cases hchk : symValCheckTy w dstTy with
                    | false => rw [hchk, if_false_eq] at h; cases h
                    | true =>
                      rw [hchk, if_true_eq] at h
                      cases hs : compGetElem? caller.core.slots dst.localId with
                      | none => rw [hs] at h; cases h
                      | some cs' =>
                        cases cs' with
                        | dead => rw [hs] at h; cases h
                        | immediate o2 =>
                          rw [hs] at h
                          dsimp only at h
                          cases hset : compSetElem? caller.core.slots
                              dst.localId (.immediate (some w)) with
                          | none => rw [hset] at h; cases h
                          | some ls' => rw [hset] at h; cases h

/-- A symbolic return from the root frame is a concrete return. -/
theorem symProgStep_ret {p : Program} {s : SymProg} {v : SymVal}
    {cs : List SymCond} (h : symProgStep p s = .ret v cs) (env : SymEnv) :
    cs = s.conds ∧
      evalStep p 0 (s.toState env) = .done (.returned ⟨v.eval env, ⟨[]⟩⟩) := by
  unfold symProgStep at h
  unfold SymProg.toState
  cases hF : s.frames with
  | nil => rw [hF] at h; cases h
  | cons f callers =>
    rw [hF] at h
    dsimp only at h
    dsimp only [evalStep, List.map]
    rw [activeFrameBody_sym,
      show (f.toFrame env).blockIdx = f.core.block from rfl,
      show (f.toFrame env).stmtIdx = f.core.stmt from rfl]
    cases hb : symActiveBody p f.hdr with
    | none => rw [hb] at h; cases h
    | some body =>
      rw [hb] at h
      repeat dsimp only at h
      repeat dsimp only
      rw [← compGetElem?_eq]
      cases hbb : compGetElem? body.basicBlocks f.core.block with
      | none => rw [hbb] at h; cases h
      | some bb =>
        rw [hbb] at h
        repeat dsimp only at h
        repeat dsimp only
        rw [← compGetElem?_eq]
        cases hst : compGetElem? bb.statements f.core.stmt with
        | some stmt =>
          rw [hst] at h
          dsimp only at h
          cases hfs : symFrameStmt body f.hdr.sysrootOp? f.core stmt with
          | none => rw [hfs] at h; cases h
          | some r => cases r with | mk c' cs' => rw [hfs] at h; cases h
        | none =>
          rw [hst] at h
          repeat dsimp only at h
          repeat dsimp only
          cases hlen : Nat.beq f.core.stmt bb.statements.length with
          | false => rw [hlen, if_false_eq] at h; cases h
          | true =>
            rw [hlen, if_true_eq] at h
            rw [if_true_eq]
            cases hT : bb.terminator with
            | call callee args dst target unwind =>
              rw [hT] at h
              dsimp only at h
              cases hcb : compGetElem? p.bodies callee with
              | none => rw [hcb] at h; cases h
              | some cb => rw [hcb] at h; exact absurd h symCall_ne_ret
            | sysrootCall op args dst target unwind =>
              rw [hT] at h
              exact absurd h symCall_ne_ret
            | return_ =>
              rw [hT] at h
              repeat dsimp only at h
              repeat dsimp only
              cases callers with
              | nil =>
                repeat dsimp only at h
                repeat dsimp only
                cases hR : symTerminator body bb f.core with
                | ret w =>
                  rw [hR] at h
                  cases h
                  refine ⟨rfl, ?_⟩
                  rw [SymFrame.toFrame_eq,
                    evalTerminator_return_meta f.hdr body bb
                      (f.core.toFrame env) entryMemory ⟨[]⟩ _ .unwind _ true hT]
                  exact symTerminator_ret hR env
                | step _ => rw [hR] at h; cases h
                | stuck => rw [hR] at h; cases h
              | cons caller rest => exact absurd h symReturn_ne_ret
            | goto t =>
              rw [hT] at h
              dsimp only at h
              cases hR : symTerminator body bb f.core <;>
                (rw [hR] at h; cases h)
            | switchInt d targets =>
              rw [hT] at h
              dsimp only at h
              cases hR : symTerminator body bb f.core <;>
                (rw [hR] at h; cases h)
            | assert _ _ _ _ _ => rw [hT] at h; cases h
            | unreachable => rw [hT] at h; cases h
            | unwindResume => rw [hT] at h; cases h
            | coreCall _ _ _ _ _ => rw [hT] at h; cases h
            | callNe _ _ _ _ _ => rw [hT] at h; cases h
            | drop _ _ _ => rw [hT] at h; cases h
            | unsupported => rw [hT] at h; cases h

/-! ## Forcing intermediate states

`symProgStep` builds its successor lazily: struct updates, `Option.map`
continuations, and `compSetElem?` results all keep pointing at the previous
state. Neither the elaborator's `whnf` nor `isDefEq` shares work across those
wrappers, so a field read at step `n` re-reduces the steps before it, and an
`rfl` check of a `k`-step run grows exponentially in `k` (a 13-step run with
one sysroot call exceeds the default `maxHeartbeats`).

`forceSymProg s k` case-splits `s` down to its frame and slot constructors in
continuation-passing style and passes `k` the rebuilt state, whose fields are
then the reduced subterms rather than references into earlier states.
`symProgRunSteps` forces every intermediate state through the discriminant of a
`match`, so `whnf` reduces the whole run in one pass. Each `force*` function is
extensionally the identity (`force*_eq`), so forcing changes only reduction
cost, not meaning. -/

/-- Rebuild `n` from its head constructor before passing it to `k`. -/
@[expose] def forceNatHead {α : Type} (n : Nat) (k : Nat → α) : α :=
  @Nat.casesOn (fun _ => α) n (k 0) (fun m => k (Nat.succ m))

theorem forceNatHead_eq {α : Type} (n : Nat) (k : Nat → α) :
    forceNatHead n k = k n := by
  cases n <;> rfl

/-- Rebuild `o` from its head constructor before passing it to `k`. -/
@[expose] def forceOptionHead {β α : Type} (o : Option β)
    (k : Option β → α) : α :=
  match o with
  | none => k none
  | some x => k (some x)

theorem forceOptionHead_eq {β α : Type} (o : Option β) (k : Option β → α) :
    forceOptionHead o k = k o := by
  cases o <;> rfl

/-- Rebuild the spine of `xs`, forcing each element with `fe`, before passing
it to `k`. -/
@[expose] def forceListWith {β α : Type}
    (fe : β → (β → List β → α) → List β → α) (xs : List β)
    (k : List β → α) : α :=
  List.foldr
    (fun (x : β) (ih : (List β → α) → α) (k : List β → α) =>
      ih fun tl => fe x (fun x' tl' => k (x' :: tl')) tl)
    (fun k => k []) xs k

theorem forceListWith_eq {β α : Type}
    {fe : β → (β → List β → α) → List β → α}
    (hfe : ∀ x c tl, fe x c tl = c x tl) :
    ∀ (xs : List β) (k : List β → α), forceListWith fe xs k = k xs
  | [], _ => rfl
  | x :: xs, k => by
    change forceListWith fe xs
        (fun tl => fe x (fun x' tl' => k (x' :: tl')) tl) = k (x :: xs)
    exact (forceListWith_eq hfe xs _).trans (hfe x _ xs)

/-- Rebuild `v` from its head constructor. -/
@[expose] def forceSymVal {α : Type} (v : SymVal) (k : SymVal → α) : α :=
  match v with
  | .conc c => k (.conc c)
  | .scalar x => k (.scalar x)
  | .bool b => k (.bool b)
  | .pair a b => k (.pair a b)

theorem forceSymVal_eq {α : Type} (v : SymVal) (k : SymVal → α) :
    forceSymVal v k = k v := by
  cases v <;> rfl

/-- Rebuild a slot, including the head of its value, as a list element. -/
@[expose] def forceSymSlot {α : Type} (sl : SymSlot)
    (k : SymSlot → List SymSlot → α) (tl : List SymSlot) : α :=
  match sl with
  | .dead => k .dead tl
  | .immediate none => k (.immediate none) tl
  | .immediate (some v) => forceSymVal v fun v' => k (.immediate (some v')) tl

theorem forceSymSlot_eq {α : Type} (sl : SymSlot)
    (k : SymSlot → List SymSlot → α) (tl : List SymSlot) :
    forceSymSlot sl k tl = k sl tl := by
  cases sl with
  | dead => rfl
  | immediate o =>
    cases o with
    | none => rfl
    | some v => exact forceSymVal_eq v (fun v' => k (.immediate (some v')) tl)

/-- Rebuild a frame's block, statement index, and slots. -/
@[expose] def forceSymState {α : Type} (s : SymState) (k : SymState → α) : α :=
  match s with
  | ⟨b, i, ls⟩ =>
    forceNatHead b fun b' => forceNatHead i fun i' =>
      forceListWith forceSymSlot ls fun ls' => k ⟨b', i', ls'⟩

theorem forceSymState_eq {α : Type} (s : SymState) (k : SymState → α) :
    forceSymState s k = k s := by
  cases s with
  | mk b i ls =>
    change forceNatHead b (fun b' => forceNatHead i fun i' =>
      forceListWith forceSymSlot ls fun ls' => k ⟨b', i', ls'⟩) = _
    exact (forceNatHead_eq b _).trans ((forceNatHead_eq i _).trans
      (forceListWith_eq forceSymSlot_eq ls _))

/-- Rebuild a frame's call-stack metadata. -/
@[expose] def forceFrameMeta {α : Type} (m : FrameMeta) (k : FrameMeta → α) :
    α :=
  match m with
  | ⟨d, op, dst, tgt⟩ =>
    forceNatHead d fun d' => forceOptionHead op fun op' =>
      forceOptionHead dst fun dst' => forceOptionHead tgt fun tgt' =>
        k ⟨d', op', dst', tgt'⟩

theorem forceFrameMeta_eq {α : Type} (m : FrameMeta) (k : FrameMeta → α) :
    forceFrameMeta m k = k m := by
  cases m with
  | mk d op dst tgt =>
    change forceNatHead d (fun d' => forceOptionHead op fun op' =>
      forceOptionHead dst fun dst' => forceOptionHead tgt fun tgt' =>
        k ⟨d', op', dst', tgt'⟩) = _
    exact (forceNatHead_eq d _).trans ((forceOptionHead_eq op _).trans
      ((forceOptionHead_eq dst _).trans (forceOptionHead_eq tgt _)))

/-- Rebuild a frame as a list element. -/
@[expose] def forceSymFrame {α : Type} (f : SymFrame)
    (k : SymFrame → List SymFrame → α) (tl : List SymFrame) : α :=
  match f with
  | ⟨c, h⟩ => forceSymState c fun c' => forceFrameMeta h fun h' => k ⟨c', h'⟩ tl

theorem forceSymFrame_eq {α : Type} (f : SymFrame)
    (k : SymFrame → List SymFrame → α) (tl : List SymFrame) :
    forceSymFrame f k tl = k f tl := by
  cases f with
  | mk c h =>
    change forceSymState c
      (fun c' => forceFrameMeta h fun h' => k ⟨c', h'⟩ tl) = _
    exact (forceSymState_eq c _).trans (forceFrameMeta_eq h _)

/-- Rebuild a side condition as a list element. -/
@[expose] def forceSymCond {α : Type} (c : SymCond)
    (k : SymCond → List SymCond → α) (tl : List SymCond) : α :=
  match c with
  | .ok op a b => k (.ok op a b) tl

theorem forceSymCond_eq {α : Type} (c : SymCond)
    (k : SymCond → List SymCond → α) (tl : List SymCond) :
    forceSymCond c k tl = k c tl := by
  cases c; rfl

/-- Rebuild a call stack and its side conditions. -/
@[expose] def forceSymProg {α : Type} (s : SymProg) (k : SymProg → α) : α :=
  match s with
  | ⟨fs, cs⟩ =>
    forceListWith forceSymFrame fs fun fs' =>
      forceListWith forceSymCond cs fun cs' => k ⟨fs', cs'⟩

theorem forceSymProg_eq {α : Type} (s : SymProg) (k : SymProg → α) :
    forceSymProg s k = k s := by
  cases s with
  | mk fs cs =>
    change forceListWith forceSymFrame fs (fun fs' =>
      forceListWith forceSymCond cs fun cs' => k ⟨fs', cs'⟩) = _
    exact (forceListWith_eq forceSymFrame_eq fs _).trans
      (forceListWith_eq forceSymCond_eq cs _)

/-- Run at most `k` multi-frame symbolic steps (`@Nat.rec`, `0`
`._unsafe_rec`), returning `.step s'` for the state reached after exactly `k`
steps if the run has neither returned nor become stuck. Each intermediate
state is forced (`forceSymProg`) in the discriminant of a `match`, so a single
`rfl` can check runs of dozens of steps (see the section comment above). -/
@[expose] noncomputable def symProgRunSteps (p : Program) (k : Nat)
    (s : SymProg) : SymProgRes :=
  @Nat.rec (fun _ => SymProg → SymProgRes)
    (fun st => .step st)
    (fun _ ih st =>
      match symProgStep p st with
      | .step st' =>
        match forceSymProg st' some with
        | some st'' => ih st''
        | none => .stuck
      | .ret v cs => .ret v cs
      | .stuck => .stuck)
    k s

theorem symProgRunSteps_zero (p : Program) (s : SymProg) :
    symProgRunSteps p 0 s = .step s := rfl

theorem symProgRunSteps_succ (p : Program) (k : Nat) (s : SymProg) :
    symProgRunSteps p (k + 1) s =
      match symProgStep p s with
      | .step s' => symProgRunSteps p k s'
      | .ret v cs => .ret v cs
      | .stuck => .stuck := by
  change (match symProgStep p s with
    | .step s' =>
      match forceSymProg s' some with
      | some s'' => symProgRunSteps p k s''
      | none => .stuck
    | .ret v cs => .ret v cs
    | .stuck => .stuck) = _
  cases symProgStep p s with
  | step s' =>
    exact congrArg (fun o => match o with
      | some s'' => symProgRunSteps p k s''
      | none => .stuck) (forceSymProg_eq s' some)
  | ret v cs => rfl
  | stuck => rfl

theorem symProgRunSteps_add (p : Program) :
    ∀ (m n : Nat) (s : SymProg),
      symProgRunSteps p (m + n) s =
        match symProgRunSteps p m s with
        | .step s' => symProgRunSteps p n s'
        | .ret v cs => .ret v cs
        | .stuck => .stuck
  | 0, n, s => by rw [Nat.zero_add]; rfl
  | m + 1, n, s => by
    rw [Nat.succ_add, symProgRunSteps_succ, symProgRunSteps_succ]
    cases symProgStep p s with
    | step s' => exact symProgRunSteps_add p m n s'
    | ret v cs => rfl
    | stuck => rfl

/-- Compose a chunk that reaches `s'` with a run from `s'`. -/
theorem symProgRunSteps_trans {p : Program} {m n : Nat} {s s' : SymProg}
    {r : SymProgRes} (h1 : symProgRunSteps p m s = .step s')
    (h2 : symProgRunSteps p n s' = r) : symProgRunSteps p (m + n) s = r := by
  rw [symProgRunSteps_add, h1]
  exact h2

theorem condsHold_suffix {env : SymEnv} {a b : List SymCond}
    (hab : ∃ cs, a = cs ++ b) (h : condsHold env a = true) :
    condsHold env b = true := by
  let ⟨cs, he⟩ := hab
  rw [he] at h
  exact (condsHold_of_append h).2

private theorem suffix_trans {a b c : List SymCond} (hab : ∃ cs, a = cs ++ b)
    (hbc : ∃ cs, b = cs ++ c) : ∃ cs, a = cs ++ c := by
  let ⟨x, hx⟩ := hab
  let ⟨y, hy⟩ := hbc
  exact ⟨x ++ y, by rw [hx, hy, List.append_assoc]⟩

/-- Prefix a concrete continuation with `k` symbolic steps. -/
theorem symProgRunSteps_step_exec {p : Program} {onDone : TerminalOut → Prop}
    {onFault : FaultKind → Prop} (env : SymEnv) :
    ∀ {k : Nat} {s s' : SymProg},
      symProgRunSteps p k s = .step s' →
      (∃ cs, s'.conds = cs ++ s.conds) ∧
        (condsHold env s'.conds = true →
          ∀ {n : Nat}, execOutcomeState p onDone onFault n (s'.toState env) →
            execOutcomeState p onDone onFault (k + n) (s.toState env))
  | 0, s, s', h => by
    cases h
    exact ⟨⟨[], rfl⟩, fun _ n hn => by rw [Nat.zero_add]; exact hn⟩
  | k + 1, s, s', h => by
    rw [symProgRunSteps_succ] at h
    cases hStep : symProgStep p s with
    | ret v cs => rw [hStep] at h; cases h
    | stuck => rw [hStep] at h; cases h
    | step s1 =>
      rw [hStep] at h
      let ⟨hSuf1, hSound1⟩ := symProgStep_sound hStep env
      let ⟨hSufK, hK⟩ := symProgRunSteps_step_exec (onDone := onDone)
        (onFault := onFault) env h
      refine ⟨suffix_trans hSufK hSuf1, fun hc n hn => ?_⟩
      rw [Nat.succ_add]
      dsimp only [execOutcomeState, execStepOutcome]
      rw [execStepPred_succ_iff, hSound1 (condsHold_suffix hSufK hc)]
      exact hK hc hn

/-- A chunked run that returns within `k` steps is a concrete return. -/
theorem symProgRunSteps_ret_exec {p : Program} {onFault : FaultKind → Prop}
    (env : SymEnv) :
    ∀ {k : Nat} {s : SymProg} {v : SymVal} {cs : List SymCond},
      symProgRunSteps p k s = .ret v cs →
      (∃ cs0, cs = cs0 ++ s.conds) ∧
        (condsHold env cs = true →
          execOutcomeState p (fun o => o = .returned ⟨v.eval env, ⟨[]⟩⟩)
            onFault k (s.toState env))
  | 0, s, v, cs, h => by cases h
  | k + 1, s, v, cs, h => by
    rw [symProgRunSteps_succ] at h
    dsimp only [execOutcomeState, execStepOutcome]
    cases hStep : symProgStep p s with
    | stuck => rw [hStep] at h; cases h
    | ret w cs' =>
      rw [hStep] at h
      cases h
      let ⟨hcs, hEv⟩ := symProgStep_ret hStep env
      refine ⟨⟨[], hcs⟩, fun _ => ?_⟩
      rw [execStepPred_succ_iff, hEv]
    | step s1 =>
      rw [hStep] at h
      let ⟨hSuf1, hSound1⟩ := symProgStep_sound hStep env
      let ⟨hSufK, hK⟩ := symProgRunSteps_ret_exec (onFault := onFault) env h
      refine ⟨suffix_trans hSufK hSuf1, fun hc => ?_⟩
      rw [execStepPred_succ_iff, hSound1 (condsHold_suffix hSufK hc)]
      exact hK hc

/-- Entry state of body `defId` with symbolic arguments `args`. -/
@[expose] noncomputable def symProgEntry (defId : DefId) (body : Body)
    (args : List SymVal) : SymProg :=
  { frames :=
      [{ core := symEntry body args, hdr := ⟨defId, none, none, none⟩ }],
    conds := [] }

theorem symProgEntry_toState (defId : DefId) (body : Body)
    (args : List SymVal) (env : SymEnv) :
    (symProgEntry defId body args).toState env =
      retagDefId defId
        (mkState 0 0 (initLocalsLoop body (args.map (SymVal.eval env)) 0
          body.locals)) := by
  unfold SymProg.toState symProgEntry retagDefId mkState
  dsimp only [List.map, SymFrame.toFrame, FrameMeta.apply, SymState.toFrame]
  rw [show (symEntry body args).slots.map (SymSlot.eval env) =
      initLocalsLoop body (args.map (SymVal.eval env)) 0 body.locals
    from symEntry_locals body args env]
  rfl

/-- Lift a chunked multi-frame run from the entry of body `defId` into
`Behavior`, `¬ Diverges`, and `SatisfiesPost` over `entryProgForBody p defId`,
given the run's side conditions. -/
theorem symProgRunSteps_entry_behavior {p : Program} {defId : DefId}
    {body : Body} {k : Nat} {args : List SymVal} {out : SymVal}
    {cs : List SymCond}
    (hBody : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (hAdm : BodyStaticAdmitted p body = true) (env : SymEnv)
    (hArgs : ValidEntryArgs body (args.map (SymVal.eval env)))
    (hRun : symProgRunSteps (entryProgForBody p defId) k
      (symProgEntry defId body args) = .ret out cs)
    (hc : condsHold env cs = true) :
    WellFormed (entryProgForBody p defId)
        { args := args.map (SymVal.eval env) } ∧
      Trusted.MirSemantics.Behavior (entryProgForBody p defId)
        { args := args.map (SymVal.eval env) }
        (.returned ⟨out.eval env, ⟨[]⟩⟩) ∧
      ¬ Diverges (entryProgForBody p defId)
          { args := args.map (SymVal.eval env) } ∧
      ∀ post : TerminalOut → Prop, post (.returned ⟨out.eval env, ⟨[]⟩⟩) →
        SatisfiesPost (entryProgForBody p defId)
          { args := args.map (SymVal.eval env) } post := by
  have hExec :
      execProg (entryProgForBody p defId) k
        { args := args.map (SymVal.eval env) }
        (fun outcome => outcome = .returned ⟨out.eval env, ⟨[]⟩⟩) := by
    unfold execProg
    rw [initState_entryProgForBody hBody hAdm hArgs,
      ← symProgEntry_toState defId body args env]
    exact (symProgRunSteps_ret_exec env hRun).2 hc
  exact spec_and_behavior_of_wp_eq (wpProg_of_execProg hExec)

end Anneal.MirSymExecCall

end
