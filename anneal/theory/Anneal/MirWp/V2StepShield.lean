-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Anneal.MirWp.V2Memory

public section

/-!
# Arity-stable Profile v2 stepping API

Proofs about Profile v2 bodies (`zerocopy/proofs/`, `tests/` fixtures, and
downstream crates) step a single-frame `State` one `evalStepV2` transition at a
time. Written directly against `Trusted.MirSemantics`, such a proof depends on
two things that change whenever the semantics grow:

* the exact field list of `FrameState` and `State`, through anonymous
  constructors such as `⟨[⟨d, b, i, locals, none, none, none⟩], cm, m⟩`; and
* the internal structure of `evalStepV2` and `evalStatementV2`, through
  `dsimp only [evalStepV2, evalStatementV2, resolvePlaceDestV2, ...]`.

This module states the common steps once, in terms that do not mention either:

* `frameV2` and `stateV2` build frames and single-frame states with structure
  instance syntax, so a new `FrameState` or `State` field with a default value
  leaves every use unchanged;
* `evalStepV2_stmt` and `evalStepV2_term` reduce one step to the statement or
  terminator being executed, given the body, block, and statement lookups;
  `evalStepV2_assign_local`, `evalStepV2_storageLive`,
  `evalStepV2_storageDead`, `evalStepV2_nop`, `evalStepV2_goto`, and
  `evalStepV2_return_ok` go on to compute the resulting state, and
  `evalRvalueV2_ref_deref_ok` evaluates a reborrow without unfolding
  `evalRvalueV2`; and
* `RunsV2` hides the execution fuel, so that elaboration never unfolds
  `execOutcomeStateV2` on a concrete fuel literal.

When `evalStepV2` changes, only the proofs in this file need to follow; proofs
that use these lemmas keep their text. `BodyCtx.initStateV2_ok_frameV2` and
`evalStepV2_return_ok` take only facts about the body and the values involved,
and `evalStepV2_assign_local` factors through `evalRvalueV2` and
`writePlaceDestV2` without naming `evalStatementV2`; `evalStepV2_stmt` and
`evalStepV2_term` name `evalStatementV2` and `evalTerminatorV2` in their
conclusions and so change whenever those functions gain parameters.
-/

namespace Anneal.MirWp

open Trusted.MirAst Trusted.MirSemantics

/-! ## Frames and states -/

/-- The frame executing statement `stmtIdx` of block `blockIdx` of body
`defId` with locals `locals`. Every other `FrameState` field takes its default
value. -/
abbrev frameV2 (defId : DefId) (blockIdx : BasicBlockId)
    (stmtIdx : Nat) (locals : List LocalSlot) : FrameState :=
  { defId := defId, blockIdx := blockIdx, stmtIdx := stmtIdx, locals := locals }

/-- The state whose only frame is `frame`. -/
abbrev stateV2 (frame : FrameState) (callerMem : CallerMemory)
    (mem : MemoryState) : State :=
  { frames := [frame], callerMem := callerMem, mem := mem }

/-- `BodyCtx.initStateV2_ok_of`, with the entry state written with `stateV2`
and `frameV2` for any body (including raw-pointer parameters). -/
theorem BodyCtx.initStateV2_ok_frameV2_forArgs (ctx : BodyCtx)
    (h_body : ctx.HasBody) {q : Query}
    (hAdm : BodyStaticAdmittedV2 ctx.program ctx.body = true)
    (hValid : ValidEntryArgsV2 ctx.body q) :
    initStateV2 ctx.entryProg q = .ok (stateV2
      (frameV2 ctx.defId 0 0 (initLocalsLoop ctx.body q.args 0 ctx.body.locals))
      q.callerMem
      (entryMemoryForArgsV2 q.callerMem
        ((ctx.body.locals.drop 1).take ctx.body.argumentCount) q.args)) :=
  ctx.initStateV2_ok_of h_body hAdm hValid

/-- `BodyCtx.initStateV2_ok_of`, with the entry state written with `stateV2`
and `frameV2` for bodies whose parameters contain no raw pointers. -/
theorem BodyCtx.initStateV2_ok_frameV2 (ctx : BodyCtx) (h_body : ctx.HasBody)
    {q : Query}
    (hAdm : BodyStaticAdmittedV2 ctx.program ctx.body = true)
    (hValid : ValidEntryArgsV2 ctx.body q)
    (hNoRaw : tyListHasRawPtrV2
      ((ctx.body.locals.drop 1).take ctx.body.argumentCount) = false :=
        by rfl) :
    initStateV2 ctx.entryProg q = .ok (stateV2
      (frameV2 ctx.defId 0 0 (initLocalsLoop ctx.body q.args 0 ctx.body.locals))
      q.callerMem (entryMemoryWithCaller q.callerMem)) := by
  have h := ctx.initStateV2_ok_of h_body hAdm hValid
  unfold entryMemoryForArgsV2 at h
  rw [hNoRaw] at h
  exact h

/-! ## One step -/

/-- A single-frame state positioned at a statement steps by that statement. -/
theorem evalStepV2_stmt {p : Program} {body : Body} {bb : BasicBlock}
    {defId : DefId} {b i : Nat} {locals : List LocalSlot}
    {cm : CallerMemory} {m : MemoryState} {stmt : StatementKind}
    (hBody : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (hBB : Trusted.MirSemantics.getElem? body.basicBlocks b = some bb)
    (hStmt : Trusted.MirSemantics.getElem? bb.statements i = some stmt) :
    evalStepV2 p (stateV2 (frameV2 defId b i locals) cm m) =
      evalStatementV2 body (frameV2 defId b i locals) m cm stmt := by
  unfold evalStepV2
  dsimp only
  rw [hBody]
  dsimp only
  rw [hBB]
  dsimp only
  rw [hStmt]

/-- A single-frame state positioned just past the last statement of a block
steps by the block's terminator. -/
theorem evalStepV2_term {p : Program} {body : Body} {bb : BasicBlock}
    {defId : DefId} {b i : Nat} {locals : List LocalSlot}
    {cm : CallerMemory} {m : MemoryState}
    (hBody : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (hBB : Trusted.MirSemantics.getElem? body.basicBlocks b = some bb)
    (hStmt : Trusted.MirSemantics.getElem? bb.statements i = none)
    (hEnd : Nat.beq i bb.statements.length = true) :
    evalStepV2 p (stateV2 (frameV2 defId b i locals) cm m) =
      evalTerminatorV2 body bb (frameV2 defId b i locals) m cm p.panicStrategy
        p.hasLocalPanicHandler p.overflowChecks := by
  unfold evalStepV2
  dsimp only
  rw [hBody]
  dsimp only
  rw [hBB]
  dsimp only
  rw [hStmt]
  dsimp only
  rw [hEnd]
  rfl

/-- An `assign` to an unprojected local, split into the evaluation of its
rvalue, the store of the result, and the copy-overlap hazard check. -/
theorem evalStatementV2_assign_local {body : Body} {defId : DefId} {b i : Nat}
    {l l1 l2 : List LocalSlot} {cm : CallerMemory} {m m1 m2 : MemoryState}
    {lid : LocalId} {rv : Rvalue} {ty : MirTy} {v : Val}
    (hTy : placeStaticTyV2 body.locals ⟨lid, []⟩ = some ty)
    (hRv : evalRvalueV2 body.locals l m ty rv = .ok (v, l1, m1))
    (hW : writePlaceDestV2 l1 m1 (.local lid) ty v = .ok (l2, m2))
    (hHaz : checkAssignCopyHazardV2 body.locals l m (.local lid) ty rv =
      .ok () := by rfl) :
    evalStatementV2 body (frameV2 defId b i l) m cm (.assign ⟨lid, []⟩ rv) =
      .step (stateV2 (frameV2 defId b (i + 1) l2) cm m2) := by
  unfold evalStatementV2
  dsimp only
  rw [hTy]
  dsimp only
  rw [show resolvePlaceDestV2 body.locals l m ⟨lid, []⟩ ty = .ok (.local lid)
    from rfl]
  dsimp only
  rw [hRv]
  dsimp only
  rw [hW]
  dsimp only
  rw [hHaz]

/-- A reborrow `&(*_lid)` (or `&mut (*_lid)`) of a valid reference held in an
immediate local evaluates to that reference. -/
theorem evalRvalueV2_ref_deref_ok {bodyLocals : List MirTy}
    {locals : List LocalSlot} {mem : MemoryState} {lid : LocalId}
    {srcMut reqMut : Mutability} {pt : MirTy} {v : Val}
    (hTy : Trusted.MirSemantics.getElem? bodyLocals lid = some (.ref srcMut pt))
    (hSlot : Trusted.MirSemantics.getElem? locals lid =
      some (.immediate (some v)))
    (hMut : (Mutability.beq srcMut .shared &&
      Mutability.beq reqMut .mut) = false)
    (hRef : refValidInMem mem reqMut pt v = .ok ()) :
    evalRvalueV2 bodyLocals locals mem (.ref reqMut pt)
      (.ref reqMut ⟨lid, [.deref]⟩) = .ok (v, locals, mem) :=
  evalRefRvalueV2_deref_ok hTy hSlot hMut hRef

/-- One `assign` step to an unprojected local. -/
theorem evalStepV2_assign_local {p : Program} {body : Body} {bb : BasicBlock}
    {defId : DefId} {b i : Nat} {l l1 l2 : List LocalSlot}
    {cm : CallerMemory} {m m1 m2 : MemoryState} {lid : LocalId} {rv : Rvalue}
    {ty : MirTy} {v : Val}
    (hBody : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (hBB : Trusted.MirSemantics.getElem? body.basicBlocks b = some bb)
    (hStmt : Trusted.MirSemantics.getElem? bb.statements i =
      some (.assign ⟨lid, []⟩ rv))
    (hTy : placeStaticTyV2 body.locals ⟨lid, []⟩ = some ty)
    (hRv : evalRvalueV2 body.locals l m ty rv = .ok (v, l1, m1))
    (hW : writePlaceDestV2 l1 m1 (.local lid) ty v = .ok (l2, m2))
    (hHaz : checkAssignCopyHazardV2 body.locals l m (.local lid) ty rv =
      .ok () := by rfl) :
    evalStepV2 p (stateV2 (frameV2 defId b i l) cm m) =
      .step (stateV2 (frameV2 defId b (i + 1) l2) cm m2) :=
  (evalStepV2_stmt hBody hBB hStmt).trans
    (evalStatementV2_assign_local hTy hRv hW hHaz)

/-- `StorageLive` of a local whose old slot deallocates successfully. -/
theorem evalStatementV2_storageLive {body : Body} {defId : DefId} {b i : Nat}
    {l l1 : List LocalSlot} {cm : CallerMemory} {m m1 : MemoryState}
    {lid : LocalId} {ty : MirTy} {old : LocalSlot}
    (hTy : Trusted.MirSemantics.getElem? body.locals lid = some ty)
    (hOld : Trusted.MirSemantics.getElem? l lid = some old)
    (hSet : setElem? l lid (liveUninitSlot ty) = some l1)
    (hFree : deallocateLocal m old = .ok m1) :
    evalStatementV2 body (frameV2 defId b i l) m cm (.storageLive lid) =
      .step (stateV2 (frameV2 defId b (i + 1) l1) cm m1) := by
  unfold evalStatementV2
  dsimp only
  rw [hTy, hOld]
  dsimp only
  rw [hSet]
  dsimp only
  rw [hFree]

/-- `StorageDead` of a non-return local whose old slot deallocates
successfully. -/
theorem evalStatementV2_storageDead {body : Body} {defId : DefId} {b i : Nat}
    {l l1 : List LocalSlot} {cm : CallerMemory} {m m1 : MemoryState}
    {lid : LocalId} {old : LocalSlot}
    (hNotRet : Nat.beq lid 0 = false)
    (hOld : Trusted.MirSemantics.getElem? l lid = some old)
    (hSet : setElem? l lid .dead = some l1)
    (hFree : deallocateLocal m old = .ok m1) :
    evalStatementV2 body (frameV2 defId b i l) m cm (.storageDead lid) =
      .step (stateV2 (frameV2 defId b (i + 1) l1) cm m1) := by
  unfold evalStatementV2
  dsimp only
  rw [ite_bool_false hNotRet, hOld]
  dsimp only
  rw [hSet]
  dsimp only
  rw [hFree]

/-- `Nop` advances to the next statement. -/
theorem evalStatementV2_nop {body : Body} {defId : DefId} {b i : Nat}
    {l : List LocalSlot} {cm : CallerMemory} {m : MemoryState} :
    evalStatementV2 body (frameV2 defId b i l) m cm .nop =
      .step (stateV2 (frameV2 defId b (i + 1) l) cm m) := rfl

/-- `Goto` jumps to the first statement of its target block. -/
theorem evalTerminatorV2_goto {body : Body} {bb : BasicBlock} {defId : DefId}
    {b i : Nat} {l : List LocalSlot} {cm : CallerMemory} {m : MemoryState}
    {ps : PanicStrategy} {hLocal oc : Bool} {target : BasicBlockId}
    (hTerm : bb.terminator = .goto target) :
    evalTerminatorV2 body bb (frameV2 defId b i l) m cm ps hLocal oc =
      .step (stateV2 (frameV2 defId target 0 l) cm m) := by
  unfold evalTerminatorV2
  rw [hTerm]
  rfl

/-- One `StorageLive` step. -/
theorem evalStepV2_storageLive {p : Program} {body : Body} {bb : BasicBlock}
    {defId : DefId} {b i : Nat} {l l1 : List LocalSlot}
    {cm : CallerMemory} {m m1 : MemoryState} {lid : LocalId} {ty : MirTy}
    {old : LocalSlot}
    (hBody : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (hBB : Trusted.MirSemantics.getElem? body.basicBlocks b = some bb)
    (hStmt : Trusted.MirSemantics.getElem? bb.statements i =
      some (.storageLive lid))
    (hTy : Trusted.MirSemantics.getElem? body.locals lid = some ty)
    (hOld : Trusted.MirSemantics.getElem? l lid = some old)
    (hSet : setElem? l lid (liveUninitSlot ty) = some l1)
    (hFree : deallocateLocal m old = .ok m1) :
    evalStepV2 p (stateV2 (frameV2 defId b i l) cm m) =
      .step (stateV2 (frameV2 defId b (i + 1) l1) cm m1) :=
  (evalStepV2_stmt hBody hBB hStmt).trans
    (evalStatementV2_storageLive hTy hOld hSet hFree)

/-- One `StorageDead` step. -/
theorem evalStepV2_storageDead {p : Program} {body : Body} {bb : BasicBlock}
    {defId : DefId} {b i : Nat} {l l1 : List LocalSlot}
    {cm : CallerMemory} {m m1 : MemoryState} {lid : LocalId}
    {old : LocalSlot}
    (hBody : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (hBB : Trusted.MirSemantics.getElem? body.basicBlocks b = some bb)
    (hStmt : Trusted.MirSemantics.getElem? bb.statements i =
      some (.storageDead lid))
    (hNotRet : Nat.beq lid 0 = false)
    (hOld : Trusted.MirSemantics.getElem? l lid = some old)
    (hSet : setElem? l lid .dead = some l1)
    (hFree : deallocateLocal m old = .ok m1) :
    evalStepV2 p (stateV2 (frameV2 defId b i l) cm m) =
      .step (stateV2 (frameV2 defId b (i + 1) l1) cm m1) :=
  (evalStepV2_stmt hBody hBB hStmt).trans
    (evalStatementV2_storageDead hNotRet hOld hSet hFree)

/-- One `Nop` step. -/
theorem evalStepV2_nop {p : Program} {body : Body} {bb : BasicBlock}
    {defId : DefId} {b i : Nat} {l : List LocalSlot}
    {cm : CallerMemory} {m : MemoryState}
    (hBody : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (hBB : Trusted.MirSemantics.getElem? body.basicBlocks b = some bb)
    (hStmt : Trusted.MirSemantics.getElem? bb.statements i = some .nop) :
    evalStepV2 p (stateV2 (frameV2 defId b i l) cm m) =
      .step (stateV2 (frameV2 defId b (i + 1) l) cm m) :=
  (evalStepV2_stmt hBody hBB hStmt).trans evalStatementV2_nop

/-- One `Goto` step. -/
theorem evalStepV2_goto {p : Program} {body : Body} {bb : BasicBlock}
    {defId : DefId} {b i : Nat} {l : List LocalSlot}
    {cm : CallerMemory} {m : MemoryState} {target : BasicBlockId}
    (hBody : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (hBB : Trusted.MirSemantics.getElem? body.basicBlocks b = some bb)
    (hStmt : Trusted.MirSemantics.getElem? bb.statements i = none)
    (hEnd : Nat.beq i bb.statements.length = true)
    (hTerm : bb.terminator = .goto target) :
    evalStepV2 p (stateV2 (frameV2 defId b i l) cm m) =
      .step (stateV2 (frameV2 defId target 0 l) cm m) :=
  (evalStepV2_term hBody hBB hStmt hEnd).trans (evalTerminatorV2_goto hTerm)

/-- A `return` step that returns a value whose references stay in caller
memory, in a body whose return type has no raw pointers. -/
theorem evalStepV2_return_ok {p : Program} {body : Body} {bb : BasicBlock}
    {defId : DefId} {b i : Nat} {l : List LocalSlot}
    {cm : CallerMemory} {m : MemoryState} {retTy : MirTy} {retVal : Val}
    (hBody : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (hBB : Trusted.MirSemantics.getElem? body.basicBlocks b = some bb)
    (hStmt : Trusted.MirSemantics.getElem? bb.statements i = none)
    (hEnd : Nat.beq i bb.statements.length = true)
    (hTerm : bb.terminator = .return_)
    (hCleanup : bb.cleanup = false)
    (hRetTy : Trusted.MirSemantics.getElem? body.locals 0 = some retTy)
    (hRetSlot : Trusted.MirSemantics.getElem? l 0 =
      some (.immediate (some retVal)))
    (hStay : refsStayInCallerMem cm retTy retVal = true)
    (hValid : refsValidInMem m retTy retVal = true)
    (hDisj : spansPairwiseDisjoint (refAccessSpans retTy retVal) = true)
    (hNoRaw : tyHasRawPtrV2 retTy = false := by rfl) :
    evalStepV2 p (stateV2 (frameV2 defId b i l) cm m) =
      .done (.returned ⟨retVal, extractCallerMemory cm m⟩) :=
  (evalStepV2_term hBody hBB hStmt hEnd).trans
    (evalTerminatorV2_return_ok hTerm hCleanup hRetTy hRetSlot hStay hValid
      hDisj hNoRaw)

/-! ## Runs -/

/-- `post` holds on the outcome reached from `s` after finitely many steps,
none of which faults. -/
abbrev RunsV2 (p : Program) (post : TerminalOut → Prop)
    (s : State) : Prop :=
  ∃ fuel, execOutcomeStateV2 p post (fun _ => False) fuel s

theorem runsV2_step {p : Program} {s s' : State} {post : TerminalOut → Prop}
    (hStep : evalStepV2 p s = .step s') (hRest : RunsV2 p post s') :
    RunsV2 p post s :=
  let ⟨fuel, h⟩ := hRest
  ⟨fuel + 1, execOutcomeStateV2_step hStep h⟩

theorem runsV2_done {p : Program} {s : State} {out : TerminalOut}
    {post : TerminalOut → Prop}
    (hDone : evalStepV2 p s = .done out) (hPost : post out) :
    RunsV2 p post s :=
  ⟨1, execOutcomeStateV2_done hDone hPost⟩

/-- Package a run from the entry state as an `execProgV2` statement. -/
theorem execProgV2_of_runsV2 {p : Program} {q : Query} {s₀ : State}
    {post : TerminalOut → Prop} (hInit : initStateV2 p q = .ok s₀)
    (hRuns : RunsV2 p post s₀) : ∃ fuel, execProgV2 p fuel q post :=
  let ⟨fuel, h⟩ := hRuns
  ⟨fuel, by unfold execProgV2; rw [hInit]; exact h⟩

end Anneal.MirWp

end
