-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- anneal-trust-tier: candidate:refinement
module
prelude
public import Init.NotationExtra
public import Init.Data.List.Basic
public import Trusted.CppAst
public import Trusted.CppSemantics.State
public import Trusted.CppSemantics.Memory
public import Trusted.CppSemantics.Eval

@[expose] public section

namespace Trusted.CppSemantics

open Trusted.CppAst

/-!
# Rung-0 C11 Small-Step Transition and Execution Predicates
(`Trusted.CppSemantics.Step`)

Deterministic tactic-free small-step semantics (`initCppState`, `evalStep`)
and unbounded execution predicates (`CppReaches`, `CppReachesResult`,
`CppWellFormed`, `CppBehavior`, `CppDiverges`, `CppFaultsUB`) for Rung-0 C11.
-/

/-- Construct initial local slots for a function frame:
- Local `0` (return slot): `.val .void` when `ret = .void`, else `.uninit`.
- Locals `1..=K` (parameters): `.val arg_i`.
- Locals `K+1..` (user locals and SSENF temporaries): `.uninit` (reading before
  initialization faults `.undefined`). -/
noncomputable def initLocalSlotsAux (args : List CppVal) :
    List CppLocalDecl → List CppLocalSlot
  | [] => []
  | _ :: rest =>
    match args with
    | v :: vs => .val v :: initLocalSlotsAux vs rest
    | []      => .uninit :: initLocalSlotsAux [] rest

/-- Build the initial local slot array for `body` given argument values `args`.
-/
noncomputable def initLocalSlots (body : CppBody) (args : List CppVal) :
    List CppLocalSlot :=
  match body.locals with
  | [] => []
  | retDecl :: rest =>
    let retSlot := match retDecl.ty with
      | .void => CppLocalSlot.val .void
      | _     => CppLocalSlot.uninit
    retSlot :: initLocalSlotsAux args rest

/-- C++ reference (and `this`) parameters flagged in `paramNonNull` must be
bound to an object (C++20 [dcl.ref]p5): the pointer argument must point to a
suitably aligned `pointee` lying entirely inside a live allocation. -/
noncomputable def refArgsOk (policy : CppLangPolicy)
    (records : List CppRecordDef) (mem : CppMemory) :
    List Bool → List CppTy → List CppVal → Bool
  | true :: fs, t :: ts, v :: vs =>
    (match t, v with
     | .ptr pointee _ _ _, .ptr (some aid) addr sr =>
       match cppTySize? policy records pointee,
             cppTyAlign? policy records pointee with
       | some sz, some al =>
         placeInBounds mem (some aid) addr sz && subRangeContains sr addr sz &&
           Nat.beq (Nat.mod addr al) 0
       | _, _ => false
     | _, _ => false) &&
      refArgsOk policy records mem fs ts vs
  | false :: fs, _ :: ts, _ :: vs => refArgsOk policy records mem fs ts vs
  | _, _, _ => true

/-- Initialize execution state for `prog` at `prog.entryDefId` on query `q`. -/
noncomputable def initCppState (prog : CppProgram) (q : CppQuery) :
    Except CppFaultKind CppState :=
  if !prog.policy.exceptionsOff then
    .error .unsupported
  else if !Nat.beq prog.policy.pointerWidthBits 64 ||
          !prog.policy.littleEndian then
    .error .unsupported
  else if !validCppMemory q.mem then
    .error .unsupported
  else
    match cppGetElem? prog.bodies prog.entryDefId with
    | none => .error .unsupported
    | some body =>
      if body.isExternal then
        .error .unsupported
      else if !checkCppArgs prog.policy prog.records q.args body.sig.params ||
              !argsLiveInMem prog.policy prog.records q.mem q.args
                body.sig.params then
        .error .unsupported
      else if !refArgsOk prog.policy prog.records q.mem body.sig.paramNonNull
                 body.sig.params q.args then
        .error .unsupported
      else if Nat.ble body.blocks.length body.entryBlock then
        .error .unsupported
      else
        let frame : CppFrame := {
          defId := prog.entryDefId
          blockId := body.entryBlock
          stmtIdx := 0
          locals := initLocalSlots body q.args
          retDst := none
          retBlock := 0
          stackAllocs := []
        }
        .ok { frames := [frame], mem := q.mem }

/-- `true` iff `place` designates memory: it has projections, or its local
has been moved to the stack. -/
noncomputable def placeInMemory (frame : CppFrame) (place : CppPlace) : Bool :=
  match place.projs with
  | _ :: _ => true
  | [] =>
    match cppGetElem? frame.locals place.base with
    | some (.stackAddr _) => true
    | _ => false

/-- Guard for an aggregate assignment `dst = src` (C11 §6.5.16.1p3): when both
sides are in memory, their objects must coincide exactly or not overlap at
all; partial overlap is `.undefined`. Resolves `dst` first (moving its base to
memory if needed) and returns the updated frame and memory. -/
noncomputable def assignOverlapCheck (prog : CppProgram) (body : CppBody)
    (frame : CppFrame) (mem : CppMemory) (dst : CppPlace) (dstTy : CppTy)
    (rhs : CppExpr) : Except CppFaultKind (CppFrame × CppMemory) :=
  let isAgg := match dstTy with
    | .array _ _ | .record _ => true
    | _ => false
  match rhs with
  | .readPlace src _ =>
    if isAgg && placeInMemory frame src && placeInMemory frame dst then
      match resolvePlaceAddr prog body frame mem false dst with
      | .error k => .error k
      | .ok (rd, f2, m2) =>
        match resolvePlaceAddr prog body f2 m2 false src,
              cppTySize? prog.policy prog.records dstTy with
        | .ok (rs, _, _), some sz =>
          let partialOverlap := match rs.allocId, rd.allocId with
            | some a, some b =>
              Nat.beq a b && Nat.blt 0 sz && !Nat.beq rs.addr rd.addr &&
                Nat.blt rs.addr (rd.addr + sz) && Nat.blt rd.addr (rs.addr + sz)
            | _, _ => false
          if partialOverlap then .error .undefined else .ok (f2, m2)
        | .error k, _ => .error k
        | _, none => .error .unsupported
    else .ok (frame, mem)
  | _ => .ok (frame, mem)

/-- Zero-initialize the object `dst` designates in memory, padding included
(C++20 [dcl.init]p6). -/
noncomputable def zeroInitInMemory (prog : CppProgram) (body : CppBody)
    (frame : CppFrame) (mem : CppMemory) (dst : CppPlace) (ty : CppTy) :
    Except CppFaultKind (CppFrame × CppMemory) :=
  match resolvePlaceAddr prog body frame mem false dst with
  | .error k => .error k
  | .ok (r, f2, m2) =>
    if !CppTy.beq r.ty ty then .error .unsupported
    else
      match writeZeroMemory prog.policy prog.records m2 r.allocId r.addr ty
              r.alignCap with
      | .error k => .error k
      | .ok m3 => .ok (f2, m3)

/-- Zero-initialize uninitialized aggregate local `lid` of type `ty`: place it
in fresh zeroed stack storage, which becomes read-only if the local is
`const`. -/
noncomputable def zeroInitFreshLocal (prog : CppProgram) (frame : CppFrame)
    (mem : CppMemory) (lid : LocalId) (ty : CppTy) :
    Except CppFaultKind (CppFrame × CppMemory) :=
  match cppTySize? prog.policy prog.records ty,
        cppTyAlign? prog.policy prog.records ty with
  | some sz, some al =>
    let (aid, mem1) := allocStack mem sz al false (some ty)
    if !Nat.blt mem1.nextAddr ptrAddrBound then .error .unsupported
    else
      match findAlloc? aid mem1.allocs with
      | none => .error .undefined
      | some alloc =>
        match writeZeroMemory prog.policy prog.records mem1 (some aid)
                alloc.baseAddr ty none with
        | .error k => .error k
        | .ok m2 =>
          match cppSetElem? frame.locals lid (.stackAddr aid) with
          | none => .error .unsupported
          | some locs' =>
            .ok ({ frame with locals := locs',
                              stackAllocs := aid :: frame.stackAllocs }, m2)
  | _, _ => .error .unsupported

/-- Execute one `CppStmt` inside the top call frame. -/
noncomputable def evalStmt (prog : CppProgram) (body : CppBody)
    (frame : CppFrame) (mem : CppMemory) (stmt : CppStmt) :
    Except CppFaultKind (CppFrame × CppMemory) :=
  match stmt with
  | .storageLive lid =>
    match cppSetElem? frame.locals lid .uninit with
    | some locs' =>
      .ok ({ frame with locals := locs', stmtIdx := frame.stmtIdx + 1 }, mem)
    | none => .error .unsupported
  | .storageDead lid =>
    match cppGetElem? frame.locals lid with
    | none => .error .unsupported
    | some (.stackAddr aid) =>
      let mem' := freeAlloc mem aid
      match cppSetElem? frame.locals lid .dead with
      | some locs' =>
        .ok ({ frame with locals := locs', stmtIdx := frame.stmtIdx + 1 }, mem')
      | none => .error .unsupported
    | some _ =>
      match cppSetElem? frame.locals lid .dead with
      | some locs' =>
        .ok ({ frame with locals := locs', stmtIdx := frame.stmtIdx + 1 }, mem)
      | none => .error .unsupported
  | .assign dst dstTy rhs =>
    match evalExpr prog body frame mem rhs with
    | .error k => .error k
    | .ok (v, f1, m1) =>
      if !checkCppVal prog.policy prog.records v dstTy then
        .error .unsupported
      else
        match assignOverlapCheck prog body f1 m1 dst dstTy rhs with
        | .error k => .error k
        | .ok (f2, m2) =>
          match writePlaceVal prog body f2 m2 dst dstTy v with
          | .error k => .error k
          | .ok (f3, m3) =>
            .ok ({ f3 with stmtIdx := f3.stmtIdx + 1 }, m3)
  | .zeroInit dst ty =>
    -- A scalar local is stored directly; anything else is zeroed in memory,
    -- padding included (C++20 [dcl.init]p6).
    let res : Except CppFaultKind (CppFrame × CppMemory) :=
      match dst.projs, zeroValOf? ty with
      | [], some v => writePlaceVal prog body frame mem dst ty v
      | [], none =>
        -- A whole aggregate local: an uninitialized one gets fresh zeroed
        -- storage (read-only if `const`); re-zeroing a `const` one modifies
        -- a `const` object.
        match cppGetElem? body.locals dst.base,
              cppGetElem? frame.locals dst.base with
        | some decl, some .uninit =>
          if !CppTy.beq decl.ty ty then .error .unsupported
          else
            match zeroInitFreshLocal prog frame mem dst.base ty with
            | .error k => .error k
            | .ok (f2, m2) =>
              match f2.stackAllocs with
              | aid :: _ =>
                if decl.isConst then
                  match setAllocConst m2 aid with
                  | .ok m3   => .ok (f2, m3)
                  | .error k => .error k
                else .ok (f2, m2)
              | [] => .error .unsupported
        | some decl, _ =>
          if decl.isConst then .error .undefined
          else zeroInitInMemory prog body frame mem dst ty
        | none, _ => .error .unsupported
      | _ :: _, _ => zeroInitInMemory prog body frame mem dst ty
    match res with
    | .error k => .error k
    | .ok (f2, m2) => .ok ({ f2 with stmtIdx := f2.stmtIdx + 1 }, m2)

/-- Execute one `CppTerminator` inside the top call frame. -/
noncomputable def evalTerminator (prog : CppProgram) (body : CppBody)
    (frame : CppFrame) (callers : List CppFrame) (mem : CppMemory)
    (term : CppTerminator) : CppStepResult CppState CppTerminalOut :=
  match term with
  | .goto target =>
    if Nat.blt target body.blocks.length then
      .step { frames := { frame with blockId := target, stmtIdx := 0 }
                          :: callers,
              mem := mem }
    else
      .fault .unsupported
  | .branch cond thenTarget elseTarget =>
    match evalExpr prog body frame mem cond with
    | .error k => .fault k
    | .ok (v, f1, m1) =>
      match v with
      | .bool b =>
        let target := if b then thenTarget else elseTarget
        if Nat.blt target body.blocks.length then
          .step { frames := { f1 with blockId := target, stmtIdx := 0 }
                              :: callers,
                  mem := m1 }
        else
          .fault .unsupported
      | _ => .fault .unsupported
  | .call callee args dst next =>
    match evalExprList prog body frame mem args with
    | .error k => .fault k
    | .ok (argVals, f1, m1) =>
      match findBodyByName? prog.bodies callee with
      | none => .fault .unsupported
      | some (calleeId, calleeBody) =>
        if calleeBody.isExternal then
          .fault .unsupported
        else if !checkCppArgs prog.policy prog.records argVals
                   calleeBody.sig.params then
          .fault .unsupported
        else if !refArgsOk prog.policy prog.records m1
                   calleeBody.sig.paramNonNull calleeBody.sig.params
                   argVals ||
                !argsLiveInMem prog.policy prog.records m1 argVals
                   calleeBody.sig.params then
          .fault .undefined
        else if !(match dst with
                  | some (p, _) => p.projs.isEmpty
                  | none => true) then
          -- C11 §6.5.16p3 leaves a projected destination's evaluation
          -- unsequenced with the call; only whole locals are admitted.
          .fault .unsupported
        else if Nat.ble calleeBody.blocks.length calleeBody.entryBlock then
          .fault .unsupported
        else if Nat.ble body.blocks.length next then
          .fault .unsupported
        else
          let calleeFrame : CppFrame := {
            defId := calleeId
            blockId := calleeBody.entryBlock
            stmtIdx := 0
            locals := initLocalSlots calleeBody argVals
            retDst := dst
            retBlock := next
            stackAllocs := []
          }
          .step { frames := calleeFrame :: f1 :: callers, mem := m1 }
  | .ret =>
    let retRes : Except CppFaultKind CppVal :=
      match body.sig.ret with
      | .void => .ok .void
      | _     => readLocalScalar prog body frame mem 0
    match retRes with
    | .error k => .fault k
    | .ok retVal =>
      if !checkCppVal prog.policy prog.records retVal body.sig.ret then
        .fault .unsupported
      else
      let mem' := freeAllocs mem frame.stackAllocs
      -- Returning a pointer to a local of the returning function yields a
      -- dangling, indeterminate value (C11 §6.2.4p2).
      if !valLiveInMem prog.policy prog.records mem' retVal body.sig.ret then
        .fault .undefined
      else
      match callers with
      | [] => .done (.returned { ret := retVal, mem := mem' })
      | caller :: restCallers =>
        match cppGetElem? prog.bodies caller.defId with
        | none => .fault .unsupported
        | some callerBody =>
          match frame.retDst with
          | none =>
            .step { frames := { caller with blockId := frame.retBlock,
                                            stmtIdx := 0 } :: restCallers,
                    mem := mem' }
          | some (dstPlace, dstTy) =>
            if !CppTy.beq body.sig.ret dstTy || !dstPlace.projs.isEmpty then
              .fault .unsupported
            else
            match writePlaceVal prog callerBody caller mem' dstPlace dstTy
                    retVal with
            | .error k => .fault k
            | .ok (caller', mem'') =>
              .step { frames := { caller' with blockId := frame.retBlock,
                                               stmtIdx := 0 } :: restCallers,
                      mem := mem'' }
  | .unreachable => .fault .undefined

/-- Deterministic single-step operational transition for Rung-0 C11. -/
noncomputable def evalStep (prog : CppProgram) (s : CppState) :
    CppStepResult CppState CppTerminalOut :=
  match s.frames with
  | [] => .fault .unsupported
  | frame :: callers =>
    match cppGetElem? prog.bodies frame.defId with
    | none => .fault .unsupported
    | some body =>
      match cppGetElem? body.blocks frame.blockId with
      | none => .fault .unsupported
      | some blk =>
        match cppGetElem? blk.stmts frame.stmtIdx with
        | some stmt =>
          match evalStmt prog body frame s.mem stmt with
          | .error k          => .fault k
          | .ok (frame', mem') =>
            .step { frames := frame' :: callers, mem := mem' }
        | none =>
          evalTerminator prog body frame callers s.mem blk.term

/-- Unbounded finite-step reachability between intermediate `CppState`s. -/
inductive CppReaches (prog : CppProgram) : CppState → CppState → Prop where
  | refl (s : CppState) : CppReaches prog s s
  | tail {s1 s2 s3 : CppState} :
      CppReaches prog s1 s2 →
      evalStep prog s2 = .step s3 →
      CppReaches prog s1 s3

/-- Outcome `res` is reached from `(prog, q)` (either at entry via
`initCppState` or in finitely many steps from `s0`). -/
def CppReachesResult (prog : CppProgram) (q : CppQuery)
    (res : CppStepResult CppState CppTerminalOut) : Prop :=
  match initCppState prog q with
  | .error k => res = .fault k
  | .ok s0 =>
    ∃ s : CppState, CppReaches prog s0 s ∧ evalStep prog s = res

/-- All-prefix well-formedness in Rung-0 C11: entry succeeds
(`initCppState prog q = .ok s0`) and no reachable transition faults
(`.undefined` or `.unsupported`). -/
def CppWellFormed (prog : CppProgram) (q : CppQuery) : Prop :=
  (∃ s0 : CppState, initCppState prog q = .ok s0) ∧
  (∀ k : CppFaultKind, ¬ CppReachesResult prog q (.fault k))

/-- Observable terminal behavior of `(prog, q)` in Rung-0 C11. -/
def CppBehavior (prog : CppProgram) (q : CppQuery)
    (out : CppTerminalOut) : Prop :=
  CppReachesResult prog q (.done out)

/-- Infinite-trace divergence of `(prog, q)` in Rung-0 C11. -/
def CppDiverges (prog : CppProgram) (q : CppQuery) : Prop :=
  ∃ s0 : CppState,
    initCppState prog q = .ok s0 ∧
    ∃ trace : Nat → CppState,
      trace 0 = s0 ∧
      ∀ n : Nat, evalStep prog (trace n) = .step (trace (n + 1))

/-- Existential UB fault witness predicate in Rung-0 C11. -/
def CppFaultsUB (prog : CppProgram) (q : CppQuery) : Prop :=
  CppReachesResult prog q (.fault .undefined)

end Trusted.CppSemantics

end
