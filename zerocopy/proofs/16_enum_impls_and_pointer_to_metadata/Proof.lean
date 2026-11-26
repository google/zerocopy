-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.SimpLemmas
import Init.Data.List.Basic
import Init.RCases
import Expected
import Anneal.MirWp.V2StepShield

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

/-! ## Shared Plumbing -/

/-- An exact-outcome execution yields well-formedness and `returnsExactly`. -/
private theorem returnsExactly_of_exec {defId : DefId} {q : Query}
    {fuel : Nat} {out : TerminalOut}
    (hExec : execProgV2 (entryProgForBody Captured.program defId) fuel q
      (fun o => o = out)) :
    WellFormedV2 (entryProgForBody Captured.program defId) q ∧
    Spec.returnsExactly Captured.program defId q out := by
  have hRes := spec_and_behaviorV2_of_exec_eq hExec
  exact ⟨hRes.1, hRes.2.1, hRes.2.2.2 _ rfl⟩

/-- A valid entry of a one-parameter body passes exactly one argument. -/
private theorem single_arg_of_valid {body : Body} {q : Query} {t : MirTy}
    (hParams : (body.locals.drop 1).take body.argumentCount = [t])
    (hValid : ValidEntryArgsV2 body q) :
    ∃ v : Val, q.args = [v] := by
  have hMatch : checkArgsMatchV2 q.args [t] = true := by
    have h : checkArgsMatchV2 q.args
        ((body.locals.drop 1).take body.argumentCount) = true := hValid.2.1
    rw [hParams] at h
    exact h
  let ⟨v, hArgs, _⟩ := checkArgsMatchV2_singleton_inv hMatch
  exact ⟨v, hArgs⟩

/-- Returning from an entry state built by `entryMemoryForArgsV2` without
touching memory hands the caller its memory back unchanged. The raw-pointer
`AllocId` bound that `entryMemoryForArgsV2` adds changes only `nextAllocId`,
so its allocations are the caller's, as in `extractCallerMemory_entry`. -/
private theorem extractCallerMemory_forArgs (cm : CallerMemory)
    (paramTys : List MirTy) (args : List Val)
    (hValid : validCallerMemory cm = true) :
    extractCallerMemory cm (entryMemoryForArgsV2 cm paramTys args) = cm := by
  cases cm with
  | mk allocs =>
    unfold extractCallerMemory
    have hAllocs :
        (entryMemoryForArgsV2 ⟨allocs⟩ paramTys args).allocations = allocs :=
      entryMemoryForArgsV2_allocations_eq ⟨allocs⟩ paramTys args
    have hEq := extractCallerAllocations_suffix
      (entryMemoryForArgsV2 ⟨allocs⟩ paramTys args) [] allocs hAllocs
      (by
        rw [hAllocs]
        exact findAllocation_in_allocIdsValid [] allocs []
          (fun _ hz => by cases hz) (fun _ hz => by cases hz) hValid)
    rw [hEq]

/-! ## Unit-Returning Bodies (`_0 = const (); return`) -/

/-- A one-parameter body whose return local starts as `()` and which steps by
`_0 = const ()` and then `return` returns `()` with caller memory unchanged on
every valid entry. -/
private theorem unit_body_exec {defId : DefId} {body : Body} {t : MirTy}
    (hBody :
      Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (hAdm : BodyStaticAdmittedV2 Captured.program body = true)
    (hParams : (body.locals.drop 1).take body.argumentCount = [t])
    (hInit : ∀ v : Val, initLocalsLoop body [v] 0 body.locals =
      [.immediate (some .unit), .immediate (some v)])
    (hStep1 : ∀ (v : Val) (cm : CallerMemory) (m : MemoryState),
      evalStepV2 (entryProgForBody Captured.program defId)
        (stateV2 (frameV2 defId 0 0
          [.immediate (some .unit), .immediate (some v)]) cm m) =
      .step (stateV2 (frameV2 defId 0 1
        [.immediate (some .unit), .immediate (some v)]) cm m))
    (hStep2 : ∀ (v : Val) (cm : CallerMemory) (m : MemoryState),
      evalStepV2 (entryProgForBody Captured.program defId)
        (stateV2 (frameV2 defId 0 1
          [.immediate (some .unit), .immediate (some v)]) cm m) =
      .done (.returned ⟨.unit, extractCallerMemory cm m⟩))
    (q : Query) (hValid : ValidEntryArgsV2 body q) :
    execProgV2 (entryProgForBody Captured.program defId) 2 q
      (fun o => o = .returned ⟨.unit, q.callerMem⟩) := by
  let ⟨v, hArgs⟩ := single_arg_of_valid hParams hValid
  have hCM : validCallerMemory q.callerMem = true := hValid.1
  let ctx : BodyCtx := ⟨Captured.program, defId, body⟩
  have hInitState :
      initStateV2 (entryProgForBody Captured.program defId) q =
      .ok (stateV2 (frameV2 defId 0 0
        [.immediate (some .unit), .immediate (some v)])
        q.callerMem (entryMemoryForArgsV2 q.callerMem
          ((body.locals.drop 1).take body.argumentCount) [v])) := by
    have h := ctx.initStateV2_ok_frameV2_forArgs hBody hAdm hValid
    rw [hArgs, hInit] at h
    exact h
  unfold execProgV2
  rw [hInitState]
  apply execOutcomeStateV2_step (hStep1 v _ _)
  exact execOutcomeStateV2_done (hStep2 v _ _)
    (by rw [extractCallerMemory_forArgs q.callerMem _ _ hCM])

/-- `unit_body_exec` packaged as `BodyVerifiedV2` plus `unitBodyPost`. -/
private theorem unit_body_verified {defId : DefId} {body : Body} {t : MirTy}
    {identity : String}
    (hBody :
      Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (hAdm : BodyStaticAdmittedV2 Captured.program body = true)
    (hId : body.identity = identity)
    (hSafe : body.isUnsafe = false)
    (hParams : (body.locals.drop 1).take body.argumentCount = [t])
    (hInit : ∀ v : Val, initLocalsLoop body [v] 0 body.locals =
      [.immediate (some .unit), .immediate (some v)])
    (hStep1 : ∀ (v : Val) (cm : CallerMemory) (m : MemoryState),
      evalStepV2 (entryProgForBody Captured.program defId)
        (stateV2 (frameV2 defId 0 0
          [.immediate (some .unit), .immediate (some v)]) cm m) =
      .step (stateV2 (frameV2 defId 0 1
        [.immediate (some .unit), .immediate (some v)]) cm m))
    (hStep2 : ∀ (v : Val) (cm : CallerMemory) (m : MemoryState),
      evalStepV2 (entryProgForBody Captured.program defId)
        (stateV2 (frameV2 defId 0 1
          [.immediate (some .unit), .immediate (some v)]) cm m) =
      .done (.returned ⟨.unit, extractCallerMemory cm m⟩)) :
    BodyVerifiedV2 Captured.program defId body
      (Spec.specs.safety body.identity) ∧
    Spec.unitBodyPost Captured.program defId identity := by
  have hExec := unit_body_exec hBody hAdm hParams hInit hStep1 hStep2
  refine ⟨⟨hBody, hAdm, fun q hValid _ =>
    (returnsExactly_of_exec (hExec q hValid)).1⟩, ?_⟩
  unfold Spec.unitBodyPost
  rw [hBody]
  exact ⟨hId, hSafe, fun q hValid =>
    (returnsExactly_of_exec (hExec q hValid)).2⟩

/-- Body 1: `<byteorder::Order as Eq>::assert_fields_are_eq`. -/
private theorem body1_verified :
    BodyVerifiedV2 Captured.program 1 Captured.body_1
      (Spec.specs.safety Captured.body_1.identity) ∧
    Spec.unitBodyPost Captured.program 1 Spec.orderAssertEqId :=
  unit_body_verified rfl (by decide) (by decide) rfl rfl (fun _ => rfl)
    (fun _ _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

/-! ## Fieldless-Enum Pointees -/

private theorem bool_and_left' {a b : Bool} (h : (a && b) = true) :
    a = true := by
  cases a <;> first | rfl | nomatch h

private theorem bool_and_right' {a b : Bool} (h : (a && b) = true) :
    b = true := by
  cases a <;> cases b <;> first | rfl | nomatch h

private theorem bool_or_false_elim {a b : Bool} (h : (a || b) = false) :
    a = false ∧ b = false := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | nomatch h

/-- A valid shared reference to a one-byte fieldless enum is a pointer with
provenance whose pointee loads as some value. -/
private theorem enum_ref_load {m : MemoryState} {ety : EnumTy} {v : Val}
    (hLay : layoutOfTyV2 (.enum ety) = some ⟨1, 0⟩)
    (hRef : refValidInMem m .shared (.enum ety) v = .ok ()) :
    ∃ (aid : AllocId) (off : UInt64) (w : IntWidth) (v0 : Val),
      v = .ptr ⟨some aid, off, w⟩ ∧
      loadIndirectV2 m (.enum ety) ⟨aid, off.toNat⟩ = .ok (some v0) := by
  cases v
  case ptr p =>
    cases p with
    | mk pAid off w =>
      unfold refValidInMem at hRef
      dsimp only at hRef
      have hSupT : isSupportedV2PointeeTy (.enum ety) = true := by
        cases hSup : isSupportedV2PointeeTy (.enum ety) with
        | true => rfl
        | false =>
          rw [ite_bool_true (b := !isSupportedV2PointeeTy (.enum ety))
            (by rw [hSup]; rfl)] at hRef
          nomatch hRef
      rw [ite_bool_false (b := !isSupportedV2PointeeTy (.enum ety))
        (by rw [hSupT]; rfl)] at hRef
      rw [hLay] at hRef
      cases pAid with
      | none =>
        dsimp only at hRef
        rw [show (Nat.beq off.toNat 0 || Nat.blt 0 1) = true by
          cases Nat.beq off.toNat 0 <;> rfl] at hRef
        nomatch hRef
      | some aid =>
        dsimp only at hRef
        cases hFind : findAllocation aid m.allocations with
        | none =>
          rw [hFind] at hRef
          nomatch hRef
        | some a =>
          rw [hFind] at hRef
          dsimp only at hRef
          cases hG : (!a.live || !isInBounds a off.toNat 1 ||
              !isAligned a off.toNat 0) with
          | true =>
            rw [hG] at hRef
            nomatch hRef
          | false =>
            rw [hG, ite_bool_false rfl,
              show (Mutability.beq Mutability.shared Mutability.mut &&
                !Mutability.beq a.mutability Mutability.mut) = false from rfl,
              ite_bool_false rfl] at hRef
            cases hD : decodeValV2 profileV2TargetEndian (.enum ety)
                ((a.bytes.drop off.toNat).take 1) with
            | error k =>
              rw [hD] at hRef
              nomatch hRef
            | ok r =>
              cases r with
              | none =>
                rw [hD] at hRef
                nomatch hRef
              | some v0 =>
                refine ⟨aid, off, w, v0, rfl, ?_⟩
                have hG1 := bool_or_false_elim hG
                have hG2 := bool_or_false_elim hG1.1
                have hLive : a.live = true := by
                  cases hl : a.live with
                  | true => rfl
                  | false => rw [hl] at hG2; nomatch hG2.1
                have hBnd : isInBounds a off.toNat 1 = true := by
                  cases hb : isInBounds a off.toNat 1 with
                  | true => rfl
                  | false => rw [hb] at hG2; nomatch hG2.2
                unfold loadIndirectV2
                rw [hLay]
                dsimp only
                rw [readBytes_ok_of_alloc hFind hLive hBnd (isAligned_zero a _)]
                exact hD
  all_goals (unfold refValidInMem at hRef; nomatch hRef)

private theorem findDiscrVariantAux_lt :
    ∀ (ds : List Nat) (idx : Nat) (bits : BitVec 128) (v : Nat),
      findDiscrVariantAux idx bits ds = some v → v < idx + ds.length
  | [], _, _, _, h => by nomatch h
  | d :: ds, idx, bits, v, h => by
    unfold findDiscrVariantAux at h
    cases hEq : (BitVec.ofNat 128 d == bits) with
    | true =>
      rw [hEq] at h
      injection h with hV
      rw [← hV]
      have hPos : 0 < ds.length + 1 := Nat.zero_lt_succ ds.length
      have hAdd := Nat.add_lt_add_left hPos idx
      rw [Nat.add_zero] at hAdd
      exact hAdd
    | false =>
      rw [hEq] at h
      have hLt := findDiscrVariantAux_lt ds (idx + 1) bits v h
      have hAssoc : idx + 1 + ds.length = idx + (ds.length + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 ds.length]
      rw [hAssoc] at hLt
      exact hLt

/-- A successful load of a one-byte scalar-tagged fieldless enum yields one of
its variants. -/
private theorem enum_load_shape {m : MemoryState} {place : MemPlace}
    {ety : EnumTy} {v0 : Val}
    (hLay : layoutOfTyV2 (.enum ety) = some ⟨1, 0⟩)
    (hLay1 : layoutOfTy (.enum ety) = some ⟨1, 0⟩)
    (hTag : ety.tagRepr = .scalar .i8 false)
    (hLoad : loadIndirectV2 m (.enum ety) place = .ok (some v0)) :
    ∃ i : Nat, v0 = .enumVal ety i ∧ i < ety.discriminants.length := by
  unfold loadIndirectV2 at hLoad
  rw [hLay] at hLoad
  dsimp only at hLoad
  cases hRB : readBytes m place 1 0 with
  | error k =>
    rw [hRB] at hLoad
    nomatch hLoad
  | ok bytes =>
    rw [hRB] at hLoad
    dsimp only at hLoad
    -- `decodeValV2` defers `.enum` to `decodeVal` definitionally; going through
    -- `rfl` rather than `unfold` keeps its equation lemma (and the
    -- `Quot.sound` that proof uses) out of this proof.
    rw [show decodeValV2 profileV2TargetEndian (.enum ety) bytes =
      decodeVal profileV2TargetEndian (.enum ety) bytes from rfl] at hLoad
    unfold decodeVal at hLoad
    rw [hLay1] at hLoad
    dsimp only at hLoad
    cases hLen : (!Nat.beq bytes.length 1) with
    | true =>
      rw [hLen, ite_bool_true rfl] at hLoad
      nomatch hLoad
    | false =>
      rw [hLen, ite_bool_false rfl,
        show Nat.beq 1 0 = false from rfl, ite_bool_false rfl] at hLoad
      cases hInit : initBytes? bytes with
      | none =>
        rw [hInit] at hLoad
        nomatch hLoad
      | some raw =>
        rw [hInit] at hLoad
        dsimp only at hLoad
        cases hC : evalConstLit (.enum ety)
            (.scalar (BitVec.ofNat 128 (decodeUInt profileV2TargetEndian raw)))
          with
        | error k =>
          rw [hC] at hLoad
          nomatch hLoad
        | ok v =>
          rw [hC] at hLoad
          injection hLoad with hSome
          injection hSome with hV
          subst hV
          unfold evalConstLit at hC
          dsimp only at hC
          rw [hTag] at hC
          dsimp only at hC
          cases hBad : (!enumAdmitted ety || truncateBits .i8
              (BitVec.ofNat 128 (decodeUInt profileV2TargetEndian raw)) !=
              BitVec.ofNat 128 (decodeUInt profileV2TargetEndian raw)) with
          | true =>
            rw [hBad, ite_bool_true rfl] at hC
            nomatch hC
          | false =>
            rw [hBad, ite_bool_false rfl] at hC
            cases hF : findDiscrVariant? (tagBitsToDiscrBits .i8 false
                ety.discrWidth
                (BitVec.ofNat 128 (decodeUInt profileV2TargetEndian raw)))
                ety.discriminants with
            | none =>
              rw [hF] at hC
              nomatch hC
            | some i =>
              rw [hF] at hC
              injection hC with hV
              refine ⟨i, hV.symm, ?_⟩
              have hLt := findDiscrVariantAux_lt ety.discriminants 0 _ i hF
              rw [Nat.zero_add] at hLt
              exact hLt

/-- Reading `*_lid` through a shared reference to a one-byte enum loads the
pointee. -/
private theorem readPlaceV2_deref_enum {bodyLocals : List MirTy}
    {l : List LocalSlot} {m : MemoryState} {lid : LocalId} {ety : EnumTy}
    {aid : AllocId} {off : UInt64} {w : IntWidth} {v0 : Val}
    (hLay : layoutOfTyV2 (.enum ety) = some ⟨1, 0⟩)
    (hTy : Trusted.MirSemantics.getElem? bodyLocals lid =
      some (.ref .shared (.enum ety)))
    (hSlot : Trusted.MirSemantics.getElem? l lid =
      some (.immediate (some (.ptr ⟨some aid, off, w⟩))))
    (hLoad : loadIndirectV2 m (.enum ety) ⟨aid, off.toNat⟩ = .ok (some v0)) :
    readPlaceV2 bodyLocals l m false ⟨lid, [.deref]⟩ =
      .ok (.enum ety, some v0, l, m) := by
  unfold readPlaceV2
  rw [hTy, hSlot]
  dsimp only
  rw [ite_bool_false rfl,
    ite_bool_false (b := !([] : List ProjectionElem).isEmpty) rfl,
    ite_bool_false (b := isUnsizedTy (.enum ety)) rfl, hLay]
  dsimp only
  rw [hLoad]

/-- `use (copy place)` evaluates to the value read from `place`. -/
private theorem evalRvalueV2_use_copy_of_read {bodyLocals : List MirTy}
    {l : List LocalSlot} {m : MemoryState} {ty : MirTy} {place : Place}
    {v0 : Val}
    (hRead : readPlaceV2 bodyLocals l m false place = .ok (ty, some v0, l, m))
    (hBeq : MirTy.beq ty ty = true) :
    evalRvalueV2 bodyLocals l m ty (.use (.copy place)) = .ok (v0, l, m) := by
  unfold evalRvalueV2
  dsimp only
  rw [show evalOperandToSlotV2 bodyLocals l m (.copy place) =
    readPlaceV2 bodyLocals l m false place from rfl, hRead]
  dsimp only
  rw [hBeq, ite_bool_false (b := !true) rfl]

/-- The single reference argument of a valid entry is a valid reference. -/
private theorem refValid_of_single {m : MemoryState} {pt : MirTy} {v : Val}
    (h : refsValidInMemList m [.ref .shared pt] [v] = true) :
    refValidInMem m .shared pt v = .ok () := by
  dsimp only [refsValidInMemList] at h
  unfold refsValidInMem at h
  cases hR : refValidInMem m .shared pt v with
  | error k =>
    rw [hR] at h
    nomatch h
  | ok u =>
    cases u
    rfl

private theorem derefEntry_of_load {q : Query} {ety : EnumTy} {aid : AllocId}
    {off : UInt64} {w : IntWidth} {v0 : Val}
    (hLoad : loadIndirectV2 (entryMemoryWithCaller q.callerMem) (.enum ety)
      ⟨aid, off.toNat⟩ = .ok (some v0)) :
    Spec.derefEntry q ety (.ptr ⟨some aid, off, w⟩) = some v0 := by
  unfold Spec.derefEntry
  dsimp only
  rw [hLoad]

/-! ## `Clone::clone` Bodies (`_0 = copy (*_1); return`) -/

private theorem clone_body_exec {defId : DefId} {body : Body} {ety : EnumTy}
    (hBody :
      Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (hAdm : BodyStaticAdmittedV2 Captured.program body = true)
    (hParams : (body.locals.drop 1).take body.argumentCount =
      [.ref .shared (.enum ety)])
    (hLay : layoutOfTyV2 (.enum ety) = some ⟨1, 0⟩)
    (hLay1 : layoutOfTy (.enum ety) = some ⟨1, 0⟩)
    (hTag : ety.tagRepr = .scalar .i8 false)
    (hInit : ∀ v : Val, initLocalsLoop body [v] 0 body.locals =
      [.immediate none, .immediate (some v)])
    (hStep1 : ∀ (aid : AllocId) (off : UInt64) (w : IntWidth) (i : Nat)
      (cm : CallerMemory) (m : MemoryState),
      loadIndirectV2 m (.enum ety) ⟨aid, off.toNat⟩ =
        .ok (some (.enumVal ety i)) →
      i < ety.discriminants.length →
      evalStepV2 (entryProgForBody Captured.program defId)
        (stateV2 (frameV2 defId 0 0
          [.immediate none, .immediate (some (.ptr ⟨some aid, off, w⟩))])
          cm m) =
      .step (stateV2 (frameV2 defId 0 1
        [.immediate (some (.enumVal ety i)),
         .immediate (some (.ptr ⟨some aid, off, w⟩))]) cm m))
    (hStep2 : ∀ (aid : AllocId) (off : UInt64) (w : IntWidth) (i : Nat)
      (cm : CallerMemory) (m : MemoryState),
      evalStepV2 (entryProgForBody Captured.program defId)
        (stateV2 (frameV2 defId 0 1
          [.immediate (some (.enumVal ety i)),
           .immediate (some (.ptr ⟨some aid, off, w⟩))]) cm m) =
      .done (.returned ⟨.enumVal ety i, extractCallerMemory cm m⟩))
    (q : Query) (hValid : ValidEntryArgsV2 body q) :
    ∃ self v : Val, q.args = [self] ∧ Spec.derefEntry q ety self = some v ∧
      execProgV2 (entryProgForBody Captured.program defId) 2 q
        (fun o => o = .returned ⟨v, q.callerMem⟩) := by
  let ⟨self, hArgs⟩ := single_arg_of_valid hParams hValid
  have hCM : validCallerMemory q.callerMem = true := hValid.1
  have hRefs : refsValidInMemList (entryMemoryWithCaller q.callerMem)
      [.ref .shared (.enum ety)] [self] = true := by
    have h : refsValidInMemList (entryMemoryWithCaller q.callerMem)
        ((body.locals.drop 1).take body.argumentCount) q.args = true :=
      hValid.2.2.1
    rw [hParams, hArgs] at h
    exact h
  let ⟨aid, off, w, v0, hSelf, hLoad⟩ := enum_ref_load hLay
    (refValid_of_single hRefs)
  let ⟨i, hV0, hi⟩ := enum_load_shape hLay hLay1 hTag hLoad
  subst hV0
  subst hSelf
  refine ⟨_, .enumVal ety i, hArgs, derefEntry_of_load hLoad, ?_⟩
  let ctx : BodyCtx := ⟨Captured.program, defId, body⟩
  have hInitState :
      initStateV2 (entryProgForBody Captured.program defId) q =
      .ok (stateV2 (frameV2 defId 0 0
        [.immediate none, .immediate (some (.ptr ⟨some aid, off, w⟩))])
        q.callerMem (entryMemoryWithCaller q.callerMem)) := by
    have hNoRaw : tyListHasRawPtrV2
        ((body.locals.drop 1).take body.argumentCount) = false := by
      rw [hParams]
      rfl
    have h := ctx.initStateV2_ok_frameV2 hBody hAdm hValid hNoRaw
    rw [hArgs, hInit] at h
    exact h
  unfold execProgV2
  rw [hInitState]
  apply execOutcomeStateV2_step (hStep1 aid off w i _ _ hLoad hi)
  exact execOutcomeStateV2_done (hStep2 aid off w i _ _)
    (by rw [extractCallerMemory_entry q.callerMem hCM])

private theorem clone_body_verified {defId : DefId} {body : Body}
    {ety : EnumTy} {identity : String}
    (hBody :
      Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (hAdm : BodyStaticAdmittedV2 Captured.program body = true)
    (hId : body.identity = identity)
    (hSafe : body.isUnsafe = false)
    (hParams : (body.locals.drop 1).take body.argumentCount =
      [.ref .shared (.enum ety)])
    (hLay : layoutOfTyV2 (.enum ety) = some ⟨1, 0⟩)
    (hLay1 : layoutOfTy (.enum ety) = some ⟨1, 0⟩)
    (hTag : ety.tagRepr = .scalar .i8 false)
    (hInit : ∀ v : Val, initLocalsLoop body [v] 0 body.locals =
      [.immediate none, .immediate (some v)])
    (hStep1 : ∀ (aid : AllocId) (off : UInt64) (w : IntWidth) (i : Nat)
      (cm : CallerMemory) (m : MemoryState),
      loadIndirectV2 m (.enum ety) ⟨aid, off.toNat⟩ =
        .ok (some (.enumVal ety i)) →
      i < ety.discriminants.length →
      evalStepV2 (entryProgForBody Captured.program defId)
        (stateV2 (frameV2 defId 0 0
          [.immediate none, .immediate (some (.ptr ⟨some aid, off, w⟩))])
          cm m) =
      .step (stateV2 (frameV2 defId 0 1
        [.immediate (some (.enumVal ety i)),
         .immediate (some (.ptr ⟨some aid, off, w⟩))]) cm m))
    (hStep2 : ∀ (aid : AllocId) (off : UInt64) (w : IntWidth) (i : Nat)
      (cm : CallerMemory) (m : MemoryState),
      evalStepV2 (entryProgForBody Captured.program defId)
        (stateV2 (frameV2 defId 0 1
          [.immediate (some (.enumVal ety i)),
           .immediate (some (.ptr ⟨some aid, off, w⟩))]) cm m) =
      .done (.returned ⟨.enumVal ety i, extractCallerMemory cm m⟩)) :
    BodyVerifiedV2 Captured.program defId body
      (Spec.specs.safety body.identity) ∧
    Spec.cloneBodyPost Captured.program defId identity ety := by
  have hExec := clone_body_exec hBody hAdm hParams hLay hLay1 hTag hInit
    hStep1 hStep2
  refine ⟨⟨hBody, hAdm, fun q hValid _ => ?_⟩, ?_⟩
  · let ⟨_, _, _, _, hE⟩ := hExec q hValid
    exact (returnsExactly_of_exec hE).1
  · unfold Spec.cloneBodyPost
    rw [hBody]
    refine ⟨hId, hSafe, fun q hValid => ?_⟩
    let ⟨self, v, hArgs, hDeref, hE⟩ := hExec q hValid
    rw [hArgs]
    exact ⟨v, hDeref, (returnsExactly_of_exec hE).2⟩

private theorem order_check (i : Nat) (hi : i < 2) :
    checkValV2 (.enumVal Spec.orderEnumTy i) (.enum Spec.orderEnumTy) = true :=
  match i, hi with
  | 0, _ => by decide
  | 1, _ => by decide
  | n + 2, h => absurd h (Nat.not_lt_of_le (Nat.le_add_left 2 n))

/-- Body 0: `<byteorder::Order as Clone>::clone`. -/
private theorem body0_verified :
    BodyVerifiedV2 Captured.program 0 Captured.body_0
      (Spec.specs.safety Captured.body_0.identity) ∧
    Spec.cloneBodyPost Captured.program 0 Spec.orderCloneId
      Spec.orderEnumTy :=
  clone_body_verified rfl (by decide) (by decide) rfl rfl rfl rfl rfl
    (fun _ => rfl)
    (fun _ _ _ i _ _ hLoad hi => evalStepV2_assign_local rfl rfl rfl rfl
      (evalRvalueV2_use_copy_of_read (readPlaceV2_deref_enum rfl rfl rfl hLoad)
        (by decide))
      (writePlaceDestV2_immediate_ok (order_check i hi) rfl rfl))
    (fun _ _ _ _ _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl)

private theorem castType_check (i : Nat) (hi : i < 2) :
    checkValV2 (.enumVal Spec.castTypeEnumTy i)
      (.enum Spec.castTypeEnumTy) = true :=
  match i, hi with
  | 0, _ => by decide
  | 1, _ => by decide
  | n + 2, h => absurd h (Nat.not_lt_of_le (Nat.le_add_left 2 n))

/-- Body 3: `<layout::CastType as Clone>::clone`. -/
private theorem body3_verified :
    BodyVerifiedV2 Captured.program 3 Captured.body_3
      (Spec.specs.safety Captured.body_3.identity) ∧
    Spec.cloneBodyPost Captured.program 3 Spec.castTypeCloneId
      Spec.castTypeEnumTy :=
  clone_body_verified rfl (by decide) (by decide) rfl rfl rfl rfl rfl
    (fun _ => rfl)
    (fun _ _ _ i _ _ hLoad hi => evalStepV2_assign_local rfl rfl rfl rfl
      (evalRvalueV2_use_copy_of_read (readPlaceV2_deref_enum rfl rfl rfl hLoad)
        (by decide))
      (writePlaceDestV2_immediate_ok (castType_check i hi) rfl rfl))
    (fun _ _ _ _ _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl)

/-! ## `KnownLayout::pointer_to_metadata` Bodies (Bodies 4-18) -/

/-- `<T as KnownLayout>::pointer_to_metadata` for sized `T` at `defId`. -/
private theorem ptrMeta_verified {defId : DefId} {body : Body} {t : MirTy}
    {tyName : String}
    (hBody :
      Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (hAdm : BodyStaticAdmittedV2 Captured.program body = true)
    (hId : body.identity = Spec.ptrMetaId tyName)
    (hSafe : body.isUnsafe = false)
    (hParams : (body.locals.drop 1).take body.argumentCount =
      [.rawPtr .mut t])
    (hInit : ∀ v : Val, initLocalsLoop body [v] 0 body.locals =
      [.immediate (some .unit), .immediate (some v)])
    (hStep1 : ∀ (v : Val) (cm : CallerMemory) (m : MemoryState),
      evalStepV2 (entryProgForBody Captured.program defId)
        (stateV2 (frameV2 defId 0 0
          [.immediate (some .unit), .immediate (some v)]) cm m) =
      .step (stateV2 (frameV2 defId 0 1
        [.immediate (some .unit), .immediate (some v)]) cm m))
    (hStep2 : ∀ (v : Val) (cm : CallerMemory) (m : MemoryState),
      evalStepV2 (entryProgForBody Captured.program defId)
        (stateV2 (frameV2 defId 0 1
          [.immediate (some .unit), .immediate (some v)]) cm m) =
      .done (.returned ⟨.unit, extractCallerMemory cm m⟩)) :
    BodyVerifiedV2 Captured.program defId body
      (Spec.specs.safety body.identity) ∧
    Spec.unitBodyPost Captured.program defId (Spec.ptrMetaId tyName) :=
  unit_body_verified hBody hAdm hId hSafe hParams hInit hStep1 hStep2

private theorem body4_verified :
    BodyVerifiedV2 Captured.program 4 Captured.body_4
      (Spec.specs.safety Captured.body_4.identity) ∧
    Spec.unitBodyPost Captured.program 4 (Spec.ptrMetaId "()") :=
  ptrMeta_verified rfl (by decide) (by decide) rfl rfl (fun _ => rfl)
    (fun _ _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

private theorem body5_verified :
    BodyVerifiedV2 Captured.program 5 Captured.body_5
      (Spec.specs.safety Captured.body_5.identity) ∧
    Spec.unitBodyPost Captured.program 5 (Spec.ptrMetaId "u8") :=
  ptrMeta_verified rfl (by decide) (by decide) rfl rfl (fun _ => rfl)
    (fun _ _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

private theorem body6_verified :
    BodyVerifiedV2 Captured.program 6 Captured.body_6
      (Spec.specs.safety Captured.body_6.identity) ∧
    Spec.unitBodyPost Captured.program 6 (Spec.ptrMetaId "i8") :=
  ptrMeta_verified rfl (by decide) (by decide) rfl rfl (fun _ => rfl)
    (fun _ _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

private theorem body7_verified :
    BodyVerifiedV2 Captured.program 7 Captured.body_7
      (Spec.specs.safety Captured.body_7.identity) ∧
    Spec.unitBodyPost Captured.program 7 (Spec.ptrMetaId "u16") :=
  ptrMeta_verified rfl (by decide) (by decide) rfl rfl (fun _ => rfl)
    (fun _ _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

private theorem body8_verified :
    BodyVerifiedV2 Captured.program 8 Captured.body_8
      (Spec.specs.safety Captured.body_8.identity) ∧
    Spec.unitBodyPost Captured.program 8 (Spec.ptrMetaId "i16") :=
  ptrMeta_verified rfl (by decide) (by decide) rfl rfl (fun _ => rfl)
    (fun _ _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

private theorem body9_verified :
    BodyVerifiedV2 Captured.program 9 Captured.body_9
      (Spec.specs.safety Captured.body_9.identity) ∧
    Spec.unitBodyPost Captured.program 9 (Spec.ptrMetaId "u32") :=
  ptrMeta_verified rfl (by decide) (by decide) rfl rfl (fun _ => rfl)
    (fun _ _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

private theorem body10_verified :
    BodyVerifiedV2 Captured.program 10 Captured.body_10
      (Spec.specs.safety Captured.body_10.identity) ∧
    Spec.unitBodyPost Captured.program 10 (Spec.ptrMetaId "i32") :=
  ptrMeta_verified rfl (by decide) (by decide) rfl rfl (fun _ => rfl)
    (fun _ _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

private theorem body11_verified :
    BodyVerifiedV2 Captured.program 11 Captured.body_11
      (Spec.specs.safety Captured.body_11.identity) ∧
    Spec.unitBodyPost Captured.program 11 (Spec.ptrMetaId "u64") :=
  ptrMeta_verified rfl (by decide) (by decide) rfl rfl (fun _ => rfl)
    (fun _ _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

private theorem body12_verified :
    BodyVerifiedV2 Captured.program 12 Captured.body_12
      (Spec.specs.safety Captured.body_12.identity) ∧
    Spec.unitBodyPost Captured.program 12 (Spec.ptrMetaId "i64") :=
  ptrMeta_verified rfl (by decide) (by decide) rfl rfl (fun _ => rfl)
    (fun _ _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

private theorem body13_verified :
    BodyVerifiedV2 Captured.program 13 Captured.body_13
      (Spec.specs.safety Captured.body_13.identity) ∧
    Spec.unitBodyPost Captured.program 13 (Spec.ptrMetaId "u128") :=
  ptrMeta_verified rfl (by decide) (by decide) rfl rfl (fun _ => rfl)
    (fun _ _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

private theorem body14_verified :
    BodyVerifiedV2 Captured.program 14 Captured.body_14
      (Spec.specs.safety Captured.body_14.identity) ∧
    Spec.unitBodyPost Captured.program 14 (Spec.ptrMetaId "i128") :=
  ptrMeta_verified rfl (by decide) (by decide) rfl rfl (fun _ => rfl)
    (fun _ _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

private theorem body15_verified :
    BodyVerifiedV2 Captured.program 15 Captured.body_15
      (Spec.specs.safety Captured.body_15.identity) ∧
    Spec.unitBodyPost Captured.program 15 (Spec.ptrMetaId "usize") :=
  ptrMeta_verified rfl (by decide) (by decide) rfl rfl (fun _ => rfl)
    (fun _ _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

private theorem body16_verified :
    BodyVerifiedV2 Captured.program 16 Captured.body_16
      (Spec.specs.safety Captured.body_16.identity) ∧
    Spec.unitBodyPost Captured.program 16 (Spec.ptrMetaId "isize") :=
  ptrMeta_verified rfl (by decide) (by decide) rfl rfl (fun _ => rfl)
    (fun _ _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

private theorem body17_verified :
    BodyVerifiedV2 Captured.program 17 Captured.body_17
      (Spec.specs.safety Captured.body_17.identity) ∧
    Spec.unitBodyPost Captured.program 17 (Spec.ptrMetaId "bool") :=
  ptrMeta_verified rfl (by decide) (by decide) rfl rfl (fun _ => rfl)
    (fun _ _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

private theorem body18_verified :
    BodyVerifiedV2 Captured.program 18 Captured.body_18
      (Spec.specs.safety Captured.body_18.identity) ∧
    Spec.unitBodyPost Captured.program 18 (Spec.ptrMetaId "char") :=
  ptrMeta_verified rfl (by decide) (by decide) rfl rfl (fun _ => rfl)
    (fun _ _ _ => evalStepV2_assign_local rfl rfl rfl rfl rfl
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    (fun _ _ _ => evalStepV2_return_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl)

/-! ## `PartialEq::eq` Body (Body 2) -/

/-- Both reference arguments of a valid two-reference entry are valid. -/
private theorem refValid_of_pair {m : MemoryState} {pt : MirTy} {a b : Val}
    (h : refsValidInMemList m [.ref .shared pt, .ref .shared pt] [a, b] =
      true) :
    refValidInMem m .shared pt a = .ok () ∧
    refValidInMem m .shared pt b = .ok () := by
  dsimp only [refsValidInMemList] at h
  have hA := bool_and_left' h
  have hB := bool_and_left' (bool_and_right' h)
  unfold refsValidInMem at hA hB
  constructor
  · cases hR : refValidInMem m .shared pt a with
    | error k =>
      rw [hR] at hA
      nomatch hA
    | ok u =>
      cases u
      rfl
  · cases hR : refValidInMem m .shared pt b with
    | error k =>
      rw [hR] at hB
      nomatch hB
    | ok u =>
      cases u
      rfl

/-- `discriminant(*_lid)` of a shared reference to an `Order` variant `i`
(whose discriminant is `i`). -/
private theorem evalRvalueV2_discr_deref_order {bodyLocals : List MirTy}
    {l : List LocalSlot} {m : MemoryState} {lid : LocalId} {aid : AllocId}
    {off : UInt64} {w : IntWidth} {i : Nat}
    (hTy : Trusted.MirSemantics.getElem? bodyLocals lid =
      some (.ref .shared (.enum Spec.orderEnumTy)))
    (hSlot : Trusted.MirSemantics.getElem? l lid =
      some (.immediate (some (.ptr ⟨some aid, off, w⟩))))
    (hLoad : loadIndirectV2 m (.enum Spec.orderEnumTy) ⟨aid, off.toNat⟩ =
      .ok (some (.enumVal Spec.orderEnumTy i)))
    (hi : i < 2) :
    evalRvalueV2 bodyLocals l m (.int .isize true)
      (.discriminant ⟨lid, [.deref]⟩) =
      .ok (.scalar ⟨.isize, true, truncateBits .isize (BitVec.ofNat 128 i)⟩,
        l, m) := by
  unfold evalRvalueV2
  dsimp only
  rw [ite_bool_true (b := !([.deref] : List ProjectionElem).isEmpty) rfl,
    readPlaceV2_deref_enum rfl hTy hSlot hLoad]
  dsimp only
  rw [ite_bool_false (b := !MirTy.beq (.int .isize true)
    (.int Spec.orderEnumTy.discrWidth Spec.orderEnumTy.discrSigned)) rfl]
  cases i with
  | zero => rfl
  | succ k =>
    cases k with
    | zero => rfl
    | succ k => exact absurd hi (Nat.not_lt_of_le (Nat.le_add_left 2 k))

/-- The `isize` discriminant value of an `Order` variant below `2`. -/
private theorem discr_check {i : Nat} (hi : i < 2) :
    checkValV2
      (.scalar ⟨.isize, true, truncateBits .isize (BitVec.ofNat 128 i)⟩)
      (.int .isize true) = true := by
  cases i with
  | zero => decide
  | succ k =>
    cases k with
    | zero => decide
    | succ k => exact absurd hi (Nat.not_lt_of_le (Nat.le_add_left 2 k))

private theorem lt_two_cases {i : Nat} (hi : i < 2) : i = 0 ∨ i = 1 := by
  cases i with
  | zero => exact .inl rfl
  | succ k =>
    cases k with
    | zero => exact .inr rfl
    | succ k => exact absurd hi (Nat.not_lt_of_le (Nat.le_add_left 2 k))

/-- `Eq(move _7, move _8)` on the two `Order` discriminants (`isize` scalars
`i` and `j`) is `i == j`. -/
private theorem evalRvalueV2_eq_discr {m : MemoryState} {pa pb : Val}
    {s4 s6 : LocalSlot} {i j : Nat} (hi : i < 2) (hj : j < 2) :
    evalRvalueV2 Captured.body_2.locals
      [.immediate none, .immediate (some pa), .immediate (some pb),
       .immediate (some (.scalar ⟨.isize, true,
         truncateBits .isize (BitVec.ofNat 128 i)⟩)),
       s4,
       .immediate (some (.scalar ⟨.isize, true,
         truncateBits .isize (BitVec.ofNat 128 j)⟩)),
       s6,
       .immediate (some (.scalar ⟨.isize, true,
         truncateBits .isize (BitVec.ofNat 128 i)⟩)),
       .immediate (some (.scalar ⟨.isize, true,
         truncateBits .isize (BitVec.ofNat 128 j)⟩))]
      m .bool (.binaryOp .eq (.move ⟨7, []⟩) (.move ⟨8, []⟩)) =
    .ok (.bool (Nat.beq i j),
      [.immediate none, .immediate (some pa), .immediate (some pb),
       .immediate (some (.scalar ⟨.isize, true,
         truncateBits .isize (BitVec.ofNat 128 i)⟩)),
       s4,
       .immediate (some (.scalar ⟨.isize, true,
         truncateBits .isize (BitVec.ofNat 128 j)⟩)),
       s6, .immediate none, .immediate none], m) := by
  rcases lt_two_cases hi with rfl | rfl <;>
    rcases lt_two_cases hj with rfl | rfl <;> rfl

/-- Body 2 (`<byteorder::Order as PartialEq>::eq`) runs `_4 = &(*_1)`,
`_3 = discriminant(*_4)`, `_6 = &(*_2)`, `_5 = discriminant(*_6)`,
`_7 = copy _3`, `_8 = copy _5`, and `_0 = Eq(move _7, move _8)`, with
`StorageLive` and `StorageDead` bookkeeping, then `return`. -/
private theorem body2_exec (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_2 q) :
    ∃ (a b : Val) (i j : Nat), q.args = [a, b] ∧
      Spec.derefEntry q Spec.orderEnumTy a =
        some (.enumVal Spec.orderEnumTy i) ∧
      Spec.derefEntry q Spec.orderEnumTy b =
        some (.enumVal Spec.orderEnumTy j) ∧
      execProgV2 (entryProgForBody Captured.program 2) 24 q
        (fun o => o = .returned ⟨.bool (Nat.beq i j), q.callerMem⟩) := by
  have hCM : validCallerMemory q.callerMem = true := hValid.1
  have hMatch : checkArgsMatchV2 q.args
      [.ref .shared (.enum Spec.orderEnumTy),
       .ref .shared (.enum Spec.orderEnumTy)] = true := hValid.2.1
  let ⟨a, b, hArgs, hCa, hCb⟩ := checkArgsMatchV2_pair_inv hMatch
  have hRefs : refsValidInMemList (entryMemoryWithCaller q.callerMem)
      [.ref .shared (.enum Spec.orderEnumTy),
       .ref .shared (.enum Spec.orderEnumTy)] [a, b] = true := by
    have h : refsValidInMemList (entryMemoryWithCaller q.callerMem)
        ((Captured.body_2.locals.drop 1).take Captured.body_2.argumentCount)
        q.args = true := hValid.2.2.1
    rw [hArgs] at h
    exact h
  let ⟨hRa, hRb⟩ := refValid_of_pair hRefs
  let ⟨aid1, off1, w1, v1, hA, hLoad1⟩ := enum_ref_load rfl hRa
  let ⟨aid2, off2, w2, v2, hB, hLoad2⟩ := enum_ref_load rfl hRb
  let ⟨i, hV1, hi⟩ := enum_load_shape rfl rfl rfl hLoad1
  let ⟨j, hV2, hj⟩ := enum_load_shape rfl rfl rfl hLoad2
  subst hV1
  subst hV2
  subst hA
  subst hB
  refine ⟨_, _, i, j, hArgs, derefEntry_of_load hLoad1,
    derefEntry_of_load hLoad2, ?_⟩
  have hInit :
      initStateV2 (entryProgForBody Captured.program 2) q =
      .ok (stateV2 (frameV2 2 0 0
        [.immediate none, .immediate (some (.ptr ⟨some aid1, off1, w1⟩)),
         .immediate (some (.ptr ⟨some aid2, off2, w2⟩)),
         .dead, .dead, .dead, .dead, .dead, .dead])
        q.callerMem (entryMemoryWithCaller q.callerMem)) := by
    have h := (⟨Captured.program, 2, Captured.body_2⟩ : BodyCtx)
      |>.initStateV2_ok_frameV2 rfl (by decide) hValid
    rw [hArgs] at h
    exact h
  unfold execProgV2
  rw [hInit]
  have hStepsTo : ∀ i' j' : Nat, i' < 2 → j' < 2 →
      loadIndirectV2 (entryMemoryWithCaller q.callerMem)
        (.enum Spec.orderEnumTy) ⟨aid1, off1.toNat⟩ =
        .ok (some (.enumVal Spec.orderEnumTy i')) →
      loadIndirectV2 (entryMemoryWithCaller q.callerMem)
        (.enum Spec.orderEnumTy) ⟨aid2, off2.toNat⟩ =
        .ok (some (.enumVal Spec.orderEnumTy j')) →
      execOutcomeStateV2 (entryProgForBody Captured.program 2)
        (fun o => o = .returned ⟨.bool (Nat.beq i' j'), q.callerMem⟩)
        (fun _ => False) 24
        (stateV2 (frameV2 2 0 0
          [.immediate none, .immediate (some (.ptr ⟨some aid1, off1, w1⟩)),
           .immediate (some (.ptr ⟨some aid2, off2, w2⟩)),
           .dead, .dead, .dead, .dead, .dead, .dead])
          q.callerMem (entryMemoryWithCaller q.callerMem)) := by
    intro i' j' hi' hj' hL1 hL2
    -- `try dsimp only` after each step reduces the record updates the step
    -- leaves in the state, which keeps later unification cheap.
    -- bb0 stmts 0, 1: StorageLive 3, 4
    apply execOutcomeStateV2_step (by rfl)
    try dsimp only
    apply execOutcomeStateV2_step (by rfl)
    try dsimp only
    -- bb0 stmt 2: _4 = &(*_1)
    apply execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl
      (evalRvalueV2_ref_deref_ok rfl rfl rfl hRa)
      (writePlaceDestV2_immediate_ok hCa rfl rfl))
    try dsimp only
    -- bb0 stmt 3: _3 = discriminant(*_4)
    apply execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl
      (evalRvalueV2_discr_deref_order rfl rfl hL1 hi')
      (writePlaceDestV2_immediate_ok (discr_check hi') rfl rfl))
    try dsimp only
    -- bb0 stmts 4, 5, 6: StorageDead 4, StorageLive 5, 6
    apply execOutcomeStateV2_step (by rfl)
    try dsimp only
    apply execOutcomeStateV2_step (by rfl)
    try dsimp only
    apply execOutcomeStateV2_step (by rfl)
    try dsimp only
    -- bb0 stmt 7: _6 = &(*_2)
    apply execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl
      (evalRvalueV2_ref_deref_ok rfl rfl rfl hRb)
      (writePlaceDestV2_immediate_ok hCb rfl rfl))
    try dsimp only
    -- bb0 stmt 8: _5 = discriminant(*_6)
    apply execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl
      (evalRvalueV2_discr_deref_order rfl rfl hL2 hj')
      (writePlaceDestV2_immediate_ok (discr_check hj') rfl rfl))
    try dsimp only
    -- bb0 stmts 9, 10: StorageDead 6, StorageLive 7
    apply execOutcomeStateV2_step (by rfl)
    try dsimp only
    apply execOutcomeStateV2_step (by rfl)
    try dsimp only
    -- bb0 stmt 11: _7 = copy _3
    apply execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl
      (evalRvalueV2_use_copy_ok rfl rfl rfl)
      (writePlaceDestV2_immediate_ok (discr_check hi') rfl rfl))
    try dsimp only
    -- bb0 stmt 12: StorageLive 8
    apply execOutcomeStateV2_step (by rfl)
    try dsimp only
    -- bb0 stmt 13: _8 = copy _5
    apply execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl
      (evalRvalueV2_use_copy_ok rfl rfl rfl)
      (writePlaceDestV2_immediate_ok (discr_check hj') rfl rfl))
    try dsimp only
    -- bb0 stmt 14: _0 = Eq(move _7, move _8)
    apply execOutcomeStateV2_step (evalStepV2_assign_local rfl rfl rfl rfl
      (evalRvalueV2_eq_discr hi' hj')
      (writePlaceDestV2_immediate_ok rfl rfl rfl))
    try dsimp only
    -- bb0 stmts 15-18: StorageDead 8, 7, 5, 3; then `return`
    apply execOutcomeStateV2_step (by rfl)
    try dsimp only
    apply execOutcomeStateV2_step (by rfl)
    try dsimp only
    apply execOutcomeStateV2_step (by rfl)
    try dsimp only
    apply execOutcomeStateV2_step (by rfl)
    try dsimp only
    exact execOutcomeStateV2_done (evalStepV2_return_ok rfl rfl rfl rfl rfl
      rfl rfl rfl rfl rfl rfl)
      (by rw [extractCallerMemory_entry q.callerMem hCM])
  exact hStepsTo i j hi hj hLoad1 hLoad2

private theorem body2_verified :
    BodyVerifiedV2 Captured.program 2 Captured.body_2
      (Spec.specs.safety Captured.body_2.identity) ∧
    Spec.eqBodyPost Captured.program 2 Spec.orderEqId Spec.orderEnumTy := by
  refine ⟨⟨rfl, by decide, fun q hValid _ => ?_⟩, ?_⟩
  · let ⟨_, _, _, _, _, _, _, hE⟩ := body2_exec q hValid
    exact (returnsExactly_of_exec hE).1
  · unfold Spec.eqBodyPost
    rw [show Trusted.MirSemantics.getElem? Captured.program.bodies 2 =
      some Captured.body_2 from rfl]
    refine ⟨by decide, rfl, fun q hValid => ?_⟩
    let ⟨a, b, i, j, hArgs, hA, hB, hE⟩ := body2_exec q hValid
    rw [hArgs]
    exact ⟨i, j, hA, hB, (returnsExactly_of_exec hE).2⟩

/-! ## Top-Level Claim -/

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, by decide, ?_, ?_⟩
  · intro defId body hBody
    match defId, hBody with
    | 0, h =>
      cases (h : some Captured.body_0 = some body); exact body0_verified.1
    | 1, h =>
      cases (h : some Captured.body_1 = some body); exact body1_verified.1
    | 2, h =>
      cases (h : some Captured.body_2 = some body); exact body2_verified.1
    | 3, h =>
      cases (h : some Captured.body_3 = some body); exact body3_verified.1
    | 4, h =>
      cases (h : some Captured.body_4 = some body); exact body4_verified.1
    | 5, h =>
      cases (h : some Captured.body_5 = some body); exact body5_verified.1
    | 6, h =>
      cases (h : some Captured.body_6 = some body); exact body6_verified.1
    | 7, h =>
      cases (h : some Captured.body_7 = some body); exact body7_verified.1
    | 8, h =>
      cases (h : some Captured.body_8 = some body); exact body8_verified.1
    | 9, h =>
      cases (h : some Captured.body_9 = some body); exact body9_verified.1
    | 10, h =>
      cases (h : some Captured.body_10 = some body); exact body10_verified.1
    | 11, h =>
      cases (h : some Captured.body_11 = some body); exact body11_verified.1
    | 12, h =>
      cases (h : some Captured.body_12 = some body); exact body12_verified.1
    | 13, h =>
      cases (h : some Captured.body_13 = some body); exact body13_verified.1
    | 14, h =>
      cases (h : some Captured.body_14 = some body); exact body14_verified.1
    | 15, h =>
      cases (h : some Captured.body_15 = some body); exact body15_verified.1
    | 16, h =>
      cases (h : some Captured.body_16 = some body); exact body16_verified.1
    | 17, h =>
      cases (h : some Captured.body_17 = some body); exact body17_verified.1
    | 18, h =>
      cases (h : some Captured.body_18 = some body); exact body18_verified.1
    | n + 19, h => nomatch (h : (none : Option Body) = some body)
  · exact ⟨body0_verified.2, body1_verified.2, body2_verified.2,
      body3_verified.2, body4_verified.2, body5_verified.2, body6_verified.2,
      body7_verified.2, body8_verified.2, body9_verified.2, body10_verified.2,
      body11_verified.2, body12_verified.2, body13_verified.2,
      body14_verified.2, body15_verified.2, body16_verified.2,
      body17_verified.2, body18_verified.2, trivial⟩

end Proof
