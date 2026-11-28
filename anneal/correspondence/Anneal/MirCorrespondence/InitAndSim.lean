-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Init.Data.BitVec.BasicAux
import Init.Data.Int.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Control.Except
import Trusted
import Trusted.Correspondence
import Anneal.MirWp
import Anneal.MirCorrespondence.Codec
import Anneal.MirCorrespondence.SimHelpers
import Anneal.MirCorrespondence.ScalarEquiv
import Anneal.MirCorrespondence.EnumEquiv
import Anneal.MirCorrespondence.MemRoundTrip
import Anneal.MirCorrespondence.RvalueStep
import Anneal.MirCorrespondence.StmtTermStep

namespace Anneal.MirCorrespondence

open Trusted Trusted.MirAst Trusted.MirSemantics Trusted.Correspondence

/-! ## Entry Initialization Simulation (`initRefState_sim_base`) -/

theorem refStmtHasStorageMarker_eq {ts : List MirTy} {localId : LocalId}
    {rstmt : RefStatementKind} {stmt : StatementKind}
    (h : decodeStmt ts rstmt = some stmt) :
    refStmtHasStorageMarker localId rstmt =
      stmtHasStorageMarker localId stmt := by
  cases rstmt with
  | storageLive id =>
    injection h with h_eq; subst h_eq; rfl
  | storageDead id =>
    injection h with h_eq; subst h_eq; rfl
  | nop =>
    injection h with h_eq; subst h_eq; rfl
  | unsupported =>
    injection h with h_eq; subst h_eq; rfl
  | assign rdst rrv =>
    dsimp only [decodeStmt, optMap2] at h
    cases h₁ : decodePlace ts rdst with
    | none => rw [h₁] at h; cases h
    | some dst =>
      cases h₂ : decodeRvalue ts rrv with
      | none => rw [h₁, h₂] at h; cases h
      | some rv =>
        rw [h₁, h₂] at h
        injection h with h_eq
        subst h_eq
        rfl

theorem refHasStorageAnnotation_eq {ts : List MirTy} {rbody : RefBody}
    {body : Body}
    (h : decodeBody ts rbody = some body) (localId : LocalId) :
    refHasStorageAnnotation rbody localId =
      hasStorageAnnotation body localId := by
  let ⟨_, _, h_bbs, _, _⟩ := decodeBody_inv h
  unfold refHasStorageAnnotation hasStorageAnnotation
  exact mapOption_any_eq
    (fun _ _ h_bb =>
      mapOption_any_eq (fun _ _ hs => refStmtHasStorageMarker_eq hs)
        (decodeBasicBlock_inv h_bb).1)
    h_bbs

noncomputable def refStmtInBounds (n : Nat) : RefStatementKind → Bool
  | .storageLive id | .storageDead id => Nat.blt id n
  | _ => true

noncomputable def stmtInBounds (n : Nat) : StatementKind → Bool
  | .storageLive id | .storageDead id => Nat.blt id n
  | _ => true

theorem refStmtInBounds_eq {ts : List MirTy} {n : Nat}
    {rstmt : RefStatementKind} {stmt : StatementKind}
    (h : decodeStmt ts rstmt = some stmt) :
    refStmtInBounds n rstmt = stmtInBounds n stmt := by
  cases rstmt with
  | storageLive id => injection h with h_eq; subst h_eq; rfl
  | storageDead id => injection h with h_eq; subst h_eq; rfl
  | nop => injection h with h_eq; subst h_eq; rfl
  | unsupported => injection h with h_eq; subst h_eq; rfl
  | assign rdst rrv =>
    dsimp only [decodeStmt, optMap2] at h
    cases h₁ : decodePlace ts rdst with
    | none => rw [h₁] at h; cases h
    | some dst =>
      cases h₂ : decodeRvalue ts rrv with
      | none => rw [h₁, h₂] at h; cases h
      | some rv =>
        rw [h₁, h₂] at h
        injection h with h_eq
        subst h_eq
        rfl

theorem refStorageAnnotationsInBounds_eq {ts : List MirTy} {rbody : RefBody}
    {body : Body}
    (h : decodeBody ts rbody = some body) :
    refStorageAnnotationsInBounds rbody = storageAnnotationsInBounds body := by
  let ⟨_, h_loc, h_bbs, _, _⟩ := decodeBody_inv h
  unfold refStorageAnnotationsInBounds storageAnnotationsInBounds
  rw [mapOption_length h_loc]
  exact mapOption_all_eq
    (fun _ _ h_bb =>
      mapOption_all_eq (fun _ _ hs => refStmtInBounds_eq hs)
        (decodeBasicBlock_inv h_bb).1)
    h_bbs

theorem initRefLocalsLoop_eq {ts : List MirTy} {rbody : RefBody} {body : Body}
    (h : decodeBody ts rbody = some body) (args : List Val) (idx : Nat)
    (tys : List MirTy) :
    initRefLocalsLoop ts rbody args idx tys =
      liftLocals ts tys (initLocalsLoop body args idx tys) := by
  induction tys generalizing idx with
  | nil => rfl
  | cons ty rest ih =>
    let ⟨h_arg, _, _, _, _⟩ := decodeBody_inv h
    dsimp only [initRefLocalsLoop, initLocalsLoop, liftLocals]
    rw [h_arg, refHasStorageAnnotation_eq h idx, refLiveUninitSlot_eq,
      ih (idx + 1)]
    rfl

private theorem checkArgsMatch_getElem? {args : List Val} {tys : List MirTy}
    (h : checkArgsMatch args tys = true) :
    ∀ (k : Nat) (ty : MirTy),
      MirSemantics.getElem? tys k = some ty →
      ∃ v : Val, MirSemantics.getElem? args k = some v ∧
        checkVal v ty = true := by
  induction args generalizing tys with
  | nil =>
    cases tys with
    | nil => intro k ty hk; cases hk
    | cons _ _ => cases h
  | cons a rest ih =>
    cases tys with
    | nil => cases h
    | cons t ts =>
      dsimp only [checkArgsMatch] at h
      cases h_cv : checkVal a t with
      | false => rw [h_cv] at h; cases h
      | true =>
        rw [h_cv] at h
        intro k ty hk
        cases k with
        | zero =>
          injection hk with h_eq; subst h_eq
          exact ⟨a, rfl, h_cv⟩
        | succ k' => exact ih h k' ty hk

private theorem getElem?_take_of_lt {α : Type} :
    ∀ (xs : List α) (n i : Nat),
      i < n → MirSemantics.getElem? (xs.take n) i = MirSemantics.getElem? xs i
  | [], n, _, _ => by cases n <;> rfl
  | x :: rest, 0, _, hlt => nomatch hlt
  | x :: rest, n + 1, 0, _ => rfl
  | x :: rest, n + 1, i + 1, hlt =>
    getElem?_take_of_lt rest n i (Nat.lt_of_succ_lt_succ hlt)

private theorem getElem?_drop_one {α : Type} (xs : List α) (j : Nat) :
    MirSemantics.getElem? (xs.drop 1) j = MirSemantics.getElem? xs (j + 1) := by
  cases xs <;> rfl

private theorem initLocalsLoop_slotsMatchTys_aux (body : Body) (args : List Val) :
    ∀ (idx : Nat) (tys : List MirTy),
      (∀ (j : Nat) (ty : MirTy),
        MirSemantics.getElem? tys j = some ty →
        Nat.beq (idx + j) 0 = false →
        Nat.ble (idx + j) body.argumentCount = true →
        ∀ (v : Val), MirSemantics.getElem? args (idx + j - 1) = some v →
          checkVal v ty = true) →
      SlotsMatchTys tys (initLocalsLoop body args idx tys) := by
  intro idx tys h_ok
  induction tys generalizing idx with
  | nil => exact SlotsMatchTys.nil
  | cons ty rest ih =>
    dsimp only [initLocalsLoop]
    apply SlotsMatchTys.cons
    · cases h0 : Nat.beq idx 0 with
      | true =>
        rw [ite_eq_left rfl]
        exact slotMatchesTy_liveUninitSlot ty
      | false =>
        rw [ite_eq_right (by decide)]
        cases hle : Nat.ble idx body.argumentCount with
        | true =>
          rw [ite_eq_left rfl]
          cases h_a : MirSemantics.getElem? args (idx - 1) with
          | none => exact True.intro
          | some v =>
            exact h_ok 0 ty rfl (by rw [Nat.add_zero]; exact h0)
              (by rw [Nat.add_zero]; exact hle) v h_a
        | false =>
          rw [ite_eq_right (by decide)]
          cases hasStorageAnnotation body idx with
          | true => exact True.intro
          | false => exact slotMatchesTy_liveUninitSlot ty
    · apply ih (idx + 1)
      intro j ty' h_get h0' hle' v h_a
      have h_assoc : idx + 1 + j = idx + (j + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 j]
      rw [h_assoc] at h0' hle' h_a
      exact h_ok (j + 1) ty' h_get h0' hle' v h_a

private theorem initLocalsLoop_slotsMatchTys (body : Body) (args : List Val)
    (h_args : checkArgsMatch args ((body.locals.drop 1).take body.argumentCount) =
      true) :
    SlotsMatchTys body.locals (initLocalsLoop body args 0 body.locals) := by
  apply initLocalsLoop_slotsMatchTys_aux body args 0 body.locals
  intro j ty h_get h0 hle v h_a
  rw [Nat.zero_add] at h0 hle h_a
  cases j with
  | zero => cases h0
  | succ k =>
    have h_le : k + 1 ≤ body.argumentCount := Nat.ble_eq.mp hle
    have h_lt : k < body.argumentCount := h_le
    have h_pt :
        MirSemantics.getElem? ((body.locals.drop 1).take body.argumentCount) k =
          some ty := by
      rw [getElem?_take_of_lt _ _ _ h_lt, getElem?_drop_one]
      exact h_get
    let ⟨v', h_av', h_cv'⟩ := checkArgsMatch_getElem? h_args k ty h_pt
    have h_sub : k + 1 - 1 = k := Nat.add_sub_cancel k 1
    rw [h_sub] at h_a
    rw [h_a] at h_av'
    injection h_av' with h_veq
    rw [h_veq]
    exact h_cv'

theorem getElem?_zero_of_blt {α : Type} {xs : List α} {n : Nat}
    (h : Nat.blt n xs.length = true) :
    ∃ x : α, MirSemantics.getElem? xs 0 = some x := by
  cases xs with
  | nil => cases h
  | cons x _ => exact ⟨x, rfl⟩

private theorem decodeTerminator_call_inv {types : List MirTy}
    {callee : DefId} {rargs : List RefOperand} {rdst : RefPlace}
    {tgt : Option BasicBlockId} {unwind : UnwindAction} {t : TerminatorKind}
    (h : decodeTerminator types (.call callee rargs rdst tgt unwind) = some t) :
    ∃ args dst,
      mapOption (decodeOperand types) rargs = some args ∧
      decodePlace types rdst = some dst ∧
      t = .call callee args dst tgt unwind := by
  dsimp only [decodeTerminator, optMap2] at h
  cases h_a : mapOption (decodeOperand types) rargs with
  | none => rw [h_a] at h; cases h
  | some args =>
    rw [h_a] at h
    cases h_d : decodePlace types rdst with
    | none => rw [h_d] at h; cases h
    | some dst =>
      rw [h_d] at h
      injection h with h_eq
      exact ⟨args, dst, rfl, rfl, h_eq.symm⟩

private theorem decodeTerminator_sysrootCall_inv {types : List MirTy}
    {op : SysrootNumOp} {rargs : List RefOperand} {rdst : RefPlace}
    {tgt : Option BasicBlockId} {unwind : UnwindAction} {t : TerminatorKind}
    (h : decodeTerminator types (.sysrootCall op rargs rdst tgt unwind) = some t) :
    ∃ args dst,
      mapOption (decodeOperand types) rargs = some args ∧
      decodePlace types rdst = some dst ∧
      t = .sysrootCall op args dst tgt unwind := by
  dsimp only [decodeTerminator, optMap2] at h
  cases h_a : mapOption (decodeOperand types) rargs with
  | none => rw [h_a] at h; cases h
  | some args =>
    rw [h_a] at h
    cases h_d : decodePlace types rdst with
    | none => rw [h_d] at h; cases h
    | some dst =>
      rw [h_d] at h
      injection h with h_eq
      exact ⟨args, dst, rfl, rfl, h_eq.symm⟩

private theorem decodeTerminator_coreCall_inv {types : List MirTy}
    {op : CoreCallOp} {rargs : List RefOperand} {rdst : RefPlace}
    {tgt : Option BasicBlockId} {unwind : UnwindAction} {t : TerminatorKind}
    (h : decodeTerminator types (.coreCall op rargs rdst tgt unwind) = some t) :
    ∃ args dst,
      mapOption (decodeOperand types) rargs = some args ∧
      decodePlace types rdst = some dst ∧
      t = .coreCall op args dst tgt unwind := by
  dsimp only [decodeTerminator, optMap2] at h
  cases h_a : mapOption (decodeOperand types) rargs with
  | none => rw [h_a] at h; cases h
  | some args =>
    rw [h_a] at h
    cases h_d : decodePlace types rdst with
    | none => rw [h_d] at h; cases h
    | some dst =>
      rw [h_d] at h
      injection h with h_eq
      exact ⟨args, dst, rfl, rfl, h_eq.symm⟩

private theorem decodeTerminator_callNe_inv {types : List MirTy}
    {eqCallee : DefId} {rargs : List RefOperand} {rdst : RefPlace}
    {tgt : Option BasicBlockId} {unwind : UnwindAction} {t : TerminatorKind}
    (h : decodeTerminator types (.callNe eqCallee rargs rdst tgt unwind) = some t) :
    ∃ args dst,
      mapOption (decodeOperand types) rargs = some args ∧
      decodePlace types rdst = some dst ∧
      t = .callNe eqCallee args dst tgt unwind := by
  dsimp only [decodeTerminator, optMap2] at h
  cases h_a : mapOption (decodeOperand types) rargs with
  | none => rw [h_a] at h; cases h
  | some args =>
    rw [h_a] at h
    cases h_d : decodePlace types rdst with
    | none => rw [h_d] at h; cases h
    | some dst =>
      rw [h_d] at h
      injection h with h_eq
      exact ⟨args, dst, rfl, rfl, h_eq.symm⟩

private theorem decodeTerminator_drop_inv {types : List MirTy}
    {rplace : RefPlace} {tgt : BasicBlockId} {unwind : UnwindAction}
    {t : TerminatorKind}
    (h : decodeTerminator types (.drop rplace tgt unwind) = some t) :
    ∃ place, decodePlace types rplace = some place ∧
      t = .drop place tgt unwind := by
  dsimp only [decodeTerminator, optMap] at h
  cases h_p : decodePlace types rplace with
  | none => rw [h_p] at h; cases h
  | some place =>
    rw [h_p] at h
    injection h with h_eq
    exact ⟨place, rfl, h_eq.symm⟩

private theorem refNatListContains_eq (x : Nat) :
    ∀ ys : List Nat, refNatListContains x ys = natListContains x ys
  | [] => rfl
  | _ :: rest => by
    dsimp only [refNatListContains, natListContains]
    rw [refNatListContains_eq x rest]

private theorem decodePlace_id_empty {ts : List MirTy} {rp : RefPlace} {p : Place}
    (h : decodePlace ts rp = some p) :
    p.localId = rp.localId ∧ p.projection.isEmpty = rp.projection.isEmpty := by
  dsimp only [decodePlace] at h
  cases h_m : mapOption (decodeProjElem ts) rp.projection with
  | none => rw [h_m] at h; cases h
  | some _ =>
    rw [h_m] at h
    injection h with h_eq
    subst h_eq
    refine ⟨rfl, ?_⟩
    cases h_rp : rp.projection with
    | nil =>
      rw [h_rp] at h_m
      injection h_m with hx
      subst hx
      rfl
    | cons pe rest =>
      rw [h_rp] at h_m
      dsimp only [mapOption, optMap2] at h_m
      cases h1 : decodeProjElem ts pe with
      | none => rw [h1] at h_m; cases h_m
      | some _ =>
        rw [h1] at h_m
        cases h2 : mapOption (decodeProjElem ts) rest with
        | none => rw [h2] at h_m; cases h_m
        | some _ => rw [h2] at h_m; injection h_m with hx; subst hx; rfl

private theorem mapOption_decodePlace_refMovePlaceList {ts : List MirTy} :
    ∀ {rargs : List RefOperand} {args : List Operand},
      mapOption (decodeOperand ts) rargs = some args →
      mapOption (decodePlace ts) (refMovePlaceList rargs) = some (movePlaceList args)
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by
    dsimp only [mapOption, optMap2] at h
    cases h_op : decodeOperand ts _ with
    | none => rw [h_op] at h; cases h
    | some _ =>
      rw [h_op] at h
      cases h_rest : mapOption (decodeOperand ts) _ <;> rw [h_rest] at h <;> cases h
  | ro :: rrest, op :: rest, h => by
    dsimp only [mapOption, optMap2] at h
    cases h1 : decodeOperand ts ro with
    | none => rw [h1] at h; cases h
    | some op' =>
      rw [h1] at h
      cases h2 : mapOption (decodeOperand ts) rrest with
      | none => rw [h2] at h; cases h
      | some rest' =>
        rw [h2] at h
        injection h with h_eq
        injection h_eq with h_o h_r
        subst h_o; subst h_r
        have ih := mapOption_decodePlace_refMovePlaceList h2
        cases ro with
        | copy rp =>
          dsimp only [decodeOperand, optMap] at h1
          cases h_p : decodePlace ts rp with
          | none => rw [h_p] at h1; cases h1
          | some _ => rw [h_p] at h1; injection h1 with hop; subst hop; exact ih
        | move rp =>
          dsimp only [decodeOperand, optMap] at h1
          cases h_p : decodePlace ts rp with
          | none => rw [h_p] at h1; cases h1
          | some _ =>
            rw [h_p] at h1; injection h1 with hop; subst hop
            dsimp only [refMovePlaceList, movePlaceList, mapOption, optMap2]
            rw [h_p, ih]
        | constant rc =>
          dsimp only [decodeOperand, optMap] at h1
          cases h_t : MirSemantics.getElem? ts rc.ty with
          | none => rw [h_t] at h1; cases h1
          | some _ => rw [h_t] at h1; injection h1 with hop; subst hop; exact ih

private theorem refPlacesDisjointAux_eq {ts : List MirTy} :
    ∀ (seen : List LocalId) (rps : List RefPlace) (ps : List Place),
      mapOption (decodePlace ts) rps = some ps →
      refPlacesDisjointAux seen rps = placesDisjointAux seen ps
  | _, [], [], _ => rfl
  | _, [], _ :: _, h => by cases h
  | _, _ :: _, [], h => by
    dsimp only [mapOption, optMap2] at h
    cases h1 : decodePlace ts _ with
    | none => rw [h1] at h; cases h
    | some _ => rw [h1] at h; cases h2 : mapOption (decodePlace ts) _ <;> rw [h2] at h <;> cases h
  | seen, rp :: rrest, p :: prest, h => by
    dsimp only [mapOption, optMap2] at h
    cases h1 : decodePlace ts rp with
    | none => rw [h1] at h; cases h
    | some p' =>
      rw [h1] at h
      cases h2 : mapOption (decodePlace ts) rrest with
      | none => rw [h2] at h; cases h
      | some prest' =>
        rw [h2] at h; injection h with h_eq; injection h_eq with hp hpr
        subst hp; subst hpr
        let ⟨h_id, h_emp⟩ := decodePlace_id_empty h1
        dsimp only [refPlacesDisjointAux, placesDisjointAux]
        rw [h_id, h_emp, refNatListContains_eq,
          refPlacesDisjointAux_eq (rp.localId :: seen) rrest prest' h2]

private theorem mapOption_append {α β : Type} (f : α → Option β) :
    ∀ {xs₁ xs₂ : List α} {ys₁ ys₂ : List β},
      mapOption f xs₁ = some ys₁ →
      mapOption f xs₂ = some ys₂ →
      mapOption f (xs₁ ++ xs₂) = some (ys₁ ++ ys₂)
  | [], _, [], _, _, h2 => h2
  | [], _, _ :: _, _, h1, _ => by cases h1
  | x :: xs, xs₂, ys₁, ys₂, h1, h2 => by
    dsimp only [mapOption, optMap2] at h1
    cases h_fx : f x with
    | none => rw [h_fx] at h1; cases h1
    | some y =>
      rw [h_fx] at h1
      cases h_rest : mapOption f xs with
      | none => rw [h_rest] at h1; cases h1
      | some ys =>
        rw [h_rest] at h1; injection h1 with h_eq; subst h_eq
        dsimp only [List.cons_append, mapOption, optMap2]
        rw [h_fx, mapOption_append f h_rest h2]

private theorem refMoveDefinitelyDisjoint_eq {ts : List MirTy}
    {rargs : List RefOperand} {args : List Operand} {rdst : RefPlace} {dst : Place}
    (h_args : mapOption (decodeOperand ts) rargs = some args)
    (h_dst : decodePlace ts rdst = some dst) :
    refMoveDefinitelyDisjoint rargs rdst = moveDefinitelyDisjoint args dst := by
  dsimp only [refMoveDefinitelyDisjoint, moveDefinitelyDisjoint]
  have h_mp := mapOption_decodePlace_refMovePlaceList h_args
  have h_one : mapOption (decodePlace ts) [rdst] = some [dst] := by
    dsimp only [mapOption, optMap2]; rw [h_dst]
  exact refPlacesDisjointAux_eq [] (refMovePlaceList rargs ++ [rdst])
    (movePlaceList args ++ [dst]) (mapOption_append (decodePlace ts) h_mp h_one)

private theorem refCallArgsMatchBody_eq {ts localTys : List MirTy} :
    ∀ {rargs : List RefOperand} {args : List Operand} {paramTys : List MirTy},
      mapOption (decodeOperand ts) rargs = some args →
      refCallArgsMatchBody ts localTys rargs paramTys =
        callArgsMatchBody localTys args paramTys
  | [], [], [], _ => rfl
  | [], [], _ :: _, _ => rfl
  | [], _ :: _, _, h => by cases h
  | _ :: _, [], _, h => by
    dsimp only [mapOption, optMap2] at h
    cases h_op : decodeOperand ts _ with
    | none => rw [h_op] at h; cases h
    | some _ =>
      rw [h_op] at h
      cases h_rest : mapOption (decodeOperand ts) _ <;> rw [h_rest] at h <;> cases h
  | _ :: _, _ :: _, [], _ => rfl
  | ro :: rrest, op :: rest, paramTy :: restParams, h => by
    dsimp only [mapOption, optMap2] at h
    cases h1 : decodeOperand ts ro with
    | none => rw [h1] at h; cases h
    | some op' =>
      rw [h1] at h
      cases h2 : mapOption (decodeOperand ts) rrest with
      | none => rw [h2] at h; cases h
      | some rest' =>
        rw [h2] at h
        injection h with h_eq
        injection h_eq with ho hr
        subst ho; subst hr
        have ih := refCallArgsMatchBody_eq (localTys := localTys)
          (paramTys := restParams) h2
        dsimp only [refCallArgsMatchBody, callArgsMatchBody]
        rw [ih]
        refine congrArg (· && _) ?_
        cases ro with
        | copy rp =>
          dsimp only [decodeOperand, optMap] at h1
          cases h_p : decodePlace ts rp with
          | none => rw [h_p] at h1; cases h1
          | some pl =>
            rw [h_p] at h1; injection h1 with hop; subst hop
            let ⟨h_id, h_emp⟩ := decodePlace_id_empty h_p
            dsimp only; rw [h_id, h_emp]; rfl
        | move rp =>
          dsimp only [decodeOperand, optMap] at h1
          cases h_p : decodePlace ts rp with
          | none => rw [h_p] at h1; cases h1
          | some pl =>
            rw [h_p] at h1; injection h1 with hop; subst hop
            let ⟨h_id, h_emp⟩ := decodePlace_id_empty h_p
            dsimp only; rw [h_id, h_emp]; rfl
        | constant rc =>
          dsimp only [decodeOperand, optMap] at h1
          cases h_t : MirSemantics.getElem? ts rc.ty with
          | none => rw [h_t] at h1; cases h1
          | some cTy =>
            rw [h_t] at h1; injection h1 with hop; subst hop
            dsimp only; rw [h_t]; dsimp only; rw [evalRefConstLit_eq]; rfl

private theorem refCallTargetAdmitted_eq {ts : List MirTy}
    {rbody : RefBody} {body calleeBody : Body}
    {rbb : RefBasicBlock} {bb : BasicBlock}
    {calleeArgCount : Nat} {calleeLocalTys : List MirTy}
    {rargs : List RefOperand} {args : List Operand}
    {rdst : RefPlace} {dst : Place}
    {target : Option BasicBlockId} {unwind : UnwindAction}
    (h_bdec : decodeBody ts rbody = some body)
    (h_bb : decodeBasicBlock ts rbb = some bb)
    (h_cac : calleeArgCount = calleeBody.argumentCount)
    (h_clt : calleeLocalTys = calleeBody.locals)
    (h_args : mapOption (decodeOperand ts) rargs = some args)
    (h_dst : decodePlace ts rdst = some dst) :
    refCallTargetAdmitted ts body.locals rbody rbb calleeArgCount calleeLocalTys
        rargs rdst target unwind =
      callTargetAdmitted body bb calleeBody args dst target unwind := by
  let ⟨_, _, h_bbs, _, _⟩ := decodeBody_inv h_bdec
  let ⟨_, _, h_cl⟩ := decodeBasicBlock_inv h_bb
  let ⟨h_did, h_demp⟩ := decodePlace_id_empty h_dst
  unfold refCallTargetAdmitted callTargetAdmitted
  rw [h_cac, h_clt, h_cl, mapOption_length h_bbs, h_did, h_demp,
    refMoveDefinitelyDisjoint_eq h_args h_dst, mapOption_length h_args,
    refCallArgsMatchBody_eq h_args]
  cases MirSemantics.getElem? body.locals rdst.localId with
  | none =>
    cases MirSemantics.getElem? calleeBody.locals 0 <;> rfl
  | some dstTy =>
    cases MirSemantics.getElem? calleeBody.locals 0 with
    | none => rfl
    | some _ => dsimp only; rw [refIsSupportedLocalTy_eq]; rfl

private theorem refCallsAdmitted_eq {rp : RefProg} {p : Program}
    {rbody : RefBody} {body : Body}
    (h_dec : decodeProg rp = some p)
    (h_bdec : decodeBody rp.types rbody = some body) :
    refCallsAdmitted rp body.locals rbody = callsAdmitted p body := by
  let ⟨_, _, _, _, h_bodies⟩ := decodeProg_inv h_dec
  let ⟨_, _, h_bbs, _, _⟩ := decodeBody_inv h_bdec
  unfold refCallsAdmitted callsAdmitted
  apply mapOption_all_eq _ h_bbs
  intro rbb bb h_bb
  let ⟨_, h_term, _⟩ := decodeBasicBlock_inv h_bb
  cases h_rt : rbb.terminator with
  | call callee rargs rdst tgt uw =>
    rw [h_rt] at h_term
    let ⟨args, dst, h_args, h_dst, h_bt⟩ := decodeTerminator_call_inv h_term
    rw [h_bt]
    dsimp only
    cases h_cb : MirSemantics.getElem? p.bodies callee with
    | none =>
      rw [(mapOption_getElem? h_bodies callee).1 h_cb]
    | some calleeBody =>
      let ⟨calleeRbody, h_rcb, h_cbdec⟩ :=
        (mapOption_getElem? h_bodies callee).2 calleeBody h_cb
      let ⟨h_carg, h_clocs, _, h_cunsafe, _⟩ := decodeBody_inv h_cbdec
      rw [h_rcb]; dsimp only; rw [h_clocs]; dsimp only
      rw [h_cunsafe]
      exact congrArg (fun b => !calleeBody.isUnsafe && b)
        (refCallTargetAdmitted_eq h_bdec h_bb h_carg rfl h_args h_dst)
  | sysrootCall op rargs rdst tgt uw =>
    rw [h_rt] at h_term
    let ⟨args, dst, h_args, h_dst, h_bt⟩ :=
      decodeTerminator_sysrootCall_inv h_term
    rw [h_bt]
    exact refCallTargetAdmitted_eq h_bdec h_bb rfl rfl h_args h_dst
  | goto tgt | return_ | unreachable | unwindResume | unsupported =>
    rw [h_rt] at h_term
    injection h_term with h_eq
    rw [← h_eq]
  | coreCall op rargs rdst tgt uw =>
    rw [h_rt] at h_term
    let ⟨_, _, _, _, h_bt⟩ := decodeTerminator_coreCall_inv h_term
    rw [h_bt]
  | callNe eqCallee rargs rdst tgt uw =>
    rw [h_rt] at h_term
    let ⟨_, _, _, _, h_bt⟩ := decodeTerminator_callNe_inv h_term
    rw [h_bt]
  | drop rplace tgt uw =>
    rw [h_rt] at h_term
    let ⟨_, _, h_bt⟩ := decodeTerminator_drop_inv h_term
    rw [h_bt]
  | switchInt discr targets =>
    rw [h_rt] at h_term
    dsimp only [decodeTerminator, optMap] at h_term
    cases h_op : decodeOperand rp.types discr with
    | none => rw [h_op] at h_term; cases h_term
    | some _ => rw [h_op] at h_term; injection h_term with h_eq; rw [← h_eq]
  | assert cond exp msg tgt uw =>
    rw [h_rt] at h_term
    dsimp only [decodeTerminator, optMap] at h_term
    cases h_op : decodeOperand rp.types cond with
    | none => rw [h_op] at h_term; cases h_term
    | some _ => rw [h_op] at h_term; injection h_term with h_eq; rw [← h_eq]

private theorem refBodyHasAnyCall_eq {ts : List MirTy} {rbody : RefBody}
    {body : Body} (h_bdec : decodeBody ts rbody = some body) :
    refBodyHasAnyCall rbody = bodyHasAnyCall body := by
  unfold refBodyHasAnyCall bodyHasAnyCall
  apply mapOption_any_eq _ (decodeBody_inv h_bdec).2.2.1
  intro rbb bb h_bb
  have h_term := (decodeBasicBlock_inv h_bb).2.1
  cases h_rt : rbb.terminator with
  | call callee rargs rdst tgt uw =>
    rw [h_rt] at h_term
    let ⟨_, _, _, _, h_bt⟩ := decodeTerminator_call_inv h_term
    rw [h_bt]
  | sysrootCall op rargs rdst tgt uw =>
    rw [h_rt] at h_term
    let ⟨_, _, _, _, h_bt⟩ := decodeTerminator_sysrootCall_inv h_term
    rw [h_bt]
  | goto _ | return_ | unreachable | unwindResume | unsupported =>
    rw [h_rt] at h_term; injection h_term with h_eq; rw [← h_eq]
  | coreCall op rargs rdst tgt uw =>
    rw [h_rt] at h_term
    let ⟨_, _, _, _, h_bt⟩ := decodeTerminator_coreCall_inv h_term
    rw [h_bt]
  | callNe eqCallee rargs rdst tgt uw =>
    rw [h_rt] at h_term
    let ⟨_, _, _, _, h_bt⟩ := decodeTerminator_callNe_inv h_term
    rw [h_bt]
  | drop rplace tgt uw =>
    rw [h_rt] at h_term
    let ⟨_, _, h_bt⟩ := decodeTerminator_drop_inv h_term
    rw [h_bt]
  | switchInt discr _ =>
    rw [h_rt] at h_term; dsimp only [decodeTerminator, optMap] at h_term
    cases h_op : decodeOperand ts discr with
    | none => rw [h_op] at h_term; cases h_term
    | some _ => rw [h_op] at h_term; injection h_term with h_eq; rw [← h_eq]
  | assert cond _ _ _ _ =>
    rw [h_rt] at h_term; dsimp only [decodeTerminator, optMap] at h_term
    cases h_op : decodeOperand ts cond with
    | none => rw [h_op] at h_term; cases h_term
    | some _ => rw [h_op] at h_term; injection h_term with h_eq; rw [← h_eq]

private theorem refSingleBodyStaticAdmitted_eq {rp : RefProg} {p : Program}
    {rbody : RefBody} {body : Body}
    (h_dec : decodeProg rp = some p)
    (h_bdec : decodeBody rp.types rbody = some body) :
    refSingleBodyStaticAdmitted rp rbody = singleBodyStaticAdmitted p body := by
  let ⟨_, h_width, h_prof, _, _⟩ := decodeProg_inv h_dec
  let ⟨h_arg, h_loc, h_bbs, _, h_id⟩ := decodeBody_inv h_bdec
  have h_str : stringIsEmpty body.identity = rbody.identity.toByteArray.data.toList.isEmpty := by
    rw [← h_id]; rfl
  unfold refSingleBodyStaticAdmitted singleBodyStaticAdmitted
  rw [h_loc]
  dsimp only
  rw [h_width, h_prof, h_str, h_arg, mapOption_isEmpty h_bbs,
    refStorageAnnotationsInBounds_eq h_bdec,
    refDiscriminantTypesValid_eq h_bdec, refCastTypesValid_eq h_bdec,
    refAssertConditionTypesValid_eq h_bdec,
    list_all_congr_eq body.locals _ _ refIsSupportedLocalTy_eq,
    refCallsAdmitted_eq h_dec h_bdec]

private theorem refCallBodyStaticAdmitted_eq {rp : RefProg} {p : Program}
    {rbody : RefBody} {body : Body}
    (h_dec : decodeProg rp = some p)
    (h_bdec : decodeBody rp.types rbody = some body) :
    refCallBodyStaticAdmitted rp rbody = callBodyStaticAdmitted p body := by
  unfold refCallBodyStaticAdmitted callBodyStaticAdmitted
  rw [refSingleBodyStaticAdmitted_eq h_dec h_bdec, (decodeBody_inv h_bdec).2.1]
  dsimp only
  rw [refAssignTypesValid_eq h_bdec]

private theorem refAllCallBodiesStaticAdmitted_eq {rp : RefProg} {p : Program}
    {rbody : RefBody} {body : Body}
    (h_dec : decodeProg rp = some p)
    (h_bdec : decodeBody rp.types rbody = some body) :
    refAllCallBodiesStaticAdmitted rp rbody =
      allCallBodiesStaticAdmitted p body := by
  let ⟨_, _, _, _, h_bodies⟩ := decodeProg_inv h_dec
  unfold refAllCallBodiesStaticAdmitted allCallBodiesStaticAdmitted
  rw [refBodyHasAnyCall_eq h_bdec]
  cases h_any : bodyHasAnyCall body with
  | false => rfl
  | true =>
    rw [(decodeBody_inv h_bdec).2.1]
    dsimp only
    rw [refAssignTypesValid_eq h_bdec,
      mapOption_all_eq (fun _ _ hb => refCallBodyStaticAdmitted_eq h_dec hb) h_bodies]

theorem initRefState_sim_base : InitRefStateSimClaim := by
  intro rp p q maxSteps h_dec
  let ⟨h_entry, h_width, h_prof, _, h_bodies⟩ := decodeProg_inv h_dec
  unfold initRefState initState
  rw [h_entry, h_width, h_prof]
  cases Nat.beq p.pointerWidthBits 64
  · refine ⟨?_, fun s₀ hs₀ => by cases hs₀⟩
    intro k hk; injection hk with hk_eq; rw [← hk_eq]; rfl
  · dsimp only
    cases Nat.beq p.mirProfileVersion 1
    · refine ⟨?_, fun s₀ hs₀ => by cases hs₀⟩
      intro k hk; injection hk with hk_eq; rw [← hk_eq]; rfl
    · cases q.callerMem.allocations.isEmpty
      · refine ⟨?_, fun s₀ hs₀ => by cases hs₀⟩
        intro k hk; injection hk with hk_eq; rw [← hk_eq]; rfl
      · cases h_b : MirSemantics.getElem? p.bodies p.entryDefId with
        | none =>
          rw [(mapOption_getElem? h_bodies p.entryDefId).1 h_b]
          refine ⟨?_, fun s₀ hs₀ => by cases hs₀⟩
          intro k hk; injection hk with hk_eq; rw [← hk_eq]; rfl
        | some body =>
          let ⟨rbody, h_rb_get, h_rb_dec⟩ :=
            (mapOption_getElem? h_bodies p.entryDefId).2 body h_b
          let ⟨h_arg, h_loc_dec, h_bbs_dec, _, _⟩ := decodeBody_inv h_rb_dec
          rw [h_rb_get]
          dsimp only
          rw [h_loc_dec]
          dsimp only
          rw [mapOption_isEmpty h_bbs_dec, h_arg,
            refStorageAnnotationsInBounds_eq h_rb_dec,
            refDiscriminantTypesValid_eq h_rb_dec,
            refCastTypesValid_eq h_rb_dec,
            refAssertConditionTypesValid_eq h_rb_dec]
          cases body.basicBlocks.isEmpty
          · cases h_blt : Nat.blt body.argumentCount body.locals.length
            · refine ⟨?_, fun s₀ hs₀ => by cases hs₀⟩
              intro k hk; injection hk with hk_eq; rw [← hk_eq]; rfl
            · cases h_sa : storageAnnotationsInBounds body
              · refine ⟨?_, fun s₀ hs₀ => by cases hs₀⟩
                intro k hk; injection hk with hk_eq; rw [← hk_eq]; rfl
              · cases h_dv : discriminantTypesValid body
                · refine ⟨?_, fun s₀ hs₀ => by cases hs₀⟩
                  intro k hk; injection hk with hk_eq; rw [← hk_eq]; rfl
                · cases h_cv : castTypesValid body
                  · refine ⟨?_, fun s₀ hs₀ => by cases hs₀⟩
                    intro k hk; injection hk with hk_eq; rw [← hk_eq]; rfl
                  · cases h_act : assertConditionTypesValid body
                    · refine ⟨?_, fun s₀ hs₀ => by cases hs₀⟩
                      intro k hk; injection hk with hk_eq; rw [← hk_eq]; rfl
                    · rw [list_all_congr_eq body.locals _ _
                        refIsSupportedLocalTy_eq]
                      cases h_supp : body.locals.all isSupportedScalarOrUnitTy
                      · refine ⟨?_, fun s₀ hs₀ => by cases hs₀⟩
                        intro k hk; injection hk with hk_eq; rw [← hk_eq]; rfl
                      · rw [refCallsAdmitted_eq h_dec h_rb_dec,
                          refAllCallBodiesStaticAdmitted_eq h_dec h_rb_dec]
                        cases h_calls : callsAdmitted p body
                        · refine ⟨?_, fun s₀ hs₀ => by cases hs₀⟩
                          intro k hk; injection hk with hk_eq; rw [← hk_eq]; rfl
                        · cases h_all_static : allCallBodiesStaticAdmitted p body
                          · refine ⟨?_, fun s₀ hs₀ => by cases hs₀⟩
                            intro k hk; injection hk with hk_eq; rw [← hk_eq]; rfl
                          · rw [checkRefArgsMatch_eq]
                            cases h_args : checkArgsMatch q.args
                                ((body.locals.drop 1).take body.argumentCount)
                            · refine ⟨?_, fun s₀ hs₀ => by cases hs₀⟩
                              intro k hk; injection hk with hk_eq; rw [← hk_eq]; rfl
                            · let ⟨retTy, h_ret⟩ := getElem?_zero_of_blt h_blt
                              let ⟨mem, retPlace, h_init_mem⟩ :=
                                refInitMemoryAndRetPlace_ok rp.types retTy
                              rw [h_ret]
                              dsimp only
                              rw [h_init_mem]
                              dsimp only
                              refine ⟨?_, ?_⟩
                              · intro k hk; cases hk
                              · intro s₀ hs₀
                                injection hs₀ with h_s₀
                                subst h_s₀
                                rw [initRefLocalsLoop_eq h_rb_dec q.args 0
                                  body.locals]
                                have h_entry_ret : entryRetTy? p = some retTy := by
                                  dsimp only [entryRetTy?]
                                  rw [h_b]
                                  exact h_ret
                                have h_sm := initLocalsLoop_slotsMatchTys body q.args h_args
                                refine ⟨_, rfl, ?_, rfl, rfl⟩
                                exact ⟨Array.mk [mkRefMiriFrame rp.types p.entryDefId rbody 0 0
                                    (liftLocals rp.types body.locals
                                      (initLocalsLoop body q.args 0 body.locals))
                                    retPlace],
                                  retTy, mem, refInitControl, none, h_dec, rfl, rfl,
                                  h_entry_ret, rfl, h_init_mem, refControlValid_init,
                                  rfl, rfl,
                                  FramesSimInv.root rfl rfl rfl rfl
                                    ⟨body, rbody, List.replicate body.locals.length true,
                                      h_b, h_rb_get, h_rb_dec, h_blt, h_sa, h_dv, h_cv, h_act,
                                      h_calls, h_all_static, h_supp, h_sm,
                                      fun _ _ => Nat.zero_le _, rfl, by
                                        rw [liftLocalsCached_replicate_true rp.types
                                          (SlotsMatchTys.length_eq h_sm)]⟩⟩
          · refine ⟨?_, fun s₀ hs₀ => by cases hs₀⟩
            intro k hk; injection hk with hk_eq; rw [← hk_eq]; rfl

/-! ## Single-Step and Multi-Step Simulation Helpers -/

theorem simulationInv_with_counters {rp : RefProg} {p : Program} {s : State}
    {rs : RefState} (steps max : Nat) (h : SimulationInv rp p s rs) :
    SimulationInv rp p s { rs with stepsExecuted := steps, maxSteps := max } := by
  let ⟨rframes, retTy, mem, ctrl, topRel?, h_dec, hne, hm, hert, hrty, hinit,
    hctrl, htr, hmiri, hfsim⟩ := h
  exact ⟨rframes, retTy, mem, ctrl, topRel?, h_dec, hne, hm, hert, hrty, hinit,
    hctrl, htr, hmiri, hfsim⟩

theorem simulationInv_of_with_counters {rp : RefProg} {p : Program} {s : State}
    {rs : RefState} {steps max : Nat}
    (h : SimulationInv rp p s
      { rs with stepsExecuted := steps, maxSteps := max }) :
    SimulationInv rp p s rs := by
  let ⟨rframes, retTy, mem, ctrl, topRel?, h_dec, hne, hm, hert, hrty, hinit,
    hctrl, htr, hmiri, hfsim⟩ := h
  exact ⟨rframes, retTy, mem, ctrl, topRel?, h_dec, hne, hm, hert, hrty, hinit,
    hctrl, htr, hmiri, hfsim⟩

private theorem array_eq_singleton_of_toList_reverse {α : Type} {xs : Array α} {x : α}
    (h : xs.toList.reverse = [x]) : xs = Array.mk [x] := by
  cases xs with
  | mk _ =>
    dsimp only at h
    have h_rev := congrArg List.reverse h
    rw [List.reverse_reverse] at h_rev
    exact congrArg Array.mk h_rev

private theorem array_eq_push_of_toList_reverse {α : Type} {xs : Array α}
    {top : α} {rest : List α}
    (h : xs.toList.reverse = top :: rest) :
    xs = (⟨rest.reverse⟩ : Array α).push top := by
  cases xs with
  | mk _ =>
    dsimp only at h
    have h_rev := congrArg List.reverse h
    rw [List.reverse_reverse, List.reverse_cons] at h_rev
    dsimp only [Array.push]
    rw [List.concat_eq_append]
    exact congrArg Array.mk h_rev

private theorem array_reverse_cons_push {α : Type} (hd : α) (tl : List α) :
    (⟨(hd :: tl).reverse⟩ : Array α) = (⟨tl.reverse⟩ : Array α).push hd := by
  simp [Array.push, List.reverse_cons, List.concat_eq_append]

private theorem array_back?_push {α : Type} (arr : Array α) (x : α) :
    (arr.push x).back? = some x := by
  simp [Array.back?]

private theorem framesSimInv_length_eq {rp : RefProg} {p : Program}
    {retPlace : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance}
    {fs : List FrameState}
    {rfs : List (Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)}
    (h : FramesSimInv rp p retPlace fs rfs) : rfs.length = fs.length := by
  induction h with
  | root => rfl
  | push _ _ _ _ _ _ _ _ _ _ _ _ ih => simp [ih]

private theorem updateCacheLoop_replicate_true (touched : Nat → Bool) :
    ∀ (idx n : Nat),
      updateCacheLoop touched idx (List.replicate n true) =
        List.replicate n true
  | _, 0 => rfl
  | idx, n + 1 => by
    dsimp only [List.replicate, updateCacheLoop]
    rw [Bool.true_or, updateCacheLoop_replicate_true touched (idx + 1) n]

private theorem calleeInitCacheLoop_length (argCount idx : Nat) :
    ∀ tys : List MirTy, (calleeInitCacheLoop argCount idx tys).length = tys.length
  | [] => rfl
  | _ :: rest => congrArg Nat.succ (calleeInitCacheLoop_length argCount (idx + 1) rest)

private theorem getElem?_updateCacheLoop_eq_true (touched : Nat → Bool) :
    ∀ (idx i : Nat) (cache : List Bool),
      i < cache.length →
      touched (idx + i) = true →
      MirSemantics.getElem? (updateCacheLoop touched idx cache) i = some true
  | _, _, [], h_lt, _ => by cases h_lt
  | idx, 0, _ :: _, _, h_t => by
    dsimp only [updateCacheLoop, MirSemantics.getElem?]
    rw [Nat.add_zero] at h_t
    rw [h_t, Bool.or_true]
  | idx, i + 1, _ :: bs, h_lt, h_t => by
    dsimp only [updateCacheLoop, MirSemantics.getElem?]
    have h_lt' : i < bs.length := Nat.lt_of_succ_lt_succ h_lt
    have h_t' : touched ((idx + 1) + i) = true := by
      rw [Nat.add_assoc, Nat.add_comm 1 i]; exact h_t
    exact getElem?_updateCacheLoop_eq_true touched (idx + 1) i bs h_lt' h_t'

private theorem getElem?_liftLocalsCached_layout_isSome_of_true
    (types : List MirTy) :
    ∀ (tys : List MirTy) (slots : List LocalSlot) (cache : List Bool) (i : Nat),
      tys.length = slots.length →
      slots.length = cache.length →
      MirSemantics.getElem? cache i = some true →
      ∃ ls,
        MirSemantics.getElem? (liftLocalsCached types tys slots cache) i =
          some ls ∧
        ls.layout.isSome = true := by
  intro tys
  induction tys with
  | nil =>
    intro slots cache i h1 h2 h_get
    cases cache with
    | nil => cases h_get
    | cons _ _ => cases slots <;> simp at h1 h2
  | cons ty tys ih =>
    intro slots cache i h1 h2 h_get
    cases slots with
    | nil => simp at h1
    | cons slot slots =>
      cases cache with
      | nil => simp at h2
      | cons b bs =>
        cases i with
        | zero =>
          dsimp only [MirSemantics.getElem?] at h_get
          injection h_get with h_eq
          subst h_eq
          exact ⟨_, rfl, rfl⟩
        | succ j =>
          exact ih slots bs j (Nat.succ.inj h1) (Nat.succ.inj h2) h_get

private theorem getElem?_liftLocalsCached_layout_isSome (types : List MirTy) :
    ∀ (tys : List MirTy) (slots : List LocalSlot) (cache : List Bool) (id : Nat)
      {ls : Miri.Interpreter.LocalState Miri.Memory.Provenance Miri.Interpreter.LocalLayout},
      tys.length = slots.length →
      slots.length = cache.length →
      MirSemantics.getElem? (liftLocalsCached types tys slots cache) id = some ls →
      ls.layout.isSome = true →
      MirSemantics.getElem? cache id = some true
  | [], _, _, _, _, _, _, h, _ => by cases h
  | _ :: _, [], _, _, _, h1, _, _, _ => by cases h1
  | _ :: _, _ :: _, [], _, _, _, h2, _, _ => by cases h2
  | ty :: tys, slot :: slots, b :: bs, 0, ls, _, _, h_get, h_is => by
    dsimp only [liftLocalsCached, MirSemantics.getElem?] at h_get
    injection h_get with h_eq
    subst h_eq
    cases b with
    | true => rfl
    | false => dsimp only [refLocalStateOfSlotWithCache] at h_is; cases h_is
  | ty :: tys, slot :: slots, b :: bs, i + 1, ls, h1, h2, h_get, h_is =>
    getElem?_liftLocalsCached_layout_isSome types tys slots bs i
      (Nat.succ.inj h1) (Nat.succ.inj h2) h_get h_is

private theorem refResolveCalleeBody_crate (rp : RefProg) (defId : DefId)
    (rbody : RefBody) (localTys : List MirTy)
    (h_get : MirSemantics.getElem? rp.bodies defId = some rbody)
    (h_locs : decodeLocalTys rp.types rbody.locals = some localTys) :
    refResolveCalleeBody rp (fnTagForCrate defId) = some (rbody, localTys) := by
  have h_mod : (Nat.mod (2 * defId) 2 == 0) = true := by
    change (HMod.hMod (2 * defId) 2 == 0) = true
    rw [Nat.mul_mod_right]; rfl
  have h_div : Nat.div (2 * defId) 2 = defId := Nat.mul_div_right defId (by decide)
  dsimp only [refResolveCalleeBody, fnTagForCrate]
  rw [h_mod, ite_eq_left rfl, h_div, h_get]
  dsimp only
  rw [h_locs]

private theorem sysrootNumOpOfCode_code (op : SysrootNumOp) :
    sysrootNumOpOfCode (sysrootNumOpCode op) = some op := by
  cases op with | mk k w s => cases k <;> cases w <;> cases s <;> rfl

private theorem refResolveCalleeBody_sysroot (rp : RefProg) (op : SysrootNumOp) :
    refResolveCalleeBody rp (fnTagForSysroot op) =
      some (sysrootNumRefBody rp.types op,
        [.int op.width op.signed, .int op.width op.signed, .int op.width op.signed]) := by
  have h_mod : (Nat.mod (2 * sysrootNumOpCode op + 1) 2 == 0) = false := by
    change (HMod.hMod (2 * sysrootNumOpCode op + 1) 2 == 0) = false
    rw [Nat.mul_add_mod]; rfl
  have h_div : Nat.div (2 * sysrootNumOpCode op + 1) 2 = sysrootNumOpCode op := by
    change HDiv.hDiv (2 * sysrootNumOpCode op + 1) 2 = sysrootNumOpCode op
    rw [Nat.mul_add_div (show 0 < 2 from by decide)]; rfl
  dsimp only [refResolveCalleeBody, fnTagForSysroot]
  rw [h_mod, ite_eq_right (by decide), h_div, sysrootNumOpOfCode_code]

private theorem sysrootNumRefBody_decode_of_types (types : List MirTy)
    (op : SysrootNumOp) {tid : TyId}
    (h_mem : MirSemantics.getElem? types tid = some (.int op.width op.signed)) :
    decodeBody types (sysrootNumRefBody types op) = some (sysrootNumBody op) := by
  have h_res : MirSemantics.getElem? types (tyIdFor types (.int op.width op.signed)) =
      some (.int op.width op.signed) := (resolveTy_tyIdFor_of_mem h_mem).1
  have h_locs :
      decodeLocalTys types (sysrootNumRefBody types op).locals =
        some [.int op.width op.signed, .int op.width op.signed,
          .int op.width op.signed] := by
    dsimp only [sysrootNumRefBody, decodeLocalTys, mapOption, optMap, optMap2]
    rw [h_res]
  dsimp only [decodeBody]
  rw [h_locs]
  dsimp only [sysrootNumRefBody, mapOption, decodeBasicBlock, decodeStmt,
    decodePlace, decodeRvalue, decodeOperand, decodeTerminator, optMap, optMap2,
    sysrootNumBody]
  cases op.kind <;> rfl

private theorem evalStatement_preserves_meta {body : Body} {f f' : FrameState}
    {amem mem' : MemoryState} {cm cm' : CallerMemory} {stmt : StatementKind}
    (h : evalStatement body f amem cm stmt =
      .step { frames := [f'], callerMem := cm', mem := mem' }) :
    f'.sysrootOp? = f.sysrootOp? ∧ f'.retDst? = f.retDst? ∧
      f'.retTarget? = f.retTarget? := by
  cases stmt with
  | nop =>
    injection h with hs; injection hs with hfs
    have h_f := (List.cons.inj hfs).1
    rw [← h_f]; exact ⟨rfl, rfl, rfl⟩
  | storageLive localId =>
    dsimp only [evalStatement] at h
    cases h1 : MirSemantics.getElem? body.locals localId with
    | none => rw [h1] at h; cases h
    | some _ =>
      rw [h1] at h; dsimp only at h
      cases h2 : MirSemantics.getElem? f.locals localId with
      | none => rw [h2] at h; cases h
      | some _ =>
        rw [h2] at h; dsimp only at h
        cases h3 : MirSemantics.setElem? f.locals localId _ with
        | none => rw [h3] at h; cases h
        | some _ =>
          rw [h3] at h; dsimp only at h
          cases h4 : deallocateLocal amem _ with
          | error _ => rw [h4] at h; cases h
          | ok _ =>
            rw [h4] at h
            injection h with hs; injection hs with hfs
            have h_f := (List.cons.inj hfs).1
            rw [← h_f]; exact ⟨rfl, rfl, rfl⟩
  | storageDead localId =>
    dsimp only [evalStatement] at h
    cases h0 : Nat.beq localId 0 <;> rw [h0] at h
    · cases h2 : MirSemantics.getElem? f.locals localId with
      | none => rw [h2] at h; cases h
      | some _ =>
        rw [h2] at h; dsimp only at h
        cases h3 : MirSemantics.setElem? f.locals localId .dead with
        | none => rw [h3] at h; cases h
        | some _ =>
          rw [h3] at h; dsimp only at h
          cases h4 : deallocateLocal amem _ with
          | error _ => rw [h4] at h; cases h
          | ok _ =>
            rw [h4] at h
            injection h with hs; injection hs with hfs
            have h_f := (List.cons.inj hfs).1
            rw [← h_f]; exact ⟨rfl, rfl, rfl⟩
    · cases h
  | assign dst rv =>
    dsimp only [evalStatement] at h
    cases h_emp : dst.projection.isEmpty <;> rw [h_emp] at h
    · cases h
    · cases h_ty : MirSemantics.getElem? body.locals dst.localId with
      | none => rw [h_ty] at h; cases h
      | some dstTy =>
        rw [h_ty] at h; dsimp only at h
        cases h_rv : evalRvalue body.locals f.locals amem dstTy rv with
        | error _ => rw [h_rv] at h; cases h
        | ok r1 =>
          rw [h_rv] at h; cases r1 with | mk val rest =>
          cases rest with | mk lR mR =>
          dsimp only at h
          cases h_wr : writePlace lR mR dst.localId dstTy val with
          | error _ => rw [h_wr] at h; cases h
          | ok p2 =>
            rw [h_wr] at h
            injection h with hs; injection hs with hfs
            have h_f := (List.cons.inj hfs).1
            rw [← h_f]; exact ⟨rfl, rfl, rfl⟩
  | unsupported => cases h

private theorem evalTerminator_preserves_meta {body : Body} {bb : BasicBlock}
    {f f' : FrameState} {amem mem' : MemoryState} {cm cm' : CallerMemory}
    {ps : PanicStrategy} {lh : Bool}
    (h : evalTerminator body bb f amem cm ps lh =
      .step { frames := [f'], callerMem := cm', mem := mem' }) :
    f'.sysrootOp? = f.sysrootOp? ∧ f'.retDst? = f.retDst? ∧
      f'.retTarget? = f.retTarget? := by
  cases bb with | mk stmts term cleanup =>
  cases term with
  | goto tgt =>
    injection h with hs; injection hs with hfs
    have h_f := (List.cons.inj hfs).1
    rw [← h_f]; exact ⟨rfl, rfl, rfl⟩
  | return_ =>
    dsimp only [evalTerminator] at h
    cases cleanup
    · cases h0 : MirSemantics.getElem? f.locals 0 with
      | none => rw [h0] at h; cases h
      | some sl =>
        rw [h0] at h
        cases sl with
        | dead => cases h
        | partialTuple _ => cases h
        | immediate o => cases o <;> cases h
        | indirect _ =>
          dsimp only at h
          cases h1 : MirSemantics.getElem? body.locals 0 with
          | none => rw [h1] at h; cases h
          | some _ =>
            rw [h1] at h; dsimp only at h
            cases h2 : loadIndirect amem _ _ with
            | error _ => rw [h2] at h; cases h
            | ok o => rw [h2] at h; cases o <;> cases h
    · cases h
  | unreachable | unwindResume | call _ _ _ _ _ | sysrootCall _ _ _ _ _
  | coreCall _ _ _ _ _ | unsupported | callNe _ _ _ _ _ | drop _ _ _ => cases h
  | assert cond expected msg target unwind =>
    dsimp only [evalTerminator] at h
    cases h_c : evalPrimitiveOperand body.locals f.locals amem cond with
    | error _ => rw [h_c] at h; cases h
    | ok res =>
      rw [h_c] at h
      cases res with | mk condVal rest =>
      cases rest with | mk lC mC =>
      dsimp only at h
      cases condVal with
      | bool b =>
        dsimp only at h
        cases h_b : (b == expected) with
        | true =>
          rw [h_b] at h
          injection h with hs; injection hs with hfs
          have h_f := (List.cons.inj hfs).1
          rw [← h_f]; exact ⟨rfl, rfl, rfl⟩
        | false =>
          rw [h_b] at h
          dsimp only [evalAssertFailure] at h
          cases msg with
          | misalignedPtrDeref | nullPtrDeref | unsupported => cases h
          | boundsCheck | overflowNeg | divByZero | remByZero =>
            cases lh <;> cases ps <;> cases unwind <;> cases h
          | overflow op =>
            cases op <;>
              (first
                | (cases lh <;> cases ps <;> cases unwind <;> cases h)
                | cases h)
      | scalar _ | char _ | unit | enumVal _ _ | tuple _ | ptr _ | slicePtr _ _
      | rangeTo _ | rangeFrom _ | bytes _ | array _ | ordering _ | optionVal _ | range _ _
      | boxPtr _ _ | vec _ _ _ =>
        cases h
  | switchInt discr targets =>
    dsimp only [evalTerminator] at h
    cases h_d : evalPrimitiveOperand body.locals f.locals amem discr with
    | error _ => rw [h_d] at h; cases h
    | ok res =>
      rw [h_d] at h
      cases res with | mk dv rest =>
      cases rest with | mk lD mD =>
      dsimp only at h
      have h_jump :
          ∀ tgt, jumpToBlock { f with locals := lD } mD cm tgt =
            .step { frames := [f'], callerMem := cm', mem := mem' } →
          f'.sysrootOp? = f.sysrootOp? ∧ f'.retDst? = f.retDst? ∧
            f'.retTarget? = f.retTarget? := by
        intro tgt hj
        injection hj with hs; injection hs with hfs
        have h_f := (List.cons.inj hfs).1
        rw [← h_f]; exact ⟨rfl, rfl, rfl⟩
      cases dv with
      | scalar sv =>
        dsimp only at h
        cases h_sw : evalSwitchBranches sv.width sv.bits targets.otherwise targets.branches <;>
          rw [h_sw] at h
        · cases h
        · exact h_jump _ h
      | bool b =>
        dsimp only at h
        cases h_sw : evalBoolSwitchBranches b targets.otherwise targets.branches <;>
          rw [h_sw] at h
        · cases h
        · exact h_jump _ h
      | char ch =>
        dsimp only at h
        cases h_sw : evalCharSwitchBranches ch targets.otherwise targets.branches <;>
          rw [h_sw] at h
        · cases h
        · exact h_jump _ h
      | unit | enumVal _ _ | tuple _ | array _ | ptr _ | bytes _ | ordering _
      | slicePtr _ _ | rangeTo _ | rangeFrom _ | range _ _ | optionVal _
      | boxPtr _ _ | vec _ _ _ =>
        dsimp only at h
        cases h_br : targets.branches with
        | cons _ _ => rw [h_br] at h; cases h
        | nil => rw [h_br] at h; exact h_jump _ h

private theorem evalCallArg_slotsMatchTys {callerLocalsTys : List MirTy}
    {locals locals' : List LocalSlot} {mem mem' : MemoryState} {hasMove : Bool}
    {opnd : Operand} {paramTy : MirTy} {v : Val}
    (h_inv : SlotsMatchTys callerLocalsTys locals)
    (h : evalCallArg callerLocalsTys locals mem hasMove opnd paramTy =
      .ok (v, locals', mem')) :
    SlotsMatchTys callerLocalsTys locals' ∧ checkVal v paramTy = true ∧
      mem' = mem := by
  unfold evalCallArg at h
  cases opnd with
  | constant c =>
    dsimp only at h
    cases h_op : evalOperandToSlot callerLocalsTys locals mem
        (fun srcTy => MirTy.beq srcTy paramTy) (.constant c) with
    | error _ => rw [h_op] at h; cases h
    | ok res =>
      rw [h_op] at h
      cases res with | mk srcTy rest =>
      cases rest with | mk optVal rest2 =>
      cases rest2 with | mk locals₁ mem₁ =>
      dsimp only at h
      let ⟨h_inv₁, h_slot₁, h_m₁⟩ := evalOperandToSlot_slotsMatchTys h_inv h_op
      cases h_beq : MirTy.beq srcTy paramTy with
      | false => rw [h_beq] at h; cases h
      | true =>
        rw [h_beq] at h; dsimp only [Bool.not, ite_false] at h
        cases optVal with
        | none => cases h
        | some v' =>
          injection h with h_eq; injection h_eq with hv hr1
          injection hr1 with hl hm; subst hv; subst hl; subst hm
          rw [MirTy.eq_of_beq h_beq] at h_slot₁
          exact ⟨h_inv₁, h_slot₁, h_m₁⟩
  | copy place =>
    dsimp only at h
    cases h_hm : hasMove with
    | false =>
      rw [h_hm] at h
      simp only [Bool.false_and] at h
      rw [ite_eq_right (by decide)] at h
      cases h_op : evalOperandToSlot callerLocalsTys locals mem
          (fun srcTy => MirTy.beq srcTy paramTy) (.copy place) with
      | error _ => rw [h_op] at h; cases h
      | ok res =>
        rw [h_op] at h
        cases res with | mk srcTy rest =>
        cases rest with | mk optVal rest2 =>
        cases rest2 with | mk locals₁ mem₁ =>
        dsimp only at h
        let ⟨h_inv₁, h_slot₁, h_m₁⟩ := evalOperandToSlot_slotsMatchTys h_inv h_op
        cases h_beq : MirTy.beq srcTy paramTy with
        | false => rw [h_beq] at h; cases h
        | true =>
          rw [h_beq] at h; rw [ite_eq_right (by decide)] at h
          cases optVal with
          | none => cases h
          | some v' =>
            injection h with h_eq; injection h_eq with hv hr1
            injection hr1 with hl hm; subst hv; subst hl; subst hm
            rw [MirTy.eq_of_beq h_beq] at h_slot₁
            exact ⟨h_inv₁, h_slot₁, h_m₁⟩
    | true =>
      cases h_gl : MirSemantics.getElem? locals place.localId with
      | none =>
        rw [h_hm, h_gl] at h
        simp only [Bool.true_and] at h
        rw [ite_eq_right (by decide)] at h
        cases h_op : evalOperandToSlot callerLocalsTys locals mem
            (fun srcTy => MirTy.beq srcTy paramTy) (.copy place) with
        | error _ => rw [h_op] at h; cases h
        | ok res =>
          rw [h_op] at h
          cases res with | mk srcTy rest =>
          cases rest with | mk optVal rest2 =>
          cases rest2 with | mk locals₁ mem₁ =>
          dsimp only at h
          let ⟨h_inv₁, h_slot₁, h_m₁⟩ := evalOperandToSlot_slotsMatchTys h_inv h_op
          cases h_beq : MirTy.beq srcTy paramTy with
          | false => rw [h_beq] at h; cases h
          | true =>
            rw [h_beq] at h; rw [ite_eq_right (by decide)] at h
            cases optVal with
            | none => cases h
            | some v' =>
              injection h with h_eq; injection h_eq with hv hr1
              injection hr1 with hl hm; subst hv; subst hl; subst hm
              rw [MirTy.eq_of_beq h_beq] at h_slot₁
              exact ⟨h_inv₁, h_slot₁, h_m₁⟩
      | some sl =>
        cases sl with
        | indirect _ => rw [h_hm, h_gl] at h; cases h
        | dead | immediate _ | partialTuple _ =>
          rw [h_hm, h_gl] at h
          simp only [Bool.true_and] at h
          rw [ite_eq_right (by decide)] at h
          cases h_op : evalOperandToSlot callerLocalsTys locals mem
              (fun srcTy => MirTy.beq srcTy paramTy) (.copy place) with
          | error _ => rw [h_op] at h; cases h
          | ok res =>
            rw [h_op] at h
            cases res with | mk srcTy rest =>
            cases rest with | mk optVal rest2 =>
            cases rest2 with | mk locals₁ mem₁ =>
            dsimp only at h
            let ⟨h_inv₁, h_slot₁, h_m₁⟩ := evalOperandToSlot_slotsMatchTys h_inv h_op
            cases h_beq : MirTy.beq srcTy paramTy with
            | false => rw [h_beq] at h; cases h
            | true =>
              rw [h_beq] at h; rw [ite_eq_right (by decide)] at h
              cases optVal with
              | none => cases h
              | some v' =>
                injection h with h_eq; injection h_eq with hv hr1
                injection hr1 with hl hm; subst hv; subst hl; subst hm
                rw [MirTy.eq_of_beq h_beq] at h_slot₁
                exact ⟨h_inv₁, h_slot₁, h_m₁⟩
  | move place =>
    dsimp only at h
    cases h_gl : MirSemantics.getElem? locals place.localId with
    | none =>
      rw [h_gl] at h
      dsimp only at h
      rw [ite_eq_right (by decide)] at h
      cases h_op : evalOperandToSlot callerLocalsTys locals mem
          (fun srcTy => MirTy.beq srcTy paramTy) (.move place) with
      | error _ => rw [h_op] at h; cases h
      | ok res =>
        rw [h_op] at h
        cases res with | mk srcTy rest =>
        cases rest with | mk optVal rest2 =>
        cases rest2 with | mk locals₁ mem₁ =>
        dsimp only at h
        let ⟨h_inv₁, h_slot₁, h_m₁⟩ := evalOperandToSlot_slotsMatchTys h_inv h_op
        cases h_beq : MirTy.beq srcTy paramTy with
        | false => rw [h_beq] at h; cases h
        | true =>
          rw [h_beq] at h; rw [ite_eq_right (by decide)] at h
          cases optVal with
          | none => cases h
          | some v' =>
            injection h with h_eq; injection h_eq with hv hr1
            injection hr1 with hl hm; subst hv; subst hl; subst hm
            rw [MirTy.eq_of_beq h_beq] at h_slot₁
            exact ⟨h_inv₁, h_slot₁, h_m₁⟩
    | some sl =>
      cases sl with
      | indirect _ => rw [h_gl] at h; cases h
      | dead | immediate _ | partialTuple _ =>
        rw [h_gl] at h
        dsimp only at h
        rw [ite_eq_right (by decide)] at h
        cases h_op : evalOperandToSlot callerLocalsTys locals mem
            (fun srcTy => MirTy.beq srcTy paramTy) (.move place) with
        | error _ => rw [h_op] at h; cases h
        | ok res =>
          rw [h_op] at h
          cases res with | mk srcTy rest =>
          cases rest with | mk optVal rest2 =>
          cases rest2 with | mk locals₁ mem₁ =>
          dsimp only at h
          let ⟨h_inv₁, h_slot₁, h_m₁⟩ := evalOperandToSlot_slotsMatchTys h_inv h_op
          cases h_beq : MirTy.beq srcTy paramTy with
          | false => rw [h_beq] at h; cases h
          | true =>
            rw [h_beq] at h; rw [ite_eq_right (by decide)] at h
            cases optVal with
            | none => cases h
            | some v' =>
              injection h with h_eq; injection h_eq with hv hr1
              injection hr1 with hl hm; subst hv; subst hl; subst hm
              rw [MirTy.eq_of_beq h_beq] at h_slot₁
              exact ⟨h_inv₁, h_slot₁, h_m₁⟩

private theorem evalCallArgs_slotsMatchTys {callerLocalsTys : List MirTy} :
    ∀ {locals locals' : List LocalSlot} {mem mem' : MemoryState}
      {hasMove : Bool} {args : List Operand} {paramTys : List MirTy}
      {vs : List Val},
      SlotsMatchTys callerLocalsTys locals →
      evalCallArgs callerLocalsTys locals mem hasMove args paramTys =
        .ok (vs, locals', mem') →
      SlotsMatchTys callerLocalsTys locals' ∧
        checkArgsMatch vs paramTys = true ∧ mem' = mem
  | _, _, _, _, _, [], [], _, h_inv, h => by
    injection h with h_eq; injection h_eq with hv hr; injection hr with hl hm
    subst hv; subst hl; subst hm; exact ⟨h_inv, rfl, rfl⟩
  | _, _, _, _, _, [], _ :: _, _, _, h => by cases h
  | _, _, _, _, _, _ :: _, [], _, _, h => by cases h
  | locals, locals', mem, mem', hasMove, op :: restArgs, pTy :: restParams, vs,
      h_inv, h => by
    dsimp only [evalCallArgs] at h
    cases h1 : evalCallArg callerLocalsTys locals mem hasMove op pTy with
    | error _ => rw [h1] at h; cases h
    | ok res1 =>
      rw [h1] at h
      cases res1 with | mk v rest1 =>
      cases rest1 with | mk l1 m1 =>
      dsimp only at h
      cases h2 : evalCallArgs callerLocalsTys l1 m1 hasMove restArgs restParams with
      | error _ => rw [h2] at h; cases h
      | ok res2 =>
        rw [h2] at h
        cases res2 with | mk vs2 rest2 =>
        cases rest2 with | mk l2 m2 =>
        injection h with h_eq; injection h_eq with hv hr; injection hr with hl hm
        subst hv; subst hl; subst hm
        let ⟨h_inv1, h_cv1, h_m1⟩ := evalCallArg_slotsMatchTys h_inv h1
        let ⟨h_inv2, h_am2, h_m2⟩ := evalCallArgs_slotsMatchTys h_inv1 h2
        refine ⟨h_inv2, ?_, h_m2.trans h_m1⟩
        dsimp only [checkArgsMatch]
        rw [h_cv1, h_am2]; rfl

private theorem simulationInv_head_aux {rp : RefProg} {p : Program}
    {retPlace : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance}
    {fs : List FrameState}
    {rfsRev : List (Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)}
    (h_fsim : FramesSimInv rp p retPlace fs rfsRev) :
    ∃ f callers body rbody,
      fs = f :: callers ∧
      activeFrameBody p f = some body ∧
      activeRefFrameBody rp f = some rbody :=
  match h_fsim with
  | @FramesSimInv.root _ _ _ f _ _ h_sro _ _ h_fs => by
    let ⟨body, rbody, _, h_bs, h_rbs, _⟩ := h_fs
    refine ⟨f, [], body, rbody, rfl, ?_, ?_⟩
    · dsimp only [activeFrameBody]; rw [h_sro]; exact h_bs
    · dsimp only [activeRefFrameBody]; rw [h_sro]; exact h_rbs
  | @FramesSimInv.push _ _ _ callee caller rest _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h_cfs => by
    let ⟨body, rbody, _, _, h_act_b, h_act_rb, _⟩ := h_cfs
    exact ⟨callee, caller :: rest, body, rbody, rfl, h_act_b, h_act_rb⟩

theorem simulationInv_head {rp : RefProg} {p : Program} {s : State}
    {rs : RefState} (h_sim : SimulationInv rp p s rs) :
    ∃ f callers body rbody,
      s.frames = f :: callers ∧
      activeFrameBody p f = some body ∧
      activeRefFrameBody rp f = some rbody := by
  let ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, h_fsim⟩ := h_sim
  exact simulationInv_head_aux h_fsim

private theorem getElem?_lt_len {α : Type} :
    ∀ {xs : List α} {i : Nat} {x : α},
      MirSemantics.getElem? xs i = some x → i < xs.length
  | [], _, _, h => by cases h
  | _ :: _, 0, _, _ => Nat.zero_lt_succ _
  | _ :: rest, i + 1, _, h => Nat.succ_lt_succ (getElem?_lt_len h)

private theorem updateCacheLoop_self_of_true :
    ∀ (cache : List Bool) (id idx : Nat),
      MirSemantics.getElem? cache id = some true →
      updateCacheLoop (fun i => Nat.beq i (idx + id)) idx cache = cache
  | [], _, _, h => by cases h
  | b :: bs, 0, idx, h => by
    injection h with hb; subst hb
    dsimp only [updateCacheLoop]
    rw [Nat.add_zero, Nat.beq_refl, Bool.true_or]
    have h_f : ∀ i, idx + 1 ≤ i → Nat.beq i idx = false := by
      intro i h_le
      cases h_eq : Nat.beq i idx with
      | false => rfl
      | true =>
        exact False.elim (Nat.lt_irrefl idx
          (Nat.lt_of_lt_of_le (Nat.lt_succ_self idx) (Nat.eq_of_beq_eq_true h_eq ▸ h_le)))
    rw [updateCacheLoop_false _ (idx + 1) bs h_f]
  | b :: bs, id + 1, idx, h => by
    dsimp only [updateCacheLoop]
    have h_ne : Nat.beq idx (idx + (id + 1)) = false := by
      cases h_eq : Nat.beq idx (idx + (id + 1)) with
      | false => rfl
      | true =>
        exact False.elim (Nat.ne_of_lt (Nat.lt_add_of_pos_right (Nat.succ_pos id))
          (Nat.eq_of_beq_eq_true h_eq))
    rw [h_ne, Bool.or_false]
    have ih := updateCacheLoop_self_of_true bs id (idx + 1) h
    have h_assoc : idx + 1 + id = idx + (id + 1) := by
      rw [Nat.add_assoc, Nat.add_comm 1 id]
    rw [h_assoc] at ih
    rw [ih]

private theorem sameDepth_step_preserves_aux {rp : RefProg} {p : Program}
    {s : State} {rs : RefState} {body : Body} {rbody : RefBody}
    {f f' : FrameState} {callers : List FrameState} {cm' : CallerMemory}
    {rframes : Array (Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)}
    {retTy : MirTy}
    {mem : Miri.Memory.MemoryState Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree Unit}
    {ctrl : Miri.Interpreter.TerminatorMachine.Control Unit}
    {topRel? : Option Nat}
    {fs : List FrameState}
    {rfsRev : List (Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)}
    (h_dec : decodeProg rp = some p)
    (h_smem : s.mem = entryMemory)
    (h_ert : entryRetTy? p = some retTy)
    (h_rty : rs.retTy = retTy)
    (h_init : refInitMemoryAndRetPlace rp.types retTy = .ok (mem, rs.retPlace))
    (h_ctrl : RefControlValid ctrl)
    (h_tr : refTopRelevanceValid rframes.size topRel?)
    (h_miri : rs.miri = mkRefMiriStackState rframes topRel? mem ctrl s.callerMem)
    (h_fsim : FramesSimInv rp p rs.retPlace fs rfsRev)
    (h_body : activeFrameBody p f = some body)
    (h_rbody : activeRefFrameBody rp f = some rbody)
    (h_def : f'.defId = f.defId)
    (h_sro : f'.sysrootOp? = f.sysrootOp?)
    (h_rdst : f'.retDst? = f.retDst?)
    (h_rtgt : f'.retTarget? = f.retTarget?)
    (h_inv' : SlotsMatchTys body.locals f'.locals)
    (h_pc' : FramePcInBounds body f') :
    fs = f :: callers →
    rframes.toList.reverse = rfsRev →
    let ctrl' := nextRefControlForStep body f rs.miri.machine.user.control
    let prevTopRel? :=
      match rs.miri.machine.threads.activeThread? with
      | some th => th.topUserRelevantFrame
      | none => none
    ∃ newFrames newTopRel?,
      liftStackStep rp body f rs.miri.stack.frames prevTopRel? (f' :: callers) =
        some (newFrames, newTopRel?) ∧
      SimulationInv rp p { frames := f' :: callers, callerMem := cm', mem := s.mem } {
        rs with
        miri := mkRefMiriStackState newFrames newTopRel?
          rs.miri.machine.memory ctrl' cm'
        stepsExecuted := rs.stepsExecuted + 1
      } :=
  match h_fsim with
  | @FramesSimInv.root _ _ _ f0 rf h_defId h_f_sro h_f_rdst h_f_rtgt h_fs => by
    intro h_fs_eq h_rev_eq
    injection h_fs_eq with h_f0_eq h_c_eq
    subst f0; subst h_c_eq
    have h_ctrl_eq : rs.miri.machine.user.control = ctrl := by rw [h_miri]; rfl
    have h_mem_eq : rs.miri.machine.memory = mem := by rw [h_miri]; rfl
    have h_sf_eq : rs.miri.stack.frames = rframes := by rw [h_miri]; rfl
    have h_tr_eq :
        (match rs.miri.machine.threads.activeThread? with
         | some th => th.topUserRelevantFrame
         | none => none) = topRel? := by
      rw [h_miri]; rfl
    let ⟨body₀, rbody₀, cache, h_b0, h_rb0, h_bdec, h_arg, h_sa, h_dv, h_cv,
      h_act, h_calls, h_all_static, h_supp, h_inv₀, _, h_crep, h_rf⟩ := h_fs
    have h_ab : activeFrameBody p f = some body₀ := by
      dsimp only [activeFrameBody]; rw [h_f_sro]; exact h_b0
    have h_arb : activeRefFrameBody rp f = some rbody₀ := by
      dsimp only [activeRefFrameBody]; rw [h_f_sro]; exact h_rb0
    rw [h_body] at h_ab; injection h_ab with hb_eq; subst hb_eq
    rw [h_rbody] at h_arb; injection h_arb with hrb_eq; subst hrb_eq
    have h_c_len : cache.length = body.locals.length := by
      rw [h_crep, List.length_replicate]
    have h_upd := updateMiriLocalsLoop_liftLocalsCached rp.types
      (stepTouchesLocal body f) 0 body.locals f'.locals f.locals cache
      (SlotsMatchTys.length_eq h_inv').symm
      ((SlotsMatchTys.length_eq h_inv').trans (SlotsMatchTys.length_eq h_inv₀).symm)
      ((SlotsMatchTys.length_eq h_inv₀).trans h_c_len.symm)
    rw [h_crep, updateCacheLoop_replicate_true] at h_upd
    have h_rf_arr := array_eq_singleton_of_toList_reverse h_rev_eq
    have h_rf_loc : rf.locals.toList = liftLocalsCached rp.types body.locals f.locals cache := by
      rw [h_rf]; rfl
    rw [h_crep] at h_rf_loc
    rw [h_sf_eq, h_rf_arr, h_tr_eq, h_ctrl_eq, h_mem_eq]
    dsimp only [liftStackStep]
    rw [show Nat.beq ((Array.mk [rf]).size) 1 = true from rfl, ite_eq_left rfl,
      show (Array.mk [rf])[0]? = some rf from rfl]
    dsimp only
    rw [h_rf_loc, h_upd]
    have h_rf' :
        { rf with
          locals := Array.mk (liftLocalsCached rp.types body.locals f'.locals
            (List.replicate body.locals.length true))
          location := .mir ⟨f'.blockIdx, f'.stmtIdx⟩ } =
        mkRefMiriFrame rp.types f'.defId rbody f'.blockIdx f'.stmtIdx
          (liftLocalsCached rp.types body.locals f'.locals
            (List.replicate body.locals.length true)) rs.retPlace := by
      rw [h_rf, h_def]; rfl
    refine ⟨_, topRel?, rfl, Array.mk [_], retTy, mem, nextRefControlForStep body f ctrl,
      topRel?, h_dec, rfl, h_smem, h_ert, h_rty, h_init,
      refControlValid_nextRefControlForStep h_ctrl, ?_, rfl, ?_⟩
    · have h_sz1 : rframes.size = 1 := by rw [h_rf_arr]; rfl
      rw [h_sz1] at h_tr; exact h_tr
    · rw [h_rf']
      refine FramesSimInv.root (h_def.trans h_defId) (h_sro.trans h_f_sro)
        (h_rdst.trans h_f_rdst) (h_rtgt.trans h_f_rtgt)
        ⟨body, rbody, List.replicate body.locals.length true,
          (h_def.symm ▸ h_b0), (h_def.symm ▸ h_rb0), h_bdec, h_arg, h_sa,
          h_dv, h_cv, h_act, h_calls, h_all_static, h_supp, h_inv', h_pc', rfl, rfl⟩
  | @FramesSimInv.push _ _ _ callee0 caller rest rf rcaller rrest callerBody calleeBody dst dstTy cRetTy
      h_fsim_callers h_cb h_calleeb h_frdst h_dst_emp h_dst_ty h_dst_supp
      h_cret_ty h_beq h_tgt_lt h_rc_cached h_cfs => by
    intro h_fs_eq h_rev_eq
    injection h_fs_eq with h_f0_eq h_c_eq
    subst callee0; subst h_c_eq
    have h_ctrl_eq : rs.miri.machine.user.control = ctrl := by rw [h_miri]; rfl
    have h_mem_eq : rs.miri.machine.memory = mem := by rw [h_miri]; rfl
    have h_sf_eq : rs.miri.stack.frames = rframes := by rw [h_miri]; rfl
    have h_tr_eq :
        (match rs.miri.machine.threads.activeThread? with
         | some th => th.topUserRelevantFrame
         | none => none) = topRel? := by
      rw [h_miri]; rfl
    let ⟨body₀, rbody₀, cache, fnTag, h_act_b0, h_act_rb0, h_bdec, h_fnTag,
      h_crate, h_sys, h_arg, h_sa, h_dv, h_cv, h_act, h_asg, h_calls, h_all_static,
      h_supp, h_inv₀, _, h_c_len, h_rf⟩ := h_cfs
    rw [h_body] at h_act_b0; injection h_act_b0 with hb_eq; subst hb_eq
    rw [h_rbody] at h_act_rb0; injection h_act_rb0 with hrb_eq; subst hrb_eq
    rw [h_body] at h_calleeb; injection h_calleeb with hcb_eq; subst hcb_eq
    have h_fb' : activeFrameBody p f' = activeFrameBody p f := by
      dsimp only [activeFrameBody]; rw [h_sro, h_def]
    have h_frb' : activeRefFrameBody rp f' = activeRefFrameBody rp f := by
      dsimp only [activeRefFrameBody]; rw [h_sro, h_def]
    have h_upd := updateMiriLocalsLoop_liftLocalsCached rp.types
      (stepTouchesLocal body f) 0 body.locals f'.locals f.locals cache
      (SlotsMatchTys.length_eq h_inv').symm
      ((SlotsMatchTys.length_eq h_inv').trans (SlotsMatchTys.length_eq h_inv₀).symm)
      ((SlotsMatchTys.length_eq h_inv₀).trans h_c_len.symm)
    have h_rf_arr := array_eq_push_of_toList_reverse h_rev_eq
    have h_len_callers : (rcaller :: rrest).length = (caller :: rest).length :=
      framesSimInv_length_eq h_fsim_callers
    have h_sz_rframes : rframes.size = rest.length + 2 := by
      rw [h_rf_arr, Array.size_push]
      change (rcaller :: rrest).reverse.length + 1 = rest.length + 2
      rw [List.length_reverse]
      change rrest.length + 1 + 1 = rest.length + 2
      rw [Nat.succ.inj h_len_callers]
    have h_newlen : Nat.beq (rest.length + 2) rframes.size = true := by
      rw [h_sz_rframes]; exact Nat.beq_refl _
    have h_back : rframes.back? = some rf := by
      rw [h_rf_arr]; exact array_back?_push _ _
    have h_pop : rframes.pop = ⟨(rcaller :: rrest).reverse⟩ := by
      rw [h_rf_arr]; exact array_pop_push_eq _ _
    have h_rf_loc : rf.locals.toList = liftLocalsCached rp.types body.locals f.locals cache := by
      rw [h_rf]; rfl
    rw [h_sf_eq, h_tr_eq, h_ctrl_eq, h_mem_eq]
    dsimp only [liftStackStep]
    rw [h_newlen, ite_eq_left rfl, h_back]
    dsimp only
    rw [h_rf_loc, h_upd, h_pop]
    let newCache := updateCacheLoop (stepTouchesLocal body f) 0 cache
    let rf' := {
      rf with
      locals := Array.mk (liftLocalsCached rp.types body.locals f'.locals newCache)
      location := .mir ⟨f'.blockIdx, f'.stmtIdx⟩
    }
    have h_rf'_eq :
        rf' = mkRefMiriCallFrame rp.types fnTag rbody f'.blockIdx f'.stmtIdx
          (liftLocalsCached rp.types body.locals f'.locals newCache)
          rest.length dst.localId dstTy f'.retTarget? := by
      dsimp only [rf']; rw [h_rf, h_rtgt]; rfl
    have h_new_sz : ((⟨(rcaller :: rrest).reverse⟩ : Array _).push rf').size = rframes.size := by
      rw [Array.size_push]
      change (rcaller :: rrest).reverse.length + 1 = rframes.size
      rw [List.length_reverse, h_sz_rframes]
      change rrest.length + 1 + 1 = rest.length + 2
      rw [Nat.succ.inj h_len_callers]
    have h_rev_new :
        ((⟨(rcaller :: rrest).reverse⟩ : Array _).push rf').toList.reverse =
          rf' :: rcaller :: rrest := by
      simp [Array.push, List.concat_eq_append]
    refine ⟨_, topRel?, rfl, _, retTy, mem, nextRefControlForStep body f ctrl, topRel?,
      h_dec, rfl, h_smem, h_ert, h_rty, h_init,
      refControlValid_nextRefControlForStep h_ctrl, ?_, rfl, ?_⟩
    · rw [h_new_sz]; exact h_tr
    · rw [h_rev_new]
      refine FramesSimInv.push h_fsim_callers h_cb ?_ (h_rdst.trans h_frdst)
        h_dst_emp h_dst_ty h_dst_supp h_cret_ty h_beq ?_ h_rc_cached ?_
      · exact h_fb'.trans h_body
      · rw [h_rtgt]; exact h_tgt_lt
      · refine ⟨body, rbody, newCache, fnTag, ?_, ?_, h_bdec, ?_, ?_, ?_,
          h_arg, h_sa, h_dv, h_cv, h_act, h_asg, h_calls, h_all_static, h_supp, h_inv',
          h_pc', (updateCacheLoop_length _ 0 cache).trans h_c_len, h_rf'_eq⟩
        · exact h_fb'.trans h_body
        · exact h_frb'.trans h_rbody
        · rw [h_sro, h_def]; exact h_fnTag
        · rw [h_sro, h_def]; exact h_crate
        · rw [h_sro, h_def]; exact h_sys

private theorem sameDepth_step_preserves {rp : RefProg} {p : Program}
    {s : State} {rs : RefState} {body : Body} {rbody : RefBody}
    {f f' : FrameState} {callers : List FrameState} {cm' : CallerMemory}
    (h_dec : decodeProg rp = some p)
    (h_sim : SimulationInv rp p s rs)
    (hs : s.frames = f :: callers)
    (h_body : activeFrameBody p f = some body)
    (h_rbody : activeRefFrameBody rp f = some rbody)
    (h_def : f'.defId = f.defId)
    (h_sro : f'.sysrootOp? = f.sysrootOp?)
    (h_rdst : f'.retDst? = f.retDst?)
    (h_rtgt : f'.retTarget? = f.retTarget?)
    (h_inv' : SlotsMatchTys body.locals f'.locals)
    (h_pc' : FramePcInBounds body f') :
    let ctrl' := nextRefControlForStep body f rs.miri.machine.user.control
    let prevTopRel? :=
      match rs.miri.machine.threads.activeThread? with
      | some th => th.topUserRelevantFrame
      | none => none
    ∃ newFrames newTopRel?,
      liftStackStep rp body f rs.miri.stack.frames prevTopRel? (f' :: callers) =
        some (newFrames, newTopRel?) ∧
      SimulationInv rp p { frames := f' :: callers, callerMem := cm', mem := s.mem } {
        rs with
        miri := mkRefMiriStackState newFrames newTopRel?
          rs.miri.machine.memory ctrl' cm'
        stepsExecuted := rs.stepsExecuted + 1
      } := by
  let ⟨_, _, _, _, _, _, _, h_smem, h_ert, h_rty,
    h_init, h_ctrl, h_tr, h_miri, h_fsim⟩ := h_sim
  exact sameDepth_step_preserves_aux h_dec h_smem h_ert h_rty h_init h_ctrl h_tr h_miri
    h_fsim h_body h_rbody h_def h_sro h_rdst h_rtgt h_inv' h_pc' hs rfl

private theorem callTouchesCallerLocal_dst {body : Body} {bb : BasicBlock}
    {f : FrameState} {dst : Place}
    (h_bb : MirSemantics.getElem? body.basicBlocks f.blockIdx = some bb)
    (h_call : (∃ callee args tgt uw, bb.terminator = .call callee args dst tgt uw) ∨
      (∃ op args tgt uw, bb.terminator = .sysrootCall op args dst tgt uw)) :
    callTouchesCallerLocal body f dst.localId = true := by
  dsimp only [callTouchesCallerLocal]
  rw [h_bb]; dsimp only
  cases h_call with
  | inl h1 =>
    cases h1 with | intro _ h1 => cases h1 with | intro _ h1 =>
    cases h1 with | intro _ h1 => cases h1 with | intro _ h_t =>
    rw [h_t]; simp [Nat.beq_refl]
  | inr h2 =>
    cases h2 with | intro _ h2 => cases h2 with | intro _ h2 =>
    cases h2 with | intro _ h2 => cases h2 with | intro _ h_t =>
    rw [h_t]; simp [Nat.beq_refl]

private theorem evalCallTerminator_args_elim
    {body calleeBody : Body} {bb : BasicBlock} {f : FrameState}
    {callers : List FrameState} {mem : MemoryState} {callerMem : CallerMemory}
    {calleeDefId : DefId} {sysrootOp? : Option SysrootNumOp}
    {args : List Operand} {dst : Place} {target : Option BasicBlockId}
    {unwind : UnwindAction} {s' : State}
    (h_chk : (!callTargetAdmitted body bb calleeBody args dst target unwind ||
        calleeBody.basicBlocks.isEmpty ||
        !storageAnnotationsInBounds calleeBody ||
        !discriminantTypesValid calleeBody ||
        !castTypesValid calleeBody ||
        !assignTypesValid calleeBody ||
        !calleeBody.locals.all isSupportedScalarOrUnitTy) = false)
    (h_ec : evalCallTerminator body bb f callers mem callerMem calleeDefId
      sysrootOp? calleeBody args dst target unwind = StepResult.step s') :
    ∃ argVals callerLocals' mem',
      evalCallArgs body.locals f.locals mem
          (args.any (fun a => match a with | .move _ => true | _ => false))
          args ((calleeBody.locals.drop 1).take calleeBody.argumentCount) =
        Except.ok (argVals, callerLocals', mem') ∧
      (show Trusted.MirSemantics.StepResult State TerminalOut from
        match MirSemantics.getElem? callerLocals' dst.localId with
        | none => .fault .unsupported
        | some .dead => .fault .undefined
        | some (.indirect _) => .fault .unsupported
        | some (.partialTuple _) => .fault .unsupported
        | some (.immediate _) =>
          .step {
            frames := {
              defId := calleeDefId
              blockIdx := 0
              stmtIdx := 0
              locals := initLocalsLoop calleeBody argVals 0 calleeBody.locals
              sysrootOp? := sysrootOp?
              retDst? := some dst
              retTarget? := target
            } :: { f with locals := callerLocals' } :: callers
            callerMem := callerMem
            mem := mem'
          }) = .step s' := by
  have h_unfold :
      (show Trusted.MirSemantics.StepResult State TerminalOut from
        match evalCallArgs body.locals f.locals mem
            (args.any (fun a => match a with | .move _ => true | _ => false))
            args ((calleeBody.locals.drop 1).take calleeBody.argumentCount) with
        | .error k => .fault k
        | .ok (argVals, callerLocals', mem') =>
          match MirSemantics.getElem? callerLocals' dst.localId with
          | none => .fault .unsupported
          | some .dead => .fault .undefined
          | some (.indirect _) => .fault .unsupported
          | some (.partialTuple _) => .fault .unsupported
          | some (.immediate _) =>
            .step {
              frames := {
                defId := calleeDefId
                blockIdx := 0
                stmtIdx := 0
                locals := initLocalsLoop calleeBody argVals 0 calleeBody.locals
                sysrootOp? := sysrootOp?
                retDst? := some dst
                retTarget? := target
              } :: { f with locals := callerLocals' } :: callers
              callerMem := callerMem
              mem := mem'
            }) = .step s' := by
    have h0 := h_ec
    unfold evalCallTerminator at h0
    rw [h_chk, ite_eq_right (by decide)] at h0
    exact h0
  cases h_eca : evalCallArgs body.locals f.locals mem
      (args.any (fun a => match a with | .move _ => true | _ => false))
      args ((calleeBody.locals.drop 1).take calleeBody.argumentCount) with
  | error k => rw [h_eca] at h_unfold; cases h_unfold
  | ok triple =>
    cases triple with | mk argVals pair =>
    cases pair with | mk callerLocals' mem' =>
    rw [h_eca] at h_unfold
    exact ⟨argVals, callerLocals', mem', rfl, h_unfold⟩

private theorem evalCallTerminator_step_preserves_aux {rp : RefProg} {p : Program}
    {s s' : State} {rs : RefState} {body : Body} {rbody calleeRbody : RefBody}
    {f : FrameState} {callers : List FrameState} {bb : BasicBlock}
    {calleeDefId : DefId} {sysrootOp? : Option SysrootNumOp}
    {calleeBody : Body} {args : List Operand} {dst : Place}
    {target : Option BasicBlockId} {unwind : UnwindAction}
    {rframes : Array (Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)}
    {retTy : MirTy}
    {mem : Miri.Memory.MemoryState Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree Unit}
    {ctrl : Miri.Interpreter.TerminatorMachine.Control Unit}
    {topRel? : Option Nat}
    {fs : List FrameState}
    {rfsRev : List (Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)}
    (h_dec : decodeProg rp = some p)
    (h_smem : s.mem = entryMemory)
    (h_ert : entryRetTy? p = some retTy)
    (h_rty : rs.retTy = retTy)
    (h_init : refInitMemoryAndRetPlace rp.types retTy = .ok (mem, rs.retPlace))
    (h_ctrl : RefControlValid ctrl)
    (_h_tr : refTopRelevanceValid rframes.size topRel?)
    (h_miri : rs.miri = mkRefMiriStackState rframes topRel? mem ctrl s.callerMem)
    (h_fsim : FramesSimInv rp p rs.retPlace fs rfsRev)
    (h_body : activeFrameBody p f = some body)
    (h_rbody : activeRefFrameBody rp f = some rbody)
    (h_bb : MirSemantics.getElem? body.basicBlocks f.blockIdx = some bb)
    (h_call : (∃ callee tgt uw, bb.terminator = .call callee args dst tgt uw ∧
        calleeDefId = callee ∧ sysrootOp? = none) ∨
      (∃ op tgt uw, bb.terminator = .sysrootCall op args dst tgt uw ∧
        calleeDefId = 0 ∧ sysrootOp? = some op ∧
        calleeBody = sysrootNumBody op))
    (h_cbdec : decodeBody rp.types calleeRbody = some calleeBody)
    (h_res_crate : sysrootOp? = none →
      refResolveCalleeBody rp (fnTagForCrate calleeDefId) =
        some (calleeRbody, calleeBody.locals))
    (h_res_sys : ∀ op, sysrootOp? = some op →
      refResolveCalleeBody rp (fnTagForSysroot op) =
        some (calleeRbody, calleeBody.locals))
    (h_crate : sysrootOp? = none →
      MirSemantics.getElem? p.bodies calleeDefId = some calleeBody)
    (h_crate_rb : sysrootOp? = none →
      MirSemantics.getElem? rp.bodies calleeDefId = some calleeRbody)
    (h_sys : ∀ op, sysrootOp? = some op → calleeDefId = 0)
    (h_cb_calls : callsAdmitted p calleeBody = true)
    (h_cb_all_static : allCallBodiesStaticAdmitted p calleeBody = true)
    (h_cb_act : assertConditionTypesValid calleeBody = true)
    (h_ec : evalCallTerminator body bb f callers s.mem s.callerMem calleeDefId
      sysrootOp? calleeBody args dst target unwind = .step s') :
    fs = f :: callers →
    rframes.toList.reverse = rfsRev →
    let ctrl' := nextRefControlForStep body f rs.miri.machine.user.control
    let prevTopRel? :=
      match rs.miri.machine.threads.activeThread? with
      | some th => th.topUserRelevantFrame
      | none => none
    ∃ newFrames newTopRel?,
      liftStackStep rp body f rs.miri.stack.frames prevTopRel? s'.frames =
        some (newFrames, newTopRel?) ∧
      SimulationInv rp p s' {
        rs with
        miri := mkRefMiriStackState newFrames newTopRel?
          rs.miri.machine.memory ctrl' s'.callerMem
        stepsExecuted := rs.stepsExecuted + 1
      } :=
  match h_fsim with
  | @FramesSimInv.root _ _ _ f0 rfCaller h_defId h_f_sro h_f_rdst h_f_rtgt h_fs => by
    intro h_fs_eq h_rev_eq
    injection h_fs_eq with h_f0_eq h_c_eq
    subst f0; subst h_c_eq
    have h_ctrl_eq : rs.miri.machine.user.control = ctrl := by rw [h_miri]; rfl
    have h_mem_eq : rs.miri.machine.memory = mem := by rw [h_miri]; rfl
    have h_sf_eq : rs.miri.stack.frames = rframes := by rw [h_miri]; rfl
    have h_tr_eq :
        (match rs.miri.machine.threads.activeThread? with
         | some th => th.topUserRelevantFrame
         | none => none) = topRel? := by
      rw [h_miri]; rfl
    have h_ec_orig := h_ec
    unfold evalCallTerminator at h_ec
    cases h_chk :
        (!callTargetAdmitted body bb calleeBody args dst target unwind ||
          calleeBody.basicBlocks.isEmpty ||
          !storageAnnotationsInBounds calleeBody ||
          !discriminantTypesValid calleeBody ||
          !castTypesValid calleeBody ||
          !assignTypesValid calleeBody ||
          !calleeBody.locals.all isSupportedScalarOrUnitTy) with
    | true => rw [h_chk] at h_ec; cases h_ec
    | false =>
      let ⟨argVals, callerLocals', mem', h_eca, h_ec⟩ :=
        evalCallTerminator_args_elim h_chk h_ec_orig
      simp only [Bool.or_eq_false_iff, Bool.not_eq_false'] at h_chk
      let ⟨⟨⟨⟨⟨⟨h_adm, h_emp⟩, h_csa⟩, h_cdv⟩, h_ccv⟩, h_casg⟩, h_csupp⟩ := h_chk
      cases h_gdst : MirSemantics.getElem? callerLocals' dst.localId with
      | none => rw [h_gdst] at h_ec; cases h_ec
      | some dstSl =>
        rw [h_gdst] at h_ec
        cases dstSl with
        | dead => cases h_ec
        | indirect _ => cases h_ec
        | partialTuple _ => cases h_ec
        | immediate _ =>
            injection h_ec with h_s'_eq
            subst h_s'_eq
            have h_cadm := h_adm
            dsimp only [callTargetAdmitted] at h_cadm
            simp only [Bool.and_eq_true] at h_cadm
            let ⟨⟨⟨⟨⟨⟨⟨_, h_tgt_ok⟩, h_dst_emp⟩, _⟩, _⟩, h_cblt⟩, h_tys⟩, _⟩ := h_cadm
            have h_tgt_lt :
                match target with
                | none => True
                | some tgt => Nat.blt tgt body.basicBlocks.length = true := by
              cases target with
              | none => exact True.intro
              | some _ => exact h_tgt_ok
            cases h_dl : MirSemantics.getElem? body.locals dst.localId with
            | none => rw [h_dl] at h_tys; cases h_tys
            | some dstTy =>
              rw [h_dl] at h_tys
              cases h_cl0 : MirSemantics.getElem? calleeBody.locals 0 with
              | none => rw [h_cl0] at h_tys; cases h_tys
              | some cRetTy =>
                rw [h_cl0] at h_tys
                dsimp only at h_tys
                rw [Bool.and_eq_true] at h_tys
                let ⟨h_dst_supp, h_dst_beq⟩ := h_tys
                have h_touch_dst :
                    callTouchesCallerLocal body f dst.localId = true := by
                  apply callTouchesCallerLocal_dst h_bb
                  cases h_call with
                  | inl h_c1 =>
                    cases h_c1 with | intro callee h_c1 => cases h_c1 with | intro tgt h_c1 =>
                    cases h_c1 with | intro uw h_c1 => exact Or.inl ⟨callee, args, tgt, uw, h_c1.1⟩
                  | inr h_c2 =>
                    cases h_c2 with | intro op h_c2 => cases h_c2 with | intro tgt h_c2 =>
                    cases h_c2 with | intro uw h_c2 => exact Or.inr ⟨op, args, tgt, uw, h_c2.1⟩
                have h_dl_lt : dst.localId < body.locals.length :=
                  getElem?_lt_len h_dl
                have h_chead :
                    calleeBody.locals[0]?.getD .unit = dstTy := by
                  cases h_l : calleeBody.locals with
                  | nil => rw [h_l] at h_cl0; cases h_cl0
                  | cons hd _ =>
                    rw [h_l] at h_cl0
                    injection h_cl0 with h_hd
                    subst h_hd
                    exact (MirTy.eq_of_beq h_dst_beq).symm
                let ⟨h_carg_dec, _, _, _, _⟩ := decodeBody_inv h_cbdec
                let fnTag :=
                  match sysrootOp? with
                  | some op => fnTagForSysroot op
                  | none => fnTagForCrate calleeDefId
                let calleeLocals :=
                  initLocalsLoop calleeBody argVals 0 calleeBody.locals
                let calleeFrame : FrameState := {
                  defId := calleeDefId
                  blockIdx := 0
                  stmtIdx := 0
                  locals := calleeLocals
                  sysrootOp? := sysrootOp?
                  retDst? := some dst
                  retTarget? := target
                }
                let calleeCache :=
                  calleeInitCacheLoop calleeRbody.argumentCount 0
                    calleeBody.locals
                let rfCallee := mkRefMiriCallFrame rp.types fnTag
                  calleeRbody 0 0
                  (liftLocalsCached rp.types calleeBody.locals
                    calleeLocals calleeCache)
                  rframes.size
                let ⟨body₀, rbody₀, cache, h_b0, h_rb0, h_bdec, h_arg, h_sa,
                  h_dv, h_cv, h_act, h_calls, h_all_static, h_supp, h_inv₀,
                  h_pc₀, h_crep, h_rf⟩ := h_fs
                have h_ab : activeFrameBody p f = some body₀ := by
                  dsimp only [activeFrameBody]; rw [h_f_sro]; exact h_b0
                have h_arb : activeRefFrameBody rp f = some rbody₀ := by
                  dsimp only [activeRefFrameBody]; rw [h_f_sro]; exact h_rb0
                rw [h_body] at h_ab; injection h_ab with hb_eq; subst hb_eq
                rw [h_rbody] at h_arb; injection h_arb with hrb_eq; subst hrb_eq
                let ⟨h_cl_inv, h_cargs, h_m_eq⟩ :=
                  evalCallArgs_slotsMatchTys h_inv₀ h_eca
                have h_callee_inv : SlotsMatchTys calleeBody.locals calleeLocals :=
                  initLocalsLoop_slotsMatchTys calleeBody argVals h_cargs
                have h_rf_arr := array_eq_singleton_of_toList_reverse h_rev_eq
                have h_sz1 : rframes.size = 1 := by rw [h_rf_arr]; rfl
                have h_c_len : cache.length = body.locals.length := by
                  rw [h_crep, List.length_replicate]
                have h_upd := updateMiriLocalsLoop_liftLocalsCached rp.types
                  (callTouchesCallerLocal body f) 0 body.locals
                  callerLocals' f.locals cache
                  (SlotsMatchTys.length_eq h_cl_inv).symm
                  ((SlotsMatchTys.length_eq h_cl_inv).trans
                    (SlotsMatchTys.length_eq h_inv₀).symm)
                  ((SlotsMatchTys.length_eq h_inv₀).trans h_c_len.symm)
                rw [h_crep, updateCacheLoop_replicate_true] at h_upd
                have h_rf_loc : rfCaller.locals.toList =
                    liftLocalsCached rp.types body.locals f.locals cache := by
                  rw [h_rf]; rfl
                rw [h_crep] at h_rf_loc
                let rfCaller' := {
                  rfCaller with
                  locals := Array.mk (liftLocalsCached rp.types body.locals
                    callerLocals' (List.replicate body.locals.length true))
                }
                let rfCallee' := mkRefMiriCallFrame rp.types fnTag
                  calleeRbody 0 0
                  (liftLocalsCached rp.types calleeBody.locals
                    calleeLocals calleeCache)
                  0 dst.localId dstTy target
                have h_rfCaller'_eq :
                    rfCaller' = mkRefMiriFrame rp.types f.defId rbody
                      f.blockIdx f.stmtIdx
                      (liftLocalsCached rp.types body.locals callerLocals'
                        (List.replicate body.locals.length true))
                      rs.retPlace := by
                  dsimp only [rfCaller']; rw [h_rf]; dsimp only [mkRefMiriFrame]
                have h_rc_cached : ∃ ls, rfCaller'.locals[dst.localId]? = some ls ∧
                    ls.layout.isSome = true := by
                  have h_get_t := getElem?_updateCacheLoop_eq_true
                    (callTouchesCallerLocal body f) 0 dst.localId
                    (List.replicate body.locals.length true)
                    (by rw [List.length_replicate]; exact h_dl_lt)
                    (by rw [Nat.zero_add]; exact h_touch_dst)
                  rw [updateCacheLoop_replicate_true] at h_get_t
                  dsimp only [rfCaller']
                  rw [array_getElem?_eq_mirGetElem?]
                  exact getElem?_liftLocalsCached_layout_isSome_of_true rp.types
                    body.locals callerLocals'
                    (List.replicate body.locals.length true) dst.localId
                    (SlotsMatchTys.length_eq h_cl_inv).symm
                    (by rw [List.length_replicate, SlotsMatchTys.length_eq h_cl_inv])
                    h_get_t
                rw [h_sf_eq, h_tr_eq, h_ctrl_eq, h_mem_eq]
                refine ⟨Array.mk [rfCaller', rfCallee'], some 1, ?_,
                  Array.mk [rfCaller', rfCallee'], retTy, mem,
                  nextRefControlForStep body f ctrl, some 1, h_dec, rfl,
                  h_m_eq.trans h_smem, h_ert, h_rty, h_init,
                  refControlValid_nextRefControlForStep h_ctrl,
                  ⟨Nat.zero_lt_succ _, rfl⟩, rfl, ?_⟩
                · rw [h_rf_arr]
                  dsimp only [liftStackStep]
                  rw [show Nat.beq (List.length ([] : List FrameState) + 2)
                      ((Array.mk [rfCaller]).size) = false from rfl, ite_eq_right (by decide),
                    show Nat.beq (List.length ([] : List FrameState) + 2)
                      ((Array.mk [rfCaller]).size + 1) = true from rfl, ite_eq_left rfl,
                    show (Array.mk [rfCaller]).back? = some rfCaller from rfl]
                  dsimp only
                  cases h_s : sysrootOp? with
                  | some op =>
                    dsimp only [rfCallee', fnTag]
                    rw [h_s]; dsimp only
                    rw [h_res_sys op h_s]
                    dsimp only; rw [h_chead, h_rf_loc, h_upd]; rfl
                  | none =>
                    dsimp only [rfCallee', fnTag]
                    rw [h_s]; dsimp only
                    rw [h_res_crate h_s]
                    dsimp only; rw [h_chead, h_rf_loc, h_upd]; rfl
                refine FramesSimInv.push
                  (FramesSimInv.root h_defId h_f_sro h_f_rdst h_f_rtgt
                    ⟨body, rbody, List.replicate body.locals.length true,
                      h_b0, h_rb0, h_bdec, h_arg, h_sa, h_dv, h_cv, h_act,
                      h_calls, h_all_static, h_supp, h_cl_inv, h_pc₀,
                      rfl, h_rfCaller'_eq⟩)
                  h_body ?_ rfl h_dst_emp h_dl h_dst_supp h_cl0 h_dst_beq
                  (by cases target with | none => exact True.intro | some _ => exact h_tgt_ok)
                  h_rc_cached ?_
                · dsimp only [activeFrameBody]
                  cases h_s : sysrootOp? with
                  | some op =>
                    have h_op_eq : calleeBody = sysrootNumBody op := by
                      cases h_call with
                      | inl h_c1 =>
                        cases h_c1 with | intro _ h_c1 => cases h_c1 with | intro _ h_c1 =>
                        cases h_c1 with | intro _ h_c1 =>
                        rw [h_s] at h_c1; cases h_c1.2.2
                      | inr h_c2 =>
                        cases h_c2 with | intro op' h_c2 => cases h_c2 with | intro _ h_c2 =>
                        cases h_c2 with | intro _ h_c2 =>
                        rw [h_s] at h_c2; injection h_c2.2.2.1 with ho; subst ho; exact h_c2.2.2.2
                    exact congrArg some h_op_eq.symm
                  | none => exact h_crate h_s
                · refine ⟨calleeBody, calleeRbody, calleeCache, fnTag, ?_, ?_,
                    h_cbdec, rfl, h_crate, h_sys, h_cblt, h_csa, h_cdv,
                    h_ccv, h_cb_act, h_casg, h_cb_calls, h_cb_all_static, h_csupp,
                    h_callee_inv, fun _ _ => Nat.zero_le _,
                    (calleeInitCacheLoop_length calleeRbody.argumentCount 0 calleeBody.locals), rfl⟩
                  · dsimp only [activeFrameBody]
                    cases h_s : sysrootOp? with
                    | some op =>
                      have h_op_eq : calleeBody = sysrootNumBody op := by
                        cases h_call with
                        | inl h_c1 =>
                          cases h_c1 with | intro _ h_c1 => cases h_c1 with | intro _ h_c1 =>
                          cases h_c1 with | intro _ h_c1 =>
                          rw [h_s] at h_c1; cases h_c1.2.2
                        | inr h_c2 =>
                          cases h_c2 with | intro op' h_c2 => cases h_c2 with | intro _ h_c2 =>
                          cases h_c2 with | intro _ h_c2 =>
                          rw [h_s] at h_c2; injection h_c2.2.2.1 with ho; subst ho; exact h_c2.2.2.2
                      exact congrArg some h_op_eq.symm
                    | none => exact h_crate h_s
                  · dsimp only [activeRefFrameBody]
                    cases h_s : sysrootOp? with
                    | some op =>
                      have h_res_s := h_res_sys op h_s
                      rw [refResolveCalleeBody_sysroot] at h_res_s
                      injection h_res_s with h_pr
                      exact congrArg some (Prod.mk.inj h_pr).1
                    | none => exact h_crate_rb h_s
  | @FramesSimInv.push _ _ _ callee0 prevCaller prevRest rf rPrevCaller rPrevRest
      prevCallerBody prevCalleeBody prevDst prevDstTy prevCRetTy
      h_fsim_callers h_cb h_calleeb h_frdst h_dst_emp' h_dst_ty'
      h_dst_supp' h_cret_ty' h_beq' h_tgt_lt' h_rc_cached' h_cfs => by
    intro h_fs_eq h_rev_eq
    injection h_fs_eq with h_f0_eq h_c_eq
    subst callee0; subst h_c_eq
    have h_ctrl_eq : rs.miri.machine.user.control = ctrl := by rw [h_miri]; rfl
    have h_mem_eq : rs.miri.machine.memory = mem := by rw [h_miri]; rfl
    have h_sf_eq : rs.miri.stack.frames = rframes := by rw [h_miri]; rfl
    have h_tr_eq :
        (match rs.miri.machine.threads.activeThread? with
         | some th => th.topUserRelevantFrame
         | none => none) = topRel? := by
      rw [h_miri]; rfl
    have h_ec_orig := h_ec
    unfold evalCallTerminator at h_ec
    cases h_chk :
        (!callTargetAdmitted body bb calleeBody args dst target unwind ||
          calleeBody.basicBlocks.isEmpty ||
          !storageAnnotationsInBounds calleeBody ||
          !discriminantTypesValid calleeBody ||
          !castTypesValid calleeBody ||
          !assignTypesValid calleeBody ||
          !calleeBody.locals.all isSupportedScalarOrUnitTy) with
    | true => rw [h_chk] at h_ec; cases h_ec
    | false =>
      let ⟨argVals, callerLocals', mem', h_eca, h_ec⟩ :=
        evalCallTerminator_args_elim h_chk h_ec_orig
      simp only [Bool.or_eq_false_iff, Bool.not_eq_false'] at h_chk
      let ⟨⟨⟨⟨⟨⟨h_adm, h_emp⟩, h_csa⟩, h_cdv⟩, h_ccv⟩, h_casg⟩, h_csupp⟩ := h_chk
      cases h_gdst : MirSemantics.getElem? callerLocals' dst.localId with
      | none => rw [h_gdst] at h_ec; cases h_ec
      | some dstSl =>
        rw [h_gdst] at h_ec
        cases dstSl with
        | dead => cases h_ec
        | indirect _ => cases h_ec
        | partialTuple _ => cases h_ec
        | immediate _ =>
            injection h_ec with h_s'_eq
            subst h_s'_eq
            have h_cadm := h_adm
            dsimp only [callTargetAdmitted] at h_cadm
            simp only [Bool.and_eq_true] at h_cadm
            let ⟨⟨⟨⟨⟨⟨⟨_, h_tgt_ok⟩, h_dst_emp⟩, _⟩, _⟩, h_cblt⟩, h_tys⟩, _⟩ := h_cadm
            have h_tgt_lt :
                match target with
                | none => True
                | some tgt => Nat.blt tgt body.basicBlocks.length = true := by
              cases target with
              | none => exact True.intro
              | some _ => exact h_tgt_ok
            cases h_dl : MirSemantics.getElem? body.locals dst.localId with
            | none => rw [h_dl] at h_tys; cases h_tys
            | some dstTy =>
              rw [h_dl] at h_tys
              cases h_cl0 : MirSemantics.getElem? calleeBody.locals 0 with
              | none => rw [h_cl0] at h_tys; cases h_tys
              | some cRetTy =>
                rw [h_cl0] at h_tys
                dsimp only at h_tys
                rw [Bool.and_eq_true] at h_tys
                let ⟨h_dst_supp, h_dst_beq⟩ := h_tys
                have h_touch_dst :
                    callTouchesCallerLocal body f dst.localId = true := by
                  apply callTouchesCallerLocal_dst h_bb
                  cases h_call with
                  | inl h_c1 =>
                    cases h_c1 with | intro callee h_c1 => cases h_c1 with | intro tgt h_c1 =>
                    cases h_c1 with | intro uw h_c1 => exact Or.inl ⟨callee, args, tgt, uw, h_c1.1⟩
                  | inr h_c2 =>
                    cases h_c2 with | intro op h_c2 => cases h_c2 with | intro tgt h_c2 =>
                    cases h_c2 with | intro uw h_c2 => exact Or.inr ⟨op, args, tgt, uw, h_c2.1⟩
                have h_dl_lt : dst.localId < body.locals.length :=
                  getElem?_lt_len h_dl
                have h_chead :
                    calleeBody.locals[0]?.getD .unit = dstTy := by
                  cases h_l : calleeBody.locals with
                  | nil => rw [h_l] at h_cl0; cases h_cl0
                  | cons hd _ =>
                    rw [h_l] at h_cl0
                    injection h_cl0 with h_hd
                    subst h_hd
                    exact (MirTy.eq_of_beq h_dst_beq).symm
                let ⟨h_carg_dec, _, _, _, _⟩ := decodeBody_inv h_cbdec
                let fnTag :=
                  match sysrootOp? with
                  | some op => fnTagForSysroot op
                  | none => fnTagForCrate calleeDefId
                let calleeLocals :=
                  initLocalsLoop calleeBody argVals 0 calleeBody.locals
                let calleeFrame : FrameState := {
                  defId := calleeDefId
                  blockIdx := 0
                  stmtIdx := 0
                  locals := calleeLocals
                  sysrootOp? := sysrootOp?
                  retDst? := some dst
                  retTarget? := target
                }
                let calleeCache :=
                  calleeInitCacheLoop calleeRbody.argumentCount 0
                    calleeBody.locals
                let rfCallee := mkRefMiriCallFrame rp.types fnTag
                  calleeRbody 0 0
                  (liftLocalsCached rp.types calleeBody.locals
                    calleeLocals calleeCache)
                  rframes.size
                let ⟨body₀, rbody₀, cache, callerFnTag, h_act_b0, h_act_rb0,
                  h_bdec, h_fnTag, h_crate₀, h_sys₀, h_arg, h_sa, h_dv, h_cv, h_act,
                  h_asg, h_calls, h_all_static, h_supp, h_inv₀, h_pc₀,
                  h_c_len, h_rf⟩ := h_cfs
                rw [h_body] at h_act_b0; injection h_act_b0 with hb_eq; subst hb_eq
                rw [h_rbody] at h_act_rb0; injection h_act_rb0 with hrb_eq; subst hrb_eq
                rw [h_body] at h_calleeb; injection h_calleeb with hcb_eq; subst hcb_eq
                let ⟨h_cl_inv, h_cargs, h_m_eq⟩ :=
                  evalCallArgs_slotsMatchTys h_inv₀ h_eca
                have h_callee_inv : SlotsMatchTys calleeBody.locals calleeLocals :=
                  initLocalsLoop_slotsMatchTys calleeBody argVals h_cargs
                have h_rf_arr := array_eq_push_of_toList_reverse h_rev_eq
                have h_len_callers :
                    (rPrevCaller :: rPrevRest).length =
                      (prevCaller :: prevRest).length :=
                  framesSimInv_length_eq h_fsim_callers
                have h_sz_rframes : rframes.size = prevRest.length + 2 := by
                  rw [h_rf_arr, Array.size_push]
                  change (rPrevCaller :: rPrevRest).reverse.length + 1 = prevRest.length + 2
                  rw [List.length_reverse]
                  change rPrevRest.length + 1 + 1 = prevRest.length + 2
                  rw [Nat.succ.inj h_len_callers]
                have h_ne_same :
                    Nat.beq (prevRest.length + 3) rframes.size = false := by
                  rw [h_sz_rframes]
                  cases h_b : Nat.beq (prevRest.length + 3) (prevRest.length + 2) with
                  | false => rfl
                  | true =>
                    exact False.elim (Nat.ne_of_lt (Nat.lt_succ_self _)
                      (Nat.eq_of_beq_eq_true h_b).symm)
                have h_eq_push :
                    Nat.beq (prevRest.length + 3) (rframes.size + 1) = true := by
                  rw [h_sz_rframes]; exact Nat.beq_refl _
                have h_back : rframes.back? = some rf := by
                  rw [h_rf_arr]; exact array_back?_push _ _
                have h_pop : rframes.pop = ⟨(rPrevCaller :: rPrevRest).reverse⟩ := by
                  rw [h_rf_arr]; exact array_pop_push_eq _ _
                have h_rf_loc : rf.locals.toList =
                    liftLocalsCached rp.types body.locals f.locals cache := by
                  rw [h_rf]; rfl
                have h_upd := updateMiriLocalsLoop_liftLocalsCached rp.types
                  (callTouchesCallerLocal body f) 0 body.locals
                  callerLocals' f.locals cache
                  (SlotsMatchTys.length_eq h_cl_inv).symm
                  ((SlotsMatchTys.length_eq h_cl_inv).trans
                    (SlotsMatchTys.length_eq h_inv₀).symm)
                  ((SlotsMatchTys.length_eq h_inv₀).trans h_c_len.symm)
                let callerCache' := updateCacheLoop (callTouchesCallerLocal body f) 0 cache
                let rfCaller' := {
                  rf with
                  locals := Array.mk (liftLocalsCached rp.types body.locals
                    callerLocals' callerCache')
                }
                let rfCallee' := mkRefMiriCallFrame rp.types fnTag
                  calleeRbody 0 0
                  (liftLocalsCached rp.types calleeBody.locals
                    calleeLocals calleeCache)
                  (rframes.size - 1) dst.localId dstTy target
                have h_rfCaller'_eq :
                    rfCaller' = mkRefMiriCallFrame rp.types callerFnTag rbody
                      f.blockIdx f.stmtIdx
                      (liftLocalsCached rp.types body.locals callerLocals' callerCache')
                      prevRest.length prevDst.localId prevDstTy f.retTarget? := by
                  dsimp only [rfCaller']; rw [h_rf]; dsimp only [mkRefMiriCallFrame]
                have h_rc_cached : ∃ ls, rfCaller'.locals[dst.localId]? = some ls ∧
                    ls.layout.isSome = true := by
                  have h_get_t := getElem?_updateCacheLoop_eq_true
                    (callTouchesCallerLocal body f) 0 dst.localId cache
                    (h_c_len.symm ▸ h_dl_lt)
                    (by rw [Nat.zero_add]; exact h_touch_dst)
                  dsimp only [rfCaller']
                  rw [array_getElem?_eq_mirGetElem?]
                  exact getElem?_liftLocalsCached_layout_isSome_of_true rp.types
                    body.locals callerLocals' callerCache' dst.localId
                    (SlotsMatchTys.length_eq h_cl_inv).symm
                    (by rw [updateCacheLoop_length, h_c_len,
                          SlotsMatchTys.length_eq h_cl_inv])
                    h_get_t
                have h_sz_idx : rframes.size - 1 = (prevCaller :: prevRest).length := by
                  rw [h_sz_rframes]; rfl
                let newFrames := ((⟨(rPrevCaller :: rPrevRest).reverse⟩ : Array _).push
                  rfCaller').push rfCallee'
                have h_new_sz : newFrames.size = rframes.size + 1 := by
                  dsimp only [newFrames]
                  rw [Array.size_push, Array.size_push]
                  change (rPrevCaller :: rPrevRest).reverse.length + 1 + 1 = rframes.size + 1
                  rw [List.length_reverse, h_sz_rframes]
                  change rPrevRest.length + 1 + 1 + 1 = prevRest.length + 2 + 1
                  rw [Nat.succ.inj h_len_callers]
                have h_rev_new :
                    newFrames.toList.reverse =
                      rfCallee' :: rfCaller' :: rPrevCaller :: rPrevRest := by
                  dsimp only [newFrames]
                  simp [Array.push, List.concat_eq_append]
                rw [h_sf_eq, h_tr_eq, h_ctrl_eq, h_mem_eq]
                refine ⟨newFrames, some rframes.size, ?_, newFrames, retTy, mem,
                  nextRefControlForStep body f ctrl, some rframes.size,
                  h_dec, rfl, h_m_eq.trans h_smem, h_ert, h_rty, h_init,
                  refControlValid_nextRefControlForStep h_ctrl,
                  ⟨by rw [h_new_sz]; exact Nat.zero_lt_succ _, by rw [h_new_sz]; simp⟩,
                  rfl, ?_⟩
                · dsimp only [liftStackStep]
                  rw [show (prevCaller :: prevRest).length + 2 = prevRest.length + 3 from rfl,
                    h_ne_same, ite_eq_right (by decide), h_eq_push, ite_eq_left rfl,
                    h_back]
                  dsimp only
                  cases h_s : sysrootOp? with
                  | some op =>
                    dsimp only [newFrames, rfCallee', fnTag]
                    rw [h_s]; dsimp only
                    rw [h_res_sys op h_s]
                    dsimp only; rw [h_chead, h_rf_loc, h_upd, h_pop]
                  | none =>
                    dsimp only [newFrames, rfCallee', fnTag]
                    rw [h_s]; dsimp only
                    rw [h_res_crate h_s]
                    dsimp only; rw [h_chead, h_rf_loc, h_upd, h_pop]
                rw [h_rev_new]
                refine FramesSimInv.push
                  (FramesSimInv.push h_fsim_callers h_cb h_body h_frdst
                    h_dst_emp' h_dst_ty' h_dst_supp' h_cret_ty' h_beq'
                    h_tgt_lt' h_rc_cached'
                    ⟨body, rbody, callerCache', callerFnTag, h_body, h_rbody,
                      h_bdec, h_fnTag, h_crate₀, h_sys₀, h_arg, h_sa, h_dv, h_cv, h_act,
                      h_asg, h_calls, h_all_static, h_supp, h_cl_inv, h_pc₀,
                      (updateCacheLoop_length _ 0 cache).trans h_c_len,
                      h_rfCaller'_eq⟩)
                  h_body ?_ rfl h_dst_emp h_dl h_dst_supp h_cl0 h_dst_beq
                  (by cases target with | none => exact True.intro | some _ => exact h_tgt_ok)
                  h_rc_cached ?_
                · dsimp only [activeFrameBody]
                  cases h_s : sysrootOp? with
                  | some op =>
                    have h_op_eq : calleeBody = sysrootNumBody op := by
                      cases h_call with
                      | inl h_c1 =>
                        cases h_c1 with | intro _ h_c1 => cases h_c1 with | intro _ h_c1 =>
                        cases h_c1 with | intro _ h_c1 =>
                        rw [h_s] at h_c1; cases h_c1.2.2
                      | inr h_c2 =>
                        cases h_c2 with | intro op' h_c2 => cases h_c2 with | intro _ h_c2 =>
                        cases h_c2 with | intro _ h_c2 =>
                        rw [h_s] at h_c2; injection h_c2.2.2.1 with ho; subst ho; exact h_c2.2.2.2
                    exact congrArg some h_op_eq.symm
                  | none => exact h_crate h_s
                · dsimp only [rfCallee']; rw [h_sz_idx]
                  refine ⟨calleeBody, calleeRbody, calleeCache, fnTag, ?_, ?_,
                    h_cbdec, rfl, h_crate, h_sys, h_cblt, h_csa, h_cdv,
                    h_ccv, h_cb_act, h_casg, h_cb_calls, h_cb_all_static, h_csupp,
                    h_callee_inv, fun _ _ => Nat.zero_le _,
                    (calleeInitCacheLoop_length calleeRbody.argumentCount 0 _), rfl⟩
                  · dsimp only [activeFrameBody]
                    cases h_s : sysrootOp? with
                    | some op =>
                      have h_op_eq : calleeBody = sysrootNumBody op := by
                        cases h_call with
                        | inl h_c1 =>
                          cases h_c1 with | intro _ h_c1 => cases h_c1 with | intro _ h_c1 =>
                          cases h_c1 with | intro _ h_c1 =>
                          rw [h_s] at h_c1; cases h_c1.2.2
                        | inr h_c2 =>
                          cases h_c2 with | intro op' h_c2 => cases h_c2 with | intro _ h_c2 =>
                          cases h_c2 with | intro _ h_c2 =>
                          rw [h_s] at h_c2; injection h_c2.2.2.1 with ho; subst ho; exact h_c2.2.2.2
                      exact congrArg some h_op_eq.symm
                    | none => exact h_crate h_s
                  · dsimp only [activeRefFrameBody]
                    cases h_s : sysrootOp? with
                    | some op =>
                      have h_res_s := h_res_sys op h_s
                      rw [refResolveCalleeBody_sysroot] at h_res_s
                      injection h_res_s with h_pr
                      exact congrArg some (Prod.mk.inj h_pr).1
                    | none => exact h_crate_rb h_s

private theorem evalCallTerminator_step_preserves {rp : RefProg} {p : Program}
    {s s' : State} {rs : RefState} {body : Body} {rbody calleeRbody : RefBody}
    {f : FrameState} {callers : List FrameState} {bb : BasicBlock}
    {calleeDefId : DefId} {sysrootOp? : Option SysrootNumOp}
    {calleeBody : Body} {args : List Operand} {dst : Place}
    {target : Option BasicBlockId} {unwind : UnwindAction}
    (h_dec : decodeProg rp = some p)
    (h_sim : SimulationInv rp p s rs)
    (hs : s.frames = f :: callers)
    (h_body : activeFrameBody p f = some body)
    (h_rbody : activeRefFrameBody rp f = some rbody)
    (h_bb : MirSemantics.getElem? body.basicBlocks f.blockIdx = some bb)
    (h_call : (∃ callee tgt uw, bb.terminator = .call callee args dst tgt uw ∧
        calleeDefId = callee ∧ sysrootOp? = none) ∨
      (∃ op tgt uw, bb.terminator = .sysrootCall op args dst tgt uw ∧
        calleeDefId = 0 ∧ sysrootOp? = some op ∧
        calleeBody = sysrootNumBody op))
    (h_cbdec : decodeBody rp.types calleeRbody = some calleeBody)
    (h_res_crate : sysrootOp? = none →
      refResolveCalleeBody rp (fnTagForCrate calleeDefId) =
        some (calleeRbody, calleeBody.locals))
    (h_res_sys : ∀ op, sysrootOp? = some op →
      refResolveCalleeBody rp (fnTagForSysroot op) =
        some (calleeRbody, calleeBody.locals))
    (h_crate : sysrootOp? = none →
      MirSemantics.getElem? p.bodies calleeDefId = some calleeBody)
    (h_crate_rb : sysrootOp? = none →
      MirSemantics.getElem? rp.bodies calleeDefId = some calleeRbody)
    (h_sys : ∀ op, sysrootOp? = some op → calleeDefId = 0)
    (h_cb_calls : callsAdmitted p calleeBody = true)
    (h_cb_all_static : allCallBodiesStaticAdmitted p calleeBody = true)
    (h_cb_act : assertConditionTypesValid calleeBody = true)
    (h_ec : evalCallTerminator body bb f callers s.mem s.callerMem calleeDefId
      sysrootOp? calleeBody args dst target unwind = .step s') :
    let ctrl' := nextRefControlForStep body f rs.miri.machine.user.control
    let prevTopRel? :=
      match rs.miri.machine.threads.activeThread? with
      | some th => th.topUserRelevantFrame
      | none => none
    ∃ newFrames newTopRel?,
      liftStackStep rp body f rs.miri.stack.frames prevTopRel? s'.frames =
        some (newFrames, newTopRel?) ∧
      SimulationInv rp p s' {
        rs with
        miri := mkRefMiriStackState newFrames newTopRel?
          rs.miri.machine.memory ctrl' s'.callerMem
        stepsExecuted := rs.stepsExecuted + 1
      } := by
  let ⟨_, _, _, _, _, _, _, h_smem, h_ert, h_rty,
    h_init, h_ctrl, h_tr, h_miri, h_fsim⟩ := h_sim
  exact evalCallTerminator_step_preserves_aux h_dec h_smem h_ert h_rty h_init h_ctrl h_tr h_miri
    h_fsim h_body h_rbody h_bb h_call h_cbdec h_res_crate h_res_sys h_crate h_crate_rb
    h_sys h_cb_calls h_cb_all_static h_cb_act h_ec hs rfl

private theorem list_any_of_mirGetElem? {α : Type} {xs : List α} {p : α → Bool}
    {i : Nat} {x : α} (h_get : MirSemantics.getElem? xs i = some x)
    (h_px : p x = true) : xs.any p = true := by
  induction xs generalizing i with
  | nil => cases h_get
  | cons hd tl ih =>
    cases i with
    | zero =>
      injection h_get with heq; subst heq
      dsimp only [List.any]
      rw [h_px]; rfl
    | succ j =>
      dsimp only [List.any]
      rw [ih h_get, Bool.or_true]

private theorem evalNonRootReturn_callers_aux {rp : RefProg} {p : Program}
    {rs : RefState} {body : Body} {f caller : FrameState} {rest : List FrameState}
    {rframes : Array (Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)}
    {rf rcaller : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra}
    {rrest : List (Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)}
    {retTy : MirTy}
    {mem : Miri.Memory.MemoryState Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree Unit}
    {ctrl : Miri.Interpreter.TerminatorMachine.Control Unit}
    {topRel? : Option Nat}
    {cFs : List FrameState}
    {cRfs : List (Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)}
    {callerBody : Body} {dst : Place} {dstTy : MirTy}
    {callerLocals' : List LocalSlot} {amem' : MemoryState} {retVal : Val} {tgt : BasicBlockId}
    {cMem : MemoryState}
    {callerMem0 : CallerMemory}
    (h_dec : decodeProg rp = some p)
    (h_smem : cMem = entryMemory)
    (h_ert : entryRetTy? p = some retTy)
    (h_rty : rs.retTy = retTy)
    (h_init : refInitMemoryAndRetPlace rp.types retTy = .ok (mem, rs.retPlace))
    (h_ctrl : RefControlValid ctrl)
    (_h_tr : refTopRelevanceValid rframes.size topRel?)
    (h_miri : rs.miri = mkRefMiriStackState rframes topRel? mem ctrl callerMem0)
    (h_fsim_callers : FramesSimInv rp p rs.retPlace cFs cRfs)
    (h_rev_arr : rframes = (⟨(rcaller :: rrest).reverse⟩ : Array _).push rf)
    (h_cb : activeFrameBody p caller = some callerBody)
    (h_frdst : f.retDst? = some dst)
    (h_dst_ty : MirSemantics.getElem? callerBody.locals dst.localId = some dstTy)
    (h_rc_cached : ∃ ls, rcaller.locals[dst.localId]? = some ls ∧ ls.layout.isSome = true)
    (h_wp : writePlace caller.locals cMem dst.localId dstTy retVal = .ok (callerLocals', amem')) :
    cFs = caller :: rest →
    cRfs = rcaller :: rrest →
    let s' : State := {
      frames := { caller with blockIdx := tgt, stmtIdx := 0, locals := callerLocals' } :: rest
      callerMem := callerMem0
      mem := amem'
    }
    let ctrl' := nextRefControlForStep body f rs.miri.machine.user.control
    let prevTopRel? :=
      match rs.miri.machine.threads.activeThread? with
      | some th => th.topUserRelevantFrame
      | none => none
    ∃ newFrames newTopRel?,
      liftStackStep rp body f rs.miri.stack.frames prevTopRel? s'.frames =
        some (newFrames, newTopRel?) ∧
      SimulationInv rp p s' {
        rs with
        miri := mkRefMiriStackState newFrames newTopRel?
          rs.miri.machine.memory ctrl' s'.callerMem
        stepsExecuted := rs.stepsExecuted + 1
      } :=
  match h_fsim_callers with
  | @FramesSimInv.root _ _ _ cF cRf h_c_defId h_c_sro h_c_rdst h_c_rtgt h_c_fs => by
    intro h_cFs h_cRfs
    injection h_cFs with h_cf h_cr; injection h_cRfs with h_rcf h_rcr
    subst cF; subst h_cr; subst cRf; subst h_rcr
    have h_ctrl_eq : rs.miri.machine.user.control = ctrl := by rw [h_miri]; rfl
    have h_mem_eq : rs.miri.machine.memory = mem := by rw [h_miri]; rfl
    have h_sf_eq : rs.miri.stack.frames = rframes := by rw [h_miri]; rfl
    have h_tr_eq :
        (match rs.miri.machine.threads.activeThread? with
         | some th => th.topUserRelevantFrame
         | none => none) = topRel? := by
      rw [h_miri]; rfl
    let ⟨cBody₀, cRbody₀, cCache, h_c_b0, h_c_rb0, h_c_bdec, h_c_arg,
      h_c_sa, h_c_dv, h_c_cv, h_c_act, h_c_calls, h_c_all_static, h_c_supp,
      h_c_inv, _, h_c_crep, h_c_rf⟩ := h_c_fs
    have h_c_ab : activeFrameBody p caller = some cBody₀ := by
      dsimp only [activeFrameBody]; rw [h_c_sro]; exact h_c_b0
    rw [h_cb] at h_c_ab; injection h_c_ab with hcb_eq; subst hcb_eq
    let ⟨h_cl_inv, h_m_eq⟩ :=
      writePlace_slotsMatchTys h_c_inv h_dst_ty h_wp
    have h_c_len : cCache.length = callerBody.locals.length := by
      rw [h_c_crep, List.length_replicate]
    have h_upd := updateMiriLocalsLoop_liftLocalsCached rp.types
      (fun idx => Nat.beq idx dst.localId) 0 callerBody.locals
      callerLocals' caller.locals cCache
      (SlotsMatchTys.length_eq h_cl_inv).symm
      ((SlotsMatchTys.length_eq h_cl_inv).trans
        (SlotsMatchTys.length_eq h_c_inv).symm)
      ((SlotsMatchTys.length_eq h_c_inv).trans h_c_len.symm)
    rw [h_c_crep, updateCacheLoop_replicate_true] at h_upd
    have h_c_filt :
        rcaller.body.locals.toList.filterMap (resolveTy rp.types) =
          callerBody.locals := by
      rw [h_c_rf]
      exact toMiriBody_locals_filterMap_resolveTy h_c_bdec
    have h_c_loc : rcaller.locals.toList =
        liftLocalsCached rp.types callerBody.locals caller.locals cCache := by
      rw [h_c_rf]; rfl
    rw [h_c_crep] at h_c_loc
    have h_arr2 : rframes = Array.mk [rcaller, rf] := by
      rw [h_rev_arr]; rfl
    rw [h_sf_eq, h_arr2, h_tr_eq, h_ctrl_eq, h_mem_eq]
    dsimp only [liftStackStep]
    rw [show Nat.beq ((Array.mk [rcaller, rf]).size) 1 = false from rfl,
      ite_eq_right (by decide),
      show Nat.beq ((Array.mk [rcaller, rf]).size) 2 = true from rfl,
      ite_eq_left rfl,
      show (Array.mk [rcaller, rf])[0]? = some rcaller from rfl,
      h_frdst]
    dsimp only
    rw [h_c_filt, h_c_loc, h_upd]
    let rcaller' := {
      rcaller with
      locals := Array.mk (liftLocalsCached rp.types callerBody.locals
        callerLocals' (List.replicate callerBody.locals.length true))
      location := .mir ⟨tgt, 0⟩
    }
    have h_rcaller'_eq :
        rcaller' = mkRefMiriFrame rp.types caller.defId cRbody₀ tgt 0
          (liftLocalsCached rp.types callerBody.locals callerLocals'
            (List.replicate callerBody.locals.length true))
          rs.retPlace := by
      dsimp only [rcaller']; rw [h_c_rf]; rfl
    refine ⟨Array.mk [rcaller'], some 0, rfl, Array.mk [rcaller'], retTy, mem,
      nextRefControlForStep body f ctrl, some 0, h_dec, rfl,
      h_m_eq.trans h_smem, h_ert, h_rty, h_init,
      refControlValid_nextRefControlForStep h_ctrl,
      ⟨Nat.zero_lt_one, rfl⟩, rfl, ?_⟩
    rw [show (Array.mk [rcaller']).toList.reverse = [rcaller'] from rfl]
    exact FramesSimInv.root h_c_defId h_c_sro h_c_rdst h_c_rtgt
      ⟨callerBody, cRbody₀, List.replicate callerBody.locals.length true,
        h_c_b0, h_c_rb0, h_c_bdec, h_c_arg, h_c_sa, h_c_dv, h_c_cv, h_c_act,
        h_c_calls, h_c_all_static, h_c_supp, h_cl_inv,
        fun _ _ => Nat.zero_le _, rfl, h_rcaller'_eq⟩
  | @FramesSimInv.push _ _ _ cCallee grand grest cRf rgrand rgrest
      gBody cBodyUnused gDst gDstTy cRetTyUnused
      h_g_callers h_gb h_cb2 h_c_frdst h_c_dst_emp h_c_dst_ty
      h_c_dst_supp h_c_cret_ty h_c_beq h_c_tgt_lt h_rg_cached h_c_cfs => by
    intro h_cFs h_cRfs
    injection h_cFs with h_cf h_cr; injection h_cRfs with h_rcf h_rcr
    subst cCallee; subst h_cr; subst cRf; subst h_rcr
    have h_ctrl_eq : rs.miri.machine.user.control = ctrl := by rw [h_miri]; rfl
    have h_mem_eq : rs.miri.machine.memory = mem := by rw [h_miri]; rfl
    have h_sf_eq : rs.miri.stack.frames = rframes := by rw [h_miri]; rfl
    have h_tr_eq :
        (match rs.miri.machine.threads.activeThread? with
         | some th => th.topUserRelevantFrame
         | none => none) = topRel? := by
      rw [h_miri]; rfl
    let ⟨cBody₀, cRbody₀, cCache, cFnTag, h_c_act_b0, h_c_act_rb0,
      h_c_bdec, h_c_fnTag, h_c_crate, h_c_sys, h_c_arg, h_c_sa,
      h_c_dv, h_c_cv, h_c_act, h_c_asg, h_c_calls, h_c_all_static, h_c_supp,
      h_c_inv, _, h_c_len, h_c_rf⟩ := h_c_cfs
    rw [h_cb] at h_c_act_b0; injection h_c_act_b0 with hcb_eq; subst hcb_eq
    rw [h_cb] at h_cb2; injection h_cb2 with hcb2_eq; subst hcb2_eq
    let ⟨h_cl_inv, h_m_eq⟩ :=
      writePlace_slotsMatchTys h_c_inv h_dst_ty h_wp
    have h_len_g : (rgrand :: rgrest).length = (grand :: grest).length :=
      framesSimInv_length_eq h_g_callers
    have h_arr_popped :
        (⟨(rcaller :: rgrand :: rgrest).reverse⟩ : Array _) =
          (⟨(rgrand :: rgrest).reverse⟩ : Array _).push rcaller :=
      array_reverse_cons_push rcaller (rgrand :: rgrest)
    have h_sz_rframes : rframes.size = grest.length + 3 := by
      rw [h_rev_arr, Array.size_push]
      change (rcaller :: rgrand :: rgrest).reverse.length + 1 = grest.length + 3
      rw [List.length_reverse]
      change rgrest.length + 1 + 1 + 1 = grest.length + 3
      rw [Nat.succ.inj h_len_g]
    have h_ne_same :
        Nat.beq (grest.length + 2) rframes.size = false := by
      rw [h_sz_rframes]
      cases h_b : Nat.beq (grest.length + 2) (grest.length + 3) with
      | false => rfl
      | true =>
        exact False.elim (Nat.ne_of_lt (Nat.lt_succ_self _)
          (Nat.eq_of_beq_eq_true h_b))
    have h_ne_push :
        Nat.beq (grest.length + 2) (rframes.size + 1) = false := by
      rw [h_sz_rframes]
      cases h_b : Nat.beq (grest.length + 2) (grest.length + 3 + 1) with
      | false => rfl
      | true =>
        exact False.elim (Nat.ne_of_lt
          (Nat.lt_trans (Nat.lt_succ_self _) (Nat.lt_succ_self _))
          (Nat.eq_of_beq_eq_true h_b))
    have h_eq_ret :
        Nat.beq (grest.length + 2 + 1) rframes.size = true := by
      rw [h_sz_rframes]; exact Nat.beq_refl _
    have h_rframes_pop :
        rframes.pop = (⟨(rgrand :: rgrest).reverse⟩ : Array _).push rcaller := by
      rw [h_rev_arr, array_pop_push_eq, h_arr_popped]
    have h_popped_back :
        rframes.pop.back? = some rcaller := by
      rw [h_rframes_pop]; exact array_back?_push _ _
    have h_popped_pop :
        rframes.pop.pop = ⟨(rgrand :: rgrest).reverse⟩ := by
      rw [h_rframes_pop]; exact array_pop_push_eq _ _
    have h_popped_sz :
        rframes.pop.size = grest.length + 2 := by
      rw [h_rframes_pop, Array.size_push]
      change (rgrand :: rgrest).reverse.length + 1 = grest.length + 2
      rw [List.length_reverse]
      change rgrest.length + 1 + 1 = grest.length + 2
      rw [Nat.succ.inj h_len_g]
    have h_c_loc : rcaller.locals.toList =
        liftLocalsCached rp.types callerBody.locals caller.locals cCache := by
      rw [h_c_rf]; rfl
    have h_c_res :
        refResolveCalleeBody rp cFnTag =
          some (cRbody₀, callerBody.locals) := by
      rw [h_c_fnTag]
      cases h_so : caller.sysrootOp? with
      | some op =>
        have h_cb_sys : callerBody = sysrootNumBody op := by
          dsimp only [activeFrameBody] at h_cb
          rw [h_so] at h_cb
          injection h_cb with h_eq; exact h_eq.symm
        have h_rb_sys : cRbody₀ = sysrootNumRefBody rp.types op := by
          dsimp only [activeRefFrameBody] at h_c_act_rb0
          rw [h_so] at h_c_act_rb0
          injection h_c_act_rb0 with h_eq; exact h_eq.symm
        rw [h_cb_sys, h_rb_sys]
        exact refResolveCalleeBody_sysroot rp op
      | none =>
        have h_get_rb : MirSemantics.getElem? rp.bodies caller.defId = some cRbody₀ := by
          dsimp only [activeRefFrameBody] at h_c_act_rb0
          rw [h_so] at h_c_act_rb0
          exact h_c_act_rb0
        exact refResolveCalleeBody_crate rp caller.defId cRbody₀ callerBody.locals
          h_get_rb (decodeBody_inv h_c_bdec).2.1
    have h_c_fi : rcaller.functionInstance.kind = .Item cFnTag := by
      rw [h_c_rf]; rfl
    have h_dst_c : MirSemantics.getElem? cCache dst.localId = some true := by
      let ⟨ls, h_ls, h_is⟩ := h_rc_cached
      have h_ls_mir : MirSemantics.getElem?
          (liftLocalsCached rp.types callerBody.locals caller.locals cCache)
          dst.localId = some ls := by
        rw [← h_c_loc, ← array_getElem?_eq_mirGetElem?]
        exact h_ls
      exact getElem?_liftLocalsCached_layout_isSome rp.types
        callerBody.locals caller.locals cCache dst.localId
        (SlotsMatchTys.length_eq h_c_inv).symm
        ((SlotsMatchTys.length_eq h_c_inv).trans h_c_len.symm)
        h_ls_mir h_is
    have h_upd := updateMiriLocalsLoop_liftLocalsCached rp.types
      (fun idx => Nat.beq idx dst.localId) 0 callerBody.locals
      callerLocals' caller.locals cCache
      (SlotsMatchTys.length_eq h_cl_inv).symm
      ((SlotsMatchTys.length_eq h_cl_inv).trans
        (SlotsMatchTys.length_eq h_c_inv).symm)
      ((SlotsMatchTys.length_eq h_c_inv).trans h_c_len.symm)
    have h_uc := updateCacheLoop_self_of_true cCache dst.localId 0 h_dst_c
    rw [show (fun i => Nat.beq i (0 + dst.localId)) = (fun idx => Nat.beq idx dst.localId) from
          by funext i; rw [Nat.zero_add]] at h_uc
    rw [h_uc] at h_upd
    rw [h_sf_eq, h_tr_eq, h_ctrl_eq, h_mem_eq]
    dsimp only [liftStackStep]
    rw [h_ne_same, ite_eq_right (by decide),
      h_ne_push, ite_eq_right (by decide),
      h_eq_ret, ite_eq_left rfl,
      h_popped_back, h_frdst]
    dsimp only
    rw [h_c_fi]
    dsimp only
    rw [h_c_res]
    dsimp only
    rw [h_c_loc, h_upd, h_popped_pop, h_popped_sz]
    let rcaller' := {
      rcaller with
      locals := Array.mk (liftLocalsCached rp.types callerBody.locals
        callerLocals' cCache)
      location := .mir ⟨tgt, 0⟩
    }
    have h_rcaller'_eq :
        rcaller' = mkRefMiriCallFrame rp.types cFnTag cRbody₀ tgt 0
          (liftLocalsCached rp.types callerBody.locals callerLocals' cCache)
          grest.length gDst.localId gDstTy caller.retTarget? := by
      dsimp only [rcaller']; rw [h_c_rf]; rfl
    let newFrames := (⟨(rgrand :: rgrest).reverse⟩ : Array _).push rcaller'
    have h_new_sz : newFrames.size = grest.length + 2 := by
      dsimp only [newFrames]
      rw [Array.size_push]
      change (rgrand :: rgrest).reverse.length + 1 = grest.length + 2
      rw [List.length_reverse]
      change rgrest.length + 1 + 1 = grest.length + 2
      rw [Nat.succ.inj h_len_g]
    have h_rev_new : newFrames.toList.reverse = rcaller' :: rgrand :: rgrest := by
      dsimp only [newFrames]
      simp [Array.push, List.concat_eq_append]
    refine ⟨newFrames, some (grest.length + 2 - 1), rfl, newFrames, retTy,
      mem, nextRefControlForStep body f ctrl, some (grest.length + 2 - 1),
      h_dec, rfl, h_m_eq.trans h_smem, h_ert, h_rty, h_init,
      refControlValid_nextRefControlForStep h_ctrl,
      ⟨by rw [h_new_sz]; exact Nat.zero_lt_succ _, by rw [h_new_sz]⟩,
      rfl, ?_⟩
    rw [h_rev_new]
    exact FramesSimInv.push h_g_callers h_gb h_cb h_c_frdst h_c_dst_emp
      h_c_dst_ty h_c_dst_supp h_c_cret_ty h_c_beq h_c_tgt_lt h_rg_cached
      ⟨callerBody, cRbody₀, cCache, cFnTag, h_cb, h_c_act_rb0,
        h_c_bdec, h_c_fnTag, h_c_crate, h_c_sys, h_c_arg, h_c_sa,
        h_c_dv, h_c_cv, h_c_act, h_c_asg, h_c_calls, h_c_all_static, h_c_supp,
        h_cl_inv, fun _ _ => Nat.zero_le _, h_c_len, h_rcaller'_eq⟩

private theorem evalNonRootReturn_step_preserves_aux {rp : RefProg} {p : Program}
    {s s' : State} {rs : RefState} {body : Body}
    {f caller : FrameState} {rest : List FrameState} {bb : BasicBlock}
    {rframes : Array (Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)}
    {retTy : MirTy}
    {mem : Miri.Memory.MemoryState Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree Unit}
    {ctrl : Miri.Interpreter.TerminatorMachine.Control Unit}
    {topRel? : Option Nat}
    {fs : List FrameState}
    {rfsRev : List (Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)}
    (h_dec : decodeProg rp = some p)
    (h_smem : s.mem = entryMemory)
    (h_ert : entryRetTy? p = some retTy)
    (h_rty : rs.retTy = retTy)
    (h_init : refInitMemoryAndRetPlace rp.types retTy = .ok (mem, rs.retPlace))
    (h_ctrl : RefControlValid ctrl)
    (h_tr : refTopRelevanceValid rframes.size topRel?)
    (h_miri : rs.miri = mkRefMiriStackState rframes topRel? mem ctrl s.callerMem)
    (h_fsim : FramesSimInv rp p rs.retPlace fs rfsRev)
    (h_ev : evalNonRootReturn p body bb f caller rest s.mem s.callerMem =
      .step s') :
    fs = f :: caller :: rest →
    rframes.toList.reverse = rfsRev →
    let ctrl' := nextRefControlForStep body f rs.miri.machine.user.control
    let prevTopRel? :=
      match rs.miri.machine.threads.activeThread? with
      | some th => th.topUserRelevantFrame
      | none => none
    ∃ newFrames newTopRel?,
      liftStackStep rp body f rs.miri.stack.frames prevTopRel? s'.frames =
        some (newFrames, newTopRel?) ∧
      SimulationInv rp p s' {
        rs with
        miri := mkRefMiriStackState newFrames newTopRel?
          rs.miri.machine.memory ctrl' s'.callerMem
        stepsExecuted := rs.stepsExecuted + 1
      } :=
  match h_fsim with
  | @FramesSimInv.root _ _ _ _ _ _ _ _ _ _ => by intro h_fs_eq _; cases h_fs_eq
  | @FramesSimInv.push _ _ _ f0 caller0 rest0 rf rcaller rrest callerBody calleeBody dst dstTy cRetTy
      h_fsim_callers h_cb h_calleeb h_frdst h_dst_emp h_dst_ty h_dst_supp
      h_cret_ty h_beq h_tgt_lt h_rc_cached h_cfs => by
    intro h_fs_eq h_rev_eq
    injection h_fs_eq with h_f0_eq h_cr_eq
    injection h_cr_eq with h_c0_eq h_rest_eq
    subst f0; subst caller0; subst rest0
    dsimp only [evalNonRootReturn] at h_ev
    cases h_cl : (bb.cleanup || localsHaveIndirect f.locals) with
    | true => rw [h_cl] at h_ev; cases h_ev
    | false =>
      rw [h_cl, ite_eq_right (by decide)] at h_ev
      have h_next :
          ∀ retVal : Val,
            (show Trusted.MirSemantics.StepResult State TerminalOut from
              match f.retDst? with
              | none => .fault .unsupported
              | some dst0 =>
                if !dst0.projection.isEmpty then .fault .unsupported
                else match activeFrameBody p caller with
                  | none => .fault .unsupported
                  | some cBody =>
                    match MirSemantics.getElem? cBody.locals dst0.localId with
                    | none => .fault .unsupported
                    | some dTy =>
                      match writePlace caller.locals s.mem dst0.localId dTy retVal with
                      | .error k => .fault k
                      | .ok (cLocals', amem') =>
                        match f.retTarget? with
                        | none => .fault .undefined
                        | some tgt' =>
                          .step {
                            frames := { caller with blockIdx := tgt', stmtIdx := 0, locals := cLocals' } :: rest
                            callerMem := s.callerMem
                            mem := amem'
                          }) = .step s' →
            ∃ newFrames newTopRel?,
              liftStackStep rp body f rs.miri.stack.frames
                (match rs.miri.machine.threads.activeThread? with
                 | some th => th.topUserRelevantFrame
                 | none => none) s'.frames = some (newFrames, newTopRel?) ∧
              SimulationInv rp p s' {
                rs with
                miri := mkRefMiriStackState newFrames newTopRel?
                  rs.miri.machine.memory (nextRefControlForStep body f rs.miri.machine.user.control) s'.callerMem
                stepsExecuted := rs.stepsExecuted + 1
              } := by
        intro retVal h_step
        rw [h_frdst] at h_step; dsimp only at h_step
        rw [h_dst_emp] at h_step; dsimp only [Bool.not, ite_false] at h_step
        rw [h_cb] at h_step; dsimp only at h_step
        rw [h_dst_ty] at h_step; dsimp only at h_step
        cases h_wp : writePlace caller.locals s.mem dst.localId dstTy retVal with
        | error _ => rw [h_wp] at h_step; cases h_step
        | ok pair =>
          cases pair with | mk callerLocals' amem' =>
          rw [h_wp] at h_step; dsimp only at h_step
          cases h_rt : f.retTarget? with
          | none => rw [h_rt] at h_step; cases h_step
          | some tgt =>
            rw [h_rt] at h_step
            injection h_step with h_s'_eq
            subst h_s'_eq
            have h_rf_arr := array_eq_push_of_toList_reverse h_rev_eq
            exact evalNonRootReturn_callers_aux h_dec h_smem h_ert h_rty h_init h_ctrl h_tr h_miri
              h_fsim_callers h_rf_arr h_cb h_frdst h_dst_ty h_rc_cached h_wp rfl rfl
      cases h_sl0 : MirSemantics.getElem? f.locals 0 with
      | none => rw [h_sl0] at h_ev; cases h_ev
      | some sl =>
        rw [h_sl0] at h_ev
        cases sl with
        | dead => cases h_ev
        | partialTuple _ => cases h_ev
        | immediate o =>
          cases o with
          | none => cases h_ev
          | some v => exact h_next v h_ev
        | indirect mp =>
          dsimp only at h_ev
          cases h_rty0 : MirSemantics.getElem? body.locals 0 with
          | none => rw [h_rty0] at h_ev; cases h_ev
          | some rTy =>
            rw [h_rty0] at h_ev; dsimp only at h_ev
            cases h_ld : loadIndirect s.mem rTy mp with
            | error _ => rw [h_ld] at h_ev; cases h_ev
            | ok ov =>
              rw [h_ld] at h_ev
              cases ov with
              | none => cases h_ev
              | some v => exact h_next v h_ev

private theorem evalNonRootReturn_step_preserves {rp : RefProg} {p : Program}
    {s s' : State} {rs : RefState} {body : Body} {rbody : RefBody}
    {f caller : FrameState} {rest : List FrameState} {bb : BasicBlock}
    (h_dec : decodeProg rp = some p)
    (h_sim : SimulationInv rp p s rs)
    (hs : s.frames = f :: caller :: rest)
    (_h_body : activeFrameBody p f = some body)
    (_h_rbody : activeRefFrameBody rp f = some rbody)
    (h_ev : evalNonRootReturn p body bb f caller rest s.mem s.callerMem =
      .step s') :
    let ctrl' := nextRefControlForStep body f rs.miri.machine.user.control
    let prevTopRel? :=
      match rs.miri.machine.threads.activeThread? with
      | some th => th.topUserRelevantFrame
      | none => none
    ∃ newFrames newTopRel?,
      liftStackStep rp body f rs.miri.stack.frames prevTopRel? s'.frames =
        some (newFrames, newTopRel?) ∧
      SimulationInv rp p s' {
        rs with
        miri := mkRefMiriStackState newFrames newTopRel?
          rs.miri.machine.memory ctrl' s'.callerMem
        stepsExecuted := rs.stepsExecuted + 1
      } := by
  let ⟨_, _, _, _, _, _, _, h_smem, h_ert, h_rty,
    h_init, h_ctrl, h_tr, h_miri, h_fsim⟩ := h_sim
  exact evalNonRootReturn_step_preserves_aux h_dec h_smem h_ert h_rty h_init h_ctrl h_tr h_miri
    h_fsim h_ev hs rfl

private theorem framesSimInv_top_props {rp : RefProg} {p : Program}
    {retPlace : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance}
    {f : FrameState} {callers : List FrameState} {body : Body} {rbody : RefBody}
    {fs : List FrameState}
    {rfsRev : List (Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)}
    (h_fsim : FramesSimInv rp p retPlace fs rfsRev)
    (h_body : activeFrameBody p f = some body)
    (h_rbody : activeRefFrameBody rp f = some rbody) :
    fs = f :: callers →
    SlotsMatchTys body.locals f.locals ∧
      callsAdmitted p body = true ∧
      allCallBodiesStaticAdmitted p body = true ∧
      decodeBody rp.types rbody = some body :=
  match h_fsim with
  | @FramesSimInv.root _ _ _ f0 _ _ h_sro _ _ h_fs => by
    intro h_fs_eq
    injection h_fs_eq with h_f0 h_c0; subst f0
    let ⟨b₀, rb₀, _, hb₀, hrb₀, hbd, _, _, _, _, _, hc, has, _, hinv, _⟩ := h_fs
    have h_ab : activeFrameBody p f = some b₀ := by
      dsimp only [activeFrameBody]; rw [h_sro]; exact hb₀
    have h_arb : activeRefFrameBody rp f = some rb₀ := by
      dsimp only [activeRefFrameBody]; rw [h_sro]; exact hrb₀
    rw [h_body] at h_ab; injection h_ab with hb_eq; subst hb_eq
    rw [h_rbody] at h_arb; injection h_arb with hrb_eq; subst hrb_eq
    exact ⟨hinv, hc, has, hbd⟩
  | @FramesSimInv.push _ _ _ f0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h_cfs => by
    intro h_fs_eq
    injection h_fs_eq with h_f0 h_c0; subst f0
    let ⟨b₀, rb₀, _, _, hb₀, hrb₀, hbd, _, _, _, _, _, _, _, _, _, hc, has, _, hinv, _⟩ :=
      h_cfs
    rw [h_body] at hb₀; injection hb₀ with hb_eq; subst hb_eq
    rw [h_rbody] at hrb₀; injection hrb₀ with hrb_eq; subst hrb_eq
    exact ⟨hinv, hc, has, hbd⟩

private theorem attachCallers_step_eq_sim (callers : List FrameState)
    (s₁ : State) :
    attachCallers callers (.step s₁) =
      .step { s₁ with frames := s₁.frames ++ callers } := by
  cases callers with
  | nil => cases s₁; simp [attachCallers]
  | cons _ _ => rfl

private theorem attachCallers_fault_eq_sim (callers : List FrameState)
    (k : FaultKind) :
    attachCallers callers (.fault k) = .fault k := by
  cases callers <;> rfl

private theorem attachCallers_done_eq_sim (callers : List FrameState)
    (out : TerminalOut) :
    attachCallers callers (.done out) = .done out := by
  cases callers <;> rfl

theorem evalStep_step_preserves {rp : RefProg} {p : Program} {c : Choice}
    {s s' : State} {rs : RefState} {body : Body} {rbody : RefBody}
    {f : FrameState} {callers : List FrameState}
    (h_dec : decodeProg rp = some p)
    (h_sim : SimulationInv rp p s rs)
    (hs : s.frames = f :: callers)
    (h_body : activeFrameBody p f = some body)
    (h_rbody : activeRefFrameBody rp f = some rbody)
    (h_es : evalStep p c s = .step s') :
    let ctrl' := nextRefControlForStep body f rs.miri.machine.user.control
    let prevTopRel? :=
      match rs.miri.machine.threads.activeThread? with
      | some th => th.topUserRelevantFrame
      | none => none
    ∃ newFrames newTopRel?,
      liftStackStep rp body f rs.miri.stack.frames prevTopRel? s'.frames =
        some (newFrames, newTopRel?) ∧
      SimulationInv rp p s' {
        rs with
        miri := mkRefMiriStackState newFrames newTopRel?
          rs.miri.machine.memory ctrl' s'.callerMem
        stepsExecuted := rs.stepsExecuted + 1
      } := by
  have h_top : SlotsMatchTys body.locals f.locals ∧
      callsAdmitted p body = true ∧
      allCallBodiesStaticAdmitted p body = true ∧
      decodeBody rp.types rbody = some body := by
    let ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, h_fsim⟩ := h_sim
    exact framesSimInv_top_props h_fsim h_body h_rbody hs
  let ⟨h_inv, h_calls, h_all_static, h_bdec⟩ := h_top
  have h_es' := h_es
  unfold evalStep at h_es'
  rw [hs] at h_es'; dsimp only at h_es'
  rw [h_body] at h_es'; dsimp only at h_es'
  cases h_bb : MirSemantics.getElem? body.basicBlocks f.blockIdx with
  | none => rw [h_bb] at h_es'; cases h_es'
  | some bb =>
    rw [h_bb] at h_es'; dsimp only at h_es'
    cases h_st : MirSemantics.getElem? bb.statements f.stmtIdx with
    | some stmt =>
      rw [h_st] at h_es'; dsimp only at h_es'
      cases h_evs : evalStatement body f s.mem s.callerMem stmt with
      | fault _ => rw [h_evs, attachCallers_fault_eq_sim] at h_es'; cases h_es'
      | done _ => rw [h_evs, attachCallers_done_eq_sim] at h_es'; cases h_es'
      | step s₁ =>
        rw [h_evs] at h_es'
        rw [attachCallers_step_eq_sim] at h_es'
        injection h_es' with h_s'_eq
        let ⟨f', h_s1_eq, h_def', h_inv', h_pc'⟩ :=
          evalStatement_step_inv h_bb h_st h_inv h_evs
        rw [h_s1_eq] at h_evs
        let ⟨h_sro', h_rdst', h_rtgt'⟩ := evalStatement_preserves_meta h_evs
        rw [h_s1_eq] at h_s'_eq
        dsimp only [List.cons_append, List.nil_append] at h_s'_eq
        rw [← h_s'_eq]
        exact sameDepth_step_preserves h_dec h_sim hs h_body h_rbody
          h_def' h_sro' h_rdst' h_rtgt' h_inv' h_pc'
    | none =>
      rw [h_st] at h_es'; dsimp only at h_es'
      cases h_end : Nat.beq f.stmtIdx bb.statements.length with
      | false => rw [h_end] at h_es'; cases h_es'
      | true =>
        rw [h_end, ite_eq_left rfl] at h_es'
        cases h_bt : bb.terminator with
        | call callee args dst tgt uw =>
          rw [h_bt] at h_es'; dsimp only at h_es'
          cases h_cb : MirSemantics.getElem? p.bodies callee with
          | none => rw [h_cb] at h_es'; cases h_es'
          | some calleeBody =>
            rw [h_cb] at h_es'; dsimp only at h_es'
            let ⟨calleeRbody, h_rcb, h_cbdec⟩ :=
              (mapOption_getElem? (decodeProg_inv h_dec).2.2.2.2 callee).2
                calleeBody h_cb
            have h_any : bodyHasAnyCall body = true := by
              dsimp only [bodyHasAnyCall]
              exact list_any_of_mirGetElem? h_bb (by rw [h_bt])
            have h_all_st := h_all_static
            dsimp only [allCallBodiesStaticAdmitted] at h_all_st
            rw [h_any, ite_eq_left rfl, Bool.and_eq_true] at h_all_st
            have h_csat : callBodyStaticAdmitted p calleeBody = true :=
              list_all_mirGetElem? h_all_st.2 h_cb
            unfold callBodyStaticAdmitted singleBodyStaticAdmitted at h_csat
            simp only [Bool.and_eq_true] at h_csat
            let ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, callee_act⟩, _⟩, callee_calls⟩,
              callee_assign⟩ := h_csat
            have h_call_all : allCallBodiesStaticAdmitted p calleeBody = true := by
              dsimp only [allCallBodiesStaticAdmitted]
              cases h_bh : bodyHasAnyCall calleeBody with
              | false => rfl
              | true => rw [callee_assign, h_all_st.2]; rfl
            have h_res := refResolveCalleeBody_crate rp callee calleeRbody
              calleeBody.locals h_rcb (decodeBody_inv h_cbdec).2.1
            exact evalCallTerminator_step_preserves h_dec h_sim hs h_body h_rbody
              h_bb (Or.inl ⟨callee, tgt, uw, h_bt, rfl, rfl⟩) h_cbdec
              (fun _ => h_res) (fun _ h => by cases h)
              (fun _ => h_cb) (fun _ => h_rcb) (fun _ h => by cases h)
              callee_calls h_call_all callee_act h_es'
        | sysrootCall op args dst tgt uw =>
          rw [h_bt] at h_es'; dsimp only at h_es'
          have h_calls_bb := list_all_mirGetElem? h_calls h_bb
          rw [h_bt] at h_calls_bb
          dsimp only [callTargetAdmitted] at h_calls_bb
          simp only [Bool.and_eq_true] at h_calls_bb
          cases h_dl : MirSemantics.getElem? body.locals dst.localId with
          | none =>
            have h_ty := h_calls_bb.1.2
            rw [h_dl] at h_ty; cases h_ty
          | some dstTy =>
            have h_ty := h_calls_bb.1.2
            rw [h_dl] at h_ty
            dsimp only [sysrootNumBody, MirSemantics.getElem?] at h_ty
            rw [Bool.and_eq_true] at h_ty
            have h_dst_eq : dstTy = .int op.width op.signed :=
              MirTy.eq_of_beq h_ty.2
            rw [h_dst_eq] at h_dl
            let ⟨tid, _, h_tmem⟩ := decodeLocalTys_mirGetElem?
              (decodeBody_inv h_bdec).2.1 h_dl
            have h_cbdec := sysrootNumRefBody_decode_of_types rp.types op h_tmem
            have h_res := refResolveCalleeBody_sysroot rp op
            have h_scalls : callsAdmitted p (sysrootNumBody op) = true := by
              cases op with | mk k w s => cases k <;> cases w <;> cases s <;> rfl
            have h_sall : allCallBodiesStaticAdmitted p (sysrootNumBody op) = true := by
              cases op with | mk k w s => cases k <;> cases w <;> cases s <;> rfl
            exact evalCallTerminator_step_preserves h_dec h_sim hs h_body h_rbody
              h_bb (Or.inr ⟨op, tgt, uw, h_bt, rfl, rfl, rfl⟩) h_cbdec
              (fun h => by cases h) (fun op' h => by injection h with ho; subst ho; exact h_res)
              (fun h => by cases h) (fun h => by cases h) (fun _ _ => rfl)
              h_scalls h_sall
              (by cases op with | mk k w s => cases k <;> cases w <;> cases s <;> rfl)
              h_es'
        | return_ =>
          rw [h_bt] at h_es'
          cases callers with
          | nil =>
            dsimp only at h_es'
            cases h_evt : evalTerminator body bb f s.mem s.callerMem
                p.panicStrategy p.hasLocalPanicHandler with
            | fault _ => rw [h_evt] at h_es'; cases h_es'
            | done _ => rw [h_evt] at h_es'; cases h_es'
            | step s₁ =>
              let ⟨f', h_s1_eq, h_def', h_inv', h_pc'⟩ := evalTerminator_step_inv h_inv h_evt
              rw [h_s1_eq] at h_evt
              let ⟨h_sro', h_rdst', h_rtgt'⟩ := evalTerminator_preserves_meta h_evt
              rw [h_evt] at h_es'
              injection h_es' with h_eq; rw [← h_eq]
              exact sameDepth_step_preserves h_dec h_sim hs h_body h_rbody
                h_def' h_sro' h_rdst' h_rtgt' h_inv' h_pc'
          | cons caller rest =>
            dsimp only at h_es'
            exact evalNonRootReturn_step_preserves h_dec h_sim hs h_body h_rbody h_es'
        | goto _ | unreachable | unwindResume | switchInt _ _
        | assert _ _ _ _ _ | coreCall _ _ _ _ _ | callNe _ _ _ _ _ | drop _ _ _ | unsupported =>
          rw [h_bt] at h_es'; dsimp only at h_es'
          cases h_evt : evalTerminator body bb f s.mem s.callerMem
              p.panicStrategy p.hasLocalPanicHandler with
          | fault _ => rw [h_evt, attachCallers_fault_eq_sim] at h_es'; cases h_es'
          | done _ => rw [h_evt, attachCallers_done_eq_sim] at h_es'; cases h_es'
          | step s₁ =>
            rw [h_evt] at h_es'
            rw [attachCallers_step_eq_sim] at h_es'
            injection h_es' with h_s'_eq
            let ⟨f', h_s1_eq, h_def', h_inv', h_pc'⟩ := evalTerminator_step_inv h_inv h_evt
            rw [h_s1_eq] at h_evt
            let ⟨h_sro', h_rdst', h_rtgt'⟩ := evalTerminator_preserves_meta h_evt
            rw [h_s1_eq] at h_s'_eq
            dsimp only [List.cons_append, List.nil_append] at h_s'_eq
            rw [← h_s'_eq]
            exact sameDepth_step_preserves h_dec h_sim hs h_body h_rbody
              h_def' h_sro' h_rdst' h_rtgt' h_inv' h_pc'

private theorem mapStepRes_step {rp : RefProg} {body : Body} {rbody : RefBody}
    {f : FrameState} {rs : RefState} {s' : State}
    {newFrames : Array (Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)}
    {newTopRel? : Option Nat}
    (h_lift : liftStackStep rp body f rs.miri.stack.frames
      (match rs.miri.machine.threads.activeThread? with
       | some th => th.topUserRelevantFrame
       | none => none) s'.frames = some (newFrames, newTopRel?)) :
    mapStepRes rp body rbody f rs (.step s') =
      .step {
        rs with
        miri := mkRefMiriStackState newFrames newTopRel?
          rs.miri.machine.memory
          (nextRefControlForStep body f rs.miri.machine.user.control)
          s'.callerMem
        stepsExecuted := rs.stepsExecuted + 1
      } := by
  cases s' with | mk frames' cm' mem' =>
  dsimp only at h_lift; dsimp only [mapStepRes]
  cases h_th : rs.miri.machine.threads.activeThread? with
  | none => rw [h_th] at h_lift; dsimp only at h_lift; rw [h_lift]
  | some th => rw [h_th] at h_lift; dsimp only at h_lift; rw [h_lift]

theorem nat_blt_eq_true_of_lt {a b : Nat} (h : a < b) : Nat.blt a b = true := by
  rw [Nat.blt_eq]
  exact h

/-- Choice-coupled single-step backward simulation: a running $M_{\text{ref}}$
transition at choice `c` from a simulated state is matched by an
$M_{\text{anneal}}$ transition at the exact same choice `c`. -/
theorem sim_of_refStep_at_choice {rp : RefProg} {p : Program} {s : State}
    {rs rs' : RefState} {c : Choice}
    (h_dec : decodeProg rp = some p)
    (h_sim : SimulationInv rp p s rs)
    (hc : ValidRefChoice rp rs c)
    (h_eval : evalRefStep rp c rs = .running rs') :
    ∃ s' : State,
      ValidChoice p s c ∧
      evalStep p c s = .step s' ∧
      SimulationInv rp p s' rs' := by
  cases h_lt : Nat.blt rs.stepsExecuted rs.maxSteps with
  | false =>
    unfold evalRefStep at h_eval
    rw [h_lt] at h_eval
    cases h_eval
  | true =>
    let ⟨f, callers, body, rbody, hs, hbody, hrbody⟩ :=
      simulationInv_head h_sim
    rw [evalRefStep_eq_base h_dec h_sim hs hbody hrbody h_lt c] at h_eval
    cases h_es : evalStep p c s with
    | done out =>
      rw [h_es] at h_eval
      cases h_eval
    | fault k =>
      rw [h_es] at h_eval
      cases k <;> cases h_eval
    | step s₁ =>
      let ⟨newFrames, newTopRel?, h_lift, h_sim'⟩ :=
        evalStep_step_preserves h_dec h_sim hs hbody hrbody h_es
      rw [h_es, mapStepRes_step h_lift] at h_eval
      dsimp only [stepResultToRefOutcome] at h_eval
      injection h_eval with h_rs'
      subst h_rs'
      exact ⟨s₁, hc, rfl, h_sim'⟩

/-- Backward simulation for one step: a running $M_{\text{ref}}$ transition
from a simulated state is matched by an $M_{\text{anneal}}$ transition that
re-establishes `SimulationInv`. -/
theorem sim_of_refStep_base : SimOfRefStepClaim := by
  intro rp p s rs rs' h_dec h_sim h_rstep
  let ⟨c, hc, h_eval⟩ := h_rstep
  let ⟨s', hc', h_es, h_sim'⟩ := sim_of_refStep_at_choice h_dec h_sim hc h_eval
  exact ⟨s', ⟨c, hc', h_es⟩, h_sim'⟩

/-- Backward simulation: every $M_{\text{ref}}$ state reachable from a
simulated state is simulated by a reachable $M_{\text{anneal}}$ state. -/
theorem sim_of_refReaches_base : SimOfRefReachesClaim := by
  intro rp p s₀ rs₀ rs h_dec h_sim₀ h_reach
  induction h_reach with
  | refl => exact ⟨s₀, Reaches.refl s₀, h_sim₀⟩
  | tail _ h_rstep ih =>
    let ⟨s₂, h_reach₂, h_sim₂⟩ := ih
    let ⟨s₃, h_step, h_sim₃⟩ := sim_of_refStep_base h_dec h_sim₂ h_rstep
    exact ⟨s₃, Reaches.tail h_reach₂ h_step, h_sim₃⟩

/-- Choice-coupled backward reachability simulation. -/
theorem sim_of_refReachesAtChoices {rp : RefProg} {p : Program}
    {s₀ : State} {rs₀ rs : RefState} {cs : List Choice}
    (h_dec : decodeProg rp = some p)
    (h_sim₀ : SimulationInv rp p s₀ rs₀)
    (h_reach : RefReachesAtChoices rp rs₀ cs rs) :
    ∃ s : State, ReachesAtChoices p s₀ cs s ∧ SimulationInv rp p s rs := by
  induction h_reach generalizing s₀ with
  | nil _ => exact ⟨s₀, ReachesAtChoices.nil s₀, h_sim₀⟩
  | cons hc h_eval _ ih =>
    let ⟨s₁, hc', h_es, h_sim₁⟩ :=
      sim_of_refStep_at_choice h_dec h_sim₀ hc h_eval
    let ⟨s₂, h_r₂, h_sim₂⟩ := ih h_sim₁
    exact ⟨s₂, ReachesAtChoices.cons hc' h_es h_r₂, h_sim₂⟩

/-- Choice-coupled single-step forward simulation: while the step budget is not
exhausted, an $M_{\text{anneal}}$ transition at choice `c` from a simulated
state is matched by one running $M_{\text{ref}}$ transition at the exact same
choice `c`. -/
theorem refStep_of_step_at_choice {rp : RefProg} {p : Program} {s s' : State}
    {rs : RefState} {c : Choice}
    (h_dec : decodeProg rp = some p)
    (h_sim : SimulationInv rp p s rs)
    (hc : ValidChoice p s c)
    (h_es : evalStep p c s = .step s')
    (h_lt : Nat.blt rs.stepsExecuted rs.maxSteps = true) :
    ∃ rs' : RefState,
      ValidRefChoice rp rs c ∧
      evalRefStep rp c rs = .running rs' ∧
      SimulationInv rp p s' rs' ∧
      rs'.stepsExecuted = rs.stepsExecuted + 1 ∧
      rs'.maxSteps = rs.maxSteps := by
  let ⟨f, callers, body, rbody, hs, hbody, hrbody⟩ :=
    simulationInv_head h_sim
  have h_ref_eq := evalRefStep_eq_base h_dec h_sim hs hbody hrbody h_lt c
  let ⟨newFrames, newTopRel?, h_lift, h_sim'⟩ :=
    evalStep_step_preserves h_dec h_sim hs hbody hrbody h_es
  rw [h_es, mapStepRes_step h_lift] at h_ref_eq
  dsimp only [stepResultToRefOutcome] at h_ref_eq
  exact ⟨_, hc, h_ref_eq, h_sim', rfl, rfl⟩

/-- Step-indexed reachability in $M_{\text{anneal}}$: `s₂` is reached from `s₁`
in exactly `n` transitions. -/
inductive ReachesN (p : Program) (s₁ : State) : Nat → State → Prop where
  | refl : ReachesN p s₁ 0 s₁
  | tail {n : Nat} {s₂ s₃ : State} :
      ReachesN p s₁ n s₂ →
      Step p s₂ (.step s₃) →
      ReachesN p s₁ (n + 1) s₃

/-- Step-indexed reachability in $M_{\text{ref}}$: `rs₂` is reached from `rs₁`
in exactly `n` `.running` transitions. -/
inductive RefReachesN (rp : RefProg) (rs₁ : RefState) :
    Nat → RefState → Prop where
  | refl : RefReachesN rp rs₁ 0 rs₁
  | tail {n : Nat} {rs₂ rs₃ : RefState} :
      RefReachesN rp rs₁ n rs₂ →
      RefStep rp rs₂ (.running rs₃) →
      RefReachesN rp rs₁ (n + 1) rs₃

theorem exists_reachesN_of_reaches {p : Program} {s₁ s₂ : State}
    (h : Reaches p s₁ s₂) :
    ∃ n : Nat, ReachesN p s₁ n s₂ := by
  induction h with
  | refl => exact ⟨0, ReachesN.refl⟩
  | tail _ h_step ih =>
    let ⟨n, h_in⟩ := ih
    exact ⟨n + 1, ReachesN.tail h_in h_step⟩

theorem refReaches_of_refReachesN {rp : RefProg} {rs₁ rs₂ : RefState}
    {n : Nat} (h : RefReachesN rp rs₁ n rs₂) :
    RefReaches rp rs₁ rs₂ := by
  induction h with
  | refl => exact RefReaches.refl rs₁
  | tail _ h_step ih => exact RefReaches.tail ih h_step

/-- Forward simulation for one step: while the step budget is not exhausted,
an $M_{\text{anneal}}$ transition from a simulated state is matched by one
running $M_{\text{ref}}$ transition that re-establishes `SimulationInv`. -/
theorem refStep_of_step {rp : RefProg} {p : Program} {s s' : State}
    {rs : RefState}
    (h_dec : decodeProg rp = some p)
    (h_sim : SimulationInv rp p s rs)
    (h_step : Step p s (.step s'))
    (h_lt : Nat.blt rs.stepsExecuted rs.maxSteps = true) :
    ∃ rs' : RefState,
      RefStep rp rs (.running rs') ∧
      SimulationInv rp p s' rs' ∧
      rs'.stepsExecuted = rs.stepsExecuted + 1 ∧
      rs'.maxSteps = rs.maxSteps := by
  let ⟨c, hc, h_es⟩ := h_step
  let ⟨rs', hc', h_ev, h_sim', h_st, h_mx⟩ :=
    refStep_of_step_at_choice h_dec h_sim hc h_es h_lt
  exact ⟨rs', ⟨c, hc', h_ev⟩, h_sim', h_st, h_mx⟩

/-- Step-indexed forward simulation: an `n`-step $M_{\text{anneal}}$ execution
from a simulated state is matched by an `n`-step $M_{\text{ref}}$ execution
whenever the reference step budget leaves room for `n` more steps. -/
theorem refReachesN_of_reachesN {rp : RefProg} {p : Program} {n : Nat}
    {s₁ s₂ : State} {rs₁ : RefState}
    (h_dec : decodeProg rp = some p)
    (h_in : ReachesN p s₁ n s₂)
    (h_sim₁ : SimulationInv rp p s₁ rs₁)
    (h_budget : rs₁.stepsExecuted + n ≤ rs₁.maxSteps) :
    ∃ rs₂ : RefState,
      RefReachesN rp rs₁ n rs₂ ∧
      SimulationInv rp p s₂ rs₂ ∧
      rs₂.stepsExecuted = rs₁.stepsExecuted + n ∧
      rs₂.maxSteps = rs₁.maxSteps := by
  induction h_in with
  | refl =>
    exact ⟨rs₁, RefReachesN.refl, h_sim₁, (Nat.add_zero _).symm, rfl⟩
  | @tail m s_mid s_next h_prev h_step ih =>
    have h_b₁ : rs₁.stepsExecuted + m ≤ rs₁.maxSteps :=
      Nat.le_of_succ_le h_budget
    let ⟨rs₂, h_rreach, h_sim₂, h_steps₂, h_max₂⟩ := ih h_b₁
    have h_lt : Nat.blt rs₂.stepsExecuted rs₂.maxSteps = true := by
      apply nat_blt_eq_true_of_lt
      rw [h_steps₂, h_max₂]
      exact h_budget
    let ⟨rs₃, h_rstep, h_sim₃, h_steps₃, h_max₃⟩ :=
      refStep_of_step h_dec h_sim₂ h_step h_lt
    refine ⟨rs₃, RefReachesN.tail h_rreach h_rstep, h_sim₃, ?_, ?_⟩
    · rw [h_steps₃, h_steps₂]
      rfl
    · rw [h_max₃, h_max₂]

/-- Choice-coupled forward reachability simulation. -/
theorem refReachesAtChoices_of_reachesAtChoices {rp : RefProg} {p : Program}
    {cs : List Choice} {s₁ s₂ : State} {rs₁ : RefState}
    (h_dec : decodeProg rp = some p)
    (h_reach : ReachesAtChoices p s₁ cs s₂)
    (h_sim₁ : SimulationInv rp p s₁ rs₁)
    (h_budget : rs₁.stepsExecuted + cs.length ≤ rs₁.maxSteps) :
    ∃ rs₂ : RefState,
      RefReachesAtChoices rp rs₁ cs rs₂ ∧
      SimulationInv rp p s₂ rs₂ ∧
      rs₂.stepsExecuted = rs₁.stepsExecuted + cs.length ∧
      rs₂.maxSteps = rs₁.maxSteps := by
  induction h_reach generalizing rs₁ with
  | nil _ =>
    exact ⟨rs₁, RefReachesAtChoices.nil rs₁, h_sim₁, (Nat.add_zero _).symm, rfl⟩
  | @cons s_a s_b s_c c rest hc h_es _ ih =>
    have h_lt : Nat.blt rs₁.stepsExecuted rs₁.maxSteps = true := by
      apply nat_blt_eq_true_of_lt
      have h_pos : rs₁.stepsExecuted + 1 ≤ rs₁.stepsExecuted + (rest.length + 1) :=
        Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le rest.length)) _
      exact Nat.le_trans h_pos h_budget
    let ⟨rs_b, hc', h_ev, h_sim_b, h_st_b, h_mx_b⟩ :=
      refStep_of_step_at_choice h_dec h_sim₁ hc h_es h_lt
    have h_budget_b : rs_b.stepsExecuted + rest.length ≤ rs_b.maxSteps := by
      rw [h_st_b, h_mx_b, Nat.add_assoc, Nat.add_comm 1 rest.length]
      exact h_budget
    let ⟨rs_c, h_r_c, h_sim_c, h_st_c, h_mx_c⟩ := ih h_sim_b h_budget_b
    refine ⟨rs_c, RefReachesAtChoices.cons hc' h_ev h_r_c, h_sim_c, ?_, ?_⟩
    · rw [h_st_c, h_st_b, Nat.add_assoc, Nat.add_comm 1 rest.length]
      rfl
    · rw [h_mx_c, h_mx_b]

/-! ## Aggregate Well-Formedness, Behavior, Divergence, and Fault Claims -/

/-- UB transfer: if `(p, q)` is well-formed in $M_{\text{anneal}}$, then
`encodeProg p` neither reaches `.ub` nor `.blocked` in $M_{\text{ref}}$ under
any step budget `maxSteps : Nat`. -/
theorem refWellFormed_of_wellFormed_base : RefWellFormedOfWellFormedClaim := by
  intro p q h_wf
  have h_dec : decodeProg (encodeProg p) = some p := decodeProg_encodeProg_base p
  let ⟨⟨s₀, h_init, _⟩, h_no_fault⟩ := h_wf
  intro maxSteps
  let ⟨rs₀, h_rinit, h_sim₀, _, _⟩ :=
    (initRefState_sim_base maxSteps h_dec).2 s₀ h_init
  refine ⟨⟨rs₀, h_rinit, fun _ _ => ⟨0, rfl⟩⟩, ?_, ?_⟩
  · intro h_ub
    unfold RefReachesOutcome at h_ub
    rw [h_rinit] at h_ub
    let ⟨rs, h_rreach, c, hc, h_reval⟩ := h_ub
    let ⟨s, h_reach, h_sim⟩ := sim_of_refReaches_base h_dec h_sim₀ h_rreach
    let ⟨f, callers, body, rbody, hs, hbody, hrbody⟩ :=
      simulationInv_head h_sim
    cases h_lt : Nat.blt rs.stepsExecuted rs.maxSteps with
    | false =>
      unfold evalRefStep at h_reval
      rw [h_lt] at h_reval
      cases h_reval
    | true =>
      rw [evalRefStep_eq_base h_dec h_sim hs hbody hrbody h_lt c] at h_reval
      cases h_es : evalStep p c s with
      | step s' =>
        let ⟨_, _, h_lift, _⟩ :=
          evalStep_step_preserves h_dec h_sim hs hbody hrbody h_es
        rw [h_es, mapStepRes_step h_lift] at h_reval
        cases h_reval
      | done out =>
        rw [h_es] at h_reval
        cases h_reval
      | fault k =>
        rw [h_es] at h_reval
        cases k with
        | unsupported => cases h_reval
        | undefined =>
          apply h_no_fault .undefined
          unfold ReachesResult
          rw [h_init]
          exact ⟨s, h_reach, c, hc, h_es⟩
  · intro h_blk
    unfold RefReachesOutcome at h_blk
    rw [h_rinit] at h_blk
    let ⟨rs, h_rreach, c, hc, h_reval⟩ := h_blk
    let ⟨s, h_reach, h_sim⟩ := sim_of_refReaches_base h_dec h_sim₀ h_rreach
    let ⟨f, callers, body, rbody, hs, hbody, hrbody⟩ :=
      simulationInv_head h_sim
    cases h_lt : Nat.blt rs.stepsExecuted rs.maxSteps with
    | false =>
      unfold evalRefStep at h_reval
      rw [h_lt] at h_reval
      cases h_reval
    | true =>
      rw [evalRefStep_eq_base h_dec h_sim hs hbody hrbody h_lt c] at h_reval
      cases h_es : evalStep p c s with
      | step s' =>
        let ⟨_, _, h_lift, _⟩ :=
          evalStep_step_preserves h_dec h_sim hs hbody hrbody h_es
        rw [h_es, mapStepRes_step h_lift] at h_reval
        cases h_reval
      | done out =>
        rw [h_es] at h_reval
        cases h_reval
      | fault k =>
        rw [h_es] at h_reval
        cases k with
        | undefined => cases h_reval
        | unsupported =>
          apply h_no_fault .unsupported
          unfold ReachesResult
          rw [h_init]
          exact ⟨s, h_reach, c, hc, h_es⟩

/-- Forward behavior transfer: every terminal behavior of `(p, q)` in
$M_{\text{anneal}}$ is a reference behavior of `encodeProg p` (witnessed by
step budget `n + 1` for an `n`-step execution). -/
theorem refBehavior_of_behavior_base : RefBehaviorOfBehaviorClaim := by
  intro p q out h_beh
  have h_dec : decodeProg (encodeProg p) = some p := decodeProg_encodeProg_base p
  unfold Behavior ReachesResult at h_beh
  cases h_init : initState p q with
  | error k =>
    rw [h_init] at h_beh
    cases h_beh
  | ok s₀ =>
    rw [h_init] at h_beh
    let ⟨s_end, h_reach, c, hc, h_es⟩ := h_beh
    let ⟨n, h_in⟩ := exists_reachesN_of_reaches h_reach
    let ⟨rs₀, h_rinit, h_sim₀, h_steps₀, h_max₀⟩ :=
      (initRefState_sim_base (n + 1) h_dec).2 s₀ h_init
    have h_budget : rs₀.stepsExecuted + n ≤ rs₀.maxSteps := by
      rw [h_steps₀, h_max₀, Nat.zero_add]
      exact Nat.le_succ n
    let ⟨rs_end, h_rreach, h_sim_end, h_steps_end, h_max_end⟩ :=
      refReachesN_of_reachesN h_dec h_in h_sim₀ h_budget
    let ⟨f, callers, body, rbody, hs, hbody, hrbody⟩ :=
      simulationInv_head h_sim_end
    have h_lt : Nat.blt rs_end.stepsExecuted rs_end.maxSteps = true := by
      apply nat_blt_eq_true_of_lt
      rw [h_steps_end, h_steps₀, Nat.zero_add, h_max_end, h_max₀]
      exact Nat.lt_succ_self n
    have h_reval := evalRefStep_eq_base h_dec h_sim_end hs hbody hrbody h_lt c
    rw [h_es] at h_reval
    refine ⟨n + 1, ?_⟩
    unfold RefReachesOutcome
    rw [h_rinit]
    exact ⟨rs_end, refReaches_of_refReachesN h_rreach, c, hc, h_reval⟩

/-- Backward behavior transfer: every reference behavior of `encodeProg p` is
a terminal behavior of `(p, q)` in $M_{\text{anneal}}$, so $M_{\text{ref}}$
has no outcomes that $M_{\text{anneal}}$ omits. -/
theorem behavior_of_refBehavior_base : BehaviorOfRefBehaviorClaim := by
  intro p q out h_ref
  have h_dec : decodeProg (encodeProg p) = some p := decodeProg_encodeProg_base p
  let ⟨maxSteps, h_out⟩ := h_ref
  unfold RefReachesOutcome at h_out
  unfold Behavior ReachesResult
  cases h_init : initState p q with
  | error k =>
    rw [(initRefState_sim_base maxSteps h_dec).1 k h_init] at h_out
    cases k <;> cases h_out
  | ok s₀ =>
    let ⟨rs₀, h_rinit, h_sim₀, _, _⟩ :=
      (initRefState_sim_base maxSteps h_dec).2 s₀ h_init
    rw [h_rinit] at h_out
    let ⟨rs, h_rreach, c, hc, h_reval⟩ := h_out
    let ⟨s, h_reach, h_sim⟩ := sim_of_refReaches_base h_dec h_sim₀ h_rreach
    let ⟨f, callers, body, rbody, hs, hbody, hrbody⟩ :=
      simulationInv_head h_sim
    cases h_lt : Nat.blt rs.stepsExecuted rs.maxSteps with
    | false =>
      unfold evalRefStep at h_reval
      rw [h_lt] at h_reval
      cases h_reval
    | true =>
      rw [evalRefStep_eq_base h_dec h_sim hs hbody hrbody h_lt c] at h_reval
      cases h_es : evalStep p c s with
      | step s' =>
        let ⟨_, _, h_lift, _⟩ :=
          evalStep_step_preserves h_dec h_sim hs hbody hrbody h_es
        rw [h_es, mapStepRes_step h_lift] at h_reval
        cases h_reval
      | fault k =>
        rw [h_es] at h_reval
        cases k <;> cases h_reval
      | done out' =>
        rw [h_es] at h_reval
        dsimp only [mapStepRes, stepResultToRefOutcome] at h_reval
        injection h_reval with h_out_eq
        subst h_out_eq
        exact ⟨s, h_reach, c, hc, h_es⟩

/-- Terminal behaviors coincide exactly in $M_{\text{anneal}}$ and
$M_{\text{ref}}$. -/
theorem behavior_iff_refBehavior_base : BehaviorIffRefBehaviorClaim :=
  fun p q out =>
    ⟨refBehavior_of_behavior_base p q out, behavior_of_refBehavior_base p q out⟩

/-- Advance a lifted $M_{\text{ref}}$ trace state across one $M_{\text{anneal}}$
transition `(sPrev → sNext)` while preserving `retPlace`, `memory`, and
advancing `control` via `nextRefControlForStep` at counters `(0, 0)`. -/
noncomputable def stepRefTrace (rp : RefProg) (p : Program)
    (sPrev sNext : State) (rsPrev : RefState) : RefState :=
  match sPrev.frames with
  | fPrev :: _ =>
    match activeFrameBody p fPrev with
    | some body =>
      let ctrl' := nextRefControlForStep body fPrev rsPrev.miri.machine.user.control
      let prevTopRel? :=
        match rsPrev.miri.machine.threads.activeThread? with
        | some th => th.topUserRelevantFrame
        | none => none
      match liftStackStep rp body fPrev rsPrev.miri.stack.frames prevTopRel? sNext.frames with
      | some (newFrames, newTopRel?) =>
        { rsPrev with
          miri := mkRefMiriStackState newFrames newTopRel?
            rsPrev.miri.machine.memory ctrl' sNext.callerMem
          stepsExecuted := 0
          maxSteps := 0 }
      | none => rsPrev
    | none => rsPrev
  | [] => rsPrev

/-- Recursively lift an infinite $M_{\text{anneal}}$ execution trace into a
corresponding $M_{\text{ref}}$ execution trace starting at `rs₀`. -/
noncomputable def liftTrace (rp : RefProg) (p : Program) (rs₀ : RefState)
    (trace : Nat → State) : Nat → RefState
  | 0 => rs₀
  | n + 1 =>
    stepRefTrace rp p (trace n) (trace (n + 1)) (liftTrace rp p rs₀ trace n)

/-- Construct the $M_{\text{anneal}}$ state trace driven deterministically by
an infinite choice stream `choiceStream : Nat → Choice`. -/
noncomputable def traceFromChoices (p : Program) (s₀ : State)
    (choiceStream : Nat → Choice) : Nat → State
  | 0 => s₀
  | n + 1 =>
    match evalStep p (choiceStream n) (traceFromChoices p s₀ choiceStream n) with
    | .step s' => s'
    | _ => s₀

/-- Choice-coupled backward divergence simulation: every infinite
$M_{\text{ref}}$ trace along `choiceStream` is matched by an infinite
$M_{\text{anneal}}$ trace along the exact same `choiceStream`. -/
theorem divergesAtChoices_of_refDivergesAtChoices (p : Program) (q : Query)
    (choiceStream : Nat → Choice)
    (h_rdiv : RefDivergesAtChoices (encodeProg p) q choiceStream) :
    DivergesAtChoices p q choiceStream := by
  have h_dec : decodeProg (encodeProg p) = some p := decodeProg_encodeProg_base p
  let ⟨rs₀, h_rinit, rtrace, h_rt0, h_rstep⟩ := h_rdiv
  cases h_init : initState p q with
  | error k =>
    rw [(initRefState_sim_base 0 h_dec).1 k h_init] at h_rinit
    cases h_rinit
  | ok s₀ =>
    let ⟨rs₀', h_rinit', h_sim₀, _, _⟩ :=
      (initRefState_sim_base 0 h_dec).2 s₀ h_init
    rw [h_rinit'] at h_rinit
    injection h_rinit with h_eq
    subst h_eq
    let tr := traceFromChoices p s₀ choiceStream
    have h_inv : ∀ n : Nat, SimulationInv (encodeProg p) p (tr n) (rtrace n) := by
      intro n
      induction n with
      | zero =>
        dsimp only [tr, traceFromChoices]
        rw [h_rt0]
        exact h_sim₀
      | succ m ih =>
        have h_sim_m := simulationInv_with_counters m (m + 1) ih
        let ⟨hc_m, h_ev_m⟩ := h_rstep m
        let ⟨s', _, h_es_m, h_sim'⟩ :=
          sim_of_refStep_at_choice h_dec h_sim_m hc_m h_ev_m
        have h_tr_next : tr (m + 1) = s' := by
          dsimp only [tr, traceFromChoices]
          rw [h_es_m]
        rw [h_tr_next]
        exact simulationInv_of_with_counters h_sim'
    refine ⟨s₀, h_init, tr, rfl, ?_⟩
    intro n
    have h_sim_n := simulationInv_with_counters n (n + 1) (h_inv n)
    let ⟨hc_n, h_ev_n⟩ := h_rstep n
    let ⟨s', hc_n', h_es_n, _⟩ :=
      sim_of_refStep_at_choice h_dec h_sim_n hc_n h_ev_n
    have h_tr_next : tr (n + 1) = s' := by
      dsimp only [tr, traceFromChoices]
      rw [h_es_n]
    rw [h_tr_next]
    exact ⟨hc_n', h_es_n⟩

/-- Divergence coincides exactly in $M_{\text{anneal}}$ and $M_{\text{ref}}$:
`(p, q)` has an infinite execution trace in $M_{\text{anneal}}$ if and only if
`encodeProg p` has an infinite running execution trace in $M_{\text{ref}}$. -/
theorem diverges_iff_refDiverges_base : DivergesIffRefDivergesClaim := by
  intro p q
  have h_dec : decodeProg (encodeProg p) = some p := decodeProg_encodeProg_base p
  let rp := encodeProg p
  constructor
  · intro h_div
    let ⟨s₀, h_init, trace, h_t0, h_step⟩ := h_div
    let ⟨rs₀, h_rinit, h_sim₀, _, _⟩ :=
      (initRefState_sim_base 0 h_dec).2 s₀ h_init
    let rtrace := liftTrace rp p rs₀ trace
    have h_inv_step : ∀ n : Nat,
        SimulationInv rp p (trace n) (rtrace n) := by
      intro n
      induction n with
      | zero =>
        dsimp only [rtrace, liftTrace]
        rw [h_t0]
        exact h_sim₀
      | succ m ih =>
        let ⟨c, hc, h_es⟩ := h_step m
        let ⟨f, callers, body, rbody, hs, hbody, hrbody⟩ :=
          simulationInv_head ih
        let ⟨newFrames, newTopRel?, h_lift, h_sim'⟩ :=
          evalStep_step_preserves h_dec ih hs hbody hrbody h_es
        have h_next : rtrace (m + 1) =
            { rtrace m with
              miri := mkRefMiriStackState newFrames newTopRel?
                (rtrace m).miri.machine.memory
                (nextRefControlForStep body f (rtrace m).miri.machine.user.control)
                (trace (m + 1)).callerMem
              stepsExecuted := 0
              maxSteps := 0 } := by
          dsimp only [rtrace, liftTrace, stepRefTrace]
          rw [hs]; dsimp only; rw [hbody]; dsimp only
          rw [h_lift]
        rw [h_next]
        exact simulationInv_with_counters 0 0 h_sim'
    refine ⟨rs₀, h_rinit, rtrace, rfl, ?_⟩
    intro n
    have h_sim_n := simulationInv_with_counters n (n + 1) (h_inv_step n)
    have h_lt : Nat.blt n (n + 1) = true :=
      nat_blt_eq_true_of_lt (Nat.lt_succ_self n)
    let ⟨c, hc, h_es⟩ := h_step n
    let ⟨f, callers, body, rbody, hs, hbody, hrbody⟩ :=
      simulationInv_head (h_inv_step n)
    let ⟨newFrames, newTopRel?, h_lift, _⟩ :=
      evalStep_step_preserves h_dec h_sim_n hs hbody hrbody h_es
    have h_ref_eq := evalRefStep_eq_base h_dec h_sim_n hs hbody hrbody h_lt c
    rw [h_es, mapStepRes_step h_lift] at h_ref_eq
    dsimp only [stepResultToRefOutcome] at h_ref_eq
    have h_next_eq :
        { rtrace (n + 1) with stepsExecuted := n + 1, maxSteps := n + 1 } =
        { rtrace n with
          miri := mkRefMiriStackState newFrames newTopRel?
            (rtrace n).miri.machine.memory
            (nextRefControlForStep body f (rtrace n).miri.machine.user.control)
            (trace (n + 1)).callerMem
          stepsExecuted := n + 1
          maxSteps := n + 1 } := by
      dsimp only [rtrace, liftTrace, stepRefTrace]
      rw [hs]; dsimp only; rw [hbody]; dsimp only
      rw [h_lift]
    rw [h_next_eq]
    exact ⟨c, hc, h_ref_eq⟩
  · intro h_rdiv
    let ⟨rs₀, h_rinit, rtrace, h_rt0, h_rstep⟩ := h_rdiv
    have h_rdiv_c : RefDivergesAtChoices (encodeProg p) q (fun _ => 0) := by
      refine ⟨rs₀, h_rinit, rtrace, h_rt0, ?_⟩
      intro n
      let ⟨c, hc, h_ev⟩ := h_rstep n
      have hc0 : c = 0 := hc
      subst hc0
      exact ⟨rfl, h_ev⟩
    let ⟨s₀, h_init, tr, h_t0, h_step⟩ :=
      divergesAtChoices_of_refDivergesAtChoices p q (fun _ => 0) h_rdiv_c
    exact ⟨s₀, h_init, tr, h_t0, fun n => ⟨0, (h_step n).1, (h_step n).2⟩⟩

/-- Main end-to-end operational correspondence theorem: for any
`p : Program` and `q : Query`, if `WellFormed p q` holds in
$M_{\text{anneal}}$, then:
1. `RefWellFormed (encodeProg p) q` holds across all step budgets
   `maxSteps : Nat` in the real `ExecutionMachine.step` reference machine
   $M_{\text{ref}}$;
2. `Behavior p q out` holds in $M_{\text{anneal}}$ exactly when
   `RefBehavior (encodeProg p) q out` holds in $M_{\text{ref}}$; and
3. `(p, q)` diverges in $M_{\text{anneal}}$ exactly when `encodeProg p`
   diverges in $M_{\text{ref}}$. -/
theorem anneal_corresponds_to_miri : CorrespondenceClaim :=
  fun p q h_wf =>
    ⟨refWellFormed_of_wellFormed_base p q h_wf, behavior_iff_refBehavior_base p q,
      diverges_iff_refDiverges_base p q⟩

/-- Bidirectional fault-kind correspondence theorem:
fault kinds `.undefined` and `.unsupported` in $M_{\text{anneal}}$ correspond
one-to-one with `.ub` and `.blocked` in $M_{\text{ref}}$
(`faultToRefOutcome k`). -/
theorem reachesResult_fault_iff_refReachesOutcome :
    FaultEquivalenceClaim := by
  intro p q k
  have h_dec : decodeProg (encodeProg p) = some p := decodeProg_encodeProg_base p
  constructor
  · intro h_res
    unfold ReachesResult at h_res
    cases h_init : initState p q with
    | error k₀ =>
      rw [h_init] at h_res
      injection h_res with h_k
      subst h_k
      refine ⟨0, ?_⟩
      unfold RefReachesOutcome
      rw [(initRefState_sim_base 0 h_dec).1 k h_init]
    | ok s₀ =>
      rw [h_init] at h_res
      let ⟨s_end, h_reach, c, hc, h_es⟩ := h_res
      let ⟨n, h_in⟩ := exists_reachesN_of_reaches h_reach
      let ⟨rs₀, h_rinit, h_sim₀, h_steps₀, h_max₀⟩ :=
        (initRefState_sim_base (n + 1) h_dec).2 s₀ h_init
      have h_budget : rs₀.stepsExecuted + n ≤ rs₀.maxSteps := by
        rw [h_steps₀, h_max₀, Nat.zero_add]
        exact Nat.le_succ n
      let ⟨rs_end, h_rreach, h_sim_end, h_steps_end, h_max_end⟩ :=
        refReachesN_of_reachesN h_dec h_in h_sim₀ h_budget
      let ⟨f, callers, body, rbody, hs, hbody, hrbody⟩ :=
        simulationInv_head h_sim_end
      have h_lt : Nat.blt rs_end.stepsExecuted rs_end.maxSteps = true := by
        apply nat_blt_eq_true_of_lt
        rw [h_steps_end, h_steps₀, Nat.zero_add, h_max_end, h_max₀]
        exact Nat.lt_succ_self n
      have h_reval := evalRefStep_eq_base h_dec h_sim_end hs hbody hrbody h_lt c
      rw [h_es] at h_reval
      refine ⟨n + 1, ?_⟩
      unfold RefReachesOutcome
      rw [h_rinit]
      exact ⟨rs_end, refReaches_of_refReachesN h_rreach, c, hc, h_reval⟩
  · intro h_ex
    let ⟨maxSteps, h_ref⟩ := h_ex
    unfold RefReachesOutcome at h_ref
    cases h_init : initState p q with
    | error k₀ =>
      rw [(initRefState_sim_base maxSteps h_dec).1 k₀ h_init] at h_ref
      unfold ReachesResult
      rw [h_init]
      cases k₀ <;> cases k <;> cases h_ref <;> rfl
    | ok s₀ =>
      let ⟨rs₀, h_rinit, h_sim₀, _, _⟩ :=
        (initRefState_sim_base maxSteps h_dec).2 s₀ h_init
      rw [h_rinit] at h_ref
      let ⟨rs, h_rreach, c, hc, h_reval⟩ := h_ref
      let ⟨s, h_reach, h_sim⟩ := sim_of_refReaches_base h_dec h_sim₀ h_rreach
      let ⟨f, callers, body, rbody, hs, hbody, hrbody⟩ :=
        simulationInv_head h_sim
      cases h_lt : Nat.blt rs.stepsExecuted rs.maxSteps with
      | false =>
        unfold evalRefStep at h_reval
        rw [h_lt] at h_reval
        cases k <;> cases h_reval
      | true =>
        rw [evalRefStep_eq_base h_dec h_sim hs hbody hrbody h_lt c] at h_reval
        cases h_es : evalStep p c s with
        | step s' =>
          let ⟨_, _, h_lift, _⟩ :=
            evalStep_step_preserves h_dec h_sim hs hbody hrbody h_es
          rw [h_es, mapStepRes_step h_lift] at h_reval
          cases k <;> cases h_reval
        | done out =>
          rw [h_es] at h_reval
          cases k <;> cases h_reval
        | fault k₀ =>
          rw [h_es] at h_reval
          have hk_eq : k₀ = k := by
            cases k₀ <;> cases k <;> cases h_reval <;> rfl
          subst hk_eq
          unfold ReachesResult
          rw [h_init]
          exact ⟨s, h_reach, c, hc, h_es⟩

/-! ## Choice-Coupled Correspondence and Fault-Equivalence Claims -/

/-- Unconditional choice-coupled correspondence theorem
(`CorrespondenceAtChoicesClaim`). -/
theorem correspondence_at_choices_claim_holds_base :
    CorrespondenceAtChoicesClaim := by
  intro p q
  have h_dec : decodeProg (encodeProg p) = some p := decodeProg_encodeProg_base p
  refine ⟨refWellFormed_of_wellFormed_base p q, ?_, ?_, ?_⟩
  · intro choices h_pref
    let ⟨maxSteps, rs₀, rs, h_rinit, h_rreach⟩ := h_pref
    cases h_init : initState p q with
    | error k =>
      rw [(initRefState_sim_base maxSteps h_dec).1 k h_init] at h_rinit
      cases h_rinit
    | ok s₀ =>
      let ⟨rs₀', h_rinit', h_sim₀, _, _⟩ :=
        (initRefState_sim_base maxSteps h_dec).2 s₀ h_init
      rw [h_rinit'] at h_rinit
      injection h_rinit with h_eq
      subst h_eq
      let ⟨s, h_reach, _⟩ := sim_of_refReachesAtChoices h_dec h_sim₀ h_rreach
      exact ⟨s₀, s, h_init, h_reach⟩
  · intro choices out h_rbeh
    let ⟨maxSteps, h_out⟩ := h_rbeh
    unfold RefReachesOutcomeAtChoices at h_out
    unfold BehaviorAtChoices ReachesResultAtChoices
    cases h_init : initState p q with
    | error k =>
      rw [(initRefState_sim_base maxSteps h_dec).1 k h_init] at h_out
      cases k <;> cases h_out.2
    | ok s₀ =>
      let ⟨rs₀, h_rinit, h_sim₀, _, _⟩ :=
        (initRefState_sim_base maxSteps h_dec).2 s₀ h_init
      rw [h_rinit] at h_out
      let ⟨prefixChoices, c, rs, h_ceq, h_rreach, hc, h_reval⟩ := h_out
      let ⟨s, h_reach, h_sim⟩ := sim_of_refReachesAtChoices h_dec h_sim₀ h_rreach
      let ⟨f, callers, body, rbody, hs, hbody, hrbody⟩ :=
        simulationInv_head h_sim
      cases h_lt : Nat.blt rs.stepsExecuted rs.maxSteps with
      | false =>
        unfold evalRefStep at h_reval
        rw [h_lt] at h_reval
        cases h_reval
      | true =>
        rw [evalRefStep_eq_base h_dec h_sim hs hbody hrbody h_lt c] at h_reval
        cases h_es : evalStep p c s with
        | step s' =>
          let ⟨_, _, h_lift, _⟩ :=
            evalStep_step_preserves h_dec h_sim hs hbody hrbody h_es
          rw [h_es, mapStepRes_step h_lift] at h_reval
          cases h_reval
        | fault k =>
          rw [h_es] at h_reval
          cases k <;> cases h_reval
        | done out' =>
          rw [h_es] at h_reval
          dsimp only [mapStepRes, stepResultToRefOutcome] at h_reval
          injection h_reval with h_out_eq
          subst h_out_eq
          exact ⟨prefixChoices, c, s, h_ceq, h_reach, hc, h_es⟩
  · intro choiceStream h_rdiv
    exact divergesAtChoices_of_refDivergesAtChoices p q choiceStream h_rdiv

/-- Unconditional choice-coupled bidirectional fault-equivalence theorem
(`FaultEquivalenceAtChoicesClaim`). -/
theorem fault_equivalence_at_choices_claim_holds_base :
    FaultEquivalenceAtChoicesClaim := by
  intro p q choices k
  have h_dec : decodeProg (encodeProg p) = some p := decodeProg_encodeProg_base p
  constructor
  · intro h_res
    unfold ReachesResultAtChoices at h_res
    cases h_init : initState p q with
    | error k₀ =>
      rw [h_init] at h_res
      let ⟨h_ch, h_fk⟩ := h_res
      injection h_fk with h_k
      subst h_k
      refine ⟨0, ?_⟩
      unfold RefReachesOutcomeAtChoices
      rw [(initRefState_sim_base 0 h_dec).1 k h_init]
      exact ⟨h_ch, rfl⟩
    | ok s₀ =>
      rw [h_init] at h_res
      let ⟨prefixChoices, c, s_end, h_ceq, h_reach, hc, h_es⟩ := h_res
      let n := prefixChoices.length
      let ⟨rs₀, h_rinit, h_sim₀, h_steps₀, h_max₀⟩ :=
        (initRefState_sim_base (n + 1) h_dec).2 s₀ h_init
      have h_budget : rs₀.stepsExecuted + prefixChoices.length ≤ rs₀.maxSteps := by
        rw [h_steps₀, h_max₀, Nat.zero_add]
        exact Nat.le_succ n
      let ⟨rs_end, h_rreach, h_sim_end, h_steps_end, h_max_end⟩ :=
        refReachesAtChoices_of_reachesAtChoices h_dec h_reach h_sim₀ h_budget
      let ⟨f, callers, body, rbody, hs, hbody, hrbody⟩ :=
        simulationInv_head h_sim_end
      have h_lt : Nat.blt rs_end.stepsExecuted rs_end.maxSteps = true := by
        apply nat_blt_eq_true_of_lt
        rw [h_steps_end, h_steps₀, Nat.zero_add, h_max_end, h_max₀]
        exact Nat.lt_succ_self n
      have h_reval := evalRefStep_eq_base h_dec h_sim_end hs hbody hrbody h_lt c
      rw [h_es] at h_reval
      refine ⟨n + 1, ?_⟩
      unfold RefReachesOutcomeAtChoices
      rw [h_rinit]
      exact ⟨prefixChoices, c, rs_end, h_ceq, h_rreach, hc, h_reval⟩
  · intro h_ex
    let ⟨maxSteps, h_ref⟩ := h_ex
    unfold RefReachesOutcomeAtChoices at h_ref
    cases h_init : initState p q with
    | error k₀ =>
      rw [(initRefState_sim_base maxSteps h_dec).1 k₀ h_init] at h_ref
      unfold ReachesResultAtChoices
      rw [h_init]
      let ⟨h_ch, h_fk⟩ := h_ref
      have hk_eq : k₀ = k := by
        cases k₀ <;> cases k <;> cases h_fk <;> rfl
      subst hk_eq
      exact ⟨h_ch, rfl⟩
    | ok s₀ =>
      let ⟨rs₀, h_rinit, h_sim₀, _, _⟩ :=
        (initRefState_sim_base maxSteps h_dec).2 s₀ h_init
      rw [h_rinit] at h_ref
      let ⟨prefixChoices, c, rs, h_ceq, h_rreach, hc, h_reval⟩ := h_ref
      let ⟨s, h_reach, h_sim⟩ := sim_of_refReachesAtChoices h_dec h_sim₀ h_rreach
      let ⟨f, callers, body, rbody, hs, hbody, hrbody⟩ :=
        simulationInv_head h_sim
      cases h_lt : Nat.blt rs.stepsExecuted rs.maxSteps with
      | false =>
        unfold evalRefStep at h_reval
        rw [h_lt] at h_reval
        cases k <;> cases h_reval
      | true =>
        rw [evalRefStep_eq_base h_dec h_sim hs hbody hrbody h_lt c] at h_reval
        cases h_es : evalStep p c s with
        | step s' =>
          let ⟨_, _, h_lift, _⟩ :=
            evalStep_step_preserves h_dec h_sim hs hbody hrbody h_es
          rw [h_es, mapStepRes_step h_lift] at h_reval
          cases k <;> cases h_reval
        | done out =>
          rw [h_es] at h_reval
          cases k <;> cases h_reval
        | fault k₀ =>
          rw [h_es] at h_reval
          have hk_eq : k₀ = k := by
            cases k₀ <;> cases k <;> cases h_reval <;> rfl
          subst hk_eq
          unfold ReachesResultAtChoices
          rw [h_init]
          exact ⟨prefixChoices, c, s, h_ceq, h_reach, hc, h_es⟩

/-! ## Vendored `ExecutionMachine` & `OperandMachine` Wiring Claim -/

theorem miri_move_deinit_wiring_claim_holds_base : MiriMoveDeinitWiringClaim := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro K U C O X Host _ cfg limits c state
    rfl
  · intro K U C O X Host _ cfg limits h_true
    refine ⟨?_, ?_⟩ <;>
      change (cfg.deinitMovedPlace || cfg.access.deinitMovedPlace) = true <;>
      rw [h_true] <;> rfl
  · intro K U C hooks c localId known state h_false
    dsimp only [Miri.Interpreter.OperandMachine.evalOperand]
    rw [h_false]
    rfl
  · intro K U C hooks c localId known state state₁ frame₁ frame₂ imm layout
        h_true h_place h_cf h_ne h_rep
    dsimp only [Miri.Interpreter.OperandMachine.evalOperand, bind, Bind.bind,
      pure, Pure.pure]
    rw [h_true]
    change EStateM.bind
      (Miri.Interpreter.OperandMachine.evalPlaceToOp hooks c
        ⟨localId, Array.empty⟩ known) _ state = _
    rw [eStateM_bind_ok h_place]
    change EStateM.bind Miri.Interpreter.MachineHooks.currentFrame _ state₁ = _
    have h_curr : Miri.Interpreter.MachineHooks.currentFrame state₁ =
        .ok frame₁ state₁ := by
      dsimp only [Miri.Interpreter.MachineHooks.currentFrame, bind, Bind.bind,
        EStateM.bind, get, MonadState.get, getThe, MonadStateOf.get, EStateM.get]
      rw [h_cf]
      rfl
    rw [eStateM_bind_ok h_curr, h_rep]
    change (EStateM.bind (EStateM.pure frame₂) _ state₁) = _
    rw [eStateM_bind_pure]
    have h_scf : Miri.Interpreter.MachineHooks.setCurrentFrame frame₂ state₁ =
        .ok () { state₁ with stack := ⟨state₁.stack.frames.pop.push frame₂⟩ } := by
      dsimp only [Miri.Interpreter.MachineHooks.setCurrentFrame, bind, Bind.bind,
        EStateM.bind, get, MonadState.get, getThe, MonadStateOf.get, EStateM.get,
        set, MonadStateOf.set, EStateM.set]
      rw [h_ne]
      rfl
    rw [eStateM_bind_ok h_scf]
    rfl
  · intro Prov Extra State hooks frame state localId known h_false
    dsimp only [Miri.Interpreter.evalOperand]
    rw [h_false]
    rfl
  · intro Prov Extra State hooks frame frame₁ frame₂ state state₁ localId
        known imm layout h_true h_place h_rep
    dsimp only [Miri.Interpreter.evalOperand]
    rw [h_true, h_place]
    dsimp only [Array.isEmpty, Array.size, List.length]
    rw [h_rep]
    rfl
  · intro K U m isMove
    rfl
  · intro P S C E Other Extern FnABI ArgABI h choice place snap
    exact ⟨rfl, rfl⟩

/-- Every non-exhausted `RefStep` transition (`.running` or `.returned`) is
directly witnessed by `RefAllowedStep` (`ExecutionMachine.AllowedStep` at
`refLimits`). -/
theorem refStep_sound_for_allowedStep_base :
    RefStepSoundForAllowedStepClaim := by
  intro rp rs out h_lt h_step
  let ⟨c, h_vc, h_ev⟩ := h_step
  dsimp only [evalRefStep] at h_ev
  rw [h_lt] at h_ev
  change (match Miri.Interpreter.ExecutionMachine.step
      (refExecutionConfig rp) refLimits c rs.miri with
    | (miri', .ok true) =>
      if miri'.stack.frames.isEmpty then
        match refReadReturnVal miri'.machine.memory rs.retTy rs.retPlace with
        | .ok retVal =>
          .returned (.returned ⟨retVal, miri'.machine.user.callerMem⟩)
        | .error k => faultToRefOutcome k
      else
        .running { rs with miri := miri', stepsExecuted := rs.stepsExecuted + 1 }
    | (_, .ok false) => .blocked
    | (miri', .error (.termination (.abort _))) =>
      .returned (.aborted miri'.machine.user.callerMem)
    | (_, .error (.undefinedBehavior _)) => .ub
    | (_, .error (.stack (.localExpectedLive _))) => .ub
    | (_, .error _) => .blocked) = out at h_ev
  cases h_st : Miri.Interpreter.ExecutionMachine.step
      (refExecutionConfig rp) refLimits c rs.miri with
  | mk miri' res =>
    rw [h_st] at h_ev
    cases res with
    | error err =>
      cases err with
      | undefinedBehavior _ =>
        change RefOutcome.ub = out at h_ev
        subst h_ev
        exact ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩
      | termination te =>
        cases te with
        | abort msg =>
          change RefOutcome.returned (.aborted miri'.machine.user.callerMem) = out at h_ev
          subst h_ev
          refine ⟨fun _ h_r => (by cases h_r), fun t h_t => ?_⟩
          injection h_t with h_teq
          exact Or.inr ⟨miri', msg, ⟨refLimits, c, h_vc, h_st⟩, h_teq.symm⟩
        | _ =>
          change RefOutcome.blocked = out at h_ev
          subst h_ev
          exact ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩
      | stack se =>
        cases se with
        | localExpectedLive _ =>
          change RefOutcome.ub = out at h_ev
          subst h_ev
          exact ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩
        | _ =>
          change RefOutcome.blocked = out at h_ev
          subst h_ev
          exact ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩
      | _ =>
        change RefOutcome.blocked = out at h_ev
        subst h_ev
        exact ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩
    | ok cont =>
      cases cont with
      | false =>
        change RefOutcome.blocked = out at h_ev
        subst h_ev
        exact ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩
      | true =>
        change (if miri'.stack.frames.isEmpty then
            match refReadReturnVal miri'.machine.memory rs.retTy rs.retPlace with
            | .ok retVal =>
              .returned (.returned ⟨retVal, miri'.machine.user.callerMem⟩)
            | .error k => faultToRefOutcome k
          else
            .running { rs with miri := miri', stepsExecuted := rs.stepsExecuted + 1 }) = out at h_ev
        cases h_emp : miri'.stack.frames.isEmpty with
        | false =>
          rw [h_emp] at h_ev
          change RefOutcome.running
            { rs with miri := miri', stepsExecuted := rs.stepsExecuted + 1 } = out at h_ev
          subst h_ev
          refine ⟨fun rs' h_r => ?_, fun _ h_t => (by cases h_t)⟩
          injection h_r with h_rs'
          subst h_rs'
          exact ⟨refLimits, c, h_vc, h_st⟩
        | true =>
          rw [h_emp] at h_ev
          change (match refReadReturnVal miri'.machine.memory rs.retTy rs.retPlace with
            | .ok retVal =>
              .returned (.returned ⟨retVal, miri'.machine.user.callerMem⟩)
            | .error k => faultToRefOutcome k) = out at h_ev
          cases h_rv : refReadReturnVal miri'.machine.memory rs.retTy rs.retPlace with
          | error k =>
            rw [h_rv] at h_ev
            cases k with
            | undefined =>
              change RefOutcome.ub = out at h_ev
              subst h_ev
              exact ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩
            | unsupported =>
              change RefOutcome.blocked = out at h_ev
              subst h_ev
              exact ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩
          | ok retVal =>
            rw [h_rv] at h_ev
            change RefOutcome.returned
              (.returned ⟨retVal, miri'.machine.user.callerMem⟩) = out at h_ev
            subst h_ev
            refine ⟨fun _ h_r => (by cases h_r), fun t h_t => by
              injection h_t with h_teq
              exact Or.inl ⟨miri', ⟨refLimits, c, h_vc, h_st⟩, h_emp, retVal, h_rv, h_teq.symm⟩⟩

end Anneal.MirCorrespondence
