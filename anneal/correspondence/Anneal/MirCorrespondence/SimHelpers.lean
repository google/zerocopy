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

namespace Anneal.MirCorrespondence

open Trusted Trusted.MirAst Trusted.MirSemantics Trusted.Correspondence

/-!
# Simulation Invariant and Type-Table Helpers
(`Anneal.MirCorrespondence.SimHelpers`)

Proves canonical `TyId` resolution (`tyIdFor` / `resolveTy` / `canonicalTyId`),
`SlotsMatchTys` and `liftLocals` structural lemmas, `Array` / `MirSemantics`
indexing bridges, `SlotsMatchTys` preservation across `evalOperandToSlot`,
`evalPrimitiveOperand`, `evalRvalue`, and `writePlace`, and right-injectivity
of `SimulationInv` (`refState_unique_of_simulationInv_base`).
-/

/-! ## Generic `MirSemantics.getElem?` / `setElem?` / `Array` Bridges -/

theorem mirGetElem?_lt_of_some {α : Type} {xs : List α} {i : Nat} {x : α}
    (h : MirSemantics.getElem? xs i = some x) : i < xs.length := by
  induction xs generalizing i with
  | nil => cases h
  | cons _ rest ih =>
    cases i with
    | zero => exact Nat.zero_lt_succ rest.length
    | succ j => exact Nat.succ_lt_succ (ih h)

theorem mirGetElem?_none_of_ge {α : Type} {xs : List α} {i : Nat}
    (h : xs.length ≤ i) : MirSemantics.getElem? xs i = none := by
  induction xs generalizing i with
  | nil => rfl
  | cons _ rest ih =>
    cases i with
    | zero => exact False.elim (Nat.not_lt_zero _ h)
    | succ j => exact ih (Nat.le_of_succ_le_succ h)

theorem mirGetElem?_some_of_lt {α : Type} {xs : List α} {i : Nat}
    (h : i < xs.length) : ∃ x : α, MirSemantics.getElem? xs i = some x := by
  induction xs generalizing i with
  | nil => exact False.elim (Nat.not_lt_zero _ h)
  | cons a rest ih =>
    cases i with
    | zero => exact ⟨a, rfl⟩
    | succ j => exact ih (Nat.lt_of_succ_lt_succ h)

theorem mirGetElem?_ge_of_none {α : Type} {xs : List α} {i : Nat}
    (h : MirSemantics.getElem? xs i = none) : xs.length ≤ i := by
  induction xs generalizing i with
  | nil => exact Nat.zero_le i
  | cons _ rest ih =>
    cases i with
    | zero => cases h
    | succ j => exact Nat.succ_le_succ (ih h)

theorem list_all_mirGetElem? {α : Type} {xs : List α} {p : α → Bool}
    {i : Nat} {x : α}
    (h_all : xs.all p = true)
    (h_get : MirSemantics.getElem? xs i = some x) :
    p x = true := by
  induction xs generalizing i with
  | nil => cases h_get
  | cons a rest ih =>
    change (p a && rest.all p) = true at h_all
    cases h_pa : p a <;> rw [h_pa] at h_all
    · cases h_all
    · cases i with
      | zero =>
        injection h_get with h_eq
        subst h_eq
        exact h_pa
      | succ j => exact ih h_all h_get

theorem mirGetElem?_map {α β : Type} (f : α → β) (xs : List α) (i : Nat) :
    MirSemantics.getElem? (xs.map f) i =
      (MirSemantics.getElem? xs i).map f := by
  induction xs generalizing i with
  | nil => rfl
  | cons a rest ih =>
    cases i with
    | zero => rfl
    | succ j => exact ih j

theorem list_get_eq_mirGetElem? {α : Type} (xs : List α) (i : Nat)
    (h : i < xs.length) :
    some (xs.get ⟨i, h⟩) = MirSemantics.getElem? xs i := by
  induction xs generalizing i with
  | nil => exact False.elim (Nat.not_lt_zero _ h)
  | cons _ rest ih =>
    cases i with
    | zero => rfl
    | succ j => exact ih j (Nat.lt_of_succ_lt_succ h)

theorem array_getElem?_eq_mirGetElem? {α : Type} (xs : List α) (i : Nat) :
    (Array.mk xs)[i]? = MirSemantics.getElem? xs i := by
  dsimp only [GetElem?.getElem?, Array.instGetElem?NatLtSize, decidableGetElem?,
    Array.size, GetElem.getElem, Array.instGetElemNatLtSize, Array.getInternal]
  cases h_dec : decide (i < xs.length) with
  | true =>
    have h_lt : i < xs.length := of_decide_eq_true h_dec
    rw [dite_eq_left h_lt]
    exact list_get_eq_mirGetElem? xs i h_lt
  | false =>
    have h_not : ¬ (i < xs.length) := of_decide_eq_false h_dec
    rw [dite_eq_right h_not]
    exact (mirGetElem?_none_of_ge (Nat.le_of_not_lt h_not)).symm

theorem mirSetElem?_eq_list_set {α : Type} (xs : List α) (i : Nat) (v : α)
    (h : i < xs.length) :
    MirSemantics.setElem? xs i v = some (xs.set i v) := by
  induction xs generalizing i with
  | nil => exact False.elim (Nat.not_lt_zero _ h)
  | cons x rest ih =>
    cases i with
    | zero => rfl
    | succ j =>
      dsimp only [MirSemantics.setElem?, List.set]
      rw [ih j (Nat.lt_of_succ_lt_succ h)]

theorem mirSetElem?_some_of_lt {α : Type} (xs : List α) (i : Nat) (v : α)
    (hi : i < xs.length) :
    ∃ xs', MirSemantics.setElem? xs i v = some xs' :=
  ⟨xs.set i v, mirSetElem?_eq_list_set xs i v hi⟩

theorem array_set_eq_mirSetElem? {α : Type} {xs xs' : List α} {i : Nat}
    {v : α} (h_lt : i < (Array.mk xs).size)
    (h_set : MirSemantics.setElem? xs i v = some xs') :
    (Array.mk xs).set i v h_lt = Array.mk xs' := by
  have h1 : MirSemantics.setElem? xs i v = some (xs.set i v) :=
    mirSetElem?_eq_list_set xs i v h_lt
  rw [h1] at h_set
  injection h_set with h_eq
  subst h_eq
  rfl

theorem setElem?_length {α : Type} {xs xs' : List α} {i : Nat} {v : α}
    (h : MirSemantics.setElem? xs i v = some xs') :
    xs'.length = xs.length := by
  induction xs generalizing xs' i with
  | nil => cases h
  | cons x rest ih =>
    cases i with
    | zero =>
      injection h with h_eq
      subst h_eq
      rfl
    | succ j =>
      dsimp only [MirSemantics.setElem?] at h
      cases h_rest : MirSemantics.setElem? rest j v with
      | none => rw [h_rest] at h; cases h
      | some rest' =>
        rw [h_rest] at h
        injection h with h_eq
        subst h_eq
        simp only [List.length_cons, ih h_rest]

theorem getElem?_some_of_length_eq {α β : Type} {xs : List α} {ys : List β}
    {i : Nat} {x : α}
    (h_len : xs.length = ys.length)
    (h_x : MirSemantics.getElem? xs i = some x) :
    ∃ y : β, MirSemantics.getElem? ys i = some y := by
  induction xs generalizing ys i with
  | nil => cases h_x
  | cons a as ih =>
    cases ys with
    | nil => cases h_len
    | cons b bs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h_len
      cases i with
      | zero => exact ⟨b, rfl⟩
      | succ j => exact @ih bs j h_len h_x

/-! ## Shared `EStateM` and Conditional Reduction Lemmas -/

theorem eStateM_bind_ok {ε σ α β : Type} {m : EStateM ε σ α}
    {f : α → EStateM ε σ β} {s s₁ : σ} {a : α}
    (h : m s = .ok a s₁) :
    EStateM.bind m f s = f a s₁ := by
  dsimp only [EStateM.bind]; rw [h]

theorem eStateM_bind_err {ε σ α β : Type} {m : EStateM ε σ α}
    {f : α → EStateM ε σ β} {s s₁ : σ} {e : ε}
    (h : m s = .error e s₁) :
    EStateM.bind m f s = .error e s₁ := by
  dsimp only [EStateM.bind]; rw [h]

theorem eStateM_bind_pure {ε σ α β : Type} (a : α)
    (f : α → EStateM ε σ β) (s : σ) :
    EStateM.bind (EStateM.pure a) f s = f a s := rfl

theorem ite_false_eq {α : Type} (a b : α) :
    (if false = true then a else b) = b := rfl

theorem ite_true_eq {α : Type} (a b : α) :
    (if true = true then a else b) = a := rfl

theorem ite_not_true_eq {α : Type} (a b : α) :
    (if (!true) = true then a else b) = b := rfl

/-! ## Canonical `TyId` Resolution (`tyIdFor`, `resolveTy`, `canonicalTyId`) -/

theorem auxTyOfCode_auxTyCode {ty : MirTy} {code : Nat}
    (h : auxTyCode ty = some code) :
    auxTyOfCode code = some ty := by
  cases ty with
  | bool => injection h with hc; subst hc; rfl
  | unit => injection h with hc; subst hc; rfl
  | int w s =>
    cases w <;> cases s <;> (injection h with hc; subst hc; rfl)
  | never | char | ordering | enum _ | tuple _ | ref _ _ | rawPtr _ _
  | slice _ | array _ _ | rangeTo _ | rangeFrom _ | range _ | option _ | unsupported => cases h

theorem indexOfTy_some_getElem? {ts : List MirTy} {ty : MirTy} {idx : TyId}
    (h : indexOfTy ts ty = some idx) :
    MirSemantics.getElem? ts idx = some ty ∧ idx < ts.length := by
  induction ts generalizing idx with
  | nil => cases h
  | cons t rest ih =>
    dsimp only [indexOfTy] at h
    cases h_eq : MirTy.beq t ty with
    | true =>
      rw [h_eq] at h
      injection h with h_idx
      subst h_idx
      rw [MirTy.eq_of_beq h_eq]
      exact ⟨rfl, Nat.zero_lt_succ rest.length⟩
    | false =>
      rw [h_eq] at h
      cases h_rest : indexOfTy rest ty with
      | none => rw [h_rest] at h; cases h
      | some j =>
        rw [h_rest] at h
        injection h with h_idx
        subst h_idx
        let ⟨h_g, h_lt⟩ := ih h_rest
        exact ⟨h_g, Nat.succ_lt_succ h_lt⟩

theorem indexOfTy_some_of_mirGetElem? {ts : List MirTy} {i : Nat} {ty : MirTy}
    (h : MirSemantics.getElem? ts i = some ty) :
    ∃ idx : TyId, indexOfTy ts ty = some idx := by
  induction ts generalizing i with
  | nil => cases h
  | cons t rest ih =>
    dsimp only [indexOfTy]
    cases h_eq : MirTy.beq t ty with
    | true => exact ⟨0, rfl⟩
    | false =>
      cases i with
      | zero =>
        injection h with h_t
        subst h_t
        rw [MirTy.beq_refl] at h_eq
        cases h_eq
      | succ j =>
        let ⟨idx, h_idx⟩ := ih h
        rw [h_idx]
        exact ⟨idx + 1, rfl⟩

theorem resolveTy_tyIdFor_of_mem {ts : List MirTy} {i : Nat} {ty : MirTy}
    (h : MirSemantics.getElem? ts i = some ty) :
    MirSemantics.getElem? ts (tyIdFor ts ty) = some ty ∧
    resolveTy ts (tyIdFor ts ty) = some ty := by
  let ⟨idx, h_idx⟩ := indexOfTy_some_of_mirGetElem? h
  have h_ty : tyIdFor ts ty = idx := by
    dsimp only [tyIdFor]
    rw [h_idx]
  let ⟨h_g, _⟩ := indexOfTy_some_getElem? h_idx
  rw [h_ty]
  refine ⟨h_g, ?_⟩
  dsimp only [resolveTy]
  rw [h_g]

theorem resolveTy_tyIdFor_of_aux {ts : List MirTy} {ty : MirTy} {code : Nat}
    (h : auxTyCode ty = some code) :
    resolveTy ts (tyIdFor ts ty) = some ty := by
  dsimp only [tyIdFor]
  cases h_idx : indexOfTy ts ty with
  | some idx =>
    let ⟨h_g, _⟩ := indexOfTy_some_getElem? h_idx
    dsimp only [resolveTy]
    rw [h_g]
  | none =>
    rw [h]
    dsimp only [resolveTy]
    have h_le : ts.length ≤ ts.length + code := Nat.le_add_right ts.length code
    rw [mirGetElem?_none_of_ge h_le]
    have h_ble : Nat.ble ts.length (ts.length + code) = true :=
      Nat.ble_eq.mpr h_le
    rw [h_ble, Nat.add_sub_cancel_left]
    exact auxTyOfCode_auxTyCode h

theorem tyIdFor_eq_iff_of_resolve {ts : List MirTy} {ty₁ ty₂ : MirTy}
    (h₁ : resolveTy ts (tyIdFor ts ty₁) = some ty₁)
    (h₂ : resolveTy ts (tyIdFor ts ty₂) = some ty₂) :
    tyIdFor ts ty₁ = tyIdFor ts ty₂ ↔ ty₁ = ty₂ := by
  constructor
  · intro h_eq
    have h_res : some ty₁ = some ty₂ := by
      rw [← h₁, h_eq, h₂]
    injection h_res
  · intro h_eq
    subst h_eq
    rfl

theorem canonicalTyId_of_some {ts : List MirTy} {tyId : TyId} {ty : MirTy}
    (h : MirSemantics.getElem? ts tyId = some ty) :
    canonicalTyId ts tyId = tyIdFor ts ty ∧
    MirSemantics.getElem? ts (canonicalTyId ts tyId) = some ty ∧
    resolveTy ts (canonicalTyId ts tyId) = some ty := by
  have h_c : canonicalTyId ts tyId = tyIdFor ts ty := by
    dsimp only [canonicalTyId]
    rw [h]
  rw [h_c]
  let ⟨h_g, h_r⟩ := resolveTy_tyIdFor_of_mem h
  exact ⟨rfl, h_g, h_r⟩

theorem canonicalTyId_of_none {ts : List MirTy} {tyId : TyId}
    (h : MirSemantics.getElem? ts tyId = none) :
    canonicalTyId ts tyId = tyId ∧
    MirSemantics.getElem? ts (canonicalTyId ts tyId) = none := by
  have h_c : canonicalTyId ts tyId = tyId := by
    dsimp only [canonicalTyId]
    rw [h]
  rw [h_c]
  exact ⟨rfl, h⟩

theorem decodeLocalTys_mirGetElem? {ts : List MirTy} {tids : List TyId}
    {tys : List MirTy} {i : Nat} {ty : MirTy}
    (h_dec : decodeLocalTys ts tids = some tys)
    (h_get : MirSemantics.getElem? tys i = some ty) :
    ∃ tid : TyId,
      MirSemantics.getElem? tids i = some tid ∧
      MirSemantics.getElem? ts tid = some ty := by
  induction tids generalizing tys i with
  | nil =>
    dsimp only [decodeLocalTys, mapOption] at h_dec
    injection h_dec with h_nil
    subst h_nil
    cases h_get
  | cons tid rest ih =>
    dsimp only [decodeLocalTys, mapOption] at h_dec
    cases h_t : MirSemantics.getElem? ts tid with
    | none => rw [h_t] at h_dec; cases h_dec
    | some t =>
      rw [h_t] at h_dec
      cases h_r : mapOption (MirSemantics.getElem? ts) rest with
      | none => rw [h_r] at h_dec; cases h_dec
      | some restTys =>
        rw [h_r] at h_dec
        injection h_dec with h_eq
        subst h_eq
        cases i with
        | zero =>
          injection h_get with h_ty
          subst h_ty
          exact ⟨tid, rfl, h_t⟩
        | succ j => exact ih h_r h_get

theorem decodeBody_local_mem_types {ts : List MirTy} {rbody : RefBody}
    {body : Body} {i : Nat} {ty : MirTy}
    (h_dec : decodeBody ts rbody = some body)
    (h_get : MirSemantics.getElem? body.locals i = some ty) :
    ∃ tid : TyId,
      MirSemantics.getElem? rbody.locals i = some tid ∧
      MirSemantics.getElem? ts tid = some ty := by
  dsimp only [decodeBody] at h_dec
  cases h_locs : decodeLocalTys ts rbody.locals with
  | none => rw [h_locs] at h_dec; cases h_dec
  | some locs =>
    rw [h_locs] at h_dec
    cases h_bbs : mapOption (decodeBasicBlock ts) rbody.basicBlocks with
    | none => rw [h_bbs] at h_dec; cases h_dec
    | some bbs =>
      rw [h_bbs] at h_dec
      injection h_dec with h_b
      subst h_b
      exact decodeLocalTys_mirGetElem? h_locs h_get

theorem refLayoutOfTyId_tyIdFor_of_resolve {ts : List MirTy} {ty : MirTy}
    (h : resolveTy ts (tyIdFor ts ty) = some ty) :
    refLayoutOfTyId ts (tyIdFor ts ty) = .ok (refLocalLayoutForTy ts ty) := by
  dsimp only [refLayoutOfTyId]
  rw [h]

/-- `refHasPadding` succeeds on every canonical $M_{\text{ref}}$ layout. -/
theorem refHasPadding_ok (types : List MirTy) (ty : MirTy) :
    ∃ b, refHasPadding (refLocalLayoutForTy types ty) = .ok b := by
  cases ty with
  | int w s => cases w <;> cases s <;> exact ⟨_, rfl⟩
  | bool | unit | never | char | ordering | ref _ _ | rawPtr _ _
  | slice _ | array _ _ | rangeTo _ | rangeFrom _ | range _ | option _ | unsupported => exact ⟨_, rfl⟩
  | enum ety =>
    dsimp only [refHasPadding, refLocalLayoutForTy, refLayoutDataForTy,
      refAsEnumTy?, refEnumLayoutData]
    cases ety.tagRepr <;> exact ⟨_, rfl⟩
  | tuple fs =>
    cases fs with
    | nil => exact ⟨_, rfl⟩
    | cons f rest =>
      cases rest with
      | nil => cases f <;> exact ⟨_, rfl⟩
      | cons g rest₂ =>
        cases rest₂ with
        | cons _ _ => cases f <;> cases g <;> exact ⟨_, rfl⟩
        | nil =>
          cases f with
          | int w s =>
            cases g with
            | bool => cases w <;> cases s <;> exact ⟨_, rfl⟩
            | _ => exact ⟨_, rfl⟩
          | _ => exact ⟨_, rfl⟩

/-! ## `SlotMatchesTy`, `SlotsMatchTys`, and `liftLocals` Lemmas -/

theorem SlotsMatchTys.length_eq {tys : List MirTy} {slots : List LocalSlot}
    (h : SlotsMatchTys tys slots) : slots.length = tys.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [List.length_cons, ih]

theorem SlotsMatchTys.getElem? {tys : List MirTy} {slots : List LocalSlot}
    {i : Nat} {ty : MirTy} {slot : LocalSlot}
    (h : SlotsMatchTys tys slots)
    (h_ty : MirSemantics.getElem? tys i = some ty)
    (h_sl : MirSemantics.getElem? slots i = some slot) :
    SlotMatchesTy ty slot := by
  induction h generalizing i with
  | nil => cases h_ty
  | cons h_hd _ ih =>
    cases i with
    | zero =>
      injection h_ty with h_t
      injection h_sl with h_s
      subst h_t; subst h_s
      exact h_hd
    | succ j => exact ih h_ty h_sl

theorem SlotsMatchTys.setElem? {tys : List MirTy} {slots slots' : List LocalSlot}
    {i : Nat} {ty : MirTy} {slot' : LocalSlot}
    (h : SlotsMatchTys tys slots)
    (h_ty : MirSemantics.getElem? tys i = some ty)
    (h_match : SlotMatchesTy ty slot')
    (h_set : MirSemantics.setElem? slots i slot' = some slots') :
    SlotsMatchTys tys slots' := by
  induction h generalizing slots' i with
  | nil => cases h_ty
  | cons h_hd h_tl ih =>
    cases i with
    | zero =>
      injection h_ty with h_t
      subst h_t
      injection h_set with h_s
      subst h_s
      exact SlotsMatchTys.cons h_match h_tl
    | succ j =>
      dsimp only [MirSemantics.setElem?] at h_set
      cases h_rest : MirSemantics.setElem? _ j slot' with
      | none => rw [h_rest] at h_set; cases h_set
      | some rest' =>
        rw [h_rest] at h_set
        injection h_set with h_s
        subst h_s
        exact SlotsMatchTys.cons h_hd (ih h_ty h_rest)

private theorem checkVal_of_ty?_some {v : Val} {vTy ty : MirTy}
    (h : v.ty? = some vTy) : checkVal v ty = MirTy.beq vTy ty := by
  change (match v.ty? with | some t => MirTy.beq t ty | none => false) = _
  rw [h]

theorem slotMatchesTy_liveUninitSlot (ty : MirTy) :
    SlotMatchesTy ty (liveUninitSlot ty) := by
  cases ty with
  | unit => rfl
  | bool | int _ _ | never | char | ordering | tuple _ | ref _ _ | rawPtr _ _
  | slice _ | array _ _ | rangeTo _ | rangeFrom _ | range _ | option _ | unsupported =>
    exact ⟨fun h => (by cases h), fun _ h => (by cases h)⟩
  | enum ety =>
    dsimp only [liveUninitSlot]
    cases h_zst : isZstEnumTy ety with
    | false =>
      dsimp only [SlotMatchesTy]
      refine ⟨fun h => (by cases h), fun ety' h_eq => ?_⟩
      injection h_eq with h_e
      subst h_e
      exact h_zst
    | true =>
      dsimp only [isZstEnumTy] at h_zst
      cases h_tr : ety.tagRepr with
      | scalar _ _ => rw [h_tr] at h_zst; cases h_zst
      | zeroSized =>
        rw [h_tr] at h_zst
        have h_adm : enumAdmitted ety = true := h_zst
        dsimp only [enumAdmitted] at h_zst
        rw [h_tr] at h_zst
        cases h_len1 : Nat.beq ety.discriminants.length 1 with
        | false =>
          rw [h_len1] at h_zst
          simp only [Bool.and_false] at h_zst
          cases h_zst
        | true =>
          have h_len_eq : ety.discriminants.length = 1 :=
            Nat.eq_of_beq_eq_true h_len1
          have h_ty : (Val.enumVal ety 0).ty? = some (.enum ety) := by
            dsimp only [Val.ty?]
            rw [h_adm, h_len_eq]
            rfl
          change checkVal (.enumVal ety 0) (.enum ety) = true
          rw [checkVal_of_ty?_some h_ty]
          dsimp only [MirTy.beq]
          exact EnumTy.beq_refl ety

theorem liftLocals_length (types : List MirTy) {bodyLocals : List MirTy}
    {slots : List LocalSlot} (h_len : slots.length = bodyLocals.length) :
    (liftLocals types bodyLocals slots).length = bodyLocals.length := by
  induction bodyLocals generalizing slots with
  | nil => rfl
  | cons _ _ ih =>
    cases slots with
    | nil => cases h_len
    | cons _ _ =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h_len
      dsimp only [liftLocals]
      rw [List.length_cons, List.length_cons, ih h_len]

theorem getElem?_liftLocals_some (types : List MirTy)
    {bodyLocals : List MirTy} {slots : List LocalSlot}
    {i : Nat} {ty : MirTy} {slot : LocalSlot}
    (h_ty : MirSemantics.getElem? bodyLocals i = some ty)
    (h_slot : MirSemantics.getElem? slots i = some slot) :
    MirSemantics.getElem? (liftLocals types bodyLocals slots) i =
      some (refLocalStateOfSlot types ty slot) := by
  induction bodyLocals generalizing slots i with
  | nil => cases h_ty
  | cons t ts ih =>
    cases slots with
    | nil => cases h_slot
    | cons s ss =>
      cases i with
      | zero =>
        injection h_ty with h_t
        injection h_slot with h_s
        subst h_t; subst h_s
        rfl
      | succ j => exact ih h_ty h_slot

theorem getElem?_liftLocals_none_left (types : List MirTy)
    {bodyLocals : List MirTy} {slots : List LocalSlot} {i : Nat}
    (h_ty : MirSemantics.getElem? bodyLocals i = none) :
    MirSemantics.getElem? (liftLocals types bodyLocals slots) i = none := by
  induction bodyLocals generalizing slots i with
  | nil => rfl
  | cons _ _ ih =>
    cases slots with
    | nil => rfl
    | cons _ _ =>
      cases i with
      | zero => cases h_ty
      | succ j => exact ih h_ty

theorem getElem?_liftLocals_none_right (types : List MirTy)
    {bodyLocals : List MirTy} {slots : List LocalSlot} {i : Nat}
    (h_slot : MirSemantics.getElem? slots i = none) :
    MirSemantics.getElem? (liftLocals types bodyLocals slots) i = none := by
  induction bodyLocals generalizing slots i with
  | nil => rfl
  | cons _ _ ih =>
    cases slots with
    | nil => rfl
    | cons _ _ =>
      cases i with
      | zero => cases h_slot
      | succ j => exact ih h_slot

theorem setElem?_liftLocals_some (types : List MirTy)
    {bodyLocals : List MirTy} {slots slots' : List LocalSlot}
    {i : Nat} {ty : MirTy} {slot' : LocalSlot}
    (h_ty : MirSemantics.getElem? bodyLocals i = some ty)
    (h_set : MirSemantics.setElem? slots i slot' = some slots') :
    MirSemantics.setElem? (liftLocals types bodyLocals slots) i
        (refLocalStateOfSlot types ty slot') =
      some (liftLocals types bodyLocals slots') := by
  induction bodyLocals generalizing slots slots' i with
  | nil => cases h_ty
  | cons _ _ ih =>
    cases slots with
    | nil => cases h_set
    | cons _ _ =>
      cases i with
      | zero =>
        injection h_ty with h_t
        injection h_set with h_s
        subst h_t; subst h_s
        rfl
      | succ j =>
        dsimp only [MirSemantics.setElem?] at h_set
        cases h_ss : MirSemantics.setElem? _ j slot' with
        | none => rw [h_ss] at h_set; cases h_set
        | some ss' =>
          rw [h_ss] at h_set
          injection h_set with h_s
          subst h_s
          dsimp only [liftLocals, MirSemantics.setElem?]
          rw [ih h_ty h_ss]

theorem setElem?_liftLocals_none (types : List MirTy)
    {bodyLocals : List MirTy} {slots : List LocalSlot} {i : Nat}
    {rval : Miri.Interpreter.LocalState Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout}
    {slot' : LocalSlot}
    (h_set : MirSemantics.setElem? slots i slot' = none) :
    MirSemantics.setElem? (liftLocals types bodyLocals slots) i rval = none := by
  induction bodyLocals generalizing slots i with
  | nil => rfl
  | cons _ _ ih =>
    cases slots with
    | nil => rfl
    | cons _ _ =>
      cases i with
      | zero => cases h_set
      | succ j =>
        dsimp only [MirSemantics.setElem?] at h_set
        cases h_ss : MirSemantics.setElem? _ j slot' with
        | some _ => rw [h_ss] at h_set; cases h_set
        | none =>
          dsimp only [liftLocals, MirSemantics.setElem?]
          rw [ih h_ss]

theorem liftLocalsCached_length (types : List MirTy) {bodyLocals : List MirTy}
    {slots : List LocalSlot} {cache : List Bool}
    (h_slots : slots.length = bodyLocals.length)
    (h_cache : cache.length = bodyLocals.length) :
    (liftLocalsCached types bodyLocals slots cache).length =
      bodyLocals.length := by
  induction bodyLocals generalizing slots cache with
  | nil => rfl
  | cons _ _ ih =>
    cases slots with
    | nil => cases h_slots
    | cons _ _ =>
      cases cache with
      | nil => cases h_cache
      | cons _ _ =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at h_slots h_cache
        dsimp only [liftLocalsCached]
        rw [List.length_cons, List.length_cons, ih h_slots h_cache]

theorem getElem?_liftLocalsCached_some (types : List MirTy)
    {bodyLocals : List MirTy} {slots : List LocalSlot} {cache : List Bool}
    {i : Nat} {ty : MirTy} {slot : LocalSlot} {b : Bool}
    (h_ty : MirSemantics.getElem? bodyLocals i = some ty)
    (h_slot : MirSemantics.getElem? slots i = some slot)
    (h_b : MirSemantics.getElem? cache i = some b) :
    MirSemantics.getElem? (liftLocalsCached types bodyLocals slots cache) i =
      some (refLocalStateOfSlotWithCache types ty slot b) := by
  induction bodyLocals generalizing slots cache i with
  | nil => cases h_ty
  | cons t ts ih =>
    cases slots with
    | nil => cases h_slot
    | cons s ss =>
      cases cache with
      | nil => cases h_b
      | cons c cs =>
        cases i with
        | zero =>
          injection h_ty with h_t
          injection h_slot with h_s
          injection h_b with h_c
          subst h_t; subst h_s; subst h_c
          rfl
        | succ j => exact ih h_ty h_slot h_b

theorem setElem?_liftLocalsCached_some (types : List MirTy)
    {bodyLocals : List MirTy} {slots slots' : List LocalSlot}
    {cache cache' : List Bool} {i : Nat} {ty : MirTy}
    {slot' : LocalSlot} {b' : Bool}
    (h_ty : MirSemantics.getElem? bodyLocals i = some ty)
    (h_set : MirSemantics.setElem? slots i slot' = some slots')
    (h_setc : MirSemantics.setElem? cache i b' = some cache') :
    MirSemantics.setElem? (liftLocalsCached types bodyLocals slots cache) i
        (refLocalStateOfSlotWithCache types ty slot' b') =
      some (liftLocalsCached types bodyLocals slots' cache') := by
  induction bodyLocals generalizing slots slots' cache cache' i with
  | nil => cases h_ty
  | cons _ _ ih =>
    cases slots with
    | nil => cases h_set
    | cons _ _ =>
      cases cache with
      | nil => cases h_setc
      | cons _ _ =>
        cases i with
        | zero =>
          injection h_ty with h_t
          injection h_set with h_s
          injection h_setc with h_c
          subst h_t; subst h_s; subst h_c
          rfl
        | succ j =>
          dsimp only [MirSemantics.setElem?] at h_set h_setc
          cases h_ss : MirSemantics.setElem? _ j slot' with
          | none => rw [h_ss] at h_set; cases h_set
          | some ss' =>
            cases h_sc : MirSemantics.setElem? _ j b' with
            | none => rw [h_sc] at h_setc; cases h_setc
            | some cc' =>
              rw [h_ss] at h_set
              rw [h_sc] at h_setc
              injection h_set with h_s
              injection h_setc with h_c
              subst h_s; subst h_c
              dsimp only [liftLocalsCached, MirSemantics.setElem?]
              rw [ih h_ty h_ss h_sc]

theorem liftLocalsCached_map_isSome (types : List MirTy)
    {bodyLocals : List MirTy} {slots : List LocalSlot} {cache : List Bool}
    (h_slots : slots.length = bodyLocals.length)
    (h_cache : cache.length = bodyLocals.length) :
    (liftLocalsCached types bodyLocals slots cache).map
        (fun l => l.layout.isSome) = cache := by
  induction bodyLocals generalizing slots cache with
  | nil =>
    cases cache with
    | nil => rfl
    | cons _ _ => cases h_cache
  | cons _ _ ih =>
    cases slots with
    | nil => cases h_slots
    | cons _ _ =>
      cases cache with
      | nil => cases h_cache
      | cons c cs =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at h_slots h_cache
        dsimp only [liftLocalsCached, List.map, refLocalStateOfSlotWithCache]
        cases c with
        | false =>
          rw [Anneal.MirWp.ite_bool_false rfl]
          exact congrArg (false :: ·) (ih h_slots h_cache)
        | true =>
          rw [Anneal.MirWp.ite_bool_true rfl]
          exact congrArg (true :: ·) (ih h_slots h_cache)

theorem liftLocalsCached_replicate_true (types : List MirTy)
    {bodyLocals : List MirTy} {slots : List LocalSlot}
    (h_slots : slots.length = bodyLocals.length) :
    liftLocalsCached types bodyLocals slots
        (List.replicate bodyLocals.length true) =
      liftLocals types bodyLocals slots := by
  induction bodyLocals generalizing slots with
  | nil => rfl
  | cons _ _ ih =>
    cases slots with
    | nil => cases h_slots
    | cons _ _ =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h_slots
      rw [List.length_cons, List.replicate_succ]
      dsimp only [liftLocalsCached, liftLocals,
        refLocalStateOfSlotWithCache, refLocalStateOfSlot]
      rw [Anneal.MirWp.ite_bool_true rfl, ih h_slots]

/-! ## Preservation of `SlotsMatchTys` Across `evalStatement` / `evalRvalue` -/

theorem evalConstLit_checkVal {ty : MirTy} {lit : ConstLit} {v : Val}
    (h : evalConstLit ty lit = .ok v) : checkVal v ty = true := by
  cases ty with
  | unit =>
    cases lit with
    | zeroSized =>
      injection h with hv; subst hv; rfl
    | scalar _ | rodataBytes _ | rodataRef _ _ _ _ => cases h
  | never | tuple _ | ref _ _ | rawPtr _ _ | slice _ | array _ _
  | rangeTo _ | rangeFrom _ | range _ | option _ | unsupported =>
    cases lit <;> cases h
  | int w s =>
    cases lit with
    | zeroSized | rodataBytes _ | rodataRef _ _ _ _ => cases h
    | scalar bits =>
      dsimp only [evalConstLit] at h
      cases h_tr : (truncateBits w bits != bits) with
      | true => rw [h_tr] at h; cases h
      | false =>
        rw [h_tr] at h
        injection h with hv
        subst hv
        cases h_beq : (truncateBits w bits == bits) with
        | true =>
          have h_eq : truncateBits w bits = bits := eq_of_beq h_beq
          have h_wf :
              ({ width := w, signed := s, bits := truncateBits w bits } :
                ScalarVal).wf = true := by
            dsimp only [ScalarVal.wf]
            rw [h_eq]
            exact h_beq
          have h_ty :
              (Val.scalar { width := w, signed := s, bits := truncateBits w bits }).ty? =
                some (.int w s) := by
            dsimp only [Val.ty?]
            rw [h_wf]
            rfl
          rw [checkVal_of_ty?_some h_ty]
          dsimp only [MirTy.beq]
          rw [IntWidth.beq_refl]
          cases s <;> rfl
        | false =>
          dsimp only [bne] at h_tr
          rw [h_beq] at h_tr
          cases h_tr
  | bool =>
    cases lit with
    | zeroSized | rodataBytes _ | rodataRef _ _ _ _ => cases h
    | scalar bits =>
      dsimp only [evalConstLit] at h
      cases h_tr : (truncateBits .i8 bits != bits) with
      | true => rw [h_tr] at h; cases h
      | false =>
        rw [h_tr] at h
        cases h0 : (UInt8.ofNat (truncateBits .i8 bits).toNat == 0) with
        | true =>
          rw [h0] at h; injection h with hv; subst hv; rfl
        | false =>
          rw [h0] at h
          cases h1 : (UInt8.ofNat (truncateBits .i8 bits).toNat == 1) with
          | true =>
            rw [h1] at h; injection h with hv; subst hv; rfl
          | false => rw [h1] at h; cases h
  | char =>
    cases lit with
    | zeroSized | rodataBytes _ | rodataRef _ _ _ _ => cases h
    | scalar bits =>
      dsimp only [evalConstLit] at h
      cases h_tr : (truncateBits .i32 bits != bits) with
      | true => rw [h_tr] at h; cases h
      | false =>
        rw [h_tr] at h
        cases h_u : isUnicodeScalar bits.toNat with
        | false => rw [h_u] at h; cases h
        | true => rw [h_u] at h; injection h with hv; subst hv; rfl
  | ordering =>
    cases lit with
    | zeroSized | rodataBytes _ | rodataRef _ _ _ _ => cases h
    | scalar bits =>
      dsimp only [evalConstLit] at h
      cases h_tr : (truncateBits .i8 bits != bits) with
      | true => rw [h_tr] at h; cases h
      | false =>
        rw [h_tr] at h
        cases h_o : orderingOfTagBits bits.toNat with
        | none => rw [h_o] at h; cases h
        | some o => rw [h_o] at h; injection h with hv; subst hv; rfl
  | enum ety =>
    cases lit with
    | rodataBytes _ | rodataRef _ _ _ _ => cases h
    | zeroSized =>
      dsimp only [evalConstLit] at h
      cases h_zst : isZstEnumTy ety with
      | false => rw [h_zst] at h; cases h
      | true =>
        rw [h_zst] at h
        injection h with hv
        subst hv
        have h_s := slotMatchesTy_liveUninitSlot (.enum ety)
        dsimp only [liveUninitSlot] at h_s
        rw [h_zst] at h_s
        exact h_s
    | scalar bits =>
      dsimp only [evalConstLit] at h
      cases h_tr : ety.tagRepr with
      | zeroSized => rw [h_tr] at h; cases h
      | scalar tagW tagS =>
        rw [h_tr] at h
        dsimp only at h
        cases h_adm : enumAdmitted ety with
        | false => rw [h_adm] at h; cases h
        | true =>
          rw [h_adm] at h
          cases h_ov : (truncateBits tagW bits != bits) with
          | true => rw [h_ov] at h; cases h
          | false =>
            rw [h_ov] at h
            cases h_f : findDiscrVariant?
                (tagBitsToDiscrBits tagW tagS ety.discrWidth bits)
                ety.discriminants with
            | none => rw [h_f] at h; cases h
            | some k =>
              rw [h_f] at h
              injection h with hv
              subst hv
              have h_lt_aux : ∀ idx ds k,
                  findDiscrVariantAux idx
                    (tagBitsToDiscrBits tagW tagS ety.discrWidth bits) ds =
                    some k → k < idx + ds.length := by
                intro idx ds
                induction ds generalizing idx with
                | nil => intro _ hk; cases hk
                | cons d rest ih =>
                  intro k hk
                  dsimp only [findDiscrVariantAux] at hk
                  cases h_eq : (BitVec.ofNat 128 d ==
                      tagBitsToDiscrBits tagW tagS ety.discrWidth bits) with
                  | true =>
                    rw [h_eq] at hk
                    injection hk with hk_eq
                    subst hk_eq
                    exact Nat.lt_add_of_pos_right (Nat.succ_pos rest.length)
                  | false =>
                    rw [h_eq] at hk
                    have h_sub := ih (idx + 1) k hk
                    have h_ar : idx + 1 + rest.length = idx + (rest.length + 1) :=
                      Nat.add_right_comm idx 1 rest.length
                    dsimp only [List.length]
                    rw [← h_ar]
                    exact h_sub
              have h_lt : k < ety.discriminants.length := by
                have h0 := h_lt_aux 0 ety.discriminants k h_f
                rw [Nat.zero_add] at h0
                exact h0
              have h_ty : (Val.enumVal ety k).ty? = some (.enum ety) := by
                dsimp only [Val.ty?]
                rw [h_adm, Nat.blt_eq.mpr h_lt]
                rfl
              rw [checkVal_of_ty?_some h_ty]
              dsimp only [MirTy.beq]
              exact EnumTy.beq_refl ety

/-- `SlotsMatchTys` excludes `.indirect` slots. -/
theorem SlotsMatchTys.not_indirect {tys : List MirTy} {slots : List LocalSlot}
    {i : Nat} {ty : MirTy} {place : MemPlace}
    (h : SlotsMatchTys tys slots)
    (h_ty : MirSemantics.getElem? tys i = some ty)
    (h_sl : MirSemantics.getElem? slots i = some (.indirect place)) : False :=
  SlotsMatchTys.getElem? h h_ty h_sl

/-- `SlotsMatchTys` excludes `.partialTuple` slots, which only Profile v2
creates. -/
theorem SlotsMatchTys.not_partialTuple {tys : List MirTy}
    {slots : List LocalSlot} {i : Nat} {ty : MirTy}
    {fields : List (Option Val)}
    (h : SlotsMatchTys tys slots)
    (h_ty : MirSemantics.getElem? tys i = some ty)
    (h_sl : MirSemantics.getElem? slots i = some (.partialTuple fields)) :
    False :=
  SlotsMatchTys.getElem? h h_ty h_sl
/-- Well-typed frame locals hold no `.indirect` slot. -/
theorem SlotsMatchTys.localsHaveIndirect_false {tys : List MirTy}
    {slots : List LocalSlot} (h : SlotsMatchTys tys slots) :
    localsHaveIndirect slots = false := by
  induction h with
  | nil => rfl
  | @cons _ _ slot _ h_hd _ ih =>
    unfold localsHaveIndirect at ih
    unfold localsHaveIndirect
    cases slot with
    | indirect _ => exact False.elim h_hd
    | dead => exact ih
    | immediate _ => exact ih
    | partialTuple _ => exact ih

theorem evalOperandToSlot_slotsMatchTys {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot} {mem mem' : MemoryState} {op : Operand}
    {tyOk : MirTy → Bool} {ty : MirTy} {optVal : Option Val}
    (h_inv : SlotsMatchTys bodyLocals locals)
    (h : evalOperandToSlot bodyLocals locals mem tyOk op =
      .ok (ty, optVal, locals', mem')) :
    SlotsMatchTys bodyLocals locals' ∧ SlotMatchesTy ty (.immediate optVal) ∧
      mem' = mem := by
  cases op with
  | copy p =>
    dsimp only [evalOperandToSlot] at h
    cases h_ty : MirSemantics.getElem? bodyLocals p.localId with
    | none => rw [h_ty] at h; cases h
    | some ty₀ =>
      rw [h_ty] at h
      cases h_sl : MirSemantics.getElem? locals p.localId with
      | none => rw [h_sl] at h; cases h
      | some slot =>
        rw [h_sl] at h
        cases slot with
        | dead => cases h
        | indirect place =>
          exact False.elim (SlotsMatchTys.not_indirect h_inv h_ty h_sl)
        | partialTuple _ =>
          exact False.elim (SlotsMatchTys.not_partialTuple h_inv h_ty h_sl)
        | immediate opt =>
          cases h_emp : p.projection.isEmpty with
          | false => rw [h_emp] at h; cases h
          | true =>
            rw [h_emp] at h
            injection h with h_tup
            injection h_tup with h_ty_eq h_rest
            injection h_rest with h_opt_eq h_rest₂
            injection h_rest₂ with h_loc_eq h_mem_eq
            subst h_ty_eq; subst h_opt_eq; subst h_loc_eq; subst h_mem_eq
            exact ⟨h_inv, SlotsMatchTys.getElem? h_inv h_ty h_sl, rfl⟩
  | move p =>
    dsimp only [evalOperandToSlot] at h
    cases h_ty : MirSemantics.getElem? bodyLocals p.localId with
    | none => rw [h_ty] at h; cases h
    | some ty₀ =>
      rw [h_ty] at h
      cases h_sl : MirSemantics.getElem? locals p.localId with
      | none => rw [h_sl] at h; cases h
      | some slot =>
        rw [h_sl] at h
        cases slot with
        | dead => cases h
        | indirect place =>
          exact False.elim (SlotsMatchTys.not_indirect h_inv h_ty h_sl)
        | partialTuple _ =>
          exact False.elim (SlotsMatchTys.not_partialTuple h_inv h_ty h_sl)
        | immediate opt =>
          cases h_emp : p.projection.isEmpty with
          | false => rw [h_emp] at h; cases h
          | true =>
            rw [h_emp] at h
            dsimp only at h
            cases h_set :
                MirSemantics.setElem? locals p.localId (liveUninitSlot ty₀) with
            | none => rw [h_set] at h; cases h
            | some locs₁ =>
              rw [h_set] at h
              injection h with h_tup
              injection h_tup with h_ty_eq h_rest
              injection h_rest with h_opt_eq h_rest₂
              injection h_rest₂ with h_loc_eq h_mem_eq
              subst h_ty_eq; subst h_opt_eq; subst h_loc_eq; subst h_mem_eq
              exact ⟨SlotsMatchTys.setElem? h_inv h_ty
                (slotMatchesTy_liveUninitSlot ty₀) h_set,
                SlotsMatchTys.getElem? h_inv h_ty h_sl, rfl⟩
  | constant c =>
    dsimp only [evalOperandToSlot] at h
    cases h_lit : evalConstLit c.ty c.lit with
    | error _ => rw [h_lit] at h; cases h
    | ok v =>
      rw [h_lit] at h
      injection h with h_tup
      injection h_tup with h_ty_eq h_rest
      injection h_rest with h_opt_eq h_rest₂
      injection h_rest₂ with h_loc_eq h_mem_eq
      subst h_ty_eq; subst h_opt_eq; subst h_loc_eq; subst h_mem_eq
      exact ⟨h_inv, evalConstLit_checkVal h_lit, rfl⟩

theorem evalPrimitiveOperand_slotsMatchTys {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot} {mem mem' : MemoryState}
    {opnd : Operand} {v : Val}
    (h_inv : SlotsMatchTys bodyLocals locals)
    (h : evalPrimitiveOperand bodyLocals locals mem opnd =
      .ok (v, locals', mem')) :
    SlotsMatchTys bodyLocals locals' ∧ mem' = mem := by
  unfold evalPrimitiveOperand at h
  cases h_op : evalOperandToSlot bodyLocals locals mem isPrimitiveReadableTy
      opnd with
  | error _ => rw [h_op] at h; cases h
  | ok res =>
    let ⟨ty, optVal, l₁, m₁⟩ := res
    rw [h_op] at h
    dsimp only at h
    cases h_pr : isPrimitiveReadableTy ty with
    | false => rw [h_pr] at h; cases h
    | true =>
      rw [h_pr] at h
      cases optVal with
      | none => cases h
      | some v₀ =>
        injection h with h_tup
        injection h_tup with _ h_rest
        injection h_rest with h_loc h_mem
        subst h_loc; subst h_mem
        let ⟨h_l, _, h_m⟩ := evalOperandToSlot_slotsMatchTys h_inv h_op
        exact ⟨h_l, h_m⟩

/-- `evalDiscriminantOfVal` leaves `locals` and `mem` unchanged. -/
theorem evalDiscriminantOfVal_ok {ety : EnumTy} {optVal : Option Val}
    {locals locals' : List LocalSlot} {mem mem' : MemoryState} {v : Val}
    (h : evalDiscriminantOfVal ety optVal locals mem = .ok (v, locals', mem')) :
    locals' = locals ∧ mem' = mem := by
  unfold evalDiscriminantOfVal at h
  cases h_adm : enumAdmitted ety with
  | false => rw [h_adm] at h; cases h
  | true =>
    rw [h_adm] at h
    cases h_tr : ety.tagRepr with
    | zeroSized =>
      rw [h_tr] at h
      cases optVal with
      | none =>
        dsimp only at h
        cases h_d : MirSemantics.getElem? ety.discriminants 0 with
        | none => rw [h_d] at h; cases h
        | some _ =>
          rw [h_d] at h
          injection h with h_tup
          injection h_tup with _ h_rest
          injection h_rest with h_l h_m
          exact ⟨h_l.symm, h_m.symm⟩
      | some val =>
        cases val with
        | enumVal ety' idx =>
          dsimp only at h
          cases h_chk : (EnumTy.beq ety ety' && Nat.beq idx 0) with
          | false => rw [h_chk] at h; cases h
          | true =>
            rw [h_chk] at h
            cases h_d : MirSemantics.getElem? ety.discriminants 0 with
            | none => rw [h_d] at h; cases h
            | some _ =>
              rw [h_d] at h
              injection h with h_tup
              injection h_tup with _ h_rest
              injection h_rest with h_l h_m
              exact ⟨h_l.symm, h_m.symm⟩
        | _ => cases h
    | scalar _ _ =>
      rw [h_tr] at h
      cases optVal with
      | none => cases h
      | some val =>
        cases val with
        | enumVal ety' idx =>
          dsimp only at h
          cases h_chk :
              (EnumTy.beq ety ety' && Nat.blt idx ety.discriminants.length) with
          | false => rw [h_chk] at h; cases h
          | true =>
            rw [h_chk] at h
            cases h_d : MirSemantics.getElem? ety.discriminants idx with
            | none => rw [h_d] at h; cases h
            | some _ =>
              rw [h_d] at h
              injection h with h_tup
              injection h_tup with _ h_rest
              injection h_rest with h_l h_m
              exact ⟨h_l.symm, h_m.symm⟩
        | _ => cases h

/-- `evalOrderingDiscriminantOfVal` leaves `locals` and `mem` unchanged. -/
theorem evalOrderingDiscriminantOfVal_ok {optVal : Option Val}
    {locals locals' : List LocalSlot} {mem mem' : MemoryState} {v : Val}
    (h : evalOrderingDiscriminantOfVal optVal locals mem =
      .ok (v, locals', mem')) :
    locals' = locals ∧ mem' = mem := by
  unfold evalOrderingDiscriminantOfVal at h
  cases optVal with
  | none => cases h
  | some val =>
    cases val with
    | ordering _ =>
      injection h with h_tup
      injection h_tup with _ h_rest
      injection h_rest with h_l h_m
      exact ⟨h_l.symm, h_m.symm⟩
    | _ => cases h

theorem evalRvalue_slotsMatchTys {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot} {mem mem' : MemoryState}
    {dstTy : MirTy} {rv : Rvalue} {v : Val}
    (h_inv : SlotsMatchTys bodyLocals locals)
    (h : evalRvalue bodyLocals locals mem dstTy rv = .ok (v, locals', mem')) :
    SlotsMatchTys bodyLocals locals' ∧ mem' = mem := by
  cases rv with
  | use opnd =>
    dsimp only [evalRvalue] at h
    cases h_op : evalOperandToSlot bodyLocals locals mem
        (fun srcTy => MirTy.beq srcTy dstTy) opnd with
    | error _ => rw [h_op] at h; cases h
    | ok res =>
      let ⟨srcTy, optVal, l₁, m₁⟩ := res
      rw [h_op] at h
      dsimp only at h
      cases h_eq_ty : MirTy.beq srcTy dstTy with
      | false => rw [h_eq_ty] at h; cases h
      | true =>
        rw [h_eq_ty] at h
        cases optVal with
        | none => cases h
        | some v₀ =>
          injection h with h_tup
          injection h_tup with _ h_rest
          injection h_rest with h_loc h_mem
          subst h_loc; subst h_mem
          let ⟨h_l, _, h_m⟩ := evalOperandToSlot_slotsMatchTys h_inv h_op
          exact ⟨h_l, h_m⟩
  | binaryOp op lhs rhs =>
    dsimp only [evalRvalue] at h
    cases h_l : evalPrimitiveOperand bodyLocals locals mem lhs with
    | error _ => rw [h_l] at h; cases h
    | ok resL =>
      let ⟨lVal, l₁, m₁⟩ := resL
      rw [h_l] at h
      dsimp only at h
      cases h_r : evalPrimitiveOperand bodyLocals l₁ m₁ rhs with
      | error _ => rw [h_r] at h; cases h
      | ok resR =>
        let ⟨rVal, l₂, m₂⟩ := resR
        rw [h_r] at h
        dsimp only at h
        cases h_b : evalBinOp op lVal rVal with
        | error _ => rw [h_b] at h; cases h
        | ok _ =>
          rw [h_b] at h
          injection h with h_tup
          injection h_tup with _ h_rest
          injection h_rest with h_loc h_mem
          subst h_loc; subst h_mem
          let ⟨h_l₁, h_m₁⟩ := evalPrimitiveOperand_slotsMatchTys h_inv h_l
          let ⟨h_l₂, h_m₂⟩ := evalPrimitiveOperand_slotsMatchTys h_l₁ h_r
          exact ⟨h_l₂, h_m₂.trans h_m₁⟩
  | unaryOp op opnd =>
    dsimp only [evalRvalue] at h
    cases h_op : evalPrimitiveOperand bodyLocals locals mem opnd with
    | error _ => rw [h_op] at h; cases h
    | ok res =>
      let ⟨v₀, l₁, m₁⟩ := res
      rw [h_op] at h
      dsimp only at h
      cases h_u : evalUnOp op v₀ with
      | error _ => rw [h_u] at h; cases h
      | ok _ =>
        rw [h_u] at h
        injection h with h_tup
        injection h_tup with _ h_rest
        injection h_rest with h_loc h_mem
        subst h_loc; subst h_mem
        exact evalPrimitiveOperand_slotsMatchTys h_inv h_op
  | cast k opnd castTy =>
    cases k with
    | unsupported | ptrToPtr | intToPtr | unsize => cases h
    | intToInt =>
      dsimp only [evalRvalue] at h
      cases h_op : evalOperandToSlot bodyLocals locals mem isIntLikeTy opnd with
      | error _ => rw [h_op] at h; cases h
      | ok res =>
        let ⟨srcTy, optVal, l₁, m₁⟩ := res
        rw [h_op] at h
        dsimp only at h
        cases h_il : isIntLikeTy srcTy with
        | false => rw [h_il] at h; cases h
        | true =>
          rw [h_il] at h
          cases optVal with
          | none => cases h
          | some v₀ =>
            dsimp only at h
            cases h_c : evalIntToIntCast v₀ castTy with
            | error _ => rw [h_c] at h; cases h
            | ok _ =>
              rw [h_c] at h
              injection h with h_tup
              injection h_tup with _ h_rest
              injection h_rest with h_loc h_mem
              subst h_loc; subst h_mem
              let ⟨h_l, _, h_m⟩ := evalOperandToSlot_slotsMatchTys h_inv h_op
              exact ⟨h_l, h_m⟩
  | discriminant place =>
    dsimp only [evalRvalue] at h
    cases h_ty : MirSemantics.getElem? bodyLocals place.localId with
    | none => rw [h_ty] at h; cases h
    | some ty =>
      rw [h_ty] at h
      cases h_sl : MirSemantics.getElem? locals place.localId with
      | none => rw [h_sl] at h; cases h
      | some slot =>
        rw [h_sl] at h
        cases slot with
        | dead => cases h
        | indirect place' =>
          exact False.elim (SlotsMatchTys.not_indirect h_inv h_ty h_sl)
        | partialTuple _ =>
          exact False.elim (SlotsMatchTys.not_partialTuple h_inv h_ty h_sl)
        | immediate opt =>
          cases h_emp : place.projection.isEmpty with
          | false => rw [h_emp] at h; cases h
          | true =>
            rw [h_emp] at h
            cases ty with
            | enum ety =>
              dsimp only at h
              let ⟨h_l, h_m⟩ := evalDiscriminantOfVal_ok h
              subst h_l; subst h_m
              exact ⟨h_inv, rfl⟩
            | ordering =>
              dsimp only at h
              let ⟨h_l, h_m⟩ := evalOrderingDiscriminantOfVal_ok h
              subst h_l; subst h_m
              exact ⟨h_inv, rfl⟩
            | _ => cases h
  | useRetag _ | ref _ _ | addressOf _ _ | fakeAddressOf _ | aggregateTuple _
  | aggregateArray _ _ | repeat_ _ _ _
  | aggregateRangeTo _ _ | aggregateRangeFrom _ _
  | aggregateRange _ _ _ | aggregateOption _ _ _ | unsupported => cases h

theorem writePlace_slotsMatchTys {bodyLocals : List MirTy}
    {locals locals' : List LocalSlot} {mem mem' : MemoryState}
    {dstLocalId : LocalId} {dstTy : MirTy} {val : Val}
    (h_inv : SlotsMatchTys bodyLocals locals)
    (h_ty : MirSemantics.getElem? bodyLocals dstLocalId = some dstTy)
    (h : writePlace locals mem dstLocalId dstTy val = .ok (locals', mem')) :
    SlotsMatchTys bodyLocals locals' ∧ mem' = mem := by
  unfold writePlace at h
  cases h_chk : checkVal val dstTy with
  | false => rw [h_chk] at h; cases h
  | true =>
    rw [h_chk] at h
    cases h_get : MirSemantics.getElem? locals dstLocalId with
    | none => rw [h_get] at h; cases h
    | some slot =>
      rw [h_get] at h
      cases slot with
      | dead => cases h
      | indirect place =>
        exact False.elim (SlotsMatchTys.not_indirect h_inv h_ty h_get)
      | partialTuple _ =>
        exact False.elim (SlotsMatchTys.not_partialTuple h_inv h_ty h_get)
      | immediate _ =>
        dsimp only at h
        cases h_set :
            MirSemantics.setElem? locals dstLocalId (.immediate (some val)) with
        | none => rw [h_set] at h; cases h
        | some locs' =>
          rw [h_set] at h
          injection h with h_eq
          injection h_eq with h_loc h_mem
          subst h_loc; subst h_mem
          exact ⟨SlotsMatchTys.setElem? (slot' := .immediate (some val))
            h_inv h_ty h_chk h_set, rfl⟩

theorem decodePlace_inv {ts : List MirTy} {rp : RefPlace} {p : Place}
    (h : decodePlace ts rp = some p) :
    rp.localId = p.localId ∧ rp.projection.isEmpty = p.projection.isEmpty := by
  dsimp only [decodePlace] at h
  cases h_proj : mapOption (decodeProjElem ts) rp.projection with
  | none => rw [h_proj] at h; cases h
  | some proj =>
    rw [h_proj] at h
    injection h with h_eq
    subst h_eq
    exact ⟨rfl, mapOption_isEmpty h_proj⟩

/-! ## Right-Injectivity of `SimulationInv` -/

theorem slotsMatchTys_length {tys : List MirTy} {slots : List LocalSlot}
    (h : SlotsMatchTys tys slots) : slots.length = tys.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [List.length_cons, ih]

private theorem topRel_eq_of_mkRefMiriStackState_threads
    {f₁ f₂ : Array (Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)}
    {t₁ t₂ : Option Nat}
    {m₁ m₂ : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit}
    {c₁ c₂ : Miri.Interpreter.TerminatorMachine.Control Unit}
    {cm₁ cm₂ : CallerMemory}
    (h : (mkRefMiriStackState f₁ t₁ m₁ c₁ cm₁).machine.threads =
      (mkRefMiriStackState f₂ t₂ m₂ c₂ cm₂).machine.threads) :
    t₁ = t₂ := by
  have h_act := congrArg (fun (tm : Miri.Concurrency.ThreadManager) =>
    Miri.Concurrency.ThreadManager.activeThread? tm) h
  dsimp only [mkRefMiriStackState] at h_act
  have h_sub : (Miri.Concurrency.ThreadManager.activeThread? {
      Miri.Concurrency.ThreadManager.initial true with
      threads := (Miri.Concurrency.ThreadManager.initial true).threads.mapIdx
        fun index thread =>
          if index == (Miri.Concurrency.ThreadManager.initial true).activeThread.toNat then
            { thread with topUserRelevantFrame := t₁ }
          else thread
    }).map (·.topUserRelevantFrame) = some t₁ := by
    rfl
  have h_sub₂ : (Miri.Concurrency.ThreadManager.activeThread? {
      Miri.Concurrency.ThreadManager.initial true with
      threads := (Miri.Concurrency.ThreadManager.initial true).threads.mapIdx
        fun index thread =>
          if index == (Miri.Concurrency.ThreadManager.initial true).activeThread.toNat then
            { thread with topUserRelevantFrame := t₂ }
          else thread
    }).map (·.topUserRelevantFrame) = some t₂ := by
    rfl
  have h_map := congrArg (Option.map (fun th => th.topUserRelevantFrame)) h_act
  rw [h_sub, h_sub₂] at h_map
  exact Option.some.inj h_map

private theorem frameSimInv_unique {rp : RefProg} {p : Program} {f : FrameState}
    {retPlace : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance}
    {rf₁ rf₂ : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra}
    (h₁ : FrameSimInv rp p f retPlace rf₁)
    (h₂ : FrameSimInv rp p f retPlace rf₂)
    (h_lay : rf₁.locals.map (fun l => l.layout.isSome) =
      rf₂.locals.map (fun l => l.layout.isSome)) :
    rf₁ = rf₂ := by
  let ⟨body₁, rbody₁, c₁, hb₁, hrb₁, _, _, _, _, _, _, _, _, _, hsm₁, _, hc₁_rep, hrf₁⟩ := h₁
  let ⟨body₂, rbody₂, c₂, hb₂, hrb₂, _, _, _, _, _, _, _, _, _, hsm₂, _, hc₂_rep, hrf₂⟩ := h₂
  have hc₁ : c₁.length = body₁.locals.length := by rw [hc₁_rep, List.length_replicate]
  have hc₂ : c₂.length = body₂.locals.length := by rw [hc₂_rep, List.length_replicate]
  rw [hb₁] at hb₂; injection hb₂ with hb_eq; subst hb_eq
  rw [hrb₁] at hrb₂; injection hrb₂ with hrb_eq; subst hrb_eq
  rw [hrf₁, hrf₂] at h_lay
  have h_list_lay := congrArg Array.toList h_lay
  rw [Array.toList_map, Array.toList_map] at h_list_lay
  dsimp only [mkRefMiriFrame] at h_list_lay
  change (liftLocalsCached rp.types body₁.locals f.locals c₁).map
      (fun l => l.layout.isSome) =
    (liftLocalsCached rp.types body₁.locals f.locals c₂).map
      (fun l => l.layout.isSome) at h_list_lay
  rw [liftLocalsCached_map_isSome rp.types (slotsMatchTys_length hsm₁) hc₁,
    liftLocalsCached_map_isSome rp.types (slotsMatchTys_length hsm₂) hc₂] at h_list_lay
  subst h_list_lay
  rw [hrf₁, hrf₂]

private theorem callFrameSimInv_unique {rp : RefProg} {p : Program}
    {f : FrameState} {callerIdx : Nat} {dstLocalId : LocalId} {dstTy : MirTy}
    {rf₁ rf₂ : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra}
    (h₁ : CallFrameSimInv rp p f callerIdx dstLocalId dstTy rf₁)
    (h₂ : CallFrameSimInv rp p f callerIdx dstLocalId dstTy rf₂)
    (h_lay : rf₁.locals.map (fun l => l.layout.isSome) =
      rf₂.locals.map (fun l => l.layout.isSome)) :
    rf₁ = rf₂ := by
  let ⟨body₁, rbody₁, c₁, fnTag₁, hb₁, hrb₁, _, hft₁, _, _, _, _, _, _, _, _, _, _, _,
    hsm₁, _, hc₁, hrf₁⟩ := h₁
  let ⟨body₂, rbody₂, c₂, fnTag₂, hb₂, hrb₂, _, hft₂, _, _, _, _, _, _, _, _, _, _, _,
    hsm₂, _, hc₂, hrf₂⟩ := h₂
  rw [hb₁] at hb₂; injection hb₂ with hb_eq; subst hb_eq
  rw [hrb₁] at hrb₂; injection hrb₂ with hrb_eq; subst hrb_eq
  have hft_eq : fnTag₁ = fnTag₂ := hft₁.trans hft₂.symm
  subst hft_eq
  rw [hrf₁, hrf₂] at h_lay
  have h_list_lay := congrArg Array.toList h_lay
  rw [Array.toList_map, Array.toList_map] at h_list_lay
  dsimp only [mkRefMiriCallFrame] at h_list_lay
  change (liftLocalsCached rp.types body₁.locals f.locals c₁).map
      (fun l => l.layout.isSome) =
    (liftLocalsCached rp.types body₁.locals f.locals c₂).map
      (fun l => l.layout.isSome) at h_list_lay
  rw [liftLocalsCached_map_isSome rp.types (slotsMatchTys_length hsm₁) hc₁,
    liftLocalsCached_map_isSome rp.types (slotsMatchTys_length hsm₂) hc₂] at h_list_lay
  subst h_list_lay
  rw [hrf₁, hrf₂]

private theorem framesSimInv_unique {rp : RefProg} {p : Program}
    {retPlace : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance}
    {fs : List FrameState}
    {rfs₁ rfs₂ : List (Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)}
    (h₁ : FramesSimInv rp p retPlace fs rfs₁)
    (h₂ : FramesSimInv rp p retPlace fs rfs₂)
    (h_lay : rfs₁.map (fun fr => fr.locals.map (fun l => l.layout.isSome)) =
      rfs₂.map (fun fr => fr.locals.map (fun l => l.layout.isSome))) :
    rfs₁ = rfs₂ := by
  induction h₁ generalizing rfs₂ with
  | root _ _ _ _ hf₁ =>
    cases h₂ with
    | root _ _ _ _ hf₂ =>
      dsimp only [List.map] at h_lay
      injection h_lay with h_l _
      exact congrArg (fun r => [r]) (frameSimInv_unique hf₁ hf₂ h_l)
  | push hp₁ hcb₁ _ hdst₁ _ hdty₁ _ _ _ _ _ hcf₁ ih =>
    cases h₂ with
    | push hp₂ hcb₂ _ hdst₂ _ hdty₂ _ _ _ _ _ hcf₂ =>
      dsimp only [List.map] at h_lay
      injection h_lay with h_top_lay h_rest_lay
      have h_rest_eq := ih hp₂ h_rest_lay
      rw [hcb₁] at hcb₂; injection hcb₂ with h_cb_eq; subst h_cb_eq
      rw [hdst₁] at hdst₂; injection hdst₂ with h_d_eq; subst h_d_eq
      rw [hdty₁] at hdty₂; injection hdty₂ with h_dt_eq; subst h_dt_eq
      have h_top_eq := callFrameSimInv_unique hcf₁ hcf₂ h_top_lay
      rw [h_top_eq, h_rest_eq]

/-- One-to-one uniqueness of `SimulationInv` (right-injective at fixed step
counters, terminator control, thread state, and local layout cache bits): any
$M_{\text{anneal}}$ `State` `s` together with those observations uniquely
determines `rs`. -/
theorem refState_unique_of_simulationInv_base :
    RefStateUniqueOfSimulationInvClaim := by
  intro rp p s rs₁ rs₂ h₁ h₂ h_steps h_max h_ctrl h_threads h_layouts
  let ⟨rf₁, retTy₁, mem₁, ctrl₁, topRel₁?, _, _, _, heret₁, hret₁, hinit₁, _, _,
    hmiri₁, hframe₁⟩ := h₁
  let ⟨rf₂, retTy₂, mem₂, ctrl₂, topRel₂?, _, _, _, heret₂, hret₂, hinit₂, _, _,
    hmiri₂, hframe₂⟩ := h₂
  rw [heret₁] at heret₂
  injection heret₂ with h_rty_eq
  subst h_rty_eq
  have h_rty : rs₁.retTy = rs₂.retTy := hret₁.trans hret₂.symm
  rw [hinit₁] at hinit₂
  injection hinit₂ with h_pair
  injection h_pair with h_mem_eq h_rp_eq
  subst h_mem_eq
  have h_ctrl_eq : ctrl₁ = ctrl₂ := by
    rw [hmiri₁, hmiri₂] at h_ctrl
    dsimp only [mkRefMiriStackState] at h_ctrl
    exact h_ctrl
  subst h_ctrl_eq
  have h_top_eq : topRel₁? = topRel₂? := by
    rw [hmiri₁, hmiri₂] at h_threads
    exact topRel_eq_of_mkRefMiriStackState_threads h_threads
  subst h_top_eq
  have h_rev_lay : rf₁.toList.reverse.map
      (fun fr => fr.locals.map (fun l => l.layout.isSome)) =
    rf₂.toList.reverse.map
      (fun fr => fr.locals.map (fun l => l.layout.isSome)) := by
    rw [hmiri₁, hmiri₂] at h_layouts
    dsimp only [mkRefMiriStackState] at h_layouts
    have h_l_arr := congrArg Array.toList h_layouts
    rw [Array.toList_map, Array.toList_map] at h_l_arr
    rw [List.map_reverse, List.map_reverse, h_l_arr]
  have h_rev_eq := framesSimInv_unique hframe₁
    (by rw [h_rp_eq]; exact hframe₂) h_rev_lay
  have h_list_eq : rf₁.toList = rf₂.toList := by
    have h_rev := congrArg List.reverse h_rev_eq
    rw [List.reverse_reverse, List.reverse_reverse] at h_rev
    exact h_rev
  have h_rf_eq : rf₁ = rf₂ := by
    cases rf₁; cases rf₂
    dsimp only at h_list_eq
    exact congrArg Array.mk h_list_eq
  subst h_rf_eq
  cases rs₁; cases rs₂
  dsimp only at h_rty h_rp_eq hmiri₁ hmiri₂ h_steps h_max
  rw [h_rty, h_rp_eq, hmiri₁, hmiri₂, h_steps, h_max]

end Anneal.MirCorrespondence
