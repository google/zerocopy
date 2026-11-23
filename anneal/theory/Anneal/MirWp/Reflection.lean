-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Init.NotationExtra
public import Init.Data.BitVec.BasicAux
public import Init.Data.Int.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.Nat.Bitwise.Basic
public import Init.Control.Except
public import Trusted
public import Trusted.MirAst
public import Trusted.MirSemantics
public import Anneal.MirWp.Core
public import Anneal.MirWp.Scalars

public section

namespace Anneal.MirWp

open Trusted.MirAst Trusted.MirSemantics

/-! ## Part II: Type Reflection, `checkVal` / `ValidEntryArgs` Inversion, and
Operator Adequacy -/

/-- Exact boolean-to-propositional equality law for `IntWidth.beq`. -/
theorem IntWidth.beq_iff {w₁ w₂ : IntWidth} :
    IntWidth.beq w₁ w₂ = true ↔ w₁ = w₂ := by
  constructor
  · intro h
    cases w₁ <;> cases w₂ <;> first | rfl | cases h
  · intro h
    subst h
    cases w₁ <;> rfl

/-- Exact boolean-to-propositional equality law for `Mutability.beq`. -/
theorem Mutability.beq_iff {m₁ m₂ : Mutability} :
    Mutability.beq m₁ m₂ = true ↔ m₁ = m₂ := by
  constructor
  · intro h
    cases m₁ <;> cases m₂ <;> first | rfl | cases h
  · intro h
    subst h
    cases m₁ <;> rfl

/-- Exact boolean-to-propositional equality law for `natListBeq`. -/
theorem natListBeq_iff {xs ys : List Nat} :
    natListBeq xs ys = true ↔ xs = ys := by
  constructor
  · intro h
    induction xs generalizing ys with
    | nil =>
      cases ys with
      | nil => rfl
      | cons _ _ => cases h
    | cons x xs ih =>
      cases ys with
      | nil => cases h
      | cons y ys =>
        change (Nat.beq x y && natListBeq xs ys) = true at h
        cases hxy : Nat.beq x y with
        | false => rw [hxy] at h; cases h
        | true =>
          rw [hxy] at h
          rw [Nat.eq_of_beq_eq_true hxy, ih h]
  · intro h
    subst h
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      change (Nat.beq x x && natListBeq xs xs) = true
      rw [Nat.beq_refl, ih]
      rfl

/-- Exact boolean-to-propositional equality law for `EnumTagRepr.beq`. -/
theorem EnumTagRepr.beq_iff {r₁ r₂ : EnumTagRepr} :
    EnumTagRepr.beq r₁ r₂ = true ↔ r₁ = r₂ := by
  constructor
  · intro h
    cases r₁ with
    | zeroSized =>
      cases r₂ with
      | zeroSized => rfl
      | scalar _ _ => cases h
    | scalar w₁ s₁ =>
      cases r₂ with
      | zeroSized => cases h
      | scalar w₂ s₂ =>
        cases w₁ <;> cases w₂ <;> cases s₁ <;> cases s₂ <;>
          first | rfl | cases h
  · intro h
    subst h
    cases r₁ with
    | zeroSized => rfl
    | scalar w s => cases w <;> cases s <;> rfl

/-- Exact boolean-to-propositional equality law for `EnumTy.beq`. -/
theorem EnumTy.beq_iff {e₁ e₂ : EnumTy} :
    EnumTy.beq e₁ e₂ = true ↔ e₁ = e₂ := by
  constructor
  · intro h
    cases e₁ with
    | mk id₁ dw₁ ds₁ tr₁ discs₁ =>
      cases e₂ with
      | mk id₂ dw₂ ds₂ tr₂ discs₂ =>
        unfold EnumTy.beq at h
        dsimp only at h
        cases h1 : Nat.beq id₁ id₂ with
        | false => rw [h1] at h; cases h
        | true =>
          rw [h1] at h
          cases h2 : IntWidth.beq dw₁ dw₂ with
          | false => rw [h2] at h; cases h
          | true =>
            rw [h2] at h
            cases h3 : (ds₁ == ds₂) with
            | false => rw [h3] at h; cases h
            | true =>
              rw [h3] at h
              cases h4 : EnumTagRepr.beq tr₁ tr₂ with
              | false => rw [h4] at h; cases h
              | true =>
                rw [h4] at h
                rw [Nat.eq_of_beq_eq_true h1, IntWidth.beq_iff.mp h2,
                    eq_of_beq h3, EnumTagRepr.beq_iff.mp h4,
                    natListBeq_iff.mp h]
  · intro h
    subst h
    cases e₁ with
    | mk id₁ dw₁ ds₁ tr₁ discs₁ =>
      unfold EnumTy.beq
      dsimp only
      rw [Nat.beq_refl, IntWidth.beq_iff.mpr rfl, beq_self_eq_true,
          EnumTagRepr.beq_iff.mpr rfl, natListBeq_iff.mpr rfl]
      rfl

mutual
  /-- Soundness direction of `MirTy.beq`. -/
  theorem mirTy_beq_sound :
      ∀ (t₁ : MirTy), ∀ (t₂ : MirTy), MirTy.beq t₁ t₂ = true → t₁ = t₂
    | .bool => fun t₂ h => by
      cases t₂ <;> first | rfl | cases h
    | .int w₁ s₁ => fun t₂ h => by
      cases t₂ with
      | int w₂ s₂ =>
        change (IntWidth.beq w₁ w₂ && (s₁ == s₂)) = true at h
        cases hw : IntWidth.beq w₁ w₂ with
        | false => rw [hw] at h; cases h
        | true =>
          rw [hw] at h
          rw [IntWidth.beq_iff.mp hw, eq_of_beq h]
      | bool | unit | never | char | ordering | enum _ | tuple _ | ref _ _
      | rawPtr _ _ | unsupported => cases h
    | .unit => fun t₂ h => by
      cases t₂ <;> first | rfl | cases h
    | .never => fun t₂ h => by
      cases t₂ <;> first | rfl | cases h
    | .char => fun t₂ h => by
      cases t₂ <;> first | rfl | cases h
    | .ordering => fun t₂ h => by
      cases t₂ <;> first | rfl | cases h
    | .enum ety₁ => fun t₂ h => by
      cases t₂ with
      | enum ety₂ =>
        change EnumTy.beq ety₁ ety₂ = true at h
        rw [EnumTy.beq_iff.mp h]
      | bool | int _ _ | unit | never | char | ordering | tuple _ | ref _ _
      | rawPtr _ _ | unsupported => cases h
    | .tuple fs₁ => fun t₂ h => by
      cases t₂ with
      | tuple fs₂ =>
        change MirTy.beqList fs₁ fs₂ = true at h
        rw [mirTy_beqList_sound fs₁ fs₂ h]
      | bool | int _ _ | unit | never | char | ordering | enum _ | ref _ _
      | rawPtr _ _ | unsupported => cases h
    | .ref m₁ p₁ => fun t₂ h => by
      cases t₂ with
      | ref m₂ p₂ =>
        change (Mutability.beq m₁ m₂ && MirTy.beq p₁ p₂) = true at h
        cases hm : Mutability.beq m₁ m₂ with
        | false => rw [hm] at h; cases h
        | true =>
          rw [hm] at h
          rw [Mutability.beq_iff.mp hm, mirTy_beq_sound p₁ p₂ h]
      | bool | int _ _ | unit | never | char | ordering | enum _ | tuple _
      | rawPtr _ _ | unsupported => cases h
    | .rawPtr m₁ p₁ => fun t₂ h => by
      cases t₂ with
      | rawPtr m₂ p₂ =>
        change (Mutability.beq m₁ m₂ && MirTy.beq p₁ p₂) = true at h
        cases hm : Mutability.beq m₁ m₂ with
        | false => rw [hm] at h; cases h
        | true =>
          rw [hm] at h
          rw [Mutability.beq_iff.mp hm, mirTy_beq_sound p₁ p₂ h]
      | bool | int _ _ | unit | never | char | ordering | enum _ | tuple _
      | ref _ _ | unsupported => cases h
    | .unsupported => fun t₂ h => by
      cases t₂ <;> first | rfl | cases h

  /-- Soundness direction of `MirTy.beqList`. -/
  theorem mirTy_beqList_sound :
      ∀ (fs₁ : List MirTy), ∀ (fs₂ : List MirTy),
        MirTy.beqList fs₁ fs₂ = true → fs₁ = fs₂
    | [] => fun fs₂ h => by
      cases fs₂ with
      | nil => rfl
      | cons _ _ => cases h
    | x :: xs => fun fs₂ h => by
      cases fs₂ with
      | nil => cases h
      | cons y ys =>
        change (MirTy.beq x y && MirTy.beqList xs ys) = true at h
        cases hx : MirTy.beq x y with
        | false => rw [hx] at h; cases h
        | true =>
          rw [hx] at h
          rw [mirTy_beq_sound x y hx, mirTy_beqList_sound xs ys h]
end

mutual
  /-- Reflexivity of `MirTy.beq` across the full `MirTy` grammar. -/
  theorem mirTy_beq_refl : ∀ (t : MirTy), MirTy.beq t t = true
    | .bool => rfl
    | .int w s => by
      change (IntWidth.beq w w && (s == s)) = true
      rw [IntWidth.beq_iff.mpr rfl, beq_self_eq_true]
      rfl
    | .unit => rfl
    | .never => rfl
    | .char => rfl
    | .ordering => rfl
    | .enum ety => EnumTy.beq_iff.mpr rfl
    | .tuple fs => mirTy_beqList_refl fs
    | .ref m p => by
      change (Mutability.beq m m && MirTy.beq p p) = true
      rw [Mutability.beq_iff.mpr rfl, mirTy_beq_refl p]
      rfl
    | .rawPtr m p => by
      change (Mutability.beq m m && MirTy.beq p p) = true
      rw [Mutability.beq_iff.mpr rfl, mirTy_beq_refl p]
      rfl
    | .unsupported => rfl

  /-- Reflexivity of `MirTy.beqList`. -/
  theorem mirTy_beqList_refl : ∀ (fs : List MirTy), MirTy.beqList fs fs = true
    | [] => rfl
    | x :: xs => by
      change (MirTy.beq x x && MirTy.beqList xs xs) = true
      rw [mirTy_beq_refl x, mirTy_beqList_refl xs]
      rfl
end

/-- Complete structural `beq ↔ =` law across all `MirTy` constructors. -/
theorem MirTy.beq_iff {t₁ t₂ : MirTy} : MirTy.beq t₁ t₂ = true ↔ t₁ = t₂ :=
  ⟨mirTy_beq_sound t₁ t₂, fun h => by subst h; exact mirTy_beq_refl t₁⟩

/-- Master characterization of `checkVal` via `Val.ty?`. -/
theorem checkVal_iff_ty? {v : Val} {ty : MirTy} :
    checkVal v ty = true ↔ v.ty? = some ty := by
  unfold checkVal
  cases hTy : v.ty? with
  | none =>
    constructor
    · intro h; cases h
    · intro h; cases h
  | some vTy =>
    dsimp only
    constructor
    · intro h
      rw [MirTy.beq_iff.mp h]
    · intro h
      injection h with hEq
      subst hEq
      exact MirTy.beq_iff.mpr rfl

/-- A tuple value has, if any, a tuple type: only an overflow pair
`.tuple [.scalar sv, .bool b]` has a type (`Val.ty?`). -/
theorem Val.ty?_tuple_some {fs : List Val} {ty : MirTy}
    (h : (Val.tuple fs).ty? = some ty) : ∃ ts, ty = .tuple ts := by
  cases fs with
  | nil => cases h
  | cons x xs =>
    cases xs with
    | nil => cases x <;> cases h
    | cons y ys =>
      cases ys with
      | cons _ _ => cases x <;> cases y <;> cases h
      | nil =>
        cases x <;> cases y <;> first
          | cases h
          | (dsimp only [Val.ty?] at h
             cases hWf : ScalarVal.wf _ with
             | false => rw [hWf] at h; cases h
             | true =>
               rw [hWf] at h
               injection h with hTy
               exact ⟨_, hTy.symm⟩)

/-- Width- and signedness-parametric `checkVal` introduction for truncated
128-bit scalar payloads across all 12 integer types. -/
theorem checkVal_scalar_truncateBits (w : IntWidth) (s : Bool)
    (x : BitVec 128) :
    checkVal (.scalar ⟨w, s, truncateBits w x⟩) (.int w s) = true := by
  apply checkVal_iff_ty?.mpr
  dsimp only [Val.ty?]
  rw [scalarWf_truncateBits w s x]
  rfl

/-- `u64` specialization of `checkVal_scalar_truncateBits` for 64-bit scalar
proofs. -/
theorem checkVal_u64_truncateBits (x : BitVec 128) :
    checkVal (.scalar ⟨.i64, false, truncateBits .i64 x⟩) (.int .i64 false) =
      true :=
  checkVal_scalar_truncateBits .i64 false x

/-- Any scalar payload bounded by `intWidthModulus w` satisfies `checkVal` at
`(.int w s)`. -/
theorem checkVal_scalar_of_toNat_lt {w : IntWidth} {s : Bool} {x : BitVec 128}
    (h : x.toNat < intWidthModulus w) :
    checkVal (.scalar ⟨w, s, x⟩) (.int w s) = true := by
  rw [← truncateBits_of_toNat_lt h]
  exact checkVal_scalar_truncateBits w s x

/-- Exact inversion and introduction law for `checkVal` at integer types. -/
theorem checkVal_int_iff {v : Val} {w : IntWidth} {s : Bool} :
    checkVal v (.int w s) = true ↔
    ∃ bits : BitVec 128,
      v = .scalar ⟨w, s, bits⟩ ∧ truncateBits w bits = bits := by
  rw [checkVal_iff_ty?]
  constructor
  · intro h
    cases v with
    | scalar sv =>
      cases sv with
      | mk sw ss bits =>
        dsimp only [Val.ty?] at h
        cases hWf : ScalarVal.wf ⟨sw, ss, bits⟩ with
        | false => rw [hWf] at h; cases h
        | true =>
          rw [hWf] at h
          change some (MirTy.int sw ss) = some (MirTy.int w s) at h
          injection h with hTy
          injection hTy with hw hs
          subst hw; subst hs
          exact ⟨bits, rfl, eq_of_beq hWf⟩
    | enumVal ety idx =>
      dsimp only [Val.ty?] at h
      cases hAdm : (enumAdmitted ety && Nat.blt idx ety.discriminants.length)
        <;> rw [hAdm] at h <;> cases h
    | ptr _ | bool _ | char _ | ordering _ | unit | bytes _ => cases h
    | tuple _ =>
      let ⟨_, hTs⟩ := Val.ty?_tuple_some h
      cases hTs
  · intro h
    let ⟨bits, hv, hTrunc⟩ := h
    subst hv
    have hWf : ScalarVal.wf ⟨w, s, bits⟩ = true := by
      unfold ScalarVal.wf
      dsimp only
      rw [hTrunc]
      exact beq_self_eq_true bits
    dsimp only [Val.ty?]
    rw [ite_bool_true hWf]

/-- Exact inversion and introduction law for `checkVal` at `.bool`. -/
theorem checkVal_bool_iff {v : Val} :
    checkVal v .bool = true ↔ ∃ b : Bool, v = .bool b := by
  rw [checkVal_iff_ty?]
  constructor
  · intro h
    cases v with
    | bool b => exact ⟨b, rfl⟩
    | scalar sv =>
      dsimp only [Val.ty?] at h
      cases hWf : sv.wf <;> rw [hWf] at h <;> cases h
    | enumVal ety idx =>
      dsimp only [Val.ty?] at h
      cases hAdm : (enumAdmitted ety && Nat.blt idx ety.discriminants.length)
        <;> rw [hAdm] at h <;> cases h
    | ptr _ | char _ | ordering _ | unit | bytes _ => cases h
    | tuple _ =>
      let ⟨_, hTs⟩ := Val.ty?_tuple_some h
      cases hTs
  · intro h
    let ⟨b, hb⟩ := h
    subst hb
    rfl

/-- Exact inversion and introduction law for `checkVal` at `.unit`. -/
theorem checkVal_unit_iff {v : Val} :
    checkVal v .unit = true ↔ v = .unit := by
  rw [checkVal_iff_ty?]
  constructor
  · intro h
    cases v with
    | unit => rfl
    | scalar sv =>
      dsimp only [Val.ty?] at h
      cases hWf : sv.wf <;> rw [hWf] at h <;> cases h
    | enumVal ety idx =>
      dsimp only [Val.ty?] at h
      cases hAdm : (enumAdmitted ety && Nat.blt idx ety.discriminants.length)
        <;> rw [hAdm] at h <;> cases h
    | ptr _ | bool _ | char _ | ordering _ | bytes _ => cases h
    | tuple _ =>
      let ⟨_, hTs⟩ := Val.ty?_tuple_some h
      cases hTs
  · intro h
    subst h
    rfl

/-- No runtime `Val` inhabits `MirTy.never` (`!`). -/
theorem checkVal_never_false (v : Val) : checkVal v .never = false := by
  cases h : checkVal v .never with
  | false => rfl
  | true =>
    have hTy := checkVal_iff_ty?.mp h
    cases v with
    | scalar sv =>
      dsimp only [Val.ty?] at hTy
      cases hWf : sv.wf <;> rw [hWf] at hTy <;> cases hTy
    | enumVal ety idx =>
      dsimp only [Val.ty?] at hTy
      cases hAdm : (enumAdmitted ety && Nat.blt idx ety.discriminants.length)
        <;> rw [hAdm] at hTy <;> cases hTy
    | ptr _ | bool _ | char _ | ordering _ | unit | bytes _ => cases hTy
    | tuple _ =>
      let ⟨_, hTs⟩ := Val.ty?_tuple_some hTy
      cases hTs

/-- Exact inversion and introduction law for `checkVal` at fieldless `.enum ety`
for arbitrary `EnumTy` and arbitrary variant count `ety.discriminants.length`.
-/
theorem checkVal_enum_iff {v : Val} {ety : EnumTy} :
    checkVal v (.enum ety) = true ↔
    enumAdmitted ety = true ∧
    ∃ idx : Fin ety.discriminants.length, v = .enumVal ety idx.val := by
  rw [checkVal_iff_ty?]
  constructor
  · intro h
    cases v with
    | enumVal ety' var =>
      dsimp only [Val.ty?] at h
      cases hAdm : enumAdmitted ety' with
      | false => rw [hAdm] at h; cases h
      | true =>
        rw [hAdm] at h
        cases hBlt : Nat.blt var ety'.discriminants.length with
        | false => rw [hBlt] at h; cases h
        | true =>
          rw [hBlt] at h
          change some (MirTy.enum ety') = some (MirTy.enum ety) at h
          injection h with hTy
          injection hTy with hEty
          subst hEty
          exact ⟨hAdm, ⟨⟨var, Nat.le_of_ble_eq_true hBlt⟩, rfl⟩⟩
    | scalar sv =>
      dsimp only [Val.ty?] at h
      cases hWf : sv.wf <;> rw [hWf] at h <;> cases h
    | ptr _ | bool _ | char _ | ordering _ | unit | bytes _ => cases h
    | tuple _ =>
      let ⟨_, hTs⟩ := Val.ty?_tuple_some h
      cases hTs
  · intro h
    let ⟨hAdm, ⟨idx, hEq⟩⟩ := h
    subst hEq
    have hBlt : Nat.blt idx.val ety.discriminants.length = true :=
      Nat.ble_eq_true_of_le idx.isLt
    dsimp only [Val.ty?]
    rw [hAdm, hBlt]
    rfl

/-- Empty-parameter inversion law for `checkArgsMatch`. -/
theorem checkArgsMatch_nil_iff {args : List Val} :
    checkArgsMatch args [] = true ↔ args = [] := by
  cases args with
  | nil =>
    constructor <;> intro _ <;> rfl
  | cons _ _ =>
    constructor <;> intro h <;> cases h

/-- Cons-parameter peeling law for `checkArgsMatch` at arbitrary arity. -/
theorem checkArgsMatch_cons_iff {args : List Val} {ty : MirTy}
    {tys : List MirTy} :
    checkArgsMatch args (ty :: tys) = true ↔
    ∃ v rest,
      args = v :: rest ∧
      checkVal v ty = true ∧
      checkArgsMatch rest tys = true := by
  cases args with
  | nil =>
    constructor
    · intro h; cases h
    · intro h; let ⟨_, _, hEq, _, _⟩ := h; cases hEq
  | cons v rest =>
    change (checkVal v ty && checkArgsMatch rest tys) = true ↔ _
    constructor
    · intro h
      cases hv : checkVal v ty with
      | false => rw [hv] at h; cases h
      | true =>
        rw [hv] at h
        exact ⟨v, rest, rfl, hv, h⟩
    · intro h
      let ⟨v', rest', hEq, hv, hRest⟩ := h
      injection hEq with hvEq hRestEq
      subst hvEq; subst hRestEq
      rw [hv, hRest]
      rfl

/-- `checkArgsMatch` enforces equal argument and parameter-type lengths. -/
theorem checkArgsMatch_length {args : List Val} {tys : List MirTy}
    (h : checkArgsMatch args tys = true) :
    args.length = tys.length := by
  induction tys generalizing args with
  | nil =>
    rw [checkArgsMatch_nil_iff.mp h]
    rfl
  | cons ty rest ih =>
    let ⟨_, argsRest, hEq, _, hRest⟩ := checkArgsMatch_cons_iff.mp h
    subst hEq
    exact congrArg Nat.succ (ih hRest)

/-- Any parameter type list containing `MirTy.never` admits zero matching
argument lists. -/
theorem not_checkArgsMatch_of_never {args : List Val} {tys : List MirTy}
    (hMem : .never ∈ tys) :
    checkArgsMatch args tys ≠ true := by
  induction hMem generalizing args with
  | head _ =>
    intro h
    let ⟨v, _, _, hv, _⟩ := checkArgsMatch_cons_iff.mp h
    rw [checkVal_never_false v] at hv
    cases hv
  | tail _ _ ih =>
    intro h
    let ⟨_, rest, _, _, hRest⟩ := checkArgsMatch_cons_iff.mp h
    exact ih hRest

/-- Any body with an uninhabited `MirTy.never` parameter has vacuously
uninhabited `ValidEntryArgs`. -/
theorem not_validEntryArgs_of_never {body : Body} {args : List Val}
    (hMem : .never ∈ (body.locals.drop 1).take body.argumentCount) :
    ¬ ValidEntryArgs body args :=
  not_checkArgsMatch_of_never hMem

/-! ### Entry Initialization (`initState`) -/

/-- Single-frame running state in body `defId` (default `0`) with empty
`callerMem` and memory `mem` (default `entryMemory`). -/
@[expose] def mkState (blockIdx stmtIdx : Nat) (locals : List LocalSlot)
    (defId : DefId := 0) (mem : MemoryState := entryMemory) : State :=
  {
    frames := [{
      defId := defId
      blockIdx := blockIdx
      stmtIdx := stmtIdx
      locals := locals
    }]
    callerMem := ⟨[]⟩
    mem := mem
  }

/-- Entry initialization equation for `initState p { args := args }` when the
entry body satisfies `BodyStaticAdmitted` and `ValidEntryArgs`: the entry state
is one frame of body `p.entryDefId` at block `0` and statement `0`, holding the
locals that `initLocalsLoop` builds. -/
theorem initState_eq_ok {p : Program} {body : Body} {args : List Val}
    (h_body : Trusted.MirSemantics.getElem? p.bodies p.entryDefId = some body)
    (h_adm : BodyStaticAdmitted p body = true)
    (h_args : ValidEntryArgs body args) :
    initState p { args := args } =
      .ok (mkState 0 0 (initLocalsLoop body args 0 body.locals)
        p.entryDefId) := by
  unfold BodyStaticAdmitted at h_adm
  unfold ValidEntryArgs at h_args
  unfold initState mkState
  dsimp only
  rw [h_body]
  dsimp only
  rw [h_args]
  cases h1 : Nat.beq p.pointerWidthBits 64 <;>
    cases h2 : Nat.beq p.mirProfileVersion 1 <;>
    cases hid : stringBeq body.identity "" <;>
    cases h3 : body.basicBlocks.isEmpty <;>
    cases h4 : Nat.blt body.argumentCount body.locals.length <;>
    cases h5 : storageAnnotationsInBounds body <;>
    cases h5d : discriminantTypesValid body <;>
    cases h5c : castTypesValid body <;>
    cases h6 : body.locals.all isSupportedScalarOrUnitTy <;>
    rw [h1, h2, hid, h3, h4, h5, h5d, h5c, h6] at h_adm <;>
    cases h_adm
  rfl

/-! ### Width- and Signedness-Parametric Operator Adequacy -/

theorem and_isUnchecked_false {b : Bool} {op : BinOp}
    (h : op.isUnchecked = false) : (b && op.isUnchecked) = false := by
  rw [h]
  exact Bool.and_false b

/-- Wrapping binary arithmetic (`.add`, `.sub`, `.mul`) succeeds and produces a
well-typed `Val` across all six `IntWidth`s and both signedness modes. -/
theorem evalBinOp_wrapping_arith_ok {op : BinOp}
    (hOp : op = .add ∨ op = .sub ∨ op = .mul)
    (w : IntWidth) (s : Bool) (b₁ b₂ : BitVec 128) :
    ∃ out : Val,
      evalBinOp op (.scalar ⟨w, s, b₁⟩) (.scalar ⟨w, s, b₂⟩) = .ok out ∧
      checkVal out (.int w s) = true := by
  have hEqW : IntWidth.beq w w = true := IntWidth.beq_iff.mpr rfl
  have hEqS : (s == s) = true := beq_self_eq_true s
  have hGuard : (!(IntWidth.beq w w && (s == s))) = false := by
    rw [hEqW, hEqS]
    rfl
  have hDiv2 :
      (s && false &&
        (decodeScalar ⟨w, s, b₁⟩ == signedMinInt w &&
          decodeScalar ⟨w, s, b₂⟩ == Neg.neg 1)) = false := by
    cases s <;> rfl
  cases hOp with
  | inl hAdd =>
    subst hAdd
    let ⟨sv, lossy, hTr, hw, hs, hWf⟩ :=
      truncateScalar_ok w s
        (decodeScalar ⟨w, s, b₁⟩ + decodeScalar ⟨w, s, b₂⟩)
    refine ⟨.scalar sv, ?_, checkVal_iff_ty?.mpr ?_⟩
    · unfold evalBinOp evalArithOp
      dsimp only
      rw [ite_bool_false (rfl : BinOp.add.isShift = false)]
      rw [ite_bool_false hGuard]
      rw [ite_bool_false hDiv2]
      rw [hTr]
      dsimp only
      exact ite_bool_false (and_isUnchecked_false rfl)
    · dsimp only [Val.ty?]
      rw [hWf, hw, hs]
      rfl
  | inr hRest =>
    cases hRest with
    | inl hSub =>
      subst hSub
      let ⟨sv, lossy, hTr, hw, hs, hWf⟩ :=
        truncateScalar_ok w s
          (decodeScalar ⟨w, s, b₁⟩ - decodeScalar ⟨w, s, b₂⟩)
      refine ⟨.scalar sv, ?_, checkVal_iff_ty?.mpr ?_⟩
      · unfold evalBinOp evalArithOp
        dsimp only
        rw [ite_bool_false (rfl : BinOp.sub.isShift = false)]
        rw [ite_bool_false hGuard]
        rw [ite_bool_false hDiv2]
        rw [hTr]
        dsimp only
        exact ite_bool_false (and_isUnchecked_false rfl)
      · dsimp only [Val.ty?]
        rw [hWf, hw, hs]
        rfl
    | inr hMul =>
      subst hMul
      let ⟨sv, lossy, hTr, hw, hs, hWf⟩ :=
        truncateScalar_ok w s
          (decodeScalar ⟨w, s, b₁⟩ * decodeScalar ⟨w, s, b₂⟩)
      refine ⟨.scalar sv, ?_, checkVal_iff_ty?.mpr ?_⟩
      · unfold evalBinOp evalArithOp
        dsimp only
        rw [ite_bool_false (rfl : BinOp.mul.isShift = false)]
        rw [ite_bool_false hGuard]
        rw [ite_bool_false hDiv2]
        rw [hTr]
        dsimp only
        exact ite_bool_false (and_isUnchecked_false rfl)
      · dsimp only [Val.ty?]
        rw [hWf, hw, hs]
        rfl

/-- Explicit closed-form equation for unsigned wrapping `.add` across all six
`IntWidth` variants. -/
theorem evalBinOp_unsigned_add (w : IntWidth) (b₁ b₂ : BitVec 128) :
    evalBinOp .add (.scalar ⟨w, false, b₁⟩) (.scalar ⟨w, false, b₂⟩) =
      .ok (.scalar ⟨w, false,
        truncateBits w (bvOfInt 128
          (decodeScalar ⟨w, false, b₁⟩ + decodeScalar ⟨w, false, b₂⟩))⟩) := by
  have hGuard : (!(IntWidth.beq w w && (false == false))) = false := by
    rw [IntWidth.beq_iff.mpr rfl]
    rfl
  unfold evalBinOp evalArithOp truncateScalar
  dsimp only
  rw [ite_bool_false (rfl : BinOp.add.isShift = false)]
  rw [ite_bool_false hGuard]
  exact ite_bool_false (and_isUnchecked_false rfl)

/-- Bitwise binary operators (`.bitAnd`, `.bitOr`, `.bitXor`) succeed and
produce a well-typed `Val` across all six `IntWidth`s and both signednesses. -/
theorem evalBinOp_bitwise_ok {op : BinOp}
    (hOp : op = .bitAnd ∨ op = .bitOr ∨ op = .bitXor)
    (w : IntWidth) (s : Bool) (b₁ b₂ : BitVec 128) :
    ∃ out : Val,
      evalBinOp op (.scalar ⟨w, s, b₁⟩) (.scalar ⟨w, s, b₂⟩) = .ok out ∧
      checkVal out (.int w s) = true := by
  have hEqW : IntWidth.beq w w = true := IntWidth.beq_iff.mpr rfl
  have hEqS : (s == s) = true := beq_self_eq_true s
  cases hOp with
  | inl hAnd =>
    subst hAnd
    unfold evalBinOp
    dsimp only [BinOp.isShift]
    rw [hEqW, hEqS]
    exact ⟨_, rfl,
      checkVal_scalar_truncateBits w s
        (bvAnd (truncateBits w b₁) (truncateBits w b₂))⟩
  | inr hRest =>
    cases hRest with
    | inl hOr =>
      subst hOr
      unfold evalBinOp
      dsimp only [BinOp.isShift]
      rw [hEqW, hEqS]
      exact ⟨_, rfl,
        checkVal_scalar_truncateBits w s
          (bvOr (truncateBits w b₁) (truncateBits w b₂))⟩
    | inr hXor =>
      subst hXor
      unfold evalBinOp
      dsimp only [BinOp.isShift]
      rw [hEqW, hEqS]
      exact ⟨_, rfl,
        checkVal_scalar_truncateBits w s
          (bvXor (truncateBits w b₁) (truncateBits w b₂))⟩

/-- Wrapping shifts (`.shl`, `.shr`) succeed and produce a well-typed `Val` for
any LHS `(w, s)` and any RHS `(rw, rs)`. -/
theorem evalBinOp_wrapping_shift_ok {op : BinOp}
    (hOp : op = .shl ∨ op = .shr)
    (w rw : IntWidth) (s rs : Bool) (b₁ b₂ : BitVec 128) :
    ∃ out : Val,
      evalBinOp op (.scalar ⟨w, s, b₁⟩) (.scalar ⟨rw, rs, b₂⟩) = .ok out ∧
      checkVal out (.int w s) = true := by
  cases hOp with
  | inl hShl =>
    subst hShl
    let ⟨sv, _, hTr, hw, hs, hWf⟩ :=
      truncateScalar_ok w s
        (intShiftLeft (decodeScalar ⟨w, s, b₁⟩)
          (intEmod (decodeScalar ⟨rw, rs, b₂⟩) (Int.ofNat w.bitWidth)).toNat)
    refine ⟨.scalar sv, ?_, checkVal_iff_ty?.mpr ?_⟩
    · unfold evalBinOp evalShiftOp
      dsimp only
      rw [ite_bool_true (rfl : BinOp.shl.isShift = true)]
      rw [hTr]
      dsimp only
      exact ite_bool_false (and_isUnchecked_false rfl)
    · dsimp only [Val.ty?]
      rw [hWf, hw, hs]
      rfl
  | inr hShr =>
    subst hShr
    let ⟨sv, _, hTr, hw, hs, hWf⟩ :=
      truncateScalar_ok w s
        (intShiftRight (decodeScalar ⟨w, s, b₁⟩)
          (intEmod (decodeScalar ⟨rw, rs, b₂⟩) (Int.ofNat w.bitWidth)).toNat)
    refine ⟨.scalar sv, ?_, checkVal_iff_ty?.mpr ?_⟩
    · unfold evalBinOp evalShiftOp
      dsimp only
      rw [ite_bool_true (rfl : BinOp.shr.isShift = true)]
      rw [hTr]
      dsimp only
      exact ite_bool_false (and_isUnchecked_false rfl)
    · dsimp only [Val.ty?]
      rw [hWf, hw, hs]
      rfl

/-- Scalar comparisons (`.eq`, `.ne`, `.lt`, `.le`, `.gt`, `.ge`) succeed and
produce a `.bool` value across all six `IntWidth`s and both signedness modes. -/
theorem evalBinOp_cmp_ok {op : BinOp}
    (hOp : op = .eq ∨ op = .ne ∨ op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge)
    (w : IntWidth) (s : Bool) (b₁ b₂ : BitVec 128) :
    ∃ b : Bool,
      evalBinOp op (.scalar ⟨w, s, b₁⟩) (.scalar ⟨w, s, b₂⟩) = .ok (.bool b) :=
  by
  have hEqW : IntWidth.beq w w = true := IntWidth.beq_iff.mpr rfl
  have hEqS : (s == s) = true := beq_self_eq_true s
  cases hOp with
  | inl h =>
    subst h; unfold evalBinOp; dsimp only [BinOp.isShift]
    rw [hEqW, hEqS]; exact ⟨_, rfl⟩
  | inr h => cases h with
    | inl h =>
      subst h; unfold evalBinOp; dsimp only [BinOp.isShift]
      rw [hEqW, hEqS]; exact ⟨_, rfl⟩
    | inr h => cases h with
      | inl h =>
        subst h; unfold evalBinOp; dsimp only [BinOp.isShift]
        rw [hEqW, hEqS]; exact ⟨_, rfl⟩
      | inr h => cases h with
        | inl h =>
          subst h; unfold evalBinOp; dsimp only [BinOp.isShift]
          rw [hEqW, hEqS]; exact ⟨_, rfl⟩
        | inr h => cases h with
          | inl h =>
            subst h; unfold evalBinOp; dsimp only [BinOp.isShift]
            rw [hEqW, hEqS]; exact ⟨_, rfl⟩
          | inr h =>
            subst h; unfold evalBinOp; dsimp only [BinOp.isShift]
            rw [hEqW, hEqS]; exact ⟨_, rfl⟩

/-- `UnOp.not` on scalars succeeds and preserves `checkVal` across all six
`IntWidth`s and both signedness modes. -/
theorem evalUnOp_not_scalar_ok (w : IntWidth) (s : Bool) (b : BitVec 128) :
    ∃ out : Val,
      evalUnOp .not (.scalar ⟨w, s, b⟩) = .ok out ∧
      checkVal out (.int w s) = true := by
  unfold evalUnOp
  dsimp only
  let ⟨sv, _, hTr, hw, hs, hWf⟩ :=
    truncateScalar_ok w s (intNot (decodeScalar ⟨w, s, b⟩))
  rw [hTr]
  refine ⟨.scalar sv, rfl, checkVal_iff_ty?.mpr ?_⟩
  dsimp only [Val.ty?]
  rw [hWf, hw, hs]
  rfl

/-- Signed `UnOp.neg` succeeds and preserves `checkVal` across all six
`IntWidth`s (including wrapping `-INT_MIN == INT_MIN`). -/
theorem evalUnOp_signed_neg_ok (w : IntWidth) (b : BitVec 128) :
    ∃ out : Val,
      evalUnOp .neg (.scalar ⟨w, true, b⟩) = .ok out ∧
      checkVal out (.int w true) = true := by
  unfold evalUnOp
  dsimp only
  let ⟨sv, _, hTr, hw, hs, hWf⟩ :=
    truncateScalar_ok w true (Neg.neg (decodeScalar ⟨w, true, b⟩))
  rw [hTr]
  refine ⟨.scalar sv, rfl, checkVal_iff_ty?.mpr ?_⟩
  dsimp only [Val.ty?]
  rw [hWf, hw, hs]
  rfl

/-! ### Compositional Multi-Body Crate Dispatch -/

/-- Right-nested conjunction of `BodyVerified` obligations for a slice of
`p.bodies` starting at `DefId` index `idx`. Reduces definitionally on concrete
body lists without manual `Nat` index splitting or `Option.some.inj`.

The definition folds over the list with `List.foldr` instead of recursing by
pattern matching: equation-compiler recursion makes Lean emit an `unsafe`
`BodiesVerified._unsafe_rec` helper even for a `Prop`, and `anneal-audit`
rejects every `unsafe` constant. -/
@[expose] def BodiesVerified (p : Program) (specs : Specs) (idx : Nat)
    (bs : List Body) : Prop :=
  bs.foldr
    (fun body ih curIdx =>
      BodyVerified p curIdx body (specs.safety body.identity) ∧
      ih (curIdx + 1))
    (fun _ => True)
    idx

/-- Soundness of `BodiesVerified`: discharges the universal `getElem? p.bodies`
body-verification obligation in `ProgramVerified` (`CrateTheorem` /
`UnitTheorem`). -/
theorem bodiesVerified_getElem {p : Program} {specs : Specs} :
    ∀ {idx : Nat} {bs : List Body},
      BodiesVerified p specs idx bs →
      ∀ (k : Nat) (b : Body),
        Trusted.MirSemantics.getElem? bs k = some b →
        BodyVerified p (idx + k) b (specs.safety b.identity)
  | _, [], _, _, _, hGet => by cases hGet
  | idx, b₀ :: rest, hBs, 0, b, hGet => by
    injection hGet with hEq
    subst hEq
    rw [Nat.add_zero]
    exact hBs.1
  | idx, _ :: rest, hBs, k + 1, b, hGet => by
    have hSub := bodiesVerified_getElem hBs.2 k b hGet
    have hIdx : idx + 1 + k = idx + (k + 1) := by
      rw [Nat.add_assoc, Nat.add_comm 1 k]
    rw [← hIdx]
    exact hSub

end Anneal.MirWp

end
