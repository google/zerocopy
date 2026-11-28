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
import Init.Data.Char.Basic
import Init.Data.Int.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Data.List.Basic
import Init.Control.Except
import Anneal.MiniRust.StepSim

namespace Anneal.MiniRust

open Trusted.MirAst
open Trusted.MirSemantics

/-!
# MiniRust Oracle Certificate & Non-Vacuity (`Anneal.MiniRust.OracleCert`)

Packages the operational correspondence theorems (`minirust_v1`) into:
- Top-level forward-simulation and exact bidirectional theorems over
  `MiniRustAdmitted` and `MiniRustExactAdmitted`.
- `minirust_admitted_never_illFormed`, proving that no reachable step from
  `initMrMachine p q` on any `MiniRustAdmitted p q` input ever yields
  `StepOutcome.illFormed` (`¬ MrIllFormed m₀`).
- `MiniRustForwardSimClaim` (`.forwardSim "minirust_v1"` over
  `MiniRustAdmitted`) and `MiniRustBiFaultEquivClaim`
  (`.biFaultEquiv "minirust_v1"` over `MiniRustExactAdmitted`).
- Constructive executable non-vacuity witnesses (`0` `Classical.choice`, `0`
  `native_decide`, `0` `sorry`) exercising both `annealRunFuel` and `mrRunFuel`
  across positive returning programs, strict-inclusion witnesses (`Operand.move`
  deinitialization and `char`-as-`u32` Unicode scalar niche), negative UB
  programs, and standalone `Machine.lean` bottom-of-stack `Return` UB.
-/

/-! ## Exact Bidirectional Correspondence Theorems -/

/-- Exact bidirectional UB equivalence (`MiniRustExactAdmitted`):
`ReachesResult p q (.fault .undefined) ↔ MrFaultsUB m₀`. -/
theorem exact_ub_iff (p : Program) (q : Query)
    (hadm : MiniRustExactAdmitted p q) :
    ∀ m₀, initMrMachine p q = .ok m₀ →
      (ReachesResult p q (.fault .undefined) ↔ MrFaultsUB m₀) := by
  intro m₀ hinitM
  constructor
  · intro hrr
    cases init_fullStateRel true p q hadm with
    | intro s₀ h1 => cases h1 with | intro m₀' h2 => cases h2 with
      | intro m₁ h3 =>
        rw [h3.2.1] at hinitM; injection hinitM with hmeq; subst hmeq
        dsimp only [ReachesResult] at hrr
        rw [h3.1] at hrr
        cases hrr with
        | intro sf hsf =>
          cases reaches_sim_forward true p h3.2.2.2 hsf.1 with
          | intro mf hmf =>
            cases hsf.2 with
            | intro c hc =>
              have hc0 : c = 0 := hc.1; subst hc0
              have hsim := fullStep_sim true p sf mf hmf.2
              rw [hc.2] at hsim
              cases hsim rfl with
              | intro reason hub =>
                exact ⟨mf, reason, MrReaches.trans h3.2.2.1 hmf.1, hub⟩
  · exact forward_ub_contrapositive p q (miniRustAdmitted_of_exact hadm) m₀ hinitM

/-- Exact bidirectional normal return equivalence (`MiniRustExactAdmitted`). -/
theorem exact_behavior_iff (p : Program) (q : Query)
    (hadm : MiniRustExactAdmitted p q) :
    ∀ m₀, initMrMachine p q = .ok m₀ →
      (∀ v, Behavior p q (.returned ⟨v, ⟨[]⟩⟩) → MrBehavior m₀ (translateVal v)) ∧
      (∀ v', MrBehavior m₀ v' →
        ∃ v, v' = translateVal v ∧ Behavior p q (.returned ⟨v, ⟨[]⟩⟩)) := by
  intro m₀ hinitM
  refine ⟨forward_behavior p q (miniRustAdmitted_of_exact hadm) m₀ hinitM,
    fun v' hmb => ?_⟩
  cases init_fullStateRel true p q hadm with
  | intro s₀ h1 => cases h1 with | intro m₀' h2 => cases h2 with
    | intro m₁ h3 =>
      rw [h3.2.1] at hinitM; injection hinitM with hmeq; subst hmeq
      cases hmb with
      | intro mEnd hmEnd =>
        have hfrom1 := mrReaches_after_init h3.2.2.1.toHead hmEnd.1.toHead hmEnd.2
          (fun _ h => by cases h)
        cases (mrReachesHead_sim_back true p h3.2.2.2 hfrom1).2 v' rfl hmEnd.2 with
        | intro sf hsf => cases hsf with | intro v hv =>
          refine ⟨v, hv.2.2, ?_⟩
          dsimp only [Behavior, ReachesResult]; rw [h3.1]
          exact ⟨sf, hv.1, hv.2.1⟩

/-- Exact bidirectional divergence equivalence (`MiniRustExactAdmitted`). -/
theorem exact_diverges_iff (p : Program) (q : Query)
    (hadm : MiniRustExactAdmitted p q) :
    ∀ m₀, initMrMachine p q = .ok m₀ →
      (Diverges p q ↔ MrDiverges m₀) := by
  intro m₀ hinitM
  constructor
  · exact forward_diverges p q (miniRustAdmitted_of_exact hadm) m₀ hinitM
  · intro hmdiv
    cases init_fullStateRel true p q hadm with
    | intro s₀ h1 => cases h1 with | intro m₀' h2 => cases h2 with
      | intro m₁ h3 =>
        rw [h3.2.1] at hinitM; injection hinitM with hmeq; subst hmeq
        cases hmdiv with
        | intro mTrace hmTrace =>
          cases mrDiverges_follow_reaches hmTrace.1 hmTrace.2 h3.2.2.1.toHead with
          | intro k hk =>
            have hlockstep : ∀ n : Nat,
                FullStateRel true p (annealIter p n s₀) (mTrace (k + n)) ∧
                evalStep p 0 (annealIter p n s₀) = .step (annealIter p (n + 1) s₀) := by
              intro n
              induction n with
              | zero =>
                rw [Nat.add_zero, hk]
                have hsim := fullStep_sim true p s₀ m₁ h3.2.2.2
                cases hev : evalStep p 0 s₀ with
                | step _ =>
                  refine ⟨h3.2.2.2, ?_⟩
                  dsimp only [annealIter, annealNext]; rw [hev]
                | done out =>
                  rw [hev] at hsim
                  cases out with
                  | unwound _ | aborted _ => exact False.elim hsim
                  | returned _ =>
                    cases hsim.2 with
                    | intro mNext hmNext =>
                      have hs0 := hmTrace.2 k; rw [hk, hmNext.1] at hs0
                      injection hs0 with hne; have hs1 := hmTrace.2 (k + 1)
                      rw [← hne, hmNext.2] at hs1; cases hs1
                | fault fk =>
                  rw [hev] at hsim
                  cases fk with
                  | unsupported => exact False.elim hsim
                  | undefined =>
                    cases hsim rfl with
                    | intro _ hub =>
                      have hs0 := hmTrace.2 k; rw [hk, hub] at hs0; cases hs0
              | succ j ih =>
                have hsim := fullStep_sim true p (annealIter p j s₀)
                  (mTrace (k + j)) ih.1
                rw [ih.2] at hsim
                cases hsim with
                | intro mNext hmNext =>
                  have hmEq : mTrace (k + Nat.succ j) = mNext := by
                    have hkn : k + Nat.succ j = (k + j) + 1 := Nat.add_succ k j
                    have hs := hmTrace.2 (k + j); rw [hmNext.1] at hs
                    injection hs with heq; rw [hkn]; exact heq.symm
                  have hrelNext : FullStateRel true p (annealIter p (j + 1) s₀)
                      (mTrace (k + Nat.succ j)) := by
                    rw [hmEq]; exact hmNext.2
                  have hsim2 := fullStep_sim true p (annealIter p (j + 1) s₀)
                    (mTrace (k + Nat.succ j)) hrelNext
                  cases hev2 : evalStep p 0 (annealIter p (j + 1) s₀) with
                  | step _ =>
                    refine ⟨hrelNext, ?_⟩
                    rw [annealIter_succ_right]; dsimp only [annealNext]; rw [hev2]
                  | done out =>
                    rw [hev2] at hsim2
                    cases out with
                    | unwound _ | aborted _ => exact False.elim hsim2
                    | returned _ =>
                      cases hsim2.2 with
                      | intro mRet hmRet =>
                        have hs1 := hmTrace.2 (k + Nat.succ j); rw [hmRet.1] at hs1
                        injection hs1 with heq; have hs2 := hmTrace.2 (k + Nat.succ j + 1)
                        rw [← heq, hmRet.2] at hs2; cases hs2
                  | fault fk =>
                    rw [hev2] at hsim2
                    cases fk with
                    | unsupported => exact False.elim hsim2
                    | undefined =>
                      cases hsim2 rfl with
                      | intro _ hub =>
                        have hs1 := hmTrace.2 (k + Nat.succ j); rw [hub] at hs1; cases hs1
            exact ⟨s₀, h3.1, fun n => annealIter p n s₀, rfl,
              fun n => ⟨0, rfl, (hlockstep n).2⟩⟩

/-! ## Runtime Ill-Formedness Freedom (`minirust_admitted_never_illFormed`) -/

private theorem decodeInt_encodable (it : IntType) (bs : List AbstractByte)
    (i : Int) (hpos : 0 < it.bitWidth) (hdec : decodeInt it bs = some i) :
    ∃ bs', encodeInt it i = some bs' := by
  dsimp only [decodeInt] at hdec
  cases hlen : Nat.beq bs.length it.size.bytes with
  | false => rw [hlen, if_not_false] at hdec; cases hdec
  | true =>
    rw [hlen, if_not_true] at hdec
    cases hex : extractInitBytes bs with
    | none => rw [hex] at hdec; cases hdec
    | some raw =>
      rw [hex] at hdec; injection hdec with hi; subst hi
      cases decodeInt_encodeInt it _ hpos (bringInBounds_canRepresent it _ hpos) with
      | intro bs' hbs => exact ⟨bs', hbs.1⟩

private theorem mrDecode_emptySized_eq_unit (sz al : Nat)
    (bs : List AbstractByte) (v : MrValue)
    (h : mrDecode (emptySizedTy sz al) bs = some v) :
    v = .tuple .nil := by
  dsimp only [emptySizedTy, mrDecode, MrType.size] at h
  cases hb : Nat.beq bs.length sz with
  | false => rw [hb, if_not_false] at h; cases h
  | true =>
    rw [hb, if_not_true] at h
    dsimp only [mrDecodeFields] at h
    injection h with hv; exact hv.symm

private theorem mrDecodeEnumVariant_build_encodable (ety : EnumTy)
    (tagW : IntWidth) (tagS : Bool) (d : Int) (bs : List AbstractByte)
    (dv : MrValue) :
    ∀ (ds : List Nat),
      mrDecodeEnumVariant d (buildEnumVariants ety tagW tagS ds) bs = some dv →
      ∃ bs', mrEncodeEnumVariant d dv (buildEnumVariants ety tagW tagS ds) =
        some bs' := by
  intro ds
  induction ds with
  | nil => intro h; cases h
  | cons x rest ih =>
    intro h
    dsimp only [buildEnumVariants, mrDecodeEnumVariant, mrEncodeEnumVariant] at h
    dsimp only [buildEnumVariants, mrDecodeEnumVariant, mrEncodeEnumVariant]
    cases hb : (discrIntOfNat ety.discrWidth ety.discrSigned x == d) with
    | false =>
      rw [hb] at h; rw [if_false_eq_true] at h; rw [if_false_eq_true]; exact ih h
    | true =>
      rw [hb] at h; rw [if_true_eq_true] at h; rw [if_true_eq_true]
      have hdv := mrDecode_emptySized_eq_unit tagW.byteSize tagW.byteSize bs dv h
      subst hdv
      dsimp only [emptySizedTy, mrEncode, mrEncodeFields, encodeDiscriminant]
      cases decodeInt_encodeInt (translateIntTy tagW tagS)
          (tagIntOfNat tagW tagS x) (intWidth_bitWidth_pos tagW)
          (canRepresent_decodeScalar tagW tagS _) with
      | intro tb htb => rw [htb.1]; exact ⟨_, rfl⟩

private theorem mrDecode_bool_encodable (bs : List AbstractByte) (v : MrValue)
    (hdec : mrDecode .bool bs = some v) :
    ∃ bs', mrEncode .bool v = some bs' := by
  dsimp only [mrDecode] at hdec
  cases bs with
  | nil => cases hdec
  | cons b0 rest =>
    cases b0 with
    | uninit => cases hdec
    | init byte =>
      cases rest with
      | cons _ _ => cases hdec
      | nil =>
        dsimp only at hdec
        cases h0 : (byte == 0) with
        | true =>
          rw [h0, if_true_eq_true] at hdec; injection hdec with hv; subst hv
          exact ⟨[.init 0], rfl⟩
        | false =>
          rw [h0, if_false_eq_true] at hdec
          cases h1 : (byte == 1) with
          | true =>
            rw [h1, if_true_eq_true] at hdec; injection hdec with hv; subst hv
            exact ⟨[.init 1], rfl⟩
          | false => rw [h1, if_false_eq_true] at hdec; cases hdec

/-- Any value decoded at `translateTy ty` (for supported `ty`) is encodable at
`translateTy ty`, guaranteeing `typedStore` never hits `.illFormed`. -/
theorem mrDecode_encodable (ty : MirTy) (bs : List AbstractByte) (v : MrValue)
    (hsupp : isSupportedScalarOrUnitTy ty = true)
    (hdec : mrDecode (translateTy ty) bs = some v) :
    ∃ bs', mrEncode (translateTy ty) v = some bs' := by
  cases ty with
  | bool => exact mrDecode_bool_encodable bs v hdec
  | int w s =>
    dsimp only [translateTy, mrDecode] at hdec; dsimp only [translateTy, mrEncode]
    cases hd : decodeInt (translateIntTy w s) bs with
    | none => rw [hd] at hdec; cases hdec
    | some i =>
      rw [hd] at hdec; injection hdec with hv; subst hv
      exact decodeInt_encodable (translateIntTy w s) bs i (intWidth_bitWidth_pos w) hd
  | char =>
    dsimp only [translateTy, mrDecode] at hdec; dsimp only [translateTy, mrEncode]
    cases hd : decodeInt u32Ty bs with
    | none => rw [hd] at hdec; cases hdec
    | some i =>
      rw [hd] at hdec; injection hdec with hv; subst hv
      exact decodeInt_encodable u32Ty bs i (by decide) hd
  | unit =>
    have hv := mrDecode_emptySized_eq_unit 0 1 bs v hdec
    subst hv; exact ⟨[], rfl⟩
  | never =>
    dsimp only [translateTy, neverTy, mrDecode, decodeDiscriminant, MrType.size] at hdec
    cases hb : Nat.beq bs.length 0 with
    | false => rw [hb, if_not_false] at hdec; cases hdec
    | true => rw [hb, if_not_true] at hdec; cases hdec
  | ordering =>
    dsimp only [translateTy, orderingTy, mrDecode, MrType.size] at hdec
    dsimp only [translateTy, orderingTy, mrEncode]
    cases hlen : Nat.beq bs.length 1 with
    | false => rw [hlen, if_not_false] at hdec; cases hdec
    | true =>
      rw [hlen, if_not_true] at hdec
      cases hd : decodeDiscriminant bs _ with
      | none => rw [hd] at hdec; cases hdec
      | some d =>
        rw [hd] at hdec; dsimp only at hdec
        dsimp only [mrDecodeEnumVariant] at hdec
        cases hm1 : (Neg.neg 1 == d) with
        | true =>
          rw [hm1, if_true_eq_true] at hdec
          cases hdv : mrDecode (emptySizedTy 1 1) bs with
          | none => rw [hdv] at hdec; cases hdec
          | some dv =>
            rw [hdv] at hdec; injection hdec with hv; subst hv
            rw [mrDecode_emptySized_eq_unit 1 1 bs dv hdv, ← eq_of_beq hm1]
            exact ⟨[.init 255], rfl⟩
        | false =>
          rw [hm1, if_false_eq_true] at hdec
          cases hm0 : ((0 : Int) == d) with
          | true =>
            rw [hm0, if_true_eq_true] at hdec
            cases hdv : mrDecode (emptySizedTy 1 1) bs with
            | none => rw [hdv] at hdec; cases hdec
            | some dv =>
              rw [hdv] at hdec; injection hdec with hv; subst hv
              rw [mrDecode_emptySized_eq_unit 1 1 bs dv hdv, ← eq_of_beq hm0]
              exact ⟨[.init 0], rfl⟩
          | false =>
            rw [hm0, if_false_eq_true] at hdec
            cases hmP1 : ((1 : Int) == d) with
            | true =>
              rw [hmP1, if_true_eq_true] at hdec
              cases hdv : mrDecode (emptySizedTy 1 1) bs with
              | none => rw [hdv] at hdec; cases hdec
              | some dv =>
                rw [hdv] at hdec; injection hdec with hv; subst hv
                rw [mrDecode_emptySized_eq_unit 1 1 bs dv hdv, ← eq_of_beq hmP1]
                exact ⟨[.init 1], rfl⟩
            | false => rw [hmP1, if_false_eq_true] at hdec; cases hdec
  | enum ety =>
    dsimp only [isSupportedScalarOrUnitTy] at hsupp
    dsimp only [translateTy, translateEnumTy] at hdec
    dsimp only [translateTy, translateEnumTy]
    cases hrepr : ety.tagRepr with
    | zeroSized =>
      rw [hrepr] at hdec; dsimp only
      dsimp only [mrDecode, MrType.size, decodeDiscriminant, mrDecodeEnumVariant] at hdec
      cases hlen : Nat.beq bs.length 0 with
      | false => rw [hlen, if_not_false] at hdec; cases hdec
      | true =>
        rw [hlen, if_not_true, beq_self_eq_true, if_true_eq_true] at hdec
        cases hdv : mrDecode unitTy bs with
        | none => rw [hdv] at hdec; cases hdec
        | some dv =>
          rw [hdv] at hdec; injection hdec with hv; subst hv
          rw [mrDecode_emptySized_eq_unit 0 1 bs dv hdv]
          dsimp only [mrEncode, mrEncodeEnumVariant]
          rw [beq_self_eq_true, if_true_eq_true]; exact ⟨[], rfl⟩
    | scalar tagW tagS =>
      rw [hrepr] at hdec; dsimp only
      dsimp only [mrDecode, MrType.size] at hdec
      cases hlen : Nat.beq bs.length tagW.byteSize with
      | false => rw [hlen, if_not_false] at hdec; cases hdec
      | true =>
        rw [hlen, if_not_true] at hdec
        cases hd : decodeDiscriminant bs _ with
        | none => rw [hd] at hdec; cases hdec
        | some d =>
          rw [hd] at hdec; dsimp only at hdec
          cases hdv : mrDecodeEnumVariant d
              (buildEnumVariants ety tagW tagS ety.discriminants) bs with
          | none => rw [hdv] at hdec; cases hdec
          | some dv =>
            rw [hdv] at hdec; injection hdec with hv; subst hv
            exact mrDecodeEnumVariant_build_encodable ety tagW tagS d bs dv
              ety.discriminants hdv
  | tuple fs =>
    dsimp only [isSupportedScalarOrUnitTy, isOverflowPairTy] at hsupp
    cases fs with
    | nil => cases hsupp
    | cons t0 rest =>
      cases t0 with
      | int w s =>
        cases rest with
        | nil => cases hsupp
        | cons t1 rest2 =>
          cases t1 with
          | bool =>
            cases rest2 with
            | cons _ _ => cases hsupp
            | nil =>
              dsimp only [translateTy, IntType.withOverflow, translateIntTy,
                mrDecode, mrDecodeFields, MrType.size] at hdec
              cases hlen : Nat.beq bs.length (2 * w.byteSize) with
              | false => rw [hlen, if_not_false] at hdec; cases hdec
              | true =>
                rw [hlen, if_not_true] at hdec
                cases hd0 : decodeInt (translateIntTy w s)
                    (byteSubslice bs 0 w.byteSize) with
                | none =>
                  dsimp only [translateIntTy] at hd0
                  rw [hd0] at hdec; cases hdec
                | some i =>
                  have henc0 := decodeInt_encodable (translateIntTy w s) _ i
                    (intWidth_bitWidth_pos w) hd0
                  dsimp only [translateIntTy] at hd0 henc0
                  rw [hd0] at hdec; dsimp only at hdec
                  cases hd1 : mrDecode .bool (byteSubslice bs w.byteSize 1) with
                  | none =>
                    have hd1' := hd1; dsimp only [mrDecode] at hd1'
                    rw [hd1'] at hdec; cases hdec
                  | some v1 =>
                    have hd1' := hd1; dsimp only [mrDecode] at hd1'
                    rw [hd1'] at hdec; dsimp only at hdec
                    injection hdec with hv; subst hv
                    cases mrDecode_bool_encodable _ v1 hd1 with
                    | intro bs1 hbs1 =>
                      cases henc0 with
                      | intro bs0 hbs0 =>
                        dsimp only [translateTy, IntType.withOverflow,
                          translateIntTy, mrEncode, mrEncodeFields]
                        rw [hbs0, hbs1]; exact ⟨_, rfl⟩
          | _ => cases hsupp
      | _ => cases hsupp
  | _ => cases hsupp

private theorem mrEncode_int_elim {it : IntType} {v : MrValue}
    {bs : List AbstractByte} (h : mrEncode (.int it) v = some bs) :
    ∃ i, v = .int i ∧ it.canRepresent i = true := by
  cases v with
  | int i =>
    dsimp only [mrEncode, encodeInt] at h
    cases hc : it.canRepresent i with
    | false => rw [hc, if_not_false] at h; cases h
    | true => exact ⟨i, rfl, hc⟩
  | _ => cases h

private theorem mrEncode_bool_elim {v : MrValue} {bs : List AbstractByte}
    (h : mrEncode .bool v = some bs) :
    ∃ b, v = .bool b := by
  cases v with
  | bool b => exact ⟨b, rfl⟩
  | _ => cases h

private def ExprWF (mirTy : MirTy)
    (res : Except EvalError (MrValue × MrType)) : Prop :=
  (∀ r, res ≠ .error (.illFormed r)) ∧
  (∀ v rty, res = .ok (v, rty) →
    rty = translateTy mirTy ∧ ∃ bs, mrEncode rty v = some bs)

private theorem exprWF_of_ok (mirTy : MirTy) (val : MrValue)
    {res : Except EvalError (MrValue × MrType)}
    (hok : res = .ok (val, translateTy mirTy))
    (henc : ∃ bs, mrEncode (translateTy mirTy) val = some bs) :
    ExprWF mirTy res := by
  rw [hok]
  refine ⟨(fun _ h => by cases h), fun v rty h => ?_⟩
  injection h with h1; injection h1 with hv hr
  subst hv; subst hr; exact ⟨rfl, henc⟩

private theorem exprWF_of_ub (mirTy : MirTy) {msg : String}
    {res : Except EvalError (MrValue × MrType)}
    (hub : res = .error (.ub msg)) : ExprWF mirTy res := by
  rw [hub]; exact ⟨(fun _ h => by cases h), (fun _ _ h => by cases h)⟩

private theorem exprWF_of_err (mirTy : MirTy) {err : EvalError}
    {res : Except EvalError (MrValue × MrType)} (herr : res = .error err)
    (hnoIF : ∀ r, err ≠ .illFormed r) : ExprWF mirTy res := by
  rw [herr]
  cases err with
  | ub _ => exact ⟨(fun _ h => by cases h), (fun _ _ h => by cases h)⟩
  | illFormed r => exact False.elim (hnoIF r rfl)

private theorem evalTransmute_exprWF (oldVal : MrValue) (oldTy : MrType)
    (targetMirTy : MirTy) (hsupp : isSupportedScalarOrUnitTy targetMirTy = true)
    (hsz : oldTy.size.bytes = (translateTy targetMirTy).size.bytes)
    (henc : ∃ bs, mrEncode oldTy oldVal = some bs) :
    ExprWF targetMirTy
      (Anneal.MiniRust.evalUnOp (.cast (.transmute (translateTy targetMirTy)))
        oldVal oldTy) := by
  cases henc with
  | intro bs hbs =>
    have hszF : (!Nat.beq oldTy.size.bytes (translateTy targetMirTy).size.bytes) =
        false := by
      rw [hsz, Nat.beq_refl]; rfl
    dsimp only [Anneal.MiniRust.evalUnOp, evalCastOp, evalTransmute]
    rw [hszF, if_false_eq_true, hbs]; dsimp only
    cases hdec : mrDecode (translateTy targetMirTy) bs with
    | none => exact exprWF_of_ub targetMirTy rfl
    | some v' =>
      exact exprWF_of_ok targetMirTy v' rfl
        (mrDecode_encodable targetMirTy bs v' hsupp hdec)

private theorem evalConst_mrWF (c : ConstOperand) (frame : StackFrame)
    (mem : MrMemory) (hadm : constAdmitted false c = true) :
    ExprWF c.ty (evalValue frame mem (translateConst c)) := by
  cases c with
  | mk ty lit =>
    cases ty with
    | int w s =>
      cases lit with
      | scalar bits =>
        cases decodeInt_encodeInt (translateIntTy w s) (decodeScalar ⟨w, s, bits⟩)
            (intWidth_bitWidth_pos w) (canRepresent_decodeScalar w s bits) with
        | intro bs hbs =>
          exact exprWF_of_ok (.int w s) (.int (decodeScalar ⟨w, s, bits⟩)) rfl
            ⟨bs, hbs.1⟩
      | _ => cases hadm
    | bool =>
      cases lit with
      | scalar bits =>
        dsimp only [constAdmitted] at hadm
        have htrunc : truncateBits .i8 bits = bits := eq_of_beq hadm
        have hlt256 : bits.toNat < 256 := by
          rw [← htrunc, truncateBits_toNat]; exact Nat.mod_lt _ (by decide)
        dsimp only [translateConst]
        cases h0 : (UInt8.ofNat (truncateBits .i8 bits).toNat == 0) with
        | true =>
          rw [if_true_eq_true]
          exact exprWF_of_ok .bool (.bool false) rfl ⟨[.init 0], rfl⟩
        | false =>
          rw [if_false_eq_true]
          cases h1 : (UInt8.ofNat (truncateBits .i8 bits).toNat == 1) with
          | true =>
            rw [if_true_eq_true]
            exact exprWF_of_ok .bool (.bool true) rfl ⟨[.init 1], rfl⟩
          | false =>
            rw [if_false_eq_true]
            have hcan : u8Ty.canRepresent
                (Int.ofNat (truncateBits .i8 bits).toNat) = true := by
              rw [htrunc]
              change (decide ((0 : Int) ≤ Int.ofNat bits.toNat) &&
                decide (Int.ofNat bits.toNat < Int.ofNat 256)) = true
              rw [decide_eq_true (int_ofNat_zero_le _),
                decide_eq_true (int_ofNat_lt_ofNat hlt256)]; rfl
            cases decodeInt_encodeInt u8Ty (Int.ofNat (truncateBits .i8 bits).toNat)
                (by decide) hcan with
            | intro bs hbs =>
              exact evalTransmute_exprWF
                (.int (Int.ofNat (truncateBits .i8 bits).toNat)) (.int u8Ty)
                .bool rfl rfl ⟨bs, hbs.1⟩
      | _ => cases hadm
    | unit =>
      cases lit with
      | zeroSized => exact exprWF_of_ok .unit (.tuple .nil) rfl ⟨[], rfl⟩
      | _ => cases hadm
    | char =>
      cases lit with
      | scalar bits =>
        have hlt32 : (truncateBits .i32 bits).toNat < Nat.pow 2 32 := by
          rw [truncateBits_toNat]; exact Nat.mod_lt _ (by decide)
        have hcan : u32Ty.canRepresent
            (Int.ofNat (truncateBits .i32 bits).toNat) = true := by
          change (decide ((0 : Int) ≤ Int.ofNat (truncateBits .i32 bits).toNat) &&
            decide (Int.ofNat (truncateBits .i32 bits).toNat <
              Int.ofNat (Nat.pow 2 32))) = true
          rw [decide_eq_true (int_ofNat_zero_le _),
            decide_eq_true (int_ofNat_lt_ofNat hlt32)]; rfl
        cases decodeInt_encodeInt u32Ty (Int.ofNat (truncateBits .i32 bits).toNat)
            (by decide) hcan with
        | intro bs hbs =>
          exact exprWF_of_ok .char
            (.int (Int.ofNat (truncateBits .i32 bits).toNat)) rfl ⟨bs, hbs.1⟩
      | _ => cases hadm
    | ordering =>
      cases lit with
      | scalar bits =>
        cases hord : orderingOfTagBits bits.toNat with
        | some ord =>
          have hev : evalValue frame mem (translateConst ⟨.ordering, .scalar bits⟩) =
              .ok (translateVal (.ordering ord), translateTy .ordering) := by
            dsimp only [translateConst]; rw [hord]; cases ord <;> rfl
          cases ord with
          | less =>
            exact exprWF_of_ok .ordering (translateVal (.ordering .less)) hev
              ⟨[.init 255], rfl⟩
          | equal =>
            exact exprWF_of_ok .ordering (translateVal (.ordering .equal)) hev
              ⟨[.init 0], rfl⟩
          | greater =>
            exact exprWF_of_ok .ordering (translateVal (.ordering .greater)) hev
              ⟨[.init 1], rfl⟩
        | none =>
          dsimp only [translateConst]; rw [hord]
          cases decodeInt_encodeInt i8Ty (decodeScalar ⟨.i8, true, bits⟩)
              (by decide) (canRepresent_decodeScalar .i8 true bits) with
          | intro bs hbs =>
            exact evalTransmute_exprWF (.int (decodeScalar ⟨.i8, true, bits⟩))
              (.int i8Ty) .ordering rfl rfl ⟨bs, hbs.1⟩
      | _ => cases hadm
    | enum ety =>
      cases lit with
      | rodataBytes _ | rodataRef _ _ _ _ => cases hadm
      | zeroSized =>
        dsimp only [constAdmitted, isZstEnumTy] at hadm
        cases hrepr : ety.tagRepr with
        | scalar _ _ => rw [hrepr] at hadm; cases hadm
        | zeroSized =>
          refine exprWF_of_ok (.enum ety) (translateVal (.enumVal ety 0))
            (evalValue_translateConst_enum_zeroSized ety frame mem hrepr)
            ⟨[], ?_⟩
          dsimp only [translateTy, translateEnumTy, translateVal]
          rw [hrepr]
          dsimp only [mrEncode, mrEncodeEnumVariant]
          rw [beq_self_eq_true, if_true_eq_true]; rfl
      | scalar bits =>
        dsimp only [constAdmitted] at hadm
        cases hrepr : ety.tagRepr with
        | zeroSized => rw [hrepr] at hadm; cases hadm
        | scalar tagW tagS =>
          rw [hrepr] at hadm
          cases hea : enumAdmitted ety with
          | false => rw [hea] at hadm; cases hadm
          | true =>
            cases hfind : findDiscrVariant?
                (tagBitsToDiscrBits tagW tagS ety.discrWidth bits)
                ety.discriminants with
            | some vIdx =>
              cases findDiscrVariant?_lt _ _ _ hfind with
              | intro _ hdEx =>
                cases hdEx with
                | intro d hd =>
                  have hd' : Trusted.MirSemantics.getElem? ety.discriminants vIdx =
                      some d := by
                    rw [getElem?_eq_listGet?]; exact hd.1
                  cases enum_discriminant_decode_roundtrip ety tagW tagS hrepr
                      hea vIdx d hd' with
                  | intro bs hbs =>
                    exact exprWF_of_ok (.enum ety)
                      (translateVal (.enumVal ety vIdx))
                      (evalValue_translateConst_enum_scalar ety tagW tagS bits
                        vIdx frame mem hrepr hfind)
                      ⟨bs, hbs.1⟩
            | none =>
              dsimp only [translateConst]; rw [hrepr]; dsimp only; rw [hfind]
              cases decodeInt_encodeInt (translateIntTy tagW tagS)
                  (decodeScalar ⟨tagW, tagS, bits⟩) (intWidth_bitWidth_pos tagW)
                  (canRepresent_decodeScalar tagW tagS bits) with
              | intro bs hbs =>
                have hsz : (MrType.int (translateIntTy tagW tagS)).size.bytes =
                    (translateTy (.enum ety)).size.bytes := by
                  dsimp only [translateTy, translateEnumTy, MrType.size]
                  rw [hrepr]; rfl
                exact evalTransmute_exprWF
                  (.int (decodeScalar ⟨tagW, tagS, bits⟩))
                  (.int (translateIntTy tagW tagS)) (.enum ety) hea hsz
                  ⟨bs, hbs.1⟩
    | _ => cases hadm

private theorem evalOperand_mrWF (bodyLocals : List MirTy) (opnd : Operand)
    (opTy : MirTy) (frame : StackFrame) (mem : MrMemory)
    (hsupp : bodyLocals.all isSupportedScalarOrUnitTy = true)
    (hfnLoc : frame.func.locals = bodyLocals.map translateTy)
    (hadm : operandAdmitted false bodyLocals opnd = true)
    (hty : operandTy? bodyLocals opnd = some opTy) :
    ExprWF opTy (evalValue frame mem (translateOperand opnd)) := by
  cases opnd with
  | copy place | move place =>
    dsimp only [operandTy?] at hty
    cases hp : place.projection.isEmpty with
    | false => rw [hp, if_false_eq_true] at hty; cases hty
    | true =>
      rw [hp, if_true_eq_true] at hty
      have htyList : listGet? bodyLocals place.localId = some opTy := by
        rw [← getElem?_eq_listGet?]; exact hty
      have hopSupp : isSupportedScalarOrUnitTy opTy = true :=
        listGet?_all isSupportedScalarOrUnitTy bodyLocals place.localId opTy
          hsupp htyList
      have hmrLoc : listGet? frame.func.locals place.localId =
          some (translateTy opTy) := by
        rw [hfnLoc, listGet?_map, htyList]; rfl
      dsimp only [translateOperand, evalValue, evalPlace]
      rw [hmrLoc]; dsimp only
      cases localMapGet? place.localId frame.locals with
      | none => exact exprWF_of_ub opTy rfl
      | some ptr =>
        dsimp only; rw [if_not_true]
        dsimp only [typedLoad]
        cases mem.load ptr (translateTy opTy).size ⟨1⟩ with
        | error _ => exact exprWF_of_ub opTy rfl
        | ok bytes =>
          dsimp only
          cases hdec : mrDecode (translateTy opTy) bytes with
          | none => exact exprWF_of_ub opTy rfl
          | some val =>
            exact exprWF_of_ok opTy val rfl
              (mrDecode_encodable opTy bytes val hopSupp hdec)
  | constant c =>
    dsimp only [operandAdmitted] at hadm
    dsimp only [operandTy?] at hty
    injection hty with hce; subst hce
    exact evalConst_mrWF c frame mem hadm

private theorem evalDiscrBranchesMem_build_wf (mem : MrMemory) (ptr : ThinPtr)
    (tv : Int) (ety : EnumTy) (tagW : IntWidth) (tagS : Bool) :
    ∀ (ds : List Nat),
      (∀ r, evalDiscrBranchesMem mem ptr tv (buildEnumBranches ety tagW tagS ds) ≠
        .error (.illFormed r)) ∧
      (∀ d, evalDiscrBranchesMem mem ptr tv (buildEnumBranches ety tagW tagS ds) =
          .ok (some (some d)) →
        (translateIntTy ety.discrWidth ety.discrSigned).canRepresent d = true) := by
  intro ds
  induction ds with
  | nil => exact ⟨(fun _ h => by cases h), (fun _ h => by cases h)⟩
  | cons x rest ih =>
    dsimp only [buildEnumBranches, evalDiscrBranchesMem]
    cases hc : (decide (tagIntOfNat tagW tagS x ≤ tv) &&
        decide (tv < tagIntOfNat tagW tagS x + 1)) with
    | false => rw [if_false_eq_true]; exact ih
    | true =>
      rw [if_true_eq_true]; dsimp only [evalDiscriminantMem]
      refine ⟨(fun _ h => by cases h), fun d h => ?_⟩
      injection h with h1; injection h1 with h2; injection h2 with hd
      rw [← hd]; exact canRepresent_decodeScalar ety.discrWidth ety.discrSigned _

private theorem evalRvalue_mrWF (bodyLocals : List MirTy) (dstTy : MirTy)
    (rv : Rvalue) (frame : StackFrame) (mem : MrMemory)
    (hsupp : bodyLocals.all isSupportedScalarOrUnitTy = true)
    (hfnLoc : frame.func.locals = bodyLocals.map translateTy)
    (hadm : rvalueAdmitted false bodyLocals dstTy rv = true) :
    ExprWF dstTy (evalValue frame mem (translateRvalue bodyLocals rv)) := by
  cases rv with
  | use opnd =>
    dsimp only [rvalueAdmitted] at hadm
    cases hoa : operandAdmitted false bodyLocals opnd with
    | false => rw [hoa] at hadm; cases hadm
    | true =>
      rw [hoa, Bool.true_and] at hadm
      cases hot : operandTy? bodyLocals opnd with
      | none => rw [hot] at hadm; cases hadm
      | some srcTy =>
        rw [hot] at hadm
        have heq := mirTy_eq_of_beq hadm; subst heq
        exact evalOperand_mrWF bodyLocals opnd srcTy frame mem hsupp hfnLoc hoa hot
  | unaryOp op opnd =>
    dsimp only [rvalueAdmitted] at hadm
    cases hoa : operandAdmitted false bodyLocals opnd with
    | false => rw [hoa] at hadm; cases hadm
    | true =>
      rw [hoa, Bool.true_and] at hadm
      cases hot : operandTy? bodyLocals opnd with
      | none => rw [hot] at hadm; cases op <;> cases hadm
      | some srcTy =>
        rw [hot] at hadm
        have hop := evalOperand_mrWF bodyLocals opnd srcTy frame mem hsupp hfnLoc
          hoa hot
        dsimp only [translateRvalue]; rw [hot]
        cases op with
        | ptrMetadata => cases hadm
        | not =>
          cases srcTy with
          | bool =>
            have hdst := mirTy_eq_of_beq hadm; subst hdst
            dsimp only [evalValue]
            cases hev : evalValue frame mem (translateOperand opnd) with
            | error err =>
              exact exprWF_of_err .bool rfl (fun r hr => hop.1 r (by rw [hev, hr]))
            | ok pr =>
              cases pr with
              | mk val rty =>
                have hwf := hop.2 val rty hev
                cases hwf.2 with
                | intro _ hbs =>
                  rw [hwf.1] at hbs
                  cases mrEncode_bool_elim hbs with
                  | intro b hb =>
                    have hrty := hwf.1; subst hb; subst hrty
                    cases b with
                    | false => exact exprWF_of_ok .bool (.bool true) rfl ⟨[.init 1], rfl⟩
                    | true => exact exprWF_of_ok .bool (.bool false) rfl ⟨[.init 0], rfl⟩
          | int w s =>
            have hdst := mirTy_eq_of_beq hadm; subst hdst
            dsimp only [evalValue]
            cases hev : evalValue frame mem (translateOperand opnd) with
            | error err =>
              exact exprWF_of_err (.int w s) rfl
                (fun r hr => hop.1 r (by rw [hev, hr]))
            | ok pr =>
              cases pr with
              | mk val rty =>
                have hwf := hop.2 val rty hev
                cases hwf.2 with
                | intro _ hbs =>
                  rw [hwf.1] at hbs
                  cases mrEncode_int_elim hbs with
                  | intro i hi =>
                    have hv := hi.1; have hrty := hwf.1; subst hv; subst hrty
                    cases decodeInt_encodeInt (translateIntTy w s)
                        ((translateIntTy w s).bringInBounds (mrIntNot i))
                        (intWidth_bitWidth_pos w)
                        (bringInBounds_canRepresent (translateIntTy w s) _
                          (intWidth_bitWidth_pos w)) with
                    | intro bs' hbs' =>
                      exact exprWF_of_ok (.int w s) _ rfl ⟨bs', hbs'.1⟩
          | _ => cases hadm
        | neg =>
          cases srcTy with
          | int w s =>
            cases s with
            | false => cases hadm
            | true =>
              have hdst := mirTy_eq_of_beq hadm; subst hdst
              dsimp only [evalValue]
              cases hev : evalValue frame mem (translateOperand opnd) with
              | error err =>
                exact exprWF_of_err (.int w true) rfl
                  (fun r hr => hop.1 r (by rw [hev, hr]))
              | ok pr =>
                cases pr with
                | mk val rty =>
                  have hwf := hop.2 val rty hev
                  cases hwf.2 with
                  | intro _ hbs =>
                    rw [hwf.1] at hbs
                    cases mrEncode_int_elim hbs with
                    | intro i hi =>
                      have hv := hi.1; have hrty := hwf.1; subst hv; subst hrty
                      cases decodeInt_encodeInt (translateIntTy w true)
                          ((translateIntTy w true).bringInBounds (Neg.neg i))
                          (intWidth_bitWidth_pos w)
                          (bringInBounds_canRepresent (translateIntTy w true) _
                            (intWidth_bitWidth_pos w)) with
                      | intro bs' hbs' =>
                        exact exprWF_of_ok (.int w true) _ rfl ⟨bs', hbs'.1⟩
          | _ => cases hadm
  | binaryOp op lhs rhs =>
    dsimp only [rvalueAdmitted] at hadm
    cases hla : operandAdmitted false bodyLocals lhs with
    | false => rw [hla] at hadm; cases hadm
    | true =>
      cases hra : operandAdmitted false bodyLocals rhs with
      | false => rw [hla, hra] at hadm; cases hadm
      | true =>
        rw [hla, hra, Bool.true_and, Bool.true_and] at hadm
        cases hlt : operandTy? bodyLocals lhs with
        | none => rw [hlt] at hadm; cases hadm
        | some lTy =>
          cases hrt : operandTy? bodyLocals rhs with
          | none => rw [hlt, hrt] at hadm; cases hadm
          | some rTy =>
            rw [hlt, hrt] at hadm; dsimp only at hadm
            cases hbr : binOpResultTy? op lTy rTy with
            | none => rw [hbr] at hadm; cases hadm
            | some resTy =>
              rw [hbr] at hadm
              have hresEq := mirTy_eq_of_beq hadm; subst hresEq
              have hlWF := evalOperand_mrWF bodyLocals lhs lTy frame mem hsupp
                hfnLoc hla hlt
              have hrWF := evalOperand_mrWF bodyLocals rhs rTy frame mem hsupp
                hfnLoc hra hrt
              dsimp only [translateRvalue]; rw [hlt]
              cases lTy with
              | int w s =>
                cases rTy with
                | int rw_ rs =>
                  cases hel : evalValue frame mem (translateOperand lhs) with
                  | error err =>
                    have hnoIF : ∀ r, err ≠ .illFormed r :=
                      fun r hr => hlWF.1 r (by rw [hel, hr])
                    cases op <;> (
                      dsimp only [translateIntBinOp?, translateWithOverflowOp?,
                        translateRelOp?, evalValue]
                      rw [hel]; exact exprWF_of_err resTy rfl hnoIF)
                  | ok pl =>
                    cases pl with
                    | mk lv lrty =>
                      have hlwf := hlWF.2 lv lrty hel
                      cases hlwf.2 with
                      | intro _ hlbs =>
                        rw [hlwf.1] at hlbs
                        cases mrEncode_int_elim hlbs with
                        | intro li hli =>
                          have hlv := hli.1; have hlr := hlwf.1; subst hlv; subst hlr
                          cases her : evalValue frame mem (translateOperand rhs) with
                          | error err =>
                            have hnoIF : ∀ r, err ≠ .illFormed r :=
                              fun r hr => hrWF.1 r (by rw [her, hr])
                            cases op with
                            | offset =>
                              have hns : BinOp.offset.isShift = false := rfl
                              dsimp only [binOpResultTy?] at hbr
                              rw [ite_bool_false hns] at hbr
                              cases hb : MirTy.beq (.int w s) (.int rw_ rs) <;>
                                (rw [hb] at hbr; cases hbr)
                            | _ =>
                              dsimp only [translateIntBinOp?,
                                translateWithOverflowOp?, translateRelOp?, evalValue]
                              rw [hel, her]
                              exact exprWF_of_err resTy rfl hnoIF
                          | ok pr =>
                            cases pr with
                            | mk rv_ rrty =>
                              have hrwf := hrWF.2 rv_ rrty her
                              cases hrwf.2 with
                              | intro _ hrbs =>
                                rw [hrwf.1] at hrbs
                                cases mrEncode_int_elim hrbs with
                                | intro ri hri =>
                                  have hrv := hri.1; have hrr := hrwf.1; subst hrv; subst hrr
                                  have hIntOp : ∀ iop : IntBinOp,
                                      ExprWF (.int w s)
                                        (Anneal.MiniRust.evalBinOp (.int iop)
                                          (.int li) (.int (translateIntTy w s))
                                          (.int ri)) := by
                                    intro iop
                                    dsimp only [Anneal.MiniRust.evalBinOp]
                                    have hnotIF : ∀ r,
                                        evalIntBinOp iop li ri (translateIntTy w s) ≠
                                          .error (.illFormed r) := by
                                      have hite : ∀ {c : Bool} {a b : Except EvalError Int} {r : String},
                                          a ≠ .error (.illFormed r) → b ≠ .error (.illFormed r) →
                                          (if c then a else b) ≠ .error (.illFormed r) := by
                                        intro c _ _ _ ha hb
                                        cases c with
                                        | true => exact ha
                                        | false => exact hb
                                      have hbw0 : (translateIntTy w s).bitWidth.beq 0 =
                                          false := by cases w <;> rfl
                                      intro r
                                      cases iop with
                                      | add | sub | mul | bitAnd | bitOr | bitXor =>
                                        intro h; cases h
                                      | addUnchecked | subUnchecked | mulUnchecked
                                      | shlUnchecked | shrUnchecked =>
                                        exact hite (fun h => by cases h) (fun h => by cases h)
                                      | div | rem =>
                                        exact hite (fun h => by cases h)
                                          (hite (fun h => by cases h) (fun h => by cases h))
                                      | divExact =>
                                        exact hite (fun h => by cases h)
                                          (hite (fun h => by cases h)
                                            (hite (fun h => by cases h) (fun h => by cases h)))
                                      | shl | shr =>
                                        dsimp only [evalIntBinOp]; rw [ite_bool_false hbw0]
                                        intro h; cases h
                                    cases hio : evalIntBinOp iop li ri
                                        (translateIntTy w s) with
                                    | error err =>
                                      exact exprWF_of_err (.int w s) rfl
                                        (fun r hr => hnotIF r (by rw [hio, hr]))
                                    | ok raw =>
                                      cases decodeInt_encodeInt (translateIntTy w s)
                                          ((translateIntTy w s).bringInBounds raw)
                                          (intWidth_bitWidth_pos w)
                                          (bringInBounds_canRepresent (translateIntTy w s)
                                            raw (intWidth_bitWidth_pos w)) with
                                      | intro bs' hbs' =>
                                        exact exprWF_of_ok (.int w s) _ rfl ⟨bs', hbs'.1⟩
                                  cases op with
                                  | shl | shr | shlUnchecked | shrUnchecked =>
                                    dsimp only [binOpResultTy?, BinOp.isShift] at hbr
                                    injection hbr with hre; subst hre
                                    dsimp only [translateIntBinOp?, evalValue]
                                    rw [hel, her]; exact hIntOp _
                                  | add | sub | mul | div | rem | addUnchecked
                                  | subUnchecked | mulUnchecked | bitAnd | bitOr
                                  | bitXor =>
                                    dsimp only [binOpResultTy?, BinOp.isShift] at hbr
                                    cases hb : MirTy.beq (.int w s) (.int rw_ rs) with
                                    | false => rw [hb, if_not_false] at hbr; cases hbr
                                    | true =>
                                      rw [hb, if_not_true] at hbr
                                      injection hbr with hre; subst hre
                                      dsimp only [translateIntBinOp?, evalValue]
                                      rw [hel, her]; exact hIntOp _
                                  | addWithOverflow | subWithOverflow | mulWithOverflow =>
                                    dsimp only [binOpResultTy?, BinOp.isShift] at hbr
                                    cases hb : MirTy.beq (.int w s) (.int rw_ rs) with
                                    | false => rw [hb, if_not_false] at hbr; cases hbr
                                    | true =>
                                      rw [hb, if_not_true] at hbr
                                      injection hbr with hre; subst hre
                                      dsimp only [translateIntBinOp?,
                                        translateWithOverflowOp?, evalValue]
                                      rw [hel, her]
                                      dsimp only [Anneal.MiniRust.evalBinOp]
                                      cases decodeInt_encodeInt (translateIntTy w s)
                                          ((translateIntTy w s).bringInBounds _)
                                          (intWidth_bitWidth_pos w)
                                          (bringInBounds_canRepresent (translateIntTy w s)
                                            _ (intWidth_bitWidth_pos w)) with
                                      | intro bs0 hbs0 =>
                                        refine exprWF_of_ok (.tuple [.int w s, .bool])
                                          _ rfl ?_
                                        dsimp only [translateTy, IntType.withOverflow,
                                          mrEncode, mrEncodeFields]
                                        rw [hbs0.1]; exact ⟨_, rfl⟩
                                  | eq | ne | lt | le | gt | ge =>
                                    dsimp only [binOpResultTy?, BinOp.isShift] at hbr
                                    cases hb : MirTy.beq (.int w s) (.int rw_ rs) with
                                    | false => rw [hb, if_not_false] at hbr; cases hbr
                                    | true =>
                                      rw [hb, if_not_true] at hbr
                                      injection hbr with hre; subst hre
                                      dsimp only [translateIntBinOp?,
                                        translateWithOverflowOp?, translateRelOp?,
                                        evalValue]
                                      rw [hel, her]
                                      dsimp only [Anneal.MiniRust.evalBinOp, evalRelOp]
                                      exact exprWF_of_ok .bool _ rfl ⟨_, rfl⟩
                                  | cmp =>
                                    dsimp only [binOpResultTy?, BinOp.isShift] at hbr
                                    cases hb : MirTy.beq (.int w s) (.int rw_ rs) with
                                    | false => rw [hb, if_not_false] at hbr; cases hbr
                                    | true =>
                                      rw [hb, if_not_true] at hbr
                                      injection hbr with hre; subst hre
                                      dsimp only [translateIntBinOp?,
                                        translateWithOverflowOp?, translateRelOp?,
                                        evalValue]
                                      rw [hel, her]
                                      dsimp only [translateTy,
                                        Anneal.MiniRust.evalBinOp, evalRelOp,
                                        Anneal.MiniRust.evalUnOp, evalCastOp]
                                      cases cmpInt li ri with
                                      | less =>
                                        exact exprWF_of_ok .ordering _ rfl ⟨[.init 255], rfl⟩
                                      | equal =>
                                        exact exprWF_of_ok .ordering _ rfl ⟨[.init 0], rfl⟩
                                      | greater =>
                                        exact exprWF_of_ok .ordering _ rfl ⟨[.init 1], rfl⟩
                                  | offset =>
                                    have hns : BinOp.offset.isShift = false := rfl
                                    dsimp only [binOpResultTy?] at hbr
                                    rw [ite_bool_false hns] at hbr
                                    cases hb : MirTy.beq (.int w s) (.int rw_ rs) <;>
                                      (rw [hb] at hbr; cases hbr)
                | _ => cases hbr
              | bool =>
                cases rTy with
                | bool =>
                  have hresB : resTy = .bool := by
                    cases op <;> cases hbr <;> rfl
                  subst hresB
                  cases hel : evalValue frame mem (translateOperand lhs) with
                  | error err =>
                    have hnoIF : ∀ r, err ≠ .illFormed r :=
                      fun r hr => hlWF.1 r (by rw [hel, hr])
                    cases op <;> (
                      dsimp only [translateRelOp?, evalValue]; rw [hel]
                      exact exprWF_of_err .bool rfl hnoIF)
                  | ok pl =>
                    cases pl with
                    | mk lv lrty =>
                      have hlwf := hlWF.2 lv lrty hel
                      cases hlwf.2 with
                      | intro _ hlbs =>
                        rw [hlwf.1] at hlbs
                        cases mrEncode_bool_elim hlbs with
                        | intro lb hlb =>
                          have hlr := hlwf.1; subst hlb; subst hlr
                          cases her : evalValue frame mem (translateOperand rhs) with
                          | error err =>
                            have hnoIF : ∀ r, err ≠ .illFormed r :=
                              fun r hr => hrWF.1 r (by rw [her, hr])
                            cases op with
                            | bitAnd | bitOr | bitXor =>
                              dsimp only [evalValue, Anneal.MiniRust.evalUnOp,
                                evalCastOp]
                              rw [hel]; dsimp only [translateTy]
                              rw [evalTransmute_bool_to_u8 lb]; dsimp only
                              rw [her]
                              exact exprWF_of_err .bool rfl hnoIF
                            | eq | ne | lt | le | gt | ge =>
                              dsimp only [translateRelOp?, evalValue]
                              rw [hel, her]
                              exact exprWF_of_err .bool rfl hnoIF
                            | _ => cases hbr
                          | ok pr =>
                            cases pr with
                            | mk rv_ rrty =>
                              have hrwf := hrWF.2 rv_ rrty her
                              cases hrwf.2 with
                              | intro _ hrbs =>
                                rw [hrwf.1] at hrbs
                                cases mrEncode_bool_elim hrbs with
                                | intro rb hrb =>
                                  have hrr := hrwf.1; subst hrb; subst hrr
                                  cases op with
                                  | eq | ne | lt | le | gt | ge =>
                                    dsimp only [translateRelOp?, evalValue]
                                    rw [hel, her]
                                    cases lb <;> cases rb <;>
                                      exact exprWF_of_ok .bool _ rfl ⟨_, rfl⟩
                                  | bitAnd | bitOr | bitXor =>
                                    dsimp only [evalValue]; rw [hel, her]
                                    cases lb <;> cases rb <;>
                                      exact exprWF_of_ok .bool _ rfl ⟨_, rfl⟩
                                  | _ => cases hbr
                | _ => cases hbr
              | char =>
                cases rTy with
                | char =>
                  cases hel : evalValue frame mem (translateOperand lhs) with
                  | error err =>
                    have hnoIF : ∀ r, err ≠ .illFormed r :=
                      fun r hr => hlWF.1 r (by rw [hel, hr])
                    cases op <;> (
                      dsimp only [translateRelOp?, evalValue]; rw [hel]
                      exact exprWF_of_err resTy rfl hnoIF)
                  | ok pl =>
                    cases pl with
                    | mk lv lrty =>
                      have hlwf := hlWF.2 lv lrty hel
                      cases hlwf.2 with
                      | intro _ hlbs =>
                        rw [hlwf.1] at hlbs
                        cases mrEncode_int_elim hlbs with
                        | intro li hli =>
                          have hlv := hli.1; have hlr := hlwf.1; subst hlv; subst hlr
                          cases her : evalValue frame mem (translateOperand rhs) with
                          | error err =>
                            have hnoIF : ∀ r, err ≠ .illFormed r :=
                              fun r hr => hrWF.1 r (by rw [her, hr])
                            cases op with
                            | eq | ne | lt | le | gt | ge | cmp =>
                              dsimp only [translateRelOp?, evalValue]
                              rw [hel, her]
                              exact exprWF_of_err resTy rfl hnoIF
                            | _ => cases hbr
                          | ok pr =>
                            cases pr with
                            | mk rv_ rrty =>
                              have hrwf := hrWF.2 rv_ rrty her
                              cases hrwf.2 with
                              | intro _ hrbs =>
                                rw [hrwf.1] at hrbs
                                cases mrEncode_int_elim hrbs with
                                | intro ri hri =>
                                  have hrv := hri.1; have hrr := hrwf.1; subst hrv; subst hrr
                                  cases op with
                                  | eq | ne | lt | le | gt | ge =>
                                    injection hbr with hre; subst hre
                                    dsimp only [translateRelOp?, evalValue, translateTy]
                                    rw [hel, her]
                                    exact exprWF_of_ok .bool _ rfl ⟨_, rfl⟩
                                  | cmp =>
                                    injection hbr with hre; subst hre
                                    dsimp only [translateRelOp?, evalValue]
                                    rw [hel, her]
                                    dsimp only [translateTy,
                                      Anneal.MiniRust.evalBinOp, evalRelOp,
                                      Anneal.MiniRust.evalUnOp, evalCastOp]
                                    cases cmpInt li ri with
                                    | less =>
                                      exact exprWF_of_ok .ordering _ rfl ⟨[.init 255], rfl⟩
                                    | equal =>
                                      exact exprWF_of_ok .ordering _ rfl ⟨[.init 0], rfl⟩
                                    | greater =>
                                      exact exprWF_of_ok .ordering _ rfl ⟨[.init 1], rfl⟩
                                  | _ => cases hbr
                | _ => cases hbr
              | _ => cases hbr
  | cast kind opnd castTy =>
    cases kind with
    | ptrToPtr | intToPtr | unsize | boxAsRef | unsupported => cases hadm
    | intToInt =>
      dsimp only [rvalueAdmitted] at hadm
      cases hoa : operandAdmitted false bodyLocals opnd with
      | false => rw [hoa] at hadm; cases hadm
      | true =>
        cases hct : MirTy.beq castTy dstTy with
        | false => rw [hoa, hct] at hadm; cases hadm
        | true =>
          rw [hoa, hct] at hadm
          have hdstEq := mirTy_eq_of_beq hct; subst hdstEq
          cases hot : operandTy? bodyLocals opnd with
          | none => rw [hot] at hadm; cases castTy <;> cases hadm
          | some srcTy =>
            rw [hot] at hadm
            have hop := evalOperand_mrWF bodyLocals opnd srcTy frame mem hsupp
              hfnLoc hoa hot
            dsimp only [translateRvalue]; rw [hot]
            have hCastHelper : ∀ (targetIt : IntType) (eInt : ValueExpr),
                0 < targetIt.bitWidth →
                translateTy castTy = .int targetIt →
                ((∀ r, evalValue frame mem eInt ≠ .error (.illFormed r)) ∧
                 (∀ v rty, evalValue frame mem eInt = .ok (v, rty) →
                   ∃ i it, v = .int i ∧ rty = .int it)) →
                ExprWF castTy
                  (evalValue frame mem
                    (.unOp (.cast (.intToInt targetIt)) eInt)) := by
              intro targetIt eInt hpos hty heIntWF
              dsimp only [evalValue]
              cases hei : evalValue frame mem eInt with
              | error err =>
                exact exprWF_of_err castTy rfl
                  (fun r hr => heIntWF.1 r (by rw [hei, hr]))
              | ok pr =>
                cases pr with
                | mk val rty =>
                  cases heIntWF.2 val rty hei with
                  | intro i hex => cases hex with | intro it hit =>
                    have hv := hit.1; have hr := hit.2; subst hv; subst hr
                    cases decodeInt_encodeInt targetIt (targetIt.bringInBounds i)
                        hpos (bringInBounds_canRepresent targetIt i hpos) with
                    | intro bs' hbs' =>
                      refine exprWF_of_ok castTy
                        (.int (targetIt.bringInBounds i)) (by rw [hty]; rfl)
                        ⟨bs', ?_⟩
                      rw [hty]; exact hbs'.1
            cases srcTy with
            | bool =>
              dsimp only
              have heB : (∀ r, evalValue frame mem
                  (.unOp (.cast (.transmute (.int u8Ty)))
                    (translateOperand opnd)) ≠ .error (.illFormed r)) ∧
                  (∀ v rty, evalValue frame mem
                    (.unOp (.cast (.transmute (.int u8Ty)))
                      (translateOperand opnd)) = .ok (v, rty) →
                    ∃ i it, v = .int i ∧ rty = .int it) := by
                dsimp only [evalValue]
                cases hev : evalValue frame mem (translateOperand opnd) with
                | error _ =>
                  exact ⟨(fun r h => hop.1 r (by rw [hev]; exact h)),
                    (fun _ _ h => by cases h)⟩
                | ok pr =>
                  cases pr with
                  | mk val rty =>
                    have hwf := hop.2 val rty hev
                    cases hwf.2 with
                    | intro _ hbs =>
                      rw [hwf.1] at hbs
                      cases mrEncode_bool_elim hbs with
                      | intro b hb =>
                        have hrty := hwf.1; subst hb; subst hrty
                        dsimp only [Anneal.MiniRust.evalUnOp, evalCastOp, translateTy]
                        rw [evalTransmute_bool_to_u8 b]
                        refine ⟨(fun _ h => by cases h), fun v rt h => ?_⟩
                        injection h with h1; injection h1 with hv hr
                        exact ⟨_, u8Ty, hv.symm, hr.symm⟩
              cases castTy with
              | int cw cs =>
                exact hCastHelper (translateIntTy cw cs) _
                  (intWidth_bitWidth_pos cw) rfl heB
              | char => cases hadm
              | _ => cases hadm
            | int sw ss =>
              dsimp only
              have heI : (∀ r, evalValue frame mem (translateOperand opnd) ≠
                  .error (.illFormed r)) ∧
                  (∀ v rty, evalValue frame mem (translateOperand opnd) =
                    .ok (v, rty) →
                    ∃ i it, v = .int i ∧ rty = .int it) := by
                refine ⟨hop.1, fun v rt h => ?_⟩
                have hwf := hop.2 v rt h
                cases hwf.2 with
                | intro _ hbs =>
                  rw [hwf.1] at hbs
                  cases mrEncode_int_elim hbs with
                  | intro i hi => exact ⟨i, translateIntTy sw ss, hi.1, hwf.1⟩
              cases castTy with
              | int cw cs =>
                exact hCastHelper (translateIntTy cw cs) _
                  (intWidth_bitWidth_pos cw) rfl heI
              | char =>
                exact hCastHelper u32Ty _ (by decide) rfl heI
              | _ => cases hadm
            | char =>
              dsimp only
              have heC : (∀ r, evalValue frame mem (translateOperand opnd) ≠
                  .error (.illFormed r)) ∧
                  (∀ v rty, evalValue frame mem (translateOperand opnd) =
                    .ok (v, rty) →
                    ∃ i it, v = .int i ∧ rty = .int it) := by
                refine ⟨hop.1, fun v rt h => ?_⟩
                have hwf := hop.2 v rt h
                cases hwf.2 with
                | intro _ hbs =>
                  rw [hwf.1] at hbs
                  cases mrEncode_int_elim hbs with
                  | intro i hi => exact ⟨i, u32Ty, hi.1, hwf.1⟩
              cases castTy with
              | int cw cs =>
                exact hCastHelper (translateIntTy cw cs) _
                  (intWidth_bitWidth_pos cw) rfl heC
              | char => cases hadm
              | _ => cases hadm
            | _ => cases castTy <;> cases hadm
  | discriminant place =>
    dsimp only [rvalueAdmitted] at hadm
    cases hp : place.projection.isEmpty with
    | false => rw [hp] at hadm; cases hadm
    | true =>
      rw [hp] at hadm
      cases hgetTy : Trusted.MirSemantics.getElem? bodyLocals place.localId with
      | none => rw [hgetTy] at hadm; cases hadm
      | some srcTy =>
        rw [hgetTy] at hadm
        have hmrLoc : listGet? frame.func.locals place.localId =
            some (translateTy srcTy) := by
          rw [hfnLoc, listGet?_map, ← getElem?_eq_listGet?, hgetTy]; rfl
        dsimp only [translateRvalue, evalValue, evalPlace]
        rw [hmrLoc]; dsimp only
        cases localMapGet? place.localId frame.locals with
        | none => exact exprWF_of_ub dstTy rfl
        | some ptr =>
          cases srcTy with
          | ordering =>
            dsimp only at hadm; rw [Bool.true_and] at hadm
            have hdstEq := mirTy_eq_of_beq hadm; subst hdstEq
            dsimp only [translateTy, orderingTy]; rw [if_not_true]
            dsimp only [evalDiscriminantMem]
            rw [ptrOffsetInbounds_zero]; dsimp only
            cases mem.load ptr i8Ty.size ⟨1⟩ with
            | error _ => exact exprWF_of_ub (.int .i8 true) rfl
            | ok tb =>
              dsimp only
              cases decodeInt i8Ty tb with
              | none => exact exprWF_of_ub (.int .i8 true) rfl
              | some tv =>
                dsimp only [evalDiscrBranchesMem]
                cases (decide (Neg.neg 1 ≤ tv) && decide (tv < 0)) with
                | true =>
                  rw [if_true_eq_true]; dsimp only [evalDiscriminantMem]
                  exact exprWF_of_ok (.int .i8 true) _ rfl ⟨[.init 255], rfl⟩
                | false =>
                  rw [if_false_eq_true]
                  cases (decide (0 ≤ tv) && decide (tv < 1)) with
                  | true =>
                    rw [if_true_eq_true]; dsimp only [evalDiscriminantMem]
                    exact exprWF_of_ok (.int .i8 true) _ rfl ⟨[.init 0], rfl⟩
                  | false =>
                    rw [if_false_eq_true]
                    cases (decide (1 ≤ tv) && decide (tv < 2)) with
                    | true =>
                      rw [if_true_eq_true]; dsimp only [evalDiscriminantMem]
                      exact exprWF_of_ok (.int .i8 true) _ rfl ⟨[.init 1], rfl⟩
                    | false =>
                      rw [if_false_eq_true]; dsimp only [evalDiscriminantMem]
                      exact exprWF_of_ub (.int .i8 true) rfl
          | enum ety =>
            dsimp only at hadm; rw [Bool.true_and] at hadm
            cases hea : enumAdmitted ety with
            | false => rw [hea] at hadm; cases hadm
            | true =>
              rw [hea, Bool.true_and] at hadm
              have hdstEq := mirTy_eq_of_beq hadm; subst hdstEq
              dsimp only [translateTy, translateEnumTy]
              cases hrepr : ety.tagRepr with
              | zeroSized =>
                dsimp only; rw [if_not_true]; dsimp only [evalDiscriminantMem]
                cases decodeInt_encodeInt
                    (translateIntTy ety.discrWidth ety.discrSigned)
                    (discrIntOfNat ety.discrWidth ety.discrSigned _)
                    (intWidth_bitWidth_pos ety.discrWidth)
                    (canRepresent_decodeScalar ety.discrWidth ety.discrSigned _) with
                | intro bs' hbs' =>
                  exact exprWF_of_ok (.int ety.discrWidth ety.discrSigned) _ rfl
                    ⟨bs', hbs'.1⟩
              | scalar tagW tagS =>
                dsimp only; rw [if_not_true]
                dsimp only [evalDiscriminantMem]
                rw [ptrOffsetInbounds_zero]; dsimp only
                cases mem.load ptr (translateIntTy tagW tagS).size ⟨1⟩ with
                | error _ =>
                  exact exprWF_of_ub (.int ety.discrWidth ety.discrSigned) rfl
                | ok tb =>
                  dsimp only
                  cases decodeInt (translateIntTy tagW tagS) tb with
                  | none =>
                    exact exprWF_of_ub (.int ety.discrWidth ety.discrSigned) rfl
                  | some tv =>
                    dsimp only
                    have hbrWF := evalDiscrBranchesMem_build_wf mem ptr tv ety
                      tagW tagS ety.discriminants
                    cases heb : evalDiscrBranchesMem mem ptr tv
                        (buildEnumBranches ety tagW tagS ety.discriminants) with
                    | error err =>
                      dsimp only
                      exact exprWF_of_err (.int ety.discrWidth ety.discrSigned)
                        rfl (fun r hr => hbrWF.1 r (by rw [heb, hr]))
                    | ok optRes =>
                      cases optRes with
                      | none =>
                        dsimp only
                        exact exprWF_of_ub (.int ety.discrWidth ety.discrSigned) rfl
                      | some subOpt =>
                        cases subOpt with
                        | none =>
                          dsimp only
                          exact exprWF_of_ub (.int ety.discrWidth ety.discrSigned) rfl
                        | some d =>
                          dsimp only
                          cases decodeInt_encodeInt
                              (translateIntTy ety.discrWidth ety.discrSigned) d
                              (intWidth_bitWidth_pos ety.discrWidth)
                              (hbrWF.2 d heb) with
                          | intro bs' hbs' =>
                            exact exprWF_of_ok
                              (.int ety.discrWidth ety.discrSigned) (.int d) rfl
                              ⟨bs', hbs'.1⟩
          | _ => cases hadm
  | useRetag _ | ref _ _ | addressOf _ _ | fakeAddressOf _
  | aggregateTuple _ | aggregateArray _ _ | repeat_ _ _ _
  | aggregateRange _ _ _ | aggregateRangeTo _ _ | aggregateRangeFrom _ _
  | aggregateOption _ _ _ | unsupported | aggregateStruct _ _ => cases hadm

private theorem storageDeadFrame_mrWF (frame : StackFrame) (mem : MrMemory)
    (id : LocalName) (hid : id < frame.func.locals.length)
    (hb : ∀ p, p ∈ frame.locals → p.1 < frame.func.locals.length) :
    (∀ r, storageDeadFrame frame mem id ≠ .error (.illFormed r)) ∧
    (∀ f' m', storageDeadFrame frame mem id = .ok (f', m') →
      f'.func = frame.func ∧ f'.nextBlock = frame.nextBlock ∧
      f'.nextStmt = frame.nextStmt ∧ f'.stackPopAction = frame.stackPopAction ∧
      (∀ p, p ∈ f'.locals → p.1 < f'.func.locals.length)) := by
  cases listGet?_some_of_lt frame.func.locals id hid with
  | intro ty hty =>
    dsimp only [storageDeadFrame]; rw [hty]; dsimp only
    cases (localMapRemove id frame.locals).1 with
    | none =>
      refine ⟨(fun _ h => by cases h), fun f' _ h => ?_⟩
      injection h with h1; injection h1 with hf _; subst hf
      exact ⟨rfl, rfl, rfl, rfl, localMapRemove_inBounds id _ frame.locals hb⟩
    | some ptr =>
      dsimp only
      cases mem.deallocate ptr ty.size ty.align with
      | error _ => exact ⟨(fun _ h => by cases h), (fun _ _ h => by cases h)⟩
      | ok _ =>
        refine ⟨(fun _ h => by cases h), fun f' _ h => ?_⟩
        injection h with h1; injection h1 with hf _; subst hf
        exact ⟨rfl, rfl, rfl, rfl, localMapRemove_inBounds id _ frame.locals hb⟩

private theorem storageLiveFrame_mrWF (frame : StackFrame) (mem : MrMemory)
    (id : LocalName) (hid : id < frame.func.locals.length)
    (hb : ∀ p, p ∈ frame.locals → p.1 < frame.func.locals.length) :
    (∀ r, storageLiveFrame frame mem id ≠ .error (.illFormed r)) ∧
    (∀ f' m', storageLiveFrame frame mem id = .ok (f', m') →
      f'.func = frame.func ∧ f'.nextBlock = frame.nextBlock ∧
      f'.nextStmt = frame.nextStmt ∧ f'.stackPopAction = frame.stackPopAction ∧
      (∀ p, p ∈ f'.locals → p.1 < f'.func.locals.length)) := by
  cases listGet?_some_of_lt frame.func.locals id hid with
  | intro ty hty =>
    have hsd := storageDeadFrame_mrWF frame mem id hid hb
    dsimp only [storageLiveFrame]; rw [hty]; dsimp only
    cases hs : storageDeadFrame frame mem id with
    | error _ =>
      exact ⟨(fun r h => hsd.1 r (by rw [hs]; exact h)), (fun _ _ h => by cases h)⟩
    | ok pr =>
      cases pr with
      | mk f1 m1 =>
        have hf1 := hsd.2 f1 m1 hs; dsimp only
        cases m1.allocate ty.size ty.align with
        | error _ => exact ⟨(fun _ h => by cases h), (fun _ _ h => by cases h)⟩
        | ok pr2 =>
          cases pr2 with
          | mk m2 ptr =>
            refine ⟨(fun _ h => by cases h), fun f' _ h => ?_⟩
            injection h with h1; injection h1 with hf _; subst hf
            refine ⟨hf1.1, hf1.2.1, hf1.2.2.1, hf1.2.2.2.1, ?_⟩
            exact localMapInsert_inBounds id ptr f1.func.locals.length
              f1.locals (by rw [hf1.1]; exact hid) hf1.2.2.2.2

private theorem deallocateAllLocals_mrWF (func : MrFunction) :
    ∀ (ls : LocalMap) (mem : MrMemory),
      (∀ p, p ∈ ls → p.1 < func.locals.length) →
      ∀ r, deallocateAllLocals func mem ls ≠ .error (.illFormed r) := by
  intro ls
  induction ls with
  | nil => intro _ _ _ h; cases h
  | cons hd rest ih =>
    intro mem hb r h
    cases hd with
    | mk id ptr =>
      cases listGet?_some_of_lt func.locals id (hb (id, ptr) (List.Mem.head _)) with
      | intro ty hty =>
        dsimp only [deallocateAllLocals] at h; rw [hty] at h; dsimp only at h
        cases hd' : mem.deallocate ptr ty.size ty.align with
        | error _ => rw [hd'] at h; cases h
        | ok mem' =>
          rw [hd'] at h
          exact ih mem' (fun q hq => hb q (List.Mem.tail _ hq)) r h

private theorem lookupSwitchCase_lt_int (numBlocks : Nat) (w : IntWidth)
    (s : Bool) (v : Int) (fallback : BbName) (hfb : fallback < numBlocks + 1) :
    ∀ (branches : List (BitVec 128 × BasicBlockId)),
      switchBranchesAdmitted numBlocks (.int w s) branches = true →
      lookupSwitchCase v fallback (translateIntSwitchBranches w s branches) <
        numBlocks + 1 := by
  intro branches
  induction branches with
  | nil => intro _; exact hfb
  | cons entry rest ih =>
    intro hadm
    cases entry with
    | mk bits target =>
      dsimp only [switchBranchesAdmitted] at hadm
      cases ht : Nat.blt target numBlocks with
      | false => rw [ht] at hadm; cases hadm
      | true =>
        cases htr : (truncateBits w bits == bits) with
        | false => rw [ht, htr] at hadm; cases hadm
        | true =>
          rw [ht, htr] at hadm
          dsimp only [translateIntSwitchBranches, lookupSwitchCase]
          cases (decodeScalar ⟨w, s, bits⟩ == v) with
          | true => exact Nat.succ_lt_succ (nat_lt_of_blt_eq_true ht)
          | false => exact ih hadm

private theorem bool_and_right {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a <;> cases b <;> cases h <;> rfl

private theorem lookupSwitchCase_lt_nat (numBlocks : Nat) (dTy : MirTy)
    (v : Int) (fallback : BbName) (hfb : fallback < numBlocks + 1) :
    ∀ (branches : List (BitVec 128 × BasicBlockId)),
      switchBranchesAdmitted numBlocks dTy branches = true →
      lookupSwitchCase v fallback (translateNatSwitchBranches branches) <
        numBlocks + 1 := by
  intro branches
  induction branches with
  | nil => intro _; exact hfb
  | cons entry rest ih =>
    intro hadm
    cases entry with
    | mk bits target =>
      dsimp only [switchBranchesAdmitted] at hadm
      have hadmRest : switchBranchesAdmitted numBlocks dTy rest = true :=
        bool_and_right hadm
      have ht : Nat.blt target numBlocks = true := by
        cases hb : Nat.blt target numBlocks with
        | true => rfl
        | false => rw [hb] at hadm; cases hadm
      dsimp only [translateNatSwitchBranches, lookupSwitchCase]
      cases (Int.ofNat bits.toNat == v) with
      | true => exact Nat.succ_lt_succ (nat_lt_of_blt_eq_true ht)
      | false => exact ih hadmRest

/-- Self-contained MiniRust runtime state invariant preserved across all steps
reachable from `initMrMachine p q` on `MiniRustAdmitted p q`. -/
def MrMachineWF (body : Body) (retMirTy : MirTy) (m : Machine) : Prop :=
  bodyAdmittedWith false body = true ∧
  Trusted.MirSemantics.getElem? body.locals 0 = some retMirTy ∧
  ((∃ (calleeFrame callerFrame : StackFrame) (callerRetPtr : ThinPtr),
      m.stack = [calleeFrame, callerFrame] ∧
      calleeFrame.func = translateBody body ∧
      calleeFrame.nextBlock < calleeFrame.func.blocks.length ∧
      (∀ bb, listGet? calleeFrame.func.blocks calleeFrame.nextBlock = some bb →
        calleeFrame.nextStmt ≤ bb.statements.length) ∧
      (∀ p, p ∈ calleeFrame.locals → p.1 < calleeFrame.func.locals.length) ∧
      (localMapGet? 0 calleeFrame.locals).isSome = true ∧
      calleeFrame.stackPopAction = .backToCaller callerRetPtr (some 0) ∧
      callerFrame.func = harnessCallerFunc (translateTy retMirTy) ∧
      callerFrame.locals = [(0, callerRetPtr)]) ∨
   (∃ (callerFrame : StackFrame) (callerRetPtr : ThinPtr),
      m.stack = [callerFrame] ∧
      callerFrame.func = harnessCallerFunc (translateTy retMirTy) ∧
      callerFrame.locals = [(0, callerRetPtr)] ∧
      callerFrame.nextBlock = 0 ∧
      callerFrame.nextStmt = 0))

private def StepWF (body : Body) (retMirTy : MirTy) (o : StepOutcome) : Prop :=
  (∀ r, o ≠ .illFormed r) ∧
  (∀ m', o = .step m' → MrMachineWF body retMirTy m')

private theorem stepWF_of_ub {body : Body} {retMirTy : MirTy} {msg : String}
    {o : StepOutcome} (h : o = .ub msg) : StepWF body retMirTy o := by
  rw [h]; exact ⟨(fun _ h1 => by cases h1), (fun _ h1 => by cases h1)⟩

private theorem stepWF_of_returned {body : Body} {retMirTy : MirTy} {v : MrValue}
    {o : StepOutcome} (h : o = .returned v) : StepWF body retMirTy o := by
  rw [h]; exact ⟨(fun _ h1 => by cases h1), (fun _ h1 => by cases h1)⟩

private theorem stepWF_of_step {body : Body} {retMirTy : MirTy} (m' : Machine)
    {o : StepOutcome} (h : o = .step m')
    (hwf : MrMachineWF body retMirTy m') : StepWF body retMirTy o := by
  rw [h]; refine ⟨(fun _ h1 => by cases h1), fun mNext h1 => ?_⟩
  injection h1 with heq; subst heq; exact hwf

private theorem mrMachineWF_step (body : Body) (retMirTy : MirTy) (m : Machine)
    (hwf : MrMachineWF body retMirTy m) :
    StepWF body retMirTy (mrStep m) := by
  cases hwf with
  | intro hbadm hrest =>
    cases hrest with
    | intro hretTy hcases =>
      cases bodyAdmittedWith_spec false body hbadm with
      | intro hbbNe hB1 => cases hB1 with | intro hargLt hB2 =>
        cases hB2 with | intro _ hB3 => cases hB3 with | intro _ hB4 =>
          cases hB4 with | intro _ hB5 => cases hB5 with | intro hsupp hblocksAdm =>
      have h0Lt : 0 < body.locals.length := Nat.lt_of_le_of_lt (Nat.zero_le _) hargLt
      have hbbPos : 0 < body.basicBlocks.length := by
        cases hb : body.basicBlocks with
        | nil => rw [hb] at hbbNe; cases hbbNe
        | cons _ _ => exact Nat.zero_lt_succ _
      cases hcases with
      | inr hcallerOnly =>
        cases hcallerOnly with
        | intro callerFrame h1 => cases h1 with | intro callerRetPtr h2 =>
          dsimp only [mrStep]; rw [h2.1]; dsimp only
          rw [h2.2.2.2.1, h2.2.2.2.2, h2.2.1]
          dsimp only [harnessCallerFunc, listGet?, List.length, Nat.beq,
            stepTerminator]
          rw [h2.2.1, h2.2.2.1]
          dsimp only [harnessCallerFunc, listGet?, localMapGet?, Nat.beq,
            typedLoad]
          rw [ite_bool_true rfl, ite_bool_true rfl]; dsimp only
          cases m.mem.load callerRetPtr (translateTy retMirTy).size
              (translateTy retMirTy).align with
          | error _ => exact stepWF_of_ub rfl
          | ok bs =>
            dsimp only
            cases mrDecode (translateTy retMirTy) bs with
            | none => exact stepWF_of_ub rfl
            | some v => exact stepWF_of_returned rfl
      | inl hcallee =>
        cases hcallee with
        | intro calleeFrame h1 => cases h1 with | intro callerFrame h2 =>
          cases h2 with | intro callerRetPtr h3 =>
            have hmStack := h3.1; have hfnEq := h3.2.1; have hblkLt := h3.2.2.1
            have hstmtLe := h3.2.2.2.1; have hlocB := h3.2.2.2.2.1
            have hret0Live := h3.2.2.2.2.2.1
            have hpop := h3.2.2.2.2.2.2.1; have hcallerFn := h3.2.2.2.2.2.2.2.1
            have hcallerLoc := h3.2.2.2.2.2.2.2.2
            have hfnLocLen : calleeFrame.func.locals.length = body.locals.length := by
              rw [hfnEq]; dsimp only [translateBody]; exact list_length_map _ _
            have hfnBlkLen : calleeFrame.func.blocks.length =
                body.basicBlocks.length + 1 := by
              rw [hfnEq]; dsimp only [translateBody, List.length]
              rw [list_length_map]
            cases listGet?_some_of_lt calleeFrame.func.blocks
                calleeFrame.nextBlock hblkLt with
            | intro mrBb hmrBb =>
              have hle := hstmtLe mrBb hmrBb
              dsimp only [mrStep]; rw [hmStack]; dsimp only; rw [hmrBb]; dsimp only
              have hadvanceWF : ∀ (f' : StackFrame) (m' : MrMemory),
                  calleeFrame.nextStmt < mrBb.statements.length →
                  f'.func = calleeFrame.func →
                  f'.nextBlock = calleeFrame.nextBlock →
                  f'.nextStmt = calleeFrame.nextStmt →
                  f'.stackPopAction = calleeFrame.stackPopAction →
                  (∀ p, p ∈ f'.locals → p.1 < f'.func.locals.length) →
                  (localMapGet? 0 f'.locals).isSome = true →
                  MrMachineWF body retMirTy {
                    prog := m.prog, mem := m',
                    stack := [{ f' with nextStmt := f'.nextStmt + 1 }, callerFrame] } := by
                intro f' m' hstLt hf1 hf2 hf3 hf4 hf5 hf0
                refine ⟨hbadm, hretTy, Or.inl ⟨{ f' with nextStmt := f'.nextStmt + 1 },
                  callerFrame, callerRetPtr, rfl, Eq.trans hf1 hfnEq,
                  by dsimp only; rw [hf2, hf1]; exact hblkLt,
                  ?_, hf5, hf0, Eq.trans hf4 hpop, hcallerFn, hcallerLoc⟩⟩
                intro bb2 hbb2; dsimp only at hbb2; dsimp only
                rw [hf2, hf1] at hbb2; rw [hmrBb] at hbb2
                injection hbb2 with he; subst he
                rw [hf3]; exact hstLt
              cases hst : listGet? mrBb.statements calleeFrame.nextStmt with
              | some mrStmt =>
                have hstLt : calleeFrame.nextStmt < mrBb.statements.length :=
                  listGet?_lt_length mrBb.statements calleeFrame.nextStmt mrStmt hst
                cases hnb : calleeFrame.nextBlock with
                | zero =>
                  have hmrBb0 := hmrBb
                  rw [hfnEq, hnb] at hmrBb0
                  dsimp only [translateBody, listGet?] at hmrBb0
                  injection hmrBb0 with hbbEq
                  have hst0 := hst; rw [← hbbEq] at hst0
                  have hmapSome : ∀ (xs : List LocalName) (i : Nat) (s : MrStatement),
                      listGet? (xs.map MrStatement.storageLive) i = some s →
                      ∃ k, k ∈ xs ∧ s = .storageLive k := by
                    intro xs; induction xs with
                    | nil => intro _ _ hg; cases hg
                    | cons a as iha =>
                      intro i s hg; cases i with
                      | zero => injection hg with hs; exact ⟨a, List.Mem.head _, hs.symm⟩
                      | succ i' =>
                        cases iha i' s hg with
                        | intro k hk => exact ⟨k, List.Mem.tail _ hk.1, hk.2⟩
                  cases hmapSome (alwaysLiveTemps body) calleeFrame.nextStmt
                      mrStmt hst0 with
                  | intro k hk =>
                    have hks := hk.2; subst hks
                    have hkLt : k < calleeFrame.func.locals.length := by
                      rw [hfnLocLen]
                      have hspec :=
                        ((alwaysLiveTempsAux_spec body 0 body.locals).1 k hk.1).2.1
                      rw [Nat.zero_add] at hspec; exact hspec
                    have hsl := storageLiveFrame_mrWF calleeFrame m.mem k hkLt hlocB
                    dsimp only [stepStatement]
                    cases hs : storageLiveFrame calleeFrame m.mem k with
                    | error err =>
                      cases err with
                      | ub _ => exact stepWF_of_ub rfl
                      | illFormed r0 => exact False.elim (hsl.1 r0 hs)
                    | ok pr =>
                      cases pr with
                      | mk f' m' =>
                        have hf' := hsl.2 f' m' hs
                        exact stepWF_of_step _ rfl
                          (hadvanceWF f' m' hstLt hf'.1 hf'.2.1 hf'.2.2.1
                            hf'.2.2.2.1 hf'.2.2.2.2
                            (storageLiveFrame_get0 calleeFrame f' m.mem m' k
                              (Or.inr hret0Live) hs))
                | succ bIdx =>
                  have hbLt : bIdx < body.basicBlocks.length := by
                    rw [hnb, hfnBlkLen] at hblkLt
                    exact Nat.lt_of_succ_lt_succ hblkLt
                  cases listGet?_some_of_lt body.basicBlocks bIdx hbLt with
                  | intro bb hbb =>
                    have hmrBbS := hmrBb
                    rw [hfnEq, hnb] at hmrBbS
                    dsimp only [translateBody, listGet?] at hmrBbS
                    rw [listGet?_map, hbb] at hmrBbS
                    injection hmrBbS with hbbEq
                    have hbbAdm := listGet?_all _ body.basicBlocks bIdx bb
                      hblocksAdm hbb
                    have hstmtsAdm : bb.statements.all
                        (stmtAdmitted false body.argumentCount body.locals) = true := by
                      dsimp only [blockAdmitted] at hbbAdm
                      cases hc : bb.cleanup with
                      | true => rw [hc] at hbbAdm; cases hbbAdm
                      | false =>
                        rw [hc] at hbbAdm
                        cases hs : bb.statements.all _ with
                        | false => rw [hs] at hbbAdm; cases hbbAdm
                        | true => rfl
                    have hstB : calleeFrame.nextStmt < bb.statements.length := by
                      have h1 := hstLt; rw [← hbbEq] at h1
                      dsimp only [translateBlock] at h1
                      rw [list_length_map] at h1; exact h1
                    cases listGet?_some_of_lt bb.statements calleeFrame.nextStmt hstB with
                    | intro mirStmt hmirStmt =>
                      have hmrStmtEq : mrStmt = translateStmt body.locals mirStmt := by
                        have h1 := hst; rw [← hbbEq] at h1
                        dsimp only [translateBlock] at h1
                        rw [listGet?_map, hmirStmt] at h1
                        injection h1 with he; exact he.symm
                      subst hmrStmtEq
                      have hsAdm := listGet?_all _ bb.statements calleeFrame.nextStmt
                        mirStmt hstmtsAdm hmirStmt
                      cases mirStmt with
                      | unsupported => cases hsAdm
                      | nop =>
                        dsimp only [translateStmt, stepStatement, evalPlace]
                        cases listGet?_some_of_lt calleeFrame.func.locals 0
                            (by rw [hfnLocLen]; exact h0Lt) with
                        | intro ty0 hty0 =>
                          rw [hty0]; dsimp only
                          cases localMapGet? 0 calleeFrame.locals with
                          | none => exact stepWF_of_ub rfl
                          | some _ =>
                            exact stepWF_of_step _ rfl
                              (hadvanceWF calleeFrame m.mem hstLt rfl rfl rfl rfl
                                hlocB hret0Live)
                      | storageLive id =>
                        dsimp only [stmtAdmitted] at hsAdm
                        have hidLt : id < calleeFrame.func.locals.length := by
                          rw [hfnLocLen]; exact nat_lt_of_blt_eq_true hsAdm
                        have hsl := storageLiveFrame_mrWF calleeFrame m.mem id
                          hidLt hlocB
                        dsimp only [translateStmt, stepStatement]
                        cases hs : storageLiveFrame calleeFrame m.mem id with
                        | error err =>
                          cases err with
                          | ub _ => exact stepWF_of_ub rfl
                          | illFormed r0 => exact False.elim (hsl.1 r0 hs)
                        | ok pr =>
                          cases pr with
                          | mk f' m' =>
                            have hf' := hsl.2 f' m' hs
                            exact stepWF_of_step _ rfl
                              (hadvanceWF f' m' hstLt hf'.1 hf'.2.1 hf'.2.2.1
                                hf'.2.2.2.1 hf'.2.2.2.2
                                (storageLiveFrame_get0 calleeFrame f' m.mem m' id
                                  (Or.inr hret0Live) hs))
                      | storageDead id =>
                        dsimp only [stmtAdmitted] at hsAdm
                        cases hargB : Nat.blt body.argumentCount id with
                        | false => rw [hargB] at hsAdm; cases hsAdm
                        | true =>
                          rw [hargB, Bool.true_and] at hsAdm
                          have hargLtId := nat_lt_of_blt_eq_true hargB
                          have h0LtId : 0 < id :=
                            Nat.lt_of_le_of_lt (Nat.zero_le _) hargLtId
                          have h0b : Nat.beq id 0 = false := by
                            cases hb : Nat.beq id 0 with
                            | false => rfl
                            | true =>
                              rw [Nat.eq_of_beq_eq_true hb] at h0LtId; cases h0LtId
                          have hfnRet : calleeFrame.func.ret = 0 := by
                            rw [hfnEq]; rfl
                          have hargsAny :
                              calleeFrame.func.args.any (Nat.beq id) = false := by
                            rw [hfnEq]; dsimp only [translateBody]
                            exact rangeNat_any_beq_false body.argumentCount 1 id
                              (by rw [Nat.add_comm]; exact hargLtId)
                          have hidLt : id < calleeFrame.func.locals.length := by
                            rw [hfnLocLen]; exact nat_lt_of_blt_eq_true hsAdm
                          have hsd := storageDeadFrame_mrWF calleeFrame m.mem id
                            hidLt hlocB
                          dsimp only [translateStmt, stepStatement]
                          rw [hfnRet, h0b, hargsAny, Bool.false_or, if_false_eq_true]
                          cases hs : storageDeadFrame calleeFrame m.mem id with
                          | error err =>
                            cases err with
                            | ub _ => exact stepWF_of_ub rfl
                            | illFormed r0 => exact False.elim (hsd.1 r0 hs)
                          | ok pr =>
                            cases pr with
                            | mk f' m' =>
                              have hf' := hsd.2 f' m' hs
                              exact stepWF_of_step _ rfl
                                (hadvanceWF f' m' hstLt hf'.1 hf'.2.1 hf'.2.2.1
                                  hf'.2.2.2.1 hf'.2.2.2.2
                                  (storageDeadFrame_get0_of_ne calleeFrame f'
                                    m.mem m' id h0b hret0Live hs))
                      | assign dst rv =>
                        dsimp only [stmtAdmitted] at hsAdm
                        cases hp : dst.projection.isEmpty with
                        | false => rw [hp] at hsAdm; cases hsAdm
                        | true =>
                          rw [hp, Bool.true_and] at hsAdm
                          cases hdstTy :
                              Trusted.MirSemantics.getElem? body.locals dst.localId with
                          | none => rw [hdstTy] at hsAdm; cases hsAdm
                          | some dstTy =>
                            rw [hdstTy] at hsAdm
                            have hfnLoc :
                                calleeFrame.func.locals = body.locals.map translateTy := by
                              rw [hfnEq]; rfl
                            have hmrDst :
                                listGet? calleeFrame.func.locals dst.localId =
                                  some (translateTy dstTy) := by
                              rw [hfnLoc, listGet?_map, ← getElem?_eq_listGet?,
                                hdstTy]; rfl
                            have hrvWF := evalRvalue_mrWF body.locals dstTy rv
                              calleeFrame m.mem hsupp hfnLoc hsAdm
                            dsimp only [translateStmt, stepStatement, evalPlace]
                            rw [hmrDst]; dsimp only
                            cases localMapGet? dst.localId calleeFrame.locals with
                            | none => exact stepWF_of_ub rfl
                            | some ptrDst =>
                              dsimp only
                              cases hev : evalValue calleeFrame m.mem
                                  (translateRvalue body.locals rv) with
                              | error err =>
                                cases err with
                                | ub _ => exact stepWF_of_ub rfl
                                | illFormed r0 => exact False.elim (hrvWF.1 r0 hev)
                              | ok pr =>
                                cases pr with
                                | mk val rty =>
                                  have hval := hrvWF.2 val rty hev
                                  rw [hval.1] at hval
                                  cases hval.2 with
                                  | intro bs hbs =>
                                    dsimp only; rw [if_not_true]
                                    dsimp only [typedStore]; rw [hbs]
                                    dsimp only [liftMemRes]
                                    cases m.mem.store ptrDst bs ⟨1⟩ with
                                    | error _ => exact stepWF_of_ub rfl
                                    | ok mem' =>
                                      exact stepWF_of_step _ rfl
                                        (hadvanceWF calleeFrame mem' hstLt
                                          rfl rfl rfl rfl hlocB hret0Live)
              | none =>
                have hstEq : calleeFrame.nextStmt = mrBb.statements.length := by
                  cases Nat.eq_or_lt_of_le hle with
                  | inl he => exact he
                  | inr hlt =>
                    cases listGet?_some_of_lt mrBb.statements
                        calleeFrame.nextStmt hlt with
                    | intro s hs => rw [hs] at hst; cases hst
                rw [hstEq, Nat.beq_refl, if_true_eq_true]
                have hjumpWF : ∀ (tgt : BbName),
                    tgt < calleeFrame.func.blocks.length →
                    MrMachineWF body retMirTy {
                      prog := m.prog, mem := m.mem,
                      stack := [{ calleeFrame with nextBlock := tgt, nextStmt := 0 },
                        callerFrame] } := by
                  intro tgt htgt
                  exact ⟨hbadm, hretTy,
                    Or.inl ⟨{ calleeFrame with nextBlock := tgt, nextStmt := 0 },
                      callerFrame, callerRetPtr, rfl, hfnEq, htgt,
                      fun _ _ => Nat.zero_le _, hlocB, hret0Live, hpop,
                      hcallerFn, hcallerLoc⟩⟩
                cases hnb : calleeFrame.nextBlock with
                | zero =>
                  rw [hfnEq, hnb] at hmrBb
                  dsimp only [translateBody, listGet?] at hmrBb
                  injection hmrBb with hbbEq; subst hbbEq
                  have h1Lt : 1 < calleeFrame.func.blocks.length := by
                    rw [hfnBlkLen]; exact Nat.succ_lt_succ hbbPos
                  have h1F : (!Nat.blt 1 calleeFrame.func.blocks.length) = false := by
                    rw [nat_blt_eq_true_of_lt h1Lt]; rfl
                  dsimp only [stepTerminator]; rw [h1F, if_false_eq_true]
                  exact stepWF_of_step _ rfl (hjumpWF 1 h1Lt)
                | succ bIdx =>
                  have hbLt : bIdx < body.basicBlocks.length := by
                    rw [hnb, hfnBlkLen] at hblkLt
                    exact Nat.lt_of_succ_lt_succ hblkLt
                  cases listGet?_some_of_lt body.basicBlocks bIdx hbLt with
                  | intro bb hbb =>
                    have hbbEq : mrBb = translateBlock body.locals bb := by
                      rw [hfnEq, hnb] at hmrBb
                      dsimp only [translateBody, listGet?] at hmrBb
                      rw [listGet?_map, hbb] at hmrBb
                      injection hmrBb with he; exact he.symm
                    subst hbbEq
                    have hbbAdm := listGet?_all _ body.basicBlocks bIdx bb
                      hblocksAdm hbb
                    have htermAdm : (match bb.terminator with
                        | .goto target => Nat.blt target body.basicBlocks.length
                        | .return_ => true
                        | .unreachable => true
                        | .switchInt discr targets =>
                          operandAdmitted false body.locals discr &&
                            Nat.blt targets.otherwise body.basicBlocks.length &&
                            match operandTy? body.locals discr with
                            | some dTy =>
                              (match dTy with
                              | .int _ _ | .bool => true
                              | .char => !false
                              | _ => false) &&
                                switchBranchesAdmitted body.basicBlocks.length dTy
                                  targets.branches &&
                                switchCasesUnique
                                  (translateSwitchCasesForTy dTy targets.branches)
                            | none => false
                        | _ => false) = true := by
                      dsimp only [blockAdmitted] at hbbAdm
                      cases hc : bb.cleanup with
                      | true => rw [hc] at hbbAdm; cases hbbAdm
                      | false =>
                        rw [hc] at hbbAdm
                        cases hs : bb.statements.all _ with
                        | false => rw [hs] at hbbAdm; cases hbbAdm
                        | true => rw [hs] at hbbAdm; exact hbbAdm
                    dsimp only [translateBlock]
                    cases hterm : bb.terminator with
                    | unwindResume | assert _ _ _ _ _ | call _ _ _ _ _ | coreCall _ _ _ _ _
                    | sysrootCall _ _ _ _ _ | unsupported | callNe _ _ _
                    | drop _ _ _ =>
                      rw [hterm] at htermAdm; cases htermAdm
                    | unreachable => exact stepWF_of_ub rfl
                    | goto target =>
                      rw [hterm] at htermAdm
                      have htLt : target + 1 < calleeFrame.func.blocks.length := by
                        rw [hfnBlkLen]
                        exact Nat.succ_lt_succ (nat_lt_of_blt_eq_true htermAdm)
                      have htF :
                          (!Nat.blt (target + 1) calleeFrame.func.blocks.length) =
                            false := by
                        rw [nat_blt_eq_true_of_lt htLt]; rfl
                      dsimp only [translateTerm, stepTerminator]
                      rw [htF, if_false_eq_true]
                      exact stepWF_of_step _ rfl (hjumpWF (target + 1) htLt)
                    | return_ =>
                      have hfnLoc :
                          calleeFrame.func.locals = body.locals.map translateTy := by
                        rw [hfnEq]; rfl
                      have hretFun0 : calleeFrame.func.ret = 0 := by rw [hfnEq]; rfl
                      have hmrLoc0 : listGet? calleeFrame.func.locals 0 =
                          some (translateTy retMirTy) := by
                        rw [hfnLoc, listGet?_map, ← getElem?_eq_listGet?, hretTy]; rfl
                      have hretSupp : isSupportedScalarOrUnitTy retMirTy = true := by
                        have h0List : listGet? body.locals 0 = some retMirTy := by
                          rw [← getElem?_eq_listGet?]; exact hretTy
                        exact listGet?_all isSupportedScalarOrUnitTy body.locals 0
                          retMirTy hsupp h0List
                      dsimp only [translateTerm, stepTerminator]
                      rw [hretFun0, hmrLoc0]
                      cases hget0 : localMapGet? 0 calleeFrame.locals with
                      | none => rw [hget0] at hret0Live; cases hret0Live
                      | some retPtr =>
                        dsimp only [typedLoad]
                        cases m.mem.load retPtr (translateTy retMirTy).size
                            (translateTy retMirTy).align with
                        | error _ => exact stepWF_of_ub rfl
                        | ok rbs =>
                          dsimp only
                          cases hdec0 : mrDecode (translateTy retMirTy) rbs with
                          | none => exact stepWF_of_ub rfl
                          | some retVal =>
                            dsimp only
                            have hda := deallocateAllLocals_mrWF calleeFrame.func
                              calleeFrame.locals m.mem hlocB
                            cases hd : deallocateAllLocals calleeFrame.func m.mem
                                calleeFrame.locals with
                            | error err =>
                              cases err with
                              | ub _ => exact stepWF_of_ub rfl
                              | illFormed r0 => exact False.elim (hda r0 hd)
                            | ok mem1 =>
                              dsimp only; rw [hpop]; dsimp only [typedStore]
                              cases mrDecode_encodable retMirTy rbs retVal
                                  hretSupp hdec0 with
                              | intro cbs hcbs =>
                                rw [hcbs]; dsimp only [liftMemRes]
                                cases mem1.store callerRetPtr cbs
                                    (translateTy retMirTy).align with
                                | error _ => exact stepWF_of_ub rfl
                                | ok mem2 =>
                                  have hcallerBlk :
                                      (!Nat.blt 0 callerFrame.func.blocks.length) =
                                        false := by
                                    rw [hcallerFn]; rfl
                                  dsimp only; rw [hcallerBlk, if_false_eq_true]
                                  exact stepWF_of_step _ rfl ⟨hbadm, hretTy,
                                    Or.inr ⟨{ callerFrame with nextBlock := 0, nextStmt := 0 },
                                      callerRetPtr, rfl, hcallerFn, hcallerLoc,
                                      rfl, rfl⟩⟩
                    | switchInt discr targets =>
                      rw [hterm] at htermAdm; dsimp only at htermAdm
                      cases hoa : operandAdmitted false body.locals discr with
                      | false => rw [hoa] at htermAdm; cases htermAdm
                      | true =>
                        cases hoth :
                            Nat.blt targets.otherwise body.basicBlocks.length with
                        | false => rw [hoa, hoth] at htermAdm; cases htermAdm
                        | true =>
                          rw [hoa, hoth, Bool.true_and, Bool.true_and] at htermAdm
                          cases hdt : operandTy? body.locals discr with
                          | none => rw [hdt] at htermAdm; cases htermAdm
                          | some dTy =>
                            rw [hdt] at htermAdm; dsimp only at htermAdm
                            have hfnLoc :
                                calleeFrame.func.locals = body.locals.map translateTy := by
                              rw [hfnEq]; rfl
                            have hop := evalOperand_mrWF body.locals discr dTy
                              calleeFrame m.mem hsupp hfnLoc hoa hdt
                            have hothLt :
                                targets.otherwise + 1 < body.basicBlocks.length + 1 :=
                              Nat.succ_lt_succ (nat_lt_of_blt_eq_true hoth)
                            dsimp only [translateTerm]; rw [hdt]
                            cases dTy with
                            | int w s =>
                              rw [Bool.true_and] at htermAdm
                              cases hsba : switchBranchesAdmitted
                                  body.basicBlocks.length (.int w s) targets.branches with
                              | false => rw [hsba] at htermAdm; cases htermAdm
                              | true =>
                                dsimp only [stepTerminator]
                                cases hev : evalValue calleeFrame m.mem
                                    (translateOperand discr) with
                                | error err =>
                                  cases err with
                                  | ub _ => exact stepWF_of_ub rfl
                                  | illFormed r0 => exact False.elim (hop.1 r0 hev)
                                | ok pr =>
                                  cases pr with
                                  | mk dv drty =>
                                    have hwf := hop.2 dv drty hev
                                    cases hwf.2 with
                                    | intro _ hbs =>
                                      rw [hwf.1] at hbs
                                      cases mrEncode_int_elim hbs with
                                      | intro iv hiv =>
                                        have hdv := hiv.1; subst hdv
                                        have htgtLt : lookupSwitchCase iv
                                            (targets.otherwise + 1)
                                            (translateIntSwitchBranches w s
                                              targets.branches) <
                                            calleeFrame.func.blocks.length := by
                                          rw [hfnBlkLen]
                                          exact lookupSwitchCase_lt_int
                                            body.basicBlocks.length w s iv
                                            (targets.otherwise + 1) hothLt
                                            targets.branches hsba
                                        have htgtF : (!Nat.blt (lookupSwitchCase iv
                                            (targets.otherwise + 1)
                                            (translateIntSwitchBranches w s
                                              targets.branches))
                                            calleeFrame.func.blocks.length) = false := by
                                          rw [nat_blt_eq_true_of_lt htgtLt]; rfl
                                        dsimp only; rw [htgtF, if_false_eq_true]
                                        exact stepWF_of_step _ rfl (hjumpWF _ htgtLt)
                            | bool =>
                              rw [Bool.true_and] at htermAdm
                              cases hsba : switchBranchesAdmitted
                                  body.basicBlocks.length .bool targets.branches with
                              | false => rw [hsba] at htermAdm; cases htermAdm
                              | true =>
                                dsimp only [stepTerminator, evalValue]
                                cases hev : evalValue calleeFrame m.mem
                                    (translateOperand discr) with
                                | error err =>
                                  cases err with
                                  | ub _ => exact stepWF_of_ub rfl
                                  | illFormed r0 => exact False.elim (hop.1 r0 hev)
                                | ok pr =>
                                  cases pr with
                                  | mk dv drty =>
                                    have hwf := hop.2 dv drty hev
                                    cases hwf.2 with
                                    | intro _ hbs =>
                                      rw [hwf.1] at hbs
                                      cases mrEncode_bool_elim hbs with
                                      | intro b hb =>
                                        have hdr := hwf.1; subst hb; subst hdr
                                        dsimp only [Anneal.MiniRust.evalUnOp,
                                          evalCastOp, translateTy]
                                        rw [evalTransmute_bool_to_u8 b]; dsimp only
                                        have htgtLt : lookupSwitchCase
                                            (if b then 1 else 0)
                                            (targets.otherwise + 1)
                                            (translateNatSwitchBranches
                                              targets.branches) <
                                            calleeFrame.func.blocks.length := by
                                          rw [hfnBlkLen]
                                          exact lookupSwitchCase_lt_nat
                                            body.basicBlocks.length .bool
                                            (if b then 1 else 0)
                                            (targets.otherwise + 1) hothLt
                                            targets.branches hsba
                                        have htgtF : (!Nat.blt (lookupSwitchCase
                                            (if b then 1 else 0)
                                            (targets.otherwise + 1)
                                            (translateNatSwitchBranches
                                              targets.branches))
                                            calleeFrame.func.blocks.length) = false := by
                                          rw [nat_blt_eq_true_of_lt htgtLt]; rfl
                                        rw [htgtF, if_false_eq_true]
                                        exact stepWF_of_step _ rfl (hjumpWF _ htgtLt)
                            | char =>
                              rw [Bool.not_false, Bool.true_and] at htermAdm
                              cases hsba : switchBranchesAdmitted
                                  body.basicBlocks.length .char targets.branches with
                              | false => rw [hsba] at htermAdm; cases htermAdm
                              | true =>
                                dsimp only [stepTerminator]
                                cases hev : evalValue calleeFrame m.mem
                                    (translateOperand discr) with
                                | error err =>
                                  cases err with
                                  | ub _ => exact stepWF_of_ub rfl
                                  | illFormed r0 => exact False.elim (hop.1 r0 hev)
                                | ok pr =>
                                  cases pr with
                                  | mk dv drty =>
                                    have hwf := hop.2 dv drty hev
                                    cases hwf.2 with
                                    | intro _ hbs =>
                                      rw [hwf.1] at hbs
                                      cases mrEncode_int_elim hbs with
                                      | intro iv hiv =>
                                        have hdv := hiv.1; subst hdv
                                        have htgtLt : lookupSwitchCase iv
                                            (targets.otherwise + 1)
                                            (translateNatSwitchBranches
                                              targets.branches) <
                                            calleeFrame.func.blocks.length := by
                                          rw [hfnBlkLen]
                                          exact lookupSwitchCase_lt_nat
                                            body.basicBlocks.length .char iv
                                            (targets.otherwise + 1) hothLt
                                            targets.branches hsba
                                        have htgtF : (!Nat.blt (lookupSwitchCase iv
                                            (targets.otherwise + 1)
                                            (translateNatSwitchBranches
                                              targets.branches))
                                            calleeFrame.func.blocks.length) = false := by
                                          rw [nat_blt_eq_true_of_lt htgtLt]; rfl
                                        dsimp only; rw [htgtF, if_false_eq_true]
                                        exact stepWF_of_step _ rfl (hjumpWF _ htgtLt)
                            | _ => cases htermAdm

private theorem initMrArgsLoop_inBounds :
    ∀ (vs : List Val) (idx : Nat) (frame frame' : StackFrame)
      (mem mem' : MrMemory),
      (∀ p, p ∈ frame.locals → p.1 < frame.func.locals.length) →
      (localMapGet? 0 frame.locals).isSome = true →
      initMrArgsLoop frame mem idx vs = .ok (frame', mem') →
      frame'.func = frame.func ∧ frame'.nextBlock = frame.nextBlock ∧
      frame'.nextStmt = frame.nextStmt ∧
      frame'.stackPopAction = frame.stackPopAction ∧
      (∀ p, p ∈ frame'.locals → p.1 < frame'.func.locals.length) ∧
      (localMapGet? 0 frame'.locals).isSome = true := by
  intro vs
  induction vs with
  | nil =>
    intro _ frame frame' _ _ hb h0 h
    dsimp only [initMrArgsLoop] at h
    injection h with h1; injection h1 with hf _; subst hf
    exact ⟨rfl, rfl, rfl, rfl, hb, h0⟩
  | cons v rest ih =>
    intro idx frame frame' mem mem' hb h0 h
    dsimp only [initMrArgsLoop] at h
    cases hsl : storageLiveFrame frame mem idx with
    | error _ => rw [hsl] at h; cases h
    | ok pr1 =>
      rw [hsl] at h; dsimp only at h
      cases pr1 with
      | mk f1 m1 =>
        have hidLt : idx < frame.func.locals.length := by
          dsimp only [storageLiveFrame] at hsl
          cases hlg : listGet? frame.func.locals idx with
          | none => rw [hlg] at hsl; cases hsl
          | some ty => exact listGet?_lt_length _ idx ty hlg
        have hf1 := (storageLiveFrame_mrWF frame mem idx hidLt hb).2 f1 m1 hsl
        have h0' := storageLiveFrame_get0 frame f1 mem m1 idx (Or.inr h0) hsl
        cases hg1 : listGet? f1.func.locals idx with
        | none => rw [hg1] at h; cases h
        | some ty =>
          rw [hg1] at h
          cases hg2 : localMapGet? idx f1.locals with
          | none => rw [hg2] at h; cases h
          | some ptr =>
            rw [hg2] at h; dsimp only at h
            cases hst : typedStore m1 ptr (translateVal v) ty ty.align with
            | error _ => rw [hst] at h; cases h
            | ok m2 =>
              rw [hst] at h
              have hf' := ih (idx + 1) f1 frame' m2 mem' hf1.2.2.2.2 h0' h
              exact ⟨Eq.trans hf'.1 hf1.1, Eq.trans hf'.2.1 hf1.2.1,
                Eq.trans hf'.2.2.1 hf1.2.2.1, Eq.trans hf'.2.2.2.1 hf1.2.2.2.1,
                hf'.2.2.2.2⟩

/-- Runtime well-formedness theorem: for every `(p, q)` satisfying
`MiniRustAdmitted p q`, no reachable step from `initMrMachine p q = .ok m₀`
ever produces `StepOutcome.illFormed` (`¬ MrIllFormed m₀`). -/
theorem minirust_admitted_never_illFormed (p : Program) (q : Query)
    (hadm : MiniRustAdmitted p q) :
    ∀ m₀, initMrMachine p q = .ok m₀ → ¬ MrIllFormed m₀ := by
  intro m₀ hinitM hill
  dsimp only [MiniRustAdmitted, MiniRustProgAdmitted] at hadm
  cases hadm with
  | intro hprog _ =>
    dsimp only [initMrMachine] at hinitM
    cases hc1 : (!Nat.beq p.pointerWidthBits 64 || !Nat.beq p.mirProfileVersion 1) with
    | true => rw [hc1, if_true_eq_true] at hinitM; cases hinitM
    | false =>
      rw [hc1, if_false_eq_true] at hinitM
      cases hc2 : !q.callerMem.allocations.isEmpty with
      | true => rw [hc2, if_true_eq_true] at hinitM; cases hinitM
      | false =>
        rw [hc2, if_false_eq_true] at hinitM
        cases hbody : Trusted.MirSemantics.getElem? p.bodies p.entryDefId with
        | none => rw [hbody] at hinitM; cases hinitM
        | some body =>
          rw [hbody] at hinitM hprog
          have hbadm : bodyAdmittedWith false body = true := by
            cases hw : Nat.beq p.pointerWidthBits 64 with
            | false => rw [hw] at hprog; cases hprog
            | true =>
              cases hv : Nat.beq p.mirProfileVersion 1 with
              | false => rw [hw, hv] at hprog; cases hprog
              | true => rw [hw, hv] at hprog; exact hprog
          dsimp only at hinitM
          cases hretTy : Trusted.MirSemantics.getElem? body.locals 0 with
          | none => rw [hretTy] at hinitM; cases hinitM
          | some retMirTy =>
            rw [hretTy] at hinitM; dsimp only at hinitM
            cases halloc : MrMemory.empty.allocate (translateTy retMirTy).size
                (translateTy retMirTy).align with
            | error _ => rw [halloc] at hinitM; cases hinitM
            | ok prC =>
              rw [halloc] at hinitM; dsimp only at hinitM
              cases prC with
              | mk mem1 callerRetPtr =>
                cases hsl0 : storageLiveFrame _ mem1 0 with
                | error _ => rw [hsl0] at hinitM; cases hinitM
                | ok pr0 =>
                  rw [hsl0] at hinitM; dsimp only at hinitM
                  cases pr0 with
                  | mk calleeFrame1 mem2 =>
                    cases hargs : initMrArgsLoop calleeFrame1 mem2 1 q.args with
                    | error _ => rw [hargs] at hinitM; cases hinitM
                    | ok prA =>
                      rw [hargs] at hinitM; dsimp only at hinitM
                      cases prA with
                      | mk calleeFrame2 mem3 =>
                        injection hinitM with hm0
                        have h0Lt : 0 < (translateBody body).locals.length := by
                          dsimp only [translateBody]; rw [list_length_map]
                          rw [getElem?_eq_listGet?] at hretTy
                          exact listGet?_lt_length _ 0 retMirTy hretTy
                        have hf1 := (storageLiveFrame_mrWF _ mem1 0 h0Lt
                          (fun _ hp => by cases hp)).2 calleeFrame1 mem2 hsl0
                        have h0Live1 := storageLiveFrame_get0 _ calleeFrame1
                          mem1 mem2 0 (Or.inl rfl) hsl0
                        have hf2 := initMrArgsLoop_inBounds q.args 1 calleeFrame1
                          calleeFrame2 mem2 mem3 hf1.2.2.2.2 h0Live1 hargs
                        have hwf0 : MrMachineWF body retMirTy m₀ := by
                          rw [← hm0]
                          refine ⟨hbadm, hretTy, Or.inl ⟨calleeFrame2, _,
                            callerRetPtr, rfl, Eq.trans hf2.1 hf1.1, ?_, ?_,
                            hf2.2.2.2.2.1, hf2.2.2.2.2.2,
                            Eq.trans hf2.2.2.2.1 hf1.2.2.2.1,
                            rfl, rfl⟩⟩
                          · rw [hf2.2.1, hf1.2.1, hf2.1, hf1.1]; exact Nat.zero_lt_succ _
                          · intro _ _; rw [hf2.2.2.1, hf1.2.2.1]; exact Nat.zero_le _
                        have hreachWF : ∀ m1 m2, MrReaches m1 m2 →
                            MrMachineWF body retMirTy m1 →
                            MrMachineWF body retMirTy m2 := by
                          intro m1 m2 hr
                          induction hr with
                          | refl => exact fun h => h
                          | tail _ hst ih =>
                            exact fun hw1 =>
                              (mrMachineWF_step body retMirTy _ (ih hw1)).2 _ hst
                        cases hill with
                        | intro mEnd hmEnd => cases hmEnd with | intro r0 hr0 =>
                          exact (mrMachineWF_step body retMirTy mEnd
                            (hreachWF m₀ mEnd hr0.1 hwf0)).1 r0 hr0.2

/-! ## Oracle Identifier and Top-Level Correspondence Claims -/

/-- Oracle identifier for the pinned MiniRust operational specification. -/
def minirustOracleId : String := "minirust_v1"

/-- Forward simulation claim over `MiniRustAdmitted`:
every admitted `(p, q)` translates to a structurally well-formed `MrProgram`,
never faults `.unsupported` in Anneal, initializes cleanly in MiniRust, never
reaches `StepOutcome.illFormed` in MiniRust, simulates normal returns forward,
reflects MiniRust UB back to Anneal `.fault .undefined` (so
`WellFormed p q → ¬ MrFaultsUB m₀`), and simulates divergence forward. -/
def MiniRustForwardSimClaim : Prop :=
  ∀ (p : Program) (q : Query),
    MiniRustAdmitted p q →
    mrProgWellFormed (translateProg p) p.entryDefId = true ∧
    ¬ ReachesResult p q (.fault .unsupported) ∧
    ∃ m₀ : Machine,
      initMrMachine p q = .ok m₀ ∧
      ¬ MrIllFormed m₀ ∧
      (∀ m r, MrReaches m₀ m → mrStep m ≠ .illFormed r) ∧
      (∀ v, Behavior p q (.returned ⟨v, ⟨[]⟩⟩) →
        MrBehavior m₀ (translateVal v)) ∧
      (MrFaultsUB m₀ → ReachesResult p q (.fault .undefined)) ∧
      (WellFormed p q → ¬ MrFaultsUB m₀) ∧
      (Diverges p q → MrDiverges m₀)

/-- Exact bidirectional fault-equivalence claim over `MiniRustExactAdmitted`:
every exact-admitted `(p, q)` translates to a structurally well-formed
`MrProgram`, never faults `.unsupported` in Anneal, initializes cleanly in
MiniRust without ever reaching `StepOutcome.illFormed`, and agrees
bidirectionally on normal returns, Undefined Behavior, and divergence. -/
def MiniRustBiFaultEquivClaim : Prop :=
  ∀ (p : Program) (q : Query),
    MiniRustExactAdmitted p q →
    mrProgWellFormed (translateProg p) p.entryDefId = true ∧
    ¬ ReachesResult p q (.fault .unsupported) ∧
    ∃ m₀ : Machine,
      initMrMachine p q = .ok m₀ ∧
      ¬ MrIllFormed m₀ ∧
      (∀ m r, MrReaches m₀ m → mrStep m ≠ .illFormed r) ∧
      (∀ v, Behavior p q (.returned ⟨v, ⟨[]⟩⟩) →
        MrBehavior m₀ (translateVal v)) ∧
      (∀ v', MrBehavior m₀ v' →
        ∃ v, v' = translateVal v ∧ Behavior p q (.returned ⟨v, ⟨[]⟩⟩)) ∧
      (ReachesResult p q (.fault .undefined) ↔ MrFaultsUB m₀) ∧
      (Diverges p q ↔ MrDiverges m₀)

/-- Base proof of `MiniRustForwardSimClaim` (`minirust_v1`). -/
theorem minirust_forward_sim_base : MiniRustForwardSimClaim := by
  intro p q hadm
  cases init_fullStateRel false p q hadm with
  | intro _ h1 => cases h1 with | intro m₀ h2 => cases h2 with
    | intro _ h3 =>
      have hnoIF := minirust_admitted_never_illFormed p q hadm m₀ h3.2.1
      exact ⟨minirust_admitted_prog_wellFormed hadm,
        forward_no_unsupported p q hadm, m₀, h3.2.1, hnoIF,
        fun m r hr hs => hnoIF ⟨m, r, hr, hs⟩,
        forward_behavior p q hadm m₀ h3.2.1,
        forward_ub_contrapositive p q hadm m₀ h3.2.1,
        forward_wellFormed_no_ub p q hadm m₀ h3.2.1,
        forward_diverges p q hadm m₀ h3.2.1⟩

/-- Base proof of `MiniRustBiFaultEquivClaim` (`minirust_v1`). -/
theorem minirust_bi_fault_equiv_base : MiniRustBiFaultEquivClaim := by
  intro p q hadm
  have hadmF := miniRustAdmitted_of_exact hadm
  cases init_fullStateRel true p q hadm with
  | intro _ h1 => cases h1 with | intro m₀ h2 => cases h2 with
    | intro _ h3 =>
      have hbeh := exact_behavior_iff p q hadm m₀ h3.2.1
      have hnoIF := minirust_admitted_never_illFormed p q hadmF m₀ h3.2.1
      exact ⟨minirust_admitted_prog_wellFormed hadmF,
        forward_no_unsupported p q hadmF, m₀, h3.2.1, hnoIF,
        fun m r hr hs => hnoIF ⟨m, r, hr, hs⟩,
        hbeh.1,
        hbeh.2,
        exact_ub_iff p q hadm m₀ h3.2.1,
        exact_diverges_iff p q hadm m₀ h3.2.1⟩

/-! ## Constructive Fuel Runner for Anneal Witness Execution -/

/-- Fuel-bounded deterministic runner for `Trusted.MirSemantics.evalStep`. -/
noncomputable def annealRunFuel (p : Program) :
    Nat → State → StepResult State TerminalOut
  | 0, s => .step s
  | n + 1, s =>
    match evalStep p 0 s with
    | .step s' => annealRunFuel p n s'
    | other => other

theorem annealRunFuel_reaches (p : Program) :
    ∀ (n : Nat) (s : State) (r : StepResult State TerminalOut),
      (∀ s', r ≠ .step s') →
      annealRunFuel p n s = r →
      ∃ sf, Reaches p s sf ∧ Step p sf r := by
  intro n
  induction n with
  | zero =>
    intro s r hns hrun
    dsimp only [annealRunFuel] at hrun
    exact False.elim (hns s hrun.symm)
  | succ k ih =>
    intro s r hns hrun
    dsimp only [annealRunFuel] at hrun
    cases hev : evalStep p 0 s with
    | step s' =>
      rw [hev] at hrun
      cases ih s' r hns hrun with
      | intro sf hsf =>
        exact ⟨sf, reaches_head ⟨0, rfl, hev⟩ hsf.1, hsf.2⟩
    | done _ =>
      rw [hev] at hrun; subst hrun
      exact ⟨s, Reaches.refl s, ⟨0, rfl, hev⟩⟩
    | fault _ =>
      rw [hev] at hrun; subst hrun
      exact ⟨s, Reaches.refl s, ⟨0, rfl, hev⟩⟩

theorem annealRunFuel_returned {p : Program} {q : Query} {s₀ : State} {n : Nat}
    {out : Out}
    (hinit : initState p q = .ok s₀)
    (hrun : annealRunFuel p n s₀ = .done (.returned out)) :
    Behavior p q (.returned out) := by
  dsimp only [Behavior, ReachesResult]
  rw [hinit]
  exact annealRunFuel_reaches p n s₀ (.done (.returned out))
    (fun _ h => by cases h) hrun

theorem annealRunFuel_fault {p : Program} {q : Query} {s₀ : State} {n : Nat}
    {fk : FaultKind}
    (hinit : initState p q = .ok s₀)
    (hrun : annealRunFuel p n s₀ = .fault fk) :
    ReachesResult p q (.fault fk) := by
  dsimp only [ReachesResult]
  rw [hinit]
  exact annealRunFuel_reaches p n s₀ (.fault fk) (fun _ h => by cases h) hrun

/-! ## Compact Witness Program Builders -/

/-- Build a 64-bit Profile v1 single-body `Program`. -/
noncomputable def mkWitnessProg (body : Body) : Program := {
  bodies := [body]
  entryDefId := 0
  pointerWidthBits := 64
  mirProfileVersion := 1
  scope := .unit
}

/-- Empty-caller-memory query carrying `args`. -/
noncomputable def mkWitnessQuery (args : List Val) : Query := {
  args := args
  callerMem := ⟨[]⟩
}

/-- Helper for scalar `Val`. -/
noncomputable def mkScalarVal (w : IntWidth) (s : Bool) (n : Nat) : Val :=
  .scalar ⟨w, s, BitVec.ofNat 128 n⟩

/-- Helper for scalar constant `Operand`. -/
noncomputable def mkScalarConst (w : IntWidth) (s : Bool) (n : Nat) : Operand :=
  .constant { ty := .int w s, lit := .scalar (BitVec.ofNat 128 n) }

/-- Helper for `Place` with empty projection. -/
noncomputable def mkLocalPlace (id : LocalId) : Place :=
  { localId := id, projection := [] }

/-- Helper for `Operand.copy` of a local. -/
noncomputable def mkCopy (id : LocalId) : Operand :=
  .copy (mkLocalPlace id)

/-- Helper for `Operand.move` of a local. -/
noncomputable def mkMove (id : LocalId) : Operand :=
  .move (mkLocalPlace id)

/-- Helper for assigning an `Rvalue` to a local. -/
noncomputable def mkAssign (dst : LocalId) (rv : Rvalue) : StatementKind :=
  .assign (mkLocalPlace dst) rv

/-- Generic helper proving Anneal `Behavior`, direct `mrRunFuel` execution, and
MiniRust `MrBehavior` for an exact-admitted witness. -/
theorem witness_exact_returned (p : Program) (q : Query) (v : Val)
    (fuelA fuelM : Nat)
    (hadm : MiniRustExactAdmitted p q)
    (s₀ : State) (m₀ : Machine)
    (hinitA : initState p q = .ok s₀)
    (_hinitM : initMrMachine p q = .ok m₀)
    (hrunA : annealRunFuel p fuelA s₀ = .done (.returned ⟨v, ⟨[]⟩⟩))
    (hrunM : mrRunFuel fuelM m₀ = .returned (translateVal v)) :
    MiniRustExactAdmitted p q ∧
    Behavior p q (.returned ⟨v, ⟨[]⟩⟩) ∧
    mrRunFuel fuelM m₀ = .returned (translateVal v) ∧
    MrBehavior m₀ (translateVal v) :=
  ⟨hadm, annealRunFuel_returned hinitA hrunA, hrunM, mrRunFuel_returned hrunM⟩

/-- Generic helper proving Anneal `.fault .undefined`, direct `mrRunFuel` UB
execution, and MiniRust `MrFaultsUB` for an exact-admitted negative witness. -/
theorem witness_exact_ub (p : Program) (q : Query) (fuelA fuelM : Nat)
    (reason : String)
    (hadm : MiniRustExactAdmitted p q)
    (s₀ : State) (m₀ : Machine)
    (hinitA : initState p q = .ok s₀)
    (_hinitM : initMrMachine p q = .ok m₀)
    (hrunA : annealRunFuel p fuelA s₀ = .fault .undefined)
    (hrunM : mrRunFuel fuelM m₀ = .ub reason) :
    MiniRustExactAdmitted p q ∧
    ReachesResult p q (.fault .undefined) ∧
    mrRunFuel fuelM m₀ = .ub reason ∧
    MrFaultsUB m₀ :=
  ⟨hadm, annealRunFuel_fault hinitA hrunA, hrunM, mrRunFuel_ub hrunM⟩

/-! ## Positive Returning Witnesses (`MiniRustExactAdmitted`) -/

/-- Witness 1: Integer arithmetic (`add`, `sub`, `mul`, `div`, `rem`) on `u32`.
Computes `((10 + 3) * 2) - (10 / 3) - (10 % 3) = 26 - 3 - 1 = 22`. -/
noncomputable def progArith : Program :=
  let u32T : MirTy := .int .i32 false
  mkWitnessProg {
    argumentCount := 2
    locals := [u32T, u32T, u32T, u32T, u32T, u32T, u32T, u32T]
    basicBlocks := [{
      statements := [
        mkAssign 3 (.binaryOp .add (mkCopy 1) (mkCopy 2)),
        mkAssign 4 (.binaryOp .mul (mkCopy 3) (mkScalarConst .i32 false 2)),
        mkAssign 5 (.binaryOp .div (mkCopy 1) (mkCopy 2)),
        mkAssign 6 (.binaryOp .rem (mkCopy 1) (mkCopy 2)),
        mkAssign 7 (.binaryOp .sub (mkCopy 4) (mkCopy 5)),
        mkAssign 0 (.binaryOp .sub (mkCopy 7) (mkCopy 6))
      ]
      terminator := .return_
    }]
  }

noncomputable def queryArith : Query :=
  mkWitnessQuery [mkScalarVal .i32 false 10, mkScalarVal .i32 false 3]

theorem witness_arith_exact :
    ∃ m₀, initMrMachine progArith queryArith = .ok m₀ ∧
      MiniRustExactAdmitted progArith queryArith ∧
      Behavior progArith queryArith (.returned ⟨mkScalarVal .i32 false 22, ⟨[]⟩⟩) ∧
      mrRunFuel 24 m₀ = .returned (translateVal (mkScalarVal .i32 false 22)) ∧
      MrBehavior m₀ (translateVal (mkScalarVal .i32 false 22)) := by
  cases hinitM : initMrMachine progArith queryArith with
  | error _ => cases hinitM
  | ok m₀ =>
    cases hinitA : initState progArith queryArith with
    | error _ => cases hinitA
    | ok s₀ =>
      exact ⟨m₀, rfl, witness_exact_returned progArith queryArith
        (mkScalarVal .i32 false 22) 12 24 ⟨rfl, rfl, rfl⟩ s₀ m₀ hinitA hinitM
        (by cases hinitA; rfl) (by cases hinitM; rfl)⟩

/-- Witness 2: Bitwise (`bitAnd`, `bitOr`, `bitXor`) and shifts (`shl`, `shr`)
on `u8`: `((((0xF0 & 0x3C) ^ 0x05) | 0x02) << 1) >> 2 = 0x1B = 27`. -/
noncomputable def progBitwiseShift : Program :=
  let u8T : MirTy := .int .i8 false
  mkWitnessProg {
    argumentCount := 2
    locals := [u8T, u8T, u8T, u8T, u8T, u8T, u8T]
    basicBlocks := [{
      statements := [
        mkAssign 3 (.binaryOp .bitAnd (mkCopy 1) (mkCopy 2)),
        mkAssign 4 (.binaryOp .bitXor (mkCopy 3) (mkScalarConst .i8 false 5)),
        mkAssign 5 (.binaryOp .bitOr (mkCopy 4) (mkScalarConst .i8 false 2)),
        mkAssign 6 (.binaryOp .shl (mkCopy 5) (mkScalarConst .i8 false 1)),
        mkAssign 0 (.binaryOp .shr (mkCopy 6) (mkScalarConst .i8 false 2))
      ]
      terminator := .return_
    }]
  }

noncomputable def queryBitwiseShift : Query :=
  mkWitnessQuery [mkScalarVal .i8 false 240, mkScalarVal .i8 false 60]

theorem witness_bitwise_shift_exact :
    ∃ m₀, initMrMachine progBitwiseShift queryBitwiseShift = .ok m₀ ∧
      MiniRustExactAdmitted progBitwiseShift queryBitwiseShift ∧
      Behavior progBitwiseShift queryBitwiseShift
        (.returned ⟨mkScalarVal .i8 false 27, ⟨[]⟩⟩) ∧
      mrRunFuel 24 m₀ = .returned (translateVal (mkScalarVal .i8 false 27)) ∧
      MrBehavior m₀ (translateVal (mkScalarVal .i8 false 27)) := by
  cases hinitM : initMrMachine progBitwiseShift queryBitwiseShift with
  | error _ => cases hinitM
  | ok m₀ =>
    cases hinitA : initState progBitwiseShift queryBitwiseShift with
    | error _ => cases hinitA
    | ok s₀ =>
      exact ⟨m₀, rfl, witness_exact_returned progBitwiseShift queryBitwiseShift
        (mkScalarVal .i8 false 27) 10 24 ⟨rfl, rfl, rfl⟩ s₀ m₀ hinitA hinitM
        (by cases hinitA; rfl) (by cases hinitM; rfl)⟩

/-- Witness 3: `BinOp.cmp` producing `core::cmp::Ordering`, followed by
`Rvalue.discriminant` yielding `i8` (`-1` = `0xFF` for `Ordering::Less`). -/
noncomputable def progCmpDiscr : Program :=
  let i8T : MirTy := .int .i8 true
  mkWitnessProg {
    argumentCount := 2
    locals := [i8T, i8T, i8T, .ordering]
    basicBlocks := [{
      statements := [
        mkAssign 3 (.binaryOp .cmp (mkCopy 1) (mkCopy 2)),
        mkAssign 0 (.discriminant (mkLocalPlace 3))
      ]
      terminator := .return_
    }]
  }

noncomputable def queryCmpDiscr : Query :=
  mkWitnessQuery [mkScalarVal .i8 true 3, mkScalarVal .i8 true 7]

theorem witness_cmp_discr_exact :
    ∃ m₀, initMrMachine progCmpDiscr queryCmpDiscr = .ok m₀ ∧
      MiniRustExactAdmitted progCmpDiscr queryCmpDiscr ∧
      Behavior progCmpDiscr queryCmpDiscr
        (.returned ⟨mkScalarVal .i8 true 255, ⟨[]⟩⟩) ∧
      mrRunFuel 16 m₀ = .returned (translateVal (mkScalarVal .i8 true 255)) ∧
      MrBehavior m₀ (translateVal (mkScalarVal .i8 true 255)) := by
  cases hinitM : initMrMachine progCmpDiscr queryCmpDiscr with
  | error _ => cases hinitM
  | ok m₀ =>
    cases hinitA : initState progCmpDiscr queryCmpDiscr with
    | error _ => cases hinitA
    | ok s₀ =>
      exact ⟨m₀, rfl, witness_exact_returned progCmpDiscr queryCmpDiscr
        (mkScalarVal .i8 true 255) 6 16 ⟨rfl, rfl, rfl⟩ s₀ m₀ hinitA hinitM
        (by cases hinitA; rfl) (by cases hinitM; rfl)⟩

/-- Witness 4: `*WithOverflow` binary operation returning tuple `(u8, bool)`.
`addWithOverflow(250u8, 10u8) = (4u8, true)`. -/
noncomputable def progOverflowPair : Program :=
  let u8T : MirTy := .int .i8 false
  mkWitnessProg {
    argumentCount := 2
    locals := [.tuple [u8T, .bool], u8T, u8T]
    basicBlocks := [{
      statements := [
        mkAssign 0 (.binaryOp .addWithOverflow (mkCopy 1) (mkCopy 2))
      ]
      terminator := .return_
    }]
  }

noncomputable def queryOverflowPair : Query :=
  mkWitnessQuery [mkScalarVal .i8 false 250, mkScalarVal .i8 false 10]

noncomputable def expectedOverflowVal : Val :=
  .tuple [mkScalarVal .i8 false 4, .bool true]

theorem witness_overflow_pair_exact :
    ∃ m₀, initMrMachine progOverflowPair queryOverflowPair = .ok m₀ ∧
      MiniRustExactAdmitted progOverflowPair queryOverflowPair ∧
      Behavior progOverflowPair queryOverflowPair
        (.returned ⟨expectedOverflowVal, ⟨[]⟩⟩) ∧
      mrRunFuel 16 m₀ = .returned (translateVal expectedOverflowVal) ∧
      MrBehavior m₀ (translateVal expectedOverflowVal) := by
  cases hinitM : initMrMachine progOverflowPair queryOverflowPair with
  | error _ => cases hinitM
  | ok m₀ =>
    cases hinitA : initState progOverflowPair queryOverflowPair with
    | error _ => cases hinitA
    | ok s₀ =>
      have hadm : MiniRustExactAdmitted progOverflowPair queryOverflowPair :=
        ⟨rfl, rfl, rfl⟩
      have hrunA : annealRunFuel progOverflowPair 6 s₀ =
          .done (.returned ⟨expectedOverflowVal, ⟨[]⟩⟩) := by
        cases hinitA; rfl
      have hrunM : mrRunFuel 16 m₀ =
          .returned (translateVal expectedOverflowVal) := by
        cases hinitM; rfl
      exact ⟨m₀, rfl, witness_exact_returned progOverflowPair queryOverflowPair
        expectedOverflowVal 6 16 hadm s₀ m₀ hinitA hinitM hrunA hrunM⟩

/-- Witness 5: `SwitchInt` exercising both a matched branch and `otherwise`. -/
noncomputable def progSwitchInt : Program :=
  let u8T : MirTy := .int .i8 false
  mkWitnessProg {
    argumentCount := 1
    locals := [u8T, u8T]
    basicBlocks := [
      { statements := []
        terminator := .switchInt (mkCopy 1) {
          branches := [(BitVec.ofNat 128 1, 1), (BitVec.ofNat 128 2, 2)]
          otherwise := 3
        } },
      { statements := [mkAssign 0 (.use (mkScalarConst .i8 false 10))]
        terminator := .return_ },
      { statements := [mkAssign 0 (.use (mkScalarConst .i8 false 20))]
        terminator := .return_ },
      { statements := [mkAssign 0 (.use (mkScalarConst .i8 false 99))]
        terminator := .return_ }
    ]
  }

theorem witness_switchInt_matched_exact :
    let q := mkWitnessQuery [mkScalarVal .i8 false 2]
    ∃ m₀, initMrMachine progSwitchInt q = .ok m₀ ∧
      MiniRustExactAdmitted progSwitchInt q ∧
      Behavior progSwitchInt q (.returned ⟨mkScalarVal .i8 false 20, ⟨[]⟩⟩) ∧
      mrRunFuel 16 m₀ = .returned (translateVal (mkScalarVal .i8 false 20)) ∧
      MrBehavior m₀ (translateVal (mkScalarVal .i8 false 20)) := by
  dsimp only
  cases hinitM : initMrMachine progSwitchInt
      (mkWitnessQuery [mkScalarVal .i8 false 2]) with
  | error _ => cases hinitM
  | ok m₀ =>
    cases hinitA : initState progSwitchInt
        (mkWitnessQuery [mkScalarVal .i8 false 2]) with
    | error _ => cases hinitA
    | ok s₀ =>
      have hadm : MiniRustExactAdmitted progSwitchInt
          (mkWitnessQuery [mkScalarVal .i8 false 2]) := ⟨rfl, rfl, rfl⟩
      have hrunA : annealRunFuel progSwitchInt 6 s₀ =
          .done (.returned ⟨mkScalarVal .i8 false 20, ⟨[]⟩⟩) := by
        cases hinitA; rfl
      have hrunM : mrRunFuel 16 m₀ =
          .returned (translateVal (mkScalarVal .i8 false 20)) := by
        cases hinitM; rfl
      exact ⟨m₀, rfl, witness_exact_returned progSwitchInt
        (mkWitnessQuery [mkScalarVal .i8 false 2])
        (mkScalarVal .i8 false 20) 6 16 hadm s₀ m₀ hinitA hinitM hrunA hrunM⟩

theorem witness_switchInt_otherwise_exact :
    let q := mkWitnessQuery [mkScalarVal .i8 false 7]
    ∃ m₀, initMrMachine progSwitchInt q = .ok m₀ ∧
      MiniRustExactAdmitted progSwitchInt q ∧
      Behavior progSwitchInt q (.returned ⟨mkScalarVal .i8 false 99, ⟨[]⟩⟩) ∧
      mrRunFuel 16 m₀ = .returned (translateVal (mkScalarVal .i8 false 99)) ∧
      MrBehavior m₀ (translateVal (mkScalarVal .i8 false 99)) := by
  dsimp only
  cases hinitM : initMrMachine progSwitchInt
      (mkWitnessQuery [mkScalarVal .i8 false 7]) with
  | error _ => cases hinitM
  | ok m₀ =>
    cases hinitA : initState progSwitchInt
        (mkWitnessQuery [mkScalarVal .i8 false 7]) with
    | error _ => cases hinitA
    | ok s₀ =>
      have hadm : MiniRustExactAdmitted progSwitchInt
          (mkWitnessQuery [mkScalarVal .i8 false 7]) := ⟨rfl, rfl, rfl⟩
      have hrunA : annealRunFuel progSwitchInt 6 s₀ =
          .done (.returned ⟨mkScalarVal .i8 false 99, ⟨[]⟩⟩) := by
        cases hinitA; rfl
      have hrunM : mrRunFuel 16 m₀ =
          .returned (translateVal (mkScalarVal .i8 false 99)) := by
        cases hinitM; rfl
      exact ⟨m₀, rfl, witness_exact_returned progSwitchInt
        (mkWitnessQuery [mkScalarVal .i8 false 7])
        (mkScalarVal .i8 false 99) 6 16 hadm s₀ m₀ hinitA hinitM hrunA hrunM⟩

/-- Witness 6: `StorageLive` / `StorageDead` lifecycle on a temporary local. -/
noncomputable def progStorageLifecycle : Program :=
  let u32T : MirTy := .int .i32 false
  mkWitnessProg {
    argumentCount := 0
    locals := [u32T, u32T]
    basicBlocks := [{
      statements := [
        .storageLive 1,
        mkAssign 1 (.use (mkScalarConst .i32 false 41)),
        mkAssign 0 (.binaryOp .add (mkCopy 1) (mkScalarConst .i32 false 1)),
        .storageDead 1
      ]
      terminator := .return_
    }]
  }

theorem witness_storage_lifecycle_exact :
    let q := mkWitnessQuery []
    ∃ m₀, initMrMachine progStorageLifecycle q = .ok m₀ ∧
      MiniRustExactAdmitted progStorageLifecycle q ∧
      Behavior progStorageLifecycle q
        (.returned ⟨mkScalarVal .i32 false 42, ⟨[]⟩⟩) ∧
      mrRunFuel 16 m₀ = .returned (translateVal (mkScalarVal .i32 false 42)) ∧
      MrBehavior m₀ (translateVal (mkScalarVal .i32 false 42)) := by
  dsimp only
  cases hinitM : initMrMachine progStorageLifecycle (mkWitnessQuery []) with
  | error _ => cases hinitM
  | ok m₀ =>
    cases hinitA : initState progStorageLifecycle (mkWitnessQuery []) with
    | error _ => cases hinitA
    | ok s₀ =>
      have hadm : MiniRustExactAdmitted progStorageLifecycle (mkWitnessQuery []) :=
        ⟨rfl, rfl, rfl⟩
      have hrunA : annealRunFuel progStorageLifecycle 8 s₀ =
          .done (.returned ⟨mkScalarVal .i32 false 42, ⟨[]⟩⟩) := by
        cases hinitA; rfl
      have hrunM : mrRunFuel 16 m₀ =
          .returned (translateVal (mkScalarVal .i32 false 42)) := by
        cases hinitM; rfl
      exact ⟨m₀, rfl, witness_exact_returned progStorageLifecycle
        (mkWitnessQuery []) (mkScalarVal .i32 false 42) 8 16 hadm s₀ m₀ hinitA
        hinitM hrunA hrunM⟩

/-- Witness 7a: `CastKind.intToInt` sign-extending `i8` (`-1` = `0xFF`) to
`i32` (`0xFFFFFFFF`). -/
noncomputable def progCastI8ToI32 : Program :=
  mkWitnessProg {
    argumentCount := 1
    locals := [.int .i32 true, .int .i8 true]
    basicBlocks := [{
      statements := [mkAssign 0 (.cast .intToInt (mkCopy 1) (.int .i32 true))]
      terminator := .return_
    }]
  }

theorem witness_cast_i8_to_i32_exact :
    let q := mkWitnessQuery [mkScalarVal .i8 true 255]
    ∃ m₀, initMrMachine progCastI8ToI32 q = .ok m₀ ∧
      MiniRustExactAdmitted progCastI8ToI32 q ∧
      Behavior progCastI8ToI32 q
        (.returned ⟨mkScalarVal .i32 true 4294967295, ⟨[]⟩⟩) ∧
      mrRunFuel 16 m₀ =
        .returned (translateVal (mkScalarVal .i32 true 4294967295)) ∧
      MrBehavior m₀ (translateVal (mkScalarVal .i32 true 4294967295)) := by
  dsimp only
  cases hinitM : initMrMachine progCastI8ToI32
      (mkWitnessQuery [mkScalarVal .i8 true 255]) with
  | error _ => cases hinitM
  | ok m₀ =>
    cases hinitA : initState progCastI8ToI32
        (mkWitnessQuery [mkScalarVal .i8 true 255]) with
    | error _ => cases hinitA
    | ok s₀ =>
      have hadm : MiniRustExactAdmitted progCastI8ToI32
          (mkWitnessQuery [mkScalarVal .i8 true 255]) := ⟨rfl, rfl, rfl⟩
      have hrunA : annealRunFuel progCastI8ToI32 6 s₀ =
          .done (.returned ⟨mkScalarVal .i32 true 4294967295, ⟨[]⟩⟩) := by
        cases hinitA; rfl
      have hrunM : mrRunFuel 16 m₀ =
          .returned (translateVal (mkScalarVal .i32 true 4294967295)) := by
        cases hinitM; rfl
      exact ⟨m₀, rfl, witness_exact_returned progCastI8ToI32
        (mkWitnessQuery [mkScalarVal .i8 true 255])
        (mkScalarVal .i32 true 4294967295) 6 16 hadm s₀ m₀ hinitA hinitM hrunA
        hrunM⟩

/-- Witness 7b: `CastKind.intToInt` truncating `u32` (`0x12A` = `298`) to `u8`
(`0x2A` = `42`). -/
noncomputable def progCastU32ToU8 : Program :=
  mkWitnessProg {
    argumentCount := 1
    locals := [.int .i8 false, .int .i32 false]
    basicBlocks := [{
      statements := [mkAssign 0 (.cast .intToInt (mkCopy 1) (.int .i8 false))]
      terminator := .return_
    }]
  }

theorem witness_cast_u32_to_u8_exact :
    let q := mkWitnessQuery [mkScalarVal .i32 false 298]
    ∃ m₀, initMrMachine progCastU32ToU8 q = .ok m₀ ∧
      MiniRustExactAdmitted progCastU32ToU8 q ∧
      Behavior progCastU32ToU8 q (.returned ⟨mkScalarVal .i8 false 42, ⟨[]⟩⟩) ∧
      mrRunFuel 16 m₀ = .returned (translateVal (mkScalarVal .i8 false 42)) ∧
      MrBehavior m₀ (translateVal (mkScalarVal .i8 false 42)) := by
  dsimp only
  cases hinitM : initMrMachine progCastU32ToU8
      (mkWitnessQuery [mkScalarVal .i32 false 298]) with
  | error _ => cases hinitM
  | ok m₀ =>
    cases hinitA : initState progCastU32ToU8
        (mkWitnessQuery [mkScalarVal .i32 false 298]) with
    | error _ => cases hinitA
    | ok s₀ =>
      have hadm : MiniRustExactAdmitted progCastU32ToU8
          (mkWitnessQuery [mkScalarVal .i32 false 298]) := ⟨rfl, rfl, rfl⟩
      have hrunA : annealRunFuel progCastU32ToU8 6 s₀ =
          .done (.returned ⟨mkScalarVal .i8 false 42, ⟨[]⟩⟩) := by
        cases hinitA; rfl
      have hrunM : mrRunFuel 16 m₀ =
          .returned (translateVal (mkScalarVal .i8 false 42)) := by
        cases hinitM; rfl
      exact ⟨m₀, rfl, witness_exact_returned progCastU32ToU8
        (mkWitnessQuery [mkScalarVal .i32 false 298])
        (mkScalarVal .i8 false 42) 6 16 hadm s₀ m₀ hinitA hinitM hrunA hrunM⟩

/-- Witness 7c: `CastKind.intToInt` sign-extending `i32` (`-2` = `0xFFFFFFFE`)
to `u64` (`0xFFFFFFFFFFFFFFFE`). -/
noncomputable def progCastI32ToU64 : Program :=
  mkWitnessProg {
    argumentCount := 1
    locals := [.int .i64 false, .int .i32 true]
    basicBlocks := [{
      statements := [mkAssign 0 (.cast .intToInt (mkCopy 1) (.int .i64 false))]
      terminator := .return_
    }]
  }

theorem witness_cast_i32_to_u64_exact :
    let q := mkWitnessQuery [mkScalarVal .i32 true 4294967294]
    let outV := mkScalarVal .i64 false 18446744073709551614
    ∃ m₀, initMrMachine progCastI32ToU64 q = .ok m₀ ∧
      MiniRustExactAdmitted progCastI32ToU64 q ∧
      Behavior progCastI32ToU64 q (.returned ⟨outV, ⟨[]⟩⟩) ∧
      mrRunFuel 16 m₀ = .returned (translateVal outV) ∧
      MrBehavior m₀ (translateVal outV) := by
  dsimp only
  cases hinitM : initMrMachine progCastI32ToU64
      (mkWitnessQuery [mkScalarVal .i32 true 4294967294]) with
  | error _ => cases hinitM
  | ok m₀ =>
    cases hinitA : initState progCastI32ToU64
        (mkWitnessQuery [mkScalarVal .i32 true 4294967294]) with
    | error _ => cases hinitA
    | ok s₀ =>
      have hadm : MiniRustExactAdmitted progCastI32ToU64
          (mkWitnessQuery [mkScalarVal .i32 true 4294967294]) := ⟨rfl, rfl, rfl⟩
      have hrunA : annealRunFuel progCastI32ToU64 6 s₀ =
          .done (.returned ⟨mkScalarVal .i64 false 18446744073709551614, ⟨[]⟩⟩) := by
        cases hinitA; rfl
      have hrunM : mrRunFuel 16 m₀ =
          .returned (translateVal (mkScalarVal .i64 false 18446744073709551614)) := by
        cases hinitM; rfl
      exact ⟨m₀, rfl, witness_exact_returned progCastI32ToU64
        (mkWitnessQuery [mkScalarVal .i32 true 4294967294])
        (mkScalarVal .i64 false 18446744073709551614) 6 16 hadm s₀ m₀ hinitA
        hinitM hrunA hrunM⟩

/-- Witness 7d: `CastKind.intToInt` converting `bool` (`true`) to `u32`. -/
noncomputable def progCastBoolToU32 : Program :=
  mkWitnessProg {
    argumentCount := 1
    locals := [.int .i32 false, .bool]
    basicBlocks := [{
      statements := [mkAssign 0 (.cast .intToInt (mkCopy 1) (.int .i32 false))]
      terminator := .return_
    }]
  }

theorem witness_cast_bool_to_u32_exact :
    let q := mkWitnessQuery [.bool true]
    ∃ m₀, initMrMachine progCastBoolToU32 q = .ok m₀ ∧
      MiniRustExactAdmitted progCastBoolToU32 q ∧
      Behavior progCastBoolToU32 q (.returned ⟨mkScalarVal .i32 false 1, ⟨[]⟩⟩) ∧
      mrRunFuel 16 m₀ = .returned (translateVal (mkScalarVal .i32 false 1)) ∧
      MrBehavior m₀ (translateVal (mkScalarVal .i32 false 1)) := by
  dsimp only
  cases hinitM : initMrMachine progCastBoolToU32
      (mkWitnessQuery [.bool true]) with
  | error _ => cases hinitM
  | ok m₀ =>
    cases hinitA : initState progCastBoolToU32
        (mkWitnessQuery [.bool true]) with
    | error _ => cases hinitA
    | ok s₀ =>
      have hadm : MiniRustExactAdmitted progCastBoolToU32
          (mkWitnessQuery [.bool true]) := ⟨rfl, rfl, rfl⟩
      have hrunA : annealRunFuel progCastBoolToU32 6 s₀ =
          .done (.returned ⟨mkScalarVal .i32 false 1, ⟨[]⟩⟩) := by
        cases hinitA; rfl
      have hrunM : mrRunFuel 16 m₀ =
          .returned (translateVal (mkScalarVal .i32 false 1)) := by
        cases hinitM; rfl
      exact ⟨m₀, rfl, witness_exact_returned progCastBoolToU32
        (mkWitnessQuery [.bool true]) (mkScalarVal .i32 false 1) 6 16 hadm s₀ m₀
        hinitA hinitM hrunA hrunM⟩

/-- Witness 8a: Scalar-tagged fieldless enum
(`#[repr(u8)] enum E { A = 0, B = 2 }`), assigning variant `B` and reading
`Rvalue.discriminant` (`2u8`). -/
noncomputable def sampleScalarEnumTy : EnumTy := {
  id := 101
  discrWidth := .i8
  discrSigned := false
  tagRepr := .scalar .i8 false
  discriminants := [0, 2]
}

noncomputable def progEnumScalarDiscr : Program :=
  mkWitnessProg {
    argumentCount := 0
    locals := [.int .i8 false, .enum sampleScalarEnumTy]
    basicBlocks := [{
      statements := [
        mkAssign 1 (.use (.constant
          { ty := .enum sampleScalarEnumTy, lit := .scalar (BitVec.ofNat 128 2) })),
        mkAssign 0 (.discriminant (mkLocalPlace 1))
      ]
      terminator := .return_
    }]
  }

theorem witness_enum_scalar_discr_exact :
    let q := mkWitnessQuery []
    ∃ m₀, initMrMachine progEnumScalarDiscr q = .ok m₀ ∧
      MiniRustExactAdmitted progEnumScalarDiscr q ∧
      Behavior progEnumScalarDiscr q
        (.returned ⟨mkScalarVal .i8 false 2, ⟨[]⟩⟩) ∧
      mrRunFuel 16 m₀ = .returned (translateVal (mkScalarVal .i8 false 2)) ∧
      MrBehavior m₀ (translateVal (mkScalarVal .i8 false 2)) := by
  dsimp only
  cases hinitM : initMrMachine progEnumScalarDiscr (mkWitnessQuery []) with
  | error _ => cases hinitM
  | ok m₀ =>
    cases hinitA : initState progEnumScalarDiscr (mkWitnessQuery []) with
    | error _ => cases hinitA
    | ok s₀ =>
      have hadm : MiniRustExactAdmitted progEnumScalarDiscr (mkWitnessQuery []) :=
        ⟨rfl, rfl, rfl⟩
      have hrunA : annealRunFuel progEnumScalarDiscr 8 s₀ =
          .done (.returned ⟨mkScalarVal .i8 false 2, ⟨[]⟩⟩) := by
        cases hinitA; rfl
      have hrunM : mrRunFuel 16 m₀ =
          .returned (translateVal (mkScalarVal .i8 false 2)) := by
        cases hinitM; rfl
      exact ⟨m₀, rfl, witness_exact_returned progEnumScalarDiscr
        (mkWitnessQuery []) (mkScalarVal .i8 false 2) 8 16 hadm s₀ m₀ hinitA
        hinitM hrunA hrunM⟩

/-- Witness 8b: 1-variant ZST fieldless enum
(`#[repr(u8)] enum Single { Only = 7 }`), assigning `ConstLit.zeroSized` and
reading `Rvalue.discriminant` (`7u8`). -/
noncomputable def sampleZstEnumTy : EnumTy := {
  id := 102
  discrWidth := .i8
  discrSigned := false
  tagRepr := .zeroSized
  discriminants := [7]
}

noncomputable def progEnumZstDiscr : Program :=
  mkWitnessProg {
    argumentCount := 0
    locals := [.int .i8 false, .enum sampleZstEnumTy]
    basicBlocks := [{
      statements := [
        mkAssign 1 (.use (.constant
          { ty := .enum sampleZstEnumTy, lit := .zeroSized })),
        mkAssign 0 (.discriminant (mkLocalPlace 1))
      ]
      terminator := .return_
    }]
  }

theorem witness_enum_zst_discr_exact :
    let q := mkWitnessQuery []
    ∃ m₀, initMrMachine progEnumZstDiscr q = .ok m₀ ∧
      MiniRustExactAdmitted progEnumZstDiscr q ∧
      Behavior progEnumZstDiscr q (.returned ⟨mkScalarVal .i8 false 7, ⟨[]⟩⟩) ∧
      mrRunFuel 16 m₀ = .returned (translateVal (mkScalarVal .i8 false 7)) ∧
      MrBehavior m₀ (translateVal (mkScalarVal .i8 false 7)) := by
  dsimp only
  cases hinitM : initMrMachine progEnumZstDiscr (mkWitnessQuery []) with
  | error _ => cases hinitM
  | ok m₀ =>
    cases hinitA : initState progEnumZstDiscr (mkWitnessQuery []) with
    | error _ => cases hinitA
    | ok s₀ =>
      have hadm : MiniRustExactAdmitted progEnumZstDiscr (mkWitnessQuery []) :=
        ⟨rfl, rfl, rfl⟩
      have hrunA : annealRunFuel progEnumZstDiscr 8 s₀ =
          .done (.returned ⟨mkScalarVal .i8 false 7, ⟨[]⟩⟩) := by
        cases hinitA; rfl
      have hrunM : mrRunFuel 16 m₀ =
          .returned (translateVal (mkScalarVal .i8 false 7)) := by
        cases hinitM; rfl
      exact ⟨m₀, rfl, witness_exact_returned progEnumZstDiscr
        (mkWitnessQuery []) (mkScalarVal .i8 false 7) 8 16 hadm s₀ m₀ hinitA
        hinitM hrunA hrunM⟩

/-! ## Strict Inclusion (`MiniRustAdmitted` vs. `MiniRustExactAdmitted`) -/

/-- Witness 9a: `CastKind.intToInt` converting `u8` (`65`) to `char` (`'A'`).
Admitted in `MiniRustAdmitted` (where `char` lowers to MiniRust `u32Ty`) and
excluded from `MiniRustExactAdmitted`. -/
noncomputable def progCastU8ToChar : Program :=
  mkWitnessProg {
    argumentCount := 1
    locals := [.char, .int .i8 false]
    basicBlocks := [{
      statements := [mkAssign 0 (.cast .intToInt (mkCopy 1) .char)]
      terminator := .return_
    }]
  }

theorem witness_cast_u8_to_char_admitted :
    let q := mkWitnessQuery [mkScalarVal .i8 false 65]
    ∃ m₀, initMrMachine progCastU8ToChar q = .ok m₀ ∧
      MiniRustAdmitted progCastU8ToChar q ∧
      ¬ MiniRustExactAdmitted progCastU8ToChar q ∧
      Behavior progCastU8ToChar q (.returned ⟨.char 'A', ⟨[]⟩⟩) ∧
      mrRunFuel 16 m₀ = .returned (translateVal (.char 'A')) ∧
      MrBehavior m₀ (translateVal (.char 'A')) := by
  dsimp only
  cases hinitM : initMrMachine progCastU8ToChar
      (mkWitnessQuery [mkScalarVal .i8 false 65]) with
  | error _ => cases hinitM
  | ok m₀ =>
    cases hinitA : initState progCastU8ToChar
        (mkWitnessQuery [mkScalarVal .i8 false 65]) with
    | error _ => cases hinitA
    | ok s₀ =>
      have hadm : MiniRustAdmitted progCastU8ToChar
          (mkWitnessQuery [mkScalarVal .i8 false 65]) := ⟨rfl, rfl, rfl⟩
      have hnotExact : ¬ MiniRustExactAdmitted progCastU8ToChar
          (mkWitnessQuery [mkScalarVal .i8 false 65]) := by
        intro hex
        dsimp only [MiniRustExactAdmitted] at hex
        have hfalse : MiniRustExactProgAdmitted progCastU8ToChar = false := rfl
        rw [hfalse] at hex; cases hex.1
      have hrunA : annealRunFuel progCastU8ToChar 6 s₀ =
          .done (.returned ⟨.char 'A', ⟨[]⟩⟩) := by
        cases hinitA; rfl
      have hrunM : mrRunFuel 16 m₀ = .returned (translateVal (.char 'A')) := by
        cases hinitM; rfl
      exact ⟨m₀, rfl, hadm, hnotExact, annealRunFuel_returned hinitA hrunA,
        hrunM, mrRunFuel_returned hrunM⟩

/-- Witness 9b: Semantic strictness on `char`'s Unicode scalar niche
(`_0 = const char(0xD800); return`). Belongs to `MiniRustAdmitted` (not
`MiniRustExactAdmitted`): Anneal faults `.undefined` on surrogate `0xD800`,
while authentic MiniRust lowers `char` to niche-free `u32` and returns
`.int 0xD800`. -/
noncomputable def progCharSurrogate : Program :=
  mkWitnessProg {
    argumentCount := 0
    locals := [.char]
    basicBlocks := [{
      statements := [
        mkAssign 0 (.use (.constant
          { ty := .char, lit := .scalar (BitVec.ofNat 128 0xD800) }))
      ]
      terminator := .return_
    }]
  }

theorem witness_char_niche_strictness :
    let q := mkWitnessQuery []
    ∃ m₀, initMrMachine progCharSurrogate q = .ok m₀ ∧
      MiniRustAdmitted progCharSurrogate q ∧
      ¬ MiniRustExactAdmitted progCharSurrogate q ∧
      ReachesResult progCharSurrogate q (.fault .undefined) ∧
      mrRunFuel 12 m₀ = .returned (.int 0xD800) ∧
      MrBehavior m₀ (.int 0xD800) := by
  dsimp only
  cases hinitM : initMrMachine progCharSurrogate (mkWitnessQuery []) with
  | error _ => cases hinitM
  | ok m₀ =>
    cases hinitA : initState progCharSurrogate (mkWitnessQuery []) with
    | error _ => cases hinitA
    | ok s₀ =>
      have hadm : MiniRustAdmitted progCharSurrogate (mkWitnessQuery []) :=
        ⟨rfl, rfl, rfl⟩
      have hnotExact :
          ¬ MiniRustExactAdmitted progCharSurrogate (mkWitnessQuery []) := by
        intro hex
        dsimp only [MiniRustExactAdmitted] at hex
        have hfalse : MiniRustExactProgAdmitted progCharSurrogate = false := rfl
        rw [hfalse] at hex; cases hex.1
      have hrunA : annealRunFuel progCharSurrogate 6 s₀ = .fault .undefined := by
        cases hinitA; rfl
      have hrunM : mrRunFuel 12 m₀ = .returned (.int 0xD800) := by
        cases hinitM; rfl
      exact ⟨m₀, rfl, hadm, hnotExact, annealRunFuel_fault hinitA hrunA,
        hrunM, mrRunFuel_returned hrunM⟩

/-- Witness 9c: Program using `Operand.move` (`_0 = move _1; return`).
Belongs to `MiniRustAdmitted` and not `MiniRustExactAdmitted`. -/
noncomputable def progMoveSimple : Program :=
  let u32T : MirTy := .int .i32 false
  mkWitnessProg {
    argumentCount := 1
    locals := [u32T, u32T]
    basicBlocks := [{
      statements := [mkAssign 0 (.use (mkMove 1))]
      terminator := .return_
    }]
  }

noncomputable def queryMoveSimple : Query :=
  mkWitnessQuery [mkScalarVal .i32 false 42]

theorem witness_strict_move_inclusion :
    ∃ m₀, initMrMachine progMoveSimple queryMoveSimple = .ok m₀ ∧
      MiniRustAdmitted progMoveSimple queryMoveSimple ∧
      ¬ MiniRustExactAdmitted progMoveSimple queryMoveSimple ∧
      Behavior progMoveSimple queryMoveSimple
        (.returned ⟨mkScalarVal .i32 false 42, ⟨[]⟩⟩) ∧
      mrRunFuel 12 m₀ = .returned (translateVal (mkScalarVal .i32 false 42)) ∧
      MrBehavior m₀ (translateVal (mkScalarVal .i32 false 42)) := by
  cases hinitM : initMrMachine progMoveSimple queryMoveSimple with
  | error _ => cases hinitM
  | ok m₀ =>
    cases hinitA : initState progMoveSimple queryMoveSimple with
    | error _ => cases hinitA
    | ok s₀ =>
      have hadm : MiniRustAdmitted progMoveSimple queryMoveSimple :=
        ⟨rfl, rfl, rfl⟩
      have hnotExact : ¬ MiniRustExactAdmitted progMoveSimple queryMoveSimple := by
        intro hex
        dsimp only [MiniRustExactAdmitted] at hex
        have hfalse : MiniRustExactProgAdmitted progMoveSimple = false := rfl
        rw [hfalse] at hex; cases hex.1
      have hrunA : annealRunFuel progMoveSimple 6 s₀ =
          .done (.returned ⟨mkScalarVal .i32 false 42, ⟨[]⟩⟩) := by
        cases hinitA; rfl
      have hrunM : mrRunFuel 12 m₀ =
          .returned (translateVal (mkScalarVal .i32 false 42)) := by
        cases hinitM; rfl
      exact ⟨m₀, rfl, hadm, hnotExact, annealRunFuel_returned hinitA hrunA,
        hrunM, mrRunFuel_returned hrunM⟩

/-- Witness 9d: Semantic separation between `deinitMovedPlace = true` (Anneal)
and MiniRust's non-deinitializing `Load` (`_2 = move _1; _0 = copy _1; return`).
Anneal faults `.undefined` (stricter), while MiniRust executes directly to
`.returned (translateVal 42u32)`. -/
noncomputable def progMoveThenRead : Program :=
  let u32T : MirTy := .int .i32 false
  mkWitnessProg {
    argumentCount := 1
    locals := [u32T, u32T, u32T]
    basicBlocks := [{
      statements := [
        mkAssign 2 (.use (mkMove 1)),
        mkAssign 0 (.use (mkCopy 1))
      ]
      terminator := .return_
    }]
  }

theorem witness_move_semantic_strictness :
    ∃ m₀, initMrMachine progMoveThenRead queryMoveSimple = .ok m₀ ∧
      MiniRustAdmitted progMoveThenRead queryMoveSimple ∧
      ¬ MiniRustExactAdmitted progMoveThenRead queryMoveSimple ∧
      ReachesResult progMoveThenRead queryMoveSimple (.fault .undefined) ∧
      mrRunFuel 12 m₀ = .returned (translateVal (mkScalarVal .i32 false 42)) ∧
      MrBehavior m₀ (translateVal (mkScalarVal .i32 false 42)) := by
  cases hinitM : initMrMachine progMoveThenRead queryMoveSimple with
  | error _ => cases hinitM
  | ok m₀ =>
    cases hinitA : initState progMoveThenRead queryMoveSimple with
    | error _ => cases hinitA
    | ok s₀ =>
      have hadm : MiniRustAdmitted progMoveThenRead queryMoveSimple :=
        ⟨rfl, rfl, rfl⟩
      have hnotExact :
          ¬ MiniRustExactAdmitted progMoveThenRead queryMoveSimple := by
        intro hex
        dsimp only [MiniRustExactAdmitted] at hex
        have hfalse : MiniRustExactProgAdmitted progMoveThenRead = false := rfl
        rw [hfalse] at hex; cases hex.1
      have hrunA : annealRunFuel progMoveThenRead 8 s₀ = .fault .undefined := by
        cases hinitA; rfl
      have hrunM : mrRunFuel 12 m₀ =
          .returned (translateVal (mkScalarVal .i32 false 42)) := by
        cases hinitM; rfl
      exact ⟨m₀, rfl, hadm, hnotExact, annealRunFuel_fault hinitA hrunA,
        hrunM, mrRunFuel_returned hrunM⟩

/-! ## Negative UB Witnesses (`MiniRustExactAdmitted`) -/

/-- Negative Witness 1: Division by zero (`10u32 / 0u32`) is UB in both Anneal
and MiniRust. -/
noncomputable def progUbDivByZero : Program :=
  let u32T : MirTy := .int .i32 false
  mkWitnessProg {
    argumentCount := 0
    locals := [u32T]
    basicBlocks := [{
      statements := [mkAssign 0 (.binaryOp .div
        (mkScalarConst .i32 false 10) (mkScalarConst .i32 false 0))]
      terminator := .return_
    }]
  }

theorem witness_ub_div_by_zero :
    let q := mkWitnessQuery []
    ∃ m₀, initMrMachine progUbDivByZero q = .ok m₀ ∧
      MiniRustExactAdmitted progUbDivByZero q ∧
      ReachesResult progUbDivByZero q (.fault .undefined) ∧
      mrRunFuel 12 m₀ = .ub "division by zero" ∧
      MrFaultsUB m₀ := by
  dsimp only
  cases hinitM : initMrMachine progUbDivByZero (mkWitnessQuery []) with
  | error _ => cases hinitM
  | ok m₀ =>
    cases hinitA : initState progUbDivByZero (mkWitnessQuery []) with
    | error _ => cases hinitA
    | ok s₀ =>
      exact ⟨m₀, rfl, witness_exact_ub progUbDivByZero (mkWitnessQuery []) 6 12
        "division by zero" ⟨rfl, rfl, rfl⟩ s₀ m₀ hinitA hinitM
        (by cases hinitA; rfl) (by cases hinitM; rfl)⟩

/-- Negative Witness 2: Signed division overflow `INT8_MIN / -1`
(`0x80i8 / 0xFFi8`). -/
noncomputable def progUbIntMinDivNegOne : Program :=
  let i8T : MirTy := .int .i8 true
  mkWitnessProg {
    argumentCount := 0
    locals := [i8T]
    basicBlocks := [{
      statements := [mkAssign 0 (.binaryOp .div
        (mkScalarConst .i8 true 128) (mkScalarConst .i8 true 255))]
      terminator := .return_
    }]
  }

theorem witness_ub_int_min_div_neg_one :
    let q := mkWitnessQuery []
    ∃ m₀, initMrMachine progUbIntMinDivNegOne q = .ok m₀ ∧
      MiniRustExactAdmitted progUbIntMinDivNegOne q ∧
      ReachesResult progUbIntMinDivNegOne q (.fault .undefined) ∧
      mrRunFuel 12 m₀ = .ub "overflow in division" ∧
      MrFaultsUB m₀ := by
  dsimp only
  cases hinitM : initMrMachine progUbIntMinDivNegOne (mkWitnessQuery []) with
  | error _ => cases hinitM
  | ok m₀ =>
    cases hinitA : initState progUbIntMinDivNegOne (mkWitnessQuery []) with
    | error _ => cases hinitA
    | ok s₀ =>
      exact ⟨m₀, rfl, witness_exact_ub progUbIntMinDivNegOne (mkWitnessQuery [])
        6 12 "overflow in division" ⟨rfl, rfl, rfl⟩ s₀ m₀ hinitA hinitM
        (by cases hinitA; rfl) (by cases hinitM; rfl)⟩

/-- Negative Witness 3: Unchecked arithmetic overflow
(`addUnchecked 250u8 10u8`). -/
noncomputable def progUbUncheckedOverflow : Program :=
  let u8T : MirTy := .int .i8 false
  mkWitnessProg {
    argumentCount := 0
    locals := [u8T]
    basicBlocks := [{
      statements := [mkAssign 0 (.binaryOp .addUnchecked
        (mkScalarConst .i8 false 250) (mkScalarConst .i8 false 10))]
      terminator := .return_
    }]
  }

theorem witness_ub_unchecked_overflow :
    let q := mkWitnessQuery []
    ∃ m₀, initMrMachine progUbUncheckedOverflow q = .ok m₀ ∧
      MiniRustExactAdmitted progUbUncheckedOverflow q ∧
      ReachesResult progUbUncheckedOverflow q (.fault .undefined) ∧
      mrRunFuel 12 m₀ = .ub "overflow in unchecked add" ∧
      MrFaultsUB m₀ := by
  dsimp only
  cases hinitM : initMrMachine progUbUncheckedOverflow (mkWitnessQuery []) with
  | error _ => cases hinitM
  | ok m₀ =>
    cases hinitA : initState progUbUncheckedOverflow (mkWitnessQuery []) with
    | error _ => cases hinitA
    | ok s₀ =>
      exact ⟨m₀, rfl, witness_exact_ub progUbUncheckedOverflow
        (mkWitnessQuery []) 6 12 "overflow in unchecked add" ⟨rfl, rfl, rfl⟩
        s₀ m₀ hinitA hinitM (by cases hinitA; rfl) (by cases hinitM; rfl)⟩

/-- Negative Witness 4: Unchecked out-of-range shift
(`shlUnchecked 1u8 8u8`). -/
noncomputable def progUbBadShift : Program :=
  let u8T : MirTy := .int .i8 false
  mkWitnessProg {
    argumentCount := 0
    locals := [u8T]
    basicBlocks := [{
      statements := [mkAssign 0 (.binaryOp .shlUnchecked
        (mkScalarConst .i8 false 1) (mkScalarConst .i8 false 8))]
      terminator := .return_
    }]
  }

theorem witness_ub_bad_shift :
    let q := mkWitnessQuery []
    ∃ m₀, initMrMachine progUbBadShift q = .ok m₀ ∧
      MiniRustExactAdmitted progUbBadShift q ∧
      ReachesResult progUbBadShift q (.fault .undefined) ∧
      mrRunFuel 12 m₀ = .ub "overflow in unchecked shift" ∧
      MrFaultsUB m₀ := by
  dsimp only
  cases hinitM : initMrMachine progUbBadShift (mkWitnessQuery []) with
  | error _ => cases hinitM
  | ok m₀ =>
    cases hinitA : initState progUbBadShift (mkWitnessQuery []) with
    | error _ => cases hinitA
    | ok s₀ =>
      exact ⟨m₀, rfl, witness_exact_ub progUbBadShift (mkWitnessQuery []) 6 12
        "overflow in unchecked shift" ⟨rfl, rfl, rfl⟩ s₀ m₀ hinitA hinitM
        (by cases hinitA; rfl) (by cases hinitM; rfl)⟩

/-- Negative Witness 5: Reading an uninitialized live local (`_0 = copy _1`). -/
noncomputable def progUbUninitRead : Program :=
  let u32T : MirTy := .int .i32 false
  mkWitnessProg {
    argumentCount := 0
    locals := [u32T, u32T]
    basicBlocks := [{
      statements := [mkAssign 0 (.use (mkCopy 1))]
      terminator := .return_
    }]
  }

theorem witness_ub_uninit_read :
    let q := mkWitnessQuery []
    ∃ m₀, initMrMachine progUbUninitRead q = .ok m₀ ∧
      MiniRustExactAdmitted progUbUninitRead q ∧
      ReachesResult progUbUninitRead q (.fault .undefined) ∧
      mrRunFuel 12 m₀ = .ub
        "load at type but the data in memory violates the language invariant" ∧
      MrFaultsUB m₀ := by
  dsimp only
  cases hinitM : initMrMachine progUbUninitRead (mkWitnessQuery []) with
  | error _ => cases hinitM
  | ok m₀ =>
    cases hinitA : initState progUbUninitRead (mkWitnessQuery []) with
    | error _ => cases hinitA
    | ok s₀ =>
      exact ⟨m₀, rfl, witness_exact_ub progUbUninitRead (mkWitnessQuery []) 6 12
        "load at type but the data in memory violates the language invariant"
        ⟨rfl, rfl, rfl⟩ s₀ m₀ hinitA hinitM (by cases hinitA; rfl)
        (by cases hinitM; rfl)⟩

/-- Negative Witness 6: Executing `TerminatorKind.unreachable`. -/
noncomputable def progUbUnreachable : Program :=
  mkWitnessProg {
    argumentCount := 0
    locals := [.unit]
    basicBlocks := [{
      statements := []
      terminator := .unreachable
    }]
  }

theorem witness_ub_unreachable :
    let q := mkWitnessQuery []
    ∃ m₀, initMrMachine progUbUnreachable q = .ok m₀ ∧
      MiniRustExactAdmitted progUbUnreachable q ∧
      ReachesResult progUbUnreachable q (.fault .undefined) ∧
      mrRunFuel 12 m₀ = .ub "reached unreachable code" ∧
      MrFaultsUB m₀ := by
  dsimp only
  cases hinitM : initMrMachine progUbUnreachable (mkWitnessQuery []) with
  | error _ => cases hinitM
  | ok m₀ =>
    cases hinitA : initState progUbUnreachable (mkWitnessQuery []) with
    | error _ => cases hinitA
    | ok s₀ =>
      exact ⟨m₀, rfl, witness_exact_ub progUbUnreachable (mkWitnessQuery [])
        6 12 "reached unreachable code" ⟨rfl, rfl, rfl⟩ s₀ m₀ hinitA hinitM
        (by cases hinitA; rfl) (by cases hinitM; rfl)⟩

/-! ## Standalone MiniRust Machine Witness (`bottomOfStack` Return UB) -/

/-- Standalone MiniRust machine exercising `Machine.lean` directly outside the
`translateProg` harness: a start frame (`StackPopAction.bottomOfStack`)
executing `MrTerminator.return_` raises UB
(`"the start function must not return"` per `spec/lang/step/terminators.md`). -/
def mrBottomOfStackReturnMachine : Machine :=
  let startFunc : MrFunction := {
    locals := [unitTy]
    args := []
    ret := 0
    blocks := [{ statements := [], terminator := .return_ }]
    start := 0
  }
  let alloc0 : MrAllocation := {
    allocId := 0
    addr := 1
    align := ⟨1⟩
    live := true
    data := []
  }
  let ptr0 : ThinPtr := { addr := 1, allocId := some 0 }
  { prog := { functions := [startFunc], start := 0 }
    mem := { allocations := [alloc0], nextAddr := 17 }
    stack := [{
      func := startFunc
      locals := [(0, ptr0)]
      stackPopAction := .bottomOfStack
      nextBlock := 0
      nextStmt := 0
    }] }

theorem witness_mr_bottom_of_stack_return_ub :
    mrStep mrBottomOfStackReturnMachine =
      .ub "the start function must not return" ∧
    MrFaultsUB mrBottomOfStackReturnMachine := by
  have hstep : mrStep mrBottomOfStackReturnMachine =
      .ub "the start function must not return" := rfl
  exact ⟨hstep, ⟨mrBottomOfStackReturnMachine,
    "the start function must not return",
    MrReaches.refl mrBottomOfStackReturnMachine, hstep⟩⟩

end Anneal.MiniRust
