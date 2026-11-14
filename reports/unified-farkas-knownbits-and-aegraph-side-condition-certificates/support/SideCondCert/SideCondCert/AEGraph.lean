-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import SideCondCert.Domain

namespace SideCondCert

/-- Directed acyclic expression (`AEGraph`) terms with explicit `let`-DAG sharing (`letBind`),
poison-producing checked addition (`addNuw`), wrapping addition (`addWrap`), subtraction,
multiplication, and `freeze`. -/
inductive DAGExpr where
  | const (v : Int)
  | var (id : Nat)
  | addWrap (a b : DAGExpr)
  | addNuw (a b : DAGExpr) (limit : Int)
  | subWrap (a b : DAGExpr)
  | mulWrap (a b : DAGExpr)
  | freeze (defaultVal : Int) (e : DAGExpr)
  | letBind (bound : DAGExpr) (body : DAGExpr)
  deriving DecidableEq, Repr

/-- Evaluate a `DAGExpr` under variable environment `env : Nat → PoisonOr Int`
and `let`-bound value `letVal : PoisonOr Int`. -/
def evalDAGExpr (env : Nat → PoisonOr Int) (letVal : PoisonOr Int) : DAGExpr → PoisonOr Int
  | .const v => .val v
  | .var 0   => letVal
  | .var (k + 1) => env k
  | .addWrap a b =>
      liftPoison2 (fun x y => .val (x + y)) (evalDAGExpr env letVal a) (evalDAGExpr env letVal b)
  | .addNuw a b limit =>
      liftPoison2
        (fun x y => if 0 ≤ x ∧ 0 ≤ y ∧ x + y < limit then .val (x + y) else .poison)
        (evalDAGExpr env letVal a) (evalDAGExpr env letVal b)
  | .subWrap a b =>
      liftPoison2 (fun x y => .val (x - y)) (evalDAGExpr env letVal a) (evalDAGExpr env letVal b)
  | .mulWrap a b =>
      liftPoison2 (fun x y => .val (x * y)) (evalDAGExpr env letVal a) (evalDAGExpr env letVal b)
  | .freeze d e =>
      freezePoison d (evalDAGExpr env letVal e)
  | .letBind bound body =>
      let vBound := evalDAGExpr env letVal bound
      evalDAGExpr env vBound body

/-- Syntactic check that a `DAGExpr` contains no `freeze` nodes (`isFreezeFree`).
Because `freeze` is non-monotonic with respect to `refinesPoison` (`poison ⊑_poison val 5`,
yet `freeze 0 poison = val 0` does not refine `freeze 0 (val 5) = val 5`), lifting a directed
refinement `bound1 ⊑_poison bound2` into `letBind bound body` requires `isFreezeFree body`. -/
def isFreezeFree : DAGExpr → Bool
  | .const _ => true
  | .var _ => true
  | .addWrap a b => isFreezeFree a && isFreezeFree b
  | .addNuw a b _ => isFreezeFree a && isFreezeFree b
  | .subWrap a b => isFreezeFree a && isFreezeFree b
  | .mulWrap a b => isFreezeFree a && isFreezeFree b
  | .freeze _ _ => false
  | .letBind bound body => isFreezeFree bound && isFreezeFree body

theorem evalDAGExpr_mono_letVal (env : Nat → PoisonOr Int) (e : DAGExpr)
    (h_ff : isFreezeFree e = true)
    {v1 v2 : PoisonOr Int} (h_ref : refinesPoison v1 v2) :
    refinesPoison (evalDAGExpr env v1 e) (evalDAGExpr env v2 e) := by
  induction e generalizing v1 v2 with
  | const v => exact refinesPoison_refl _
  | var id =>
    cases id with
    | zero => exact h_ref
    | succ k => exact refinesPoison_refl _
  | addWrap a b iha ihb =>
    simp only [isFreezeFree, Bool.and_eq_true] at h_ff
    exact liftPoison2_mono _ (iha h_ff.1 h_ref) (ihb h_ff.2 h_ref)
  | addNuw a b limit iha ihb =>
    simp only [isFreezeFree, Bool.and_eq_true] at h_ff
    exact liftPoison2_mono _ (iha h_ff.1 h_ref) (ihb h_ff.2 h_ref)
  | subWrap a b iha ihb =>
    simp only [isFreezeFree, Bool.and_eq_true] at h_ff
    exact liftPoison2_mono _ (iha h_ff.1 h_ref) (ihb h_ff.2 h_ref)
  | mulWrap a b iha ihb =>
    simp only [isFreezeFree, Bool.and_eq_true] at h_ff
    exact liftPoison2_mono _ (iha h_ff.1 h_ref) (ihb h_ff.2 h_ref)
  | freeze d inner =>
    simp [isFreezeFree] at h_ff
  | letBind bound body ihBound ihBody =>
    simp only [isFreezeFree, Bool.and_eq_true] at h_ff
    simp only [evalDAGExpr]
    exact ihBody h_ff.2 (ihBound h_ff.1 h_ref)

/-- Directed poison-monotonic e-graph refinement certificates (`AEGraphCert`). -/
inductive AEGraphCert where
  | refl (e : DAGExpr)
  | addZeroRight (e : DAGExpr)
  | addComm (a b : DAGExpr)
  | subSelfToZero (e : DAGExpr)
  | mulOneRight (e : DAGExpr)
  | dropNuwToWrap (a b : DAGExpr) (limit : Int)
  | insertFreeze (d : Int) (e : DAGExpr)
  | elimFreezeConst (d v : Int)
  | congAddWrap (c1 c2 : AEGraphCert)
  | congSubWrap (c1 c2 : AEGraphCert)
  | congMulWrap (c1 c2 : AEGraphCert)
  | congLetBind (cBound cBody : AEGraphCert)
  deriving DecidableEq, Repr

/-- Synthesize `(src, tgt)` endpoints for an `AEGraphCert`. -/
def inferAEGraphPair : AEGraphCert → DAGExpr × DAGExpr
  | .refl e => (e, e)
  | .addZeroRight e => (.addWrap e (.const 0), e)
  | .addComm a b => (.addWrap a b, .addWrap b a)
  | .subSelfToZero e => (.subWrap e e, .const 0)
  | .mulOneRight e => (.mulWrap e (.const 1), e)
  | .dropNuwToWrap a b limit => (.addNuw a b limit, .addWrap a b)
  | .insertFreeze d e => (e, .freeze d e)
  | .elimFreezeConst d v => (.freeze d (.const v), .const v)
  | .congAddWrap c1 c2 =>
      let (s1, t1) := inferAEGraphPair c1
      let (s2, t2) := inferAEGraphPair c2
      (.addWrap s1 s2, .addWrap t1 t2)
  | .congSubWrap c1 c2 =>
      let (s1, t1) := inferAEGraphPair c1
      let (s2, t2) := inferAEGraphPair c2
      (.subWrap s1 s2, .subWrap t1 t2)
  | .congMulWrap c1 c2 =>
      let (s1, t1) := inferAEGraphPair c1
      let (s2, t2) := inferAEGraphPair c2
      (.mulWrap s1 s2, .mulWrap t1 t2)
  | .congLetBind cBound cBody =>
      let (sB, tB) := inferAEGraphPair cBound
      let (sBody, tBody) := inferAEGraphPair cBody
      (.letBind sB sBody, .letBind tB tBody)

/-- Context monotonicity side condition checker for `AEGraphCert`:
In `congLetBind cBound cBody`, the target body `(inferAEGraphPair cBody).2` must be
`freeze`-free (`isFreezeFree = true`) so that refining `sB ⊑_poison tB` preserves refinement
through `letBind`. -/
def checkAEGraphMono : AEGraphCert → Bool
  | .refl _ => true
  | .addZeroRight _ => true
  | .addComm _ _ => true
  | .subSelfToZero _ => true
  | .mulOneRight _ => true
  | .dropNuwToWrap _ _ _ => true
  | .insertFreeze _ _ => true
  | .elimFreezeConst _ _ => true
  | .congAddWrap c1 c2 => checkAEGraphMono c1 && checkAEGraphMono c2
  | .congSubWrap c1 c2 => checkAEGraphMono c1 && checkAEGraphMono c2
  | .congMulWrap c1 c2 => checkAEGraphMono c1 && checkAEGraphMono c2
  | .congLetBind cBound cBody =>
      checkAEGraphMono cBound &&
      checkAEGraphMono cBody &&
      isFreezeFree (inferAEGraphPair cBody).2

/-- Executable boolean checker for `AEGraphCert`. -/
def checkAEGraphCert (src tgt : DAGExpr) (cert : AEGraphCert) : Bool :=
  let (s, t) := inferAEGraphPair cert
  decide (src = s ∧ tgt = t) && checkAEGraphMono cert

/-- Soundness of `inferAEGraphPair`: every certificate passing `checkAEGraphMono`
produces a valid poison refinement `eval s ⊑_poison eval t`!
Notice how `subSelfToZero` (`e - e ⊑_poison 0`) holds even when `e` evaluates to `.poison`,
because `.poison - .poison = .poison ⊑_poison .val 0`! -/
theorem inferAEGraphPair_sound (cert : AEGraphCert)
    (h_mono : checkAEGraphMono cert = true)
    (env : Nat → PoisonOr Int) (letVal : PoisonOr Int) :
    refinesPoison
      (evalDAGExpr env letVal (inferAEGraphPair cert).1)
      (evalDAGExpr env letVal (inferAEGraphPair cert).2) := by
  induction cert generalizing letVal with
  | refl e => exact refinesPoison_refl _
  | addZeroRight e =>
    simp only [inferAEGraphPair, evalDAGExpr]
    cases evalDAGExpr env letVal e with
    | val a => simp [liftPoison2, refinesPoison]
    | poison => exact Or.inl rfl
  | addComm a b =>
    simp only [inferAEGraphPair, evalDAGExpr]
    cases evalDAGExpr env letVal a <;> cases evalDAGExpr env letVal b <;>
      simp [liftPoison2, refinesPoison, Int.add_comm]
  | subSelfToZero e =>
    simp only [inferAEGraphPair, evalDAGExpr]
    cases evalDAGExpr env letVal e with
    | val a => simp [liftPoison2, refinesPoison, Int.sub_self]
    | poison => exact Or.inl rfl
  | mulOneRight e =>
    simp only [inferAEGraphPair, evalDAGExpr]
    cases evalDAGExpr env letVal e with
    | val a => simp [liftPoison2, refinesPoison, Int.mul_one]
    | poison => exact Or.inl rfl
  | dropNuwToWrap a b limit =>
    simp only [inferAEGraphPair, evalDAGExpr]
    cases evalDAGExpr env letVal a with
    | poison => exact Or.inl rfl
    | val va =>
      cases evalDAGExpr env letVal b with
      | poison => exact Or.inl rfl
      | val vb =>
        simp only [liftPoison2]
        by_cases h_ok : 0 ≤ va ∧ 0 ≤ vb ∧ va + vb < limit
        · simp [h_ok, refinesPoison]
        · simp [h_ok, refinesPoison]
  | insertFreeze d e =>
    simp only [inferAEGraphPair, evalDAGExpr]
    exact refinesPoison_freeze d (evalDAGExpr env letVal e)
  | elimFreezeConst d v =>
    simp only [inferAEGraphPair, evalDAGExpr, freezePoison]
    exact refinesPoison_refl _
  | congAddWrap c1 c2 ih1 ih2 =>
    simp only [checkAEGraphMono, Bool.and_eq_true] at h_mono
    simp only [inferAEGraphPair, evalDAGExpr]
    exact liftPoison2_mono _ (ih1 h_mono.1 letVal) (ih2 h_mono.2 letVal)
  | congSubWrap c1 c2 ih1 ih2 =>
    simp only [checkAEGraphMono, Bool.and_eq_true] at h_mono
    simp only [inferAEGraphPair, evalDAGExpr]
    exact liftPoison2_mono _ (ih1 h_mono.1 letVal) (ih2 h_mono.2 letVal)
  | congMulWrap c1 c2 ih1 ih2 =>
    simp only [checkAEGraphMono, Bool.and_eq_true] at h_mono
    simp only [inferAEGraphPair, evalDAGExpr]
    exact liftPoison2_mono _ (ih1 h_mono.1 letVal) (ih2 h_mono.2 letVal)
  | congLetBind cBound cBody ihBound ihBody =>
    simp only [checkAEGraphMono, Bool.and_eq_true] at h_mono
    rcases h_mono with ⟨⟨h_mB, h_mBody⟩, h_ff⟩
    simp only [inferAEGraphPair, evalDAGExpr]
    have h_refB := ihBound h_mB letVal
    have h_step1 := ihBody h_mBody (evalDAGExpr env letVal (inferAEGraphPair cBound).1)
    have h_step2 := evalDAGExpr_mono_letVal env (inferAEGraphPair cBody).2 h_ff h_refB
    exact refinesPoison_trans h_step1 h_step2

/-- Soundness of `checkAEGraphCert`. -/
theorem checkAEGraphCert_sound {src tgt : DAGExpr} {cert : AEGraphCert}
    (h_check : checkAEGraphCert src tgt cert = true)
    (env : Nat → PoisonOr Int) (letVal : PoisonOr Int) :
    refinesPoison (evalDAGExpr env letVal src) (evalDAGExpr env letVal tgt) := by
  simp only [checkAEGraphCert, Bool.and_eq_true, decide_eq_true_eq] at h_check
  rcases h_check with ⟨⟨rfl, rfl⟩, h_mono⟩
  exact inferAEGraphPair_sound cert h_mono env letVal

/-- Declarative validity specification for `AEGraphCert`. -/
structure ValidAEGraphCert (src tgt : DAGExpr) (cert : AEGraphCert) : Prop where
  src_eq  : src = (inferAEGraphPair cert).1
  tgt_eq  : tgt = (inferAEGraphPair cert).2
  mono_ok : checkAEGraphMono cert = true

/-- Bidirectional equivalence between `checkAEGraphCert` and `ValidAEGraphCert`. -/
theorem checkAEGraphCert_iff_valid (src tgt : DAGExpr) (cert : AEGraphCert) :
    checkAEGraphCert src tgt cert = true ↔ ValidAEGraphCert src tgt cert := by
  constructor
  · intro h
    simp only [checkAEGraphCert, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  · intro ⟨hs, ht, hm⟩
    simp [checkAEGraphCert, hs, ht, hm]

end SideCondCert
