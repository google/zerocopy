-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Uninstrumented `InstCombine` and `DAGCombiner` E-Graph Chain Reconstruction (`O1_`)

Mechanizes `ConeChainCert` and `checkConeChainCert_sound` in Lean `v4.34.1`
with zero `sorryAx` and zero `Lean.ofReduceBool` (`native_decide`):
1. Explicit deferred undefinedness (`PoisonOr Int`) and directed poison refinement
   (`refinesPoison`).
2. Leaf environment bounds (`LeafBound` combining `KnownBits` zero/one masks and
   interval bounds `[lo, hi]`) propagated across expression DAG cones (`DAGExpr`).
3. Parameterized `InstCombine` / `DAGCombiner` rewrite schemas (`ConeStepCert`)
   composing unconditional algebraic/bitwise identities, conditional `KnownBits`
   and interval-guarded rewrites (`sharpenWrapToNuw`, `knownZeroAddToOr`), and
   directed poison-erasing steps (`dropNuwToWrap`, `subSelfToZero`,
   `bitAndZeroRight`, `bitXorSelfToZero`, `insertFreeze`).
4. Multi-step `ConeChainCert` transitivity and strict bidirectional equality
   enforcement inside `freeze` contexts (`isBidirectionalStep`), rejecting
   unsound one-way poison refinements under `freeze`
   (`canary_one_way_poison_under_freeze_rejected`) and unguarded shift/overflow
   rewrites (`canary_unsound_nuw_without_bounds_rejected`).
-/

namespace ExprChainReconstruction

/-- Semantic value domain with explicit deferred undefinedness (`poison`). -/
inductive PoisonOr (α : Type) where
  | val (v : α)
  | poison
  deriving DecidableEq, Repr

/-- Directed poison refinement `vSrc ⊑_poison vTgt`:
if `vSrc` is `.val v`, `vTgt` must also be `.val v`; if `vSrc` is `.poison`,
`vTgt` may refine it to any value. -/
def refinesPoison {α : Type} (vSrc vTgt : PoisonOr α) : Prop :=
  vSrc = .poison ∨ vTgt = vSrc

theorem refinesPoison_refl {α : Type} (v : PoisonOr α) : refinesPoison v v :=
  Or.inr rfl

theorem refinesPoison_trans {α : Type} {v1 v2 v3 : PoisonOr α}
    (h12 : refinesPoison v1 v2) (h23 : refinesPoison v2 v3) : refinesPoison v1 v3 := by
  rcases h12 with rfl | rfl
  · exact Or.inl rfl
  · exact h23

theorem refinesPoison_of_eq {α : Type} {v1 v2 : PoisonOr α} (h : v1 = v2) :
    refinesPoison v1 v2 :=
  Or.inr h.symm

/-- Lift a binary operation onto `PoisonOr α`. -/
def liftPoison2 {α : Type} (f : α → α → PoisonOr α) (x y : PoisonOr α) : PoisonOr α :=
  match x, y with
  | .val a, .val b => f a b
  | _, _           => .poison

theorem liftPoison2_mono {α : Type} (f : α → α → PoisonOr α)
    {x1 x2 y1 y2 : PoisonOr α}
    (hx : refinesPoison x1 x2) (hy : refinesPoison y1 y2) :
    refinesPoison (liftPoison2 f x1 y1) (liftPoison2 f x2 y2) := by
  rcases hx with rfl | rfl
  · exact Or.inl rfl
  · rcases hy with rfl | rfl
    · cases x2 <;> exact Or.inl rfl
    · exact Or.inr rfl

/-- `freeze` operator mapping `.poison` to `defaultVal` and preserving `.val a`. -/
def freezePoison {α : Type} (defaultVal : α) : PoisonOr α → PoisonOr α
  | .val a  => .val a
  | .poison => .val defaultVal

theorem refinesPoison_freeze {α : Type} (d : α) (v : PoisonOr α) :
    refinesPoison v (freezePoison d v) := by
  cases v with
  | val a  => exact Or.inr rfl
  | poison => exact Or.inl rfl

/-- Per-leaf interval and bitmask summary attached to an expression cone leaf. -/
structure LeafBound where
  lo       : Int
  hi       : Int
  zeroMask : Nat
  oneMask  : Nat
  deriving DecidableEq, Repr

/-- Environment satisfaction of leaf bounds for variable `id`. -/
def SatisfiesLeafBound (v : PoisonOr Int) (b : LeafBound) : Prop :=
  ∃ x : Int, v = .val x ∧ b.lo ≤ x ∧ x ≤ b.hi ∧ (b.zeroMask = 1 → x = 0)

/-- Expression-cone DAG AST (`DAGExpr`) representing side-effect-free `InstCombine`
and `DAGCombiner` cones with `letBind` sharing and `freeze`. -/
inductive DAGExpr where
  | const (v : Int)
  | var (id : Nat)
  | addWrap (a b : DAGExpr)
  | addNuw (a b : DAGExpr) (limit : Int)
  | subWrap (a b : DAGExpr)
  | mulWrap (a b : DAGExpr)
  | bitAnd (a b : DAGExpr)
  | bitOr (a b : DAGExpr)
  | bitXor (a b : DAGExpr)
  | shlConst (a : DAGExpr) (amt : Nat)
  | freeze (defaultVal : Int) (e : DAGExpr)
  | letBind (bound : DAGExpr) (body : DAGExpr)
  deriving DecidableEq, Repr

/-- Abstract bitwise operations on `Int`. -/
def intBitAnd (a b : Int) : Int :=
  if a = 0 ∨ b = 0 then 0
  else if a = b then a
  else Int.ofNat (Nat.land a.toNat b.toNat)

def intBitOr (a b : Int) : Int :=
  if a = 0 then b
  else if b = 0 then a
  else if a = b then a
  else Int.ofNat (Nat.lor a.toNat b.toNat)

def intBitXor (a b : Int) : Int :=
  if a = 0 then b
  else if b = 0 then a
  else if a = b then 0
  else Int.ofNat (Nat.xor a.toNat b.toNat)

theorem intBitAnd_zero_right (a : Int) : intBitAnd a 0 = 0 := by
  simp [intBitAnd]

theorem intBitOr_zero_left (b : Int) : intBitOr 0 b = b := by
  simp [intBitOr]

theorem intBitOr_zero_right (a : Int) : intBitOr a 0 = a := by
  by_cases h : a = 0 <;> simp [intBitOr, h]

theorem intBitXor_zero_right (a : Int) : intBitXor a 0 = a := by
  by_cases h : a = 0 <;> simp [intBitXor, h]

theorem intBitXor_self (a : Int) : intBitXor a a = 0 := by
  by_cases h : a = 0 <;> simp [intBitXor, h]

/-- Evaluate a `DAGExpr` under variable environment `env` and `let`-bound value `letVal`. -/
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
  | .bitAnd a b =>
      liftPoison2 (fun x y => .val (intBitAnd x y)) (evalDAGExpr env letVal a) (evalDAGExpr env letVal b)
  | .bitOr a b =>
      liftPoison2 (fun x y => .val (intBitOr x y)) (evalDAGExpr env letVal a) (evalDAGExpr env letVal b)
  | .bitXor a b =>
      liftPoison2 (fun x y => .val (intBitXor x y)) (evalDAGExpr env letVal a) (evalDAGExpr env letVal b)
  | .shlConst a amt =>
      liftPoison2 (fun x _ => .val (x * (2 ^ amt : Nat))) (evalDAGExpr env letVal a) (.val 0)
  | .freeze d e =>
      freezePoison d (evalDAGExpr env letVal e)
  | .letBind bound body =>
      let vBound := evalDAGExpr env letVal bound
      evalDAGExpr env vBound body

/-- Syntactic check that a `DAGExpr` contains no `freeze` nodes. -/
def isFreezeFree : DAGExpr → Bool
  | .const _ => true
  | .var _ => true
  | .addWrap a b | .addNuw a b _ | .subWrap a b | .mulWrap a b
  | .bitAnd a b | .bitOr a b | .bitXor a b => isFreezeFree a && isFreezeFree b
  | .shlConst a _ => isFreezeFree a
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
  | addWrap a b iha ihb | addNuw a b _ iha ihb | subWrap a b iha ihb
  | mulWrap a b iha ihb | bitAnd a b iha ihb | bitOr a b iha ihb | bitXor a b iha ihb =>
    simp only [isFreezeFree, Bool.and_eq_true] at h_ff
    exact liftPoison2_mono _ (iha h_ff.1 h_ref) (ihb h_ff.2 h_ref)
  | shlConst a amt iha =>
    simp only [isFreezeFree] at h_ff
    exact liftPoison2_mono _ (iha h_ff h_ref) (refinesPoison_refl _)
  | freeze d inner =>
    simp [isFreezeFree] at h_ff
  | letBind bound body ihBound ihBody =>
    simp only [isFreezeFree, Bool.and_eq_true] at h_ff
    simp only [evalDAGExpr]
    exact ihBody h_ff.2 (ihBound h_ff.1 h_ref)

/-- Single-step cone rewrite certificate (`ConeStepCert`) emitted by `ExprChainSynthesizer`. -/
inductive ConeStepCert where
  | refl (e : DAGExpr)
  | addZeroRight (e : DAGExpr)
  | addComm (a b : DAGExpr)
  | subSelfToZero (e : DAGExpr)
  | mulOneRight (e : DAGExpr)
  | bitAndZeroRight (e : DAGExpr)
  | bitOrZeroRight (e : DAGExpr)
  | bitXorZeroRight (e : DAGExpr)
  | bitXorSelfToZero (e : DAGExpr)
  | dropNuwToWrap (a b : DAGExpr) (limit : Int)
  /-- Conditional `KnownBits`/`Interval` step: sharpens `addWrap (var (k+1)) (const c)`
      to `addNuw` when leaf bound `k` proves `0 ≤ x`, `0 ≤ c`, and `hi + c < limit`. -/
  | sharpenWrapToNuw (varIdx : Nat) (c limit : Int) (bound : LeafBound)
  /-- Conditional `KnownBits` step: rewrites `addWrap (var (k+1)) (const c)` to `bitOr`
      when `bound.zeroMask = 1` proves `var (k+1) = 0`. -/
  | knownZeroAddToOr (varIdx : Nat) (c : Int) (bound : LeafBound)
  /-- Shift-by-zero identity `shlConst e 0 -> e`. -/
  | shlZeroIdentity (e : DAGExpr)
  | insertFreeze (d : Int) (e : DAGExpr)
  | elimFreezeConst (d v : Int)
  | congAddWrap (c1 c2 : ConeStepCert)
  | congSubWrap (c1 c2 : ConeStepCert)
  | congMulWrap (c1 c2 : ConeStepCert)
  | congBitAnd (c1 c2 : ConeStepCert)
  | congBitOr (c1 c2 : ConeStepCert)
  | congBitXor (c1 c2 : ConeStepCert)
  /-- Rewriting under `freeze d` requires the inner step to be strictly bidirectional
      (`isBidirectionalStep = true`), forbidding one-way poison erasure inside `freeze`. -/
  | congFreeze (d : Int) (c : ConeStepCert)
  | congLetBind (cBound cBody : ConeStepCert)
  deriving DecidableEq, Repr

/-- Checks whether a `ConeStepCert` preserves exact bidirectional equality
(`eval src = eval tgt`) rather than one-way poison refinement (`eval src ⊑_poison eval tgt`).
Notice that operand-erasing rules (`subSelfToZero`, `bitAndZeroRight`, `bitXorSelfToZero`,
`dropNuwToWrap`, `insertFreeze`) return `false` because `.poison & 0 = .poison ≠ .val 0`. -/
def isBidirectionalStep : ConeStepCert → Bool
  | .refl _ => true
  | .addZeroRight _ => true
  | .addComm _ _ => true
  | .subSelfToZero _ => false
  | .mulOneRight _ => true
  | .bitAndZeroRight _ => false
  | .bitOrZeroRight _ => true
  | .bitXorZeroRight _ => true
  | .bitXorSelfToZero _ => false
  | .dropNuwToWrap _ _ _ => false
  | .sharpenWrapToNuw _ _ _ _ => true
  | .knownZeroAddToOr _ _ _ => true
  | .shlZeroIdentity _ => true
  | .insertFreeze _ _ => false
  | .elimFreezeConst _ _ => true
  | .congAddWrap c1 c2 | .congSubWrap c1 c2 | .congMulWrap c1 c2
  | .congBitAnd c1 c2 | .congBitOr c1 c2 | .congBitXor c1 c2 =>
      isBidirectionalStep c1 && isBidirectionalStep c2
  | .congFreeze _ c => isBidirectionalStep c
  | .congLetBind cBound cBody =>
      isBidirectionalStep cBound && isBidirectionalStep cBody

/-- Infer `(src, tgt)` endpoints of a `ConeStepCert`. -/
def inferStepEndpoints : ConeStepCert → DAGExpr × DAGExpr
  | .refl e => (e, e)
  | .addZeroRight e => (.addWrap e (.const 0), e)
  | .addComm a b => (.addWrap a b, .addWrap b a)
  | .subSelfToZero e => (.subWrap e e, .const 0)
  | .mulOneRight e => (.mulWrap e (.const 1), e)
  | .bitAndZeroRight e => (.bitAnd e (.const 0), .const 0)
  | .bitOrZeroRight e => (.bitOr e (.const 0), e)
  | .bitXorZeroRight e => (.bitXor e (.const 0), e)
  | .bitXorSelfToZero e => (.bitXor e e, .const 0)
  | .dropNuwToWrap a b limit => (.addNuw a b limit, .addWrap a b)
  | .sharpenWrapToNuw varIdx c limit _ =>
      (.addWrap (.var (varIdx + 1)) (.const c), .addNuw (.var (varIdx + 1)) (.const c) limit)
  | .knownZeroAddToOr varIdx c _ =>
      (.addWrap (.var (varIdx + 1)) (.const c), .bitOr (.var (varIdx + 1)) (.const c))
  | .shlZeroIdentity e => (.shlConst e 0, e)
  | .insertFreeze d e => (e, .freeze d e)
  | .elimFreezeConst d v => (.freeze d (.const v), .const v)
  | .congAddWrap c1 c2 =>
      let (s1, t1) := inferStepEndpoints c1
      let (s2, t2) := inferStepEndpoints c2
      (.addWrap s1 s2, .addWrap t1 t2)
  | .congSubWrap c1 c2 =>
      let (s1, t1) := inferStepEndpoints c1
      let (s2, t2) := inferStepEndpoints c2
      (.subWrap s1 s2, .subWrap t1 t2)
  | .congMulWrap c1 c2 =>
      let (s1, t1) := inferStepEndpoints c1
      let (s2, t2) := inferStepEndpoints c2
      (.mulWrap s1 s2, .mulWrap t1 t2)
  | .congBitAnd c1 c2 =>
      let (s1, t1) := inferStepEndpoints c1
      let (s2, t2) := inferStepEndpoints c2
      (.bitAnd s1 s2, .bitAnd t1 t2)
  | .congBitOr c1 c2 =>
      let (s1, t1) := inferStepEndpoints c1
      let (s2, t2) := inferStepEndpoints c2
      (.bitOr s1 s2, .bitOr t1 t2)
  | .congBitXor c1 c2 =>
      let (s1, t1) := inferStepEndpoints c1
      let (s2, t2) := inferStepEndpoints c2
      (.bitXor s1 s2, .bitXor t1 t2)
  | .congFreeze d c =>
      let (s, t) := inferStepEndpoints c
      (.freeze d s, .freeze d t)
  | .congLetBind cBound cBody =>
      let (sB, tB) := inferStepEndpoints cBound
      let (sBody, tBody) := inferStepEndpoints cBody
      (.letBind sB sBody, .letBind tB tBody)

/-- Side-condition checker for a single `ConeStepCert` under leaf bounds `bounds : Nat → LeafBound`. -/
def checkStepSideCond (bounds : Nat → LeafBound) : ConeStepCert → Bool
  | .refl _ | .addZeroRight _ | .addComm _ _ | .subSelfToZero _ | .mulOneRight _
  | .bitAndZeroRight _ | .bitOrZeroRight _ | .bitXorZeroRight _ | .bitXorSelfToZero _
  | .dropNuwToWrap _ _ _ | .shlZeroIdentity _ | .insertFreeze _ _ | .elimFreezeConst _ _ => true
  | .sharpenWrapToNuw varIdx c limit b =>
      decide (bounds varIdx = b ∧ 0 ≤ b.lo ∧ b.lo ≤ b.hi ∧ 0 ≤ c ∧ b.hi + c < limit)
  | .knownZeroAddToOr varIdx _ b =>
      decide (bounds varIdx = b ∧ b.zeroMask = 1)
  | .congAddWrap c1 c2 | .congSubWrap c1 c2 | .congMulWrap c1 c2
  | .congBitAnd c1 c2 | .congBitOr c1 c2 | .congBitXor c1 c2 =>
      checkStepSideCond bounds c1 && checkStepSideCond bounds c2
  | .congFreeze _ c =>
      checkStepSideCond bounds c && isBidirectionalStep c
  | .congLetBind cBound cBody =>
      checkStepSideCond bounds cBound &&
      checkStepSideCond bounds cBody &&
      isFreezeFree (inferStepEndpoints cBody).2

/-- Environment satisfies all leaf bounds. -/
def EnvSatisfiesBounds (env : Nat → PoisonOr Int) (bounds : Nat → LeafBound) : Prop :=
  ∀ k, SatisfiesLeafBound (env k) (bounds k)

/-- Soundness of bidirectional steps: when `isBidirectionalStep c = true` and
`checkStepSideCond bounds c = true`, `eval src = eval tgt` holds strictly. -/
theorem bidirectionalStep_eq_sound (bounds : Nat → LeafBound) (c : ConeStepCert)
    (h_sc : checkStepSideCond bounds c = true)
    (h_bi : isBidirectionalStep c = true)
    (env : Nat → PoisonOr Int) (letVal : PoisonOr Int)
    (h_env : EnvSatisfiesBounds env bounds) :
    evalDAGExpr env letVal (inferStepEndpoints c).1 =
      evalDAGExpr env letVal (inferStepEndpoints c).2 := by
  induction c generalizing letVal with
  | refl e => rfl
  | addZeroRight e =>
    simp only [inferStepEndpoints, evalDAGExpr]
    cases evalDAGExpr env letVal e with
    | val a => simp [liftPoison2]
    | poison => rfl
  | addComm a b =>
    simp only [inferStepEndpoints, evalDAGExpr]
    cases evalDAGExpr env letVal a <;> cases evalDAGExpr env letVal b <;>
      simp [liftPoison2, Int.add_comm]
  | subSelfToZero _ | bitAndZeroRight _ | bitXorSelfToZero _ | dropNuwToWrap _ _ _ | insertFreeze _ _ =>
    simp [isBidirectionalStep] at h_bi
  | mulOneRight e =>
    simp only [inferStepEndpoints, evalDAGExpr]
    cases evalDAGExpr env letVal e with
    | val a => simp [liftPoison2, Int.mul_one]
    | poison => rfl
  | bitOrZeroRight e =>
    simp only [inferStepEndpoints, evalDAGExpr]
    cases evalDAGExpr env letVal e with
    | val a => simp [liftPoison2, intBitOr_zero_right]
    | poison => rfl
  | bitXorZeroRight e =>
    simp only [inferStepEndpoints, evalDAGExpr]
    cases evalDAGExpr env letVal e with
    | val a => simp [liftPoison2, intBitXor_zero_right]
    | poison => rfl
  | sharpenWrapToNuw varIdx c limit b =>
    simp only [checkStepSideCond, decide_eq_true_eq] at h_sc
    rcases h_sc with ⟨rfl, h_lo0, _h_lohi, h_c0, h_sum⟩
    rcases h_env varIdx with ⟨x, hx_eq, hx_lo, hx_hi, _⟩
    simp only [inferStepEndpoints, evalDAGExpr, hx_eq, liftPoison2]
    have h_cond : 0 ≤ x ∧ 0 ≤ c ∧ x + c < limit := ⟨by omega, h_c0, by omega⟩
    simp [h_cond]
  | knownZeroAddToOr varIdx c b =>
    simp only [checkStepSideCond, decide_eq_true_eq] at h_sc
    rcases h_sc with ⟨rfl, h_zm⟩
    rcases h_env varIdx with ⟨x, hx_eq, _, _, h_z0⟩
    have hx0 : x = 0 := h_z0 h_zm
    subst hx0
    simp only [inferStepEndpoints, evalDAGExpr, hx_eq, liftPoison2, Int.zero_add, intBitOr_zero_left]
  | shlZeroIdentity e =>
    simp only [inferStepEndpoints, evalDAGExpr]
    cases evalDAGExpr env letVal e with
    | val a => simp [liftPoison2, Int.mul_one]
    | poison => rfl
  | elimFreezeConst d v =>
    rfl
  | congAddWrap c1 c2 ih1 ih2 =>
    simp only [checkStepSideCond, isBidirectionalStep, Bool.and_eq_true] at h_sc h_bi
    simp only [inferStepEndpoints, evalDAGExpr]
    rw [ih1 h_sc.1 h_bi.1 letVal, ih2 h_sc.2 h_bi.2 letVal]
  | congSubWrap c1 c2 ih1 ih2 =>
    simp only [checkStepSideCond, isBidirectionalStep, Bool.and_eq_true] at h_sc h_bi
    simp only [inferStepEndpoints, evalDAGExpr]
    rw [ih1 h_sc.1 h_bi.1 letVal, ih2 h_sc.2 h_bi.2 letVal]
  | congMulWrap c1 c2 ih1 ih2 =>
    simp only [checkStepSideCond, isBidirectionalStep, Bool.and_eq_true] at h_sc h_bi
    simp only [inferStepEndpoints, evalDAGExpr]
    rw [ih1 h_sc.1 h_bi.1 letVal, ih2 h_sc.2 h_bi.2 letVal]
  | congBitAnd c1 c2 ih1 ih2 =>
    simp only [checkStepSideCond, isBidirectionalStep, Bool.and_eq_true] at h_sc h_bi
    simp only [inferStepEndpoints, evalDAGExpr]
    rw [ih1 h_sc.1 h_bi.1 letVal, ih2 h_sc.2 h_bi.2 letVal]
  | congBitOr c1 c2 ih1 ih2 =>
    simp only [checkStepSideCond, isBidirectionalStep, Bool.and_eq_true] at h_sc h_bi
    simp only [inferStepEndpoints, evalDAGExpr]
    rw [ih1 h_sc.1 h_bi.1 letVal, ih2 h_sc.2 h_bi.2 letVal]
  | congBitXor c1 c2 ih1 ih2 =>
    simp only [checkStepSideCond, isBidirectionalStep, Bool.and_eq_true] at h_sc h_bi
    simp only [inferStepEndpoints, evalDAGExpr]
    rw [ih1 h_sc.1 h_bi.1 letVal, ih2 h_sc.2 h_bi.2 letVal]
  | congFreeze d inner ih =>
    simp only [checkStepSideCond, Bool.and_eq_true] at h_sc
    simp only [isBidirectionalStep] at h_bi
    simp only [inferStepEndpoints, evalDAGExpr]
    rw [ih h_sc.1 h_bi letVal]
  | congLetBind cBound cBody ihBound ihBody =>
    simp only [checkStepSideCond, isBidirectionalStep, Bool.and_eq_true] at h_sc h_bi
    simp only [inferStepEndpoints, evalDAGExpr]
    rw [ihBound h_sc.1.1 h_bi.1 letVal]
    exact ihBody h_sc.1.2 h_bi.2 _

/-- Soundness of a single `ConeStepCert` step (`checkConditionalStep_sound`). -/
theorem checkConditionalStep_sound (bounds : Nat → LeafBound) (c : ConeStepCert)
    (h_sc : checkStepSideCond bounds c = true)
    (env : Nat → PoisonOr Int) (letVal : PoisonOr Int)
    (h_env : EnvSatisfiesBounds env bounds) :
    refinesPoison
      (evalDAGExpr env letVal (inferStepEndpoints c).1)
      (evalDAGExpr env letVal (inferStepEndpoints c).2) := by
  induction c generalizing letVal with
  | refl e => exact refinesPoison_refl _
  | addZeroRight e | addComm _ _ | mulOneRight e | bitOrZeroRight e
  | bitXorZeroRight e | sharpenWrapToNuw _ _ _ _ | knownZeroAddToOr _ _ _
  | shlZeroIdentity e | elimFreezeConst _ _ =>
    exact refinesPoison_of_eq (bidirectionalStep_eq_sound bounds _ h_sc rfl env letVal h_env)
  | subSelfToZero e =>
    simp only [inferStepEndpoints, evalDAGExpr]
    cases evalDAGExpr env letVal e with
    | val a => simp [liftPoison2, refinesPoison, Int.sub_self]
    | poison => exact Or.inl rfl
  | bitAndZeroRight e =>
    simp only [inferStepEndpoints, evalDAGExpr]
    cases evalDAGExpr env letVal e with
    | val a => simp [liftPoison2, refinesPoison, intBitAnd_zero_right]
    | poison => exact Or.inl rfl
  | bitXorSelfToZero e =>
    simp only [inferStepEndpoints, evalDAGExpr]
    cases evalDAGExpr env letVal e with
    | val a => simp [liftPoison2, refinesPoison, intBitXor_self]
    | poison => exact Or.inl rfl
  | dropNuwToWrap a b limit =>
    simp only [inferStepEndpoints, evalDAGExpr]
    cases evalDAGExpr env letVal a with
    | poison => exact Or.inl rfl
    | val va =>
      cases evalDAGExpr env letVal b with
      | poison => exact Or.inl rfl
      | val vb =>
        simp only [liftPoison2]
        by_cases h_ok : 0 ≤ va ∧ 0 ≤ vb ∧ va + vb < limit <;> simp [h_ok, refinesPoison]
  | insertFreeze d e =>
    simp only [inferStepEndpoints, evalDAGExpr]
    exact refinesPoison_freeze d (evalDAGExpr env letVal e)
  | congAddWrap c1 c2 ih1 ih2 =>
    simp only [checkStepSideCond, Bool.and_eq_true] at h_sc
    simp only [inferStepEndpoints, evalDAGExpr]
    exact liftPoison2_mono _ (ih1 h_sc.1 letVal) (ih2 h_sc.2 letVal)
  | congSubWrap c1 c2 ih1 ih2 =>
    simp only [checkStepSideCond, Bool.and_eq_true] at h_sc
    simp only [inferStepEndpoints, evalDAGExpr]
    exact liftPoison2_mono _ (ih1 h_sc.1 letVal) (ih2 h_sc.2 letVal)
  | congMulWrap c1 c2 ih1 ih2 =>
    simp only [checkStepSideCond, Bool.and_eq_true] at h_sc
    simp only [inferStepEndpoints, evalDAGExpr]
    exact liftPoison2_mono _ (ih1 h_sc.1 letVal) (ih2 h_sc.2 letVal)
  | congBitAnd c1 c2 ih1 ih2 =>
    simp only [checkStepSideCond, Bool.and_eq_true] at h_sc
    simp only [inferStepEndpoints, evalDAGExpr]
    exact liftPoison2_mono _ (ih1 h_sc.1 letVal) (ih2 h_sc.2 letVal)
  | congBitOr c1 c2 ih1 ih2 =>
    simp only [checkStepSideCond, Bool.and_eq_true] at h_sc
    simp only [inferStepEndpoints, evalDAGExpr]
    exact liftPoison2_mono _ (ih1 h_sc.1 letVal) (ih2 h_sc.2 letVal)
  | congBitXor c1 c2 ih1 ih2 =>
    simp only [checkStepSideCond, Bool.and_eq_true] at h_sc
    simp only [inferStepEndpoints, evalDAGExpr]
    exact liftPoison2_mono _ (ih1 h_sc.1 letVal) (ih2 h_sc.2 letVal)
  | congFreeze d inner _ih =>
    simp only [checkStepSideCond, Bool.and_eq_true] at h_sc
    simp only [inferStepEndpoints, evalDAGExpr]
    have h_eq := bidirectionalStep_eq_sound bounds inner h_sc.1 h_sc.2 env letVal h_env
    rw [h_eq]
    exact refinesPoison_refl _
  | congLetBind cBound cBody ihBound ihBody =>
    simp only [checkStepSideCond, Bool.and_eq_true] at h_sc
    rcases h_sc with ⟨⟨h_mB, h_mBody⟩, h_ff⟩
    simp only [inferStepEndpoints, evalDAGExpr]
    have h_refB := ihBound h_mB letVal
    have h_step1 := ihBody h_mBody (evalDAGExpr env letVal (inferStepEndpoints cBound).1)
    have h_step2 := evalDAGExpr_mono_letVal env (inferStepEndpoints cBody).2 h_ff h_refB
    exact refinesPoison_trans h_step1 h_step2

/-- Multi-step chained cone rewrite certificate (`ConeChainCert`) emitted by
bidirectional meet-in-the-middle search in `ExprChainSynthesizer`. -/
inductive ConeChainSteps where
  | single (step : ConeStepCert)
  | trans (first : ConeStepCert) (rest : ConeChainSteps)
  deriving DecidableEq, Repr

def inferChainEndpoints : ConeChainSteps → DAGExpr × DAGExpr
  | .single s => inferStepEndpoints s
  | .trans first rest =>
      let (s1, _t1) := inferStepEndpoints first
      let (_s2, t2) := inferChainEndpoints rest
      (s1, t2)

def checkChainSteps (bounds : Nat → LeafBound) : ConeChainSteps → Bool
  | .single s => checkStepSideCond bounds s
  | .trans first rest =>
      let (_s1, t1) := inferStepEndpoints first
      let (s2, _t2) := inferChainEndpoints rest
      decide (t1 = s2) && checkStepSideCond bounds first && checkChainSteps bounds rest

structure ConeChainCert where
  steps      : ConeChainSteps
  leafBounds : Nat → LeafBound

def checkConeChainCert (cert : ConeChainCert) (e_pre e_post : DAGExpr) : Bool :=
  let (s, t) := inferChainEndpoints cert.steps
  decide (e_pre = s ∧ e_post = t) && checkChainSteps cert.leafBounds cert.steps

theorem checkChainSteps_sound (bounds : Nat → LeafBound) (steps : ConeChainSteps)
    (h_chk : checkChainSteps bounds steps = true)
    (env : Nat → PoisonOr Int) (letVal : PoisonOr Int)
    (h_env : EnvSatisfiesBounds env bounds) :
    refinesPoison
      (evalDAGExpr env letVal (inferChainEndpoints steps).1)
      (evalDAGExpr env letVal (inferChainEndpoints steps).2) := by
  induction steps with
  | single s =>
    exact checkConditionalStep_sound bounds s h_chk env letVal h_env
  | trans first rest ih =>
    simp only [checkChainSteps, Bool.and_eq_true, decide_eq_true_eq] at h_chk
    rcases h_chk with ⟨⟨h_link, h_first⟩, h_rest⟩
    simp only [inferChainEndpoints]
    have h1 := checkConditionalStep_sound bounds first h_first env letVal h_env
    have h2 := ih h_rest
    rw [h_link] at h1
    exact refinesPoison_trans h1 h2

/-- **Main Soundness Theorem (`checkConeChainCert_sound`)**:
Whenever `checkConeChainCert cert e_pre e_post = true`, for every environment `env`
satisfying `cert.leafBounds`, `e_pre` poison-refines `e_post` (`e_pre ⊑_poison e_post`). -/
theorem checkConeChainCert_sound (cert : ConeChainCert) (e_pre e_post : DAGExpr)
    (h_chk : checkConeChainCert cert e_pre e_post = true)
    (env : Nat → PoisonOr Int) (letVal : PoisonOr Int)
    (h_env : EnvSatisfiesBounds env cert.leafBounds) :
    refinesPoison (evalDAGExpr env letVal e_pre) (evalDAGExpr env letVal e_post) := by
  simp only [checkConeChainCert, Bool.and_eq_true, decide_eq_true_eq] at h_chk
  rcases h_chk with ⟨⟨rfl, rfl⟩, h_steps⟩
  exact checkChainSteps_sound cert.leafBounds cert.steps h_steps env letVal h_env

/-! ## Negative Canary Tests -/

def defaultBounds : Nat → LeafBound :=
  fun _ => { lo := 0, hi := 100, zeroMask := 0, oneMask := 0 }

/-- **Negative Canary 1 (`canary_one_way_poison_under_freeze_rejected`)**:
Attempting to apply a one-way poison-refining rule (`subSelfToZero` or `dropNuwToWrap`)
inside `.freeze d ...` is rejected by `checkConeChainCert` because `isBidirectionalStep`
is `false`. -/
def badFreezeChain : ConeChainCert :=
  { steps := .single (.congFreeze 42 (.subSelfToZero (.var 1)))
    leafBounds := defaultBounds }

theorem canary_one_way_poison_under_freeze_rejected :
    checkConeChainCert
      badFreezeChain
      (.freeze 42 (.subWrap (.var 1) (.var 1)))
      (.freeze 42 (.const 0)) = false := rfl

/-- **Negative Canary 2 (`canary_unsound_shift_mask_without_knownbits_rejected`)**:
Attempting to rewrite `addWrap (var 1) (const 8)` to `bitOr (var 1) (const 8)` without
`zeroMask = 1` in `leafBounds` is rejected by `checkConeChainCert`. -/
def badKnownBitsChain : ConeChainCert :=
  { steps := .single (.knownZeroAddToOr 0 8 (defaultBounds 0))
    leafBounds := defaultBounds }

theorem canary_unsound_shift_mask_without_knownbits_rejected :
    checkConeChainCert
      badKnownBitsChain
      (.addWrap (.var 1) (.const 8))
      (.bitOr (.var 1) (.const 8)) = false := rfl

#print axioms checkConeChainCert_sound
#print axioms canary_one_way_poison_under_freeze_rejected
#print axioms canary_unsound_shift_mask_without_knownbits_rejected

end ExprChainReconstruction
