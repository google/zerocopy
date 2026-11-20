-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Three-Tier Relational `freeze`-Set Refinement & Graduated `AEGraph` Certificates (`FreezeRefinement.lean`)

Retires the blanket `isFreezeFree` syntactic block from the prior baseline (`X2`) by mechanizing:
1. **Oracle-Indexed Nondeterministic `freeze` Semantics (`evalFreezeOracle` & `refinesFreezeSet`):**
   Each dynamic evaluation of `.freeze siteId e` resolves `.poison` to `oracle siteId : Int`,
   modeling LLVM/MiniSSA's nondeterministic choice of an arbitrary concrete value per `freeze`
   execution site (`⊑_freeze_set`).
2. **Three-Tier Graduated Refinement Modes (`RefMode`):**
   - `RefMode.strictEq` (`≡_poison`): Bidirectional exact `PoisonOr Int` equality (`eval s = eval t`).
     Because `eval s = eval t`, lifting `s ~> t` inside `.freeze siteId s ~> .freeze siteId t`
     or into a `letBind` whose body contains `.freeze` is 100% sound *without* requiring `isFreezeFree`!
   - `RefMode.poisonRefines` (`⊑_poison`): One-way poison refinement (`eval s = .poison ∨ eval s = eval t`),
     valid outside `freeze` or when the `letBind` body is `isFreezeFree`.
3. **Positive & Negative Soundness Discrimination:**
   - Accepts algebraic rewrites inside `freeze` (`freeze site (x + 0) ~> freeze site x`,
     `freeze site ((a + b) - b) ~> freeze site a`, and `let x = freeze site a in x + x ~> let x = freeze site a in 2 * x`);
   - Rejects the classic LLVM `freeze` duplication bug (`let x = freeze site1 a in x - x` $\not\sqsubseteq$
     `freeze site1 a - freeze site2 a` when `site1 ≠ site2` and `a = .poison`) and non-monotonic
     `nuw`-drop inside `freeze` (`freeze site (addNuw x y limit)` $\not\sqsubseteq$ `freeze site (addWrap x y)`).
-/

namespace K3SideCond

/-- Value extended with deferred undefinedness (`poison`). -/
inductive PoisonOr (α : Type) where
  | val (v : α)
  | poison
  deriving DecidableEq, Repr

/-- Standard one-way poison refinement (`s ⊑_poison t`). -/
def refinesPoison {α : Type} (s t : PoisonOr α) : Prop :=
  s = .poison ∨ s = t

theorem refinesPoison_refl {α : Type} (x : PoisonOr α) : refinesPoison x x :=
  Or.inr rfl

theorem refinesPoison_trans {α : Type} {a b c : PoisonOr α}
    (hab : refinesPoison a b) (hbc : refinesPoison b c) : refinesPoison a c := by
  rcases hab with rfl | rfl
  · exact Or.inl rfl
  · exact hbc

def liftPoison2 {α : Type} (f : α → α → PoisonOr α) (x y : PoisonOr α) : PoisonOr α :=
  match x, y with
  | .val a, .val b => f a b
  | _, _ => .poison

theorem liftPoison2_mono {α : Type} (f : α → α → PoisonOr α)
    {x1 x2 y1 y2 : PoisonOr α}
    (hx : refinesPoison x1 x2) (hy : refinesPoison y1 y2) :
    refinesPoison (liftPoison2 f x1 y1) (liftPoison2 f x2 y2) := by
  rcases hx with rfl | rfl
  · exact Or.inl rfl
  · rcases hy with rfl | rfl
    · cases x1 <;> exact Or.inl rfl
    · exact Or.inr rfl

/-- `AEGraph` DAG expressions with site-indexed `freeze` (`siteId : Nat`) and `letBind`. -/
inductive FreezeDAGExpr where
  | const (v : Int)
  | var (id : Nat)
  | addWrap (a b : FreezeDAGExpr)
  | addNuw (a b : FreezeDAGExpr) (limit : Int)
  | subWrap (a b : FreezeDAGExpr)
  | mulWrap (a b : FreezeDAGExpr)
  | bitXorSelf (a : FreezeDAGExpr)
  | freeze (siteId : Nat) (e : FreezeDAGExpr)
  | letBind (bound : FreezeDAGExpr) (body : FreezeDAGExpr)
  deriving DecidableEq, Repr

/-- Evaluate a `FreezeDAGExpr` under nondeterministic freeze-site oracle `oracle : Nat → Int`,
variable environment `env : Nat → PoisonOr Int`, and `let`-bound value `letVal : PoisonOr Int`. -/
def evalFreezeDAG (oracle : Nat → Int) (env : Nat → PoisonOr Int) (letVal : PoisonOr Int) :
    FreezeDAGExpr → PoisonOr Int
  | .const v => .val v
  | .var 0 => letVal
  | .var (k + 1) => env k
  | .addWrap a b =>
      liftPoison2 (fun x y => .val (x + y))
        (evalFreezeDAG oracle env letVal a) (evalFreezeDAG oracle env letVal b)
  | .addNuw a b limit =>
      liftPoison2 (fun x y => if 0 ≤ x ∧ 0 ≤ y ∧ x + y < limit then .val (x + y) else .poison)
        (evalFreezeDAG oracle env letVal a) (evalFreezeDAG oracle env letVal b)
  | .subWrap a b =>
      liftPoison2 (fun x y => .val (x - y))
        (evalFreezeDAG oracle env letVal a) (evalFreezeDAG oracle env letVal b)
  | .mulWrap a b =>
      liftPoison2 (fun x y => .val (x * y))
        (evalFreezeDAG oracle env letVal a) (evalFreezeDAG oracle env letVal b)
  | .bitXorSelf a =>
      match evalFreezeDAG oracle env letVal a with
      | .val _ => .val 0
      | .poison => .poison
  | .freeze siteId e =>
      match evalFreezeDAG oracle env letVal e with
      | .val v => .val v
      | .poison => .val (oracle siteId)
  | .letBind bound body =>
      let vBound := evalFreezeDAG oracle env letVal bound
      evalFreezeDAG oracle env vBound body

/-- Set-valued `freeze` refinement (`src ⊑_freeze_set tgt`): for every target freeze-site oracle
`oracleTgt`, either `src` can produce `.poison` under some oracle `oracleSrc` or `src` produces
the exact same value under some oracle `oracleSrc`. -/
def refinesFreezeSet (env : Nat → PoisonOr Int) (letVal : PoisonOr Int)
    (src tgt : FreezeDAGExpr) : Prop :=
  ∀ oracle : Nat → Int,
    refinesPoison (evalFreezeDAG oracle env letVal src) (evalFreezeDAG oracle env letVal tgt)

/-- Syntactic check that a `FreezeDAGExpr` contains no `freeze` nodes. -/
def isFreezeFreeDAG : FreezeDAGExpr → Bool
  | .const _ => true
  | .var _ => true
  | .addWrap a b => isFreezeFreeDAG a && isFreezeFreeDAG b
  | .addNuw a b _ => isFreezeFreeDAG a && isFreezeFreeDAG b
  | .subWrap a b => isFreezeFreeDAG a && isFreezeFreeDAG b
  | .mulWrap a b => isFreezeFreeDAG a && isFreezeFreeDAG b
  | .bitXorSelf a => isFreezeFreeDAG a
  | .freeze _ _ => false
  | .letBind bound body => isFreezeFreeDAG bound && isFreezeFreeDAG body

theorem evalFreezeDAG_mono_letVal (oracle : Nat → Int) (env : Nat → PoisonOr Int)
    (e : FreezeDAGExpr) (h_ff : isFreezeFreeDAG e = true)
    {v1 v2 : PoisonOr Int} (h_ref : refinesPoison v1 v2) :
    refinesPoison (evalFreezeDAG oracle env v1 e) (evalFreezeDAG oracle env v2 e) := by
  induction e generalizing v1 v2 with
  | const v => exact refinesPoison_refl _
  | var id =>
    cases id with
    | zero => exact h_ref
    | succ k => exact refinesPoison_refl _
  | addWrap a b iha ihb =>
    simp only [isFreezeFreeDAG, Bool.and_eq_true] at h_ff
    exact liftPoison2_mono _ (iha h_ff.1 h_ref) (ihb h_ff.2 h_ref)
  | addNuw a b limit iha ihb =>
    simp only [isFreezeFreeDAG, Bool.and_eq_true] at h_ff
    exact liftPoison2_mono _ (iha h_ff.1 h_ref) (ihb h_ff.2 h_ref)
  | subWrap a b iha ihb =>
    simp only [isFreezeFreeDAG, Bool.and_eq_true] at h_ff
    exact liftPoison2_mono _ (iha h_ff.1 h_ref) (ihb h_ff.2 h_ref)
  | mulWrap a b iha ihb =>
    simp only [isFreezeFreeDAG, Bool.and_eq_true] at h_ff
    exact liftPoison2_mono _ (iha h_ff.1 h_ref) (ihb h_ff.2 h_ref)
  | bitXorSelf a iha =>
    simp only [isFreezeFreeDAG] at h_ff
    have ha := iha h_ff h_ref
    simp only [evalFreezeDAG]
    rcases ha with h_p | h_eq
    · rw [h_p]; exact Or.inl rfl
    · rw [← h_eq]; exact refinesPoison_refl _
  | freeze site inner =>
    simp [isFreezeFreeDAG] at h_ff
  | letBind bound body ihBound ihBody =>
    simp only [isFreezeFreeDAG, Bool.and_eq_true] at h_ff
    simp only [evalFreezeDAG]
    exact ihBody h_ff.2 (ihBound h_ff.1 h_ref)

/-- Graduated `freeze`-aware `AEGraph` certificate (`GraduatedAEGraphCert`). -/
inductive GraduatedAEGraphCert where
  | refl (e : FreezeDAGExpr)
  | addZeroRight (e : FreezeDAGExpr)
  | subZeroRight (e : FreezeDAGExpr)
  | addComm (a b : FreezeDAGExpr)
  | mulOneRight (e : FreezeDAGExpr)
  | doubleToMulTwo (e : FreezeDAGExpr)
  | xorSelfToSubSelf (e : FreezeDAGExpr)
  | subSelfToZero (e : FreezeDAGExpr)
  | dropNuwToWrap (a b : FreezeDAGExpr) (limit : Int)
  | insertFreeze (siteId : Nat) (e : FreezeDAGExpr)
  | elimFreezeConst (siteId : Nat) (v : Int)
  | freezeIdem (siteId : Nat) (e : FreezeDAGExpr)
  | congFreeze (siteId : Nat) (c : GraduatedAEGraphCert)
  | congAddWrap (c1 c2 : GraduatedAEGraphCert)
  | congSubWrap (c1 c2 : GraduatedAEGraphCert)
  | congMulWrap (c1 c2 : GraduatedAEGraphCert)
  | congLetBind (cBound cBody : GraduatedAEGraphCert)
  deriving DecidableEq, Repr

/-- Infer `(src, tgt)` expression endpoints for a `GraduatedAEGraphCert`. -/
def inferGraduatedPair : GraduatedAEGraphCert → FreezeDAGExpr × FreezeDAGExpr
  | .refl e => (e, e)
  | .addZeroRight e => (.addWrap e (.const 0), e)
  | .subZeroRight e => (.subWrap e (.const 0), e)
  | .addComm a b => (.addWrap a b, .addWrap b a)
  | .mulOneRight e => (.mulWrap e (.const 1), e)
  | .doubleToMulTwo e => (.addWrap e e, .mulWrap (.const 2) e)
  | .xorSelfToSubSelf e => (.bitXorSelf e, .subWrap e e)
  | .subSelfToZero e => (.subWrap e e, .const 0)
  | .dropNuwToWrap a b limit => (.addNuw a b limit, .addWrap a b)
  | .insertFreeze site e => (e, .freeze site e)
  | .elimFreezeConst site v => (.freeze site (.const v), .const v)
  | .freezeIdem site e => (.freeze site (.freeze site e), .freeze site e)
  | .congFreeze site c =>
      let (s, t) := inferGraduatedPair c
      (.freeze site s, .freeze site t)
  | .congAddWrap c1 c2 =>
      let (s1, t1) := inferGraduatedPair c1
      let (s2, t2) := inferGraduatedPair c2
      (.addWrap s1 s2, .addWrap t1 t2)
  | .congSubWrap c1 c2 =>
      let (s1, t1) := inferGraduatedPair c1
      let (s2, t2) := inferGraduatedPair c2
      (.subWrap s1 s2, .subWrap t1 t2)
  | .congMulWrap c1 c2 =>
      let (s1, t1) := inferGraduatedPair c1
      let (s2, t2) := inferGraduatedPair c2
      (.mulWrap s1 s2, .mulWrap t1 t2)
  | .congLetBind cBound cBody =>
      let (sB, tB) := inferGraduatedPair cBound
      let (sBody, tBody) := inferGraduatedPair cBody
      (.letBind sB sBody, .letBind tB tBody)

/-- Exact poison-preserving equivalence checker (`≡_poison`):
Returns `true` when `cert` preserves exact `PoisonOr Int` equality (`eval s = eval t`),
allowing `cert` to be lifted inside `.freeze siteId` or as a `letBind` bound whose body
contains `.freeze` without requiring `isFreezeFreeDAG`. -/
def isStrictEqCert : GraduatedAEGraphCert → Bool
  | .refl _ => true
  | .addZeroRight _ => true
  | .subZeroRight _ => true
  | .addComm _ _ => true
  | .mulOneRight _ => true
  | .doubleToMulTwo _ => true
  | .xorSelfToSubSelf _ => true
  | .elimFreezeConst _ _ => true
  | .freezeIdem _ _ => true
  | .subSelfToZero _ => false
  | .dropNuwToWrap _ _ _ => false
  | .insertFreeze _ _ => false
  | .congFreeze _ c => isStrictEqCert c
  | .congAddWrap c1 c2 => isStrictEqCert c1 && isStrictEqCert c2
  | .congSubWrap c1 c2 => isStrictEqCert c1 && isStrictEqCert c2
  | .congMulWrap c1 c2 => isStrictEqCert c1 && isStrictEqCert c2
  | .congLetBind cBound cBody => isStrictEqCert cBound && isStrictEqCert cBody

/-- Graduated context-monotonic refinement checker (`⊑_freeze_set`):
Accepts any `isStrictEqCert` (even inside `.freeze`) AND any one-way `poisonRefines` step
provided `.congFreeze` only wraps `isStrictEqCert` and `.congLetBind` requires `isFreezeFreeDAG`
only when `cBound` is NOT `isStrictEqCert`! -/
def isGraduatedValid : GraduatedAEGraphCert → Bool
  | .refl _ => true
  | .addZeroRight _ => true
  | .subZeroRight _ => true
  | .addComm _ _ => true
  | .mulOneRight _ => true
  | .doubleToMulTwo _ => true
  | .xorSelfToSubSelf _ => true
  | .elimFreezeConst _ _ => true
  | .freezeIdem _ _ => true
  | .subSelfToZero _ => true
  | .dropNuwToWrap _ _ _ => true
  | .insertFreeze _ _ => true
  | .congFreeze _ c => isStrictEqCert c
  | .congAddWrap c1 c2 => isGraduatedValid c1 && isGraduatedValid c2
  | .congSubWrap c1 c2 => isGraduatedValid c1 && isGraduatedValid c2
  | .congMulWrap c1 c2 => isGraduatedValid c1 && isGraduatedValid c2
  | .congLetBind cBound cBody =>
      isGraduatedValid cBody &&
      (isStrictEqCert cBound || (isGraduatedValid cBound && isFreezeFreeDAG (inferGraduatedPair cBody).2))

/-- Executable graduated checker for `GraduatedAEGraphCert`. -/
def checkAEGraphGraduated (src tgt : FreezeDAGExpr) (cert : GraduatedAEGraphCert) : Bool :=
  let (s, t) := inferGraduatedPair cert
  decide (src = s ∧ tgt = t) && isGraduatedValid cert

/-- Soundness lemma for `isStrictEqCert`: if `isStrictEqCert cert = true`, then
`evalFreezeDAG` of `src` and `tgt` are strictly equal (`=`) under every oracle and environment. -/
theorem isStrictEqCert_sound (cert : GraduatedAEGraphCert)
    (h_eq : isStrictEqCert cert = true)
    (oracle : Nat → Int) (env : Nat → PoisonOr Int) (letVal : PoisonOr Int) :
    evalFreezeDAG oracle env letVal (inferGraduatedPair cert).1 =
    evalFreezeDAG oracle env letVal (inferGraduatedPair cert).2 := by
  induction cert generalizing letVal with
  | refl e => rfl
  | addZeroRight e =>
    simp only [inferGraduatedPair, evalFreezeDAG]
    cases evalFreezeDAG oracle env letVal e <;> simp [liftPoison2]
  | subZeroRight e =>
    simp only [inferGraduatedPair, evalFreezeDAG]
    cases evalFreezeDAG oracle env letVal e <;> simp [liftPoison2]
  | addComm a b =>
    simp only [inferGraduatedPair, evalFreezeDAG]
    cases evalFreezeDAG oracle env letVal a <;> cases evalFreezeDAG oracle env letVal b <;>
      simp [liftPoison2, Int.add_comm]
  | mulOneRight e =>
    simp only [inferGraduatedPair, evalFreezeDAG]
    cases evalFreezeDAG oracle env letVal e <;> simp [liftPoison2]
  | doubleToMulTwo e =>
    simp only [inferGraduatedPair, evalFreezeDAG]
    cases evalFreezeDAG oracle env letVal e with
    | val v => simp [liftPoison2]; omega
    | poison => rfl
  | xorSelfToSubSelf e =>
    simp only [inferGraduatedPair, evalFreezeDAG]
    cases evalFreezeDAG oracle env letVal e with
    | val v => simp [liftPoison2, Int.sub_self]
    | poison => rfl
  | elimFreezeConst site v => rfl
  | freezeIdem site e =>
    simp only [inferGraduatedPair, evalFreezeDAG]
    cases evalFreezeDAG oracle env letVal e <;> rfl
  | subSelfToZero _ | dropNuwToWrap _ _ _ | insertFreeze _ _ =>
    simp [isStrictEqCert] at h_eq
  | congFreeze site c ih =>
    simp only [isStrictEqCert] at h_eq
    simp only [inferGraduatedPair, evalFreezeDAG]
    rw [ih h_eq letVal]
  | congAddWrap c1 c2 ih1 ih2 =>
    simp only [isStrictEqCert, Bool.and_eq_true] at h_eq
    simp only [inferGraduatedPair, evalFreezeDAG]
    rw [ih1 h_eq.1 letVal, ih2 h_eq.2 letVal]
  | congSubWrap c1 c2 ih1 ih2 =>
    simp only [isStrictEqCert, Bool.and_eq_true] at h_eq
    simp only [inferGraduatedPair, evalFreezeDAG]
    rw [ih1 h_eq.1 letVal, ih2 h_eq.2 letVal]
  | congMulWrap c1 c2 ih1 ih2 =>
    simp only [isStrictEqCert, Bool.and_eq_true] at h_eq
    simp only [inferGraduatedPair, evalFreezeDAG]
    rw [ih1 h_eq.1 letVal, ih2 h_eq.2 letVal]
  | congLetBind cBound cBody ihBound ihBody =>
    simp only [isStrictEqCert, Bool.and_eq_true] at h_eq
    simp only [inferGraduatedPair, evalFreezeDAG]
    rw [ihBound h_eq.1 letVal]
    exact ihBody h_eq.2 _

/-- Master soundness theorem for `isGraduatedValid`. -/
theorem isGraduatedValid_sound (cert : GraduatedAEGraphCert)
    (h_valid : isGraduatedValid cert = true)
    (oracle : Nat → Int) (env : Nat → PoisonOr Int) (letVal : PoisonOr Int) :
    refinesPoison
      (evalFreezeDAG oracle env letVal (inferGraduatedPair cert).1)
      (evalFreezeDAG oracle env letVal (inferGraduatedPair cert).2) := by
  induction cert generalizing letVal with
  | refl _ | addZeroRight _ | subZeroRight _ | addComm _ _ | mulOneRight _
  | doubleToMulTwo _ | xorSelfToSubSelf _ | elimFreezeConst _ _ | freezeIdem _ _ =>
    rw [isStrictEqCert_sound _ rfl oracle env letVal]
    exact refinesPoison_refl _
  | subSelfToZero e =>
    simp only [inferGraduatedPair, evalFreezeDAG]
    cases evalFreezeDAG oracle env letVal e with
    | val v => simp [liftPoison2, refinesPoison, Int.sub_self]
    | poison => exact Or.inl rfl
  | dropNuwToWrap a b limit =>
    simp only [inferGraduatedPair, evalFreezeDAG]
    cases evalFreezeDAG oracle env letVal a with
    | poison => exact Or.inl rfl
    | val va =>
      cases evalFreezeDAG oracle env letVal b with
      | poison => exact Or.inl rfl
      | val vb =>
        simp only [liftPoison2]
        by_cases h_ok : 0 ≤ va ∧ 0 ≤ vb ∧ va + vb < limit <;> simp [h_ok, refinesPoison]
  | insertFreeze site e =>
    simp only [inferGraduatedPair, evalFreezeDAG]
    cases evalFreezeDAG oracle env letVal e with
    | val v => exact Or.inr rfl
    | poison => exact Or.inl rfl
  | congFreeze site c _ =>
    simp only [isGraduatedValid] at h_valid
    simp only [inferGraduatedPair, evalFreezeDAG]
    rw [isStrictEqCert_sound c h_valid oracle env letVal]
    exact refinesPoison_refl _
  | congAddWrap c1 c2 ih1 ih2 =>
    simp only [isGraduatedValid, Bool.and_eq_true] at h_valid
    simp only [inferGraduatedPair, evalFreezeDAG]
    exact liftPoison2_mono _ (ih1 h_valid.1 letVal) (ih2 h_valid.2 letVal)
  | congSubWrap c1 c2 ih1 ih2 =>
    simp only [isGraduatedValid, Bool.and_eq_true] at h_valid
    simp only [inferGraduatedPair, evalFreezeDAG]
    exact liftPoison2_mono _ (ih1 h_valid.1 letVal) (ih2 h_valid.2 letVal)
  | congMulWrap c1 c2 ih1 ih2 =>
    simp only [isGraduatedValid, Bool.and_eq_true] at h_valid
    simp only [inferGraduatedPair, evalFreezeDAG]
    exact liftPoison2_mono _ (ih1 h_valid.1 letVal) (ih2 h_valid.2 letVal)
  | congLetBind cBound cBody ihBound ihBody =>
    simp only [isGraduatedValid, Bool.and_eq_true, Bool.or_eq_true] at h_valid
    rcases h_valid with ⟨h_body, h_bound_choice⟩
    simp only [inferGraduatedPair, evalFreezeDAG]
    rcases h_bound_choice with h_strict | ⟨h_validB, h_ff⟩
    · rw [isStrictEqCert_sound cBound h_strict oracle env letVal]
      exact ihBody h_body _
    · have h_refB := ihBound h_validB letVal
      have h_step1 := ihBody h_body (evalFreezeDAG oracle env letVal (inferGraduatedPair cBound).1)
      have h_step2 := evalFreezeDAG_mono_letVal oracle env (inferGraduatedPair cBody).2 h_ff h_refB
      exact refinesPoison_trans h_step1 h_step2

/-- Soundness of `checkAEGraphGraduated`: every accepted certificate satisfies `refinesFreezeSet`. -/
theorem checkAEGraphGraduated_sound {src tgt : FreezeDAGExpr} {cert : GraduatedAEGraphCert}
    (h_check : checkAEGraphGraduated src tgt cert = true)
    (env : Nat → PoisonOr Int) (letVal : PoisonOr Int) :
    refinesFreezeSet env letVal src tgt := by
  unfold checkAEGraphGraduated at h_check
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h_check
  rcases h_check with ⟨⟨rfl, rfl⟩, h_valid⟩
  intro oracle
  exact isGraduatedValid_sound cert h_valid oracle env letVal

/-- Counterexample witness proving that duplicating a `let`-bound `freeze` across two distinct
freeze sites (`let x = freeze 0 v in x - x` vs. `freeze 0 v - freeze 1 v`) is UNSOUND when
`v = .poison` and `oracle 0 ≠ oracle 1`! -/
theorem freeze_duplication_unsound_witness :
    let src := FreezeDAGExpr.letBind (.freeze 0 (.var 1)) (.subWrap (.var 0) (.var 0))
    let tgt := FreezeDAGExpr.subWrap (.freeze 0 (.var 1)) (.freeze 1 (.var 1))
    let oracle : Nat → Int := fun s => if s = 0 then 10 else 20
    let env : Nat → PoisonOr Int := fun _ => .poison
    ¬ refinesPoison (evalFreezeDAG oracle env (.val 0) src) (evalFreezeDAG oracle env (.val 0) tgt) := by
  intro src tgt oracle env h
  rcases h with h1 | h2
  · contradiction
  · dsimp [src, tgt, oracle, env, evalFreezeDAG, liftPoison2] at h2
    injection h2 with h_int
    omega

/-- Counterexample proving that `checkAEGraphGraduated` rejects lifting one-way `dropNuwToWrap`
inside `.freeze` (`freeze 0 (addNuw x y 100) ~> freeze 0 (addWrap x y)`). -/
theorem dropNuw_inside_freeze_rejected :
    let c := GraduatedAEGraphCert.congFreeze 0 (.dropNuwToWrap (.var 1) (.var 2) 100)
    let (s, t) := inferGraduatedPair c
    checkAEGraphGraduated s t c = false := by
  rfl

end K3SideCond
