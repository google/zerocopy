import ToyProphecy.Sim.Basic

/-!
# Proof infrastructure: the checker gets stuck exactly where the semantics do

Auxiliary lemmas used only inside proofs of the main statements.
-/

namespace Toy.Prophecy
namespace Sim

open CState

/-! ## Operations -/

/-- Why a check of a basic operation got stuck. -/
def OpStuck (L : Bool) (c : CState) : Op → Prop
  | .assign _ e => L = false ∨ ExprStuck L c e
  | .borrow _ _ => L = false
  | .borrowSel _ e _ _ => L = false ∨ ExprStuck L c e
  | .reborrow _ r => c.status r = .unborn
  | .write r e => ExprStuck L c e ∨ c.status r = .unborn
  | .endBorrow r => c.status r = .unborn

theorem checkOp_of_stuck {L : Bool} {c : CState} (h : c.stuck = true) (o : Op) :
    checkOp L c o = c := by simp [checkOp, h]

theorem addV_ite_status (c : CState) (b : Bool) (v : Violation) :
    (if b = true then c.addV v else c).status = c.status := by split <;> rfl
theorem addV_ite_lent (c : CState) (b : Bool) (v : Violation) :
    (if b = true then c.addV v else c).lent = c.lent := by split <;> rfl
theorem addV_ite_lender (c : CState) (b : Bool) (v : Violation) :
    (if b = true then c.addV v else c).lender = c.lender := by split <;> rfl
theorem addV_ite_stuck (c : CState) (b : Bool) (v : Violation) :
    (if b = true then c.addV v else c).stuck = c.stuck := by split <;> rfl

theorem checkOp_stuck {L : Bool} {c : CState} {o : Op} (hc : c.stuck = false)
    (h : (checkOp L c o).stuck = true) : OpStuck L c o := by
  cases o with
  | assign x e =>
      cases L
      · exact Or.inl rfl
      · right
        simp only [checkOp, hc, Bool.false_eq_true, ↓reduceIte, Bool.not_true] at h
        rw [addV_ite_stuck] at h
        exact checkExpr_stuck true c e hc h
  | borrow r x =>
      cases L
      · rfl
      · simp only [checkOp, hc, Bool.false_eq_true, ↓reduceIte, Bool.not_true] at h
        rw [bindRef_stuck, addV_ite_stuck] at h
        simp [hc] at h
  | borrowSel r e x y =>
      cases L
      · exact Or.inl rfl
      · right
        simp only [checkOp, hc, Bool.false_eq_true, ↓reduceIte, Bool.not_true] at h
        rw [bindRef_stuck, addV_ite_stuck] at h
        exact checkExpr_stuck true c e hc h
  | reborrow t r =>
      show c.status r = .unborn
      cases hr : c.status r
      · rfl
      all_goals
        simp [checkOp, hc, CState.useRef, hr, CState.addV, bindRef_stuck] at h
  | write r e =>
      show ExprStuck L c e ∨ c.status r = .unborn
      by_cases hs : (checkExpr L c e).stuck = true
      · exact Or.inl (checkExpr_stuck L c e hc hs)
      · right
        have hs' : (checkExpr L c e).stuck = false := by simpa using hs
        simp only [checkOp, hc, hs', Bool.false_eq_true, ↓reduceIte] at h
        rw [useRef_stuck_iff, hs'] at h
        simpa [(checkExpr_shape L c e).status] using h
  | endBorrow r =>
      show c.status r = .unborn
      cases hr : c.status r
      · rfl
      all_goals
        simp [checkOp, hc, CState.useRef, hr, CState.addV, release_stuck] at h

/-- After a non-stuck checker step, the `unborn` names are the previously
`unborn` names other than the one the operation binds. -/
theorem checkOp_status_unborn {L : Bool} {c : CState} {o : Op}
    (h : (checkOp L c o).stuck = false) (k : RefVar) :
    (checkOp L c o).status k = .unborn ↔ (c.status k = .unborn ∧ o.binds ≠ some k) := by
  have hc : c.stuck = false := by
    cases hc : c.stuck
    · rfl
    · rw [checkOp_of_stuck hc] at h; simp [hc] at h
  cases o with
  | assign x e =>
      cases L
      · simp [checkOp, hc, CState.setStuck] at h
      · simp only [checkOp, hc, Bool.false_eq_true, ↓reduceIte, Bool.not_true]
        rw [addV_ite_status, (checkExpr_shape true c e).status]
        simp [Op.binds]
  | borrow r x =>
      cases L
      · simp [checkOp, hc, CState.setStuck] at h
      · simp only [checkOp, hc, Bool.false_eq_true, ↓reduceIte, Bool.not_true]
        simp only [upd_apply, bindRef_status, addV_ite_status, Op.binds]
        by_cases hk : k = r
        · subst hk; simp
        · simp [hk, Ne.symm hk]
  | borrowSel r e x y =>
      cases L
      · simp [checkOp, hc, CState.setStuck] at h
      · simp only [checkOp, hc, Bool.false_eq_true, ↓reduceIte, Bool.not_true]
        simp only [upd_apply, bindRef_status, addV_ite_status, (checkExpr_shape true c e).status,
          Op.binds]
        by_cases hk : k = r
        · subst hk; simp
        · simp [hk, Ne.symm hk]
  | reborrow t r =>
      have hr : c.status r ≠ .unborn := by
        intro hr
        simp [checkOp, hc, CState.useRef, hr, CState.setStuck] at h
      have hs : (c.useRef r).stuck = false := by rw [useRef_stuck_iff]; simp [hc, hr]
      simp only [checkOp, hc, hs, Bool.false_eq_true, ↓reduceIte]
      simp only [upd_apply, bindRef_status, (useRef_shape c r).status, Op.binds]
      by_cases hkt : k = t
      · subst hkt; simp
      · simp only [hkt, ite_false]
        split
        · simp [Ne.symm hkt]
        · simp only [upd_apply]
          by_cases hkr : k = r
          · subst hkr; simp [hr, Ne.symm hkt]
          · simp [hkr, Ne.symm hkt]
  | write r e =>
      simp only [checkOp, hc, Bool.false_eq_true, ↓reduceIte]
      have := (checkExpr_shape L c e).status
      split
      · simp [this, Op.binds]
      · simp [(useRef_shape _ r).status, this, Op.binds]
  | endBorrow r =>
      have hr : c.status r ≠ .unborn := by
        intro hr
        simp [checkOp, hc, CState.useRef, hr, CState.setStuck] at h
      have hs : (c.useRef r).stuck = false := by rw [useRef_stuck_iff]; simp [hc, hr]
      simp only [checkOp, hc, hs, Bool.false_eq_true, ↓reduceIte]
      split
      · simp [(useRef_shape c r).status, Op.binds]
      · simp only [upd_apply, Op.binds]
        split
        · subst_vars; simp [hr]
        · rw [release_status_unborn, (useRef_shape c r).status]; simp

theorem checkOp_viol (L : Bool) (c : CState) (o : Op) :
    ∃ l, (checkOp L c o).viol = c.viol ++ l ∧
      ∀ v ∈ l, v ≠ .unendedAtExit ∧ (L = false → v ≠ .lentAccess) := by
  by_cases hc : c.stuck = true
  · exact ⟨[], by simp [checkOp_of_stuck hc], by simp⟩
  have hc' : c.stuck = false := by simpa using hc
  have hE : ∀ (c : CState) e, ∃ l, (checkExpr L c e).viol = c.viol ++ l ∧
      ∀ v ∈ l, v ≠ .unendedAtExit ∧ (L = false → v ≠ .lentAccess) := by
    intro c e
    obtain ⟨l, hl, hv⟩ := checkExpr_viol L c e
    refine ⟨l, hl, fun v hv' => ?_⟩
    rcases hv v hv' with ⟨rfl, hL⟩ | rfl | rfl <;> simp_all
  have hU : ∀ (c : CState) r, ∃ l, (c.useRef r).viol = c.viol ++ l ∧
      ∀ v ∈ l, v ≠ .unendedAtExit ∧ (L = false → v ≠ .lentAccess) := by
    intro c r
    obtain ⟨l, hl, hv⟩ := useRef_viol c r
    refine ⟨l, hl, fun v hv' => ?_⟩
    rcases hv v hv' with rfl | rfl <;> simp
  have hB : ∀ (c : CState) t, ∃ l, (c.bindRef t).viol = c.viol ++ l ∧
      ∀ v ∈ l, v ≠ .unendedAtExit ∧ (L = false → v ≠ .lentAccess) := by
    intro c t
    obtain ⟨l, hl, hv⟩ := bindRef_viol c t
    refine ⟨l, hl, fun v hv' => ?_⟩
    rcases hv v hv' with rfl; simp
  cases o with
  | assign x e =>
      simp only [checkOp, hc', Bool.false_eq_true, ↓reduceIte]
      cases L
      · exact ⟨[], by simp [CState.setStuck], by simp⟩
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        obtain ⟨l, hl, hv⟩ := hE c e
        split
        · exact ⟨l ++ [.lentAccess], by simp [CState.addV, hl], by
            intro v hv'; rcases List.mem_append.mp hv' with h | h
            · exact hv v h
            · simp at h; subst h; simp⟩
        · exact ⟨l, hl, hv⟩
  | borrow r x =>
      simp only [checkOp, hc', Bool.false_eq_true, ↓reduceIte]
      cases L
      · exact ⟨[], by simp [CState.setStuck], by simp⟩
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        split
        · obtain ⟨l, hl, hv⟩ := hB (c.addV .lentAccess) r
          refine ⟨.lentAccess :: l, by simp only [hl]; simp [CState.addV], ?_⟩
          intro v hv'; rcases List.mem_cons.mp hv' with h | h
          · subst h; simp
          · exact hv v h
        · obtain ⟨l, hl, hv⟩ := hB c r
          exact ⟨l, by simp only [hl] <;> simp, hv⟩
  | borrowSel r e x y =>
      simp only [checkOp, hc', Bool.false_eq_true, ↓reduceIte]
      cases L
      · exact ⟨[], by simp [CState.setStuck], by simp⟩
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        obtain ⟨l, hl, hv⟩ := hE c e
        split
        · obtain ⟨l2, hl2, hv2⟩ := hB ((checkExpr true c e).addV .lentAccess) r
          refine ⟨l ++ .lentAccess :: l2, by simp only [hl2]; simp [hl, CState.addV], ?_⟩
          intro v hv'; rcases List.mem_append.mp hv' with h | h
          · exact hv v h
          · rcases List.mem_cons.mp h with h | h
            · subst h; simp
            · exact hv2 v h
        · obtain ⟨l2, hl2, hv2⟩ := hB (checkExpr true c e) r
          refine ⟨l ++ l2, by simp only [hl2]; simp [hl], ?_⟩
          intro v hv'; rcases List.mem_append.mp hv' with h | h
          · exact hv v h
          · exact hv2 v h
  | reborrow t r =>
      simp only [checkOp, hc', Bool.false_eq_true, ↓reduceIte]
      obtain ⟨l, hl, hv⟩ := hU c r
      split
      · exact ⟨l, hl, hv⟩
      · obtain ⟨l2, hl2, hv2⟩ := hB (c.useRef r) t
        refine ⟨l ++ l2, by simp only [hl2]; simp [hl], ?_⟩
        intro v hv'; rcases List.mem_append.mp hv' with h | h
        · exact hv v h
        · exact hv2 v h
  | write r e =>
      simp only [checkOp, hc', Bool.false_eq_true, ↓reduceIte]
      obtain ⟨l, hl, hv⟩ := hE c e
      split
      · exact ⟨l, hl, hv⟩
      · obtain ⟨l2, hl2, hv2⟩ := hU (checkExpr L c e) r
        refine ⟨l ++ l2, by simp only [hl2]; simp [hl], ?_⟩
        intro v hv'; rcases List.mem_append.mp hv' with h | h
        · exact hv v h
        · exact hv2 v h
  | endBorrow r =>
      simp only [checkOp, hc', Bool.false_eq_true, ↓reduceIte]
      obtain ⟨l, hl, hv⟩ := hU c r
      split
      · exact ⟨l, hl, hv⟩
      · split
        · exact ⟨l, hl, hv⟩
        · exact ⟨l, by simp [release_viol, hl], hv⟩

theorem checkOps_viol (L : Bool) : ∀ (c : CState) (os : List Op),
    ∃ l, (checkOps L c os).viol = c.viol ++ l ∧
      ∀ v ∈ l, v ≠ .unendedAtExit ∧ (L = false → v ≠ .lentAccess)
  | c, [] => ⟨[], by simp [checkOps], by simp⟩
  | c, o :: os => by
      obtain ⟨l1, h1, hv1⟩ := checkOp_viol L c o
      obtain ⟨l2, h2, hv2⟩ := checkOps_viol L (checkOp L c o) os
      refine ⟨l1 ++ l2, by simp [checkOps, h2, h1], ?_⟩
      intro v hv; rcases List.mem_append.mp hv with h | h
      · exact hv1 v h
      · exact hv2 v h

theorem checkOps_of_stuck' {L : Bool} {c : CState} (h : c.stuck = true) :
    ∀ os, checkOps L c os = c
  | [] => rfl
  | o :: os => by simp only [checkOps, checkOp_of_stuck h]; exact checkOps_of_stuck' h os

theorem checkCallee_viol (f : Callee) :
    ∀ v ∈ (checkCallee f).viol, v ≠ .unendedAtExit ∧ v ≠ .lentAccess := by
  obtain ⟨l, hl, hv⟩ := checkOps_viol false CState.calleeInit f.body
  have hl' : (checkOps false CState.calleeInit f.body).viol = l := by
    simpa [CState.calleeInit] using hl
  intro v hv'
  simp only [checkCallee] at hv'
  split at hv'
  · rw [hl'] at hv'; exact ⟨(hv v hv').1, (hv v hv').2 rfl⟩
  · obtain ⟨l2, hl2, hv2⟩ := useRef_viol (checkOps false CState.calleeInit f.body) f.ret
    rw [hl2, hl'] at hv'
    rcases List.mem_append.mp hv' with h | h
    · exact ⟨(hv v h).1, (hv v h).2 rfl⟩
    · rcases hv2 v h with rfl | rfl <;> simp

/-! ## Semantic steps on bound names -/

theorem stepOpR_none {L : Bool} {c : CState} {s : RState} (hb : BRel c.status s.refs) :
    ∀ {o : Op}, OpStuck L c o → stepOpR L s o = none
  | .assign x e, h => by
      rcases h with h | h
      · simp [stepOpR, h]
      · simp [stepOpR, evalR_none_of_stuck hb e h]
  | .borrow r x, h => by simp [stepOpR, show L = false from h]
  | .borrowSel r e x y, h => by
      rcases h with h | h
      · simp [stepOpR, h]
      · simp [stepOpR, evalR_none_of_stuck hb e h]
  | .reborrow t r, h => by simp [stepOpR, (hb r).1 h]
  | .write r e, h => by
      rcases h with h | h
      · simp only [stepOpR, evalR_none_of_stuck hb e h]
        cases s.refs r <;> rfl
      · simp [stepOpR, (hb r).1 h]
  | .endBorrow r, h => by simp [stepOpR, (hb r).1 h]

theorem stepOpB_none {L : Bool} {c : CState} {s : BState} (hb : BRel c.status s.refs) :
    ∀ {o : Op}, OpStuck L c o → stepOpB L s o = none
  | .assign x e, h => by
      rcases h with h | h
      · simp [stepOpB, h]
      · simp [stepOpB, evalB_none_of_stuck hb e h]
  | .borrow r x, h => by simp [stepOpB, show L = false from h]
  | .borrowSel r e x y, h => by
      rcases h with h | h
      · simp [stepOpB, h]
      · simp [stepOpB, evalB_none_of_stuck hb e h]
  | .reborrow t r, h => by simp [stepOpB, (hb r).1 h]
  | .write r e, h => by
      rcases h with h | h
      · simp only [stepOpB, evalB_none_of_stuck hb e h]
        cases s.refs r <;> rfl
      · simp [stepOpB, (hb r).1 h]
  | .endBorrow r, h => by simp [stepOpB, (hb r).1 h]

theorem stepOpP_none {L : Bool} {c : CState} {s : PState} (hb : BRel c.status s.refs)
    (res : RefVar → Bool) (φ : Nat → Int) :
    ∀ {o : Op}, OpStuck L c o → stepOpP L res φ s o = none
  | .assign x e, h => by
      rcases h with h | h
      · simp [stepOpP, h]
      · simp [stepOpP, evalP_none_of_stuck hb e h]
  | .borrow r x, h => by simp [stepOpP, show L = false from h]
  | .borrowSel r e x y, h => by
      rcases h with h | h
      · simp [stepOpP, h]
      · simp [stepOpP, evalP_none_of_stuck hb e h]
  | .reborrow t r, h => by simp [stepOpP, (hb r).1 h]
  | .write r e, h => by
      rcases h with h | h
      · simp only [stepOpP, evalP_none_of_stuck hb e h]
        cases s.refs r <;> rfl
      · simp [stepOpP, (hb r).1 h]
  | .endBorrow r, h => by simp [stepOpP, (hb r).1 h]

theorem stepOpR_refs {L : Bool} {s s' : RState} {o : Op} (h : stepOpR L s o = some s') (k : RefVar) :
    s'.refs k = none ↔ (s.refs k = none ∧ o.binds ≠ some k) := by
  cases o with
  | assign x e =>
      simp only [stepOpR] at h; split at h
      · simp only [Option.map_eq_some_iff] at h; obtain ⟨v, -, rfl⟩ := h; simp [Op.binds]
      · simp at h
  | borrow r x =>
      simp only [stepOpR] at h; split at h
      · simp only [Option.some.injEq] at h; subst h
        by_cases hk : k = r
        · subst hk; simp [Op.binds]
        · simp [hk, Op.binds, Ne.symm hk]
      · simp at h
  | borrowSel r e x y =>
      simp only [stepOpR] at h; split at h
      · simp only [Option.map_eq_some_iff] at h; obtain ⟨v, -, rfl⟩ := h
        by_cases hk : k = r
        · subst hk; simp [Op.binds]
        · simp [hk, Op.binds, Ne.symm hk]
      · simp at h
  | reborrow t r =>
      simp only [stepOpR, Option.map_eq_some_iff] at h; obtain ⟨a, -, rfl⟩ := h
      by_cases hk : k = t
      · subst hk; simp [Op.binds]
      · simp [hk, Op.binds, Ne.symm hk]
  | write r e =>
      simp only [stepOpR, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨a, -, v, -, rfl⟩ := h; simp [Op.binds]
  | endBorrow r =>
      simp only [stepOpR, Option.map_eq_some_iff] at h; obtain ⟨a, -, rfl⟩ := h; simp [Op.binds]

theorem applyBack_refs : ∀ {s s' : BState} {l : List (Target × Int)}, applyBack s l = some s' →
    ∀ k, (s'.refs k = none ↔ s.refs k = none)
  | s, s', [], h, k => by simp [applyBack] at h; subst h; rfl
  | s, s', (.loc x, v) :: rest, h, k => by
      simp only [applyBack] at h
      exact (applyBack_refs h k).trans Iff.rfl
  | s, s', (.ref q, v) :: rest, h, k => by
      simp only [applyBack, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨p, hp, h⟩ := h
      rw [applyBack_refs h k]
      by_cases hk : k = q
      · subst hk; simp [hp]
      · simp [hk]

theorem stepOpB_refs {L : Bool} {s s' : BState} {o : Op} (h : stepOpB L s o = some s') (k : RefVar) :
    s'.refs k = none ↔ (s.refs k = none ∧ o.binds ≠ some k) := by
  cases o with
  | assign x e =>
      simp only [stepOpB] at h; split at h
      · simp only [Option.map_eq_some_iff] at h; obtain ⟨v, -, rfl⟩ := h; simp [Op.binds]
      · simp at h
  | borrow r x =>
      simp only [stepOpB] at h; split at h
      · simp only [Option.some.injEq] at h; subst h
        by_cases hk : k = r
        · subst hk; simp [Op.binds]
        · simp [hk, Op.binds, Ne.symm hk]
      · simp at h
  | borrowSel r e x y =>
      simp only [stepOpB] at h; split at h
      · simp only [Option.map_eq_some_iff] at h; obtain ⟨v, -, rfl⟩ := h
        by_cases hk : k = r
        · subst hk; simp [Op.binds]
        · simp [hk, Op.binds, Ne.symm hk]
      · simp at h
  | reborrow t r =>
      simp only [stepOpB, Option.map_eq_some_iff] at h; obtain ⟨a, -, rfl⟩ := h
      by_cases hk : k = t
      · subst hk; simp [Op.binds]
      · simp [hk, Op.binds, Ne.symm hk]
  | write r e =>
      simp only [stepOpB, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨a, ha, v, -, rfl⟩ := h
      by_cases hk : k = r
      · subst hk; simp [ha, Op.binds]
      · simp [hk, Op.binds]
  | endBorrow r =>
      simp only [stepOpB, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨q, -, h⟩ := h
      rw [applyBack_refs h k]; simp [Op.binds]

theorem stepOpP_refs {L : Bool} {res : RefVar → Bool} {φ : Nat → Int} {s s' : PState} {o : Op}
    (h : stepOpP L res φ s o = some s') (k : RefVar) :
    s'.refs k = none ↔ (s.refs k = none ∧ o.binds ≠ some k) := by
  cases o with
  | assign x e =>
      simp only [stepOpP] at h; split at h
      · simp only [Option.map_eq_some_iff] at h; obtain ⟨v, -, rfl⟩ := h; simp [Op.binds]
      · simp at h
  | borrow r x =>
      simp only [stepOpP] at h; split at h
      · simp only [Option.some.injEq] at h; subst h
        by_cases hk : k = r
        · subst hk; simp [Op.binds]
        · simp [hk, Op.binds, Ne.symm hk]
      · simp at h
  | borrowSel r e x y =>
      simp only [stepOpP] at h; split at h
      · simp only [Option.map_eq_some_iff] at h; obtain ⟨v, -, rfl⟩ := h
        split
        · by_cases hk : k = r
          · subst hk; simp [Op.binds]
          · simp [hk, Op.binds, Ne.symm hk]
        · by_cases hk : k = r
          · subst hk; simp [Op.binds]
          · simp [hk, Op.binds, Ne.symm hk]
      · simp at h
  | reborrow t r =>
      simp only [stepOpP, Option.map_eq_some_iff] at h; obtain ⟨a, ha, rfl⟩ := h
      by_cases hk : k = t
      · simp [hk, Op.binds]
      · by_cases hkr : k = r
        · subst hkr; simp [hk, ha, Op.binds, Ne.symm hk]
        · simp [hk, hkr, Op.binds, Ne.symm hk]
  | write r e =>
      simp only [stepOpP, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨a, ha, v, -, rfl⟩ := h
      by_cases hk : k = r
      · subst hk; simp [ha, Op.binds]
      · simp [hk, Op.binds]
  | endBorrow r =>
      simp only [stepOpP, Option.map_eq_some_iff] at h; obtain ⟨a, ha, rfl⟩ := h
      by_cases hk : k = r
      · subst hk; simp [ha, Op.binds]
      · simp [hk, Op.binds]

theorem brel_step {α : Type} {L : Bool} {c : CState} {o : Op} {refs refs' : RefVar → Option α}
    (hb : BRel c.status refs) (hs : (checkOp L c o).stuck = false)
    (hr : ∀ k, refs' k = none ↔ (refs k = none ∧ o.binds ≠ some k)) :
    BRel (checkOp L c o).status refs' := by
  intro k
  rw [checkOp_status_unborn hs, hr, hb k]

/-! ## Runs of basic operations -/

theorem checkOp_not_stuck_of_checkOps {L : Bool} {c : CState} {o : Op} {os : List Op}
    (h : (checkOps L (checkOp L c o) os).stuck = false) : (checkOp L c o).stuck = false := by
  cases hc : (checkOp L c o).stuck
  · rfl
  · rw [checkOps_of_stuck' hc] at h; simp [hc] at h

theorem runOpsR_none_of_stuck {L : Bool} : ∀ {c : CState} {s : RState} {os : List Op},
    BRel c.status s.refs → c.stuck = false → (checkOps L c os).stuck = true → runOpsR L s os = none
  | c, s, [], _, hc, h => by simp [checkOps, hc] at h
  | c, s, o :: os, hb, hc, h => by
      simp only [checkOps] at h
      simp only [runOpsR]
      by_cases h1 : (checkOp L c o).stuck = true
      · simp [stepOpR_none hb (checkOp_stuck hc h1)]
      · have h1' : (checkOp L c o).stuck = false := by simpa using h1
        cases hst : stepOpR L s o with
        | none => rfl
        | some s' =>
            exact runOpsR_none_of_stuck (brel_step hb h1' (stepOpR_refs hst)) h1' h

theorem runOpsB_none_of_stuck {L : Bool} : ∀ {c : CState} {s : BState} {os : List Op},
    BRel c.status s.refs → c.stuck = false → (checkOps L c os).stuck = true → runOpsB L s os = none
  | c, s, [], _, hc, h => by simp [checkOps, hc] at h
  | c, s, o :: os, hb, hc, h => by
      simp only [checkOps] at h
      simp only [runOpsB]
      by_cases h1 : (checkOp L c o).stuck = true
      · simp [stepOpB_none hb (checkOp_stuck hc h1)]
      · have h1' : (checkOp L c o).stuck = false := by simpa using h1
        cases hst : stepOpB L s o with
        | none => rfl
        | some s' =>
            exact runOpsB_none_of_stuck (brel_step hb h1' (stepOpB_refs hst)) h1' h

theorem runOpsP_none_of_stuck {L : Bool} {res : RefVar → Bool} {φ : Nat → Int} :
    ∀ {c : CState} {s : PState} {os : List Op},
    BRel c.status s.refs → c.stuck = false → (checkOps L c os).stuck = true →
      runOpsP L res φ s os = none
  | c, s, [], _, hc, h => by simp [checkOps, hc] at h
  | c, s, o :: os, hb, hc, h => by
      simp only [checkOps] at h
      simp only [runOpsP]
      by_cases h1 : (checkOp L c o).stuck = true
      · simp [stepOpP_none hb res φ (checkOp_stuck hc h1)]
      · have h1' : (checkOp L c o).stuck = false := by simpa using h1
        cases hst : stepOpP L res φ s o with
        | none => rfl
        | some s' =>
            exact runOpsP_none_of_stuck (brel_step hb h1' (stepOpP_refs hst)) h1' h

/-- `BRel` is preserved along a run whose check never gets stuck. -/
theorem runOpsR_brel {L : Bool} : ∀ {c : CState} {s s' : RState} {os : List Op},
    BRel c.status s.refs → (checkOps L c os).stuck = false → runOpsR L s os = some s' →
      BRel (checkOps L c os).status s'.refs
  | c, s, s', [], hb, _, h => by simp [runOpsR] at h; subst h; exact hb
  | c, s, s', o :: os, hb, hc, h => by
      simp only [checkOps] at hc ⊢
      simp only [runOpsR, Option.bind_eq_some_iff] at h
      obtain ⟨s1, h1, h2⟩ := h
      exact runOpsR_brel (brel_step hb (checkOp_not_stuck_of_checkOps hc) (stepOpR_refs h1)) hc h2

theorem runOpsB_brel {L : Bool} : ∀ {c : CState} {s s' : BState} {os : List Op},
    BRel c.status s.refs → (checkOps L c os).stuck = false → runOpsB L s os = some s' →
      BRel (checkOps L c os).status s'.refs
  | c, s, s', [], hb, _, h => by simp [runOpsB] at h; subst h; exact hb
  | c, s, s', o :: os, hb, hc, h => by
      simp only [checkOps] at hc ⊢
      simp only [runOpsB, Option.bind_eq_some_iff] at h
      obtain ⟨s1, h1, h2⟩ := h
      exact runOpsB_brel (brel_step hb (checkOp_not_stuck_of_checkOps hc) (stepOpB_refs h1)) hc h2

theorem runOpsP_brel {L : Bool} {res : RefVar → Bool} {φ : Nat → Int} :
    ∀ {c : CState} {s s' : PState} {os : List Op},
    BRel c.status s.refs → (checkOps L c os).stuck = false → runOpsP L res φ s os = some s' →
      BRel (checkOps L c os).status s'.refs
  | c, s, s', [], hb, _, h => by simp [runOpsP] at h; subst h; exact hb
  | c, s, s', o :: os, hb, hc, h => by
      simp only [checkOps] at hc ⊢
      simp only [runOpsP, Option.bind_eq_some_iff] at h
      obtain ⟨s1, h1, h2⟩ := h
      exact runOpsP_brel (brel_step hb (checkOp_not_stuck_of_checkOps hc) (stepOpP_refs h1)) hc h2

/-! ## Callees with a scoping error -/

theorem calleeInit_brelR (a : Var) :
    BRel CState.calleeInit.status (calleeRefsR a) := by
  intro k; by_cases hk : k = 0 <;> simp [CState.calleeInit, calleeRefsR, hk, Callee.param]

theorem calleeInit_brelB (a : Int) :
    BRel CState.calleeInit.status (calleeInitB a).refs := by
  intro k; by_cases hk : k = 0 <;> simp [CState.calleeInit, calleeInitB, hk, Callee.param]

theorem calleeInit_brelP (a pf : Int) (n : Nat) :
    BRel CState.calleeInit.status (calleeInitP a pf n).refs := by
  intro k; by_cases hk : k = 0 <;> simp [CState.calleeInit, calleeInitP, hk, Callee.param]

/-- A callee whose check is stuck has a stuck reference run or an unbound
returned name. -/
theorem calleeR_stuck {f : Callee} (h : (checkCallee f).stuck = true) (σ : Store) (a : Var) :
    ∀ s', runOpsR false { store := σ, refs := calleeRefsR a } f.body = some s' →
      s'.refs f.ret = none := by
  intro s' hs'
  simp only [checkCallee] at h
  split at h
  · rename_i hst
    rw [runOpsR_none_of_stuck (calleeInit_brelR a) rfl hst] at hs'; simp at hs'
  · rename_i hst
    have hst' : (checkOps false CState.calleeInit f.body).stuck = false := by simpa using hst
    have hb := runOpsR_brel (calleeInit_brelR a) hst' hs'
    rw [useRef_stuck_iff] at h
    simp [hst'] at h
    exact (hb f.ret).1 h

theorem calleeB_stuck {f : Callee} (h : (checkCallee f).stuck = true) (a : Int) :
    calleeFwd f a = none := by
  simp only [calleeFwd, calleeRunB]
  simp only [checkCallee] at h
  split at h
  · rename_i hst
    rw [runOpsB_none_of_stuck (calleeInit_brelB a) rfl hst]; rfl
  · rename_i hst
    have hst' : (checkOps false CState.calleeInit f.body).stuck = false := by simpa using hst
    cases hs' : runOpsB false (calleeInitB a) f.body with
    | none => rfl
    | some s' =>
      have hb := runOpsB_brel (calleeInit_brelB a) hst' hs'
      rw [useRef_stuck_iff] at h
      simp [hst'] at h
      simp [(hb f.ret).1 h]

theorem calleeP_stuck {f : Callee} (h : (checkCallee f).stuck = true) (ex : Bool)
    (φ : Nat → Int) (a pf : Int) (n : Nat) :
    ∀ fr, calleeRunP ex φ f a pf n = some fr → fr.refs f.ret = none := by
  intro fr hfr
  simp only [calleeRunP, Option.map_eq_some_iff] at hfr
  obtain ⟨s', hs', rfl⟩ := hfr
  simp only [checkCallee] at h
  split at h
  · rename_i hst
    rw [runOpsP_none_of_stuck (calleeInit_brelP a pf n) rfl hst] at hs'; simp at hs'
  · rename_i hst
    have hst' : (checkOps false CState.calleeInit f.body).stuck = false := by simpa using hst
    have hb := runOpsP_brel (calleeInit_brelP a pf n) hst' hs'
    rw [useRef_stuck_iff] at h
    simp [hst'] at h
    exact (hb f.ret).1 h

end Sim
end Toy.Prophecy
