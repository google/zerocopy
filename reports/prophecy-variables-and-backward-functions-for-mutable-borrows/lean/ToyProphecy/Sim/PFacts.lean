import ToyProphecy.Sim.CalleeBack

/-!
# Proof infrastructure: general facts about single steps and runs

Auxiliary lemmas used only inside proofs of the main statements.
-/

namespace Toy.Prophecy
namespace Sim

open CState

/-! ## Successful evaluation and steps when the checker is not stuck -/

theorem evalR_some_of_not_stuck {L : Bool} {c : CState} {s : RState}
    (hb : BRel c.status s.refs) : ∀ e, (checkExpr L c e).stuck = false →
      ∃ v, evalR L s e = some v
  | .lit n, _ => ⟨n, rfl⟩
  | .var x, h => by
      cases L
      · simp [checkExpr, CState.setStuck] at h
      · exact ⟨_, rfl⟩
  | .deref r, h => by
      simp only [checkExpr] at h
      rw [useRef_stuck_iff] at h
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
      cases hr : s.refs r with
      | none => exact absurd ((hb r).2 hr) h.2
      | some q => exact ⟨s.store q, by simp [evalR, hr]⟩
  | .add a b, h => by
      simp only [checkExpr] at h
      have ha : (checkExpr L c a).stuck = false := by
        cases h' : (checkExpr L c a).stuck
        · rfl
        · rw [checkExpr_stuck_mono L _ b h'] at h; exact h
      have hb' : BRel (checkExpr L c a).status s.refs := by
        rw [(checkExpr_shape L c a).status]; exact hb
      obtain ⟨u, hu⟩ := evalR_some_of_not_stuck hb a ha
      obtain ⟨v, hv⟩ := evalR_some_of_not_stuck hb' b h
      exact ⟨u + v, by simp [evalR, hu, hv]⟩

theorem evalP_some_of_not_stuck {L : Bool} {c : CState} {s : PState}
    (hb : BRel c.status s.refs) : ∀ e, (checkExpr L c e).stuck = false →
      ∃ v, evalP L s e = some v
  | .lit n, _ => ⟨n, rfl⟩
  | .var x, h => by
      cases L
      · simp [checkExpr, CState.setStuck] at h
      · exact ⟨_, rfl⟩
  | .deref r, h => by
      simp only [checkExpr] at h
      rw [useRef_stuck_iff] at h
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
      cases hr : s.refs r with
      | none => exact absurd ((hb r).2 hr) h.2
      | some q => exact ⟨q.cur, by simp [evalP, hr]⟩
  | .add a b, h => by
      simp only [checkExpr] at h
      have ha : (checkExpr L c a).stuck = false := by
        cases h' : (checkExpr L c a).stuck
        · rfl
        · rw [checkExpr_stuck_mono L _ b h'] at h; exact h
      have hb' : BRel (checkExpr L c a).status s.refs := by
        rw [(checkExpr_shape L c a).status]; exact hb
      obtain ⟨u, hu⟩ := evalP_some_of_not_stuck hb a ha
      obtain ⟨v, hv⟩ := evalP_some_of_not_stuck hb' b h
      exact ⟨u + v, by simp [evalP, hu, hv]⟩

/-- Facts about the checker for a non-stuck step, by operation. -/
theorem checkOp_ns_cases {L : Bool} {c : CState} {o : Op} (hs : (checkOp L c o).stuck = false) :
    c.stuck = false ∧
    match o with
    | .assign _ e => L = true ∧ (checkExpr L c e).stuck = false
    | .borrow _ _ => L = true
    | .borrowSel _ e _ _ => L = true ∧ (checkExpr L c e).stuck = false
    | .reborrow _ r => c.status r ≠ .unborn
    | .write r e => (checkExpr L c e).stuck = false ∧ c.status r ≠ .unborn
    | .endBorrow r => c.status r ≠ .unborn := by
  have hc : c.stuck = false := by
    cases hc : c.stuck
    · rfl
    · rw [checkOp_of_stuck hc] at hs; simp [hc] at hs
  refine ⟨hc, ?_⟩
  cases o with
  | assign x e =>
      cases L
      · simp [checkOp, hc, CState.setStuck] at hs
      · simp only [checkOp, hc, Bool.false_eq_true, ↓reduceIte, Bool.not_true] at hs
        rw [addV_ite_stuck] at hs
        exact ⟨rfl, hs⟩
  | borrow r x =>
      cases L
      · simp [checkOp, hc, CState.setStuck] at hs
      · rfl
  | borrowSel r e x y =>
      cases L
      · simp [checkOp, hc, CState.setStuck] at hs
      · simp only [checkOp, hc, Bool.false_eq_true, ↓reduceIte, Bool.not_true] at hs
        rw [bindRef_stuck, addV_ite_stuck] at hs
        exact ⟨rfl, hs⟩
  | reborrow t r =>
      intro hr; simp [checkOp, hc, CState.useRef, hr, CState.setStuck] at hs
  | write r e =>
      have hes : (checkExpr L c e).stuck = false := by
        cases h : (checkExpr L c e).stuck
        · rfl
        · simp [checkOp, hc, h] at hs
      refine ⟨hes, fun hr => ?_⟩
      simp only [checkOp, hc, hes, Bool.false_eq_true, ↓reduceIte] at hs
      rw [useRef_stuck_iff] at hs
      simp [hes, (checkExpr_shape L c e).status, hr] at hs
  | endBorrow r =>
      intro hr; simp [checkOp, hc, CState.useRef, hr, CState.setStuck] at hs

theorem stepOpR_some {L : Bool} {c : CState} {s : RState} {o : Op}
    (hb : BRel c.status s.refs) (hs : (checkOp L c o).stuck = false) :
    ∃ s', stepOpR L s o = some s' := by
  have hcs := (checkOp_ns_cases hs).2
  have bound : ∀ r, c.status r ≠ .unborn → ∃ a, s.refs r = some a := by
    intro r hr
    cases h : s.refs r with
    | none => exact absurd ((hb r).2 h) hr
    | some a => exact ⟨a, rfl⟩
  cases o with
  | assign x e =>
      obtain ⟨hL, he⟩ := hcs; subst hL
      obtain ⟨v, hv⟩ := evalR_some_of_not_stuck hb e he
      simp [stepOpR, hv]
  | borrow r x =>
      cases L
      · exact absurd hcs (by simp)
      · simp [stepOpR]
  | borrowSel r e x y =>
      obtain ⟨hL, he⟩ := hcs; subst hL
      obtain ⟨v, hv⟩ := evalR_some_of_not_stuck hb e he
      simp [stepOpR, hv]
  | reborrow t r =>
      obtain ⟨a, ha⟩ := bound r hcs
      simp [stepOpR, ha]
  | write r e =>
      obtain ⟨he, hr⟩ := hcs
      obtain ⟨a, ha⟩ := bound r hr
      obtain ⟨v, hv⟩ := evalR_some_of_not_stuck hb e he
      simp [stepOpR, ha, hv]
  | endBorrow r =>
      obtain ⟨a, ha⟩ := bound r hcs
      simp [stepOpR, ha]

theorem stepOpP_some {L : Bool} {c : CState} {s : PState} {o : Op}
    (hb : BRel c.status s.refs) (hs : (checkOp L c o).stuck = false)
    (res : RefVar → Bool) (φ : Nat → Int) :
    ∃ s', stepOpP L res φ s o = some s' := by
  have hcs := (checkOp_ns_cases hs).2
  have bound : ∀ r, c.status r ≠ .unborn → ∃ a, s.refs r = some a := by
    intro r hr
    cases h : s.refs r with
    | none => exact absurd ((hb r).2 h) hr
    | some a => exact ⟨a, rfl⟩
  cases o with
  | assign x e =>
      obtain ⟨hL, he⟩ := hcs; subst hL
      obtain ⟨v, hv⟩ := evalP_some_of_not_stuck hb e he
      simp [stepOpP, hv]
  | borrow r x =>
      cases L
      · exact absurd hcs (by simp)
      · simp [stepOpP]
  | borrowSel r e x y =>
      obtain ⟨hL, he⟩ := hcs; subst hL
      obtain ⟨v, hv⟩ := evalP_some_of_not_stuck hb e he
      simp [stepOpP, hv]
  | reborrow t r =>
      obtain ⟨a, ha⟩ := bound r hcs
      simp [stepOpP, ha]
  | write r e =>
      obtain ⟨he, hr⟩ := hcs
      obtain ⟨a, ha⟩ := bound r hr
      obtain ⟨v, hv⟩ := evalP_some_of_not_stuck hb e he
      simp [stepOpP, ha, hv]
  | endBorrow r =>
      obtain ⟨a, ha⟩ := bound r hcs
      simp [stepOpP, ha]

/-! ## Bookkeeping of the prophecy translation -/

/-- The prophecy assignment is read only at the current counter, and only by
borrow-creating operations, which then advance the counter. -/
theorem stepOpP_next {L : Bool} {res : RefVar → Bool} {φ : Nat → Int} {s s' : PState} {o : Op}
    (h : stepOpP L res φ s o = some s') :
    s'.next = if o.binds.isSome then s.next + 1 else s.next := by
  cases o with
  | assign x e =>
      simp only [stepOpP] at h; split at h
      · simp only [Option.map_eq_some_iff] at h; obtain ⟨v, -, rfl⟩ := h; simp [Op.binds]
      · simp at h
  | borrow r x =>
      simp only [stepOpP] at h; split at h
      · simp only [Option.some.injEq] at h; subst h; simp [Op.binds]
      · simp at h
  | borrowSel r e x y =>
      simp only [stepOpP] at h; split at h
      · simp only [Option.map_eq_some_iff] at h; obtain ⟨v, -, rfl⟩ := h
        split <;> simp [Op.binds]
      · simp at h
  | reborrow t r =>
      simp only [stepOpP, Option.map_eq_some_iff] at h; obtain ⟨a, -, rfl⟩ := h; simp [Op.binds]
  | write r e =>
      simp only [stepOpP, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨a, -, v, -, rfl⟩ := h; simp [Op.binds]
  | endBorrow r =>
      simp only [stepOpP, Option.map_eq_some_iff] at h; obtain ⟨a, -, rfl⟩ := h; simp [Op.binds]

theorem stepOpP_congr {L : Bool} {res : RefVar → Bool} {φ φ' : Nat → Int} {s s' : PState} {o : Op}
    (h : stepOpP L res φ s o = some s') (hφ : ∀ i < s'.next, φ' i = φ i) :
    stepOpP L res φ' s o = some s' := by
  have hn := stepOpP_next h
  cases o with
  | borrow r x =>
      have : φ' s.next = φ s.next := hφ _ (by simp [Op.binds] at hn; omega)
      simpa [stepOpP, this] using h
  | borrowSel r e x y =>
      have : φ' s.next = φ s.next := hφ _ (by simp [Op.binds] at hn; omega)
      simpa [stepOpP, this] using h
  | reborrow t r =>
      have : φ' s.next = φ s.next := hφ _ (by simp [Op.binds] at hn; omega)
      simpa [stepOpP, this] using h
  | assign x e => simpa [stepOpP] using h
  | write r e => simpa [stepOpP] using h
  | endBorrow r => simpa [stepOpP] using h

theorem runOpsP_next {L : Bool} {res : RefVar → Bool} {φ : Nat → Int} :
    ∀ {s s' : PState} {os : List Op}, runOpsP L res φ s os = some s' → s.next ≤ s'.next
  | s, s', [], h => by simp [runOpsP] at h; subst h; exact Nat.le_refl _
  | s, s', o :: os, h => by
      simp only [runOpsP, Option.bind_eq_some_iff] at h
      obtain ⟨s1, h1, h2⟩ := h
      have := stepOpP_next h1
      have := runOpsP_next h2
      split at *  <;> omega

theorem runOpsP_congr {L : Bool} {res : RefVar → Bool} {φ φ' : Nat → Int} :
    ∀ {s s' : PState} {os : List Op}, runOpsP L res φ s os = some s' →
      (∀ i < s'.next, φ' i = φ i) → runOpsP L res φ' s os = some s'
  | s, s', [], h, _ => h
  | s, s', o :: os, h, hφ => by
      simp only [runOpsP, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨s1, h1, h2⟩ := h
      have hn := runOpsP_next h2
      exact ⟨s1, stepOpP_congr h1 (fun i hi => hφ i (by omega)), runOpsP_congr h2 hφ⟩

theorem stepOpP_cs {L : Bool} {res : RefVar → Bool} {φ : Nat → Int} {s s' : PState} {o : Op}
    (h : stepOpP L res φ s o = some s') :
    ∃ l, s'.cs = s.cs ++ l ∧
      ((∀ r, o ≠ .endBorrow r) → l = []) ∧
      (∀ r, o = .endBorrow r → ∃ p, s.refs r = some p ∧ l = if res r then [(p.cur, p.fin)] else []) := by
  cases o with
  | assign x e =>
      simp only [stepOpP] at h; split at h
      · simp only [Option.map_eq_some_iff] at h; obtain ⟨v, -, rfl⟩ := h
        exact ⟨[], by simp, fun _ => rfl, by simp⟩
      · simp at h
  | borrow r x =>
      simp only [stepOpP] at h; split at h
      · simp only [Option.some.injEq] at h; subst h
        exact ⟨[], by simp, fun _ => rfl, by simp⟩
      · simp at h
  | borrowSel r e x y =>
      simp only [stepOpP] at h; split at h
      · simp only [Option.map_eq_some_iff] at h; obtain ⟨v, -, rfl⟩ := h
        refine ⟨[], ?_, fun _ => rfl, by simp⟩
        split <;> simp
      · simp at h
  | reborrow t r =>
      simp only [stepOpP, Option.map_eq_some_iff] at h; obtain ⟨a, -, rfl⟩ := h
      exact ⟨[], by simp, fun _ => rfl, by simp⟩
  | write r e =>
      simp only [stepOpP, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨a, -, v, -, rfl⟩ := h
      exact ⟨[], by simp, fun _ => rfl, by simp⟩
  | endBorrow r =>
      simp only [stepOpP, Option.map_eq_some_iff] at h; obtain ⟨a, ha, rfl⟩ := h
      refine ⟨if res r then [(a.cur, a.fin)] else [], ?_, fun h => absurd rfl (h r), ?_⟩
      · split <;> simp_all
      · intro r' hr'; cases hr'; exact ⟨a, ha, rfl⟩

theorem runOpsP_cs {L : Bool} {res : RefVar → Bool} {φ : Nat → Int} :
    ∀ {s s' : PState} {os : List Op}, runOpsP L res φ s os = some s' → ∃ l, s'.cs = s.cs ++ l
  | s, s', [], h => by simp [runOpsP] at h; subst h; exact ⟨[], by simp⟩
  | s, s', o :: os, h => by
      simp only [runOpsP, Option.bind_eq_some_iff] at h
      obtain ⟨s1, h1, h2⟩ := h
      obtain ⟨l1, hl1, -⟩ := stepOpP_cs h1
      obtain ⟨l2, hl2⟩ := runOpsP_cs h2
      exact ⟨l1 ++ l2, by rw [hl2, hl1, List.append_assoc]⟩

theorem sat_of_append {l1 l2 : List (Int × Int)} (h : Sat (l1 ++ l2)) : Sat l1 ∧ Sat l2 :=
  ⟨fun c hc => h c (List.mem_append_left _ hc), fun c hc => h c (List.mem_append_right _ hc)⟩

theorem sat_append {l1 l2 : List (Int × Int)} (h1 : Sat l1) (h2 : Sat l2) : Sat (l1 ++ l2) := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact h1 c hc
  · exact h2 c hc

/-- Fins of names other than the bound one are unchanged by a step. -/
theorem stepOpP_fin {L : Bool} {res : RefVar → Bool} {φ : Nat → Int} {s s' : PState} {o : Op}
    (h : stepOpP L res φ s o = some s') (k : RefVar) (hk : o.binds ≠ some k) :
    (s'.refs k).map PRef.fin = (s.refs k).map PRef.fin := by
  cases o with
  | assign x e =>
      simp only [stepOpP] at h; split at h
      · simp only [Option.map_eq_some_iff] at h; obtain ⟨v, -, rfl⟩ := h; rfl
      · simp at h
  | borrow r x =>
      simp only [stepOpP] at h; split at h
      · simp only [Option.some.injEq] at h; subst h
        have : k ≠ r := fun h' => hk (by simp [Op.binds, h'])
        simp [this]
      · simp at h
  | borrowSel r e x y =>
      simp only [stepOpP] at h; split at h
      · simp only [Option.map_eq_some_iff] at h; obtain ⟨v, -, rfl⟩ := h
        have : k ≠ r := fun h' => hk (by simp [Op.binds, h'])
        split <;> simp [this]
      · simp at h
  | reborrow t r =>
      simp only [stepOpP, Option.map_eq_some_iff] at h; obtain ⟨a, ha, rfl⟩ := h
      have : k ≠ t := fun h' => hk (by simp [Op.binds, h'])
      by_cases hkr : k = r
      · subst hkr; simp [this, ha]
      · simp [this, hkr]
  | write r e =>
      simp only [stepOpP, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨a, ha, v, -, rfl⟩ := h
      by_cases hkr : k = r
      · subst hkr; simp [ha]
      · simp [hkr]
  | endBorrow r =>
      simp only [stepOpP, Option.map_eq_some_iff] at h; obtain ⟨a, ha, rfl⟩ := h
      by_cases hkr : k = r
      · subst hkr; simp [ha]
      · simp [hkr]

/-- Names bound at the end of a run were bound at its start or are bound by an
operation of the run. -/
theorem runOpsP_bound {L : Bool} {res : RefVar → Bool} {φ : Nat → Int} :
    ∀ {s s' : PState} {os : List Op}, runOpsP L res φ s os = some s' →
      ∀ j, s'.refs j ≠ none → s.refs j ≠ none ∨ j ∈ os.filterMap Op.binds
  | s, s', [], h, j, hj => by simp [runOpsP] at h; subst h; exact Or.inl hj
  | s, s', o :: os, h, j, hj => by
      simp only [runOpsP, Option.bind_eq_some_iff] at h
      obtain ⟨s1, h1, h2⟩ := h
      rcases runOpsP_bound h2 j hj with h | h
      · have := stepOpP_refs h1 j
        by_cases hb : o.binds = some j
        · right; simp [hb]
        · left; intro hn; exact h (this.2 ⟨hn, hb⟩)
      · right
        simp only [List.filterMap_cons]
        split <;> simp_all

end Sim
end Toy.Prophecy
