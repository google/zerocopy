import ToyProphecy.Monotone

/-!
# Proof infrastructure: basic facts about the checker and the semantics

Auxiliary lemmas used only inside proofs of the main statements.
-/

namespace Toy.Prophecy
namespace Sim

open CState

@[scoped simp] theorem fupd_apply {α : Type} (f : Nat → α) (k : Nat) (v : α) (j : Nat) :
    fupd f k v j = if j = k then v else f j := rfl

@[scoped simp] theorem upd_apply {α : Type} (f : Nat → α) (k : Nat) (v : α) (j : Nat) :
    CState.upd f k v j = if j = k then v else f j := rfl

@[scoped simp] theorem store_set_apply (σ : Store) (x : Var) (v : Int) (y : Var) :
    σ.set x v y = if y = x then v else σ y := rfl

/-! ## The checker: field lemmas -/

theorem useRef_unborn {c : CState} {r : RefVar} (h : c.status r = .unborn) :
    c.useRef r = c.setStuck := by simp [CState.useRef, h]
theorem useRef_active {c : CState} {r : RefVar} (h : c.status r = .active) :
    c.useRef r = c := by simp [CState.useRef, h]
theorem useRef_frozen {c : CState} {r : RefVar} (h : c.status r = .frozen) :
    c.useRef r = c.addV .frozenAccess := by simp [CState.useRef, h]
theorem useRef_ended {c : CState} {r : RefVar} (h : c.status r = .ended) :
    c.useRef r = c.addV .useAfterEnd := by simp [CState.useRef, h]

/-- A checker step is described by: same lent/status/lender/bound, violations
appended, stuck flag possibly raised. -/
structure SameShape (c c' : CState) : Prop where
  lent : c'.lent = c.lent
  status : c'.status = c.status
  lender : c'.lender = c.lender
  bound : c'.bound = c.bound

theorem useRef_shape (c : CState) (r : RefVar) : SameShape c (c.useRef r) := by
  unfold CState.useRef
  split <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem useRef_viol (c : CState) (r : RefVar) :
    ∃ l, (c.useRef r).viol = c.viol ++ l ∧ ∀ v ∈ l, v = .frozenAccess ∨ v = .useAfterEnd := by
  unfold CState.useRef
  split
  · exact ⟨[], by simp [CState.setStuck], by simp⟩
  · exact ⟨[], by simp, by simp⟩
  · exact ⟨[.frozenAccess], by simp [CState.addV], by simp⟩
  · exact ⟨[.useAfterEnd], by simp [CState.addV], by simp⟩

theorem useRef_stuck_mono {c : CState} (r : RefVar) (h : c.stuck = true) :
    (c.useRef r).stuck = true := by
  unfold CState.useRef
  split <;> simp_all [CState.setStuck, CState.addV]

theorem useRef_stuck_iff (c : CState) (r : RefVar) :
    (c.useRef r).stuck = (c.stuck || decide (c.status r = .unborn)) := by
  unfold CState.useRef
  split <;> simp_all [CState.setStuck, CState.addV]

/-- A clean, non-stuck use of `r` means `r` is active. -/
theorem useRef_clean {c : CState} {r : RefVar}
    (hs : (c.useRef r).stuck = false) (hv : (c.useRef r).viol = c.viol) :
    c.status r = .active ∧ c.useRef r = c := by
  cases h : c.status r
  · rw [useRef_unborn h] at hs; simp [CState.setStuck] at hs
  · exact ⟨rfl, useRef_active h⟩
  · rw [useRef_frozen h] at hv; simp [CState.addV] at hv
  · rw [useRef_ended h] at hv; simp [CState.addV] at hv

theorem bindRef_clean {c : CState} {t : RefVar} (hv : (c.bindRef t).viol = c.viol) :
    c.status t = .unborn ∧ c.bindRef t = { c with bound := c.bound ++ [t] } := by
  unfold CState.bindRef at *
  by_cases h : c.status t = .unborn
  · simp [h]
  · simp [h, CState.addV] at hv

theorem bindRef_viol (c : CState) (t : RefVar) :
    ∃ l, (c.bindRef t).viol = c.viol ++ l ∧ ∀ v ∈ l, v = .rebind := by
  unfold CState.bindRef
  split
  · exact ⟨[], by simp, by simp⟩
  · exact ⟨[.rebind], by simp [CState.addV], by simp⟩

theorem bindRef_stuck (c : CState) (t : RefVar) : (c.bindRef t).stuck = c.stuck := by
  unfold CState.bindRef; split <;> simp [CState.addV]

theorem bindRef_status (c : CState) (t : RefVar) : (c.bindRef t).status = c.status := by
  unfold CState.bindRef; split <;> simp [CState.addV]

theorem bindRef_lent (c : CState) (t : RefVar) : (c.bindRef t).lent = c.lent := by
  unfold CState.bindRef; split <;> simp [CState.addV]

theorem bindRef_bound (c : CState) (t : RefVar) : (c.bindRef t).bound = c.bound ++ [t] := by
  unfold CState.bindRef; split <;> simp [CState.addV]

theorem release_stuck (c : CState) (r : RefVar) : (c.release r).stuck = c.stuck := by
  unfold CState.release; split <;> (try split) <;> rfl

theorem release_viol (c : CState) (r : RefVar) : (c.release r).viol = c.viol := by
  unfold CState.release; split <;> (try split) <;> rfl

theorem release_bound (c : CState) (r : RefVar) : (c.release r).bound = c.bound := by
  unfold CState.release; split <;> (try split) <;> rfl

theorem release_lender (c : CState) (r : RefVar) : (c.release r).lender = c.lender := by
  unfold CState.release; split <;> (try split) <;> rfl

/-- `release` never makes a status `unborn` or changes an `unborn` status. -/
theorem release_status_unborn (c : CState) (r k : RefVar) :
    (c.release r).status k = .unborn ↔ c.status k = .unborn := by
  unfold CState.release
  split
  · rfl
  · rfl
  · split
    · rename_i q _ hq
      simp only [upd_apply]
      split
      · subst_vars; simp [hq]
      · rfl
    · rfl
  · rfl

/-! ## Expressions -/

/-- What a clean, non-stuck check of an expression guarantees. -/
def ExprOK (L : Bool) (c : CState) : Expr → Prop
  | .lit _ => True
  | .var x => L = true ∧ c.lent x = false
  | .deref r => c.status r = .active
  | .add a b => ExprOK L c a ∧ ExprOK L c b

theorem checkExpr_shape (L : Bool) : ∀ (c : CState) (e : Expr), SameShape c (checkExpr L c e)
  | c, .lit _ => ⟨rfl, rfl, rfl, rfl⟩
  | c, .var x => by
      simp only [checkExpr]
      split
      · exact ⟨rfl, rfl, rfl, rfl⟩
      · split <;> exact ⟨rfl, rfl, rfl, rfl⟩
  | c, .deref r => useRef_shape c r
  | c, .add a b => by
      have h1 := checkExpr_shape L c a
      have h2 := checkExpr_shape L (checkExpr L c a) b
      simp only [checkExpr]
      exact ⟨h2.lent.trans h1.lent, h2.status.trans h1.status, h2.lender.trans h1.lender,
        h2.bound.trans h1.bound⟩

theorem checkExpr_viol (L : Bool) : ∀ (c : CState) (e : Expr),
    ∃ l, (checkExpr L c e).viol = c.viol ++ l ∧
      ∀ v ∈ l, (v = .lentAccess ∧ L = true) ∨ v = .frozenAccess ∨ v = .useAfterEnd
  | c, .lit _ => ⟨[], by simp [checkExpr], by simp⟩
  | c, .var x => by
      simp only [checkExpr]
      cases L
      · exact ⟨[], by simp [CState.setStuck], by simp⟩
      · by_cases h : c.lent x
        · exact ⟨[.lentAccess], by simp [h, CState.addV], by simp⟩
        · exact ⟨[], by simp [h], by simp⟩
  | c, .deref r => by
      obtain ⟨l, hl, hv⟩ := useRef_viol c r
      exact ⟨l, hl, fun v hv' => Or.inr (hv v hv')⟩
  | c, .add a b => by
      obtain ⟨l1, h1, hv1⟩ := checkExpr_viol L c a
      obtain ⟨l2, h2, hv2⟩ := checkExpr_viol L (checkExpr L c a) b
      refine ⟨l1 ++ l2, by simp [checkExpr, h2, h1], ?_⟩
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact hv1 v hv
      · exact hv2 v hv

theorem checkExpr_stuck_mono (L : Bool) : ∀ (c : CState) (e : Expr), c.stuck = true →
    (checkExpr L c e).stuck = true
  | c, .lit _, h => h
  | c, .var x, h => by
      simp only [checkExpr]
      split
      · rfl
      · split <;> simp [CState.addV, h]
  | c, .deref r, h => useRef_stuck_mono r h
  | c, .add a b, h => checkExpr_stuck_mono L _ b (checkExpr_stuck_mono L c a h)

theorem viol_eq_of_append {l0 l1 l2 m : List Violation} (h1 : m = l0 ++ l1)
    (h2 : m ++ l2 = l0) : l1 = [] ∧ l2 = [] := by
  subst h1
  have := congrArg List.length h2
  rw [List.length_append, List.length_append] at this
  constructor
  · exact List.eq_nil_of_length_eq_zero (by omega)
  · exact List.eq_nil_of_length_eq_zero (by omega)

theorem checkExpr_clean (L : Bool) : ∀ (c : CState) (e : Expr),
    (checkExpr L c e).stuck = false → (checkExpr L c e).viol = c.viol →
    c.stuck = false ∧ ExprOK L c e
  | c, .lit _, hs, _ => ⟨hs, trivial⟩
  | c, .var x, hs, hv => by
      simp only [checkExpr] at hs hv
      cases L
      · simp [CState.setStuck] at hs
      · by_cases h : c.lent x
        · simp [h, CState.addV] at hv
        · simp [h] at hs
          exact ⟨hs, rfl, by simpa using h⟩
  | c, .deref r, hs, hv => by
      simp only [checkExpr] at hs hv
      obtain ⟨h1, h2⟩ := useRef_clean hs hv
      rw [h2] at hs
      exact ⟨hs, h1⟩
  | c, .add a b, hs, hv => by
      simp only [checkExpr] at hs hv
      obtain ⟨l1, h1, _⟩ := checkExpr_viol L c a
      obtain ⟨l2, h2, _⟩ := checkExpr_viol L (checkExpr L c a) b
      rw [h2] at hv
      obtain ⟨hl1, hl2⟩ := viol_eq_of_append h1 hv
      subst hl1 hl2
      have hsa : (checkExpr L c a).stuck = false := by
        cases h : (checkExpr L c a).stuck
        · rfl
        · rw [checkExpr_stuck_mono L _ b h] at hs; exact hs
      have ha := checkExpr_clean L c a hsa (by simpa using h1)
      have hb := checkExpr_clean L (checkExpr L c a) b hs (by simpa using h2)
      have hsh := checkExpr_shape L c a
      refine ⟨ha.1, ha.2, ?_⟩
      -- transport `ExprOK` along the unchanged shape
      have key : ∀ e, ExprOK L (checkExpr L c a) e → ExprOK L c e := by
        intro e
        induction e with
        | lit _ => intro h; exact h
        | var x => intro h; simpa [ExprOK, hsh.lent] using h
        | deref r => intro h; simpa [ExprOK, hsh.status] using h
        | add a b iha ihb => intro h; exact ⟨iha h.1, ihb h.2⟩
      exact key b hb.2

/-- A stuck check of an expression from a non-stuck state: the expression reads
a local in a callee frame, or dereferences an unbound reference variable. -/
def ExprStuck (L : Bool) (c : CState) : Expr → Prop
  | .lit _ => False
  | .var _ => L = false
  | .deref r => c.status r = .unborn
  | .add a b => ExprStuck L c a ∨ ExprStuck L c b

theorem checkExpr_stuck (L : Bool) : ∀ (c : CState) (e : Expr), c.stuck = false →
    (checkExpr L c e).stuck = true → ExprStuck L c e
  | c, .lit _, h, h' => by simp_all [checkExpr]
  | c, .var x, h, h' => by
      simp only [checkExpr] at h'
      cases L
      · rfl
      · by_cases hl : c.lent x <;> simp_all [CState.addV]
  | c, .deref r, h, h' => by
      simp only [checkExpr] at h'
      rw [useRef_stuck_iff] at h'
      simp_all [ExprStuck]
  | c, .add a b, h, h' => by
      simp only [checkExpr] at h'
      by_cases ha : (checkExpr L c a).stuck = true
      · exact Or.inl (checkExpr_stuck L c a h ha)
      · have ha' : (checkExpr L c a).stuck = false := by simpa using ha
        have hb := checkExpr_stuck L _ b ha' h'
        have hsh := checkExpr_shape L c a
        right
        have key : ∀ e, ExprStuck L (checkExpr L c a) e → ExprStuck L c e := by
          intro e
          induction e with
          | lit _ => intro h; exact h
          | var x => intro h; exact h
          | deref r => intro h; simpa [ExprStuck, hsh.status] using h
          | add a b iha ihb => intro h; exact h.elim (fun h => Or.inl (iha h)) (fun h => Or.inr (ihb h))
        exact key b hb

/-! ## Bound-name correspondence -/

/-- The checker's `unborn` statuses are exactly the unbound names of a semantic
state. -/
def BRel {α : Type} (st : RefVar → RStatus) (refs : RefVar → Option α) : Prop :=
  ∀ k, st k = .unborn ↔ refs k = none

theorem evalR_none_of_stuck {L : Bool} {c : CState} {s : RState}
    (hb : BRel c.status s.refs) : ∀ e, ExprStuck L c e → evalR L s e = none
  | .lit _, h => h.elim
  | .var _, h => by simp [ExprStuck] at h; simp [evalR, h]
  | .deref r, h => by simp [ExprStuck] at h; simp [evalR, (hb r).1 h]
  | .add a b, h => by
      rcases h with h | h
      · simp [evalR, evalR_none_of_stuck hb a h]
      · simp only [evalR, evalR_none_of_stuck hb b h]
        cases evalR L s a <;> rfl

theorem evalB_none_of_stuck {L : Bool} {c : CState} {s : BState}
    (hb : BRel c.status s.refs) : ∀ e, ExprStuck L c e → evalB L s e = none
  | .lit _, h => h.elim
  | .var _, h => by simp [ExprStuck] at h; simp [evalB, h]
  | .deref r, h => by simp [ExprStuck] at h; simp [evalB, (hb r).1 h]
  | .add a b, h => by
      rcases h with h | h
      · simp [evalB, evalB_none_of_stuck hb a h]
      · simp only [evalB, evalB_none_of_stuck hb b h]
        cases evalB L s a <;> rfl

theorem evalP_none_of_stuck {L : Bool} {c : CState} {s : PState}
    (hb : BRel c.status s.refs) : ∀ e, ExprStuck L c e → evalP L s e = none
  | .lit _, h => h.elim
  | .var _, h => by simp [ExprStuck] at h; simp [evalP, h]
  | .deref r, h => by simp [ExprStuck] at h; simp [evalP, (hb r).1 h]
  | .add a b, h => by
      rcases h with h | h
      · simp [evalP, evalP_none_of_stuck hb a h]
      · simp only [evalP, evalP_none_of_stuck hb b h]
        cases evalP L s a <;> rfl

end Sim
end Toy.Prophecy
