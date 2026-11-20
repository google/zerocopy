import ToyProphecy.Sim.PFacts

/-!
# Proof infrastructure: checker steps that record no violation

Auxiliary lemmas used only inside proofs of the main statements.
-/

namespace Toy.Prophecy
namespace Sim

open CState

theorem cstate_ext {c c' : CState} (h : SameShape c c') (hv : c'.viol = c.viol)
    (hs : c'.stuck = c.stuck) : c' = c := by
  cases c; cases c'
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp_all

theorem checkExpr_clean_eq {L : Bool} {c : CState} {e : Expr}
    (hs : (checkExpr L c e).stuck = false) (hv : (checkExpr L c e).viol = c.viol) :
    ExprOK L c e ∧ checkExpr L c e = c := by
  obtain ⟨hc, hok⟩ := checkExpr_clean L c e hs hv
  exact ⟨hok, cstate_ext (checkExpr_shape L c e) hv (by rw [hs, hc])⟩

theorem append_eq_self {l l' : List Violation} (h : l ++ l' = l) : l' = [] := by
  have := congrArg List.length h
  rw [List.length_append] at this
  exact List.eq_nil_of_length_eq_zero (by omega)

theorem viol_prefix_eq {l l1 l2 : List Violation} (h : (l ++ l1) ++ l2 = l) : l1 = [] ∧ l2 = [] := by
  have := congrArg List.length h
  rw [List.length_append, List.length_append] at this
  exact ⟨List.eq_nil_of_length_eq_zero (by omega), List.eq_nil_of_length_eq_zero (by omega)⟩

theorem clean_assign {c : CState} {x : Var} {e : Expr}
    (hs : (checkOp true c (.assign x e)).stuck = false)
    (hv : (checkOp true c (.assign x e)).viol = c.viol) :
    ExprOK true c e ∧ c.lent x = false ∧ checkOp true c (.assign x e) = c := by
  have hc := (checkOp_ns_cases hs).1
  simp only [checkOp, hc, Bool.false_eq_true, ↓reduceIte, Bool.not_true] at hs hv ⊢
  obtain ⟨l, hl, -⟩ := checkExpr_viol true c e
  have hsh := checkExpr_shape true c e
  by_cases hx : (checkExpr true c e).lent x = true
  · simp only [hx, ↓reduceIte, CState.addV] at hv
    rw [hl] at hv
    have := congrArg List.length hv
    simp at this
  · simp only [hx, Bool.false_eq_true, ↓reduceIte] at hs hv ⊢
    obtain ⟨hok, heq⟩ := checkExpr_clean_eq hs hv
    refine ⟨hok, ?_, heq⟩
    rw [heq] at hx; simpa using hx

theorem clean_write {L : Bool} {c : CState} {r : RefVar} {e : Expr}
    (hs : (checkOp L c (.write r e)).stuck = false)
    (hv : (checkOp L c (.write r e)).viol = c.viol) :
    ExprOK L c e ∧ c.status r = .active ∧ checkOp L c (.write r e) = c := by
  have hc := (checkOp_ns_cases hs).1
  have hes := (checkOp_ns_cases hs).2.1
  simp only [checkOp, hc, hes, Bool.false_eq_true, ↓reduceIte] at hs hv ⊢
  obtain ⟨l, hl, -⟩ := checkExpr_viol L c e
  obtain ⟨l2, hl2, -⟩ := useRef_viol (checkExpr L c e) r
  rw [hl2, hl] at hv
  obtain ⟨h1, h2⟩ := viol_prefix_eq hv
  subst h1 h2
  obtain ⟨hok, heq⟩ := checkExpr_clean_eq hes (by simpa using hl)
  rw [heq] at hs hl2 ⊢
  obtain ⟨hr, hu⟩ := useRef_clean hs (by simpa using hl2)
  exact ⟨hok, hr, hu⟩

theorem clean_reborrow {L : Bool} {c : CState} {t r : RefVar}
    (hs : (checkOp L c (.reborrow t r)).stuck = false)
    (hv : (checkOp L c (.reborrow t r)).viol = c.viol) :
    c.status r = .active ∧ c.status t = .unborn ∧
    checkOp L c (.reborrow t r) =
      { c with status := upd (upd c.status r .frozen) t .active,
               lender := upd c.lender t (some (.ref r)), bound := c.bound ++ [t] } := by
  have hc := (checkOp_ns_cases hs).1
  have hr0 := (checkOp_ns_cases hs).2
  have hus : (c.useRef r).stuck = false := by rw [useRef_stuck_iff]; simp [hc, hr0]
  simp only [checkOp, hc, hus, Bool.false_eq_true, ↓reduceIte] at hs hv ⊢
  obtain ⟨l, hl, -⟩ := useRef_viol c r
  obtain ⟨l2, hl2, -⟩ := bindRef_viol (c.useRef r) t
  rw [hl2, hl] at hv
  obtain ⟨h1, h2⟩ := viol_prefix_eq hv
  subst h1 h2
  obtain ⟨hr, hu⟩ := useRef_clean hus (by simpa using hl)
  rw [hu] at hl2 ⊢
  obtain ⟨ht, hb⟩ := bindRef_clean (by simpa using hl2)
  refine ⟨hr, ht, ?_⟩
  rw [hb]
  simp [hr, hc]

theorem clean_endBorrow {L : Bool} {c : CState} {r : RefVar}
    (hs : (checkOp L c (.endBorrow r)).stuck = false)
    (hv : (checkOp L c (.endBorrow r)).viol = c.viol) :
    c.status r = .active ∧
    checkOp L c (.endBorrow r) = { c.release r with status := upd (c.release r).status r .ended } := by
  have hc := (checkOp_ns_cases hs).1
  have hr0 := (checkOp_ns_cases hs).2
  have hus : (c.useRef r).stuck = false := by rw [useRef_stuck_iff]; simp [hc, hr0]
  obtain ⟨l, hl, -⟩ := useRef_viol c r
  have hcl : (c.useRef r).viol = c.viol := by
    simp only [checkOp, hc, hus, Bool.false_eq_true, ↓reduceIte] at hv
    split at hv
    · exact hv
    · rw [release_viol] at hv; exact hv
  obtain ⟨hr, hu⟩ := useRef_clean hus hcl
  refine ⟨hr, ?_⟩
  simp only [checkOp, hc, Bool.false_eq_true, ↓reduceIte, hu, hr]
  simp

theorem clean_borrow {c : CState} {r : RefVar} {x : Var}
    (hs : (checkOp true c (.borrow r x)).stuck = false)
    (hv : (checkOp true c (.borrow r x)).viol = c.viol) :
    c.lent x = false ∧ c.status r = .unborn ∧
    checkOp true c (.borrow r x) =
      { c with lent := upd c.lent x true, status := upd c.status r .active,
               lender := upd c.lender r (some (.loc x)), bound := c.bound ++ [r] } := by
  have hc := (checkOp_ns_cases hs).1
  simp only [checkOp, hc, Bool.false_eq_true, ↓reduceIte, Bool.not_true] at hs hv ⊢
  by_cases hx : c.lent x = true
  · simp only [hx, ↓reduceIte] at hv
    obtain ⟨l2, hl2, -⟩ := bindRef_viol (c.addV .lentAccess) r
    rw [hl2] at hv
    have := congrArg List.length hv
    simp [CState.addV] at this
  · simp only [hx, Bool.false_eq_true, ↓reduceIte] at hv ⊢
    obtain ⟨ht, hb⟩ := bindRef_clean hv
    refine ⟨by simp, ht, ?_⟩
    rw [hb]; simp [hc]

theorem clean_borrowSel {c : CState} {r : RefVar} {e : Expr} {x y : Var}
    (hs : (checkOp true c (.borrowSel r e x y)).stuck = false)
    (hv : (checkOp true c (.borrowSel r e x y)).viol = c.viol) :
    ExprOK true c e ∧ c.lent x = false ∧ c.lent y = false ∧ c.status r = .unborn ∧
    checkOp true c (.borrowSel r e x y) =
      { c with lent := upd (upd c.lent x true) y true, status := upd c.status r .active,
               lender := upd c.lender r (some (.sel x y)), bound := c.bound ++ [r] } := by
  have hc := (checkOp_ns_cases hs).1
  have hes := (checkOp_ns_cases hs).2.2
  simp only [checkOp, hc, Bool.false_eq_true, ↓reduceIte, Bool.not_true] at hs hv ⊢
  obtain ⟨l, hl, -⟩ := checkExpr_viol true c e
  by_cases hx : ((checkExpr true c e).lent x || (checkExpr true c e).lent y) = true
  · simp only [hx, ↓reduceIte] at hv
    obtain ⟨l2, hl2, -⟩ := bindRef_viol ((checkExpr true c e).addV .lentAccess) r
    rw [hl2] at hv
    simp only [CState.addV] at hv
    rw [hl] at hv
    have := congrArg List.length hv
    simp at this
  · simp only [hx, Bool.false_eq_true, ↓reduceIte] at hv ⊢
    obtain ⟨l2, hl2, -⟩ := bindRef_viol (checkExpr true c e) r
    rw [hl2, hl] at hv
    obtain ⟨h1, h2⟩ := viol_prefix_eq hv
    subst h1 h2
    obtain ⟨hok, heq⟩ := checkExpr_clean_eq hes (by simpa using hl)
    rw [heq] at hl2 hx ⊢
    obtain ⟨ht, hb⟩ := bindRef_clean (by simpa using hl2)
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hx
    refine ⟨hok, hx.1, hx.2, ht, ?_⟩
    rw [hb]; simp [hc]

theorem clean_call {c : CState} {t r : RefVar} {f : Callee}
    (hs : (checkStmt c (.call t f r)).stuck = false)
    (hv : (checkStmt c (.call t f r)).viol = c.viol) :
    c.stuck = false ∧ c.status r = .active ∧ (checkCallee f).stuck = false ∧
    (checkCallee f).viol = [] ∧ c.status t = .unborn ∧
    checkStmt c (.call t f r) =
      { c with status := upd (upd c.status r .frozen) t .active,
               lender := upd c.lender t (some (.ref r)), bound := c.bound ++ [t] } := by
  have hc : c.stuck = false := by
    cases hc : c.stuck
    · rfl
    · simp [checkStmt, hc] at hs
  have hus : (c.useRef r).stuck = false := by
    cases h : (c.useRef r).stuck
    · rfl
    · simp [checkStmt, hc, h] at hs
  have hcf : (checkCallee f).stuck = false := by
    cases h : (checkCallee f).stuck
    · rfl
    · simp [checkStmt, hc, hus, h, CState.setStuck] at hs
  have hlenB : ∀ (X : CState), X.viol.length ≤ (X.bindRef t).viol.length := by
    intro X; unfold CState.bindRef; split <;> simp [CState.addV]
  have hr : c.status r = .active := by
    cases h : c.status r
    · rw [useRef_unborn h] at hus; simp [CState.setStuck] at hus
    · rfl
    all_goals
      exfalso
      simp only [checkStmt, hc, hus, hcf, Bool.false_eq_true, ↓reduceIte] at hv
      simp only [h, CState.useRef, CState.addV] at hv
      unfold CState.bindRef at hv
      split at hv <;> (have := congrArg List.length hv; simp [CState.addV] at this)
  have hu := useRef_active hr
  simp only [checkStmt, hc, hu, hcf, Bool.false_eq_true, ↓reduceIte] at hv ⊢
  unfold CState.bindRef at hv ⊢
  by_cases ht : c.status t = .unborn
  · simp only [ht, ↓reduceIte] at hv ⊢
    have h2 : (checkCallee f).viol = [] := append_eq_self hv
    refine ⟨?_, hr, ?_, h2, ?_, ?_⟩
    all_goals first | trivial | exact hc | exact hcf | exact ht | simp [h2, hr]
  · exfalso
    simp only [ht, ↓reduceIte, CState.addV] at hv
    have := congrArg List.length hv
    simp at this

end Sim
end Toy.Prophecy
