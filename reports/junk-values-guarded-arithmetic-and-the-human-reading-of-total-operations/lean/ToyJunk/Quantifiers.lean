import ToyJunk.Traps

/-!
# Result 6: quantifiers

Bounded quantifiers can supply guards. Under the `partialNat` reading, no formula is
human-false and Lean-true (or human-true and Lean-false): an unbounded quantifier over a
junk-dependent body can only turn a human-*undefined* statement into a Lean-true or
Lean-false one. Genuine flips between human truth and Lean truth occur under the
`intValued` reading of natural subtraction.
-/

namespace Toy.Junk

open Classical

theorem tvAll_eq_some_true_of {α : Type} {f : α → Option Bool} (h : ∀ v, f v = some true) :
    tvAll f = some true :=
  tvAll_eq_some_true.mpr h

theorem tvAll_eq_some_false_of {α : Type} {f : α → Option Bool} (h : ∃ v, f v = some false) :
    tvAll f = some false := by
  unfold tvAll
  have hn : ¬ ∀ v, f v = some true := by
    intro ha
    obtain ⟨v, hv⟩ := h
    rw [ha v] at hv
    cases hv
  simp only [hn, ↓reduceIte, h]

theorem tvAll_eq_none_of {α : Type} {f : α → Option Bool} (h : ∀ v, f v = none) [Inhabited α] :
    tvAll f = none := by
  unfold tvAll
  have h1 : ¬ ∀ v, f v = some true := fun ha => by
    have := ha default
    rw [h default] at this
    cases this
  have h2 : ¬ ∃ v, f v = some false := fun ⟨v, hv⟩ => by
    rw [h v] at hv
    cases hv
  simp only [h1, h2, ↓reduceIte]

theorem tvAll_eq_none_of_not {α : Type} {f : α → Option Bool} (h1 : ¬ ∀ v, f v = some true)
    (h2 : ¬ ∃ v, f v = some false) : tvAll f = none := by
  unfold tvAll
  simp only [h1, h2, ↓reduceIte]

/-- Human value of `a - b + b = a` under `partialNat`: true where `b ≤ a`, undefined
elsewhere. -/
theorem hEval_subAddCancel_partialNat (c : Conn) (ρ : Env) :
    hEval c .partialNat fSubAddCancel ρ = if ρ.nat 1 ≤ ρ.nat 0 then some true else none := by
  by_cases h : ρ.nat 1 ≤ ρ.nat 0
  · have h' : ((ρ.nat 1 : Nat) : Int) ≤ ρ.nat 0 := by omega
    simp [hEval, fSubAddCancel, hEvalT, obind2, hSub, hAtom, h, h']
  · have h' : ¬ ((ρ.nat 1 : Nat) : Int) ≤ ρ.nat 0 := by omega
    simp [hEval, fSubAddCancel, hEvalT, obind2, hSub, hAtom, h, h']

theorem tvEx_eq_none_of {α : Type} {f : α → Option Bool} (h : ∀ v, f v = none) [Inhabited α] :
    tvEx f = none := by
  unfold tvEx
  have h1 : ¬ ∃ v, f v = some true := fun ⟨v, hv⟩ => by
    rw [h v] at hv
    cases hv
  have h2 : ¬ ∀ v, f v = some false := fun ha => by
    have := ha default
    rw [h default] at this
    cases this
  simp only [h1, h2, ↓reduceIte]

/-- `∀ a, ∀ b ≤ a, a - b + b = a` at `Nat` (bounded inner quantifier). -/
def fBoundedCancel : Formula := .allNat 0 (ballNat 1 vA fSubAddCancel)

/-- `∀ a b, a - b + b = a` at `Nat` (unbounded). -/
def fUnboundedCancel : Formula := .allNat 0 (.allNat 1 fSubAddCancel)

/-- `∀ a, 0 ≤ a - 1` at `Nat`. -/
def fAllZeroLeSubOne : Formula := .allNat 0 (.le (.natLit 0) (.sub vA (.natLit 1)))

/-- `∀ a, a - (a + 1) = 0` at `Nat`. -/
def fAllSubSucc : Formula := .allNat 0 (.eq (.sub vA (.add vA (.natLit 1))) (.natLit 0))

/-- `∃ a, ¬ (a - (a + 1) = 0)` at `Nat`. -/
def fExSubSuccNe : Formula :=
  .exNat 0 (.not (.eq (.sub vA (.add vA (.natLit 1))) (.natLit 0)))

/-! ## The guard rule for `ballNat` -/

theorem contains_of_mem {Δ : List Formula} {f : Formula} (h : f ∈ Δ) : Δ.contains f = true := by
  simpa using h

/-- Term guardedness is monotone in the list of facts. -/
theorem Term.guardedIn_mono {Γ Δ : List Formula} (hsub : ∀ f ∈ Γ, f ∈ Δ) :
    ∀ {s : Srt} (t : Term s), t.guardedIn Γ = true → t.guardedIn Δ = true := by
  have hc : ∀ f, Γ.contains f = true → Δ.contains f = true :=
    fun f h => contains_of_mem (hsub f (mem_of_contains h))
  intro s t
  induction t with
  | natVar _ => intro _; rfl
  | intVar _ => intro _; rfl
  | natLit _ => intro _; rfl
  | intLit _ => intro _; rfl
  | add t u iht ihu =>
    intro hg
    simp only [Term.guardedIn, Bool.and_eq_true] at hg ⊢
    exact ⟨iht hg.1, ihu hg.2⟩
  | mul t u iht ihu =>
    intro hg
    simp only [Term.guardedIn, Bool.and_eq_true] at hg ⊢
    exact ⟨iht hg.1, ihu hg.2⟩
  | @sub s t u iht ihu =>
    cases s
    · intro hg
      simp only [Term.guardedIn, Bool.and_eq_true] at hg ⊢
      exact ⟨⟨iht hg.1.1, ihu hg.1.2⟩, hc _ hg.2⟩
    · intro hg
      simp only [Term.guardedIn, Bool.and_eq_true] at hg ⊢
      exact ⟨iht hg.1, ihu hg.2⟩
  | @div s t u iht ihu =>
    intro hg
    simp only [Term.guardedIn, Bool.and_eq_true] at hg ⊢
    exact ⟨⟨⟨iht hg.1.1.1, ihu hg.1.1.2⟩, hc _ hg.1.2⟩, hc _ hg.2⟩
  | @mod s t u iht ihu =>
    cases s
    · intro hg
      simp only [Term.guardedIn, Bool.and_eq_true] at hg ⊢
      exact ⟨⟨iht hg.1.1, ihu hg.1.2⟩, hc _ hg.2⟩
    · intro hg
      simp only [Term.guardedIn, Bool.and_eq_true] at hg ⊢
      exact ⟨⟨⟨iht hg.1.1.1, ihu hg.1.1.2⟩, hc _ hg.1.2⟩, hc _ hg.2⟩
  | cast t iht => intro hg; exact iht hg
  | toNat t iht =>
    intro hg
    simp only [Term.guardedIn, Bool.and_eq_true] at hg ⊢
    exact ⟨iht hg.1, hc _ hg.2⟩

/-- If a term does not mention natural variable `x`, no fact it requires mentions `x`, so
filtering out the facts that mention `x` preserves its guardedness. -/
theorem Term.guardedIn_filter_of_not_mentionsNat (Γ : List Formula) (x : Nat) :
    ∀ {s : Srt} (t : Term s), t.mentionsNat x = false → t.guardedIn Γ = true →
      t.guardedIn (Γ.filter fun f => !f.mentionsNat x) = true := by
  intro s t
  induction t with
  | natVar i => intros; rfl
  | intVar i => intros; rfl
  | natLit n => intros; rfl
  | intLit z => intros; rfl
  | add t u iht ihu | mul t u iht ihu =>
    intro hm hg
    simp only [Term.mentionsNat, Bool.or_eq_false_iff] at hm
    simp only [Term.guardedIn, Bool.and_eq_true] at hg ⊢
    exact ⟨iht hm.1 hg.1, ihu hm.2 hg.2⟩
  | @sub s t u iht ihu =>
    cases s
    · intro hm hg
      simp only [Term.mentionsNat, Bool.or_eq_false_iff] at hm
      simp only [Term.guardedIn, Bool.and_eq_true] at hg ⊢
      refine ⟨⟨iht hm.1 hg.1.1, ihu hm.2 hg.1.2⟩, ?_⟩
      simp only [List.contains_iff_mem, List.mem_filter]
      exact ⟨mem_of_contains hg.2, by simp [Formula.mentionsNat, hm.1, hm.2]⟩
    · intro hm hg
      simp only [Term.mentionsNat, Bool.or_eq_false_iff] at hm
      simp only [Term.guardedIn, Bool.and_eq_true] at hg ⊢
      exact ⟨iht hm.1 hg.1, ihu hm.2 hg.2⟩
  | @div s t u iht ihu =>
    intro hm hg
    simp only [Term.mentionsNat, Bool.or_eq_false_iff] at hm
    simp only [Term.guardedIn, Bool.and_eq_true] at hg ⊢
    have hz : (zeroOf s).mentionsNat x = false := by cases s <;> rfl
    refine ⟨⟨⟨iht hm.1 hg.1.1.1, ihu hm.2 hg.1.1.2⟩, ?_⟩, ?_⟩
    · simp only [List.contains_iff_mem, List.mem_filter]
      exact ⟨mem_of_contains hg.1.2, by simp [Formula.mentionsNat, hm.2, hz]⟩
    · simp only [List.contains_iff_mem, List.mem_filter]
      exact ⟨mem_of_contains hg.2, by simp [Formula.mentionsNat, hm.1, hm.2]⟩
  | @mod s t u iht ihu =>
    cases s
    · intro hm hg
      simp only [Term.mentionsNat, Bool.or_eq_false_iff] at hm
      simp only [Term.guardedIn, Bool.and_eq_true] at hg ⊢
      refine ⟨⟨iht hm.1 hg.1.1, ihu hm.2 hg.1.2⟩, ?_⟩
      simp only [List.contains_iff_mem, List.mem_filter]
      exact ⟨mem_of_contains hg.2, by simp [Formula.mentionsNat, hm.2, Term.mentionsNat]⟩
    · intro hm hg
      simp only [Term.mentionsNat, Bool.or_eq_false_iff] at hm
      simp only [Term.guardedIn, Bool.and_eq_true] at hg ⊢
      refine ⟨⟨⟨iht hm.1 hg.1.1.1, ihu hm.2 hg.1.1.2⟩, ?_⟩, ?_⟩
      · simp only [List.contains_iff_mem, List.mem_filter]
        exact ⟨mem_of_contains hg.1.2, by simp [Formula.mentionsNat, hm.2, Term.mentionsNat]⟩
      · simp only [List.contains_iff_mem, List.mem_filter]
        exact ⟨mem_of_contains hg.2, by simp [Formula.mentionsNat, hm.1, Term.mentionsNat]⟩
  | cast t iht =>
    intro hm hg
    exact iht hm hg
  | toNat t iht =>
    intro hm hg
    simp only [Term.mentionsNat] at hm
    simp only [Term.guardedIn, Bool.and_eq_true] at hg ⊢
    refine ⟨iht hm hg.1, ?_⟩
    simp only [List.contains_iff_mem, List.mem_filter]
    exact ⟨mem_of_contains hg.2, by simp [Formula.mentionsNat, hm, Term.mentionsNat]⟩

/-- **Guard rule for bounded quantifiers.** For every list of facts `Γ`, natural variable
`x`, bound term `t` that does not mention `x`, and body `φ`: `ballNat x t φ`
(`∀ x, x ≤ t → φ`) is accepted relative to `Γ` iff `t` is guarded by `Γ` and `φ` is guarded
by the facts of `Γ` that do not mention `x` together with the fact `x ≤ t`. -/
theorem ballNat_guardedIn_iff_of_not_mentionsNat (Γ : List Formula) (x : Nat) (t : Term .nat)
    (φ : Formula) (hm : t.mentionsNat x = false) :
    (ballNat x t φ).guardedIn Γ = true ↔
      t.guardedIn Γ = true ∧
        φ.guardedIn ((Γ.filter fun f => !f.mentionsNat x) ++ [.le (.natVar x) t]) = true := by
  simp only [ballNat, Formula.guardedIn, Term.guardedIn, Bool.true_and, Formula.facts,
    Bool.and_eq_true]
  constructor
  · rintro ⟨ht, hφ⟩
    exact ⟨Term.guardedIn_mono (fun f hf => (List.mem_filter.mp hf).1) t ht, hφ⟩
  · rintro ⟨ht, hφ⟩
    exact ⟨Term.guardedIn_filter_of_not_mentionsNat Γ x t hm ht, hφ⟩

/-- Tightness of `t.mentionsNat x = false` in `ballNat_guardedIn_iff_of_not_mentionsNat`
(canonical form): with `Γ = [a ≤ b]`, `x = a` and bound `t = b - a` (which mentions `a`),
the equivalence fails: the right side holds while `ballNat` is rejected, because inside the
quantifier `a` is rebound. With sequential connectives the formula is human-undefined at
`a = b = 0`. -/
theorem ce_ballNat_bound_mentions_var :
    (Term.sub vB vA).mentionsNat 0 = true ∧
      ¬ ((ballNat 0 (.sub vB vA) (.eq (.natLit 0) (.natLit 0))).guardedIn [.le vA vB] = true ↔
        (Term.sub vB vA).guardedIn [.le vA vB] = true ∧
          (Formula.eq (.natLit 0) (.natLit 0)).guardedIn
            (([.le vA vB] : List Formula).filter (fun f => !f.mentionsNat 0) ++
              [.le (.natVar 0) (.sub vB vA)]) = true) ∧
      hEval .seq .partialNat (ballNat 0 (.sub vB vA) (.eq (.natLit 0) (.natLit 0))) (envAB 0 0) =
        none := by
  refine ⟨by decide, by decide, ?_⟩
  simp only [hEval, ballNat]
  apply tvAll_eq_none_of_not
  · intro ha
    have h1 := ha 1
    revert h1
    decide
  · rintro ⟨v, hv⟩
    by_cases hv0 : v = 0
    · subst hv0; revert hv; decide
    · simp [hEvalT, obind2, hSub, hAtom, tvImp, tvOr, tvNot, Env.setNat, envAB, hv0] at hv

/-- Non-vacuity of `ballNat_guardedIn_iff_of_not_mentionsNat`: the bound `a` does not
mention the bound variable `b`, and `∀ b ≤ a, a - b + b = a` is accepted with no facts. -/
theorem nv_ballNat_guardedIn_iff : (vA : Term .nat).mentionsNat 1 = false ∧
    (ballNat 1 vA fSubAddCancel).guardedIn [] = true ∧
    fSubAddCancel.guardedIn (([] : List Formula).filter (fun f => !f.mentionsNat 1) ++
      [.le (.natVar 1) vA]) = true := by
  decide

/-- **Strict bounds are not recognized.** `∀ a b, b < a → a - b + b = a` and
`∀ a b, b < a + 1 → a - b + b = a` (at `Nat`) are Lean-valid but rejected by the checker,
which matches only the fact `b ≤ a`. -/
theorem guarded_rejects_strict_bound :
    (guarded (.allNat 0 (.allNat 1 (.imp (.lt vB vA) fSubAddCancel))) = false ∧
        LeanValid (.allNat 0 (.allNat 1 (.imp (.lt vB vA) fSubAddCancel)))) ∧
      (guarded (.allNat 0 (.allNat 1 (.imp (.lt vB (.add vA (.natLit 1))) fSubAddCancel))) = false ∧
        LeanValid (.allNat 0 (.allNat 1 (.imp (.lt vB (.add vA (.natLit 1))) fSubAddCancel)))) := by
  refine ⟨⟨by decide, ?_⟩, ⟨by decide, ?_⟩⟩
  · intro ρ
    rw [evalJ_leanJ_iff]
    intro v w
    show ((ρ.setNat 0 v).setNat 1 w).nat 1 < ((ρ.setNat 0 v).setNat 1 w).nat 0 →
      ((ρ.setNat 0 v).setNat 1 w).nat 0 - ((ρ.setNat 0 v).setNat 1 w).nat 1 +
        ((ρ.setNat 0 v).setNat 1 w).nat 1 = ((ρ.setNat 0 v).setNat 1 w).nat 0
    simp only [Env.setNat]
    simp
    omega
  · intro ρ
    rw [evalJ_leanJ_iff]
    intro v w
    show ((ρ.setNat 0 v).setNat 1 w).nat 1 < ((ρ.setNat 0 v).setNat 1 w).nat 0 + 1 →
      ((ρ.setNat 0 v).setNat 1 w).nat 0 - ((ρ.setNat 0 v).setNat 1 w).nat 1 +
        ((ρ.setNat 0 v).setNat 1 w).nat 1 = ((ρ.setNat 0 v).setNat 1 w).nat 0
    simp only [Env.setNat]
    simp
    omega

/-- **Instance: a bounded inner quantifier.** For every connective semantics and reading,
`∀ a, ∀ b ≤ a, a - b + b = a` is accepted by the checker, Lean-valid, and human-valid. -/
theorem boundedCancel_guarded_leanValid_humanValid (c : Conn) (r : SubReading) :
    guarded fBoundedCancel = true ∧ LeanValid fBoundedCancel ∧ HumanValid c r fBoundedCancel := by
  have hg : guarded fBoundedCancel = true := by decide
  have hv : LeanValid fBoundedCancel := by
    intro ρ
    rw [evalJ_leanJ_iff]
    intro v w
    show ((ρ.setNat 0 v).setNat 1 w).nat 1 ≤ ((ρ.setNat 0 v).setNat 1 w).nat 0 →
      ((ρ.setNat 0 v).setNat 1 w).nat 0 - ((ρ.setNat 0 v).setNat 1 w).nat 1 +
        ((ρ.setNat 0 v).setNat 1 w).nat 1 = ((ρ.setNat 0 v).setNat 1 w).nat 0
    simp only [Env.setNat]
    simp
    omega
  exact ⟨hg, hv, (leanValid_iff_humanValid_of_guarded c r _ hg).mp hv⟩

/-- **Without the bound.** `∀ a b, a - b + b = a` is rejected by the checker, Lean-false,
undefined under `partialNat`, and human-true under `intValued`. -/
theorem ce_unbounded_cancel (c : Conn) :
    guarded fUnboundedCancel = false ∧ evalJ leanJ fUnboundedCancel Env.zero = false ∧
      hEval c .partialNat fUnboundedCancel Env.zero = none ∧
      hEval c .intValued fUnboundedCancel Env.zero = some true := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · cases h : evalJ leanJ fUnboundedCancel Env.zero
    · rfl
    · simp only [fUnboundedCancel, evalJ] at h
      have := of_decide_eq_true (of_decide_eq_true h 0) 1
      revert this
      decide
  · -- Undefined at `a = 0, b = 1`, and never false (true or undefined elsewhere).
    simp only [hEval, fUnboundedCancel]
    apply tvAll_eq_none_of_not
    · intro ha
      have h0 := tvAll_eq_some_true.mp (ha 0) 1
      rw [hEval_subAddCancel_partialNat] at h0
      revert h0
      decide
    · rintro ⟨v, hv⟩
      obtain ⟨w, hw⟩ := tvAll_eq_some_false hv
      rw [hEval_subAddCancel_partialNat] at hw
      split at hw <;> cases hw
  · apply tvAll_eq_some_true_of
    intro v
    apply tvAll_eq_some_true_of
    intro w
    cases c <;> simp [hEval, fSubAddCancel, hEvalT, obind2, hSub, hAtom]

/-- A human-false formula under `partialNat`: `5 - 3 = 3` (at `Nat`). -/
theorem nv_hEval_eq_some_false_partialNat (c : Conn) :
    hEval c .partialNat (.eq (.sub (.natLit 5) (.natLit 3)) (.natLit 3)) Env.zero = some false := by
  cases c <;> decide

/-- **Flip under `intValued`, human-false and Lean-true** (tightness of the `partialNat`
reading in `no_flip_partialNat`). `∀ a, 0 ≤ a - 1` is human-false under `intValued` (at `a = 0`, `0 - 1 = -1`) and
Lean-true. -/
theorem ce_intValued_forall_humanFalse_leanTrue (c : Conn) :
    hEval c .intValued fAllZeroLeSubOne Env.zero = some false ∧
      evalJ leanJ fAllZeroLeSubOne Env.zero = true := by
  constructor
  · apply tvAll_eq_some_false_of
    exact ⟨0, by cases c <;> decide⟩
  · rw [evalJ_leanJ_iff]
    intro v
    exact Nat.zero_le _

/-- **Flip under `intValued`, human-true and Lean-false.** `∀ a b, a - b + b = a` is
human-true under `intValued` and Lean-false. -/
theorem ce_intValued_forall_humanTrue_leanFalse (c : Conn) :
    hEval c .intValued fUnboundedCancel Env.zero = some true ∧
      evalJ leanJ fUnboundedCancel Env.zero = false :=
  ⟨(ce_unbounded_cancel c).2.2.2, (ce_unbounded_cancel c).2.1⟩

/-- **Undefined to Lean-true under `partialNat`.** `∀ a, a - (a + 1) = 0` is undefined in
the `partialNat` reading (every instance is undefined), true in Lean, and false for the
junk record `oneJ`. -/
theorem ce_partialNat_forall_undefined_leanTrue (c : Conn) :
    hEval c .partialNat fAllSubSucc Env.zero = none ∧ evalJ leanJ fAllSubSucc Env.zero = true ∧
      evalJ oneJ fAllSubSucc Env.zero = false := by
  refine ⟨?_, ?_, ?_⟩
  · apply tvAll_eq_none_of
    intro v
    have : ¬ ((v : Int) + 1 ≤ v) := by omega
    cases c <;> simp [hEval, hEvalT, obind2, hSub, hAtom, Env.setNat, this]
  · rw [evalJ_leanJ_iff]
    intro v
    show (Env.zero.setNat 0 v).nat 0 - ((Env.zero.setNat 0 v).nat 0 + 1) = 0
    omega
  · cases h : evalJ oneJ fAllSubSucc Env.zero
    · rfl
    · simp only [fAllSubSucc, evalJ] at h
      have := of_decide_eq_true h 0
      revert this
      decide

/-- **Undefined to Lean-false under `partialNat`.** `∃ a, ¬ (a - (a + 1) = 0)` is undefined
in the `partialNat` reading, false in Lean, and true for the junk record `oneJ`. -/
theorem ce_partialNat_exists_undefined_leanFalse (c : Conn) :
    hEval c .partialNat fExSubSuccNe Env.zero = none ∧
      evalJ leanJ fExSubSuccNe Env.zero = false ∧ evalJ oneJ fExSubSuccNe Env.zero = true := by
  refine ⟨?_, ?_, ?_⟩
  · apply tvEx_eq_none_of
    intro v
    have : ¬ ((v : Int) + 1 ≤ v) := by omega
    cases c <;> simp [hEval, hEvalT, obind2, hSub, hAtom, tvNot, Env.setNat, this]
  · cases h : evalJ leanJ fExSubSuccNe Env.zero
    · rfl
    · obtain ⟨v, hv⟩ := (evalJ_leanJ_iff _ _).mp h
      have h0 : (Env.zero.setNat 0 v).nat 0 - ((Env.zero.setNat 0 v).nat 0 + 1) = 0 := by omega
      exact absurd h0 hv
  · simp only [fExSubSuccNe, evalJ]
    exact decide_eq_true ⟨0, by decide⟩

/-- `1 / 2 = 0` at `Nat`. -/
def fOneDivTwo : Formula := .eq (.div (.natLit 1) (.natLit 2)) (.natLit 0)

/-- `∀ n, 2 < n → 1 / n = 0` at `Nat`. -/
def fAllOneDivZero : Formula :=
  .allNat 0 (.imp (.lt (.natLit 2) vA) (.eq (.div (.natLit 1) vA) (.natLit 0)))

/-- **Inexact quotients are undefined, not false.** For every connective semantics and
reading, `1 / 2 = 0` and `∀ n, 2 < n → 1 / n = 0` (at `Nat`) are true in Lean's reading and
human-undefined in this package's reading of `/` (exact quotient or undefined). -/
theorem inexact_quotient_undefined_leanTrue (c : Conn) (r : SubReading) :
    hEval c r fOneDivTwo Env.zero = none ∧ evalJ leanJ fOneDivTwo Env.zero = true ∧
      hEval c r fAllOneDivZero Env.zero = none ∧ evalJ leanJ fAllOneDivZero Env.zero = true := by
  have hbody : ∀ v : Nat, hEval c r (.imp (.lt (.natLit 2) vA) (.eq (.div (.natLit 1) vA) (.natLit 0)))
      (Env.zero.setNat 0 v) = if 2 < v then none else some true := by
    intro v
    by_cases hv : 2 < v
    · have hnd : ¬ DivDom 1 (v : Int) := by
        rintro ⟨_, hd⟩
        have := Int.le_of_dvd (by decide) hd
        omega
      have hlt : (2 : Int) < (v : Int) := by omega
      simp only [hv, ↓reduceIte]
      simp [hEval, hEvalT, obind2, hDiv, hnd, hAtom, Env.setNat, Env.zero, hlt]
      cases c <;> rfl
    · have hnlt : ¬ (2 : Int) < (v : Int) := by omega
      simp only [hv, ↓reduceIte]
      simp [hEval, hEvalT, hAtom, Env.setNat, Env.zero, hnlt, tvImp_some_false]
  refine ⟨by cases c <;> cases r <;> decide, by decide, ?_, ?_⟩
  · show tvAll (fun v : Nat => hEval c r
        (.imp (.lt (.natLit 2) vA) (.eq (.div (.natLit 1) vA) (.natLit 0))) (Env.zero.setNat 0 v)) = none
    rw [show (fun v : Nat => hEval c r
        (.imp (.lt (.natLit 2) vA) (.eq (.div (.natLit 1) vA) (.natLit 0))) (Env.zero.setNat 0 v)) =
        fun v => if 2 < v then none else some true from funext hbody]
    apply tvAll_eq_none_of_not
    · intro ha
      have h3 := ha 3
      simp at h3
    · rintro ⟨v, hv⟩
      split at hv <;> cases hv
  · rw [evalJ_leanJ_iff]
    intro v
    show 2 < (Env.zero.setNat 0 v).nat 0 → 1 / (Env.zero.setNat 0 v).nat 0 = 0
    simp only [Env.setNat, ↓reduceIte]
    intro h
    exact Nat.div_eq_of_lt (by omega)

end Toy.Junk
