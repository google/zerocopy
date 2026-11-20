import ToySemType.Concrete

/-!
# Results

Main results: adequacy, the fundamental theorem, and semantic
let-compatibility (linking), with their corollaries (syntactic type safety and
the encapsulation principle); the concrete encapsulated library; the absence
of a semantic type for `cast` of an `int` variable; ablations of the semantic
model; tightness counterexamples; non-vacuity witnesses; and boundary facts
used by the non-claims.
-/

namespace Toy.SemType

open Expr

/-- Close a goal `Reaches c d` between concrete configurations by computing steps. -/
macro "reach" : tactic =>
  `(tactic| repeat (first | exact Reaches.refl _ | refine Reaches.step rfl ?_))

/-! ## Kripke monotonicity of the standard value interpretation -/

/-- **Kripke monotonicity.** In the standard model, a value in the
interpretation of `τ` at world `W` stays there in every larger world. -/
theorem V_std_mono {τ : Ty} {W W' : Nat} {v : Expr} (hW : W ≤ W')
    (h : V Recipe.std τ W v) : V Recipe.std τ W' v := by
  cases τ with
  | int => exact h
  | ref =>
    obtain ⟨l, rfl, hl⟩ := h
    exact ⟨l, rfl, Nat.lt_of_lt_of_le hl hW⟩
  | arrow σ τ =>
    obtain ⟨b, rfl, hb, hf⟩ := h
    exact ⟨b, rfl, hb, fun W'' hW'' => hf W'' (Nat.le_trans hW hW'')⟩

/-! ## Proof infrastructure for the main results

Heap monotonicity of reduction, closing-substitution facts, and an
evaluation-context bind lemma. These are used only inside the proofs of the
main results below. -/

/-- One reduction step never shrinks the heap. -/
theorem step_heap_mono {e e' : Expr} {h h' : Heap} (hs : step e h = some (e', h')) :
    h.length ≤ h'.length := by
  induction e generalizing e' h' with
  | var _ | lam _ | num _ | loc _ => simp [step] at hs
  | size => simp [step] at hs; obtain ⟨_, rfl⟩ := hs; exact Nat.le_refl _
  | app f a ihf iha =>
    simp only [step] at hs
    split at hs
    · split at hs
      · cases f <;> simp at hs; obtain ⟨_, rfl⟩ := hs; exact Nat.le_refl _
      · obtain ⟨c, hc, rfl, rfl⟩ := Option.map_eq_some_iff.mp hs; exact iha hc
    · obtain ⟨c, hc, rfl, rfl⟩ := Option.map_eq_some_iff.mp hs; exact ihf hc
  | lt a b iha ihb =>
    simp only [step] at hs
    split at hs
    · split at hs
      · cases a <;> cases b <;> simp at hs; obtain ⟨_, rfl⟩ := hs; exact Nat.le_refl _
      · obtain ⟨c, hc, rfl, rfl⟩ := Option.map_eq_some_iff.mp hs; exact ihb hc
    · obtain ⟨c, hc, rfl, rfl⟩ := Option.map_eq_some_iff.mp hs; exact iha hc
  | ifz c t e ihc _ _ =>
    simp only [step] at hs
    split at hs
    · cases c with
      | num n =>
        cases n <;> simp at hs <;> obtain ⟨_, rfl⟩ := hs <;> exact Nat.le_refl _
      | _ => simp at hs
    · obtain ⟨d, hd, rfl, rfl⟩ := Option.map_eq_some_iff.mp hs; exact ihc hd
  | alloc a ih =>
    simp only [step] at hs
    split at hs
    · cases a <;> simp at hs; obtain ⟨_, rfl⟩ := hs; simp
    · obtain ⟨c, hc, rfl, rfl⟩ := Option.map_eq_some_iff.mp hs; exact ih hc
  | read a ih =>
    simp only [step] at hs
    split at hs
    · cases a with
      | loc l =>
        cases hget : h[l]? <;> simp [hget] at hs; obtain ⟨_, rfl⟩ := hs; exact Nat.le_refl _
      | _ => simp at hs
    · obtain ⟨c, hc, rfl, rfl⟩ := Option.map_eq_some_iff.mp hs; exact ih hc
  | write a b iha ihb =>
    simp only [step] at hs
    split at hs
    · split at hs
      · cases a <;> cases b <;> simp at hs
        obtain ⟨_, _, rfl⟩ := hs; simp
      · obtain ⟨c, hc, rfl, rfl⟩ := Option.map_eq_some_iff.mp hs; exact ihb hc
    · obtain ⟨c, hc, rfl, rfl⟩ := Option.map_eq_some_iff.mp hs; exact iha hc
  | cast a ih =>
    simp only [step] at hs
    split at hs
    · cases a <;> simp at hs; obtain ⟨_, rfl⟩ := hs; exact Nat.le_refl _
    · obtain ⟨c, hc, rfl, rfl⟩ := Option.map_eq_some_iff.mp hs; exact ih hc

/-- Reduction never shrinks the heap. -/
theorem reaches_heap_mono {c d : Config} (hr : Reaches c d) : c.2.length ≤ d.2.length := by
  induction hr with
  | refl => exact Nat.le_refl _
  | step hs _ ih => exact Nat.le_trans (step_heap_mono hs) ih

/-- Kripke monotonicity lifted to closing substitutions (standard model). -/
theorem G_std_mono {Γ : List Ty} {W W' : Nat} {γ : List Expr}
    (hW : W ≤ W') (hG : G Recipe.std Γ W γ) : G Recipe.std Γ W' γ := by
  induction Γ generalizing γ with
  | nil => cases γ <;> simp_all [G]
  | cons τ Γ ih =>
    cases γ with
    | nil => simp [G] at hG
    | cons v γ => exact ⟨V_std_mono hW hG.1, ih hG.2⟩

theorem G_length {R : Recipe} {Γ : List Ty} {W : Nat} {γ : List Expr}
    (hG : G R Γ W γ) : γ.length = Γ.length := by
  induction Γ generalizing γ with
  | nil => cases γ <;> simp_all [G]
  | cons _ _ ih =>
    cases γ with
    | nil => simp [G] at hG
    | cons _ _ => simp [G] at hG ⊢; exact ih hG.2

/-- Every entry of a closing substitution is a closed expression. -/
theorem G_closed {R : Recipe} {Γ : List Ty} {W : Nat} {γ : List Expr}
    (hG : G R Γ W γ) : ∀ u ∈ γ, u.closedAt 0 = true := by
  induction Γ generalizing γ with
  | nil => cases γ <;> simp_all [G]
  | cons _ _ ih =>
    cases γ with
    | nil => simp [G] at hG
    | cons v γ =>
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hmem
      · exact V_closed hG.1
      · exact ih hG.2 u hmem

theorem G_lookup {R : Recipe} {Γ : List Ty} {W : Nat} {γ : List Expr} {i : Nat} {τ : Ty}
    (hG : G R Γ W γ) (hi : Γ[i]? = some τ) : ∃ v, γ[i]? = some v ∧ V R τ W v := by
  induction Γ generalizing γ i with
  | nil => simp at hi
  | cons σ Γ ih =>
    cases γ with
    | nil => simp [G] at hG
    | cons v γ =>
      cases i with
      | zero => simp at hi; subst hi; exact ⟨v, rfl, hG.1⟩
      | succ j => simp at hi ⊢; exact ih hG.2 hi

theorem closedAt_mono {n m : Nat} {e : Expr} (hnm : n ≤ m) (h : e.closedAt n = true) :
    e.closedAt m = true := by
  induction e generalizing n m with
  | var i => simp only [closedAt, decide_eq_true_eq] at h ⊢; exact Nat.lt_of_lt_of_le h hnm
  | lam b ih => exact ih (Nat.succ_le_succ hnm) h
  | app f a ihf iha =>
    simp only [closedAt, Bool.and_eq_true] at h ⊢; exact ⟨ihf hnm h.1, iha hnm h.2⟩
  | lt a b iha ihb =>
    simp only [closedAt, Bool.and_eq_true] at h ⊢; exact ⟨iha hnm h.1, ihb hnm h.2⟩
  | ifz c t e ihc iht ihe =>
    simp only [closedAt, Bool.and_eq_true] at h ⊢
    exact ⟨⟨ihc hnm h.1.1, iht hnm h.1.2⟩, ihe hnm h.2⟩
  | alloc a ih | read a ih | cast a ih => exact ih hnm h
  | write a b iha ihb =>
    simp only [closedAt, Bool.and_eq_true] at h ⊢; exact ⟨iha hnm h.1, ihb hnm h.2⟩
  | num _ | size | loc _ => rfl

theorem substAllAt_of_closedAt {k : Nat} {γ : List Expr} {e : Expr}
    (h : e.closedAt k = true) : substAllAt k γ e = e := by
  induction e generalizing k with
  | var i => simp only [closedAt, decide_eq_true_eq] at h; simp [substAllAt, h]
  | lam b ih => simp [substAllAt, ih h]
  | app f a ihf iha =>
    simp only [closedAt, Bool.and_eq_true] at h; simp [substAllAt, ihf h.1, iha h.2]
  | lt a b iha ihb =>
    simp only [closedAt, Bool.and_eq_true] at h; simp [substAllAt, iha h.1, ihb h.2]
  | ifz c t e ihc iht ihe =>
    simp only [closedAt, Bool.and_eq_true] at h; simp [substAllAt, ihc h.1.1, iht h.1.2, ihe h.2]
  | alloc a ih | read a ih | cast a ih => simp [substAllAt, ih h]
  | write a b iha ihb =>
    simp only [closedAt, Bool.and_eq_true] at h; simp [substAllAt, iha h.1, ihb h.2]
  | num _ | size | loc _ => rfl

theorem closedAt_substAllAt {k : Nat} {γ : List Expr} {e : Expr}
    (hγ : ∀ u ∈ γ, u.closedAt 0 = true) (he : e.closedAt (k + γ.length) = true) :
    (substAllAt k γ e).closedAt k = true := by
  induction e generalizing k with
  | var i =>
    simp only [closedAt, decide_eq_true_eq] at he
    simp only [substAllAt]
    split
    · next hik => simp [closedAt, hik]
    · next hnot =>
      have hlt : i - k < γ.length := by omega
      rw [List.getElem?_eq_getElem hlt]
      exact closedAt_mono (Nat.zero_le k) (hγ _ (List.getElem_mem hlt))
  | lam b ih =>
    have he' : b.closedAt ((k + 1) + γ.length) = true := by
      simpa [closedAt, Nat.add_right_comm] using he
    exact ih he'
  | app f a ihf iha =>
    simp only [closedAt, Bool.and_eq_true] at he
    simp only [substAllAt, closedAt, Bool.and_eq_true]
    exact ⟨ihf he.1, iha he.2⟩
  | lt a b iha ihb =>
    simp only [closedAt, Bool.and_eq_true] at he
    simp only [substAllAt, closedAt, Bool.and_eq_true]
    exact ⟨iha he.1, ihb he.2⟩
  | ifz c t e ihc iht ihe =>
    simp only [closedAt, Bool.and_eq_true] at he
    simp only [substAllAt, closedAt, Bool.and_eq_true]
    exact ⟨⟨ihc he.1.1, iht he.1.2⟩, ihe he.2⟩
  | alloc a ih | read a ih | cast a ih => exact ih he
  | write a b iha ihb =>
    simp only [closedAt, Bool.and_eq_true] at he
    simp only [substAllAt, closedAt, Bool.and_eq_true]
    exact ⟨iha he.1, ihb he.2⟩
  | num _ | size | loc _ => rfl

/-- Substituting a closing substitution under one binder and then the bound
variable equals substituting the extended substitution. -/
theorem substAllAt_comp_cons {k : Nat} {v : Expr} {γ : List Expr}
    (hγ : ∀ u ∈ γ, u.closedAt 0 = true) (e : Expr) :
    substAllAt k [v] (substAllAt (k + 1) γ e) = substAllAt k (v :: γ) e := by
  induction e generalizing k with
  | var i =>
    simp only [substAllAt]
    by_cases hik : i < k
    · have hik1 : i < k + 1 := Nat.lt_succ_of_lt hik
      simp [hik, hik1, substAllAt]
    · by_cases hik' : i = k
      · subst hik'
        have hk1 : i < i + 1 := Nat.lt_succ_self i
        simp [hk1, substAllAt]
      · have hgt : k + 1 ≤ i := by omega
        have hnot1 : ¬ i < k + 1 := Nat.not_lt.mpr hgt
        simp only [hik, hnot1, ↓reduceIte]
        have hsub : i - k = (i - (k + 1)) + 1 := by omega
        rw [hsub]
        simp only [List.getElem?_cons_succ]
        cases hget : γ[i - (k + 1)]? with
        | some u =>
          exact substAllAt_of_closedAt
            (closedAt_mono (Nat.zero_le k) (hγ u (List.mem_of_getElem? hget)))
        | none =>
          have hlen : γ.length ≤ i - (k + 1) := List.getElem?_eq_none_iff.mp hget
          have hnotk : ¬ (i - γ.length < k) := by omega
          have hge1 : 1 ≤ i - γ.length - k := by omega
          have hnone : ([v] : List Expr)[i - γ.length - k]? = none :=
            List.getElem?_eq_none_iff.mpr hge1
          simp only [substAllAt, hnotk, ↓reduceIte, hnone, List.length_cons]
          congr 1
  | lam b ih => simp [substAllAt, ih]
  | app f a ihf iha => simp [substAllAt, ihf, iha]
  | lt a b iha ihb => simp [substAllAt, iha, ihb]
  | ifz c t e ihc iht ihe => simp [substAllAt, ihc, iht, ihe]
  | alloc a ih | read a ih | cast a ih => simp [substAllAt, ih]
  | write a b iha ihb => simp [substAllAt, iha, ihb]
  | num _ | size | loc _ => rfl

/-- Evaluation-context bind: if `e₀` is safe with results satisfying `Q`, and
plugging any `Q`-value (in a world at least as large) into the context `K`
yields a safe expression with results satisfying `P`, then `K e₀` is safe with
results satisfying `P`. -/
theorem bind_goodFrom {K : Expr → Expr} {Q P : Nat → Expr → Prop}
    (hK_nv : ∀ e₀, (K e₀).isValue = false)
    (hK_step : ∀ {e₀ : Expr} {h₀ : Heap}, e₀.isValue = false →
      step (K e₀) h₀ = (step e₀ h₀).map fun c => (K c.1, c.2))
    {e₀ : Expr} {h₀ : Heap}
    (he₀ : ∀ e₁ h₁, Reaches (e₀, h₀) (e₁, h₁) →
      ¬ Stuck (e₁, h₁) ∧ (e₁.isValue = true → Q h₁.length e₁))
    (hK_val : ∀ v h₁, h₀.length ≤ h₁.length → v.isValue = true → Q h₁.length v →
      ∀ e' h', Reaches (K v, h₁) (e', h') →
        ¬ Stuck (e', h') ∧ (e'.isValue = true → P h'.length e')) :
    ∀ e' h', Reaches (K e₀, h₀) (e', h') →
      ¬ Stuck (e', h') ∧ (e'.isValue = true → P h'.length e') := by
  suffices ∀ c d, Reaches c d → ∀ e₀ h₀, c = (K e₀, h₀) →
      (∀ e₁ h₁, Reaches (e₀, h₀) (e₁, h₁) →
        ¬ Stuck (e₁, h₁) ∧ (e₁.isValue = true → Q h₁.length e₁)) →
      (∀ v h₁, h₀.length ≤ h₁.length → v.isValue = true → Q h₁.length v →
        ∀ e' h', Reaches (K v, h₁) (e', h') →
          ¬ Stuck (e', h') ∧ (e'.isValue = true → P h'.length e')) →
      ¬ Stuck d ∧ (d.1.isValue = true → P d.2.length d.1) from
    fun e' h' hr => this (K e₀, h₀) (e', h') hr e₀ h₀ rfl he₀ hK_val
  intro c d hrd
  induction hrd with
  | refl =>
    intro e₀ h₀ hcfg hgood hval
    subst hcfg
    refine ⟨?_, fun hv => by rw [hK_nv] at hv; cases hv⟩
    by_cases hv : e₀.isValue = true
    · exact (hval e₀ h₀ (Nat.le_refl _) hv ((hgood e₀ h₀ (.refl _)).2 hv) (K e₀) h₀ (.refl _)).1
    · have hvF : e₀.isValue = false := by cases h' : e₀.isValue <;> simp_all
      cases hst : step e₀ h₀ with
      | none => exact absurd ⟨hvF, hst⟩ (hgood e₀ h₀ (.refl _)).1
      | some p =>
        exact not_stuck_of_step (c' := (K p.1, p.2)) (by rw [hK_step hvF, hst]; rfl)
  | step hs hr' ih =>
    intro e₀ h₀ hcfg hgood hval
    subst hcfg
    by_cases hv : e₀.isValue = true
    · exact hval e₀ h₀ (Nat.le_refl _) hv ((hgood e₀ h₀ (.refl _)).2 hv) _ _ (.step hs hr')
    · have hvF : e₀.isValue = false := by cases h' : e₀.isValue <;> simp_all
      rw [hK_step hvF] at hs
      obtain ⟨p, hst, hc'⟩ := Option.map_eq_some_iff.mp hs
      cases hc'
      exact ih p.1 p.2 rfl
        (fun e₁ h₁ hr₁ => hgood e₁ h₁ (.step hst hr₁))
        (fun v h₁ hle => hval v h₁ (Nat.le_trans (step_heap_mono hst) hle))

/-! ## Main results -/

/-- **Adequacy.** An expression that is semantically well typed in the empty
context `[]` (standard model) never reaches a stuck configuration, from any
initial heap. (The empty context does not force syntactic closedness
`e.closedAt 0 = true`: free variables in unreachable code are allowed.) -/
theorem adequacy_semTyped_nil_safe {e : Expr} {τ : Ty}
    (hsem : SemTyped Recipe.std [] e τ) (h : Heap) : Safe (e, h) :=
  fun d hr => ((semTyped_nil_iff.mp hsem 0) h (Nat.zero_le _) d.1 d.2 hr).1

/-- **Fundamental theorem.** Every syntactically well-typed expression is
semantically well typed (in the standard model), in any context. -/
theorem fundamental_hasType_semTyped {Γ : List Ty} {e : Expr} {τ : Ty}
    (hty : HasType Γ e τ) : SemTyped Recipe.std Γ e τ := by
  induction hty with
  | @var Γ i τ hi =>
    intro W γ hγ h hW
    obtain ⟨v, hget, hv⟩ := G_lookup hγ hi
    have hsub : substAll γ (.var i) = v := by simp [substAll, substAllAt, hget]
    rw [hsub]
    exact goodFrom_value (V_isValue hv) (V_std_mono hW hv)
  | @lam Γ σ τ b hbody ih =>
    intro W γ hγ h hW
    let b' := substAllAt 1 γ b
    have hb_closed : b'.closedAt 1 = true := by
      have hlen : 1 + γ.length = (σ :: Γ).length := by simp [G_length hγ, Nat.add_comm]
      exact closedAt_substAllAt (G_closed hγ) (hlen ▸ hbody.closedAt)
    refine goodFrom_value rfl ⟨b', rfl, hb_closed, fun W' hW' v hv => ?_⟩
    have hcomp : substAt 0 v b' = substAll (v :: γ) b :=
      substAllAt_comp_cons (G_closed hγ) b
    rw [hcomp]
    exact ih W' (v :: γ) ⟨hv, G_std_mono (Nat.le_trans hW hW') hγ⟩
  | @app Γ σ τ f a _ _ ihf iha =>
    intro W γ hγ h hW
    refine bind_goodFrom (K := fun x => .app x (substAll γ a)) (Q := V Recipe.std (.arrow σ τ))
      (fun _ => rfl)
      (fun {e₀ h₀} hvF => by conv => lhs; unfold step; simp [hvF])
      (ihf W γ hγ h hW) ?_
    rintro vf h₁ hle₁ hvf hQvf
    refine bind_goodFrom (K := fun y => .app vf y) (Q := V Recipe.std σ)
      (fun _ => rfl)
      (fun {e₀ h₀} hvF => by conv => lhs; unfold step; simp [hvf, hvF])
      (iha W γ hγ h₁ (Nat.le_trans hW hle₁)) ?_
    rintro va h₂ hle₂ hva hQva
    obtain ⟨b, rfl, _, hfun⟩ := hQvf
    have hlam : (Expr.lam b).isValue = true := rfl
    have hstep : step (.app (.lam b) va) h₂ = some (substAt 0 va b, h₂) := by
      conv => lhs; unfold step; simp [hlam, hva]
    exact goodFrom_step hstep (hfun h₂.length hle₂ va hQva h₂ (Nat.le_refl _))
  | num =>
    intro W γ _ h _
    exact goodFrom_value rfl ⟨_, rfl⟩
  | @lt Γ a b _ _ iha ihb =>
    intro W γ hγ h hW
    refine bind_goodFrom (K := fun x => .lt x (substAll γ b)) (Q := V Recipe.std .int)
      (fun _ => rfl)
      (fun {e₀ h₀} hvF => by conv => lhs; unfold step; simp [hvF])
      (iha W γ hγ h hW) ?_
    rintro va h₁ hle₁ hva ⟨na, rfl⟩
    have hna : (Expr.num na).isValue = true := rfl
    refine bind_goodFrom (K := fun y => .lt (.num na) y) (Q := V Recipe.std .int)
      (fun _ => rfl)
      (fun {e₀ h₀} hvF => by conv => lhs; unfold step; simp [hna, hvF])
      (ihb W γ hγ h₁ (Nat.le_trans hW hle₁)) ?_
    rintro vb h₂ _ _ ⟨nb, rfl⟩
    exact goodFrom_step rfl (goodFrom_value rfl ⟨_, rfl⟩)
  | @ifz Γ τ c t e _ _ _ ihc iht ihe =>
    intro W γ hγ h hW
    refine bind_goodFrom (K := fun x => .ifz x (substAll γ t) (substAll γ e))
      (Q := V Recipe.std .int)
      (fun _ => rfl)
      (fun {e₀ h₀} hvF => by conv => lhs; unfold step; simp [hvF])
      (ihc W γ hγ h hW) ?_
    rintro vc h₁ hle₁ _ ⟨nc, rfl⟩
    cases nc with
    | zero => exact goodFrom_step rfl (iht W γ hγ h₁ (Nat.le_trans hW hle₁))
    | succ k => exact goodFrom_step rfl (ihe W γ hγ h₁ (Nat.le_trans hW hle₁))
  | size =>
    intro W γ _ h _
    exact goodFrom_step rfl (goodFrom_value rfl ⟨h.length, rfl⟩)
  | @alloc Γ a _ ih =>
    intro W γ hγ h hW
    refine bind_goodFrom (K := fun x => .alloc x) (Q := V Recipe.std .int)
      (fun _ => rfl)
      (fun {e₀ h₀} hvF => by conv => lhs; unfold step; simp [hvF])
      (ih W γ hγ h hW) ?_
    rintro va h₁ _ _ ⟨na, rfl⟩
    exact goodFrom_step rfl
      (goodFrom_value rfl ⟨h₁.length, rfl, show h₁.length < (h₁ ++ [na]).length by simp⟩)
  | @read Γ a _ ih =>
    intro W γ hγ h hW
    refine bind_goodFrom (K := fun x => .read x) (Q := V Recipe.std .ref)
      (fun _ => rfl)
      (fun {e₀ h₀} hvF => by conv => lhs; unfold step; simp [hvF])
      (ih W γ hγ h hW) ?_
    rintro va h₁ _ _ ⟨l, rfl, hl⟩
    exact goodFrom_step (e₁ := .num h₁[l]) (h₁ := h₁)
      (by simp [step, Expr.isValue, List.getElem?_eq_getElem hl])
      (goodFrom_value rfl ⟨h₁[l], rfl⟩)
  | @write Γ a b _ _ iha ihb =>
    intro W γ hγ h hW
    refine bind_goodFrom (K := fun x => .write x (substAll γ b)) (Q := V Recipe.std .ref)
      (fun _ => rfl)
      (fun {e₀ h₀} hvF => by conv => lhs; unfold step; simp [hvF])
      (iha W γ hγ h hW) ?_
    rintro va h₁ hle₁ _ ⟨l, rfl, hl⟩
    have hloc : (Expr.loc l).isValue = true := rfl
    refine bind_goodFrom (K := fun y => .write (.loc l) y) (Q := V Recipe.std .int)
      (fun _ => rfl)
      (fun {e₀ h₀} hvF => by conv => lhs; unfold step; simp [hloc, hvF])
      (ihb W γ hγ h₁ (Nat.le_trans hW hle₁)) ?_
    rintro vb h₂ hle₂ _ ⟨nb, rfl⟩
    have hl₂ : l < h₂.length := Nat.lt_of_lt_of_le hl hle₂
    exact goodFrom_step (e₁ := .num 0) (h₁ := h₂.set l nb)
      (by simp [step, Expr.isValue, hl₂])
      (goodFrom_value rfl ⟨0, rfl⟩)

/-- **Semantic let-compatibility (linking).** In the standard model, if a client
`c` is semantically well typed at `τ` in context `σ :: Γ`, and a library
expression `lib` is semantically well typed at `σ` in context `Γ`, then the
call-by-value linked program `(λ. c) lib` is semantically well typed at `τ` in
context `Γ`. Neither `c` nor `lib` need be syntactically typable. -/
theorem semTyped_let_compat {Γ : List Ty} {σ τ : Ty} {c lib : Expr}
    (hc : SemTyped Recipe.std (σ :: Γ) c τ) (hlib : SemTyped Recipe.std Γ lib σ) :
    SemTyped Recipe.std Γ (.app (.lam c) lib) τ := by
  intro W γ hγ h hW
  let b' := substAllAt 1 γ c
  have hb'_val : (Expr.lam b').isValue = true := rfl
  show ∀ e' h', Reaches (.app (.lam b') (substAll γ lib), h) (e', h') → _
  refine bind_goodFrom (K := fun x => .app (.lam b') x) (Q := V Recipe.std σ)
    (fun _ => rfl)
    (fun {e₀ h₀} hvF => by conv => lhs; unfold step; simp [hb'_val, hvF])
    (hlib W γ hγ h hW) ?_
  intro v h₁ hle hv hQv
  have hstep : step (.app (.lam b') v) h₁ = some (substAt 0 v b', h₁) := by
    conv => lhs; unfold step; simp [hb'_val, hv]
  refine goodFrom_step hstep ?_
  have hcomp : substAt 0 v b' = substAll (v :: γ) c :=
    substAllAt_comp_cons (G_closed hγ) c
  rw [hcomp]
  exact hc h₁.length (v :: γ) ⟨hQv, G_std_mono (Nat.le_trans hW hle) hγ⟩ h₁ (Nat.le_refl _)

/-! ## Corollaries of the main results -/

/-- **Syntactic type safety, derived semantically.** A closed, syntactically
well-typed expression never gets stuck, from any initial heap. -/
theorem hasType_closed_safe {e : Expr} {τ : Ty} (hty : HasType [] e τ) (h : Heap) :
    Safe (e, h) :=
  adequacy_semTyped_nil_safe (fundamental_hasType_semTyped hty) h

/-- Linking (call-by-value `app (lam c) lib`, standard model) a client `c` that
is semantically well typed in the one-variable context `[σ]` with a library
`lib` semantically well typed at `σ` in the empty context is safe from every
heap. -/
theorem semTyped_client_semTyped_lib_safe {σ τ : Ty} {c lib : Expr}
    (hc : SemTyped Recipe.std [σ] c τ) (hlib : SemTyped Recipe.std [] lib σ) (h : Heap) :
    Safe (.app (.lam c) lib, h) :=
  adequacy_semTyped_nil_safe (semTyped_let_compat hc hlib) h

/-- **Encapsulation principle.** Linking (call-by-value `app (lam c) lib`) a
client `c` that is syntactically well typed in the one-variable context `[σ]`
with a library `lib` that is semantically well typed at `σ` in the empty
context (standard model; `lib` may use `cast`) is safe from every heap. -/
theorem hasType_client_semTyped_lib_safe {σ τ : Ty} {c lib : Expr}
    (hc : HasType [σ] c τ) (hlib : SemTyped Recipe.std [] lib σ) (h : Heap) :
    Safe (.app (.lam c) lib, h) :=
  semTyped_client_semTyped_lib_safe (fundamental_hasType_semTyped hc) hlib h

/-! ## Encapsulation: the concrete library -/

/-- The bounds-checked raw read has no syntactic type in any context
(it contains the unsafe primitive). -/
theorem checkedRead_not_hasType (Γ : List Ty) (τ : Ty) : ¬ HasType Γ checkedRead τ :=
  not_hasType_of_not_castFree rfl Γ τ

/-- Every client that is syntactically well typed in the context `[int ⇒ int]`
is safe from every heap when linked (call-by-value) with `checkedRead`. -/
theorem checkedRead_hasType_clients_safe {τ : Ty} {c : Expr}
    (hc : HasType [.arrow .int .int] c τ) (h : Heap) :
    Safe (.app (.lam c) checkedRead, h) :=
  hasType_client_semTyped_lib_safe hc checkedRead_semTyped h

/-! ## Unsafe uses and the unsafe primitive -/

theorem forgedRead_reaches_stuck :
    Reaches (forgedRead, []) (.read (.loc 7), []) ∧ Stuck (.read (.loc 7), []) :=
  ⟨by reach, rfl, rfl⟩

/-- **Unsafe use.** `read (cast 7)` is not syntactically typable in any context,
is not semantically well typed at any type in the empty context, and gets
stuck from the empty heap. -/
theorem forgedRead_unsafe_ill_typed :
    (∀ Γ τ, ¬ HasType Γ forgedRead τ) ∧ (∀ τ, ¬ SemTyped Recipe.std [] forgedRead τ) ∧
    ¬ Safe (forgedRead, []) := by
  refine ⟨fun Γ τ => not_hasType_of_not_castFree rfl Γ τ, fun τ hs => ?_, ?_⟩
  · exact not_safeAndIn_of_reaches_stuck (h := []) (Nat.le_refl _)
      forgedRead_reaches_stuck.1 forgedRead_reaches_stuck.2 (semTyped_nil_iff.mp hs 0)
  · exact not_safe_of_reaches_stuck forgedRead_reaches_stuck.1 forgedRead_reaches_stuck.2

/-- The standard closure enforces values. -/
theorem std_closureEnforcesValues : Recipe.std.ClosureEnforcesValues :=
  fun _ _ _ h => valuesIn_of_safeAndIn h

/-- The standard recipe has an invalid reference (address `0` in world `0`). -/
theorem std_hasInvalidRef : Recipe.std.HasInvalidRef :=
  ⟨0, 0, Nat.lt_irrefl 0⟩

/-- **No semantic type for `cast` of an `int` variable (general form).** For any
recipe whose expression closure enforces value membership and which has some
invalid reference, `cast x` with `x : int` is not semantically well typed in
context `[int]` at any type. -/
theorem cast_of_int_var_not_semTyped_of_closureEnforcesValues_of_hasInvalidRef {R : Recipe}
    (hclose : R.ClosureEnforcesValues) (hinv : R.HasInvalidRef) (τ : Ty) :
    ¬ SemTyped R [.int] (.cast (.var 0)) τ := by
  intro hs
  obtain ⟨W, l, hl⟩ := hinv
  have hE := hclose _ _ _ (hs W [.num l] ⟨⟨l, rfl⟩, trivial⟩)
  have hlen : (List.replicate W 0).length = W := List.length_replicate
  have hV := hE (List.replicate W 0) (Nat.le_of_eq hlen.symm) (.loc l) (List.replicate W 0)
    (Reaches.step rfl (Reaches.refl _)) rfl
  rw [hlen] at hV
  cases τ with
  | int => obtain ⟨n, hn⟩ := hV; cases hn
  | ref => obtain ⟨l', hl', hok⟩ := hV; cases hl'; exact hl hok
  | arrow σ τ => obtain ⟨b, hb, _⟩ := hV; cases hb

/-- **No semantic type for `cast` of an `int` variable (standard model).** In
context `[int]`, `cast x` is not semantically well typed at any type. -/
theorem cast_of_int_var_not_semTyped (τ : Ty) :
    ¬ SemTyped Recipe.std [.int] (.cast (.var 0)) τ :=
  cast_of_int_var_not_semTyped_of_closureEnforcesValues_of_hasInvalidRef
    std_closureEnforcesValues std_hasInvalidRef τ

/-- Consequently, no typing relation that derives `[int] ⊢ cast (var 0) : τ`
for some `τ` is sound for the standard semantic model. -/
theorem typing_relation_deriving_cast_of_int_var_unsound
    (T : List Ty → Expr → Ty → Prop) (τ : Ty) (hT : T [.int] (.cast (.var 0)) τ) :
    ¬ (∀ Γ e τ', T Γ e τ' → SemTyped Recipe.std Γ e τ') :=
  fun hsound => cast_of_int_var_not_semTyped τ (hsound _ _ _ hT)

/-- Syntactic typing extended with the uniform root rule
`Γ ⊢ a : int ⟹ Γ ⊢ cast a : ref` (the tempting typing rule for an
integer-to-reference cast). By `typing_relation_deriving_cast_of_int_var_unsound`
it is not sound for the standard model. -/
def withCastRootRule (Γ : List Ty) (e : Expr) (τ : Ty) : Prop :=
  HasType Γ e τ ∨ ∃ a, e = .cast a ∧ τ = .ref ∧ HasType Γ a .int

/-- Two *restricted* typing rules with `cast` at the root, over the unmodified
types: `ref :: Γ ⊢ cast 0 : ref` (a `ref` assumption forces cell 0 to be
allocated) and `Γ ⊢ cast ((λ _. 0) (alloc 0)) : ref` (the argument allocates a
cell before returning `0`). Both are sound for the standard model
(`restrictedCastRule_sound`). -/
inductive RestrictedCastRule : List Ty → Expr → Ty → Prop where
  | refCtx {Γ : List Ty} : RestrictedCastRule (.ref :: Γ) (.cast (.num 0)) .ref
  | allocArg {Γ : List Ty} : RestrictedCastRule Γ (.cast zeroAfterAlloc) .ref

theorem substAll_cast_zeroAfterAlloc (γ : List Expr) :
    substAll γ (.cast zeroAfterAlloc) = .cast zeroAfterAlloc := rfl

/-- Both restricted rules are sound for the standard model: some typing rules
with `cast` at the root are semantically sound even without refinement types. -/
theorem restrictedCastRule_sound :
    ∀ Γ e τ, RestrictedCastRule Γ e τ → SemTyped Recipe.std Γ e τ := by
  intro Γ e τ hr
  cases hr with
  | refCtx =>
    intro W γ hγ
    match γ, hγ with
    | v :: γ', ⟨hv, _⟩ =>
      obtain ⟨l, rfl, hl⟩ := hv
      intro h hW
      have h0 : 0 < h.length := Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt (Nat.zero_le l) hl) hW
      exact goodFrom_step (e₁ := .loc 0) (h₁ := h) rfl (goodFrom_value rfl ⟨0, rfl, h0⟩)
  | allocArg =>
    intro W γ _
    rw [substAll_cast_zeroAfterAlloc]
    intro h _
    refine goodFrom_step (e₁ := .cast (.app (.lam (.num 0)) (.loc h.length))) (h₁ := h ++ [0])
      rfl ?_
    refine goodFrom_step (e₁ := .cast (.num 0)) (h₁ := h ++ [0]) rfl ?_
    refine goodFrom_step (e₁ := .loc 0) (h₁ := h ++ [0]) rfl ?_
    exact goodFrom_value rfl ⟨0, rfl, show 0 < (h ++ [0]).length by simp⟩

/-- A cast of any literal address is safe from every heap, yet is not
semantically well typed at any type in the empty context (operational safety
of a closed term does not imply semantic typing). -/
theorem cast_literal_safe_but_not_semTyped (n : Nat) :
    (∀ h, Safe (.cast (.num n), h)) ∧ ∀ τ, ¬ SemTyped Recipe.std [] (.cast (.num n)) τ := by
  refine ⟨fun h => safe_of_step (c' := (.loc n, h)) rfl (safe_of_isValue rfl), fun τ hs => ?_⟩
  have hV := (semTyped_nil_iff.mp hs 0 [] (Nat.le_refl _) (.loc n) [] (by reach)).2 rfl
  cases τ with
  | int => obtain ⟨m, hm⟩ := hV; cases hm
  | ref => obtain ⟨l, hl, hlt⟩ := hV; cases hl; exact Nat.not_lt_zero _ hlt
  | arrow σ τ => obtain ⟨b, hb, _⟩ := hV; cases hb

/-! ## Ablated models -/

/-- **Dropping safety from the expression closure breaks adequacy.** Under
`Recipe.valuesOnly`, `read (cast 7)` is semantically well typed at `int` in the
empty context (every value it reaches is a word), yet it gets stuck from the
empty heap. -/
theorem valuesOnly_adequacy_fails :
    SemTyped Recipe.valuesOnly [] forgedRead .int ∧ ¬ Safe (forgedRead, []) := by
  refine ⟨?_, forgedRead_unsafe_ill_typed.2.2⟩
  rw [semTyped_nil_iff]
  intro W h _
  refine valFrom_step (e₁ := .read (.loc 7)) (h₁ := h) rfl ?_
  by_cases h7 : 7 < h.length
  · refine valFrom_step (e₁ := .num h[7]) (h₁ := h)
      (by simp [step, Expr.isValue, List.getElem?_eq_getElem h7]) ?_
    intro e' h' hr _
    have := reaches_of_isValue rfl hr
    simp only [Prod.mk.injEq] at this
    obtain ⟨rfl, rfl⟩ := this
    exact ⟨_, rfl⟩
  · exact valFrom_stuck ⟨rfl, by
      simp [step, Expr.isValue, List.getElem?_eq_none_iff.mpr (Nat.le_of_not_lt h7)]⟩

/-- Under `Recipe.safetyOnly`, semantic typing in the empty context at any type
is exactly safety from every heap: the type plays no role. -/
theorem safetyOnly_semTyped_nil_iff_safe {e : Expr} {τ : Ty} :
    SemTyped Recipe.safetyOnly [] e τ ↔ ∀ h, Safe (e, h) := by
  rw [semTyped_nil_iff]
  constructor
  · intro hs h d hr
    exact hs 0 h (Nat.zero_le _) d hr
  · intro hs W h _ d hr
    exact hs h d hr

theorem castSeven_V_safetyOnly (W : Nat) :
    V Recipe.safetyOnly (.arrow .int .ref) W castSeven := by
  refine ⟨_, rfl, rfl, fun W' _ v _ => ?_⟩
  intro h _
  show Safe (.cast (.num 7), h)
  exact safe_of_step (c' := (.loc 7, h)) rfl (safe_of_isValue rfl)

/-- **Dropping the value part of the expression closure breaks the fundamental
theorem and the encapsulation principle.** Under `Recipe.safetyOnly`, the
library `λ _. cast 7` is semantically well typed at `int ⇒ ref`; the
syntactically typed client `read (f 0)` is not semantically well typed (the
fundamental theorem fails); and the linked program gets stuck (the
syntactic-client encapsulation principle fails). -/
theorem safetyOnly_breaks_fundamental_and_encapsulation :
    HasType [.arrow .int .ref] readResultOf0 .int ∧
    SemTyped Recipe.safetyOnly [] castSeven (.arrow .int .ref) ∧
    ¬ SemTyped Recipe.safetyOnly [.arrow .int .ref] readResultOf0 .int ∧
    ¬ Safe (.app (.lam readResultOf0) castSeven, []) := by
  refine ⟨.read (.app (.var rfl) .num), ?_, ?_, ?_⟩
  · rw [safetyOnly_semTyped_nil_iff_safe]
    intro h
    exact safe_of_isValue rfl
  · intro hs
    exact not_safeOnly_of_reaches_stuck (P := V Recipe.safetyOnly .int) (h := [])
      (d := (.read (.loc 7), [])) (Nat.le_refl _)
      (by reach) ⟨rfl, rfl⟩ (hs 0 [castSeven] ⟨castSeven_V_safetyOnly 0, trivial⟩)
  · exact not_safe_of_reaches_stuck (d := (.read (.loc 7), [])) (by reach) ⟨rfl, rfl⟩

/-- **Dropping the value part of the expression closure breaks semantic
linking.** Under `Recipe.safetyOnly`, the `cast`-free client `lt x 0` is
semantically well typed at `int` in context `[int]`, the `cast`-free library
`λ _. 0` is semantically well typed at `int` in the empty context, yet the
linked program is not semantically well typed and gets stuck (it compares a
function with a number). -/
theorem safetyOnly_breaks_let_compat :
    SemTyped Recipe.safetyOnly [.int] (.lt (.var 0) (.num 0)) .int ∧
    SemTyped Recipe.safetyOnly [] (.lam (.num 0)) .int ∧
    ¬ SemTyped Recipe.safetyOnly [] (.app (.lam (.lt (.var 0) (.num 0))) (.lam (.num 0))) .int ∧
    ¬ Safe (.app (.lam (.lt (.var 0) (.num 0))) (.lam (.num 0)), []) := by
  refine ⟨fun W γ hγ => ?_, ?_, ?_, ?_⟩
  · obtain ⟨v, rfl, n, rfl⟩ := G_singleton.mp hγ
    intro h _
    exact safe_of_step (c' := (.num (if n < 0 then 1 else 0), h)) rfl (safe_of_isValue rfl)
  · rw [safetyOnly_semTyped_nil_iff_safe]
    intro h
    exact safe_of_isValue rfl
  · intro hs
    exact not_safeOnly_of_reaches_stuck (P := V Recipe.safetyOnly .int) (h := [])
      (d := (.lt (.lam (.num 0)) (.num 0), [])) (Nat.le_refl _) (by reach) ⟨rfl, rfl⟩
      (semTyped_nil_iff.mp hs 0)
  · exact not_safe_of_reaches_stuck (d := (.lt (.lam (.num 0)) (.num 0), [])) (by reach)
      ⟨rfl, rfl⟩

/-- In the non-Kripke model, `probeCellZero` is in the interpretation of
`ref ⇒ int` at world 1 (whose only valid reference is `loc 0`). -/
theorem probeCellZero_V_nonKripke_one : V Recipe.nonKripke (.arrow .ref .int) 1 probeCellZero := by
  refine ⟨_, rfl, rfl, fun W' hW' v hv => ?_⟩
  obtain ⟨l, rfl, hl⟩ := hv
  have h1 : W' = 1 := hW'
  have hl' : l < W' := hl
  have hl0 : l = 0 := by omega
  subst h1 hl0
  intro h hh
  have hpos : 0 < h.length := hh
  refine goodFrom_step (e₁ := .app probeBody (.num 0)) (h₁ := h.set 0 1)
    (by simp [substAt, substAllAt, probeBody, step, Expr.isValue, hpos]) ?_
  refine goodFrom_step (e₁ := .ifz (.read (.cast (.num 0))) (.read (.cast (.num 99))) (.num 0))
    (h₁ := h.set 0 1) rfl ?_
  refine goodFrom_step (e₁ := .ifz (.read (.loc 0)) (.read (.cast (.num 99))) (.num 0))
    (h₁ := h.set 0 1) rfl ?_
  refine goodFrom_step (e₁ := .ifz (.num 1) (.read (.cast (.num 99))) (.num 0))
    (h₁ := h.set 0 1) (by simp [step, Expr.isValue, hpos]) ?_
  refine goodFrom_step (e₁ := .num 0) (h₁ := h.set 0 1) rfl ?_
  exact goodFrom_value rfl ⟨0, rfl⟩

/-- In the non-Kripke model, `probeCellZero` is (vacuously) in the
interpretation of `ref ⇒ int` at world 0, which has no valid reference. -/
theorem probeCellZero_V_nonKripke_zero : V Recipe.nonKripke (.arrow .ref .int) 0 probeCellZero := by
  refine ⟨_, rfl, rfl, fun W' hW' v hv => ?_⟩
  obtain ⟨l, rfl, hl⟩ := hv
  have h0 : W' = 0 := hW'
  subst h0
  exact absurd hl (Nat.not_lt_zero l)

/-- From the heap `[0, 0]`, calling `probeCellZero` on `loc 1` gets stuck. -/
theorem probeCellZero_loc1_reaches_stuck :
    Reaches (substAt 0 (.loc 1) (.app probeBody (.write (.var 0) (.num 1))), [0, 0])
      (.read (.loc 99), [0, 1]) ∧ Stuck (.read (.loc 99), [0, 1]) :=
  ⟨by reach, rfl, rfl⟩

/-- **Dropping the Kripke structure breaks monotonicity and the fundamental
theorem.** Under `Recipe.nonKripke`, `probeCellZero` is in the interpretation
of `ref ⇒ int` at world 1 but not at world 2; the standard (Kripke) model
rejects it already at world 1; and the syntactically typed client
`f (alloc 0)` is not semantically well typed under `Recipe.nonKripke`. -/
theorem nonKripke_breaks_monotonicity_and_fundamental :
    V Recipe.nonKripke (.arrow .ref .int) 1 probeCellZero ∧
    ¬ V Recipe.nonKripke (.arrow .ref .int) 2 probeCellZero ∧
    ¬ V Recipe.std (.arrow .ref .int) 1 probeCellZero ∧
    HasType [.arrow .ref .int] callOnFreshCell .int ∧
    ¬ SemTyped Recipe.nonKripke [.arrow .ref .int] callOnFreshCell .int := by
  refine ⟨probeCellZero_V_nonKripke_one, ?_, ?_, .app (.var rfl) (.alloc .num), ?_⟩
  · intro hV
    obtain ⟨b, hb, _, hf⟩ := hV
    simp only [probeCellZero, Expr.lam.injEq] at hb
    subst hb
    exact not_safeAndIn_of_reaches_stuck (h := [0, 0]) (Nat.le_refl _)
      probeCellZero_loc1_reaches_stuck.1 probeCellZero_loc1_reaches_stuck.2
      (hf 2 rfl (.loc 1) ⟨1, rfl, Nat.lt_succ_self 1⟩)
  · intro hV
    obtain ⟨b, hb, _, hf⟩ := hV
    simp only [probeCellZero, Expr.lam.injEq] at hb
    subst hb
    exact not_safeAndIn_of_reaches_stuck (h := [0, 0]) (Nat.le_refl _)
      probeCellZero_loc1_reaches_stuck.1 probeCellZero_loc1_reaches_stuck.2
      (hf 2 (Nat.le_succ 1) (.loc 1) ⟨1, rfl, Nat.lt_succ_self 1⟩)
  · intro hs
    exact not_safeAndIn_of_reaches_stuck (h := [0]) (d := (.read (.loc 99), [0, 1]))
      (Nat.le_refl _) (by reach) ⟨rfl, rfl⟩
      (hs 1 [probeCellZero] ⟨probeCellZero_V_nonKripke_one, trivial⟩)

/-- **Dropping the Kripke structure also breaks closed encapsulation.** Under
`Recipe.nonKripke`, the closed library `sizeGuardedProbe` (which returns
`probeCellZero` when `size < 2` and `λ _. 0` otherwise) is semantically well
typed at `ref ⇒ int` in the empty context, the client `f (alloc 0)` is
syntactically well typed, and the linked program gets stuck from the heap `[0]`. -/
theorem nonKripke_breaks_closed_encapsulation :
    HasType [.arrow .ref .int] callOnFreshCell .int ∧
    SemTyped Recipe.nonKripke [] sizeGuardedProbe (.arrow .ref .int) ∧
    ¬ Safe (.app (.lam callOnFreshCell) sizeGuardedProbe, [0]) := by
  refine ⟨.app (.var rfl) (.alloc .num), ?_, ?_⟩
  · rw [semTyped_nil_iff]
    intro W h _
    refine goodFrom_step (e₁ := .ifz (.lt (.num h.length) (.num 2)) (.lam (.num 0)) probeCellZero)
      (h₁ := h) rfl ?_
    refine goodFrom_step
      (e₁ := .ifz (.num (if h.length < 2 then 1 else 0)) (.lam (.num 0)) probeCellZero)
      (h₁ := h) rfl ?_
    by_cases hlt : h.length < 2
    · simp only [hlt, ↓reduceIte]
      refine goodFrom_step (e₁ := probeCellZero) (h₁ := h) rfl ?_
      have hcases : h.length = 0 ∨ h.length = 1 := by omega
      rcases hcases with h0 | h1
      · refine goodFrom_value rfl ?_
        rw [h0]
        exact probeCellZero_V_nonKripke_zero
      · refine goodFrom_value rfl ?_
        rw [h1]
        exact probeCellZero_V_nonKripke_one
    · simp only [hlt, ↓reduceIte]
      refine goodFrom_step (e₁ := .lam (.num 0)) (h₁ := h) rfl ?_
      refine goodFrom_value rfl ⟨.num 0, rfl, rfl, fun W' _ v _ h' _ => ?_⟩
      exact goodFrom_value rfl ⟨0, rfl⟩
  · exact not_safe_of_reaches_stuck (d := (.read (.loc 99), [0, 1])) (by reach) ⟨rfl, rfl⟩

/-- **Treating every address as a valid reference breaks the fundamental
theorem.** Under `Recipe.anyLoc`, the syntactically typed `λ r. read r` is not
semantically well typed at `ref ⇒ int`. -/
theorem anyLoc_breaks_fundamental :
    HasType [] derefArg (.arrow .ref .int) ∧
    ¬ SemTyped Recipe.anyLoc [] derefArg (.arrow .ref .int) := by
  refine ⟨.lam (.read (.var rfl)), fun hs => ?_⟩
  have hE := semTyped_nil_iff.mp hs 0
  obtain ⟨b, hb, _, hf⟩ := (hE [] (Nat.le_refl _) derefArg [] (Reaches.refl _)).2 rfl
  simp only [derefArg, Expr.lam.injEq] at hb
  subst hb
  exact not_safeAndIn_of_reaches_stuck (h := []) (d := (.read (.loc 0), []))
    (Nat.le_refl _) (Reaches.refl _) ⟨rfl, rfl⟩ (hf 0 (Nat.le_refl 0) (.loc 0) ⟨0, rfl, trivial⟩)

/-- **The syntactic value interpretation cannot express encapsulation.**
`checkedRead` is in the standard semantic interpretation of `int ⇒ int` at
every world, but at no type and no world is it in the store-typed
syntactic-typability interpretation `SynVal`, nor in the expression closure
`safeAndIn` of `SynVal`. -/
theorem synVal_rejects_checkedRead :
    (∀ W, V Recipe.std (.arrow .int .int) W checkedRead) ∧
    (∀ τ W, ¬ SynVal τ W checkedRead) ∧
    (∀ τ W, ¬ safeAndIn (SynVal τ) W checkedRead) := by
  have hno : ∀ τ W, ¬ SynVal τ W checkedRead := fun τ W hs => by
    have := hs.castFree
    simp [checkedRead, Expr.castFree] at this
  refine ⟨checkedRead_V, hno, fun τ W hs => ?_⟩
  have hlen : (List.replicate W 0).length = W := List.length_replicate
  exact hno τ _ ((hs (List.replicate W 0) (Nat.le_of_eq hlen.symm) checkedRead _
    (Reaches.refl _)).2 rfl)

/-! ## Tightness counterexamples -/

/-- Adequacy needs the semantic-typing hypothesis: `read (cast 7)` violates it
(at every type) and is unsafe. -/
theorem adequacy_semTyped_hyp_tight :
    (∀ τ, ¬ SemTyped Recipe.std [] forgedRead τ) ∧ ¬ Safe (forgedRead, []) :=
  ⟨forgedRead_unsafe_ill_typed.2.1, forgedRead_unsafe_ill_typed.2.2⟩

/-- Adequacy (and syntactic type safety) need the empty context: `var 0` is
syntactically and semantically well typed at `int` in context `[int]` but is
stuck as a program. -/
theorem adequacy_nil_ctx_hyp_tight :
    HasType [.int] (.var 0) .int ∧ SemTyped Recipe.std [.int] (.var 0) .int ∧
    ¬ Safe (.var 0, []) := by
  refine ⟨.var rfl, ?_, not_safe_of_reaches_stuck (Reaches.refl _) ⟨rfl, rfl⟩⟩
  intro W γ hγ
  obtain ⟨v, rfl, hv⟩ := G_singleton.mp hγ
  obtain ⟨n, rfl⟩ := hv
  intro h _
  exact goodFrom_value rfl ⟨n, rfl⟩

/-- The fundamental theorem needs syntactic typing: the unguarded library
`λ n. read (cast n)` is not syntactically typable and not semantically well
typed at `int ⇒ int`. -/
theorem fundamental_hasType_hyp_tight :
    (∀ Γ τ, ¬ HasType Γ uncheckedRead τ) ∧
    ¬ SemTyped Recipe.std [] uncheckedRead (.arrow .int .int) := by
  refine ⟨fun Γ τ => not_hasType_of_not_castFree rfl Γ τ, fun hs => ?_⟩
  have hE := semTyped_nil_iff.mp hs 0
  obtain ⟨b, hb, _, hf⟩ := (hE [] (Nat.le_refl _) uncheckedRead [] (Reaches.refl _)).2 rfl
  simp only [uncheckedRead, Expr.lam.injEq] at hb
  subst hb
  exact not_safeAndIn_of_reaches_stuck (h := []) (d := (.read (.loc 7), []))
    (Nat.le_refl _) (by reach) ⟨rfl, rfl⟩ (hf 0 (Nat.le_refl 0) (.num 7) ⟨7, rfl⟩)

/-- The client hypothesis is needed (for let-compatibility and both linking
corollaries): with the semantically typed library `7`, the client
`read (cast x)` (syntactically and semantically untypable in `[int]` at every
type) makes the linked program unsafe and not semantically typed. -/
theorem client_hyp_tight :
    (∀ τ, ¬ HasType [.int] readCastVar τ) ∧
    (∀ τ, ¬ SemTyped Recipe.std [.int] readCastVar τ) ∧
    SemTyped Recipe.std [] (.num 7) .int ∧
    ¬ SemTyped Recipe.std [] (.app (.lam readCastVar) (.num 7)) .int ∧
    ¬ Safe (.app (.lam readCastVar) (.num 7), []) := by
  refine ⟨fun τ => not_hasType_of_not_castFree rfl _ τ, fun τ hs => ?_, ?_, fun hs => ?_, ?_⟩
  · exact not_safeAndIn_of_reaches_stuck (h := []) (d := (.read (.loc 7), []))
      (Nat.le_refl _) (by reach) ⟨rfl, rfl⟩ (hs 0 [.num 7] ⟨⟨7, rfl⟩, trivial⟩)
  · rw [semTyped_nil_iff]
    intro W h _
    exact goodFrom_value rfl ⟨7, rfl⟩
  · exact not_safeAndIn_of_reaches_stuck (h := []) (d := (.read (.loc 7), []))
      (Nat.le_refl _) (by reach) ⟨rfl, rfl⟩ (semTyped_nil_iff.mp hs 0)
  · exact not_safe_of_reaches_stuck (d := (.read (.loc 7), [])) (by reach) ⟨rfl, rfl⟩

/-- The client `x 7` is semantically well typed in context `[int ⇒ int]`. -/
theorem callWith7_semTyped : SemTyped Recipe.std [.arrow .int .int] callWith7 .int := by
  intro W γ hγ
  obtain ⟨f, rfl, hf⟩ := G_singleton.mp hγ
  obtain ⟨b, rfl, _, hfun⟩ := hf
  intro h hW
  exact goodFrom_step (e₁ := substAt 0 (.num 7) b) (h₁ := h) rfl
    (hfun h.length hW (.num 7) ⟨7, rfl⟩ h (Nat.le_refl _))

theorem callWith7_hasType : HasType [.arrow .int .int] callWith7 .int :=
  .app (.var rfl) .num

/-- `λ n. read (cast n)` has no semantic type at all in the empty context. -/
theorem uncheckedRead_not_semTyped (σ : Ty) : ¬ SemTyped Recipe.std [] uncheckedRead σ := by
  intro hs
  have hE := semTyped_nil_iff.mp hs 0
  have hV := (hE [] (Nat.le_refl _) uncheckedRead [] (Reaches.refl _)).2 rfl
  cases σ with
  | int => obtain ⟨n, hn⟩ := hV; cases hn
  | ref => obtain ⟨l, hl, _⟩ := hV; cases hl
  | arrow α β =>
    obtain ⟨b, hb, _, hf⟩ := hV
    simp only [uncheckedRead, Expr.lam.injEq] at hb
    subst hb
    cases α with
    | int =>
      exact not_safeAndIn_of_reaches_stuck (h := []) (d := (.read (.loc 7), []))
        (Nat.le_refl _) (by reach) ⟨rfl, rfl⟩ (hf 0 (Nat.le_refl 0) (.num 7) ⟨7, rfl⟩)
    | ref =>
      exact not_safeAndIn_of_reaches_stuck (h := [0]) (d := (.read (.cast (.loc 0)), [0]))
        (Nat.le_refl _) (Reaches.refl _) ⟨rfl, rfl⟩
        (hf 1 (Nat.zero_le 1) (.loc 0) ⟨0, rfl, Nat.zero_lt_one⟩)
    | arrow γ δ =>
      obtain ⟨v, hv⟩ := V_std_inhabited_one (.arrow γ δ)
      obtain ⟨b', rfl, hb', hf'⟩ := hv
      exact not_safeAndIn_of_reaches_stuck (h := [0]) (d := (.read (.cast (.lam b')), [0]))
        (Nat.le_refl _) (Reaches.refl _) ⟨rfl, rfl⟩
        (hf 1 (Nat.zero_le 1) (.lam b') ⟨b', rfl, hb', hf'⟩)

/-- The library hypothesis is needed (for let-compatibility and both linking
corollaries): the client `x 7` is syntactically and semantically typed, the
unguarded library has no semantic type at all, and the linked program is
unsafe and not semantically typed. -/
theorem lib_hyp_tight :
    HasType [.arrow .int .int] callWith7 .int ∧
    SemTyped Recipe.std [.arrow .int .int] callWith7 .int ∧
    (∀ σ, ¬ SemTyped Recipe.std [] uncheckedRead σ) ∧
    ¬ SemTyped Recipe.std [] (.app (.lam callWith7) uncheckedRead) .int ∧
    ¬ Safe (.app (.lam callWith7) uncheckedRead, []) := by
  refine ⟨callWith7_hasType, callWith7_semTyped, uncheckedRead_not_semTyped,
    fun hs => ?_, ?_⟩
  · exact not_safeAndIn_of_reaches_stuck (h := []) (d := (.read (.loc 7), []))
      (Nat.le_refl _) (by reach) ⟨rfl, rfl⟩ (semTyped_nil_iff.mp hs 0)
  · exact not_safe_of_reaches_stuck (d := (.read (.loc 7), [])) (by reach) ⟨rfl, rfl⟩

/-- The linking corollaries need the client context to be the single library
variable: in the two-variable context `[int, int]`, `var 1` is syntactically
and semantically typed and the library `7` is semantically typed, yet the
linked program is stuck (the second variable is never bound). -/
theorem linking_single_var_ctx_tight :
    HasType [.int, .int] (.var 1) .int ∧ SemTyped Recipe.std [.int, .int] (.var 1) .int ∧
    SemTyped Recipe.std [] (.num 7) .int ∧ ¬ Safe (.app (.lam (.var 1)) (.num 7), []) := by
  refine ⟨.var rfl, fun W γ hγ => ?_, client_hyp_tight.2.2.1,
    not_safe_of_reaches_stuck (d := (.var 0, [])) (by reach) ⟨rfl, rfl⟩⟩
  match γ, hγ with
  | [v0, v1], ⟨_, ⟨n, hn⟩, _⟩ =>
    subst hn
    intro h _
    exact goodFrom_value rfl ⟨n, rfl⟩

/-- The linking corollaries need the library to be typed in the empty context:
the client `x` is typed in `[int]`, the library `var 0` is semantically typed,
but only in the non-empty context `[int]`, and the linked program is stuck. -/
theorem linking_lib_nil_ctx_tight :
    HasType [.int] (.var 0) .int ∧ SemTyped Recipe.std [.int] (.var 0) .int ∧
    ¬ Safe (.app (.lam (.var 0)) (.var 0), []) :=
  ⟨.var rfl, adequacy_nil_ctx_hyp_tight.2.1,
    not_safe_of_reaches_stuck (Reaches.refl _) ⟨rfl, rfl⟩⟩

/-- The linking corollaries need the client's variable type and the library's
type to agree: the client `read x` is typed with `x : ref`, the library `7` is
typed at `int`, and the linked program is stuck. -/
theorem linking_interface_match_tight :
    HasType [.ref] (.read (.var 0)) .int ∧ SemTyped Recipe.std [.ref] (.read (.var 0)) .int ∧
    SemTyped Recipe.std [] (.num 7) .int ∧ ¬ Safe (.app (.lam (.read (.var 0))) (.num 7), []) := by
  refine ⟨.read (.var rfl), fun W γ hγ => ?_, client_hyp_tight.2.2.1,
    not_safe_of_reaches_stuck (d := (.read (.num 7), [])) (by reach) ⟨rfl, rfl⟩⟩
  obtain ⟨v, rfl, l, rfl, hl⟩ := G_singleton.mp hγ
  intro h hW
  have hl' : l < h.length := Nat.lt_of_lt_of_le hl hW
  refine goodFrom_step (e₁ := .num h[l]) (h₁ := h)
    (by simp [substAll, substAllAt, step, Expr.isValue, List.getElem?_eq_getElem hl']) ?_
  exact goodFrom_value rfl ⟨_, rfl⟩

/-- `checkedRead_hasType_clients_safe` needs the client context to be the single
library variable: `var 1` is typed in `[int ⇒ int, int]`, yet linked with
`checkedRead` it is stuck. -/
theorem checkedRead_single_var_ctx_tight :
    HasType [.arrow .int .int, .int] (.var 1) .int ∧
    ¬ Safe (.app (.lam (.var 1)) checkedRead, []) :=
  ⟨.var rfl, not_safe_of_reaches_stuck (d := (.var 0, [])) (by reach) ⟨rfl, rfl⟩⟩

/-- The syntactic-client hypothesis of `checkedRead_hasType_clients_safe` is
needed: the ill-typed client `read (cast (f 0))` linked with `checkedRead` gets
stuck from the empty heap (`checkedRead 0` returns `0`, which is then used as
an address). -/
theorem checkedRead_client_hyp_tight :
    (∀ τ, ¬ HasType [.arrow .int .int] castResultClient τ) ∧
    ¬ Safe (.app (.lam castResultClient) checkedRead, []) := by
  refine ⟨fun τ => not_hasType_of_not_castFree rfl _ τ, ?_⟩
  exact not_safe_of_reaches_stuck (d := (.read (.loc 0), [])) (by reach) ⟨rfl, rfl⟩

/-- Kripke monotonicity needs `W ≤ W'`: with `W = 1`, `W' = 0` (so `W ≤ W'`
fails), `loc 0` is a valid reference at world 1 but not at world 0. -/
theorem V_std_mono_hyp_tight :
    ¬ (1 ≤ 0) ∧ V Recipe.std .ref 1 (.loc 0) ∧ ¬ V Recipe.std .ref 0 (.loc 0) :=
  ⟨by decide, ⟨0, rfl, Nat.zero_lt_one⟩,
    fun ⟨l, hl, hlt⟩ => by cases hl; exact Nat.not_lt_zero _ hlt⟩

/-- Kripke monotonicity needs `V Recipe.std τ W v`: with `0 ≤ 1`, `loc 1` is not
valid at world 0, and not at world 1 either. -/
theorem V_std_mono_val_hyp_tight :
    (0 ≤ 1) ∧ ¬ V Recipe.std .ref 0 (.loc 1) ∧ ¬ V Recipe.std .ref 1 (.loc 1) :=
  ⟨Nat.zero_le 1,
   fun ⟨_, hl, hlt⟩ => by cases hl; exact Nat.not_lt_zero _ hlt,
   fun ⟨_, hl, hlt⟩ => by cases hl; exact Nat.lt_irrefl _ hlt⟩

/-- The safety-only characterization needs the empty context: `var 0` is
semantically typed under `Recipe.safetyOnly` in context `[int]`, but it is not
safe from the empty heap. -/
theorem safetyOnly_nil_ctx_hyp_tight :
    SemTyped Recipe.safetyOnly [.int] (.var 0) .int ∧ ¬ (∀ h, Safe (.var 0, h)) := by
  refine ⟨fun W γ hγ => ?_, fun hs => not_safe_of_reaches_stuck (Reaches.refl _) ⟨rfl, rfl⟩ (hs [])⟩
  obtain ⟨v, rfl, n, rfl⟩ := G_singleton.mp hγ
  intro h _
  exact safe_of_isValue rfl

/-- `cast_of_int_var_not_semTyped_of_closureEnforcesValues_of_hasInvalidRef`
needs `ClosureEnforcesValues`: `Recipe.safetyOnly` has an invalid reference,
yet `cast x` is semantically typed under it in `[int]` at every type. -/
theorem cast_of_int_var_semTyped_safetyOnly :
    Recipe.safetyOnly.HasInvalidRef ∧
    ∀ τ, SemTyped Recipe.safetyOnly [.int] (.cast (.var 0)) τ := by
  refine ⟨⟨0, 0, Nat.lt_irrefl 0⟩, fun τ W γ hγ => ?_⟩
  obtain ⟨v, rfl, n, rfl⟩ := G_singleton.mp hγ
  intro h _
  exact safe_of_step (c' := (.loc n, h)) rfl (safe_of_isValue rfl)

/-- Positive control, and tightness of `HasInvalidRef`: under `Recipe.anyLoc`
(whose closure enforces values) `cast x` is semantically well typed at `ref` in
`[int]`. -/
theorem cast_of_int_var_semTyped_anyLoc_ref :
    Recipe.anyLoc.ClosureEnforcesValues ∧
    SemTyped Recipe.anyLoc [.int] (.cast (.var 0)) .ref := by
  refine ⟨fun _ _ _ h => valuesIn_of_safeAndIn h, fun W γ hγ => ?_⟩
  obtain ⟨v, rfl, hv⟩ := G_singleton.mp hγ
  obtain ⟨n, rfl⟩ := hv
  intro h _
  exact goodFrom_step (e₁ := .loc n) (h₁ := h) rfl (goodFrom_value rfl ⟨n, rfl, trivial⟩)

/-- `typing_relation_deriving_cast_of_int_var_unsound` needs its hypothesis
`hT`: `RestrictedCastRule` does not derive `[int] ⊢ cast (var 0) : τ` for any
`τ`, and it is sound for the standard model. -/
theorem typing_relation_hyp_tight :
    (∀ τ, ¬ RestrictedCastRule [.int] (.cast (.var 0)) τ) ∧
    (∀ Γ e τ, RestrictedCastRule Γ e τ → SemTyped Recipe.std Γ e τ) :=
  ⟨fun τ h => (by cases h), restrictedCastRule_sound⟩

/-! ## Non-vacuity witnesses -/

/-- Both sides of the safety-only characterization hold for `λ _. cast 7`
(at `int ⇒ ref`) and both fail for `read (cast 7)`. -/
theorem safetyOnly_semTyped_nil_iff_safe_nonvacuous :
    SemTyped Recipe.safetyOnly [] castSeven (.arrow .int .ref) ∧
    (∀ h, Safe (castSeven, h)) ∧
    ¬ SemTyped Recipe.safetyOnly [] forgedRead .int ∧ ¬ Safe (forgedRead, []) :=
  ⟨safetyOnly_breaks_fundamental_and_encapsulation.2.1, fun _ => safe_of_isValue rfl,
    fun hs => forgedRead_unsafe_ill_typed.2.2 (safetyOnly_semTyped_nil_iff_safe.mp hs []),
    forgedRead_unsafe_ill_typed.2.2⟩

/-- Adequacy's hypothesis holds for a closed non-value program that executes
the unsafe primitive. -/
theorem adequacy_nonvacuous : SemTyped Recipe.std [] (.app checkedRead (.num 0)) .int :=
  checkedRead_applied_semTyped 0

/-- The fundamental theorem's hypothesis holds for a closed program that
allocates and reads, and for an open client. -/
theorem fundamental_nonvacuous :
    HasType [] allocThenRead .int ∧ HasType [.arrow .int .int] callWith7 .int :=
  ⟨.app (.lam (.read (.var rfl))) (.alloc .num), callWith7_hasType⟩

/-- Let-compatibility's hypotheses hold together for the client `x 7` and the
encapsulated library. -/
theorem semTyped_let_compat_nonvacuous :
    SemTyped Recipe.std [.arrow .int .int] callWith7 .int ∧
    SemTyped Recipe.std [] checkedRead (.arrow .int .int) :=
  ⟨callWith7_semTyped, checkedRead_semTyped⟩

/-- The encapsulation principle's hypotheses hold together for the client
`x 7` and the encapsulated library. -/
theorem hasType_client_semTyped_lib_nonvacuous :
    HasType [.arrow .int .int] callWith7 .int ∧
    SemTyped Recipe.std [] checkedRead (.arrow .int .int) :=
  ⟨callWith7_hasType, checkedRead_semTyped⟩

/-- Kripke monotonicity's two hypotheses hold together non-trivially: a
reference (worlds `1 ≤ 2`) and a function on references (worlds `0 ≤ 1`). -/
theorem V_std_mono_nonvacuous :
    (1 ≤ 2 ∧ V Recipe.std .ref 1 (.loc 0)) ∧
    (0 ≤ 1 ∧ V Recipe.std (.arrow .ref .int) 0 derefArg) := by
  refine ⟨⟨Nat.le_succ 1, 0, rfl, Nat.zero_lt_one⟩, Nat.zero_le 1, ⟨_, rfl, rfl, fun W' _ v hv => ?_⟩⟩
  obtain ⟨l, rfl, hl⟩ := hv
  intro h hW
  have hl' : l < h.length := Nat.lt_of_lt_of_le hl hW
  apply goodFrom_step (e₁ := .num h[l]) (h₁ := h)
    (by simp [substAt, substAllAt, step, Expr.isValue, List.getElem?_eq_getElem hl'])
  exact goodFrom_value rfl ⟨_, rfl⟩

/-- The standard recipe satisfies both hypotheses of the general impossibility,
and the context `[int]` is inhabited at world 0, so the impossibility is not an
artifact of an empty context interpretation. -/
theorem cast_of_int_var_not_semTyped_nonvacuous :
    Recipe.std.ClosureEnforcesValues ∧ Recipe.std.HasInvalidRef ∧
    G Recipe.std [.int] 0 [.num 7] :=
  ⟨std_closureEnforcesValues, std_hasInvalidRef, ⟨7, rfl⟩, trivial⟩

/-- The context `[int]` is inhabited at world 0. -/
theorem cast_of_int_var_context_inhabited : G Recipe.std [.int] 0 [.num 7] :=
  ⟨⟨7, rfl⟩, trivial⟩

/-- The hypothesis `hT` of `typing_relation_deriving_cast_of_int_var_unsound`
holds for syntactic typing extended with the uniform root rule for `cast`. -/
theorem typing_relation_nonvacuous : withCastRootRule [.int] (.cast (.var 0)) .ref :=
  Or.inr ⟨.var 0, rfl, rfl, .var rfl⟩

/-- The structural constraints of the linking corollaries hold for the
client `x 7` (single variable of the library's type `int ⇒ int`) and the
closed library `checkedRead`. -/
theorem linking_structure_nonvacuous :
    HasType [.arrow .int .int] callWith7 .int ∧ (Expr.closedAt 0 checkedRead = true) :=
  ⟨callWith7_hasType, rfl⟩

/-! ## Boundary facts (evidence for non-claims) -/

/-- The empty typing context does not force syntactic closedness: `ifz 1 (var 0) 0`
has a free variable (in an unreachable branch) and is semantically well typed
at `int` in the empty context. -/
theorem semTyped_nil_open_dead_var :
    (Expr.ifz (.num 1) (.var 0) (.num 0)).closedAt 0 = false ∧
    SemTyped Recipe.std [] (.ifz (.num 1) (.var 0) (.num 0)) .int := by
  refine ⟨rfl, semTyped_nil_iff.mpr fun W h _ => ?_⟩
  exact goodFrom_step (e₁ := .num 0) (h₁ := h) rfl (goodFrom_value rfl ⟨0, rfl⟩)

/-- The client hypothesis of `checkedRead_hasType_clients_safe` is not minimal:
the client `checkedRead (f 0)` (which uses `cast`, so it has no syntactic type)
is semantically well typed in `[int ⇒ int]` and is safe from every heap when
linked with `checkedRead`. -/
theorem checkedClient_semTyped_safe_not_hasType :
    (∀ τ, ¬ HasType [.arrow .int .int] checkedClient τ) ∧
    SemTyped Recipe.std [.arrow .int .int] checkedClient .int ∧
    (∀ h, Safe (.app (.lam checkedClient) checkedRead, h)) := by
  have step_nv : ∀ {e0 : Expr}, e0.isValue = false → ∀ h0 : Heap,
      step (.app checkedRead e0) h0 = (step e0 h0).map fun c => (.app checkedRead c.1, c.2) := by
    intro e0 hvF h0
    conv => lhs; unfold step
    have hcr : checkedRead.isValue = true := rfl
    simp [hcr, hvF]
  -- If every execution of `e0` is safe and ends in a word, so is every
  -- execution of `checkedRead e0`.
  have aux : ∀ (c d : Config), Reaches c d → ∀ (e0 : Expr) (h0 : Heap),
      c = (.app checkedRead e0, h0) →
      (∀ e1 h1, Reaches (e0, h0) (e1, h1) →
        ¬ Stuck (e1, h1) ∧ (e1.isValue = true → V Recipe.std .int h1.length e1)) →
      ¬ Stuck d ∧ (d.1.isValue = true → V Recipe.std .int d.2.length d.1) := by
    intro c d hrd
    induction hrd with
    | refl =>
      intro e0 h0 hcfg hgood
      subst hcfg
      refine ⟨?_, fun hv => by cases hv⟩
      by_cases hv : e0.isValue = true
      · obtain ⟨n, rfl⟩ := (hgood e0 h0 (Reaches.refl _)).2 hv
        exact not_stuck_of_step (c' := (checkedBody n, h0)) rfl
      · have hnotst := (hgood e0 h0 (Reaches.refl _)).1
        have hvF : e0.isValue = false := by cases h' : e0.isValue <;> simp_all
        cases hst : step e0 h0 with
        | none => exact absurd ⟨hvF, hst⟩ hnotst
        | some p =>
          exact not_stuck_of_step (c' := (.app checkedRead p.1, p.2))
            (by rw [step_nv hvF, hst]; rfl)
    | step hs hr' ih =>
      intro e0 h0 hcfg hgood
      subst hcfg
      by_cases hv : e0.isValue = true
      · obtain ⟨n, rfl⟩ := (hgood e0 h0 (Reaches.refl _)).2 hv
        have hstep : step (.app checkedRead (.num n)) h0 = some (checkedBody n, h0) := rfl
        rw [hstep] at hs
        cases hs
        exact checkedBody_good n h0 _ _ hr'
      · have hvF : e0.isValue = false := by cases h' : e0.isValue <;> simp_all
        rw [step_nv hvF] at hs
        cases hst : step e0 h0 with
        | none => simp [hst] at hs
        | some p =>
          simp only [hst, Option.map_some] at hs
          cases hs
          exact ih p.1 p.2 rfl (fun e1 h1 hr1 => hgood e1 h1 (Reaches.step hst hr1))
  have hsem : SemTyped Recipe.std [.arrow .int .int] checkedClient .int := by
    intro W γ hγ
    obtain ⟨f, rfl, hf⟩ := G_singleton.mp hγ
    obtain ⟨b, rfl, _, hfun⟩ := hf
    intro h hW
    have hsub : substAll [.lam b] checkedClient = .app checkedRead (.app (.lam b) (.num 0)) := rfl
    rw [hsub]
    refine goodFrom_step (e₁ := .app checkedRead (substAt 0 (.num 0) b)) (h₁ := h) rfl ?_
    have hbody := hfun h.length hW (.num 0) ⟨0, rfl⟩ h (Nat.le_refl _)
    intro e' h' hr
    exact aux _ _ hr (substAt 0 (.num 0) b) h rfl hbody
  refine ⟨fun τ => not_hasType_of_not_castFree rfl _ τ, hsem, fun h => ?_⟩
  -- After one β-step the linked program is `checkedRead (checkedRead 0)`.
  refine safe_of_step (c' := (.app checkedRead (.app checkedRead (.num 0)), h)) rfl ?_
  intro d hr
  exact (aux _ _ hr (.app checkedRead (.num 0)) h rfl
    (checkedRead_applied_semTyped 0 0 [] trivial h (Nat.zero_le _))).1

/-- A stateful library whose safety rests on an invariant over a stored cell is
not semantically well typed in the standard model: after `cellBoundRead`
allocates its private cell, the model tests the returned closure on heaps in
which that cell holds an arbitrary word. -/
theorem cellBoundRead_not_semTyped :
    ¬ SemTyped Recipe.std [] cellBoundRead (.arrow .int .int) := by
  intro hs
  have hE := semTyped_nil_iff.mp hs 0
  have hV := (hE [] (Nat.le_refl _)
    (.lam (.ifz (.lt (.var 0) (.read (.loc 0))) (.num 0) (.read (.cast (.var 0))))) [0]
    (by reach)).2 rfl
  obtain ⟨b, hb, _, hf⟩ := hV
  simp only [Expr.lam.injEq] at hb
  subst hb
  exact not_safeAndIn_of_reaches_stuck (h := [7]) (d := (.read (.loc 5), [7]))
    (Nat.le_refl _) (by reach) ⟨rfl, rfl⟩ (hf 1 (Nat.le_refl 1) (.num 5) ⟨5, rfl⟩)

/-- `cellBoundRead` is nevertheless safe with the client `x 7` from every heap:
its rejection by the standard model reflects the model's inability to state an
invariant about a private cell, not an unsafe execution of this program. -/
theorem cellBoundRead_callWith7_safe (h : Heap) :
    Safe (.app (.lam callWith7) cellBoundRead, h) := by
  let body : Expr := .ifz (.lt (.var 0) (.read (.var 1))) (.num 0) (.read (.cast (.var 0)))
  let body' : Expr := .ifz (.lt (.var 0) (.read (.loc h.length))) (.num 0) (.read (.cast (.var 0)))
  refine safe_of_step
    (c' := (Expr.app (.lam callWith7) (.app (.lam (.lam body)) (.loc h.length)), h ++ [0])) rfl ?_
  refine safe_of_step (c' := (Expr.app (.lam callWith7) (.lam body'), h ++ [0])) rfl ?_
  refine safe_of_step (c' := (Expr.app (.lam body') (.num 7), h ++ [0])) rfl ?_
  refine safe_of_step (c' := (Expr.ifz (.lt (.num 7) (.read (.loc h.length))) (.num 0)
    (.read (.cast (.num 7))), h ++ [0])) rfl ?_
  refine safe_of_step (c' := (Expr.ifz (.lt (.num 7) (.num 0)) (.num 0)
    (.read (.cast (.num 7))), h ++ [0])) (by simp [step, Expr.isValue]) ?_
  refine safe_of_step (c' := (Expr.ifz (.num 0) (.num 0) (.read (.cast (.num 7))), h ++ [0])) rfl ?_
  exact safe_of_step (c' := (Expr.num 0, h ++ [0])) rfl (safe_of_isValue rfl)

/-- Safety from the empty heap does not imply semantic typing in the empty
context: `ifz size 0 (read (cast 99))` is safe from `[]` but has no semantic
type (it is stuck from the heap `[0]`). -/
theorem sizeZeroOrForged_safe_nil_not_semTyped :
    Safe (sizeZeroOrForged, []) ∧ ∀ τ, ¬ SemTyped Recipe.std [] sizeZeroOrForged τ := by
  refine ⟨?_, fun τ hs => ?_⟩
  · refine safe_of_step (c' := (.ifz (.num 0) (.num 0) (.read (.cast (.num 99))), [])) rfl ?_
    exact safe_of_step (c' := (.num 0, [])) rfl (safe_of_isValue rfl)
  · exact not_safeAndIn_of_reaches_stuck (h := [0]) (d := (.read (.loc 99), [0]))
      (Nat.zero_le _) (by reach) ⟨rfl, rfl⟩ (semTyped_nil_iff.mp hs 0)

/-- Semantic ill-typedness of a forged read depends on the context:
`read (cast 0)` is semantically well typed at `int` in context `[ref]` (a `ref`
assumption forces cell 0 to be allocated) but has no semantic type in the empty
context. -/
theorem read_cast_zero_semTyped_ref_ctx :
    SemTyped Recipe.std [.ref] (.read (.cast (.num 0))) .int ∧
    ∀ τ, ¬ SemTyped Recipe.std [] (.read (.cast (.num 0))) τ := by
  refine ⟨fun W γ hγ => ?_, fun τ hs => ?_⟩
  · obtain ⟨v, rfl, l, rfl, hl⟩ := G_singleton.mp hγ
    intro h hW
    have h0 : 0 < h.length := Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt (Nat.zero_le l) hl) hW
    refine goodFrom_step (e₁ := .read (.loc 0)) (h₁ := h) rfl ?_
    refine goodFrom_step (e₁ := .num h[0]) (h₁ := h)
      (by simp [step, Expr.isValue, List.getElem?_eq_getElem h0]) ?_
    exact goodFrom_value rfl ⟨_, rfl⟩
  · exact not_safeAndIn_of_reaches_stuck (h := []) (d := (.read (.loc 0), []))
      (Nat.le_refl _) (by reach) ⟨rfl, rfl⟩ (semTyped_nil_iff.mp hs 0)

/-- The arrow case of `V` has a syntactic closedness side condition: the
abstraction `λ x. ifz 0 x y` (with `y` free in dead code) is excluded at every
world, although applying it to any word is safe from every heap. -/
theorem V_std_rejects_open_dead_lam :
    (∀ W, ¬ V Recipe.std (.arrow .int .int) W (.lam (.ifz (.num 0) (.var 0) (.var 1)))) ∧
    (∀ n h, Safe (.app (.lam (.ifz (.num 0) (.var 0) (.var 1))) (.num n), h)) := by
  refine ⟨fun W ⟨b, hb, hc, _⟩ => ?_, fun n h => ?_⟩
  · simp only [Expr.lam.injEq] at hb
    subst hb
    exact absurd hc (by decide)
  · refine safe_of_step (c' := (.ifz (.num 0) (.num n) (.var 0), h)) rfl ?_
    exact safe_of_step (c' := (.num n, h)) rfl (safe_of_isValue rfl)

/-- Under `Recipe.nonKripke`, `probeCellZero` itself is not semantically typed
at `ref ⇒ int` in the empty context (which quantifies over all worlds,
including world 2). -/
theorem probeCellZero_not_semTyped_nonKripke_nil :
    ¬ SemTyped Recipe.nonKripke [] probeCellZero (.arrow .ref .int) := by
  intro hs
  exact nonKripke_breaks_monotonicity_and_fundamental.2.1
    ((semTyped_nil_iff.mp hs 2 [0, 0] (Nat.le_refl _) probeCellZero [0, 0] (Reaches.refl _)).2 rfl)

/-- The store-typed syntactic interpretation admits safe runtime closures that
capture allocated references: from every heap, every value reached by
`(λ r. λ _. read r) (alloc 5)` is in `SynVal (int ⇒ int)`, and the run is safe. -/
theorem captureRef_safeAndIn_synVal : safeAndIn (SynVal (.arrow .int .int)) 0 captureRef := by
  intro h _
  refine goodFrom_step (e₁ := .app (.lam (.lam (.read (.var 1)))) (.loc h.length))
    (h₁ := h ++ [5]) rfl ?_
  refine goodFrom_step (e₁ := .lam (.read (.loc h.length))) (h₁ := h ++ [5]) rfl ?_
  exact goodFrom_value rfl ⟨rfl, .lam (.read (.loc (by simp)))⟩

/-! ## Boundary facts for the linking results -/

/-- Semantic `lam`-introduction needs a closedness side condition, while
semantic let-compatibility does not. The open-dead-code client
`ifz 1 (var 1) 0` is semantically typed at `int` in `[int]`, yet
`λ. ifz 1 (var 1) 0` is not semantically typed at `int ⇒ int` in the empty
context (the function case of `V` requires `closedAt 1` of the body), whereas
the linked program `(λ. ifz 1 (var 1) 0) 7` is semantically typed at `int` in
the empty context (call-by-value β-reduction never places `λ. c` in `V`). -/
theorem semTyped_lam_compat_needs_closedAt :
    SemTyped Recipe.std [.int] (.ifz (.num 1) (.var 1) (.num 0)) .int ∧
    ¬ SemTyped Recipe.std [] (.lam (.ifz (.num 1) (.var 1) (.num 0))) (.arrow .int .int) ∧
    SemTyped Recipe.std [] (.app (.lam (.ifz (.num 1) (.var 1) (.num 0))) (.num 7)) .int := by
  refine ⟨?_, ?_, semTyped_let_compat ?_ (fundamental_hasType_semTyped .num)⟩
  · intro W γ hγ
    obtain ⟨v, rfl, n, rfl⟩ := G_singleton.mp hγ
    intro h _
    exact goodFrom_step (e₁ := .num 0) (h₁ := h) rfl (goodFrom_value rfl ⟨0, rfl⟩)
  · intro hs
    have hV := (semTyped_nil_iff.mp hs 0 [] (Nat.le_refl _)
      (.lam (.ifz (.num 1) (.var 1) (.num 0))) [] (Reaches.refl _)).2 rfl
    obtain ⟨b, hb, hc, _⟩ := hV
    simp only [Expr.lam.injEq] at hb
    subst hb
    exact absurd hc (by decide)
  · intro W γ hγ
    obtain ⟨v, rfl, n, rfl⟩ := G_singleton.mp hγ
    intro h _
    exact goodFrom_step (e₁ := .num 0) (h₁ := h) rfl (goodFrom_value rfl ⟨0, rfl⟩)

/-- Under `Recipe.nonKripke`, linking a client semantically typed in `[σ]`
with a library semantically typed at `σ` in the empty context is still safe
from every heap: with an empty ambient context there is no closing
substitution that would have to survive the library's allocations. Contrast
`safetyOnly_breaks_let_compat`, where this fails for `Recipe.safetyOnly`. -/
theorem nonKripke_semTyped_client_nil_safe {σ τ : Ty} {c lib : Expr}
    (hc : SemTyped Recipe.nonKripke [σ] c τ)
    (hlib : SemTyped Recipe.nonKripke [] lib σ) (h : Heap) :
    Safe (.app (.lam c) lib, h) := by
  have hb_val : (Expr.lam c).isValue = true := rfl
  have hgood := bind_goodFrom (K := fun x => .app (.lam c) x)
    (Q := V Recipe.nonKripke σ) (P := V Recipe.nonKripke τ)
    (fun _ => rfl)
    (fun {e₀ h₀} hvF => by conv => lhs; unfold step; simp [hb_val, hvF])
    (semTyped_nil_iff.mp hlib 0 h (Nat.zero_le _))
    (fun v h₁ _ hv hQv => by
      have hstep : step (.app (.lam c) v) h₁ = some (substAt 0 v c, h₁) := by
        conv => lhs; unfold step; simp [hb_val, hv]
      exact goodFrom_step hstep (hc h₁.length [v] ⟨hQv, trivial⟩ h₁ (Nat.le_refl _)))
  exact fun d hr => (hgood d.1 d.2 hr).1

/-- Under `Recipe.nonKripke`, semantic let-compatibility fails in a non-empty
ambient context: in `[ref ⇒ int]`, the client `f r` (`var 1 (var 0)`) is
semantically typed at `int` in `[ref, ref ⇒ int]` and the library `alloc 0` is
semantically typed at `ref`, but `(λ r. f r) (alloc 0)` is not semantically
typed at `int` in `[ref ⇒ int]` (instantiate `f := probeCellZero` at world 1). -/
theorem nonKripke_breaks_open_let_compat :
    SemTyped Recipe.nonKripke [.ref, .arrow .ref .int] (.app (.var 1) (.var 0)) .int ∧
    SemTyped Recipe.nonKripke [.arrow .ref .int] (.alloc (.num 0)) .ref ∧
    ¬ SemTyped Recipe.nonKripke [.arrow .ref .int]
        (.app (.lam (.app (.var 1) (.var 0))) (.alloc (.num 0))) .int := by
  refine ⟨?_, ?_, ?_⟩
  · intro W γ hγ h hW
    rcases γ with _ | ⟨vr, _ | ⟨vf, _ | _⟩⟩ <;> try (simp [G] at hγ; done)
    obtain ⟨⟨l, rfl, hl⟩, ⟨b, rfl, _, hfun⟩, _⟩ := hγ
    have hsub : substAll [.loc l, .lam b] (.app (.var 1) (.var 0)) = .app (.lam b) (.loc l) := rfl
    rw [hsub]
    exact goodFrom_step (e₁ := substAt 0 (.loc l) b) (h₁ := h) rfl
      (hfun W rfl (.loc l) ⟨l, rfl, hl⟩ h hW)
  · intro W γ _ h _
    have hsub : substAll γ (.alloc (.num 0)) = .alloc (.num 0) := rfl
    rw [hsub]
    exact goodFrom_step (e₁ := .loc h.length) (h₁ := h ++ [0]) rfl
      (goodFrom_value rfl ⟨h.length, rfl, show h.length < (h ++ [0]).length by simp⟩)
  · intro hs
    exact not_safeAndIn_of_reaches_stuck (h := [0]) (d := (.read (.loc 99), [0, 1]))
      (Nat.le_refl _) (by reach) ⟨rfl, rfl⟩
      (hs 1 [probeCellZero] ⟨probeCellZero_V_nonKripke_one, trivial⟩)

/-- Exact characterization of the store-typed syntactic value interpretation:
`SynVal τ W v` holds iff `v` is a value that is store-typed at `τ` in the empty
context under store typing `W`. -/
theorem synVal_iff_isValue_and_hasTypeStore (τ : Ty) (W : Nat) (v : Expr) :
    SynVal τ W v ↔ v.isValue = true ∧ HasTypeStore W [] v τ := by
  cases τ with
  | int =>
    constructor
    · rintro ⟨n, rfl⟩; exact ⟨rfl, .num⟩
    · rintro ⟨hv, ht⟩
      cases v <;> simp [Expr.isValue] at hv
      · nomatch ht
      · exact ⟨_, rfl⟩
      · nomatch ht
  | ref =>
    constructor
    · rintro ⟨l, rfl, hl⟩; exact ⟨rfl, .loc hl⟩
    · rintro ⟨hv, ht⟩
      cases v <;> simp [Expr.isValue] at hv
      · nomatch ht
      · nomatch ht
      · cases ht with
        | loc hl => exact ⟨_, rfl, hl⟩
  | arrow σ ρ => rfl

/-- `HasInvalidRef` is needed only for the type `ref`: under `Recipe.anyLoc`
(which has no invalid reference but whose closure enforces values), `cast x`
with `x : int` is still not semantically typed at `int` or at any arrow type. -/
theorem cast_of_int_var_not_semTyped_anyLoc_nonRef :
    ¬ Recipe.anyLoc.HasInvalidRef ∧
    ¬ SemTyped Recipe.anyLoc [.int] (.cast (.var 0)) .int ∧
    ∀ σ τ, ¬ SemTyped Recipe.anyLoc [.int] (.cast (.var 0)) (.arrow σ τ) := by
  refine ⟨fun ⟨_, _, h⟩ => h trivial, ?_, fun σ τ hs => ?_⟩
  · intro hs
    have hV := (hs 0 [.num 0] ⟨⟨0, rfl⟩, trivial⟩ [] (Nat.le_refl _) (.loc 0) [] (by reach)).2 rfl
    obtain ⟨n, hn⟩ := hV; cases hn
  · have hV := (hs 0 [.num 0] ⟨⟨0, rfl⟩, trivial⟩ [] (Nat.le_refl _) (.loc 0) [] (by reach)).2 rfl
    obtain ⟨b, hb, _⟩ := hV; cases hb

end Toy.SemType
