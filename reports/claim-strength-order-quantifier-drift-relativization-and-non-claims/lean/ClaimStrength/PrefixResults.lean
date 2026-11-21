import ClaimStrength.Complete

/-!
# Results on quantifier prefixes

Unrelativized prefixes are relativized prefixes over the trivial signature (one domain class,
interpreted as all of `α`; one premise, interpreted as true). Schematic entailment `SEntailsAt`
uses environment semantics. If no variable is bound twice in `φ` and every variable is bound
exactly once in `ψ`, the prefix criterion implies `SEntailsAt α φ ψ` at every base type `α`
(vacuously so on an empty base type when `n ≥ 1`). If no variable is bound twice in `φ` or in `ψ`,
the criterion follows from `SEntailsAt α φ ψ` at every base type `α` with two distinct elements. On
a base type with at most one element every two prefixes are equivalent.
-/

namespace Toy.ClaimStrength

variable {n : Nat} {K P : Type} {α : Type}

/-! ## Decision procedures -/

theorem wfB_iff (φ : List (Binder n K)) : wfB φ = true ↔ WF φ := by
  simp [wfB, WF, List.all_eq_true, List.mem_finRange]

theorem prefixCritB_iff (φ ψ : List (Binder n K)) : prefixCritB φ ψ = true ↔ PrefixCrit φ ψ := by
  simp only [prefixCritB, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
    PrefixCrit, UnivReflected, SkolemOrderPreserved, Precedes]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun v hv => ?_, fun u v hv hu hu' hp => ?_⟩
    · have := h1 v; simp [hv] at this; exact this
    · have := h2 u v; simp [hv, hu, hu', hp] at this; exact this
  · rintro ⟨h1, h2⟩
    refine ⟨fun v => ?_, fun u v => ?_⟩
    · by_cases hv : qOf ψ v = some .all
      · simp [hv, h1 v hv]
      · simp [hv]
    · by_cases hv : qOf φ v = some .ex
      · by_cases hu : qOf φ u = some .all
        · by_cases hu' : qOf ψ u = some .all
          · by_cases hp : precL (bvars φ) u v = true
            · simp [hv, hu, hu', hp, h2 u v hv hu hu' hp]
            · simp [hp]
          · simp [hu']
        · simp [hu]
      · simp [hv]

/-! ## Unrelativized prefixes as shapes over the trivial signature -/

/-- The trivial class interpretation: every domain is all of `α`. -/
def trivI (α : Type) : Unit → α → Prop := fun _ _ => True

/-- The trivial premise interpretation. -/
def trivJ (n : Nat) (α : Type) : Unit → (Fin n → α) → Prop := fun _ _ => True

/-- The shape of an unrelativized prefix, with the trivial premise. -/
def toShape (φ : Prefix n) : Shape n Unit Unit := ⟨φ, ()⟩

theorem eval_iff_holds (φ : Prefix n) (R : (Fin n → α) → Prop) (ρ : Fin n → α) :
    eval φ R ρ ↔ Holds (trivI α) (trivJ n α) (toShape φ) R ρ :=
  ⟨evalR_mono _ (fun _ hσ _ => hσ) φ ρ, evalR_mono _ (fun _ hσ => hσ trivial) φ ρ⟩

/-- Evaluation depends on the environment only at variables the prefix does not bind. -/
theorem evalR_env_irrelevant (I : K → α → Prop) (L : (Fin n → α) → Prop) :
    ∀ (φ : List (Binder n K)) (ρ ρ' : Fin n → α), (∀ v, v ∉ bvars φ → ρ v = ρ' v) →
      evalR I φ L ρ → evalR I φ L ρ'
  | [], ρ, ρ', h, hφ => by
    have : ρ = ρ' := funext fun v => h v (by simp [bvars])
    exact this ▸ hφ
  | b :: rest, ρ, ρ', h, hφ =>
    quantify_mono (fun a _ => evalR_env_irrelevant I L rest _ _ (fun v hv => by
      by_cases hvb : v = b.var
      · subst hvb; simp
      · rw [upd_ne _ hvb, upd_ne _ hvb]
        refine h v ?_
        rw [bvars_cons]
        intro hm
        rcases List.mem_cons.1 hm with e | e
        · exact hvb e
        · exact hv e)) hφ

/-- If a prefix binds every variable (repetitions allowed), the environment is irrelevant. -/
theorem eval_env_irrelevant_of_covers {φ : Prefix n} (hcov : ∀ v : Fin n, v ∈ bvars φ)
    (R : (Fin n → α) → Prop) (ρ ρ' : Fin n → α) : eval φ R ρ ↔ eval φ R ρ' :=
  ⟨evalR_env_irrelevant _ R φ ρ ρ' (fun v hv => absurd (hcov v) hv),
    evalR_env_irrelevant _ R φ ρ' ρ (fun v hv => absurd (hcov v) hv)⟩

/-- For prefixes that bind every variable, schematic entailment at `α` is entailment at any one
fixed environment `ρ₀` (which exists iff `α` is inhabited or `n = 0`): the quantification over
environments in `SEntailsAt` only matters for prefixes that leave a variable free, and for an
empty `α` (where it makes `SEntailsAt` vacuous). -/
theorem sentailsAt_iff_fixed_env_of_covers {φ ψ : Prefix n} (hφ : ∀ v : Fin n, v ∈ bvars φ)
    (hψ : ∀ v : Fin n, v ∈ bvars ψ) (ρ₀ : Fin n → α) :
    SEntailsAt α φ ψ ↔ ∀ R : (Fin n → α) → Prop, eval φ R ρ₀ → eval ψ R ρ₀ :=
  ⟨fun h R => h R ρ₀, fun h R ρ hR =>
    (eval_env_irrelevant_of_covers hψ R ρ₀ ρ).1
      (h R ((eval_env_irrelevant_of_covers hφ R ρ ρ₀).1 hR))⟩

/-- Vacuity on an empty base type: if `α` is empty and `n ≥ 1`, every prefix schematically
entails every other (there is no environment `Fin (n + 1) → α`). -/
theorem sentailsAt_of_isEmpty (hα : α → False) (φ ψ : Prefix (n + 1)) : SEntailsAt α φ ψ :=
  fun _ ρ _ => (hα (ρ 0)).elim

/-- In contrast, the closed (environment-free) implication from `∀x, P x` to `∃x, P x` holds
for every predicate `P` on `α` iff `α` is nonempty; it fails on an empty type. -/
theorem closed_forall_imp_exists_iff_nonempty (α : Type) :
    (∀ P : α → Prop, (∀ x, P x) → ∃ x, P x) ↔ Nonempty α :=
  ⟨fun h => let ⟨x, _⟩ := h (fun _ => True) (fun _ => trivial); ⟨x⟩,
    fun ⟨a⟩ _ hP => ⟨a, hP a⟩⟩

/-! ## The prefix criterion -/

/-- **Sufficiency.** For prefixes `φ`, `ψ` on the variables `Fin n` (same matrix, variables
matched by index), if no variable is bound twice in `φ`, every variable is bound exactly once in
`ψ`, and the prefix criterion holds, then `SEntailsAt α φ ψ` holds at every base type `α` (for
every matrix and every environment; vacuous when `α` is empty and `n ≥ 1`). -/
theorem prefixCrit_sound_of_nodup_wf {φ ψ : Prefix n} (hφ : (bvars φ).Nodup) (hψ : WF ψ)
    (h : PrefixCrit φ ψ) : SEntailsAt α φ ψ := by
  suffices aux : ∀ (k : Nat) (ψ' : Prefix n), ψ'.length ≤ k →
      (bvars ψ').Nodup →
      (∀ v, v ∈ bvars φ → v ∈ bvars ψ') →
      PrefixCrit φ ψ' →
      ∀ R ρ, eval φ R ρ → eval ψ' R ρ from
    aux ψ.length ψ (Nat.le_refl _) hψ.1 (fun v _ => hψ.2 v) h
  intro k
  induction k with
  | zero =>
    intro ψ' hk _ hsub _ R ρ hR
    have hψnil : ψ' = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hk)
    subst hψnil
    have hφnil : φ = [] := nil_of_no_vars (fun v hv => by simpa [bvars] using hsub v hv)
    subst hφnil
    exact hR
  | succ k ih =>
    intro ψ' hk hndψ hsub hcrit R ρ hR
    by_cases hextra : ∃ y, y ∈ bvars ψ' ∧ y ∉ bvars φ
    · obtain ⟨y, hyψ, hyφ⟩ := hextra
      obtain ⟨b', hb'⟩ := bOf_of_mem hyψ
      have hb'q : b'.q = .ex := by
        cases hq : b'.q with
        | ex => rfl
        | all =>
          have := hcrit.1 y (by rw [qOf_of_bOf hb', hq])
          rw [qOf, bOf_eq_none hyφ] at this
          cases this
      have hlen : (eraseVar ψ' y).length ≤ k :=
        Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (length_eraseVar_lt hyψ) hk)
      have hsub' : ∀ v, v ∈ bvars φ → v ∈ bvars (eraseVar ψ' y) := fun v hv =>
        mem_bvars_eraseVar.2 ⟨hsub v hv, fun e => hyφ (e ▸ hv)⟩
      have hcrit' : PrefixCrit φ (eraseVar ψ' y) := by
        have hc := prefixCrit_eraseVar y hcrit
        rwa [eraseVar_of_not_mem hyφ] at hc
      have hstep := ih (eraseVar ψ' y) hlen (nodup_eraseVar y hndψ) hsub' hcrit' R ρ hR
      exact evalR_intro_ex (fun (_ : Unit) (_ : α) => True) R ψ' y b' (ρ y) ρ
        hndψ hb' hb'q trivial (by rwa [upd_self])
    · have hsame : ∀ v, v ∈ bvars φ ↔ v ∈ bvars ψ' := fun v =>
        ⟨hsub v, fun hv => Classical.byContradiction fun hnv => hextra ⟨v, hv, hnv⟩⟩
      have hne : Nonempty α ∨ φ = [] := by
        cases φ with
        | nil => exact Or.inr rfl
        | cons b _ => exact Or.inl ⟨ρ b.var⟩
      rcases hne with hne | rfl
      · obtain ⟨a0⟩ := hne
        exact rcrit_sound_aux (fun (_ : Unit) (_ : α) => True) (fun _ _ => true) (fun _ _ => true)
          (fun _ _ _ _ _ => trivial) (fun _ _ _ => ⟨a0, trivial, trivial⟩)
          φ.length φ ψ' (Nat.le_refl _) hφ hndψ hsame hcrit
          (fun _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ => rfl)
          R R (fun _ h => h) ρ hR
      · have hψnil : ψ' = [] :=
          nil_of_no_vars (fun v hv => by simpa [bvars] using (hsame v).2 hv)
        subst hψnil
        exact hR

/-- **Necessity.** For prefixes `φ`, `ψ` on the variables `Fin n` in which no variable is bound
twice, and a base type `α` with two distinct elements, `SEntailsAt α φ ψ` implies the prefix
criterion. -/
theorem prefixCrit_necessary_of_two_point_nodup (hα : ∃ a b : α, a ≠ b) {φ ψ : Prefix n}
    (hφ : (bvars φ).Nodup) (hψ : (bvars ψ).Nodup) (h : SEntailsAt α φ ψ) :
    PrefixCrit φ ψ := by
  classical
  obtain ⟨a1, a2, h12⟩ := hα
  have hneU : ∀ (ξ : Prefix n), ∀ c ∈ ξ, ∃ a : α, (fun (_ : Unit) (_ : α) => True) c.dom a :=
    fun _ _ _ => ⟨a1, trivial⟩
  have hUR : UnivReflected φ ψ := by
    intro v hv
    obtain ⟨b', hb', hb'q⟩ := qOf_eq_some.1 hv
    let R : (Fin n → α) → Prop := fun σ => σ v = a1
    have hRdep : ∀ σ σ', σ v = σ' v → R σ → R σ' := fun _ _ e hr => e.symm.trans hr
    let ρ0 : Fin n → α := fun _ => a1
    have hψfalse : ¬ eval ψ R ρ0 := by
      intro hψR
      rw [eval, evalR_only_var _ hψ hb' (hneU ψ) hRdep ρ0, hb'q] at hψR
      have e2 : upd ρ0 v a2 v = a1 := hψR a2 trivial
      rw [upd_same] at e2
      exact h12 e2.symm
    by_cases hvφ : v ∈ bvars φ
    · obtain ⟨b, hb⟩ := bOf_of_mem hvφ
      rw [qOf_of_bOf hb]
      cases hbq : b.q with
      | all => rfl
      | ex =>
        exfalso
        apply hψfalse (h R ρ0 _)
        rw [eval, evalR_only_var _ hφ hb (hneU φ) hRdep ρ0, hbq]
        exact ⟨a1, trivial, upd_same _ _ _⟩
    · exfalso
      apply hψfalse (h R ρ0 _)
      rw [eval, evalR_keepVars _ R (fun x => decide (x = v))
        (fun σ σ' hs => hRdep σ σ' (hs v (by simp))) φ ρ0 (hneU φ)]
      rw [keepVars_nil_of (s := fun x => decide (x = v))
        (fun b hb e => hvφ ((of_decide_eq_true e) ▸ List.mem_map_of_mem hb))]
      rfl
  refine ⟨hUR, ?_⟩
  intro u v hv hu hu' hp
  apply Classical.byContradiction
  intro hnp
  have huv : u ≠ v := by intro e; subst e; rw [hu] at hv; simp at hv
  obtain ⟨bu, hbu, hbuq⟩ := qOf_eq_some.1 hu
  obtain ⟨bv, hbv, hbvq⟩ := qOf_eq_some.1 hv
  obtain ⟨bu', hbu', hbu'q⟩ := qOf_eq_some.1 hu'
  let g : α → α := fun a => if a = a1 then a1 else a2
  let R : (Fin n → α) → Prop := fun σ => σ v = g (σ u)
  have hRdep : ∀ σ σ', σ u = σ' u → σ v = σ' v → R σ → R σ' := by
    intro σ σ' e1 e2 hσ; show σ' v = g (σ' u); rw [← e1, ← e2]; exact hσ
  let ρ0 : Fin n → α := fun _ => a1
  have hφR : eval φ R ρ0 := by
    rw [eval, evalR_only_two_vars _ hφ huv hbu hbv hp (hneU φ) hRdep ρ0, hbuq, hbvq]
    intro a _
    refine ⟨g a, trivial, ?_⟩
    show upd (upd ρ0 u a) v (g a) v = g (upd (upd ρ0 u a) v (g a) u)
    rw [upd_same, upd_ne _ huv, upd_same]
  have hψR := h R ρ0 hφR
  have g1 : g a1 = a1 := ite_eq_left rfl
  have g2 : g a2 = a2 := ite_eq_right (Ne.symm h12)
  by_cases hvψ : v ∈ bvars ψ
  · obtain ⟨bv', hbv'⟩ := bOf_of_mem hvψ
    have hbv'q : bv'.q = .ex := by
      cases hq : bv'.q with
      | ex => rfl
      | all =>
        have := hUR v (by rw [qOf_of_bOf hbv', hq])
        rw [hv] at this; simp at this
    have hp' : precL (bvars ψ) v u = true :=
      (precL_total huv (mem_bvars_of_bOf hbu') hvψ).resolve_left hnp
    rw [eval, evalR_only_two_vars _ hψ (Ne.symm huv) hbv' hbu' hp' (hneU ψ)
      (fun σ σ' e1 e2 => hRdep σ σ' e2 e1) ρ0, hbv'q, hbu'q] at hψR
    obtain ⟨c, _, hc⟩ := hψR
    have e1 : upd (upd ρ0 v c) u a1 v = g (upd (upd ρ0 v c) u a1 u) := hc a1 trivial
    have e2 : upd (upd ρ0 v c) u a2 v = g (upd (upd ρ0 v c) u a2 u) := hc a2 trivial
    rw [upd_ne _ (Ne.symm huv), upd_same, upd_same] at e1 e2
    rw [g1] at e1; rw [g2] at e2
    exact h12 (e1.symm.trans e2)
  · rw [eval, evalR_only_two_vars_free _ hψ hbu' hvψ (hneU ψ) hRdep ρ0, hbu'q] at hψR
    have e2 : upd ρ0 u a2 v = g (upd ρ0 u a2 u) := hψR a2 trivial
    rw [upd_ne _ (Ne.symm huv), upd_same, g2] at e2
    exact h12 e2

/-- Schematic entailment at a base type with two distinct elements is characterized by the
prefix criterion, when no variable is bound twice in `φ` and every variable is bound exactly once
in `ψ`. -/
theorem sentailsAt_iff_prefixCrit_of_two_point_nodup_wf (hα : ∃ a b : α, a ≠ b) {φ ψ : Prefix n}
    (hφ : (bvars φ).Nodup) (hψ : WF ψ) : SEntailsAt α φ ψ ↔ PrefixCrit φ ψ :=
  ⟨prefixCrit_necessary_of_two_point_nodup hα hφ hψ.1, prefixCrit_sound_of_nodup_wf hφ hψ⟩

theorem eval_subsingleton [Subsingleton α] :
    ∀ (φ : Prefix n) (R : (Fin n → α) → Prop) (ρ : Fin n → α), eval φ R ρ ↔ R ρ
  | [], _, _ => Iff.rfl
  | b :: rest, R, ρ => by
    show quantify b.q (fun _ => True) (fun a => eval rest R (upd ρ b.var a)) ↔ R ρ
    have hu : ∀ a, upd ρ b.var a = ρ := fun a => funext fun _ => Subsingleton.elim _ _
    rw [quantify_congr (P' := fun _ => R ρ)
      (fun a _ => by rw [hu a]; exact eval_subsingleton rest R ρ)]
    exact quantify_const ⟨ρ b.var, trivial⟩

/-- On a base type with at most one element, every prefix entails every other (the theorem has
no hypothesis on the prefixes). -/
theorem sentailsAt_of_subsingleton [Subsingleton α] (φ ψ : Prefix n) : SEntailsAt α φ ψ :=
  fun R ρ h => (eval_subsingleton ψ R ρ).2 ((eval_subsingleton φ R ρ).1 h)

/-- Restricting `SEntails` to base types with two distinct elements does not change it. -/
theorem sentails_iff_twoPoint_types (φ ψ : Prefix n) :
    SEntails φ ψ ↔ ∀ α : Type, (∃ a b : α, a ≠ b) → SEntailsAt α φ ψ := by
  refine ⟨fun h α _ => h α, fun h α => ?_⟩
  by_cases h2 : ∃ a b : α, a ≠ b
  · exact h α h2
  · have : Subsingleton α :=
      ⟨fun a b => Classical.byContradiction fun hab => h2 ⟨a, b, hab⟩⟩
    exact sentailsAt_of_subsingleton φ ψ

/-- Schematic entailment at every base type is characterized by the prefix criterion, when no
variable is bound twice in `φ` and every variable is bound exactly once in `ψ`. -/
theorem sentails_iff_prefixCrit_of_nodup_wf {φ ψ : Prefix n} (hφ : (bvars φ).Nodup) (hψ : WF ψ) :
    SEntails φ ψ ↔ PrefixCrit φ ψ :=
  ⟨fun h => prefixCrit_necessary_of_two_point_nodup ⟨true, false, by decide⟩ hφ hψ.1 (h Bool),
    fun h _ => prefixCrit_sound_of_nodup_wf hφ hψ h⟩

/-! ## Decidability and instances on one and two variables -/

/-- Schematic entailment at a base type with two distinct elements is decided by the Boolean
function `prefixCritB`, when no variable is bound twice in `φ` and every variable is bound exactly
once in `ψ`. -/
theorem sentailsAt_iff_prefixCritB_of_two_point_nodup_wf (hα : ∃ a b : α, a ≠ b)
    {φ ψ : Prefix n} (hφ : (bvars φ).Nodup) (hψ : WF ψ) :
    SEntailsAt α φ ψ ↔ prefixCritB φ ψ = true := by
  rw [prefixCritB_iff]; exact sentailsAt_iff_prefixCrit_of_two_point_nodup_wf hα hφ hψ

/-- `∃y ∀x ⊨ₛ ∀x ∃y` (variables `x = 0`, `y = 1`), at every base type. -/
theorem exists_forall_sentails_forall_exists (α : Type) :
    SEntailsAt α ([X 1, A 0] : Prefix 2) [A 0, X 1] := by
  intro R ρ h
  rw [eval_cons_ex] at h
  obtain ⟨b, hb⟩ := h
  rw [eval_cons_all] at hb
  rw [eval_cons_all]
  intro a
  rw [eval_cons_ex]
  refine ⟨b, ?_⟩
  rw [upd_comm ρ (by decide : (0 : Fin 2) ≠ 1)]
  exact hb a

/-- `∀x ∃y ⊭ₛ ∃y ∀x` at `Bool`, with the matrix `y = x`. -/
theorem forall_exists_not_sentails_exists_forall :
    ¬ SEntailsAt Bool ([A 0, X 1] : Prefix 2) [X 1, A 0] := by
  intro h
  have := h (fun σ => σ 1 = σ 0) (fun _ => false) (by
    rw [eval_cons_all]; intro a; rw [eval_cons_ex]
    exact ⟨a, by simp [eval_nil, upd]⟩)
  rw [eval_cons_ex] at this
  obtain ⟨b, hb⟩ := this
  rw [eval_cons_all] at hb
  have := hb (!b)
  simp [eval_nil, upd] at this

/-- `∀x ⊨ₛ ∃x` (one variable) at every base type `α`, under environment semantics: the
environment supplies a witness. When `α` is empty there is no environment and the statement holds
vacuously; the closed implication `(∀x, P x) → ∃x, P x` fails on an empty type
(`closed_forall_imp_exists_iff_nonempty`). -/
theorem forall_sentails_exists (α : Type) : SEntailsAt α ([A 0] : Prefix 1) [X 0] := by
  intro R ρ h
  rw [eval_cons_all] at h
  rw [eval_cons_ex]
  exact ⟨ρ 0, h (ρ 0)⟩

/-- `∃x ⊭ₛ ∀x` at `Bool`, with the matrix `x = true`. -/
theorem exists_not_sentails_forall : ¬ SEntailsAt Bool ([X 0] : Prefix 1) [A 0] := by
  intro h
  have := h (fun σ => σ 0 = true) (fun _ => true) (by
    rw [eval_cons_ex]; exact ⟨true, by simp [eval_nil, upd]⟩)
  rw [eval_cons_all] at this
  have := this false
  simp [eval_nil, upd] at this

theorem prefixCritB_exists_forall_forall_exists :
    prefixCritB ([X 1, A 0] : Prefix 2) [A 0, X 1] = true := by decide

theorem prefixCritB_forall_exists_exists_forall :
    prefixCritB ([A 0, X 1] : Prefix 2) [X 1, A 0] = false := by decide

theorem prefixCritB_forall_exists : prefixCritB ([A 0] : Prefix 1) [X 0] = true := by decide

theorem prefixCritB_exists_forall : prefixCritB ([X 0] : Prefix 1) [A 0] = false := by decide

/-- Variables are matched by index, not up to renaming: `∀x₀ ∃x₁` and `∀x₁ ∃x₀` (the same
prefix with the two variables renamed, in front of the same matrix) fail the criterion. -/
theorem prefixCritB_renamed_false : prefixCritB ([A 0, X 1] : Prefix 2) [A 1, X 0] = false := by
  decide

/-! ## Definition examples -/

theorem wf_example_pos : WF ([X 1, A 0] : Prefix 2) := (wfB_iff _).1 (by decide)

theorem wf_example_neg_dup : ¬ WF ([X 0, A 0] : Prefix 1) :=
  fun h => absurd ((wfB_iff _).2 h) (by decide)

theorem wf_example_neg_missing : ¬ WF ([X 0] : Prefix 2) :=
  fun h => absurd ((wfB_iff _).2 h) (by decide)

theorem prefixCrit_example_pos : PrefixCrit ([X 1, A 0] : Prefix 2) [A 0, X 1] :=
  (prefixCritB_iff _ _).1 prefixCritB_exists_forall_forall_exists

theorem prefixCrit_example_neg : ¬ PrefixCrit ([A 0, X 1] : Prefix 2) [X 1, A 0] := by
  intro h
  have := (prefixCritB_iff _ _).2 h
  rw [prefixCritB_forall_exists_exists_forall] at this
  cases this

/-- A positive example of part (i) in which `ψ` has a universal binder. -/
theorem univReflected_example_pos :
    UnivReflected ([X 1, A 0] : Prefix 2) [A 0, X 1] ∧ qOf ([A 0, X 1] : Prefix 2) 0 = some .all :=
  ⟨((prefixCritB_iff _ _).1 prefixCritB_exists_forall_forall_exists).1, rfl⟩

theorem univReflected_example_neg : ¬ UnivReflected ([X 0] : Prefix 1) [A 0] := by
  intro h
  have := h 0 (by decide)
  revert this; decide

theorem skolemOrder_example_pos : SkolemOrderPreserved ([A 0, X 1] : Prefix 2) [A 0, X 1] :=
  ((prefixCritB_iff _ _).1 (by decide)).2

theorem skolemOrder_example_neg : ¬ SkolemOrderPreserved ([A 0, X 1] : Prefix 2) [X 1, A 0] := by
  intro h
  have := h 0 1 (by decide) (by decide) (by decide) (by decide)
  revert this; decide

theorem precedes_example_pos : Precedes ([A 0, X 1] : Prefix 2) 0 1 := by decide

theorem precedes_example_neg : ¬ Precedes ([A 0, X 1] : Prefix 2) 1 0 := by decide

theorem sentailsAt_example_pos : SEntailsAt Bool ([X 1, A 0] : Prefix 2) [A 0, X 1] :=
  exists_forall_sentails_forall_exists Bool

theorem sentailsAt_example_neg : ¬ SEntailsAt Bool ([A 0, X 1] : Prefix 2) [X 1, A 0] :=
  forall_exists_not_sentails_exists_forall

theorem sentails_example_pos : SEntails ([X 1, A 0] : Prefix 2) [A 0, X 1] :=
  fun α => exists_forall_sentails_forall_exists α

theorem sentails_example_neg : ¬ SEntails ([X 0] : Prefix 1) [A 0] :=
  fun h => exists_not_sentails_forall (h Bool)

theorem eval_example_pos : eval ([A 0, X 1] : Prefix 2) (fun σ => σ 1 = σ 0) (fun _ => (0 : Nat)) := by
  rw [eval_cons_all]; intro a; rw [eval_cons_ex]; exact ⟨a, by simp [eval_nil, upd]⟩

theorem eval_example_neg :
    ¬ eval ([X 1, A 0] : Prefix 2) (fun σ => σ 1 = σ 0) (fun _ => (0 : Nat)) := by
  rw [eval_cons_ex]
  rintro ⟨b, hb⟩
  rw [eval_cons_all] at hb
  have := hb (b + 1)
  simp [eval_nil, upd] at this

/-! ## Tightness and non-vacuity for the prefix criterion -/

theorem bool_twoPoint : ∃ a b : Bool, a ≠ b := ⟨true, false, by decide⟩

/-- Non-vacuity of `prefixCrit_sound_of_nodup_wf`: a reordering plus an instantiated universal
(`∀x ∃y ⊨ₛ ∃y ∃x`); the premise `∀x ∃y` is satisfiable at `Bool` (matrix `True`). -/
theorem prefixCrit_sound_nonvacuous :
    (bvars ([A 0, X 1] : Prefix 2)).Nodup ∧ WF ([X 1, X 0] : Prefix 2) ∧
    PrefixCrit ([A 0, X 1] : Prefix 2) [X 1, X 0] ∧
    eval ([A 0, X 1] : Prefix 2) (fun _ => True) (fun _ => true) :=
  ⟨by decide, (wfB_iff _).1 (by decide), (prefixCritB_iff _ _).1 (by decide),
    fun _ _ => ⟨true, trivial, trivial⟩⟩

/-- Non-vacuity of `prefixCrit_necessary_of_two_point_nodup`: all hypotheses hold for
`∃y ∀x ⊨ₛ ∀x ∃y` at `Bool`. -/
theorem prefixCrit_necessary_nonvacuous :
    (∃ a b : Bool, a ≠ b) ∧ (bvars ([X 1, A 0] : Prefix 2)).Nodup ∧
    (bvars ([A 0, X 1] : Prefix 2)).Nodup ∧
    SEntailsAt Bool ([X 1, A 0] : Prefix 2) [A 0, X 1] :=
  ⟨bool_twoPoint, by decide, by decide, exists_forall_sentails_forall_exists Bool⟩

/-- Tightness of part (i) of `h` in `prefixCrit_sound_of_nodup_wf` (witness class: one variable
at `Bool`): the other hypotheses and part (ii) hold, part (i) fails, and the entailment fails
(`∃x ⊭ₛ ∀x`). -/
theorem prefixCrit_part_i_tight :
    (bvars ([X 0] : Prefix 1)).Nodup ∧ WF ([A 0] : Prefix 1) ∧
    SkolemOrderPreserved ([X 0] : Prefix 1) [A 0] ∧
    ¬ UnivReflected ([X 0] : Prefix 1) [A 0] ∧ ¬ SEntailsAt Bool ([X 0] : Prefix 1) [A 0] := by
  refine ⟨by decide, (wfB_iff _).1 (by decide), ?_,
    univReflected_example_neg, exists_not_sentails_forall⟩
  intro u v hv hu _ _
  have hu' : u = 0 := Fin.ext (by have := u.isLt; omega)
  have hv' : v = 0 := Fin.ext (by have := v.isLt; omega)
  subst hu' hv'
  rw [hu] at hv; simp at hv

/-- Tightness of part (ii) of `h` in `prefixCrit_sound_of_nodup_wf` (witness class: two
variables at `Bool`): the other hypotheses and part (i) hold, part (ii) fails, and the entailment
fails (`∀x ∃y ⊭ₛ ∃y ∀x`). -/
theorem prefixCrit_part_ii_tight :
    (bvars ([A 0, X 1] : Prefix 2)).Nodup ∧ WF ([X 1, A 0] : Prefix 2) ∧
    UnivReflected ([A 0, X 1] : Prefix 2) [X 1, A 0] ∧
    ¬ SkolemOrderPreserved ([A 0, X 1] : Prefix 2) [X 1, A 0] ∧
    ¬ SEntailsAt Bool ([A 0, X 1] : Prefix 2) [X 1, A 0] := by
  refine ⟨by decide, (wfB_iff _).1 (by decide), ?_, skolemOrder_example_neg,
    forall_exists_not_sentails_exists_forall⟩
  intro v hv
  have : v = 0 ∨ v = 1 := by
    rcases v with ⟨_ | _ | k, hk⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
    · omega
  rcases this with rfl | rfl
  · decide
  · revert hv; decide

/-- Tightness of `hφ` in `prefixCrit_sound_of_nodup_wf` (witness class: one variable at
`Bool`, `φ = ∀x ∃x`): `ψ` is well formed, the criterion holds, the entailment fails. -/
theorem prefixCrit_sound_hφ_tight :
    ¬ (bvars ([A 0, X 0] : Prefix 1)).Nodup ∧ WF ([A 0] : Prefix 1) ∧
    PrefixCrit ([A 0, X 0] : Prefix 1) [A 0] ∧ ¬ SEntailsAt Bool ([A 0, X 0] : Prefix 1) [A 0] := by
  refine ⟨by decide, (wfB_iff _).1 (by decide), (prefixCritB_iff _ _).1 (by decide), ?_⟩
  intro h
  have := h (fun σ => σ 0 = true) (fun _ => true) (by
    rw [eval_cons_all]; intro a; rw [eval_cons_ex]; exact ⟨true, by simp [eval_nil, upd]⟩)
  rw [eval_cons_all] at this
  have := this false
  simp [eval_nil, upd] at this

/-- Tightness of `hψ` in `prefixCrit_sound_of_nodup_wf`, duplicate half (witness class: one
variable at `Bool`, `ψ = ∃x ∀x`): no repeated binder in `φ`, the criterion holds, the entailment
fails. -/
theorem prefixCrit_sound_hψ_tight_dup :
    (bvars ([X 0] : Prefix 1)).Nodup ∧ ¬ WF ([X 0, A 0] : Prefix 1) ∧
    PrefixCrit ([X 0] : Prefix 1) [X 0, A 0] ∧ ¬ SEntailsAt Bool ([X 0] : Prefix 1) [X 0, A 0] := by
  refine ⟨by decide, wf_example_neg_dup, (prefixCritB_iff _ _).1 (by decide), ?_⟩
  intro h
  have := h (fun σ => σ 0 = true) (fun _ => true) (by
    rw [eval_cons_ex]; exact ⟨true, by simp [eval_nil, upd]⟩)
  rw [eval_cons_ex] at this
  obtain ⟨_, hb⟩ := this
  rw [eval_cons_all] at hb
  have := hb false
  simp [eval_nil, upd] at this

/-- Tightness of `hψ` in `prefixCrit_sound_of_nodup_wf`, covering half (witness class: one
variable at `Bool`, `ψ` the empty prefix, `x` free): the criterion holds, the entailment fails. -/
theorem prefixCrit_sound_hψ_tight_missing :
    (bvars ([X 0] : Prefix 1)).Nodup ∧ ¬ WF ([] : Prefix 1) ∧
    PrefixCrit ([X 0] : Prefix 1) [] ∧ ¬ SEntailsAt Bool ([X 0] : Prefix 1) [] := by
  refine ⟨by decide, fun h => absurd ((wfB_iff _).2 h) (by decide),
    (prefixCritB_iff _ _).1 (by decide), ?_⟩
  intro h
  have := h (fun σ => σ 0 = true) (fun _ => false) (by
    rw [eval_cons_ex]; exact ⟨true, by simp [eval_nil, upd]⟩)
  simp [eval_nil] at this

/-- Tightness of `hα` in `prefixCrit_necessary_of_two_point_nodup` (witness class: the
one-element type `Unit`): `∃x ⊨ₛ ∀x` holds though the criterion fails. -/
theorem prefixCrit_necessary_hα_tight :
    ¬ (∃ a b : Unit, a ≠ b) ∧ (bvars ([X 0] : Prefix 1)).Nodup ∧
    (bvars ([A 0] : Prefix 1)).Nodup ∧
    SEntailsAt Unit ([X 0] : Prefix 1) [A 0] ∧ ¬ PrefixCrit ([X 0] : Prefix 1) [A 0] :=
  ⟨fun ⟨a, b, h⟩ => h (Subsingleton.elim a b), by decide, by decide,
    sentailsAt_of_subsingleton _ _, fun h => univReflected_example_neg h.1⟩

/-- Tightness of `hφ` in `prefixCrit_necessary_of_two_point_nodup` (witness class: one variable
at `Bool`, `φ = ∃x ∀x`): the entailment holds, the criterion fails. -/
theorem prefixCrit_necessary_hφ_tight :
    (∃ a b : Bool, a ≠ b) ∧ ¬ (bvars ([X 0, A 0] : Prefix 1)).Nodup ∧
    (bvars ([A 0] : Prefix 1)).Nodup ∧
    SEntailsAt Bool ([X 0, A 0] : Prefix 1) [A 0] ∧ ¬ PrefixCrit ([X 0, A 0] : Prefix 1) [A 0] := by
  refine ⟨bool_twoPoint, by decide, by decide, ?_, fun h => absurd
    ((prefixCritB_iff _ _).2 h) (by decide)⟩
  intro R ρ h
  rw [eval_cons_ex] at h
  obtain ⟨a, ha⟩ := h
  rw [eval_cons_all] at ha
  rw [eval_cons_all]
  intro b
  have := ha b
  have e : upd (upd ρ 0 a) 0 b = upd ρ 0 b := by
    funext z; simp only [upd]; split <;> rfl
  rw [e] at this
  exact this

/-- Tightness of `hψ` in `prefixCrit_necessary_of_two_point_nodup` (witness class: one variable
at `Bool`, `ψ = ∀x ∃x`): the entailment holds, the criterion fails. -/
theorem prefixCrit_necessary_hψ_tight :
    (∃ a b : Bool, a ≠ b) ∧ (bvars ([X 0] : Prefix 1)).Nodup ∧
    ¬ (bvars ([A 0, X 0] : Prefix 1)).Nodup ∧
    SEntailsAt Bool ([X 0] : Prefix 1) [A 0, X 0] ∧ ¬ PrefixCrit ([X 0] : Prefix 1) [A 0, X 0] := by
  refine ⟨bool_twoPoint, by decide, by decide, ?_,
    fun h => absurd ((prefixCritB_iff _ _).2 h) (by decide)⟩
  intro R ρ h
  rw [eval_cons_ex] at h
  obtain ⟨a, ha⟩ := h
  rw [eval_cons_all]
  intro b
  rw [eval_cons_ex]
  refine ⟨a, ?_⟩
  have e : upd (upd ρ 0 b) 0 a = upd ρ 0 a := by
    funext z; simp only [upd]; split <;> rfl
  rw [e]
  exact ha

/-- Tightness of `h` in `prefixCrit_necessary_of_two_point_nodup` (witness class: two variables
at `Bool`): the other hypotheses hold, the entailment `∀x ∃y ⊨ₛ ∃y ∀x` fails, and so does the
criterion. -/
theorem prefixCrit_necessary_h_tight :
    (∃ a b : Bool, a ≠ b) ∧ (bvars ([A 0, X 1] : Prefix 2)).Nodup ∧
    (bvars ([X 1, A 0] : Prefix 2)).Nodup ∧
    ¬ SEntailsAt Bool ([A 0, X 1] : Prefix 2) [X 1, A 0] ∧
    ¬ PrefixCrit ([A 0, X 1] : Prefix 2) [X 1, A 0] :=
  ⟨bool_twoPoint, by decide, by decide, forall_exists_not_sentails_exists_forall,
    prefixCrit_example_neg⟩

/-- Tightness of `[Subsingleton α]` in `sentailsAt_of_subsingleton` (witness class: `Bool`):
`Bool` is not a subsingleton and `∀x ∃y ⊭ₛ ∃y ∀x` at `Bool`. -/
theorem sentailsAt_of_subsingleton_tight :
    ¬ Subsingleton Bool ∧ ¬ SEntailsAt Bool ([A 0, X 1] : Prefix 2) [X 1, A 0] :=
  ⟨fun h => absurd (h.elim true false) (by decide), forall_exists_not_sentails_exists_forall⟩

/-- Tightness of the covering hypothesis in `eval_env_irrelevant_of_covers` (witness class: one
variable at `Bool`, the empty prefix): the value of the free variable matters. -/
theorem eval_env_irrelevant_hcov_tight :
    ¬ (∀ v : Fin 1, v ∈ bvars ([] : Prefix 1)) ∧
    ¬ (eval ([] : Prefix 1) (fun σ => σ 0 = true) (fun _ => true) ↔
      eval ([] : Prefix 1) (fun σ => σ 0 = true) (fun _ => false)) := by
  refine ⟨fun h => by simpa [bvars] using h 0, ?_⟩
  simp [eval_nil]

/-- Tightness of `hα` in `sentailsAt_of_isEmpty` (witness class: `Bool`): `Bool` is inhabited
and `∃x ⊭ₛ ∀x` at `Bool`. -/
theorem sentailsAt_of_isEmpty_tight :
    ¬ (Bool → False) ∧ ¬ SEntailsAt Bool ([X 0] : Prefix 1) [A 0] :=
  ⟨fun h => h true, exists_not_sentails_forall⟩

/-- Non-vacuity of `sentailsAt_of_isEmpty`: `Empty` is empty. -/
theorem sentailsAt_of_isEmpty_nonvacuous : Empty → False := fun e => nomatch e

/-! ## Tightness and non-vacuity for the biconditionals and the subsingleton results

Each tightness theorem below states that every hypothesis of the named theorem except one holds
and that its conclusion (a biconditional) fails. The witnesses for the two biconditionals at a
fixed base type, `sentailsAt_iff_prefixCrit_of_two_point_nodup_wf` and
`sentailsAt_iff_prefixCritB_of_two_point_nodup_wf`, are shared: those theorems have the same
hypotheses. -/

/-- `∃x ∀x` (whose inner binder shadows the outer one, so it means `∀x`) entails `∀x` at every
base type. -/
theorem shadowed_exists_forall_sentailsAt (α : Type) :
    SEntailsAt α ([X 0, A 0] : Prefix 1) [A 0] := by
  intro R ρ h
  rw [eval_cons_ex] at h
  obtain ⟨a, ha⟩ := h
  rw [eval_cons_all] at ha
  rw [eval_cons_all]
  intro b
  have := ha b
  have e : upd (upd ρ 0 a) 0 b = upd ρ 0 b := by
    funext z; simp only [upd]; split <;> rfl
  rw [e] at this
  exact this

/-- Tightness of `hα` in `sentailsAt_iff_prefixCrit_of_two_point_nodup_wf` and in
`sentailsAt_iff_prefixCritB_of_two_point_nodup_wf` (witness class: the one-element type `Unit`,
one variable, `φ = ∃x`, `ψ = ∀x`): `φ` has no repeated binder, `ψ` is well formed, and both
biconditionals fail (`∃x ⊨ₛ ∀x` at `Unit`, while the criterion fails). -/
theorem sentailsAt_iff_hα_tight :
    ¬ (∃ a b : Unit, a ≠ b) ∧ (bvars ([X 0] : Prefix 1)).Nodup ∧ WF ([A 0] : Prefix 1) ∧
    ¬ (SEntailsAt Unit ([X 0] : Prefix 1) [A 0] ↔ PrefixCrit ([X 0] : Prefix 1) [A 0]) ∧
    ¬ (SEntailsAt Unit ([X 0] : Prefix 1) [A 0] ↔
        prefixCritB ([X 0] : Prefix 1) [A 0] = true) := by
  refine ⟨prefixCrit_necessary_hα_tight.1, by decide, (wfB_iff _).1 (by decide),
    fun h => ?_, fun h => ?_⟩
  · exact prefixCrit_necessary_hα_tight.2.2.2.2 (h.1 prefixCrit_necessary_hα_tight.2.2.2.1)
  · exact prefixCrit_necessary_hα_tight.2.2.2.2
      ((prefixCritB_iff _ _).1 (h.1 prefixCrit_necessary_hα_tight.2.2.2.1))

/-- Tightness of `hφ` in `sentailsAt_iff_prefixCrit_of_two_point_nodup_wf` and in
`sentailsAt_iff_prefixCritB_of_two_point_nodup_wf` (witness class: one variable at `Bool`,
`φ = ∃x ∀x`, `ψ = ∀x`): `Bool` has two elements, `ψ` is well formed, and both biconditionals
fail (the entailment holds, the criterion fails). -/
theorem sentailsAt_iff_hφ_tight :
    (∃ a b : Bool, a ≠ b) ∧ ¬ (bvars ([X 0, A 0] : Prefix 1)).Nodup ∧ WF ([A 0] : Prefix 1) ∧
    ¬ (SEntailsAt Bool ([X 0, A 0] : Prefix 1) [A 0] ↔
        PrefixCrit ([X 0, A 0] : Prefix 1) [A 0]) ∧
    ¬ (SEntailsAt Bool ([X 0, A 0] : Prefix 1) [A 0] ↔
        prefixCritB ([X 0, A 0] : Prefix 1) [A 0] = true) := by
  refine ⟨bool_twoPoint, by decide, (wfB_iff _).1 (by decide), fun h => ?_, fun h => ?_⟩
  · exact prefixCrit_necessary_hφ_tight.2.2.2.2 (h.1 (shadowed_exists_forall_sentailsAt Bool))
  · exact prefixCrit_necessary_hφ_tight.2.2.2.2
      ((prefixCritB_iff _ _).1 (h.1 (shadowed_exists_forall_sentailsAt Bool)))

/-- Tightness of `hψ`, covering half, in `sentailsAt_iff_prefixCrit_of_two_point_nodup_wf` and in
`sentailsAt_iff_prefixCritB_of_two_point_nodup_wf` (witness class: one variable at `Bool`,
`φ = ∃x`, `ψ` the empty prefix with `x` free): `Bool` has two elements, `φ` has no repeated
binder, `ψ` has no repeated binder but does not bind `x`, and both biconditionals fail (the
criterion holds, the entailment fails). -/
theorem sentailsAt_iff_hψ_tight_missing :
    (∃ a b : Bool, a ≠ b) ∧ (bvars ([X 0] : Prefix 1)).Nodup ∧ ¬ WF ([] : Prefix 1) ∧
    ¬ (SEntailsAt Bool ([X 0] : Prefix 1) [] ↔ PrefixCrit ([X 0] : Prefix 1) []) ∧
    ¬ (SEntailsAt Bool ([X 0] : Prefix 1) [] ↔ prefixCritB ([X 0] : Prefix 1) [] = true) := by
  refine ⟨bool_twoPoint, by decide, prefixCrit_sound_hψ_tight_missing.2.1, fun h => ?_,
    fun h => ?_⟩
  · exact prefixCrit_sound_hψ_tight_missing.2.2.2 (h.2 prefixCrit_sound_hψ_tight_missing.2.2.1)
  · exact prefixCrit_sound_hψ_tight_missing.2.2.2
      (h.2 ((prefixCritB_iff _ _).2 prefixCrit_sound_hψ_tight_missing.2.2.1))

/-- Tightness of `hψ`, duplicate half, in `sentailsAt_iff_prefixCrit_of_two_point_nodup_wf` and
in `sentailsAt_iff_prefixCritB_of_two_point_nodup_wf` (witness class: one variable at `Bool`,
`φ = ∃x`, `ψ = ∃x ∀x`): `Bool` has two elements, `φ` has no repeated binder, `ψ` binds `x`
twice, and both biconditionals fail (the criterion holds, the entailment fails). -/
theorem sentailsAt_iff_hψ_tight_dup :
    (∃ a b : Bool, a ≠ b) ∧ (bvars ([X 0] : Prefix 1)).Nodup ∧ ¬ WF ([X 0, A 0] : Prefix 1) ∧
    ¬ (SEntailsAt Bool ([X 0] : Prefix 1) [X 0, A 0] ↔
        PrefixCrit ([X 0] : Prefix 1) [X 0, A 0]) ∧
    ¬ (SEntailsAt Bool ([X 0] : Prefix 1) [X 0, A 0] ↔
        prefixCritB ([X 0] : Prefix 1) [X 0, A 0] = true) := by
  refine ⟨bool_twoPoint, by decide, prefixCrit_sound_hψ_tight_dup.2.1, fun h => ?_, fun h => ?_⟩
  · exact prefixCrit_sound_hψ_tight_dup.2.2.2 (h.2 prefixCrit_sound_hψ_tight_dup.2.2.1)
  · exact prefixCrit_sound_hψ_tight_dup.2.2.2
      (h.2 ((prefixCritB_iff _ _).2 prefixCrit_sound_hψ_tight_dup.2.2.1))

/-- Non-vacuity of `sentailsAt_iff_prefixCrit_of_two_point_nodup_wf` and
`sentailsAt_iff_prefixCritB_of_two_point_nodup_wf`: every hypothesis holds for `φ = ∃y ∀x`,
`ψ = ∀x ∃y` at `Bool` (both sides of the biconditionals hold). -/
theorem sentailsAt_iff_nonvacuous :
    (∃ a b : Bool, a ≠ b) ∧ (bvars ([X 1, A 0] : Prefix 2)).Nodup ∧ WF ([A 0, X 1] : Prefix 2) ∧
    SEntailsAt Bool ([X 1, A 0] : Prefix 2) [A 0, X 1] ∧
    PrefixCrit ([X 1, A 0] : Prefix 2) [A 0, X 1] :=
  ⟨bool_twoPoint, by decide, (wfB_iff _).1 (by decide), exists_forall_sentails_forall_exists Bool,
    prefixCrit_example_pos⟩

/-- Tightness of `hφ` in `sentails_iff_prefixCrit_of_nodup_wf` (witness class: one variable,
`φ = ∃x ∀x`, `ψ = ∀x`): `ψ` is well formed and the biconditional fails (the entailment holds at
every base type, the criterion fails). -/
theorem sentails_iff_hφ_tight :
    ¬ (bvars ([X 0, A 0] : Prefix 1)).Nodup ∧ WF ([A 0] : Prefix 1) ∧
    ¬ (SEntails ([X 0, A 0] : Prefix 1) [A 0] ↔ PrefixCrit ([X 0, A 0] : Prefix 1) [A 0]) :=
  ⟨by decide, (wfB_iff _).1 (by decide),
    fun h => prefixCrit_necessary_hφ_tight.2.2.2.2 (h.1 shadowed_exists_forall_sentailsAt)⟩

/-- Tightness of `hψ`, covering half, in `sentails_iff_prefixCrit_of_nodup_wf` (witness class:
one variable, `φ = ∃x`, `ψ` the empty prefix with `x` free; the entailment fails at `Bool`): `φ`
has no repeated binder and the biconditional fails. -/
theorem sentails_iff_hψ_tight_missing :
    (bvars ([X 0] : Prefix 1)).Nodup ∧ ¬ WF ([] : Prefix 1) ∧
    ¬ (SEntails ([X 0] : Prefix 1) [] ↔ PrefixCrit ([X 0] : Prefix 1) []) :=
  ⟨by decide, prefixCrit_sound_hψ_tight_missing.2.1, fun h =>
    prefixCrit_sound_hψ_tight_missing.2.2.2 (h.2 prefixCrit_sound_hψ_tight_missing.2.2.1 Bool)⟩

/-- Tightness of `hψ`, duplicate half, in `sentails_iff_prefixCrit_of_nodup_wf` (witness class:
one variable, `φ = ∃x`, `ψ = ∃x ∀x`; the entailment fails at `Bool`): `φ` has no repeated binder
and the biconditional fails. -/
theorem sentails_iff_hψ_tight_dup :
    (bvars ([X 0] : Prefix 1)).Nodup ∧ ¬ WF ([X 0, A 0] : Prefix 1) ∧
    ¬ (SEntails ([X 0] : Prefix 1) [X 0, A 0] ↔ PrefixCrit ([X 0] : Prefix 1) [X 0, A 0]) :=
  ⟨by decide, prefixCrit_sound_hψ_tight_dup.2.1, fun h =>
    prefixCrit_sound_hψ_tight_dup.2.2.2 (h.2 prefixCrit_sound_hψ_tight_dup.2.2.1 Bool)⟩

/-- Non-vacuity of `sentails_iff_prefixCrit_of_nodup_wf`: both hypotheses hold for
`φ = ∃y ∀x`, `ψ = ∀x ∃y` (and both sides of the biconditional hold). -/
theorem sentails_iff_nonvacuous :
    (bvars ([X 1, A 0] : Prefix 2)).Nodup ∧ WF ([A 0, X 1] : Prefix 2) ∧
    SEntails ([X 1, A 0] : Prefix 2) [A 0, X 1] ∧ PrefixCrit ([X 1, A 0] : Prefix 2) [A 0, X 1] :=
  ⟨by decide, (wfB_iff _).1 (by decide), exists_forall_sentails_forall_exists,
    prefixCrit_example_pos⟩

/-- Tightness of `[Subsingleton α]` in `eval_subsingleton` (witness class: `Bool`, one variable):
`Bool` is not a subsingleton, and `∀x (x = true)` does not evaluate to its matrix at the
environment `x := true`. -/
theorem eval_subsingleton_tight :
    ¬ Subsingleton Bool ∧
    ¬ (eval ([A 0] : Prefix 1) (fun σ => σ 0 = true) (fun _ => true) ↔
        (fun σ : Fin 1 → Bool => σ 0 = true) (fun _ => true)) := by
  refine ⟨fun h => absurd (h.elim true false) (by decide), fun h => ?_⟩
  have := (h.2 rfl)
  rw [eval_cons_all] at this
  have := this false
  simp [eval_nil, upd] at this

/-- Non-vacuity of `sentailsAt_of_subsingleton` and `eval_subsingleton`: `Unit` is a
subsingleton; there `∃x ⊨ₛ ∀x`. -/
theorem subsingleton_nonvacuous :
    Subsingleton Unit ∧ SEntailsAt Unit ([X 0] : Prefix 1) [A 0] :=
  ⟨inferInstance, sentailsAt_of_subsingleton _ _⟩

/-- Non-vacuity of `eval_env_irrelevant_of_covers`: the prefix `∀x` binds the only variable. -/
theorem eval_env_irrelevant_of_covers_nonvacuous : ∀ v : Fin 1, v ∈ bvars ([A 0] : Prefix 1) := by
  intro v
  have : v = 0 := Fin.ext (by have := v.isLt; omega)
  subst this
  decide


end Toy.ClaimStrength
