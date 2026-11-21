import ClaimStrength.Relativized

/-!
# Completeness of the combined criterion on a restricted fragment

On the fragment where no variable is bound twice in either prefix, the base type is nonempty,
every existential domain of `φ` and every universal domain of `ψ` has at least two elements, both
premises are true at every assignment, and the inclusion, overlap, and implication relations are
exact, schematic entailment implies the combined criterion. Prefixes may leave variables unbound
(the environment supplies their values). Each criterion part is refuted by a matrix that mentions
one or two variables; the other binders are vacuous because their domains are nonempty (which
follows from the hypotheses, `nonempty_domains_of_rEntails`).
-/

namespace Toy.ClaimStrength

variable {n : Nat} {K P : Type} {α : Type}

/-- Keep only the binders whose variable satisfies `s`. -/
def keepVars (s : Fin n → Bool) (φ : List (Binder n K)) : List (Binder n K) :=
  φ.filter (fun b => s b.var)

theorem keepVars_cons_pos {s : Fin n → Bool} {c : Binder n K} {rest : List (Binder n K)}
    (h : s c.var = true) : keepVars s (c :: rest) = c :: keepVars s rest := by
  simp [keepVars, h]

theorem keepVars_cons_neg {s : Fin n → Bool} {c : Binder n K} {rest : List (Binder n K)}
    (h : ¬ s c.var = true) : keepVars s (c :: rest) = keepVars s rest := by
  simp [keepVars, h]

theorem keepVars_nil_of {s : Fin n → Bool} :
    ∀ {φ : List (Binder n K)}, (∀ b ∈ φ, ¬ s b.var = true) → keepVars s φ = []
  | [], _ => rfl
  | c :: rest, h => by
    rw [keepVars_cons_neg (h c List.mem_cons_self)]
    exact keepVars_nil_of (fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem keepVars_congr {s s' : Fin n → Bool} :
    ∀ {φ : List (Binder n K)}, (∀ b ∈ φ, s b.var = s' b.var) → keepVars s φ = keepVars s' φ
  | [], _ => rfl
  | c :: rest, h => by
    have hc := h c List.mem_cons_self
    have ih := keepVars_congr (φ := rest) (fun b hb => h b (List.mem_cons_of_mem _ hb))
    by_cases hs : s c.var = true
    · rw [keepVars_cons_pos hs, keepVars_cons_pos (hc ▸ hs), ih]
    · rw [keepVars_cons_neg hs, keepVars_cons_neg (fun e => hs (hc ▸ e)), ih]

theorem evalR_agree (I : K → α → Prop) (L : (Fin n → α) → Prop) (s : Fin n → Bool)
    (hL : ∀ σ σ', (∀ v, s v = true → σ v = σ' v) → L σ → L σ') :
    ∀ (φ : List (Binder n K)) (ρ ρ' : Fin n → α), (∀ b ∈ φ, s b.var = true) →
      (∀ v, s v = true → ρ v = ρ' v) → evalR I φ L ρ → evalR I φ L ρ'
  | [], ρ, ρ', _, hρ, h => hL ρ ρ' hρ h
  | c :: rest, ρ, ρ', hs, hρ, h =>
    quantify_mono (fun a _ h' => evalR_agree I L s hL rest (upd ρ c.var a) (upd ρ' c.var a)
      (fun b hb => hs b (List.mem_cons_of_mem _ hb))
      (fun v hv => by by_cases hvc : v = c.var <;> simp [upd, hvc, hρ v hv]) h') h

/-- Binders of variables the leaf does not depend on can be dropped, provided their domains
are nonempty. -/
theorem evalR_keepVars (I : K → α → Prop) (L : (Fin n → α) → Prop) (s : Fin n → Bool)
    (hL : ∀ σ σ', (∀ v, s v = true → σ v = σ' v) → L σ → L σ') :
    ∀ (φ : List (Binder n K)) (ρ : Fin n → α), (∀ b ∈ φ, ∃ a, I b.dom a) →
      (evalR I φ L ρ ↔ evalR I (keepVars s φ) L ρ)
  | [], _, _ => Iff.rfl
  | c :: rest, ρ, hne => by
    have hne' : ∀ b ∈ rest, ∃ a, I b.dom a := fun b hb => hne b (List.mem_cons_of_mem _ hb)
    by_cases hs : s c.var = true
    · rw [keepVars_cons_pos hs]
      exact quantify_congr (fun a _ => evalR_keepVars I L s hL rest _ hne')
    · rw [keepVars_cons_neg hs]
      have hall : ∀ b ∈ keepVars s rest, s b.var = true := fun b hb => (List.mem_filter.1 hb).2
      have hagree : ∀ a v, s v = true → upd ρ c.var a v = ρ v := fun a v hv =>
        upd_ne ρ (fun e => hs (by rw [← e]; exact hv)) a
      show quantify c.q (I c.dom) (fun a => evalR I rest L (upd ρ c.var a)) ↔ _
      rw [quantify_congr (P' := fun _ => evalR I (keepVars s rest) L ρ) (fun a _ => by
        rw [evalR_keepVars I L s hL rest _ hne']
        exact ⟨evalR_agree I L s hL _ _ _ hall (hagree a),
          evalR_agree I L s hL _ _ _ hall (fun v hv => (hagree a v hv).symm)⟩)]
      exact quantify_const (hne c List.mem_cons_self)

theorem keepVars_single {v : Fin n} :
    ∀ {φ : List (Binder n K)} {b : Binder n K}, (bvars φ).Nodup → bOf φ v = some b →
      keepVars (fun x => decide (x = v)) φ = [b]
  | [], _, _, hb => by simp [bOf] at hb
  | c :: rest, b, hnd, hb => by
    rw [bvars_cons, nodup_cons_iff] at hnd
    by_cases hc : c.var = v
    · rw [bOf_cons_eq hc] at hb; cases hb
      rw [keepVars_cons_pos (by simp [hc]), keepVars_nil_of]
      intro b hb e
      have : b.var = v := of_decide_eq_true e
      exact hnd.1 (hc ▸ this ▸ List.mem_map_of_mem hb)
    · rw [bOf_cons_ne hc] at hb
      rw [keepVars_cons_neg (by simp [hc])]
      exact keepVars_single hnd.2 hb

theorem keepVars_pair {u v : Fin n} (huv : u ≠ v) :
    ∀ {φ : List (Binder n K)} {bu bv : Binder n K}, (bvars φ).Nodup → bOf φ u = some bu →
      bOf φ v = some bv → precL (bvars φ) u v = true →
      keepVars (fun x => decide (x = u ∨ x = v)) φ = [bu, bv]
  | [], _, _, _, hb, _, _ => by simp [bOf] at hb
  | c :: rest, bu, bv, hnd, hbu, hbv, hp => by
    have hnd' := hnd
    rw [bvars_cons, nodup_cons_iff] at hnd'
    by_cases hcu : c.var = u
    · rw [bOf_cons_eq hcu] at hbu; cases hbu
      rw [bOf_cons_ne (fun e => huv (hcu.symm.trans e))] at hbv
      rw [keepVars_cons_pos (by simp [hcu])]
      rw [keepVars_congr (s' := fun x => decide (x = v)) (fun b hb => by
        have : b.var ≠ u := fun e => hnd'.1 (hcu ▸ e ▸ List.mem_map_of_mem hb)
        simp [this])]
      rw [keepVars_single hnd'.2 hbv]
    · by_cases hcv : c.var = v
      · rw [bvars_cons] at hp
        simp only [precL] at hp
        rw [ite_eq_right hcu, ite_eq_left hcv] at hp
        cases hp
      · rw [bOf_cons_ne hcu] at hbu
        rw [bOf_cons_ne hcv] at hbv
        rw [bvars_cons, precL_cons_ne hcu hcv] at hp
        rw [keepVars_cons_neg (by simp [hcu, hcv])]
        exact keepVars_pair huv hnd'.2 hbu hbv hp

/-- Evaluation of a prefix in front of a matrix that depends only on `v`. -/
theorem evalR_only_var (I : K → α → Prop) {φ : List (Binder n K)} {v : Fin n}
    {b : Binder n K} (hnd : (bvars φ).Nodup) (hb : bOf φ v = some b)
    (hne : ∀ c ∈ φ, ∃ a, I c.dom a) {M : (Fin n → α) → Prop}
    (hM : ∀ σ σ', σ v = σ' v → M σ → M σ') (ρ : Fin n → α) :
    evalR I φ M ρ ↔ quantify b.q (I b.dom) (fun a => M (upd ρ v a)) := by
  rw [evalR_keepVars I M (fun x => decide (x = v)) (fun σ σ' h => hM σ σ' (h v (by simp))) φ ρ
    hne, keepVars_single hnd hb]
  have hbv := (bOf_some hb).2
  show quantify b.q (I b.dom) (fun a => M (upd ρ b.var a)) ↔ _
  rw [hbv]

/-- Evaluation of a prefix in front of a matrix that depends only on `u` and `v`, with `u`
bound before `v`. -/
theorem evalR_only_two_vars (I : K → α → Prop) {φ : List (Binder n K)} {u v : Fin n}
    {bu bv : Binder n K} (hnd : (bvars φ).Nodup) (huv : u ≠ v) (hbu : bOf φ u = some bu)
    (hbv : bOf φ v = some bv) (hp : precL (bvars φ) u v = true)
    (hne : ∀ c ∈ φ, ∃ a, I c.dom a) {M : (Fin n → α) → Prop}
    (hM : ∀ σ σ', σ u = σ' u → σ v = σ' v → M σ → M σ') (ρ : Fin n → α) :
    evalR I φ M ρ ↔ quantify bu.q (I bu.dom)
      (fun a => quantify bv.q (I bv.dom) (fun c => M (upd (upd ρ u a) v c))) := by
  rw [evalR_keepVars I M (fun x => decide (x = u ∨ x = v))
    (fun σ σ' h => hM σ σ' (h u (by simp)) (h v (by simp))) φ ρ hne,
    keepVars_pair huv hnd hbu hbv hp]
  have hu := (bOf_some hbu).2
  have hv := (bOf_some hbv).2
  show quantify bu.q (I bu.dom)
    (fun a => quantify bv.q (I bv.dom) (fun c => M (upd (upd ρ bu.var a) bv.var c))) ↔ _
  rw [hu, hv]

/-- Evaluation of a prefix in front of a matrix that depends only on `u` and `v`, when `u` is
bound and `v` is not bound by the prefix. -/
theorem evalR_only_two_vars_free (I : K → α → Prop) {ψ : List (Binder n K)} {u v : Fin n}
    {bu : Binder n K} (hnd : (bvars ψ).Nodup) (hbu : bOf ψ u = some bu) (hv : v ∉ bvars ψ)
    (hne : ∀ c ∈ ψ, ∃ a, I c.dom a) {M : (Fin n → α) → Prop}
    (hM : ∀ σ σ', σ u = σ' u → σ v = σ' v → M σ → M σ') (ρ : Fin n → α) :
    evalR I ψ M ρ ↔ quantify bu.q (I bu.dom) (fun a => M (upd ρ u a)) := by
  rw [evalR_keepVars I M (fun x => decide (x = u ∨ x = v))
    (fun σ σ' h => hM σ σ' (h u (by simp)) (h v (by simp))) ψ ρ hne]
  rw [keepVars_congr (s' := fun x => decide (x = u)) (fun b hb => by
    have : b.var ≠ v := fun e => hv (by rw [← e]; exact List.mem_map_of_mem hb)
    simp [this])]
  rw [keepVars_single hnd hbu]
  have hu := (bOf_some hbu).2
  show quantify bu.q (I bu.dom) (fun a => M (upd ρ bu.var a)) ↔ _
  rw [hu]

/-! ## Polarized completeness -/

/-- A prefix whose existential binders have nonempty domains holds in front of a valid leaf. -/
theorem evalR_of_valid (I : K → α → Prop) {L : (Fin n → α) → Prop} (hL : ∀ σ, L σ) :
    ∀ (φ : List (Binder n K)) (ρ : Fin n → α), (∀ b ∈ φ, b.q = .ex → ∃ a, I b.dom a) →
      evalR I φ L ρ
  | [], ρ, _ => hL ρ
  | b :: rest, ρ, hne => by
    have hne' : ∀ c ∈ rest, c.q = .ex → ∃ a, I c.dom a :=
      fun c hc => hne c (List.mem_cons_of_mem _ hc)
    show quantify b.q (I b.dom) (fun a => evalR I rest L (upd ρ b.var a))
    cases hq : b.q with
    | all => intro a _; exact evalR_of_valid I hL rest _ hne'
    | ex =>
      obtain ⟨a, ha⟩ := hne b List.mem_cons_self hq
      exact ⟨a, ha, evalR_of_valid I hL rest _ hne'⟩

/-- A prefix whose universal binders have nonempty domains fails in front of an unsatisfiable
leaf. -/
theorem not_evalR_of_unsat (I : K → α → Prop) {L : (Fin n → α) → Prop} (hL : ∀ σ, ¬ L σ) :
    ∀ (φ : List (Binder n K)) (ρ : Fin n → α), (∀ b ∈ φ, b.q = .all → ∃ a, I b.dom a) →
      ¬ evalR I φ L ρ
  | [], ρ, _, h => hL ρ h
  | b :: rest, ρ, hne, h => by
    have hne' : ∀ c ∈ rest, c.q = .all → ∃ a, I c.dom a :=
      fun c hc => hne c (List.mem_cons_of_mem _ hc)
    change quantify b.q (I b.dom) (fun a => evalR I rest L (upd ρ b.var a)) at h
    cases hq : b.q with
    | all =>
      rw [hq] at h
      obtain ⟨a, ha⟩ := hne b List.mem_cons_self hq
      exact not_evalR_of_unsat I hL rest _ hne' (h a ha)
    | ex =>
      rw [hq] at h
      obtain ⟨a, _, h'⟩ := h
      exact not_evalR_of_unsat I hL rest _ hne' h'

/-- An empty universal domain, with every existential domain nonempty, makes a prefix hold in
front of every leaf. -/
theorem evalR_of_empty_univ (I : K → α → Prop) (L : (Fin n → α) → Prop) :
    ∀ (φ : List (Binder n K)) (ρ : Fin n → α), (∀ b ∈ φ, b.q = .ex → ∃ a, I b.dom a) →
      (∃ b ∈ φ, b.q = .all ∧ ∀ a, ¬ I b.dom a) → evalR I φ L ρ
  | [], _, _, ⟨_, hb, _⟩ => absurd hb List.not_mem_nil
  | b :: rest, ρ, hne, ⟨c, hc, hcq, hce⟩ => by
    have hne' : ∀ c ∈ rest, c.q = .ex → ∃ a, I c.dom a :=
      fun c hc => hne c (List.mem_cons_of_mem _ hc)
    show quantify b.q (I b.dom) (fun a => evalR I rest L (upd ρ b.var a))
    rcases List.mem_cons.1 hc with e | hc'
    · subst e; rw [hcq]; intro a ha; exact absurd ha (hce a)
    · cases hq : b.q with
      | all => intro a _; exact evalR_of_empty_univ I L rest _ hne' ⟨c, hc', hcq, hce⟩
      | ex =>
        obtain ⟨a, ha⟩ := hne b List.mem_cons_self hq
        exact ⟨a, ha, evalR_of_empty_univ I L rest _ hne' ⟨c, hc', hcq, hce⟩⟩

/-- An empty existential domain, with every universal domain nonempty, makes a prefix fail in
front of every leaf. -/
theorem not_evalR_of_empty_ex (I : K → α → Prop) (L : (Fin n → α) → Prop) :
    ∀ (φ : List (Binder n K)) (ρ : Fin n → α), (∀ b ∈ φ, b.q = .all → ∃ a, I b.dom a) →
      (∃ b ∈ φ, b.q = .ex ∧ ∀ a, ¬ I b.dom a) → ¬ evalR I φ L ρ
  | [], _, _, ⟨_, hb, _⟩, _ => absurd hb List.not_mem_nil
  | b :: rest, ρ, hne, ⟨c, hc, hcq, hce⟩, h => by
    have hne' : ∀ c ∈ rest, c.q = .all → ∃ a, I c.dom a :=
      fun c hc => hne c (List.mem_cons_of_mem _ hc)
    change quantify b.q (I b.dom) (fun a => evalR I rest L (upd ρ b.var a)) at h
    rcases List.mem_cons.1 hc with e | hc'
    · subst e; rw [hcq] at h; obtain ⟨a, ha, _⟩ := h; exact hce a ha
    · cases hq : b.q with
      | all =>
        rw [hq] at h
        obtain ⟨a, ha⟩ := hne b List.mem_cons_self hq
        exact not_evalR_of_empty_ex I L rest _ hne' ⟨c, hc', hcq, hce⟩ (h a ha)
      | ex =>
        rw [hq] at h
        obtain ⟨a, _, h'⟩ := h
        exact not_evalR_of_empty_ex I L rest _ hne' ⟨c, hc', hcq, hce⟩ h'

/-- Nonemptiness of every domain is derivable on the polarized fragment: over a nonempty base
type, if every existential domain of `φ` and every universal domain of `ψ` has two elements,
the premise of `ψ` holds everywhere, and `φ` entails `ψ`, then every domain of `φ` and of `ψ` is
nonempty. -/
theorem nonempty_domains_of_rEntails {I : K → α → Prop} {J : P → (Fin n → α) → Prop}
    {φ ψ : Shape n K P} (hα : Nonempty α)
    (h2φ : ∀ b ∈ φ.pre, b.q = .ex → TwoPoint (I b.dom))
    (h2ψ : ∀ b ∈ ψ.pre, b.q = .all → TwoPoint (I b.dom))
    (hpψ : ∀ σ, J ψ.prem σ) (h : REntails I J φ ψ) :
    (∀ b ∈ φ.pre, ∃ a, I b.dom a) ∧ (∀ b ∈ ψ.pre, ∃ a, I b.dom a) := by
  classical
  obtain ⟨a0⟩ := hα
  let ρ0 : Fin n → α := fun _ => a0
  have exφ : ∀ b ∈ φ.pre, b.q = .ex → ∃ a, I b.dom a :=
    fun b hb hq => let ⟨a, _, _, ha, _⟩ := h2φ b hb hq; ⟨a, ha⟩
  have allψ : ∀ b ∈ ψ.pre, b.q = .all → ∃ a, I b.dom a :=
    fun b hb hq => let ⟨a, _, _, ha, _⟩ := h2ψ b hb hq; ⟨a, ha⟩
  refine ⟨fun b hb => Classical.byContradiction fun hne => ?_,
    fun b hb => Classical.byContradiction fun hne => ?_⟩
  · have hne' : ∀ a, ¬ I b.dom a := fun a ha => hne ⟨a, ha⟩
    cases hq : b.q with
    | ex => exact hne (exφ b hb hq)
    | all =>
      have hφv : Holds I J φ (fun _ => False) ρ0 :=
        evalR_of_empty_univ I _ φ.pre ρ0 exφ ⟨b, hb, hq, hne'⟩
      exact not_evalR_of_unsat I (fun σ hσ => hσ (hpψ σ)) ψ.pre ρ0 allψ (h _ ρ0 hφv)
  · have hne' : ∀ a, ¬ I b.dom a := fun a ha => hne ⟨a, ha⟩
    cases hq : b.q with
    | all => exact hne (allψ b hb hq)
    | ex =>
      have hφt : Holds I J φ (fun _ => True) ρ0 :=
        evalR_of_valid I (fun _ _ => trivial) φ.pre ρ0 exφ
      exact not_evalR_of_empty_ex I _ ψ.pre ρ0 allψ ⟨b, hb, hq, hne'⟩ (h _ ρ0 hφt)

/-- The countermodel construction behind completeness, with nonemptiness of every domain taken
as a hypothesis (`hneφ`, `hneψ`). It is used by both completeness theorems below, which derive
these hypotheses (`nonempty_domains_of_rEntails`, or directly from two-point domains). -/
theorem rcrit_complete_of_nonempty_domains {I : K → α → Prop} {J : P → (Fin n → α) → Prop}
    {incl meets : K → K → Bool} {impl : P → P → Bool} {φ ψ : Shape n K P}
    (hφ : (bvars φ.pre).Nodup) (hψ : (bvars ψ.pre).Nodup) (hI : InclExact I incl)
    (hM : MeetsExact I meets) (hJ : ImplExact J impl)
    (hneφ : ∀ b ∈ φ.pre, ∃ a, I b.dom a) (hneψ : ∀ b ∈ ψ.pre, ∃ a, I b.dom a)
    (h2φ : ∀ b ∈ φ.pre, b.q = .ex → TwoPoint (I b.dom))
    (h2ψ : ∀ b ∈ ψ.pre, b.q = .all → TwoPoint (I b.dom))
    (hpφ : ∀ σ, J φ.prem σ) (hpψ : ∀ σ, J ψ.prem σ) (h : REntails I J φ ψ) :
    RCrit incl meets impl φ ψ := by
  classical
  have hE : ∀ (M : (Fin n → α) → Prop) ρ, evalR I φ.pre M ρ → evalR I ψ.pre M ρ :=
    fun M ρ hφM => evalR_mono I (fun σ hσ => hσ (hpψ σ)) ψ.pre ρ
      (h M ρ (evalR_mono I (L' := fun σ => J φ.prem σ → M σ) (fun σ hσ _ => hσ) φ.pre ρ hφM))
  have one : ∀ (v : Fin n) (b b' : Binder n K) (M : (Fin n → α) → Prop),
      (∀ σ σ', σ v = σ' v → M σ → M σ') → ∀ ρ, bOf φ.pre v = some b →
      bOf ψ.pre v = some b' → quantify b.q (I b.dom) (fun a => M (upd ρ v a)) →
      quantify b'.q (I b'.dom) (fun a => M (upd ρ v a)) := by
    intro v b b' M hMd ρ hb hb' hq
    have h1 := (evalR_only_var I hφ hb hneφ hMd ρ).2 hq
    exact (evalR_only_var I hψ hb' hneψ hMd ρ).1 (hE M ρ h1)
  -- (i): a variable universal in `ψ` is bound in `φ` (else `σ v = a1` refutes the entailment)
  -- and universal there (else `σ v = c` does).
  have hUR : UnivReflected φ.pre ψ.pre := by
    intro v hv
    obtain ⟨b', hb', hb'q⟩ := qOf_eq_some.1 hv
    obtain ⟨a1, a2, h12, ha1, ha2⟩ := h2ψ b' (bOf_some hb').1 hb'q
    by_cases hvφ : v ∈ bvars φ.pre
    · obtain ⟨b, hb⟩ := bOf_of_mem hvφ
      rw [qOf_of_bOf hb]
      cases hbq : b.q with
      | all => rfl
      | ex =>
        exfalso
        obtain ⟨c, hc⟩ := hneφ b (bOf_some hb).1
        have := one v b b' (fun σ => σ v = c) (fun σ σ' e hr => e.symm.trans hr) (fun _ => c) hb hb'
          (by rw [hbq]; exact ⟨c, hc, by simp⟩)
        rw [hb'q] at this
        have e1 : upd (fun _ => c) v a1 v = c := this a1 ha1
        have e2 : upd (fun _ => c) v a2 v = c := this a2 ha2
        rw [upd_same] at e1 e2
        exact h12 (e1.trans e2.symm)
    · exfalso
      let M : (Fin n → α) → Prop := fun σ => σ v = a1
      have hMd : ∀ σ σ', σ v = σ' v → M σ → M σ' := fun _ _ e hr => e.symm.trans hr
      let ρ0 : Fin n → α := fun _ => a1
      have hφM : evalR I φ.pre M ρ0 := by
        rw [evalR_keepVars I M (fun x => decide (x = v))
          (fun σ σ' hs => hMd σ σ' (hs v (by simp))) φ.pre ρ0 hneφ]
        rw [keepVars_nil_of (s := fun x => decide (x = v))
          (fun b hb e => hvφ ((of_decide_eq_true e) ▸ List.mem_map_of_mem hb))]
        rfl
      have hψM := (evalR_only_var I hψ hb' hneψ hMd ρ0).1 (hE M ρ0 hφM)
      rw [hb'q] at hψM
      have e2 : upd ρ0 v a2 v = a1 := hψM a2 ha2
      rw [upd_same] at e2
      exact h12 e2.symm
  -- (ii): the matrix `σ v = g (σ u)` with a two-valued `g`; `v` may be free in `ψ`.
  have hSO : SkolemOrderPreserved φ.pre ψ.pre := by
    intro u v hv hu hu' hp
    apply Classical.byContradiction
    intro hnp
    have huv : u ≠ v := by intro e; subst e; rw [hu] at hv; simp at hv
    obtain ⟨bu, hbu, hbuq⟩ := qOf_eq_some.1 hu
    obtain ⟨bv, hbv, hbvq⟩ := qOf_eq_some.1 hv
    obtain ⟨bu', hbu', hbu'q⟩ := qOf_eq_some.1 hu'
    obtain ⟨a1, a2, h12, ha1, ha2⟩ := h2ψ bu' (bOf_some hbu').1 hbu'q
    obtain ⟨c1, c2, hc12, hc1, hc2⟩ := h2φ bv (bOf_some hbv).1 hbvq
    let g : α → α := fun a => if a = a1 then c1 else c2
    let M : (Fin n → α) → Prop := fun σ => σ v = g (σ u)
    have hMdep : ∀ σ σ', σ u = σ' u → σ v = σ' v → M σ → M σ' := by
      intro σ σ' e1 e2 hσ; show σ' v = g (σ' u); rw [← e1, ← e2]; exact hσ
    let ρ0 : Fin n → α := fun _ => c1
    have hφM : evalR I φ.pre M ρ0 := by
      rw [evalR_only_two_vars I hφ huv hbu hbv hp hneφ hMdep, hbuq, hbvq]
      intro a _
      refine ⟨g a, ?_, ?_⟩
      · show I bv.dom (if a = a1 then c1 else c2)
        split
        · exact hc1
        · exact hc2
      · show upd (upd ρ0 u a) v (g a) v = g (upd (upd ρ0 u a) v (g a) u)
        rw [upd_same, upd_ne _ huv, upd_same]
    have hψM := hE M ρ0 hφM
    have g1 : g a1 = c1 := ite_eq_left rfl
    have g2 : g a2 = c2 := ite_eq_right (Ne.symm h12)
    by_cases hvψ : v ∈ bvars ψ.pre
    · obtain ⟨bv', hbv'⟩ := bOf_of_mem hvψ
      have hbv'q : bv'.q = .ex := by
        cases hq : bv'.q with
        | ex => rfl
        | all =>
          have := hUR v (by rw [qOf_of_bOf hbv', hq])
          rw [hv] at this; simp at this
      have hp' : precL (bvars ψ.pre) v u = true :=
        (precL_total huv (mem_bvars_of_bOf hbu') hvψ).resolve_left hnp
      rw [evalR_only_two_vars I hψ (Ne.symm huv) hbv' hbu' hp' hneψ
        (fun σ σ' e1 e2 => hMdep σ σ' e2 e1), hbv'q, hbu'q] at hψM
      obtain ⟨c, _, hc⟩ := hψM
      have e1 : upd (upd ρ0 v c) u a1 v = g (upd (upd ρ0 v c) u a1 u) := hc a1 ha1
      have e2 : upd (upd ρ0 v c) u a2 v = g (upd (upd ρ0 v c) u a2 u) := hc a2 ha2
      rw [upd_ne _ (Ne.symm huv), upd_same, upd_same] at e1 e2
      rw [g1] at e1; rw [g2] at e2
      exact hc12 (e1.symm.trans e2)
    · rw [evalR_only_two_vars_free I hψ hbu' hvψ hneψ hMdep ρ0, hbu'q] at hψM
      have e2 : upd ρ0 u a2 v = g (upd ρ0 u a2 u) := hψM a2 ha2
      rw [upd_ne _ (Ne.symm huv), upd_same, g2] at e2
      exact hc12 e2
  have hUD : UnivDomainsContravariant incl φ.pre ψ.pre := by
    intro v b b' hb hb' hb'q
    rw [hI]; intro a ha'; apply Classical.byContradiction; intro hna
    have hbq : b.q = .all := by
      have := hUR v (by rw [qOf_of_bOf hb', hb'q]); rw [qOf_of_bOf hb] at this
      exact Option.some.inj this
    have := one v b b' (fun σ => σ v ≠ a) (fun σ σ' e hr h' => hr (e.trans h')) (fun _ => a) hb hb'
      (by rw [hbq]; intro x hx e; rw [upd_same] at e; exact hna (e ▸ hx))
    rw [hb'q] at this
    exact this a ha' (upd_same _ _ _)
  have hED : ExDomainsCovariant incl φ.pre ψ.pre := by
    intro v b b' hb hb' hbq
    rw [hI]; intro a ha
    have hb'q : b'.q = .ex := by
      cases hq : b'.q with
      | ex => rfl
      | all =>
        have := hUR v (by rw [qOf_of_bOf hb', hq]); rw [qOf_of_bOf hb, hbq] at this; simp at this
    have := one v b b' (fun σ => σ v = a) (fun σ σ' e hr => e.symm.trans hr) (fun _ => a) hb hb'
      (by rw [hbq]; exact ⟨a, ha, upd_same _ _ _⟩)
    rw [hb'q] at this
    obtain ⟨x, hx, e⟩ := this
    have e' : x = a := by rw [← e, upd_same]
    exact e' ▸ hx
  have hMD : InstantiatedDomainsMeet meets φ.pre ψ.pre := by
    intro v b b' hb hb' hbq hb'q
    rw [hM]
    obtain ⟨a0, _⟩ := hneφ b (bOf_some hb).1
    have := one v b b' (fun σ => I b.dom (σ v)) (fun σ σ' e hr => by rw [← e]; exact hr)
      (fun _ => a0) hb hb'
      (by rw [hbq]; intro x hx; show I b.dom (upd _ v x v); rw [upd_same]; exact hx)
    rw [hb'q] at this
    obtain ⟨x, hx, e⟩ := this
    exact ⟨x, by rw [upd_same] at e; exact e, hx⟩
  exact ⟨⟨hUR, hSO⟩, hUD, hED, hMD, (hJ _ _).2 (fun σ _ => hpφ σ)⟩

/-- **Completeness on the polarized, premise-free fragment.** Suppose no variable is bound twice
in either prefix (a prefix may leave variables unbound; they then take their values from the
environment), the inclusion, overlap, and premise-implication relations are exact, the base type
`α` is nonempty, every existential domain of `φ` and every universal domain of `ψ` has at least
two elements, and both premises are true at every assignment. Then schematic entailment
`REntails I J φ ψ` implies the combined criterion. -/
theorem rcrit_complete_polarized_two_point_premise_free {I : K → α → Prop}
    {J : P → (Fin n → α) → Prop} {incl meets : K → K → Bool} {impl : P → P → Bool}
    {φ ψ : Shape n K P}
    (hφ : (bvars φ.pre).Nodup) (hψ : (bvars ψ.pre).Nodup) (hI : InclExact I incl)
    (hM : MeetsExact I meets) (hJ : ImplExact J impl) (hα : Nonempty α)
    (h2φ : ∀ b ∈ φ.pre, b.q = .ex → TwoPoint (I b.dom))
    (h2ψ : ∀ b ∈ ψ.pre, b.q = .all → TwoPoint (I b.dom))
    (hpφ : ∀ σ, J φ.prem σ) (hpψ : ∀ σ, J ψ.prem σ) (h : REntails I J φ ψ) :
    RCrit incl meets impl φ ψ :=
  let hne := nonempty_domains_of_rEntails hα h2φ h2ψ hpψ h
  rcrit_complete_of_nonempty_domains hφ hψ hI hM hJ hne.1 hne.2 h2φ h2ψ hpφ hpψ h

/-- Completeness on the premise-free fragment, unpolarized form: as
`rcrit_complete_polarized_two_point_premise_free`, but requiring every domain occurring in either
shape to have at least two elements (this implies the polarized hypotheses and nonemptiness of
every domain, so the theorem has no hypothesis on `α`). -/
theorem rcrit_complete_two_point_premise_free {I : K → α → Prop} {J : P → (Fin n → α) → Prop}
    {incl meets : K → K → Bool} {impl : P → P → Bool} {φ ψ : Shape n K P}
    (hφ : (bvars φ.pre).Nodup) (hψ : (bvars ψ.pre).Nodup) (hI : InclExact I incl)
    (hM : MeetsExact I meets) (hJ : ImplExact J impl)
    (h2φ : ∀ b ∈ φ.pre, TwoPoint (I b.dom)) (h2ψ : ∀ b ∈ ψ.pre, TwoPoint (I b.dom))
    (hpφ : ∀ σ, J φ.prem σ) (hpψ : ∀ σ, J ψ.prem σ) (h : REntails I J φ ψ) :
    RCrit incl meets impl φ ψ :=
  rcrit_complete_of_nonempty_domains hφ hψ hI hM hJ
    (fun b hb => let ⟨a, _, _, ha, _⟩ := h2φ b hb; ⟨a, ha⟩)
    (fun b hb => let ⟨a, _, _, ha, _⟩ := h2ψ b hb; ⟨a, ha⟩)
    (fun b hb _ => h2φ b hb) (fun b hb _ => h2ψ b hb) hpφ hpψ h

end Toy.ClaimStrength
