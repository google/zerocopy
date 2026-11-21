import ClaimStrength.PrefixList

/-!
# Relativized claim shapes and soundness of the combined syntactic criterion

A *shape* is a relativized prefix (each binder carries a named domain class) together with one
named premise. With class interpretation `I : K → α → Prop`, premise interpretation
`J : P → (Fin n → α) → Prop`, and an uninterpreted matrix `M`, the shape denotes
`Q₁ x₁ ∈ I k₁. … Qₘ xₘ ∈ I kₘ. (J p x⃗ → M x⃗)`.

The combined criterion is the prefix criterion plus: contravariant domains for variables
universal in `ψ`, covariant domains for variables existential in `φ`, overlapping domains for
variables universal in `φ` and existential in `ψ` (instantiated by a common element), and a
contravariant premise. The inclusion, overlap, and implication relations are supplied
externally; soundness assumes they are sound, completeness (elsewhere) assumes they are exact.
-/

namespace Toy.ClaimStrength

variable {n : Nat} {K P : Type} {α : Type}

/-- A relativized claim shape: a prefix with named domain classes, and a named premise. -/
structure Shape (n : Nat) (K P : Type) where
  pre : List (Binder n K)
  prem : P

/-- The shape `s` holds for matrix `M` from environment `ρ`: the prenex form
`Q₁ x₁ ∈ I k₁. … Qₘ xₘ ∈ I kₘ. (J p x⃗ → M x⃗)`. The premise is an implication antecedent inside
the scope of every binder, including existential ones. When the premise does not depend on the
variables bound after some position (and their domains are nonempty) it can be pulled out to
that position (`evalR_premise_pull_out`); a premise that constrains an existentially bound
variable is *not* a filter on witnesses: `∃ y ∈ D, (H y → M y)` holds as soon as some `y ∈ D`
falsifies `H` (`holds_premise_on_existential_trivial` in `RelResults`). Constraints on witnesses
belong in the binder domains. -/
def Holds (I : K → α → Prop) (J : P → (Fin n → α) → Prop) (s : Shape n K P)
    (M : (Fin n → α) → Prop) (ρ : Fin n → α) : Prop :=
  evalR I s.pre (fun σ => J s.prem σ → M σ) ρ

/-- Schematic entailment of relativized shapes: for every matrix and environment. Domains and
premises are interpreted (fixed by `I` and `J`); only the matrix is uninterpreted. As for
`SEntailsAt`, when `α` is empty and `n ≥ 1` there is no environment and `REntails` holds
vacuously (`rEntails_of_isEmpty`). -/
def REntails (I : K → α → Prop) (J : P → (Fin n → α) → Prop) (φ ψ : Shape n K P) : Prop :=
  ∀ (M : (Fin n → α) → Prop) (ρ : Fin n → α), Holds I J φ M ρ → Holds I J ψ M ρ

/-- Domains of variables universal in `ψ` shrink (contravariance of `∀`). -/
def UnivDomainsContravariant (incl : K → K → Bool) (φ ψ : List (Binder n K)) : Prop :=
  ∀ v b b', bOf φ v = some b → bOf ψ v = some b' → b'.q = .all → incl b'.dom b.dom = true

/-- Domains of variables existential in `φ` grow (covariance of `∃`). -/
def ExDomainsCovariant (incl : K → K → Bool) (φ ψ : List (Binder n K)) : Prop :=
  ∀ v b b', bOf φ v = some b → bOf ψ v = some b' → b.q = .ex → incl b.dom b'.dom = true

/-- A variable universal in `φ` and existential in `ψ` has overlapping domains. -/
def InstantiatedDomainsMeet (meets : K → K → Bool) (φ ψ : List (Binder n K)) : Prop :=
  ∀ v b b', bOf φ v = some b → bOf ψ v = some b' → b.q = .all → b'.q = .ex →
    meets b.dom b'.dom = true

/-- The premise of `ψ` implies the premise of `φ` (contravariance of the premise). -/
def PremiseContravariant (impl : P → P → Bool) (φ ψ : Shape n K P) : Prop :=
  impl ψ.prem φ.prem = true

/-- The combined syntactic criterion for relativized shapes. -/
def RCrit (incl meets : K → K → Bool) (impl : P → P → Bool) (φ ψ : Shape n K P) : Prop :=
  PrefixCrit φ.pre ψ.pre ∧ UnivDomainsContravariant incl φ.pre ψ.pre ∧
  ExDomainsCovariant incl φ.pre ψ.pre ∧ InstantiatedDomainsMeet meets φ.pre ψ.pre ∧
  PremiseContravariant impl φ ψ

/-- The inclusion relation is sound for the interpretation. -/
def InclSound (I : K → α → Prop) (incl : K → K → Bool) : Prop :=
  ∀ k k', incl k k' = true → ∀ a, I k a → I k' a

/-- The overlap relation is sound for the interpretation. -/
def MeetsSound (I : K → α → Prop) (meets : K → K → Bool) : Prop :=
  ∀ k k', meets k k' = true → ∃ a, I k a ∧ I k' a

/-- The premise implication relation is sound for the interpretation. -/
def ImplSound (J : P → (Fin n → α) → Prop) (impl : P → P → Bool) : Prop :=
  ∀ p p', impl p p' = true → ∀ σ, J p σ → J p' σ

/-- The inclusion relation is exact. -/
def InclExact (I : K → α → Prop) (incl : K → K → Bool) : Prop :=
  ∀ k k', incl k k' = true ↔ ∀ a, I k a → I k' a

/-- The overlap relation is exact. -/
def MeetsExact (I : K → α → Prop) (meets : K → K → Bool) : Prop :=
  ∀ k k', meets k k' = true ↔ ∃ a, I k a ∧ I k' a

/-- The premise implication relation is exact. -/
def ImplExact (J : P → (Fin n → α) → Prop) (impl : P → P → Bool) : Prop :=
  ∀ p p', impl p p' = true ↔ ∀ σ, J p σ → J p' σ

/-- A domain with at least two distinct elements. -/
def TwoPoint (D : α → Prop) : Prop := ∃ a b, a ≠ b ∧ D a ∧ D b

/-! ## Moving binders -/

/-- Existential introduction at the position of `y`. -/
theorem evalR_intro_ex (I : K → α → Prop) (L : (Fin n → α) → Prop) :
    ∀ (ψ : List (Binder n K)) (y : Fin n) (b : Binder n K) (a : α) (ρ : Fin n → α),
      (bvars ψ).Nodup → bOf ψ y = some b → b.q = .ex → I b.dom a →
      evalR I (eraseVar ψ y) L (upd ρ y a) → evalR I ψ L ρ
  | [], _, _, _, _, _, hb, _, _, _ => by simp [bOf] at hb
  | c :: rest, y, b, a, ρ, hnd, hb, hq, ha, h => by
    by_cases hc : c.var = y
    · rw [bOf_cons_eq hc] at hb; cases hb
      have hnd' := hnd; rw [bvars_cons, nodup_cons_iff] at hnd'
      rw [eraseVar_cons_eq hc, eraseVar_of_not_mem (hc ▸ hnd'.1)] at h
      show quantify c.q (I c.dom) (fun a' => evalR I rest L (upd ρ c.var a'))
      rw [hq]; exact ⟨a, ha, hc ▸ h⟩
    · rw [eraseVar_cons_ne hc] at h
      rw [bOf_cons_ne hc] at hb
      rw [bvars_cons, nodup_cons_iff] at hnd
      show quantify c.q (I c.dom) (fun a' => evalR I rest L (upd ρ c.var a'))
      exact quantify_mono (fun a' _ h' => evalR_intro_ex I L rest y b a (upd ρ c.var a')
        hnd.2 hb hq ha (by rw [upd_comm ρ hc]; exact h')) h

/-- Universal elimination at the position of `y`. -/
theorem evalR_elim_all (I : K → α → Prop) (L : (Fin n → α) → Prop) :
    ∀ (φ : List (Binder n K)) (y : Fin n) (b : Binder n K) (a : α) (ρ : Fin n → α),
      (bvars φ).Nodup → bOf φ y = some b → b.q = .all → I b.dom a →
      evalR I φ L ρ → evalR I (eraseVar φ y) L (upd ρ y a)
  | [], _, _, _, _, _, hb, _, _, _ => by simp [bOf] at hb
  | c :: rest, y, b, a, ρ, hnd, hb, hq, ha, h => by
    by_cases hc : c.var = y
    · rw [bOf_cons_eq hc] at hb; cases hb
      have hnd' := hnd; rw [bvars_cons, nodup_cons_iff] at hnd'
      rw [eraseVar_cons_eq hc, eraseVar_of_not_mem (hc ▸ hnd'.1)]
      change quantify c.q (I c.dom) (fun a' => evalR I rest L (upd ρ c.var a')) at h
      rw [hq] at h; exact hc ▸ h a ha
    · rw [eraseVar_cons_ne hc]
      rw [bOf_cons_ne hc] at hb
      rw [bvars_cons, nodup_cons_iff] at hnd
      change quantify c.q (I c.dom) (fun a' => evalR I rest L (upd ρ c.var a')) at h
      show quantify c.q (I c.dom) (fun a' => evalR I (eraseVar rest y) L (upd (upd ρ y a) c.var a'))
      exact quantify_mono (fun a' _ h' => by
        rw [← upd_comm ρ hc]
        exact evalR_elim_all I L rest y b a (upd ρ c.var a') hnd.2 hb hq ha h') h

/-- A universal binder preceded only by universal binders can be moved to the front. -/
theorem evalR_all_front (I : K → α → Prop) (L : (Fin n → α) → Prop) :
    ∀ (ψ : List (Binder n K)) (x : Fin n) (b : Binder n K) (ρ : Fin n → α),
      (bvars ψ).Nodup → bOf ψ x = some b → b.q = .all →
      (∀ y, precL (bvars ψ) y x = true → qOf ψ y = some .all) →
      (∀ a, I b.dom a → evalR I (eraseVar ψ x) L (upd ρ x a)) → evalR I ψ L ρ
  | [], _, _, _, _, hb, _, _, _ => by simp [bOf] at hb
  | c :: rest, x, b, ρ, hnd, hb, hq, hpre, h => by
    have hnd' := hnd; rw [bvars_cons, nodup_cons_iff] at hnd'
    by_cases hc : c.var = x
    · rw [bOf_cons_eq hc] at hb; cases hb
      show quantify c.q (I c.dom) (fun a' => evalR I rest L (upd ρ c.var a'))
      rw [hq]
      intro a ha
      have := h a ha
      rw [eraseVar_cons_eq hc, eraseVar_of_not_mem (hc ▸ hnd'.1)] at this
      exact hc ▸ this
    · rw [bOf_cons_ne hc] at hb
      have hxrest : x ∈ bvars rest := mem_bvars_of_bOf hb
      have hcq : c.q = .all := by
        have := hpre c.var (by rw [bvars_cons]; exact precL_head hxrest)
        rw [qOf_of_bOf (bOf_cons_eq rfl)] at this
        exact Option.some.inj this
      show quantify c.q (I c.dom) (fun a' => evalR I rest L (upd ρ c.var a'))
      rw [hcq]
      intro z hz
      refine evalR_all_front I L rest x b (upd ρ c.var z) hnd'.2 hb hq ?_ ?_
      · intro y hy
        have hyc : c.var ≠ y := fun e => hnd'.1 (e ▸ precL_mem_left hy)
        have := hpre y (by rw [bvars_cons, precL_cons_ne hyc hc]; exact hy)
        rwa [qOf, bOf_cons_ne hyc] at this
      · intro a ha
        have := h a ha
        rw [eraseVar_cons_ne hc] at this
        change quantify c.q (I c.dom)
          (fun a' => evalR I (eraseVar rest x) L (upd (upd ρ x a) c.var a')) at this
        rw [hcq] at this
        have h2 : evalR I (eraseVar rest x) L (upd (upd ρ x a) c.var z) := this z hz
        rwa [upd_comm ρ (Ne.symm hc)] at h2

/-! ## The criterion is preserved by erasing a variable from both sides -/

theorem prefixCrit_eraseVar {φ ψ : List (Binder n K)} (y : Fin n) (h : PrefixCrit φ ψ) :
    PrefixCrit (eraseVar φ y) (eraseVar ψ y) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun v hv => ?_, fun u v hv hu hu' hp => ?_⟩
  · by_cases hvy : v = y
    · subst hvy; rw [qOf_eraseVar_self] at hv; cases hv
    · rw [qOf_eraseVar_ne hvy] at hv ⊢; exact h1 v hv
  · by_cases hvy : v = y
    · subst hvy; rw [qOf_eraseVar_self] at hv; cases hv
    by_cases huy : u = y
    · subst huy; rw [qOf_eraseVar_self] at hu; cases hu
    rw [qOf_eraseVar_ne hvy] at hv
    rw [qOf_eraseVar_ne huy] at hu hu'
    rw [precedes_eraseVar huy hvy] at hp ⊢
    exact h2 u v hv hu hu' hp

theorem bOf_eraseVar_some {φ : List (Binder n K)} {y v : Fin n} {b : Binder n K}
    (h : bOf (eraseVar φ y) v = some b) : v ≠ y ∧ bOf φ v = some b := by
  by_cases hvy : v = y
  · subst hvy; rw [bOf_eraseVar_self] at h; cases h
  · exact ⟨hvy, by rwa [bOf_eraseVar_ne hvy] at h⟩

theorem univDomains_eraseVar {incl : K → K → Bool} {φ ψ : List (Binder n K)} (y : Fin n)
    (h : UnivDomainsContravariant incl φ ψ) :
    UnivDomainsContravariant incl (eraseVar φ y) (eraseVar ψ y) :=
  fun v b b' hb hb' hq => h v b b' (bOf_eraseVar_some hb).2 (bOf_eraseVar_some hb').2 hq

theorem exDomains_eraseVar {incl : K → K → Bool} {φ ψ : List (Binder n K)} (y : Fin n)
    (h : ExDomainsCovariant incl φ ψ) :
    ExDomainsCovariant incl (eraseVar φ y) (eraseVar ψ y) :=
  fun v b b' hb hb' hq => h v b b' (bOf_eraseVar_some hb).2 (bOf_eraseVar_some hb').2 hq

theorem meet_eraseVar {meets : K → K → Bool} {φ ψ : List (Binder n K)} (y : Fin n)
    (h : InstantiatedDomainsMeet meets φ ψ) :
    InstantiatedDomainsMeet meets (eraseVar φ y) (eraseVar ψ y) :=
  fun v b b' hb hb' hq hq' =>
    h v b b' (bOf_eraseVar_some hb).2 (bOf_eraseVar_some hb').2 hq hq'

theorem sameVars_eraseVar {φ ψ : List (Binder n K)} (y : Fin n)
    (h : ∀ v, v ∈ bvars φ ↔ v ∈ bvars ψ) :
    ∀ v, v ∈ bvars (eraseVar φ y) ↔ v ∈ bvars (eraseVar ψ y) := by
  intro v; rw [mem_bvars_eraseVar, mem_bvars_eraseVar, h v]

/-! ## Soundness -/

theorem nil_of_no_vars {ψ : List (Binder n K)} (h : ∀ v, v ∉ bvars ψ) : ψ = [] := by
  cases ψ with
  | nil => rfl
  | cons b rest => exact absurd (by rw [bvars_cons]; exact List.mem_cons_self) (h b.var)

/-- The soundness argument, by induction on the length of `φ`. Variables universal in `φ` and
existential in `ψ` are instantiated by a common domain element on both sides; otherwise the
head binder of `φ` is matched in `ψ` (an existential witness is transferred; a universal binder
of `ψ` is preceded only by universal binders, so it can be moved to the front). -/
theorem rcrit_sound_aux (I : K → α → Prop) (incl meets : K → K → Bool)
    (hI : InclSound I incl) (hM : MeetsSound I meets) :
    ∀ (m : Nat) (φ ψ : List (Binder n K)), φ.length ≤ m → (bvars φ).Nodup → (bvars ψ).Nodup →
      (∀ v, v ∈ bvars φ ↔ v ∈ bvars ψ) → PrefixCrit φ ψ →
      UnivDomainsContravariant incl φ ψ → ExDomainsCovariant incl φ ψ →
      InstantiatedDomainsMeet meets φ ψ →
      ∀ (L L' : (Fin n → α) → Prop), (∀ σ, L σ → L' σ) →
      ∀ ρ, evalR I φ L ρ → evalR I ψ L' ρ := by
  intro m
  induction m with
  | zero =>
    intro φ ψ hlen _ _ hsame _ _ _ _ L L' hL ρ h
    have hφ : φ = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hlen)
    subst hφ
    have hψ : ψ = [] := nil_of_no_vars (fun v hv => by simpa [bvars] using (hsame v).2 hv)
    subst hψ
    exact hL ρ h
  | succ m ih =>
    intro φ ψ hlen hndφ hndψ hsame hcrit hU hE hMt L L' hL ρ h
    -- Recursive step on `(eraseVar φ y, eraseVar ψ y)`.
    have step : ∀ y, y ∈ bvars φ → ∀ ρ', evalR I (eraseVar φ y) L ρ' →
        evalR I (eraseVar ψ y) L' ρ' := fun y hy ρ' =>
      ih (eraseVar φ y) (eraseVar ψ y)
        (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (length_eraseVar_lt hy) hlen))
        (nodup_eraseVar y hndφ) (nodup_eraseVar y hndψ) (sameVars_eraseVar y hsame)
        (prefixCrit_eraseVar y hcrit) (univDomains_eraseVar y hU) (exDomains_eraseVar y hE)
        (meet_eraseVar y hMt) L L' hL ρ'
    by_cases hA : ∃ y, qOf φ y = some .all ∧ qOf ψ y = some .ex
    · obtain ⟨y, hyφ, hyψ⟩ := hA
      obtain ⟨b, hb, hbq⟩ := qOf_eq_some.1 hyφ
      obtain ⟨b', hb', hbq'⟩ := qOf_eq_some.1 hyψ
      obtain ⟨a, ha, ha'⟩ := hM _ _ (hMt y b b' hb hb' hbq hbq')
      exact evalR_intro_ex I L' ψ y b' a ρ hndψ hb' hbq' ha'
        (step y (mem_bvars_of_bOf hb) _ (evalR_elim_all I L φ y b a ρ hndφ hb hbq ha h))
    · cases φ with
      | nil =>
        have hψ : ψ = [] := nil_of_no_vars (fun v hv => by simpa [bvars] using (hsame v).2 hv)
        subst hψ
        exact hL ρ h
      | cons c φ' =>
        have hcφ : bOf (c :: φ') c.var = some c := bOf_cons_eq rfl
        have hxmem : c.var ∈ bvars (c :: φ') := mem_bvars_of_bOf hcφ
        obtain ⟨b', hb'⟩ := bOf_of_mem ((hsame c.var).1 hxmem)
        have herase : eraseVar (c :: φ') c.var = φ' := eraseVar_head hndφ
        change quantify c.q (I c.dom) (fun a => evalR I φ' L (upd ρ c.var a)) at h
        cases hcq : c.q with
        | ex =>
          rw [hcq] at h
          obtain ⟨a, ha, h'⟩ := h
          have hb'q : b'.q = .ex := by
            cases hq : b'.q with
            | ex => rfl
            | all =>
              have := hcrit.1 c.var (by rw [qOf_of_bOf hb', hq])
              rw [qOf_of_bOf hcφ, hcq] at this; cases this
          have ha' : I b'.dom a := hI _ _ (hE c.var c b' hcφ hb' hcq) a ha
          exact evalR_intro_ex I L' ψ c.var b' a ρ hndψ hb' hb'q ha'
            (step c.var hxmem _ (by rw [herase]; exact h'))
        | all =>
          rw [hcq] at h
          have hb'q : b'.q = .all := by
            cases hq : b'.q with
            | all => rfl
            | ex => exact absurd ⟨c.var, by rw [qOf_of_bOf hcφ, hcq], by rw [qOf_of_bOf hb', hq]⟩ hA
          refine evalR_all_front I L' ψ c.var b' ρ hndψ hb' hb'q ?_ ?_
          · intro y hy
            have hyψ : y ∈ bvars ψ := precL_mem_left hy
            obtain ⟨by', hby'⟩ := bOf_of_mem hyψ
            cases hyq : by'.q with
            | all => rw [qOf_of_bOf hby', hyq]
            | ex =>
              exfalso
              obtain ⟨bφy, hbφy⟩ := bOf_of_mem ((hsame y).2 hyψ)
              have hyx : y ≠ c.var := by
                intro e; subst e; rw [hby'] at hb'; cases hb'; rw [hyq] at hb'q; cases hb'q
              cases hφyq : bφy.q with
              | all =>
                exact hA ⟨y, by rw [qOf_of_bOf hbφy, hφyq], by rw [qOf_of_bOf hby', hyq]⟩
              | ex =>
                have hprec : Precedes ψ c.var y := hcrit.2 c.var y
                  (by rw [qOf_of_bOf hbφy, hφyq]) (by rw [qOf_of_bOf hcφ, hcq])
                  (by rw [qOf_of_bOf hb', hb'q])
                  (by
                    unfold Precedes; rw [bvars_cons]
                    apply precL_head
                    have := (hsame y).2 hyψ
                    rw [bvars_cons] at this
                    exact (List.mem_cons.1 this).resolve_left hyx)
                exact precL_antisymm (Ne.symm hyx) hprec hy
          · intro a ha
            have hac : I c.dom a := hI _ _ (hU c.var c b' hcφ hb' hb'q) a ha
            exact step c.var hxmem _ (by rw [herase]; exact h a hac)

/-- **Soundness of the combined criterion.** For well-formed shapes (every variable bound
exactly once on each side) and inclusion, overlap, and premise-implication tables `incl`, `meets`,
`impl` that are sound for the interpretation, if the criterion holds for these tables then `φ`
schematically entails `ψ` (for every matrix and environment). No cardinality assumption on `α`;
when `α` is empty and `n ≥ 1` the conclusion holds vacuously (`rEntails_of_isEmpty`). -/
theorem rcrit_sound {I : K → α → Prop} {J : P → (Fin n → α) → Prop}
    {incl meets : K → K → Bool} {impl : P → P → Bool} {φ ψ : Shape n K P}
    (hφ : WF φ.pre) (hψ : WF ψ.pre) (hI : InclSound I incl) (hM : MeetsSound I meets)
    (hJ : ImplSound J impl) (h : RCrit incl meets impl φ ψ) : REntails I J φ ψ := by
  obtain ⟨hcrit, hU, hE, hMt, hP⟩ := h
  intro M ρ hφM
  exact rcrit_sound_aux I incl meets hI hM φ.pre.length φ.pre ψ.pre (Nat.le_refl _) hφ.1 hψ.1
    (fun v => ⟨fun _ => hψ.2 v, fun _ => hφ.2 v⟩) hcrit hU hE hMt _ _
    (fun σ hσ hJψ => hσ (hJ _ _ hP σ hJψ)) ρ hφM

/-! ## Where the premise sits -/

/-- Vacuity on an empty base type: if `α` is empty and `n ≥ 1`, every shape entails every other. -/
theorem rEntails_of_isEmpty {I : K → α → Prop} {J : P → (Fin (n + 1) → α) → Prop}
    (hα : α → False) (φ ψ : Shape (n + 1) K P) : REntails I J φ ψ :=
  fun _ ρ _ => (hα (ρ 0)).elim

/-- Pulling the premise out of a prefix: if every domain in `pre` is nonempty and the premise `H`
does not depend on any variable bound in `pre`, then `pre` in front of `H → L` holds iff `H`
implies `pre` in front of `L`. -/
theorem evalR_premise_pull_out (I : K → α → Prop) (H L : (Fin n → α) → Prop) :
    ∀ (pre : List (Binder n K)) (ρ : Fin n → α), (∀ b ∈ pre, ∃ a, I b.dom a) →
      (∀ b ∈ pre, ∀ (σ : Fin n → α) (a : α), H (upd σ b.var a) ↔ H σ) →
      (evalR I pre (fun σ => H σ → L σ) ρ ↔ (H ρ → evalR I pre L ρ))
  | [], _, _, _ => Iff.rfl
  | b :: rest, ρ, hne, hind => by
    have hne' : ∀ c ∈ rest, ∃ a, I c.dom a := fun c hc => hne c (List.mem_cons_of_mem _ hc)
    have hind' : ∀ c ∈ rest, ∀ (σ : Fin n → α) (a : α), H (upd σ c.var a) ↔ H σ :=
      fun c hc => hind c (List.mem_cons_of_mem _ hc)
    show quantify b.q (I b.dom) (fun a => evalR I rest (fun σ => H σ → L σ) (upd ρ b.var a)) ↔
      (H ρ → quantify b.q (I b.dom) (fun a => evalR I rest L (upd ρ b.var a)))
    rw [quantify_congr (P' := fun a => H ρ → evalR I rest L (upd ρ b.var a)) (fun a _ => by
      rw [evalR_premise_pull_out I H L rest _ hne' hind', hind b List.mem_cons_self ρ a])]
    obtain ⟨a0, ha0⟩ := hne b List.mem_cons_self
    cases b.q with
    | all => exact ⟨fun h hH a ha => h a ha hH, fun h a ha hH => h hH a ha⟩
    | ex =>
      constructor
      · rintro ⟨a, ha, h⟩ hH; exact ⟨a, ha, h hH⟩
      · intro h
        by_cases hH : H ρ
        · obtain ⟨a, ha, h'⟩ := h hH; exact ⟨a, ha, fun _ => h'⟩
        · exact ⟨a0, ha0, fun h' => absurd h' hH⟩

end Toy.ClaimStrength
