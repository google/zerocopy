import ToyUnify.DefExamples

/-!
# Auxiliary lemmas for the correctness proofs of `unify`

Term size, the variables of a substituted term, lookups in association lists, the specification
of decomposition, and one pass of the algorithm (`step`): unifiers of the combined system
"pending equations plus solved bindings" are preserved by every pass, and with the occurs check
on, the solved part stays in solved form (distinct bound variables that occur neither in any
right-hand side nor in the pending equations).
-/

namespace Toy.Unify

/-! ## Term size -/

mutual
/-- The number of nodes of a term. -/
def Term.size : Term → Nat
  | .var _ => 1
  | .con _ ts => Term.sizeList ts + 1
/-- The total number of nodes of a list of terms (companion of `Term.size`). -/
def Term.sizeList : List Term → Nat
  | [] => 0
  | t :: ts => Term.size t + Term.sizeList ts
end

mutual
theorem size_substVar_le (σ : Subst) :
    ∀ (t : Term) (x : Nat), x ∈ t.vars → (substVar σ x).size ≤ (subst σ t).size
  | .var y, x, h => by
    simp only [Term.vars, List.mem_singleton] at h
    subst h
    exact Nat.le_refl _
  | .con f ts, x, h => by
    have := size_substVar_le_list σ ts x (by simpa [Term.vars] using h)
    simp only [subst, Term.size]
    omega
theorem size_substVar_le_list (σ : Subst) :
    ∀ (ts : List Term) (x : Nat), x ∈ Term.varsList ts →
      (substVar σ x).size ≤ Term.sizeList (substList σ ts)
  | [], x, h => by simp [Term.varsList] at h
  | t :: ts, x, h => by
    simp only [Term.varsList, List.mem_append] at h
    simp only [substList, Term.sizeList]
    rcases h with h | h
    · have := size_substVar_le σ t x h
      omega
    · have := size_substVar_le_list σ ts x h
      omega
end

/-- A variable occurring strictly inside a constructor application is smaller after any
substitution. -/
theorem size_substVar_lt_con (σ : Subst) (f : Nat) (ts : List Term) (x : Nat)
    (h : x ∈ (Term.con f ts).vars) :
    (substVar σ x).size < (subst σ (.con f ts)).size := by
  have := size_substVar_le_list σ ts x (by simpa [Term.vars] using h)
  simp only [subst, Term.size]
  omega

theorem mem_vars_of_occurs {x : Nat} {u : Term} (h : occurs x u = true) : x ∈ u.vars := by
  simpa [occurs] using h

theorem not_mem_vars_of_occurs_false {x : Nat} {u : Term} (h : occurs x u = false) :
    x ∉ u.vars := by
  simpa [occurs] using h

/-- No substitution equates a variable with a different term in which it occurs. -/
theorem not_unifies_var_of_occurs {x : Nat} {u : Term} (hocc : occurs x u = true)
    (hne : u ≠ .var x) (σ : Subst) : subst σ (.var x) ≠ subst σ u := by
  have hx := mem_vars_of_occurs hocc
  cases u with
  | var y =>
    simp only [Term.vars, List.mem_singleton] at hx
    subst hx
    exact absurd rfl hne
  | con f ts =>
    intro h
    have := size_substVar_lt_con σ f ts x hx
    rw [← h] at this
    exact Nat.lt_irrefl _ this

/-! ## Variables of a substituted term -/

mutual
theorem mem_vars_subst (σ : Subst) :
    ∀ (w : Term) (z : Nat), z ∈ (subst σ w).vars → ∃ y ∈ w.vars, z ∈ (substVar σ y).vars
  | .var y, z, h => ⟨y, by simp [Term.vars], h⟩
  | .con f ts, z, h => by
    simp only [subst, Term.vars] at h
    obtain ⟨y, hy, hz⟩ := mem_varsList_substList σ ts z h
    exact ⟨y, by simpa [Term.vars] using hy, hz⟩
theorem mem_varsList_substList (σ : Subst) :
    ∀ (ts : List Term) (z : Nat), z ∈ Term.varsList (substList σ ts) →
      ∃ y ∈ Term.varsList ts, z ∈ (substVar σ y).vars
  | [], z, h => by simp [substList, Term.varsList] at h
  | t :: ts, z, h => by
    simp only [substList, Term.varsList, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨y, hy, hz⟩ := mem_vars_subst σ t z h
      exact ⟨y, by simp [Term.varsList, hy], hz⟩
    · obtain ⟨y, hy, hz⟩ := mem_varsList_substList σ ts z h
      exact ⟨y, by simp [Term.varsList, hy], hz⟩
end

theorem substVar_single (x : Nat) (u : Term) (y : Nat) :
    substVar [(x, u)] y = if y = x then u else .var y := by
  rw [substVar_cons, substVar_nil]

/-- The variables of `w[x := u]` are those of `w` other than `x`, and those of `u`. -/
theorem mem_vars_subst_single {x : Nat} {u w : Term} {z : Nat}
    (h : z ∈ (subst [(x, u)] w).vars) : (z ∈ w.vars ∧ z ≠ x) ∨ z ∈ u.vars := by
  obtain ⟨y, hy, hz⟩ := mem_vars_subst [(x, u)] w z h
  rw [substVar_single] at hz
  by_cases hyx : y = x
  · simp only [hyx, ite_true] at hz
    exact Or.inr hz
  · simp only [hyx, ite_false, Term.vars, List.mem_singleton] at hz
    subst hz
    exact Or.inl ⟨hy, hyx⟩

/-! ## Lookups in association lists -/

/-- The image of a variable is either a right-hand side bound to it, or the variable itself. -/
theorem substVar_cases (σ : Subst) (x : Nat) :
    (∃ q ∈ σ, q.1 = x ∧ substVar σ x = q.2) ∨ substVar σ x = .var x := by
  induction σ with
  | nil => exact Or.inr rfl
  | cons q σ ih =>
    obtain ⟨y, w⟩ := q
    rw [substVar_cons]
    by_cases hxy : x = y
    · subst hxy
      exact Or.inl ⟨(x, w), List.mem_cons_self, rfl, by simp⟩
    · simp only [hxy, ite_false]
      rcases ih with ⟨q, hq, h1, h2⟩ | h
      · exact Or.inl ⟨q, List.mem_cons_of_mem _ hq, h1, h2⟩
      · exact Or.inr h

theorem substVar_of_not_key {σ : Subst} {x : Nat} (h : ∀ q ∈ σ, q.1 ≠ x) :
    substVar σ x = .var x := by
  rcases substVar_cases σ x with ⟨q, hq, h1, _⟩ | h'
  · exact absurd h1 (h q hq)
  · exact h'

theorem substVar_of_mem_nodup {σ : Subst} (hnd : (σ.map Prod.fst).Nodup) {p : Nat × Term}
    (hp : p ∈ σ) : substVar σ p.1 = p.2 := by
  induction σ with
  | nil => cases hp
  | cons q σ ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    obtain ⟨hq, hnd⟩ := hnd
    obtain ⟨y, w⟩ := q
    rw [substVar_cons]
    rcases List.mem_cons.1 hp with rfl | hp
    · simp
    · have hne : p.1 ≠ y := fun h => hq ⟨p, hp, h⟩
      simp only [hne, ite_false]
      exact ih hnd hp

/-! ## Decomposition -/

mutual
/-- The unifier set of an equation is unchanged by decomposition. -/
theorem decomp_some_iff : ∀ (s t : Term) (bs : List (Nat × Term)), decomp s t = some bs →
    ∀ τ : Subst, (subst τ s = subst τ t ↔ ∀ p ∈ bs, substVar τ p.1 = subst τ p.2)
  | .var x, .var y, bs, h, τ => by
    by_cases hxy : x = y
    · simp only [decomp, hxy, ite_true, Option.some.injEq] at h
      subst h hxy
      simp
    · simp only [decomp, hxy, ite_false, Option.some.injEq] at h
      subst h
      simp [subst]
  | .var x, .con g ts, bs, h, τ => by
    simp only [decomp, Option.some.injEq] at h
    subst h
    simp [subst_var]
  | .con f ss, .var x, bs, h, τ => by
    simp only [decomp, Option.some.injEq] at h
    subst h
    simp [subst_var, eq_comm]
  | .con f ss, .con g ts, bs, h, τ => by
    by_cases hfg : f = g
    · subst hfg
      simp only [decomp, ite_true] at h
      simp only [subst, Term.con.injEq, true_and]
      exact decompList_some_iff ss ts bs h τ
    · simp [decomp, hfg] at h
/-- List companion of `decomp_some_iff`. -/
theorem decompList_some_iff : ∀ (ss ts : List Term) (bs : List (Nat × Term)),
    decompList ss ts = some bs →
    ∀ τ : Subst, (substList τ ss = substList τ ts ↔ ∀ p ∈ bs, substVar τ p.1 = subst τ p.2)
  | [], [], bs, h, τ => by
    simp only [decompList, Option.some.injEq] at h
    subst h
    simp [substList]
  | s :: ss, t :: ts, bs, h, τ => by
    cases h1 : decomp s t with
    | none => simp [decompList, h1] at h
    | some a =>
      cases h2 : decompList ss ts with
      | none => simp [decompList, h1, h2] at h
      | some b =>
        simp only [decompList, h1, h2, Option.some.injEq] at h
        subst h
        simp only [substList, List.cons.injEq, decomp_some_iff s t a h1 τ,
          decompList_some_iff ss ts b h2 τ, List.mem_append]
        constructor
        · rintro ⟨ha, hb⟩ p (hp | hp)
          · exact ha p hp
          · exact hb p hp
        · intro hab
          exact ⟨fun p hp => hab p (Or.inl hp), fun p hp => hab p (Or.inr hp)⟩
  | [], _ :: _, bs, h, _ => by simp [decompList] at h
  | _ :: _, [], bs, h, _ => by simp [decompList] at h
end

mutual
/-- A decomposition failure (clash) means no substitution unifies the equation. -/
theorem decomp_none : ∀ (s t : Term), decomp s t = none → ∀ τ : Subst, subst τ s ≠ subst τ t
  | .var x, .var y, h, _ => by by_cases hxy : x = y <;> simp [decomp, hxy] at h
  | .var _, .con _ _, h, _ => by simp [decomp] at h
  | .con _ _, .var _, h, _ => by simp [decomp] at h
  | .con f ss, .con g ts, h, τ => by
    intro heq
    simp only [subst, Term.con.injEq] at heq
    obtain ⟨hfg, hl⟩ := heq
    subst hfg
    simp only [decomp, ite_true] at h
    exact decompList_none ss ts h τ hl
/-- List companion of `decomp_none`. -/
theorem decompList_none : ∀ (ss ts : List Term), decompList ss ts = none →
    ∀ τ : Subst, substList τ ss ≠ substList τ ts
  | [], [], h, _ => by simp [decompList] at h
  | s :: ss, t :: ts, h, τ => by
    intro heq
    simp only [substList, List.cons.injEq] at heq
    cases h1 : decomp s t with
    | none => exact decomp_none s t h1 τ heq.1
    | some a =>
      cases h2 : decompList ss ts with
      | none => exact decompList_none ss ts h2 τ heq.2
      | some b => simp [decompList, h1, h2] at h
  | [], _ :: _, _, τ => by intro heq; simp [substList] at heq
  | _ :: _, [], _, τ => by intro heq; simp [substList] at heq
end

/-- A binding produced by decomposition, relative to the variable list `V` of the decomposed
equations: its variable and the variables of its right-hand side are in `V`, and the right-hand
side is not the bound variable itself. -/
def BindingOK (V : List Nat) (p : Nat × Term) : Prop :=
  p.1 ∈ V ∧ (∀ z ∈ p.2.vars, z ∈ V) ∧ p.2 ≠ .var p.1

theorem BindingOK.mono {V W : List Nat} (hVW : ∀ z ∈ V, z ∈ W) {p : Nat × Term}
    (h : BindingOK V p) : BindingOK W p :=
  ⟨hVW _ h.1, fun z hz => hVW z (h.2.1 z hz), h.2.2⟩

mutual
theorem decomp_bindingOK : ∀ (s t : Term) (bs : List (Nat × Term)), decomp s t = some bs →
    ∀ p ∈ bs, BindingOK (s.vars ++ t.vars) p
  | .var x, .var y, bs, h, p, hp => by
    by_cases hxy : x = y
    · simp only [decomp, hxy, ite_true, Option.some.injEq] at h
      subst h
      cases hp
    · simp only [decomp, hxy, ite_false, Option.some.injEq] at h
      subst h
      simp only [List.mem_singleton] at hp
      subst hp
      refine ⟨by simp [Term.vars], fun z hz => by simp_all [Term.vars], ?_⟩
      intro h'
      exact hxy (Term.var.inj h').symm
  | .var x, .con g ts, bs, h, p, hp => by
    simp only [decomp, Option.some.injEq] at h
    subst h
    simp only [List.mem_singleton] at hp
    subst hp
    exact ⟨by simp [Term.vars], fun z hz => by simp_all [Term.vars], nofun⟩
  | .con f ss, .var x, bs, h, p, hp => by
    simp only [decomp, Option.some.injEq] at h
    subst h
    simp only [List.mem_singleton] at hp
    subst hp
    exact ⟨by simp [Term.vars], fun z hz => by simp_all [Term.vars], nofun⟩
  | .con f ss, .con g ts, bs, h, p, hp => by
    by_cases hfg : f = g
    · subst hfg
      simp only [decomp, ite_true] at h
      exact decompList_bindingOK ss ts bs h p hp
    · simp [decomp, hfg] at h
theorem decompList_bindingOK : ∀ (ss ts : List Term) (bs : List (Nat × Term)),
    decompList ss ts = some bs →
    ∀ p ∈ bs, BindingOK (Term.varsList ss ++ Term.varsList ts) p
  | [], [], bs, h, p, hp => by
    simp only [decompList, Option.some.injEq] at h
    subst h
    cases hp
  | s :: ss, t :: ts, bs, h, p, hp => by
    cases h1 : decomp s t with
    | none => simp [decompList, h1] at h
    | some a =>
      cases h2 : decompList ss ts with
      | none => simp [decompList, h1, h2] at h
      | some b =>
        simp only [decompList, h1, h2, Option.some.injEq] at h
        subst h
        rcases List.mem_append.1 hp with hp | hp
        · exact (decomp_bindingOK s t a h1 p hp).mono
            (fun z hz => by
              simp only [Term.varsList, List.mem_append] at hz ⊢
              rcases hz with h | h <;> simp [h])
        · exact (decompList_bindingOK ss ts b h2 p hp).mono
            (fun z hz => by
              simp only [Term.varsList, List.mem_append] at hz ⊢
              rcases hz with h | h <;> simp [h])
  | [], _ :: _, bs, h, _, _ => by simp [decompList] at h
  | _ :: _, [], bs, h, _, _ => by simp [decompList] at h
end

/-! ## Decomposition of an equation list -/

theorem mem_eqsVars {eqs : List (Term × Term)} {z : Nat} :
    z ∈ eqsVars eqs ↔ ∃ e ∈ eqs, z ∈ e.1.vars ∨ z ∈ e.2.vars := by
  simp [eqsVars, List.mem_flatMap]

theorem decompAll_some_iff : ∀ (eqs : List (Term × Term)) (bs : List (Nat × Term)),
    decompAll eqs = some bs →
    ∀ τ : Subst, ((∀ e ∈ eqs, subst τ e.1 = subst τ e.2) ↔
      ∀ p ∈ bs, substVar τ p.1 = subst τ p.2)
  | [], bs, h, τ => by
    simp only [decompAll, Option.some.injEq] at h
    subst h
    simp
  | (s, t) :: es, bs, h, τ => by
    cases h1 : decomp s t with
    | none => simp [decompAll, h1] at h
    | some a =>
      cases h2 : decompAll es with
      | none => simp [decompAll, h1, h2] at h
      | some b =>
        simp only [decompAll, h1, h2, Option.some.injEq] at h
        subst h
        simp only [List.mem_cons, forall_eq_or_imp, decomp_some_iff s t a h1 τ,
          decompAll_some_iff es b h2 τ, List.mem_append]
        constructor
        · rintro ⟨ha, hb⟩ p (hp | hp)
          · exact ha p hp
          · exact hb p hp
        · intro hab
          exact ⟨fun p hp => hab p (Or.inl hp), fun p hp => hab p (Or.inr hp)⟩

theorem decompAll_none : ∀ (eqs : List (Term × Term)), decompAll eqs = none →
    ∀ τ : Subst, ¬ ∀ e ∈ eqs, subst τ e.1 = subst τ e.2
  | [], h, _ => by simp [decompAll] at h
  | (s, t) :: es, h, τ => by
    intro hall
    cases h1 : decomp s t with
    | none => exact decomp_none s t h1 τ (hall (s, t) List.mem_cons_self)
    | some a =>
      cases h2 : decompAll es with
      | none => exact decompAll_none es h2 τ (fun e he => hall e (List.mem_cons_of_mem _ he))
      | some b => simp [decompAll, h1, h2] at h

theorem decompAll_bindingOK : ∀ (eqs : List (Term × Term)) (bs : List (Nat × Term)),
    decompAll eqs = some bs → ∀ p ∈ bs, BindingOK (eqsVars eqs) p
  | [], bs, h, p, hp => by
    simp only [decompAll, Option.some.injEq] at h
    subst h
    cases hp
  | (s, t) :: es, bs, h, p, hp => by
    cases h1 : decomp s t with
    | none => simp [decompAll, h1] at h
    | some a =>
      cases h2 : decompAll es with
      | none => simp [decompAll, h1, h2] at h
      | some b =>
        simp only [decompAll, h1, h2, Option.some.injEq] at h
        subst h
        rcases List.mem_append.1 hp with hp | hp
        · exact (decomp_bindingOK s t a h1 p hp).mono (fun z hz => by
            rw [mem_eqsVars]
            simp only [List.mem_append] at hz
            exact ⟨(s, t), List.mem_cons_self, hz⟩)
        · exact (decompAll_bindingOK es b h2 p hp).mono (fun z hz => by
            rw [mem_eqsVars] at hz ⊢
            obtain ⟨e, he, hz⟩ := hz
            exact ⟨e, List.mem_cons_of_mem _ he, hz⟩)

/-! ## One pass of the algorithm -/

/-- The new solved substitution after eliminating `x ↦ u`. -/
def elimSolved (x : Nat) (u : Term) (σ : Subst) : Subst :=
  (x, u) :: σ.map (fun p => (p.1, subst [(x, u)] p.2))

/-- Case analysis of one pass. -/
theorem step_cases (oc : Bool) (eqs : List (Term × Term)) (σ : Subst) :
    (decompAll eqs = none ∧ step oc eqs σ = .done .fail) ∨
    (decompAll eqs = some [] ∧ step oc eqs σ = .done (.ok σ)) ∨
    (∃ x u bs, decompAll eqs = some ((x, u) :: bs) ∧ oc = true ∧ occurs x u = true ∧
      step oc eqs σ = .done .fail) ∨
    (∃ x u bs, decompAll eqs = some ((x, u) :: bs) ∧ (oc && occurs x u) = false ∧
      step oc eqs σ = .next (bs.map (elimBinding x u)) (elimSolved x u σ)) := by
  cases h : decompAll eqs with
  | none => exact Or.inl ⟨rfl, by simp [step, h]⟩
  | some bs =>
    cases bs with
    | nil => exact Or.inr (Or.inl ⟨rfl, by simp [step, h]⟩)
    | cons b bs =>
      obtain ⟨x, u⟩ := b
      cases hoc : (oc && occurs x u) with
      | true =>
        simp only [Bool.and_eq_true] at hoc
        exact Or.inr (Or.inr (Or.inl ⟨x, u, bs, rfl, hoc.1, hoc.2, by simp [step, h, hoc]⟩))
      | false =>
        refine Or.inr (Or.inr (Or.inr ⟨x, u, bs, rfl, hoc, ?_⟩))
        simp [step, h, hoc, elimSolved]

/-- `τ` solves the combined system: the pending equations and the solved bindings. -/
def Sys (τ : Subst) (eqs : List (Term × Term)) (σ : Subst) : Prop :=
  (∀ e ∈ eqs, subst τ e.1 = subst τ e.2) ∧ ∀ p ∈ σ, substVar τ p.1 = subst τ p.2

/-- If `τ` maps `x` and `u` to the same term, substituting `u` for `x` first changes nothing. -/
theorem subst_subst_single_of_eq {τ : Subst} {x : Nat} {u : Term}
    (hx : substVar τ x = subst τ u) (w : Term) : subst τ (subst [(x, u)] w) = subst τ w := by
  refine (subst_comp_of_vars w (fun y _ => ?_)).symm
  rw [substVar_single]
  by_cases hyx : y = x
  · subst hyx
    simp [hx]
  · simp [hyx, subst_var]

/-- One elimination pass preserves the solutions of the combined system. -/
theorem sys_elim_iff (τ : Subst) (x : Nat) (u : Term) (bs : List (Nat × Term)) (σ : Subst) :
    ((∀ p ∈ (x, u) :: bs, substVar τ p.1 = subst τ p.2) ∧
      ∀ p ∈ σ, substVar τ p.1 = subst τ p.2) ↔
    Sys τ (bs.map (elimBinding x u)) (elimSolved x u σ) := by
  unfold Sys elimSolved
  simp only [List.mem_cons, forall_eq_or_imp, List.mem_map, forall_exists_index, and_imp]
  constructor
  · rintro ⟨⟨hx, hbs⟩, hσ⟩
    refine ⟨?_, hx, ?_⟩
    · rintro e b hb rfl
      simp only [elimBinding, subst_subst_single_of_eq hx]
      exact hbs b hb
    · rintro p q hq rfl
      simp only [subst_subst_single_of_eq hx]
      exact hσ q hq
  · rintro ⟨hbs, hx, hσ⟩
    refine ⟨⟨hx, fun b hb => ?_⟩, fun q hq => ?_⟩
    · have := hbs _ b hb rfl
      simp only [elimBinding, subst_subst_single_of_eq hx] at this
      exact this
    · have := hσ _ q hq rfl
      simp only [subst_subst_single_of_eq hx] at this
      exact this

/-- A `next` pass preserves the solutions of the combined system. -/
theorem step_next_sys {oc : Bool} {eqs eqs' : List (Term × Term)} {σ σ' : Subst}
    (h : step oc eqs σ = .next eqs' σ') (τ : Subst) : Sys τ eqs σ ↔ Sys τ eqs' σ' := by
  rcases step_cases oc eqs σ with ⟨_, hs⟩ | ⟨_, hs⟩ | ⟨_, _, _, _, _, _, hs⟩ |
      ⟨x, u, bs, hd, _, hs⟩
  · rw [hs] at h; cases h
  · rw [hs] at h; cases h
  · rw [hs] at h; cases h
  · rw [hs] at h
    cases h
    rw [← sys_elim_iff]
    unfold Sys
    rw [decompAll_some_iff eqs _ hd τ]

/-- A `fail` pass with the occurs check on means the combined system has no solution. -/
theorem step_true_fail {eqs : List (Term × Term)} {σ : Subst}
    (h : step true eqs σ = .done .fail) (τ : Subst) : ¬ Sys τ eqs σ := by
  rintro ⟨heqs, _⟩
  rcases step_cases true eqs σ with ⟨hd, _⟩ | ⟨_, hs⟩ | ⟨x, u, bs, hd, _, hocc, _⟩ |
      ⟨_, _, _, _, _, hs⟩
  · exact decompAll_none eqs hd τ heqs
  · rw [hs] at h; cases h
  · have hb := (decompAll_some_iff eqs _ hd τ).1 heqs (x, u) List.mem_cons_self
    have hok := decompAll_bindingOK eqs _ hd (x, u) List.mem_cons_self
    exact not_unifies_var_of_occurs hocc hok.2.2 τ hb
  · rw [hs] at h; cases h

/-- An `ok` pass: the pending equations impose nothing. -/
theorem step_ok {oc : Bool} {eqs : List (Term × Term)} {σ σ' : Subst}
    (h : step oc eqs σ = .done (.ok σ')) : σ' = σ ∧ ∀ τ, Sys τ eqs σ ↔ Sys τ [] σ := by
  rcases step_cases oc eqs σ with ⟨_, hs⟩ | ⟨hd, hs⟩ | ⟨_, _, _, _, _, _, hs⟩ |
      ⟨_, _, _, _, _, hs⟩
  · rw [hs] at h; cases h
  · rw [hs] at h
    cases h
    refine ⟨rfl, fun τ => ?_⟩
    unfold Sys
    rw [decompAll_some_iff eqs _ hd τ]
    simp
  · rw [hs] at h; cases h
  · rw [hs] at h; cases h

theorem step_ne_outOfFuel (oc : Bool) (eqs : List (Term × Term)) (σ : Subst) :
    step oc eqs σ ≠ .done .outOfFuel := by
  rcases step_cases oc eqs σ with ⟨_, hs⟩ | ⟨_, hs⟩ | ⟨_, _, _, _, _, _, hs⟩ |
      ⟨_, _, _, _, _, hs⟩ <;> rw [hs] <;> nofun

/-! ## The solved-form invariant -/

/-- After eliminating `x ↦ u` (with `x` not in `u`), every variable of the new pending
equations is a variable of the old ones other than `x`. -/
theorem mem_eqsVars_elim {V : List Nat} {x : Nat} {u : Term} {bs : List (Nat × Term)}
    (hbs : ∀ b ∈ bs, BindingOK V b) (hu : ∀ z ∈ u.vars, z ∈ V) (hxu : x ∉ u.vars) {z : Nat}
    (hz : z ∈ eqsVars (bs.map (elimBinding x u))) : z ≠ x ∧ z ∈ V := by
  rw [mem_eqsVars] at hz
  obtain ⟨e, he, hz⟩ := hz
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 he
  have hok := hbs b hb
  have key : ∀ w : Term, (∀ y ∈ w.vars, y ∈ V) → z ∈ (subst [(x, u)] w).vars →
      z ≠ x ∧ z ∈ V := by
    intro w hw hzw
    rcases mem_vars_subst_single hzw with ⟨hzw, hzx⟩ | hzu
    · exact ⟨hzx, hw z hzw⟩
    · exact ⟨fun h => hxu (h ▸ hzu), hu z hzu⟩
  rcases hz with hz | hz
  · exact key (.var b.1) (fun y hy => by
      simp only [Term.vars, List.mem_singleton] at hy
      exact hy ▸ hok.1) hz
  · exact key b.2 hok.2.1 hz

/-- The solved-form invariant of a state: the bound variables of `σ` are pairwise distinct and
occur neither in any right-hand side of `σ` nor in the pending equations. -/
def Inv (eqs : List (Term × Term)) (σ : Subst) : Prop :=
  (σ.map Prod.fst).Nodup ∧ (∀ p ∈ σ, ∀ q ∈ σ, q.1 ∉ p.2.vars) ∧ ∀ q ∈ σ, q.1 ∉ eqsVars eqs

theorem inv_init (eqs : List (Term × Term)) : Inv eqs [] :=
  ⟨List.nodup_nil, nofun, nofun⟩

theorem mem_elimSolved {x : Nat} {u : Term} {σ : Subst} {p : Nat × Term}
    (hp : p ∈ elimSolved x u σ) : p = (x, u) ∨ ∃ q ∈ σ, p = (q.1, subst [(x, u)] q.2) := by
  unfold elimSolved at hp
  rcases List.mem_cons.1 hp with h | h
  · exact Or.inl h
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 h
    exact Or.inr ⟨q, hq, rfl⟩

/-- With the occurs check on, a `next` pass preserves the solved-form invariant. -/
theorem step_true_next_inv {eqs eqs' : List (Term × Term)} {σ σ' : Subst}
    (h : step true eqs σ = .next eqs' σ') (hinv : Inv eqs σ) : Inv eqs' σ' := by
  obtain ⟨hnd, hrhs, heqs⟩ := hinv
  rcases step_cases true eqs σ with ⟨_, hs⟩ | ⟨_, hs⟩ | ⟨_, _, _, _, _, _, hs⟩ |
      ⟨x, u, bs, hd, hocc, hs⟩
  · rw [hs] at h; cases h
  · rw [hs] at h; cases h
  · rw [hs] at h; cases h
  rw [hs] at h
  cases h
  simp only [Bool.true_and] at hocc
  have hxu := not_mem_vars_of_occurs_false hocc
  have hok := decompAll_bindingOK eqs _ hd
  have hx : x ∈ eqsVars eqs := (hok (x, u) List.mem_cons_self).1
  have hu : ∀ z ∈ u.vars, z ∈ eqsVars eqs := (hok (x, u) List.mem_cons_self).2.1
  have hbs : ∀ b ∈ bs, BindingOK (eqsVars eqs) b := fun b hb => hok b (List.mem_cons_of_mem _ hb)
  -- every key of the new solved part is `x` or an old key
  have hkeys : ∀ q' ∈ elimSolved x u σ, q'.1 = x ∨ ∃ q ∈ σ, q'.1 = q.1 := by
    intro q' hq'
    rcases mem_elimSolved hq' with rfl | ⟨q, hq, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨q, hq, rfl⟩
  -- a variable that is neither `x` nor an old key is not a new key
  have hfree : ∀ z, z ≠ x → (∀ q ∈ σ, q.1 ≠ z) → ∀ q' ∈ elimSolved x u σ, q'.1 ≠ z := by
    intro z hzx hzσ q' hq'
    rcases hkeys q' hq' with h | ⟨q, hq, h⟩
    · rw [h]; exact fun h' => hzx h'.symm
    · rw [h]; exact hzσ q hq
  have hV : ∀ z ∈ eqsVars eqs, ∀ q ∈ σ, q.1 ≠ z := fun z hz q hq h => heqs q hq (h ▸ hz)
  refine ⟨?_, ?_, ?_⟩
  · unfold elimSolved
    simp only [List.map_cons, List.map_map, List.nodup_cons]
    refine ⟨?_, ?_⟩
    · intro hmem
      obtain ⟨q, hq, hqx⟩ := List.mem_map.1 hmem
      exact hV x hx q hq hqx
    · have : (Prod.fst ∘ fun p : Nat × Term => (p.1, subst [(x, u)] p.2)) = Prod.fst := rfl
      rw [this]
      exact hnd
  · intro p hp q' hq' hmem
    refine hfree q'.1 ?_ ?_ q' hq' rfl
    · rcases mem_elimSolved hp with rfl | ⟨q, _, rfl⟩
      · exact fun h => hxu (h ▸ hmem)
      · rcases mem_vars_subst_single hmem with ⟨_, hne⟩ | hzu
        · exact hne
        · exact fun h => hxu (h ▸ hzu)
    · rcases mem_elimSolved hp with rfl | ⟨q, hq, rfl⟩
      · exact hV q'.1 (hu _ hmem)
      · rcases mem_vars_subst_single hmem with ⟨hzq, _⟩ | hzu
        · exact fun q'' hq'' h => hrhs q hq q'' hq'' (h ▸ hzq)
        · exact hV q'.1 (hu _ hzu)
  · intro q' hq' hmem
    have := mem_eqsVars_elim hbs hu hxu hmem
    exact hfree q'.1 this.1 (hV q'.1 this.2) q' hq' rfl

/-! ## The termination measure -/

theorem nodup_eraseDups_nat : ∀ (l : List Nat), l.eraseDups.Nodup
  | [] => List.nodup_nil
  | a :: as => by
    rw [List.eraseDups_cons, List.nodup_cons]
    have : (as.filter fun b => !b == a).length < as.length + 1 :=
      Nat.lt_add_one_of_le (List.length_filter_le _ as)
    refine ⟨?_, nodup_eraseDups_nat _⟩
    intro h
    rw [List.mem_eraseDups, List.mem_filter] at h
    simp at h
termination_by l => l.length

theorem length_le_of_nodup_of_subset : ∀ {a b : List Nat}, a.Nodup → (∀ x ∈ a, x ∈ b) →
    a.length ≤ b.length
  | [], _, _, _ => Nat.zero_le _
  | x :: a, b, hnd, hsub => by
    rw [List.nodup_cons] at hnd
    have hxb : x ∈ b := hsub x List.mem_cons_self
    have ih := length_le_of_nodup_of_subset (b := b.erase x) hnd.2 (fun y hy => by
      have hyx : y ≠ x := fun h => hnd.1 (h ▸ hy)
      exact (List.mem_erase_of_ne hyx).2 (hsub y (List.mem_cons_of_mem _ hy)))
    rw [List.length_erase_of_mem hxb] at ih
    have : 0 < b.length := List.length_pos_of_mem hxb
    simp only [List.length_cons]
    omega

/-- The measure strictly decreases when a variable disappears and none is added. -/
theorem numVars_lt {eqs eqs' : List (Term × Term)} {x : Nat}
    (hsub : ∀ z ∈ eqsVars eqs', z ∈ eqsVars eqs) (hx : x ∈ eqsVars eqs)
    (hx' : x ∉ eqsVars eqs') : numVars eqs' < numVars eqs := by
  unfold numVars
  have h := length_le_of_nodup_of_subset (a := x :: (eqsVars eqs').eraseDups)
    (b := (eqsVars eqs).eraseDups)
    (List.nodup_cons.2 ⟨by rw [List.mem_eraseDups]; exact hx', nodup_eraseDups_nat _⟩)
    (fun y hy => by
      rw [List.mem_eraseDups]
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hx
      · exact hsub y (List.mem_eraseDups.1 hy))
  simp only [List.length_cons] at h
  omega

theorem numVars_pos {eqs : List (Term × Term)} {x : Nat} (hx : x ∈ eqsVars eqs) :
    0 < numVars eqs :=
  List.length_pos_of_mem (List.mem_eraseDups.2 hx)

/-- With the occurs check on, a `next` pass strictly decreases the measure. -/
theorem step_true_next_numVars {eqs eqs' : List (Term × Term)} {σ σ' : Subst}
    (h : step true eqs σ = .next eqs' σ') : numVars eqs' < numVars eqs := by
  rcases step_cases true eqs σ with ⟨_, hs⟩ | ⟨_, hs⟩ | ⟨_, _, _, _, _, _, hs⟩ |
      ⟨x, u, bs, hd, hocc, hs⟩
  · rw [hs] at h; cases h
  · rw [hs] at h; cases h
  · rw [hs] at h; cases h
  rw [hs] at h
  cases h
  simp only [Bool.true_and] at hocc
  have hxu := not_mem_vars_of_occurs_false hocc
  have hok := decompAll_bindingOK eqs _ hd
  have hbs : ∀ b ∈ bs, BindingOK (eqsVars eqs) b := fun b hb => hok b (List.mem_cons_of_mem _ hb)
  exact numVars_lt (fun z hz => (mem_eqsVars_elim hbs (hok (x, u) List.mem_cons_self).2.1 hxu hz).2)
    (hok (x, u) List.mem_cons_self).1
    (fun hz => (mem_eqsVars_elim hbs (hok (x, u) List.mem_cons_self).2.1 hxu hz).1 rfl)

/-! ## Runs -/

theorem run_true_ne_outOfFuel : ∀ (fuel : Nat) (eqs : List (Term × Term)) (σ : Subst),
    numVars eqs ≤ fuel → run true fuel eqs σ ≠ .outOfFuel := by
  intro fuel
  induction fuel with
  | zero =>
    intro eqs σ hf
    unfold run
    cases hs : step true eqs σ with
    | done r =>
      simp only
      intro hr
      subst hr
      exact step_ne_outOfFuel true eqs σ hs
    | next eqs' σ' =>
      exfalso
      have h1 := step_true_next_numVars hs
      omega
  | succ n ih =>
    intro eqs σ hf
    unfold run
    cases hs : step true eqs σ with
    | done r =>
      simp only
      intro hr
      subst hr
      exact step_ne_outOfFuel true eqs σ hs
    | next eqs' σ' =>
      simp only
      have h1 := step_true_next_numVars hs
      exact ih eqs' σ' (by omega)

theorem run_true_fail : ∀ (fuel : Nat) (eqs : List (Term × Term)) (σ : Subst),
    run true fuel eqs σ = .fail → ∀ τ, ¬ Sys τ eqs σ := by
  intro fuel
  induction fuel with
  | zero =>
    intro eqs σ h τ
    unfold run at h
    cases hs : step true eqs σ with
    | done r =>
      rw [hs] at h
      simp only at h
      subst h
      exact step_true_fail hs τ
    | next eqs' σ' => rw [hs] at h; simp at h
  | succ n ih =>
    intro eqs σ h τ
    unfold run at h
    cases hs : step true eqs σ with
    | done r =>
      rw [hs] at h
      simp only at h
      subst h
      exact step_true_fail hs τ
    | next eqs' σ' =>
      rw [hs] at h
      simp only at h
      rw [step_next_sys hs τ]
      exact ih eqs' σ' h τ

theorem run_true_ok : ∀ (fuel : Nat) (eqs : List (Term × Term)) (σ σ' : Subst),
    run true fuel eqs σ = .ok σ' → Inv eqs σ →
      Inv [] σ' ∧ ∀ τ, Sys τ eqs σ ↔ Sys τ [] σ' := by
  intro fuel
  induction fuel with
  | zero =>
    intro eqs σ σ' h hinv
    unfold run at h
    cases hs : step true eqs σ with
    | done r =>
      rw [hs] at h
      simp only at h
      subst h
      obtain ⟨rfl, hsys⟩ := step_ok hs
      exact ⟨⟨hinv.1, hinv.2.1, fun _ _ h => by simp [eqsVars] at h⟩, hsys⟩
    | next eqs' σ'' => rw [hs] at h; simp at h
  | succ n ih =>
    intro eqs σ σ' h hinv
    unfold run at h
    cases hs : step true eqs σ with
    | done r =>
      rw [hs] at h
      simp only at h
      subst h
      obtain ⟨rfl, hsys⟩ := step_ok hs
      exact ⟨⟨hinv.1, hinv.2.1, fun _ _ h => by simp [eqsVars] at h⟩, hsys⟩
    | next eqs' σ'' =>
      rw [hs] at h
      simp only at h
      obtain ⟨hinv', hsys⟩ := ih eqs' σ'' σ' h (step_true_next_inv hs hinv)
      exact ⟨hinv', fun τ => (step_next_sys hs τ).trans (hsys τ)⟩

end Toy.Unify
