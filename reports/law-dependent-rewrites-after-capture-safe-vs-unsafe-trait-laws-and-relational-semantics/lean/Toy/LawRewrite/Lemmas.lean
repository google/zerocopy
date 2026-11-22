import Toy.LawRewrite.Basic

/-!
# Auxiliary lemmas

Small, fully proved facts about the toy language used by the examples and
counterexamples: reflexivity of refinement, the direct capture of an all-safe
environment, rewrites whose replacement equals the impl, shadowed rewrites, and the
extreme site selections of `Rewrite.applyAt`.
-/

namespace Toy.LawRewrite

/-- Prefix-preserving refinement is reflexive. -/
theorem refinesPP_refl (l : List Beh) : RefinesPP l l :=
  fun b hb => ⟨b, hb, Or.inl rfl⟩

/-- If every instance is safe, the direct capture (with either relies position) is the
compiled semantics. -/
theorem capDirect_eq_compiled_of_allSafe (env : Env) (pos : RelyPos)
    (h : ∀ i, env.safety i = .safeTrait) : capDirect env pos = compiled env := by
  have hc : directCalls env pos = compiledCalls env := by
    funext i v
    simp [directCalls, compiledCalls, h i]
  funext p σ
  simp [capDirect, compiled, hc]

/-- A rewrite whose replacement equals the impl at every targeted instance does not
change the compiled behaviours of any program. -/
theorem compiled_apply_eq_of_repl_eq_impl (env : Env) (ρ : Rewrite)
    (h : ∀ i, ρ.targets i = true → ρ.repl i = env.impl i) :
    ∀ (p : Prog) (σ : Store), compiled env (ρ.apply p) σ = compiled env p σ := by
  intro p
  induction p with
  | nil => intro σ; rfl
  | cons s p ih =>
    intro σ
    cases s with
    | set x v =>
      simp only [compiled, Rewrite.apply, List.map_cons, Rewrite.rwStmt, exec] at ih ⊢
      exact ih _
    | out x =>
      simp only [compiled, Rewrite.apply, List.map_cons, Rewrite.rwStmt, exec] at ih ⊢
      rw [ih]
    | prim f dst src =>
      simp only [compiled, Rewrite.apply, List.map_cons, Rewrite.rwStmt, exec] at ih ⊢
      rw [ih]
    | call i dst src =>
      cases ht : ρ.targets i with
      | false =>
        simp only [compiled, Rewrite.apply, List.map_cons, Rewrite.rwStmt, ht,
          Bool.false_eq_true, ↓reduceIte, exec, compiledCalls, List.flatMap_singleton] at ih ⊢
        rw [ih]
      | true =>
        simp only [compiled, Rewrite.apply, List.map_cons, Rewrite.rwStmt, ht, ↓reduceIte,
          exec, compiledCalls, List.flatMap_singleton, h i ht] at ih ⊢
        rw [ih]
    | ub => rfl

/-- If every instance that `ρ₂` targets is also targeted by `ρ₁`, then applying `ρ₂`
after `ρ₁` changes nothing: `ρ₁` has already replaced every call `ρ₂` could match. -/
theorem apply_apply_of_targets_le (ρ₁ ρ₂ : Rewrite)
    (h : ∀ i, ρ₂.targets i = true → ρ₁.targets i = true) (p : Prog) :
    ρ₂.apply (ρ₁.apply p) = ρ₁.apply p := by
  induction p with
  | nil => rfl
  | cons s p ih =>
    simp only [Rewrite.apply, List.map_cons] at ih ⊢
    rw [ih]
    congr 1
    cases s with
    | call i dst src =>
      cases h1 : ρ₁.targets i with
      | true => simp [Rewrite.rwStmt, h1]
      | false =>
        have h2 : ρ₂.targets i = false := by
          cases h2 : ρ₂.targets i with
          | false => rfl
          | true => exact absurd (h i h2) (by simp [h1])
        simp [Rewrite.rwStmt, h1, h2]
    | _ => rfl

/-- Selecting every site applies the rewrite everywhere. -/
theorem applyAt_const_true (ρ : Rewrite) :
    ∀ (k : Nat) (p : Prog), ρ.applyAt (fun _ => true) k p = ρ.apply p := by
  intro k p
  induction p generalizing k with
  | nil => rfl
  | cons s p ih =>
    simp only [Rewrite.applyAt, ↓reduceIte, Rewrite.apply, List.map_cons] at ih ⊢
    rw [ih]

/-- Selecting no site leaves the program unchanged. -/
theorem applyAt_const_false (ρ : Rewrite) :
    ∀ (k : Nat) (p : Prog), ρ.applyAt (fun _ => false) k p = p := by
  intro k p
  induction p generalizing k with
  | nil => rfl
  | cons s p ih =>
    simp only [Rewrite.applyAt, Bool.false_eq_true, ↓reduceIte] at ih ⊢
    rw [ih]

/-- Applying a two-element sequence is applying its elements in order. -/
theorem applySeq_pair (ρ₁ ρ₂ : Rewrite) (p : Prog) :
    applySeq [ρ₁, ρ₂] p = ρ₂.apply (ρ₁.apply p) := rfl

/-- For an instance of a safe trait, `ContextSafeAt` is the law at that argument. -/
theorem contextSafeAt_iff_lawAt_of_safe (env : Env) (pos : RelyPos) (ρ : Rewrite)
    (i : Inst) (v : Val) (hsafe : env.safety i = .safeTrait) :
    ContextSafeAt env pos ρ i v ↔ LawAt env ρ i v := by
  constructor
  · rintro (h | ⟨hu, _, _⟩)
    · exact h
    · rw [hsafe] at hu; cases hu
  · exact Or.inl

/-- Relational choices compose by list concatenation: the alternatives at a call for
`ρs₁ ++ ρs₂` are those for `ρs₁` followed by the replacement alternatives that `ρs₂`
contributes (the alternatives for `ρs₂` without its leading impl alternative). -/
theorem relCalls_append (env : Env) (ρs₁ ρs₂ : List Rewrite) (i : Inst) (v : Val) :
    relCalls env (ρs₁ ++ ρs₂) i v = relCalls env ρs₁ i v ++ (relCalls env ρs₂ i v).tail := by
  simp [relCalls, List.filterMap_append]

/-- When every targeted instance is safe, pointwise `ContextSafeAt` across all targeted
instances and arguments is equivalent to `LawOnTargets`. -/
theorem contextSafeAt_forall_iff_lawOnTargets_of_targetsSafe (env : Env) (pos : RelyPos)
    (ρ : Rewrite) (hsafe : ∀ i, ρ.targets i = true → env.safety i = .safeTrait) :
    (∀ i, ρ.targets i = true → ∀ v, ContextSafeAt env pos ρ i v) ↔ LawOnTargets env ρ := by
  unfold LawOnTargets
  constructor
  · intro h i ht v
    exact (contextSafeAt_iff_lawAt_of_safe env pos ρ i v (hsafe i ht)).mp (h i ht v)
  · intro h i ht v
    exact (contextSafeAt_iff_lawAt_of_safe env pos ρ i v (hsafe i ht)).mpr (h i ht v)

/-- Every compiled execution produces exactly one behaviour. -/
theorem compiled_singleton (env : Env) (p : Prog) (σ : Store) :
    ∃ b, compiled env p σ = [b] := by
  induction p generalizing σ with
  | nil => exact ⟨.done [], rfl⟩
  | cons s p ih =>
    cases s with
    | set x v => exact ih (σ.upd x v)
    | out x =>
      obtain ⟨b, hb⟩ := ih σ
      exact ⟨Beh.prepend [σ x] b, by simp only [compiled, exec] at hb ⊢; rw [hb]; rfl⟩
    | prim f dst src =>
      obtain ⟨b, hb⟩ := ih (σ.upd dst (f (σ src)).2)
      exact ⟨Beh.prepend (f (σ src)).1 b, by simp only [compiled, exec] at hb ⊢; rw [hb]; rfl⟩
    | call i dst src =>
      obtain ⟨b, hb⟩ := ih (σ.upd dst (env.impl i (σ src)).2)
      exact ⟨Beh.prepend (env.impl i (σ src)).1 b,
        by simp only [compiled, exec, compiledCalls, List.flatMap_singleton] at hb ⊢; rw [hb]; rfl⟩
    | ub => exact ⟨.ub [], rfl⟩

/-- Every direct-capture execution produces exactly one behaviour. -/
theorem capDirect_singleton (env : Env) (pos : RelyPos) (p : Prog) (σ : Store) :
    ∃ b, capDirect env pos p σ = [b] := by
  induction p generalizing σ with
  | nil => exact ⟨.done [], rfl⟩
  | cons s p ih =>
    cases s with
    | set x v => exact ih (σ.upd x v)
    | out x =>
      obtain ⟨b, hb⟩ := ih σ
      exact ⟨Beh.prepend [σ x] b, by simp only [capDirect, exec] at hb ⊢; rw [hb]; rfl⟩
    | prim f dst src =>
      obtain ⟨b, hb⟩ := ih (σ.upd dst (f (σ src)).2)
      exact ⟨Beh.prepend (f (σ src)).1 b, by simp only [capDirect, exec] at hb ⊢; rw [hb]; rfl⟩
    | call i dst src =>
      unfold capDirect
      simp only [exec, directCalls]
      cases env.safety i with
      | safeTrait =>
        obtain ⟨b, hb⟩ := ih (σ.upd dst (env.impl i (σ src)).2)
        unfold capDirect at hb
        exact ⟨Beh.prepend (env.impl i (σ src)).1 b, by simp only [List.flatMap_singleton, hb]; rfl⟩
      | unsafeTrait =>
        by_cases hc : env.impl i (σ src) = env.contract i (σ src)
        · obtain ⟨b, hb⟩ := ih (σ.upd dst (env.impl i (σ src)).2)
          unfold capDirect at hb
          exact ⟨Beh.prepend (env.impl i (σ src)).1 b,
            by simp only [ite_eq_left_iff.mpr (fun hne => absurd hc hne), List.flatMap_singleton, hb]; rfl⟩
        · cases pos with
          | before =>
            exact ⟨.ub [], by simp only [ite_eq_right_iff.mpr (fun heq => absurd heq hc), List.flatMap_singleton]⟩
          | after =>
            exact ⟨.ub (env.impl i (σ src)).1,
              by simp only [ite_eq_right_iff.mpr (fun heq => absurd heq hc), List.flatMap_singleton]⟩
    | ub => exact ⟨.ub [], rfl⟩

/-- Every relational-capture execution produces a non-empty list of behaviours. -/
theorem capRel_ne_nil (env : Env) (ρs : List Rewrite) (p : Prog) (σ : Store) :
    capRel env ρs p σ ≠ [] := by
  induction p generalizing σ with
  | nil => simp [capRel, exec]
  | cons s p ih =>
    cases s with
    | set x v => exact ih (σ.upd x v)
    | out x =>
      have ih' := ih σ
      unfold capRel at ih' ⊢
      simp only [exec, ne_eq, List.map_eq_nil_iff]
      exact ih'
    | prim f dst src =>
      have ih' := ih (σ.upd dst (f (σ src)).2)
      unfold capRel at ih' ⊢
      simp only [exec, ne_eq, List.map_eq_nil_iff]
      exact ih'
    | call i dst src =>
      simp only [capRel, exec, relCalls, List.flatMap_cons]
      intro h
      have h1 := (List.append_eq_nil_iff.mp h).1
      simp only [List.map_eq_nil_iff] at h1
      exact ih (σ.upd dst (env.impl i (σ src)).2) h1
    | ub => simp [capRel, exec]

/-- The single rewrite equivalent to applying a sequence `ρs` of call-free inline
rewrites in order: each instance `i` matched by some rewrite in `ρs` is replaced by the
replacement of the first matching rewrite in `ρs`. -/
def firstMatch (ρs : List Rewrite) : Rewrite where
  targets i := ρs.any (fun ρ => ρ.targets i)
  repl i := match ρs.find? (fun ρ => ρ.targets i) with
    | some ρ => ρ.repl i
    | none => copyImpl

private theorem applySeq_nil_prog (ρs : List Rewrite) : applySeq ρs [] = [] := by
  induction ρs with
  | nil => rfl
  | cons _ _ ih => exact ih

private theorem applySeq_noncall (ρs : List Rewrite) (s : Stmt) (p : Prog)
    (hnc : ∀ ρ : Rewrite, ρ.rwStmt s = s) :
    applySeq ρs (s :: p) = s :: applySeq ρs p := by
  induction ρs generalizing p with
  | nil => rfl
  | cons ρ ρs ih =>
    simp only [applySeq, List.foldl_cons, Rewrite.apply, List.map_cons, hnc ρ]
    exact ih (ρ.apply p)

private theorem applySeq_call (ρs : List Rewrite) (i : Inst) (dst src : Var) (p : Prog) :
    applySeq ρs (.call i dst src :: p) =
      (firstMatch ρs).rwStmt (.call i dst src) :: applySeq ρs p := by
  induction ρs generalizing p with
  | nil =>
    simp [applySeq, firstMatch, Rewrite.rwStmt]
  | cons ρ ρs ih =>
    cases ht : ρ.targets i with
    | true =>
      simp only [applySeq, List.foldl_cons, Rewrite.apply, List.map_cons, Rewrite.rwStmt,
        ht, ↓reduceIte, firstMatch, List.any_cons, Bool.true_or, List.find?_cons_of_pos]
      exact applySeq_noncall ρs _ (ρ.apply p) (fun _ => rfl)
    | false =>
      have hfm : (firstMatch (ρ :: ρs)).rwStmt (.call i dst src) =
          (firstMatch ρs).rwStmt (.call i dst src) := by
        simp [firstMatch, Rewrite.rwStmt, ht]
      rw [hfm]
      have hstep : applySeq (ρ :: ρs) (.call i dst src :: p) =
          applySeq ρs (.call i dst src :: ρ.apply p) := by
        simp [applySeq, Rewrite.apply, Rewrite.rwStmt, ht]
      rw [hstep]
      exact ih (ρ.apply p)

/-- Because every replacement is call-free inline code `prim f`, applying a sequence `ρs`
of rewrites equals applying the single rewrite `firstMatch ρs`. -/
theorem applySeq_eq_firstMatch (ρs : List Rewrite) (p : Prog) :
    applySeq ρs p = (firstMatch ρs).apply p := by
  induction p with
  | nil => exact applySeq_nil_prog ρs
  | cons s p ih =>
    cases s with
    | set x v => rw [applySeq_noncall ρs _ p (fun _ => rfl), ih]; rfl
    | out x => rw [applySeq_noncall ρs _ p (fun _ => rfl), ih]; rfl
    | prim f dst src => rw [applySeq_noncall ρs _ p (fun _ => rfl), ih]; rfl
    | ub => rw [applySeq_noncall ρs _ p (fun _ => rfl), ih]; rfl
    | call i dst src => rw [applySeq_call ρs i dst src p, ih]; rfl

end Toy.LawRewrite
