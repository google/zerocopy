import ToyGhost.Programs

/-!
# Generic tools for counterexamples (fully proved)
-/

namespace Toy.Ghost

/-- If `A` from `σ` and `C` from `τ` have different real behaviours and the
behaviour of `A` is not in `Bot`, then `C` does not refine `A` up to `Bot`. -/
theorem not_refinesUpTo_of_behaves {Bot : RBehaviour → Prop} {A C : Stmt} {σ τ : Store}
    {a c : Behaviour} (hA : Behaves A σ a) (hC : Behaves C τ c) (hne : c.real ≠ a.real)
    (hbot : ¬ Bot a.real) : ¬ RefinesUpTo Bot A σ C τ := by
  rintro (⟨a', ha', hA'⟩ | h)
  · rw [(RBehaves.iff_of_behaves hA a').1 hA'] at ha'
    exact hbot ha'
  · have := h c.real (RBehaves.of_behaves hC)
    exact hne ((RBehaves.iff_of_behaves hA _).1 this)

/-- If `A` from `σ` and `C` from `τ` have different real behaviours, their real
behaviour sets differ. -/
theorem not_rbehaves_iff_of_behaves {A C : Stmt} {σ τ : Store} {a c : Behaviour}
    (hA : Behaves A σ a) (hC : Behaves C τ c) (hne : c.real ≠ a.real) :
    ¬ ∀ b, RBehaves A σ b ↔ RBehaves C τ b := by
  intro h
  have := (h c.real).2 (RBehaves.of_behaves hC)
  exact hne ((RBehaves.iff_of_behaves hA _).1 this)

/-- Refinement up to failure and up to divergence together give equality of real
behaviours (determinism and totality do the rest). -/
theorem rbehaves_iff_of_refinesUpTo_failBot_of_refinesUpTo_divBot {A C : Stmt} {σ τ : Store}
    (hF : RefinesUpTo failBot A σ C τ) (hD : RefinesUpTo divBot A σ C τ) :
    ∀ b, RBehaves A σ b ↔ RBehaves C τ b := by
  have hsub : ∀ b, RBehaves C τ b → RBehaves A σ b := by
    rcases hF with ⟨a, ha, hAa⟩ | h
    · rcases hD with ⟨a', ha', hAa'⟩ | h'
      · have := RBehaves.unique hAa hAa'
        simp only [failBot] at ha; simp only [divBot] at ha'
        subst ha ha'; cases this
      · exact h'
    · exact h
  obtain ⟨c, hc⟩ := RBehaves.exists C τ
  have hac := hsub c hc
  intro b
  constructor
  · intro hb; rw [RBehaves.unique hb hac]; exact hc
  · exact hsub b

theorem term_real_ne {σ τ : Store} (h : realPart σ ≠ realPart τ) :
    (Behaviour.term σ).real ≠ (Behaviour.term τ).real :=
  fun e => h (RBehaviour.term.inj e)

theorem realPart_update_congr {σ τ : Store} (h : realPart σ = realPart τ) (v : Var) (k : Int) :
    realPart (σ.update v k) = realPart (τ.update v k) := by
  funext j
  have := congrFun h j
  simp only [realPart, Store.update] at this ⊢
  split <;> simp_all

theorem rbehaves_term_iff {s : Stmt} {σ : Store} {r : RStore} :
    RBehaves s σ (.term r) ↔ ∃ σ', Behaves s σ (.term σ') ∧ realPart σ' = r := by
  constructor
  · rintro ⟨b, hb, hbr⟩
    cases b with
    | term σ' => exact ⟨σ', hb, RBehaviour.term.inj hbr⟩
    | fail => cases hbr
    | diverge => cases hbr
  · rintro ⟨σ', hb, rfl⟩; exact ⟨_, hb, rfl⟩

theorem rbehaves_fail_iff {s : Stmt} {σ : Store} : RBehaves s σ .fail ↔ Fails s σ := by
  constructor
  · rintro ⟨b, hb, hbr⟩
    cases b with
    | term _ => cases hbr
    | fail => exact hb
    | diverge => cases hbr
  · intro h; exact ⟨_, h, rfl⟩

theorem rbehaves_diverge_iff {s : Stmt} {σ : Store} : RBehaves s σ .diverge ↔ Diverges s σ := by
  constructor
  · rintro ⟨b, hb, hbr⟩
    cases b with
    | term _ => cases hbr
    | fail => cases hbr
    | diverge => exact hb
  · intro h; exact ⟨_, h, rfl⟩

/-! ## Establishing per-run ghost conditions for concrete programs -/

theorem ghostReach_skip (Q : Stmt → Store → Prop) (σ : Store) : ∀ n, GhostReach Q n .skip σ := by
  intro n; cases n <;> trivial

theorem ghostReach_assign (Q : Stmt → Store → Prop) (v : Var) (e : Expr) (σ : Store) :
    ∀ n, GhostReach Q n (.assign v e) σ := by
  intro n; cases n <;> trivial

theorem ghostReach_assert (Q : Stmt → Store → Prop) (e : Expr) (σ : Store) :
    ∀ n, GhostReach Q n (.assert e) σ := by
  intro n; cases n <;> trivial

theorem ghostReach_ghost {Q : Stmt → Store → Prop} {s : Stmt} {σ : Store} (h : Q s σ) :
    ∀ n, GhostReach Q n (.ghost s) σ := by
  intro n; cases n
  · trivial
  · exact h

/-- Sequencing: if the first statement terminates normally, the condition for the
sequence follows from the conditions for its parts. -/
theorem ghostReach_seq {Q : Stmt → Store → Prop} {s t : Stmt} {σ σ' : Store}
    (hs : ∀ n, GhostReach Q n s σ) (hrun : Behaves s σ (.term σ'))
    (ht : ∀ n, GhostReach Q n t σ') : ∀ n, GhostReach Q n (.seq s t) σ := by
  intro n; cases n with
  | zero => trivial
  | succ n =>
    refine ⟨hs n, fun σ'' h => ?_⟩
    obtain ⟨m, hm⟩ := hrun
    cases run_det h hm
    exact ht n

theorem assert_not_diverges (e : Expr) (σ : Store) : ¬ Diverges (.assert e) σ := by
  intro h
  have := h 1
  simp only [run] at this
  split at this <;> cases this

theorem assign_not_diverges (v : Var) (e : Expr) (σ : Store) : ¬ Diverges (.assign v e) σ := by
  intro h; cases h 1

theorem assign_not_fails (v : Var) (e : Expr) (σ : Store) : ¬ Fails (.assign v e) σ := by
  rintro ⟨n, hn⟩
  cases n with
  | zero => cases hn
  | succ n => cases hn

/-- A generic way to prove `ErasureExact` for a program whose original and erased
versions both terminate from every state. -/
theorem erasureExact_of_term {P : Stmt} (f h : Store → Store)
    (hP : ∀ σ, Behaves P σ (.term (f σ))) (hE : ∀ τ, Behaves (erase P) τ (.term (h τ)))
    (hr : ∀ σ τ, realPart σ = realPart τ → realPart (f σ) = realPart (h τ)) : ErasureExact P := by
  intro σ τ hστ b
  rw [RBehaves.iff_of_behaves (hP σ), RBehaves.iff_of_behaves (hE τ)]
  simp only [Behaviour.real, hr σ τ hστ]

/-! ## Loops with an empty body -/

theorem run_loop_skip_ok {c : Expr} {n : Nat} {σ σ' : Store}
    (h : run n (.loop c .skip) σ = some (.ok σ')) : σ' = σ := by
  induction n with
  | zero => cases h
  | succ n ih =>
    simp only [run] at h
    split at h
    · cases h; rfl
    · cases n with
      | zero => cases h
      | succ m =>
        simp only [run, Outcome.bind] at h
        exact ih h

theorem run_loop_skip_none {c : Expr} {σ : Store} (hc : ¬ c.eval σ = 0) :
    ∀ n, run n (.loop c .skip) σ = none := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [run, hc, ↓reduceIte]
    cases n with
    | zero => rfl
    | succ m => simpa [run, Outcome.bind] using ih

theorem run_loop_skip_not_fail {c : Expr} {n : Nat} {σ : Store} :
    run n (.loop c .skip) σ ≠ some .fail := by
  intro h
  induction n generalizing σ with
  | zero => cases h
  | succ n ih =>
    simp only [run] at h
    split at h
    · cases h
    · cases n with
      | zero => cases h
      | succ m =>
        simp only [run, Outcome.bind] at h
        exact ih h

end Toy.Ghost
