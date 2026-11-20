import ToyPredTrans.Programs

/-!
# Program algebra: `wp`/`wlp` of sequential composition and demonic choice

Everything in this file is fully proved.  These are shallow calculations: each is an
unfolding of the definitions followed by a rearrangement of quantifiers.
-/

namespace Toy.PredTrans

universe u

variable {σ : Type u}

/-! ## Sequential composition -/

/-- The `wlp` of a relational composition is the composition of the `wlp`s. -/
theorem wlp_comp (R₁ R₂ : Rel σ) :
    wlp (comp R₁ R₂) = fun Q => wlp R₁ (wlp R₂ Q) := by
  apply trans_ext
  intro Q s
  constructor
  · intro h s' h1 s'' h2
    exact h s'' ⟨s', h1, h2⟩
  · intro h s'' hc
    obtain ⟨s', h1, h2⟩ := hc
    exact h s' h1 s'' h2

/-- `seqTerm R₁ t₁ t₂` is, by definition, the `wp` of the first program applied to the
non-abortion domain of the second. -/
theorem seqTerm_eq_wp (R₁ : Rel σ) (t₁ t₂ : Pred σ) : seqTerm R₁ t₁ t₂ = wp R₁ t₁ t₂ := rfl

/-- The `wp` of a sequential composition is the composition of the `wp`s, where the composite
does not abort from `s` exactly when the first program does not abort from `s` and the second
does not abort from any intermediate state the first can reach (`seqTerm`). -/
theorem wp_comp (R₁ R₂ : Rel σ) (t₁ t₂ : Pred σ) :
    wp (comp R₁ R₂) (seqTerm R₁ t₁ t₂) = fun Q => wp R₁ t₁ (wp R₂ t₂ Q) := by
  apply trans_ext
  intro Q s
  constructor
  · intro h
    obtain ⟨⟨ht1, ht2⟩, hw⟩ := h
    exact ⟨ht1, fun s' h1 => ⟨ht2 s' h1, fun s'' h2 => hw s'' ⟨s', h1, h2⟩⟩⟩
  · intro h
    obtain ⟨ht1, hw⟩ := h
    refine ⟨⟨ht1, fun s' h1 => (hw s' h1).1⟩, ?_⟩
    intro s'' hc
    obtain ⟨s', h1, h2⟩ := hc
    exact (hw s' h1).2 s'' h2

/-- The termination predicate of the composite really is `seqTerm`, not the termination
predicate of the first component: `skip` followed by `abort` is not `wp` of the composed
relation with the first component's termination predicate. -/
theorem wp_comp_first_term_wrong :
    wp (comp (skipR : Rel Unit) skipR) (fun _ => True)
      ≠ fun Q => wp skipR (fun _ => True) (wp skipR (fun _ => False) Q) := by
  intro h
  have h1 : wp (comp (skipR : Rel Unit) skipR) (fun _ => True) (fun _ => True) () :=
    ⟨trivial, fun _ _ => trivial⟩
  rw [h] at h1
  exact (h1.2 () rfl).1

/-- The non-abortion domain of the composite is not the conjunction `t₁ ∧ t₂` of the
components' domains either: with `t₂` = "the state is `0`", the conjunction holds at `0`, but
`stepR` leaves `0`, so the composite of the `wp`s does not establish `True` there. -/
theorem wp_comp_conj_term_wrong :
    wp (comp stepR skipR) (fun s => True ∧ s = 0) ≠
      fun Q => wp stepR (fun _ => True) (wp skipR (fun s => s = 0) Q) := by
  intro h
  have h1 : wp (comp stepR skipR) (fun s => True ∧ s = 0) (fun _ => True) 0 :=
    ⟨⟨trivial, rfl⟩, fun _ _ => trivial⟩
  have h2 : wp stepR (fun _ => True) (wp skipR (fun s => s = 0) (fun _ => True)) 0 :=
    (congrFun (congrFun h (fun _ => True)) 0).mp h1
  have hbad : (1 : Nat) = 0 := (h2.2 1 (Or.inl rfl)).1
  omega

/-- A concrete instance of `wp_comp`: from `0`, `stepR` followed by the partial decrement
terminates and ends in a state `≤ 1`. -/
theorem wp_comp_example :
    wp (comp stepR predR) (seqTerm stepR (fun _ => True) posP) (fun n => n ≤ 1) 0 := by
  rw [wp_comp]
  refine ⟨trivial, ?_⟩
  intro s' hs
  have hs' : s' = 0 + 1 ∨ s' = 0 + 2 := hs
  refine ⟨?_, ?_⟩
  · show s' ≠ 0
    omega
  · intro s'' hp
    have hp' : s' = s'' + 1 := hp
    show s'' ≤ 1
    omega

/-- The chaos normal form is not preserved by `comp` and `seqTerm`: `abort` (in chaos normal
form) followed by `magic` (in chaos normal form) composes to a pair that is not. -/
theorem chaosNormal_not_preserved_by_comp :
    ChaosNormal (havocR : Rel Unit) (fun _ => False) ∧
    ChaosNormal (emptyR : Rel Unit) (fun _ => True) ∧
    ¬ ChaosNormal (comp (havocR : Rel Unit) emptyR)
        (seqTerm (havocR : Rel Unit) (fun _ => False) (fun _ => True)) := by
  refine ⟨fun _ _ _ => trivial, fun _ h => (h trivial).elim, ?_⟩
  intro h
  have hc : comp (havocR : Rel Unit) emptyR () () := h () (fun ht => ht.1) ()
  obtain ⟨_, _, hf⟩ := hc
  exact hf

/-! ## Demonic choice -/

/-- The `wlp` of a union of relations is the pointwise conjunction of the `wlp`s. -/
theorem wlp_union (R₁ R₂ : Rel σ) (Q : Pred σ) (s : σ) :
    wlp (union R₁ R₂) Q s ↔ wlp R₁ Q s ∧ wlp R₂ Q s := by
  constructor
  · intro h
    exact ⟨fun s' h1 => h s' (Or.inl h1), fun s' h2 => h s' (Or.inr h2)⟩
  · intro h s' hu
    rcases hu with h1 | h2
    · exact h.1 s' h1
    · exact h.2 s' h2

/-- The `wp` of a demonic choice is the pointwise conjunction of the `wp`s; the choice
terminates exactly where both alternatives terminate. -/
theorem wp_union (R₁ R₂ : Rel σ) (t₁ t₂ : Pred σ) (Q : Pred σ) (s : σ) :
    wp (union R₁ R₂) (fun s => t₁ s ∧ t₂ s) Q s ↔ wp R₁ t₁ Q s ∧ wp R₂ t₂ Q s := by
  constructor
  · intro h
    obtain ⟨⟨ht1, ht2⟩, hw⟩ := h
    exact ⟨⟨ht1, fun s' h1 => hw s' (Or.inl h1)⟩, ⟨ht2, fun s' h2 => hw s' (Or.inr h2)⟩⟩
  · intro h
    obtain ⟨⟨ht1, hw1⟩, ⟨ht2, hw2⟩⟩ := h
    refine ⟨⟨ht1, ht2⟩, ?_⟩
    intro s' hu
    rcases hu with h1 | h2
    · exact hw1 s' h1
    · exact hw2 s' h2

/-- The non-abortion domain of a demonic choice is the conjunction of the components' domains,
not their disjunction: with `t₁ = True` and `t₂ = False` the disjunction holds, but the second
alternative aborts. -/
theorem wp_union_disj_term_wrong :
    ¬ ∀ (Q : Pred Unit) (s : Unit),
      wp (union skipR skipR) (fun s => (fun _ => True) s ∨ (fun _ => False) s) Q s ↔
        wp skipR (fun _ => True) Q s ∧ wp skipR (fun _ => False) Q s := by
  intro h
  have h1 : wp (union (skipR : Rel Unit) skipR) (fun s => (fun _ => True) s ∨ (fun _ => False) s)
      (fun _ => True) () := ⟨Or.inl trivial, fun _ _ => trivial⟩
  exact ((h _ ()).mp h1).2.1

/-- The `wlp` of an arbitrary (possibly empty, possibly infinite) union of relations is the
conjunction of the `wlp`s. -/
theorem wlp_iUnion {ι : Sort _} (R : ι → Rel σ) (Q : Pred σ) (s : σ) :
    wlp (fun s s' => ∃ i, R i s s') Q s ↔ ∀ i, wlp (R i) Q s := by
  constructor
  · intro h i s' hr
    exact h s' ⟨i, hr⟩
  · intro h s' hr
    obtain ⟨i, hi⟩ := hr
    exact h i s' hi

/-! ## Units -/

/-- The `wp` of `skip` with the everywhere-true termination predicate is the identity
transformer. -/
theorem wp_skipR_true : wp (skipR : Rel σ) (fun _ => True) = fun Q => Q := by
  apply trans_ext
  intro Q s
  constructor
  · intro h
    exact h.2 s rfl
  · intro h
    refine ⟨trivial, ?_⟩
    intro s' hs
    have e : s' = s := hs
    rw [e]
    exact h

/-- The `wlp` of the empty relation establishes every postcondition (the miracle `magic` in the
demonic-update reading; guaranteed divergence in the partial-correctness reading). -/
theorem wlp_emptyR (Q : Pred σ) (s : σ) : wlp emptyR Q s :=
  fun _ h => False.elim h

end Toy.PredTrans
