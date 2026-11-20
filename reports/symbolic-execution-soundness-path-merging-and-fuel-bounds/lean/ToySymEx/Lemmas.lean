import ToySymEx.Basic

/-!
General lemmas about the model, all fully proved: the encoded Boolean
connectives, guarded merging, membership congruence of the leaf-set
properties, closed terms, and CFG shapes. The examples and counterexamples use
them, and several result cards cite them as supporting facts.
-/

namespace Toy.SymEx

open Term

/-! ## Encoded connectives -/

theorem holds_or (c₁ c₂ : Term) (ρ : Valuation) :
    holds (Term.or c₁ c₂) ρ ↔ holds c₁ ρ ∨ holds c₂ ρ := by
  unfold holds Term.or
  show (if (c₁.eval ρ).toBool = true then Term.tt.eval ρ else c₂.eval ρ).toBool = true ↔ _
  by_cases h : (c₁.eval ρ).toBool = true
  · simp only [h, ↓reduceIte, true_or, iff_true]; rfl
  · simp only [h, ↓reduceIte, false_or, Bool.false_eq_true]

theorem holds_and (a b : Term) (ρ : Valuation) :
    holds (Term.and a b) ρ ↔ holds a ρ ∧ holds b ρ := by
  unfold holds Term.and
  show (if (a.eval ρ).toBool = true then b.eval ρ else Term.ff.eval ρ).toBool = true ↔ _
  cases ha : (a.eval ρ).toBool
  · constructor
    · intro h; nomatch h
    · rintro ⟨h, _⟩; nomatch h
  · exact ⟨fun h => ⟨rfl, h⟩, fun ⟨_, h⟩ => h⟩

theorem holds_not (a : Term) (ρ : Valuation) :
    holds (Term.not a) ρ ↔ ¬ holds a ρ := by
  unfold holds Term.not
  show (if (a.eval ρ).toBool = true then Term.ff.eval ρ else Term.tt.eval ρ).toBool = true ↔
    ¬ ((a.eval ρ).toBool = true)
  cases ha : (a.eval ρ).toBool
  · constructor
    · intro _ h; nomatch h
    · intro _; rfl
  · constructor
    · intro h; nomatch h
    · intro h; exact absurd rfl h

/-! ## Guarded merging -/

theorem mergeStore_inst_of_holds (c₁ : Term) (σ₁ σ₂ : SymStore) (ρ : Valuation)
    (h : holds c₁ ρ) : (mergeStore c₁ σ₁ σ₂).inst ρ = σ₁.inst ρ := by
  funext x
  simp only [SymStore.inst, mergeStore, Term.eval]
  split
  · rfl
  · exact absurd h (by assumption)

theorem mergeStore_inst_of_not_holds (c₁ : Term) (σ₁ σ₂ : SymStore) (ρ : Valuation)
    (h : ¬ holds c₁ ρ) : (mergeStore c₁ σ₁ σ₂).inst ρ = σ₂.inst ρ := by
  funext x
  simp only [SymStore.inst, mergeStore, Term.eval]
  split
  · exact absurd (by assumption) h
  · rfl

/-- Disjoint guards agree on their (empty) overlap. -/
theorem agree_on_overlap_of_disjoint {α : Type} (K : Store → α) (c₁ : Term) (σ₁ : SymStore)
    (c₂ : Term) (σ₂ : SymStore) (h : Disjoint c₁ c₂) :
    ∀ ρ, holds c₁ ρ → holds c₂ ρ → K (σ₂.inst ρ) = K (σ₁.inst ρ) :=
  fun ρ h₁ h₂ => absurd ⟨h₁, h₂⟩ (h ρ)

/-- Two states sound for the same single-valued reference agree (through `K`)
wherever both guards hold. This is a consequence of soundness; the proof of
merge soundness does not need it. -/
theorem agree_on_overlap_of_guardedSound {α : Type} (R : Valuation → α) (K : Store → α)
    (c₁ : Term) (σ₁ : SymStore) (c₂ : Term) (σ₂ : SymStore)
    (h₁ : GuardedSound R K c₁ σ₁) (h₂ : GuardedSound R K c₂ σ₂) :
    ∀ ρ, holds c₁ ρ → holds c₂ ρ → K (σ₂.inst ρ) = K (σ₁.inst ρ) :=
  fun ρ hc₁ hc₂ => (h₂ ρ hc₂).symm.trans (h₁ ρ hc₁)

/-- Merge soundness for a possibly many-valued behaviour relation `B`: if every
behaviour produced by each state under its guard is allowed by `B`, so is every
behaviour produced by the guarded merge. No disjointness and no agreement on
the overlap is needed, because the merged store selects `σ₁` wherever `c₁`
holds. -/
theorem guardedMerge_sound_rel {α : Type} (B : Valuation → α → Prop) (K : Store → α)
    (c₁ : Term) (σ₁ : SymStore) (c₂ : Term) (σ₂ : SymStore)
    (h₁ : ∀ ρ, holds c₁ ρ → B ρ (K (σ₁.inst ρ)))
    (h₂ : ∀ ρ, holds c₂ ρ → B ρ (K (σ₂.inst ρ))) :
    ∀ ρ, holds (Term.or c₁ c₂) ρ → B ρ (K ((mergeStore c₁ σ₁ σ₂).inst ρ)) := by
  intro ρ hor
  by_cases hc₁ : holds c₁ ρ
  · rw [mergeStore_inst_of_holds _ _ _ _ hc₁]; exact h₁ ρ hc₁
  · rw [mergeStore_inst_of_not_holds _ _ _ _ hc₁]
    exact h₂ ρ (((holds_or c₁ c₂ ρ).1 hor).resolve_left hc₁)

/-- When dropping the merge guard is harmless: keeping `σ₁` under `c₁ ∨ c₂` is
sound if, wherever `c₂` holds, `σ₁` and `σ₂` are indistinguishable through
the continuation `K` (for example, they differ only in locals that `K` never
reads). -/
theorem unguardedMerge_sound_of_agree_on_second_guard {α : Type} (R : Valuation → α)
    (K : Store → α) (c₁ : Term) (σ₁ : SymStore) (c₂ : Term) (σ₂ : SymStore)
    (h₁ : GuardedSound R K c₁ σ₁) (h₂ : GuardedSound R K c₂ σ₂)
    (hag : ∀ ρ, holds c₂ ρ → K (σ₁.inst ρ) = K (σ₂.inst ρ)) :
    GuardedSound R K (Term.or c₁ c₂) σ₁ := by
  intro ρ hor
  rcases (holds_or c₁ c₂ ρ).1 hor with hc₁ | hc₂
  · exact h₁ ρ hc₁
  · exact (h₂ ρ hc₂).trans (hag ρ hc₂).symm

/-- Path-specific simplification stays sound when it is applied to each branch
before merging, under that branch's own path condition, and the merge guard is
left unchanged. -/
theorem guardedMerge_sound_of_simp_branches {α : Type} (R : Valuation → α) (K : Store → α)
    (c₁ : Term) (σ₁ : SymStore) (c₂ : Term) (σ₂ : SymStore) (S₁ S₂ : Term → Term)
    (hS₁ : SimpSoundUnder c₁ S₁) (hS₂ : SimpSoundUnder c₂ S₂)
    (h₁ : GuardedSound R K c₁ σ₁) (h₂ : GuardedSound R K c₂ σ₂) :
    GuardedSound R K (Term.or c₁ c₂) (mergeStore c₁ (fun x => S₁ (σ₁ x)) (fun x => S₂ (σ₂ x))) := by
  intro ρ hor
  by_cases hc₁ : holds c₁ ρ
  · rw [mergeStore_inst_of_holds _ _ _ _ hc₁]
    have e : SymStore.inst (fun x => S₁ (σ₁ x)) ρ = σ₁.inst ρ := by
      funext x; exact hS₁ (σ₁ x) ρ hc₁
    rw [e]; exact h₁ ρ hc₁
  · rw [mergeStore_inst_of_not_holds _ _ _ _ hc₁]
    have hc₂ := ((holds_or c₁ c₂ ρ).1 hor).resolve_left hc₁
    have e : SymStore.inst (fun x => S₂ (σ₂ x)) ρ = σ₂.inst ρ := by
      funext x; exact hS₂ (σ₂ x) ρ hc₂
    rw [e]; exact h₂ ρ hc₂

theorem mem_pairwise_or {α : Type} {R : α → α → Prop} {L : List α}
    (hpw : L.Pairwise R) {x y : α} (hx : x ∈ L) (hy : y ∈ L) :
    x = y ∨ R x y ∨ R y x := by
  induction L with
  | nil => nomatch hx
  | cons a rest ih =>
      obtain ⟨ha, hrest⟩ := List.pairwise_cons.1 hpw
      rcases List.mem_cons.1 hx with rfl | hx' <;> rcases List.mem_cons.1 hy with rfl | hy'
      · exact Or.inl rfl
      · exact Or.inr (Or.inl (ha y hy'))
      · exact Or.inr (Or.inr (ha x hx'))
      · exact ih hrest hx' hy'

/-- If every pair of guarded states in a covering list agrees (through `K`) on
the overlap of their guards — in particular, if the guards are pairwise
disjoint — then the covered relation has at most one behaviour per valuation.
So a genuinely many-valued relation can only be covered by a list in which
some pair of overlapping states disagrees. -/
theorem covers_pairwise_agree_single_valued {α : Type}
    (B : Valuation → α → Prop) (K : Store → α) (L : List (Term × SymStore))
    (hcov : Covers B K L)
    (hpw : L.Pairwise (fun cs₁ cs₂ => ∀ ρ, holds cs₁.1 ρ → holds cs₂.1 ρ →
      K (cs₂.2.inst ρ) = K (cs₁.2.inst ρ))) :
    ∀ ρ a₁ a₂, B ρ a₁ → B ρ a₂ → a₁ = a₂ := by
  intro ρ a₁ a₂ hb₁ hb₂
  obtain ⟨cs₁, hm₁, hc₁, hk₁⟩ := hcov ρ a₁ hb₁
  obtain ⟨cs₂, hm₂, hc₂, hk₂⟩ := hcov ρ a₂ hb₂
  rcases mem_pairwise_or hpw hm₁ hm₂ with rfl | h12 | h21
  · exact hk₁.symm.trans hk₂
  · exact hk₁.symm.trans ((h12 ρ hc₁ hc₂).symm.trans hk₂)
  · exact hk₁.symm.trans ((h21 ρ hc₂ hc₁).trans hk₂)

/-! ## Leaf-set properties depend only on membership

`LeavesSound`, `LeavesExhaustive` and `LeavesProve` quantify over list
membership, so they are invariant under reordering and duplication. In
particular the merge lemmas, stated for the first two leaves of a list, apply
to any two leaves after reordering. -/

theorem leavesSound_of_subset (p : Cfg) (f : Nat) {L L' : List Leaf}
    (hsub : ∀ l, l ∈ L' → l ∈ L) (hs : LeavesSound p f L) : LeavesSound p f L' :=
  fun l hl => hs l (hsub l hl)

theorem leavesExhaustive_of_subset {L L' : List Leaf}
    (hsub : ∀ l, l ∈ L → l ∈ L') (he : LeavesExhaustive L) : LeavesExhaustive L' :=
  fun ρ => let ⟨l, hl, hpc⟩ := he ρ; ⟨l, hsub l hl, hpc⟩

theorem leavesProve_of_subset {L L' : List Leaf} (Q : Store → Prop)
    (hsub : ∀ l, l ∈ L' → l ∈ L) (hp : LeavesProve L Q) : LeavesProve L' Q :=
  fun l hl => hp l (hsub l hl)

/-! ## Closed terms

A term without variables evaluates to the same value under every valuation.
Path conditions built from such terms can be checked at one valuation. -/

/-- The term mentions no variable. -/
def Term.closed : Term → Bool
  | .var _ => false
  | .lit _ => true
  | .add a b => a.closed && b.closed
  | .eq a b => a.closed && b.closed
  | .ite c t e => c.closed && t.closed && e.closed

theorem Term.eval_of_closed : ∀ (t : Term), t.closed = true → ∀ ρ ρ', t.eval ρ = t.eval ρ'
  | .var _, h, _, _ => nomatch h
  | .lit _, _, _, _ => rfl
  | .add a b, h, ρ, ρ' => by
      simp only [Term.closed, Bool.and_eq_true] at h
      simp only [Term.eval, Term.eval_of_closed a h.1 ρ ρ', Term.eval_of_closed b h.2 ρ ρ']
  | .eq a b, h, ρ, ρ' => by
      simp only [Term.closed, Bool.and_eq_true] at h
      simp only [Term.eval, Term.eval_of_closed a h.1 ρ ρ', Term.eval_of_closed b h.2 ρ ρ']
  | .ite c t e, h, ρ, ρ' => by
      simp only [Term.closed, Bool.and_eq_true] at h
      simp only [Term.eval, Term.eval_of_closed c h.1.1 ρ ρ', Term.eval_of_closed t h.1.2 ρ ρ',
        Term.eval_of_closed e h.2 ρ ρ']

theorem not_holds_of_closed (c : Term) (hc : c.closed = true) (ρ₀ : Valuation)
    (h : ¬ holds c ρ₀) (ρ : Valuation) : ¬ holds c ρ := by
  unfold holds at *
  rw [Term.eval_of_closed c hc ρ ρ₀]; exact h

/-! ## CFG shapes -/

theorem acyclic_of_forwardEdges (p : Cfg) (h : ForwardEdges p) : Acyclic p :=
  ⟨id, fun i hi b hb _ => h i hi b hb⟩

theorem forwardEdges_of_straightLine (p : Cfg) (hsl : StraightLine p) : ForwardEdges p := by
  intro i hi b hb
  have hterm := hsl.2 i hi
  by_cases hnext : i + 1 < p.length
  · simp only [hnext, ↓reduceIte] at hterm
    rw [hterm] at hb
    simp [Terminator.targetsOf] at hb
    omega
  · simp only [hnext, ↓reduceIte] at hterm
    rw [hterm] at hb
    nomatch hb

theorem acyclic_of_straightLine (p : Cfg) (hsl : StraightLine p) : Acyclic p :=
  acyclic_of_forwardEdges p (forwardEdges_of_straightLine p hsl)

end Toy.SymEx
