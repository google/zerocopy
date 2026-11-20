/-
Toy.Lens.Unfolded
=================

Everything in this file is **proved**.

Machine-checked *elementary readings* of the bundled notions used in the
conclusions of F1, F2 and F3.  Each lemma says that a bundled notion is
equivalent to a statement that mentions only `get`, `put`, `=`, `∀`, `∃`, `∧`.
The "unfolded" forms of the main results quote these right-hand sides, so the
unfolding itself is checked by Lean rather than by hand.
-/
import Toy.Lens.Complement

namespace Toy

namespace Lens

universe u v w x

section Pair

variable {S : Type u} {A : Type v} {B : Type w}

/-- Elementary reading of `Intertwines f l fst`: under `f`, `get` is the first
projection and `put` is first-coordinate update. -/
theorem intertwines_fst_iff {C : Type x} (f : S → A × C) (l : Lens S A) :
    Intertwines f l (fst : Lens (A × C) A) ↔
      (∀ s, (f s).1 = l.get s) ∧ (∀ s a, f (l.put s a) = (a, (f s).2)) :=
  ⟨fun h => ⟨h.get_eq, h.put_eq⟩, fun h => ⟨h.1, h.2⟩⟩

/-- Elementary reading of `IsProductDecomposition l₁ l₂` (the conclusion of
F1), mentioning only `get` and `put`:

1. two states with the same two views are equal;
2. every pair of views is realised by some state;
3. writing `a` through `l₁` makes the first view `a` and keeps the second;
4. writing `b` through `l₂` keeps the first view and makes the second `b`. -/
theorem isProductDecomposition_iff_elementary (l₁ : Lens S A) (l₂ : Lens S B) :
    IsProductDecomposition l₁ l₂ ↔
      (∀ s t, l₁.get s = l₁.get t → l₂.get s = l₂.get t → s = t) ∧
      (∀ a b, ∃ s, l₁.get s = a ∧ l₂.get s = b) ∧
      (∀ s a, l₁.get (l₁.put s a) = a ∧ l₂.get (l₁.put s a) = l₂.get s) ∧
      (∀ s b, l₁.get (l₂.put s b) = l₁.get s ∧ l₂.get (l₂.put s b) = b) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro s t h₁ h₂
      apply h.injective
      show (l₁.get s, l₂.get s) = (l₁.get t, l₂.get t)
      rw [h₁, h₂]
    · intro a b
      obtain ⟨s, hs⟩ := h.surjective (a, b)
      exact ⟨s, congrArg Prod.fst hs, congrArg Prod.snd hs⟩
    · intro s a
      have e := h.intertwines_fst.put_eq s a
      exact ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩
    · intro s b
      have e := h.intertwines_snd.put_eq s b
      exact ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩
  · intro ⟨hinj, hsurj, hp₁, hp₂⟩
    refine ⟨?_, ?_, ⟨fun _ => rfl, ?_⟩, ⟨fun _ => rfl, ?_⟩⟩
    · intro s t hst
      exact hinj s t (congrArg Prod.fst hst) (congrArg Prod.snd hst)
    · intro p
      obtain ⟨s, h₁, h₂⟩ := hsurj p.1 p.2
      refine ⟨s, ?_⟩
      show (l₁.get s, l₂.get s) = p
      rw [h₁, h₂]
    · intro s a
      show (l₁.get (l₁.put s a), l₂.get (l₁.put s a)) = (a, l₂.get s)
      rw [(hp₁ s a).1, (hp₁ s a).2]
    · intro s b
      show (l₁.get (l₂.put s b), l₂.get (l₂.put s b)) = (l₁.get s, b)
      rw [(hp₂ s b).1, (hp₂ s b).2]

/-- Elementary reading of `HasConstantComplement l` (the right-hand side of
F3). -/
theorem hasConstantComplement_iff_elementary (l : Lens S A) :
    HasConstantComplement l ↔
      ∃ (C : Type u) (e : Equiv S (A × C)),
        (∀ s, (e.toFun s).1 = l.get s) ∧
        (∀ s a, e.toFun (l.put s a) = (a, (e.toFun s).2)) := by
  constructor
  · intro ⟨C, e, h⟩
    exact ⟨C, e, h.get_eq, h.put_eq⟩
  · intro ⟨C, e, h₁, h₂⟩
    exact ⟨C, e, h₁, h₂⟩

/-- Elementary reading of `HasGhostComplement l₁ l₂` (the right-hand side of
the pair form of F3). -/
theorem hasGhostComplement_iff_elementary (l₁ : Lens S A) (l₂ : Lens S B) :
    HasGhostComplement l₁ l₂ ↔
      ∃ (G : Type u) (e : Equiv S (A × B × G)),
        (∀ s, (e.toFun s).1 = l₁.get s) ∧
        (∀ s a, e.toFun (l₁.put s a) = (a, (e.toFun s).2.1, (e.toFun s).2.2)) ∧
        (∀ s, (e.toFun s).2.1 = l₂.get s) ∧
        (∀ s b, e.toFun (l₂.put s b) = ((e.toFun s).1, b, (e.toFun s).2.2)) := by
  constructor
  · intro ⟨G, e, h₁, h₂⟩
    exact ⟨G, e, h₁.get_eq, h₁.put_eq, h₂.get_eq, h₂.put_eq⟩
  · intro ⟨G, e, g₁, p₁, g₂, p₂⟩
    exact ⟨G, e, ⟨g₁, p₁⟩, ⟨g₂, p₂⟩⟩

end Pair

section Family

variable {S : Type u} {ι : Type w} {A : ι → Type v}

/-- Elementary reading of `IsPiDecomposition l` (the conclusion of F2),
mentioning only `get` and `put`:

1. two states with the same views at every index are equal;
2. every tuple of views is realised by some state;
3. writing `a` through `l i` makes view `i` equal to `a`;
4. writing through `l i` keeps every other view. -/
theorem isPiDecomposition_iff_elementary [DecidableEq ι] (l : (i : ι) → Lens S (A i)) :
    IsPiDecomposition l ↔
      (∀ s t, (∀ i, (l i).get s = (l i).get t) → s = t) ∧
      (∀ f : (i : ι) → A i, ∃ s, ∀ i, (l i).get s = f i) ∧
      (∀ i s a, (l i).get ((l i).put s a) = a) ∧
      (∀ i j, i ≠ j → ∀ s a, (l j).get ((l i).put s a) = (l j).get s) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro s t hst
      exact h.injective (funext hst)
    · intro f
      obtain ⟨s, hs⟩ := h.surjective f
      exact ⟨s, fun i => congrFun hs i⟩
    · intro i s a
      have e := congrFun ((h.intertwines i).put_eq s a) i
      exact e.trans (update_same (famGet l s) i a)
    · intro i j hij s a
      have e := congrFun ((h.intertwines i).put_eq s a) j
      exact e.trans (update_of_ne (famGet l s) (fun hji => hij hji.symm) a)
  · intro ⟨hinj, hsurj, hpg, hind⟩
    refine ⟨?_, ?_, ?_⟩
    · intro s t hst
      exact hinj s t (fun i => congrFun hst i)
    · intro f
      obtain ⟨s, hs⟩ := hsurj f
      exact ⟨s, funext hs⟩
    · intro i
      refine ⟨fun _ => rfl, ?_⟩
      intro s a
      funext j
      show (l j).get ((l i).put s a) = update (famGet l s) i a j
      by_cases hji : j = i
      · subst hji
        rw [update_same]
        exact hpg j s a
      · rw [update_of_ne _ hji]
        exact hind i j (fun h => hji h.symm) s a

end Family

end Lens

end Toy
