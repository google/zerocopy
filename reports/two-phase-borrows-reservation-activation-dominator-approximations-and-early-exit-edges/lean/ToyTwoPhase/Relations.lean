import ToyTwoPhase.Graph

/-!
# Walk lemmas and graph relations used by the package

`Dom`, `PDom` and `Acyclic` are defined by quantifying over walks. Each comes with a proved
equivalence to a `PathVia` formulation, which yields a `Decidable` instance through
`pathViaB_iff`.
-/

namespace Toy.TwoPhase

variable {n : Nat}

/-! ## List lemmas about walks -/

theorem isWalk_ne_nil {E : Edges n} : ∀ {π : List (Fin n)}, IsWalk E π → π ≠ []
  | [], h, _ => h
  | _ :: _, _, h => List.cons_ne_nil _ _ h

theorem isWalk_tail {E : Edges n} {a : Fin n} :
    ∀ {π : List (Fin n)}, π ≠ [] → IsWalk E (a :: π) → IsWalk E π
  | [], h, _ => absurd rfl h
  | _ :: _, _, h => h.2

/-- Joining a walk ending at `x` with a walk starting at `x`. -/
theorem isWalk_join {E : Edges n} (x : Fin n) (m : List (Fin n)) (hm : IsWalk E (x :: m)) :
    ∀ l : List (Fin n), IsWalk E (l ++ [x]) → IsWalk E (l ++ x :: m)
  | [], _ => hm
  | [_], h => ⟨h.1, hm⟩
  | _ :: b :: t, h => ⟨h.1, isWalk_join x m hm (b :: t) h.2⟩

/-- The prefix of a walk up to (and including) a node `x` is a walk. -/
theorem isWalk_prefix {E : Edges n} (x : Fin n) (m : List (Fin n)) :
    ∀ l : List (Fin n), IsWalk E (l ++ x :: m) → IsWalk E (l ++ [x])
  | [], _ => trivial
  | [_], h => ⟨h.1, trivial⟩
  | _ :: b :: t, h => ⟨h.1, isWalk_prefix x m (b :: t) h.2⟩

/-- The suffix of a walk from a node `x` is a walk. -/
theorem isWalk_suffix {E : Edges n} (x : Fin n) (m : List (Fin n)) :
    ∀ l : List (Fin n), IsWalk E (l ++ x :: m) → IsWalk E (x :: m)
  | [], h => h
  | [_], h => h.2
  | _ :: b :: t, h => isWalk_suffix x m (b :: t) h.2

theorem head?_append_cons (l m : List (Fin n)) (x : Fin n) :
    (l ++ x :: m).head? = (l ++ [x]).head? := by
  cases l <;> rfl

/-! ## Dominance, post-dominance, acyclicity (walk definitions) -/

/-- `Dom E entry a b`: every walk from `entry` to `b` contains `a` (`a` dominates `b`).
Nodes unreachable from `entry` are dominated by every node. -/
def Dom (E : Edges n) (entry a b : Fin n) : Prop :=
  ∀ π : List (Fin n), IsWalk E π → π.head? = some entry → π.getLast? = some b → a ∈ π

/-- `PDom E a b`: every walk from `b` to an exit (a node with no `E`-successor) contains `a`
(`a` post-dominates `b`). -/
def PDom (E : Edges n) (a b : Fin n) : Prop :=
  ∀ (π : List (Fin n)) (x : Fin n), IsWalk E π → π.head? = some b → π.getLast? = some x →
    E x = [] → a ∈ π

/-- `Acyclic E`: no walk of one or more steps returns to its start. -/
def Acyclic (E : Edges n) : Prop :=
  ∀ (x : Fin n) (mid : List (Fin n)), ¬ IsWalk E (x :: (mid ++ [x]))

/-! ## `PathVia` formulations -/

theorem walk_eq_dropLast_append {π : List (Fin n)} {b : Fin n} (h : π.getLast? = some b) :
    π = π.dropLast ++ [b] := by
  have hne : π ≠ [] := by
    intro h'; subst h'; simp at h
  have hb : π.getLast hne = b := by
    rw [List.getLast?_eq_some_getLast hne] at h; exact Option.some.inj h
  conv => lhs; rw [← List.dropLast_concat_getLast hne]
  rw [hb]

theorem dom_iff_not_pathVia (E : Edges n) (entry a b : Fin n) :
    Dom E entry a b ↔ ¬ (b ≠ a ∧ PathVia E (fun x => x != a) entry b) := by
  constructor
  · rintro hd ⟨hba, π, hw, hh, hall⟩
    have := hd (π ++ [b]) hw hh (by simp)
    rcases List.mem_append.1 this with h | h
    · have := hall a h; simp at this
    · simp at h; exact hba h.symm
  · intro hn π hw hh hl
    apply Classical.byContradiction
    intro ha
    apply hn
    have hπ := walk_eq_dropLast_append hl
    refine ⟨?_, π.dropLast, ?_, ?_, ?_⟩
    · intro hba; subst hba
      exact ha (List.mem_of_getLast? hl)
    · rw [← hπ]; exact hw
    · rw [← hπ]; exact hh
    · intro x hx
      have : x ∈ π := List.dropLast_subset _ hx
      simp only [bne_iff_ne, ne_eq]
      intro hxa; subst hxa; exact ha this

instance (E : Edges n) (entry a b : Fin n) : Decidable (Dom E entry a b) :=
  decidable_of_iff _ (dom_iff_not_pathVia E entry a b).symm

theorem pdom_iff_not_pathVia (E : Edges n) (a b : Fin n) :
    PDom E a b ↔ ¬ ∃ x : Fin n, E x = [] ∧ x ≠ a ∧ PathVia E (fun y => y != a) b x := by
  constructor
  · rintro hd ⟨x, hx, hxa, π, hw, hh, hall⟩
    have := hd (π ++ [x]) x hw hh (by simp) hx
    rcases List.mem_append.1 this with h | h
    · have := hall a h; simp at this
    · simp at h; exact hxa h.symm
  · intro hn π x hw hh hl hx
    apply Classical.byContradiction
    intro ha
    apply hn
    have hπ := walk_eq_dropLast_append hl
    refine ⟨x, hx, ?_, π.dropLast, ?_, ?_, ?_⟩
    · intro hxa; subst hxa
      exact ha (List.mem_of_getLast? hl)
    · rw [← hπ]; exact hw
    · rw [← hπ]; exact hh
    · intro y hy
      have : y ∈ π := List.dropLast_subset _ hy
      simp only [bne_iff_ne, ne_eq]
      intro hya; subst hya; exact ha this

instance (E : Edges n) (a b : Fin n) : Decidable (PDom E a b) :=
  decidable_of_iff _ (pdom_iff_not_pathVia E a b).symm

theorem acyclic_iff (E : Edges n) :
    Acyclic E ↔ ∀ x : Fin n, ∀ y ∈ E x, ¬ PathVia E (fun _ => true) y x := by
  constructor
  · rintro hac x y hy ⟨π, hw, hh, _⟩
    apply hac x π
    cases π with
    | nil => simp at hh; subst hh; exact ⟨hy, trivial⟩
    | cons c t =>
      simp at hh; subst hh
      exact ⟨hy, hw⟩
  · intro h x mid hw
    cases mid with
    | nil => exact h x x hw.1 ⟨[], trivial, rfl, by simp⟩
    | cons c t => exact h x c hw.1 ⟨c :: t, hw.2, rfl, by simp⟩

instance (E : Edges n) : Decidable (Acyclic E) :=
  decidable_of_iff _ (acyclic_iff E).symm

end Toy.TwoPhase
