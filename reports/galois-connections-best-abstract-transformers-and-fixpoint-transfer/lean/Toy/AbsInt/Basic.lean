/-
Toy.AbsInt.Basic
================

Concrete domain (predicates ordered by inclusion), order laws for an abstract
domain given only by a `≤` relation, monotonicity, strict steps, and chain
conditions.  Everything here is a definition or a small fully proved helper
lemma; the main results of the package live in the other modules.

Scope: every generic definition and theorem of the package quantifies over a
state type `σ : Type` and an abstract domain `A : Type` (universe level 0).
-/

namespace Toy.AbsInt

/-! ## Concrete domain -/

/-- The concrete domain: predicates on states `σ`, i.e. sets of states.  This
models the collecting semantics of a program, where a "concrete value" is a set
of reachable states. -/
def Pred (σ : Type) : Type := σ → Prop

/-- The inclusion order on predicates: `x ≤ y` iff every state satisfying `x`
satisfies `y`.  (Written `⊆` in the informal statements.) -/
instance instLEPred (σ : Type) : LE (Pred σ) := ⟨fun x y => ∀ s, x s → y s⟩

theorem Pred.le_def {σ : Type} (x y : Pred σ) : x ≤ y ↔ ∀ s, x s → y s := Iff.rfl

theorem Pred.le_refl {σ : Type} (x : Pred σ) : x ≤ x := fun _ h => h

theorem Pred.le_trans {σ : Type} {x y z : Pred σ} (h₁ : x ≤ y) (h₂ : y ≤ z) : x ≤ z :=
  fun s hs => h₂ s (h₁ s hs)

/-- The empty predicate (no state). -/
def Pred.empty (σ : Type) : Pred σ := fun _ => False

/-- The full predicate (every state). -/
def Pred.univ (σ : Type) : Pred σ := fun _ => True

/-- On the one-state type, inclusion is implication at the unique state. -/
theorem Pred.unit_le_iff (x y : Pred Unit) : x ≤ y ↔ (x () → y ()) :=
  ⟨fun h => h (), fun h s => by cases s; exact h⟩

/-- `if` evaluation helpers (proved). -/
theorem ite_of_pos {c : Prop} [Decidable c] {α : Sort _} {t e : α} (h : c) :
    (if c then t else e) = t := by simp [h]

theorem ite_of_neg {c : Prop} [Decidable c] {α : Sort _} {t e : α} (h : ¬ c) :
    (if c then t else e) = e := by simp [h]

/-! ## Order laws for an abstract domain

The abstract domain is a type `A` with a bare `[LE A]` relation.  Each order law
is a separate named proposition so that every theorem lists exactly the laws it
uses. -/

/-- Reflexivity of the abstract order. -/
def IsRefl (A : Type) [LE A] : Prop := ∀ a : A, a ≤ a

/-- Transitivity of the abstract order. -/
def IsTrans (A : Type) [LE A] : Prop := ∀ a b c : A, a ≤ b → b ≤ c → a ≤ c

/-- Antisymmetry of the abstract order.  No main result of this package assumes
it: all of them are stated for preorders or for even weaker relations, as recorded
in each statement. -/
def IsAntisymm (A : Type) [LE A] : Prop := ∀ a b : A, a ≤ b → b ≤ a → a = b

/-- Monotonicity of a map between two types carrying `≤` relations.  Used for
the abstraction `α`, the concretization `γ`, concrete transformers on `Pred σ`,
and abstract transformers on `A`. -/
def Monotone {X Y : Type} [LE X] [LE Y] (h : X → Y) : Prop :=
  ∀ a b, a ≤ b → h a ≤ h b

/-- A strict step `a < b`, defined from `≤` alone as `a ≤ b ∧ ¬ b ≤ a`
(the standard strict part of a preorder). -/
def StrictLt {A : Type} [LE A] (a b : A) : Prop := a ≤ b ∧ ¬ b ≤ a

instance StrictLt.instDecidable {A : Type} [LE A] [∀ a b : A, Decidable (a ≤ b)] (a b : A) :
    Decidable (StrictLt a b) :=
  inferInstanceAs (Decidable (a ≤ b ∧ ¬ b ≤ a))

/-- Ascending chain condition: there is no infinite sequence that strictly
increases at every step (`c n < c (n + 1)` for all `n`, with `<` the strict part
`StrictLt`).

Only *consecutive* steps are compared.  For a transitive relation this is the
usual ascending chain condition ("every ascending chain eventually stops
increasing strictly").  For a non-transitive relation it is weaker: an ascending
sequence can then fail to stabilize even though no two consecutive steps are both
strict (`nb_heightLE_one_ascending_not_stabilizing`), and a finite relation with a
strict cycle `a < b < c < a` violates it (`cyc3_not_acc`). -/
def ACC (A : Type) [LE A] : Prop := ¬ ∃ c : Nat → A, ∀ n, StrictLt (c n) (c (n + 1))

/-- Height at most `h`: every finite sequence `c 0 < c 1 < … < c k` of strict
steps has `k ≤ h`.  Only consecutive steps are required to be strict; for a
transitive order this is the usual notion of a strictly increasing chain with
`k + 1` elements, while for a non-transitive relation it bounds the length of
paths of consecutive strict steps.  A finite non-transitive relation need not have
any height bound (`cyc3_not_heightLE`). -/
def HeightLE (A : Type) [LE A] (h : Nat) : Prop :=
  ∀ (c : Nat → A) (k : Nat), (∀ i, i < k → StrictLt (c i) (c (i + 1))) → k ≤ h

/-- `b` is a least element. -/
def IsBot {A : Type} [LE A] (b : A) : Prop := ∀ a, b ≤ a

/-- A strict step from an element to itself is impossible, for any relation. -/
theorem StrictLt.irrefl {A : Type} [LE A] (a : A) : ¬ StrictLt a a :=
  fun h => h.2 h.1

/-- Helper (proved): a rank function that strictly increases along strict steps
and is bounded gives the ascending chain condition. -/
theorem acc_of_rank {A : Type} [LE A] (r : A → Nat) (K : Nat)
    (hr : ∀ a b, StrictLt a b → r a < r b) (hK : ∀ a, r a ≤ K) : ACC A := by
  intro ⟨c, hc⟩
  have key : ∀ n, n ≤ r (c n) := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih => have := hr _ _ (hc n); omega
  have h1 := key (K + 1)
  have h2 := hK (c (K + 1))
  omega

/-- Helper (proved): a rank function that strictly increases along strict steps
and is bounded by `K` gives height at most `K`. -/
theorem heightLE_of_rank {A : Type} [LE A] (r : A → Nat) (K : Nat)
    (hr : ∀ a b, StrictLt a b → r a < r b) (hK : ∀ a, r a ≤ K) : HeightLE A K := by
  intro c k hc
  have key : ∀ n, n ≤ k → n ≤ r (c n) := by
    intro n
    induction n with
    | zero => intro _; exact Nat.zero_le _
    | succ n ih =>
      intro hn
      have h1 := hr _ _ (hc n (by omega))
      have h2 := ih (by omega)
      omega
  have h1 := key k (Nat.le_refl _)
  have h2 := hK (c k)
  omega

end Toy.AbsInt
