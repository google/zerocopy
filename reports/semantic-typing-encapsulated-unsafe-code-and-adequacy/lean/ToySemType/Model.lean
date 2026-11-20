import ToySemType.Semantics
import ToySemType.Typing

/-!
# The semantic (unary logical-relation) model

Types are interpreted as world-indexed predicates on closed values. A *world*
`W : Nat` is a lower bound on the heap size: "cells `0 … W-1` are known to be
allocated". Because allocation only appends, knowledge only grows, and the
function case quantifies over future (larger) worlds (Kripke monotonicity).

The model is built from a `Recipe` with three ingredients so that each
ingredient can be ablated independently:

* `refOK W l`: which addresses count as valid references in world `W`;
* `future W W'`: which worlds count as futures of `W` (function case);
* `close P W e`: how a value predicate `P` is lifted to expressions.

The standard recipe `Recipe.std` uses `l < W`, `W ≤ W'`, and `safeAndIn`
("safe, and every value reached is in `P`"). The expression interpretation is
a *safety* (partial-correctness) interpretation over all finite execution
prefixes: it does not require termination and is not step-indexed. Step
indexing is unnecessary here because types are interpreted by structural
recursion and the store holds only words (no recursive types, no higher-order
store).
-/

namespace Toy.SemType

open Expr

/-- The three ingredients of a semantic model (see module docstring). -/
structure Recipe where
  /-- `refOK W l`: address `l` is a valid reference in world `W`. -/
  refOK : Nat → Nat → Prop
  /-- `future W W'`: world `W'` is an accessible future of world `W`. -/
  future : Nat → Nat → Prop
  /-- Expression closure: lifts a world-indexed value predicate to expressions. -/
  close : (Nat → Expr → Prop) → Nat → Expr → Prop

/-- The standard expression closure: starting from any heap with at least `W`
cells, no reachable configuration is stuck, and every value reached is in `P`
at the then-current heap size. -/
def safeAndIn (P : Nat → Expr → Prop) (W : Nat) (e : Expr) : Prop :=
  ∀ h : Heap, W ≤ h.length → ∀ e' h', Reaches (e, h) (e', h') →
    ¬ Stuck (e', h') ∧ (e'.isValue = true → P h'.length e')

/-- Value interpretation `V R τ W v` of type `τ` in world `W`.

* `int`: word constants.
* `ref`: references `loc l` with `R.refOK W l`.
* `arrow σ τ`: closed abstractions `lam b` such that in every future world `W'`
  and for every argument `v` in `V R σ W'`, the body instance `b[v/0]` is in the
  expression closure of `V R τ` at `W'`.

The closedness condition `b.closedAt 1` keeps all interpreted values closed,
so that the no-shifting substitution of `Expr.substAllAt` is capture-free. It is
a syntactic side condition, not an extensional one: an abstraction whose body
mentions a free variable only in dead code (e.g. `λ x. ifz 0 x y`) is excluded
even if every call to it is safe (`V_std_rejects_open_dead_lam`). -/
def V (R : Recipe) : Ty → Nat → Expr → Prop
  | .int, _, e => ∃ n, e = .num n
  | .ref, W, e => ∃ l, e = .loc l ∧ R.refOK W l
  | .arrow σ τ, W, e => ∃ b, e = .lam b ∧ b.closedAt 1 = true ∧
      ∀ W', R.future W W' → ∀ v, V R σ W' v → R.close (V R τ) W' (substAt 0 v b)

/-- Expression interpretation: the recipe's closure of the value interpretation. -/
def E (R : Recipe) (τ : Ty) : Nat → Expr → Prop := R.close (V R τ)

/-- Context interpretation: `γ` has one value per context entry, each in the
value interpretation of its type at world `W`. -/
def G (R : Recipe) : List Ty → Nat → List Expr → Prop
  | [], _, [] => True
  | τ :: Γ, W, v :: γ => V R τ W v ∧ G R Γ W γ
  | _, _, _ => False

/-- Semantic typing `Γ ⊨ e : τ`: for every world and every closing substitution
in the context interpretation, the closed instance is in the expression
interpretation. This is a semantic, not syntactic, judgment: it can hold for
expressions that use `cast`. -/
def SemTyped (R : Recipe) (Γ : List Ty) (e : Expr) (τ : Ty) : Prop :=
  ∀ W γ, G R Γ W γ → E R τ W (substAll γ e)

/-- The standard recipe: valid references are allocated addresses (`l < W`),
future worlds are larger (`W ≤ W'`), and the closure is `safeAndIn`. -/
def Recipe.std : Recipe where
  refOK W l := l < W
  future W W' := W ≤ W'
  close := safeAndIn

/-! ## Ablated ("shortcut") recipes -/

/-- Closure that keeps only the safety part of `safeAndIn` (ignores `P`). -/
def safeOnly (_P : Nat → Expr → Prop) (W : Nat) (e : Expr) : Prop :=
  ∀ h : Heap, W ≤ h.length → ∀ d, Reaches (e, h) d → ¬ Stuck d

/-- Closure that keeps only the value part of `safeAndIn` (ignores stuckness). -/
def valuesIn (P : Nat → Expr → Prop) (W : Nat) (e : Expr) : Prop :=
  ∀ h : Heap, W ≤ h.length → ∀ e' h', Reaches (e, h) (e', h') →
    e'.isValue = true → P h'.length e'

/-- Shortcut: semantic typing of expressions is just safety. -/
def Recipe.safetyOnly : Recipe := { Recipe.std with close := safeOnly }

/-- Shortcut: semantic typing of expressions only constrains the values reached. -/
def Recipe.valuesOnly : Recipe := { Recipe.std with close := valuesIn }

/-- Shortcut: no Kripke structure; the only future of `W` is `W` itself. -/
def Recipe.nonKripke : Recipe := { Recipe.std with future := fun W W' => W' = W }

/-- Shortcut: every address counts as a valid reference. -/
def Recipe.anyLoc : Recipe := { Recipe.std with refOK := fun _ _ => True }

/-- Shortcut: types interpreted by syntactic typability of values under a store
typing. In world `W` (cells `0 … W-1` allocated), a value of type `τ` is a
value `v` with `HasTypeStore W [] v τ`; for `int` and `ref` this is spelled out
as a word constant and an allocated reference `loc l` with `l < W`. This is the
value interpretation implicit in a purely syntactic (progress-and-preservation)
account with store typing: it admits runtime closures that capture allocated
references (e.g. `λ _. read (loc 0)` in world 1), but, like `HasTypeStore`, it
admits no value containing `cast`. -/
def SynVal : Ty → Nat → Expr → Prop
  | .int, _, e => ∃ n, e = .num n
  | .ref, W, e => ∃ l, e = .loc l ∧ l < W
  | .arrow σ τ, W, e => e.isValue = true ∧ HasTypeStore W [] e (.arrow σ τ)

/-! ## Named properties of recipes -/

/-- The recipe's expression closure enforces that every value reached is in the
value predicate (it implies `valuesIn`). Holds for `safeAndIn` (hence for
`Recipe.std`, `Recipe.anyLoc`, `Recipe.nonKripke`); fails for `safeOnly`. -/
def Recipe.ClosureEnforcesValues (R : Recipe) : Prop :=
  ∀ (P : Nat → Expr → Prop) (W : Nat) (e : Expr), R.close P W e → valuesIn P W e

/-- Some world has some address that is not a valid reference. Holds for
`Recipe.std` (`l < W` fails for `l = W`); fails for `Recipe.anyLoc`. -/
def Recipe.HasInvalidRef (R : Recipe) : Prop := ∃ W l, ¬ R.refOK W l

/-! ## Basic facts about the model -/

theorem V_isValue {R : Recipe} {τ : Ty} {W : Nat} {v : Expr} (h : V R τ W v) :
    v.isValue = true := by
  cases τ with
  | int => obtain ⟨n, rfl⟩ := h; rfl
  | ref => obtain ⟨l, rfl, _⟩ := h; rfl
  | arrow σ τ => obtain ⟨b, rfl, _⟩ := h; rfl

theorem V_closed {R : Recipe} {τ : Ty} {W : Nat} {v : Expr} (h : V R τ W v) :
    v.closedAt 0 = true := by
  cases τ with
  | int => obtain ⟨n, rfl⟩ := h; rfl
  | ref => obtain ⟨l, rfl, _⟩ := h; rfl
  | arrow σ τ => obtain ⟨b, rfl, hb, _⟩ := h; simpa [Expr.closedAt] using hb

theorem G_nil {R : Recipe} {W : Nat} {γ : List Expr} : G R [] W γ ↔ γ = [] := by
  cases γ <;> simp [G]

theorem G_singleton {R : Recipe} {τ : Ty} {W : Nat} {γ : List Expr} :
    G R [τ] W γ ↔ ∃ v, γ = [v] ∧ V R τ W v := by
  match γ with
  | [] => simp [G]
  | [v] => simp [G]
  | _ :: _ :: _ => simp [G]

/-- Closed semantic typing unfolds to the expression interpretation at every world. -/
theorem semTyped_nil_iff {R : Recipe} {e : Expr} {τ : Ty} :
    SemTyped R [] e τ ↔ ∀ W, E R τ W e := by
  constructor
  · intro h W
    have := h W [] (G_nil.mpr rfl)
    simpa [Expr.substAll_nil] using this
  · intro h W γ hγ
    rw [G_nil.mp hγ, Expr.substAll_nil]
    exact h W

/-- Values in the syntactic-typability interpretation contain no `cast`. -/
theorem SynVal.castFree {τ : Ty} {W : Nat} {v : Expr} (h : SynVal τ W v) :
    v.castFree = true := by
  cases τ with
  | int => obtain ⟨n, rfl⟩ := h; rfl
  | ref => obtain ⟨l, rfl, _⟩ := h; rfl
  | arrow σ τ => exact h.2.castFree

/-- `safeAndIn` enforces values (it implies `valuesIn`). -/
theorem valuesIn_of_safeAndIn {P : Nat → Expr → Prop} {W : Nat} {e : Expr}
    (h : safeAndIn P W e) : valuesIn P W e :=
  fun hh hW e' h' hr => (h hh hW e' h' hr).2

end Toy.SemType
