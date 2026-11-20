/-!
# Toy model of yes/no analysis tools

Programs are the elements of an arbitrary type `P`. The semantic property a
framework cares about is a predicate `good : P → Prop` (for example "never
dereferences a dangling pointer", "type-safe", "terminates"). A *checker* is a
Boolean function `P → Bool`, read as the input–output behavior of a third-party
analysis tool that answers *accept* (`true`) or *reject* (`false`) for each
program. A *law* is any predicate on checkers; a framework would admit only
tools whose behavior satisfies its laws.

This file fixes the vocabulary used by every other module: soundness, relative
completeness, the pointwise order, the reject-all / accept-all / pointwise-or /
allowlist checkers, the classical oracle of a predicate, and a running toy
instance (`evenGood` on `Nat`). Every definition is accompanied by proved
positive and negative examples.

Modeling gaps (kept explicit):
* A checker here is a mathematical function. Running time, nontermination,
  crashes, nondeterminism, and the tool's source code are not represented.
* "Decidable" in Lean's logic is not "computable": every predicate has a
  (noncomputable) classical decision procedure, see `classicalOracle`.
* Polarity: `true` means "certified good" (a verifier or type checker that
  accepts only safe programs). A bug finder that promises no false alarms
  has the opposite polarity: its guarantee is `c p = false → ¬ good p`
  (completeness in the sense of `CompleteOn good (fun _ => True)`), and its
  degenerate tool is `acceptAll` (report nothing), not `rejectAll`. Results
  about `Sound` transfer to such tools only after swapping the roles of
  `true`/`false` and of `good`/`¬ good`.
-/

namespace Toy.Checker

universe u v w

/-! ## Core notions -/

/-- `Sound good c`: every program the checker `c` accepts satisfies `good`.
Captures "the tool never accepts a bad program" for tools whose `true`
answer certifies goodness. It says nothing about which good programs are
accepted. (For bug finders, whose reported alarms must be real, the
corresponding guarantee is the dual one; see the module comment.) -/
def Sound {P : Type u} (good : P → Prop) (c : P → Bool) : Prop :=
  ∀ p, c p = true → good p

/-- `CompleteOn good F c`: the checker `c` accepts every good program that lies
in the fragment `F`. Captures *relative* completeness: good programs outside
`F` may be rejected. -/
def CompleteOn {P : Type u} (good F : P → Prop) (c : P → Bool) : Prop :=
  ∀ p, good p → F p → c p = true

/-- Pointwise order on checkers: `CheckerLE c₁ c₂` means `c₁` accepts nothing
that `c₂` rejects (`c₁` is at least as conservative as `c₂`). -/
def CheckerLE {P : Type u} (c₁ c₂ : P → Bool) : Prop :=
  ∀ p, c₁ p = true → c₂ p = true

/-- The degenerate checker that rejects every program. It is the bottom of the
pointwise order and is sound for every `good`. -/
def rejectAll {P : Type u} : P → Bool := fun _ => false

/-- The degenerate checker that accepts every program (top of the order). -/
def acceptAll {P : Type u} : P → Bool := fun _ => true

/-- Pointwise disjunction: accept iff at least one of the two checkers
accepts. Models running two tools and accepting if either accepts. -/
def orChecker {P : Type u} (c₁ c₂ : P → Bool) : P → Bool :=
  fun p => c₁ p || c₂ p

/-- The allowlist (lookup-table) checker of a finite list `A`: accept exactly
the members of `A`. Models a tool that ignores program structure and consults
a fixed table. -/
def allowlist {P : Type u} [DecidableEq P] (A : List P) : P → Bool :=
  fun p => decide (p ∈ A)

/-- A law is an arbitrary predicate on checkers (on their input–output
behavior, since a checker *is* its input–output behavior in this model). -/
abbrev Law (P : Type u) : Type u := (P → Bool) → Prop

/-- The classical oracle of a predicate `Q`: the Boolean function returning
`true` exactly on the programs satisfying `Q`. It exists for every `Q` by the
law of excluded middle and is in general noncomputable; it is the reason that
"there is a Boolean checker with property X" is a much weaker statement in
this model than "there is an implementable tool with property X". -/
noncomputable def classicalOracle {P : Type u} (Q : P → Prop) : P → Bool :=
  fun p => @decide (Q p) (Classical.propDecidable (Q p))

/-- The classical oracle agrees with `decide` for any decidability instance,
so for decidable predicates nothing is lost by using `classicalOracle`. -/
theorem classicalOracle_eq_decide {P : Type u} (Q : P → Prop) [DecidablePred Q] :
    classicalOracle Q = fun p => decide (Q p) := by
  funext p
  unfold classicalOracle
  apply decide_eq_decide.mpr
  exact Iff.rfl

/-- Defining property of the classical oracle. -/
theorem classicalOracle_eq_true_iff {P : Type u} (Q : P → Prop) (p : P) :
    classicalOracle Q p = true ↔ Q p := by
  unfold classicalOracle
  exact @decide_eq_true_iff (Q p) (Classical.propDecidable (Q p))

/-! ## Running toy instance

Programs are natural numbers; the "good" ones are the even numbers. This is a
stand-in for any semantic property; nothing below depends on parity except the
concrete examples and counterexamples. -/

/-- Toy semantic property: a program (a natural number) is good iff it is
even. -/
def evenGood : Nat → Prop := fun n => n % 2 = 0

instance : DecidablePred evenGood := fun n => inferInstanceAs (Decidable (n % 2 = 0))

/-- A conservative honest checker for `evenGood`: accepts exactly the even
numbers below `10`. -/
def evenBelowTen : Nat → Bool := fun n => decide (n < 10) && n % 2 == 0

/-- An exact checker for `evenGood`. -/
def evenExact : Nat → Bool := fun n => n % 2 == 0

/-! ## Examples for `Sound` -/

/-- Positive example: the exact parity checker is sound for `evenGood`. -/
theorem sound_example_evenExact : Sound evenGood evenExact := by
  intro p h
  simpa [evenExact, evenGood] using h

/-- Positive example: the conservative checker `evenBelowTen` is sound. -/
theorem sound_example_evenBelowTen : Sound evenGood evenBelowTen := by
  intro p h
  simp [evenBelowTen] at h
  exact h.2

/-- Negative example: accept-all is not sound for `evenGood` (it accepts `1`). -/
theorem not_sound_example_acceptAll : ¬ Sound evenGood acceptAll := by
  intro h
  have h1 := h 1 rfl
  simp [evenGood] at h1

/-- Negative example: a checker that accepts a single odd program is not
sound. -/
theorem not_sound_example_acceptsThree : ¬ Sound evenGood (fun n => n == 3) := by
  intro h
  have h3 := h 3 rfl
  simp [evenGood] at h3

/-! ## Examples for `CompleteOn` -/

/-- Positive example: `evenBelowTen` is complete on the fragment `n < 10`. -/
theorem completeOn_example_evenBelowTen :
    CompleteOn evenGood (fun n => n < 10) evenBelowTen := by
  intro p hg hF
  simp [evenBelowTen, evenGood] at *
  exact ⟨hF, hg⟩

/-- Negative example: `evenBelowTen` is not complete on all programs (it
rejects the good program `10`). -/
theorem not_completeOn_example_evenBelowTen :
    ¬ CompleteOn evenGood (fun _ => True) evenBelowTen := by
  intro h
  have h10 := h 10 rfl trivial
  simp [evenBelowTen] at h10

/-- Negative example: reject-all is not complete on any fragment containing a
good program, e.g. `n < 10`. -/
theorem not_completeOn_example_rejectAll :
    ¬ CompleteOn evenGood (fun n => n < 10) rejectAll := by
  intro h
  have h0 := h 0 rfl (by decide)
  simp [rejectAll] at h0

/-! ## Examples for `CheckerLE` -/

/-- Positive example: reject-all is below every checker. -/
theorem checkerLE_example_rejectAll {P : Type u} (c : P → Bool) : CheckerLE rejectAll c := by
  intro p h
  simp [rejectAll] at h

/-- Positive example: the conservative checker is below the exact one. -/
theorem checkerLE_example_evenBelowTen_evenExact : CheckerLE evenBelowTen evenExact := by
  intro p h
  simp [evenBelowTen, evenExact] at *
  exact h.2

/-- Negative example: the exact checker is not below the conservative one
(they differ at `10`). -/
theorem not_checkerLE_example_evenExact_evenBelowTen : ¬ CheckerLE evenExact evenBelowTen := by
  intro h
  have h10 := h 10 rfl
  simp [evenBelowTen] at h10

/-- Negative example: accept-all is not below reject-all on an inhabited type. -/
theorem not_checkerLE_example_acceptAll_rejectAll :
    ¬ CheckerLE (acceptAll : Nat → Bool) rejectAll := by
  intro h
  have h0 := h 0 rfl
  simp [rejectAll] at h0

/-- Negative examples for `evenExact`: it rejects the odd program `1`, and it
is not sound for the stronger predicate "is `0`" (it accepts `2`). -/
theorem not_evenExact_examples :
    evenExact 1 = false ∧ ¬ Sound (fun n => n = 0) evenExact := by
  refine ⟨rfl, fun h => ?_⟩
  have h2 := h 2 rfl
  exact Nat.noConfusion h2

/-! ## Examples for the named checkers -/

/-- `rejectAll`, `acceptAll`, `orChecker`, `allowlist` evaluate as intended
(positive instances). -/
theorem namedCheckers_examples :
    (rejectAll : Nat → Bool) 4 = false ∧ (acceptAll : Nat → Bool) 3 = true ∧
    orChecker (fun n => n == 0) (fun n => n == 2) 2 = true ∧
    allowlist [0, 2] 2 = true := by
  decide

/-- Negative instances: `orChecker` rejects what both components reject, and
an allowlist rejects non-members. -/
theorem namedCheckers_negative_examples :
    orChecker (fun n => n == 0) (fun n => n == 2) 4 = false ∧
    allowlist [0, 2] 4 = false := by
  decide

/-- Example for `classicalOracle`: the classical oracle of `evenGood` accepts
`4` and rejects `3`. -/
theorem classicalOracle_examples :
    classicalOracle evenGood 4 = true ∧ classicalOracle evenGood 3 = false := by
  constructor
  · exact (classicalOracle_eq_true_iff evenGood 4).mpr rfl
  · cases h : classicalOracle evenGood 3 with
    | false => rfl
    | true =>
      have := (classicalOracle_eq_true_iff evenGood 3).mp h
      simp [evenGood] at this

/-! ## Arithmetic helper -/

/-- Every member of a list of naturals is at most the list's sum. -/
theorem le_sum_of_mem_nat : ∀ {A : List Nat} {a : Nat}, a ∈ A → a ≤ A.sum
  | [], _, h => by simp at h
  | b :: l, a, h => by
    rw [List.sum_cons]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := le_sum_of_mem_nat h
      omega

end Toy.Checker
