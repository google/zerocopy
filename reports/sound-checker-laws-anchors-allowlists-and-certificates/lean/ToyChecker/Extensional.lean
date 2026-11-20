import ToyChecker.Anchors

/-!
# The extensionality barrier

To talk about a tool's internals at all, separate the *implementation* of a
tool (an element of an arbitrary type `I`) from its *behavior*
`run i : P → Bool`. A law on implementations is *extensional* if it respects
pointwise equality of behavior. An extensional law cannot distinguish two
implementations that accept exactly the same programs, e.g. an honest
structural checker and a lookup table that happens to accept the same set.

This is `definitional`: it is the definition of extensionality, restated.
Side facts that make its scope precise:
* every law stated directly on Boolean functions `P → Bool` is automatically
  extensional (function extensionality), so for laws on input–output
  behavior the extensionality hypothesis is free;
* intensional laws, i.e. predicates on the implementation `i : I` itself
  (here: which constructor built it; in practice source inspection or build
  provenance), can separate such implementations;
* requiring richer *output* (for example a certificate with each answer, see
  `ToyChecker.Certificates`) is not intensional: it replaces `P → Bool` by a
  richer behavior type, and the barrier applies again to that behavior. A
  lookup table that stores precomputed valid certificates has exactly the
  same certified behavior as an honest tool on the same finite set
  (`cachedCertTool_eq_boundedHonestTool`).

Scope of "extensional": this is extensionality at the level of *tools*
(two implementations give the same answer on every program text). It is not
the semantic extensionality of Rice's theorem (a property of programs that
depends only on the function a program computes); a law on tools may well
distinguish two semantically equivalent target programs.
-/

namespace Toy.Checker

universe u v

/-- `ExtensionalLaw run L`: the law `L` on implementations `I` respects
pointwise equality of behavior. Captures "the law looks only at what the tool
answers, never at how it was built". -/
def ExtensionalLaw {P : Type u} {I : Type v} (run : I → P → Bool) (L : I → Prop) : Prop :=
  ∀ i j, (∀ p, run i p = run j p) → L i → L j

/-! ## Toy implementations -/

/-- Two kinds of toy tool implementation for `evenGood`: an arithmetic
("structural") test `p < n ∧ p even`, and a lookup table. -/
inductive ToyImpl where
  /-- Arithmetic test: accept `p` iff `p < n` and `p` is even. -/
  | evenBelow (n : Nat)
  /-- Lookup table: accept exactly the listed programs. -/
  | table (entries : List Nat)
  deriving DecidableEq

/-- Behavior of a toy implementation. -/
def toyRun : ToyImpl → Nat → Bool
  | .evenBelow n, p => decide (p < n) && p % 2 == 0
  | .table l, p => decide (p ∈ l)

/-- The honest conservative implementation: arithmetic test below `10`. -/
def honestImpl : ToyImpl := .evenBelow 10

/-- A lookup table that happens to accept exactly what `honestImpl`
accepts. -/
def tableImpl : ToyImpl := .table [0, 2, 4, 6, 8]

/-- An intensional law: "the implementation is an arithmetic test, not a
table". It inspects the implementation, not its behavior. -/
def IsStructural : ToyImpl → Prop
  | .evenBelow _ => True
  | .table _ => False

/-- Examples for `toyRun`: the honest implementation accepts `4` and rejects
`10`; the table accepts `4` and rejects `5`. -/
theorem toyRun_examples :
    toyRun honestImpl 4 = true ∧ toyRun honestImpl 10 = false ∧
    toyRun tableImpl 4 = true ∧ toyRun tableImpl 5 = false := by
  decide

/-- The honest implementation and the lookup table have the same behavior. -/
theorem toyRun_honest_table_same_behavior : ∀ p, toyRun honestImpl p = toyRun tableImpl p := by
  intro p
  by_cases h : p < 10
  · have hall : ∀ q, q < 10 → toyRun honestImpl q = toyRun tableImpl q := by decide
    exact hall p h
  · simp only [toyRun, honestImpl, tableImpl]
    have h1 : decide (p < 10) = false := decide_eq_false h
    have h2 : decide (p ∈ [0, 2, 4, 6, 8]) = false := by
      apply decide_eq_false
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      omega
    rw [h1, h2]
    rfl

/-! ## Examples for `ExtensionalLaw` -/

/-- Positive example: "the behavior is sound for `evenGood`" is an
extensional law on toy implementations. -/
theorem extensionalLaw_example_sound :
    ExtensionalLaw toyRun (fun i => Sound evenGood (toyRun i)) := by
  intro i j hij hi p hp
  exact hi p ((hij p).trans hp)

/-- Negative example: the intensional law `IsStructural` is not
extensional. -/
theorem not_extensionalLaw_example_isStructural : ¬ ExtensionalLaw toyRun IsStructural := by
  intro h
  exact h honestImpl tableImpl toyRun_honest_table_same_behavior trivial

/-! ## Main statements -/

/-- R3a. An extensional law takes the same truth value on any two
implementations with the same behavior. -/
theorem extensionalLaw_iff_of_same_behavior {P : Type u} {I : Type v} {run : I → P → Bool}
    {L : I → Prop} {i j : I} (hL : ExtensionalLaw run L) (hij : ∀ p, run i p = run j p) :
    L i ↔ L j :=
  ⟨hL i j hij, hL j i (fun p => (hij p).symm)⟩

/-- R3a (part). Every law stated directly on Boolean checkers is extensional
(by function extensionality). So for laws on input–output behavior the
extensionality hypothesis of R3a is derivable, not an extra assumption. -/
theorem extensionalLaw_id_of_law {P : Type u} (L : Law P) :
    ExtensionalLaw (id : (P → Bool) → P → Bool) L := by
  intro c₁ c₂ h hc
  have : c₁ = c₂ := funext h
  subst this
  exact hc

/-- R3a (part, toy instance). No extensional law separates the specific
implementation `honestImpl` (accept `p` iff `p < 10` and `p` is even) from the
specific lookup table `tableImpl` (`[0, 2, 4, 6, 8]`), because they have the
same behavior. This concerns these two finite-acceptance implementations
only: an honest checker accepting infinitely many programs has no finite
table with the same behavior. -/
theorem extensionalLaw_cannot_separate_honestImpl_from_tableImpl {L : ToyImpl → Prop}
    (hL : ExtensionalLaw toyRun L) : L honestImpl ↔ L tableImpl :=
  extensionalLaw_iff_of_same_behavior hL toyRun_honest_table_same_behavior

/-! ## Tightness counterexamples and positive control -/

/-- R3a without `hL` (and positive control for R3a): the intensional law
`IsStructural` separates two implementations with the same behavior. -/
theorem cex_extensionalLaw_iff_needs_extensional :
    (∀ p, toyRun honestImpl p = toyRun tableImpl p) ∧
    ¬ (IsStructural honestImpl ↔ IsStructural tableImpl) := by
  refine ⟨toyRun_honest_table_same_behavior, fun h => ?_⟩
  exact h.mp trivial

/-- The law "accepts program `10`". -/
def acceptsTenImplLaw : ToyImpl → Prop := fun i => toyRun i 10 = true

/-- R3a without `hij`: an extensional law ("accepts `10`") separates two
implementations whose behaviors differ (at `10`). -/
theorem cex_extensionalLaw_iff_needs_same_behavior :
    ExtensionalLaw toyRun acceptsTenImplLaw ∧
    ¬ (acceptsTenImplLaw (.evenBelow 12) ↔ acceptsTenImplLaw honestImpl) := by
  refine ⟨fun i j hij hi => (hij 10).symm.trans hi, fun h => ?_⟩
  have := h.mp (show toyRun (.evenBelow 12) 10 = true by decide)
  simp [acceptsTenImplLaw, toyRun, honestImpl] at this

/-- Positive control for R3a: an intensional law separates the honest
implementation from the table. -/
theorem positive_control_intensional_law_separates :
    IsStructural honestImpl ∧ ¬ IsStructural tableImpl :=
  ⟨trivial, fun h => h⟩

/-! ## Non-vacuity witnesses -/

/-- R3a hypotheses hold: an extensional law, and two implementations
with the same behavior. -/
theorem nonvacuous_extensionalLaw_iff :
    ExtensionalLaw toyRun (fun i => Sound evenGood (toyRun i)) ∧
    (∀ p, toyRun honestImpl p = toyRun tableImpl p) :=
  ⟨extensionalLaw_example_sound, toyRun_honest_table_same_behavior⟩

/-- `extensionalLaw_id_of_law` instance: soundness for `evenGood`, as a law on Boolean checkers, is
extensional. -/
theorem nonvacuous_extensionalLaw_id :
    ExtensionalLaw (id : (Nat → Bool) → Nat → Bool) (Sound evenGood) :=
  extensionalLaw_id_of_law (Sound evenGood)

end Toy.Checker
