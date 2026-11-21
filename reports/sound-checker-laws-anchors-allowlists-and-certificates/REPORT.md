# Sound checker laws: anchors, allowlists, extensional laws, certificates, relabeling, and relative completeness

## Summary

This package is a set of 20 precise reference points about *laws* that a verification framework might impose on third-party yes/no analysis tools, stated and kernel-checked in Lean 4 for a deliberately small model: programs are elements of an arbitrary type `P`, the semantic property of interest is a predicate `good : P → Prop`, a tool is identified with its input-output behavior `c : P → Bool` (`true` = accept = certified good), and a law is any predicate on such checkers. Almost all results are elementary: 10 are labeled `definitional` and 10 `shallow`, none `substantive`. Their value is in fixing exactly how strong each informal remark is (for example "soundness cannot rule out the do-nothing tool", "a lookup table passes any finite test", "certificates move trust to the verifier"), with every hypothesis shown necessary by a proved counterexample, except four `[DecidableEq P]` instance arguments that only serve to define allowlists and lookup tables as Boolean functions (marked `harmless`), and except that for R5c's bijective `Relabeling` argument only the left-inverse half (`left_inv`, injectivity) is used and shown necessary, while the right-inverse half (`right_inv`, surjectivity) is unused; and with every card shown non-vacuous by a proved instance. Nothing here is a deep theorem, and none of it is a statement about any real tool.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

One sentence per result (identifiers refer to the Lean definitions quoted under Findings):

- **R1a** (characterization, definitional). For every predicate `good`, a checker is sound iff it is pointwise below the classical (in general noncomputable) oracle of `good`; hence the sound checkers contain `rejectAll`, are closed downward in the pointwise order, and are closed under the pointwise `or` of two checkers that are sound for the same `good`.
- **R1e** (impossibility, definitional). Any law that every sound checker satisfies is also satisfied by `rejectAll`, so a law implied by soundness alone cannot exclude the do-nothing tool.
- **R2a** (characterization, definitional). The anchored law (sound, and accepts every program of a finite anchor list `A`) excludes `rejectAll` iff `A` is nonempty, whether or not the anchors are good; if every anchor is good it admits the allowlist of `A`.
- **R2c** (characterization, shallow). If every anchor is good, the programs that every checker admitted by the anchored law must accept are exactly the anchors, and those it must reject are exactly the bad programs; for each good non-anchor `p` the allowlists of `A` and of `p :: A` are both admitted and disagree on `p`.
- **R2f** (impossibility, shallow). If some checker `c` passes a finite test suite `T`, the lookup table of `T` passes `T` and is pointwise below `c`, and if `c` is sound the table is sound; so no law of the form "sound and passes `T`" admits a checker while excluding the lookup table of `T`.
- **R3a** (impossibility, definitional). If a law on tool implementations respects equality of behavior (is extensional) and two implementations give the same answer on every program, the law holds of both or of neither; every law stated directly on Boolean checkers is extensional, and in the toy model no extensional law separates the arithmetic implementation `honestImpl` from the lookup table `tableImpl`.
- **R4a** (theorem, definitional). In one-sided certification (accept iff the tool outputs a certificate that a fixed verifier `V` accepts), if `V` is sound then the checker induced by every tool is sound.
- **R4b** (characterization, shallow). In one-sided certification, every tool induces a sound checker iff `V` is sound; explicitly, a certificate that `V` accepts for a bad program makes the constant tool that outputs it unsound.
- **R4c** (characterization, definitional). In one-sided certification, the induced checker is complete on a fragment `F` iff for every good program of `F` the tool outputs a certificate that `V` accepts; in particular this requires `V` to accept some certificate for each good program of `F`.
- **R4d** (counterexample, definitional). In one-sided certification, a verifier that is sound and complete does not make the induced checker complete: with the sound and complete toy verifier `halfV`, the tool that never outputs a certificate induces an incomplete checker.
- **R4e** (characterization, shallow). A Boolean checker is induced by some one-sided certifying tool for `V` iff it is sound for the predicate "has a certificate that `V` accepts".
- **R4f** (theorem, shallow). In two-sided certification (a verdict plus a certificate or a refutation), if the certificate verifier is sound for `good`, the refutation verifier is sound for `¬ good`, and every answer of the tool on a fragment `F` carries evidence that its verifier accepts, then the induced checker is sound everywhere and complete on `F`.
- **R5b** (impossibility, shallow). If `good` is invariant under a surjective map `π` of programs (for example the forward map of a bijective relabeling), a checker `c` is sound iff `c ∘ π` is sound.
- **R5c** (impossibility, shallow). If a law `L` on checkers is invariant under precomposition with a map `π`, every answer that `L` forces at a program `p` is also forced at `π p`; for a bijective relabeling `σ`, `L` forces answer `b` at `σ p` iff it forces `b` at `p`.
- **R6a** (characterization, definitional). A checker is sound and complete on a fragment `F` iff it lies pointwise between the classical oracles of `F ∧ good` and of `good`; the lower end is itself a satisfier, so in this model the law is always satisfiable, in general by a noncomputable function.
- **R6c** (characterization, shallow). A checker is sound and complete on `F` iff the same checker is sound and decides `good` on `F`; so for any class `K` of admissible checkers the law has a satisfier in `K` iff some member of `K` is sound and decides `good` on `F` (for `F` = all programs: iff some member of `K` decides `good`), and if `K` is closed under pointwise `&&` and contains a decider of `F`, the soundness requirement can be dropped from that criterion.
- **R6e** (characterization, shallow). The law "sound and complete on `F`" excludes `rejectAll` iff `F` contains at least one good program.
- **R6f** (characterization, definitional). The allowlist of `A` is sound and complete on `F` iff every member of `A` is good and every good program of `F` is in `A`.
- **R6g** (impossibility, shallow). In the toy instance, no allowlist is sound and complete for `evenGood` on all programs, although the law is satisfiable (by `evenExact`).
- **R6h** (counterexample, definitional). "Some member of `K` decides `good` on `F`" does not imply that the law "sound and complete on `F`" has a satisfier in `K`: for `K = {acceptAll}` and `good = F = (· = 0)`, `acceptAll` decides `good` on `F` but is unsound off `F`.

What these results do *not* establish is listed first under Boundaries; in particular: extensional (behavior-only) laws cannot tell an honest tool from a behaviorally identical lookup table (R3a); for anchors or a finite test suite fixed before the tool is chosen, if the law "sound and accepts every anchor" or "sound and passes the suite" admits some checker, it also admits the allowlist of the anchors or the lookup table of the suite (R2a, R2f), and suites chosen after the tool, as in held-out or randomized testing, are not modeled; one-sided certificates transfer soundness from the verifier to every tool but not completeness, and completeness on a fragment is forced only under two-sided certification with checked answers required on that fragment (R4f); and "there exists a checker" in this model never means "there exists an implementable tool".

## Applicability

**Model fidelity: toy model.** The definitions are a toy model, not production definitions of any tool or framework. They are meant to capture the admission question for analysis tools whose positive answer certifies a property (verifiers, type checkers, translation validators, certifying tools): which requirements on a tool's observable answers (soundness, anchors, conformance suites, certificates, invariance under renaming, completeness on a fragment) exclude degenerate tools, and which cannot. The correspondence to real systems is a modeling bridge, recorded separately for each result under Findings as `Basis: derived (modeling bridge)`; the theorems themselves say nothing about real tools.

Known gaps of the model, which apply to every result:

- A checker is a total mathematical function `P → Bool`. Running time, nontermination, crashes, nondeterminism, resource limits, and the tool's source code are not represented; a real tool fits the model only after deciding how such outcomes are read (typically as "reject").
- Lean's logic is classical: every predicate has a (noncomputable) Boolean oracle (`classicalOracle`). "There is a Boolean checker with property X" is therefore much weaker than "there is an implementable tool with property X". Computability is not defined; where implementability matters (R6c) it is represented by an abstract class `K` of admissible checkers.
- Polarity: `Sound` models tools whose `true` answer certifies goodness. Bug finders that promise no false alarms have the dual guarantee (`c p = false → ¬ good p`) and the dual degenerate tool (`acceptAll`, report nothing); no result is stated for that polarity.
- The running toy instance is parity on `Nat` (`evenGood n := n % 2 = 0`); results stated for it (R4d, R6g, R6h, the relational law `ClosedUnderDoubling`) are illustrations, not general theorems.
- Programs are opaque elements of `P`; relabeling (R5) is modeled by maps `P → P`, and whether a concrete renaming of a concrete program representation is such a map, and preserves `good`, is outside the model.
- Certification (R4) models only *what* a tool outputs (a certificate, or a verdict with evidence) and that a fixed trusted verifier checks it against the original program; the cost of producing or checking evidence is not modeled.

**Toolchain.** Lean `leanprover/lean4` `v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`), core library only. **No Mathlib**, no `Std` import, no Lake dependencies (`lakefile.toml` declares a single `[[lean_lib]]` named `ToyChecker` and no `[[require]]`). All theorems live in namespace `Toy.Checker`.

**Relation of the subjects.** The Lean toolchain release is the proof checker of every theorem. The papers, books, and the Mathlib 4 revision listed in `REPORT.json` are prior art (Mathlib is not a dependency of this package): each card says what a source contains and how (if at all) it corresponds to the card; none of those systems or formalisms was re-examined or formalized here, and every stated correspondence is a reading, not a theorem.

**Source layout.** `lean/ToyChecker/Basic.lean` (vocabulary, toy instance), `DownSet.lean` (R1a, R1e), `Anchors.lean` (R2a, R2c, R2f, the relational law), `Extensional.lean` (R3a), `Certificates.lean` (R4a-R4f), `Relabel.lean` (R5b, R5c), `RelativeCompleteness.lean` (R6a, R6c, R6e-R6h). Card ids are stable labels. Gaps in the numbering are statements merged into other cards, with one exception: the gap at R5a is the lemma `invariantUnder_cannot_separate` in `Relabel.lean`, which is kept as a supporting lemma rather than a card because it is the definition of `InvariantUnder` read at one point (see Boundaries, Disproved or dropped statements).

## Findings

Every theorem named in this section is checked by the Lean kernel (`Basis: execution (Lean kernel check)`), with axioms and hashes recorded under Evidence. Claims about real systems are separate and labeled `Basis: derived (modeling bridge)`.

### Core definitions (quoted from the Lean sources)

Quoted verbatim from `lean/ToyChecker/*.lean` with doc comments omitted; universe variables `u`, `v` are declared in each module.

```lean
def Sound {P : Type u} (good : P → Prop) (c : P → Bool) : Prop :=
  ∀ p, c p = true → good p

def CompleteOn {P : Type u} (good F : P → Prop) (c : P → Bool) : Prop :=
  ∀ p, good p → F p → c p = true

def CheckerLE {P : Type u} (c₁ c₂ : P → Bool) : Prop :=
  ∀ p, c₁ p = true → c₂ p = true

def rejectAll {P : Type u} : P → Bool := fun _ => false

def acceptAll {P : Type u} : P → Bool := fun _ => true

def orChecker {P : Type u} (c₁ c₂ : P → Bool) : P → Bool :=
  fun p => c₁ p || c₂ p

def allowlist {P : Type u} [DecidableEq P] (A : List P) : P → Bool :=
  fun p => decide (p ∈ A)

abbrev Law (P : Type u) : Type u := (P → Bool) → Prop

noncomputable def classicalOracle {P : Type u} (Q : P → Prop) : P → Bool :=
  fun p => @decide (Q p) (Classical.propDecidable (Q p))

def AnchoredSound {P : Type u} (good : P → Prop) (A : List P) (c : P → Bool) : Prop :=
  Sound good c ∧ ∀ a ∈ A, c a = true

abbrev TestSuite (P : Type u) : Type u := List (P × Bool)

def Passes {P : Type u} (c : P → Bool) (T : TestSuite P) : Prop :=
  ∀ q ∈ T, c q.1 = q.2

def tableChecker {P : Type u} [DecidableEq P] (T : TestSuite P) : P → Bool :=
  fun p => decide ((p, true) ∈ T)

def ClosedUnderDoubling (c : Nat → Bool) : Prop :=
  ∀ p, c p = true → c (2 * p) = true

def ExtensionalLaw {P : Type u} {I : Type v} (run : I → P → Bool) (L : I → Prop) : Prop :=
  ∀ i j, (∀ p, run i p = run j p) → L i → L j

def VerifierSound {P : Type u} {W : Type v} (good : P → Prop) (V : P → W → Bool) : Prop :=
  ∀ p w, V p w = true → good p

def VerifierComplete {P : Type u} {W : Type v} (good : P → Prop) (V : P → W → Bool) : Prop :=
  ∀ p, good p → ∃ w, V p w = true

def certChecker {P : Type u} {W : Type v} (V : P → W → Bool) (t : P → Option W) : P → Bool :=
  fun p =>
    match t p with
    | some w => V p w
    | none => false

def TwoSidedVerifiedOn {P : Type u} {W : Type v} (Vpos Vneg : P → W → Bool) (F : P → Prop)
    (t : P → Bool × W) : Prop :=
  ∀ p, F p → ((t p).1 = true → Vpos p (t p).2 = true) ∧ ((t p).1 = false → Vneg p (t p).2 = true)

def twoSidedChecker {P : Type u} {W : Type v} (Vpos : P → W → Bool) (t : P → Bool × W) :
    P → Bool :=
  fun p => (t p).1 && Vpos p (t p).2

def InvariantUnder {S : Type u} (π : S → S) (Q : S → Prop) : Prop :=
  ∀ s, Q (π s) ↔ Q s

structure Relabeling (α : Type u) where
  toFun : α → α
  invFun : α → α
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ a, toFun (invFun a) = a

def SoundCompleteOn {P : Type u} (good F : P → Prop) (c : P → Bool) : Prop :=
  Sound good c ∧ CompleteOn good F c

def AndClosed {P : Type u} (K : (P → Bool) → Prop) : Prop :=
  ∀ c₁ c₂, K c₁ → K c₂ → K (fun p => c₁ p && c₂ p)

def DecidedIn {P : Type u} (K : (P → Bool) → Prop) (F : P → Prop) : Prop :=
  ∃ d, K d ∧ ∀ p, d p = true ↔ F p
```

Every core definition has proved positive and negative examples in the sources (for example `sound_example_evenExact` / `not_sound_example_acceptAll`, `anchoredSound_example_evenExact` / `not_anchoredSound_example_rejectAll`, `twoSidedVerifiedOn_example_honest` / `not_twoSidedVerifiedOn_example_silent`, `not_relabeling_example_const`, `andClosed_decidedIn_example_all` / `not_andClosed_example_belowTwo_zeroOrLarge`). `classicalOracle_eq_true_iff : classicalOracle Q p = true ↔ Q p` and `classicalOracle_eq_decide : classicalOracle Q = fun p => decide (Q p)` (for decidable `Q`) state what the oracle is.

### Toy instance and named examples

```lean
def evenGood : Nat → Prop := fun n => n % 2 = 0

def evenBelowTen : Nat → Bool := fun n => decide (n < 10) && n % 2 == 0

def evenExact : Nat → Bool := fun n => n % 2 == 0

def acceptsZeroLaw : Law Nat := fun c => c 0 = true

def fourOrTwo : Nat → Bool := fun n => n % 4 == 0 || n == 2

inductive ToyImpl where
  | evenBelow (n : Nat)
  | table (entries : List Nat)
  deriving DecidableEq

def toyRun : ToyImpl → Nat → Bool
  | .evenBelow n, p => decide (p < n) && p % 2 == 0
  | .table l, p => decide (p ∈ l)

def honestImpl : ToyImpl := .evenBelow 10

def tableImpl : ToyImpl := .table [0, 2, 4, 6, 8]

def IsStructural : ToyImpl → Prop
  | .evenBelow _ => True
  | .table _ => False

def acceptsTenImplLaw : ToyImpl → Prop := fun i => toyRun i 10 = true

def halfV : Nat → Nat → Bool := fun p w => w + w == p

def trustAllV : Nat → Unit → Bool := fun _ _ => true

def rejectAllV : Nat → Unit → Bool := fun _ _ => false

def honestTool : Nat → Option Nat := fun p => if p % 2 = 0 then some (p / 2) else none

def silentTool : Nat → Option Nat := fun _ => none

def lyingTool : Nat → Option Nat := fun _ => some 7

def cachedCertTool : Nat → Option Nat :=
  fun p => if p ∈ [0, 2, 4, 6, 8] then some (p / 2) else none

def boundedHonestTool : Nat → Option Nat :=
  fun p => if p < 10 ∧ p % 2 = 0 then some (p / 2) else none

def oddV : Nat → Nat → Bool := fun p w => w + w + 1 == p

def honestTwoSidedTool : Nat → Bool × Nat := fun p => (p % 2 == 0, p / 2)

def silentTwoSidedTool : Nat → Bool × Nat := fun _ => (false, 0)

def relabelList {α : Type u} (σ : Relabeling α) : List α → List α :=
  List.map σ.toFun

def swap02Fun : Nat → Nat := fun n => if n = 0 then 2 else if n = 2 then 0 else n

def swap01Fun : Nat → Nat := fun n => if n = 0 then 1 else if n = 1 then 0 else n

def swap02 : Relabeling Nat :=
  ⟨swap02Fun, swap02Fun, swap02Fun_swap02Fun, swap02Fun_swap02Fun⟩

def belowTwo : Nat → Bool := fun n => decide (n < 2)

def zeroOrLarge : Nat → Bool := fun n => decide (n = 0 ∨ 2 ≤ n)
```

### R1a. The set of sound checkers is the down-set below the classical oracle

Kind: characterization. Tier: **T0** (Textbook facts about yes/no analyzers (always-false is trivially sound) and elementary order facts (subsets of the good programs form a down-set closed under union), restated for Boolean checkers.) Depth: **definitional**. Module: `lean/ToyChecker/DownSet.lean`.

**Plain claim.** For a fixed semantic predicate good, a checker is sound iff it is pointwise below the classical oracle of good (the possibly noncomputable Boolean function that is true exactly on good programs); hence the set of sound checkers contains rejectAll, is downward closed in the pointwise order, and is closed under the pointwise or of two checkers that are sound for the same good.

**Lean statements** (namespace `Toy.Checker`):

```lean
theorem sound_iff_checkerLE_classicalOracle {P : Type u} (good : P → Prop) (c : P → Bool) :
    Sound good c ↔ CheckerLE c (classicalOracle good)

theorem sound_rejectAll {P : Type u} (good : P → Prop) : Sound good rejectAll

theorem sound_of_checkerLE_of_sound {P : Type u} {good : P → Prop} {c₁ c₂ : P → Bool}
    (hle : CheckerLE c₁ c₂) (h₂ : Sound good c₂) : Sound good c₁

theorem sound_orChecker_of_sound_of_sound {P : Type u} {good : P → Prop} {c₁ c₂ : P → Bool}
    (h₁ : Sound good c₁) (h₂ : Sound good c₂) : Sound good (orChecker c₁ c₂)
```

Unfolded:

- `sound_iff_checkerLE_classicalOracle`: `(∀ p, c p = true → good p) ↔ (∀ p, c p = true → classicalOracle good p = true)`, where `classicalOracle good p = true ↔ good p` (`classicalOracle_eq_true_iff`).
- `sound_rejectAll`: `∀ p, (fun _ => false) p = true → good p`.
- `sound_of_checkerLE_of_sound`: from `∀ p, c₁ p = true → c₂ p = true` and `∀ p, c₂ p = true → good p`, conclude `∀ p, c₁ p = true → good p`.
- `sound_orChecker_of_sound_of_sound`: from `Sound good c₁` and `Sound good c₂`, conclude `∀ p, (c₁ p || c₂ p) = true → good p`.

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `hle : CheckerLE c₁ c₂ (sound_of_checkerLE_of_sound)` | c1 must not accept anything c2 rejects; otherwise c1 can accept programs about which c2's soundness says nothing. | tight: counterexample `cex_sound_of_checkerLE_needs_le` |
| `h₂ : Sound good c₂ (sound_of_checkerLE_of_sound)` | Soundness has to come from somewhere; the order only transfers it downward. | tight: counterexample `cex_sound_of_checkerLE_needs_sound` |
| `h₁ : Sound good c₁ (sound_orChecker_of_sound_of_sound)` | Accepting on c1's say-so requires c1 to be sound. | tight: counterexample `cex_sound_orChecker_needs_left` |
| `h₂ : Sound good c₂ (sound_orChecker_of_sound_of_sound)` | Symmetric to h1. | tight: counterexample `cex_sound_orChecker_needs_right` |

Each tight counterexample is stated in the form "all other hypotheses hold and the conclusion fails" for a concrete instance.

**Non-vacuity witness** (`nonvacuous_sound_iff_checkerLE_classicalOracle`, `nonvacuous_sound_of_checkerLE_of_sound`, `nonvacuous_sound_orChecker`). Both sides of the characterization occur: evenExact is below the oracle of evenGood and acceptAll is not (so soundness is not trivial in the toy instance). The closure hypotheses hold for evenBelowTen <= evenExact with evenExact sound, and for the two sound single-program checkers (· == 0) and (· == 2).

**Prior art.**

- X. Rival and K. Yi, Introduction to Static Analysis: An Abstract Interpretation Perspective, MIT Press, 2020, Chapter 1. Defines soundness (answer true implies the property) and completeness (the property implies answer true) of a yes/no analysis as here (Sound; CompleteOn with F = all programs), and notes that the analysis answering false everywhere is trivially sound and the one answering true everywhere trivially complete.
- P. Cousot and R. Cousot, 'Abstract interpretation: a unified lattice model for static analysis of programs by construction or approximation of fixpoints', POPL 1977, pp. 238-252, doi:10.1145/512950.512973. Source of the soundness-as-over-approximation framing of static analysis. Correspondence (our reading, not a statement of the paper): sound abstractions over-approximate the reachable behaviors and form an up-set whose top element carries no information; a yes/no checker derived from an abstraction accepts p only if the over-approximation lies within the safe behaviors. That passage reverses the order, so the up-set of sound over-approximations corresponds to the down-set of sound checkers, and the top element to rejectAll at the bottom.
- P. W. O'Hearn, 'Incorrectness logic', Proceedings of the ACM on Programming Languages 4(POPL):1-32, 2020, doi:10.1145/3371078. Under-approximate reasoning for bug finding: reported bugs are guaranteed to be real (no false positives), at the price of missed bugs. Cited for the opposite polarity: for such tools the degenerate tool reports nothing, which corresponds to acceptAll rather than rejectAll; this package states results for the certifying polarity only.

**Design question.** Can a framework exclude degenerate tools (reject-all) using soundness-style laws alone, or does it need an additional positive requirement?

Basis: execution (Lean kernel check): `sound_iff_checkerLE_classicalOracle`, `sound_rejectAll`, `sound_of_checkerLE_of_sound`, `sound_orChecker_of_sound_of_sound`.

Basis: derived (modeling bridge): A verifier, type checker, or translation validator whose "accept" certifies a safety property has, as input-output behavior, a Boolean function on program texts once nontermination and crashes are read as "reject"; its soundness is `Sound good c` for the property `good` it certifies. Under that reading the set of sound tools for a fixed property is downward closed and contains the tool that rejects everything. Gap: tools that assume different language dialects, memory models, or undefined-behavior conventions certify different predicates, and the `or` closure holds only for a shared predicate.

### R1e. Laws implied by soundness cannot exclude the reject-all checker

Kind: impossibility. Tier: **T0** (Immediate consequence of the textbook fact that rejecting everything is sound (R1a), stated as a fact about laws.) Depth: **definitional**. Module: `lean/ToyChecker/DownSet.lean`.

**Plain claim.** Any law L satisfied by every sound checker is also satisfied by rejectAll; consequently no law implied by soundness alone can exclude rejectAll.

**Lean statement** (namespace `Toy.Checker`):

```lean
theorem law_of_all_sound_holds_for_rejectAll {P : Type u} (good : P → Prop) (L : Law P)
    (hL : ∀ c, Sound good c → L c) : L rejectAll
```

Unfolded:

- `law_of_all_sound_holds_for_rejectAll`: for an arbitrary predicate `L : (P → Bool) → Prop`, `(∀ c, (∀ p, c p = true → good p) → L c) → L (fun _ => false)`.

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `hL : ∀ c, Sound good c → L c` | The law is implied by soundness (every sound checker satisfies it). | tight: counterexample `cex_law_of_all_sound_needs_hL` |

Each tight counterexample is stated in the form "all other hypotheses hold and the conclusion fails" for a concrete instance.

**Non-vacuity witness** (`nonvacuous_law_of_all_sound`). L := Sound evenGood satisfies hL.

**Positive control.** `positive_control_anchor_law_excludes_rejectAll`: the nearby law "sound for `evenGood` and accepts `0`" (not implied by soundness) is satisfied by `evenExact` and excludes `rejectAll`.

**Prior art.**

- X. Rival and K. Yi, Introduction to Static Analysis: An Abstract Interpretation Perspective, MIT Press, 2020, Chapter 1. Defines soundness (answer true implies the property) and completeness (the property implies answer true) of a yes/no analysis as here (Sound; CompleteOn with F = all programs), and notes that the analysis answering false everywhere is trivially sound and the one answering true everywhere trivially complete.
- P. Cousot and R. Cousot, 'Abstract interpretation: a unified lattice model for static analysis of programs by construction or approximation of fixpoints', POPL 1977, pp. 238-252, doi:10.1145/512950.512973. Source of the soundness-as-over-approximation framing of static analysis. Correspondence (our reading, not a statement of the paper): sound abstractions over-approximate the reachable behaviors and form an up-set whose top element carries no information; a yes/no checker derived from an abstraction accepts p only if the over-approximation lies within the safe behaviors. That passage reverses the order, so the up-set of sound over-approximations corresponds to the down-set of sound checkers, and the top element to rejectAll at the bottom.

**Design question.** Can a framework exclude degenerate tools (reject-all) using soundness-style laws alone, or does it need an additional positive requirement?

Basis: execution (Lean kernel check): `law_of_all_sound_holds_for_rejectAll`.

Basis: derived (modeling bridge): An admission policy for third-party analysis tools stated only as "the tool must be sound", or as any condition every sound tool meets, admits a tool that rejects every program; excluding it needs a positive requirement (anchors, completeness on a fragment, or checked two-sided answers). Gap: for bug finders that promise no false alarms the polarity is reversed and the degenerate tool is the one that reports nothing.

### R2a. Anchors exclude reject-all exactly when nonempty, and admit the allowlist of good anchors

Kind: characterization. Tier: **T0** (Restatement of version-space facts for an unrestricted hypothesis space: the empty hypothesis is consistent iff there are no positive examples, and the disjunction of the positive examples is consistent when they are all good.) Depth: **definitional**. Module: `lean/ToyChecker/Anchors.lean`.

**Plain claim.** The anchored law (sound and accepts every anchor in the finite list A) excludes rejectAll iff A is nonempty, for every good and every A whether or not the anchors are good; and if every anchor is good, the anchored law admits the allowlist checker that accepts exactly the members of A.

**Lean statements** (namespace `Toy.Checker`):

```lean
theorem not_anchoredSound_rejectAll_iff_anchors_ne_nil {P : Type u} (good : P → Prop)
    (A : List P) : ¬ AnchoredSound good A rejectAll ↔ A ≠ []

theorem allowlist_anchoredSound_of_anchors_good {P : Type u} [DecidableEq P]
    {good : P → Prop} {A : List P} (hA : ∀ a ∈ A, good a) :
    AnchoredSound good A (allowlist A)
```

Unfolded:

- `not_anchoredSound_rejectAll_iff_anchors_ne_nil`: `¬ ((∀ p, false = true → good p) ∧ ∀ a ∈ A, false = true) ↔ A ≠ []`.
- `allowlist_anchoredSound_of_anchors_good`: `(∀ a ∈ A, good a) → (∀ p, decide (p ∈ A) = true → good p) ∧ ∀ a ∈ A, decide (a ∈ A) = true`.

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `[DecidableEq P] (allowlist_anchoredSound_of_anchors_good)` | Needed only to define the allowlist as a Boolean function; the allowlist does not depend on which instance is used, and one always exists classically. | harmless |
| `hA : ∀ a ∈ A, good a (allowlist_anchoredSound_of_anchors_good)` | Accepting a bad anchor contradicts soundness, so with a bad anchor nothing is admitted. | tight: counterexample `cex_allowlist_anchoredSound_needs_anchors_good` |

Each tight counterexample is stated in the form "all other hypotheses hold and the conclusion fails" for a concrete instance.

**Non-vacuity witness** (`nonvacuous_not_anchoredSound_rejectAll`, `nonvacuous_anchors_good`). Both sides of the first statement occur (anchors [0] exclude rejectAll; no anchors admit it); the anchors [0, 2] are good for evenGood.

**Prior art.**

- T. M. Mitchell, 'Generalization as search', Artificial Intelligence 18(2):203-226, 1982, doi:10.1016/0004-3702(82)90040-6. Version spaces: the hypotheses consistent with labeled examples, ordered by generality and represented by their most specific and most general boundary sets.
- T. M. Mitchell, Machine Learning, McGraw-Hill, 1997, Chapter 2 (concept learning, the version space representation theorem, and the unbiased learner whose hypothesis space contains every subset of the instances). For that learner the most specific consistent hypothesis is the disjunction of the positive examples and no instance outside the training examples is classified unanimously. Correspondence (our reading): checkers are hypotheses, the pointwise order is the generality order, anchors and suite entries are labeled examples, and soundness acts as a negative example at every bad program (infinitely many in general, unlike a finite training set); the results cited here restate that picture in this vocabulary.

**Design question.** What do positive anchors and finite conformance suites actually force on an admitted tool, and can they exclude lookup-table tools?

Basis: execution (Lean kernel check): `not_anchoredSound_rejectAll_iff_anchors_ne_nil`, `allowlist_anchoredSound_of_anchors_good`.

Basis: derived (modeling bridge): A reference corpus of known-good programs that an admitted tool must accept excludes the do-nothing tool as soon as the corpus is nonempty, but is also met by a tool that accepts exactly the corpus. Gap: real corpora are fixed in advance; the theorem says nothing about corpora chosen after the tool.

### R2c. What the anchored law forces: acceptance exactly on anchors, rejection exactly on bad programs

Kind: characterization. Tier: **T0** (Restatement of the unanimous-vote facts for an unbiased version space (only training examples are classified unanimously), with soundness playing the role of a negative example at every bad program.) Depth: **shallow**. Module: `lean/ToyChecker/Anchors.lean`.

**Plain claim.** If every anchor in A is good, a program is accepted by every checker that the anchored law admits iff it is an anchor, and is rejected by every admitted checker iff it is bad; explicitly, for any good program p not in A, the allowlists of A and of p :: A are both admitted and disagree on p.

**Lean statements** (namespace `Toy.Checker`):

```lean
theorem forced_accept_iff_mem_anchors_of_anchors_good {P : Type u} {good : P → Prop} {A : List P}
    (hA : ∀ a ∈ A, good a) (p : P) :
    (∀ c, AnchoredSound good A c → c p = true) ↔ p ∈ A

theorem forced_reject_iff_not_good_of_anchors_good {P : Type u} {good : P → Prop} {A : List P}
    (hA : ∀ a ∈ A, good a) (p : P) :
    (∀ c, AnchoredSound good A c → c p = false) ↔ ¬ good p

theorem anchoredSound_admits_allowlists_disagreeing_at_good_nonanchor_of_anchors_good
    {P : Type u} [DecidableEq P] {good : P → Prop} {A : List P} {p : P}
    (hA : ∀ a ∈ A, good a) (hp : good p) (hpA : p ∉ A) :
    AnchoredSound good A (allowlist A) ∧ AnchoredSound good A (allowlist (p :: A)) ∧
    allowlist A p = false ∧ allowlist (p :: A) p = true
```

Unfolded:

- `forced_accept_iff_mem_anchors_of_anchors_good`: assuming `∀ a ∈ A, good a`, `(∀ c, (Sound good c ∧ ∀ a ∈ A, c a = true) → c p = true) ↔ p ∈ A`.
- `forced_reject_iff_not_good_of_anchors_good`: assuming `∀ a ∈ A, good a`, `(∀ c, (Sound good c ∧ ∀ a ∈ A, c a = true) → c p = false) ↔ ¬ good p`.
- `anchoredSound_admits_allowlists_disagreeing_at_good_nonanchor_of_anchors_good`: assuming `∀ a ∈ A, good a`, `good p` and `p ∉ A`, both `fun q => decide (q ∈ A)` and `fun q => decide (q ∈ p :: A)` satisfy `AnchoredSound good A`, the first answers `false` at `p` and the second `true`.

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `hA : ∀ a ∈ A, good a (forced_accept_iff_mem_anchors_of_anchors_good)` | With a bad anchor the law admits nothing and every program is vacuously forced to be accepted. | tight: counterexample `cex_forced_accept_needs_anchors_good` |
| `hA : ∀ a ∈ A, good a (forced_reject_iff_not_good_of_anchors_good)` | With a bad anchor the law admits nothing and every program is vacuously forced to be rejected. | tight: counterexample `cex_forced_reject_needs_anchors_good` |
| `[DecidableEq P] (anchoredSound_admits_allowlists_disagreeing_at_good_nonanchor_of_anchors_good)` | Needed only to define allowlists; they do not depend on the instance. | harmless |
| `hA : ∀ a ∈ A, good a (witness family)` | Otherwise neither allowlist is admitted. | tight: counterexample `cex_admits_allowlists_needs_anchors_good` |
| `hp : good p (witness family)` | Otherwise the allowlist of p :: A is unsound. | tight: counterexample `cex_admits_allowlists_needs_good_p` |
| `hpA : p ∉ A (witness family)` | Otherwise the allowlist of A accepts p, so the two allowlists do not disagree on p. | tight: counterexample `cex_admits_allowlists_needs_not_mem` |

Each tight counterexample is stated in the form "all other hypotheses hold and the conclusion fails" for a concrete instance.

**Non-vacuity witness** (`nonvacuous_anchors_good`, `nonvacuous_admits_allowlists`). Anchors [0, 2] are good for evenGood; for the witness family, anchors [0] and the good non-anchor 2.

**Prior art.**

- T. M. Mitchell, Machine Learning, McGraw-Hill, 1997, Chapter 2 (concept learning, the version space representation theorem, and the unbiased learner whose hypothesis space contains every subset of the instances). For that learner the most specific consistent hypothesis is the disjunction of the positive examples and no instance outside the training examples is classified unanimously. Correspondence (our reading): checkers are hypotheses, the pointwise order is the generality order, anchors and suite entries are labeled examples, and soundness acts as a negative example at every bad program (infinitely many in general, unlike a finite training set); the results cited here restate that picture in this vocabulary.
- T. M. Mitchell, 'Generalization as search', Artificial Intelligence 18(2):203-226, 1982, doi:10.1016/0004-3702(82)90040-6. Version spaces: the hypotheses consistent with labeled examples, ordered by generality and represented by their most specific and most general boundary sets.

**Design question.** What do positive anchors and finite conformance suites actually force on an admitted tool, and can they exclude lookup-table tools?

Basis: execution (Lean kernel check): `forced_accept_iff_mem_anchors_of_anchors_good`, `forced_reject_iff_not_good_of_anchors_good`, `anchoredSound_admits_allowlists_disagreeing_at_good_nonanchor_of_anchors_good`.

Basis: derived (modeling bridge): A tool admitted under "sound plus a known-good corpus" is constrained only on the corpus (must accept) and on the bad programs (must reject); on every other good program admitted tools may disagree. Gap: the witness tools presuppose knowing which programs are good.

### R2f. A lookup table passes every finite suite that a sound checker passes

Kind: impossibility. Tier: **T0** (Restatement of the fact that the most specific hypothesis consistent with labeled examples in an unrestricted hypothesis space is the disjunction of the positive examples, read as the informal lookup-table argument against finite behavioral tests.) Depth: **shallow**. Module: `lean/ToyChecker/Anchors.lean`.

**Plain claim.** For a finite test suite T (programs with expected answers): if some checker c passes T, then the lookup table of T (accept exactly the programs that T expects to be accepted) passes T and is pointwise below c, so it is the least checker passing T; if moreover c is sound, the lookup table is sound. So no law of the form 'sound and passes T' admits some checker while excluding the lookup table of T.

**Lean statements** (namespace `Toy.Checker`):

```lean
theorem tableChecker_sound_passes_le_of_sound_passes {P : Type u} [DecidableEq P]
    {good : P → Prop} {c : P → Bool} {T : TestSuite P}
    (hc : Sound good c) (hT : Passes c T) :
    Sound good (tableChecker T) ∧ Passes (tableChecker T) T ∧ CheckerLE (tableChecker T) c

theorem tableChecker_passes_and_le_of_passes {P : Type u} [DecidableEq P]
    {c : P → Bool} {T : TestSuite P} (hT : Passes c T) :
    Passes (tableChecker T) T ∧ CheckerLE (tableChecker T) c
```

Unfolded:

- With `Passes c T := ∀ q ∈ T, c q.1 = q.2` and `tableChecker T := fun p => decide ((p, true) ∈ T)`:
- `tableChecker_passes_and_le_of_passes`: `Passes c T → Passes (tableChecker T) T ∧ ∀ p, decide ((p, true) ∈ T) = true → c p = true`.
- `tableChecker_sound_passes_le_of_sound_passes`: `Sound good c → Passes c T → Sound good (tableChecker T) ∧ Passes (tableChecker T) T ∧ CheckerLE (tableChecker T) c`.

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `[DecidableEq P]` | Needed only to define the lookup table; it does not depend on the instance. | harmless |
| `hc : Sound good c (tableChecker_sound_passes_le_of_sound_passes)` | Soundness of the table is inherited from c via the order; a suite passed only by unsound checkers can expect acceptance of a bad program. | tight: counterexample `cex_tableChecker_sound_needs_sound` |
| `hT : Passes c T (tableChecker_sound_passes_le_of_sound_passes)` | Some sound checker must pass T, so T expects acceptance only of good programs. | tight: counterexample `cex_tableChecker_sound_needs_passes` |
| `hT : Passes c T (tableChecker_passes_and_le_of_passes)` | Without a passing checker the table need not be below c (consistent suite, c = rejectAll) and need not pass T (inconsistent suite). | tight: counterexample `cex_tableChecker_passes_and_le_needs_passes` |

Each tight counterexample is stated in the form "all other hypotheses hold and the conclusion fails" for a concrete instance.

**Non-vacuity witness** (`nonvacuous_tableChecker`). evenExact is sound for evenGood and passes [(0, true), (1, false), (2, true)].

**Positive control.** `positive_control_completeOn_admits_evenExact_excludes_tableChecker`: adding completeness on all programs to "sound and passes `[(0, true), (1, false)]`" admits `evenExact` and excludes the lookup table of that suite (which is sound and passes it). `positive_control_doubling_law_admits_fourOrTwo_excludes_every_tableChecker`: the relational law "sound, passes `[(2, true)]`, and accepting `p` forces accepting `2 * p`" admits the conservative, incomplete checker `fourOrTwo` (`n % 4 == 0 || n == 2`) and excludes the lookup table of every finite suite.

**Prior art.**

- T. M. Mitchell, Machine Learning, McGraw-Hill, 1997, Chapter 2 (concept learning, the version space representation theorem, and the unbiased learner whose hypothesis space contains every subset of the instances). For that learner the most specific consistent hypothesis is the disjunction of the positive examples and no instance outside the training examples is classified unanimously. Correspondence (our reading): checkers are hypotheses, the pointwise order is the generality order, anchors and suite entries are labeled examples, and soundness acts as a negative example at every bad program (infinitely many in general, unlike a finite training set); the results cited here restate that picture in this vocabulary.
- J. B. Goodenough and S. L. Gerhart, 'Toward a theory of test data selection', IEEE Transactions on Software Engineering SE-1(2):156-173, 1975, doi:10.1109/TSE.1975.6312836. Formal account of when passing a finite test set establishes correctness: only under conditions on the test selection criterion (reliability and validity) that tie the tested inputs to the untested ones.
- M.-C. Gaudel, 'Testing can be formal, too', TAPSOFT '95, LNCS 915, pp. 82-96, 1995, doi:10.1007/3-540-59293-8_188. Specification-based testing in which a finite test set is justified only together with explicit hypotheses on the implementation under test (uniformity, regularity). The lookup-table statement here is the situation without any such hypothesis.
- N. Block, 'Psychologism and Behaviorism', The Philosophical Review 90(1):5-43, 1981, doi:10.2307/2184371. The lookup-table thought experiment: a system that reproduces any finite stretch of required behavior by table lookup, used to argue that behavioral tests alone cannot certify how behavior is produced. Philosophical background only; no formal statement there corresponds to these theorems.

**Design question.** What do positive anchors and finite conformance suites actually force on an admitted tool, and can they exclude lookup-table tools?

Basis: execution (Lean kernel check): `tableChecker_sound_passes_le_of_sound_passes`, `tableChecker_passes_and_le_of_passes`.

Basis: derived (modeling bridge): A conformance suite with expected verdicts, fixed before tools are submitted, is passed by the memorizing tool that accepts exactly the suite's positive entries whenever it is passed by any sound tool. Gap: held-out or randomized suites, and testing hypotheses on the implementation under test, are not modeled.

### R3a. Extensional laws cannot separate behaviorally identical implementations

Kind: impossibility. Tier: **T0** (Restatement of the definition of an extensional property and of function extensionality, for laws on tool implementations, with a concrete instance.) Depth: **definitional**. Module: `lean/ToyChecker/Extensional.lean`.

**Plain claim.** If a law on tool implementations is extensional (respects pointwise equality of behavior) and two implementations have the same behavior on every program, the law holds of one iff it holds of the other; every law stated directly on Boolean checkers is extensional (by function extensionality), so for laws on input-output behavior the hypothesis is automatic; in particular, in the toy model no extensional law separates the specific arithmetic implementation honestImpl ('accept p iff p < 10 and p is even') from the specific lookup table tableImpl ([0, 2, 4, 6, 8]).

**Lean statements** (namespace `Toy.Checker`):

```lean
theorem extensionalLaw_iff_of_same_behavior {P : Type u} {I : Type v} {run : I → P → Bool}
    {L : I → Prop} {i j : I} (hL : ExtensionalLaw run L) (hij : ∀ p, run i p = run j p) :
    L i ↔ L j

theorem extensionalLaw_id_of_law {P : Type u} (L : Law P) :
    ExtensionalLaw (id : (P → Bool) → P → Bool) L

theorem extensionalLaw_cannot_separate_honestImpl_from_tableImpl {L : ToyImpl → Prop}
    (hL : ExtensionalLaw toyRun L) : L honestImpl ↔ L tableImpl
```

Unfolded:

- With `ExtensionalLaw run L := ∀ i j, (∀ p, run i p = run j p) → L i → L j`:
- `extensionalLaw_iff_of_same_behavior`: `ExtensionalLaw run L → (∀ p, run i p = run j p) → (L i ↔ L j)`.
- `extensionalLaw_id_of_law`: for every `L : (P → Bool) → Prop`, `∀ c₁ c₂, (∀ p, c₁ p = c₂ p) → L c₁ → L c₂`.
- `extensionalLaw_cannot_separate_honestImpl_from_tableImpl`: `ExtensionalLaw toyRun L → (L (.evenBelow 10) ↔ L (.table [0, 2, 4, 6, 8]))`, where `toyRun (.evenBelow n) p = (decide (p < n) && p % 2 == 0)` and `toyRun (.table l) p = decide (p ∈ l)`.

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `hL : ExtensionalLaw run L (extensionalLaw_iff_of_same_behavior)` | The law must look only at behavior; an intensional law can separate behaviorally identical implementations. | tight: counterexample `cex_extensionalLaw_iff_needs_extensional` |
| `hij : ∀ p, run i p = run j p (extensionalLaw_iff_of_same_behavior)` | The two implementations must agree everywhere; an extensional law can separate implementations that differ on one program. | tight: counterexample `cex_extensionalLaw_iff_needs_same_behavior` |
| `hL : ExtensionalLaw toyRun L (extensionalLaw_cannot_separate_honestImpl_from_tableImpl)` | Only behavior-respecting laws are blind to the difference; IsStructural is not extensional and separates the two implementations. | tight: counterexample `cex_extensionalLaw_iff_needs_extensional` |

Each tight counterexample is stated in the form "all other hypotheses hold and the conclusion fails" for a concrete instance.

**Non-vacuity witness** (`nonvacuous_extensionalLaw_iff`, `nonvacuous_extensionalLaw_id`). The law 'behavior is sound for evenGood' is extensional and honestImpl, tableImpl have the same behavior; soundness for evenGood, as a law on Boolean checkers, instantiates the second statement.

**Positive control.** `positive_control_intensional_law_separates`: the intensional law `IsStructural` (true for `.evenBelow n`, false for `.table l`) holds of `honestImpl` and fails for `tableImpl`.

**Prior art.**

- H. G. Rice, 'Classes of recursively enumerable sets and their decision problems', Transactions of the American Mathematical Society 74(2):358-366, 1953, doi:10.1090/S0002-9947-1953-0053041-6. Rice's theorem: a class of recursively enumerable sets has a decidable index set only if it is trivial. Context only, and a different notion of extensionality: Rice's hypothesis concerns properties of programs that depend only on the function a program computes, whereas ExtensionalLaw concerns laws on tools that depend only on the tools' answers. Not formalized here.
- R. Bruni, R. Giacobazzi, R. Gori, I. Garcia-Contreras and D. Pavlovic, 'Abstract extensionality: on the properties of incomplete abstract interpretations', Proceedings of the ACM on Programming Languages 4(POPL):1-28, 2020, doi:10.1145/3371096. Non-trivial abstract interpretations distinguish some extensionally equivalent programs: analyzer precision is an intensional property of the analyzed programs. Illustrates the difference between tool-level extensionality (here) and semantic extensionality of target programs.
- N. Block, 'Psychologism and Behaviorism', The Philosophical Review 90(1):5-43, 1981, doi:10.2307/2184371. The lookup-table thought experiment: a system that reproduces any finite stretch of required behavior by table lookup, used to argue that behavioral tests alone cannot certify how behavior is produced. Philosophical background only; no formal statement there corresponds to these theorems.

**Design question.** Can laws about a tool's input-output behavior distinguish an honest analysis from a behaviorally identical lookup table or wrapper?

Basis: execution (Lean kernel check): `extensionalLaw_iff_of_same_behavior`, `extensionalLaw_id_of_law`, `extensionalLaw_cannot_separate_honestImpl_from_tableImpl`.

Basis: derived (modeling bridge): Any admission check that runs a tool and inspects only its answers is an extensional law; it cannot tell an honest analyzer from a wrapper or table with the same answers on every input. Gap: real behavioral checks observe finitely many inputs, which is weaker still (R2f); checks that inspect source code or build provenance are intensional and outside the statement.

### R4a. One-sided certification: a sound verifier makes every certifying tool sound

Kind: theorem. Tier: **T0** (Core soundness argument of proof-carrying code, certifying algorithms and verified validators, re-derived in the toy model.) Depth: **definitional**. Module: `lean/ToyChecker/Certificates.lean`.

**Plain claim.** If a fixed verifier V is sound (V p w = true implies good p), then for every one-sided certifying tool t the induced checker (accept p iff t p = some w and V p w = true; silence or a rejected certificate means reject) is sound, whatever t does.

**Lean statement** (namespace `Toy.Checker`):

```lean
theorem certChecker_sound_of_verifierSound {P : Type u} {W : Type v} {good : P → Prop}
    {V : P → W → Bool} (hV : VerifierSound good V) (t : P → Option W) :
    Sound good (certChecker V t)
```

Unfolded:

- `certChecker_sound_of_verifierSound`: `(∀ p w, V p w = true → good p) → ∀ t p, (match t p with | some w => V p w | none => false) = true → good p`.

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `hV : VerifierSound good V` | The trust is carried by V; with an unsound V some tool yields an unsound checker. | tight: counterexample `cex_certChecker_sound_needs_verifierSound` |

Each tight counterexample is stated in the form "all other hypotheses hold and the conclusion fails" for a concrete instance.

**Non-vacuity witness** (`nonvacuous_certChecker_sound`). halfV (w certifies p iff w + w = p) is sound for evenGood; the lying tool that always outputs 7 is an admissible t and its induced checker accepts 14.

**Prior art.**

- G. C. Necula, 'Proof-carrying code', POPL 1997, pp. 106-119, doi:10.1145/263699.263712. Untrusted code is shipped with a safety proof that the code consumer validates with a small proof checker against a fixed safety policy (one-sided: code without a valid proof is simply refused).
- R. M. McConnell, K. Mehlhorn, S. Näher and P. Schweitzer, 'Certifying algorithms', Computer Science Review 5(2):119-161, 2011, doi:10.1016/j.cosrev.2010.09.009. Algorithms that output a witness with each answer, checked by a simple checker, so that trust moves from the algorithm to the checker. For decision problems a certifying algorithm supplies a witness for either answer (for bipartiteness: a 2-coloring for yes, an odd cycle for no); that is the two-sided shape of R4f, not the one-sided certChecker of R4a-R4e, in which a rejection needs no witness.
- J.-B. Tristan and X. Leroy, 'Formal verification of translation validators: a case study on instruction scheduling optimizations', POPL 2008, pp. 17-27, doi:10.1145/1328438.1328444. A translation validator verified in Coq checks each run of an untrusted optimization; soundness of the validator gives correctness of every validated run, whatever the untrusted transformation does. A mechanized instance of the R4a pattern.
- E. Alkassar, S. Böhme, K. Mehlhorn and C. Rizkallah, 'A framework for the verification of certifying computations', Journal of Automated Reasoning 52(3):241-273, 2014, doi:10.1007/s10817-013-9289-2 (conference version CAV 2011, LNCS 6806, pp. 67-82, doi:10.1007/978-3-642-22110-1_7). Verifies witness checkers (with VCC) and the mathematical witness properties (with Isabelle/HOL), so that certified computations can be trusted without trusting the algorithm.
- R. Thiemann and C. Sternagel, 'Certification of termination proofs using CeTA', TPHOLs 2009, LNCS 5674, pp. 452-468, doi:10.1007/978-3-642-03359-9_31. A certifier, generated from an Isabelle/HOL formalization, that checks termination proofs produced by untrusted tools; a mechanized trusted verifier for certificates.
- A. Pnueli, M. Siegel and E. Singerman, 'Translation validation', TACAS 1998, LNCS 1384, pp. 151-166, doi:10.1007/BFb0054170. Instead of verifying a compiler once, each individual run is followed by a validation that the produced target implements the source.
- H. Barendregt and F. Wiedijk, 'The challenge of computer mathematics', Philosophical Transactions of the Royal Society A 363(1835):2351-2375, 2005, doi:10.1098/rsta.2005.1650. Discusses the de Bruijn criterion: proof assistants that emit proof objects checkable by a small independent checker.
- M. Blum and S. Kannan, 'Designing programs that check their work', Journal of the ACM 42(1):269-291, 1995, doi:10.1145/200836.200880. Program checkers: the answer of a program on a given input is checked by a separate (typically randomized) procedure that queries the program as a black box; the program emits no certificate. A contrasting model of per-run checking, not the one formalized by certChecker.

**Design question.** If tools must emit certificates checked by a fixed trusted verifier, which guarantees transfer from the verifier to every admitted tool, and which remain the tool's responsibility?

Basis: execution (Lean kernel check): `certChecker_sound_of_verifierSound`.

Basis: derived (modeling bridge): In proof-carrying code, translation validation, and certifying-algorithm designs, the soundness of the small trusted checker gives soundness of every accepted output, whatever the untrusted producer does. Gap: the trusted checker must check the certificate against the original input; any parser or verification-condition generator that maps the input to proof obligations is part of the trusted checker.

### R4b. One-sided certification: all certifying tools are sound iff the verifier is sound

Kind: characterization. Tier: **T0** (The trusted-checker principle as an exact equivalence, with the explicit witness for the converse.) Depth: **shallow**. Module: `lean/ToyChecker/Certificates.lean`.

**Plain claim.** Every one-sided certifying tool induces a sound checker iff the verifier V is sound; explicitly, if V accepts a certificate w for a bad program p, the tool that always outputs w induces an unsound checker.

**Lean statements** (namespace `Toy.Checker`):

```lean
theorem verifierSound_iff_forall_certChecker_sound {P : Type u} {W : Type v}
    (good : P → Prop) (V : P → W → Bool) :
    VerifierSound good V ↔ ∀ t : P → Option W, Sound good (certChecker V t)

theorem certChecker_const_not_sound_of_bad_certificate {P : Type u} {W : Type v}
    {good : P → Prop} {V : P → W → Bool} {p : P} {w : W}
    (hVpw : V p w = true) (hp : ¬ good p) :
    ¬ Sound good (certChecker V (fun _ => some w))
```

Unfolded:

- `verifierSound_iff_forall_certChecker_sound`: `(∀ p w, V p w = true → good p) ↔ ∀ t : P → Option W, Sound good (certChecker V t)`.
- `certChecker_const_not_sound_of_bad_certificate`: `V p w = true → ¬ good p → ¬ Sound good (certChecker V (fun _ => some w))`; here `certChecker V (fun _ => some w) q = V q w` for every `q`.

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `hVpw : V p w = true (certChecker_const_not_sound_of_bad_certificate)` | The certificate must actually be accepted for the bad program. | tight: counterexample `cex_const_not_sound_needs_accepted_certificate` |
| `hp : ¬ good p (certChecker_const_not_sound_of_bad_certificate)` | The program must actually be bad. | tight: counterexample `cex_const_not_sound_needs_bad_program` |

Each tight counterexample is stated in the form "all other hypotheses hold and the conclusion fails" for a concrete instance.

**Non-vacuity witness** (`nonvacuous_verifierSound_iff`, `nonvacuous_certChecker_const_not_sound`). Both sides of the equivalence occur (halfV is sound, trustAllV is not); trustAllV accepts () for the bad program 1.

**Prior art.**

- G. C. Necula, 'Proof-carrying code', POPL 1997, pp. 106-119, doi:10.1145/263699.263712. Untrusted code is shipped with a safety proof that the code consumer validates with a small proof checker against a fixed safety policy (one-sided: code without a valid proof is simply refused).
- R. M. McConnell, K. Mehlhorn, S. Näher and P. Schweitzer, 'Certifying algorithms', Computer Science Review 5(2):119-161, 2011, doi:10.1016/j.cosrev.2010.09.009. Algorithms that output a witness with each answer, checked by a simple checker, so that trust moves from the algorithm to the checker. For decision problems a certifying algorithm supplies a witness for either answer (for bipartiteness: a 2-coloring for yes, an odd cycle for no); that is the two-sided shape of R4f, not the one-sided certChecker of R4a-R4e, in which a rejection needs no witness.
- H. Barendregt and F. Wiedijk, 'The challenge of computer mathematics', Philosophical Transactions of the Royal Society A 363(1835):2351-2375, 2005, doi:10.1098/rsta.2005.1650. Discusses the de Bruijn criterion: proof assistants that emit proof objects checkable by a small independent checker.

**Design question.** If tools must emit certificates checked by a fixed trusted verifier, which guarantees transfer from the verifier to every admitted tool, and which remain the tool's responsibility?

Basis: execution (Lean kernel check): `verifierSound_iff_forall_certChecker_sound`, `certChecker_const_not_sound_of_bad_certificate`.

Basis: derived (modeling bridge): A framework that admits arbitrary certifying tools is exactly as trustworthy as its verifier: an unsound verifier is exploitable by some tool. Gap: for a restricted family of tools the converse can fail.

### R4c. One-sided certification: exact condition for completeness of the induced checker

Kind: characterization. Tier: **T0** (Exact unfolding of completeness for the one-sided certifying pipeline, with its consequence for the verifier.) Depth: **definitional**. Module: `lean/ToyChecker/Certificates.lean`.

**Plain claim.** The checker induced by a one-sided tool t and verifier V is complete on fragment F iff for every good program p in F the tool outputs some certificate w with V p w = true; in particular, completeness on F requires V to accept some certificate for every good program of F.

**Lean statements** (namespace `Toy.Checker`):

```lean
theorem certChecker_completeOn_iff {P : Type u} {W : Type v} (good F : P → Prop)
    (V : P → W → Bool) (t : P → Option W) :
    CompleteOn good F (certChecker V t) ↔
      ∀ p, good p → F p → ∃ w, t p = some w ∧ V p w = true

theorem verifierCompleteOn_of_certChecker_completeOn {P : Type u} {W : Type v}
    {good F : P → Prop} {V : P → W → Bool} {t : P → Option W}
    (h : CompleteOn good F (certChecker V t)) : ∀ p, good p → F p → ∃ w, V p w = true
```

Unfolded:

- `certChecker_completeOn_iff`: `(∀ p, good p → F p → certChecker V t p = true) ↔ ∀ p, good p → F p → ∃ w, t p = some w ∧ V p w = true`.
- `verifierCompleteOn_of_certChecker_completeOn`: `CompleteOn good F (certChecker V t) → ∀ p, good p → F p → ∃ w, V p w = true`.

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `h : CompleteOn good F (certChecker V t) (verifierCompleteOn_of_certChecker_completeOn)` | Without a complete pipeline nothing forces V to have certificates (e.g. rejectAllV has none). | tight: counterexample `cex_verifierCompleteOn_needs_completeOn` |

Each tight counterexample is stated in the form "all other hypotheses hold and the conclusion fails" for a concrete instance.

**Non-vacuity witness** (`nonvacuous_certChecker_completeOn_iff`, `nonvacuous_verifierCompleteOn_of_certChecker_completeOn`). Both sides of the equivalence occur for halfV on all programs (the honest tool satisfies the right-hand side, the silent tool does not); the honest tool's pipeline is complete on all programs.

**Prior art.**

- R. M. McConnell, K. Mehlhorn, S. Näher and P. Schweitzer, 'Certifying algorithms', Computer Science Review 5(2):119-161, 2011, doi:10.1016/j.cosrev.2010.09.009. Algorithms that output a witness with each answer, checked by a simple checker, so that trust moves from the algorithm to the checker. For decision problems a certifying algorithm supplies a witness for either answer (for bipartiteness: a 2-coloring for yes, an odd cycle for no); that is the two-sided shape of R4f, not the one-sided certChecker of R4a-R4e, in which a rejection needs no witness.
- A. Pnueli, M. Siegel and E. Singerman, 'Translation validation', TACAS 1998, LNCS 1384, pp. 151-166, doi:10.1007/BFb0054170. Instead of verifying a compiler once, each individual run is followed by a validation that the produced target implements the source.
- J.-B. Tristan and X. Leroy, 'Formal verification of translation validators: a case study on instruction scheduling optimizations', POPL 2008, pp. 17-27, doi:10.1145/1328438.1328444. A translation validator verified in Coq checks each run of an untrusted optimization; soundness of the validator gives correctness of every validated run, whatever the untrusted transformation does. A mechanized instance of the R4a pattern.

**Design question.** If tools must emit certificates checked by a fixed trusted verifier, which guarantees transfer from the verifier to every admitted tool, and which remain the tool's responsibility?

Basis: execution (Lean kernel check): `certChecker_completeOn_iff`, `verifierCompleteOn_of_certChecker_completeOn`.

Basis: derived (modeling bridge): In a one-sided certifying design, completeness on a fragment is the tool's responsibility and additionally needs certificates to exist in the verifier's language for every good input of the fragment. Gap: the cost of finding certificates is not modeled.

### R4d. One-sided certification: a sound and complete verifier does not give a complete checker

Kind: counterexample. Tier: **T1** (Concrete counterexample to the tempting reading that a sound and complete trusted verifier makes a one-sided certifying pipeline complete.) Depth: **definitional**. Module: `lean/ToyChecker/Certificates.lean`.

**Plain claim.** In one-sided certification completeness is not transferred from the verifier: halfV is sound and complete for evenGood (every even number has a certificate), yet the tool that never outputs a certificate induces a checker that is not complete on all programs.

**Lean statement** (namespace `Toy.Checker`):

```lean
theorem cex_verifierSound_verifierComplete_not_completeOn :
    VerifierSound evenGood halfV ∧ VerifierComplete evenGood halfV ∧
    ¬ CompleteOn evenGood (fun _ => True) (certChecker halfV silentTool)
```

Unfolded:

- With `halfV p w := (w + w == p)` and `silentTool := fun _ => none`: `(∀ p w, halfV p w = true → p % 2 = 0) ∧ (∀ p, p % 2 = 0 → ∃ w, halfV p w = true) ∧ ¬ (∀ p, p % 2 = 0 → True → certChecker halfV silentTool p = true)`.

**Hypothesis ledger.** None: a closed statement about a concrete instance.

**Non-vacuity witness** (`cex_verifierSound_verifierComplete_not_completeOn`). It is itself a concrete instance.

**Prior art.**

- R. M. McConnell, K. Mehlhorn, S. Näher and P. Schweitzer, 'Certifying algorithms', Computer Science Review 5(2):119-161, 2011, doi:10.1016/j.cosrev.2010.09.009. Algorithms that output a witness with each answer, checked by a simple checker, so that trust moves from the algorithm to the checker. For decision problems a certifying algorithm supplies a witness for either answer (for bipartiteness: a 2-coloring for yes, an odd cycle for no); that is the two-sided shape of R4f, not the one-sided certChecker of R4a-R4e, in which a rejection needs no witness.
- G. C. Necula, 'Proof-carrying code', POPL 1997, pp. 106-119, doi:10.1145/263699.263712. Untrusted code is shipped with a safety proof that the code consumer validates with a small proof checker against a fixed safety policy (one-sided: code without a valid proof is simply refused).

**Design question.** If tools must emit certificates checked by a fixed trusted verifier, which guarantees transfer from the verifier to every admitted tool, and which remain the tool's responsibility?

Basis: execution (Lean kernel check): `cex_verifierSound_verifierComplete_not_completeOn`.

Basis: derived (modeling bridge): A certifying design whose trusted verifier is complete for the property still admits a tool that never certifies anything, unless completeness is required of the tool. Gap: none beyond those of R4c.

### R4e. One-sided certification: the Boolean checkers induced by certifying tools

Kind: characterization. Tier: **T1** (Folklore made precise; no source stating it in this form was found.) Depth: **shallow**. Module: `lean/ToyChecker/Certificates.lean`.

**Plain claim.** A Boolean checker c is the checker induced by some one-sided certifying tool for V iff c is sound for the V-certifiability predicate 'p has some certificate that V accepts' (fun p => ∃ w, V p w = true).

**Lean statement** (namespace `Toy.Checker`):

```lean
theorem exists_certChecker_eq_iff_sound_certifiable {P : Type u} {W : Type v}
    (V : P → W → Bool) (c : P → Bool) :
    (∃ t : P → Option W, certChecker V t = c) ↔ Sound (fun p => ∃ w, V p w = true) c
```

Unfolded:

- `exists_certChecker_eq_iff_sound_certifiable`: `(∃ t : P → Option W, certChecker V t = c) ↔ ∀ p, c p = true → ∃ w, V p w = true`.

**Hypothesis ledger.** No hypotheses beyond the universally quantified data.

**Non-vacuity witness** (`nonvacuous_exists_certChecker_eq_iff`). Both sides occur for halfV: evenExact is sound for 'has a halfV certificate', acceptAll is not.

**Prior art.**

- R. M. McConnell, K. Mehlhorn, S. Näher and P. Schweitzer, 'Certifying algorithms', Computer Science Review 5(2):119-161, 2011, doi:10.1016/j.cosrev.2010.09.009. Algorithms that output a witness with each answer, checked by a simple checker, so that trust moves from the algorithm to the checker. For decision problems a certifying algorithm supplies a witness for either answer (for bipartiteness: a 2-coloring for yes, an odd cycle for no); that is the two-sided shape of R4f, not the one-sided certChecker of R4a-R4e, in which a rejection needs no witness.
- G. C. Necula, 'Proof-carrying code', POPL 1997, pp. 106-119, doi:10.1145/263699.263712. Untrusted code is shipped with a safety proof that the code consumer validates with a small proof checker against a fixed safety policy (one-sided: code without a valid proof is simply refused).

**Design question.** If tools must emit certificates checked by a fixed trusted verifier, which guarantees transfer from the verifier to every admitted tool, and which remain the tool's responsibility?

Basis: execution (Lean kernel check): `exists_certChecker_eq_iff_sound_certifiable`.

Basis: derived (modeling bridge): At the level of Boolean behavior, one-sided certification admits exactly the checkers sound for certifiability; certificates change what a tool must output, not which accept sets are possible (lookup tables that cache valid certificates included). Gap: the right-to-left direction picks certificates by choice and says nothing about computing them.

### R4f. Two-sided certification with checked answers on F: sound everywhere, complete on F

Kind: theorem. Tier: **T0** (Restatement of the certifying-algorithm principle for decision problems (a checked witness for either answer makes the answer trustworthy), for a framework that requires checked answers on a fragment.) Depth: **shallow**. Module: `lean/ToyChecker/Certificates.lean`.

**Plain claim.** In two-sided certification, where a tool answers each program with a verdict plus evidence (a certificate for true, a refutation for false): if the certificate verifier is sound for good, the refutation verifier is sound for not-good, and every answer of the tool on fragment F carries evidence that its verifier accepts, then the induced checker (accept iff the verdict is true and its certificate is accepted) is sound everywhere and complete on F.

**Lean statement** (namespace `Toy.Checker`):

```lean
theorem twoSidedChecker_sound_completeOn_of_verifiedOn {P : Type u} {W : Type v}
    {good F : P → Prop} {Vpos Vneg : P → W → Bool} {t : P → Bool × W}
    (hpos : VerifierSound good Vpos) (hneg : VerifierSound (fun p => ¬ good p) Vneg)
    (hver : TwoSidedVerifiedOn Vpos Vneg F t) :
    Sound good (twoSidedChecker Vpos t) ∧ CompleteOn good F (twoSidedChecker Vpos t)
```

Unfolded:

- `twoSidedChecker_sound_completeOn_of_verifiedOn`: assuming `∀ p w, Vpos p w = true → good p`, `∀ p w, Vneg p w = true → ¬ good p`, and `∀ p, F p → ((t p).1 = true → Vpos p (t p).2 = true) ∧ ((t p).1 = false → Vneg p (t p).2 = true)`, conclude `(∀ p, ((t p).1 && Vpos p (t p).2) = true → good p) ∧ ∀ p, good p → F p → ((t p).1 && Vpos p (t p).2) = true`.

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `hpos : VerifierSound good Vpos` | Accepted verdicts are trusted only through Vpos; with an unsound Vpos a tool answering true everywhere is admitted and accepts bad programs. | tight: counterexample `cex_twoSidedChecker_needs_pos_sound` |
| `hneg : VerifierSound (fun p => ¬ good p) Vneg` | A false verdict on a good program must be impossible to justify; with an unsound Vneg a tool answering false everywhere is admitted. | tight: counterexample `cex_twoSidedChecker_needs_neg_sound` |
| `hver : TwoSidedVerifiedOn Vpos Vneg F t` | The law must demand checked evidence for every answer on F; otherwise a silent tool is admitted and rejects good programs. | tight: counterexample `cex_twoSidedChecker_needs_verified` |

Each tight counterexample is stated in the form "all other hypotheses hold and the conclusion fails" for a concrete instance.

**Non-vacuity witness** (`nonvacuous_twoSidedChecker_sound_completeOn`). halfV (certificates) and oddV (w refutes p iff w + w + 1 = p) are sound, and the honest two-sided tool p |-> (p even?, p / 2) is verified on all programs.

**Prior art.**

- R. M. McConnell, K. Mehlhorn, S. Näher and P. Schweitzer, 'Certifying algorithms', Computer Science Review 5(2):119-161, 2011, doi:10.1016/j.cosrev.2010.09.009. Algorithms that output a witness with each answer, checked by a simple checker, so that trust moves from the algorithm to the checker. For decision problems a certifying algorithm supplies a witness for either answer (for bipartiteness: a 2-coloring for yes, an odd cycle for no); that is the two-sided shape of R4f, not the one-sided certChecker of R4a-R4e, in which a rejection needs no witness.

**Design question.** If tools must emit certificates checked by a fixed trusted verifier, which guarantees transfer from the verifier to every admitted tool, and which remain the tool's responsibility?

Basis: execution (Lean kernel check): `twoSidedChecker_sound_completeOn_of_verifiedOn`.

Basis: derived (modeling bridge): Certifying decision procedures that emit a witness for either answer (for bipartiteness, a 2-coloring or an odd cycle), combined with a framework rule that every answer on a fragment carry a checked witness, admit only tools that are sound everywhere and complete on that fragment. Gap: tools that decline to answer or time out on the fragment are excluded by the rule rather than represented; a framework that tolerates unverified answers is back in the one-sided case.

### R5b. Soundness cannot distinguish a checker from its relabeled twin

Kind: impossibility. Tier: **T0** (Invariance of soundness under precomposition with a goodness-preserving surjection; elementary rewriting along a surjection.) Depth: **shallow**. Module: `lean/ToyChecker/Relabel.lean`.

**Plain claim.** If good is invariant under a surjective map pi of programs (in particular the forward map of any bijective relabeling), then a checker c is sound iff c composed with pi is sound; so soundness cannot distinguish a checker from its relabeled twin.

**Lean statement** (namespace `Toy.Checker`):

```lean
theorem sound_comp_iff_of_surjective_of_invariantUnder {P : Type u} {good : P → Prop}
    {π : P → P} (hsurj : Function.Surjective π) (hgood : InvariantUnder π good)
    (c : P → Bool) : Sound good (c ∘ π) ↔ Sound good c
```

Unfolded:

- `sound_comp_iff_of_surjective_of_invariantUnder`: `(∀ q, ∃ p, π p = q) → (∀ s, good (π s) ↔ good s) → ((∀ p, c (π p) = true → good p) ↔ ∀ p, c p = true → good p)`.

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `hsurj : Function.Surjective π` | Used only for the direction from c composed with pi to c (the other direction holds for any pi: sound_comp_of_invariantUnder); a non-surjective pi hides some inputs of c. | tight: counterexample `cex_sound_comp_iff_needs_surjective` |
| `hgood : InvariantUnder π good` | If relabeling changes goodness, soundness can separate c from its relabeled twin. | tight: counterexample `cex_sound_comp_iff_needs_invariant` |

Each tight counterexample is stated in the form "all other hypotheses hold and the conclusion fails" for a concrete instance.

**Non-vacuity witness** (`nonvacuous_sound_comp_iff`). swap02Fun (transpose 0 and 2) is surjective and leaves evenGood invariant.

**Positive control.** `positive_control_anchor_law_separates_relabeled_checker`: `evenGood` is invariant under the surjective transposition `swap02Fun` of `0` and `2`; `(· == 0)` and its relabeled twin `(· == 0) ∘ swap02Fun` are both sound, yet the anchored law with anchor `0` admits the first and excludes the second.

**Prior art.**

- A. Lindenbaum and A. Tarski, 'Über die Beschränktheit der Ausdrucksmittel deduktiver Theorien', Ergebnisse eines mathematischen Kolloquiums 7:15-22, 1936 (English translation 'On the limitations of the means of expression of deductive theories', in A. Tarski, Logic, Semantics, Metamathematics, Oxford University Press, 1956). Notions definable by purely logical means are invariant under every permutation of the domain, hence cannot distinguish an object from its image; the mathematical principle behind the relabeling statements here.
- A. Tarski, 'What are logical notions?' (ed. J. Corcoran), History and Philosophy of Logic 7(2):143-154, 1986, doi:10.1080/01445348608837096. Proposes invariance under all permutations of the domain as the criterion of logicality.
- H. Putnam, Reason, Truth and History, Cambridge University Press, 1981, doi:10.1017/CBO9780511625398, chapter 2 'A problem about reference' and the book's mathematical appendix. Model-theoretic permutation argument: permuting the domain and reinterpreting the non-logical vocabulary accordingly preserves the truth value of every sentence, so truth-value constraints alone do not fix reference. Informal source of the relabeling idea only; there every constant is reinterpreted along with everything else, whereas the anchors here are programs supplied by the framework and fixed outside the relabeling.

**Design question.** Can a law that is invariant under renaming of programs pin down behavior on specific named inputs?

Basis: execution (Lean kernel check): `sound_comp_iff_of_surjective_of_invariantUnder`.

Basis: derived (modeling bridge): If the certified property is invariant under a renaming of program labels (for example alpha-renaming of bound variables in a representation where renaming is a surjective map on program texts), soundness alone cannot distinguish a tool from the same tool run on renamed inputs. Gap: whether a concrete renaming preserves the property depends on the representation; anchors supplied by the framework are not renamed.

### R5c. Relabeling-invariant laws force answers only uniformly along relabelings

Kind: impossibility. Tier: **T1** (Folklore ('a renaming-invariant requirement cannot single out a name') made precise for laws on checkers; the nearest formal source is permutation invariance of logical notions.) Depth: **shallow**. Module: `lean/ToyChecker/Relabel.lean`.

**Plain claim.** Let L be a law on checkers that is invariant under relabeling programs by pi (L (c composed with pi) iff L c, for every checker c). If every checker that L admits gives answer b on program p, then every admitted checker gives b on pi p; and for a bijective relabeling sigma, L forces answer b on sigma p iff it forces b on p. So such a law can force answers on specific programs only uniformly along relabeling orbits.

**Lean statements** (namespace `Toy.Checker`):

```lean
theorem forced_value_relabeled_iff_of_invariantUnder_comp {P : Type u} (σ : Relabeling P)
    {L : Law P} (hL : InvariantUnder (fun c : P → Bool => c ∘ σ.toFun) L) (p : P) (b : Bool) :
    (∀ c, L c → c (σ.toFun p) = b) ↔ (∀ c, L c → c p = b)

theorem forced_value_at_image_of_invariantUnder_comp {P : Type u} {π : P → P} {L : Law P}
    (hL : InvariantUnder (fun c : P → Bool => c ∘ π) L) {p : P} {b : Bool}
    (hp : ∀ c, L c → c p = b) : ∀ c, L c → c (π p) = b
```

Unfolded:

- `forced_value_relabeled_iff_of_invariantUnder_comp`: for `σ : Relabeling P` (a map `σ.toFun` with a two-sided inverse `σ.invFun`), `(∀ c, L (c ∘ σ.toFun) ↔ L c) → ((∀ c, L c → c (σ.toFun p) = b) ↔ (∀ c, L c → c p = b))`.
- `forced_value_at_image_of_invariantUnder_comp`: for an arbitrary `π : P → P`, `(∀ c, L (c ∘ π) ↔ L c) → (∀ c, L c → c p = b) → ∀ c, L c → c (π p) = b`.

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `hL : InvariantUnder (fun c => c ∘ σ.toFun) L (forced_value_relabeled_iff_of_invariantUnder_comp)` | A law that mentions a fixed program (a single anchor) is not invariant and can force an answer at that program but not at its image. | tight: counterexample `cex_forced_value_relabeled_needs_invariant` |
| `σ : Relabeling P (left_inv / injectivity tight; right_inv unused; forced_value_relabeled_iff_of_invariantUnder_comp)` | Needed for the direction from sigma p to p. Only the left-inverse half of the bijection (sigma.left_inv, which makes sigma.toFun injective) is used; sigma.right_inv (surjectivity) is not. Tightness counterexample: for the constant map 0, which is neither injective nor surjective, an invariant law forces an answer at the image of p without forcing it at p. Surjectivity alone does not suffice either (cex_forced_value_relabeled_surjective_not_injective, with the surjective, non-injective map n \|-> n - 2); a left inverse suffices (forced_value_relabeled_iff_of_leftInverse), and classically injectivity suffices (forced_value_relabeled_iff_of_injective). | tight: counterexample `cex_forced_value_relabeled_needs_bijective` |
| `hL : InvariantUnder (fun c => c ∘ π) L (forced_value_at_image_of_invariantUnder_comp)` | As above, for the one-directional statement about an arbitrary map. | tight: counterexample `cex_forced_value_at_image_needs_invariant` |
| `hp : ∀ c, L c → c p = b (forced_value_at_image_of_invariantUnder_comp)` | The answer at p must actually be forced; an invariant law that forces nothing transfers nothing. | tight: counterexample `cex_forced_value_at_image_needs_forced` |

Each tight counterexample is stated in the form "all other hypotheses hold and the conclusion fails" for a concrete instance.

**Non-vacuity witness** (`nonvacuous_forced_value_relabeled`). The anchored law with anchors [0, 2] is invariant under the transposition of 0 and 2, and every checker it admits accepts 0: an invariant law can force an answer outright.

**Positive control.** `cex_forced_value_relabeled_needs_invariant`: the anchored law with the single anchor `0`, which is not invariant under `swap02`, forces acceptance at `0` but not at `swap02.toFun 0 = 2` (the allowlist `[0]` is admitted and rejects `2`).

**Prior art.**

- A. Lindenbaum and A. Tarski, 'Über die Beschränktheit der Ausdrucksmittel deduktiver Theorien', Ergebnisse eines mathematischen Kolloquiums 7:15-22, 1936 (English translation 'On the limitations of the means of expression of deductive theories', in A. Tarski, Logic, Semantics, Metamathematics, Oxford University Press, 1956). Notions definable by purely logical means are invariant under every permutation of the domain, hence cannot distinguish an object from its image; the mathematical principle behind the relabeling statements here.
- A. Tarski, 'What are logical notions?' (ed. J. Corcoran), History and Philosophy of Logic 7(2):143-154, 1986, doi:10.1080/01445348608837096. Proposes invariance under all permutations of the domain as the criterion of logicality.
- H. Putnam, Reason, Truth and History, Cambridge University Press, 1981, doi:10.1017/CBO9780511625398, chapter 2 'A problem about reference' and the book's mathematical appendix. Model-theoretic permutation argument: permuting the domain and reinterpreting the non-logical vocabulary accordingly preserves the truth value of every sentence, so truth-value constraints alone do not fix reference. Informal source of the relabeling idea only; there every constant is reinterpreted along with everything else, whereas the anchors here are programs supplied by the framework and fixed outside the relabeling.

**Design question.** Can a law that is invariant under renaming of programs pin down behavior on specific named inputs?

Basis: execution (Lean kernel check): `forced_value_relabeled_iff_of_invariantUnder_comp`, `forced_value_at_image_of_invariantUnder_comp`.

Basis: derived (modeling bridge): If every admission law of a framework is invariant under a renaming of program labels, the laws can force a verdict on a particular program only by forcing the same verdict on its renamed image. Gap: laws that mention fixed programs supplied by the framework are typically not invariant; the statement covers one relabeling at a time.

### R6a. Satisfiers of 'sound and complete on F' form an interval; the law is always satisfiable

Kind: characterization. Tier: **T0** (Restatement of the interval structure of consistent hypotheses (version space representation) for soundness plus completeness on a fragment, with the classical character of the witness explicit.) Depth: **definitional**. Module: `lean/ToyChecker/RelativeCompleteness.lean`.

**Plain claim.** A checker is sound and complete on fragment F iff it lies, pointwise, between the classical oracle of 'F p and good p' and the classical oracle of good; the lower end is itself sound and complete on F, so in the Boolean-function model the law 'sound and complete on F' is always satisfiable (by a possibly noncomputable function).

**Lean statements** (namespace `Toy.Checker`):

```lean
theorem soundCompleteOn_iff_between {P : Type u} (good F : P → Prop) (c : P → Bool) :
    SoundCompleteOn good F c ↔
      CheckerLE (classicalOracle (fun p => F p ∧ good p)) c ∧
      CheckerLE c (classicalOracle good)

theorem soundCompleteOn_classicalOracle_inter {P : Type u} (good F : P → Prop) :
    SoundCompleteOn good F (classicalOracle (fun p => F p ∧ good p))
```

Unfolded:

- `soundCompleteOn_iff_between`: `(Sound good c ∧ ∀ p, good p → F p → c p = true) ↔ (∀ p, classicalOracle (fun q => F q ∧ good q) p = true → c p = true) ∧ (∀ p, c p = true → classicalOracle good p = true)`; by `classicalOracle_eq_true_iff` the right-hand side is `(∀ p, F p ∧ good p → c p = true) ∧ (∀ p, c p = true → good p)`.
- `soundCompleteOn_classicalOracle_inter`: the checker `p ↦ classicalOracle (fun q => F q ∧ good q) p` (true exactly when `F p ∧ good p`) is sound and complete on `F`.

**Hypothesis ledger.** No hypotheses beyond the universally quantified data.

**Non-vacuity witness** (`nonvacuous_soundCompleteOn`). No hypotheses. In the toy instance the law on p < 10 is satisfied by the computable evenBelowTen and excludes rejectAll, so both sides of the characterization occur.

**Prior art.**

- T. M. Mitchell, Machine Learning, McGraw-Hill, 1997, Chapter 2 (concept learning, the version space representation theorem, and the unbiased learner whose hypothesis space contains every subset of the instances). For that learner the most specific consistent hypothesis is the disjunction of the positive examples and no instance outside the training examples is classified unanimously. Correspondence (our reading): checkers are hypotheses, the pointwise order is the generality order, anchors and suite entries are labeled examples, and soundness acts as a negative example at every bad program (infinitely many in general, unlike a finite training set); the results cited here restate that picture in this vocabulary.
- R. Giacobazzi, F. Ranzato and F. Scozzari, 'Making abstract interpretations complete', Journal of the ACM 47(2):361-416, 2000, doi:10.1145/333979.333989. Completeness of an abstract interpretation (no loss of precision relative to the abstract domain), shown to depend only on the domain. A different, domain-level notion from the per-program relative completeness used here.
- R. Bruni, R. Giacobazzi, R. Gori and F. Ranzato, 'A logic for locally complete abstract interpretations', LICS 2021, pp. 1-13, doi:10.1109/LICS52264.2021.9470608. Local completeness: precision required only on specific inputs rather than globally; the closest abstract-interpretation analogue of completeness relative to a fragment, at the level of abstract domains.
- H. G. Rice, 'Classes of recursively enumerable sets and their decision problems', Transactions of the American Mathematical Society 74(2):358-366, 1953, doi:10.1090/S0002-9947-1953-0053041-6. Rice's theorem: a class of recursively enumerable sets has a decidable index set only if it is trivial. Context only; not formalized here.

**Design question.** When a framework requires soundness plus completeness on a fragment, when is the law satisfiable, when does it lock out the do-nothing tool or all lookup tables, and what does 'decidable' mean in the model?

Basis: execution (Lean kernel check): `soundCompleteOn_iff_between`, `soundCompleteOn_classicalOracle_inter`.

Basis: derived (modeling bridge): A framework requirement "sound, and complete on a fragment F" is always met by some Boolean function; whether it is met by an implementable tool is a separate question (R6c). Gap: computability is not represented in the model.

### R6c. 'Sound and complete on F' is 'sound and decides good on F', relative to a class K

Kind: characterization. Tier: **T1** (The pointwise and class forms are elementary restatements (T0 taken alone); the closure condition under which the soundness requirement can be dropped, which locates exactly where the counterexample R6h stops applying, is folklore made precise with no source found stating it in this form, so the card as a whole is T1.) Depth: **shallow**. Module: `lean/ToyChecker/RelativeCompleteness.lean`.

**Plain claim.** A checker is sound and complete on F iff the same checker is sound everywhere and decides good on F; hence, for any class K of admissible checkers, the law has a satisfier in K iff some checker in K is sound and decides good on F. For F = all programs, a checker satisfies the law iff it decides good, so the law has a satisfier in K iff good is decided by some checker in K. If K is closed under pointwise and (AndClosed K) and contains a decider for F (DecidedIn K F), the soundness requirement can be dropped: the law has a satisfier in K iff some checker in K decides good on F.

**Lean statements** (namespace `Toy.Checker`):

```lean
theorem soundCompleteOn_iff_sound_and_decides_on {P : Type u} (good F : P → Prop)
    (c : P → Bool) :
    SoundCompleteOn good F c ↔ Sound good c ∧ ∀ p, F p → (c p = true ↔ good p)

theorem exists_soundCompleteOn_in_class_iff {P : Type u} (good F : P → Prop)
    (K : (P → Bool) → Prop) :
    (∃ c, K c ∧ SoundCompleteOn good F c) ↔
      ∃ c, K c ∧ Sound good c ∧ ∀ p, F p → (c p = true ↔ good p)

theorem soundCompleteOn_univ_iff_decides {P : Type u} (good : P → Prop) (c : P → Bool) :
    SoundCompleteOn good (fun _ => True) c ↔ ∀ p, c p = true ↔ good p

theorem exists_soundCompleteOn_univ_in_class_iff {P : Type u} (good : P → Prop)
    (K : (P → Bool) → Prop) :
    (∃ c, K c ∧ SoundCompleteOn good (fun _ => True) c) ↔
      ∃ c, K c ∧ ∀ p, c p = true ↔ good p

theorem exists_soundCompleteOn_in_class_iff_decides_on_of_andClosed_of_decidedIn
    {P : Type u} (good F : P → Prop) (K : (P → Bool) → Prop)
    (hK : AndClosed K) (hF : DecidedIn K F) :
    (∃ c, K c ∧ SoundCompleteOn good F c) ↔ ∃ c, K c ∧ ∀ p, F p → (c p = true ↔ good p)
```

Unfolded:

- `soundCompleteOn_iff_sound_and_decides_on`: `(Sound good c ∧ ∀ p, good p → F p → c p = true) ↔ Sound good c ∧ ∀ p, F p → (c p = true ↔ good p)`.
- `exists_soundCompleteOn_in_class_iff`: the same equivalence under `∃ c, K c ∧ _`.
- `soundCompleteOn_univ_iff_decides` / `exists_soundCompleteOn_univ_in_class_iff`: for `F = fun _ => True`, `SoundCompleteOn good F c ↔ ∀ p, c p = true ↔ good p`, and its form under `∃ c, K c ∧ _`.
- `exists_soundCompleteOn_in_class_iff_decides_on_of_andClosed_of_decidedIn`: assuming `AndClosed K := ∀ c₁ c₂, K c₁ → K c₂ → K (fun p => c₁ p && c₂ p)` and `DecidedIn K F := ∃ d, K d ∧ ∀ p, d p = true ↔ F p`, `(∃ c, K c ∧ SoundCompleteOn good F c) ↔ ∃ c, K c ∧ ∀ p, F p → (c p = true ↔ good p)`.

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `hK : AndClosed K (exists_soundCompleteOn_in_class_iff_decides_on_of_andClosed_of_decidedIn)` | Restricting a checker that decides good on F to F (by and-ing it with a decider of F) must stay in K. | tight: counterexample `cex_decides_on_iff_needs_andClosed` |
| `hF : DecidedIn K F (exists_soundCompleteOn_in_class_iff_decides_on_of_andClosed_of_decidedIn)` | Restriction to F needs a decider of F inside K; without one the soundness requirement cannot be dropped (R6h). | tight: counterexample `cex_decides_on_iff_needs_decidedIn` |

Each tight counterexample is stated in the form "all other hypotheses hold and the conclusion fails" for a concrete instance.

**Non-vacuity witness** (`nonvacuous_soundCompleteOn_iff_sound_and_decides_on`, `nonvacuous_soundCompleteOn_univ_iff_decides`, `nonvacuous_exists_soundCompleteOn_in_class_iff_decides_on`). On the proper fragment p < 10 the right-hand sides hold for evenBelowTen (which rejects the good program 10 outside the fragment) and fail for rejectAll, and correspondingly for the classes {evenBelowTen} and {rejectAll}; on all programs they hold for evenExact and fail for evenBelowTen; the class of all checkers is closed under and and decides p < 10. The class of all checkers already contains a sound decider of good on F, so the last witness does not exercise the repair step of the closure statement (and-ing an unsound decider with a decider of F). That step is exercised by the four-element class {rejectAll, belowTwo, zeroOrLarge, (· == 0)}: it is closed under and, decides p < 2, contains zeroOrLarge, which decides p = 0 on p < 2 but is unsound, and belowTwo && zeroOrLarge = (· == 0) is a member that is sound and complete on p < 2 (andClosed_class_repairs_unsound_decider_example). In the two-element class {rejectAll, belowTwo}, also closed under and and deciding p < 2, both sides of the closure statement are false for good = (p = 0) (andClosed_class_both_sides_false_example).

**Prior art.**

- H. G. Rice, 'Classes of recursively enumerable sets and their decision problems', Transactions of the American Mathematical Society 74(2):358-366, 1953, doi:10.1090/S0002-9947-1953-0053041-6. Rice's theorem: a class of recursively enumerable sets has a decidable index set only if it is trivial. Context only; not formalized here.
- The mathlib Community, 'The Lean mathematical library', CPP 2020, pp. 367-381, doi:10.1145/3372885.3373824. General reference for the Lean mathematical library, described there for Lean 3. It mentions a library on computability theory that proves the undecidability of the halting problem and cites Carneiro (ITP 2019, next entry) for it; it does not mention Rice's theorem or the declaration ComputablePred.rice₂ cited below (checked against its arXiv version, arXiv:1910.09336).
- M. Carneiro, 'Formalizing computability theory via partial recursive functions', 10th International Conference on Interactive Theorem Proving (ITP 2019), LIPIcs 141, 12:1-12:17, 2019, doi:10.4230/LIPIcs.ITP.2019.12 (arXiv version arXiv:1810.08380). Describes that computability library (Lean 3 mathlib); the arXiv version states Rice's theorem for partial recursive functions and their codes as Theorem 6 (rice).
- Mathlib 4, repository leanprover-community/mathlib4, commit bbb39fe579406d36e4aacdc6d49a0055e4cf0d75, file Mathlib/Computability/Halting.lean, lines 42-43 (namespace ComputablePred): theorem rice₂ (C : Set Code) (H : ∀ cf cg, eval cf = eval cg → (cf ∈ C ↔ cg ∈ C)) : (ComputablePred fun c => c ∈ C) ↔ C = ∅ ∨ C = Set.univ. A mechanized Rice's theorem for codes of partial recursive functions, with semantic extensionality (codes computing the same partial function are treated alike) as hypothesis. Background for the outside-the-package remark on R6c's full-fragment form (see the non-claims); this package does not use Mathlib.
- R. Bruni, R. Giacobazzi, R. Gori and F. Ranzato, 'A logic for locally complete abstract interpretations', LICS 2021, pp. 1-13, doi:10.1109/LICS52264.2021.9470608. Local completeness: precision required only on specific inputs rather than globally; the closest abstract-interpretation analogue of completeness relative to a fragment, at the level of abstract domains.
- M. Campion, M. Dalla Preda, R. Giacobazzi and C. Urban, 'Monotonicity and the precision of program analysis', Proceedings of the ACM on Programming Languages 8(POPL):1629-1662, 2024, doi:10.1145/3632897. Identifies a class of programs (monotone ones) that admit complete abstract interpretation over a class of numerical domains: completeness restricted to a program fragment, at the level of abstract domains.

**Design question.** When a framework requires soundness plus completeness on a fragment, when is the law satisfiable, when does it lock out the do-nothing tool or all lookup tables, and what does 'decidable' mean in the model?

Basis: execution (Lean kernel check): `soundCompleteOn_iff_sound_and_decides_on`, `exists_soundCompleteOn_in_class_iff`, `soundCompleteOn_univ_iff_decides`, `exists_soundCompleteOn_univ_in_class_iff`, `exists_soundCompleteOn_in_class_iff_decides_on_of_andClosed_of_decidedIn`.

Basis: derived (modeling bridge): Whether "sound and complete on F" admits an implementable tool is whether some implementable tool is sound and decides the property on F; when membership in F is itself decidable by an admissible tool and admissible tools are closed under conjunction, this is whether the property is decidable on F. Gap: the class of computable checkers is not defined here, so the package neither proves nor refutes that an implementable tool satisfies the law; the remark on Rice's theorem in the non-claims is background from outside the package, not a result of it.

### R6e. 'Sound and complete on F' excludes reject-all iff F contains a good program

Kind: characterization. Tier: **T0** (Elementary: rejectAll is sound (textbook), and it is complete on F exactly when F has no good program.) Depth: **shallow**. Module: `lean/ToyChecker/RelativeCompleteness.lean`.

**Plain claim.** The law 'sound and complete on F' excludes rejectAll iff F contains at least one good program.

**Lean statement** (namespace `Toy.Checker`):

```lean
theorem not_soundCompleteOn_rejectAll_iff {P : Type u} (good F : P → Prop) :
    ¬ SoundCompleteOn good F rejectAll ↔ ∃ p, F p ∧ good p
```

Unfolded:

- `not_soundCompleteOn_rejectAll_iff`: `¬ (Sound good (fun _ => false) ∧ ∀ p, good p → F p → false = true) ↔ ∃ p, F p ∧ good p`.

**Hypothesis ledger.** No hypotheses beyond the universally quantified data.

**Non-vacuity witness** (`nonvacuous_not_soundCompleteOn_rejectAll_iff`). No hypotheses. Both sides occur: on p < 10 there is a good program; on the fragment p = 1 there is none and rejectAll is admitted.

**Prior art.**

- X. Rival and K. Yi, Introduction to Static Analysis: An Abstract Interpretation Perspective, MIT Press, 2020, Chapter 1. Defines soundness (answer true implies the property) and completeness (the property implies answer true) of a yes/no analysis as here (Sound; CompleteOn with F = all programs), and notes that the analysis answering false everywhere is trivially sound and the one answering true everywhere trivially complete.

**Design question.** When a framework requires soundness plus completeness on a fragment, when is the law satisfiable, when does it lock out the do-nothing tool or all lookup tables, and what does 'decidable' mean in the model?

Basis: execution (Lean kernel check): `not_soundCompleteOn_rejectAll_iff`.

Basis: derived (modeling bridge): Requiring completeness on a fragment locks out the do-nothing tool exactly when the fragment contains a good program. Gap: none beyond the model's.

### R6f. When an allowlist is sound and complete on F

Kind: characterization. Tier: **T0** (Elementary set reading: the accepted set of the allowlist is A, so soundness is A ⊆ good and completeness on F is good ∩ F ⊆ A.) Depth: **definitional**. Module: `lean/ToyChecker/RelativeCompleteness.lean`.

**Plain claim.** The allowlist of A is sound and complete on F iff every member of A is good and every good program in F is a member of A.

**Lean statement** (namespace `Toy.Checker`):

```lean
theorem soundCompleteOn_allowlist_iff {P : Type u} [DecidableEq P] (good F : P → Prop)
    (A : List P) :
    SoundCompleteOn good F (allowlist A) ↔
      (∀ a ∈ A, good a) ∧ ∀ p, F p → good p → p ∈ A
```

Unfolded:

- `soundCompleteOn_allowlist_iff`: `((∀ p, decide (p ∈ A) = true → good p) ∧ ∀ p, good p → F p → decide (p ∈ A) = true) ↔ (∀ a ∈ A, good a) ∧ ∀ p, F p → good p → p ∈ A`.

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `[DecidableEq P]` | Needed only to define the allowlist; it does not depend on the instance. | harmless |

**Non-vacuity witness** (`nonvacuous_soundCompleteOn_allowlist_iff`). On the fragment p < 10 for evenGood the right-hand side holds for [0, 2, 4, 6, 8] and fails for [0, 2, 4, 6].

**Prior art.**

- T. M. Mitchell, Machine Learning, McGraw-Hill, 1997, Chapter 2 (concept learning, the version space representation theorem, and the unbiased learner whose hypothesis space contains every subset of the instances). For that learner the most specific consistent hypothesis is the disjunction of the positive examples and no instance outside the training examples is classified unanimously. Correspondence (our reading): checkers are hypotheses, the pointwise order is the generality order, anchors and suite entries are labeled examples, and soundness acts as a negative example at every bad program (infinitely many in general, unlike a finite training set); the results cited here restate that picture in this vocabulary.

**Design question.** When a framework requires soundness plus completeness on a fragment, when is the law satisfiable, when does it lock out the do-nothing tool or all lookup tables, and what does 'decidable' mean in the model?

Basis: execution (Lean kernel check): `soundCompleteOn_allowlist_iff`.

Basis: derived (modeling bridge): A memorizing tool meets "sound and complete on F" exactly when it lists only good programs and lists every good program of F; this is possible only when F contains finitely many good programs. Gap: only allowlists are classified.

### R6g. No allowlist is sound and complete for evenGood on all programs

Kind: impossibility. Tier: **T0** (Concrete instance of R6f: there are infinitely many even numbers.) Depth: **shallow**. Module: `lean/ToyChecker/RelativeCompleteness.lean`.

**Plain claim.** In the toy instance, no allowlist (finite list of programs) is sound and complete for evenGood on all programs.

**Lean statement** (namespace `Toy.Checker`):

```lean
theorem no_allowlist_soundCompleteOn_evenGood_univ (A : List Nat) :
    ¬ SoundCompleteOn evenGood (fun _ => True) (allowlist A)
```

Unfolded:

- `no_allowlist_soundCompleteOn_evenGood_univ`: for every `A : List Nat`, `¬ ((∀ p, decide (p ∈ A) = true → p % 2 = 0) ∧ ∀ p, p % 2 = 0 → True → decide (p ∈ A) = true)`.

**Hypothesis ledger.** No hypotheses beyond the universally quantified data.

**Non-vacuity witness** (`nonvacuous_no_allowlist_soundCompleteOn_evenGood_univ`). The law 'sound and complete for evenGood on all programs' is satisfied by evenExact, so excluding every allowlist is not an artifact of an unsatisfiable law.

**Positive control.** `positive_control_allowlist_soundCompleteOn_finite_fragment`: on the finite fragment `n < 10`, the allowlist `[0, 2, 4, 6, 8]` is sound and complete for `evenGood`.

**Prior art.**

- N. Block, 'Psychologism and Behaviorism', The Philosophical Review 90(1):5-43, 1981, doi:10.2307/2184371. The lookup-table thought experiment: a system that reproduces any finite stretch of required behavior by table lookup, used to argue that behavioral tests alone cannot certify how behavior is produced. Philosophical background only; no formal statement there corresponds to these theorems.

**Design question.** When a framework requires soundness plus completeness on a fragment, when is the law satisfiable, when does it lock out the do-nothing tool or all lookup tables, and what does 'decidable' mean in the model?

Basis: execution (Lean kernel check): `no_allowlist_soundCompleteOn_evenGood_univ`.

Basis: derived (modeling bridge): Requiring completeness on a fragment with infinitely many good programs excludes every memorizing tool, illustrated for the even numbers. Gap: proved for the toy instance only; the general statement follows from R6f but is not separately stated.

### R6h. Deciding good on F inside K does not suffice without soundness

Kind: counterexample. Tier: **T1** (Counterexample to a tempting simplification of R6c ('satisfiable in K iff good restricted to F is K-decidable').) Depth: **definitional**. Module: `lean/ToyChecker/RelativeCompleteness.lean`.

**Plain claim.** 'good restricted to F is decided by some checker in K' does not imply that the law 'sound and complete on F' has a satisfier in K: with K = {acceptAll} and good = F = (p = 0), acceptAll decides good on F but is unsound off F.

**Lean statement** (namespace `Toy.Checker`):

```lean
theorem cex_decides_on_fragment_without_soundness :
    (∃ c, (fun c => c = (acceptAll : Nat → Bool)) c ∧
      ∀ p, (fun n => n = 0) p → (c p = true ↔ (fun n => n = 0) p)) ∧
    ¬ ∃ c, (fun c => c = (acceptAll : Nat → Bool)) c ∧
      SoundCompleteOn (fun n => n = 0) (fun n => n = 0) c
```

Unfolded:

- `cex_decides_on_fragment_without_soundness`: `(∃ c, c = (fun _ => true) ∧ ∀ p, p = 0 → (c p = true ↔ p = 0)) ∧ ¬ ∃ c, c = (fun _ => true) ∧ SoundCompleteOn (· = 0) (· = 0) c`.

**Hypothesis ledger.** None: a closed statement about a concrete instance.

**Non-vacuity witness** (`cex_decides_on_fragment_without_soundness`). It is itself a concrete instance.

**Prior art.**

- H. G. Rice, 'Classes of recursively enumerable sets and their decision problems', Transactions of the American Mathematical Society 74(2):358-366, 1953, doi:10.1090/S0002-9947-1953-0053041-6. Rice's theorem: a class of recursively enumerable sets has a decidable index set only if it is trivial. Context only; not formalized here.

**Design question.** When a framework requires soundness plus completeness on a fragment, when is the law satisfiable, when does it lock out the do-nothing tool or all lookup tables, and what does 'decidable' mean in the model?

Basis: execution (Lean kernel check): `cex_decides_on_fragment_without_soundness`.

Basis: derived (modeling bridge): Knowing that the property is decidable on the fragment by some admissible tool is not enough for admission under "sound and complete on F" when the admissible tools cannot be restricted to F. Gap: the class used is a one-element toy class.

## Boundaries

### Non-claims

Package-wide non-claims, which take precedence over any reading of a card:

1. **Extensional laws do not see implementations.** A law that depends only on a tool's answers cannot separate an honest analyzer from a wrapper or lookup table with the same answers on every program (R3a), and every law stated on Boolean checkers is of this kind. This does *not* say behavioral laws are useless: they constrain behavior, and suitable behavioral laws exclude every finite table (completeness on an infinite fragment, R6g; the relational law `ClosedUnderDoubling` with one anchor, `doubling_law_admits_fourOrTwo_excludes_every_allowlist`). Intensional checks (source inspection, build provenance) are outside the model.
2. **Anchors and finite suites force only what they list.** The anchored law forces acceptance exactly on the anchors and rejection exactly on bad programs (R2c); a lookup table passes every finite suite that some sound checker passes (R2f). Suites chosen after the tool, randomized or held-out testing, and testing hypotheses on the implementation under test are not modeled; nothing here says testing is useless.
3. **Certificates transfer soundness, not completeness.** In one-sided certification a sound verifier makes every tool sound (R4a, R4b), but completeness needs the tool to find certificates that exist in the verifier's language (R4c), and a sound and complete verifier does not supply it (R4d). Completeness on a fragment `F` is obtained only with two-sided certification and a law that every answer on `F` carry checked evidence (R4f), and even then it is forced by that law, not inherited from the verifiers; outside `F` nothing is required. Certificates do not exclude lookup tables: a table that caches valid certificates has exactly the output of an honest bounded tool (`cachedCertTool_eq_boundedHonestTool`), and at the level of Boolean behavior one-sided certification admits exactly the checkers sound for certifiability (R4e).
4. **Renaming invariance is about one map at a time and about laws that are invariant.** R5b covers only the soundness law; R5c covers laws invariant under precomposition with one given map, and says that such a law can force an answer at `p` only by forcing it at the image of `p`, not that it cannot force answers at all (it can: anchors `[0, 2]` under the swap of `0` and `2` force acceptance of `0`). Anchors supplied by the framework are fixed outside the relabeling; if a tool could choose the encoding of programs the positive controls would not apply. Neither result formalizes the Lindenbaum-Tarski theorem or Putnam's permutation argument.
5. **Satisfiable is not implementable.** "Sound and complete on `F`" always has a satisfier (R6a), but in general a noncomputable one. Computability is not defined in this package, so no theorem here establishes or refutes that a law has an implementable (computable) satisfier; in particular the package neither proves nor refutes that, for every property `good` and fragment `F`, some implementable tool is sound and complete on `F`. R6c relativizes to an arbitrary class `K` of admissible checkers and proves no decidability or undecidability result. Every mention of Rice's theorem in the cards (H. G. Rice, 1953, listed under Evidence) refers to background from outside this package, not to a result of it; no theorem here states or depends on it.
6. **Model limits.** Only total Boolean checkers; no time, divergence, or nondeterminism; classical logic throughout (several proofs use `Classical.choice`, recorded per theorem under Evidence); certifying polarity only; parity on `Nat` is a stand-in property and the results stated for it are illustrations.

Per-result non-claims (verbatim from the machine-readable cards):

- **R1a.**
  - The oracle is a mathematical function, in general not computable; nothing says an implementable tool attains the top of this down-set. For decidable good the oracle equals fun p => decide (good p) (classicalOracle_eq_decide); nothing more is claimed about decidability.
  - Uses classical logic (Classical.choice via the oracle's definition).
  - Does not say soundness is upward closed (it is not: rejectAll <= acceptAll), nor that a more conservative checker is preferable; conservativeness costs completeness, which is not measured here.
  - Only binary (hence finite) disjunctions are covered; arbitrary unions of sound checkers are not stated (in the classical model they are also sound, but that is not a theorem of this package).
  - Closure under or needs both checkers to be sound for the same predicate good. Combining real tools that assume different language dialects, memory models or undefined-behavior conventions and accepting when either accepts is sound only for the disjunction of their predicates, not for either stricter one.
  - Polarity: Sound models tools whose true answer certifies goodness. For bug finders that promise no false alarms (every reported problem is real), the guarantee is the dual one, c p = false implies not good p; the order is reversed and the degenerate tool is acceptAll (report nothing), not rejectAll. Nothing here is stated for that polarity.
  - Says nothing about completeness, running time, or termination of any tool.
- **R1e.**
  - Does not say no law can exclude rejectAll: laws not implied by soundness (anchors, completeness on a fragment, checked two-sided answers) can (positive control; R2a, R6e, R4f).
  - Does not say that excluding rejectAll requires excluding an honest tool: the law fun c => c ≠ rejectAll excludes rejectAll and no other checker.
  - Stated for the certifying polarity; for bug finders that promise no false alarms the degenerate tool is acceptAll (see R1a).
  - Says nothing about intensional evidence (source inspection) or about laws on richer outputs such as certificates (R4).
- **R2a.**
  - If some anchor is bad, the law excludes every checker, so 'excludes rejectAll' is then vacuous; that the law admits anything needs good anchors (second statement).
  - Excluding rejectAll does not exclude near-trivial tools: the allowlist of the anchors is admitted (second statement; R2c).
  - Does not say the allowlist is the only admitted checker, nor that an allowlist is an acceptable tool for a framework; it says the anchored law cannot tell it apart from honest tools.
- **R2c.**
  - Concerns acceptance forced by the anchored law alone. Laws with further requirements can force more: completeness on a fragment (R6f), or a relational requirement linking answers on different programs, such as 'accepting p forces accepting 2 * p', which with the single anchor 2 forces infinitely many acceptances and excludes every allowlist while admitting a conservative, incomplete checker (doubling_law_admits_fourOrTwo_excludes_every_allowlist).
  - The anchored law is a pointwise law on finitely many inputs; nothing here is claimed for relational or metamorphic laws beyond the single example cited above.
  - Does not say an admitted checker can be found algorithmically; the witness for a good p is the allowlist of p :: A, which presupposes knowing that p is good.
  - The first two statements have no DecidableEq P hypothesis; their proofs build the witness allowlists with classical decidable equality (Classical.choice), and the forced-acceptance statement, quantified over all types, implies double-negation elimination, so it is not constructive. With a DecidableEq P instance the witnesses are the computable allowlists of the third statement.
  - Exhibits two admitted checkers for each good non-anchor; does not enumerate all admitted checkers, and does not quantify how many anchors are needed for any practical purpose.
- **R2f.**
  - The table is built from T: the theorem is about a suite fixed before the table is chosen. It does not say a single table passes every suite, nor that a table fixed in advance passes suites chosen afterwards (held-out or randomized tests are not modeled).
  - Does not say tests are useless. Nearby laws exclude lookup tables while admitting honest tools: completeness on an infinite fragment (first positive control; R6g), and, without any completeness requirement, the relational law 'passes [(2, true)] and accepting p forces accepting 2 * p', which admits the conservative, incomplete checker fourOrTwo and excludes the lookup table of every finite suite (second positive control).
  - The impossibility concerns only laws of the form 'sound and passes T', which are pointwise laws on finitely many inputs.
  - Says nothing about intensional checks (code inspection) that could detect a table. Conclusions about untested inputs from finite testing need hypotheses on the implementation under test (as in the testing literature cited); none is assumed here.
- **R3a.**
  - Definitional: the first statement is the definition of extensionality read in both directions, the second is function extensionality (a theorem in Lean, derived from Quot.sound; in a setting without it the statement would have to be assumed), the third instantiates the first. The value is in naming the barrier, not in depth.
  - Intensional laws, i.e. predicates on the implementation itself (source inspection, build provenance; here IsStructural), are outside the barrier and can separate such implementations (positive control). Requiring richer output, such as a certificate with each answer, is not intensional: the barrier applies again to the richer behavior, and a lookup table that stores precomputed valid certificates has the same certified output as an honest tool on the same finite set (cachedCertTool_eq_boundedHonestTool; R4e).
  - The toy instance concerns two implementations that accept the same finite set. An honest checker that accepts infinitely many programs has no finite table with the same behavior, and extensional laws can separate it from every finite table (R6g; the positive controls of R2f).
  - Not Rice's theorem, and a different notion of extensionality: ExtensionalLaw is extensionality at the level of tools (two implementations give the same answer on every program), not semantic extensionality of target programs (a property of programs that depends only on the function a program computes). A law on tools may distinguish two semantically equivalent programs. Nothing about decidability is stated or used.
  - Does not say behavioral laws are useless; they constrain behavior, just not implementation.
- **R4a.**
  - Does not transfer completeness (R4c, R4d). With two-sided certification and a requirement of checked answers on a fragment, completeness on that fragment is forced (R4f).
  - Assumes the framework, not the tool, runs V on each output; a tool that reports 'accepted' without its certificate being checked is outside the model.
  - certChecker V t passes the original program p itself to V. In an implementation, if the untrusted tool can alter the program, or supply a certificate for a transformed representation that V does not relate back to p, soundness can fail; any parser or verification-condition generator that maps p to proof obligations belongs to V and hence to the trusted base.
  - Rules out unsound tools without inspecting their internals, but does not rule out lookup tables: a table that stores precomputed valid certificates for finitely many programs induces a sound checker and has the same output as an honest tool on the same finite set (cachedCertTool_eq_boundedHonestTool).
  - Says nothing about the cost of checking or of finding certificates.
- **R4b.**
  - Quantifies over all tools t : P -> Option W; for a restricted family of tools the converse may fail.
  - The witness tool is constant; no claim is made about which realistic tools expose an unsound verifier.
- **R4c.**
  - Completeness is a property of neither the tool alone nor the verifier alone: it needs certificates to exist in V's language for every good program of F (second statement; with rejectAllV no tool succeeds, no_tool_completeOn_rejectAllV) and the tool to find them; verifier completeness alone does not suffice (R4d).
  - Concerns one-sided certification, in which a rejection needs no evidence. Under two-sided certification with checked answers required on F, a tool that rejects a good program of F is excluded instead (R4f).
  - Does not say certificates are efficiently findable.
- **R4d.**
  - Does not say certifying designs are weak: with one-sided certification completeness must be required of the tool separately (R4c, R6). With two-sided certification and checked answers required on a fragment, the silent tool is excluded (it cannot refute good programs) and admitted tools are complete on that fragment (R4f).
  - The silent tool is the certifying analogue of rejectAll; the counterexample concerns a law that checks certificates only when they are offered.
- **R4e.**
  - The V-certifiability predicate is not in general a different predicate from good: it equals good when V is sound and complete for good (certifiable_eq_good_of_verifierSound_of_verifierComplete; for halfV it is evenGood, halfV_certifiable_eq_evenGood), and it implies good when V is sound (certifiable_imp_good_of_verifierSound), strictly so when V is incomplete.
  - Certificates do not escape R1 or R3 at the level of Boolean behavior; their benefit is that the evidence is checked per run by a fixed trusted V, which changes what the tool must output.
  - In particular, allowlist-like tools are induced by certifying tools whenever their accepted programs have certificates: a table caching valid certificates (cachedCertTool) has the same output as an honest bounded tool (cachedCertTool_eq_boundedHonestTool).
  - Concerns one-sided certification only; the Boolean image of two-sided certification (R4f) is not characterized here.
  - The right-to-left direction uses choice to pick certificates; it says nothing about computing them.
- **R4f.**
  - Completeness on F is not transferred from the verifiers: it is forced by the law that every answer on F carry checked evidence. A tool that cannot produce such evidence for some program of F is excluded by that law (not_twoSidedVerifiedOn_example_silent), so the law admits some tool only if certificates exist for the good programs of F and refutations for the bad ones.
  - Outside F nothing is required; the induced checker is still sound there (it accepts only certified verdicts) but need not be complete.
  - Does not model tools that decline to answer or time out on F; a framework that tolerates unverified answers on F is back in the one-sided situation of R4c and R4d.
  - Says nothing about the cost of producing evidence, or about which predicates admit verifier pairs with evidence for every program of F.
- **R5b.**
  - Only the soundness law is covered; other laws (anchors) can separate a checker from its relabeling (positive control).
  - The anchor positive control works because the framework supplies the anchor program 0 itself, fixed outside the relabeling. If a tool could choose how programs are encoded, a relabeling would move the anchors as well, and the anchored law would not separate the twins.
  - Says nothing about relabelings that change goodness.
  - Not a formalization of the permutation-invariance theorem of Lindenbaum and Tarski or of Putnam's permutation argument; it states only the elementary invariance fact for the soundness law.
- **R5c.**
  - Does not say an invariant law cannot pin down behavior on specific programs: it can force an answer at p outright, e.g. at a fixed point of the relabeling or by constraining the whole orbit of p (nonvacuity witness: anchors [0, 2] under the swap of 0 and 2 force acceptance of 0). It only cannot force an answer at p without forcing the same answer at pi p.
  - Bijectivity of sigma is more than the proof uses: only sigma.left_inv is used, never sigma.right_inv. The equivalence also holds for any map with a left inverse (forced_value_relabeled_iff_of_leftInverse) and, classically, for any injective map (forced_value_relabeled_iff_of_injective); it fails for some surjective, non-injective maps (cex_forced_value_relabeled_surjective_not_injective). The statement takes a Relabeling because relabelings of programs are bijections and orbits are defined through them; the tightness counterexample for the hypothesis sigma : Relabeling P removes injectivity, and no claim is made that injectivity is necessary for every law.
  - Concerns invariance under one given relabeling; invariance under a group of relabelings gives the statement for each element of the group, which is not separately stated.
  - Laws that mention fixed programs (anchors) are typically not invariant; they single out p because the framework supplies p itself, fixed outside the relabeling (see R5b).
  - Not a formalization of the Lindenbaum-Tarski theorem or of Putnam's permutation argument.
- **R6a.**
  - Satisfiability here is not implementability: the witness is defined by excluded middle and is in general not computable. Lean's logic does not see computability, so this does not contradict Rice-style undecidability.
  - For decidable F and good the witness equals fun p => decide (F p ∧ good p) (classicalOracle_eq_decide).
  - Describes the set of satisfiers in the Boolean-function model only; which of them are implementable is not addressed (R6c relativizes to a class K).
  - Uses classical logic.
- **R6c.**
  - K is arbitrary and left abstract; the computable functions are the intended example but are not defined here, so no undecidability result follows.
  - The soundness conjunct cannot be dropped in general (R6h, with K = {acceptAll}); it can be dropped under the stated closure conditions. That natural classes such as computable or polynomial-time checkers are closed under and is an informal remark; those classes are not defined here.
  - The closure statement's non-vacuity witness with K = all checkers is degenerate in one respect: that class already contains a sound decider, so the soundness repair (restricting an unsound decider of good on F to F with the decider of F) is not needed there. Restricted classes that do need the repair, and one where both sides fail, are proved separately (andClosed_class_repairs_unsound_decider_example, andClosed_class_both_sides_false_example); neither is a further hypothesis of the theorem.
  - Background from outside this package, not a result of it: if P were program texts of a Turing-complete language, K the computable checkers, and good a nontrivial property of the partial function a program computes, Rice's theorem (H. G. Rice 1953, listed under prior art) would make the full-fragment right-hand side false, so the law on all programs would have no computable satisfier. None of this is formalized or proved here: the package defines neither program texts nor computability, and it neither proves nor refutes the general claim that every property and fragment admit an implementable (computable) checker that is sound and complete on that fragment. The remark also leaves the standard alternatives open: properties that are not semantic (e.g. syntactic or type-structural ones) may be decidable; restricting completeness to a fragment F that is decided in K reduces the question to deciding good on F (closure statement); and procedures that may diverge are outside this model of total checkers P -> Bool.
  - The pointwise forms keep the witness (the same checker witnesses both sides); the class forms are their existential consequences.
- **R6e.**
  - Excluding rejectAll does not exclude lookup tables when F has finitely many good programs (R6f; positive control of R6g).
  - The left-to-right direction is classical: quantified over all types, the statement implies double-negation elimination, so it cannot be proved by unfolding definitions alone.
- **R6f.**
  - Concerns allowlists only; other degenerate tools are not classified.
  - When F contains infinitely many good programs no allowlist satisfies the law; R6g gives a concrete instance, and the general statement is not separately stated.
- **R6g.**
  - Proved only for evenGood on all programs; the general statement (an allowlist satisfies the law iff F has finitely many good programs, all listed) follows from R6f but is not separately stated.
  - Excludes finite tables only; an infinite 'table' is just an arbitrary function and is not excluded (R6a).
  - Completeness on an infinite fragment is one way to exclude every finite table, not the only one: a relational law with a single anchor ('accepting p forces accepting 2 * p') also excludes every allowlist while admitting a conservative, incomplete checker (doubling_law_admits_fourOrTwo_excludes_every_allowlist).
- **R6h.**
  - The class used does not contain a decider for F. For classes closed under pointwise and that do contain one, the simplification holds (R6c, closure statement; this counterexample is its tightness witness for that hypothesis, cex_decides_on_iff_needs_decidedIn).

### Escape hatches of the impossibility results

- **R1e** (soundness-implied laws admit `rejectAll`): any law not implied by soundness can exclude `rejectAll`, e.g. a nonempty anchor list (R2a), completeness on a fragment containing a good program (R6e), or checked two-sided answers (R4f); `fun c => c ≠ rejectAll` excludes exactly `rejectAll`.
- **R2f** (lookup tables pass finite suites): drop the restriction to pointwise laws on finitely many inputs. Completeness on an infinite fragment, or a relational law linking answers on different programs, excludes every table while admitting honest tools (both positive controls). Suites chosen after the table are outside the statement.
- **R3a** (extensional laws cannot separate behaviorally identical implementations): intensional laws (`IsStructural`) can; and implementations that differ on even one program can be separated by an extensional law (`cex_extensionalLaw_iff_needs_same_behavior`).
- **R5b** (soundness cannot see relabeling): fails without surjectivity (`cex_sound_comp_iff_needs_surjective`) or when `good` is not invariant (`cex_sound_comp_iff_needs_invariant`); laws that mention framework-supplied programs, such as anchors, can separate a checker from its relabeled twin.
- **R5c** (invariant laws force answers only uniformly): fails for laws that are not invariant (single anchor) and, for the converse direction, for maps without a left inverse (constant map; also the surjective, non-injective map `n ↦ n - 2`, `cex_forced_value_relabeled_surjective_not_injective`).
- **R6g** (no allowlist on all programs): on a fragment with finitely many good programs an allowlist can be sound and complete (`positive_control_allowlist_soundCompleteOn_finite_fragment`; R6f in general).

### Tightness status `unknown`

None. Every hypothesis of every main statement is either `tight`, with a proved counterexample, or `harmless`; the `harmless` ones are the four `[DecidableEq P]` instance arguments, which are needed only to define allowlists or lookup tables as Boolean functions and whose choice does not affect the checker: `decide (p ∈ A)` is `true` exactly when `p ∈ A`, whatever instance is used (a standard property of `decide`, not separately stated in the package).

### Disproved or dropped statements

No statement was disproved: all 37 main statements of the 20 cards are proved, and none was found false. One proved statement is not carried as a card: `invariantUnder_cannot_separate` (`lean/ToyChecker/Relabel.lean`), which states that for a predicate `Q : S → Prop` invariant under a map `π : S → S` (`InvariantUnder π Q`, defined as `∀ s, Q (π s) ↔ Q s`), `Q (π s) ↔ Q s` holds for every `s`. That is the definition of `InvariantUnder` read at `s`, so it is kept as a supporting lemma (axioms listed under Evidence) rather than as a result card; it accounts for the gap at id R5a.

### Not examined

- Infinitary versions (arbitrary unions of sound checkers; invariance under a group of relabelings rather than one map; the general form of R6g for every fragment with infinitely many good programs) are not separately stated.
- Whether bijectivity is *necessary* in R5c for every law is not examined; only sufficiency of a left inverse or of injectivity, and failure for one surjective, non-injective map, are proved.
- The Boolean image of two-sided certification (the analogue of R4e for R4f) is not characterized.
- Tools that decline to answer, time out, or answer nondeterministically are not modeled.

## Evidence

### Kernel-check record

Observed 2026-11-20 with Lean `v4.34.1` (`leanprover/lean4`, tag commit `5045d0056413266e57c625dcd7c365b10e377c52`, `x86_64-unknown-linux-gnu` release build), building `lean/` with `lake build` (10 jobs, no warnings). The package contains no `sorry`, `admit`, `native_decide`, `axiom`, `opaque`, `implemented_by`, `@[extern]`, or `unsafe`.

Axioms: all 310 declarations of the `ToyChecker` modules (as recorded in `audit/axioms.json`) depend on at most `propext`, `Classical.choice`, `Quot.sound`. 

Hashes (`audit/statements.json`): for each referenced theorem, `statement sha256` is the SHA-256 of `toString (repr ci.type)` of the theorem's statement, and `closure sha256` is the SHA-256 of the newline-joined, sorted list of lines `name : repr type` (followed by ` := repr value` for non-theorems) over all package constants reachable from the statement through types, definition bodies, and constructors. Changing any definition a statement depends on changes its closure hash. The table lists every Lean name referenced by a card (main statements, tightness counterexamples, non-vacuity witnesses, positive controls).

| Theorem | Role | Axioms | Statement sha256 | Closure sha256 (size) |
| :--- | :--- | :--- | :--- | :--- |
| `sound_iff_checkerLE_classicalOracle` | R1a main | `Classical.choice`, `Quot.sound`, `propext` | `29cff6a734abace720b7a250696435375730050f80c951e421a54749a5faeaae` | `6224e036a27ae5853f1281950f58ac41c313ad43eafa9db2e183ccbec94a0d84` (3) |
| `sound_rejectAll` | R1a main | `propext` | `9de95cb9f8d1dfe6e4a88290dfdd85d23e0e51a4091de50977f021ffe807d5c1` | `f88ba4994df8d3bf182fcff65efd18428e58d2b22b97598aa3e76dc2a0719d74` (2) |
| `sound_of_checkerLE_of_sound` | R1a main | none | `e96cda4142931f26c2cd5207da134354ffc1d9e52859f61838db323af6e630ed` | `b334f8e85df0c4d23b20601e5ce3051712559417831b5107387389fd1a781134` (2) |
| `sound_orChecker_of_sound_of_sound` | R1a main | `propext` | `a0122cab01ae2006fda9d162f7d2cc75950066da1135a11b7ce1531575999f25` | `9e29842ef9b0dae4a02e22688930ecc39c06500051e286a0746d98b7a7f39774` (2) |
| `law_of_all_sound_holds_for_rejectAll` | R1e main | `propext` | `f98f44eff2a144b354f707610ebf05bb610b956b314a9db07139b7e723ad319d` | `b94d68ec4e91b8a622ad545cbba2a3c7f93d0a69f7245d2f54b4b2bdfa999166` (3) |
| `not_anchoredSound_rejectAll_iff_anchors_ne_nil` | R2a main | `propext` | `022d89599ccb9c9e306bcd24c07ea129495d52f588e7b7f28b8357a2a32a9d8a` | `eb3c19db2e61e0d9a2f62d47afb2719f4d839a06270fca237d52d5758c5b5959` (3) |
| `allowlist_anchoredSound_of_anchors_good` | R2a main | `propext` | `7a1ee416064bfcff8325455221ee527195fe9f7a1231ba6cf92cb33eefc0972d` | `f2e93cba05b32f9fae58eeb94974f4797dc5342d0d24cad25aa9deb006f2a13c` (3) |
| `forced_accept_iff_mem_anchors_of_anchors_good` | R2c main | `Classical.choice`, `Quot.sound`, `propext` | `a449892d2b367eb8d9ee2a03822fd5cc00f402a5b2ba44c17d3f0e437ee8bb48` | `4f182e8eedb9cfe76efee888ec3662a9d4d347d9e5eeffbc763836134d8e5d8c` (2) |
| `forced_reject_iff_not_good_of_anchors_good` | R2c main | `Classical.choice`, `Quot.sound`, `propext` | `dc2692738c0d5f4787da6280b4f3611e230b0136348965970269f6d6aff78d57` | `4f182e8eedb9cfe76efee888ec3662a9d4d347d9e5eeffbc763836134d8e5d8c` (2) |
| `anchoredSound_admits_allowlists_disagreeing_at_good_nonanchor_of_anchors_good` | R2c main | `propext` | `5980c1e044f9232c51a1d6e5a43b6a0ac9d0397f73dc9e4834ae5f517e4d77ea` | `f2e93cba05b32f9fae58eeb94974f4797dc5342d0d24cad25aa9deb006f2a13c` (3) |
| `tableChecker_sound_passes_le_of_sound_passes` | R2f main | `propext` | `5b059e7e9b426b8229d4036af9ab54e513f829948a4151a9146c27c484435bb7` | `98df649fc0514fb52ab1a5eead99b5aa3ea1d08a2055c01b770b6ddf45c6b29a` (6) |
| `tableChecker_passes_and_le_of_passes` | R2f main | `propext` | `f8bafb9910b0d901357d6c7bdb2783e17336eeb5bd09eedf4dd41af59b842f03` | `e0e822e30ece5526dc4c684cc77cf96ea9f6c33db1acb2460d60cfd7d4d31ef6` (5) |
| `extensionalLaw_iff_of_same_behavior` | R3a main | none | `463c626f7e1f7d668dbac870cd4cd346b95bb4a886b0d1a741f4b8b2aa25cc6b` | `dc61c4c45e1d3195b485433e42bafb8e01703e042acdea4bbc74099fb63f1242` (1) |
| `extensionalLaw_id_of_law` | R3a main | `Quot.sound` | `25421c0670d956587c7928d987de1f20c458b82c47f3d0ecad093833fd9c1944` | `4d341807f48491445bb04653c2ea08c2199a5de868ba73486fe661e1b50a4cda` (2) |
| `extensionalLaw_cannot_separate_honestImpl_from_tableImpl` | R3a main | `Quot.sound`, `propext` | `f9bf9dbdfef7e3577942ee7dacf06493dabeec69238ded30cce812ab17fe37c2` | `42017d5c434118f6cf0a7b833ca3880ce9e4089e339618483e6c59e19cb326fb` (10) |
| `certChecker_sound_of_verifierSound` | R4a main | none | `ba95ffda89580c2463ad236b154d1815ebdc0568c43383f026f750b1167a8a22` | `5ed9ec81343abef3d83b179757582fca81ba83d1a4edf02a7dfbc1dad9aeb70e` (4) |
| `verifierSound_iff_forall_certChecker_sound` | R4b main | none | `efd60af5620f2155f948d4cf56de35a7c6e7e7a3818a7c16b4cbe1831d03a985` | `5ed9ec81343abef3d83b179757582fca81ba83d1a4edf02a7dfbc1dad9aeb70e` (4) |
| `certChecker_const_not_sound_of_bad_certificate` | R4b main | none | `38dcd8c8d1bc68b1d86ba05b362f9876534a22a813a7c864b528ae2e444b9313` | `ae75e8999dcbe521e0103b496053c096e52685cef8d89494ac5baea780243053` (3) |
| `certChecker_completeOn_iff` | R4c main | none | `da1c992a2cafa344c45623fa9016ae3e87ca259206328af0d5743877fec7904e` | `c089d64ea1d09942e8ca30f9d75ae47af5504e720e4e8163b743e6770cb58475` (3) |
| `verifierCompleteOn_of_certChecker_completeOn` | R4c main | none | `6b2a8586ecd74639f73679f22af22f4bbc51a385c12588f58bb96fa318361a61` | `c089d64ea1d09942e8ca30f9d75ae47af5504e720e4e8163b743e6770cb58475` (3) |
| `cex_verifierSound_verifierComplete_not_completeOn` | R4d main; R4d non-vacuity | `Quot.sound`, `propext` | `495c45b174533b0cb49d15d3f57b174f302ac6bcfc7c364fd0d9ad564d78bb3c` | `0cdabb079b56dac7ca64e5630f4d9f4ba529271da2e8c5fe990e245a7d84e246` (8) |
| `exists_certChecker_eq_iff_sound_certifiable` | R4e main | `Classical.choice`, `Quot.sound`, `propext` | `a5e918f352d00937d1899f4c9be9cdade56b4c0f114827d5e451729eaa17b0fc` | `ae75e8999dcbe521e0103b496053c096e52685cef8d89494ac5baea780243053` (3) |
| `twoSidedChecker_sound_completeOn_of_verifiedOn` | R4f main | none | `54aca359cd8aab1b989c9dadae1844ccccb71ad2957415914c96434f2213c99a` | `d1295c866c39e1963e5a91721c1c1325d73528b65acb103f8610883b4b41bb4c` (5) |
| `sound_comp_iff_of_surjective_of_invariantUnder` | R5b main | none | `80e4a110e7274c9731f8ec5dff0331a56e29a6831ce4a713e75f1fc7690eec65` | `455b2ce759308784ef56bc7953a75f32f45909b58ec5b651d0f89b3a585b0f7c` (2) |
| `forced_value_relabeled_iff_of_invariantUnder_comp` | R5c main | `Quot.sound`, `propext` | `24e44c88d967dc5fbe7ef328cd45aab598b7a145389b7cbec14622aa0680e8d0` | `7dccb28a29d23236b20fe913f10da35644f88da4ba862904c503231c48d838cc` (5) |
| `forced_value_at_image_of_invariantUnder_comp` | R5c main | none | `cbd03417b63ab4784d7d0097c95474a446d93af4c48555d2e6f0ec5d2c23ab34` | `d5d4afe14228cd31d700ae8a20802e0da0444cf70fbfd2a56ed44d07076b399b` (2) |
| `soundCompleteOn_iff_between` | R6a main | `Classical.choice`, `Quot.sound`, `propext` | `78408cff902d0b0dab03787cedd834a582924106a6383958cb1fd29a62760c24` | `3133096450ab5bfe824b2d0566b392156994fba72e3ef20159ba5035abfa303e` (5) |
| `soundCompleteOn_classicalOracle_inter` | R6a main | `Classical.choice`, `Quot.sound`, `propext` | `78f62f521775f21fd756ee8f0d9558958403b8e911fd9014b646982508a5c82e` | `61cfde6d56f5011635934aa5c55913a2a17e1a415155603df4ae1cf86eec9c0f` (4) |
| `soundCompleteOn_iff_sound_and_decides_on` | R6c main | none | `058c8784e5a127a70f46217d5b9224fee79132b80b4467a3453d0d27bff70408` | `e8a961a3995fb1be7a42cc761080cc65d63a74b098371929ef19f3d77b574c8a` (3) |
| `exists_soundCompleteOn_in_class_iff` | R6c main | none | `cfc825c60e5b7ccc82510fc9d88a2c85d7da0c2d50535a015101d67230d0b069` | `e8a961a3995fb1be7a42cc761080cc65d63a74b098371929ef19f3d77b574c8a` (3) |
| `soundCompleteOn_univ_iff_decides` | R6c main | none | `fdff791492e265929c18e34547aa8a5e2853b32e4df1142e6961bfc7a6637020` | `e8a961a3995fb1be7a42cc761080cc65d63a74b098371929ef19f3d77b574c8a` (3) |
| `exists_soundCompleteOn_univ_in_class_iff` | R6c main | none | `9aef2b89dd0d0347d0047a0a60ad6145fe39ec61c308e3f42004a1da07a844de` | `e8a961a3995fb1be7a42cc761080cc65d63a74b098371929ef19f3d77b574c8a` (3) |
| `exists_soundCompleteOn_in_class_iff_decides_on_of_andClosed_of_decidedIn` | R6c main | none | `d8a9f7466798b897ead5c71af5ba4238892c929bcbc79d048ffdd76e18a8fa90` | `84f6c4ea51400296434c769d9ab8fd8b33da2f07e94ea88f7fddb0b46bdcb9cc` (5) |
| `not_soundCompleteOn_rejectAll_iff` | R6e main | `Classical.choice`, `Quot.sound`, `propext` | `17702c6f4aae7afb4710c1a80d1f73cdc936e05ad7eec4200ca7ea30ef8d6c1a` | `2a597cf1e601b80d2077979c7452a10be7335a07390a30d827bf4dd580c85463` (4) |
| `soundCompleteOn_allowlist_iff` | R6f main | `propext` | `e5a187d07cecfcb4210c6807543e98e352079104d1172dca3d8fa700852d66eb` | `0e7e39ef975df3c422468f28568556a034b18d1d7fb9155d5b54c2f9652e8557` (4) |
| `no_allowlist_soundCompleteOn_evenGood_univ` | R6g main | `Quot.sound`, `propext` | `f1278a1924d2eda856d961834ed10790b24b3139f0e0898fa1542518632d5030` | `8686de51f7047ecf495931fd379f6993c2988f1fed2a4a97abfe22b02a498591` (5) |
| `cex_decides_on_fragment_without_soundness` | R6h main; R6h non-vacuity | `propext` | `07982b39c362bcf65128278017335bee4328c542add684066919d3c10266d9a0` | `bc7d11cbf610d9c5c1d1ed643d5e1e91afc38ee3b8d775119c6ef309a91d70f5` (4) |
| `cex_admits_allowlists_needs_anchors_good` | R2c counterexample | `Quot.sound`, `propext` | `1f308343503e17da8226a732c3670bd1001694db6785e807cf105a59aad3fd5e` | `403fc45e3b8fd73140b2e748557f9344e4b69ad011766478dfd47e861095fdee` (4) |
| `cex_admits_allowlists_needs_good_p` | R2c counterexample | `Quot.sound`, `propext` | `34bcb756308db4fea24e3df0c10cdd206f2298541907cd6dcd2721dac54d94c9` | `403fc45e3b8fd73140b2e748557f9344e4b69ad011766478dfd47e861095fdee` (4) |
| `cex_admits_allowlists_needs_not_mem` | R2c counterexample | `propext` | `c2d06ccdc4e891ed70131a39da41538bde8c1877c804a968fabb61c50fa43747` | `403fc45e3b8fd73140b2e748557f9344e4b69ad011766478dfd47e861095fdee` (4) |
| `cex_allowlist_anchoredSound_needs_anchors_good` | R2a counterexample | `propext` | `b72462c2c7ab3b29224ba7c3b3199e0a7ce2aea474429787ea1c5a64311be1a5` | `403fc45e3b8fd73140b2e748557f9344e4b69ad011766478dfd47e861095fdee` (4) |
| `cex_certChecker_sound_needs_verifierSound` | R4a counterexample | `propext` | `6920f5c0320d12c54d7f2e1b8e1594458513f62f8b587a8b55aa292bf71f0656` | `c149a524fb1d7527352afea03a24ecc72a969c41daf22bf06eeb8eefba9f69f8` (5) |
| `cex_const_not_sound_needs_accepted_certificate` | R4b counterexample | `Quot.sound`, `propext` | `cd695f1d39c88389e9c6e1744c072a370562e7a67246ce7fae64a4f5efde740f` | `ed86c55ed1efebb927e1ade254c13da7a9c595d138455b6b3c641109857e580b` (5) |
| `cex_const_not_sound_needs_bad_program` | R4b counterexample | `Quot.sound`, `propext` | `d6abc125c1148f0bea58901becfc03d9626f7e0784ca41c8ac4ba6d5427e3a04` | `ed86c55ed1efebb927e1ade254c13da7a9c595d138455b6b3c641109857e580b` (5) |
| `cex_decides_on_iff_needs_andClosed` | R6c counterexample | `Classical.choice`, `Quot.sound`, `propext` | `91d2877b9f8801b041ce7fb6844e99e23ba3a39afb80938e7d2075944fc3cdf2` | `feb0edf4702ba4a2f38720f675547fa31fe3ce8edfdd94851e9f6246b9983d19` (6) |
| `cex_decides_on_iff_needs_decidedIn` | R6c counterexample | `propext` | `ac388599661bc7bcf76f2585beb518cea936260af54305106ff191b8882ca0fe` | `9db3fa54db37968f1d0a19a7a8b03fde73a4fdd1256583c3ea4bd295ce204ce0` (5) |
| `cex_extensionalLaw_iff_needs_extensional` | R3a counterexample | `Quot.sound`, `propext` | `23a6c73e5c36f775dd57cb02514dc4731f00c03a7465bb4231614e10f7391371` | `7da13cb3e55f9dfdef6291b7172c06e2db7969f6aeb913992104e42748f5f1ad` (11) |
| `cex_extensionalLaw_iff_needs_same_behavior` | R3a counterexample | `Classical.choice`, `Quot.sound`, `propext` | `f090817a3c7e271c26623693b8b87952187579ddf8a5f778e8c437ee8d16370c` | `bdaf40aea4a94db5436f714afd0f364033f9084cd39c5c6613229d6a2644128a` (10) |
| `cex_forced_accept_needs_anchors_good` | R2c counterexample | `Quot.sound`, `propext` | `68e4ba11257e63ef43c2a2e1eb393a391a5fc1723ba26a7315f3f796558be5a9` | `924753b9fcd0e20090100c7dfde2cb07795241109a0195f85dd10de0c83b1b3d` (3) |
| `cex_forced_reject_needs_anchors_good` | R2c counterexample | `propext` | `680f3f0e951741f6262d5b1a7b7235b8e9d8d3ad4926ceea63226c7ef783aaf7` | `924753b9fcd0e20090100c7dfde2cb07795241109a0195f85dd10de0c83b1b3d` (3) |
| `cex_forced_value_at_image_needs_forced` | R5c counterexample | `propext` | `94704b78845f68dcd5520dacaa9e628125ddbead78d12ecea4946862b939407b` | `2e98aec6b3991e82ec41fbe9d251afdb7c0fcaf5b325cc3572b40efb5335c7e1` (1) |
| `cex_forced_value_at_image_needs_invariant` | R5c counterexample | `propext` | `f73a194bb9e87666883b7e13ebf2d072aa93a10938bc54bdf127c45dfd0b39fc` | `59da1c32f5c684f09002a093e3b5a85c1e33f341ce7a440bd8b97d67ffa41c96` (4) |
| `cex_forced_value_relabeled_needs_bijective` | R5c counterexample | none | `c76a24283002521eb079c93498067d17ba6ec1b20376a6a75ec8ffcb1d6ba2c1` | `17a967a9d9801ca20d4b3a952569417b4bf5e3849cf8c5c405ed95a63ec65469` (3) |
| `cex_forced_value_relabeled_needs_invariant` | R5c counterexample; R5c positive control | `propext` | `e3f3e6c532e3d8b67a4daa26ea3d089c0f328808b351ea27c12d17260417f02a` | `cd7e9d0e3047c514806840a134b1d3d0de3817667bcb632bef6846c57b959aa5` (9) |
| `cex_law_of_all_sound_needs_hL` | R1e counterexample | `propext` | `67331a8c333a0a8021a78f32d32227e24963a4391470d27453de560cd54933ac` | `5dd88c8d1c413d0484def2d7e5eb8bcdad76ce07b5be832029c53e0440359209` (5) |
| `cex_sound_comp_iff_needs_invariant` | R5b counterexample | `Quot.sound`, `propext` | `1b82d5ec459424a6539f8c8095d1d00c384bcfd21e28100611eb9cc1606d2c3c` | `60972af450f21fdd6cc1badedb520d7cf36c1ca52c498cc6e3a56895029c6a49` (3) |
| `cex_sound_comp_iff_needs_surjective` | R5b counterexample | `propext` | `01a8b37fa556ba1391c4fb87829f5fab119ca46d4fd3b2e82cf8bac208934d75` | `455b2ce759308784ef56bc7953a75f32f45909b58ec5b651d0f89b3a585b0f7c` (2) |
| `cex_sound_of_checkerLE_needs_le` | R1a counterexample | `propext` | `eaac1c564df9bdceedd03fe3835223ddcb4e2b7850538fa145cd5fea5b248297` | `86179bc261ff1579baec13d50cd2835d563f269b0084dc01fd77d9187419227e` (4) |
| `cex_sound_of_checkerLE_needs_sound` | R1a counterexample | `propext` | `29230b2409ad1458c9e713c32351a99cc827f224c1fc608f92f4c40bd66e21dd` | `2b8d9688b9fdbc1b95375d724ef0ccae9960773bc52a8d24731658381f2aaa09` (4) |
| `cex_sound_orChecker_needs_left` | R1a counterexample | `propext` | `ab43209e2a2829047e87ac705d2935a3d7b4bc764d7a08da62b3b22dc96d6c56` | `94408f134c2c585657a4ba3b7b3f1fd99a7ca57fb75ce9b53d375691f5050911` (5) |
| `cex_sound_orChecker_needs_right` | R1a counterexample | `propext` | `3f6c6648f172c03fa70e96b1d1f533400383557b1c0d146b45185873998a5016` | `94408f134c2c585657a4ba3b7b3f1fd99a7ca57fb75ce9b53d375691f5050911` (5) |
| `cex_tableChecker_passes_and_le_needs_passes` | R2f counterexample | `propext` | `9f1254b3afbc8a239002f9dbfaace5074840049e5e59333b8781da01403517b1` | `1a983e6c6ec3e23ba842521d9f9a1169a3731de2afefd7ebdace25bb257e18d3` (7) |
| `cex_tableChecker_sound_needs_passes` | R2f counterexample | `propext` | `6d14178629dac033e2210f09a92d0b395488eb818b7a27be8bb3eeeeb72005ba` | `8310cc89be5e8441daa6dacc98e0f97ce02ad30229ce0c1ef9fe5a25a0283764` (8) |
| `cex_tableChecker_sound_needs_sound` | R2f counterexample | `propext` | `816f9ea1a034d3665c89f7be4b3079dd73cec237a8482f664166b2fa344bb62d` | `b97eea1a6f77446bb555d68da812a42b2b838b36fc7fea0380dccb4488047e45` (8) |
| `cex_twoSidedChecker_needs_neg_sound` | R4f counterexample | `Quot.sound`, `propext` | `89e6ce37ad0b7f24dc0464aa941767ab9e5b3bdfff7db479f43d023780543b08` | `f946f6f95f2f70982a2c053514b426b40bc0614f6ab2a806339b2a216413c72a` (7) |
| `cex_twoSidedChecker_needs_pos_sound` | R4f counterexample | `propext` | `da0de944792f93b678f0edb5ebaff01e1fa222d3c1983af80523b33a41ddd8b2` | `0e2a27d882976c3e076229a2b00716f1d4602710935a74e8d33266104014bf27` (6) |
| `cex_twoSidedChecker_needs_verified` | R4f counterexample | `Quot.sound`, `propext` | `98c7720f9da9627104f4a69b66b66424a6213d1b34754a994e9e55c0d22550e5` | `1e16e2aec4625f72b01c94fa2715c81172fa2e0ab9a943312365927b9ffce5d2` (8) |
| `cex_verifierCompleteOn_needs_completeOn` | R4c counterexample | `propext` | `138744ddafd8d6a84b0a3bb353759ddde106e538d8aa9b09e02eb9ee91e06b3a` | `2a6dc866cf5c0b7ef814262faeab9d9e30f962860b7d52369a4bc588c25b94b8` (2) |
| `nonvacuous_admits_allowlists` | R2c non-vacuity | `Quot.sound`, `propext` | `7458055ff1fa69b969a27b6044d074007efa08f0920af24883e183959bd8c573` | `7d4c1274289747bd322667e516d6911b6fdb542490c0f1940d733bb219e10a32` (1) |
| `nonvacuous_anchors_good` | R2a non-vacuity; R2c non-vacuity | none | `8b74e9bb4c7ecd9bd4a706f33cf3168806378b2da907c1dc591738b5a64661dd` | `7d4c1274289747bd322667e516d6911b6fdb542490c0f1940d733bb219e10a32` (1) |
| `nonvacuous_certChecker_completeOn_iff` | R4c non-vacuity | `Quot.sound`, `propext` | `56bb595675a4f2f4549892b3a27eeaf4df3c07b87d5e1a25e10c6df63922f4a1` | `00649867c189d8722b89dc6b5a67845c5913a5d5257fd836f51eebfd1f445218` (4) |
| `nonvacuous_certChecker_const_not_sound` | R4b non-vacuity | `propext` | `727b324c0bd7208f56752dfd3568438088f2ce1058b21e465285159e3c89eb46` | `8ce58d62b25d61771228948e9f8fd07d8483fb5668c1a70837e738e9fff8ea2c` (2) |
| `nonvacuous_certChecker_sound` | R4a non-vacuity | `Quot.sound`, `propext` | `d883381e0de966a57592c908e9d3b26752d475c39631a2c8cce260bd0c4d35b2` | `5000e6c36c7199510225877207c8b13a81dd43e7a539685ddccd108100f684f6` (6) |
| `nonvacuous_exists_certChecker_eq_iff` | R4e non-vacuity | `Quot.sound`, `propext` | `18027296888dea3eec3c7703347e95a5b8e90723ebb505a08aca9fc6c0e1fb03` | `23079a8759c837dafe504b7e8f8b0fd5305755cb86bddaf5e58723625173b439` (4) |
| `nonvacuous_exists_soundCompleteOn_in_class_iff_decides_on` | R6c non-vacuity | `propext` | `65337b62da49fc3401b99b38a27e301456d0b72a8aaf8eedac20c831c5fc821d` | `f001a9547fe0bcf39e6b40dde7e3e2244f1272acb4b310ceb36cb5d355027534` (2) |
| `nonvacuous_extensionalLaw_id` | R3a non-vacuity | `Quot.sound` | `f0c63bd228592e32351f7e6f9314bec852576344a32b8692234e45ea1ebb5399` | `a2b3ad7d6f8b720b35b87d0f2de6cb96a7713abe43fdf72a8af9b8ed4f7722ad` (3) |
| `nonvacuous_extensionalLaw_iff` | R3a non-vacuity | `Quot.sound`, `propext` | `d059081dd97f713100886c2c725304094ca2e5dc93ebee3169300d86c52a6a7d` | `8cb9b5b4c6fbdda41fffa3ca98f5905af600b85acdb37c31ea42fab4dbf69938` (12) |
| `nonvacuous_forced_value_relabeled` | R5c non-vacuity | `propext` | `82d6d39709e09b70275f55ea323f699abf44b4aea67b275aa56cfad280cd7afd` | `820b4bfa2123d72fd335835fcae4490bfea5817a6b4eb0bc5e05f608a7735595` (10) |
| `nonvacuous_law_of_all_sound` | R1e non-vacuity | none | `1540759b04b2d090703e80c9ad411ada98937e4c61c7ddd6e74f9748ab10b1d3` | `f6fe10e977dd73616d7a9bbbd834cf4da1f0fe127a1b596871edc92c498c5645` (2) |
| `nonvacuous_no_allowlist_soundCompleteOn_evenGood_univ` | R6g non-vacuity | `Quot.sound`, `propext` | `fe85b417d92fe3cf6bcb6ffc4b150fda7be7a9dbb75b1f200ba9682419472b8e` | `3b8b4c67a2c0245aa18b9016e28207d094296ae209f84013c93c119253ba884a` (5) |
| `nonvacuous_not_anchoredSound_rejectAll` | R2a non-vacuity | `propext` | `b1cbf7c10ff226c8a35c25751bfaa7088eaf745d174f2266d2562b889c8bacdf` | `26ee3e47a4575ea03796a176fc03f93f79fb5333480db781809af8165bc6bf30` (4) |
| `nonvacuous_not_soundCompleteOn_rejectAll_iff` | R6e non-vacuity | `propext` | `272dec93b07b71447758d814e5719111151beee81c25fa1746c3c86f6526c639` | `49cae6ef1d5bd34aa413d8a2a9edf1c5f025140aa029fb3e8dcde9ee4eddfd20` (5) |
| `nonvacuous_soundCompleteOn` | R6a non-vacuity | `Quot.sound`, `propext` | `bc02e67aafe0e51adb852234231e0dda561c53342713d6b267d817081791df19` | `21e355550ae3cb65e490ea4f97865c0f54976516ef6f19a10824448c240ac039` (6) |
| `nonvacuous_soundCompleteOn_allowlist_iff` | R6f non-vacuity | `Quot.sound`, `propext` | `016c4fd0e522441d1fcb3e59ad591138a77df335a18c7c4c090bce94fb5fd814` | `7d4c1274289747bd322667e516d6911b6fdb542490c0f1940d733bb219e10a32` (1) |
| `nonvacuous_soundCompleteOn_iff_sound_and_decides_on` | R6c non-vacuity | `Quot.sound`, `propext` | `2494572739a2db4b49c199ac58f79679565bd3d617b61ce13318910b05dd5486` | `eedb72365c16373ff7ff203e653ab7c047608d5fa83bac64824e6a61ab96a35a` (4) |
| `nonvacuous_soundCompleteOn_univ_iff_decides` | R6c non-vacuity | `Classical.choice`, `Quot.sound`, `propext` | `56ddccff64043bcce657fe2f2301c21ee3c7857d4ffe0b8b554521166576ef2b` | `3bad7a4644de6dcfb6e74df3d2a31b30d9ada18f373e41e627fae3f224f527f0` (3) |
| `nonvacuous_sound_comp_iff` | R5b non-vacuity | `propext` | `2074efb3b09d8c7ca9a298ef3c3f21e140226bd834d42285eb9d45faf8e302d6` | `796886227f49224889c3c90e37faff28cde168522cbfeb9df593cdacaa4dfe77` (3) |
| `nonvacuous_sound_iff_checkerLE_classicalOracle` | R1a non-vacuity | `Classical.choice`, `Quot.sound`, `propext` | `77feed28c39a1e7a3ca6178137258dc9b76a5d8d53d0668f83aa1c9603e75f2d` | `2d2e469b6677c33b377b9ba71556ee8d5d002bdd28c0ba5ea6f4cb00b6113444` (5) |
| `nonvacuous_sound_of_checkerLE_of_sound` | R1a non-vacuity | `Quot.sound`, `propext` | `222ee6fd4479ba8370f3ec7eeb61ce72ff82d239be9635359b87e4e5ad6f1cfa` | `6b91f1e48b92fceb5186399a99ae03ac6f3f526be5fde76927ebd7d0a4867361` (5) |
| `nonvacuous_sound_orChecker` | R1a non-vacuity | `Quot.sound`, `propext` | `4c43f82e888a64951c87ddc268dcace740659e91d44c19d4069a542d60f15e40` | `f6fe10e977dd73616d7a9bbbd834cf4da1f0fe127a1b596871edc92c498c5645` (2) |
| `nonvacuous_tableChecker` | R2f non-vacuity | `Quot.sound`, `propext` | `62c632310525eb1f2884037bd8567e0f8c49705bd82ae45d38ea374b8410e0d1` | `00ca7d3cb10761abca9f5565cd5ed99fc4bde752b2aa485ba7144355497cf45f` (5) |
| `nonvacuous_twoSidedChecker_sound_completeOn` | R4f non-vacuity | `Quot.sound`, `propext` | `b6f598b1ab16e41ca48203ba701d4f57192071a98e42deca43c3b873a067a83d` | `288676fc87833a7cc9bdc16c0a7fac9f30fdcb3d0e634e5c3da655b2c889dfcf` (6) |
| `nonvacuous_verifierCompleteOn_of_certChecker_completeOn` | R4c non-vacuity | `Quot.sound`, `propext` | `4cf14b19689ca554afb09b2b44c5d35763aa1bbdd190d22c2111252a7cfb9f4b` | `9fd33a612e6e6ed9b264aa63eb8419cef57cd9712328c575a667ed52247d9d73` (6) |
| `nonvacuous_verifierSound_iff` | R4b non-vacuity | `Quot.sound`, `propext` | `76814109a8de40b1498509cc6fc38529b1238fae42033b79f6caeed180d3c509` | `c9963cc54c5dd7233e8d13e7a00a9f300e6696b35bfa4a018d7582260b92e356` (4) |
| `positive_control_allowlist_soundCompleteOn_finite_fragment` | R6g positive control | `Quot.sound`, `propext` | `9708404e983311a58ade98b32b6a3a42c5ebb5e9d9c4a15349ddaad8e57719ee` | `8686de51f7047ecf495931fd379f6993c2988f1fed2a4a97abfe22b02a498591` (5) |
| `positive_control_anchor_law_excludes_rejectAll` | R1e positive control | `Quot.sound`, `propext` | `d434f4c3255c3cb972258577bac6e8d8716b11e067fcaaec853c13909b30fa2d` | `b34c3e3d7faed884abae59b975e2f8f7ad7656632d08b6ca86fc9a06292789f1` (6) |
| `positive_control_anchor_law_separates_relabeled_checker` | R5b positive control | `Quot.sound`, `propext` | `7f80b606acb2ec1737f6f363ca1d975906dad50852e4d8cb3ccdc56642a77ef4` | `603fda4380332797178280198ab6cdd965fe3fe601a269dc1ad00d6827977fe9` (5) |
| `positive_control_completeOn_admits_evenExact_excludes_tableChecker` | R2f positive control | `Quot.sound`, `propext` | `170de71a235a7d52e05633dd44ca1961f2e72daa28538d24a54c22fdc7f77c60` | `38959a1a6974ed5ef16da56d7ec687bf0c2589e76900bd1fce0aa5199bfb4bd5` (8) |
| `positive_control_doubling_law_admits_fourOrTwo_excludes_every_tableChecker` | R2f positive control | `Quot.sound`, `propext` | `ff76ce449dd2afde99885af58e5d6865d2e28fd0b8e9b62da36a8d4a4246aa66` | `cdfbda513c4c76bcd1b828d221c6013992f1082ee236edae5d36175a0c6ef6b3` (9) |
| `positive_control_intensional_law_separates` | R3a positive control | none | `f6a83354e77551c96a3e293574d22eb0631f83a772b1daf1209dd029b3897bbf` | `dcab2020c0460a6061a6569d086dfad5ed8d623a359cbc31d419a5c2c6d3cc91` (9) |

Supporting theorems mentioned in the text but not referenced as card fields (no hash recorded; they do not enter any statement):

| Theorem | Axioms |
| :--- | :--- |
| `anchoredSound_example_evenExact` | `Quot.sound`, `propext` |
| `andClosed_class_both_sides_false_example` | `Quot.sound`, `propext` |
| `andClosed_class_repairs_unsound_decider_example` | `Classical.choice`, `Quot.sound`, `propext` |
| `andClosed_decidedIn_example_all` | `propext` |
| `cachedCertTool_eq_boundedHonestTool` | `Quot.sound`, `propext` |
| `certifiable_eq_good_of_verifierSound_of_verifierComplete` | `Quot.sound`, `propext` |
| `certifiable_imp_good_of_verifierSound` | none |
| `cex_forced_value_relabeled_surjective_not_injective` | `propext` |
| `classicalOracle_eq_decide` | `Classical.choice`, `Quot.sound`, `propext` |
| `classicalOracle_eq_true_iff` | `Classical.choice`, `Quot.sound`, `propext` |
| `doubling_law_admits_fourOrTwo_excludes_every_allowlist` | `Quot.sound`, `propext` |
| `forced_value_relabeled_iff_of_injective` | `Classical.choice`, `Quot.sound`, `propext` |
| `forced_value_relabeled_iff_of_leftInverse` | `Quot.sound`, `propext` |
| `halfV_certifiable_eq_evenGood` | `Quot.sound`, `propext` |
| `invariantUnder_cannot_separate` | none |
| `no_tool_completeOn_rejectAllV` | `propext` |
| `not_anchoredSound_example_rejectAll` | `propext` |
| `not_andClosed_example_belowTwo_zeroOrLarge` | none |
| `not_relabeling_example_const` | none |
| `not_sound_example_acceptAll` | `propext` |
| `not_twoSidedVerifiedOn_example_silent` | `propext` |
| `sound_comp_of_invariantUnder` | none |
| `sound_example_evenExact` | `Quot.sound`, `propext` |
| `swap02Fun_swap02Fun` | `propext` |
| `twoSidedVerifiedOn_example_honest` | `Quot.sound`, `propext` |

Of these, `forced_value_relabeled_iff_of_leftInverse`, `forced_value_relabeled_iff_of_injective`, `cex_forced_value_relabeled_surjective_not_injective` (`lean/ToyChecker/Relabel.lean`) and `andClosed_class_repairs_unsound_decider_example`, `andClosed_class_both_sides_false_example` (`lean/ToyChecker/RelativeCompleteness.lean`) document, respectively, which half of the bijectivity hypothesis of R5c is used, and restricted classes for the `&&`-closure statement of R6c. `invariantUnder_cannot_separate` (`lean/ToyChecker/Relabel.lean`) is the definitional lemma described under Boundaries, Disproved or dropped statements.

### Primary sources

Bibliographic data for every DOI below was checked against the Crossref metadata of that DOI (for the one DOI registered with DataCite rather than Crossref, against its DataCite metadata) on 2026-11-20 (authors, title and subtitle, venue, volume and issue, pages, year; for articles published online before print, the print year is given; Lecture Notes in Computer Science volume numbers, which Crossref does not record, were confirmed by web search). Book identities were checked against Open Library ISBN records on the same date. Content correspondences are stated in the cards; they are readings of the sources, not formal results.

- Patrick Cousot and Radhia Cousot, “Abstract interpretation: a unified lattice model for static analysis of programs by construction or approximation of fixpoints”, Proceedings of the 4th ACM SIGACT-SIGPLAN symposium on Principles of programming languages - POPL '77, pp. 238-252, 1977, doi:10.1145/512950.512973.
- Peter W. O'Hearn, “Incorrectness logic”, Proceedings of the ACM on Programming Languages 4(POPL), pp. 1-32, 2020, doi:10.1145/3371078.
- Tom M. Mitchell, “Generalization as search”, Artificial Intelligence 18(2), pp. 203-226, 1982, doi:10.1016/0004-3702(82)90040-6.
- John B. Goodenough and Susan L. Gerhart, “Toward a theory of test data selection”, IEEE Transactions on Software Engineering SE-1(2), pp. 156-173, 1975, doi:10.1109/TSE.1975.6312836.
- M.-C. Gaudel, “Testing can be formal, too”, TAPSOFT '95: Theory and Practice of Software Development, Lecture Notes in Computer Science 915, pp. 82-96, 1995, doi:10.1007/3-540-59293-8_188.
- Ned Block, “Psychologism and Behaviorism”, The Philosophical Review 90(1), pp. 5-43, 1981, doi:10.2307/2184371 (Crossref records the first page only; the page range 5-43 was confirmed by web search).
- H. G. Rice, “Classes of recursively enumerable sets and their decision problems”, Transactions of the American Mathematical Society 74(2), pp. 358-366, 1953, doi:10.1090/S0002-9947-1953-0053041-6.
- Roberto Bruni, Roberto Giacobazzi, Roberta Gori, Isabel Garcia-Contreras and Dusko Pavlovic, “Abstract extensionality: on the properties of incomplete abstract interpretations”, Proceedings of the ACM on Programming Languages 4(POPL), pp. 1-28, 2020, doi:10.1145/3371096.
- George C. Necula, “Proof-carrying code”, Proceedings of the 24th ACM SIGPLAN-SIGACT symposium on Principles of programming languages - POPL '97, pp. 106-119, 1997, doi:10.1145/263699.263712.
- R.M. McConnell, K. Mehlhorn, S. Näher and P. Schweitzer, “Certifying algorithms”, Computer Science Review 5(2), pp. 119-161, 2011, doi:10.1016/j.cosrev.2010.09.009.
- Jean-Baptiste Tristan and Xavier Leroy, “Formal verification of translation validators: a case study on instruction scheduling optimizations”, Proceedings of the 35th annual ACM SIGPLAN-SIGACT symposium on Principles of programming languages, pp. 17-27, 2008, doi:10.1145/1328438.1328444.
- Eyad Alkassar, Sascha Böhme, Kurt Mehlhorn and Christine Rizkallah, “A Framework for the Verification of Certifying Computations”, Journal of Automated Reasoning 52(3), pp. 241-273, 2014, doi:10.1007/s10817-013-9289-2.
- Eyad Alkassar, Sascha Böhme, Kurt Mehlhorn and Christine Rizkallah, “Verification of Certifying Computations”, Computer Aided Verification, Lecture Notes in Computer Science 6806, pp. 67-82, 2011, doi:10.1007/978-3-642-22110-1_7.
- René Thiemann and Christian Sternagel, “Certification of Termination Proofs Using CeTA”, Theorem Proving in Higher Order Logics, Lecture Notes in Computer Science 5674, pp. 452-468, 2009, doi:10.1007/978-3-642-03359-9_31.
- A. Pnueli, M. Siegel and E. Singerman, “Translation validation”, Tools and Algorithms for the Construction and Analysis of Systems, Lecture Notes in Computer Science 1384, pp. 151-166, 1998, doi:10.1007/BFb0054170.
- Henk Barendregt and Freek Wiedijk, “The challenge of computer mathematics”, Philosophical Transactions of the Royal Society A: Mathematical, Physical and Engineering Sciences 363(1835), pp. 2351-2375, 2005, doi:10.1098/rsta.2005.1650.
- Manuel Blum and Sampath Kannan, “Designing programs that check their work”, Journal of the ACM 42(1), pp. 269-291, 1995, doi:10.1145/200836.200880.
- Alfred Tarski (edited by John Corcoran), “What are logical notions?”, History and Philosophy of Logic 7(2), pp. 143-154, 1986, doi:10.1080/01445348608837096.
- Hilary Putnam, “Reason, Truth and History”, Cambridge University Press (chapter 2, “A problem about reference”, and the mathematical appendix), 1981, doi:10.1017/CBO9780511625398.
- Roberto Giacobazzi, Francesco Ranzato and Francesca Scozzari, “Making abstract interpretations complete”, Journal of the ACM 47(2), pp. 361-416, 2000, doi:10.1145/333979.333989.
- Roberto Bruni, Roberto Giacobazzi, Roberta Gori and Francesco Ranzato, “A Logic for Locally Complete Abstract Interpretations”, 2021 36th Annual ACM/IEEE Symposium on Logic in Computer Science (LICS), pp. 1-13, 2021, doi:10.1109/LICS52264.2021.9470608.
- Marco Campion, Mila Dalla Preda, Roberto Giacobazzi and Caterina Urban, “Monotonicity and the Precision of Program Analysis”, Proceedings of the ACM on Programming Languages 8(POPL), pp. 1629-1662, 2024, doi:10.1145/3632897.
- The mathlib Community, “The lean mathematical library”, Proceedings of the 9th ACM SIGPLAN International Conference on Certified Programs and Proofs, pp. 367-381, 2020, doi:10.1145/3372885.3373824.
- Mario Carneiro, “Formalizing Computability Theory via Partial Recursive Functions”, 10th International Conference on Interactive Theorem Proving (ITP 2019), Leibniz International Proceedings in Informatics (LIPIcs) 141, pp. 12:1-12:17, 2019, doi:10.4230/LIPIcs.ITP.2019.12 (registered with DataCite; arXiv version arXiv:1810.08380, where Rice's theorem is Theorem 6, `rice`).
- Mathlib 4, repository `leanprover-community/mathlib4`, commit `bbb39fe579406d36e4aacdc6d49a0055e4cf0d75` (inspected 2026-11-20), file `Mathlib/Computability/Halting.lean`, lines 42-43, inside `namespace ComputablePred`: `theorem rice₂ (C : Set Code) (H : ∀ cf cg, eval cf = eval cg → (cf ∈ C ↔ cg ∈ C)) : (ComputablePred fun c => c ∈ C) ↔ C = ∅ ∨ C = Set.univ`. Cited as background only; this package does not depend on Mathlib.
- Xavier Rival and Kwangkeun Yi, “Introduction to Static Analysis: An Abstract Interpretation Perspective”, MIT Press, 2020, ISBN 978-0-262-04341-0, Chapter 1 (no DOI recorded).
- Tom M. Mitchell, “Machine Learning”, McGraw-Hill, 1997, ISBN 0-07-042807-7, Chapter 2 (no DOI recorded).
- Adolf Lindenbaum and Alfred Tarski, “Über die Beschränktheit der Ausdrucksmittel deduktiver Theorien”, Ergebnisse eines mathematischen Kolloquiums 7 (for 1934-35, published 1936), pp. 15-22; English translation “On the limitations of the means of expression of deductive theories” in A. Tarski, Logic, Semantics, Metamathematics, Oxford University Press, 1956. No DOI exists; venue, volume, pages and translation were confirmed by web search on 2026-11-20, and this source is therefore not listed as a subject in `REPORT.json`. (The module comment of `Relabel.lean` dates it by the 1934-35 volume.)

Section and page pointers inside the books above were not verified and are not used; only chapters are cited.

## Revalidation

Requirements: `elan` (which installs and selects the toolchain `leanprover/lean4:v4.34.1` pinned in `lean/lean-toolchain`, so that `lake` and `lean` resolve to it) and `python3` (standard library only). No network access is needed after the toolchain is installed.

All commands run from the package root (the directory containing `REPORT.md`).

### Primary check

```sh
python3 support/revalidate.py .
```

`support/revalidate.py` is included in the package. It copies `lean/` to a temporary directory (the package itself is not modified), and its module docstring describes exactly what it checks and hashes:

1. `lake build` of the copied Lean project succeeds.
2. No Lean source under `lean/` contains `sorry`, `admit`, or `native_decide`, or declares an `axiom` (comments are ignored).
3. Every (non-internal) declaration of the library modules declared in `lean/lakefile.toml` (here `ToyChecker`) depends only on the axioms `propext`, `Classical.choice`, `Quot.sound`, as computed by Lean's `collectAxioms` in an audit file that the script generates inside the temporary copy.
4. Every Lean name referenced by `results.json` (fields `lean`, `nonvacuity_witness_lean`, `positive_control_lean`, and the `counterexample` of each hypothesis) and every name recorded in `audit/statements.json` exists; for every recorded name the statement hash, closure hash, and closure size equal the recorded values. The statement hash is the SHA-256 of the UTF-8 text `toString (repr ci.type)` of the declaration's type. The closure hash is the SHA-256 of the newline-joined, sorted list of lines `name : repr type` (followed by ` := repr value` for constants that are not theorems) over all constants of the library modules reachable from the statement through types, definition bodies, and inductive constructors (theorem bodies are not followed); the closure size is the number of those lines.

Expected output (exit status 0; any failed check prints a line starting with `FAIL` and the script exits with status 1):

```text
ok   lake build
ok   axioms (310 declarations)
ok   statement hashes (100 hashed names; 0 referenced names exist but carry no recorded hash)
REVALIDATED
```

### Step-by-step equivalent

The same checks without the script, using only `lake`, `lean`, and `python3`:

1. Build (fails if any proof breaks; a remaining `sorry` would also show up as a `declaration uses 'sorry'` warning and in step 2):

```sh
(cd lean && lake build)
```

2. Axiom check of every declaration in the package modules (expected output: `310 declarations checked; 0 non-standard axiom dependencies`). A `sorry` would appear here as a dependency on `sorryAx`, and `native_decide` as a dependency on `Lean.ofReduceBool`:

```sh
cat > /tmp/axiom_check.lean <<'EOF'
import ToyChecker
import Lean
open Lean Elab Command

-- Every declaration of the `ToyChecker` modules may depend only on the three standard axioms.
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut total : Nat := 0
  let mut bad : Nat := 0
  for (c, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? c then
      if (`ToyChecker).isPrefixOf env.header.moduleNames[idx.toNat]! && !c.isInternal then
        total := total + 1
        for a in (← collectAxioms c) do
          unless a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
            bad := bad + 1
            logInfo m!"{c} depends on {a}"
  logInfo m!"{total} declarations checked; {bad} non-standard axiom dependencies"
EOF
(cd lean && lake env lean /tmp/axiom_check.lean)
```

For a single theorem, `#print axioms Toy.Checker.<name>` after `import ToyChecker` gives the per-theorem list recorded in the Evidence table.

3. Statement and closure hashes (expected output: `100 recorded, 0 mismatches []`):

```sh
cat > /tmp/statement_texts.lean <<'EOF'
import ToyChecker
import Lean
open Lean Elab Command

-- For every theorem of the `ToyChecker` modules, print one JSON line with the `repr` of its
-- statement and the sorted closure texts (types, and values of non-theorems, of all package
-- constants reachable from the statement).
private def inPkg (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => (`ToyChecker).isPrefixOf env.header.moduleNames[idx.toNat]!
  | none => false

private partial def closure (env : Environment) (todo : List Name) (acc : NameSet) : NameSet :=
  match todo with
  | [] => acc
  | n :: rest =>
    if acc.contains n || !inPkg env n then closure env rest acc else
    let acc := acc.insert n
    match env.find? n with
    | none => closure env rest acc
    | some ci =>
      let cs := ci.type.getUsedConstants.toList ++
        (match ci.value? (allowOpaque := true) with
         | some v => if ci.isTheorem then [] else v.getUsedConstants.toList
         | none => []) ++
        (match ci with
         | .inductInfo iv => iv.ctors
         | _ => [])
      closure env (cs ++ rest) acc

#eval show CommandElabM Unit from do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    if inPkg env n && !n.isInternal && ci.isTheorem then
      let cl := closure env ci.type.getUsedConstants.toList {}
      let clTxt := cl.toList.map (fun c =>
        match env.find? c with
        | some cc => c.toString ++ " : " ++ toString (repr cc.type) ++
            (match cc.value? (allowOpaque := true) with
             | some v => if cc.isTheorem then "" else " := " ++ toString (repr v)
             | none => "")
        | none => c.toString)
      IO.println (Json.mkObj [("name", toJson n.toString),
        ("type_repr", toJson (toString (repr ci.type))),
        ("closure", toJson (clTxt.toArray.qsort (· < ·)))]).compress
EOF
(cd lean && lake env lean /tmp/statement_texts.lean > /tmp/statement_texts.jsonl)
python3 - <<'EOF'
import hashlib, json
rec = json.load(open("audit/statements.json"))["statements"]
got = {}
for line in open("/tmp/statement_texts.jsonl"):
    if line.startswith("{"):
        s = json.loads(line)
        got[s["name"]] = {"statement_sha256": hashlib.sha256(s["type_repr"].encode()).hexdigest(),
                          "closure_sha256": hashlib.sha256("\n".join(s["closure"]).encode()).hexdigest(),
                          "closure_size": len(s["closure"])}
bad = [n for n in rec if got.get(n) != rec[n]]
print(len(rec), "recorded,", len(bad), "mismatches", bad)
EOF
```

A hash mismatch means a statement or a definition it depends on changed; the cards that cite that theorem must then be re-checked before reuse. The hashes depend on Lean's `repr` of terms and may change across toolchain versions even if nothing else changes; on a different toolchain, rebuild and re-run the build and axiom checks, and compare statements by reading them.

### What a passing check does not establish

The checks above confirm that the theorems hold, that they use only the three standard axioms, and that their statements are unchanged. Whether a card's prose, non-claims, and modeling bridges are faithful to those statements is checked only by reading the card against the quoted Lean statement.
