# Galois connections, best abstract transformers, and fixpoint transfer: a Lean 4 toy model with tight hypotheses

## Summary

This package states and kernel-checks, in Lean 4 without Mathlib, nineteen results on the order-theoretic core of abstract interpretation: the characterization of Galois connections, soundness, optimality and monotonicity of best abstract transformers, precision loss under composition, transfer of abstract post-fixpoints to concrete (least) fixpoints, termination of Kleene iteration, and termination of iteration with widening. The concrete domain is sets of states (`Pred σ := σ → Prop`, ordered by inclusion); the abstract domain is any type with a bare `≤` relation, and every order law (reflexivity, transitivity, antisymmetry, chain conditions) is a separate, explicitly named hypothesis. Every hypothesis of every theorem has a proved counterexample showing it cannot be dropped, and every result has a proved non-vacuity instance. No result is claimed novel; all are re-derivations (`T0`) except one folklore attainment example (`T1`). Below, `⊆` is the inclusion order on `Pred σ`, `f♯` an abstract transformer, and `h♯ = α ∘ h ∘ γ` the best abstract transformer of `h`.

- **R1-gc-iff** (`galoisConnection_iff_monotone_extensive_reductive_of_refl_of_trans`). Over a reflexive and transitive abstract order (antisymmetry not needed), `α : Pred σ → A` and `γ : A → Pred σ` form a Galois connection (`α x ≤ a ↔ x ⊆ γ a`) exactly when `α` and `γ` are monotone, `x ⊆ γ (α x)` for every `x`, and `α (γ a) ≤ a` for every `a`; dropping reflexivity or transitivity breaks the equivalence.
- **R1-gc-forward** (`monotone_extensive_reductive_of_galoisConnection_of_refl_of_trans`). Over a reflexive and transitive abstract order, a Galois connection has monotone `α` and `γ`, extensive `γ ∘ α` and reductive `α ∘ γ` (reference point: the forward half of `R1-gc-iff`).
- **R1-gc-backward** (`galoisConnection_of_monotone_extensive_reductive_of_trans`). Over an abstract order that is only assumed transitive (reflexivity not needed), monotone `α` and `γ` with extensive `γ ∘ α` and reductive `α ∘ γ` form a Galois connection; each of the five hypotheses is necessary.
- **R2-best-sound** (`bestTransformer_sound_of_galoisConnection_of_refl`). Given a Galois connection over a reflexive abstract order, the best abstract transformer `α ∘ f ∘ γ` is `γ`-sound (`f (γ a) ⊆ γ (α (f (γ a)))` for all `a`) for every concrete transformer `f`, monotone or not; for non-monotone `f` this constrains `f` only on the sets `γ a`.
- **R2-best-least** (`sound_iff_bestTransformer_le_of_galoisConnection`). Given only a Galois connection (no order law, no monotonicity of `f` or `f♯`), `f♯` is `γ`-sound for `f` exactly when `α (f (γ a)) ≤ f♯ a` for all `a`, so `α ∘ f ∘ γ` is a pointwise lower bound of all `γ`-sound transformers; it is guaranteed to be sound itself, hence a least sound transformer, when the order is also reflexive (`R2-best-sound`), and without reflexivity it can fail to be sound.
- **R2-best-mono** (`bestTransformer_monotone_of_galoisConnection_of_refl_of_trans_of_monotone`). Given a Galois connection over a reflexive and transitive abstract order and a monotone concrete transformer `f`, the best abstract transformer `α ∘ f ∘ γ` is monotone.
- **R3-comp-le** (`bestTransformer_comp_le_of_galoisConnection_of_refl_of_monotone`). Given a Galois connection over a reflexive abstract order and a monotone `f`, `(f ∘ g)♯ a ≤ f♯ (g♯ a)` for every `g` and `a` (with `h♯ = α ∘ h ∘ γ`): composing best transformers is never more precise than the best transformer of the composition.
- **R3-comp-strict** (`bestTransformer_comp_strict_sign`). In the sign domain over `Int`, with `g` the transformer of `x := x + 1` and `f` that of `x := x - 1`, all hypotheses of `R3-comp-le` hold and `(f ∘ g)♯ pos = pos` is strictly below `f♯ (g♯ pos) = top`, so the inequality of `R3-comp-le` can be strict.
- **R4-lfp-fix** (`lfp_eq_of_monotone`). For a monotone concrete transformer `f` on predicates, `lfp f` (the intersection of all concrete post-fixpoints `{x | f x ⊆ x}`) is a fixpoint: `f (lfp f) = lfp f`; without monotonicity it need not be.
- **R4-lfp-least** (`lfp_le_of_le`). For every concrete transformer `f`, monotone or not, and every concrete post-fixpoint `x` (`f x ⊆ x`), `lfp f ⊆ x` (reference point: an unfolding of the definition of `lfp`).
- **R4-transfer** (`lfp_le_gamma_of_monotone_gamma_of_sound_of_postFixpoint`). If `γ` is monotone, `f♯` is `γ`-sound for `f` and `f♯ a ≤ a`, then `lfp f ⊆ γ a`, where `lfp f` is the intersection of all concrete post-fixpoints; it is guaranteed to be the concrete least fixpoint only when `f` is monotone (without monotonicity it need not be a fixpoint; see `R4-transfer-lfp`).
- **R4-transfer-lfp** (`isLeastFixpoint_lfp_and_le_gamma_of_monotone_of_monotone_gamma_of_sound_of_postFixpoint`). If, in addition, the concrete transformer `f` is monotone, then `lfp f` is the least fixpoint of `f` and every least fixpoint of `f` is included in `γ a`; monotonicity of `f` cannot be dropped, since without it `γ a` can miss the least fixpoint.
- **R4-kleene-acc** (`exists_kleene_postFixpoint_of_monotone_of_acc_of_le_apply`). If `f♯` is monotone, the abstract order has no infinite sequence of consecutive strict steps (`ACC`), and `a₀ ≤ f♯ a₀`, then some Kleene iterate `f♯ⁿ a₀` is a post-fixpoint of `f♯`; reflexivity and transitivity are not needed.
- **R4-kleene-height** (`exists_kleene_postFixpoint_le_of_monotone_of_heightLE_of_le_apply`). If `f♯` is monotone, the abstract order has height at most `h`, and `a₀ ≤ f♯ a₀`, then some Kleene iterate `f♯ⁿ a₀` with `n ≤ h` is a post-fixpoint of `f♯`.
- **R4-kleene-bound** (`kleeneHeight_bound_attained`). For every `h`, on the chain `Fin (h + 1)` with the capped successor started at `0`, every hypothesis of `R4-kleene-height` holds and the `h`-th iterate is the first post-fixpoint, so the bound `n ≤ h` is attained; started from the top element instead, a post-fixpoint is reached at step 0.
- **R4-height-acc** (`acc_of_heightLE`). An abstract order of height at most `h` satisfies `ACC` (auxiliary bridge).
- **R5-widen** (`exists_widenIter_postFixpoint_of_trans_of_upperLeft_of_upperRight_of_terminates_of_monotone_of_le_apply`). If the abstract order is transitive, the widening `∇` satisfies `a ≤ a ∇ b`, `b ≤ a ∇ b` and the termination axiom (for every ascending input the widened chain is not strictly increasing at every step), `f♯` is monotone, and `a₀ ≤ f♯ a₀`, then some widened iterate (`x₀ = a₀`, `xₙ₊₁ = xₙ ∇ f♯ xₙ`) is a post-fixpoint of `f♯`, with no chain condition on the domain; each of the six hypotheses is necessary.
- **R5-widen-diverge** (`kleene_diverges_widen_converges_ub`). On the infinite-height domain `UB`, plain Kleene iteration from `bot` of the sound, monotone abstraction of a counter loop never reaches a post-fixpoint and no iterate over-approximates the concrete least fixpoint, whereas iteration with the jump-to-top widening reaches the post-fixpoint `top` at step 1.
- **R5-widen-bridge** (`widenTerminates_of_widenStabilizes`). The textbook widening termination axiom (the widened chain of every ascending input eventually becomes constant, with Lean equality) implies the termination axiom used by `R5-widen`, with no order law assumed (auxiliary bridge).

The single most important limitation: a `γ`-sound abstract post-fixpoint is guaranteed to over-approximate the concrete *least fixpoint* only when the concrete transformer is monotone (`R4-transfer-lfp`); without monotonicity, `R4-transfer` bounds only `lfp f`, the intersection of all concrete post-fixpoints, which then need not be a fixpoint at all. What each result does **not** show is listed first under **Boundaries** (and in the `non_claims` field of each card in `results.json`).

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

## Applicability

**Model fidelity: this is a toy model.** The definitions capture the order-theoretic skeleton of abstract interpretation as used by static analyzers (Cousot and Cousot 1977, 1979, 1992) and by mechanized abstract interpreters (for example the concretization-based framework of Nipkow and Klein, *Concrete Semantics*, Chapter 13). They do not model any particular analyzer, programming language, or abstract domain implementation:

- **Programs are not modelled syntactically.** A "program" or "statement" is just a concrete transformer `f : Pred σ → Pred σ` on sets of states; `post h` is the image (strongest-postcondition) transformer of a deterministic assignment `s := h s`. Real analyzers compute transfer functions per statement and per control-flow edge, over relational, multi-variable domains, with widening at loop heads; none of that structure is present.
- **Concrete domain.** Fixed to `Pred σ := σ → Prop` ordered by inclusion (`x ≤ y :↔ ∀ s, x s → y s`), i.e. a powerset lattice; no other concrete domain is covered. Concrete transformers are arbitrary functions; monotonicity is a separate hypothesis wherever it is used.
- **Abstract domain.** Any `A : Type` with a bare `[LE A]` instance. No lattice operations (joins, meets, completeness) are assumed anywhere. Reflexivity (`IsRefl`), transitivity (`IsTrans`), antisymmetry (`IsAntisymm`), the ascending chain condition (`ACC`), a height bound (`HeightLE`) and a least element (`IsBot`) are separate propositions; each theorem lists exactly the ones it uses. No main result assumes antisymmetry.
- **Soundness** is the `γ`-form `f ∘ γ ⊆ γ ∘ f♯` (`Sound γ f fs := ∀ a, f (γ a) ≤ γ (fs a)`) throughout. It constrains `f` only on the sets `γ a`; it is guaranteed to imply soundness on subsets of `γ a` only when `f` is monotone (without monotonicity it need not). The `α`-form `α ∘ f ≤ f♯ ∘ α` is not formalized.
- **Terminology.** A *post-fixpoint* of a map `h` is a `z` with `h z ≤ z`, on the concrete side (`f x ⊆ x`) and on the abstract side (`PostFixpoint fs a := fs a ≤ a`) alike; this is Cousot and Cousot's convention. Nipkow and Klein, and several order-theory texts, call the same condition a *pre-fixpoint*. `lfp f` is defined as the intersection of all concrete post-fixpoints; it is guaranteed to be the least fixpoint only when `f` is monotone (without monotonicity it need not be a fixpoint).
- **Widening** is a stateless binary operator `w : A → A → A`; delayed widening, widening with thresholds, step-indexed widenings and narrowing are not covered. The termination axiom `WidenTerminates` is Cousot and Cousot's (1992) condition (8), quantified over ascending inputs only.
- **Universe and logic.** Every generic definition and theorem quantifies over `σ : Type` and `A : Type` (universe level 0). Abstraction functions on `Pred σ` (`unitAlpha`, `boolAlpha`, `signAlpha`) are noncomputable, and several proofs are classical; decidability of `≤` and computability of transformers are never assumed or concluded.
- **Fixtures.** Counterexamples and witnesses use small finite relations and a few standard domains (sign domain, an upper-bound domain `UB` for a natural-number counter); see the fixture table under **Findings**.

**Toolchain.** Lean `leanprover/lean4:v4.34.1` (commit `5045d0056413266e57c625dcd7c365b10e377c52`), core Lean only: no Mathlib, no `Std` import, no Lake dependencies. The Lake project is `lean/` (library root `Toy`, namespace `Toy.AbsInt`, modules `Basic`, `Domains`, `Galois`, `Sign`, `Transformer`, `Fixpoint`, `Widening`). The results were checked only under this toolchain; behaviour under other Lean versions was not examined.

**Relationship of the subjects.** The Lean toolchain is the checker of every theorem. The papers listed in `REPORT.json` are prior-art sources for the known results restated here (and, for `R3-comp-strict`, for the phenomenon it instantiates); the Lean statements are restatements in this package's vocabulary, typically with weaker hypotheses than the cited sources (preorders or bare relations instead of posets or complete lattices), not mechanizations of the papers' own formal systems.

Basis: derived (modeling bridge). Applying a result to a real analyzer requires checking that the analyzer's concrete semantics, abstract domain, transformer and iteration strategy instantiate these definitions (in particular: concrete semantics on sets of states ordered by inclusion; the stated order laws on the abstract precision order; `γ`-soundness of transformers; a monotone concrete transformer where `R4-transfer-lfp` is used; a stateless widening stopped at the first post-fixpoint where `R5-widen` is used). Each card under **Findings** states its own bridge.

## Findings

All Lean statements below are the output of Lean's pretty-printer on the compiled declarations (option `pp.fieldNotation.generalized false`; namespace `Toy.AbsInt` omitted), except the three structurally recursive definitions, which are shown by their source equations, and the two blocks under **Fixture domains and transformers** that are labelled as Lean source excerpts. Every `Toy.AbsInt` declaration named in this report is defined or quoted in it: key definitions and fixtures in this section, definition examples under **Definition examples**, and further proved statements on the cards and under **Proved boundary examples**. The pretty-printer omits implicit arguments, including the carrier type of predicates such as `Monotone` or `WidenTerminates` when the printed term does not fix it; where the truth of a quoted counterexample or example depends on such a hidden carrier, the carrier is stated in the hypothesis ledger or in a comment next to the statement. *Unfolded* blocks are hand-written elementary readings in which `x ⊆ y` abbreviates `x ≤ y` on `Pred σ`, i.e. `∀ s, x s → y s`.

### Key definitions

```lean
def Pred : Type → Type :=
  fun σ => σ → Prop

def instLEPred : (σ : Type) → LE (Pred σ) :=
  fun σ => { le := fun x y => ∀ (s : σ), x s → y s }

def IsRefl : (A : Type) → [LE A] → Prop :=
  fun A [LE A] => ∀ (a : A), a ≤ a

def IsTrans : (A : Type) → [LE A] → Prop :=
  fun A [LE A] => ∀ (a b c : A), a ≤ b → b ≤ c → a ≤ c

def IsAntisymm : (A : Type) → [LE A] → Prop :=
  fun A [LE A] => ∀ (a b : A), a ≤ b → b ≤ a → a = b

def Monotone : {X Y : Type} → [LE X] → [LE Y] → (X → Y) → Prop :=
  fun {X Y} [LE X] [LE Y] h => ∀ (a b : X), a ≤ b → h a ≤ h b

def StrictLt : {A : Type} → [LE A] → A → A → Prop :=
  fun {A} [LE A] a b => a ≤ b ∧ ¬b ≤ a

def ACC : (A : Type) → [LE A] → Prop :=
  fun A [LE A] => ¬∃ c, ∀ (n : Nat), StrictLt (c n) (c (n + 1))

def HeightLE : (A : Type) → [LE A] → Nat → Prop :=
  fun A [LE A] h => ∀ (c : Nat → A) (k : Nat), (∀ (i : Nat), i < k → StrictLt (c i) (c (i + 1))) → k ≤ h

def IsBot : {A : Type} → [LE A] → A → Prop :=
  fun {A} [LE A] b => ∀ (a : A), b ≤ a

def GaloisConnection : {σ A : Type} → [LE A] → (Pred σ → A) → (A → Pred σ) → Prop :=
  fun {σ A} [LE A] α γ => ∀ (x : Pred σ) (a : A), α x ≤ a ↔ x ≤ γ a

def Extensive : {σ A : Type} → (Pred σ → A) → (A → Pred σ) → Prop :=
  fun {σ A} α γ => ∀ (x : Pred σ), x ≤ γ (α x)

def Reductive : {σ A : Type} → [LE A] → (Pred σ → A) → (A → Pred σ) → Prop :=
  fun {σ A} [LE A] α γ => ∀ (a : A), α (γ a) ≤ a

def bestTransformer : {σ A : Type} → (Pred σ → A) → (A → Pred σ) → (Pred σ → Pred σ) → A → A :=
  fun {σ A} α γ f a => α (f (γ a))

def Sound : {σ A : Type} → (A → Pred σ) → (Pred σ → Pred σ) → (A → A) → Prop :=
  fun {σ A} γ f fs => ∀ (a : A), f (γ a) ≤ γ (fs a)

def post : {σ : Type} → (σ → σ) → Pred σ → Pred σ :=
  fun {σ} h x t' => ∃ s, x s ∧ h s = t'

def lfp : {σ : Type} → (Pred σ → Pred σ) → Pred σ :=
  fun {σ} f s => ∀ (x : Pred σ), f x ≤ x → x s

def IsLeastFixpoint : {σ : Type} → (Pred σ → Pred σ) → Pred σ → Prop :=
  fun {σ} f x => f x = x ∧ ∀ (y : Pred σ), f y = y → x ≤ y

def PostFixpoint : {A : Type} → [LE A] → (A → A) → A → Prop :=
  fun {A} [LE A] fs a => fs a ≤ a

def WidenUpperLeft : {A : Type} → [LE A] → (A → A → A) → Prop :=
  fun {A} [LE A] w => ∀ (a b : A), a ≤ w a b

def WidenUpperRight : {A : Type} → [LE A] → (A → A → A) → Prop :=
  fun {A} [LE A] w => ∀ (a b : A), b ≤ w a b

def Ascending : {A : Type} → [LE A] → (Nat → A) → Prop :=
  fun {A} [LE A] b => ∀ (n : Nat), b n ≤ b (n + 1)

def WidenTerminates : {A : Type} → [LE A] → (A → A → A) → Prop :=
  fun {A} [LE A] w => ∀ (b : Nat → A), Ascending b → ¬∀ (n : Nat), StrictLt (widenChain w b n) (widenChain w b (n + 1))

def WidenStabilizes : {A : Type} → [LE A] → (A → A → A) → Prop :=
  fun {A} [LE A] w => ∀ (b : Nat → A), Ascending b → ∃ N, ∀ (m : Nat), N ≤ m → widenChain w b m = widenChain w b N

def kleene {A : Type} (fs : A → A) (a₀ : A) : Nat → A
  | 0 => a₀
  | n + 1 => fs (kleene fs a₀ n)

def widenChain {A : Type} (w : A → A → A) (b : Nat → A) : Nat → A
  | 0 => b 0
  | n + 1 => w (widenChain w b n) (b (n + 1))

def widenIter {A : Type} (w : A → A → A) (fs : A → A) (a₀ : A) : Nat → A
  | 0 => a₀
  | n + 1 => w (widenIter w fs a₀ n) (fs (widenIter w fs a₀ n))
```

What they capture: `GaloisConnection` is the isotone form (an adjunction `α ⊣ γ`, not Ore's antitone form and not necessarily a Galois insertion `α (γ a) = a`); over a reflexive order it says `α x` is a most precise abstract value soundly describing `x`, unique up to `a ≤ b ∧ b ≤ a` (up to equality only under antisymmetry); without reflexivity the connection can hold although `α x` does not describe `x` soundly (`nr2_gc`, `nr2_not_extensive`, quoted under **Proved boundary examples**). `StrictLt a b := a ≤ b ∧ ¬ b ≤ a`; `ACC` forbids infinite sequences of *consecutive* strict steps and `HeightLE A h` bounds the length of such sequences, which for non-transitive relations differs from the usual chain notions (boundary examples `cyc3_not_acc`, `cyc3_not_heightLE`, `nb_heightLE_one_ascending_not_stabilizing`). `IsLeastFixpoint` is stated independently of `lfp`. `WidenTerminates` gives one non-strict step of each widened chain of an ascending input; `WidenStabilizes` is the textbook "eventually constant" axiom with Lean equality. `widenIter` widens at every step and never stops by itself.

Every core definition has proved positive and negative examples in the Lean sources, named after the definition (with a lower-case initial) followed by `_example_pos` or `_example_neg`, for example `galoisConnection_example_pos`, `acc_example_neg` and `widenStabilizes_example_neg`; for the inclusion order `instLEPred` they are `Pred.le_refl`, `le_U`, `E_le` and `not_U_le_E`. All of these statements are quoted under **Definition examples** below, after the fixtures they use.

#### Fixture domains and transformers

| Fixture | Carrier and order | Properties |
| --- | --- | --- |
| `Sign` | `bot`, `neg`, `zero`, `pos`, `top`; `bot` below everything, `top` above everything, `neg`, `zero`, `pos` pairwise incomparable | Reflexive, transitive, antisymmetric, height 2 (`Sign.heightLE`), with a proved Galois connection `signGC` to `Pred Int` (`signAlpha`, `signGamma`). |
| `UB` | `bot`, `atMost n` (`n : Nat`), `top`; `bot ≤ everything`, `atMost m ≤ atMost n ↔ m ≤ n`, everything `≤ top` | Reflexive, transitive, infinite height (`UB.not_acc`, `UB.not_heightLE`); concretization `ubGamma`, `atMost n ↦ {k | k ≤ n}`. |
| `B2` | `lo ≤ hi` | Two-element chain; Galois connections `b2Alpha`/`b2Gamma` with `Pred Unit` (`galoisConnection_example_pos`) and `boolAlpha`/`boolGamma` with `Pred Bool` (a conjunct of `compLe_tight_monoF` and of `sound_not_subset_of_not_monotone`). |
| `NR2`, `NR3` | `NR2`: `lo ≤ x` for all `x`, nothing else; `NR3`: `lo ≤ x` for all `x`, `mid ≤ hi`, `hi ≤ hi` | Transitive, not reflexive (`NR2` at `hi`, `NR3` at `mid`). |
| `NT3`, `NT4`, `NT4w` | small finite relations | Reflexive, not transitive (e.g. `NT3`: `lo ≤ mid ≤ hi` but not `lo ≤ hi`). |
| `Dis2` | two elements, discrete order | Height 0; `dis2Swap` is monotone with no post-fixpoint. |
| `V3`, `W4` | `V3`: `bot` below two incomparable elements; `W4`: `z < m < p`, `m < q` | Small posets. |
| `PT` | pairs of naturals with the product order, plus `top` above everything | Reflexive and transitive. |
| `E2` | two elements, `a ≤ b` and `b ≤ a` | Total preorder that is not antisymmetric. |
| `Cyc3`, `NB`, `PB` | boundary fixtures | `Cyc3`: reflexive relation with a strict 3-cycle; `NB`: non-transitive relation of height 1; `PB`: non-antisymmetric preorder with widening `pbWiden`. |
| `Fin (h + 1)` | the chain `0 < 1 < … < h` | Height `h`; capped successor `capSucc`. |

```lean
def signGamma : Sign → Pred Int :=
  fun x =>
    match x with
    | Sign.bot => fun x => False
    | Sign.neg => fun n => n < 0
    | Sign.zero => fun n => n = 0
    | Sign.pos => fun n => 0 < n
    | Sign.top => fun x => True

def signAlpha : Pred Int → Sign :=
  fun x =>
    if x ≤ signGamma Sign.bot then Sign.bot
    else
      if x ≤ signGamma Sign.neg then Sign.neg
      else if x ≤ signGamma Sign.zero then Sign.zero else if x ≤ signGamma Sign.pos then Sign.pos else Sign.top

def ubGamma : UB → Pred Nat :=
  fun x =>
    match x with
    | UB.bot => fun x => False
    | UB.atMost n => fun k => k ≤ n
    | UB.top => fun x => True

def ubIncr : UB → UB :=
  fun x =>
    match x with
    | UB.bot => UB.atMost 0
    | UB.atMost n => UB.atMost (n + 1)
    | UB.top => UB.top

def ubWiden : UB → UB → UB :=
  fun a b => if b ≤ a then a else UB.top

def counterStep : Pred Nat → Pred Nat :=
  fun x n => n = 0 ∨ ∃ m, x m ∧ n = m + 1

def posLoop : Pred Int → Pred Int :=
  fun x n => n = 1 ∨ ∃ m, x m ∧ n = m + 1

def signPosLoop : Sign → Sign :=
  fun x =>
    match x with
    | Sign.bot => Sign.pos
    | Sign.pos => Sign.pos
    | x => Sign.top

def signLoop : Sign → Sign :=
  fun x =>
    match x with
    | Sign.bot => Sign.zero
    | x => Sign.top

def capSucc : (h : Nat) → Fin (h + 1) → Fin (h + 1) :=
  fun h i => ⟨min (↑i + 1) h, ⋯⟩

def capZero : (h : Nat) → Fin (h + 1) :=
  fun h => ⟨0, ⋯⟩

def capTop : (h : Nat) → Fin (h + 1) :=
  fun h => ⟨h, ⋯⟩

def nonMonoUniqueFix : Pred Bool → Pred Bool :=
  fun x b => x true ∧ ¬x false ∧ b = true ∨ ¬x false ∧ ¬x true

def pTrue : Pred Bool :=
  fun b => b = true

def pFalse : Pred Bool :=
  fun b => b = false

def incr : Int → Int :=
  fun n => n + 1

def decr : Int → Int :=
  fun n => n - 1

def compl : {σ : Type} → Pred σ → Pred σ :=
  fun {σ} x s => ¬x s

```

`counterStep` is the concrete transformer of `x := 0; while * do x := x + 1` on a natural-number variable (its least fixpoint is all of `Nat`, `lfp_counterStep`); `posLoop` that of `x := 1; while * do x := x + 1` on an integer variable, with sound abstraction `signPosLoop` on `Sign`; `nonMonoUniqueFix` is a non-monotone transformer on `Pred Bool` (`∅ ↦ univ`, `{false} ↦ ∅`, `{true} ↦ {true}`, `univ ↦ ∅`) whose unique fixpoint is `{true}` while `lfp nonMonoUniqueFix = ∅`.

**Fixture carriers and orders (Lean source).** The carrier types used by the fixtures, quoted verbatim from the Lean source (modules `Sign`, `Domains` and `Widening`). Each `LE` instance defines `a ≤ b` as `T.leb a b = true`, except for `E2`, where `a ≤ b` is `True` for all `a` and `b`; in a `match`, the first matching alternative applies. Omitted are the `Decidable (a ≤ b)` instances, which only make `≤` decidable through `leb`, and the proofs of the order properties listed in the table above.

```lean
inductive Sign | bot | neg | zero | pos | top
  deriving DecidableEq, Repr
def Sign.leb : Sign → Sign → Bool
  | .bot, _ => true
  | _, .top => true
  | .neg, .neg => true
  | .zero, .zero => true
  | .pos, .pos => true
  | _, _ => false
instance : LE Sign := ⟨fun a b => Sign.leb a b = true⟩

inductive B2 | lo | hi
  deriving DecidableEq, Repr
def B2.leb : B2 → B2 → Bool
  | .lo, _ => true
  | .hi, .hi => true
  | .hi, .lo => false
instance : LE B2 := ⟨fun a b => B2.leb a b = true⟩

inductive NR2 | lo | hi
  deriving DecidableEq, Repr
def NR2.leb : NR2 → NR2 → Bool
  | .lo, _ => true
  | .hi, _ => false
instance : LE NR2 := ⟨fun a b => NR2.leb a b = true⟩

inductive NR3 | lo | mid | hi
  deriving DecidableEq, Repr
def NR3.leb : NR3 → NR3 → Bool
  | .lo, _ => true
  | .mid, .hi => true
  | .hi, .hi => true
  | _, _ => false
instance : LE NR3 := ⟨fun a b => NR3.leb a b = true⟩

inductive NT3 | lo | mid | hi
  deriving DecidableEq, Repr
def NT3.leb : NT3 → NT3 → Bool
  | .lo, .lo => true
  | .mid, .mid => true
  | .hi, .hi => true
  | .lo, .mid => true
  | .mid, .hi => true
  | _, _ => false
instance : LE NT3 := ⟨fun a b => NT3.leb a b = true⟩

inductive NT4 | z | p | q | r
  deriving DecidableEq, Repr
def NT4.leb : NT4 → NT4 → Bool
  | .z, _ => true
  | .p, .p => true
  | .p, .q => true
  | .q, .q => true
  | .q, .r => true
  | .r, .r => true
  | _, _ => false
instance : LE NT4 := ⟨fun a b => NT4.leb a b = true⟩

inductive NT4w | bot | u | t | w
  deriving DecidableEq, Repr
def NT4w.leb : NT4w → NT4w → Bool
  | .bot, _ => true
  | .u, .u => true
  | .u, .bot => true
  | .t, .t => true
  | .t, .u => true
  | .t, .w => true
  | .w, .w => true
  | .w, .t => true
  | .w, .bot => true
  | _, _ => false
instance : LE NT4w := ⟨fun a b => NT4w.leb a b = true⟩

inductive Dis2 | a | b
  deriving DecidableEq, Repr
def Dis2.leb : Dis2 → Dis2 → Bool
  | .a, .a => true
  | .b, .b => true
  | _, _ => false
instance : LE Dis2 := ⟨fun x y => Dis2.leb x y = true⟩

inductive V3 | bot | x | y
  deriving DecidableEq, Repr
def V3.leb : V3 → V3 → Bool
  | .bot, _ => true
  | .x, .x => true
  | .y, .y => true
  | _, _ => false
instance : LE V3 := ⟨fun a b => V3.leb a b = true⟩

inductive W4 | z | m | p | q
  deriving DecidableEq, Repr
def W4.leb : W4 → W4 → Bool
  | .z, _ => true
  | .m, .m => true
  | .m, .p => true
  | .m, .q => true
  | .p, .p => true
  | .q, .q => true
  | _, _ => false
instance : LE W4 := ⟨fun a b => W4.leb a b = true⟩

inductive PT | pt (i j : Nat) | top
  deriving DecidableEq, Repr
def PT.leb : PT → PT → Bool
  | .pt i j, .pt i' j' => decide (i ≤ i') && decide (j ≤ j')
  | _, .top => true
  | .top, .pt _ _ => false
instance : LE PT := ⟨fun a b => PT.leb a b = true⟩

inductive UB | bot | atMost (n : Nat) | top
  deriving DecidableEq, Repr
def UB.leb : UB → UB → Bool
  | .bot, _ => true
  | .atMost m, .atMost n => decide (m ≤ n)
  | _, .top => true
  | _, _ => false
instance : LE UB := ⟨fun a b => UB.leb a b = true⟩

inductive E2 | a | b
  deriving DecidableEq, Repr
instance : LE E2 := ⟨fun _ _ => True⟩

inductive Cyc3 | c0 | c1 | c2
  deriving DecidableEq, Repr
def Cyc3.leb : Cyc3 → Cyc3 → Bool
  | .c0, .c0 => true
  | .c1, .c1 => true
  | .c2, .c2 => true
  | .c0, .c1 => true
  | .c1, .c2 => true
  | .c2, .c0 => true
  | _, _ => false
instance : LE Cyc3 := ⟨fun a b => Cyc3.leb a b = true⟩

inductive NB | mk (n : Nat) (b : Bool)
  deriving DecidableEq, Repr
def NB.leb : NB → NB → Bool
  | .mk m s, .mk n t => decide (m = n) || (s && !t && decide (n = m + 1))
instance : LE NB := ⟨fun a b => NB.leb a b = true⟩

inductive PB | pt (m : Nat) (s : Bool) | top
  deriving DecidableEq, Repr
def PB.leb : PB → PB → Bool
  | .pt m _, .pt n _ => decide (m ≤ n)
  | _, .top => true
  | .top, .pt _ _ => false
instance : LE PB := ⟨fun a b => PB.leb a b = true⟩
```

**Fixture maps and helpers (Lean source).** Every helper and fixture map that occurs in a quoted statement of this report and is not shown in the pretty-printed block above, quoted verbatim from the Lean source (modules `Basic`, `Domains`, `Galois`, `Transformer`, `Fixpoint` and `Widening`; `ptJoin` is included because `ptWiden` uses it). `E` and `U` are abbreviations for the empty and the full predicate on `Unit`; `unitAlpha lo hi x` is `hi` if `x ()` holds and `lo` otherwise, and `b2Alpha`, `nr2Alpha`, `nr3Alpha`, `nt3Alpha` and `nt4Alpha` are instances of it. The `by omega` terms inside `Fin` literals only discharge the bound proof.

```lean
def Pred.empty (σ : Type) : Pred σ := fun _ => False

def Pred.univ (σ : Type) : Pred σ := fun _ => True

abbrev E : Pred Unit := Pred.empty Unit

abbrev U : Pred Unit := Pred.univ Unit

noncomputable def unitAlpha {A : Type} (lo hi : A) (x : Pred Unit) : A :=
  open Classical in if x () then hi else lo

def b2Gamma : B2 → Pred Unit
  | .lo => E
  | .hi => U

noncomputable def b2Alpha : Pred Unit → B2 := unitAlpha B2.lo B2.hi

def b2GammaRev : B2 → Pred Unit
  | .lo => U
  | .hi => E

def nr2Gamma : NR2 → Pred Unit := fun _ => E

noncomputable def nr2Alpha : Pred Unit → NR2 := unitAlpha NR2.lo NR2.hi

def nr3Gamma : NR3 → Pred Unit
  | .lo => E
  | .mid => E
  | .hi => U

noncomputable def nr3Alpha : Pred Unit → NR3 := unitAlpha NR3.lo NR3.mid

def nt3Gamma : NT3 → Pred Unit
  | .lo => E
  | .mid => U
  | .hi => U

noncomputable def nt3Alpha : Pred Unit → NT3 := unitAlpha NT3.lo NT3.mid

def nt4Gamma : NT4 → Pred Unit
  | .z => E
  | .p => U
  | .q => U
  | .r => E

noncomputable def nt4Alpha : Pred Unit → NT4 := unitAlpha NT4.z NT4.p

noncomputable def boolAlpha (x : Pred Bool) : B2 :=
  open Classical in if x ≤ Pred.empty Bool then .lo else .hi

def boolGamma : B2 → Pred Bool
  | .lo => Pred.empty Bool
  | .hi => Pred.univ Bool

def notAtFalse (x : Pred Bool) : Pred Bool := fun _ => ¬ x false

def constTrue (_ : Pred Bool) : Pred Bool := fun s => s = true

def v3Step : V3 → V3
  | .bot => .x
  | .x => .y
  | .y => .x

def dis2Swap : Dis2 → Dis2
  | .a => .b
  | .b => .a

def nbChain (n : Nat) : NB := NB.mk (n / 2) (n % 2 == 1)

def nt4wWiden : NT4w → NT4w → NT4w
  | .bot, .bot => .bot
  | .bot, .u => .u
  | .bot, .t => .u
  | .bot, .w => .bot
  | .u, .bot => .u
  | .u, .u => .u
  | .u, .t => .u
  | .u, .w => .bot
  | .t, .bot => .t
  | .t, .u => .u
  | .t, .t => .t
  | .t, .w => .t
  | .w, .bot => .w
  | .w, .u => .bot
  | .w, .t => .t
  | .w, .w => .w

def nt4wStep : NT4w → NT4w
  | .bot => .t
  | .u => .w
  | .t => .t
  | .w => .t

def w4Widen (_ b : W4) : W4 :=
  match b with
  | .q => .q
  | _ => .p

def w4Step : W4 → W4
  | .z => .m
  | .m => .m
  | .p => .q
  | .q => .p

def ptJoin : PT → PT → PT
  | .pt i j, .pt i' j' => .pt (max i i') (max j j')
  | _, _ => .top

def ptWiden (a b : PT) : PT :=
  if b ≤ a then a
  else if a = PT.pt 0 0 then b
  else if a ≤ b then PT.top
  else ptJoin a b

def ptBadStep : PT → PT
  | .pt i j => if i ≤ j then .pt (j + 1) 0 else .pt 0 (i + 1)
  | .top => .top

def ptShift : PT → PT
  | .pt i j => .pt (i + 1) (j - 1)
  | .top => .top

def flipWiden : E2 → E2 → E2
  | .a, _ => .b
  | .b, _ => .a

def step4 (i : Fin 4) : Fin 4 :=
  if i.val ≤ 1 then ⟨1, by omega⟩ else ⟨3, by omega⟩

def widen4 (a b : Fin 4) : Fin 4 :=
  if a.val = 1 ∧ b.val = 1 then ⟨2, by omega⟩
  else ⟨max a.val b.val, by have := a.isLt; have := b.isLt; omega⟩

def pbWiden : PB → PB → PB
  | .top, _ => .top
  | .pt _ _, .top => .top
  | .pt m false, .pt n _ => if n ≤ m then .pt m true else .top
  | .pt m true, .pt n _ => if n ≤ m then .pt m true else .pt n false

def pbStutter (n : Nat) : PB := .pt ((n + 1) / 2) true
```

Definitions reachable from a statement listed in the **Evidence** tables are part of that statement's definition closure, so they are covered by the closure hash recorded for that statement.

**Facts about the fixtures cited in the text** (pretty-printed statements):

```lean
theorem signGC :
  GaloisConnection signAlpha signGamma

theorem Sign.heightLE :
  HeightLE Sign 2

theorem UB.not_acc :
  ¬ACC UB

theorem UB.not_heightLE :
  ∀ (h : Nat), ¬HeightLE UB h

theorem lfp_counterStep :
  ∀ (k : Nat), lfp counterStep k

theorem post_monotone :
  ∀ {σ : Type} (h : σ → σ), Monotone (post h)
```

#### Definition examples

Proved positive and negative examples for the key definitions, in the order of the key-definition block, followed by examples for the fixtures `ubGamma`, `posLoop` and `signPosLoop` (pretty-printed statements; the fixtures are defined above). A comment states the carrier where the pretty-printer hides an implicit carrier type on which the statement depends.

```lean
theorem pred_example_pos :
  signGamma Sign.pos 1

theorem pred_example_neg :
  ¬signGamma Sign.pos 0

theorem Pred.le_refl :
  ∀ {σ : Type} (x : Pred σ), x ≤ x

theorem le_U :
  ∀ {σ : Type} (x : Pred σ), x ≤ Pred.univ σ

theorem E_le :
  ∀ {σ : Type} (x : Pred σ), Pred.empty σ ≤ x

theorem not_U_le_E :
  ¬U ≤ E

theorem isRefl_example_pos :
  IsRefl B2

theorem isRefl_example_neg :
  ¬IsRefl NR2

theorem isTrans_example_pos :
  IsTrans B2

theorem isTrans_example_neg :
  ¬IsTrans NT3

theorem isAntisymm_example_pos :
  IsAntisymm Sign

theorem isAntisymm_example_neg :
  IsRefl E2 ∧ IsTrans E2 ∧ ¬IsAntisymm E2

theorem isAntisymm_example_neg_nonTrans :
  ¬IsAntisymm NT4w

theorem monotone_example_pos :
  Monotone b2Gamma

theorem monotone_example_neg :
  ¬Monotone (unitAlpha B2.hi B2.lo)

theorem strictLt_example_pos :
  StrictLt Sign.bot Sign.neg

theorem strictLt_example_neg :
  ¬StrictLt Sign.neg Sign.zero

theorem acc_example_pos :
  ACC Sign

theorem acc_example_neg :
  ¬ACC UB

theorem heightLE_example_pos :
  HeightLE Sign 2

theorem heightLE_example_neg :
  ¬HeightLE Sign 1

theorem isBot_example_pos :
  IsBot Sign.bot

theorem isBot_example_neg :
  ¬IsBot Sign.neg

theorem galoisConnection_example_pos :
  GaloisConnection b2Alpha b2Gamma

theorem galoisConnection_example_neg :
  ¬GaloisConnection (fun x => B2.lo) fun x => E

theorem extensive_example_pos :
  Extensive b2Alpha b2Gamma

theorem extensive_example_neg :
  ¬Extensive (fun x => B2.lo) fun x => E

theorem reductive_example_pos :
  Reductive b2Alpha b2Gamma

theorem reductive_example_neg :
  ¬Reductive (fun x => B2.hi) fun x => U

theorem bestTransformer_example_pos :
  bestTransformer signAlpha signGamma (post incr) Sign.pos = Sign.pos

theorem bestTransformer_example_neg :
  bestTransformer signAlpha signGamma (post decr) Sign.pos ≠ Sign.pos

theorem sound_example_pos :
  Sound signGamma (post incr) fun x => Sign.top

theorem sound_example_neg :
  ¬Sound signGamma (post incr) fun x => Sign.bot

theorem post_example_pos :
  post incr (signGamma Sign.zero) 1

theorem post_example_neg :
  ¬post incr (signGamma Sign.zero) 0

theorem lfp_example_pos :
  ∀ (k : Nat), lfp counterStep k

theorem lfp_example_neg :
  ¬lfp (fun x => Pred.empty Nat) 0

theorem isLeastFixpoint_example_pos :
  IsLeastFixpoint (fun x => U) U

theorem isLeastFixpoint_example_neg :
  ¬IsLeastFixpoint id U

theorem postFixpoint_example_pos :
  PostFixpoint ubIncr UB.top

theorem postFixpoint_example_neg :
  ¬PostFixpoint ubIncr (UB.atMost 0)

theorem widenUpperLeft_example_pos :
  WidenUpperLeft ubWiden

theorem widenUpperLeft_example_neg :
  ¬WidenUpperLeft fun x b => b
  -- the operator `fun x b => b` is on `B2` (implicit `A := B2`)

theorem widenUpperRight_example_pos :
  WidenUpperRight ubWiden

theorem widenUpperRight_example_neg :
  ¬WidenUpperRight fun a x => a
  -- the operator `fun a x => a` is on `B2` (implicit `A := B2`)

theorem ascending_example_pos :
  Ascending fun n => n
  -- on `Nat` (implicit `A := Nat`)

theorem ascending_example_neg :
  ¬Ascending fun n => 10 - n
  -- on `Nat` (implicit `A := Nat`; `10 - n` is truncated subtraction)

theorem widenTerminates_example_pos :
  WidenTerminates ubWiden

theorem widenTerminates_example_neg :
  ¬WidenTerminates max
  -- `max` on `Nat` (implicit `A := Nat`)

theorem widenStabilizes_example_pos :
  WidenStabilizes ubWiden

theorem widenStabilizes_example_neg :
  ¬WidenStabilizes max
  -- `max` on `Nat` (implicit `A := Nat`)

theorem kleene_example_pos :
  kleene ubIncr UB.bot 3 = UB.atMost 2

theorem kleene_example_neg :
  kleene ubIncr UB.bot 3 ≠ UB.top

theorem widenChain_example_pos :
  widenChain ubWiden (fun n => UB.atMost n) 1 = UB.top

theorem widenChain_example_neg :
  widenChain ubWiden (fun n => UB.atMost n) 1 ≠ UB.atMost 1

theorem widenIter_example_pos :
  widenIter ubWiden ubIncr UB.bot 1 = UB.top

theorem widenIter_example_neg :
  widenIter ubWiden ubIncr UB.bot 1 ≠ kleene ubIncr UB.bot 1

theorem ubGamma_example_pos :
  ubGamma (UB.atMost 2) 1

theorem ubGamma_example_neg :
  ¬ubGamma (UB.atMost 0) 1

theorem posLoop_example_pos :
  posLoop (Pred.empty Int) 1

theorem posLoop_example_neg :
  ¬posLoop (Pred.empty Int) 2

theorem signPosLoop_example_pos :
  PostFixpoint signPosLoop Sign.pos

theorem signPosLoop_example_neg :
  ¬PostFixpoint signPosLoop Sign.zero
```

### Galois connections

#### R1-gc-iff — `galoisConnection_iff_monotone_extensive_reductive_of_refl_of_trans`

- **Tier:** T0 (re-derivation: a known result restated in this vocabulary). **Kind:** characterization. **Depth:** shallow. **Module:** `Toy.AbsInt.Galois`.
- **Plain claim.** If the abstract order is reflexive and transitive (antisymmetry is not assumed), then alpha : Pred sigma -> A and gamma : A -> Pred sigma form a Galois connection (alpha x <= a iff x is included in gamma a) exactly when alpha and gamma are monotone, x is included in gamma (alpha x) for every x, and alpha (gamma a) <= a for every a.

```lean
theorem galoisConnection_iff_monotone_extensive_reductive_of_refl_of_trans :
  ∀ {σ A : Type} [inst : LE A],
    IsRefl A →
      IsTrans A →
        ∀ (α : Pred σ → A) (γ : A → Pred σ),
          GaloisConnection α γ ↔ Monotone α ∧ Monotone γ ∧ Extensive α γ ∧ Reductive α γ
```

*Unfolded*

```text
For a preorder (A, ≤) (reflexive and transitive, not necessarily antisymmetric) and any α : Pred σ → A, γ : A → Pred σ:
(∀ x a, α x ≤ a ↔ ∀ s, x s → γ a s)  ↔  (∀ x y, x ⊆ y → α x ≤ α y) ∧ (∀ a b, a ≤ b → γ a ⊆ γ b) ∧ (∀ x, x ⊆ γ (α x)) ∧ (∀ a, α (γ a) ≤ a).
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| --- | --- | --- |
| `hrefl : IsRefl A` | Used (only in the Galois-connection-to-laws direction) to instantiate the connection at a = alpha x, which yields extensivity and monotonicity of alpha. | tight: counterexample `gcIff_tight_refl` |
| `htrans : IsTrans A` | Used for monotonicity of gamma (forward direction) and to chain alpha x <= alpha (gamma a) <= a (backward direction). | tight: counterexample `gcIff_tight_trans` |

Each counterexample states that a concrete instance satisfies every other hypothesis, that the dropped hypothesis fails (where stated), and that the conclusion fails:

```lean
theorem gcIff_tight_refl :
  IsTrans NR2 ∧
    ¬IsRefl NR2 ∧
      ¬(GaloisConnection nr2Alpha nr2Gamma ↔
          Monotone nr2Alpha ∧ Monotone nr2Gamma ∧ Extensive nr2Alpha nr2Gamma ∧ Reductive nr2Alpha nr2Gamma)

theorem gcIff_tight_trans :
  IsRefl NT3 ∧
    ¬IsTrans NT3 ∧
      ¬(GaloisConnection nt3Alpha nt3Gamma ↔
          Monotone nt3Alpha ∧ Monotone nt3Gamma ∧ Extensive nt3Alpha nt3Gamma ∧ Reductive nt3Alpha nt3Gamma)

```

- **Non-vacuity witness** (`gc_nonvacuous`). The sign domain (Sign, with its order, signAlpha, signGamma over Pred Int) is reflexive and transitive and is a Galois connection, so both sides of the equivalence are exercised at a true instance.

```lean
theorem gc_nonvacuous :
  IsRefl Sign ∧ IsTrans Sign ∧ GaloisConnection signAlpha signGamma
```

- **Prior art.**
  - P. Cousot and R. Cousot, "Comparing the Galois connection and widening/narrowing approaches to abstract interpretation", PLILP 1992, LNCS 631, pp. 269-295, doi:10.1007/3-540-55844-6_142 (author-hosted reprint). Definition 4: Galois connection between posets, alpha(x) <= y iff x <= gamma(y). Appendix Prop. 24: for posets, this is equivalent to extensive gamma . alpha, reductive alpha . gamma, monotone alpha and monotone gamma. This package weakens posets to preorders (R1-gc-iff) and, for the backward direction, to transitive relations.
  - O. Ore, "Galois connexions", Transactions of the American Mathematical Society 55(3):493-513, 1944, doi:10.1090/S0002-9947-1944-0010555-7. Introduces Galois connections in the antitone form; the definition used here is the isotone form (an adjunction alpha -| gamma).
  - Mathlib (leanprover-community/mathlib4, commit 5f78f9ce46fc85fa3cb45561d47b489c4c98cd04), Mathlib/Order/GaloisConnection/Defs.lean: GaloisConnection l u := forall a b, l a <= b <-> a <= u b over [Preorder] on both sides; GaloisConnection.monotone_intro (monotone u, monotone l, a <= u (l a) and l (u a) <= a give a Galois connection), le_u_l, l_u_le, monotone_u, monotone_l. Preorders are assumed on both sides; the necessity of each order law is not addressed.
  - G. Struth, "Properties of Orderings and Lattices", Archive of Formal Proofs, December 2018, https://isa-afp.org/entries/Order_Lattice_Props.html. Isabelle/HOL theory Galois_Connections defines adjunctions f -| g by (f x <= y) = (x <= g y) and develops their properties; theory Fixpoint_Fusion treats fixpoints under adjunctions.
  - D. Darais and D. Van Horn, "Constructive Galois connections: taming the Galois connection framework for mechanized metatheory", ICFP 2016, pp. 311-324, doi:10.1145/2951913.2951934; journal version "Constructive Galois connections", Journal of Functional Programming 29, e11, 2019, doi:10.1017/S0956796819000066. Agda mechanization of classical and constructive Galois connections and of calculational abstract interpretation; explains why classical abstraction functions on sets (such as signAlpha here) are not computable.
  - P. Cousot and R. Cousot, "Abstract interpretation frameworks", Journal of Logic and Computation 2(4):511-547, 1992, doi:10.1093/logcom/2.4.511 (author-hosted text). Section 5 (p. 520) motivates modelling precision by a preorder that need not be antisymmetric (when the same property can be expressed by several elements), and Sections 4 and 6-8 relax the Galois connection framework to correspondences given by a soundness relation (Section 4, pp. 515-520), by an abstraction relation or function (Section 6, pp. 520-538), by a concretization relation or function only (Section 7, pp. 538-541), and by both (Section 8, pp. 542-544); page numbers as printed in the author-hosted text.
- **Design question.** Which order laws must an abstract-domain interface require for the Galois-connection condition to be equivalent to the four elementary laws (monotone alpha and gamma, extensive gamma . alpha, reductive alpha . gamma)? A preorder suffices; antisymmetry is never needed. Reading the connection as 'alpha x is a most precise sound description of x' additionally relies on reflexivity (see the GaloisConnection definition).

Basis: execution (Lean kernel check). `galoisConnection_iff_monotone_extensive_reductive_of_refl_of_trans` and every counterexample, witness and control named on this card are kernel-checked under Lean v4.34.1; axioms of the main theorem: none.

Basis: derived (modeling bridge). An abstract domain of an analyzer instantiates these definitions when its abstract values carry a precision order satisfying the stated order laws, its concretization maps abstract values to sets of concrete states ordered by inclusion, and its abstraction function maps each set of states to an abstract value. Under those conditions the equivalence transfers. Real domains typically provide a decidable order on representations but no computable abstraction of arbitrary (infinite) sets of states; the statement says nothing about computability.

#### R1-gc-forward — `monotone_extensive_reductive_of_galoisConnection_of_refl_of_trans`

- **Tier:** T0 (re-derivation: a known result restated in this vocabulary). **Kind:** theorem. **Depth:** shallow. **Module:** `Toy.AbsInt.Galois`.
- **Plain claim.** If the abstract order is reflexive and transitive and alpha, gamma form a Galois connection, then alpha and gamma are monotone, gamma . alpha is extensive, and alpha . gamma is reductive.

```lean
theorem monotone_extensive_reductive_of_galoisConnection_of_refl_of_trans :
  ∀ {σ A : Type} [inst : LE A],
    IsRefl A →
      IsTrans A →
        ∀ {α : Pred σ → A} {γ : A → Pred σ},
          GaloisConnection α γ → Monotone α ∧ Monotone γ ∧ Extensive α γ ∧ Reductive α γ
```

*Unfolded*

```text
Preorder A, (∀ x a, α x ≤ a ↔ x ⊆ γ a)  ⟹  α monotone ∧ γ monotone ∧ (∀ x, x ⊆ γ (α x)) ∧ (∀ a, α (γ a) ≤ a).
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| --- | --- | --- |
| `hrefl : IsRefl A` | Gives alpha x <= alpha x, hence extensivity x <= gamma (alpha x) and monotonicity of alpha. | tight: counterexample `gcForward_tight_refl` |
| `htrans : IsTrans A` | Gives monotonicity of gamma from alpha (gamma a) <= a <= b. | tight: counterexample `gcForward_tight_trans` |
| `hgc : GaloisConnection α γ` | The premise being unpacked. | tight: counterexample `gcForward_tight_gc` |

Each counterexample states that a concrete instance satisfies every other hypothesis, that the dropped hypothesis fails (where stated), and that the conclusion fails:

```lean
theorem gcForward_tight_refl :
  IsTrans NR2 ∧
    ¬IsRefl NR2 ∧
      GaloisConnection nr2Alpha nr2Gamma ∧
        ¬(Monotone nr2Alpha ∧ Monotone nr2Gamma ∧ Extensive nr2Alpha nr2Gamma ∧ Reductive nr2Alpha nr2Gamma)

theorem gcForward_tight_trans :
  IsRefl NT4 ∧
    ¬IsTrans NT4 ∧
      GaloisConnection nt4Alpha nt4Gamma ∧
        ¬(Monotone nt4Alpha ∧ Monotone nt4Gamma ∧ Extensive nt4Alpha nt4Gamma ∧ Reductive nt4Alpha nt4Gamma)

theorem gcForward_tight_gc :
  IsRefl B2 ∧
    IsTrans B2 ∧
      (¬GaloisConnection (fun x => B2.lo) fun x => E) ∧
        ¬((Monotone fun x => B2.lo) ∧
            (Monotone fun x => E) ∧ (Extensive (fun x => B2.lo) fun x => E) ∧ Reductive (fun x => B2.lo) fun x => E)

```

- **Non-vacuity witness** (`gc_nonvacuous`). Sign domain: reflexive, transitive, and signAlpha/signGamma form a Galois connection.

```lean
theorem gc_nonvacuous :
  IsRefl Sign ∧ IsTrans Sign ∧ GaloisConnection signAlpha signGamma
```

- **Prior art.**
  - P. Cousot and R. Cousot, "Comparing the Galois connection and widening/narrowing approaches to abstract interpretation", PLILP 1992, LNCS 631, pp. 269-295, doi:10.1007/3-540-55844-6_142 (author-hosted reprint). Appendix Prop. 24 (posets): a Galois connection has monotone alpha and gamma, extensive gamma . alpha and reductive alpha . gamma.
  - Mathlib (leanprover-community/mathlib4, commit 5f78f9ce46fc85fa3cb45561d47b489c4c98cd04), Mathlib/Order/GaloisConnection/Defs.lean: GaloisConnection l u := forall a b, l a <= b <-> a <= u b over [Preorder] on both sides; GaloisConnection.monotone_intro (monotone u, monotone l, a <= u (l a) and l (u a) <= a give a Galois connection), le_u_l, l_u_le, monotone_u, monotone_l. Preorders are assumed on both sides; the necessity of each order law is not addressed.
  - G. Struth, "Properties of Orderings and Lattices", Archive of Formal Proofs, December 2018, https://isa-afp.org/entries/Order_Lattice_Props.html. Isabelle/HOL theory Galois_Connections defines adjunctions f -| g by (f x <= y) = (x <= g y) and develops their properties; theory Fixpoint_Fusion treats fixpoints under adjunctions.
- **Design question.** Reference point. Which derived laws can client code of an abstract domain rely on once a Galois connection is established, and which order law each one costs.

Basis: execution (Lean kernel check). `monotone_extensive_reductive_of_galoisConnection_of_refl_of_trans` and every counterexample, witness and control named on this card are kernel-checked under Lean v4.34.1; axioms of the main theorem: none.

Basis: derived (modeling bridge). Same instantiation conditions as `R1-gc-iff`; client code of such a domain may rely on the four laws once the connection and the two order laws are established.

#### R1-gc-backward — `galoisConnection_of_monotone_extensive_reductive_of_trans`

- **Tier:** T0 (re-derivation: a known result restated in this vocabulary). **Kind:** theorem. **Depth:** shallow. **Module:** `Toy.AbsInt.Galois`.
- **Plain claim.** If the abstract order is transitive (reflexivity not needed), alpha and gamma are monotone, x is included in gamma (alpha x) for all x, and alpha (gamma a) <= a for all a, then alpha and gamma form a Galois connection.

```lean
theorem galoisConnection_of_monotone_extensive_reductive_of_trans :
  ∀ {σ A : Type} [inst : LE A],
    IsTrans A →
      ∀ {α : Pred σ → A} {γ : A → Pred σ}, Monotone α → Monotone γ → Extensive α γ → Reductive α γ → GaloisConnection α γ
```

*Unfolded*

```text
Transitive ≤ on A, α monotone, γ monotone, (∀ x, x ⊆ γ (α x)), (∀ a, α (γ a) ≤ a)  ⟹  ∀ x a, α x ≤ a ↔ x ⊆ γ a.
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| --- | --- | --- |
| `htrans : IsTrans A` | Chains alpha x <= alpha (gamma a) <= a. | tight: counterexample `gcBackward_tight_trans` |
| `hα : Monotone α` | Gives alpha x <= alpha (gamma a) from x included in gamma a. | tight: counterexample `gcBackward_tight_monoAlpha` |
| `hγ : Monotone γ` | Gives gamma (alpha x) included in gamma a from alpha x <= a. | tight: counterexample `gcBackward_tight_monoGamma` |
| `hext : Extensive α γ` | Gives x included in gamma (alpha x). | tight: counterexample `gcBackward_tight_extensive` |
| `hred : Reductive α γ` | Gives alpha (gamma a) <= a. | tight: counterexample `gcBackward_tight_reductive` |

Each counterexample states that a concrete instance satisfies every other hypothesis, that the dropped hypothesis fails (where stated), and that the conclusion fails:

```lean
theorem gcBackward_tight_trans :
  Monotone nt3Alpha ∧
    Monotone nt3Gamma ∧
      Extensive nt3Alpha nt3Gamma ∧ Reductive nt3Alpha nt3Gamma ∧ ¬IsTrans NT3 ∧ ¬GaloisConnection nt3Alpha nt3Gamma

theorem gcBackward_tight_monoAlpha :
  IsTrans B2 ∧
    (Monotone fun x => U) ∧
      (Extensive (unitAlpha B2.hi B2.lo) fun x => U) ∧
        (Reductive (unitAlpha B2.hi B2.lo) fun x => U) ∧
          ¬Monotone (unitAlpha B2.hi B2.lo) ∧ ¬GaloisConnection (unitAlpha B2.hi B2.lo) fun x => U

theorem gcBackward_tight_monoGamma :
  IsTrans B2 ∧
    (Monotone fun x => B2.lo) ∧
      Extensive (fun x => B2.lo) b2GammaRev ∧
        Reductive (fun x => B2.lo) b2GammaRev ∧ ¬Monotone b2GammaRev ∧ ¬GaloisConnection (fun x => B2.lo) b2GammaRev

theorem gcBackward_tight_extensive :
  IsTrans B2 ∧
    (Monotone fun x => B2.lo) ∧
      (Monotone fun x => E) ∧
        (Reductive (fun x => B2.lo) fun x => E) ∧
          (¬Extensive (fun x => B2.lo) fun x => E) ∧ ¬GaloisConnection (fun x => B2.lo) fun x => E

theorem gcBackward_tight_reductive :
  IsTrans B2 ∧
    (Monotone fun x => B2.hi) ∧
      (Monotone fun x => U) ∧
        (Extensive (fun x => B2.hi) fun x => U) ∧
          (¬Reductive (fun x => B2.hi) fun x => U) ∧ ¬GaloisConnection (fun x => B2.hi) fun x => U

```

- **Non-vacuity witness** (`gcBackward_nonvacuous`). Sign domain: transitive, and signAlpha, signGamma satisfy the four laws (derived directly from the proved Galois connection signGC).

```lean
theorem gcBackward_nonvacuous :
  IsTrans Sign ∧ Monotone signAlpha ∧ Monotone signGamma ∧ Extensive signAlpha signGamma ∧ Reductive signAlpha signGamma
```

- **Prior art.**
  - P. Cousot and R. Cousot, "Comparing the Galois connection and widening/narrowing approaches to abstract interpretation", PLILP 1992, LNCS 631, pp. 269-295, doi:10.1007/3-540-55844-6_142 (author-hosted reprint). Definition 4: Galois connection between posets, alpha(x) <= y iff x <= gamma(y). Appendix Prop. 24: for posets, this is equivalent to extensive gamma . alpha, reductive alpha . gamma, monotone alpha and monotone gamma. This package weakens posets to preorders (R1-gc-iff) and, for the backward direction, to transitive relations.
  - Mathlib (leanprover-community/mathlib4, commit 5f78f9ce46fc85fa3cb45561d47b489c4c98cd04), Mathlib/Order/GaloisConnection/Defs.lean: GaloisConnection l u := forall a b, l a <= b <-> a <= u b over [Preorder] on both sides; GaloisConnection.monotone_intro (monotone u, monotone l, a <= u (l a) and l (u a) <= a give a Galois connection), le_u_l, l_u_le, monotone_u, monotone_l. Preorders are assumed on both sides; the necessity of each order law is not addressed.
  - G. Struth, "Properties of Orderings and Lattices", Archive of Formal Proofs, December 2018, https://isa-afp.org/entries/Order_Lattice_Props.html. Isabelle/HOL theory Galois_Connections defines adjunctions f -| g by (f x <= y) = (x <= g y) and develops their properties; theory Fixpoint_Fusion treats fixpoints under adjunctions.
- **Design question.** What must an implementer of a new abstract domain prove to obtain a Galois connection, and with how little order structure.

Basis: execution (Lean kernel check). `galoisConnection_of_monotone_extensive_reductive_of_trans` and every counterexample, witness and control named on this card are kernel-checked under Lean v4.34.1; axioms of the main theorem: none.

Basis: derived (modeling bridge). An implementer who proves monotonicity of both maps, extensivity and reductivity for a domain whose precision order is transitive obtains the Galois connection; the reading `α x` soundly describes `x` additionally needs reflexivity.

### Best abstract transformers

#### R2-best-sound — `bestTransformer_sound_of_galoisConnection_of_refl`

- **Tier:** T0 (re-derivation: a known result restated in this vocabulary). **Kind:** theorem. **Depth:** definitional. **Module:** `Toy.AbsInt.Transformer`.
- **Plain claim.** If alpha, gamma form a Galois connection and the abstract order is reflexive, then for every concrete transformer f (monotone or not) the best abstract transformer alpha . f . gamma is gamma-sound: f (gamma a) is included in gamma (alpha (f (gamma a))) for every a. For non-monotone f this gamma-form constrains f only on the sets gamma a.

```lean
theorem bestTransformer_sound_of_galoisConnection_of_refl :
  ∀ {σ A : Type} [inst : LE A],
    IsRefl A →
      ∀ {α : Pred σ → A} {γ : A → Pred σ},
        GaloisConnection α γ → ∀ (f : Pred σ → Pred σ), Sound γ f (bestTransformer α γ f)
```

*Unfolded*

```text
Reflexive ≤ on A, Galois connection α, γ  ⟹  ∀ f : Pred σ → Pred σ, ∀ a, f (γ a) ⊆ γ (α (f (γ a))).
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| --- | --- | --- |
| `hrefl : IsRefl A` | Instantiates the Galois connection at alpha (f (gamma a)) <= alpha (f (gamma a)). | tight: counterexample `bestSound_tight_refl` |
| `hgc : GaloisConnection α γ` | Turns that inequality into the inclusion. | tight: counterexample `bestSound_tight_gc` |

Each counterexample states that a concrete instance satisfies every other hypothesis, that the dropped hypothesis fails (where stated), and that the conclusion fails:

```lean
theorem bestSound_tight_refl :
  ¬IsRefl NR2 ∧
    GaloisConnection nr2Alpha nr2Gamma ∧ ¬Sound nr2Gamma (fun x => U) (bestTransformer nr2Alpha nr2Gamma fun x => U)

theorem bestSound_tight_gc :
  IsRefl B2 ∧
    (¬GaloisConnection (fun x => B2.lo) fun x => E) ∧
      ¬Sound (fun x => E) (fun x => U) (bestTransformer (fun x => B2.lo) (fun x => E) fun x => U)

```

- **Non-vacuity witness** (`bestSound_nonvacuous`). Sign domain: reflexive and a Galois connection; f is arbitrary (e.g. the concrete transformer of x := x + 1).

```lean
theorem bestSound_nonvacuous :
  IsRefl Sign ∧ GaloisConnection signAlpha signGamma
```

- **Prior art.**
  - P. Cousot and R. Cousot, "Abstract interpretation frameworks", Journal of Logic and Computation 2(4):511-547, 1992, doi:10.1093/logcom/2.4.511 (author-hosted text). Eq. (4.15) gives the best abstract transformer F# = alpha . F . gamma, attributed there to the 1977 and 1979 POPL papers.
  - P. Cousot and R. Cousot, "Systematic design of program analysis frameworks", POPL 1979, pp. 269-282, doi:10.1145/567752.567778. Bibliographic record verified; its content is cited only as attributed by Cousot and Cousot (PLILP 1992; Journal of Logic and Computation 1992): the Galois-connection approach and the best abstract transformer alpha . F . gamma.
  - P. Cousot and R. Cousot, "Comparing the Galois connection and widening/narrowing approaches to abstract interpretation", PLILP 1992, LNCS 631, pp. 269-295, doi:10.1007/3-540-55844-6_142 (author-hosted reprint). Eqs. (4)-(5) and Appendix Prop. 25: functional lifting alpha(phi) = alpha . phi . gamma on monotone maps. Appendix Prop. 26 (posets, monotone F and F#): alpha . F . gamma <= F# iff F . gamma <= gamma . F# iff alpha . F <= F# . alpha. Prop. 26 assumes posets and monotone F and F#; R2-best-sound assumes only a Galois connection over a reflexive abstract order, with no monotonicity of f and no transitivity or antisymmetry (the pointwise characterization R2-best-least needs no order law at all).
  - T. Reps, M. Sagiv and G. Yorsh, "Symbolic implementation of the best transformer", VMCAI 2004, LNCS 2937, pp. 252-266, doi:10.1007/978-3-540-24622-0_21. Computes best abstract transformers alpha . f . gamma symbolically, for single statements or whole blocks.
  - D. Darais and D. Van Horn, "Constructive Galois connections: taming the Galois connection framework for mechanized metatheory", ICFP 2016, pp. 311-324, doi:10.1145/2951913.2951934; journal version "Constructive Galois connections", Journal of Functional Programming 29, e11, 2019, doi:10.1017/S0956796819000066. Agda mechanization of classical and constructive Galois connections and of calculational abstract interpretation; explains why classical abstraction functions on sets (such as signAlpha here) are not computable.
  - P. Cousot, Principles of Abstract Interpretation, MIT Press, 2021, ISBN 978-0-262-04490-5. Monograph; cited as a general reference without section-level attribution.
- **Design question.** Can an analyzer specify each abstract transformer as alpha . f . gamma and rely on its soundness without proving anything about f? For the gamma-form (f (gamma a) included in gamma (f# a)) yes, given a Galois connection over a reflexive order. If the analyzer also relies on soundness for subsets of gamma a (for example individual states), f must be monotone.

Basis: execution (Lean kernel check). `bestTransformer_sound_of_galoisConnection_of_refl` and every counterexample, witness and control named on this card are kernel-checked under Lean v4.34.1; axioms of the main theorem: none.

Basis: derived (modeling bridge). An analyzer that specifies a transfer function as `α ∘ f ∘ γ` obtains `γ`-soundness on the sets `γ a`. Collecting-semantics transformers built as images of sets of states under a statement are monotone (proved here for the image transformer `post h`, `post_monotone`); for such transformers soundness also lifts to subsets of `γ a` (`sound_le_of_le_gamma_of_monotone`). For a semantics whose transformer is not monotone, only the `γ a` form is obtained.

#### R2-best-least — `sound_iff_bestTransformer_le_of_galoisConnection`

- **Tier:** T0 (re-derivation: a known result restated in this vocabulary). **Kind:** characterization. **Depth:** definitional. **Module:** `Toy.AbsInt.Transformer`.
- **Plain claim.** If alpha, gamma form a Galois connection, then an abstract transformer f# is gamma-sound for f (f (gamma a) included in gamma (f# a) for all a) exactly when alpha (f (gamma a)) <= f# a for all a; hence alpha . f . gamma is a pointwise lower bound of all gamma-sound transformers. No order law and no monotonicity of f or f# is assumed.

```lean
theorem sound_iff_bestTransformer_le_of_galoisConnection :
  ∀ {σ A : Type} [inst : LE A] {α : Pred σ → A} {γ : A → Pred σ},
    GaloisConnection α γ → ∀ (f : Pred σ → Pred σ) (fs : A → A), Sound γ f fs ↔ ∀ (a : A), bestTransformer α γ f a ≤ fs a
```

*Unfolded*

```text
Galois connection α, γ  ⟹  ∀ f fs, (∀ a, f (γ a) ⊆ γ (fs a)) ↔ (∀ a, α (f (γ a)) ≤ fs a).
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| --- | --- | --- |
| `hgc : GaloisConnection α γ` | The equivalence is the Galois connection applied pointwise at x = f (gamma a). | tight: counterexample `soundIff_tight_gc` |

Each counterexample states that a concrete instance satisfies every other hypothesis, that the dropped hypothesis fails (where stated), and that the conclusion fails:

```lean
theorem soundIff_tight_gc :
  IsRefl B2 ∧
    IsTrans B2 ∧
      (¬GaloisConnection (fun x => B2.hi) fun x => U) ∧
        ¬((Sound (fun x => U) id fun x => B2.lo) ↔
            ∀ (a : B2), bestTransformer (fun x => B2.hi) (fun x => U) id a ≤ (fun x => B2.lo) a)

```

- **Non-vacuity witness** (`bestSound_nonvacuous`). Sign domain Galois connection (signAlpha, signGamma).

```lean
theorem bestSound_nonvacuous :
  IsRefl Sign ∧ GaloisConnection signAlpha signGamma
```

- **Prior art.**
  - P. Cousot and R. Cousot, "Comparing the Galois connection and widening/narrowing approaches to abstract interpretation", PLILP 1992, LNCS 631, pp. 269-295, doi:10.1007/3-540-55844-6_142 (author-hosted reprint). Eqs. (4)-(5) and Appendix Prop. 25: functional lifting alpha(phi) = alpha . phi . gamma on monotone maps. Appendix Prop. 26 (posets, monotone F and F#): alpha . F . gamma <= F# iff F . gamma <= gamma . F# iff alpha . F <= F# . alpha. Prop. 26 assumes monotone F and F#; R2-best-least assumes neither and no order law.
  - P. Cousot and R. Cousot, "Abstract interpretation frameworks", Journal of Logic and Computation 2(4):511-547, 1992, doi:10.1093/logcom/2.4.511 (author-hosted text). Eq. (4.15) gives the best abstract transformer F# = alpha . F . gamma, attributed there to the 1977 and 1979 POPL papers.
  - P. Cousot and R. Cousot, "Systematic design of program analysis frameworks", POPL 1979, pp. 269-282, doi:10.1145/567752.567778. Bibliographic record verified; its content is cited only as attributed by Cousot and Cousot (PLILP 1992; Journal of Logic and Computation 1992): the Galois-connection approach and the best abstract transformer alpha . F . gamma.
  - D. Darais and D. Van Horn, "Constructive Galois connections: taming the Galois connection framework for mechanized metatheory", ICFP 2016, pp. 311-324, doi:10.1145/2951913.2951934; journal version "Constructive Galois connections", Journal of Functional Programming 29, e11, 2019, doi:10.1017/S0956796819000066. Agda mechanization of classical and constructive Galois connections and of calculational abstract interpretation; explains why classical abstraction functions on sets (such as signAlpha here) are not computable.
- **Design question.** How should a verified analyzer state the correctness of a hand-written abstract transformer? Proving f# a >= alpha (f (gamma a)) pointwise is equivalent to gamma-soundness, given only a Galois connection.

Basis: execution (Lean kernel check). `sound_iff_bestTransformer_le_of_galoisConnection` and every counterexample, witness and control named on this card are kernel-checked under Lean v4.34.1; axioms of the main theorem: none.

Basis: derived (modeling bridge). A verified analyzer can state the correctness of a hand-written transfer function as the pointwise inequality `α (f (γ a)) ≤ f♯ a`, which is equivalent to `γ`-soundness under a Galois connection; real analyzers usually avoid computing `α` on infinite sets and prove the `γ`-form directly, which this result shows is the same condition.

#### R2-best-mono — `bestTransformer_monotone_of_galoisConnection_of_refl_of_trans_of_monotone`

- **Tier:** T0 (re-derivation: a known result restated in this vocabulary). **Kind:** theorem. **Depth:** shallow. **Module:** `Toy.AbsInt.Transformer`.
- **Plain claim.** If alpha, gamma form a Galois connection over a reflexive, transitive abstract order and the concrete transformer f is monotone, then the best abstract transformer alpha . f . gamma is monotone.

```lean
theorem bestTransformer_monotone_of_galoisConnection_of_refl_of_trans_of_monotone :
  ∀ {σ A : Type} [inst : LE A],
    IsRefl A →
      IsTrans A →
        ∀ {α : Pred σ → A} {γ : A → Pred σ},
          GaloisConnection α γ → ∀ {f : Pred σ → Pred σ}, Monotone f → Monotone (bestTransformer α γ f)
```

*Unfolded*

```text
Preorder A, Galois connection α, γ, f monotone  ⟹  ∀ a b, a ≤ b → α (f (γ a)) ≤ α (f (γ b)).
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| --- | --- | --- |
| `hrefl : IsRefl A` | Needed for monotonicity of alpha and extensivity. | tight: counterexample `bestMono_tight_refl` |
| `htrans : IsTrans A` | Needed for monotonicity of gamma. | tight: counterexample `bestMono_tight_trans` |
| `hgc : GaloisConnection α γ` | Supplies monotone alpha, gamma. | tight: counterexample `bestMono_tight_gc` |
| `hf : Monotone f` | Among R2-best-sound, R2-best-least and R2-best-mono, the only place where monotonicity of f is used. In the counterexample, f is compl on Pred Unit (implicit argument sigma := Unit, which the pretty-printer does not show in the conjunct stating that compl is not monotone). | tight: counterexample `bestMono_tight_monoF` |

Each counterexample states that a concrete instance satisfies every other hypothesis, that the dropped hypothesis fails (where stated), and that the conclusion fails:

```lean
theorem bestMono_tight_refl :
  IsTrans NR2 ∧
    ¬IsRefl NR2 ∧
      GaloisConnection nr2Alpha nr2Gamma ∧
        (Monotone fun x => U) ∧ ¬Monotone (bestTransformer nr2Alpha nr2Gamma fun x => U)

theorem bestMono_tight_trans :
  IsRefl NT4 ∧
    ¬IsTrans NT4 ∧ GaloisConnection nt4Alpha nt4Gamma ∧ Monotone id ∧ ¬Monotone (bestTransformer nt4Alpha nt4Gamma id)

theorem bestMono_tight_gc :
  IsRefl B2 ∧
    IsTrans B2 ∧ Monotone id ∧ ¬GaloisConnection b2Alpha b2GammaRev ∧ ¬Monotone (bestTransformer b2Alpha b2GammaRev id)

theorem bestMono_tight_monoF :
  IsRefl B2 ∧
    IsTrans B2 ∧ GaloisConnection b2Alpha b2Gamma ∧ ¬Monotone compl ∧ ¬Monotone (bestTransformer b2Alpha b2Gamma compl)

```

- **Non-vacuity witness** (`bestMono_nonvacuous`). Sign domain with f = post incr (the concrete transformer of x := x + 1).

```lean
theorem bestMono_nonvacuous :
  IsRefl Sign ∧ IsTrans Sign ∧ GaloisConnection signAlpha signGamma ∧ Monotone (post incr)
```

- **Prior art.**
  - P. Cousot and R. Cousot, "Comparing the Galois connection and widening/narrowing approaches to abstract interpretation", PLILP 1992, LNCS 631, pp. 269-295, doi:10.1007/3-540-55844-6_142 (author-hosted reprint). Appendix Prop. 25 and p. 283, where F# = alpha . F . gamma is noted to be monotone for monotone F (posets).
  - P. Cousot and R. Cousot, "Abstract interpretation frameworks", Journal of Logic and Computation 2(4):511-547, 1992, doi:10.1093/logcom/2.4.511 (author-hosted text). Eq. (4.15) gives the best abstract transformer F# = alpha . F . gamma, attributed there to the 1977 and 1979 POPL papers.
- **Design question.** Does using best transformers automatically discharge the monotonicity premise of Kleene iteration (R4-kleene-acc, R4-kleene-height) and of iteration with widening (R5-widen)? Yes when the concrete transformer is monotone and the domain is a preorder with a Galois connection; the counterexamples show which premise breaks it otherwise.

Basis: execution (Lean kernel check). `bestTransformer_monotone_of_galoisConnection_of_refl_of_trans_of_monotone` and every counterexample, witness and control named on this card are kernel-checked under Lean v4.34.1; axioms of the main theorem: none.

Basis: derived (modeling bridge). When an analyzer uses best transformers of a monotone collecting semantics over a preorder with a Galois connection, the monotonicity premise of `R4-kleene-acc`, `R4-kleene-height` and `R5-widen` is discharged; analyzers whose transfer functions are not best transformers must establish monotonicity separately.

### Composition of best transformers

#### R3-comp-le — `bestTransformer_comp_le_of_galoisConnection_of_refl_of_monotone`

- **Tier:** T0 (re-derivation: a known result restated in this vocabulary). **Kind:** theorem. **Depth:** shallow. **Module:** `Toy.AbsInt.Transformer`.
- **Plain claim.** If alpha, gamma form a Galois connection over a reflexive abstract order and f is monotone, then for every g and every abstract a, the best transformer of the composition is below the composition of best transformers: (f . g)# a <= f# (g# a). Transitivity and monotonicity of g are not needed.

```lean
theorem bestTransformer_comp_le_of_galoisConnection_of_refl_of_monotone :
  ∀ {σ A : Type} [inst : LE A],
    IsRefl A →
      ∀ {α : Pred σ → A} {γ : A → Pred σ},
        GaloisConnection α γ →
          ∀ {f : Pred σ → Pred σ},
            Monotone f →
              ∀ (g : Pred σ → Pred σ) (a : A),
                bestTransformer α γ (f ∘ g) a ≤ bestTransformer α γ f (bestTransformer α γ g a)
```

*Unfolded*

```text
Reflexive ≤ on A, Galois connection α, γ, f monotone  ⟹  ∀ g a, α (f (g (γ a))) ≤ α (f (γ (α (g (γ a))))).
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| --- | --- | --- |
| `hrefl : IsRefl A` | Extensivity x included in gamma (alpha x), used twice. | tight: counterexample `compLe_tight_refl` |
| `hgc : GaloisConnection α γ` | Extensivity, and the final conversion of an inclusion into <=. | tight: counterexample `compLe_tight_gc` |
| `hf : Monotone f` | Pushes g (gamma a) included in gamma (alpha (g (gamma a))) through f. | tight: counterexample `compLe_tight_monoF` |

Each counterexample states that a concrete instance satisfies every other hypothesis, that the dropped hypothesis fails (where stated), and that the conclusion fails:

```lean
theorem compLe_tight_refl :
  ¬IsRefl NR2 ∧
    GaloisConnection nr2Alpha nr2Gamma ∧
      Monotone id ∧
        ¬bestTransformer nr2Alpha nr2Gamma (id ∘ fun x => U) NR2.lo ≤
            bestTransformer nr2Alpha nr2Gamma id (bestTransformer nr2Alpha nr2Gamma (fun x => U) NR2.lo)

theorem compLe_tight_gc :
  IsRefl B2 ∧
    Monotone id ∧
      (¬GaloisConnection b2Alpha fun x => E) ∧
        ¬bestTransformer b2Alpha (fun x => E) (id ∘ fun x => U) B2.lo ≤
            bestTransformer b2Alpha (fun x => E) id (bestTransformer b2Alpha (fun x => E) (fun x => U) B2.lo)

theorem compLe_tight_monoF :
  IsRefl B2 ∧
    GaloisConnection boolAlpha boolGamma ∧
      ¬Monotone notAtFalse ∧
        ¬bestTransformer boolAlpha boolGamma (notAtFalse ∘ constTrue) B2.lo ≤
            bestTransformer boolAlpha boolGamma notAtFalse (bestTransformer boolAlpha boolGamma constTrue B2.lo)

```

- **Non-vacuity witness** (`compLe_nonvacuous`). Sign domain with f = post decr.

```lean
theorem compLe_nonvacuous :
  IsRefl Sign ∧ GaloisConnection signAlpha signGamma ∧ Monotone (post decr)
```

- **Prior art.**
  - R. Giacobazzi, F. Ranzato and F. Scozzari, "Making abstract interpretations complete", Journal of the ACM 47(2):361-416, 2000, doi:10.1145/333979.333989. Theory of completeness (no loss of precision in abstract computation) and of refining or simplifying abstract domains to obtain it; the escape hatches of R3-comp-strict are completeness conditions in this sense.
  - A. Thakur, A. Lal, J. Lim and T. Reps, "PostHat and all that: automating abstract interpretation", Electronic Notes in Theoretical Computer Science 311:15-32, 2015, doi:10.1016/j.entcs.2015.02.003. Example 1.2 (author preprint): for two machine instructions, applying the best transformer of each in sequence yields top, whereas the best transformer of the sequential composition yields eax' = 42, because the intermediate state is not expressible in the abstract domain.
  - T. Reps, M. Sagiv and G. Yorsh, "Symbolic implementation of the best transformer", VMCAI 2004, LNCS 2937, pp. 252-266, doi:10.1007/978-3-540-24622-0_21. Computes best abstract transformers alpha . f . gamma symbolically, for single statements or whole blocks.
  - X. Rival and K. Yi, Introduction to Static Analysis: An Abstract Interpretation Perspective, MIT Press, 2020, ISBN 978-0-262-04341-0. Textbook; cited as a general reference without section-level attribution.
- **Design question.** Should an analyzer abstract whole blocks (one best transformer of the composed concrete semantics) or compose per-statement best transformers? Composition is never more precise and is sometimes strictly less precise.

Basis: execution (Lean kernel check). `bestTransformer_comp_le_of_galoisConnection_of_refl_of_monotone` and every counterexample, witness and control named on this card are kernel-checked under Lean v4.34.1; axioms of the main theorem: none.

Basis: derived (modeling bridge). An analyzer that composes per-statement best transformers is never more precise than one that abstracts the composed block, provided the later statement's concrete transformer is monotone. Real analyzers rarely compute best transformers exactly, so this bounds an idealized analyzer only.

#### R3-comp-strict — `bestTransformer_comp_strict_sign`

- **Tier:** T0 (re-derivation: a known result restated in this vocabulary). **Kind:** counterexample. **Depth:** shallow. **Module:** `Toy.AbsInt.Transformer`.
- **Plain claim.** In the sign domain over Int, with g the concrete transformer of x := x + 1 and f that of x := x - 1, all hypotheses of R3-comp-le hold, (f . g)# pos = pos, g# pos = pos and f# pos = top, so (f . g)# pos < f# (g# pos) strictly (pos <= top and not top <= pos).

```lean
theorem bestTransformer_comp_strict_sign :
  GaloisConnection signAlpha signGamma ∧
    IsRefl Sign ∧
      IsTrans Sign ∧
        Monotone (post decr) ∧
          Monotone (post incr) ∧
            bestTransformer signAlpha signGamma (post incr) Sign.pos = Sign.pos ∧
              bestTransformer signAlpha signGamma (post decr) Sign.pos = Sign.top ∧
                bestTransformer signAlpha signGamma (post decr ∘ post incr) Sign.pos = Sign.pos ∧
                  StrictLt (bestTransformer signAlpha signGamma (post decr ∘ post incr) Sign.pos)
                    (bestTransformer signAlpha signGamma (post decr)
                      (bestTransformer signAlpha signGamma (post incr) Sign.pos))
```

*Unfolded*

```text
With g = post incr (x := x + 1), f = post decr (x := x − 1) on Pred Int and the sign domain: all hypotheses of R3-comp-le hold, signAlpha (g (signGamma pos)) = pos, signAlpha (f (signGamma pos)) = top, signAlpha (f (g (signGamma pos))) = pos, and pos ≤ top ∧ ¬ (top ≤ pos), i.e. (f ∘ g)♯ pos < f♯ (g♯ pos) strictly.
```

**Hypothesis ledger.** None: the statement is about explicitly given instances, and the relevant hypotheses of the general theorem it illustrates are proved as conjuncts of the statement.

- **Non-vacuity witness.** The statement is itself a concrete instance.

- **Positive control** (`bestTransformer_comp_exact_sign_incr`), a nearby setting where the conclusion fails:

```lean
theorem bestTransformer_comp_exact_sign_incr :
  bestTransformer signAlpha signGamma (post incr ∘ post incr) Sign.pos = Sign.pos ∧
    bestTransformer signAlpha signGamma (post incr) (bestTransformer signAlpha signGamma (post incr) Sign.pos) = Sign.pos
```

- **Prior art.**
  - A. Thakur, A. Lal, J. Lim and T. Reps, "PostHat and all that: automating abstract interpretation", Electronic Notes in Theoretical Computer Science 311:15-32, 2015, doi:10.1016/j.entcs.2015.02.003. Example 1.2 (author preprint): for two machine instructions, applying the best transformer of each in sequence yields top, whereas the best transformer of the sequential composition yields eax' = 42, because the intermediate state is not expressible in the abstract domain.
  - R. Giacobazzi, F. Ranzato and F. Scozzari, "Making abstract interpretations complete", Journal of the ACM 47(2):361-416, 2000, doi:10.1145/333979.333989. Theory of completeness (no loss of precision in abstract computation) and of refining or simplifying abstract domains to obtain it; the escape hatches of R3-comp-strict are completeness conditions in this sense.
  - A. Miné, "Tutorial on static inference of numeric invariants by abstract interpretation", Foundations and Trends in Programming Languages 4(3-4):120-372, 2017, doi:10.1561/2500000034. Tutorial covering Galois connections, the sign and interval domains, and widening.
- **Design question.** Is the inequality of R3-comp-le ever strict in a domain an analyzer would actually use? Yes, already in the sign domain.

Basis: execution (Lean kernel check). `bestTransformer_comp_strict_sign` and every counterexample, witness and control named on this card are kernel-checked under Lean v4.34.1; axioms of the main theorem: `Classical.choice`, `Quot.sound`, `propext`.

Basis: derived (modeling bridge). The sign domain and the statements `x := x + 1`, `x := x - 1` are standard textbook examples; the strict loss shown here is the same phenomenon as the published machine-code example of Thakur et al. (2015, Example 1.2), but only this toy instance is formalized.

### Least fixpoints and fixpoint transfer

#### R4-lfp-fix — `lfp_eq_of_monotone`

- **Tier:** T0 (re-derivation: a known result restated in this vocabulary). **Kind:** theorem. **Depth:** shallow. **Module:** `Toy.AbsInt.Fixpoint`.
- **Plain claim.** For a monotone concrete transformer f on predicates, the intersection lfp f of all post-fixpoints {x | f x included in x} is a fixpoint: f (lfp f) = lfp f.

```lean
theorem lfp_eq_of_monotone :
  ∀ {σ : Type} {f : Pred σ → Pred σ}, Monotone f → f (lfp f) = lfp f
```

*Unfolded*

```text
f monotone on Pred σ  ⟹  f (fun s => ∀ x, f x ⊆ x → x s) = (fun s => ∀ x, f x ⊆ x → x s).
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| --- | --- | --- |
| `hf : Monotone f` | Knaster-Tarski argument. In the counterexample, f is compl on Pred Unit (implicit argument sigma := Unit, which the pretty-printer does not show). | tight: counterexample `lfpEq_tight_monotone` |

Each counterexample states that a concrete instance satisfies every other hypothesis, that the dropped hypothesis fails (where stated), and that the conclusion fails:

```lean
theorem lfpEq_tight_monotone :
  ¬Monotone compl ∧ ¬compl (lfp compl) = lfp compl

```

- **Non-vacuity witness** (`lfpEq_nonvacuous`). counterStep (the concrete transformer of x := 0; while * do x := x + 1) is monotone.

```lean
theorem lfpEq_nonvacuous :
  Monotone counterStep
```

- **Prior art.**
  - B. Knaster, "Un théorème sur les fonctions d'ensembles", Annales de la Société Polonaise de Mathématique 6:133-134, 1928. The fixpoint theorem for monotone set functions on a powerset, the setting Pred sigma of this package.
  - A. Tarski, "A lattice-theoretical fixpoint theorem and its applications", Pacific Journal of Mathematics 5(2):285-309, 1955, doi:10.2140/pjm.1955.5.285. The fixpoints of a monotone map on a complete lattice form a complete lattice; the least fixpoint is the infimum of {x | f x <= x}.
  - Mathlib (leanprover-community/mathlib4, commit 5f78f9ce46fc85fa3cb45561d47b489c4c98cd04), Mathlib/Order/FixedPoints.lean: OrderHom.lfp f := sInf {a | f a <= a} for a bundled monotone map f on a complete lattice, with map_lfp (f (lfp f) = lfp f) and lfp_le.
- **Design question.** Is the collecting semantics of a loop, defined as an intersection of invariants, actually a fixpoint? Yes for monotone transformers.

Basis: execution (Lean kernel check). `lfp_eq_of_monotone` and every counterexample, witness and control named on this card are kernel-checked under Lean v4.34.1; axioms of the main theorem: `Quot.sound`, `propext`.

Basis: derived (modeling bridge). The collecting semantics of a loop is commonly defined as the least fixpoint of a monotone transformer on sets of states; for monotone `f`, `lfp f` as defined here is that fixpoint.

#### R4-lfp-least — `lfp_le_of_le`

- **Tier:** T0 (re-derivation: a known result restated in this vocabulary). **Kind:** theorem. **Depth:** definitional. **Module:** `Toy.AbsInt.Fixpoint`.
- **Plain claim.** For every concrete transformer f (monotone or not) and every concrete post-fixpoint x (f x included in x), lfp f is included in x.

```lean
theorem lfp_le_of_le :
  ∀ {σ : Type} (f : Pred σ → Pred σ) (x : Pred σ), f x ≤ x → lfp f ≤ x
```

*Unfolded*

```text
f x ⊆ x  ⟹  (fun s => ∀ y, f y ⊆ y → y s) ⊆ x.
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| --- | --- | --- |
| `hx : f x ≤ x` | Defining condition of the sets that lfp intersects. | tight: counterexample `lfpLe_tight_postFixpoint` |

Each counterexample states that a concrete instance satisfies every other hypothesis, that the dropped hypothesis fails (where stated), and that the conclusion fails:

```lean
theorem lfpLe_tight_postFixpoint :
  ¬counterStep (Pred.empty Nat) ≤ Pred.empty Nat ∧ ¬lfp counterStep ≤ Pred.empty Nat

```

- **Non-vacuity witness** (`lfpLe_nonvacuous`). counterStep with x = all naturals. All hypotheses hold, but the conclusion lfp counterStep included in all naturals is trivially true for this x; necessity of the hypothesis is shown separately by lfpLe_tight_postFixpoint (x = empty).

```lean
theorem lfpLe_nonvacuous :
  counterStep (Pred.univ Nat) ≤ Pred.univ Nat
```

- **Prior art.**
  - A. Tarski, "A lattice-theoretical fixpoint theorem and its applications", Pacific Journal of Mathematics 5(2):285-309, 1955, doi:10.2140/pjm.1955.5.285. The fixpoints of a monotone map on a complete lattice form a complete lattice; the least fixpoint is the infimum of {x | f x <= x}.
  - Mathlib (leanprover-community/mathlib4, commit 5f78f9ce46fc85fa3cb45561d47b489c4c98cd04), Mathlib/Order/FixedPoints.lean: OrderHom.lfp_le is stated for bundled monotone maps; the statement for an arbitrary f is an instance of the complete-lattice fact sInf_le (an infimum is below each member of the set).
- **Design question.** Reference point. What does an analyzer need to prove about a candidate invariant to conclude it contains lfp f? Only that it is closed under the concrete transformer.

Basis: execution (Lean kernel check). `lfp_le_of_le` and every counterexample, witness and control named on this card are kernel-checked under Lean v4.34.1; axioms of the main theorem: none.

Basis: derived (modeling bridge). An analyzer that wants to show that a candidate set of states contains `lfp f` needs only that the set is closed under the concrete transformer.

#### R4-transfer — `lfp_le_gamma_of_monotone_gamma_of_sound_of_postFixpoint`

- **Tier:** T0 (re-derivation: a known result restated in this vocabulary). **Kind:** theorem. **Depth:** shallow. **Module:** `Toy.AbsInt.Fixpoint`.
- **Plain claim.** If gamma is monotone and the abstract transformer f# is gamma-sound for f (f (gamma a) included in gamma (f# a) for all a), then for every abstract post-fixpoint a (f# a <= a), lfp f, the intersection of all concrete post-fixpoints {x | f x included in x}, is included in gamma a. No abstraction function, Galois connection, order law on A, or monotonicity of f or f# is assumed; lfp f is guaranteed to be the concrete least fixpoint only when f is monotone (without monotonicity it need not be a fixpoint; R4-transfer-lfp).

```lean
theorem lfp_le_gamma_of_monotone_gamma_of_sound_of_postFixpoint :
  ∀ {σ A : Type} [inst : LE A] {γ : A → Pred σ} {f : Pred σ → Pred σ} {fs : A → A},
    Monotone γ → Sound γ f fs → ∀ {a : A}, PostFixpoint fs a → lfp f ≤ γ a
```

*Unfolded*

```text
γ monotone, (∀ a, f (γ a) ⊆ γ (fs a)), fs a ≤ a  ⟹  (fun s => ∀ x, f x ⊆ x → x s) ⊆ γ a.   (The left side is the intersection of all concrete post-fixpoints; it is guaranteed to be the least fixpoint of f only when f is monotone; without monotonicity it need not be a fixpoint.)
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| --- | --- | --- |
| `hγ : Monotone γ` | Turns f# a <= a into gamma (f# a) included in gamma a. | tight: counterexample `lfpGamma_tight_monoGamma` |
| `hs : Sound γ f fs` | Gives f (gamma a) included in gamma (f# a), so gamma a is a concrete post-fixpoint. | tight: counterexample `lfpGamma_tight_sound` |
| `ha : PostFixpoint fs a` | The abstract invariant condition f# a <= a. | tight: counterexample `lfpGamma_tight_postFixpoint` |

Each counterexample states that a concrete instance satisfies every other hypothesis, that the dropped hypothesis fails (where stated), and that the conclusion fails:

```lean
theorem lfpGamma_tight_monoGamma :
  (Sound b2GammaRev (fun x => U) fun x => B2.lo) ∧
    PostFixpoint (fun x => B2.lo) B2.hi ∧ ¬Monotone b2GammaRev ∧ ¬(lfp fun x => U) ≤ b2GammaRev B2.hi

theorem lfpGamma_tight_sound :
  Monotone b2Gamma ∧ PostFixpoint id B2.lo ∧ ¬Sound b2Gamma (fun x => U) id ∧ ¬(lfp fun x => U) ≤ b2Gamma B2.lo

theorem lfpGamma_tight_postFixpoint :
  Monotone b2Gamma ∧
    (Sound b2Gamma (fun x => U) fun x => B2.hi) ∧ ¬PostFixpoint (fun x => B2.hi) B2.lo ∧ ¬(lfp fun x => U) ≤ b2Gamma B2.lo

```

- **Non-vacuity witness** (`lfpGamma_nonvacuous`). Sign domain over Int with the loop x := 1; while * do x := x + 1 (posLoop), its sound abstraction signPosLoop, and the post-fixpoint pos, whose concretization {n | 0 < n} is not the full set.

```lean
theorem lfpGamma_nonvacuous :
  Monotone signGamma ∧ Sound signGamma posLoop signPosLoop ∧ PostFixpoint signPosLoop Sign.pos ∧ ¬signGamma Sign.pos 0
```

- **Prior art.**
  - T. Nipkow and G. Klein, Concrete Semantics with Isabelle/HOL, Springer 2014, doi:10.1007/978-3-319-10542-0; Chapter 13 "Abstract Interpretation", pp. 219-280, doi:10.1007/978-3-319-10542-0_13. The framework uses concretization functions only (no abstraction function, no Galois connection); its correctness theorem (AI_correct in the accompanying Isabelle theories) transfers an abstract post-fixpoint to the collecting semantics using monotonicity of gamma and the lower-bound property of lfp. The book calls x with f x <= x a pre-fixpoint.
  - J.-H. Jourdan, V. Laporte, S. Blazy, X. Leroy and D. Pichardie, "A formally-verified C static analyzer", POPL 2015, pp. 247-259, doi:10.1145/2676726.2676966. A Coq-verified abstract interpreter (Verasco) whose abstract domains are specified by concretization-based soundness without Galois connections or abstraction functions, and whose post-fixpoint iteration with widening is bounded by fuel rather than justified by a widening termination proof.
  - P. Cousot and R. Cousot, "Comparing the Galois connection and widening/narrowing approaches to abstract interpretation", PLILP 1992, LNCS 631, pp. 269-295, doi:10.1007/3-540-55844-6_142 (author-hosted reprint). Appendix Prop. 32: on a concrete poset with continuous F, F(A) <= A and bottom <= A imply lfp F <= A. Appendix Prop. 35 ("preordered upward iteration with widening"): with the abstract preorder defined by x <= y iff gamma(x) <= gamma(y), continuous F, monotone F#, F . gamma <= gamma . F# and a widening, the stopping iteration (9) ends at A with lfp F <= gamma(A). R4-transfer isolates the transfer step of Prop. 35 and drops continuity, the gamma-induced preorder and the widening.
  - P. Cousot and R. Cousot, "Abstract interpretation frameworks", Journal of Logic and Computation 2(4):511-547, 1992, doi:10.1093/logcom/2.4.511 (author-hosted text). Section 5 (p. 520) motivates modelling precision by a preorder that need not be antisymmetric (when the same property can be expressed by several elements), and Sections 4 and 6-8 relax the Galois connection framework to correspondences given by a soundness relation (Section 4, pp. 515-520), by an abstraction relation or function (Section 6, pp. 520-538), by a concretization relation or function only (Section 7, pp. 538-541), and by both (Section 8, pp. 542-544); page numbers as printed in the author-hosted text.
  - F. Besson, D. Cachera, T. Jensen and D. Pichardie, "Certified static analysis by abstract interpretation", Foundations of Security Analysis and Design V, LNCS 5705, pp. 223-257, 2009, doi:10.1007/978-3-642-03829-7_8. Tutorial on building and proving an abstract interpreter (an interval analysis) in Coq.
  - T. Nipkow, "Abstract interpretation of annotated commands", ITP 2012, LNCS 7406, pp. 116-132, doi:10.1007/978-3-642-32347-8_9, with the Archive of Formal Proofs entry Abs_Int_ITP2012. Isabelle/HOL abstract interpreter with widening and narrowing, the predecessor of the Concrete Semantics development.
- **Design question.** What is the minimal soundness interface an analyzer needs to justify that gamma of a checked abstract invariant contains lfp f? Monotone gamma, gamma-soundness of the transformer, and a checked post-fixpoint; no abstraction function or Galois connection. Identifying lfp f with the concrete least fixpoint (the collecting semantics) additionally needs a monotone concrete transformer (R4-transfer-lfp).

Basis: execution (Lean kernel check). `lfp_le_gamma_of_monotone_gamma_of_sound_of_postFixpoint` and every counterexample, witness and control named on this card are kernel-checked under Lean v4.34.1; axioms of the main theorem: none.

Basis: derived (modeling bridge). A verified analyzer that checks `f♯ a ≤ a` for an abstract invariant `a`, with `γ` monotone and `f♯` proved `γ`-sound, may conclude `lfp f ⊆ γ a` with no abstraction function. Identifying `lfp f` with the collecting semantics requires that the collecting semantics be the least fixpoint of a monotone transformer (`R4-transfer-lfp`).

#### R4-transfer-lfp — `isLeastFixpoint_lfp_and_le_gamma_of_monotone_of_monotone_gamma_of_sound_of_postFixpoint`

- **Tier:** T0 (re-derivation: a known result restated in this vocabulary). **Kind:** theorem. **Depth:** shallow. **Module:** `Toy.AbsInt.Fixpoint`.
- **Plain claim.** If the concrete transformer f is monotone, gamma is monotone, f# is gamma-sound for f, and a is an abstract post-fixpoint (f# a <= a), then lfp f is the least fixpoint of f and every least fixpoint of f is included in gamma a: the abstract invariant over-approximates the concrete least fixpoint (the collecting semantics).

```lean
theorem isLeastFixpoint_lfp_and_le_gamma_of_monotone_of_monotone_gamma_of_sound_of_postFixpoint :
  ∀ {σ A : Type} [inst : LE A] {γ : A → Pred σ} {f : Pred σ → Pred σ} {fs : A → A},
    Monotone f →
      Monotone γ →
        Sound γ f fs →
          ∀ {a : A}, PostFixpoint fs a → IsLeastFixpoint f (lfp f) ∧ ∀ (x : Pred σ), IsLeastFixpoint f x → x ≤ γ a
```

*Unfolded*

```text
f monotone, γ monotone, (∀ a, f (γ a) ⊆ γ (fs a)), fs a ≤ a  ⟹  [f L = L ∧ ∀ y, f y = y → L ⊆ y] ∧ ∀ x, (f x = x ∧ ∀ y, f y = y → x ⊆ y) → x ⊆ γ a,  where L = (fun s => ∀ x, f x ⊆ x → x s).
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| --- | --- | --- |
| `hf : Monotone f` | Makes lfp f a fixpoint (Knaster-Tarski) and hence the least fixpoint; without it gamma a can miss the unique fixpoint of f. | tight: counterexample `lfpFixGamma_tight_monotone` |
| `hγ : Monotone γ` | Turns f# a <= a into gamma (f# a) included in gamma a. | tight: counterexample `lfpFixGamma_tight_monoGamma` |
| `hs : Sound γ f fs` | Makes gamma a a concrete post-fixpoint. | tight: counterexample `lfpFixGamma_tight_sound` |
| `ha : PostFixpoint fs a` | The abstract invariant condition f# a <= a. | tight: counterexample `lfpFixGamma_tight_postFixpoint` |

Each counterexample states that a concrete instance satisfies every other hypothesis, that the dropped hypothesis fails (where stated), and that the conclusion fails:

```lean
theorem lfpFixGamma_tight_monotone :
  ¬Monotone nonMonoUniqueFix ∧
    Monotone id ∧
      Sound id nonMonoUniqueFix nonMonoUniqueFix ∧
        PostFixpoint nonMonoUniqueFix pFalse ∧
          ¬(IsLeastFixpoint nonMonoUniqueFix (lfp nonMonoUniqueFix) ∧
                ∀ (x : Pred Bool), IsLeastFixpoint nonMonoUniqueFix x → x ≤ id pFalse) ∧
            IsLeastFixpoint nonMonoUniqueFix pTrue ∧
              ¬pTrue ≤ id pFalse ∧ ¬IsLeastFixpoint nonMonoUniqueFix (lfp nonMonoUniqueFix)

theorem lfpFixGamma_tight_monoGamma :
  (Monotone fun x => U) ∧
    ¬Monotone b2GammaRev ∧
      (Sound b2GammaRev (fun x => U) fun x => B2.lo) ∧
        PostFixpoint (fun x => B2.lo) B2.hi ∧
          ¬(IsLeastFixpoint (fun x => U) (lfp fun x => U) ∧
              ∀ (x : Pred Unit), IsLeastFixpoint (fun x => U) x → x ≤ b2GammaRev B2.hi)

theorem lfpFixGamma_tight_sound :
  (Monotone fun x => U) ∧
    Monotone b2Gamma ∧
      PostFixpoint id B2.lo ∧
        ¬Sound b2Gamma (fun x => U) id ∧
          ¬(IsLeastFixpoint (fun x => U) (lfp fun x => U) ∧
              ∀ (x : Pred Unit), IsLeastFixpoint (fun x => U) x → x ≤ b2Gamma B2.lo)

theorem lfpFixGamma_tight_postFixpoint :
  (Monotone fun x => U) ∧
    Monotone b2Gamma ∧
      (Sound b2Gamma (fun x => U) fun x => B2.hi) ∧
        ¬PostFixpoint (fun x => B2.hi) B2.lo ∧
          ¬(IsLeastFixpoint (fun x => U) (lfp fun x => U) ∧
              ∀ (x : Pred Unit), IsLeastFixpoint (fun x => U) x → x ≤ b2Gamma B2.lo)

```

- **Non-vacuity witness** (`lfpFixGamma_nonvacuous`). Sign domain over Int with the monotone loop transformer posLoop (x := 1; while * do x := x + 1), its sound abstraction signPosLoop, and the post-fixpoint pos, whose concretization {n | 0 < n} is not the full set.

```lean
theorem lfpFixGamma_nonvacuous :
  Monotone posLoop ∧
    Monotone signGamma ∧ Sound signGamma posLoop signPosLoop ∧ PostFixpoint signPosLoop Sign.pos ∧ ¬signGamma Sign.pos 0
```

- **Prior art.**
  - T. Nipkow and G. Klein, Concrete Semantics with Isabelle/HOL, Springer 2014, doi:10.1007/978-3-319-10542-0; Chapter 13 "Abstract Interpretation", pp. 219-280, doi:10.1007/978-3-319-10542-0_13. The framework uses concretization functions only (no abstraction function, no Galois connection); its correctness theorem (AI_correct in the accompanying Isabelle theories) transfers an abstract post-fixpoint to the collecting semantics using monotonicity of gamma and the lower-bound property of lfp. The book calls x with f x <= x a pre-fixpoint.
  - P. Cousot and R. Cousot, "Comparing the Galois connection and widening/narrowing approaches to abstract interpretation", PLILP 1992, LNCS 631, pp. 269-295, doi:10.1007/3-540-55844-6_142 (author-hosted reprint). Appendix Prop. 32: on a concrete poset with continuous F, F(A) <= A and bottom <= A imply lfp F <= A. Appendix Prop. 35 ("preordered upward iteration with widening"): with the abstract preorder defined by x <= y iff gamma(x) <= gamma(y), continuous F, monotone F#, F . gamma <= gamma . F# and a widening, the stopping iteration (9) ends at A with lfp F <= gamma(A). R4-transfer-lfp keeps only monotonicity of the concrete transformer f (weaker than the continuity assumed in Prop. 35), drops the gamma-induced preorder (no order law on A is assumed), monotonicity of F# and the widening, and concludes both that lfp f is the least fixpoint of f and that every least fixpoint of f is included in gamma a.
  - B. Knaster, "Un théorème sur les fonctions d'ensembles", Annales de la Société Polonaise de Mathématique 6:133-134, 1928. The fixpoint theorem for monotone set functions on a powerset, the setting Pred sigma of this package.
  - A. Tarski, "A lattice-theoretical fixpoint theorem and its applications", Pacific Journal of Mathematics 5(2):285-309, 1955, doi:10.2140/pjm.1955.5.285. The fixpoints of a monotone map on a complete lattice form a complete lattice; the least fixpoint is the infimum of {x | f x <= x}.
  - J.-H. Jourdan, V. Laporte, S. Blazy, X. Leroy and D. Pichardie, "A formally-verified C static analyzer", POPL 2015, pp. 247-259, doi:10.1145/2676726.2676966. A Coq-verified abstract interpreter (Verasco) whose abstract domains are specified by concretization-based soundness without Galois connections or abstraction functions, and whose post-fixpoint iteration with widening is bounded by fuel rather than justified by a widening termination proof.
- **Design question.** When does a checked abstract post-fixpoint soundly over-approximate the concrete least fixpoint (the collecting semantics)? When the concrete transformer and gamma are monotone and the abstract transformer is gamma-sound; monotonicity of the concrete transformer is necessary for the conclusion to concern its least fixpoint.

Basis: execution (Lean kernel check). `isLeastFixpoint_lfp_and_le_gamma_of_monotone_of_monotone_gamma_of_sound_of_postFixpoint` and every counterexample, witness and control named on this card are kernel-checked under Lean v4.34.1; axioms of the main theorem: `Quot.sound`, `propext`.

Basis: derived (modeling bridge). Collecting semantics defined from images and unions of sets of states are monotone, so for them a checked abstract post-fixpoint over-approximates the least fixpoint. A concrete semantics whose transformer is not monotone (for example one that tests whether the current set of states is empty) is not covered, and the counterexample shows that the conclusion can then fail.

### Kleene iteration

#### R4-kleene-acc — `exists_kleene_postFixpoint_of_monotone_of_acc_of_le_apply`

- **Tier:** T0 (re-derivation: a known result restated in this vocabulary). **Kind:** theorem. **Depth:** shallow. **Module:** `Toy.AbsInt.Fixpoint`.
- **Plain claim.** If f# is monotone, the abstract order has no infinite sequence of consecutive strict steps (ACC), and the start a0 satisfies a0 <= f# a0 (e.g. a0 is a least element), then some Kleene iterate kleene f# a0 n = f#^n(a0) is a post-fixpoint of f#. Reflexivity and transitivity of the order are not needed.

```lean
theorem exists_kleene_postFixpoint_of_monotone_of_acc_of_le_apply :
  ∀ {A : Type} [inst : LE A] {fs : A → A},
    Monotone fs → ACC A → ∀ (a₀ : A), a₀ ≤ fs a₀ → ∃ n, PostFixpoint fs (kleene fs a₀ n)
```

*Unfolded*

```text
fs monotone, ¬ ∃ c : ℕ → A, ∀ n, c n ≤ c (n+1) ∧ ¬ c (n+1) ≤ c n, a₀ ≤ fs a₀  ⟹  ∃ n, fs (fsⁿ a₀) ≤ fsⁿ a₀.
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| --- | --- | --- |
| `hmono : Monotone fs` | Makes the Kleene sequence ascending. | tight: counterexample `kleeneAcc_tight_monotone` |
| `hacc : ACC A` | Rules out an infinite strictly ascending Kleene sequence. | tight: counterexample `kleeneAcc_tight_acc` |
| `hstart : a₀ ≤ fs a₀` | First step of the ascending sequence. Weaker than a0 being a least element. | tight: counterexample `kleeneAcc_tight_start` |

Each counterexample states that a concrete instance satisfies every other hypothesis, that the dropped hypothesis fails (where stated), and that the conclusion fails:

```lean
theorem kleeneAcc_tight_monotone :
  ACC V3 ∧ V3.bot ≤ v3Step V3.bot ∧ ¬Monotone v3Step ∧ ∀ (n : Nat), ¬PostFixpoint v3Step (kleene v3Step V3.bot n)

theorem kleeneAcc_tight_acc :
  Monotone ubIncr ∧
    UB.bot ≤ ubIncr UB.bot ∧
      ¬ACC UB ∧ PostFixpoint ubIncr UB.top ∧ ∀ (n : Nat), ¬PostFixpoint ubIncr (kleene ubIncr UB.bot n)

theorem kleeneAcc_tight_start :
  Monotone dis2Swap ∧
    ACC Dis2 ∧ ¬Dis2.a ≤ dis2Swap Dis2.a ∧ ∀ (n : Nat), ¬PostFixpoint dis2Swap (kleene dis2Swap Dis2.a n)

```

- **Non-vacuity witness** (`kleeneAcc_nonvacuous`). Sign domain (ACC via a rank function), the monotone signLoop, start bot.

```lean
theorem kleeneAcc_nonvacuous :
  Monotone signLoop ∧ ACC Sign ∧ Sign.bot ≤ signLoop Sign.bot
```

- **Prior art.**
  - P. Cousot and R. Cousot, "Comparing the Galois connection and widening/narrowing approaches to abstract interpretation", PLILP 1992, LNCS 631, pp. 269-295, doi:10.1007/3-540-55844-6_142 (author-hosted reprint). Sections 2 (p. 273) and 7 (p. 283): Kleene iterates from bottom reach the least fixpoint in finitely many steps when no strictly increasing chain is infinite. (Appendix Prop. 23 is Kleene's theorem for continuous F, assuming the lub of the iterates exists; it is not an ascending-chain termination statement.) No explicit iteration bound in terms of the height is stated there.
  - D. Cachera, T. Jensen, D. Pichardie and V. Rusu, "Extracting a data flow analyser in constructive logic", Theoretical Computer Science 342(1):56-78, 2005, doi:10.1016/j.tcs.2005.06.004. Coq formalization of lattice-based data-flow analysis with fixpoint iteration justified by an ascending chain condition.
  - T. Nipkow and G. Klein, Concrete Semantics with Isabelle/HOL, Springer 2014, doi:10.1007/978-3-319-10542-0; Chapter 13 "Abstract Interpretation", pp. 219-280, doi:10.1007/978-3-319-10542-0_13. In the accompanying Isabelle theory Abs_Int0, termination of the iteration pfp is proved with a bounded natural-number measure, not from an abstract ascending chain condition.
  - A. Yamada and J. Dubut, "Complete Non-Orders and Fixed Points", Archive of Formal Proofs, June 2019, https://isa-afp.org/entries/Complete_Non_Orders.html (ITP 2019), and J. Dubut and A. Yamada, "Fixed Points Theorems for Non-Transitive Relations", Logical Methods in Computer Science 18(1):30, 2022, doi:10.46298/LMCS-18(1:30)2022. Isabelle/HOL versions of the Knaster-Tarski and Kleene fixed-point theorems for relations without some of the order axioms. Neither treats abstract-interpretation transfer or widening.
- **Design question.** Which properties of an abstract domain and transformer guarantee that plain Kleene iteration terminates at an abstract invariant?

Basis: execution (Lean kernel check). `exists_kleene_postFixpoint_of_monotone_of_acc_of_le_apply` and every counterexample, witness and control named on this card are kernel-checked under Lean v4.34.1; axioms of the main theorem: `Classical.choice`, `Quot.sound`, `propext`.

Basis: derived (modeling bridge). For an analyzer over a domain without infinite strictly ascending chains (for example signs or constants), with a monotone abstract transformer and a start below its image (typically the least element), plain Kleene iteration terminates at an abstract invariant. Decidability of the stopping test is not covered.

#### R4-kleene-height — `exists_kleene_postFixpoint_le_of_monotone_of_heightLE_of_le_apply`

- **Tier:** T0 (re-derivation: a known result restated in this vocabulary). **Kind:** theorem. **Depth:** shallow. **Module:** `Toy.AbsInt.Fixpoint`.
- **Plain claim.** If f# is monotone, the abstract order has height at most h (every sequence of consecutive strict steps has at most h steps), and a0 <= f# a0, then some Kleene iterate kleene f# a0 n with n <= h is a post-fixpoint of f#.

```lean
theorem exists_kleene_postFixpoint_le_of_monotone_of_heightLE_of_le_apply :
  ∀ {A : Type} [inst : LE A] {fs : A → A},
    Monotone fs → ∀ (h : Nat), HeightLE A h → ∀ (a₀ : A), a₀ ≤ fs a₀ → ∃ n, n ≤ h ∧ PostFixpoint fs (kleene fs a₀ n)
```

*Unfolded*

```text
fs monotone, (∀ c k, (∀ i < k, c i ≤ c (i+1) ∧ ¬ c (i+1) ≤ c i) → k ≤ h), a₀ ≤ fs a₀  ⟹  ∃ n ≤ h, fs (fsⁿ a₀) ≤ fsⁿ a₀.
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| --- | --- | --- |
| `hmono : Monotone fs` | Makes the Kleene sequence ascending. | tight: counterexample `kleeneHeight_tight_monotone` |
| `hh : HeightLE A h` | Bounds the number of strict steps. | tight: counterexample `kleeneHeight_tight_height` |
| `hstart : a₀ ≤ fs a₀` | First step of the ascending sequence. | tight: counterexample `kleeneHeight_tight_start` |

Each counterexample states that a concrete instance satisfies every other hypothesis, that the dropped hypothesis fails (where stated), and that the conclusion fails:

```lean
theorem kleeneHeight_tight_monotone :
  HeightLE V3 1 ∧ V3.bot ≤ v3Step V3.bot ∧ ¬Monotone v3Step ∧ ¬∃ n, n ≤ 1 ∧ PostFixpoint v3Step (kleene v3Step V3.bot n)

theorem kleeneHeight_tight_height :
  Monotone ubIncr ∧
    UB.bot ≤ ubIncr UB.bot ∧ ∀ (h : Nat), ¬HeightLE UB h ∧ ¬∃ n, n ≤ h ∧ PostFixpoint ubIncr (kleene ubIncr UB.bot n)

theorem kleeneHeight_tight_start :
  Monotone dis2Swap ∧
    HeightLE Dis2 0 ∧ ¬Dis2.a ≤ dis2Swap Dis2.a ∧ ¬∃ n, n ≤ 0 ∧ PostFixpoint dis2Swap (kleene dis2Swap Dis2.a n)

```

- **Non-vacuity witness** (`kleeneHeight_nonvacuous`). Sign domain (height 2), signLoop, start bot.

```lean
theorem kleeneHeight_nonvacuous :
  Monotone signLoop ∧ HeightLE Sign 2 ∧ Sign.bot ≤ signLoop Sign.bot
```

- **Prior art.**
  - P. Cousot and R. Cousot, "Comparing the Galois connection and widening/narrowing approaches to abstract interpretation", PLILP 1992, LNCS 631, pp. 269-295, doi:10.1007/3-540-55844-6_142 (author-hosted reprint). Sections 2 (p. 273) and 7 (p. 283): Kleene iterates from bottom reach the least fixpoint in finitely many steps when no strictly increasing chain is infinite. (Appendix Prop. 23 is Kleene's theorem for continuous F, assuming the lub of the iterates exists; it is not an ascending-chain termination statement.) No explicit iteration bound in terms of the height is stated there.
  - F. Nielson, H. R. Nielson and C. Hankin, Principles of Program Analysis, Springer 1999, doi:10.1007/978-3-662-03811-6; Chapter 4 "Abstract Interpretation", pp. 211-282, doi:10.1007/978-3-662-03811-6_4. Cited at chapter level (fixpoint iteration and widening operators over complete lattices); no section-level content is relied on.
  - D. Cachera, T. Jensen, D. Pichardie and V. Rusu, "Extracting a data flow analyser in constructive logic", Theoretical Computer Science 342(1):56-78, 2005, doi:10.1016/j.tcs.2005.06.004. Coq formalization of lattice-based data-flow analysis with fixpoint iteration justified by an ascending chain condition.
- **Design question.** How many iterations can an analyzer over a finite-height domain need before reaching an invariant? At most the height.

Basis: execution (Lean kernel check). `exists_kleene_postFixpoint_le_of_monotone_of_heightLE_of_le_apply` and every counterexample, witness and control named on this card are kernel-checked under Lean v4.34.1; axioms of the main theorem: `Classical.choice`, `Quot.sound`, `propext`.

Basis: derived (modeling bridge). For finite-height domains the number of plain iterations before reaching an abstract invariant is at most the height; the bound counts iterations, not their cost.

#### R4-kleene-bound — `kleeneHeight_bound_attained`

- **Tier:** T1 (folklore made precise). **Kind:** counterexample. **Depth:** shallow. **Module:** `Toy.AbsInt.Fixpoint`.
- **Plain claim.** For every h, on the chain Fin (h+1) (height h) with the capped successor, every hypothesis of R4-kleene-height holds, the h-th Kleene iterate from 0 is a post-fixpoint, and no earlier iterate is; so the bound n <= h is attained.

```lean
theorem kleeneHeight_bound_attained :
  ∀ (h : Nat),
    HeightLE (Fin (h + 1)) h ∧
      Monotone (capSucc h) ∧
        capZero h ≤ capSucc h (capZero h) ∧
          PostFixpoint (capSucc h) (kleene (capSucc h) (capZero h) h) ∧
            ∀ (n : Nat), n < h → ¬PostFixpoint (capSucc h) (kleene (capSucc h) (capZero h) n)
```

*Unfolded*

```text
On Fin (h+1) with i ↦ min (i+1) h, from 0: height ≤ h, monotone, 0 ≤ step 0, the h-th iterate is a post-fixpoint, and ∀ n < h the n-th iterate is not.
```

**Hypothesis ledger.** None: the statement is about explicitly given instances, and the relevant hypotheses of the general theorem it illustrates are proved as conjuncts of the statement.

- **Non-vacuity witness.** The statement is itself a family of concrete instances.

- **Positive control** (`kleeneHeight_bound_not_attained_from_top`), a nearby setting where the conclusion fails:

```lean
theorem kleeneHeight_bound_not_attained_from_top :
  ∀ (h : Nat),
    0 < h →
      HeightLE (Fin (h + 1)) h ∧
        Monotone (capSucc h) ∧
          capTop h ≤ capSucc h (capTop h) ∧ ∃ n, n < h ∧ PostFixpoint (capSucc h) (kleene (capSucc h) (capTop h) n)
```

- **Prior art.**
  - Elementary example; no published statement of the attainment of the height bound is cited, so the result is recorded as folklore made precise. The bound itself is the subject of R4-kleene-height.
- **Design question.** Is the height bound of R4-kleene-height tight?

Basis: execution (Lean kernel check). `kleeneHeight_bound_attained` and every counterexample, witness and control named on this card are kernel-checked under Lean v4.34.1; axioms of the main theorem: `Quot.sound`, `propext`.

Basis: derived (modeling bridge). The worst case of `h` iterations occurs already on a single chain; analyzers that start higher, widen, or iterate several variables chaotically can need fewer steps.

#### R4-height-acc — `acc_of_heightLE`

- **Tier:** T0 (re-derivation: a known result restated in this vocabulary). **Kind:** theorem. **Depth:** shallow. **Module:** `Toy.AbsInt.Fixpoint`.
- **Plain claim.** An abstract order of height at most h has no infinite sequence of consecutive strict steps (ACC).

```lean
theorem acc_of_heightLE :
  ∀ {A : Type} [inst : LE A] (h : Nat), HeightLE A h → ACC A
```

*Unfolded*

```text
(∀ c k, (∀ i < k, strict step c i → c (i+1)) → k ≤ h)  ⟹  ¬ ∃ c : ℕ → A, ∀ n, strict step c n → c (n+1).
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| --- | --- | --- |
| `hh : HeightLE A h` | A strictly ascending chain would give h + 1 strict steps. | tight: counterexample `accOfHeight_tight` |

Each counterexample states that a concrete instance satisfies every other hypothesis, that the dropped hypothesis fails (where stated), and that the conclusion fails:

```lean
theorem accOfHeight_tight :
  ¬ACC UB ∧ ∀ (h : Nat), ¬HeightLE UB h

```

- **Non-vacuity witness** (`accOfHeight_nonvacuous`). Sign domain has height 2.

```lean
theorem accOfHeight_nonvacuous :
  HeightLE Sign 2
```

- **Prior art.**
  - Elementary; no source is needed.
  - F. Nielson, H. R. Nielson and C. Hankin, Principles of Program Analysis, Springer 1999, doi:10.1007/978-3-662-03811-6; Chapter 4 "Abstract Interpretation", pp. 211-282, doi:10.1007/978-3-662-03811-6_4. Cited at chapter level (fixpoint iteration and widening operators over complete lattices); no section-level content is relied on.
- **Design question.** Auxiliary bridge: lets the results stated under ACC, namely R4-kleene-acc and the helper widenTerminates_of_acc (statement: ACC A implies WidenTerminates w for every binary operator w : A -> A -> A), be applied to domains of finite height.

Basis: execution (Lean kernel check). `acc_of_heightLE` and every counterexample, witness and control named on this card are kernel-checked under Lean v4.34.1; axioms of the main theorem: none.

Basis: derived (modeling bridge). Auxiliary bridge; no modeling claim beyond allowing `R4-kleene-acc` and `widenTerminates_of_acc` to be applied to finite-height domains.

### Widening

#### R5-widen — `exists_widenIter_postFixpoint_of_trans_of_upperLeft_of_upperRight_of_terminates_of_monotone_of_le_apply`

- **Tier:** T0 (re-derivation: a known result restated in this vocabulary). **Kind:** theorem. **Depth:** shallow. **Module:** `Toy.AbsInt.Widening`.
- **Plain claim.** If the abstract order is transitive, the operator widen satisfies a <= a widen b and b <= a widen b and the termination axiom (for every ascending input sequence the widened chain is not strictly increasing at every step), f# is monotone, and a0 <= f# a0, then some widened iterate (x0 = a0, x(n+1) = x n widen f# (x n)) is a post-fixpoint of f#; equivalently, the loop that widens until the first post-fixpoint terminates. No chain condition on the domain is needed.

```lean
theorem exists_widenIter_postFixpoint_of_trans_of_upperLeft_of_upperRight_of_terminates_of_monotone_of_le_apply :
  ∀ {A : Type} [inst : LE A],
    IsTrans A →
      ∀ {w : A → A → A},
        WidenUpperLeft w →
          WidenUpperRight w →
            WidenTerminates w →
              ∀ {fs : A → A}, Monotone fs → ∀ (a₀ : A), a₀ ≤ fs a₀ → ∃ n, PostFixpoint fs (widenIter w fs a₀ n)
```

*Unfolded*

```text
≤ transitive; ∀ a b, a ≤ a ∇ b; ∀ a b, b ≤ a ∇ b; for every ascending b, the chain y₀ = b 0, yₙ₊₁ = yₙ ∇ b (n+1) is not strictly increasing at every step; fs monotone; a₀ ≤ fs a₀  ⟹  ∃ n, fs (xₙ) ≤ xₙ where x₀ = a₀, xₙ₊₁ = xₙ ∇ fs xₙ.
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| --- | --- | --- |
| `htrans : IsTrans A` | Chains f# (x n) <= x (n+1) <= x n. | tight: counterexample `widen_tight_trans` |
| `hL : WidenUpperLeft w` | Makes the widened iterates ascending, hence the input to the termination axiom ascending. | tight: counterexample `widen_tight_upperLeft` |
| `hR : WidenUpperRight w` | Gives f# (x n) <= x (n+1). In the counterexample, w is the left projection fun a x => a on B2 (implicit carrier B2, which the pretty-printer does not show in the WidenUpperLeft, WidenUpperRight and WidenTerminates conjuncts). | tight: counterexample `widen_tight_upperRight` |
| `hT : WidenTerminates w` | Supplies a step with x (n+1) <= x n. In the counterexample, w is max on Nat (implicit argument A := Nat, which the pretty-printer does not show in the WidenUpperLeft, WidenUpperRight and WidenTerminates conjuncts). | tight: counterexample `widen_tight_terminates` |
| `hmono : Monotone fs` | Makes the input sequence a0, f# x0, f# x1, ... ascending, as the termination axiom requires. | tight: counterexample `widen_tight_monotone` |
| `hstart : a₀ ≤ fs a₀` | First step of that input sequence. | tight: counterexample `widen_tight_start` |

Each counterexample states that a concrete instance satisfies every other hypothesis, that the dropped hypothesis fails (where stated), and that the conclusion fails:

```lean
theorem widen_tight_trans :
  ¬IsTrans NT4w ∧
    WidenUpperLeft nt4wWiden ∧
      WidenUpperRight nt4wWiden ∧
        WidenTerminates nt4wWiden ∧
          Monotone nt4wStep ∧
            NT4w.bot ≤ nt4wStep NT4w.bot ∧ ∀ (n : Nat), ¬PostFixpoint nt4wStep (widenIter nt4wWiden nt4wStep NT4w.bot n)

theorem widen_tight_upperLeft :
  IsTrans W4 ∧
    ¬WidenUpperLeft w4Widen ∧
      WidenUpperRight w4Widen ∧
        WidenTerminates w4Widen ∧
          Monotone w4Step ∧ W4.z ≤ w4Step W4.z ∧ ∀ (n : Nat), ¬PostFixpoint w4Step (widenIter w4Widen w4Step W4.z n)

theorem widen_tight_upperRight :
  IsTrans B2 ∧
    (WidenUpperLeft fun a x => a) ∧
      (¬WidenUpperRight fun a x => a) ∧
        (WidenTerminates fun a x => a) ∧
          (Monotone fun x => B2.hi) ∧
            B2.lo ≤ (fun x => B2.hi) B2.lo ∧
              ∀ (n : Nat), ¬PostFixpoint (fun x => B2.hi) (widenIter (fun a x => a) (fun x => B2.hi) B2.lo n)

theorem widen_tight_terminates :
  IsTrans Nat ∧
    WidenUpperLeft max ∧
      WidenUpperRight max ∧
        ¬WidenTerminates max ∧
          Monotone Nat.succ ∧ 0 ≤ Nat.succ 0 ∧ ∀ (n : Nat), ¬PostFixpoint Nat.succ (widenIter max Nat.succ 0 n)

theorem widen_tight_monotone :
  IsTrans PT ∧
    WidenUpperLeft ptWiden ∧
      WidenUpperRight ptWiden ∧
        WidenTerminates ptWiden ∧
          ¬Monotone ptBadStep ∧
            PT.pt 0 0 ≤ ptBadStep (PT.pt 0 0) ∧
              ∀ (n : Nat), ¬PostFixpoint ptBadStep (widenIter ptWiden ptBadStep (PT.pt 0 0) n)

theorem widen_tight_start :
  IsTrans PT ∧
    WidenUpperLeft ptWiden ∧
      WidenUpperRight ptWiden ∧
        WidenTerminates ptWiden ∧
          Monotone ptShift ∧
            ¬PT.pt 0 1 ≤ ptShift (PT.pt 0 1) ∧
              ∀ (n : Nat), ¬PostFixpoint ptShift (widenIter ptWiden ptShift (PT.pt 0 1) n)

```

- **Non-vacuity witness** (`widen_nonvacuous`). UB domain with the jump-to-top widening ubWiden, the counter-loop transformer ubIncr, start bot.

```lean
theorem widen_nonvacuous :
  IsTrans UB ∧
    WidenUpperLeft ubWiden ∧ WidenUpperRight ubWiden ∧ WidenTerminates ubWiden ∧ Monotone ubIncr ∧ UB.bot ≤ ubIncr UB.bot
```

- **Prior art.**
  - P. Cousot and R. Cousot, "Comparing the Galois connection and widening/narrowing approaches to abstract interpretation", PLILP 1992, LNCS 631, pp. 269-295, doi:10.1007/3-540-55844-6_142 (author-hosted reprint). Conditions (6)-(8), p. 275, define a widening; (8) reads "for all increasing chains x0 <= x1 <= ..., the increasing chain defined by y0 = x0, ..., y(i+1) = y(i) widen x(i+1), ... is not strictly increasing". Eq. (9) is upward iteration that stops at the first post-fixpoint; Prop. 33 (cpo, continuous F, bottom <= F(bottom)) and Prop. 35 (preordered version) show that it is ultimately stationary at a post-fixpoint above lfp F. R5-widen assumes no cpo and no continuity and states termination of the same stopping iteration as the existence of a post-fixpoint iterate.
  - T. Nipkow and G. Klein, Concrete Semantics with Isabelle/HOL, Springer 2014, doi:10.1007/978-3-319-10542-0; Chapter 13 "Abstract Interpretation", pp. 219-280, doi:10.1007/978-3-319-10542-0_13. Section 13.9 requires x <= x widen y and y <= x widen y and defines iter_widen f = while_option (lambda x. not f x <= x) (lambda x. x widen f x), which stops at the first post-fixpoint. The accompanying Isabelle theory HOL-IMP Abs_Int3 (Isabelle2025 release, https://isabelle.in.tum.de/website-Isabelle2025/dist/library/HOL/HOL-IMP/Abs_Int3.html) proves that a result of iter_widen is a post-fixpoint (lemma iter_widen_pfp) and also mechanizes termination of widening: lemma iter_widen_termination derives termination of iter_widen from an invariant preserved by the step and by widening and a natural-number measure m with m (C1 widen C2) < m C1 whenever not C2 <= C1; locale Measure_wn assumes such a measure on abstract values (m_anti_mono, m_widen); and for intervals the measure m_ivl (lemma m_ivl_widen) yields lemma iter_winden_step_ivl_termination and theorem AI_wn_ivl_termination. The predecessor Archive of Formal Proofs entry Abs_Int_ITP2012 (theory Abs_Int3, Isabelle2025 AFP release branch, mirror https://github.com/isabelle-prover/mirror-afp-2025 at commit 400ee45cf836394b0b35dde6d20ab5ecd2012ee3) likewise proves iter_widen_termination (from a well-foundedness hypothesis) and termination of its interval analyzer (measure m_ivl, lemma m_ivl_widen, theorem AI_ivl'_termination). These are measure-based termination proofs for concrete widenings, not a chain-condition hypothesis on the widening such as WidenTerminates.
  - T. Nipkow, "Abstract interpretation of annotated commands", ITP 2012, LNCS 7406, pp. 116-132, doi:10.1007/978-3-642-32347-8_9, with the Archive of Formal Proofs entry Abs_Int_ITP2012. Isabelle/HOL abstract interpreter with widening and narrowing, the predecessor of the Concrete Semantics development.
  - J.-H. Jourdan, V. Laporte, S. Blazy, X. Leroy and D. Pichardie, "A formally-verified C static analyzer", POPL 2015, pp. 247-259, doi:10.1145/2676726.2676966. A Coq-verified abstract interpreter (Verasco) whose abstract domains are specified by concretization-based soundness without Galois connections or abstraction functions, and whose post-fixpoint iteration with widening is bounded by fuel rather than justified by a widening termination proof.
  - D. Cachera and D. Pichardie, "A certified denotational abstract interpreter", ITP 2010, LNCS 6172, pp. 9-24, doi:10.1007/978-3-642-14052-5_3. Coq-verified abstract interpreter using widening and narrowing with syntax-directed iteration strategies.
  - P. Cousot and R. Cousot, "Abstract interpretation: a unified lattice model for static analysis of programs by construction or approximation of fixpoints", POPL 1977, pp. 238-252, doi:10.1145/512950.512973. Bibliographic record verified; cited only as the origin of abstract interpretation and of widening as attributed by Cousot and Cousot (PLILP 1992).
  - P. Cousot and R. Cousot, "Abstract interpretation frameworks", Journal of Logic and Computation 2(4):511-547, 1992, doi:10.1093/logcom/2.4.511 (author-hosted text). Section 5 (p. 520) motivates modelling precision by a preorder that need not be antisymmetric (when the same property can be expressed by several elements), and Sections 4 and 6-8 relax the Galois connection framework to correspondences given by a soundness relation (Section 4, pp. 515-520), by an abstraction relation or function (Section 6, pp. 520-538), by a concretization relation or function only (Section 7, pp. 538-541), and by both (Section 8, pp. 542-544); page numbers as printed in the author-hosted text.
  - F. Nielson, H. R. Nielson and C. Hankin, Principles of Program Analysis, Springer 1999, doi:10.1007/978-3-662-03811-6; Chapter 4 "Abstract Interpretation", pp. 211-282, doi:10.1007/978-3-662-03811-6_4. Cited at chapter level (fixpoint iteration and widening operators over complete lattices); no section-level content is relied on.
- **Design question.** Which widening axioms are load-bearing for termination of an analyzer on infinite-height domains, and what else must hold of the transformer and the order?

Basis: execution (Lean kernel check). `exists_widenIter_postFixpoint_of_trans_of_upperLeft_of_upperRight_of_terminates_of_monotone_of_le_apply` and every counterexample, witness and control named on this card are kernel-checked under Lean v4.34.1; axioms of the main theorem: `Classical.choice`, `Quot.sound`, `propext`.

Basis: derived (modeling bridge). Analyzers over infinite-height domains (for example intervals) stop upward iteration at the first post-fixpoint; this theorem justifies termination of that loop for any stateless binary widening satisfying the two upper-bound axioms and Cousot and Cousot's condition (8), over a transitive order, with a monotone abstract transformer and a start below its image. Delayed widening, widening with thresholds and narrowing are not covered.

#### R5-widen-diverge — `kleene_diverges_widen_converges_ub`

- **Tier:** T0 (re-derivation: a known result restated in this vocabulary). **Kind:** counterexample. **Depth:** shallow. **Module:** `Toy.AbsInt.Widening`.
- **Plain claim.** On the infinite-height UB domain, for the monotone counter loop counterStep and its sound monotone abstraction ubIncr, with the jump-to-top widening ubWiden satisfying every widening hypothesis of R5-widen: plain Kleene iteration from bot never reaches a post-fixpoint and no Kleene iterate over-approximates the concrete least fixpoint (so stopping plain iteration at any finite step is unsound here), whereas iteration with ubWiden reaches the post-fixpoint top at step 1, whose concretization contains the least fixpoint.

```lean
theorem kleene_diverges_widen_converges_ub :
  Monotone ubIncr ∧
    IsBot UB.bot ∧
      ¬ACC UB ∧
        Sound ubGamma counterStep ubIncr ∧
          Monotone counterStep ∧
            IsTrans UB ∧
              WidenUpperLeft ubWiden ∧
                WidenUpperRight ubWiden ∧
                  WidenTerminates ubWiden ∧
                    (∀ (n : Nat), ¬PostFixpoint ubIncr (kleene ubIncr UB.bot n)) ∧
                      (∀ (n : Nat), ¬lfp counterStep ≤ ubGamma (kleene ubIncr UB.bot n)) ∧
                        widenIter ubWiden ubIncr UB.bot 1 = UB.top ∧
                          PostFixpoint ubIncr (widenIter ubWiden ubIncr UB.bot 1) ∧
                            lfp counterStep ≤ ubGamma (widenIter ubWiden ubIncr UB.bot 1)
```

*Unfolded*

```text
UB domain, counterStep, ubIncr, ubWiden a b = if b ≤ a then a else top: ubIncr monotone, bot least, ¬ ACC UB, ubIncr sound, counterStep monotone, ≤ transitive on UB, ubWiden satisfies a ≤ a ∇ b, b ≤ a ∇ b and the termination axiom; ∀ n, ¬ ubIncr (ubIncrⁿ bot) ≤ ubIncrⁿ bot; ∀ n, ¬ lfp counterStep ⊆ ubGamma (ubIncrⁿ bot); the widened iterate at step 1 is top, a post-fixpoint, and lfp counterStep ⊆ ubGamma top.
```

**Hypothesis ledger.** None: the statement is about explicitly given instances, and the relevant hypotheses of the general theorem it illustrates are proved as conjuncts of the statement.

- **Non-vacuity witness.** The statement is itself a concrete instance.

- **Positive control** (`kleene_converges_sign`), a nearby setting where the conclusion fails:

```lean
theorem kleene_converges_sign :
  kleene signLoop Sign.bot 2 = Sign.top ∧ PostFixpoint signLoop (kleene signLoop Sign.bot 2)
```

- **Prior art.**
  - P. Cousot and R. Cousot, "Comparing the Galois connection and widening/narrowing approaches to abstract interpretation", PLILP 1992, LNCS 631, pp. 269-295, doi:10.1007/3-540-55844-6_142 (author-hosted reprint). Example 8 (p. 273): plain iteration on intervals for a bounded loop equation, with iterates bottom, [1, 1], [1, 2], ..., [1, 100], followed by the remark that such a sequence might be infinite and strictly increasing (e.g. for nonterminating programs); Example 11 (pp. 276-277): the interval widening and narrowing applied to the same equation, where the widened iterates stabilize at [1, +infinity] and narrowing then yields [1, 100].
  - T. Nipkow and G. Klein, Concrete Semantics with Isabelle/HOL, Springer 2014, doi:10.1007/978-3-319-10542-0; Chapter 13 "Abstract Interpretation", pp. 219-280, doi:10.1007/978-3-319-10542-0_13. Section 13.9 requires x <= x widen y and y <= x widen y and defines iter_widen f = while_option (lambda x. not f x <= x) (lambda x. x widen f x), which stops at the first post-fixpoint. The accompanying Isabelle theory HOL-IMP Abs_Int3 (Isabelle2025 release, https://isabelle.in.tum.de/website-Isabelle2025/dist/library/HOL/HOL-IMP/Abs_Int3.html) proves that a result of iter_widen is a post-fixpoint (lemma iter_widen_pfp) and also mechanizes termination of widening: lemma iter_widen_termination derives termination of iter_widen from an invariant preserved by the step and by widening and a natural-number measure m with m (C1 widen C2) < m C1 whenever not C2 <= C1; locale Measure_wn assumes such a measure on abstract values (m_anti_mono, m_widen); and for intervals the measure m_ivl (lemma m_ivl_widen) yields lemma iter_winden_step_ivl_termination and theorem AI_wn_ivl_termination. The predecessor Archive of Formal Proofs entry Abs_Int_ITP2012 (theory Abs_Int3, Isabelle2025 AFP release branch, mirror https://github.com/isabelle-prover/mirror-afp-2025 at commit 400ee45cf836394b0b35dde6d20ab5ecd2012ee3) likewise proves iter_widen_termination (from a well-foundedness hypothesis) and termination of its interval analyzer (measure m_ivl, lemma m_ivl_widen, theorem AI_ivl'_termination). These are measure-based termination proofs for concrete widenings, not a chain-condition hypothesis on the widening such as WidenTerminates.
- **Design question.** Is the chain condition of R4-kleene-acc dispensable in practice? No: without it, plain iteration of a sound monotone transformer can run forever.

Basis: execution (Lean kernel check). `kleene_diverges_widen_converges_ub` and every counterexample, witness and control named on this card are kernel-checked under Lean v4.34.1; axioms of the main theorem: `Quot.sound`, `propext`.

Basis: derived (modeling bridge). `UB` models the upper-bound component of an interval domain for a counter; the divergence of plain iteration on unbounded counter loops is the phenomenon that motivates widening in interval analyzers.

#### R5-widen-bridge — `widenTerminates_of_widenStabilizes`

- **Tier:** T0 (re-derivation: a known result restated in this vocabulary). **Kind:** theorem. **Depth:** shallow. **Module:** `Toy.AbsInt.Widening`.
- **Plain claim.** The textbook termination axiom (the widened chain of every ascending input eventually becomes constant, with constancy meaning equality) implies the termination axiom used in R5-widen (the widened chain is not strictly increasing at every step), with no order law assumed.

```lean
theorem widenTerminates_of_widenStabilizes :
  ∀ {A : Type} [inst : LE A] {w : A → A → A}, WidenStabilizes w → WidenTerminates w
```

*Unfolded*

```text
(∀ b ascending, ∃ N, ∀ m ≥ N, yₘ = y_N)  ⟹  (∀ b ascending, ¬ ∀ n, yₙ < yₙ₊₁ strictly).
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| --- | --- | --- |
| `h : WidenStabilizes w` | Gives a step N with widenChain (N+1) = widenChain N, which cannot be strict. In the counterexample, w is max on Nat (implicit argument A := Nat, which the pretty-printer does not show). | tight: counterexample `widenBridge_tight` |

Each counterexample states that a concrete instance satisfies every other hypothesis, that the dropped hypothesis fails (where stated), and that the conclusion fails:

```lean
theorem widenBridge_tight :
  ¬WidenStabilizes max ∧ ¬WidenTerminates max

```

- **Non-vacuity witness** (`widenBridge_nonvacuous`). ubWiden stabilizes.

```lean
theorem widenBridge_nonvacuous :
  WidenStabilizes ubWiden
```

- **Prior art.**
  - F. Nielson, H. R. Nielson and C. Hankin, Principles of Program Analysis, Springer 1999, doi:10.1007/978-3-662-03811-6; Chapter 4 "Abstract Interpretation", pp. 211-282, doi:10.1007/978-3-662-03811-6_4. Cited at chapter level (fixpoint iteration and widening operators over complete lattices); no section-level content is relied on.
  - P. Cousot and R. Cousot, "Comparing the Galois connection and widening/narrowing approaches to abstract interpretation", PLILP 1992, LNCS 631, pp. 269-295, doi:10.1007/3-540-55844-6_142 (author-hosted reprint). Condition (8), p. 275: the widened chain of every increasing chain "is not strictly increasing"; this is the form of WidenTerminates.
- **Design question.** Auxiliary bridge. Can widening operators proved correct against the textbook stabilization axiom be used with R5-widen? Yes, with no order law.

Basis: execution (Lean kernel check). `widenTerminates_of_widenStabilizes` and every counterexample, witness and control named on this card are kernel-checked under Lean v4.34.1; axioms of the main theorem: none.

Basis: derived (modeling bridge). Widening operators proved correct against the textbook stabilization axiom can be used with `R5-widen` without re-proof; the bridge assumes no order law.

## Boundaries

### Non-claims

**Leading non-claim: fixpoint transfer needs a monotone concrete transformer.** A `γ`-sound abstract post-fixpoint is guaranteed to over-approximate the concrete least fixpoint (the collecting semantics) only when the concrete transformer `f` is monotone (`R4-transfer-lfp`, hypothesis `hf : Monotone f`, tight). Without monotonicity, the "least fixpoint" `lfp f` of this package is merely the intersection of all concrete post-fixpoints: it need not be a fixpoint (`lfpEq_tight_monotone`) or even a post-fixpoint (`lfp_not_postFixpoint_of_not_monotone`), and `R4-transfer` then says nothing about the fixpoints of `f`. Concretely, for the non-monotone `nonMonoUniqueFix` on `Pred Bool`, with the exact abstraction `α = γ = id` on the partial order `Pred Bool` and `a = {false}`, `γ` is monotone, `nonMonoUniqueFix` is `γ`-sound for itself and `a` is a post-fixpoint, yet the unique (hence least) fixpoint `{true}` is not included in `γ a`, and `lfp nonMonoUniqueFix = ∅` is not a fixpoint (it is mapped to the full set):

```lean
theorem lfpFixGamma_tight_monotone :
  ¬Monotone nonMonoUniqueFix ∧
    Monotone id ∧
      Sound id nonMonoUniqueFix nonMonoUniqueFix ∧
        PostFixpoint nonMonoUniqueFix pFalse ∧
          ¬(IsLeastFixpoint nonMonoUniqueFix (lfp nonMonoUniqueFix) ∧
                ∀ (x : Pred Bool), IsLeastFixpoint nonMonoUniqueFix x → x ≤ id pFalse) ∧
            IsLeastFixpoint nonMonoUniqueFix pTrue ∧
              ¬pTrue ≤ id pFalse ∧ ¬IsLeastFixpoint nonMonoUniqueFix (lfp nonMonoUniqueFix)

theorem transfer_misses_leastFixpoint_of_not_monotone :
  IsRefl (Pred Bool) ∧
    IsTrans (Pred Bool) ∧
      IsAntisymm (Pred Bool) ∧
        GaloisConnection id id ∧
          Monotone id ∧
            Sound id nonMonoUniqueFix nonMonoUniqueFix ∧
              PostFixpoint nonMonoUniqueFix pFalse ∧
                (∀ (x : Pred Bool), nonMonoUniqueFix x = x ↔ x = pTrue) ∧ ¬pTrue ≤ id pFalse

theorem lfp_nonMonoUniqueFix_eq_empty :
  lfp nonMonoUniqueFix = Pred.empty Bool

theorem nonMonoUniqueFix_empty :
  nonMonoUniqueFix (Pred.empty Bool) = Pred.univ Bool
```

This shows that the conclusion *can* fail without monotonicity; it does not show that it fails for every non-monotone `f`.

**Per-result non-claims** (verbatim from `results.json`; escape hatches are listed separately below):

- **R1-gc-iff**
  - Does not say that a Galois connection exists for a given gamma; it characterizes when a given pair is one.
  - Does not assume or conclude antisymmetry; uniqueness of alpha given gamma (which needs antisymmetry) is not stated.
  - Galois-connection insertion is not established: alpha (gamma a) = a is not claimed, and gamma need not be injective (distinct abstract elements may have the same concretization).
  - Does not claim that alpha is computable or definable without classical choice; the abstraction functions on Pred sigma used here (for example signAlpha) are noncomputable.
  - Preservation of joins by alpha and of meets by gamma (standard consequences of a Galois connection wherever those bounds exist) is neither stated nor needed.
  - Without antisymmetry, alpha (gamma (alpha x)) = alpha x is not established; only the two inequalities alpha (gamma (alpha x)) <= alpha x and alpha x <= alpha (gamma (alpha x)) follow.
  - The concrete side is fixed to predicates ordered by inclusion; no claim is made for an arbitrary concrete preorder, although nothing in the statement uses more than reflexivity and transitivity of inclusion.
  - Does not require or provide lattice structure (joins, meets, completeness) on A.
  - Universe-restricted: sigma and A live in Type (as everywhere in this package).
- **R1-gc-forward**
  - Reference point: this is the forward direction of R1-gc-iff under the same hypotheses; it is kept as a separately citable statement of the laws a client may rely on.
  - Reductivity alone needs none of the order laws, and extensivity and monotonicity of alpha need only reflexivity; the statement bundles them and does not separate these finer dependencies (they are recorded in the hypothesis ledger, not as separate Lean theorems).
  - Galois-connection insertion is not established: alpha (gamma a) = a is not claimed, and gamma need not be injective (distinct abstract elements may have the same concretization).
  - Preservation of joins by alpha and of meets by gamma is not stated.
- **R1-gc-backward**
  - Does not say that the four laws are independent in every setting; tightness is shown only by the five specific two- or three-element counterexamples.
  - Does not need or establish reflexivity of the abstract order.
  - Although the Galois connection is obtained without reflexivity, reading it as 'alpha x soundly describes x' and the downstream results R2-best-sound and R3-comp-le still require IsRefl A (counterexamples nr2_not_extensive, bestSound_tight_refl, compLe_tight_refl).
- **R2-best-sound**
  - Does not claim alpha . f . gamma is computable or effectively representable; it is a specification.
  - Does not imply soundness on subsets (for all x and a, x included in gamma a implies f x included in gamma (alpha (f (gamma a)))) or on individual states unless f is monotone: for non-monotone f, gamma-soundness constrains f only on the sets gamma a (counterexample sound_not_subset_of_not_monotone; for monotone f the lift holds, sound_le_of_le_gamma_of_monotone).
  - Soundness here is the gamma-form (f . gamma included in gamma . f#); the alpha-form (alpha . f <= f# . alpha) is not stated. For f# = alpha . f . gamma the alpha-form follows from a Galois connection over a reflexive order together with monotonicity of f; conversely, deriving gamma-soundness of an arbitrary f# from its alpha-form uses monotonicity of f# and transitivity of A. Neither derivation is formalized here.
  - Monotonicity of f is not required for this statement and is not implied by it.
  - Does not say that alpha . f . gamma is exact (gamma (f# a) = f (gamma a)); in general it over-approximates.
- **R2-best-least**
  - Without reflexivity of A this shows only that alpha . f . gamma is a pointwise lower bound of the gamma-sound transformers; it need not itself be gamma-sound, even when sound transformers exist and A is transitive (bestTransformer_lowerBound_not_sound_without_refl). It is guaranteed to be gamma-sound itself, hence a least gamma-sound transformer, when A is also reflexive (R2-best-sound, IsRefl A). Such a least element is unique up to the equivalence a <= b and b <= a when A is a preorder (IsRefl A and IsTrans A), and guaranteed to be unique up to equality when A is also antisymmetric.
  - Does not imply that the best transformer is exact or complete (gamma (f# a) = f (gamma a), or alpha (f x) = f# (alpha x)); in general it over-approximates.
  - Does not imply soundness on subsets of gamma a when f is not monotone (see R2-best-sound).
  - Does not say the best transformer is monotone (see R2-best-mono) or that it is the abstraction of f in any functional Galois connection.
  - Does not compare transformers that are sound only on part of the abstract domain.
- **R2-best-mono**
  - Does not claim that every sound transformer of a monotone f is monotone.
  - Monotone does not mean continuous or join-preserving; neither is claimed.
- **R3-comp-le**
  - Does not say composition always loses precision; the inequality can be an equality (positive control bestTransformer_comp_exact_sign_incr).
  - Does not bound the amount of precision lost.
  - Does not characterize when equality (f . g)# a = f# (g# a) holds; sufficient conditions are listed as escape hatches of R3-comp-strict.
  - Applies only to best transformers alpha . f . gamma; it says nothing about how (f . g)# compares with a composite f# . g# of other sound transformers.
  - Without monotone f the inequality can fail (compLe_tight_monoF): composing best transformers is then not even an over-approximation of the best transformer of the composition.
  - The composition f# . g# of transformers that are sound for f and g is sound for f . g when f is monotone; that fact is not stated here.
- **R3-comp-strict**
  - Shows strictness for one domain and one pair of statements; it does not say every non-trivial domain exhibits strict loss.
  - Does not say relational domains avoid this loss in general.
- **R4-lfp-fix**
  - Stated only for the powerset lattice Pred sigma, not for an arbitrary complete lattice.
  - Does not claim that lfp f is the unique fixpoint of f (the identity has every predicate as a fixpoint); together with R4-lfp-least it is the least fixpoint.
  - Without continuity of f, lfp f need not equal the countable union of the Kleene iterates f^n (empty); no such characterization or computation method is claimed.
  - Equality of predicates is Lean equality of functions; proving it needs function and propositional extensionality.
- **R4-lfp-least**
  - Reference point: an unfolding of the definition of lfp, kept because R4-transfer and R4-transfer-lfp are stated in terms of it.
  - For non-monotone f, lfp f (the intersection of all post-fixpoints) need not itself be a post-fixpoint (lfp_not_postFixpoint_of_not_monotone) or a fixpoint (lfpEq_tight_monotone); it is guaranteed to be the least post-fixpoint and the least fixpoint only when f is monotone (R4-lfp-fix); without monotonicity it need not be a fixpoint.
- **R4-transfer**
  - Without monotonicity of f, lfp f is only the intersection of all concrete post-fixpoints: it need not be a fixpoint (lfpEq_tight_monotone) or even a post-fixpoint (lfp_not_postFixpoint_of_not_monotone), and gamma a can miss the unique fixpoint of f even with an exact Galois connection on a poset (transfer_misses_leastFixpoint_of_not_monotone). To conclude that gamma a over-approximates the concrete least fixpoint, use R4-transfer-lfp, which adds monotonicity of f.
  - The conclusion is only lfp f included in gamma a. That gamma a is itself a concrete post-fixpoint (f (gamma a) included in gamma a) is an intermediate step of the proof and is not part of the stated conclusion.
  - Does not say a post-fixpoint exists or how to find one (see R4-kleene-acc, R4-kleene-height and R5-widen).
  - Does not say gamma a is a tight over-approximation; top is always a post-fixpoint when it exists and gives no information.
  - Does not establish completeness (gamma a = lfp f) or optimality of a relative to alpha (lfp f), even when a Galois connection exists.
  - Does not relate a to the abstract least fixpoint of f#, which need not exist without completeness.
  - Soundness here is the gamma-form for all abstract inputs, not only for those reachable during iteration.
- **R4-transfer-lfp**
  - Monotonicity of the concrete transformer f cannot be dropped: the guarantee that a gamma-sound abstract post-fixpoint bounds the concrete least fixpoint needs f monotone, and without it the conclusion can fail (this does not say it fails for every non-monotone f). For the non-monotone nonMonoUniqueFix on Pred Bool with the exact gamma = id and a = {false}, monotonicity of gamma, gamma-soundness and the post-fixpoint condition hold, but the unique (hence least) fixpoint {true} is not included in gamma a (lfpFixGamma_tight_monotone); moreover lfp f is empty (lfp_nonMonoUniqueFix_eq_empty), which is not a fixpoint because f maps the empty set to the full set (nonMonoUniqueFix_empty). Without monotone f, only R4-transfer applies, and its conclusion concerns lfp f, the intersection of all concrete post-fixpoints, not a fixpoint of f.
  - Does not say a post-fixpoint exists or how to find one (see R4-kleene-acc, R4-kleene-height and R5-widen).
  - Does not say gamma a is a tight over-approximation (gamma a = lfp f); top-like post-fixpoints give no information.
  - Does not require or use an abstraction function, a Galois connection, or any order law on A.
  - Concerns the least fixpoint on Pred sigma ordered by inclusion only; no claim is made for other concrete domains.
  - Does not identify lfp f with the countable union of the Kleene iterates f^n (empty); no continuity is assumed.
- **R4-kleene-acc**
  - Gives no bound on n (see R4-kleene-height for a bound under a height bound).
  - Does not say the post-fixpoint reached is a fixpoint or the least post-fixpoint; without antisymmetry, f# x <= x together with x <= f# x does not give f# x = x, and later iterates need not be syntactically equal.
  - On a non-transitive relation, ACC forbids only infinite sequences of consecutive strict steps: it does not make ascending sequences stabilize (nb_heightLE_one_ascending_not_stabilizing), and a finite non-transitive relation with a strict cycle violates it (cyc3_not_acc).
  - Says nothing about soundness by itself; combine with R4-transfer or R4-transfer-lfp.
  - The proof is classical; decidability of <= and computability of f# are not assumed, and no algorithm for deciding when to stop is claimed beyond checking f# x <= x.
- **R4-kleene-height**
  - The bound counts iterations of f#, not the cost of evaluating f# or of checking f# x <= x.
  - For non-transitive relations, height counts consecutive strict steps (path length), which can differ from chain length; a finite non-transitive relation with a strict cycle has no height bound at all (cyc3_not_heightLE).
  - The bound n <= h cannot be improved to n < h in general (R4-kleene-bound), but may be loose for a particular f#.
  - Does not say the post-fixpoint reached is a fixpoint (f# x = x) or the least post-fixpoint, in particular when a0 is not a least element or the order is not a partial order.
  - Says nothing about soundness with respect to the concrete semantics by itself; combine with R4-transfer or R4-transfer-lfp.
  - Decidability of the stopping test f# x <= x and computability of f# are not assumed.
- **R4-kleene-bound**
  - Does not say every domain of height h needs h iterations.
- **R4-height-acc**
  - Auxiliary bridge: it carries no design content beyond connecting the two chain conditions.
  - The converse (ACC implies some finite height) is not claimed; it is false in general and no counterexample is formalized here.
  - On a non-transitive relation, neither HeightLE A h nor ACC A implies that ascending sequences stabilize (nb_heightLE_one_ascending_not_stabilizing).
- **R5-widen**
  - widenIter widens at every step and never stops by itself: being a post-fixpoint is not preserved by later iterates, even on a total order with a widening that also satisfies WidenStabilizes (widenIter_postFixpoint_not_persistent). An analyzer must test f# (x n) <= x n at each step and stop at the first success; the theorem guarantees that this happens.
  - On a preorder that is not antisymmetric, WidenTerminates guarantees only one non-strict step of each widened chain of an ascending input, not finitely many strict steps or stabilization up to <= (pbWiden_terminates_infinitely_many_strict). This suffices for the single stopping loop of this theorem; it does not justify widening inside iteration schemes that keep widening after a non-strict step (for example nested loops or chaotic iteration over preorders).
  - Does not bound the number of steps.
  - Does not claim precision: the post-fixpoint reached may be top.
  - Does not say the post-fixpoint reached is a fixpoint or the least post-fixpoint, and does not assume widen is monotone, commutative or associative.
  - Covers only stateless binary widening operators w : A -> A -> A, not delayed widening, widening with thresholds, or step-indexed widenings; does not cover narrowing.
  - The proof is classical; decidability of <= and computability of f# and widen are not assumed.
  - The termination axiom is quantified over ascending inputs only (as in Cousot & Cousot 1992, condition (8)). A variant whose termination axiom quantifies over all input sequences would not need monotonicity of f# or the start condition (by the same argument); that variant is neither stated nor proved here.
  - Soundness for the concrete semantics follows only by combining with R4-transfer or R4-transfer-lfp; it is not part of this statement.
- **R5-widen-diverge**
  - Does not say widening is necessary on every infinite-height domain; only that plain iteration can diverge.
  - The widened result top is sound but maximally imprecise; no precision claim is made.
- **R5-widen-bridge**
  - Auxiliary bridge: lets operators verified against the textbook axiom be used with R5-widen.
  - The converse fails on preorders that are not antisymmetric: WidenStabilizes requires equality, and a widening whose chains cycle between distinct order-equivalent elements satisfies WidenTerminates (and every axiom used by R5-widen) but not WidenStabilizes (widenTerminates_not_widenStabilizes_preorder).
  - Whether the converse holds on partial orders for widenings satisfying a <= a widen b is not formalized here. (Sketch: on a partial order such a widened chain is ascending; if it never stabilized, deleting the inputs at its non-strict steps would give an ascending input whose widened chain is strict at every step.)
  - Stabilization up to the preorder (eventually y m <= y N) is not defined or used here.

**Attractive stronger conclusions that are not established.**

- That `γ a` over-approximates the least fixpoint of a non-monotone concrete transformer (false in general; see the leading non-claim).
- That `γ`-soundness of `α ∘ f ∘ γ` implies soundness on subsets of `γ a` or on individual states for non-monotone `f` (false: `sound_not_subset_of_not_monotone`).
- That `α ∘ f ∘ γ` is a least sound transformer without reflexivity (false: `bestTransformer_lowerBound_not_sound_without_refl`), or that it is unique up to equality without antisymmetry.
- That `WidenTerminates` bounds the number of strict steps, or implies stabilization, on preorders (false: `pbWiden_terminates_infinitely_many_strict`, `widenTerminates_not_widenStabilizes_preorder`), or that a post-fixpoint persists along later widened iterates (false: `widenIter_postFixpoint_not_persistent`).
- That `ACC` or a height bound makes ascending sequences stabilize on a non-transitive relation (false: `nb_heightLE_one_ascending_not_stabilizing`).
- Any precision, exactness, completeness, iteration-count (beyond `R4-kleene-height`), computability or decidability property of the transformers or iterations.

### Escape hatches

Ways around the counterexample-style results (`R3-comp-strict`, `R4-kleene-bound`, `R5-widen-diverge`), verbatim from `results.json`:

- **R3-comp-strict**
  - Escape hatch (exactness of the inner step): equality (f . g)# a = f# (g# a) holds whenever gamma (g# a) = g (gamma a), since then f# (g# a) = alpha (f (g (gamma a))).
  - Escape hatch (completeness of the outer step): more generally, equality holds exactly when alpha (f (gamma (alpha y))) = alpha (f y) for y = g (gamma a), a completeness condition in the sense of Giacobazzi, Ranzato and Scozzari.
  - Escape hatch (domain refinement): a different abstract domain can remove the loss for the same statements; for example, in the interval domain x := x + 1 followed by x := x - 1 maps [1, +infinity) to [1, +infinity) both step by step and as a block.
  - Escape hatch (whole-block abstraction): computing the best transformer of the composed block f . g directly avoids the intermediate abstraction g# a.
- **R4-kleene-bound**
  - Escape hatch: the worst case of h iterations is for plain Kleene iteration from 0 on this chain; on the same chain started from the top element h, the iterate with index 0 is already a post-fixpoint (positive control kleeneHeight_bound_not_attained_from_top, for h >= 1); widening or other iteration strategies (chaotic or worklist iteration over several variables) can also reach a post-fixpoint in fewer steps.
- **R5-widen-diverge**
  - Escape hatch (bounded loops): even on UB, plain Kleene iteration terminates without widening when the loop is bounded (for a counter capped at K, the iterates reach the post-fixpoint atMost K after K + 1 steps).
  - Escape hatch (finite height or ACC): replacing UB by a domain with the ascending chain condition, such as Sign (positive control kleene_converges_sign), restores termination of plain iteration.
  - Escape hatch (refined widening): this does not imply that widening on UB must jump to top at the first step; delayed widening, widening with thresholds, or a subsequent narrowing can keep finite bounds for bounded loops.

For the theorems, every hypothesis is tight, so dropping any single one defeats the conclusion in the named counterexample; weakening a hypothesis in other ways was not examined.

### Tightness status

All 43 hypotheses of the 16 theorems with hypotheses are `tight`, each with a proved counterexample. No hypothesis is labelled `harmless` or `unknown`. Tightness is one hypothesis at a time: a counterexample drops exactly one hypothesis and keeps all others; joint or partial weakenings are not examined.

### Disproved, dropped, and not examined

- **Disproved or dropped statements:** none. Every main statement of the package is proved exactly as stated.
- **Not examined (considered, not formalized):** the relation between `α`-form and `γ`-form soundness (described in the `R2-best-sound` non-claims, not proved); the converse of `R5-widen-bridge` on partial orders (a proof sketch is recorded in its non-claims, not formalized); stabilization up to the preorder as an alternative textbook axiom (not defined); uniqueness of `α` given `γ` (needs antisymmetry); that `ACC` does not imply a finite height (false in general, no counterexample formalized); narrowing; delayed widening, widening with thresholds and other stateful widenings; an end-to-end corollary combining `R4-kleene-acc` with `R4-transfer-lfp` (the faithful content is to apply `R4-transfer-lfp` to the iterate produced by `R4-kleene-acc`).
- **Not examined (scope):** concrete domains other than `Pred σ`; universe-polymorphic statements; other Lean versions; any real analyzer, language or domain implementation.

### Proved boundary examples

These proved statements back the non-claims above.

- `nr2_gc` — Without reflexivity, a Galois connection can hold although `α x` does not soundly describe `x`: on `NR2` (transitive, not reflexive), `nr2Alpha` and `nr2Gamma` form a Galois connection (`GaloisConnection`, `R1-gc-backward`).

  ```lean
  theorem nr2_gc :
    GaloisConnection nr2Alpha nr2Gamma
  ```

- `nr2_not_extensive` — For the same pair, `γ ∘ α` is not extensive: `nr2Gamma` maps every element to `E`, so `x ⊆ nr2Gamma (nr2Alpha x)` fails at `x = U` (`GaloisConnection`, `R1-gc-backward`).

  ```lean
  theorem nr2_not_extensive :
    ¬Extensive nr2Alpha nr2Gamma
  ```

- `sound_le_of_le_gamma_of_monotone` — For monotone `f`, `γ`-soundness lifts to every subset of `γ a` (`R2-best-sound`, `Sound`).

  ```lean
  theorem sound_le_of_le_gamma_of_monotone :
    ∀ {σ A : Type} [LE A] {γ : A → Pred σ} {f : Pred σ → Pred σ} {fs : A → A},
      Monotone f → Sound γ f fs → ∀ {x : Pred σ} {a : A}, x ≤ γ a → f x ≤ γ (fs a)
  ```

- `sound_not_subset_of_not_monotone` — For non-monotone `f` it does not (`R2-best-sound`, `Sound`).

  ```lean
  theorem sound_not_subset_of_not_monotone :
    IsRefl B2 ∧
      GaloisConnection boolAlpha boolGamma ∧
        ¬Monotone notAtFalse ∧
          Sound boolGamma notAtFalse (bestTransformer boolAlpha boolGamma notAtFalse) ∧
            constTrue (Pred.empty Bool) ≤ boolGamma B2.hi ∧
              ¬notAtFalse (constTrue (Pred.empty Bool)) ≤ boolGamma (bestTransformer boolAlpha boolGamma notAtFalse B2.hi)
  ```

- `bestTransformer_lowerBound_not_sound_without_refl` — Without reflexivity the best transformer is only a lower bound of the sound transformers and need not be sound (`R2-best-least`).

  ```lean
  theorem bestTransformer_lowerBound_not_sound_without_refl :
    IsTrans NR3 ∧
      ¬IsRefl NR3 ∧
        GaloisConnection nr3Alpha nr3Gamma ∧
          (Sound nr3Gamma (fun x => U) fun x => NR3.hi) ∧
            (∀ (fs : NR3 → NR3),
                Sound nr3Gamma (fun x => U) fs → ∀ (a : NR3), bestTransformer nr3Alpha nr3Gamma (fun x => U) a ≤ fs a) ∧
              ¬Sound nr3Gamma (fun x => U) (bestTransformer nr3Alpha nr3Gamma fun x => U) ∧
                ¬bestTransformer nr3Alpha nr3Gamma (fun x => U) NR3.lo ≤
                    bestTransformer nr3Alpha nr3Gamma (fun x => U) NR3.lo
  ```

- `lfp_not_postFixpoint_of_not_monotone` — For non-monotone `f`, `lfp f` need not be a post-fixpoint (`lfp`, `R4-lfp-least`).

  ```lean
  theorem lfp_not_postFixpoint_of_not_monotone :
    ¬Monotone nonMonoUniqueFix ∧ ¬nonMonoUniqueFix (lfp nonMonoUniqueFix) ≤ lfp nonMonoUniqueFix
  ```

- `lfp_nonMonoUniqueFix_eq_empty` — For the non-monotone `nonMonoUniqueFix`, `lfp` is empty (`R4-transfer-lfp`).

  ```lean
  theorem lfp_nonMonoUniqueFix_eq_empty :
    lfp nonMonoUniqueFix = Pred.empty Bool
  ```

- `nonMonoUniqueFix_empty` — `nonMonoUniqueFix` maps the empty set to the full set, so the empty set is not a fixpoint (`R4-transfer-lfp`).

  ```lean
  theorem nonMonoUniqueFix_empty :
    nonMonoUniqueFix (Pred.empty Bool) = Pred.univ Bool
  ```

- `isLeastFixpoint_nonMonoUniqueFix_pTrue` — `{true}` is the least (indeed unique) fixpoint of `nonMonoUniqueFix` (`R4-transfer-lfp`).

  ```lean
  theorem isLeastFixpoint_nonMonoUniqueFix_pTrue :
    IsLeastFixpoint nonMonoUniqueFix pTrue
  ```

- `transfer_misses_leastFixpoint_of_not_monotone` — For non-monotone `f`, `γ a` can miss the unique fixpoint of `f`, even with an exact Galois connection on a partial order (`R4-transfer`).

  ```lean
  theorem transfer_misses_leastFixpoint_of_not_monotone :
    IsRefl (Pred Bool) ∧
      IsTrans (Pred Bool) ∧
        IsAntisymm (Pred Bool) ∧
          GaloisConnection id id ∧
            Monotone id ∧
              Sound id nonMonoUniqueFix nonMonoUniqueFix ∧
                PostFixpoint nonMonoUniqueFix pFalse ∧
                  (∀ (x : Pred Bool), nonMonoUniqueFix x = x ↔ x = pTrue) ∧ ¬pTrue ≤ id pFalse
  ```

- `cyc3_not_acc` — A finite non-transitive relation with a strict cycle violates `ACC` (`R4-kleene-acc`).

  ```lean
  theorem cyc3_not_acc :
    IsRefl Cyc3 ∧ ¬IsTrans Cyc3 ∧ ¬ACC Cyc3
  ```

- `cyc3_not_heightLE` — The same relation has no height bound (`R4-kleene-height`).

  ```lean
  theorem cyc3_not_heightLE :
    ∀ (h : Nat), ¬HeightLE Cyc3 h
  ```

- `nb_heightLE_one_ascending_not_stabilizing` — Height 1 on a non-transitive relation does not make ascending sequences stabilize (`ACC`, `HeightLE`, `R4-height-acc`).

  ```lean
  theorem nb_heightLE_one_ascending_not_stabilizing :
    IsRefl NB ∧
      ¬IsTrans NB ∧
        HeightLE NB 1 ∧
          ACC NB ∧ (∀ (n : Nat), nbChain n ≤ nbChain (n + 1)) ∧ ¬∃ N, ∀ (m : Nat), N ≤ m → nbChain m ≤ nbChain N
  ```

- `widenTerminates_not_widenStabilizes_preorder` — `WidenTerminates` does not imply `WidenStabilizes` on a preorder that is not antisymmetric (`R5-widen-bridge`).

  ```lean
  theorem widenTerminates_not_widenStabilizes_preorder :
    IsRefl E2 ∧
      IsTrans E2 ∧
        ¬IsAntisymm E2 ∧
          HeightLE E2 0 ∧
            WidenUpperLeft flipWiden ∧ WidenUpperRight flipWiden ∧ WidenTerminates flipWiden ∧ ¬WidenStabilizes flipWiden
  ```

- `widenIter_postFixpoint_not_persistent` — Being a post-fixpoint is not preserved along `widenIter` (`R5-widen`).

  ```lean
  theorem widenIter_postFixpoint_not_persistent :
    IsRefl (Fin 4) ∧
      IsTrans (Fin 4) ∧
        IsAntisymm (Fin 4) ∧
          WidenUpperLeft widen4 ∧
            WidenUpperRight widen4 ∧
              WidenStabilizes widen4 ∧
                WidenTerminates widen4 ∧
                  Monotone step4 ∧
                    ⟨0, ⋯⟩ ≤ step4 ⟨0, ⋯⟩ ∧
                      PostFixpoint step4 (widenIter widen4 step4 ⟨0, ⋯⟩ 1) ∧
                        ¬PostFixpoint step4 (widenIter widen4 step4 ⟨0, ⋯⟩ 2)
  ```

- `pbWiden_terminates_infinitely_many_strict` — On a preorder that is not antisymmetric, `WidenTerminates` allows widened chains of ascending inputs with infinitely many strict steps (`R5-widen`, `WidenTerminates`).

  ```lean
  theorem pbWiden_terminates_infinitely_many_strict :
    IsRefl PB ∧
      IsTrans PB ∧
        ¬IsAntisymm PB ∧
          WidenUpperLeft pbWiden ∧
            WidenUpperRight pbWiden ∧
              WidenTerminates pbWiden ∧
                Ascending pbStutter ∧
                  (∀ (k : Nat),
                      StrictLt (widenChain pbWiden pbStutter (2 * k)) (widenChain pbWiden pbStutter (2 * k + 1))) ∧
                    ¬∃ N, ∀ (m : Nat), N ≤ m → widenChain pbWiden pbStutter m ≤ widenChain pbWiden pbStutter N
  ```

- `widenTerminates_of_acc` — Helper: under `ACC` every binary operator satisfies `WidenTerminates` (`R4-height-acc`).

  ```lean
  theorem widenTerminates_of_acc :
    ∀ {A : Type} [inst : LE A], ACC A → ∀ (w : A → A → A), WidenTerminates w
  ```

## Evidence

Basis: execution (Lean kernel check), observed 2026-11-20.

**Toolchain.** `leanprover/lean4` release `v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`. The tag was resolved on 2026-11-20 with the GitHub API (`GET /repos/leanprover/lean4/git/ref/tags/v4.34.1` returns an object of type `commit` with this SHA), and the installed toolchain reports `Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)`.

**Build and audit.** `lake build` of a fresh copy of `lean/` succeeds with no errors and no `sorry` warnings. The Lean sources contain no `sorry`, `admit`, `native_decide`, `axiom` or `opaque` declarations, `implemented_by`, `@[extern]`, `unsafe`, `debug.skipKernelTC`, `#exit` or `Lean.ofReduce*`. An axiom audit over all 921 non-internal declarations defined in the `Toy` modules (via `Lean.collectAxioms`) finds only `propext`, `Classical.choice` and `Quot.sound`; the per-declaration record is `audit/axioms.json`. Every Lean name referenced in `results.json` exists.

**Statement hashes.** For every Lean name referenced in `results.json` (results, counterexamples, non-vacuity witnesses, positive controls), `audit/statements.json` records `statement_sha256` = SHA-256 of `toString (repr ci.type)` (the `Lean.Expr` of the statement), and `closure_sha256` = SHA-256 of the newline-joined, sorted list of entries `name : repr type [:= repr value]` for all constants of the `Toy` modules reachable from the statement's type through types, through values of non-theorems, and through constructors of inductive types (theorem proofs are excluded). The program under **Revalidation** recomputes both hashes.

Main results:

| Card | Theorem | Axioms | `statement_sha256` | `closure_sha256` (closure size) |
| --- | --- | --- | --- | --- |
| R1-gc-iff | `galoisConnection_iff_monotone_extensive_reductive_of_refl_of_trans` | none | `a9fcfadf5699b622bd39da72cafccbac70af79b2544e306a3d61f35fff06295b` | `dd0be8fffa7ec9afa9062890946b61b64719476e52dc65e454531dbe397a6605` (8) |
| R1-gc-forward | `monotone_extensive_reductive_of_galoisConnection_of_refl_of_trans` | none | `e9745e504f5c4b12d55aa30e9030bec9b07943d73c71e0901a289439980e2d92` | `dd0be8fffa7ec9afa9062890946b61b64719476e52dc65e454531dbe397a6605` (8) |
| R1-gc-backward | `galoisConnection_of_monotone_extensive_reductive_of_trans` | none | `c32165606f85535b25800e0c480dad736f0ea2e70626b397a9856b6adf52bfed` | `58b69dd12b38b1e4e583d5a85d6bffb681c75fd60387e6ccaea04aa86493f030` (7) |
| R2-best-sound | `bestTransformer_sound_of_galoisConnection_of_refl` | none | `d45f1a6ac5ba43ef9dad28f8d4c14f0a58873f2b02fcc6b24ba94cad2f0e3a92` | `0de17319ffefd5e1fc0be099311d153359689f0ff1bbeae77cefd75870fa1e8e` (6) |
| R2-best-least | `sound_iff_bestTransformer_le_of_galoisConnection` | none | `eccbbc5aea144283153c76cc320d57f62918eed7dc60ce51555fd92b05a5f717` | `da591974e16ea65795d3eabb49c3876a29a995264c6124d01379e35d1cb53e93` (5) |
| R2-best-mono | `bestTransformer_monotone_of_galoisConnection_of_refl_of_trans_of_monotone` | none | `c791e82ce6f7cfdab41b494feb5c3f69a6bad7bb40697d659a48907c08a6bf2f` | `de9832997ee358d042059888be0f8e0a3c4b51d45f8ce5739d90988939ac0fbf` (7) |
| R3-comp-le | `bestTransformer_comp_le_of_galoisConnection_of_refl_of_monotone` | none | `e328895831dadbb33c74edec399de219731006e9c9aac2323844e129d82ee25f` | `d18c6099cab881fe73703d06d552eaf1136ffbcef9d9e370dacbad44b20edbb0` (6) |
| R3-comp-strict | `bestTransformer_comp_strict_sign` | `Classical.choice`, `Quot.sound`, `propext` | `a7e1b9938159a9b90feeda1dddadc617e63b1ec6915ab05ab5e52b9f2b994779` | `bb9ff7afddc5b1e8e27dc86a3fc2109b15745b8e22a1d566b2384983fca575c5` (31) |
| R4-lfp-fix | `lfp_eq_of_monotone` | `Quot.sound`, `propext` | `e3058f281715acd209d314c71199ea7a078b09d76a04cc47b4181ca07a571fba` | `ff8c09cf45035e3f15d78fa703b582860d9df6f3ccdb11311edb37b381cfaba4` (4) |
| R4-lfp-least | `lfp_le_of_le` | none | `8be4be74f3baf4208a6294cd6d945c16fd4cfddc411eaba8cb76124eee5838df` | `6cb6414fba17a36806ff27d4f7b1b4d43cb0832822c9d8f56fa2b2fde80f9cdc` (3) |
| R4-transfer | `lfp_le_gamma_of_monotone_gamma_of_sound_of_postFixpoint` | none | `eb8088de37d0ecc6a0d55b39dd8b1a3d7f75c9c3ad232de38ae5d664092f88c9` | `42c1013aa9e5d336ed17c5bd30cc5a54e3e2c85501c2a59ea6a4af3fd9492fa0` (6) |
| R4-transfer-lfp | `isLeastFixpoint_lfp_and_le_gamma_of_monotone_of_monotone_gamma_of_sound_of_postFixpoint` | `Quot.sound`, `propext` | `cc1d28ac9e226ccec22790cf5d650030fd2fb5d7bf217b1fd9618e2515c27c9a` | `fd9c2430a7f9dc14f50576457cf334b1d873ef4a774f34563b6fc6aebe910198` (7) |
| R4-kleene-acc | `exists_kleene_postFixpoint_of_monotone_of_acc_of_le_apply` | `Classical.choice`, `Quot.sound`, `propext` | `2e36d349690d71945e43c865258fbc1eeaed86333262f05a6ea7ad97dc869977` | `44dce5854cb431eecdabe6267971569a82667dc2806fd480d692358a4358edc3` (7) |
| R4-kleene-height | `exists_kleene_postFixpoint_le_of_monotone_of_heightLE_of_le_apply` | `Classical.choice`, `Quot.sound`, `propext` | `c41118784e30b7f2a00c2669bf793b98e191133ab62efd0f3a1394304b958704` | `f9464469320be5e817617abf2491500feb78cbd649b5377545c46619d821e1f1` (7) |
| R4-kleene-bound | `kleeneHeight_bound_attained` | `Quot.sound`, `propext` | `48c3599d412abf21a25072978a0c8e6e148a971346ee9b3fb9c40f7a14957ec4` | `a2c82a99b4cb421b205111538b3aa80674af485ad514ac37be467cd69105c47c` (11) |
| R4-height-acc | `acc_of_heightLE` | none | `d0bef06a3a2aab1f6323fa43b4aa469034395650071d51e2041cbeaee21271e8` | `0bff2bb7354e739e44e97fe6e8ba29213a861cd7e95b5a4be8c1b000dffc8573` (3) |
| R5-widen | `exists_widenIter_postFixpoint_of_trans_of_upperLeft_of_upperRight_of_terminates_of_monotone_of_le_apply` | `Classical.choice`, `Quot.sound`, `propext` | `b089fc6491f0d6cdb91d96bc0a93998ccf02032c11984d1cbffe3cee518dfe86` | `495f3a336ffef1dd196b5fe234ee59ff457c8f23f728fbd2dc94f7109e6ea5ec` (13) |
| R5-widen-diverge | `kleene_diverges_widen_converges_ub` | `Quot.sound`, `propext` | `a8db594c40a22310f92004261e3db5114a02c8a4f70def97fc1159ceb552fa42` | `b33564118f264633f4600e5c5e202ec8ee1c510656b4991ddc2f5a234c831da5` (42) |
| R5-widen-bridge | `widenTerminates_of_widenStabilizes` | none | `9a3539b1384b3a27350dbc351593c12a501f8ddf656c7536c294930b24276574` | `f91af732de2045593f89448334eea92457341ff8abda243f45461bb4920f5cd8` (7) |

Counterexamples, non-vacuity witnesses and positive controls:

| Declaration | Role | Axioms | `statement_sha256` | `closure_sha256` (closure size) |
| --- | --- | --- | --- | --- |
| `accOfHeight_nonvacuous` | R4-height-acc non-vacuity | `Quot.sound`, `propext` | `480f262aa8ae8368b29b7aa72d1ad7c8276371c251712679c7cde90d0e43f7e8` | `cc4b1a904ee7a7795c09ce52088c31905a3268f89dbf9da98a905be219dcdee2` (19) |
| `accOfHeight_tight` | R4-height-acc tight `hh` | `Quot.sound`, `propext` | `22d1b17ec971f075cc75390071b81f615dc33240cbfe7a72e94913986bb59a86` | `35af2172e9d8a55286e9a6296941050493acce5b1044166c76ab2d0311f74ded` (16) |
| `bestMono_nonvacuous` | R2-best-mono non-vacuity | `Classical.choice`, `Quot.sound`, `propext` | `4b451cfc52c5ab7117872e39a8dee6cc00463ea4e2cc43445ee97c25f4bad027` | `8b32c8224b1323925895d582258664d708e9042a64d953edce188434fb43ac9f` (28) |
| `bestMono_tight_gc` | R2-best-mono tight `hgc` | `Classical.choice`, `Quot.sound`, `propext` | `3ad2e765397a2020c9f6cd98fa3c1a43a9d7178121ae3c19b53fa5a70d70b0cd` | `ec545e7080210fff6aca0cb7ed2c95ea1521bc851f1c9f6b300b53f48ed150fd` (23) |
| `bestMono_tight_monoF` | R2-best-mono tight `hf` | `Classical.choice`, `Quot.sound`, `propext` | `963795e6545eeab0ec97a19b975f7fe6704b6d739748337f4457a7797b4fe834` | `8c55877768e74228310212470222d2045ccf82a757b1c98bc017ebdcba1d621e` (24) |
| `bestMono_tight_refl` | R2-best-mono tight `hrefl` | `Classical.choice`, `Quot.sound`, `propext` | `df8203fd8cbb155e02b32f23791904c09e73a4a0e9687f61b26d577ccce4ca5f` | `1498cb5b918bc565ef289a68527f1bd3aa06e77362e545933d2e42c0c9369226` (22) |
| `bestMono_tight_trans` | R2-best-mono tight `htrans` | `Classical.choice`, `Quot.sound`, `propext` | `ec6c229664c71cd54f4024141fa55b53dd538266c266772aefbb131e6fecaec6` | `834b745b62d4a7046c0c2b36e3816270cb4334c2fd17d832624cf075226c6db8` (29) |
| `bestSound_nonvacuous` | R2-best-sound non-vacuity; R2-best-least non-vacuity | `Classical.choice`, `Quot.sound`, `propext` | `7a94fd40f85d85421e4c490ba1a85b3e775ee389f066e131eaf6634cec837bcc` | `ecbd202e52fcb36be8708509eeb36574a6024e24a87e696767833c861c41c5fe` (24) |
| `bestSound_tight_gc` | R2-best-sound tight `hgc` | none | `a3344784eaf7acbd1957a99e20b8078b134f1780197c0dd033da607e4b4a3ddf` | `1eaa114143637d39cc8dd7d3497bf8798a0556df6354e6d92bada682cd775301` (18) |
| `bestSound_tight_refl` | R2-best-sound tight `hrefl` | `Classical.choice`, `Quot.sound`, `propext` | `17993be6bd4b7815be6665e8bf034f22cb4ff7340cb61b00df36320e0fcb7373` | `02c6950aa53ef08c0925b4aed648afb371e1ebc5075492cc3d178bce8eb55a8b` (21) |
| `bestTransformer_comp_exact_sign_incr` | R3-comp-strict positive control | `Classical.choice`, `Quot.sound`, `propext` | `66acc5c13948eec3d1087b40e0e373ca5aca5c2cde0f2a16c2c14f6b7607c7c0` | `cb369b2ebdabbfd70193168738e9a3ef69ac278ccbf9d3a413a51ea821b2c76a` (16) |
| `compLe_nonvacuous` | R3-comp-le non-vacuity | `Classical.choice`, `Quot.sound`, `propext` | `78b57f8171f5fc539a907043519bd8095d00e7d9740d94f0b3201f83ce928d6b` | `f2da13208dac01e839a63ad44e456e1598cd3bf2c7a5c9fc4cd57d3e070c57d1` (27) |
| `compLe_tight_gc` | R3-comp-le tight `hgc` | `Classical.choice`, `Quot.sound`, `propext` | `ae32a8b77ab04fe6d3ece9317f34f3cab4b1869f9367305b223217e5aa82c78b` | `4341cdb83e850051ed347b057eb74014ea742a93754af952ace68d0efe283add` (20) |
| `compLe_tight_monoF` | R3-comp-le tight `hf` | `Classical.choice`, `Quot.sound`, `propext` | `889f5834bea727d9971c5a590a2051f453c3b9e194241df8e1285515825ef557` | `3f60e074e5b10bccf652e8abba6ff836a4f3dcbc7366ed6d2be4fe587ac4edd6` (21) |
| `compLe_tight_refl` | R3-comp-le tight `hrefl` | `Classical.choice`, `Quot.sound`, `propext` | `1ac6573d5eaf6f30e0d937d6123149fb3d9290d0441d24173cda7be3eaf20057` | `4c95517af3e269178c903cc24946cb9648b97da34a8d494c743e8fd724849902` (21) |
| `gcBackward_nonvacuous` | R1-gc-backward non-vacuity | `Classical.choice`, `Quot.sound`, `propext` | `361205fbb52664e346390fd0b7ee073820e9a1e227661ab105204f9092b9dad9` | `b98b6e514241c69afa23529b8e26049629d7106dcde698cfed0cfc61814b3ae1` (26) |
| `gcBackward_tight_extensive` | R1-gc-backward tight `hext` | none | `9495f61712a0c91fb845d2b73cb2e4a08d184a147f0e912abb135c3cc54cb22e` | `19fd39d530612eb2796beb78b7b7beb2b466d9475bac14e8a3f8c1f4186b6bc8` (17) |
| `gcBackward_tight_monoAlpha` | R1-gc-backward tight `hα` | `Classical.choice`, `Quot.sound`, `propext` | `81b39787e729c92eb201171b5f67fe0b75b9abb4585909977c19bb1e9d5833bb` | `ca65fb3f5f622a50abd13d4543bac1ad0fa20ee78188dde7e66412d9172ab8f6` (18) |
| `gcBackward_tight_monoGamma` | R1-gc-backward tight `hγ` | none | `8aaa8d94d8ffb5c59b0147eacbc6c44207321f9c55550197ef2c41c62abbc74d` | `542a39585386fdb1d5b01e46a0e090e54101c77e114c8a4707346fe0b1a2005f` (21) |
| `gcBackward_tight_reductive` | R1-gc-backward tight `hred` | none | `05a42e63deaecb1401bbe09a20014e41b6198ef591d3d7042b5de01546f7cfda` | `683a6eae96015ee2744223c29b77ab57170179dff41f54c864e4d60164bc5964` (17) |
| `gcBackward_tight_trans` | R1-gc-backward tight `htrans` | `Classical.choice`, `Quot.sound`, `propext` | `432c7c375477f757da2c795912d1375474f86b8da6d4daa8d31903ad960118b8` | `a579e4036584e5405456ed16f93d468e4621649c0a138f59822ebc33e9227657` (28) |
| `gcForward_tight_gc` | R1-gc-forward tight `hgc` | none | `8ac72bdc192bb1a22f6d3ef01b70f62d911e3e263cf64bfd00bc2818a9b5ef40` | `400acf0ccbc77154f1a78265cf3845db4e764e59be784f70370ae0c5e1ae68a2` (18) |
| `gcForward_tight_refl` | R1-gc-forward tight `hrefl` | `Classical.choice`, `Quot.sound`, `propext` | `fecffd4669566dea15a7f3382edd57e19c0d8dc1a4a378a70901619b627d29cb` | `88b03c529bb0356032fa5846eb48792a8b2964eb936973806ba56b220a8e3ea8` (21) |
| `gcForward_tight_trans` | R1-gc-forward tight `htrans` | `Classical.choice`, `Quot.sound`, `propext` | `5b1d638727fab8820f770124db3c6a735a9688393cd1fdf9675995582e59a598` | `bb5d8e4cc0a90d1b618846e54d7e60b7b392124c24e78aa4d4cbbeefb8759c6c` (30) |
| `gcIff_tight_refl` | R1-gc-iff tight `hrefl` | `Classical.choice`, `Quot.sound`, `propext` | `936c2514cca40b9df05f9278c333e4602c5828c609a631d703b282f3141324bd` | `88b03c529bb0356032fa5846eb48792a8b2964eb936973806ba56b220a8e3ea8` (21) |
| `gcIff_tight_trans` | R1-gc-iff tight `htrans` | `Classical.choice`, `Quot.sound`, `propext` | `7cdb11cce5ea0d5d1be3ddfddecaa88f6461acd7a1762b27a97c8b32dce69a26` | `f88359ab755a481b1f83b988a479473ef62f37836d50c8c7ee2903a5100e4604` (29) |
| `gc_nonvacuous` | R1-gc-iff non-vacuity; R1-gc-forward non-vacuity | `Classical.choice`, `Quot.sound`, `propext` | `cf794031fd7b7034aed936b4dfd5a1ddfb3fa9bc175fabfe433e287d092ce09f` | `3c09ae3ec9653d6093da944b0de9a7f726ebf6642ef6cc760747e54051b06bdb` (25) |
| `kleeneAcc_nonvacuous` | R4-kleene-acc non-vacuity | `Quot.sound`, `propext` | `1f18ae0522ca037c199040043441732121bd478cd25df8081c9c589eccf7160a` | `aa71a8e84cc5598e2345c4b9e169aefca00c8171f09ec9fec96d52aa9f104ab8` (23) |
| `kleeneAcc_tight_acc` | R4-kleene-acc tight `hacc` | `Quot.sound`, `propext` | `d4368375887bcb332ed38cef7bf5d2c71fcc94f6f352322ddd9c2cc184241a0e` | `1b8e44b9862a3c28da6b07afea6c531a848fb6cdfcf80ee0755e70dfbc6d81de` (22) |
| `kleeneAcc_tight_monotone` | R4-kleene-acc tight `hmono` | `Quot.sound`, `propext` | `d36afdba8052275ac217295e317e33349372d7180259a3195c9e0f768726d43d` | `3eea657396f1f8914e542da53d685e3897736a080b2628fd797ed8e982cd131b` (21) |
| `kleeneAcc_tight_start` | R4-kleene-acc tight `hstart` | `Quot.sound`, `propext` | `4ff5e3851720604c966648a68eb0263f32ee8e0cd44734d427fb5e44e3466da2` | `533b55187d5858cceba696b8c820fe22ce9a8b68a16565bff5936f3b6944f612` (20) |
| `kleeneHeight_bound_not_attained_from_top` | R4-kleene-bound positive control | `Quot.sound`, `propext` | `ac5c56359f0ea8f0b3cd8342d254892797b3e83cca7feaee22888c33506751fa` | `e8b9c0328b391a06ffc1e05134a7406cea02839e7914114ec40cdb17e9331d6e` (11) |
| `kleeneHeight_nonvacuous` | R4-kleene-height non-vacuity | `Quot.sound`, `propext` | `85b43716bbce9bde85cc2d3ffcc6ba3275fdd768e66ff169038ae31f03e4f19c` | `4b77b660806d39027dc7f1f162003f13afe8497b81ee50f014a70e37091ccbe9` (23) |
| `kleeneHeight_tight_height` | R4-kleene-height tight `hh` | `Quot.sound`, `propext` | `6e4a238f70dae3f5160f8dc2f2332fcb2f1522fddec8f9aee80e05e60a8ff099` | `843594c25dae6983a1eae965626698f5ceed9047832d918fc2cb60cef6c148c3` (22) |
| `kleeneHeight_tight_monotone` | R4-kleene-height tight `hmono` | `Quot.sound`, `propext` | `d42df8c17cfab53945bd534cddf49800c85cb243e0090f124cc8607936ce145c` | `ea3466735ba448fa39e558b46299fca82342a0241afea9be77f5aa1598b4becb` (21) |
| `kleeneHeight_tight_start` | R4-kleene-height tight `hstart` | `Quot.sound`, `propext` | `4e29982c4f03ace995a7ad6fba0cef51a2b2a423474854fa6a4f55c42283f0c4` | `71bddec2ffb455fefb227c92072cc0594d4dbfa29d23da17d4cba3302e489160` (20) |
| `kleene_converges_sign` | R5-widen-diverge positive control | `propext` | `b90ccf97de8be2663017061e951abd3240e6548f5ca2e7a66ab8ff157a50e693` | `fa99d9edbe595e6e904b59cfeda44f09e735011b0a3030f8b3d36baa90802394` (24) |
| `lfpEq_nonvacuous` | R4-lfp-fix non-vacuity | none | `a356df30fcebb7cda59bf3685bf0b5fa6e4cd81174d0be5e8477740a2cf64268` | `fd3080b8ba3fe8d18a02dfa7e67b4f3ad4b1413ed8f698adfe3b6994ad989b33` (4) |
| `lfpEq_tight_monotone` | R4-lfp-fix tight `hf` | `Classical.choice`, `Quot.sound`, `propext` | `53579488115f30947eefae1fb2f74aef93e8016f0d530b5f9a8a8fb6e5897ce3` | `29df494055c6aa1e0c3d22d3d0d2b468b6ea028225e4537a07883fcfaa853895` (5) |
| `lfpFixGamma_nonvacuous` | R4-transfer-lfp non-vacuity | `Quot.sound`, `propext` | `68f169b49e2597be479a5ab51ad514d509e81c9f048696d855514809a35abf38` | `e08bae2a7b400ff563adc78f4c1b0c1bd3021dd1c6bd7d3eac1fb8b46d094a74` (28) |
| `lfpFixGamma_tight_monoGamma` | R4-transfer-lfp tight `hγ` | none | `f805ed23dccdeb951eeb2dc1229f0a9a11c59f12606d088b42cfc291fddc970d` | `9b6a910f8fb0affaa54c2262f32d31d3354adf8d9883ecf064792078e505741a` (21) |
| `lfpFixGamma_tight_monotone` | R4-transfer-lfp tight `hf` | `Classical.choice`, `Quot.sound`, `propext` | `c82ff371db75bfa18db2fcc5dd3d4b6a6890371d3b760363bd3cefe20c2741ff` | `66bfa933b2ef3f7340a91beaa9c5b398452dc3402501d46c028a21421dbc8483` (10) |
| `lfpFixGamma_tight_postFixpoint` | R4-transfer-lfp tight `ha` | none | `025ac6f0aa12b5918a84da195102768855194960aa6f86b53f078ead240f00ef` | `cc97528ced1d999c823e4f1ca0526b8da2add17d65e5f6750abb91fcc34013fe` (21) |
| `lfpFixGamma_tight_sound` | R4-transfer-lfp tight `hs` | none | `52f1acac7c28b64e9c49b31b98857d465a4ba3c1ca31dab94d44db8633a44801` | `cc97528ced1d999c823e4f1ca0526b8da2add17d65e5f6750abb91fcc34013fe` (21) |
| `lfpGamma_nonvacuous` | R4-transfer non-vacuity | `Quot.sound`, `propext` | `ce646e87a4bf4bcc4680f36777f76658b3c3bdb6522b29ff27525169b9482d54` | `e08bae2a7b400ff563adc78f4c1b0c1bd3021dd1c6bd7d3eac1fb8b46d094a74` (28) |
| `lfpGamma_tight_monoGamma` | R4-transfer tight `hγ` | none | `01c13bcf1f9a3835e6a8a747b8b41bb525c435403cfb7021e734382236783e5c` | `460d5e3088f51d27754b1f02c97d06610b2dab55928afd9e0e835a60446a2770` (20) |
| `lfpGamma_tight_postFixpoint` | R4-transfer tight `ha` | none | `c6b857affeab68616aefe0e529f50d776a9f840bb84eeeed25462cff0f281089` | `5458b3afe67987ce47799db181a92c2168e3ea964c260bc161e43925f26caa83` (20) |
| `lfpGamma_tight_sound` | R4-transfer tight `hs` | none | `5b9548b9852851b409a4a100ce80c097403a03eb62c9dfc6d510ddcdb0387f4e` | `5458b3afe67987ce47799db181a92c2168e3ea964c260bc161e43925f26caa83` (20) |
| `lfpLe_nonvacuous` | R4-lfp-least non-vacuity | none | `b8685bf56766f0b396f092613e11bed1189d89c8ec39ef958cfb3f6e5777e373` | `7003ea28a955a8c2602cd36ff2475e676c0ab0bd2d1707840f4376f0109fb478` (4) |
| `lfpLe_tight_postFixpoint` | R4-lfp-least tight `hx` | none | `27ccb3bedeeda9d6b5990442fd9e6e7e0a299fc5445149728376ef4e780cd796` | `ed3437b9ffd06165a0cfc147ae9d088595847acd4d309baf4631845f222905fd` (5) |
| `soundIff_tight_gc` | R2-best-least tight `hgc` | none | `07071f0592f126e5dd3e2a34de62a10b3e1d647baf8c1cefaab0694f4b96156c` | `a14cf9ffabccfe15d93292a44b6b131d122c620fbfa8b5f720c12c5e17ee4dd0` (17) |
| `widenBridge_nonvacuous` | R5-widen-bridge non-vacuity | `Classical.choice`, `Quot.sound`, `propext` | `2b0fd62988f36d315d4f384d25cc11603fcdbfee23525a4a52a96a289e0bd8a7` | `a77bd816b6a655c28b3283435f86c3afa3ef3171a744bc0248b435526e0a26fb` (20) |
| `widenBridge_tight` | R5-widen-bridge tight `h` | `Quot.sound`, `propext` | `9f07e27c2b79f1884266a7fa8ff375f29a0e2d57577910ac5c46885ead1e2bc3` | `f91af732de2045593f89448334eea92457341ff8abda243f45461bb4920f5cd8` (7) |
| `widen_nonvacuous` | R5-widen non-vacuity | `Quot.sound`, `propext` | `3df21698a8192ca8870e50f0da472a82f7e7ef0bd5b79bce1e8625b13ef55427` | `b0d5426e539e734d128ec21d80cbfaba4115891cafd47e0c256de05e9539afdc` (27) |
| `widen_tight_monotone` | R5-widen tight `hmono` | `Classical.choice`, `Quot.sound`, `propext` | `4ff4200b75cc8efd6b793825590c1095fd75abccae9bb14fc5d8610b576844dc` | `dd4d6670e3cb4c6e0341b9fd2ec46f8d6e09979e9be71b1f2187f2799dd26e02` (37) |
| `widen_tight_start` | R5-widen tight `hstart` | `Classical.choice`, `Quot.sound`, `propext` | `868ee31d9575cb02a235a46b284fe8a5798236121b6ff6cdd6c274ad42c56720` | `0e91797cb324304ddb93aa08ba5cd823575c855a4618cc94b921990a772b7b63` (37) |
| `widen_tight_terminates` | R5-widen tight `hT` | `Quot.sound`, `propext` | `6932257f7cabc805caeebdb5987822f5d0544633981ac7da30e0601cbf1f2e09` | `495f3a336ffef1dd196b5fe234ee59ff457c8f23f728fbd2dc94f7109e6ea5ec` (13) |
| `widen_tight_trans` | R5-widen tight `htrans` | `Quot.sound`, `propext` | `c9996643aa1201a4cd932fc8cbcb434a3f2eafede33555f2e924d60c70d3cf63` | `b708e648fbbf5d5de1cb663b708ca271756195b18cb407d91c6adda9418cc4b6` (31) |
| `widen_tight_upperLeft` | R5-widen tight `hL` | `Quot.sound`, `propext` | `fb4ac1b96cf795b0fceea8bddeeaa5827751ef1711cd63363813555438db90a2` | `78652b963bc7a1f830161d7cdc9106f49d84a2073c22e04c118e6fb4244ee40f` (32) |
| `widen_tight_upperRight` | R5-widen tight `hR` | `Quot.sound`, `propext` | `7db72bbff69b0267de63828256dbe6874dcbfec25eb89ac9ea897a540c83848c` | `e9032edbd91f77f525b7b65b906f6b7f4cd1a14fe739d16aa254bfecdceda109` (21) |

Proved boundary examples (axioms): `nr2_gc`: `Classical.choice`, `Quot.sound`, `propext`; `nr2_not_extensive`: `Classical.choice`, `Quot.sound`, `propext`; `sound_le_of_le_gamma_of_monotone`: none; `sound_not_subset_of_not_monotone`: `Classical.choice`, `Quot.sound`, `propext`; `bestTransformer_lowerBound_not_sound_without_refl`: `Classical.choice`, `Quot.sound`, `propext`; `lfp_not_postFixpoint_of_not_monotone`: `Quot.sound`, `propext`; `lfp_nonMonoUniqueFix_eq_empty`: `Quot.sound`, `propext`; `nonMonoUniqueFix_empty`: `Quot.sound`, `propext`; `isLeastFixpoint_nonMonoUniqueFix_pTrue`: `Classical.choice`, `Quot.sound`, `propext`; `transfer_misses_leastFixpoint_of_not_monotone`: `Classical.choice`, `Quot.sound`, `propext`; `cyc3_not_acc`: `propext`; `cyc3_not_heightLE`: `Quot.sound`, `propext`; `nb_heightLE_one_ascending_not_stabilizing`: `Classical.choice`, `Quot.sound`, `propext`; `widenTerminates_not_widenStabilizes_preorder`: none; `widenIter_postFixpoint_not_persistent`: `Classical.choice`, `Quot.sound`, `propext`; `pbWiden_terminates_infinitely_many_strict`: `Classical.choice`, `Quot.sound`, `propext`; `widenTerminates_of_acc`: none.

Facts about the fixtures (axioms): `signGC`: `Classical.choice`, `Quot.sound`, `propext`; `Sign.heightLE`: `Quot.sound`, `propext`; `UB.not_acc`: `propext`; `UB.not_heightLE`: `Quot.sound`, `propext`; `lfp_counterStep`: none; `post_monotone`: none. The axioms of each definition example (under **Findings**) are recorded in `audit/axioms.json`; like every declaration of the package, each uses at most `propext`, `Classical.choice` and `Quot.sound`.

**Primary sources.** Exact records as cited on the cards. The bibliographic metadata (title, authors, venue, volume, pages) of every DOI below was confirmed against Crossref on 2026-11-20; the Knaster record (no DOI) against bibliographic databases; the Mathlib commit `5f78f9ce46fc85fa3cb45561d47b489c4c98cd04` and the two cited Mathlib files (`Mathlib/Order/GaloisConnection/Defs.lean`, `Mathlib/Order/FixedPoints.lean`, including `GaloisConnection`, `monotone_intro`, `le_u_l`, `monotone_u`, `OrderHom.lfp`, `lfp_le`, `map_lfp`) were confirmed at that commit. Section- and proposition-level content attributions are as stated on each card and were checked against the full texts named there (author-hosted reprints where noted); where a card says a work is cited at chapter level, as a general reference, or only as attributed by another source, no further content is relied on. The published title of the LMCS article is "Fixed Points Theorems for Non-Transitive Relations" (publisher page and Crossref).

- P. Cousot and R. Cousot, "Abstract interpretation: a unified lattice model for static analysis of programs by construction or approximation of fixpoints", POPL 1977, pp. 238-252, doi:10.1145/512950.512973.
- P. Cousot and R. Cousot, "Systematic design of program analysis frameworks", POPL 1979, pp. 269-282, doi:10.1145/567752.567778.
- P. Cousot and R. Cousot, "Comparing the Galois connection and widening/narrowing approaches to abstract interpretation", PLILP 1992, LNCS 631, pp. 269-295, doi:10.1007/3-540-55844-6_142.
- P. Cousot and R. Cousot, "Abstract interpretation frameworks", Journal of Logic and Computation 2(4):511-547, 1992, doi:10.1093/logcom/2.4.511.
- B. Knaster, "Un théorème sur les fonctions d'ensembles", Annales de la Société Polonaise de Mathématique 6:133-134, 1928.
- A. Tarski, "A lattice-theoretical fixpoint theorem and its applications", Pacific Journal of Mathematics 5(2):285-309, 1955, doi:10.2140/pjm.1955.5.285.
- O. Ore, "Galois connexions", Transactions of the American Mathematical Society 55(3):493-513, 1944, doi:10.1090/S0002-9947-1944-0010555-7.
- T. Nipkow and G. Klein, Concrete Semantics with Isabelle/HOL, Springer 2014, doi:10.1007/978-3-319-10542-0; Chapter 13 "Abstract Interpretation", pp. 219-280, doi:10.1007/978-3-319-10542-0_13.
- R. Giacobazzi, F. Ranzato and F. Scozzari, "Making abstract interpretations complete", Journal of the ACM 47(2):361-416, 2000, doi:10.1145/333979.333989.
- A. Thakur, A. Lal, J. Lim and T. Reps, "PostHat and all that: automating abstract interpretation", Electronic Notes in Theoretical Computer Science 311:15-32, 2015, doi:10.1016/j.entcs.2015.02.003.
- J. Dubut and A. Yamada, "Fixed Points Theorems for Non-Transitive Relations", Logical Methods in Computer Science 18(1):30, 2022, doi:10.46298/LMCS-18(1:30)2022; A. Yamada and J. Dubut, "Complete Non-Orders and Fixed Points", Archive of Formal Proofs, 2019, https://isa-afp.org/entries/Complete_Non_Orders.html.
- T. Reps, M. Sagiv and G. Yorsh, "Symbolic implementation of the best transformer", VMCAI 2004, LNCS 2937, pp. 252-266, doi:10.1007/978-3-540-24622-0_21.
- D. Darais and D. Van Horn, "Constructive Galois connections: taming the Galois connection framework for mechanized metatheory", ICFP 2016, pp. 311-324, doi:10.1145/2951913.2951934; "Constructive Galois connections", Journal of Functional Programming 29, e11, 2019, doi:10.1017/S0956796819000066.
- A. Miné, "Tutorial on static inference of numeric invariants by abstract interpretation", Foundations and Trends in Programming Languages 4(3-4):120-372, 2017, doi:10.1561/2500000034.
- J.-H. Jourdan, V. Laporte, S. Blazy, X. Leroy and D. Pichardie, "A formally-verified C static analyzer", POPL 2015, pp. 247-259, doi:10.1145/2676726.2676966.
- F. Besson, D. Cachera, T. Jensen and D. Pichardie, "Certified static analysis by abstract interpretation", FOSAD V, LNCS 5705, pp. 223-257, 2009, doi:10.1007/978-3-642-03829-7_8.
- D. Cachera, T. Jensen, D. Pichardie and V. Rusu, "Extracting a data flow analyser in constructive logic", Theoretical Computer Science 342(1):56-78, 2005, doi:10.1016/j.tcs.2005.06.004.
- D. Cachera and D. Pichardie, "A certified denotational abstract interpreter", ITP 2010, LNCS 6172, pp. 9-24, doi:10.1007/978-3-642-14052-5_3.
- T. Nipkow, "Abstract interpretation of annotated commands", ITP 2012, LNCS 7406, pp. 116-132, doi:10.1007/978-3-642-32347-8_9.
- F. Nielson, H. R. Nielson and C. Hankin, Principles of Program Analysis, Springer 1999, doi:10.1007/978-3-662-03811-6; Chapter 4, pp. 211-282, doi:10.1007/978-3-662-03811-6_4.
- G. Struth, "Properties of Orderings and Lattices", Archive of Formal Proofs, 2018, https://isa-afp.org/entries/Order_Lattice_Props.html.
- Mathlib, leanprover-community/mathlib4, commit 5f78f9ce46fc85fa3cb45561d47b489c4c98cd04 (cited for comparison only; not a dependency).
- P. Cousot, Principles of Abstract Interpretation, MIT Press, 2021, ISBN 978-0-262-04490-5; X. Rival and K. Yi, Introduction to Static Analysis, MIT Press, 2020, ISBN 978-0-262-04341-0 (general references; no section-level content relied on).

## Revalidation

Requires `elan` (the file `lean/lean-toolchain` selects `leanprover/lean4:v4.34.1`, which `elan` installs on first use) and `python3`. The primary check is one command, run from the package directory:

```sh
python3 support/revalidate.py .
```

`support/revalidate.py` (a self-contained Python 3 script with no dependencies beyond the standard library) never modifies the package. It scans the Lean sources, builds a copy of `lean/` in a temporary directory, and checks, in this order:

1. No Lean source under `lean/` contains `sorry`, `admit` or `native_decide`, or declares an `axiom` (comments are stripped before the scan).
2. `lake build` of the copy succeeds.
3. Every non-internal declaration of the `Toy` modules depends only on `propext`, `Classical.choice` and `Quot.sound`, as computed by `Lean.collectAxioms` in a generated audit file that imports `Toy`.
4. For every Lean name referenced in `results.json` (fields `lean`, `nonvacuity_witness_lean`, `positive_control_lean`, and the `counterexample` of each hypothesis) and every name recorded in `audit/statements.json`, the declaration exists, and its two hashes equal the recorded ones. Exactly what is hashed: `statement_sha256` is the SHA-256 of `toString (repr ci.type)`, the `Lean.Expr` of the statement; `closure_sha256` is the SHA-256 of the newline-joined, sorted list of entries `name : repr type`, followed by ` := repr value` for constants that are not theorems, over all constants of the `Toy` modules reachable from the statement's type through types, through values of non-theorems, and through constructors of inductive types (theorem proofs are excluded); `closure_size` is the number of entries.

Expected output for this package:

```text
ok   lake build
ok   axioms (921 declarations)
ok   statement hashes (79 hashed names; 0 referenced names exist but carry no recorded hash)
REVALIDATED
```

The exit status is 0 exactly when every check passes. The build, axiom and hash checks can also be run by hand with `lake` and `python3` only, as follows.

Build, from the package directory:

```sh
cd lean
lake build                      # must end with: Build completed successfully
```

Axiom audit, run from `lean/` (fails on any axiom outside `propext`, `Classical.choice`, `Quot.sound`, or on any `axiom`/`opaque` declaration); expected output `AXIOM_AUDIT_OK 921 declarations; ...`:

```sh
cat > /tmp/AxiomAudit.lean <<'EOF'
import Lean
import Toy
open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked := 0
  for (n, ci) in env.constants.toList do
    match env.getModuleIdxFor? n with
    | some idx =>
      if (`Toy).isPrefixOf env.header.moduleNames[idx.toNat]! && !n.isInternal then
        if ci matches .axiomInfo _ || ci matches .opaqueInfo _ then
          throwError "{n} is an axiom or opaque declaration"
        for a in (← collectAxioms n) do
          unless allowed.contains a do throwError "{n} depends on {a}"
        checked := checked + 1
    | none => pure ()
  IO.println s!"AXIOM_AUDIT_OK {checked} declarations; axioms within propext, Classical.choice, Quot.sound"
EOF
lake env lean /tmp/AxiomAudit.lean
```

For a readable per-theorem record, `#print axioms Toy.AbsInt.<name>` for any name in the Evidence tables prints the same axiom sets.

Statement and closure hashes, run from `lean/` (the commands below write and remove a temporary `names.txt` there); expected output `{"checked": 79, "mismatches": []}`:

```sh
cat > /tmp/names.py <<'EOF'
import json, sys
names = set()
for r in json.load(open(sys.argv[1])):
    names.add(r["lean"])
    for k in ("nonvacuity_witness_lean", "positive_control_lean"):
        if r.get(k):
            names.add(r[k])
    for h in r["hypotheses"]:
        if h.get("counterexample"):
            names.add(h["counterexample"])
print("\n".join(sorted(names)))
EOF
cat > /tmp/hashes.py <<'EOF'
import hashlib, json, sys
out = {}
for l in sys.stdin:
    if l.startswith("{"):
        d = json.loads(l)
        out[d["name"]] = {
            "statement_sha256": hashlib.sha256(d["type_repr"].encode()).hexdigest(),
            "closure_sha256": hashlib.sha256("\n".join(d["closure"]).encode()).hexdigest(),
            "closure_size": len(d["closure"]),
        }
ref = json.load(open(sys.argv[1]))["statements"]
bad = sorted(n for n in set(ref) | set(out) if ref.get(n) != out.get(n))
print(json.dumps({"checked": len(out), "mismatches": bad}))
sys.exit(1 if bad else 0)
EOF
cat > /tmp/StatementHashes.lean <<'EOF'
import Lean
import Toy
open Lean Elab Command

/-- Constants defined in a module of the `Toy` library. -/
def inToy (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => (`Toy).isPrefixOf env.header.moduleNames[idx.toNat]!
  | none => false

/-- `Toy` constants reachable from the given names through types, and through
values of non-theorems, plus constructors of inductive types. -/
partial def closure (env : Environment) : List Name → NameSet → NameSet
  | [], acc => acc
  | n :: rest, acc =>
    if acc.contains n || !inToy env n then closure env rest acc else
    let acc := acc.insert n
    match env.find? n with
    | none => closure env rest acc
    | some ci =>
      let vs := match ci.value? (allowOpaque := true) with
        | some v => if ci.isTheorem then [] else v.getUsedConstants.toList
        | none => []
      let ks := match ci with
        | .inductInfo iv => iv.ctors
        | _ => []
      closure env (ci.type.getUsedConstants.toList ++ vs ++ ks ++ rest) acc

def line (env : Environment) (c : Name) : String :=
  match env.find? c with
  | some cc => c.toString ++ " : " ++ toString (repr cc.type) ++
      (match cc.value? (allowOpaque := true) with
       | some v => if cc.isTheorem then "" else " := " ++ toString (repr v)
       | none => "")
  | none => c.toString

#eval show CommandElabM Unit from do
  let env ← getEnv
  let names := ((← IO.FS.readFile "names.txt").splitOn "\n").filter (· ≠ "")
  for s in names do
    let n := s.toName
    let some ci := env.find? n | throwError "missing {n}"
    let cl := (closure env ci.type.getUsedConstants.toList {}).toList.map (line env)
    IO.println (Json.mkObj [("name", toJson s), ("type_repr", toJson (toString (repr ci.type))),
      ("closure", toJson (cl.toArray.qsort (· < ·)))]).compress
EOF
python3 /tmp/names.py ../results.json > names.txt
lake env lean /tmp/StatementHashes.lean | python3 /tmp/hashes.py ../audit/statements.json
rm names.txt
```

A change of any statement or of any definition it depends on changes its hashes; a change confined to proofs does not. The checks establish only kernel validity, axiom usage and statement identity; the modeling bridges and the prior-art attributions must be re-checked by reading.
