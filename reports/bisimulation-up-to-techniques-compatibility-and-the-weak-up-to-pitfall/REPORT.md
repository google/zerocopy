# Bisimulation up-to techniques: compatibility, and the weak up-to pitfall

## Summary

This package is a Lean 4 mechanization (no Mathlib) of the first-order theory of up-to techniques for bisimulation proofs, of the standard strong and weak techniques, and of the classical failure of "weak bisimulation up to weak bisimilarity". All 17 results are kernel-checked; none uses `sorry`, and the only axioms used are `propext` and `Quot.sound`. One sentence per result, with its key hypotheses (`b` is a functional on `Prop`-valued relations, `f`, `g` are up-to functions, `sb` / `wb` are the strong and the strong-challenge/weak-response weak bisimulation functionals of a labelled transition system (LTS), `~`, `≈`, `≳` are strong bisimilarity, weak bisimilarity and expansion):

1. **compatible-implies-sound.** For a monotone functional `b`, every monotone up-to function `f` with `f (b R) ⊑ b (f R)` for all `R` is sound for `b`: `R ⊑ b (f R)` implies `R ⊑ gfp b`.
2. **compatible-closed-under-composition.** If `f` and `g` are monotone and each satisfies `f ∘ b ⊑ b ∘ f`, `g ∘ b ⊑ b ∘ g`, then `f ∘ g` is compatible with `b` (monotone and commuting with `b`); `b` need not be monotone.
3. **compatible-closed-under-union.** For a monotone functional `b`, the pointwise union of any family (possibly empty) of monotone functions that each commute with `b` is compatible with `b`.
4. **compatible-closed-under-iteration.** For a monotone functional `b` and a monotone `f` with `f ∘ b ⊑ b ∘ f`, the ω-iteration `f^ω R = ⋃ₙ fⁿ R` (with `f⁰ R = R`) is compatible with `b`.
5. **strong-upto-union-with-bisimilarity.** For every monotone functional `b`, up to union with the greatest fixpoint (`R ↦ R ∪ gfp b`) is compatible with `b`, hence sound; for every LTS this gives `R ∪ ~` for `sb` and `R ∪ ≈` for `wb`.
6. **strong-upto-bisimilarity-both-sides.** For every LTS, strong bisimulation up to strong bisimilarity on both sides (`R ↦ ~R~`) is compatible with `sb`, hence sound.
7. **strong-upto-equivalence-closure.** For every LTS, strong bisimulation up to equivalence closure is compatible with `sb`, hence sound.
8. **weak-upto-weak-bisimilarity-unsound.** Over the finite process LTS with two visible labels, weak bisimulation up to weak bisimilarity (`R ↦ ≈R≈`) is not sound for `wb`: `R = {(τ.a.0, 0)}` satisfies `R ⊑ wb (≈R≈)`, yet `τ.a.0 ≉ 0`.
9. **weak-upto-strong-bisimilarity.** For every LTS, weak bisimulation up to strong bisimilarity on both sides (`R ↦ ~R~`) is compatible with `wb`, hence sound.
10. **weak-upto-expansion-asymmetric.** For every LTS and relation `R`, if every move of the left state of an `R`-pair is answered by a weak move of the right state into `≳R≈`, and every move of the right state is answered into `≈R≲`, then `R ⊑ ≈`.
11. **weak-upto-expansion.** For every LTS, weak bisimulation up to expansion (`R ↦ ≳R≲`) is sound for `wb`.
12. **weak-upto-expansion-not-compatible.** Over the process LTS with any label type (even an empty one), `R ↦ ≳R≲` is monotone but does not commute with `wb`, hence is not compatible with `wb` (witness: `R = ∅` and the pair `(τ.0, 0)`).
13. **weak-upto-expansion-left-weak-right-symmetric-unsound.** Over the finite process LTS with two visible labels, using `≳R≈` in both clauses of `wb` is not sound: `R = {(0, τ.a.0)}` satisfies `R ⊑ wb (≳R≈)`, yet `0 ≉ τ.a.0`.
14. **weak-bisimilarity-not-sum-congruence** (reference point). Over the finite process LTS with two visible labels, `τ.a.0 ≈ a.0` but `τ.a.0 + b.0 ≉ a.0 + b.0`; over any label type with an element `a`, `τ.0 ≈ 0` but `τ.0 + a.0 ≉ 0 + a.0`.
15. **weak-upto-sum-context-unsound.** Over the finite process LTS with two visible labels, weak bisimulation up to `+`-contexts is not sound for `wb`; over the process LTS with label type `L`, it is sound if and only if `L` is empty.
16. **strong-upto-sum-context.** Over the process LTS with any label type, strong bisimulation up to `+`-contexts (closure under the hole, closed terms and nested binary choice) is compatible with `sb`, hence sound.
17. **companion-compatible-and-sound.** For a monotone functional `b`, the companion of `b` (the pointwise union of all monotone functions commuting with `b`) is compatible with `b` and sound for `b`; for every `b`, every monotone function commuting with `b` is below the companion, and `companion b ∅ = gfp b`.

The failure in result 8 is exact in scope: the technique `≈R≈` is unsound for the symmetric weak functional `wb` in general (the one-pair relation `{(τ.a.0, 0)}` is a counterexample), and the sound variants proved here are listed, with their exact hypotheses, in the card for result 8 under **Findings**. What each result does *not* establish is listed first under **Boundaries**; read those non-claims before using any result. Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about up-to techniques used in real equivalence, refinement or compiler-correctness proofs (the **Modeling bridge** subsection under **Findings** argues the connection separately).

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

## Applicability

**What is modelled.** This is a toy model. All definitions live in the Lean namespace `Toy.UpTo` of the self-contained Lake project in `lean/` (library `ToyUpTo`):

- relations are `Prop`-valued and homogeneous, `Rel S := S → S → Prop`, ordered by inclusion `⊑`; the greatest fixpoint `gfp b` is defined, without any lattice library, as the union of all post-fixpoints of `b`;
- a labelled transition system is an arbitrary relation `T : S → Option L → S → Prop` over an arbitrary state type `S` and label type `L`, where `none` is the silent action τ;
- strong bisimilarity `~`, weak bisimilarity `≈` and the expansion preorder `≳` are `gfp` of the functionals `sb`, `wb` and `ex`; `wb` is Milner's strong-challenge/weak-response form, and a weak-challenge variant `wbWeak` is defined for comparison;
- concrete examples and counterexamples use one finite, recursion-free process syntax with inaction `0`, prefix `μ.P` (`μ` a visible label or τ) and binary choice `P + Q`, with its usual structural operational semantics `PStep`; most examples use a two-element label type `Lbl = {a, b}`.

Results 1–4 and 17 hold for every functional on relations satisfying their hypotheses; results 5–7, 9–11 hold for every LTS (results 6, 7, 9, 11 with no hypotheses at all); results 12, 15 (characterization) and 16 hold for the process LTS over an arbitrary label type; the counterexamples 8, 13, 14 and the first half of 15 are closed statements about the process LTS over `Lbl` (with one-label variants over an arbitrary non-empty label type for 14 and 15).

**What real systems the definitions are meant to capture.** The definitions are the textbook ones for CCS-like process calculi (Milner 1989; Sangiorgi–Milner 1992; Pous 2007; Pous–Sangiorgi 2011). The design question they inform is which up-to techniques a refinement or equivalence proof can rely on, including simulation-based compiler-correctness proofs that discharge a matching obligation "up to" a closure of the simulation relation. That connection is a modeling bridge, argued in prose under **Findings** and labelled `derived (modeling bridge)`; no theorem here is about a real compiler or verification framework.

**Known gaps** between the toy model and real simulation-based proofs:

- *Divergence insensitivity.* `≈` and `≳` as defined here identify a silently diverging state with a dead one (`divergence_insensitive`: in a two-state system, a τ-loop is weakly bisimilar to, and expands, a dead state, while the two are not strongly bisimilar). Divergence-sensitive equivalences and simulations with well-founded stuttering measures are not modelled. The recursion-free process terms cannot diverge, so the concrete examples never exercise this.
- *Homogeneous state space.* `Rel S` relates states of one type. Simulations between different source and target systems (`S₁ → S₂ → Prop`) are not modelled.
- *First-order compatibility only.* Sangiorgi's respectful functions and second-order notions (functions below the companion, size preservation) are not formalized, apart from the definition of the companion and result 17.
- *Small syntax.* No recursion, parallel composition, restriction or name passing; contexts are limited to `+`-contexts (and, for one negative result, prefix contexts).

**Subjects.** `REPORT.json` lists the Lean 4 toolchain release that checks every proof, the primary papers whose definitions and results are restated, and four external proof-assistant developments at pinned commits: the Agda development `nad/up-to` and the Coq/Rocq developments `damien-pous/coinduction`, `damien-pous/coinduction-examples` and `rocq-archive/weak-up-to` (see **Evidence**). The papers and these developments are prior art for the definitions and the known results; nothing is imported from any of them or from any other proof development. The proofs were checked with `leanprover/lean4:v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`), with core Lean only (no Mathlib, no `[[require]]` dependencies). Other toolchain versions were not examined.

## Findings

Every theorem below is checked by the Lean kernel. Unless a card says otherwise, each card's evidence is:

```text
Basis: execution (Lean kernel check)
```

Any statement connecting a theorem to real systems is a separate claim marked `Basis: derived (modeling bridge)`, with its reasoning (see "Modeling bridge" at the end of this section).

Each card's statement block quotes the Lean source verbatim with the proof omitted, each theorem labelled by a `-- lean/ToyUpTo/<File>.lean:<lines>` comment. All declarations live in namespace `Toy.UpTo`; free `S` and `L` are the enclosing section's implicit variables (`{S : Type u}`, `{L : Type v}`). The other `--` lines in a statement block are informal glosses (prose), not checked Lean terms.

### Definitions (key definitions unfolded)

The Lean sources are in `lean/ToyUpTo/` (modules `Basic`, `BasicExamples`, `LTS`, `WeakFacts`, `Proc`, `Strong`, `Weak`, `Context`, `Companion`, `Checks`, `Witnesses`). All names below are in the namespace `Toy.UpTo`.

**Relations and the abstract theory** (`Basic.lean`):

```lean
abbrev Rel (S : Type u) : Type u := S → S → Prop
def Incl (R R' : Rel S) : Prop := ∀ p q, R p q → R' p q          -- notation  R ⊑ R'
def botRel : Rel S := fun _ _ => False                             -- ∅
def topRel : Rel S := fun _ _ => True                              -- ⊤
def idRel  : Rel S := fun p q => p = q
def MonoRel (F : Rel S → Rel S) : Prop := ∀ R R', R ⊑ R' → F R ⊑ F R'
def gfp (b : Rel S → Rel S) : Rel S := fun p q => ∃ R, R ⊑ b R ∧ R p q
     -- union of all post-fixpoints; the greatest fixpoint when b is monotone
def Progresses (b) (R R' : Rel S) : Prop := R ⊑ b R'
def Sound (b f : Rel S → Rel S) : Prop := ∀ R, Progresses b R (f R) → R ⊑ gfp b
     -- unfolded: ∀ R, R ⊑ b (f R) → R ⊑ gfp b
def Commutes (b f : Rel S → Rel S) : Prop := ∀ R, f (b R) ⊑ b (f R)
structure Compatible (b f : Rel S → Rel S) : Prop where
  mono : MonoRel f
  comm : Commutes b f
def comp (f g) : Rel S → Rel S := fun R => f (g R)
def iSup {ι : Type v} (F : ι → Rel S → Rel S) : Rel S → Rel S := fun R p q => ∃ i, F i R p q
def iter (f) : Nat → Rel S → Rel S   | 0, R => R  | n+1, R => f (iter f n R)
def omega (f) : Rel S → Rel S := fun R p q => ∃ n, iter f n R p q
def constGfp (b) : Rel S → Rel S := fun _ => gfp b
def reflClo (R) : Rel S := fun p q => R p q ∨ p = q                  -- R ∪ id
def symClo  (R) : Rel S := fun p q => R p q ∨ R q p                  -- R ∪ R⁻¹
def stepSq  (R) : Rel S := fun p q => R p q ∨ ∃ r, R p r ∧ R r q      -- R ∪ R;R
def unionGfp (b) : Rel S → Rel S := fun R p q => R p q ∨ gfp b p q    -- R ∪ gfp b
```

`Compatible` is Pous's first-order notion of `b`-compatibility; the two components `MonoRel f` and `Commutes b f` are used as separate hypotheses by the theorems below. Proved infrastructure: `incl_gfp_of_postfixed` (`R ⊑ b R → R ⊑ gfp b`, no monotonicity needed), `gfp_postfixed` (`MonoRel b → gfp b ⊑ b (gfp b)`), `compatible_id`, `compatible_constGfp` (needs `MonoRel b` as a hypothesis), `iter_mono`, `iter_commutes`.

**Transition systems and behavioural relations** (`LTS.lean`, `WeakFacts.lean`):

```lean
abbrev LTS (S : Type u) (L : Type v) := S → Option L → S → Prop     -- none = τ
def sb (T) (R : Rel S) : Rel S := fun p q =>
  (∀ l p', T p l p' → ∃ q', T q l q' ∧ R p' q') ∧ (∀ l q', T q l q' → ∃ p', T p l p' ∧ R p' q')
def bisim (T) : Rel S := gfp (sb T)                                   -- ~
inductive TauStar (T) : S → S → Prop                                 -- τ*
  | refl p | step : T p none p' → TauStar T p' p'' → TauStar T p p''
def WStep (T) : S → Option L → S → Prop                              -- p =l̂⇒ p'
  | p, none,   p' => TauStar T p p'
  | p, some a, p' => ∃ p₁ p₂, TauStar T p p₁ ∧ T p₁ (some a) p₂ ∧ TauStar T p₂ p'
def wsimL (T) (R) : Rel S := fun p q => ∀ l p', T p l p' → ∃ q', WStep T q l q' ∧ R p' q'
def wsimR (T) (R) : Rel S := fun p q => ∀ l q', T q l q' → ∃ p', WStep T p l p' ∧ R p' q'
def wb (T) (R) : Rel S := fun p q => wsimL T R p q ∧ wsimR T R p q   -- strong challenge, weak answer
def wbisim (T) : Rel S := gfp (wb T)                                  -- ≈
def StepHat (T) p l p' : Prop := T p l p' ∨ (l = none ∧ p' = p)       -- p -l̂→ p'
def WStepPlus (T) : S → Option L → S → Prop                          -- at least one l-step
  | p, none,   p' => ∃ p₁, T p none p₁ ∧ TauStar T p₁ p'              -- τ⁺
  | p, some a, p' => WStep T p (some a) p'
def ex (T) (R) : Rel S := fun p q =>
  (∀ l p', T p l p' → ∃ q', StepHat T q l q' ∧ R p' q') ∧
  (∀ l q', T q l q' → ∃ p', WStepPlus T p l p' ∧ R p' q')
def expands (T) : Rel S := gfp (ex T)        -- expands T p q  ≡  p ≳ q  ("p expands q")
def wbWeak (T) (R) : Rel S := fun p q =>     -- weak challenges
  (∀ l p', WStep T p l p' → ∃ q', WStep T q l q' ∧ R p' q') ∧
  (∀ l q', WStep T q l q' → ∃ p', WStep T p l p' ∧ R p' q')
def NoTau (T) : Prop := ∀ p p', ¬ T p none p'
```

`expands T p q` reads "`p` expands `q`", written `p ≳ q`: the left state is the slower one (`τ.a.0 ≳ a.0`). Moves of `p` are answered by `q` with at most one step; moves of `q` are answered by `p` with at least one step of the same label. These clauses match Definition 2.5 of Sakayori–Sangiorgi (2025), whose `P ≲ Q` is `expands T Q P` here. Arun-Kumar and Hennessy (1992) write their efficiency preorder with the opposite orientation of the symbols; reading `≳R≲` with the symbols reversed gives an unsound technique (`weak_upto_reversed_expansion_unsound`).

**Up-to functions** (`LTS.lean`, `Weak.lean`):

```lean
def unionBisim  (T) (R) := fun p q => R p q ∨ bisim T p q                               -- R ∪ ~
def unionWbisim (T) (R) := fun p q => R p q ∨ wbisim T p q                              -- R ∪ ≈
def strongUpTo  (T) (R) := fun p q => ∃ p₁ q₁, bisim T p p₁   ∧ R p₁ q₁ ∧ bisim T q₁ q    -- ~R~
def weakUpTo    (T) (R) := fun p q => ∃ p₁ q₁, wbisim T p p₁  ∧ R p₁ q₁ ∧ wbisim T q₁ q   -- ≈R≈
def expUpTo     (T) (R) := fun p q => ∃ p₁ q₁, expands T p p₁ ∧ R p₁ q₁ ∧ expands T q q₁ -- ≳R≲
def expWeakUpTo (T) (R) := fun p q => ∃ p₁ q₁, expands T p p₁ ∧ R p₁ q₁ ∧ wbisim T q₁ q  -- ≳R≈
def weakExpUpTo (T) (R) := fun p q => ∃ p₁ q₁, wbisim T p p₁  ∧ R p₁ q₁ ∧ expands T q q₁ -- ≈R≲
def revExpUpTo  (T) (R) := fun p q => ∃ p₁ q₁, expands T p₁ p ∧ R p₁ q₁ ∧ expands T q₁ q -- ≲R≳
inductive EqvClo (R : Rel S) : Rel S                                                    -- equivalence closure
  | base : R p q → EqvClo R p q | refl p : EqvClo R p p
  | symm : EqvClo R p q → EqvClo R q p | trans : EqvClo R p q → EqvClo R q r → EqvClo R p r
```

The two-sided closures (`~R~`, `≈R≈`, `≳R≲`, `≳R≈`, `≈R≲`) are relational compositions: they relate `p` and `q` only through a middle `R`-pair, so each maps `∅` to `∅`.

**Process syntax** (`Proc.lean`, `Context.lean`):

```lean
inductive Proc (L : Type v) | nil | pre : Option L → Proc L → Proc L | sum : Proc L → Proc L → Proc L
abbrev tau P := Proc.pre none P;   abbrev act a P := Proc.pre (some a) P     -- τ.P, a.P
inductive PStep : Proc L → Option L → Proc L → Prop
  | pre μ P : PStep (.pre μ P) μ P
  | sumL : PStep P μ P' → PStep (.sum P Q) μ P'
  | sumR : PStep Q μ Q' → PStep (.sum P Q) μ Q'
inductive Lbl | a | b
inductive SumClo (R : Rel (Proc L)) : Rel (Proc L)        -- +-context closure (no prefix contexts)
  | base : R P Q → SumClo R P Q
  | refl P : SumClo R P P
  | sum : SumClo R P₁ Q₁ → SumClo R P₂ Q₂ → SumClo R (.sum P₁ P₂) (.sum Q₁ Q₂)
inductive CtxClo (R) : Rel (Proc L)        -- all contexts: base | refl | pre μ | sum
inductive SumCloNoRefl (R) : Rel (Proc L)  -- base | sum (no closed terms)
```

**Companion** (`Companion.lean`):

```lean
def companion (b : Rel S → Rel S) : Rel S → Rel S :=
  fun R p q => ∃ f : Rel S → Rel S, MonoRel f ∧ Commutes b f ∧ f R p q
```

**Named witness relations** used by the cards (all on `Proc Lbl`; `0` is `.nil`, `a.P` is `act .a P`, `τ.P` is `tau P`):

| Name | Pairs |
| :--- | :--- |
| `relU` | `{(a.(0+0), a.0)}` |
| `relS` | `{(a.(0+0), a.0), (0, 0)}` |
| `relE` | `{(a.0, a.(0+0)), (0+0, 0)}` |
| `relC` | `{(a.((0+0)+b.0), a.(0+b.0)), (0+0, 0)}` |
| `relExp` | `{(a.τ.0, a.0), (0, 0)}` |
| `asymStrictRel` | `{(τ.b.τ.0, b.0), (b.τ.0, b.τ.0), (τ.0, τ.0), (0, 0)}` |
| `pitfallRel` | `{(τ.a.0, 0)}` |
| `mirrorRel` | `{(0, τ.a.0)}` |
| `singletonExpRel` | `{(a.τ.0, a.0)}` |
| `ctxRel` | `{(a.(τ.a.0 + b.0), a.(a.0 + b.0)), (τ.a.0, a.0)}` |
| `ctxRel1 a` (any `L`, `a : L`) | `{(a.(τ.0 + a.0), a.(0 + a.0)), (τ.0, 0)}` |

The synthetic functionals and up-to functions used by tightness counterexamples live on relations over `Unit` (one state) or `Bool` (two states), in `BasicExamples.lean`: `negB R = {((),()) | ¬ R () ()}` (antitone), `negF` (pointwise complement), `botFun = const ∅`, `topFunU = const ⊤`, `relX = {(false,false)}`, `relY = {(true,true)}`, `killB R = R` unless `R` contains both `(false,false)` and `(true,true)` (then `∅`), `shiftB R = {(p, false) | R false true}` (monotone), `pickF` (maps exactly `{(false,false)}` to `{(false,true)}`, everything else to `∅`), `fillE` (adds `(false,false)` to the empty relation only), `swapB W = {(false,false) | (true,true) ∈ W ∧ (false,false) ∈ W} ∪ {(true,true) | (true,true) ∈ W ∧ (false,false) ∉ W}` (non-monotone; `gfp swapB = {(true,true)}`).

**Definition adequacy.** Every core definition has proved positive and negative examples (for instance `bisim_example_pos`: `0+0 ~ 0`; `bisim_example_neg`: `a.0 ≁ τ.a.0`; `wbisim_example_pos`: `τ.a.0 ≈ a.0`; `wbisim_example_neg`: `τ.a.0 ≉ 0`; `expands_example_pos`: `τ.a.0 ≳ a.0`; `expands_example_neg`: `a.0 ⋧ τ.a.0`; `sumClo_example_neg`: prefix contexts are excluded from `SumClo`; `companion_example_pos`: the companion contains the identity; `companion_example_neg`: `companion sb ∅` does not relate `a.0` and `0`). The Boolean module `Checks` re-implements the weak functionals for finite terms and re-checks several counterexamples by `decide`; it has no proved link to the `Prop`-level definitions and is a sanity check only.

### Result cards

Design question shared by all cards (each card says which part it informs): *Which up-to techniques can a refinement or equivalence proof (including a simulation-based compiler-correctness proof) rely on: (a) what general condition makes a technique sound, (b) which common techniques satisfy it, and (c) what is the smallest counterexample for each unsound one?*

Hypothesis ledgers use the convention: **tight** means there is a proved counterexample theorem in which all the other hypotheses hold and the conclusion fails; the ledger names that theorem and the class its witness lies in. Prior-art keys refer to the source list under **Evidence**.

#### 1. `compatible-implies-sound` — T0, depth: shallow

```lean
-- lean/ToyUpTo/Basic.lean:166-167
theorem sound_of_compatible_of_monotone_functional {b f : Rel S → Rel S}
    (hb : MonoRel b) (hf : MonoRel f) (hc : Commutes b f) : Sound b f
-- unfolded (prose): (∀ R R', R ⊑ R' → b R ⊑ b R') → (∀ R R', R ⊑ R' → f R ⊑ f R') →
--           (∀ R, f (b R) ⊑ b (f R)) → ∀ R, R ⊑ b (f R) → R ⊑ gfp b
```

Plain claim: for a monotone functional `b` on relations, an up-to function `f` that is monotone and satisfies `f (b R) ⊑ b (f R)` for every `R` is sound: every `R` with `R ⊑ b (f R)` is contained in `gfp b`.

| Hypothesis | Role | Tightness | Counterexample | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `hb : MonoRel b` | pushes each iterate `fⁿ R` under `b` | tight | `sound_counterexample_nonmonotone_functional` | antitone `negB` on relations over the 1-element type `Unit`, `f = const ∅` |
| `hf : MonoRel f` | iterates the commutation | tight | `sound_counterexample_nonmonotone_upto` | monotone `shiftB` with non-monotone `pickF`, relations over the 2-element type `Bool` |
| `hc : Commutes b f` | the semi-commutation `f ∘ b ⊑ b ∘ f` | tight | `sound_counterexample_noncommuting` | `sb` of the finite process LTS over `Lbl`, `f = const ⊤` (proof uses `R = {(a.0, a.a.0)}`) |

Each counterexample states that the other two hypotheses hold and `¬ Sound b f`. Non-vacuity: `sound_of_compatible_nonvacuity` — `b = sb PStep` (over `Lbl`), `f = constGfp (sb PStep)` ("constantly `~`"); all three hypotheses hold, and `relU = {(a.(0+0), a.0)}` is not a strong bisimulation but progresses to `f relU`. The proof iterates `f`: the union `⋃ₙ fⁿ R` is a post-fixpoint of `b`. Prior art: [Pous07], [Pous16], [Sangiorgi98], [PS11]. Informs (a).

Basis: execution (Lean kernel check).

#### 2. `compatible-closed-under-composition` — T0, depth: definitional

```lean
-- lean/ToyUpTo/Basic.lean:180-182
theorem compatible_comp {b f g : Rel S → Rel S}
    (hf : MonoRel f) (hg : MonoRel g) (hcf : Commutes b f) (hcg : Commutes b g) :
    Compatible b (comp f g)
-- unfolded conclusion (prose): (∀ R R', R ⊑ R' → f (g R) ⊑ f (g R')) ∧ ∀ R, f (g (b R)) ⊑ b (f (g R))
```

Plain claim: if `f` and `g` are monotone and each commutes with `b`, then `f ∘ g` is compatible with `b`; monotonicity of `b` is not a hypothesis.

| Hypothesis | Role | Tightness | Counterexample | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `hf : MonoRel f` | monotonicity of `f ∘ g`; pushes `g`'s commutation under `f` | tight (two halves) | `comp_counterexample_nonmonotone_left` (refutes the monotonicity half, `b = id`); `comp_counterexample_nonmonotone_left_commutation` (refutes the commutation half while `f ∘ g` is monotone) | relations over `Unit` (`b = id`, `f = negF`, `g = id`); relations over `Bool` (`b = const relY`, `f = fillE`, `g = const ∅`) |
| `hg : MonoRel g` | monotonicity of `f ∘ g` | tight | `comp_counterexample_nonmonotone_right` | relations over `Unit` (`b = id`, `f = id`, `g = negF`) |
| `hcf : Commutes b f` | commutation of the outer function | tight | `comp_counterexample_noncommuting_left` | relations over `Unit` (`b = const ∅`, `f = const ⊤`, `g = id`) |
| `hcg : Commutes b g` | commutation of the inner function | tight | `comp_counterexample_noncommuting_right` | relations over `Unit` (`b = const ∅`, `f = id`, `g = const ⊤`) |

Non-vacuity: `compatible_comp_nonvacuity` — `b = sb PStep`, `f = symClo`, `g = reflClo`; all four hypotheses hold, and `symClo (reflClo relU)` differs from both `symClo relU` (it contains `(0, 0)`) and `reflClo relU` (it contains `(a.0, a.(0+0))`). Prior art: [Pous07]; `compat_comp` (`theories/companion.v` L29 of [coinduction], the Coq development accompanying [Pous16]). Informs (a).

Basis: execution (Lean kernel check).

#### 3. `compatible-closed-under-union` — T0, depth: definitional

```lean
-- lean/ToyUpTo/Basic.lean:187-190
theorem compatible_iSup_of_monotone_functional {ι : Type v} {b : Rel S → Rel S}
    {F : ι → Rel S → Rel S}
    (hb : MonoRel b) (hF : ∀ i, MonoRel (F i)) (hcF : ∀ i, Commutes b (F i)) :
    Compatible b (iSup F)
-- iSup F R p q  ≡  ∃ i, F i R p q
```

Plain claim: for a monotone functional `b`, the pointwise union of any family (possibly empty, indexed by any type `ι`) of monotone functions that each commute with `b` is compatible with `b`.

| Hypothesis | Role | Tightness | Counterexample | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `hb : MonoRel b` | moves each member's `b`-image into `b` of the union | tight | `iSup_counterexample_nonmonotone_functional` | non-monotone `killB` on relations over `Bool`, family `{const relX, const relY}` indexed by `Bool` |
| `hF : ∀ i, MonoRel (F i)` | monotonicity of the union | tight | `iSup_counterexample_nonmonotone_member` | relations over `Unit`, `b = id`, family `{negF}` indexed by `Unit` (refutes the monotonicity half) |
| `hcF : ∀ i, Commutes b (F i)` | commutation of each member | tight | `iSup_counterexample_noncommuting_member` | relations over `Unit`, `b = const ∅`, family `{const ⊤}` indexed by `Unit` |

Non-vacuity: `compatible_iSup_nonvacuity` — `b = sb PStep`, the family `idOrBisim = {id, const ~}` indexed by `Bool` (whose union is `R ↦ R ∪ ~`); all three hypotheses hold. (For the empty index type the hypotheses `hF`, `hcF` hold vacuously and the union is `const ∅`.) Prior art: [Pous07]; `compat_sup` (`theories/companion.v` L43–48 of [coinduction], the Coq development accompanying [Pous16]). Informs (a).

Basis: execution (Lean kernel check).

#### 4. `compatible-closed-under-iteration` — T0, depth: shallow

```lean
-- lean/ToyUpTo/Basic.lean:196-198
theorem compatible_omega_of_monotone_functional {b f : Rel S → Rel S}
    (hb : MonoRel b) (hf : MonoRel f) (hc : Commutes b f) :
    Compatible b (omega f)
-- omega f R p q  ≡  ∃ n, iter f n R p q   (iter f 0 R = R)
```

Plain claim: for a monotone functional `b` and a monotone `f` with `f ∘ b ⊑ b ∘ f`, the ω-iteration `f^ω R = ⋃ₙ fⁿ R` (including `f⁰ R = R`) is compatible with `b`.

| Hypothesis | Role | Tightness | Counterexample | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `hb : MonoRel b` | moves each iterate's `b`-image into `b` of the union | tight | `omega_counterexample_nonmonotone_functional` | non-monotone `killB` on relations over `Bool`, `f = const relX` |
| `hf : MonoRel f` | iterates the commutation; monotonicity of `f^ω` | tight | `omega_counterexample_nonmonotone_upto` | relations over `Bool`, `b = id`, `f = fillE` (refutes the monotonicity half) |
| `hc : Commutes b f` | commutation of `f` | tight | `omega_counterexample_noncommuting` | relations over `Unit`, `b = const ∅`, `f = const ⊤` |

Non-vacuity: `compatible_omega_nonvacuity` — `b = sb PStep`, `f = stepSq` (`R ↦ R ∪ R;R`); all three hypotheses hold. The same theorem records that the iterates grow strictly on the chain `0 → 1 → 2 → 3` over the state type `Fin 4` (the pair `(0, 3)` first appears at the second iterate); `stepSq_strict_on_proc` shows the same on the process language itself (chain `0 → τ.0 → τ.τ.0 → τ.τ.τ.0`). Prior art: [Pous07], [Sangiorgi98]. Informs (a).

Basis: execution (Lean kernel check).

#### 5. `strong-upto-union-with-bisimilarity` — T0, depth: definitional

```lean
-- lean/ToyUpTo/Basic.lean:205-206
theorem compatible_union_gfp_of_monotone_functional {b : Rel S → Rel S} (hb : MonoRel b) :
    Compatible b (unionGfp b)
-- unionGfp b R = R ∪ gfp b
-- lean/ToyUpTo/Basic.lean:215-216
theorem sound_union_gfp_of_monotone_functional {b : Rel S → Rel S} (hb : MonoRel b) :
    Sound b (unionGfp b)
-- lean/ToyUpTo/Strong.lean:34-35
theorem strong_upto_union_bisim_compatible (T : LTS S L) :
    Compatible (sb T) (unionBisim T)
-- R ∪ ~
-- lean/ToyUpTo/Strong.lean:85
theorem strong_upto_union_bisim_sound (T : LTS S L) : Sound (sb T) (unionBisim T)
-- lean/ToyUpTo/Weak.lean:179-180
theorem weak_upto_union_wbisim_compatible (T : LTS S L) :
    Compatible (wb T) (unionWbisim T)
-- R ∪ ≈
-- lean/ToyUpTo/Weak.lean:184
theorem weak_upto_union_wbisim_sound (T : LTS S L) : Sound (wb T) (unionWbisim T)
```

Plain claim: for every monotone functional `b`, up to union with the greatest fixpoint (`R ↦ R ∪ gfp b`) is compatible with `b`, hence sound. Instances, for every LTS: strong bisimulation up to union with strong bisimilarity (`R ↦ R ∪ ~`) for `sb`, and weak bisimulation up to union with weak bisimilarity (`R ↦ R ∪ ≈`) for `wb`.

| Hypothesis | Role | Tightness | Counterexample | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `hb : MonoRel b` (general theorems only) | makes `gfp b` a post-fixpoint, so `gfp b ⊑ b (R ∪ gfp b)` | tight | `union_gfp_counterexample_nonmonotone_functional` (neither compatible nor sound) | non-monotone `swapB` on relations over `Bool`; no LTS functional is a counterexample, since `sb T`, `wb T` are always monotone (`sb_mono`, `wb_mono`) |

The four LTS instances have no hypotheses: they are unconditional over every `T : LTS S L`. Non-vacuity: `strong_upto_union_bisim_useful` — `relU` is not a strong bisimulation but progresses to `relU ∪ ~` under `sb PStep`; for the weak instance, `weak_upto_union_wbisim_useful_singleton` — `singletonExpRel = {(a.τ.0, a.0)}` is not a weak bisimulation but progresses to `R ∪ ≈` under `wb PStep`. This card is an instance of result 3 for the family `{id, const (gfp b)}`. Prior art: [Milner89], [Pous07], [Sangiorgi98]. Informs (b).

Basis: execution (Lean kernel check).

#### 6. `strong-upto-bisimilarity-both-sides` — T0, depth: shallow

```lean
-- lean/ToyUpTo/Strong.lean:40-41
theorem strong_upto_bisim_both_sides_compatible (T : LTS S L) :
    Compatible (sb T) (strongUpTo T)
-- lean/ToyUpTo/Strong.lean:90
theorem strong_upto_bisim_both_sides_sound (T : LTS S L) : Sound (sb T) (strongUpTo T)
-- strongUpTo T R p q  ≡  ∃ p₁ q₁, p ~ p₁ ∧ R p₁ q₁ ∧ q₁ ~ q
```

Plain claim: for every labelled transition system, strong bisimulation up to strong bisimilarity on both sides (`R ↦ ~R~`) is compatible with `sb`, hence sound. Hypotheses: none (unconditional over every LTS `T : LTS S L`). Non-vacuity: `strong_upto_bisim_both_sides_useful` — `relS = {(a.(0+0), a.0), (0, 0)}` is not a strong bisimulation but progresses to `~relS~` under `sb PStep`. Prior art: [Milner89], [Pous07], [Sangiorgi98]. Informs (b).

Basis: execution (Lean kernel check).

#### 7. `strong-upto-equivalence-closure` — T0, depth: shallow

```lean
-- lean/ToyUpTo/Strong.lean:58-59
theorem strong_upto_equivalence_closure_compatible (T : LTS S L) :
    Compatible (sb T) (EqvClo (S := S))
-- lean/ToyUpTo/Strong.lean:95-96
theorem strong_upto_equivalence_closure_sound (T : LTS S L) :
    Sound (sb T) (EqvClo (S := S))
```

Plain claim: for every labelled transition system, strong bisimulation up to equivalence closure (reflexive, symmetric, transitive closure) is compatible with `sb`, hence sound. Hypotheses: none (unconditional over every LTS `T : LTS S L`). Non-vacuity: `strong_upto_equivalence_closure_useful` — `relE = {(a.0, a.(0+0)), (0+0, 0)}` is not a strong bisimulation but progresses to `EqvClo relE` under `sb PStep`. Related weak-case facts proved here: `reflClo` and `symClo` are each compatible with `wb T` for every `T` (`reflClo_compatible_wb`, `symClo_compatible_wb`); nothing about the transitive closure and `wb` is proved. Prior art: [Pous07], [DHS19], [PS11], [coinduction-examples]. Informs (b).

Basis: execution (Lean kernel check).

#### 8. `weak-upto-weak-bisimilarity-unsound` — T0, counterexample, depth: shallow

```lean
-- lean/ToyUpTo/Weak.lean:385-386
theorem weak_upto_weak_bisim_unsound :
    pitfallRel ⊑ wb PStep (weakUpTo PStep pitfallRel) ∧ ¬ pitfallRel ⊑ wbisim PStep
-- lean/ToyUpTo/Weak.lean:394
theorem weak_upto_weak_bisim_not_sound : ¬ Sound (wb (@PStep Lbl)) (weakUpTo PStep)
-- pitfallRel = {(τ.a.0, 0)} on Proc Lbl;  weakUpTo T R p q ≡ ∃ p₁ q₁, p ≈ p₁ ∧ R p₁ q₁ ∧ q₁ ≈ q
```

Plain claim: over the finite process LTS with two visible labels (`PStep` on `Proc Lbl`), weak bisimulation up to weak bisimilarity (`R ↦ ≈R≈`) is not sound for the strong-challenge/weak-response functional `wb`: the one-pair relation `R = {(τ.a.0, 0)}` satisfies `R ⊑ wb (≈R≈)` (the τ-move of `τ.a.0` is answered by `0` standing still, and `a.0 ≈ τ.a.0 R 0 ≈ 0`), yet `τ.a.0 ≉ 0`. Consequently `≈R≈` is not a sound technique for `wb` over labelled transition systems in general. Hypotheses: none (closed statement over the process LTS on `Proc Lbl`); the witness relation is exposed in the statement.

Exact failure scope and sound variants. The failure is for the symmetric functional `wb` with single-step challenges, witnessed by the relation `{(τ.a.0, 0)}` above. Each of the following is proved, with exactly the stated hypotheses, and has a non-vacuity witness:

| Variant | Hypotheses | Theorem(s) | Non-vacuity witness |
| :--- | :--- | :--- | :--- |
| `≈R≈` with weak challenges: compatible with and sound for `wbWeak T`; `gfp (wbWeak T) = ≈` | none (every LTS `T`) | `weak_challenge_upto_weak_bisim_compatible`, `weak_challenge_upto_weak_bisim_sound`, `gfp_wbWeak_eq_wbisim` | `weak_challenge_upto_weak_bisim_useful` (`relExp` is not a `wbWeak`-post-fixpoint but progresses to `≈relExp≈`) |
| `≈R≈` sound for `wb T` | `NoTau T` (no silent transitions) | `weak_upto_weak_bisim_sound_of_noTau` | `noTau_nonvacuity` (a 3-state system with one label and no τ-steps, where `≈` is neither the identity nor total) |
| every up-to function sound for `wb T` | `L → False` (no visible labels) | `sound_wb_of_no_visible` | `no_visible_nonvacuity` (a 2-state system over the empty label type with a live τ-loop) |
| `~R~` compatible with and sound for `wb T` | none (every LTS `T`) | result 9 | `weak_upto_strong_bisim_useful` |
| `≳R≲` sound for `wb T`; asymmetric `≳R≈` (left moves) / `≈R≲` (right moves) sound | none beyond the two clauses for the asymmetric form (every LTS `T`) | results 11 and 10 | `weak_upto_expansion_useful`; `weak_upto_expansion_asymmetric_nonvacuity` |
| `R ∪ ≈` compatible with and sound for `wb T` | none (every LTS `T`) | result 5 (weak instance) | `weak_upto_union_wbisim_useful_singleton` |

Positive controls at the level of the witness: the same relation progresses neither to `~R~` nor to `≳R≲` under `wb` (`pitfall_control_strong`, `pitfall_control_expansion`), and with weak challenges it does not progress to `≈R≈` (`pitfall_not_progress_wbWeak`). Reversing the expansion symbols (`≲R≳`) also admits the pitfall relation (`weak_upto_reversed_expansion_unsound`). Prior art: [SM92] (the problem and this one-pair counterexample), [Milner89], [DHS19], [PS11], [Pous05], [weak-up-to]. Informs (c).

Basis: execution (Lean kernel check).

#### 9. `weak-upto-strong-bisimilarity` — T0, depth: shallow

```lean
-- lean/ToyUpTo/Weak.lean:118-119
theorem weak_upto_strong_bisim_compatible (T : LTS S L) :
    Compatible (wb T) (strongUpTo T)
-- lean/ToyUpTo/Weak.lean:133
theorem weak_upto_strong_bisim_sound (T : LTS S L) : Sound (wb T) (strongUpTo T)
```

Plain claim: for every labelled transition system, weak bisimulation up to strong bisimilarity on both sides (`R ↦ ~R~`) is compatible with the weak functional `wb`, hence sound. Hypotheses: none (unconditional over every LTS `T : LTS S L`). Non-vacuity: `weak_upto_strong_bisim_useful` — `relS` is not a weak bisimulation but progresses to `~relS~` under `wb PStep`. Prior art: [SM92], [Pous07]. Informs (b).

Basis: execution (Lean kernel check).

#### 10. `weak-upto-expansion-asymmetric` — T0, depth: substantive

```lean
-- lean/ToyUpTo/Weak.lean:141-143
theorem weak_upto_expansion_asymmetric_sound (T : LTS S L) (R : Rel S)
    (hL : R ⊑ wsimL T (expWeakUpTo T R)) (hR : R ⊑ wsimR T (weakExpUpTo T R)) :
    R ⊑ wbisim T
-- hL: if R p q and p -l→ p', then q =l̂⇒ q' with p' ≳ p₁, R p₁ q₁, q₁ ≈ q'   (≳R≈)
-- hR: if R p q and q -l→ q', then p =l̂⇒ p' with p' ≈ p₁, R p₁ q₁, q' ≳ q₁   (≈R≲)
```

Plain claim: for every labelled transition system `T` and relation `R`, if every move of the left state of an `R`-pair is answered (by a weak move of the right state) into `≳R≈`, and every move of the right state is answered into `≈R≲`, then `R ⊑ ≈`; in both clauses the expansion sits on the challenger's derivative.

| Hypothesis | Role | Tightness | Counterexample | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `hL` | left-challenge clause, expansion on the challenger's (left) derivative | tight | `asym_counterexample_left_weakened` (satisfies `hR` and the weaker `R ⊑ wsimL T (≈R≈)`; `R ⊄ ≈`) | the one-pair relation `{(τ.a.0, 0)}` on the finite process LTS over `Lbl` (3 reachable states) |
| `hR` | right-challenge clause, expansion on the challenger's (right) derivative | tight | `asym_counterexample_right_weakened` (satisfies `hL` and the weaker `R ⊑ wsimR T (≈R≈)`; `R ⊄ ≈`) | the one-pair relation `{(0, τ.a.0)}` on the finite process LTS over `Lbl` (3 reachable states) |

Each counterexample satisfies the other hypothesis as stated, and the named one with expansion weakened to weak bisimilarity, so it also witnesses that the named hypothesis cannot be dropped (within the class "one-pair relation on the process LTS over `Lbl`"). Whether some intermediate weakening is sound is not examined. Non-vacuity: `weak_upto_expansion_asymmetric_nonvacuity` (`relExp` satisfies both clauses and is not a weak bisimulation) and `weak_upto_expansion_asymmetric_strict_nonvacuity` (`asymStrictRel` satisfies both clauses but does not progress under the symmetric `≳R≲`). The proof shows that `≈R≈` is a post-fixpoint of `wb`, using lifting lemmas (`asym_wstepL`, `asym_wstepR`) that carry the invariants `X ≳ X₁ R Y₁ ≈ Y` (left moves) and `X ≈ X₁ R Y₁ ≲ Y` (right moves) along weak transitions by induction on silent sequences, together with transitivity of `≈`; this is the main proof effort of the package (hence "substantive"). Prior art: [PS11] Section 6.5.2.4 (as cited by the mechanization), [nad/up-to] theorem `6-5-2-4` with the same two hypotheses, [Danielsson18]; a special case of [Pous05] Theorem 2.5 as mechanized in [weak-up-to]; expansion clauses as in [SS25], orientation contrasted with [AKH92]. Informs (b).

Basis: execution (Lean kernel check).

#### 11. `weak-upto-expansion` — T0, depth: shallow

```lean
-- lean/ToyUpTo/Weak.lean:163
theorem weak_upto_expansion_sound (T : LTS S L) : Sound (wb T) (expUpTo T)
-- expUpTo T R p q  ≡  ∃ p₁ q₁, p ≳ p₁ ∧ R p₁ q₁ ∧ q ≳ q₁
```

Plain claim: for every labelled transition system, weak bisimulation up to expansion (`R ↦ ≳R≲`: `p ≳ p₁`, `p₁ R q₁`, `q ≳ q₁`) is sound for `wb`. Hypotheses: none (unconditional over every LTS `T : LTS S L`). It follows from result 10 in a few lines, because `≳ ⊑ ≈` and `≈` is symmetric. Non-vacuity: `weak_upto_expansion_useful` — `relExp` is not a weak bisimulation but progresses to `≳relExp≲` under `wb PStep`. Prior art: [SM92], [PS11], [nad/up-to] (`Up-to-expansion`, proved size-preserving), [Danielsson18], [AKH92], [SS25]. Informs (b).

Basis: execution (Lean kernel check).

#### 12. `weak-upto-expansion-not-compatible` — T1, counterexample, depth: shallow

```lean
-- lean/ToyUpTo/Weak.lean:530-534
theorem weak_upto_expansion_commutes_counterexample {L : Type v} :
    expUpTo (@PStep L) (wb PStep botRel) (tau .nil) .nil ∧
    ¬ wb (@PStep L) (expUpTo PStep botRel) (tau .nil) .nil ∧
    (wb (@PStep L) (expUpTo PStep botRel) ⊑ wb PStep botRel) ∧
    (wb (@PStep L) botRel ⊑ wb PStep (expUpTo PStep botRel))
-- lean/ToyUpTo/Weak.lean:546-549
theorem weak_upto_expansion_not_compatible {L : Type v} :
    MonoRel (expUpTo (@PStep L)) ∧
    ¬ Commutes (wb (@PStep L)) (expUpTo PStep) ∧
    ¬ Compatible (wb (@PStep L)) (expUpTo PStep)
```

Plain claim: over the toy process language with any label type (even with no visible labels), the up-to-expansion function `R ↦ ≳R≲` is monotone but does not commute with `wb`, hence is not compatible with `wb`: for `R = ∅`, `(τ.0, 0)` is in `≳ (wb ∅) ≲` but not in `wb (≳ ∅ ≲)`, and `wb (≳ ∅ ≲) = wb ∅`. Hypotheses: none (unconditional over `@PStep L` for an arbitrary label type `L`); the witness `R = ∅` and the pair `(τ.0, 0)` are exposed in the statement. Positive control: on every LTS without silent steps (`NoTau T`), `≳R≲` commutes with `wb T` (`expUpTo_commutes_of_noTau`; non-vacuity `noTau_nonvacuity`). Together with results 1 and 11 this shows that, for the monotone functional `wb`, compatibility is sufficient but not necessary for soundness. Tier T1: no published statement or mechanization of this non-commutation was located ([nad/up-to] proves up to expansion size-preserving, not compatible, and contains no (non-)compatibility statement for it; [weak-up-to] uses a different decomposition of the weak functional); the full text of [PS11] was not inspected. Prior art: [Pous07], [PS11], [nad/up-to], [Danielsson18]. Informs (c).

Basis: execution (Lean kernel check).

#### 13. `weak-upto-expansion-left-weak-right-symmetric-unsound` — T0, counterexample, depth: shallow

```lean
-- lean/ToyUpTo/Weak.lean:446-447
theorem weak_upto_expansion_left_weak_right_unsound :
    mirrorRel ⊑ wb PStep (expWeakUpTo PStep mirrorRel) ∧ ¬ mirrorRel ⊑ wbisim PStep
-- lean/ToyUpTo/Weak.lean:455-456
theorem weak_upto_expansion_left_weak_right_not_sound :
    ¬ Sound (wb (@PStep Lbl)) (expWeakUpTo PStep)
-- mirrorRel = {(0, τ.a.0)};  expWeakUpTo T R p q ≡ ∃ p₁ q₁, p ≳ p₁ ∧ R p₁ q₁ ∧ q₁ ≈ q
```

Plain claim: over the finite process LTS with two visible labels (`PStep` on `Proc Lbl`), using expansion on the left and weak bisimilarity on the right (`R ↦ ≳R≈`) for both clauses of the symmetric functional `wb` is not sound: the one-pair relation `R = {(0, τ.a.0)}` satisfies `R ⊑ wb (≳R≈)` (the right τ-move is answered by `0` standing still, and `0 ≳ 0 R τ.a.0 ≈ a.0`), yet `0 ≉ τ.a.0`. Consequently `≳R≈` in both clauses is not a sound technique for `wb` over labelled transition systems in general. Hypotheses: none (closed statement over the process LTS on `Proc Lbl`).

Exact failure scope and sound variants: the failure is for `wb` with `≳R≈` also used for moves of the right state. With exactly the stated hypotheses: for every LTS `T` and relation `R`, `R ⊑ wsimL T (≳R≈)` implies `R ⊑ gfp (wsimL T)` (one-sided weak simulation; `weak_upto_expansion_left_weak_right_sound_for_wsimL`, non-vacuity `one_sided_wsimL_nonvacuity`, in which `mirrorRel` itself satisfies the hypothesis); and the asymmetric form of result 10 (≈R≲ for right moves) is sound for every LTS. Witness-level positive controls: `mirrorRel` does not progress to `≳R≲` under `wb` (`mirror_control_expansion`) and violates the right-hand hypothesis of result 10 (`mirror_control_asymmetric`). `mirrorRel` is the converse of the pitfall relation of result 8. Prior art: [SM92], [PS11] Section 6.5.2.4, [nad/up-to] `6-5-2-4`, [Danielsson18]. Informs (c).

Basis: execution (Lean kernel check).

#### 14. `weak-bisimilarity-not-sum-congruence` — T0, counterexample (reference point), depth: shallow

```lean
-- lean/ToyUpTo/Context.lean:66-68
theorem wbisim_not_sum_congruence :
    wbisim (@PStep Lbl) (tau (act .a .nil)) (act .a .nil) ∧
    ¬ wbisim (@PStep Lbl) (.sum (tau (act .a .nil)) (act .b .nil)) (.sum (act .a .nil) (act .b .nil))
-- lean/ToyUpTo/Context.lean:197-199
theorem wbisim_not_sum_congruence_one_label (a : L) :
    wbisim (@PStep L) (tau .nil) .nil ∧
    ¬ wbisim (@PStep L) (.sum (tau .nil) (act a .nil)) (.sum .nil (act a .nil))
```

Plain claim (reference point): over the finite process LTS with two visible labels (`PStep` on `Proc Lbl`), weak bisimilarity is not preserved by binary choice: `τ.a.0 ≈ a.0`, but `τ.a.0 + b.0 ≉ a.0 + b.0`; one visible label suffices: over any label type with an element `a`, `τ.0 ≈ 0` but `τ.0 + a.0 ≉ 0 + a.0`.

| Hypothesis | Role | Tightness | Counterexample | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `a : L` (one-label version only) | the visible action that distinguishes `τ.0 + a.0` from `0 + a.0` | tight | `wbisim_sum_congruence_no_visible` (over the empty label type, `P ≈ P'` implies `P + Q ≈ P' + Q` for all `P, P', Q`) | the process LTS over the empty label type `Proc Empty`, where `≈` is total |

Positive controls: prefix-guarded choice preserves weak bisimilarity, `P ≈ P' → μ.P + Q ≈ μ.P' + Q`, for every label type and every prefix `μ` including τ (`wbisim_guarded_sum_congruence`; non-vacuity `guarded_sum_congruence_nonvacuity` with `τ.τ.0 + a.0 ≈ τ.0 + a.0`); over the empty label type `+` preserves `≈` (`wbisim_sum_congruence_no_visible`). This card is a fact about `≈`, not about an up-to technique; it explains result 15. Prior art: [Milner89], [nad/up-to] `¬⊕-congˡ` and `⊕·-cong`, [Danielsson18], [AKH92]. Informs (c) as a reference point.

Basis: execution (Lean kernel check).

#### 15. `weak-upto-sum-context-unsound` — T1, counterexample, depth: shallow

```lean
-- lean/ToyUpTo/Context.lean:95-96
theorem weak_upto_sum_context_unsound :
    ctxRel ⊑ wb PStep (SumClo ctxRel) ∧ ¬ ctxRel ⊑ wbisim PStep
-- lean/ToyUpTo/Context.lean:114
theorem weak_upto_sum_context_not_sound : ¬ Sound (wb (@PStep Lbl)) SumClo
-- lean/ToyUpTo/Context.lean:210-211
theorem weak_upto_sum_context_unsound_one_label (a : L) :
    ctxRel1 a ⊑ wb PStep (SumClo (ctxRel1 a)) ∧ ¬ ctxRel1 a ⊑ wbisim PStep
-- lean/ToyUpTo/Context.lean:234-235
theorem weak_upto_sum_context_sound_iff_no_visible :
    Sound (wb (@PStep L)) SumClo ↔ (L → False)
```

Plain claim: over the finite process LTS with two visible labels (`PStep` on `Proc Lbl`), weak bisimulation up to `+`-contexts (`SumClo`) is not sound for `wb`: `R = {(a.(τ.a.0 + b.0), a.(a.0 + b.0)), (τ.a.0, a.0)}` satisfies `R ⊑ wb (SumClo R)`, because `(τ.a.0 + b.0, a.0 + b.0)` arises from `(τ.a.0, a.0)` by the context `[·] + b.0`, yet `a.(τ.a.0 + b.0) ≉ a.(a.0 + b.0)`. More generally, over the process language with label type `L`, the technique is sound if and only if `L` is empty: with a single label `a`, `{(a.(τ.0 + a.0), a.(0 + a.0)), (τ.0, 0)}` is a counterexample.

| Hypothesis | Role | Tightness | Counterexample | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `a : L` (one-label version only) | the visible action observed after the silent step | tight | `weak_upto_sum_context_sound_no_visible` (`Sound (wb (@PStep Empty)) SumClo`) | the process LTS over the empty label type `Proc Empty` |

Positive controls: `ctxRel` does not progress to `SumClo ctxRel` under the strong functional (`sum_context_control_strong`), and strong bisimulation up to `+`-contexts is sound (result 16); over the empty label type the weak technique is sound. The prefix `a.[·]` in the witness matters: the one-pair relation `{(τ.a.0 + b.0, a.0 + b.0)}` does not progress to its `+`-context closure under `wb` (`one_pair_sum_not_progresses_sumClo`). Tier T1: that weak up to context must be restricted is reflected in published developments ([nad/up-to] proves soundness only for non-degenerate contexts, and non-compatibility of that technique (not proved here), after a counterexample of Pous and Sangiorgi), but no published statement or mechanization of unsoundness for unguarded `+`-contexts was located; the full text of [PS11] was not inspected. Prior art: [PS11], [nad/up-to], [Danielsson18], [Pous07]. Informs (c).

Basis: execution (Lean kernel check).

#### 16. `strong-upto-sum-context` — T0, depth: shallow

```lean
-- lean/ToyUpTo/Context.lean:24-25
theorem strong_upto_sum_context_compatible {L : Type v} :
    Compatible (sb (@PStep L)) SumClo
-- lean/ToyUpTo/Context.lean:47
theorem strong_upto_sum_context_sound {L : Type v} : Sound (sb (@PStep L)) SumClo
```

Plain claim: for the toy process language over any label type, strong bisimulation up to `+`-contexts (closure under the hole, closed terms and nested binary choice) is compatible with `sb`, hence sound. Hypotheses: none (unconditional over `@PStep L` for an arbitrary label type `L`). Non-vacuity: `strong_upto_sum_context_useful` — `relC = {(a.((0+0)+b.0), a.(0+b.0)), (0+0, 0)}` is not a strong bisimulation but progresses to `SumClo relC` under `sb PStep`. Related facts: adding prefix contexts breaks compatibility (`prefix_context_not_compatible_sb`); the closed-term constructor `SumClo.refl` is not needed for compatibility (`sumCloNoRefl_compatible_sb`) but supplies closed summands such as `[·] + b.0` (`sumCloNoRefl_misses_closed_context`). Prior art: [Sangiorgi98], [Milner89], [Pous07], [Pous16]. Informs (b).

Basis: execution (Lean kernel check).

#### 17. `companion-compatible-and-sound` — T0, depth: shallow

```lean
-- lean/ToyUpTo/Companion.lean:55-56
theorem companion_compatible_and_sound_of_monotone_functional {b : Rel S → Rel S}
    (hb : MonoRel b) : Compatible b (companion b) ∧ Sound b (companion b)
-- lean/ToyUpTo/Companion.lean:27-28
theorem companion_greatest {b f : Rel S → Rel S} (hf : MonoRel f) (hc : Commutes b f)
    (R : Rel S) : f R ⊑ companion b R
-- lean/ToyUpTo/Companion.lean:47-48
theorem companion_bot_eq_gfp {b : Rel S → Rel S} :
    companion b botRel ⊑ gfp b ∧ gfp b ⊑ companion b botRel
-- companion b R p q  ≡  ∃ f, MonoRel f ∧ Commutes b f ∧ f R p q
```

Plain claim: for a monotone functional `b`, the companion of `b` (pointwise union of all monotone functions commuting with `b`) is itself compatible with `b` and sound for `b`. For every `b`, monotone or not, every monotone function commuting with `b` is below the companion (`companion_greatest`), and `companion b ∅ = gfp b` (both inclusions).

| Hypothesis | Role | Tightness | Counterexample | Witness class |
| :--- | :--- | :--- | :--- | :--- |
| `hb : MonoRel b` (main theorem only; `companion_greatest` and `companion_bot_eq_gfp` hold for every `b`) | used for both conclusions of the main theorem | tight | `companion_counterexample_nonmonotone_functional` (companion neither compatible nor sound) | non-monotone `swapB` on relations over `Bool`; no LTS functional is a counterexample, since `sb T`, `wb T` are always monotone |

For the non-monotone `killB` the companion is sound but not compatible (`killB_companion_not_compatible_but_sound`). Non-vacuity: `companion_nonvacuity` — `b = sb PStep` is monotone, and `relU` is not a strong bisimulation but progresses to its companion image. The companion is defined by an impredicative union over all functions `Rel S → Rel S`. Prior art: [Pous16], [coinduction] (`theories/companion.v` L53–56: the companion `t` and `compat_t`), [nad/up-to], [Danielsson18]. Informs (a).

Basis: execution (Lean kernel check).

### Modeling bridge

```text
Basis: derived (modeling bridge)
```

Simulation-based refinement and compiler-correctness proofs often discharge a matching obligation "up to" some closure of the candidate relation: up to silent steps of the target, up to an equivalence on intermediate states, or up to a context. The following is reasoned from the theorems above; it is not proved about any real development, and the toy model's gaps (divergence insensitivity, homogeneous relations, a small syntax; see **Applicability**) apply.

- A closure that is compatible with the one-step functional the proof actually uses (the analogue of `sb` or `wb`) is safe if that functional is monotone (result 1), and compatible closures can be combined by composition, union and iteration (results 2–4). A closure that is merely known to be sound needs a fresh argument before it is combined with others: this package proves no closure property for sound functions, and their non-closure under composition is known from the literature but not proved here.
- If the one-step functional answers a single challenger step with a possibly empty sequence of silent responder steps (the shape of `wb`), then closing the derivative pair under the same weak equivalence on both sides can be unsound (result 8): the closure may silently undo the challenger's progress. Safe alternatives exercised here, each proved for every LTS: union with the weak equivalence instead of composition with it (result 5), closing under a strong step-for-step equivalence (result 9), an expansion-like preorder on the challenger's side (results 10, 11), or weak challenges (`wbWeak`, result 8's table).
- Closure under contexts should not be assumed safe without an argument that the contexts preserve the one-step game: unguarded choice contexts break the weak game in the toy language (results 14, 15), and even for the strong game prefix contexts break first-order compatibility there (`prefix_context_not_compatible_sb`, result 16), while `+`-contexts are compatible with the strong game (result 16).

Simulation diagrams for multi-pass compilers (forward and backward simulations with stuttering measures) are not formalized; connecting them to `sb` and `wb` would need its own modeling argument.

## Boundaries

### Non-claims (read these first)

Each result's non-claims, as recorded in `results.json`. A remark that a technique fails either names the theorem that proves the failure or carries the marker "(not proved here)".

**1. `compatible-implies-sound`**

- Compatibility is sufficient, not necessary, for soundness: weak bisimulation up to expansion is sound for wb on every transition system (weak_upto_expansion_sound) but not compatible with wb on the process LTS over any label type (weak_upto_expansion_not_compatible; card weak-upto-expansion-not-compatible).
- Sound up-to functions are not closed under composition in general, even for monotone and extensive functions (not proved here; known from the Agda development nad/up-to, ¬-∘-closure, and Pous and Sangiorgi (2011, Section 6.5.4) discuss an instance). This package proves closure only for compatible functions (cards compatible-closed-under-composition, -union, -iteration) and mechanizes no counterexample for sound ones.
- Does not cover functionals on lattices other than Prop-valued binary relations on one state type, nor non-monotone b.
- Compatibility here is Pous's first-order notion. Respectful functions (Sangiorgi 1998) and functions below the companion (second-order) are larger classes of sound functions; they are not formalized here.
- Homogeneous relations only: Rel S relates states of a single type S. Simulations between different source and target systems (S₁ → S₂ → Prop) are not modelled; closures such as the equivalence or symmetric closure, which relate states of one type, have no direct analogue there (not examined here).
- Toy model: Prop-valued binary relations on an arbitrary state type, an arbitrary labelled transition system with labels Option L (none = silent step), and, for concrete examples, a finite process syntax with only inaction, prefix and binary choice (no recursion, parallel composition, restriction or name passing). The result is a statement about this toy model; it neither establishes nor refutes the corresponding claims about up-to techniques used in real equivalence, refinement or compiler-correctness proofs.
- Any application to a real proof (for example a forward or backward simulation in a compiler-correctness development) is a separate modeling-bridge argument, not established by this theorem.

**2. `compatible-closed-under-composition`**

- Says nothing about composing merely sound functions.
- The conclusion is compatibility. Soundness of f ∘ g follows when b is also monotone (sound_of_compatible_of_monotone_functional; card compatible-implies-sound), and MonoRel b cannot be dropped from that theorem (sound_counterexample_nonmonotone_functional, an instance on relations over the 1-element state type Unit).
- Toy model: Prop-valued binary relations on an arbitrary state type, an arbitrary labelled transition system with labels Option L (none = silent step), and, for concrete examples, a finite process syntax with only inaction, prefix and binary choice (no recursion, parallel composition, restriction or name passing). The result is a statement about this toy model; it neither establishes nor refutes the corresponding claims about up-to techniques used in real equivalence, refinement or compiler-correctness proofs.

**3. `compatible-closed-under-union`**

- Pointwise union of up-to functions, not union of the relations they are applied to.
- Says nothing about unions of merely sound functions.
- Toy model: Prop-valued binary relations on an arbitrary state type, an arbitrary labelled transition system with labels Option L (none = silent step), and, for concrete examples, a finite process syntax with only inaction, prefix and binary choice (no recursion, parallel composition, restriction or name passing). The result is a statement about this toy model; it neither establishes nor refutes the corresponding claims about up-to techniques used in real equivalence, refinement or compiler-correctness proofs.

**4. `compatible-closed-under-iteration`**

- Only countable (ω) iteration starting from n = 0 is covered; transfinite iteration is not discussed.
- Toy model: Prop-valued binary relations on an arbitrary state type, an arbitrary labelled transition system with labels Option L (none = silent step), and, for concrete examples, a finite process syntax with only inaction, prefix and binary choice (no recursion, parallel composition, restriction or name passing). The result is a statement about this toy model; it neither establishes nor refutes the corresponding claims about up-to techniques used in real equivalence, refinement or compiler-correctness proofs.

**5. `strong-upto-union-with-bisimilarity`**

- Union, not composition: R ∪ ≈ is compatible with and sound for wb on every transition system (this card), but ≈R≈ is not sound for wb on the process LTS over two labels (weak_upto_weak_bisim_not_sound; card weak-upto-weak-bisimilarity-unsound). Neither fact may be inferred from the other.
- This card is a direct instance of card compatible-closed-under-union (the family {id, const (gfp b)}); it adds no new proof technique. The union only adds pairs that are already in gfp b.
- Toy model: Prop-valued binary relations on an arbitrary state type, an arbitrary labelled transition system with labels Option L (none = silent step), and, for concrete examples, a finite process syntax with only inaction, prefix and binary choice (no recursion, parallel composition, restriction or name passing). The result is a statement about this toy model; it neither establishes nor refutes the corresponding claims about up-to techniques used in real equivalence, refinement or compiler-correctness proofs.
- Any application to a real proof (for example a forward or backward simulation in a compiler-correctness development) is a separate modeling-bridge argument, not established by this theorem.

**6. `strong-upto-bisimilarity-both-sides`**

- ~R~ needs a middle R-pair; it does not contain ~ itself when R is empty (see strongUpTo_example_neg).
- Nothing is claimed here for ≈R≈ under the weak functional wb; that technique is not sound for wb on the process LTS over two labels (weak_upto_weak_bisim_not_sound; card weak-upto-weak-bisimilarity-unsound).
- Toy model: Prop-valued binary relations on an arbitrary state type, an arbitrary labelled transition system with labels Option L (none = silent step), and, for concrete examples, a finite process syntax with only inaction, prefix and binary choice (no recursion, parallel composition, restriction or name passing). The result is a statement about this toy model; it neither establishes nor refutes the corresponding claims about up-to techniques used in real equivalence, refinement or compiler-correctness proofs.
- Any application to a real proof (for example a forward or backward simulation in a compiler-correctness development) is a separate modeling-bridge argument, not established by this theorem.

**7. `strong-upto-equivalence-closure`**

- Transitive closure is not claimed compatible with, or sound for, the weak functional; up to transitivity is reported in the literature to be unsound in the weak case (not proved here; Durier-Hirschkoff-Sangiorgi 2019, citing Pous-Sangiorgi).
- For the weak functional wb, the reflexive closure (R ↦ R ∪ id) and the symmetric closure (R ↦ R ∪ R⁻¹) are each compatible with wb on every transition system (reflClo_compatible_wb, symClo_compatible_wb), hence sound. That the transitive part fails in the weak case is not proved here (see the first non-claim, and not_Transitive_wt in damien-pous/coinduction-examples).
- Homogeneous relations only: Rel S relates states of a single type S. Simulations between different source and target systems (S₁ → S₂ → Prop) are not modelled; closures such as the equivalence or symmetric closure, which relate states of one type, have no direct analogue there (not examined here).
- Toy model: Prop-valued binary relations on an arbitrary state type, an arbitrary labelled transition system with labels Option L (none = silent step), and, for concrete examples, a finite process syntax with only inaction, prefix and binary choice (no recursion, parallel composition, restriction or name passing). The result is a statement about this toy model; it neither establishes nor refutes the corresponding claims about up-to techniques used in real equivalence, refinement or compiler-correctness proofs.
- Any application to a real proof (for example a forward or backward simulation in a compiler-correctness development) is a separate modeling-bridge argument, not established by this theorem.

**8. `weak-upto-weak-bisimilarity-unsound`**

- Concerns wb with strong (single-step) challenges. With weak challenges (wbWeak: p =l̂⇒ p' answered by q =l̂⇒ q'), ≈R≈ is compatible and sound, and gfp (wbWeak T) = ≈ (weak_challenge_upto_weak_bisim_compatible, weak_challenge_upto_weak_bisim_sound, gfp_wbWeak_eq_wbisim); the pitfall relation does not progress there (pitfall_not_progress_wbWeak). Of the two weak functionals defined here, the failure occurs for wb (single-step challenges) and not for wbWeak.
- Does not say that every use of ≈ inside an up-to function is unsound: ~R~ and ≳R≲ are sound for wb on every transition system (weak_upto_strong_bisim_sound, weak_upto_expansion_sound), and so is the asymmetric ≳R≈ / ≈R≲ form (weak_upto_expansion_asymmetric_sound).
- Does not say ≈ is not transitive or not an equivalence (≈ is symmetric and transitive here: wbisim_symm, wbisim_trans); it is only the proof technique ≈R≈ for wb that fails.
- Union with weak bisimilarity (R ↦ R ∪ ≈) is compatible with and sound for wb on every LTS (weak_upto_union_wbisim_compatible, weak_upto_union_wbisim_sound; card strong-upto-union-with-bisimilarity, weak instance). The counterexample composes ≈ with R on both sides (≈R≈).
- The failure needs both silent and visible transitions: ≈R≈ is sound for wb on every LTS without silent steps (weak_upto_weak_bisim_sound_of_noTau; non-vacuity noTau_nonvacuity) and on every LTS without visible labels, where ≈ is total (sound_wb_of_no_visible; non-vacuity no_visible_nonvacuity).
- Treating silent and visible challenges differently can be sound: Pous (ICALP 2005 / TCS 2007), Theorem 2.5, mechanized as Theorem upto in rocq-archive/weak-up-to, allows visible challenges to be answered into (R ∪ ≈)* provided silent challenges are answered into ≳R≈ (and symmetrically). Not formalized here.
- Divergence insensitivity: weak bisimilarity and expansion as defined here identify a silently diverging state with a dead one (divergence_insensitive: in a two-state system a τ-loop is weakly bisimilar to, and expands, a dead state, though the two are not strongly bisimilar). Nothing is claimed about divergence-sensitive equivalences or simulations, such as those with well-founded stuttering measures used in compiler-correctness proofs.
- Toy model: Prop-valued binary relations on an arbitrary state type, an arbitrary labelled transition system with labels Option L (none = silent step), and, for concrete examples, a finite process syntax with only inaction, prefix and binary choice (no recursion, parallel composition, restriction or name passing). The result is a statement about this toy model; it neither establishes nor refutes the corresponding claims about up-to techniques used in real equivalence, refinement or compiler-correctness proofs.
- Any application to a real proof (for example a forward or backward simulation in a compiler-correctness development) is a separate modeling-bridge argument, not established by this theorem.

**9. `weak-upto-strong-bisimilarity`**

- Strong bisimilarity does not absorb τ-steps (a.0 ≁ τ.a.0: bisim_example_neg); for example the pitfall relation {(τ.a.0, 0)} does not progress to ~R~ under wb (pitfall_control_strong).
- Two-sided closures (~R~, ≳R≈, ≈R≲, ≳R≲) are relational compositions: each relates p and q only through a middle R-pair, so each maps ∅ to ∅. A candidate relation whose derivatives reach identical or already-equivalent states may therefore have to contain such pairs (for example (0, 0)) or be combined with the identity. For example, the singleton {(a.τ.0, a.0)} relates processes with a.τ.0 ≳ a.0, yet progresses under none of ~R~, ≳R≲ or (for left moves) ≳R≈ (singleton_expanding_pair_fails_without_refl_pair).
- Divergence insensitivity: weak bisimilarity and expansion as defined here identify a silently diverging state with a dead one (divergence_insensitive: in a two-state system a τ-loop is weakly bisimilar to, and expands, a dead state, though the two are not strongly bisimilar). Nothing is claimed about divergence-sensitive equivalences or simulations, such as those with well-founded stuttering measures used in compiler-correctness proofs.
- Toy model: Prop-valued binary relations on an arbitrary state type, an arbitrary labelled transition system with labels Option L (none = silent step), and, for concrete examples, a finite process syntax with only inaction, prefix and binary choice (no recursion, parallel composition, restriction or name passing). The result is a statement about this toy model; it neither establishes nor refutes the corresponding claims about up-to techniques used in real equivalence, refinement or compiler-correctness proofs.
- Any application to a real proof (for example a forward or backward simulation in a compiler-correctness development) is a separate modeling-bridge argument, not established by this theorem.

**10. `weak-upto-expansion-asymmetric`**

- Using ≳R≈ in both clauses of the symmetric functional is not sound (weak_upto_expansion_left_weak_right_not_sound, on the process LTS over two labels; card weak-upto-expansion-left-weak-right-symmetric-unsound).
- Not claimed to be compatible with wsimL or wsimR; only soundness is stated.
- Expansion is defined with τ⁺ (at least one τ) in the slower process's answer; other variants of expansion are not examined.
- Two-sided closures (~R~, ≳R≈, ≈R≲, ≳R≲) are relational compositions: each relates p and q only through a middle R-pair, so each maps ∅ to ∅. A candidate relation whose derivatives reach identical or already-equivalent states may therefore have to contain such pairs (for example (0, 0)) or be combined with the identity. For example, the singleton {(a.τ.0, a.0)} relates processes with a.τ.0 ≳ a.0, yet progresses under none of ~R~, ≳R≲ or (for left moves) ≳R≈ (singleton_expanding_pair_fails_without_refl_pair).
- Symbol convention: here p ≳ q (expands T p q) means that p is the slower process (τ.a.0 ≳ a.0), following Sangiorgi-Milner (1992) and Pous-Sangiorgi (2011); Arun-Kumar and Hennessy (1992) write their efficiency preorder with the opposite orientation of the symbols (p ≲ q for 'q is at least as fast as p'). Reading ≳R≲ with the symbols reversed (≲R≳) gives an unsound technique: the pitfall relation {(τ.a.0, 0)} progresses under it while τ.a.0 ≉ 0 (weak_upto_reversed_expansion_unsound).
- Divergence insensitivity: weak bisimilarity and expansion as defined here identify a silently diverging state with a dead one (divergence_insensitive: in a two-state system a τ-loop is weakly bisimilar to, and expands, a dead state, though the two are not strongly bisimilar). Nothing is claimed about divergence-sensitive equivalences or simulations, such as those with well-founded stuttering measures used in compiler-correctness proofs.
- Toy model: Prop-valued binary relations on an arbitrary state type, an arbitrary labelled transition system with labels Option L (none = silent step), and, for concrete examples, a finite process syntax with only inaction, prefix and binary choice (no recursion, parallel composition, restriction or name passing). The result is a statement about this toy model; it neither establishes nor refutes the corresponding claims about up-to techniques used in real equivalence, refinement or compiler-correctness proofs.
- Any application to a real proof (for example a forward or backward simulation in a compiler-correctness development) is a separate modeling-bridge argument, not established by this theorem.

**11. `weak-upto-expansion`**

- Up to expansion is not compatible with wb on the process LTS over any label type (weak_upto_expansion_not_compatible; card weak-upto-expansion-not-compatible), so the first-order closure cards (composition, union, iteration) do not apply to it. This does not make its composites with wb-compatible functions unsound: in the Agda development nad/up-to (Danielsson 2018), up to expansion is proved size-preserving and size-preserving functions are proved to be exactly those below the companion, which gives sound composition there. That second-order argument is not formalized here (not proved here), and that development's definitions differ in detail from ours.
- Replacing the right-hand ≲ by ≈ (≳R≈ in both clauses) breaks soundness (weak_upto_expansion_left_weak_right_not_sound, on the process LTS over two labels; card weak-upto-expansion-left-weak-right-symmetric-unsound).
- Follows from the asymmetric card (weak-upto-expansion-asymmetric) by monotonicity, given ≳ ⊆ ≈ and symmetry of ≈.
- Two-sided closures (~R~, ≳R≈, ≈R≲, ≳R≲) are relational compositions: each relates p and q only through a middle R-pair, so each maps ∅ to ∅. A candidate relation whose derivatives reach identical or already-equivalent states may therefore have to contain such pairs (for example (0, 0)) or be combined with the identity. For example, the singleton {(a.τ.0, a.0)} relates processes with a.τ.0 ≳ a.0, yet progresses under none of ~R~, ≳R≲ or (for left moves) ≳R≈ (singleton_expanding_pair_fails_without_refl_pair).
- Symbol convention: here p ≳ q (expands T p q) means that p is the slower process (τ.a.0 ≳ a.0), following Sangiorgi-Milner (1992) and Pous-Sangiorgi (2011); Arun-Kumar and Hennessy (1992) write their efficiency preorder with the opposite orientation of the symbols (p ≲ q for 'q is at least as fast as p'). Reading ≳R≲ with the symbols reversed (≲R≳) gives an unsound technique: the pitfall relation {(τ.a.0, 0)} progresses under it while τ.a.0 ≉ 0 (weak_upto_reversed_expansion_unsound).
- Divergence insensitivity: weak bisimilarity and expansion as defined here identify a silently diverging state with a dead one (divergence_insensitive: in a two-state system a τ-loop is weakly bisimilar to, and expands, a dead state, though the two are not strongly bisimilar). Nothing is claimed about divergence-sensitive equivalences or simulations, such as those with well-founded stuttering measures used in compiler-correctness proofs.
- Toy model: Prop-valued binary relations on an arbitrary state type, an arbitrary labelled transition system with labels Option L (none = silent step), and, for concrete examples, a finite process syntax with only inaction, prefix and binary choice (no recursion, parallel composition, restriction or name passing). The result is a statement about this toy model; it neither establishes nor refutes the corresponding claims about up-to techniques used in real equivalence, refinement or compiler-correctness proofs.
- Any application to a real proof (for example a forward or backward simulation in a compiler-correctness development) is a separate modeling-bridge argument, not established by this theorem.

**12. `weak-upto-expansion-not-compatible`**

- Does not contradict soundness of up to expansion (weak_upto_expansion_sound; card weak-upto-expansion); it shows compatibility is not necessary for soundness.
- Specific to this formulation of wb and ≳R≲; other decompositions of the weak functional (for example Pous's separate treatment of silent and visible challenges) are not examined.
- The first-order closure cards (composition, union, iteration) do not apply to up to expansion. This does not make its composites with wb-compatible functions unsound: in the Agda development nad/up-to (Danielsson 2018), up to expansion is proved size-preserving and size-preserving functions are proved to be exactly those below the companion, which gives sound composition there. That second-order argument is not formalized here (not proved here), and that development's definitions differ in detail from ours.
- The failure needs silent steps but does not need visible labels: ≳R≲ commutes with wb on every transition system without silent steps (expUpTo_commutes_of_noTau), while the witness above lives in the process language over any label type, including the empty one.
- Divergence insensitivity: weak bisimilarity and expansion as defined here identify a silently diverging state with a dead one (divergence_insensitive: in a two-state system a τ-loop is weakly bisimilar to, and expands, a dead state, though the two are not strongly bisimilar). Nothing is claimed about divergence-sensitive equivalences or simulations, such as those with well-founded stuttering measures used in compiler-correctness proofs.
- Toy model: Prop-valued binary relations on an arbitrary state type, an arbitrary labelled transition system with labels Option L (none = silent step), and, for concrete examples, a finite process syntax with only inaction, prefix and binary choice (no recursion, parallel composition, restriction or name passing). The result is a statement about this toy model; it neither establishes nor refutes the corresponding claims about up-to techniques used in real equivalence, refinement or compiler-correctness proofs.

**13. `weak-upto-expansion-left-weak-right-symmetric-unsound`**

- Does not refute the asymmetric technique (≳R≈ for left moves, ≈R≲ for right moves), which is sound on every transition system (weak_upto_expansion_asymmetric_sound).
- Escape hatch (one-sided simulation): ≳R≈ is sound for the one-sided weak simulation functional wsimL: R ⊑ wsimL T (≳R≈) implies R ⊑ gfp (wsimL T) (weak_upto_expansion_left_weak_right_sound_for_wsimL). Unsoundness arises only from also using ≳R≈ for moves of the right state.
- Divergence insensitivity: weak bisimilarity and expansion as defined here identify a silently diverging state with a dead one (divergence_insensitive: in a two-state system a τ-loop is weakly bisimilar to, and expands, a dead state, though the two are not strongly bisimilar). Nothing is claimed about divergence-sensitive equivalences or simulations, such as those with well-founded stuttering measures used in compiler-correctness proofs.
- Toy model: Prop-valued binary relations on an arbitrary state type, an arbitrary labelled transition system with labels Option L (none = silent step), and, for concrete examples, a finite process syntax with only inaction, prefix and binary choice (no recursion, parallel composition, restriction or name passing). The result is a statement about this toy model; it neither establishes nor refutes the corresponding claims about up-to techniques used in real equivalence, refinement or compiler-correctness proofs.
- Any application to a real proof (for example a forward or backward simulation in a compiler-correctness development) is a separate modeling-bridge argument, not established by this theorem.

**14. `weak-bisimilarity-not-sum-congruence`**

- Says nothing about other operators (prefix, parallel composition, restriction).
- Strong bisimilarity's preservation by + follows from card strong-upto-sum-context but is not stated separately.
- Escape hatch 1 (guarded choice): prefix-guarded choice preserves weak bisimilarity, P ≈ P' → μ.P + Q ≈ μ.P' + Q, for every label type and every prefix μ, including μ = τ (wbisim_guarded_sum_congruence; non-vacuity guarded_sum_congruence_nonvacuity). Weak bisimulation up to non-degenerate contexts is reported sound in the Agda development nad/up-to (up-to-context-size-preserving); not formalized here.
- Escape hatch 2 (observation congruence): rooted weak bisimilarity, which requires a root silent step to be answered by at least one silent step, is classically a congruence for unguarded + (Milner 1989). Not formalized here (not proved here).
- Two distinct visible labels are not needed: one label suffices (wbisim_not_sum_congruence_one_label); over the empty label type the failure disappears (wbisim_sum_congruence_no_visible).
- This is a fact about weak bisimilarity, not about an up-to technique; its role here is to explain card weak-upto-sum-context-unsound.
- Toy model: Prop-valued binary relations on an arbitrary state type, an arbitrary labelled transition system with labels Option L (none = silent step), and, for concrete examples, a finite process syntax with only inaction, prefix and binary choice (no recursion, parallel composition, restriction or name passing). The result is a statement about this toy model; it neither establishes nor refutes the corresponding claims about up-to techniques used in real equivalence, refinement or compiler-correctness proofs.

**15. `weak-upto-sum-context-unsound`**

- SumClo excludes prefix contexts; nothing is claimed about prefix-only contexts, non-degenerate (guarded) contexts or general CCS contexts. Up to non-degenerate contexts is reported sound for weak bisimilarity in nad/up-to (not formalized here), and prefix-guarded choice preserves ≈ (wbisim_guarded_sum_congruence).
- The one-pair relation {(τ.a.0 + b.0, a.0 + b.0)} does not progress to its +-context closure under wb (one_pair_sum_not_progresses_sumClo; a bounded Boolean re-check also appears in Checks.lean, which has no proved link to the Prop-level wb); the prefix a.[·] in the witness is what makes the bad pair reachable as a derivative.
- Two distinct visible labels are not needed: the technique is sound if and only if the label type is empty (weak_upto_sum_context_sound_iff_no_visible).
- Divergence insensitivity: weak bisimilarity and expansion as defined here identify a silently diverging state with a dead one (divergence_insensitive: in a two-state system a τ-loop is weakly bisimilar to, and expands, a dead state, though the two are not strongly bisimilar). Nothing is claimed about divergence-sensitive equivalences or simulations, such as those with well-founded stuttering measures used in compiler-correctness proofs.
- Toy model: Prop-valued binary relations on an arbitrary state type, an arbitrary labelled transition system with labels Option L (none = silent step), and, for concrete examples, a finite process syntax with only inaction, prefix and binary choice (no recursion, parallel composition, restriction or name passing). The result is a statement about this toy model; it neither establishes nor refutes the corresponding claims about up-to techniques used in real equivalence, refinement or compiler-correctness proofs.
- Any application to a real proof (for example a forward or backward simulation in a compiler-correctness development) is a separate modeling-bridge argument, not established by this theorem.

**16. `strong-upto-sum-context`**

- Prefix contexts are not part of SumClo, and adding them breaks compatibility: the full context closure CtxClo (with μ.[·]) is not sb-compatible, because (0+0, 0) ∈ sb ∅ puts (a.(0+0), a.0) in the closure of sb ∅, while its a-derivative (0+0, 0) is not in the closure of ∅, which is the identity (prefix_context_not_compatible_sb). Prefix contexts are reported to be respectful (Sangiorgi 1998) and below the companion of sb (Pous 2016), hence sound; neither is formalized here.
- Specific to the toy syntax (inaction, prefix, choice) and its structural operational semantics.
- The closed-term constructor SumClo.refl is not needed for compatibility: the closure without it is also compatible with sb (sumCloNoRefl_compatible_sb). It is what lets closed terms appear in contexts, as in [·] + b.0 for the witnesses relC and ctxRel (sumCloNoRefl_misses_closed_context).
- Toy model: Prop-valued binary relations on an arbitrary state type, an arbitrary labelled transition system with labels Option L (none = silent step), and, for concrete examples, a finite process syntax with only inaction, prefix and binary choice (no recursion, parallel composition, restriction or name passing). The result is a statement about this toy model; it neither establishes nor refutes the corresponding claims about up-to techniques used in real equivalence, refinement or compiler-correctness proofs.
- Any application to a real proof (for example a forward or backward simulation in a compiler-correctness development) is a separate modeling-bridge argument, not established by this theorem.

**17. `companion-compatible-and-sound`**

- Existence is by an impredicative union over all functions; no constructive description is given.
- Whether up to expansion (not compatible with wb) lies below the companion of wb is not established here. The Agda development nad/up-to proves that up to expansion is size-preserving and that size-preserving functions are exactly those below the companion, which gives it there; this is not formalized here.
- The companion is not monotone in the functional: although sb PStep R ⊑ wb PStep R for every R, the companion of sb is not below the companion of wb on the process LTS over two labels, since SumClo lies below the former but is not sound for wb there (companion_not_monotone_in_functional). Membership below the companion of sb says nothing about the weak case.
- Toy model: Prop-valued binary relations on an arbitrary state type, an arbitrary labelled transition system with labels Option L (none = silent step), and, for concrete examples, a finite process syntax with only inaction, prefix and binary choice (no recursion, parallel composition, restriction or name passing). The result is a statement about this toy model; it neither establishes nor refutes the corresponding claims about up-to techniques used in real equivalence, refinement or compiler-correctness proofs.

### Attractive stronger conclusions that are not established

- **known not to apply:** "compatible" and "sound" are not interchangeable: up to expansion is sound for `wb` (result 11) but not compatible with it (result 12), so the closure results 2–4 do not apply to it.
- **not examined:** whether merely sound up-to functions are closed under composition, union or iteration (they are reported not to be closed under composition in the literature; not proved here).
- **not examined:** respectful functions, size preservation, functions below the companion of `wb` (in particular whether up to expansion lies below it), tower induction, parameterized coinduction.
- **known not to apply:** the pitfall of result 8 is a property of the technique `≈R≈` for `wb`, not of `≈`: `≈` is symmetric and transitive here (`wbisim_symm`, `wbisim_trans`).
- **not examined:** divergence-sensitive equivalences, simulations with well-founded stuttering measures, heterogeneous simulations between different source and target systems, and any real compiler or verification framework.
- **not examined:** processes with recursion, parallel composition, restriction or name passing; contexts other than `+`-contexts and (for one negative result) prefix contexts; transfinite iteration.
- **not examined:** toolchains other than `leanprover/lean4:v4.34.1`.

### Escape hatches (what defeats each negative result)

- Result 8 (`≈R≈` unsound for `wb`): weak challenges (`wbWeak`), no silent transitions (`NoTau T`), or no visible labels each make `≈R≈` (respectively every technique) sound; replacing `≈` by `~` on both sides, by `≳ … ≲`, by the asymmetric `≳R≈`/`≈R≲`, or composition by union (`R ∪ ≈`) gives sound techniques for every LTS. Pous's Theorem 2.5 (silent challenges answered into `≳R≈`, visible challenges into `(R ∪ ≈)*`) is a further sound refinement reported in [Pous05] and mechanized in [weak-up-to]; not formalized here.
- Result 12 (`≳R≲` not compatible with `wb`): on transition systems without silent steps it commutes with `wb` (`expUpTo_commutes_of_noTau`).
- Result 13 (`≳R≈` in both clauses unsound): sound for the one-sided functional `wsimL` (`weak_upto_expansion_left_weak_right_sound_for_wsimL`); sound when right moves use `≈R≲` (result 10).
- Result 14 (`≈` not a `+`-congruence): prefix-guarded choice preserves `≈` (`wbisim_guarded_sum_congruence`); over the empty label type `+` preserves `≈` (`wbisim_sum_congruence_no_visible`); rooted weak bisimilarity (observation congruence) is classically a congruence for `+` [Milner89], not formalized here.
- Result 15 (up to `+`-contexts unsound for `wb`): sound if and only if the label type is empty (`weak_upto_sum_context_sound_iff_no_visible`); sound for the strong functional (result 16); up to non-degenerate contexts is reported sound for weak bisimilarity in [nad/up-to], not formalized here.

### Unknown tightness

No ledger entry has tightness `unknown`. For result 10, each tightness counterexample weakens one clause from expansion to weak bisimilarity (and so also covers dropping it); whether intermediate weakenings of a clause are sound is not examined.

### Disproved or dropped draft statements

None. No conjectured statement in this theory was disproved or dropped; each of the 17 results is proved in the form stated in its card.

## Evidence

**Kernel check.** Observed on 2026-11-21 with `leanprover/lean4:v4.34.1` (GitHub `leanprover/lean4`, tag `v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`), core Lean only. A fresh copy of `lean/` was built with `lake build` with Lake's artifact cache disabled, so every proof was re-elaborated and re-checked by the kernel. `#print axioms`-equivalent data (Lean's `collectAxioms`) for every declaration of the library is recorded in `audit/axioms.json`: 595 declarations audited; 574 declarations use no axioms; 12 declarations use `propext`; 9 declarations use `Quot.sound`, `propext`. `Classical.choice` is not used. No `sorry`, `admit`, `native_decide`, `axiom`, `opaque`, `implemented_by`, `extern` or `unsafe` occurs in the sources.

**Statement hashes.** For every Lean name referenced by a card in `results.json`, `audit/statements.json` records the SHA-256 of the statement (the Lean `repr` of the declaration's type) and the SHA-256 of its definition closure (the sorted, newline-joined entries `name : repr(type)`, followed by ` := repr(value)` for non-theorem constants, over all package-local constants reachable from the statement; theorem bodies excluded). Card roles: `result`, `nonvacuity`, `control` (positive control), `ce:<hyp>` (tightness counterexample).

| Theorem (`Toy.UpTo.`) | Card: role | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
| :--- | :--- | :--- | :--- | :--- |
| `sound_counterexample_noncommuting` | 1 ce:hc | none | `d899006f4e495cccad1f28daeb26d1f55e83dac47967e0f7e6638a063342476a` | `77f90e1ff4129b10896f732ef82898a4eca65daec05b6fb4bb4703d6570cb489` (20) |
| `sound_counterexample_nonmonotone_functional` | 1 ce:hb | none | `562c73621076cfc804ea2a25687b8dc949fdbf95228fc24bc74fa89236702e60` | `3b3b8475edefcafbbfb63a91b3ea38444b8dff913d401ee51070887dddb6f5a9` (9) |
| `sound_counterexample_nonmonotone_upto` | 1 ce:hf | none | `6f25893177b2e75dea504b247445d2dfbc5fad3899d8943408e3127a757e8d84` | `6416138dfb181d42eec43139450485c1b934bc2ac6e0dcf67e9c607c7ece33f1` (9) |
| `sound_of_compatible_nonvacuity` | 1 nonvacuity | none | `8e1a2d26711f62c4c97cb783aab3650f9e9765acb4b469fa50db9c8fa3e0a6d0` | `cc9329032685e579a06a696eb3d4bc0c9cc58ea5a5828a43600a873460a3f9e4` (22) |
| `sound_of_compatible_of_monotone_functional` | 1 result | none | `8b673d0d7f4ff779876325efe5418cc006b693efb8e93f84c92e5e90ddf73c51` | `dd428b6b2f4343b11ba6fbb320c6af4cf518c14df84130c8d85d721cb52684e8` (7) |
| `comp_counterexample_noncommuting_left` | 2 ce:hcf | none | `8644c289827c2194c45fd32837514d1b518a637102e1338ffc3c74fe6f7ed1a4` | `4004e720cc64f51ffa240701385eda730cae1ba0e09dc9eb452fe4419c89d943` (11) |
| `comp_counterexample_noncommuting_right` | 2 ce:hcg | none | `817d8ed94bf1ecf60fdbfbba303c08433a2fcf8f8c6d66d5017ca43374cc16da` | `4004e720cc64f51ffa240701385eda730cae1ba0e09dc9eb452fe4419c89d943` (11) |
| `comp_counterexample_nonmonotone_left` | 2 ce:hf | none | `bc8fd1f0df357cd9f26aba8fddc72958aba400feceba295adf548c615a0b9543` | `244d3e4fafc691c0762a2aec339ac14fa29c42cc21d52be6c21c946d3df8d08f` (8) |
| `comp_counterexample_nonmonotone_left_commutation` | 2 ce:hf | none | `8b11b093127bbc696d102fc628a7fc5dc9f81fb5a578227a6afeb2ecb37593a7` | `b52124e04d09d3d1f762b0579288021ed12c4db514875b90f540c00bfccddda3` (8) |
| `comp_counterexample_nonmonotone_right` | 2 ce:hg | none | `d5d180ea4241bf214182c2b9c914825ae8d1f08d14be5fefb8a9bc88683cd0a2` | `244d3e4fafc691c0762a2aec339ac14fa29c42cc21d52be6c21c946d3df8d08f` (8) |
| `compatible_comp` | 2 result | none | `85e19680254a3f3a3d8956108a6881689f5f73ccfce886ca05466ee9df6ceba0` | `aff2dfcfee2747ddb8dea05dc372b2b95278d56137e4828ac0520dc1a11db9ab` (7) |
| `compatible_comp_nonvacuity` | 2 nonvacuity | none | `8afb16a2b99a9bc7b41b48f7b579a28012fbe502741e3c14c4549309ef93b014` | `c71c92cf68ddd71720c164bd879429285d25ea5ae15751b09c0e2343216c1ccc` (22) |
| `compatible_iSup_nonvacuity` | 3 nonvacuity | none | `c938c86924559f7db67bf61ff58d931f5c402b9859962549dd81d07f021c1d52` | `a3b5f27189a5720cb35531e35cfc312436b90e53d69cfb165ce316fd5a457eb9` (20) |
| `compatible_iSup_of_monotone_functional` | 3 result | none | `406942a6d831611d2e11681b1dd664941215ab72c80443c43b329aec0654f9dc` | `df85a29cf4e416e5a31d52a4dc31b292f34d86b4ef44973aa429f44b26a73711` (7) |
| `iSup_counterexample_noncommuting_member` | 3 ce:hcF | none | `e0c5489a7a149803d9bdfbd5fa3b780bf503533eb61d224d268c44612c87ad5c` | `25b4fd9d09090485157e7b7dad13efd23ff5439d5d09469edfec78d4c9a9daa0` (11) |
| `iSup_counterexample_nonmonotone_functional` | 3 ce:hb | Quot.sound, propext | `5bd047cd729e6dcf982a9db5add1c469e643b5deefb5482062440be12e6b2ef4` | `7feda91311056726f86d233c8783d09d1f499de5e54423219c59a5b0e32475ee` (11) |
| `iSup_counterexample_nonmonotone_member` | 3 ce:hF | none | `073578e3dda6eb2aae866131b37f755d07ea11329d6d5eaf1d28d44077b7b20c` | `70ded9ff7864529bea3c70b1392724a91d465d8984325eb6730704c56cb2e606` (8) |
| `compatible_omega_nonvacuity` | 4 nonvacuity | propext | `9b47fceccb1c9f2d217e43d4192bfffde05c8136af98e7f96854430223451d1c` | `26ff2d7c0f76f6f107fc35d265be51824e3ec51d8fa52e40785a101df41c2a4d` (23) |
| `compatible_omega_of_monotone_functional` | 4 result | none | `1987ef307a4a15e947e78f34fea7c44661132e08eff0791ad966a971c0dd382c` | `7ceff65f541b353c9054723a0c54977ca8be25073e7d8f5801f236a2b70c9f00` (10) |
| `omega_counterexample_noncommuting` | 4 ce:hc | none | `02c05c5fa5443055818d639e340d7ae2bd22c4fd3862c65cbd3c69aa49d64d05` | `245f0d1b9e208622e4a0e87c33391de6316974b52b0fd4685af1c0d26aa94c22` (14) |
| `omega_counterexample_nonmonotone_functional` | 4 ce:hb | Quot.sound, propext | `28e125bc503229ec1cc66131f5119ff9073c488ae063ffd425a3a19814476dfe` | `cefe81b3d3fd078d88dd7008ff8de48371634c853e4bd46fd18de9954ae426c7` (12) |
| `omega_counterexample_nonmonotone_upto` | 4 ce:hf | none | `60d3226b694088cdc2ed91bc4a891bc40ce179cba174a144843650990170c52d` | `4a74765249e9375b213db80ebfeee925dbe0101c7f4a1ef6f9bb3175a0f76e31` (11) |
| `compatible_union_gfp_of_monotone_functional` | 5 result | none | `054f41270507b0ba235311c5217ed03de6c61c59992257d88b5dd3d84e1a9a38` | `d1d796c83238792fe123d1ad0b8ba6f66cdc451de76856cd959efd3a1d075cd5` (8) |
| `sound_union_gfp_of_monotone_functional` | 5 result | none | `5f88b3dbb67779450df2b7276705fb7d7348fb12dda05b9279041c15f3a1ed03` | `8ccdf86f5b5ee710371a519ebf4247cbe8c36a26fa2ae40e72fcc8183e8182a4` (7) |
| `strong_upto_union_bisim_compatible` | 5 result | none | `76029fa59b337254294d508b44b8c73d1f5cbfa6eeaca75d3b9108781de79bf9` | `985e8a8bba5e9b520a22852955b08761363fff18e7116023ae1a351dbd5657ae` (11) |
| `strong_upto_union_bisim_sound` | 5 result | none | `33231f284111ebf6ca5791aa4e989c19a1219dce275b1398ba57d9f7e8429dbe` | `75d5077bdac039abf0820f126727db65f196ceff6e15b4e26022fcbfbe753393` (9) |
| `strong_upto_union_bisim_useful` | 5 nonvacuity | none | `dd755f4a1e0593f7e7afb93deff05156a01544fd56dd3e84ef2a17e0411feaaa` | `16b07a657f7f3a56da8684cc256d6124ca982ae75a511e5231f06b451ea560cc` (20) |
| `union_gfp_counterexample_nonmonotone_functional` | 5 ce:hb | none | `6135fca60a4a9b347ca50bc6ac9a761499d227047e695f7015aba691a6234720` | `b4e00aa2453bbd2cbfdd7ee639580fe6c01c3c3e58d2b3bc4f4d55e44af8af7b` (11) |
| `weak_upto_union_wbisim_compatible` | 5 result | none | `9e95c9f96c92a61dff7618dc966aba546ad9d0792732e77b812ba0c49d593988` | `4f54e411a04da26db64aeb71f62d83e317bab027e0858cb4d5a72d8763db04e0` (18) |
| `weak_upto_union_wbisim_sound` | 5 result | none | `e89200745a9821403a840aa11de684567da61a2aee170b3046bad467abff63f1` | `0c6164700ecb15a40d7767360cf5b846010398b3cfa23192fe5d5a780b809037` (16) |
| `strong_upto_bisim_both_sides_compatible` | 6 result | none | `d06ddde8b75644ac79041c68a701e36c6a7b3b6c268b0b67934a4222ad8750a3` | `ac108ca174f083c4f4d98ed18e53e05de4d53798351d26d2d16b90cc35e3ebfc` (11) |
| `strong_upto_bisim_both_sides_sound` | 6 result | none | `6b071f6312b53e30029b0d7f99466eed0f527278823efac9348cc6c5c7131645` | `77e11bb619d6e18881970d4187f3a4331511ff556107d3d32dc99068fdba0e11` (9) |
| `strong_upto_bisim_both_sides_useful` | 6 nonvacuity | none | `c4fb6472187fb9cd37a882f0b35aa1f8daef19dd93b017513d62065d9b3f0ca6` | `865775b08295e4685b8c961c0b2619e3365fecac4b056d5a7b2fc95f15ba0b61` (20) |
| `strong_upto_equivalence_closure_compatible` | 7 result | none | `36a332435d009c69f012b9af59d22f3946abeac8332ce702a780266072c760b7` | `d95194e99352f2123d1e5c0c5a8913338437a748ba185d2dae42f762c6823154` (13) |
| `strong_upto_equivalence_closure_sound` | 7 result | none | `19780cae1156fb710a7ae1dd07485e1cb8f1ea4a41625181e841ad12dc3d312c` | `50efffbdbb3e0c39b07d7383309cc3764767b9b840447a2bf7b33d1b11caadcd` (12) |
| `strong_upto_equivalence_closure_useful` | 7 nonvacuity | none | `abc21db8dd2ce7694fa190c7a03f2a2b1dd81111d63422c7c32edc0db61489e6` | `f3992ab5698bf853793bac976c3e8e9eee987fe64666f964f78fd189c06a08ad` (22) |
| `pitfall_control_expansion` | 8 control | none | `63203883edf35054d2b055d0d790d5c0e2979981fcf5c0bb66a55478a9bef79d` | `a5884700b8386205c8c59536f4906f7b9560957c335500c0fe63ba57a62203f3` (31) |
| `pitfall_control_strong` | 8 control | none | `f1e6840063de2dccf5cc07aa9995591a5f79bba7270e662d90ed608aa76c0d38` | `b326e70bfc83bd1b29604630f8a300e657dee1598eabc2535fa5d199e5f848a5` (29) |
| `weak_challenge_upto_weak_bisim_sound` | 8 control | none | `c3dcdb3a74f4aa78eb1436429accbfa69908529e141be321987c4cb33c8abed0` | `e0239f2c0db6a94210d5fed69fbdd18d28952aac8a80e64c37c86b23695e5acb` (15) |
| `weak_upto_weak_bisim_not_sound` | 8 result | none | `64d39e3e59677132696978f87bc011d6566b61cab11c1116f9372967fcf95141` | `dbbd6d4aaba64292d710dee023723f533cbdfd177d73e05a54380856520bd367` (27) |
| `weak_upto_weak_bisim_sound_of_noTau` | 8 control | none | `add6c4f813df90ce482d31c95a82c480d4a3e45b5f363f931b314dd3731301be` | `99738608ac0c817a0e3352539829dec20cdcfd8b87f00b969a29e38f589f143b` (17) |
| `weak_upto_weak_bisim_unsound` | 8 result | none | `6841322813257558ef4e5ce7fd89e2a7c6ede3b4ce3ec1f3e4e6b3cd7160ab1d` | `52eef789f0c52f96fc3eb4079a481d600797e1fe29405a746ed65d4bde591e79` (28) |
| `weak_upto_strong_bisim_compatible` | 9 result | none | `1ed0a8b47b650a4c1b1b735462cbffc2b433577b53ae9c3a9340ddaadea53de3` | `405732d3e7a459d8aec204301036aa8fac617d3593a82fe8563e79bb8ce78c6e` (19) |
| `weak_upto_strong_bisim_sound` | 9 result | none | `9535c8e6ecf5bac4a3ab126e72d21802e0fd492266d84354f330003b4779b6ab` | `4e80e3ab4d62aac1d5700fbff78fab84283373ba3d01b0dbacffc1d041b7d30f` (17) |
| `weak_upto_strong_bisim_useful` | 9 nonvacuity | none | `8686fa040335612bb52a2eaa9424cc600f34e0e675e2417942db188a53bfd851` | `ead02147997268c736af741c2dd1131c2d8d8a845e02ead5b50c13dec8f8732d` (28) |
| `asym_counterexample_left_weakened` | 10 ce:hL | none | `2f2a73bf45ed1536e907fe8edff162d7f2fc481bff76cfd7cdb1190130fd3c4c` | `2d63c57993f288e862539bb149f1a7cafba3b376e29836011fd9e976bf0f642e` (33) |
| `asym_counterexample_right_weakened` | 10 ce:hR | none | `522bbff335dd57b2edce4d0c9aa5d8796529e98adf5017c5129dc74718beee1a` | `d26d6e76a8cbf2c38827e62092709d5733dc14da5d805a1366760d29361f3bdc` (33) |
| `weak_upto_expansion_asymmetric_nonvacuity` | 10 nonvacuity | none | `5d0fd2935e0c48646d07d02f23dbefc7884d0db179650a74aa4a46ab3449bf6d` | `ccfb08a07b799aa6499d4d29d1ddcb7fdd43b9648ba62e25387d8ecccc22163e` (33) |
| `weak_upto_expansion_asymmetric_sound` | 10 result | none | `8d22d7286bc5f2d39b708c66467314ca589c7ee5687f108202ab7d3bf211b2c1` | `a1f3686a0fc50bc7ad122d25813381cf2db73efa1dfd93bfa24cf52d9c5c6425` (19) |
| `weak_upto_expansion_asymmetric_strict_nonvacuity` | 10 nonvacuity | none | `9f4deb2b34088e300f1d72e28e59f721d0618c7f1a474b6618f50c43766b8287` | `78caeb4d7b77a83036305ea517ad4110286d43c1df5e25a1888fce98addfedcb` (34) |
| `weak_upto_expansion_sound` | 11 result | none | `cbcd6855c2d17309279ef7241fdd814eee5739127660aedadf850194b5827379` | `0b3df65cc8ff61d44cbc6dfe6000055b2b406362cc4c6881d8a31d18bbb025ce` (19) |
| `weak_upto_expansion_useful` | 11 nonvacuity | none | `2d734aa14bf3d0608d89ba78ca6b55e506343a417f5379f4e08b3ba2baa88362` | `8db3221a22b3deb517aa223cdd3f232885463c74846f2ac3ee76d171d5e9177c` (31) |
| `expUpTo_commutes_of_noTau` | 12 control | none | `9a54d3019eff5b63cad8d01e2f1f44d0067930a41f27901f6e5efc0eaab537d2` | `693720d04c962ce5bfdbcf9ca9b02f5871f19954b7011d7429ac4e6ed5cac77a` (19) |
| `weak_upto_expansion_commutes_counterexample` | 12 result | none | `268a0168ba078207ca0ec11561990fe83e9718a05e3af5c5e824c0328bc6683f` | `9d735b3db97bcb937a3eb52e337d6977dfb6d284b3bed7cff18cba904c7d3571` (27) |
| `weak_upto_expansion_not_compatible` | 12 result | none | `7faabf30e8650c31eebfdc059e7a89728d1d70bf419f688b7682b18d68e2fd59` | `476f99c0f4cb7ab35fd144dd8180e0835c72ea444bb138f14c57dda677d961e9` (29) |
| `mirror_control_asymmetric` | 13 control | none | `0ca3f717f81cd6018d4744f571703786732f72721526623df6784d3099f94db9` | `f5065f9d7206777575fc5574fd88ca6e88cdd7726f5902cc03581b0aaf906993` (32) |
| `mirror_control_expansion` | 13 control | none | `3f1be3a1e64093b070eab7c427b0707e94f670ecb2fb2f835c64264bce489803` | `5bc67e656335f012e0ad7e9132dab771b114d83c272652bbddec005845dc9d93` (31) |
| `weak_upto_expansion_left_weak_right_not_sound` | 13 result | none | `48690817aac8aa119147e8ccf261ee331f1096fe020fa2d482bff90284a5e5ea` | `3bbc98ad15b058e33e9fffa5038fe73681957a9ebba851c179c9ffc84ca8fe25` (31) |
| `weak_upto_expansion_left_weak_right_sound_for_wsimL` | 13 control | none | `c57721277a5f144e7a4362b36d031516ae120d3f21d439ebc8d0f34c230a764d` | `011425783548478220f4e9276ed3efa2e0380acc68fad7c3416098e25feff43f` (18) |
| `weak_upto_expansion_left_weak_right_unsound` | 13 result | none | `4dbf109b13bb138e1221666429a2dd56dd9250bd76d0c0c171142e4bdec5ce04` | `c131d9a6ec594793aa7c07586e791207e40ef59657dcbce011f846556c7eb9b9` (32) |
| `wbisim_guarded_sum_congruence` | 14 control | none | `b41b206f3cda5390037d2f3428e3c7b99bf797377f0bd125f4ec043594b4cb16` | `2a4d4bb49db3d6e3d5e10f546cc412c928ae52bc06dffdb4acbefa8d59ca4d86` (21) |
| `wbisim_not_sum_congruence` | 14 result | none | `d4680d1251c7c685eb6492a6db5e06cebcccfd7d6fd630c3224df023a3ea3334` | `9ed9ce2ab74dc6ecf7e223b65529cd510ed8b5157a692517720b385dd76429a3` (26) |
| `wbisim_not_sum_congruence_one_label` | 14 result | none | `18883ea782acf1fc85c8aa7b81840410d4aaf65decd4dd88e456a861b2cc62f1` | `c593af57c383c448e355bf243a8236cb8a41028cb33270eb5e46112bb6ac0b86` (23) |
| `wbisim_sum_congruence_no_visible` | 14 control; 14 ce:a | none | `e7d4c18a0e7483069ffd2043f31bbe7b4367262822b3de8e36816317364fc501` | `2a4d4bb49db3d6e3d5e10f546cc412c928ae52bc06dffdb4acbefa8d59ca4d86` (21) |
| `sum_context_control_strong` | 15 control | none | `de7d54948f5a5984d79d43ccfccf82ec4318a9dfad8e1cb83d68d032fb597beb` | `86c36b55d45453a2b308b5cbe6613828d0c7d8a2dd99c59176fa4fd173fc707b` (22) |
| `weak_upto_sum_context_not_sound` | 15 result | none | `a0b652564d6e58a5825b3952b6e4603a21541d8e3e7b05ea6dfa21245b7fd92b` | `ad7e9bf0d9153e89e661085c5049366ea4cd13ca0d5b6dee9321fc5d222e9df1` (29) |
| `weak_upto_sum_context_sound_iff_no_visible` | 15 result | none | `5f58b018e78f61f864287f6f5eac2f8d7bb822216db421853d624d7a21cab42f` | `8cd51bff91cc924531195198ac0832c78794f52edd2ec29180434dc2abcb833b` (26) |
| `weak_upto_sum_context_sound_no_visible` | 15 control; 15 ce:a | none | `a7b8aaf8efecc71d6b8f4cc5dd32e7c334a370e9dd11abc8aee0a6b46c182df3` | `8cd51bff91cc924531195198ac0832c78794f52edd2ec29180434dc2abcb833b` (26) |
| `weak_upto_sum_context_unsound` | 15 result | none | `aa94c6190a9939a30d3812116b7475c7f2b37a08d12066ce22b4a904349fcca0` | `84c7860bbafa898f231f333051f66bfacf76fe26aeba9d1bf0c4133454f37dbe` (31) |
| `weak_upto_sum_context_unsound_one_label` | 15 result | none | `513cdde0fb0b770243132d90006c36a1df4eb1d66ba2f0b46890b3b39c19f05d` | `532709df2a4b8552836f53589072c4aaafa49bb3af684ce187092842e7177a15` (28) |
| `strong_upto_sum_context_compatible` | 16 result | none | `67945b4b5a6249eb6cc51ce061f4c9b6a00bde647971aa559326e014a243c958` | `48bfc0484182a579e63d2098edd975a154303943ae2c8a0419159a4c00c9a2d3` (20) |
| `strong_upto_sum_context_sound` | 16 result | none | `193667768e108c65362dc27c1c06bf5f5948aa91236c2468ef30c97442f454e1` | `f33d5f24b74b88a7dbf11c3a0d6f33f60b36857b6aa08a4adaae6a968e1506dd` (19) |
| `strong_upto_sum_context_useful` | 16 nonvacuity | none | `e401393f73617602573b043e89d25934658e3af71fc6977e3e790bc1be83c361` | `116a41eb818abbd19dd271d0da6a9341556fed7a9a0a4860e18843f40a9ceb1c` (21) |
| `companion_bot_eq_gfp` | 17 result | none | `6a9507d1bce11f118be82434c62fc65ea626d20dc94bfdf496d6c33fb065acd6` | `0eaf36a8ae8f1d0d4e835ce5ef6920954dad8776738f5af8214eab446094b4ef` (7) |
| `companion_compatible_and_sound_of_monotone_functional` | 17 result | none | `66991968710f15accdceb014834028f68c5281e2c998c0404ebae80cf424ee62` | `d398d3de129a9c920ae4e72c6a7ba56deb2fea9834db22ef045e6faaaafef325` (10) |
| `companion_counterexample_nonmonotone_functional` | 17 ce:hb | none | `5ef3dc7d3d95fd400d933793de52906d22f089394b787cc7a14153ba916e4c8d` | `f6c0bdba25d0322529e5bd671d566ec01d61b55c3e0d51a7ad3587da1b0bb7d1` (11) |
| `companion_greatest` | 17 result | none | `d5d2538618bfdaabf5b7f06f8e8c2db82ecc361bc465e2e48092f08bfd38746a` | `f5ba59d64ec44d1706919db87db15ef440ecab58bf9d29dee78eea6200caed34` (5) |
| `companion_nonvacuity` | 17 nonvacuity | none | `f119e70aa1a7f3952553eaa533b5304df778808681f5669b6ee0b1f03232a7bc` | `7c3673c4b7f24f4707540dfb94cbb8e02d3c13ec3e0e7ffa2031160fb34d38e0` (21) |

**Supporting theorems cited in prose.** These are kernel-checked declarations of the same library (axioms in `audit/axioms.json`) that the cards cite by name but that carry no recorded statement hash: `asym_wstepL` (no axioms); `asym_wstepR` (no axioms); `bisim_example_neg` (no axioms); `bisim_example_pos` (no axioms); `companion_example_neg` (no axioms); `companion_example_pos` (no axioms); `companion_not_monotone_in_functional` (no axioms); `compatible_constGfp` (no axioms); `compatible_id` (no axioms); `divergence_insensitive` (no axioms); `expands_example_neg` (no axioms); `expands_example_pos` (no axioms); `gfp_postfixed` (no axioms); `gfp_wbWeak_eq_wbisim` (no axioms); `guarded_sum_congruence_nonvacuity` (no axioms); `incl_gfp_of_postfixed` (no axioms); `iter_commutes` (no axioms); `iter_mono` (no axioms); `killB_companion_not_compatible_but_sound` (Quot.sound, propext); `noTau_nonvacuity` (propext); `no_visible_nonvacuity` (no axioms); `one_pair_sum_not_progresses_sumClo` (no axioms); `one_sided_wsimL_nonvacuity` (no axioms); `pitfall_not_progress_wbWeak` (no axioms); `prefix_context_not_compatible_sb` (no axioms); `reflClo_compatible_wb` (no axioms); `sb_mono` (no axioms); `singleton_expanding_pair_fails_without_refl_pair` (no axioms); `sound_wb_of_no_visible` (no axioms); `stepSq_strict_on_proc` (no axioms); `strongUpTo_example_neg` (no axioms); `sumCloNoRefl_compatible_sb` (no axioms); `sumCloNoRefl_misses_closed_context` (no axioms); `sumClo_example_neg` (no axioms); `symClo_compatible_wb` (no axioms); `wb_mono` (no axioms); `wbisim_example_neg` (no axioms); `wbisim_example_pos` (no axioms); `wbisim_symm` (no axioms); `wbisim_trans` (no axioms); `weak_challenge_upto_weak_bisim_compatible` (no axioms); `weak_challenge_upto_weak_bisim_useful` (no axioms); `weak_upto_reversed_expansion_unsound` (no axioms); `weak_upto_union_wbisim_useful_singleton` (no axioms).

**Primary sources** (bibliographic data checked against Crossref on 2026-11-21; repository commits and the cited files and line ranges read at the stated commits on 2026-11-21):

- [Milner89] R. Milner. *Communication and Concurrency*. Prentice Hall, 1989. ISBN 0-13-115007-3. Origin of "bisimulation up to" for the strong case (per the abstract of [SM92]), weak bisimilarity not preserved by summation, observation congruence; chapter and section numbers not verified from the book.
- [SM92] D. Sangiorgi, R. Milner. The problem of "weak bisimulation up to". CONCUR '92, LNCS 630, pp. 32–46, Springer, 1992. doi:10.1007/BFb0084781. Abstract: up-to "works smoothly in the strong case" but "does not directly generalize to the weak case"; proposes techniques based on expansion.
- [Sangiorgi98] D. Sangiorgi. On the bisimulation proof method. *Mathematical Structures in Computer Science* 8(5):447–479, 1998. doi:10.1017/S0960129598002527. Bibliographic data verified; full text not inspected; commonly credited with respectful functions and up to context (attribution not verified at the source).
- [Pous05] D. Pous. Up-to techniques for weak bisimulation. ICALP 2005, LNCS 3580, pp. 730–741, Springer, 2005. doi:10.1007/11523468_59. Journal version: D. Pous. New up-to techniques for weak bisimulation. *Theoretical Computer Science* 380(1–2):164–180, 2007. doi:10.1016/j.tcs.2007.02.060. Content cited as mechanized in [weak-up-to].
- [Pous07] D. Pous. Complete lattices and up-to techniques. APLAS 2007, LNCS 4807, pp. 351–366, Springer, 2007. doi:10.1007/978-3-540-76637-7_24. HAL ensl-00155308. Abstract: theory of up-to techniques in complete lattices via a semi-commutation property.
- [PS11] D. Pous, D. Sangiorgi. Enhancements of the bisimulation proof method. In D. Sangiorgi, J. Rutten (eds.), *Advanced Topics in Bisimulation and Coinduction*, Cambridge Tracts in Theoretical Computer Science 52, pp. 233–289, Cambridge University Press, 2011. doi:10.1017/CBO9780511792588.007. ISBN 978-1-107-00497-9. Full text not inspected; section numbers cited here are those given in the comments of [nad/up-to].
- [Pous16] D. Pous. Coinduction all the way up. LICS 2016, pp. 307–316, ACM, 2016. doi:10.1145/2933575.2934564. HAL hal-01259622. The companion of a monotone function is the largest compatible function.
- [Danielsson18] N. A. Danielsson. Up-to techniques using sized types. *Proc. ACM Program. Lang.* 2(POPL), Article 43, 2018. doi:10.1145/3158131.
- [AKH92] S. Arun-Kumar, M. Hennessy. An efficiency preorder for processes. *Acta Informatica* 29(8):737–760, 1992. doi:10.1007/BF01191894. Writes the efficiency preorder with the opposite orientation of the symbols to the one used here.
- [DHS19] A. Durier, D. Hirschkoff, D. Sangiorgi. Divergence and unique solution of equations. *Logical Methods in Computer Science* 15(3), Article 12, 2019. doi:10.23638/LMCS-15(3:12)2019. arXiv:1806.11354. States that "up to weak bisimilarity" and "up to transitivity" are known to be unsound techniques, citing Pous–Sangiorgi.
- [SS25] K. Sakayori, D. Sangiorgi. Extensional and non-extensional functions as processes. *Logical Methods in Computer Science* 21(3), Article 25, 2025. doi:10.46298/LMCS-21(3:25)2025. arXiv:2405.03536. Definition 2.5 (expansion clauses); their `P ≲ Q` is `expands T Q P` here.
- [nad/up-to] Agda development `nad/up-to` (GitHub), commit `cf302a9ed4b794c2e3ce59660e4d0847a02e6075` (2025-09-17): `src/Bisimilarity/Weak/Up-to.agda` L43–56 (`Up-to-expansion R = Expansion ∞ ⊙ R ⊙ Expansion ∞ ⁻¹`, proved size-preserving) and L69–87 (theorem `6-5-2-4`, "a non-symmetric variant of up to expansion, based on the technique presented in Section 6.5.2.4" of [PS11]); `src/Up-to.agda` L158 (`size-preserving→up-to`) and L361–367 (a transformer is below the companion iff it is size-preserving); `src/Bisimilarity/Up-to/Counterexamples.agda` L685–696 (`¬-∘-closure`: up-to techniques are not closed under composition, not even for monotone and extensive transformers) and L639–643 (Pous and Sangiorgi discuss another instance in Section 6.5.4); `src/Bisimilarity/Weak/CCS.agda` L155–158 (`¬⊕-congˡ`) and L173–177 (`⊕·-cong`); `src/Bisimilarity/Weak/Up-to/CCS.agda` L29–62 (up to non-degenerate contexts, size-preserving at L53–56) and L64–73 (`¬-up-to-context-compatible`, a variant of a counterexample of Pous and Sangiorgi, Section 6.5.3). No statement that up to expansion is, or is not, compatible was found there.
- [coinduction] Coq/Rocq library `damien-pous/coinduction` (GitHub), commit `07d2a09f9cb971209683298e9f5b3f5031d98b3f` (2026-11-02): `theories/companion.v` L29 (`compat_comp`: compatible functions are closed under composition), L43–48 (`compat_sup`: compatible functions are closed under arbitrary unions) and L53–56 (`Definition t`, the companion as the union of all compatible functions, and `compat_t`: the companion is compatible); `theories/tower.v` (tower induction). Its README describes the library as initially based on the companion and now on tower induction, and lists `companion.v` as no longer used.
- [coinduction-examples] Coq/Rocq development `damien-pous/coinduction-examples` (GitHub), commit `467300e04f56fd465817179589383e37db7e9cbc`: `ccs.v` L605, `not_Transitive_wt` (with at least one channel name, the elements of the tower for the weak functional are not all transitive).
- [weak-up-to] Coq/Rocq development `rocq-archive/weak-up-to` (GitHub), commit `6780e1d43bc9583d5e6fe47418980d4dbc8f6527`: `Applications.v` L12–13 (`F := ≳R≈` for silent challenges, `G := (R ∪ ≈)*` for visible challenges) and L56–57 (`(** Theorem 2.5 *) Theorem upto: incl R (bisim TX TX)`).

Related mechanizations, cited for orientation only (nothing imported): parameterized coinduction (C.-K. Hur, G. Neis, D. Dreyer, V. Vafeiadis, POPL 2013, pp. 193–206, doi:10.1145/2429069.2429093); generalized parameterized coinduction (Y. Zakowski, P. He, C.-K. Hur, S. Zdancewic, CPP 2020, pp. 71–84, doi:10.1145/3372885.3373813); tower induction for CCS (S. Schäfer, G. Smolka, RAMiCS 2017, LNCS 10226, pp. 274–289, doi:10.1007/978-3-319-57418-9_17); textbook: D. Sangiorgi, *Introduction to Bisimulation and Coinduction*, Cambridge University Press, 2011, doi:10.1017/CBO9780511777110; Lean 4 Mathlib defines `OrderHom.gfp` in `Mathlib/Order/FixedPoints.lean` (mathlib4 commit `3eae40f5eb25c5934211edf662d3b24c5afbe47a`), which this package does not use.

## Revalidation

Requirements: `elan` (the Lean toolchain manager, so that `lake` uses the toolchain pinned in `lean/lean-toolchain`, `leanprover/lean4:v4.34.1`) and `python3`. The Lean project has no dependencies (no Mathlib, no `[[require]]`).

Primary check, run from the package directory:

```sh
python3 support/revalidate.py .
```

`support/revalidate.py` never modifies the package: it copies `lean/` to a temporary directory and there (1) runs `lake build`; (2) scans every Lean source for `sorry`, `admit`, `native_decide` and `axiom` declarations; (3) runs a generated Lean program that calls `Lean.collectAxioms` on every declaration of the library `ToyUpTo` and fails if any axiom other than `propext`, `Classical.choice`, `Quot.sound` occurs; and (4) for every Lean name referenced by `results.json` or recorded in `audit/statements.json`, recomputes the SHA-256 of the statement (`repr` of the declaration's type) and of its definition closure (as described under **Evidence**) and compares them with `audit/statements.json`. It prints `REVALIDATED` and exits with status 0 exactly when all checks pass.

Manual spot check of axioms, from the package directory:

```sh
cd lean
lake build
cat > /tmp/AxiomCheck.lean <<'EOF'
import ToyUpTo
#print axioms Toy.UpTo.sound_of_compatible_of_monotone_functional
#print axioms Toy.UpTo.weak_upto_weak_bisim_unsound
#print axioms Toy.UpTo.weak_upto_expansion_asymmetric_sound
#print axioms Toy.UpTo.weak_upto_sum_context_sound_iff_no_visible
EOF
lake env lean /tmp/AxiomCheck.lean
```

A passing run establishes only that the recorded statements still build and kernel-check with the recorded axioms under the pinned toolchain. Under a different toolchain the statement hashes may change even when the mathematics does not (they hash Lean's `repr` of terms); in that case compare the statements in `lean/ToyUpTo/` with the ones quoted under **Findings** by reading them. The modeling-bridge claims are not revalidated by any command.
