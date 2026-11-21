# Semantic typing, encapsulated unsafe code, and adequacy in a toy call-by-value language (Lean 4)

## Summary

This package is a self-contained Lean 4 development (namespace `Toy.SemType`, library `ToySemType`, core Lean only) of a unary, Kripke-style logical-relation model for a small call-by-value language with a heap of word cells and one unsafe primitive, `cast : word → reference`, which has no syntactic typing rule. It proves the three pillars of semantic type soundness (adequacy, the fundamental theorem, and semantic let-compatibility), derives the encapsulation principle ("every syntactically typed client of a semantically typed library is safe"), exhibits a concrete library that uses `cast` behind a dynamic bounds check and is semantically but not syntactically typed, proves that `cast` of an `int` variable has no semantic type (with both model ingredients that force this shown necessary), and shows by fully proved ablations that each ingredient of the model is needed. Every result below is kernel-checked with no `sorry` and uses no axioms other than `propext` and `Quot.sound`.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

Results (card id in brackets; `std` = `Recipe.std`, the standard model):

* **R1** [`adequacy`]: In the standard model, an expression that is semantically well typed at some type in the empty typing context (`SemTyped Recipe.std [] e τ`) never reaches a stuck configuration, from any initial heap (`∀ h, Safe (e, h)`). The empty context does not require syntactic closedness `e.closedAt 0 = true`.
* **R2** [`fundamental-theorem`]: Every expression that is syntactically well typed in a context `Γ` at type `τ` (`HasType Γ e τ`) is semantically well typed in `Γ` at `τ` in the standard model (`SemTyped Recipe.std Γ e τ`).
* **R3** [`syntactic-type-safety-corollary`]: A syntactically well-typed expression in the empty context (`HasType [] e τ`, which also makes `e` closed) never gets stuck, from any initial heap; derived from adequacy and the fundamental theorem.
* **R4** [`semantic-let-compatibility`]: In the standard model, if a client `c` is semantically well typed at `τ` in context `σ :: Γ` (`SemTyped Recipe.std (σ :: Γ) c τ`) and a library expression `lib` is semantically well typed at `σ` in context `Γ` (`SemTyped Recipe.std Γ lib σ`), then the call-by-value linked program `app (lam c) lib` is semantically well typed at `τ` in context `Γ`; neither piece needs to be syntactically typable.
* **R5** [`linking-safety-semantic-client`]: In the standard model, linking (call-by-value `app (lam c) lib`) a client `c` that is semantically well typed at some `τ` in the one-variable context `[σ]` with a library `lib` that is semantically well typed at `σ` in the empty context yields a program that never gets stuck, from any heap.
* **R6** [`encapsulation-principle`]: In the standard model, linking (call-by-value `app (lam c) lib`) a client `c` that is syntactically well typed at some `τ` in the one-variable context `[σ]` with a library `lib` that is semantically well typed at `σ` in the empty context (even if `lib` uses `cast`) yields a program that never gets stuck, from any heap.
* **R7** [`checked-read-not-syntactically-typable`]: The bounds-checked raw read `checkedRead = λ n. ifz (lt n size) 0 (read (cast n))` (i.e. if `n < size` then `read (cast n)` else `0`; `ifz` takes its first branch on `0`) has no syntactic type in any context.
* **R8** [`checked-read-semantically-typed`]: In the standard model, the bounds-checked raw read `checkedRead` is semantically well typed at `int ⇒ int` in the empty context, even though it uses the unsafe primitive.
* **R9** [`checked-read-syntactic-clients-safe`]: Every client that is syntactically well typed at some `τ` in the context `[int ⇒ int]` is safe from every heap when linked (call-by-value `app (lam c) checkedRead`) with `checkedRead`.
* **R10** [`forged-read-unsafe-and-semantically-ill-typed`]: `read (cast 7)` is not syntactically typable in any context, is not semantically well typed at any type in the empty context (standard model), and reaches a stuck configuration from the empty heap.
* **R11** [`cast-of-int-variable-has-no-semantic-type`]: For every recipe whose expression closure enforces membership of reached values in the value interpretation (`ClosureEnforcesValues`) and which has some invalid reference (`HasInvalidRef`), and in particular for the standard model, `cast x` with `x : int` is not semantically well typed in context `[int]` at any type; consequently no typing relation that derives `[int] ⊢ cast (var 0) : τ` for some `τ` is sound for the standard model.
* **R11b** [`cast-literal-safe-but-not-semantically-typed`]: For every word `n`, the literal cast `cast n` is safe from every heap, yet in the standard model it is not semantically well typed at any type in the empty context: operational safety of a closed term does not imply semantic typing.
* **R12** [`values-only-closure-breaks-adequacy`]: If the expression interpretation only requires every reached value to be in the value interpretation (`Recipe.valuesOnly`, no safety requirement), then `read (cast 7)` is semantically well typed at `int` in the empty context and yet gets stuck from the empty heap: adequacy fails.
* **R13** [`safety-only-closure-collapses-typing-to-safety`]: If the expression interpretation only requires safety (`Recipe.safetyOnly`), then an expression is semantically typed at a type `τ` in the empty context iff it is safe from every heap, independently of `τ`; in particular adequacy holds trivially for this shortcut.
* **R14** [`safety-only-closure-breaks-fundamental-theorem-and-linking`]: Under the safety-only expression interpretation (`Recipe.safetyOnly`): (1) the library `λ _. cast 7` is semantically typed at `int ⇒ ref`, the syntactically typed client `read (f 0)` is not semantically typed in `[int ⇒ ref]` (the fundamental theorem fails), and their linked program gets stuck from the empty heap (syntactic-client encapsulation fails); (2) the `cast`-free client `lt x 0` is semantically typed at `int` in `[int]` and the `cast`-free library `λ _. 0` is semantically typed at `int`, yet their linked program is not semantically typed and gets stuck (semantic let-compatibility and semantic-client linking fail).
* **R15** [`non-kripke-model-breaks-monotonicity-and-fundamental-theorem`]: If the function case quantifies only over the current world (`Recipe.nonKripke`), then `probeCellZero = λ r. (λ _. ifz (read (cast 0)) (read (cast 99)) 0) (write r 1)` is in the interpretation of `ref ⇒ int` at world 1 but not at world 2, the standard (Kripke) model rejects it already at world 1, and the syntactically typed client `f (alloc 0)` is not semantically typed in `[ref ⇒ int]` (the fundamental theorem fails); moreover the closed library `sizeGuardedProbe = ifz (lt size 2) (λ _. 0) probeCellZero` is semantically typed at `ref ⇒ int` in the empty context and its link with `f (alloc 0)` gets stuck from the heap `[0]` (closed encapsulation fails).
* **R16** [`any-location-model-breaks-fundamental-theorem`]: If every address counts as a valid reference (`Recipe.anyLoc`), the syntactically typed `λ r. read r` is not semantically typed at `ref ⇒ int` in the empty context, so the fundamental theorem fails.
* **R17** [`syntactic-value-interpretation-rejects-encapsulated-library`]: `checkedRead` is in the standard semantic interpretation of `int ⇒ int` at every world, but at no type and no world is it in the store-typed syntactic-typability interpretation `SynVal` (values typable by `HasTypeStore W []`), nor in the expression closure `safeAndIn (SynVal τ)`; so the syntactic-typability interpretation `SynVal` (and its expression closure `safeAndIn (SynVal τ)`) cannot certify this encapsulated library.
* **R18** [`kripke-monotonicity`]: In the standard model, a value in the interpretation of `τ` at world `W` remains in it at every world `W' ≥ W`.

What these results do **not** show is listed first under **Boundaries** (per-result non-claims), followed by escape hatches and open questions. In particular, nothing here is a theorem about Rust or about any real verifier; connections to real systems are separate `derived (modeling bridge)` claims. Model–system relation: none proved (adequacy and the fundamental theorem relate the package's semantic model to its own operational semantics and syntactic typing). These are statements about the toy model; they neither establish nor refute the corresponding claims about Rust, RustBelt-style verification of Rust libraries, or any other real verifier.

## Applicability

### Model fidelity (toy model)

This is a **toy model**. Its definitions are meant to capture, in the smallest setting where the phenomena appear, the semantic-typing account of "unsafe code encapsulated behind a safe interface" used by RustBelt-style verification of Rust libraries (Jung et al. 2018) and by the logical approach to type soundness of Timany et al. 2024. The precise scope:

* **Language.** Call-by-value λ-calculus with de Bruijn indices; natural-number words (`num`, standing for unsigned `usize`-like machine words); `lt` (yields `num 1` if `a < b`, else `num 0`); `ifz` ("if zero": `ifz c t e` runs `t` when `c = num 0` and `e` when `c = num (k+1)`, so `ifz (lt a b) t e` runs `t` when `a < b` is **false**); a heap of word cells (`alloc`, `read`, `write`, `size`); runtime references `loc l`; and one unsafe primitive `cast` that turns a word `n` into `loc n` with no validity check. No recursion operator, no products or sums, no deallocation.
* **Undefined behavior** is modeled as a stuck configuration: a non-value with no step (for example `read (loc l)` with `l` unallocated, applying a non-function, or a free variable). Undefined behavior is *deferred*: `cast 7` itself steps to `loc 7`; only a later `read`/`write` of an unallocated address gets stuck. (In Rust, producing a dangling reference is already undefined behavior.)
* **Semantics.** A deterministic small-step function `step : Expr → Heap → Option (Expr × Heap)`; the heap is a list of words (valid addresses `0 … length-1`); allocation appends, so the heap never shrinks.
* **Syntactic typing** `HasType`: the standard rules for the safe fragment, with **no rule for `cast`** and **no rule for `loc`**. `HasTypeStore W` adds the store-typing rule `l < W ⊢ loc l : ref` and is used only by the syntactic value interpretation `SynVal`.
* **Semantic model.** Worlds are naturals (`W` means "cells `0 … W-1` are allocated"). Types are interpreted by structural recursion. The expression interpretation is a safety (partial-correctness) interpretation over all finite execution prefixes: it does not require termination and is not step-indexed (step-indexing is unnecessary because types are interpreted by structural recursion and cells hold only words). The model is parameterized by a `Recipe` (valid references, future worlds, expression closure) so that each ingredient can be ablated.
* **Syntactic side condition.** The function case of `V` requires the body to be closed under one binder (`b.closedAt 1 = true`) so that the shifting-free substitution is capture-free. This excludes operationally safe abstractions with free variables in dead code (`V_std_rejects_open_dead_lam`: `λ x. ifz 0 x y`, i.e. `lam (ifz (num 0) (var 0) (var 1))`, is in `V std (int ⇒ int) W` for no `W`, yet applying it to any `num n` is safe from every heap).
* **Known gaps relative to real systems** (each discussed in the modeling bridge under Findings): no ownership or borrowing, no lifetimes, no deallocation, no aliasing discipline, no concurrency, no higher-order store, no recursive types, no data abstraction, no invariants on stored cell contents (worlds record only how many cells exist), no signed integers, no raw-pointer type, and no Rust validity invariants.

### Subjects and their relation

The Lean 4 toolchain `v4.34.1` is the only executed subject: every finding with basis `execution (Lean kernel check)` was obtained by building the package's Lake project with that toolchain and checking axioms with `Lean.collectAxioms`. The papers listed in `REPORT.json` are prior art: the results restate known facts (tier `T0`) or make informal remarks precise (tier `T1`) in this package's own toy vocabulary; no definitions are imported or mirrored from those papers or from any other code base. Claims about real Rust or real verifiers are never established by the Lean checks; they appear only as separately labeled `derived (modeling bridge)` claims.

### Toolchain

Lean `leanprover/lean4:v4.34.1` (core Lean only; no Mathlib; no `Std` import is needed). The Lake project in `lean/` has one `[[lean_lib]]` (`ToySemType`) and no dependencies.


## Findings

All Lean names are in namespace `Toy.SemType` (module paths `lean/ToySemType/*.lean`). Notation: `std = Recipe.std`; `|h|` = `h.length`; `b[v/0]` = `substAt 0 v b`; `e[γ]` = `substAll γ e`. Each core definition comes with fully proved intended positive and negative examples in `lean/ToySemType/Examples.lean`. A theorem named `foo_pos` / `foo_neg` there checks the definition `foo` on specific concrete inputs: `_pos` states instances where it holds (for a function, where it computes the intended result) and `_neg` instances where it fails (for a function, where it does not produce a tempting wrong result). The concrete instances are glossed below where they matter; otherwise they are only in the Lean source.

### Definitions

**Syntax** (`Syntax.lean`).

```lean
inductive Ty where
  | int | ref | arrow (σ τ : Ty)

inductive Expr where
  | var (i : Nat) | lam (b : Expr) | app (f a : Expr)
  | num (n : Nat) | lt (a b : Expr) | ifz (c t e : Expr)
  | size | alloc (a : Expr) | read (a : Expr) | write (a b : Expr)
  | loc (l : Nat)          -- runtime reference; no rule in HasType
  | cast (a : Expr)        -- the unsafe primitive; no typing rule

def Expr.isValue : Expr → Bool         -- true exactly for lam _, num _, loc _
def Expr.closedAt : Nat → Expr → Bool  -- every free de Bruijn index is < n
def Expr.castFree : Expr → Bool        -- `cast` does not occur
```

`isValue`: values of call-by-value evaluation (`isValue_pos` / `isValue_neg`). `closedAt`: closedness under `n` binders (`closedAt_pos` / `closedAt_neg`). `castFree`: "uses no unsafe primitive" (`castFree_pos` / `castFree_neg`).

**Substitution.**

```lean
def substAllAt (k : Nat) (γ : List Expr) : Expr → Expr
  | var i => if i < k then var i
             else match γ[i - k]? with
               | some v => v
               | none   => var (i - γ.length)
  | lam b => lam (substAllAt (k + 1) γ b)
  | ...   -- structural on every other constructor
def substAll (γ : List Expr) (e : Expr) : Expr := substAllAt 0 γ e   -- closing substitution
def substAt (k : Nat) (v : Expr) (e : Expr) : Expr := substAllAt k [v] e  -- β uses k = 0
```

No shifting is performed on substituted terms, so substitution is capture-free exactly when they are closed; the value interpretation only ever contains closed values. Examples: `substAt_pos`, `substAll_pos`; `substAt_neg` (an inner binder's own index is not replaced), `substAll_neg`; capture with open substituends: `substAt_open_captures` (`substAt 0 (var 0) (lam (var 1)) = lam (var 0)`).

**Operational semantics** (`Semantics.lean`).

```lean
abbrev Heap := List Nat
abbrev Config := Expr × Heap

def step : Expr → Heap → Option Config
  -- primitive rules (left-to-right call-by-value congruences otherwise;
  -- values and stuck terms give none):
  -- app (lam b) v          ⟶ substAt 0 v b              (v a value)
  -- lt (num a) (num b)     ⟶ num (if a < b then 1 else 0)
  -- ifz (num 0) t e ⟶ t ;  ifz (num (k+1)) t e ⟶ e
  -- size, h                ⟶ num h.length, h
  -- alloc (num n), h       ⟶ loc h.length, h ++ [n]
  -- read (loc l), h        ⟶ num h[l], h                only if h[l]? = some _
  -- write (loc l) (num n), h ⟶ num 0, h.set l n         only if l < h.length
  -- cast (num n), h        ⟶ loc n, h                   (no check)

inductive Reaches : Config → Config → Prop where
  | refl (c : Config) : Reaches c c
  | step {c c' d : Config} : step c.1 c.2 = some c' → Reaches c' d → Reaches c d

def Stuck (c : Config) : Prop := c.1.isValue = false ∧ step c.1 c.2 = none
def Safe (c : Config) : Prop := ∀ d, Reaches c d → ¬ Stuck d
```

Examples: `step_pos`/`step_neg`, `reaches_pos`/`reaches_neg`, `stuck_pos`/`stuck_neg`, `safe_pos`/`safe_neg`. `Safe` allows divergence. Helper: `safe_of_reaches_value` (by determinism, a configuration that reaches a value is safe).

**Syntactic typing** (`Typing.lean`).

```lean
inductive HasType : List Ty → Expr → Ty → Prop where
  | var   : Γ[i]? = some τ → HasType Γ (.var i) τ
  | lam   : HasType (σ :: Γ) b τ → HasType Γ (.lam b) (.arrow σ τ)
  | app   : HasType Γ f (.arrow σ τ) → HasType Γ a σ → HasType Γ (.app f a) τ
  | num   : HasType Γ (.num n) .int
  | lt    : HasType Γ a .int → HasType Γ b .int → HasType Γ (.lt a b) .int
  | ifz   : HasType Γ c .int → HasType Γ t τ → HasType Γ e τ → HasType Γ (.ifz c t e) τ
  | size  : HasType Γ .size .int
  | alloc : HasType Γ a .int → HasType Γ (.alloc a) .ref
  | read  : HasType Γ a .ref → HasType Γ (.read a) .int
  | write : HasType Γ a .ref → HasType Γ b .int → HasType Γ (.write a b) .int
  -- no rule for `cast`, no rule for `loc`

inductive HasTypeStore (W : Nat) : List Ty → Expr → Ty → Prop where
  -- the ten rules of HasType (with HasTypeStore W in place of HasType), plus
  | loc : l < W → HasTypeStore W Γ (.loc l) .ref
  -- still no rule for `cast`
```

`HasType` is a standard simple type system for the safe fragment (`hasType_pos` / `hasType_neg`; lemmas `HasType.castFree`: `HasType Γ e τ → e.castFree = true`; `HasType.closedAt`: `HasType Γ e τ → e.closedAt |Γ| = true`; `not_hasType_of_not_castFree`: `e.castFree = false → ¬ HasType Γ e τ`; `HasType.toStore`: `HasType Γ e τ → HasTypeStore W Γ e τ` for every `W`). `HasTypeStore W` types runtime terms under a store typing; since every cell holds a word, the store typing is just the number `W` of allocated cells (`hasTypeStore_pos`: `loc 0` and `λ _. read (loc 0)` in world 1; `hasTypeStore_neg`: `loc 1` in world 1 and `checkedRead` in every world; lemma `HasTypeStore.castFree`: `HasTypeStore W Γ e τ → e.castFree = true`).

**Semantic model** (`Model.lean`; definitions unabbreviated, doc comments condensed into `--` comments).

```lean
structure Recipe where
  refOK : Nat → Nat → Prop                              -- valid reference l in world W
  future : Nat → Nat → Prop                             -- W' is an accessible future of W
  close : (Nat → Expr → Prop) → Nat → Expr → Prop        -- expression closure

def safeAndIn (P : Nat → Expr → Prop) (W : Nat) (e : Expr) : Prop :=
  ∀ h : Heap, W ≤ h.length → ∀ e' h', Reaches (e, h) (e', h') →
    ¬ Stuck (e', h') ∧ (e'.isValue = true → P h'.length e')

def V (R : Recipe) : Ty → Nat → Expr → Prop
  | .int, _, e => ∃ n, e = .num n
  | .ref, W, e => ∃ l, e = .loc l ∧ R.refOK W l
  | .arrow σ τ, W, e => ∃ b, e = .lam b ∧ b.closedAt 1 = true ∧
      ∀ W', R.future W W' → ∀ v, V R σ W' v → R.close (V R τ) W' (substAt 0 v b)

def E (R : Recipe) (τ : Ty) : Nat → Expr → Prop := R.close (V R τ)

def G (R : Recipe) : List Ty → Nat → List Expr → Prop
  | [], _, [] => True
  | τ :: Γ, W, v :: γ => V R τ W v ∧ G R Γ W γ
  | _, _, _ => False

def SemTyped (R : Recipe) (Γ : List Ty) (e : Expr) (τ : Ty) : Prop :=
  ∀ W γ, G R Γ W γ → E R τ W (substAll γ e)

def Recipe.std : Recipe where
  refOK W l := l < W
  future W W' := W ≤ W'
  close := safeAndIn
```

**Unfolded standard model.** With `R = std`:

* `V std int W e ⟺ ∃ n, e = num n`
* `V std ref W e ⟺ ∃ l, e = loc l ∧ l < W`
* `V std (σ ⇒ τ) W e ⟺ ∃ b, e = lam b ∧ b.closedAt 1 = true ∧ ∀ W' ≥ W, ∀ v, V std σ W' v → ∀ h, W' ≤ |h| → ∀ e' h', Reaches (b[v/0], h) (e', h') → ¬ Stuck (e', h') ∧ (e'.isValue = true → V std τ |h'| e')`
* `SemTyped std Γ e τ ⟺ ∀ W γ, G std Γ W γ → ∀ h, W ≤ |h| → ∀ e' h', Reaches (e[γ], h) (e', h') → ¬ Stuck (e', h') ∧ (e'.isValue = true → V std τ |h'| e')`, where `G std Γ W γ` says `γ` has exactly one entry per context entry, each in `V std` of its type at `W`.
* `SemTyped R [] e τ ⟺ ∀ W, E R τ W e` (`semTyped_nil_iff`). The empty context does **not** force `e.closedAt 0 = true` (`semTyped_nil_open_dead_var`).

Examples: `safeAndIn_pos`/`safeAndIn_neg`, `V_std_pos`/`V_std_neg`, `E_std_pos`/`E_std_neg`, `G_pos`/`G_neg`, `semTyped_pos`/`semTyped_neg`, `std_pos`/`std_neg`. Helper facts: `V_isValue` (`V R τ W v → v.isValue = true`), `V_closed` (`V R τ W v → v.closedAt 0 = true`), `G_nil` (`G R [] W γ ↔ γ = []`), `G_singleton` (`G R [τ] W γ ↔ ∃ v, γ = [v] ∧ V R τ W v`), `semTyped_nil_iff` (above), `valuesIn_of_safeAndIn` (`safeAndIn P W e → valuesIn P W e`, with `valuesIn` defined below), `V_std_inhabited_one` (`∀ τ, ∃ v, V std τ 1 v`).

**Named properties of recipes.**

```lean
def Recipe.ClosureEnforcesValues (R : Recipe) : Prop :=
  ∀ (P : Nat → Expr → Prop) (W : Nat) (e : Expr), R.close P W e → valuesIn P W e
def Recipe.HasInvalidRef (R : Recipe) : Prop := ∃ W l, ¬ R.refOK W l
```

`ClosureEnforcesValues`: the closure forces reached values into the value predicate (`closureEnforcesValues_pos`: `std`, `nonKripke`; `closureEnforcesValues_neg`: `safetyOnly`). `HasInvalidRef`: some address is invalid in some world (`hasInvalidRef_pos`: `std`, `safetyOnly`; `hasInvalidRef_neg`: `anyLoc`).

**Ablated ("shortcut") models** (`Model.lean`; definitions unabbreviated, doc comments condensed into `--` comments).

```lean
def safeOnly (_P : Nat → Expr → Prop) (W : Nat) (e : Expr) : Prop :=
  ∀ h : Heap, W ≤ h.length → ∀ d, Reaches (e, h) d → ¬ Stuck d
def valuesIn (P : Nat → Expr → Prop) (W : Nat) (e : Expr) : Prop :=
  ∀ h : Heap, W ≤ h.length → ∀ e' h', Reaches (e, h) (e', h') →
    e'.isValue = true → P h'.length e'

def Recipe.safetyOnly : Recipe := { Recipe.std with close := safeOnly }   -- drop "values in P"
def Recipe.valuesOnly : Recipe := { Recipe.std with close := valuesIn }   -- drop "not stuck"
def Recipe.nonKripke : Recipe := { Recipe.std with future := fun W W' => W' = W }
def Recipe.anyLoc : Recipe := { Recipe.std with refOK := fun _ _ => True }

def SynVal : Ty → Nat → Expr → Prop   -- types as store-typed syntactic typability of values
  | .int, _, e => ∃ n, e = .num n
  | .ref, W, e => ∃ l, e = .loc l ∧ l < W
  | .arrow σ τ, W, e => e.isValue = true ∧ HasTypeStore W [] e (.arrow σ τ)
```

Examples: `safeOnly_pos`/`safeOnly_neg`, `safetyOnly_pos`/`safetyOnly_neg`, `valuesIn_pos`/`valuesIn_neg`, `valuesOnly_pos`/`valuesOnly_neg`, `nonKripke_pos`/`nonKripke_neg`, `anyLoc_pos`/`anyLoc_neg`; `synVal_pos` (`λ r. read r` in world 0, `loc 0` in world 1, the runtime closure `λ _. read (loc 0)` in world 1) / `synVal_neg` (`checkedRead`; `λ _. read (loc 0)` in world 0). `SynVal τ W v ↔ v.isValue = true ∧ HasTypeStore W [] v τ` at every type (`synVal_iff_isValue_and_hasTypeStore`). Lemma: `SynVal.castFree` (`SynVal τ W v → v.castFree = true`).

**Auxiliary typing relations** (used by the `cast` cards).

```lean
def withCastRootRule (Γ : List Ty) (e : Expr) (τ : Ty) : Prop :=   -- HasType + a uniform cast rule
  HasType Γ e τ ∨ ∃ a, e = .cast a ∧ τ = .ref ∧ HasType Γ a .int

inductive RestrictedCastRule : List Ty → Expr → Ty → Prop where   -- two restricted cast rules
  | refCtx {Γ : List Ty} : RestrictedCastRule (.ref :: Γ) (.cast (.num 0)) .ref
  | allocArg {Γ : List Ty} : RestrictedCastRule Γ (.cast zeroAfterAlloc) .ref
```

`zeroAfterAlloc = (λ _. 0) (alloc 0)`. Examples: `withCastRootRule_pos`/`withCastRootRule_neg`, `restrictedCastRule_pos`/`restrictedCastRule_neg`.

**Concrete programs** (`Programs.lean`).

| Name | Term | Role |
|---|---|---|
| `checkedRead` | `λ n. ifz (lt n size) 0 (read (cast n))` (if `n < size` then `read (cast n)` else `0`) | encapsulated library: bounds-checked raw read of the global heap |
| `checkedBody n` | `ifz (lt (num n) size) 0 (read (cast (num n)))` | its body at argument `n` |
| `uncheckedRead` | `λ n. read (cast n)` | the same library without the guard |
| `forgedRead` | `read (cast 7)` | unsafe closed use |
| `derefArg` | `λ r. read r` | safe dereference |
| `castSeven` | `λ _. cast 7` | returns a forged reference |
| `probeBody` | `λ _. ifz (read (cast 0)) (read (cast 99)) 0` | closed continuation |
| `probeCellZero` | `λ r. probeBody (write r 1)` | safe iff `r = loc 0` (when cell 0 holds `0`) |
| `sizeGuardedProbe` | `ifz (lt size 2) (λ _. 0) probeCellZero` | closed library: `probeCellZero` when `size < 2` |
| `callWith7` | `x 7` (free `x = var 0`) | client |
| `readResultOf0` | `read (f 0)` | client |
| `callOnFreshCell` | `f (alloc 0)` | client |
| `readCastVar` | `read (cast x)` | ill-typed client |
| `castResultClient` | `read (cast (f 0))` | ill-typed client |
| `checkedClient` | `checkedRead (f 0)` | `cast`-using client that is semantically typed |
| `allocThenRead` | `(λ r. read r) (alloc 5)` | well-typed closed program |
| `captureRef` | `(λ r. λ _. read r) (alloc 5)` | well-typed program returning a closure over a fresh cell |
| `capturedClosure` | `λ _. read (loc 0)` | its result from the empty heap |
| `cellBoundRead` | `(λ c. λ n. ifz (lt n (read c)) 0 (read (cast n))) (alloc 0)` | stateful library guarded by a stored bound |
| `sizeZeroOrForged` | `ifz size 0 (read (cast 99))` | safe from `[]`, unsafe from `[0]` |
| `zeroAfterAlloc` | `(λ _. 0) (alloc 0)` | `int` argument that allocates first |
| `omegaExpr` | `(λ x. x x) (λ x. x x)` | divergent term |

The linked program of a client `c` (whose free variable `0` is the library) and a library `lib` is `app (lam c) lib`, i.e. `let x = lib in c` under call-by-value.


### Results

Each result lists: kind, tier, and depth; the Lean statement (verbatim); a reading with the key definitions unfolded; the plain-language claim; the hypothesis ledger (`tight` means a fully proved counterexample shows that, with this hypothesis dropped and all others kept, the conclusion fails); the non-vacuity witness (a fully proved instance satisfying all hypotheses together); positive controls for the impossibility result; prior art and the basis for the tier; the design question; and the evidentiary basis. Non-claims for every result are collected under **Boundaries**. The verbatim statements of every counterexample, witness, and control named in a card are given after the card.

#### R1. Adequacy [`adequacy`]

* **Kind / tier / depth:** theorem / `T0` / `definitional`.
* **Lean name(s):** `adequacy_semTyped_nil_safe`.

```lean
-- lean/ToySemType/Results.lean:315-316
theorem adequacy_semTyped_nil_safe {e : Expr} {τ : Ty}
    (hsem : SemTyped Recipe.std [] e τ) (h : Heap) : Safe (e, h)
```

* **Unfolded reading / proof idea:** `SemTyped std [] e τ` unfolds (via `semTyped_nil_iff`, `G std [] W γ ↔ γ = []`, `substAll [] e = e`) to `∀ W h, W ≤ |h| → ∀ e' h', Reaches (e, h) (e', h') → ¬ Stuck (e', h') ∧ (e'.isValue = true → V std τ |h'| e')`. The conclusion `Safe (e, h)` is `∀ d, Reaches (e, h) d → ¬ Stuck d`, with `Stuck d ⟺ d.1.isValue = false ∧ step d.1 d.2 = none`. The proof instantiates the hypothesis at world `0`.
* **Plain claim:** In the standard model, an expression that is semantically well typed at some type in the empty typing context (`SemTyped Recipe.std [] e τ`) never reaches a stuck configuration, from any initial heap (`∀ h, Safe (e, h)`). The empty context does not require syntactic closedness `e.closedAt 0 = true`.
* **Hypothesis ledger:**
  * `hsem` — Semantic typing of `e` at `τ` in the empty context, in the standard model. — **tight**: counterexample `adequacy_semTyped_hyp_tight`.
  * `empty typing context (Γ = [] in hsem)` — Semantic typing in a non-empty context only constrains closed instances; the open term itself can be stuck. — **tight**: counterexample `adequacy_nil_ctx_hyp_tight`.
* **Non-vacuity witness:** `checkedRead (num 0)` (a closed non-value that executes the unsafe primitive) is semantically well typed at `int` in the empty context. Lean: `adequacy_nonvacuous`.
* **Prior art / tier basis:**
  * Robin Milner. "A Theory of Type Polymorphism in Programming." Journal of Computer and System Sciences 17(3):348-375, December 1978. DOI 10.1016/0022-0000(78)90014-4. (Semantic soundness in a denotational setting: well-typed expressions do not denote the error value; not a small-step operational statement.)
  * Amin Timany, Robbert Krebbers, Derek Dreyer, Lars Birkedal. "A Logical Approach to Type Soundness." Journal of the ACM 71(6), Article 40, November 2024. DOI 10.1145/3676954. Theorem 6.6 (adequacy of unary logical relations); Section 4.1 remarks that adequacy is usually almost trivial because safety is built into the definition of semantic typing.
  * Andrew W. Appel, David McAllester. "An Indexed Model of Recursive Types for Foundational Proof-Carrying Code." ACM Transactions on Programming Languages and Systems 23(5):657-683, September 2001. DOI 10.1145/504709.504712.
  * Amal Jamil Ahmed. "Semantics of Types for Mutable State." PhD thesis, Princeton University, November 2004; Princeton Computer Science Technical Report TR-713-04 (https://www.cs.princeton.edu/techreports/2004/713.pdf).
* **Design question:** Rust's safety story rests on unsafe code encapsulated behind safe interfaces: a syntactic type system rejects the unsafe primitive, but a library using it internally can still be semantically well typed, and then every safe client is safe. What is the minimal formal content of semantic typing + adequacy + fundamental theorem, and which tempting shortcuts fail? (Adequacy is the cheap ingredient once safety is part of the expression interpretation.)
* **Non-claims:** see **Boundaries**, item R1.

Basis: execution (Lean kernel check) — the statement(s) above and every witness below build without `sorry` and use no axioms other than `propext` and `Quot.sound` (per-declaration lists in **Evidence**).

Verbatim statements of the counterexamples, witnesses, and controls named above:

```lean
-- lean/ToySemType/Results.lean:828-829
theorem adequacy_semTyped_hyp_tight :
    (∀ τ, ¬ SemTyped Recipe.std [] forgedRead τ) ∧ ¬ Safe (forgedRead, [])

-- lean/ToySemType/Results.lean:835-837
theorem adequacy_nil_ctx_hyp_tight :
    HasType [.int] (.var 0) .int ∧ SemTyped Recipe.std [.int] (.var 0) .int ∧
    ¬ Safe (.var 0, [])

-- lean/ToySemType/Results.lean:1061
theorem adequacy_nonvacuous : SemTyped Recipe.std [] (.app checkedRead (.num 0)) .int
```

#### R2. Fundamental theorem [`fundamental-theorem`]

* **Kind / tier / depth:** theorem / `T0` / `substantive`.
* **Lean name(s):** `fundamental_hasType_semTyped`.

```lean
-- lean/ToySemType/Results.lean:321-322
theorem fundamental_hasType_semTyped {Γ : List Ty} {e : Expr} {τ : Ty}
    (hty : HasType Γ e τ) : SemTyped Recipe.std Γ e τ
```

* **Unfolded reading / proof idea:** If `HasType Γ e τ` (the ten syntactic rules; none for `cast` or `loc`), then `∀ W γ, G std Γ W γ → ∀ h, W ≤ |h| → ∀ e' h', Reaches (e[γ], h) (e', h') → ¬ Stuck (e', h') ∧ (e'.isValue = true → V std τ |h'| e')`. Proof: induction on the typing derivation with one compatibility argument per rule, using Kripke monotonicity (R18) lifted to `G`, heap growth under `step`, an evaluation-context bind lemma for `Reaches` (`bind_goodFrom`), closedness of `substAllAt 1 γ b` for typed `b` and closed `γ` (`closedAt_substAllAt`), and the substitution composition `substAt 0 v (substAllAt 1 γ b) = substAll (v :: γ) b` for closed `γ` (`substAllAt_comp_cons`).
* **Plain claim:** Every expression that is syntactically well typed in a context `Γ` at type `τ` (`HasType Γ e τ`) is semantically well typed in `Γ` at `τ` in the standard model (`SemTyped Recipe.std Γ e τ`).
* **Hypothesis ledger:**
  * `hty` — Syntactic typing; in particular `e` contains no `cast` and no runtime reference literal. — **tight**: counterexample `fundamental_hasType_hyp_tight`.
* **Non-vacuity witness:** `HasType [] ((λ r. read r) (alloc 5)) int` and `HasType [int ⇒ int] (x 7) int`. Lean: `fundamental_nonvacuous`.
* **Prior art / tier basis:**
  * Amin Timany, Robbert Krebbers, Derek Dreyer, Lars Birkedal. "A Logical Approach to Type Soundness." Journal of the ACM 71(6), Article 40, November 2024. DOI 10.1145/3676954. Theorem 6.5 (fundamental theorem of unary logical relations), proved from semantic typing rules (compatibility lemmas).
  * Coq development accompanying Timany et al. 2024 (https://gitlab.mpi-sws.org/iris/examples, directory theories/logrel/F_mu_ref_conc); per the article it mechanizes the semantic type soundness proof (Sections 5-6) and the proofs that the symbol ADT is semantically well typed and gremlin is not (Section 7).
  * Andrew M. Pitts. "Typed Operational Reasoning." In B. C. Pierce (ed.), Advanced Topics in Types and Programming Languages, Chapter 7, pp. 245-289. MIT Press, 2005. ISBN 978-0-262-16228-9. Author copy: https://www.cl.cam.ac.uk/~amp12/papers/typor/typor.pdf.
  * Amal Jamil Ahmed. "Semantics of Types for Mutable State." PhD thesis, Princeton University, November 2004; Princeton Computer Science Technical Report TR-713-04 (https://www.cs.princeton.edu/techreports/2004/713.pdf).
  * Andrew W. Appel, David McAllester. "An Indexed Model of Recursive Types for Foundational Proof-Carrying Code." ACM Transactions on Programming Languages and Systems 23(5):657-683, September 2001. DOI 10.1145/504709.504712.
  * Jeremy Siek. "Declarative Semantics for Functional Languages." Archive of Formal Proofs, July 2017 (https://www.isa-afp.org/entries/Decl_Sem_Fun_PL.html). Isabelle/HOL; case studies include semantic type soundness for a polymorphic lambda-calculus with general recursion and an adaptation to a call-by-value lambda-calculus with mutable references.
  * Yuquan Fu, Carlo Angiuli, Sam Tobin-Hochstadt. "Revisiting Soundness for Occurrence Typing, Semantically." arXiv:2609.16299, 2026. (Semantic type soundness via step-indexed logical relations, formalized in Lean.)
* **Design question:** Rust's safety story rests on unsafe code encapsulated behind safe interfaces: a syntactic type system rejects the unsafe primitive, but a library using it internally can still be semantically well typed, and then every safe client is safe. What is the minimal formal content of semantic typing + adequacy + fundamental theorem, and which tempting shortcuts fail? (The obligation a verification framework discharges once, for the safe fragment, so that safe code needs no per-program proofs.)
* **Non-claims:** see **Boundaries**, item R2.

Basis: execution (Lean kernel check) — the statement(s) above and every witness below build without `sorry` and use no axioms other than `propext` and `Quot.sound` (per-declaration lists in **Evidence**).

Verbatim statements of the counterexamples, witnesses, and controls named above:

```lean
-- lean/ToySemType/Results.lean:848-850
theorem fundamental_hasType_hyp_tight :
    (∀ Γ τ, ¬ HasType Γ uncheckedRead τ) ∧
    ¬ SemTyped Recipe.std [] uncheckedRead (.arrow .int .int)

-- lean/ToySemType/Results.lean:1066-1067
theorem fundamental_nonvacuous :
    HasType [] allocThenRead .int ∧ HasType [.arrow .int .int] callWith7 .int
```

#### R3. Syntactic type safety (corollary) [`syntactic-type-safety-corollary`]

* **Kind / tier / depth:** theorem / `T0` / `shallow`.
* **Lean name(s):** `hasType_closed_safe`.

```lean
-- lean/ToySemType/Results.lean:455-456
theorem hasType_closed_safe {e : Expr} {τ : Ty} (hty : HasType [] e τ) (h : Heap) :
    Safe (e, h)
```

* **Unfolded reading / proof idea:** `HasType [] e τ → ∀ h, ∀ d, Reaches (e, h) d → ¬ Stuck d`. The Lean proof is the term `adequacy_semTyped_nil_safe (fundamental_hasType_semTyped hty) h`.
* **Plain claim:** A syntactically well-typed expression in the empty context (`HasType [] e τ`, which also makes `e` closed) never gets stuck, from any initial heap; derived from adequacy and the fundamental theorem.
* **Hypothesis ledger:**
  * `hty` — Syntactic typing in the empty context. — **tight**: counterexample `forgedRead_unsafe_ill_typed`.
  * `empty typing context (Γ = [] in hty)` — An open well-typed term is stuck as a program. — **tight**: counterexample `adequacy_nil_ctx_hyp_tight`.
* **Non-vacuity witness:** `HasType [] ((λ r. read r) (alloc 5)) int`. Lean: `fundamental_nonvacuous`.
* **Prior art / tier basis:**
  * Andrew K. Wright, Matthias Felleisen. "A Syntactic Approach to Type Soundness." Information and Computation 115(1):38-94, November 1994. DOI 10.1006/inco.1994.1093.
  * Amin Timany, Robbert Krebbers, Derek Dreyer, Lars Birkedal. "A Logical Approach to Type Soundness." Journal of the ACM 71(6), Article 40, November 2024. DOI 10.1145/3676954. Corollary 6.7 (semantic type soundness implies safety of closed well-typed programs) and footnote 7 (it does not imply preservation).
* **Design question:** Rust's safety story rests on unsafe code encapsulated behind safe interfaces: a syntactic type system rejects the unsafe primitive, but a library using it internally can still be semantically well typed, and then every safe client is safe. What is the minimal formal content of semantic typing + adequacy + fundamental theorem, and which tempting shortcuts fail? (Reference point (corollary): syntactic safety is the special case without unsafe code; it says nothing about libraries such as `checkedRead`.)
* **Non-claims:** see **Boundaries**, item R3.

Basis: execution (Lean kernel check) — the statement(s) above and every witness below build without `sorry` and use no axioms other than `propext` and `Quot.sound` (per-declaration lists in **Evidence**).

Verbatim statements of the counterexamples, witnesses, and controls named above:

```lean
-- lean/ToySemType/Results.lean:500-502
theorem forgedRead_unsafe_ill_typed :
    (∀ Γ τ, ¬ HasType Γ forgedRead τ) ∧ (∀ τ, ¬ SemTyped Recipe.std [] forgedRead τ) ∧
    ¬ Safe (forgedRead, [])

-- lean/ToySemType/Results.lean:835-837
theorem adequacy_nil_ctx_hyp_tight :
    HasType [.int] (.var 0) .int ∧ SemTyped Recipe.std [.int] (.var 0) .int ∧
    ¬ Safe (.var 0, [])

-- lean/ToySemType/Results.lean:1066-1067
theorem fundamental_nonvacuous :
    HasType [] allocThenRead .int ∧ HasType [.arrow .int .int] callWith7 .int
```

#### R4. Semantic let-compatibility (linking) [`semantic-let-compatibility`]

* **Kind / tier / depth:** theorem / `T0` / `substantive`.
* **Lean name(s):** `semTyped_let_compat`.

```lean
-- lean/ToySemType/Results.lean:431-433
theorem semTyped_let_compat {Γ : List Ty} {σ τ : Ty} {c lib : Expr}
    (hc : SemTyped Recipe.std (σ :: Γ) c τ) (hlib : SemTyped Recipe.std Γ lib σ) :
    SemTyped Recipe.std Γ (.app (.lam c) lib) τ
```

* **Unfolded reading / proof idea:** For all `W γ` with `G std Γ W γ` and all `h` with `W ≤ |h|`, every configuration reachable from `((app (lam c) lib)[γ], h) = (app (lam (substAllAt 1 γ c)) (lib[γ]), h)` is not stuck, and every value reached is in `V std τ` at the then-current heap size. Proof: the bind lemma runs `lib[γ]` to a value `v ∈ V std σ |h₁|` with `|h| ≤ |h₁|`; one β-step gives `c[v :: γ]`; `G std Γ` is lifted from `W` to `|h₁|` by monotonicity; `hc` finishes. It does not go through R2 or through a semantic `lam` rule.
* **Plain claim:** In the standard model, if a client `c` is semantically well typed at `τ` in context `σ :: Γ` (`SemTyped Recipe.std (σ :: Γ) c τ`) and a library expression `lib` is semantically well typed at `σ` in context `Γ` (`SemTyped Recipe.std Γ lib σ`), then the call-by-value linked program `app (lam c) lib` is semantically well typed at `τ` in context `Γ`; neither piece needs to be syntactically typable.
* **Hypothesis ledger:**
  * `hc` — Semantic typing of the client under the library variable. — **tight**: counterexample `client_hyp_tight`.
  * `hlib` — Semantic typing of the library expression. — **tight**: counterexample `lib_hyp_tight`.
* **Non-vacuity witness:** Client `x 7` is semantically typed in `[int ⇒ int]`, and `checkedRead` (which uses `cast`) is semantically typed at `int ⇒ int` in the empty context. Lean: `semTyped_let_compat_nonvacuous`.
* **Prior art / tier basis:**
  * Amin Timany, Robbert Krebbers, Derek Dreyer, Lars Birkedal. "A Logical Approach to Type Soundness." Journal of the ACM 71(6), Article 40, November 2024. DOI 10.1145/3676954. Sections 4.1 and 6 (semantic typing rules, a.k.a. compatibility lemmas).
  * Andrew M. Pitts. "Typed Operational Reasoning." In B. C. Pierce (ed.), Advanced Topics in Types and Programming Languages, Chapter 7, pp. 245-289. MIT Press, 2005. ISBN 978-0-262-16228-9. Author copy: https://www.cl.cam.ac.uk/~amp12/papers/typor/typor.pdf.
  * Ralf Jung, Jacques-Henri Jourdan, Robbert Krebbers, Derek Dreyer. "RustBelt: Securing the Foundations of the Rust Programming Language." Proceedings of the ACM on Programming Languages 2(POPL), Article 66, January 2018. DOI 10.1145/3158154. Coq development: https://gitlab.mpi-sws.org/iris/lambda-rust.
* **Design question:** Rust's safety story rests on unsafe code encapsulated behind safe interfaces: a syntactic type system rejects the unsafe primitive, but a library using it internally can still be semantically well typed, and then every safe client is safe. What is the minimal formal content of semantic typing + adequacy + fundamental theorem, and which tempting shortcuts fail? (Compositionality: verify an unsafe library once, then link it with arbitrary semantically typed clients.)
* **Non-claims:** see **Boundaries**, item R4.

Basis: execution (Lean kernel check) — the statement(s) above and every witness below build without `sorry` and use no axioms other than `propext` and `Quot.sound` (per-declaration lists in **Evidence**).

Basis: derived (modeling bridge) — Compositional verification in RustBelt-style frameworks rests on the same shape of lemma (semantic typing rules / compatibility lemmas proved once and composed). The toy lemma establishes this shape only for call-by-value `let`-linking in a model whose worlds count allocated cells; it does not transfer the guarantee to Rust, whose models need ownership, lifetimes, and invariants on stored data (see the modeling bridge).

Verbatim statements of the counterexamples, witnesses, and controls named above:

```lean
-- lean/ToySemType/Results.lean:863-868
theorem client_hyp_tight :
    (∀ τ, ¬ HasType [.int] readCastVar τ) ∧
    (∀ τ, ¬ SemTyped Recipe.std [.int] readCastVar τ) ∧
    SemTyped Recipe.std [] (.num 7) .int ∧
    ¬ SemTyped Recipe.std [] (.app (.lam readCastVar) (.num 7)) .int ∧
    ¬ Safe (.app (.lam readCastVar) (.num 7), [])

-- lean/ToySemType/Results.lean:922-927
theorem lib_hyp_tight :
    HasType [.arrow .int .int] callWith7 .int ∧
    SemTyped Recipe.std [.arrow .int .int] callWith7 .int ∧
    (∀ σ, ¬ SemTyped Recipe.std [] uncheckedRead σ) ∧
    ¬ SemTyped Recipe.std [] (.app (.lam callWith7) uncheckedRead) .int ∧
    ¬ Safe (.app (.lam callWith7) uncheckedRead, [])

-- lean/ToySemType/Results.lean:1072-1074
theorem semTyped_let_compat_nonvacuous :
    SemTyped Recipe.std [.arrow .int .int] callWith7 .int ∧
    SemTyped Recipe.std [] checkedRead (.arrow .int .int)
```

#### R5. Linking safety, semantic client [`linking-safety-semantic-client`]

* **Kind / tier / depth:** theorem / `T0` / `shallow`.
* **Lean name(s):** `semTyped_client_semTyped_lib_safe`.

```lean
-- lean/ToySemType/Results.lean:463-465
theorem semTyped_client_semTyped_lib_safe {σ τ : Ty} {c lib : Expr}
    (hc : SemTyped Recipe.std [σ] c τ) (hlib : SemTyped Recipe.std [] lib σ) (h : Heap) :
    Safe (.app (.lam c) lib, h)
```

* **Unfolded reading / proof idea:** `SemTyped std [σ] c τ → SemTyped std [] lib σ → ∀ h, ∀ d, Reaches (app (lam c) lib, h) d → ¬ Stuck d`. The Lean proof is the term `adequacy_semTyped_nil_safe (semTyped_let_compat hc hlib) h`.
* **Plain claim:** In the standard model, linking (call-by-value `app (lam c) lib`) a client `c` that is semantically well typed at some `τ` in the one-variable context `[σ]` with a library `lib` that is semantically well typed at `σ` in the empty context yields a program that never gets stuck, from any heap.
* **Hypothesis ledger:**
  * `hc` — Semantic typing of the client in the context `[σ]`. — **tight**: counterexample `client_hyp_tight`.
  * `hlib` — Semantic typing of the library in the empty context. — **tight**: counterexample `lib_hyp_tight`.
  * `client context is exactly the library variable ([σ])` — With more client variables than the linking binds, the linked program is open and stuck. — **tight**: counterexample `linking_single_var_ctx_tight`.
  * `library typed in the empty context ([])` — A library typed only in a non-empty context may be an open term, and the linked program is stuck. — **tight**: counterexample `linking_lib_nil_ctx_tight`.
  * `matching interface type (the same σ in hc and hlib)` — A client expecting a `ref` linked with a library typed at `int` gets stuck. — **tight**: counterexample `linking_interface_match_tight`.
* **Non-vacuity witness:** Client `x 7` (semantically typed in `[int ⇒ int]`) and library `checkedRead`. Lean: `semTyped_let_compat_nonvacuous`, `linking_structure_nonvacuous`.
* **Prior art / tier basis:**
  * Amin Timany, Robbert Krebbers, Derek Dreyer, Lars Birkedal. "A Logical Approach to Type Soundness." Journal of the ACM 71(6), Article 40, November 2024. DOI 10.1145/3676954. Section 3.2 (safe encapsulation of unsafe features, with an assert-based symbol ADT) and Section 7.
  * Ralf Jung, Jacques-Henri Jourdan, Robbert Krebbers, Derek Dreyer. "RustBelt: Securing the Foundations of the Rust Programming Language." Proceedings of the ACM on Programming Languages 2(POPL), Article 66, January 2018. DOI 10.1145/3158154. Coq development: https://gitlab.mpi-sws.org/iris/lambda-rust.
* **Design question:** Rust's safety story rests on unsafe code encapsulated behind safe interfaces: a syntactic type system rejects the unsafe primitive, but a library using it internally can still be semantically well typed, and then every safe client is safe. What is the minimal formal content of semantic typing + adequacy + fundamental theorem, and which tempting shortcuts fail? (Reference point: the minimal-hypothesis form of the encapsulation principle. The client side of the contract need only be semantic; e.g. `checkedRead (f 0)`, which uses `cast` and has no syntactic type, is a semantically typed client (`checkedClient_semTyped_safe_not_hasType`).)
* **Non-claims:** see **Boundaries**, item R5.

Basis: execution (Lean kernel check) — the statement(s) above and every witness below build without `sorry` and use no axioms other than `propext` and `Quot.sound` (per-declaration lists in **Evidence**).

Verbatim statements of the counterexamples, witnesses, and controls named above:

```lean
-- lean/ToySemType/Results.lean:863-868
theorem client_hyp_tight :
    (∀ τ, ¬ HasType [.int] readCastVar τ) ∧
    (∀ τ, ¬ SemTyped Recipe.std [.int] readCastVar τ) ∧
    SemTyped Recipe.std [] (.num 7) .int ∧
    ¬ SemTyped Recipe.std [] (.app (.lam readCastVar) (.num 7)) .int ∧
    ¬ Safe (.app (.lam readCastVar) (.num 7), [])

-- lean/ToySemType/Results.lean:922-927
theorem lib_hyp_tight :
    HasType [.arrow .int .int] callWith7 .int ∧
    SemTyped Recipe.std [.arrow .int .int] callWith7 .int ∧
    (∀ σ, ¬ SemTyped Recipe.std [] uncheckedRead σ) ∧
    ¬ SemTyped Recipe.std [] (.app (.lam callWith7) uncheckedRead) .int ∧
    ¬ Safe (.app (.lam callWith7) uncheckedRead, [])

-- lean/ToySemType/Results.lean:938-940
theorem linking_single_var_ctx_tight :
    HasType [.int, .int] (.var 1) .int ∧ SemTyped Recipe.std [.int, .int] (.var 1) .int ∧
    SemTyped Recipe.std [] (.num 7) .int ∧ ¬ Safe (.app (.lam (.var 1)) (.num 7), [])

-- lean/ToySemType/Results.lean:952-954
theorem linking_lib_nil_ctx_tight :
    HasType [.int] (.var 0) .int ∧ SemTyped Recipe.std [.int] (.var 0) .int ∧
    ¬ Safe (.app (.lam (.var 0)) (.var 0), [])

-- lean/ToySemType/Results.lean:961-963
theorem linking_interface_match_tight :
    HasType [.ref] (.read (.var 0)) .int ∧ SemTyped Recipe.std [.ref] (.read (.var 0)) .int ∧
    SemTyped Recipe.std [] (.num 7) .int ∧ ¬ Safe (.app (.lam (.read (.var 0))) (.num 7), [])

-- lean/ToySemType/Results.lean:1072-1074
theorem semTyped_let_compat_nonvacuous :
    SemTyped Recipe.std [.arrow .int .int] callWith7 .int ∧
    SemTyped Recipe.std [] checkedRead (.arrow .int .int)

-- lean/ToySemType/Results.lean:1117-1118
theorem linking_structure_nonvacuous :
    HasType [.arrow .int .int] callWith7 .int ∧ (Expr.closedAt 0 checkedRead = true)
```

#### R6. Encapsulation principle [`encapsulation-principle`]

* **Kind / tier / depth:** theorem / `T0` / `shallow`.
* **Lean name(s):** `hasType_client_semTyped_lib_safe`.

```lean
-- lean/ToySemType/Results.lean:472-474
theorem hasType_client_semTyped_lib_safe {σ τ : Ty} {c lib : Expr}
    (hc : HasType [σ] c τ) (hlib : SemTyped Recipe.std [] lib σ) (h : Heap) :
    Safe (.app (.lam c) lib, h)
```

* **Unfolded reading / proof idea:** `HasType [σ] c τ → SemTyped std [] lib σ → ∀ h, ∀ d, Reaches (app (lam c) lib, h) d → ¬ Stuck d`, where `lib` may contain `cast`. The Lean proof is the term `semTyped_client_semTyped_lib_safe (fundamental_hasType_semTyped hc) hlib h`.
* **Plain claim:** In the standard model, linking (call-by-value `app (lam c) lib`) a client `c` that is syntactically well typed at some `τ` in the one-variable context `[σ]` with a library `lib` that is semantically well typed at `σ` in the empty context (even if `lib` uses `cast`) yields a program that never gets stuck, from any heap.
* **Hypothesis ledger:**
  * `hc` — Syntactic typing of the client; can be weakened to semantic typing (`semTyped_client_semTyped_lib_safe`). — **tight**: counterexample `client_hyp_tight`.
  * `hlib` — Semantic typing of the library in the empty context. — **tight**: counterexample `lib_hyp_tight`.
  * `client context is exactly the library variable ([σ])` — With more client variables than the linking binds, the linked program is open and stuck. — **tight**: counterexample `linking_single_var_ctx_tight`.
  * `library typed in the empty context ([])` — A library typed only in a non-empty context may be an open term, and the linked program is stuck. — **tight**: counterexample `linking_lib_nil_ctx_tight`.
  * `matching interface type (the same σ in hc and hlib)` — A client expecting a `ref` linked with a library typed at `int` gets stuck. — **tight**: counterexample `linking_interface_match_tight`.
* **Non-vacuity witness:** Client `x 7` (syntactically typed in `[int ⇒ int]`) and library `checkedRead`. Lean: `hasType_client_semTyped_lib_nonvacuous`, `linking_structure_nonvacuous`.
* **Prior art / tier basis:**
  * Ralf Jung, Jacques-Henri Jourdan, Robbert Krebbers, Derek Dreyer. "RustBelt: Securing the Foundations of the Rust Programming Language." Proceedings of the ACM on Programming Languages 2(POPL), Article 66, January 2018. DOI 10.1145/3158154. Coq development: https://gitlab.mpi-sws.org/iris/lambda-rust.
  * Ralf Jung. "Understanding and Evolving the Rust Programming Language." PhD thesis, Saarland University, 2020. DOI 10.22028/D291-31946.
  * Amin Timany, Robbert Krebbers, Derek Dreyer, Lars Birkedal. "A Logical Approach to Type Soundness." Journal of the ACM 71(6), Article 40, November 2024. DOI 10.1145/3676954. Sections 3.2 and 7.
  * Coq development accompanying Timany et al. 2024 (https://gitlab.mpi-sws.org/iris/examples, directory theories/logrel/F_mu_ref_conc); per the article it mechanizes the semantic type soundness proof (Sections 5-6) and the proofs that the symbol ADT is semantically well typed and gremlin is not (Section 7).
* **Design question:** Rust's safety story rests on unsafe code encapsulated behind safe interfaces: a syntactic type system rejects the unsafe primitive, but a library using it internally can still be semantically well typed, and then every safe client is safe. What is the minimal formal content of semantic typing + adequacy + fundamental theorem, and which tempting shortcuts fail? (The exact statement a Rust-style verification framework aims for.)
* **Non-claims:** see **Boundaries**, item R6.

Basis: execution (Lean kernel check) — the statement(s) above and every witness below build without `sorry` and use no axioms other than `propext` and `Quot.sound` (per-declaration lists in **Evidence**).

Basis: derived (modeling bridge) — This is the toy form of the statement RustBelt-style frameworks aim for: a library whose implementation uses unsafe operations, once shown semantically well typed at its interface type, is safe to use from any client the safe type system accepts. The inference to Rust holds only to the extent that the real semantic model has the ingredients shown necessary here (safety plus value membership in the expression interpretation, future-world quantification, a non-trivial validity predicate for references) and the additional ones this toy omits; it is reasoning by analogy, not a theorem about Rust.

Verbatim statements of the counterexamples, witnesses, and controls named above:

```lean
-- lean/ToySemType/Results.lean:863-868
theorem client_hyp_tight :
    (∀ τ, ¬ HasType [.int] readCastVar τ) ∧
    (∀ τ, ¬ SemTyped Recipe.std [.int] readCastVar τ) ∧
    SemTyped Recipe.std [] (.num 7) .int ∧
    ¬ SemTyped Recipe.std [] (.app (.lam readCastVar) (.num 7)) .int ∧
    ¬ Safe (.app (.lam readCastVar) (.num 7), [])

-- lean/ToySemType/Results.lean:922-927
theorem lib_hyp_tight :
    HasType [.arrow .int .int] callWith7 .int ∧
    SemTyped Recipe.std [.arrow .int .int] callWith7 .int ∧
    (∀ σ, ¬ SemTyped Recipe.std [] uncheckedRead σ) ∧
    ¬ SemTyped Recipe.std [] (.app (.lam callWith7) uncheckedRead) .int ∧
    ¬ Safe (.app (.lam callWith7) uncheckedRead, [])

-- lean/ToySemType/Results.lean:938-940
theorem linking_single_var_ctx_tight :
    HasType [.int, .int] (.var 1) .int ∧ SemTyped Recipe.std [.int, .int] (.var 1) .int ∧
    SemTyped Recipe.std [] (.num 7) .int ∧ ¬ Safe (.app (.lam (.var 1)) (.num 7), [])

-- lean/ToySemType/Results.lean:952-954
theorem linking_lib_nil_ctx_tight :
    HasType [.int] (.var 0) .int ∧ SemTyped Recipe.std [.int] (.var 0) .int ∧
    ¬ Safe (.app (.lam (.var 0)) (.var 0), [])

-- lean/ToySemType/Results.lean:961-963
theorem linking_interface_match_tight :
    HasType [.ref] (.read (.var 0)) .int ∧ SemTyped Recipe.std [.ref] (.read (.var 0)) .int ∧
    SemTyped Recipe.std [] (.num 7) .int ∧ ¬ Safe (.app (.lam (.read (.var 0))) (.num 7), [])

-- lean/ToySemType/Results.lean:1079-1081
theorem hasType_client_semTyped_lib_nonvacuous :
    HasType [.arrow .int .int] callWith7 .int ∧
    SemTyped Recipe.std [] checkedRead (.arrow .int .int)

-- lean/ToySemType/Results.lean:1117-1118
theorem linking_structure_nonvacuous :
    HasType [.arrow .int .int] callWith7 .int ∧ (Expr.closedAt 0 checkedRead = true)
```

#### R7. The encapsulated library is not syntactically typable [`checked-read-not-syntactically-typable`]

* **Kind / tier / depth:** theorem / `T0` / `shallow`.
* **Lean name(s):** `checkedRead_not_hasType`.

```lean
-- lean/ToySemType/Results.lean:481
theorem checkedRead_not_hasType (Γ : List Ty) (τ : Ty) : ¬ HasType Γ checkedRead τ
```

* **Unfolded reading / proof idea:** `checkedRead = lam (ifz (lt (var 0) size) (num 0) (read (cast (var 0))))`; the statement is `∀ Γ τ, ¬ HasType Γ checkedRead τ`. Proof: `checkedRead.castFree = false` and every `HasType` derivation is `cast`-free (`not_hasType_of_not_castFree`).
* **Plain claim:** The bounds-checked raw read `checkedRead = λ n. ifz (lt n size) 0 (read (cast n))` (i.e. if `n < size` then `read (cast n)` else `0`; `ifz` takes its first branch on `0`) has no syntactic type in any context.
* **Hypothesis ledger:** no hypotheses (a closed statement about concrete terms or models).
* **Non-vacuity witness:** No hypotheses; `checkedRead` is a meaningful executable library (`checkedRead_applied_semTyped`). Lean: `checkedRead_applied_semTyped`.
* **Prior art / tier basis:**
  * Amin Timany, Robbert Krebbers, Derek Dreyer, Lars Birkedal. "A Logical Approach to Type Soundness." Journal of the ACM 71(6), Article 40, November 2024. DOI 10.1145/3676954. Section 3.2: the symbol ADT is not syntactically well typed because it uses the unsafe assert expression (the analogue of this statement).
* **Design question:** Rust's safety story rests on unsafe code encapsulated behind safe interfaces: a syntactic type system rejects the unsafe primitive, but a library using it internally can still be semantically well typed, and then every safe client is safe. What is the minimal formal content of semantic typing + adequacy + fundamental theorem, and which tempting shortcuts fail? (Witnesses that the syntactic system rejects the encapsulated library outright.)
* **Non-claims:** see **Boundaries**, item R7.

Basis: execution (Lean kernel check) — the statement(s) above and every witness below build without `sorry` and use no axioms other than `propext` and `Quot.sound` (per-declaration lists in **Evidence**).

Verbatim statements of the counterexamples, witnesses, and controls named above:

```lean
-- lean/ToySemType/Concrete.lean:51-52
theorem checkedRead_applied_semTyped (n : Nat) :
    SemTyped Recipe.std [] (.app checkedRead (.num n)) .int
```

#### R8. The encapsulated library is semantically well typed [`checked-read-semantically-typed`]

* **Kind / tier / depth:** theorem / `T0` / `shallow`.
* **Lean name(s):** `checkedRead_semTyped`.

```lean
-- lean/ToySemType/Concrete.lean:45
theorem checkedRead_semTyped : SemTyped Recipe.std [] checkedRead (.arrow .int .int)
```

* **Unfolded reading / proof idea:** `∀ W h, W ≤ |h| → checkedRead ∈ V std (int ⇒ int) |h|`, i.e. `∀ W' ≥ |h|, ∀ n, ∀ h', W' ≤ |h'| →` every configuration reachable from `(ifz (lt (num n) size) (num 0) (read (cast (num n))), h')` is not stuck and every value reached is a word (`checkedBody_good`, `checkedRead_V`).
* **Plain claim:** In the standard model, the bounds-checked raw read `checkedRead` is semantically well typed at `int ⇒ int` in the empty context, even though it uses the unsafe primitive.
* **Hypothesis ledger:** no hypotheses (a closed statement about concrete terms or models).
* **Non-vacuity witness:** No hypotheses; `checkedRead (num n)` is semantically typed at `int` for every `n`. Lean: `checkedRead_applied_semTyped`.
* **Prior art / tier basis:**
  * Amin Timany, Robbert Krebbers, Derek Dreyer, Lars Birkedal. "A Logical Approach to Type Soundness." Journal of the ACM 71(6), Article 40, November 2024. DOI 10.1145/3676954. Theorem 7.1 (the symbol ADT, which uses assert, is semantically well typed); the symbol ADT relies on an invariant about a private counter, which this model cannot express.
  * Coq development accompanying Timany et al. 2024 (https://gitlab.mpi-sws.org/iris/examples, directory theories/logrel/F_mu_ref_conc); per the article it mechanizes the semantic type soundness proof (Sections 5-6) and the proofs that the symbol ADT is semantically well typed and gremlin is not (Section 7).
  * Ralf Jung, Jacques-Henri Jourdan, Robbert Krebbers, Derek Dreyer. "RustBelt: Securing the Foundations of the Rust Programming Language." Proceedings of the ACM on Programming Languages 2(POPL), Article 66, January 2018. DOI 10.1145/3158154. Coq development: https://gitlab.mpi-sws.org/iris/lambda-rust.
* **Design question:** Rust's safety story rests on unsafe code encapsulated behind safe interfaces: a syntactic type system rejects the unsafe primitive, but a library using it internally can still be semantically well typed, and then every safe client is safe. What is the minimal formal content of semantic typing + adequacy + fundamental theorem, and which tempting shortcuts fail? (A concrete instance of 'unsafe inside, safe interface' that the syntactic system rejects.)
* **Non-claims:** see **Boundaries**, item R8.

Basis: execution (Lean kernel check) — the statement(s) above and every witness below build without `sorry` and use no axioms other than `propext` and `Quot.sound` (per-declaration lists in **Evidence**).

Basis: derived (modeling bridge) — A Rust library that wraps an unchecked access behind a dynamic bounds check is the real-world pattern this mirrors. The toy check compares with the primitive heap size on every call; a real library typically relies on an invariant over its own state (a stored length), which this model cannot express (`cellBoundRead_not_semTyped`), so this card does not show that any particular Rust library is sound.

Verbatim statements of the counterexamples, witnesses, and controls named above:

```lean
-- lean/ToySemType/Concrete.lean:51-52
theorem checkedRead_applied_semTyped (n : Nat) :
    SemTyped Recipe.std [] (.app checkedRead (.num n)) .int
```

#### R9. Every syntactically typed client of the library is safe [`checked-read-syntactic-clients-safe`]

* **Kind / tier / depth:** theorem / `T0` / `shallow`.
* **Lean name(s):** `checkedRead_hasType_clients_safe`.

```lean
-- lean/ToySemType/Results.lean:486-488
theorem checkedRead_hasType_clients_safe {τ : Ty} {c : Expr}
    (hc : HasType [.arrow .int .int] c τ) (h : Heap) :
    Safe (.app (.lam c) checkedRead, h)
```

* **Unfolded reading / proof idea:** `HasType [int ⇒ int] c τ → ∀ h, ∀ d, Reaches (app (lam c) checkedRead, h) d → ¬ Stuck d`. The Lean proof is the term `hasType_client_semTyped_lib_safe hc checkedRead_semTyped h`.
* **Plain claim:** Every client that is syntactically well typed at some `τ` in the context `[int ⇒ int]` is safe from every heap when linked (call-by-value `app (lam c) checkedRead`) with `checkedRead`.
* **Hypothesis ledger:**
  * `hc` — Syntactic typing of the client in `[int ⇒ int]`. Not minimal: it can be weakened to `SemTyped Recipe.std [int ⇒ int] c τ` (via `semTyped_client_semTyped_lib_safe` and `checkedRead_semTyped`); `checkedClient_semTyped_safe_not_hasType` exhibits a `cast`-using client that is semantically typed and safe. — **tight**: counterexample `checkedRead_client_hyp_tight`.
  * `client context is exactly the library variable ([int ⇒ int])` — A client with a second free variable is open after linking and gets stuck. — **tight**: counterexample `checkedRead_single_var_ctx_tight`.
* **Non-vacuity witness:** Client `x 7`. Lean: `hasType_client_semTyped_lib_nonvacuous`.
* **Prior art / tier basis:**
  * Amin Timany, Robbert Krebbers, Derek Dreyer, Lars Birkedal. "A Logical Approach to Type Soundness." Journal of the ACM 71(6), Article 40, November 2024. DOI 10.1145/3676954. Section 7 (symbol is safe to use in all well-typed contexts).
  * Coq development accompanying Timany et al. 2024 (https://gitlab.mpi-sws.org/iris/examples, directory theories/logrel/F_mu_ref_conc); per the article it mechanizes the semantic type soundness proof (Sections 5-6) and the proofs that the symbol ADT is semantically well typed and gremlin is not (Section 7).
  * Ralf Jung, Jacques-Henri Jourdan, Robbert Krebbers, Derek Dreyer. "RustBelt: Securing the Foundations of the Rust Programming Language." Proceedings of the ACM on Programming Languages 2(POPL), Article 66, January 2018. DOI 10.1145/3158154. Coq development: https://gitlab.mpi-sws.org/iris/lambda-rust.
* **Design question:** Rust's safety story rests on unsafe code encapsulated behind safe interfaces: a syntactic type system rejects the unsafe primitive, but a library using it internally can still be semantically well typed, and then every safe client is safe. What is the minimal formal content of semantic typing + adequacy + fundamental theorem, and which tempting shortcuts fail? (Reference point (corollary): the end-to-end guarantee a user of a verified unsafe library receives without any proof about client code.)
* **Non-claims:** see **Boundaries**, item R9.

Basis: execution (Lean kernel check) — the statement(s) above and every witness below build without `sorry` and use no axioms other than `propext` and `Quot.sound` (per-declaration lists in **Evidence**).

Verbatim statements of the counterexamples, witnesses, and controls named above:

```lean
-- lean/ToySemType/Results.lean:985-987
theorem checkedRead_client_hyp_tight :
    (∀ τ, ¬ HasType [.arrow .int .int] castResultClient τ) ∧
    ¬ Safe (.app (.lam castResultClient) checkedRead, [])

-- lean/ToySemType/Results.lean:976-978
theorem checkedRead_single_var_ctx_tight :
    HasType [.arrow .int .int, .int] (.var 1) .int ∧
    ¬ Safe (.app (.lam (.var 1)) checkedRead, [])

-- lean/ToySemType/Results.lean:1079-1081
theorem hasType_client_semTyped_lib_nonvacuous :
    HasType [.arrow .int .int] callWith7 .int ∧
    SemTyped Recipe.std [] checkedRead (.arrow .int .int)
```

#### R10. An unsafe use: stuck and semantically ill typed [`forged-read-unsafe-and-semantically-ill-typed`]

* **Kind / tier / depth:** counterexample / `T0` / `shallow`.
* **Lean name(s):** `forgedRead_unsafe_ill_typed`.

```lean
-- lean/ToySemType/Results.lean:500-502
theorem forgedRead_unsafe_ill_typed :
    (∀ Γ τ, ¬ HasType Γ forgedRead τ) ∧ (∀ τ, ¬ SemTyped Recipe.std [] forgedRead τ) ∧
    ¬ Safe (forgedRead, [])
```

* **Unfolded reading / proof idea:** `forgedRead = read (cast (num 7))`. From `[]`: `cast 7 ⟶ loc 7`, and `read (loc 7)` is stuck because `[][7]? = none` (`forgedRead_reaches_stuck`).
* **Plain claim:** `read (cast 7)` is not syntactically typable in any context, is not semantically well typed at any type in the empty context (standard model), and reaches a stuck configuration from the empty heap.
* **Hypothesis ledger:** no hypotheses (a closed statement about concrete terms or models).
* **Non-vacuity witness:** Concrete term `read (cast 7)`, empty heap.
* **Prior art / tier basis:**
  * Amin Timany, Robbert Krebbers, Derek Dreyer, Lars Birkedal. "A Logical Approach to Type Soundness." Journal of the ACM 71(6), Article 40, November 2024. DOI 10.1145/3676954. Theorem 6.6 (adequacy); this statement is a concrete instance of its contrapositive (a term with a stuck execution has no semantic type).
* **Design question:** Rust's safety story rests on unsafe code encapsulated behind safe interfaces: a syntactic type system rejects the unsafe primitive, but a library using it internally can still be semantically well typed, and then every safe client is safe. What is the minimal formal content of semantic typing + adequacy + fundamental theorem, and which tempting shortcuts fail? (The unsafe primitive is genuinely dangerous, and semantic typing rejects this use.)
* **Non-claims:** see **Boundaries**, item R10.

Basis: execution (Lean kernel check) — the statement(s) above and every witness below build without `sorry` and use no axioms other than `propext` and `Quot.sound` (per-declaration lists in **Evidence**).

#### R11. `cast` of an `int` variable has no semantic type (impossibility) [`cast-of-int-variable-has-no-semantic-type`]

* **Kind / tier / depth:** impossibility / `T1` / `shallow`.
* **Lean name(s):** `cast_of_int_var_not_semTyped_of_closureEnforcesValues_of_hasInvalidRef`, `cast_of_int_var_not_semTyped`, `typing_relation_deriving_cast_of_int_var_unsound`.

```lean
-- lean/ToySemType/Results.lean:520-522
theorem cast_of_int_var_not_semTyped_of_closureEnforcesValues_of_hasInvalidRef {R : Recipe}
    (hclose : R.ClosureEnforcesValues) (hinv : R.HasInvalidRef) (τ : Ty) :
    ¬ SemTyped R [.int] (.cast (.var 0)) τ

-- lean/ToySemType/Results.lean:537-538
theorem cast_of_int_var_not_semTyped (τ : Ty) :
    ¬ SemTyped Recipe.std [.int] (.cast (.var 0)) τ

-- lean/ToySemType/Results.lean:544-546
theorem typing_relation_deriving_cast_of_int_var_unsound
    (T : List Ty → Expr → Ty → Prop) (τ : Ty) (hT : T [.int] (.cast (.var 0)) τ) :
    ¬ (∀ Γ e τ', T Γ e τ' → SemTyped Recipe.std Γ e τ')
```

* **Unfolded reading / proof idea:** `SemTyped R [int] (cast (var 0)) τ` would give, for every `W` and `n` and every heap `h` with `W ≤ |h|`, that `loc n` (reached from `cast (num n)`) is in `V R τ |h|`. `ClosureEnforcesValues` turns the closure into value membership; for `τ = int` or an arrow type the reached value `loc n` has the wrong shape; for `τ = ref`, `HasInvalidRef` supplies `W, l` with `¬ R.refOK W l` and the argument `n := l` at a heap of length `W` refutes it. For the third statement: if `T [int] (cast (var 0)) τ` and `T` were sound, then `SemTyped std [int] (cast (var 0)) τ`, contradicting the second statement.
* **Plain claim:** For every recipe whose expression closure enforces membership of reached values in the value interpretation (`ClosureEnforcesValues`) and which has some invalid reference (`HasInvalidRef`), and in particular for the standard model, `cast x` with `x : int` is not semantically well typed in context `[int]` at any type; consequently no typing relation that derives `[int] ⊢ cast (var 0) : τ` for some `τ` is sound for the standard model.
* **Hypothesis ledger:**
  * `hclose : R.ClosureEnforcesValues` — The expression closure implies `valuesIn`: the result `loc l` of the cast must be in the value interpretation of `τ`. — **tight**: counterexample `cast_of_int_var_semTyped_safetyOnly`.
  * `hinv : R.HasInvalidRef` — Some world has an address that is not a valid reference, which the argument can name. Needed only at `τ = ref`: `Recipe.anyLoc` satisfies `hclose` but not `hinv`, and there `cast (var 0)` is still not semantically typed at `int` or at any arrow type (`cast_of_int_var_not_semTyped_anyLoc_nonRef`). — **tight**: counterexample `cast_of_int_var_semTyped_anyLoc_ref`.
  * `hT (typing_relation_deriving_cast_of_int_var_unsound)` — The typing relation derives `[int] ⊢ cast (var 0) : τ`. — **tight**: counterexample `typing_relation_hyp_tight`.
* **Non-vacuity witness:** `Recipe.std` satisfies both hypotheses and `[int]` is inhabited at world 0; syntactic typing extended with the uniform root rule `Γ ⊢ a : int ⟹ Γ ⊢ cast a : ref` derives `[int] ⊢ cast (var 0) : ref`. Lean: `cast_of_int_var_not_semTyped_nonvacuous`, `typing_relation_nonvacuous`.
* **Positive controls (nearby settings where the conclusion fails):** `cast_of_int_var_semTyped_anyLoc_ref`, `cast_of_int_var_semTyped_safetyOnly`.
* **Prior art / tier basis:**
  * Amin Timany, Robbert Krebbers, Derek Dreyer, Lars Birkedal. "A Logical Approach to Type Soundness." Journal of the ACM 71(6), Article 40, November 2024. DOI 10.1145/3676954. Section 3.2 observes informally that no type of their language ensures the argument of assert evaluates to true, so assert is an unsafe feature. Their Theorem 7.2 (gremlin is semantically ill typed) concerns an abstraction-breaking operator, not a typing rule for the unsafe feature, so it is not a mechanized form of this statement. Verbatim: “However, seeing as there is no type in MyLang that would ensure that e satisfies this property, assert is an example of an unsafe feature.” (Section 3.2, p. 40:15)
* **Design question:** Rust's safety story rests on unsafe code encapsulated behind safe interfaces: a syntactic type system rejects the unsafe primitive, but a library using it internally can still be semantically well typed, and then every safe client is safe. What is the minimal formal content of semantic typing + adequacy + fundamental theorem, and which tempting shortcuts fail? (Why the syntactic system cannot give the primitive a uniform typing rule, and which model ingredients force this.)
* **Non-claims:** see **Boundaries**, item R11.

Basis: execution (Lean kernel check) — the statement(s) above and every witness below build without `sorry` and use no axioms other than `propext` and `Quot.sound` (per-declaration lists in **Evidence**).

Basis: derived (modeling bridge) — In Rust, a uniform rule turning integers into references is exactly what the safe type system withholds; this card is the toy reason (a model that forces values into the interpretation and has invalid addresses cannot type `cast x`). It does not say anything about raw pointers, whose integer-to-pointer casts are safe in Rust and whose dereference is gated behind `unsafe`; the toy has no raw-pointer type.

Verbatim statements of the counterexamples, witnesses, and controls named above:

```lean
-- lean/ToySemType/Results.lean:1019-1021
theorem cast_of_int_var_semTyped_safetyOnly :
    Recipe.safetyOnly.HasInvalidRef ∧
    ∀ τ, SemTyped Recipe.safetyOnly [.int] (.cast (.var 0)) τ

-- lean/ToySemType/Results.lean:1030-1032
theorem cast_of_int_var_semTyped_anyLoc_ref :
    Recipe.anyLoc.ClosureEnforcesValues ∧
    SemTyped Recipe.anyLoc [.int] (.cast (.var 0)) .ref

-- lean/ToySemType/Results.lean:1042-1044
theorem typing_relation_hyp_tight :
    (∀ τ, ¬ RestrictedCastRule [.int] (.cast (.var 0)) τ) ∧
    (∀ Γ e τ, RestrictedCastRule Γ e τ → SemTyped Recipe.std Γ e τ)

-- lean/ToySemType/Results.lean:1100-1102
theorem cast_of_int_var_not_semTyped_nonvacuous :
    Recipe.std.ClosureEnforcesValues ∧ Recipe.std.HasInvalidRef ∧
    G Recipe.std [.int] 0 [.num 7]

-- lean/ToySemType/Results.lean:1111
theorem typing_relation_nonvacuous : withCastRootRule [.int] (.cast (.var 0)) .ref
```

#### R11b. Safety does not imply semantic typing [`cast-literal-safe-but-not-semantically-typed`]

* **Kind / tier / depth:** counterexample / `T1` / `shallow`.
* **Lean name(s):** `cast_literal_safe_but_not_semTyped`.

```lean
-- lean/ToySemType/Results.lean:595-596
theorem cast_literal_safe_but_not_semTyped (n : Nat) :
    (∀ h, Safe (.cast (.num n), h)) ∧ ∀ τ, ¬ SemTyped Recipe.std [] (.cast (.num n)) τ
```

* **Unfolded reading / proof idea:** For every `n` and `h`: `cast (num n) ⟶ loc n`, a value, so the run is safe; but `SemTyped std [] (cast (num n)) τ` would require `loc n ∈ V std τ |h|` for every heap `h`, which fails at a heap of length `n` for `τ = ref` (and by value shape for `int` and arrows).
* **Plain claim:** For every word `n`, the literal cast `cast n` is safe from every heap, yet in the standard model it is not semantically well typed at any type in the empty context: operational safety of a closed term does not imply semantic typing.
* **Hypothesis ledger:** no hypotheses (a closed statement about concrete terms or models).
* **Non-vacuity witness:** Every `n`; e.g. `cast 7`.
* **Prior art / tier basis:**
  * The Rust Reference, "Behavior considered undefined" (https://doc.rust-lang.org/reference/behavior-considered-undefined.html): producing an invalid value is undefined behavior, and a reference must be aligned and non-null and cannot be dangling (rules undefined.invalid and undefined.validity.reference-box).
* **Design question:** Rust's safety story rests on unsafe code encapsulated behind safe interfaces: a syntactic type system rejects the unsafe primitive, but a library using it internally can still be semantically well typed, and then every safe client is safe. What is the minimal formal content of semantic typing + adequacy + fundamental theorem, and which tempting shortcuts fail? (Semantic typing is strictly stronger than safety of the term itself: the result must also inhabit the type.)
* **Non-claims:** see **Boundaries**, item R11b.

Basis: execution (Lean kernel check) — the statement(s) above and every witness below build without `sorry` and use no axioms other than `propext` and `Quot.sound` (per-declaration lists in **Evidence**).

Basis: derived (modeling bridge) — The safety half of this card depends on deferred undefined behavior. In Rust, producing a dangling or unaligned reference is undefined behavior even without a dereference (Rust Reference, "Behavior considered undefined"), so a Rust analogue of `cast n` at a reference type would not be safe; the card's transferable content is only that semantic typing is strictly stronger than safety of the term itself.

#### R12. Dropping safety from the expression closure breaks adequacy [`values-only-closure-breaks-adequacy`]

* **Kind / tier / depth:** counterexample / `T1` / `shallow`.
* **Lean name(s):** `valuesOnly_adequacy_fails`.

```lean
-- lean/ToySemType/Results.lean:610-611
theorem valuesOnly_adequacy_fails :
    SemTyped Recipe.valuesOnly [] forgedRead .int ∧ ¬ Safe (forgedRead, [])
```

* **Unfolded reading / proof idea:** `valuesIn (V valuesOnly int) W forgedRead` holds vacuously: no run of `read (cast 7)` from any heap reaches a non-integer value (from heaps of length ≤ 7 it gets stuck; from larger heaps it reaches a word). From `[]` it is stuck.
* **Plain claim:** If the expression interpretation only requires every reached value to be in the value interpretation (`Recipe.valuesOnly`, no safety requirement), then `read (cast 7)` is semantically well typed at `int` in the empty context and yet gets stuck from the empty heap: adequacy fails.
* **Hypothesis ledger:** no hypotheses (a closed statement about concrete terms or models).
* **Non-vacuity witness:** Concrete term `read (cast 7)`, empty heap.
* **Prior art / tier basis:**
  * Amin Timany, Robbert Krebbers, Derek Dreyer, Lars Birkedal. "A Logical Approach to Type Soundness." Journal of the ACM 71(6), Article 40, November 2024. DOI 10.1145/3676954. [Establishes the positive ingredient: an expression interpretation built from Iris weakest preconditions, which require both safety and the postcondition (Theorem 6.6, adequacy). It does not define or refute the ablated recipe of this card; the counterexample here is specific to this package.]
* **Design question:** Rust's safety story rests on unsafe code encapsulated behind safe interfaces: a syntactic type system rejects the unsafe primitive, but a library using it internally can still be semantically well typed, and then every safe client is safe. What is the minimal formal content of semantic typing + adequacy + fundamental theorem, and which tempting shortcuts fail? (The safety conjunct of the expression interpretation is necessary.)
* **Non-claims:** see **Boundaries**, item R12.

Basis: execution (Lean kernel check) — the statement(s) above and every witness below build without `sorry` and use no axioms other than `propext` and `Quot.sound` (per-declaration lists in **Evidence**).

#### R13. The safety-only closure collapses semantic typing to safety [`safety-only-closure-collapses-typing-to-safety`]

* **Kind / tier / depth:** characterization / `T1` / `definitional`.
* **Lean name(s):** `safetyOnly_semTyped_nil_iff_safe`.

```lean
-- lean/ToySemType/Results.lean:629-630
theorem safetyOnly_semTyped_nil_iff_safe {e : Expr} {τ : Ty} :
    SemTyped Recipe.safetyOnly [] e τ ↔ ∀ h, Safe (e, h)
```

* **Unfolded reading / proof idea:** `SemTyped safetyOnly [] e τ ⟺ ∀ W, safeOnly (V safetyOnly τ) W e ⟺ ∀ W h, W ≤ |h| → ∀ d, Reaches (e, h) d → ¬ Stuck d ⟺ ∀ h, Safe (e, h)`; the value predicate is ignored, so `τ` plays no role.
* **Plain claim:** If the expression interpretation only requires safety (`Recipe.safetyOnly`), then an expression is semantically typed at a type `τ` in the empty context iff it is safe from every heap, independently of `τ`; in particular adequacy holds trivially for this shortcut.
* **Hypothesis ledger:**
  * `empty typing context (Γ = [])` — In a non-empty context the context interpretation still restricts the substituted values, and the open term itself can be stuck. — **tight**: counterexample `safetyOnly_nil_ctx_hyp_tight`.
* **Non-vacuity witness:** Both sides hold for `λ _. cast 7` at `int ⇒ ref`; both fail for `read (cast 7)`. Lean: `safetyOnly_semTyped_nil_iff_safe_nonvacuous`.
* **Prior art / tier basis:**
  * Amin Timany, Robbert Krebbers, Derek Dreyer, Lars Birkedal. "A Logical Approach to Type Soundness." Journal of the ACM 71(6), Article 40, November 2024. DOI 10.1145/3676954. [Establishes the positive ingredient: Section 4.1 remarks that adequacy is usually almost trivial because safety is built into semantic typing. It does not define or refute the ablated recipe of this card; the counterexample here is specific to this package.] Verbatim: “This theorem is usually almost trivial to prove, because, as explained above, it is typically more or less baked into the extensional definition of semantic typing.” (Section 4.1, p. 40:16, about adequacy)
* **Design question:** Rust's safety story rests on unsafe code encapsulated behind safe interfaces: a syntactic type system rejects the unsafe primitive, but a library using it internally can still be semantically well typed, and then every safe client is safe. What is the minimal formal content of semantic typing + adequacy + fundamental theorem, and which tempting shortcuts fail? (Adequacy alone does not validate a semantic model.)
* **Non-claims:** see **Boundaries**, item R13.

Basis: execution (Lean kernel check) — the statement(s) above and every witness below build without `sorry` and use no axioms other than `propext` and `Quot.sound` (per-declaration lists in **Evidence**).

Verbatim statements of the counterexamples, witnesses, and controls named above:

```lean
-- lean/ToySemType/Results.lean:1009-1010
theorem safetyOnly_nil_ctx_hyp_tight :
    SemTyped Recipe.safetyOnly [.int] (.var 0) .int ∧ ¬ (∀ h, Safe (.var 0, h))

-- lean/ToySemType/Results.lean:1051-1054
theorem safetyOnly_semTyped_nil_iff_safe_nonvacuous :
    SemTyped Recipe.safetyOnly [] castSeven (.arrow .int .ref) ∧
    (∀ h, Safe (castSeven, h)) ∧
    ¬ SemTyped Recipe.safetyOnly [] forgedRead .int ∧ ¬ Safe (forgedRead, [])
```

#### R14. Dropping the value part breaks the fundamental theorem, encapsulation, and linking [`safety-only-closure-breaks-fundamental-theorem-and-linking`]

* **Kind / tier / depth:** counterexample / `T1` / `shallow`.
* **Lean name(s):** `safetyOnly_breaks_fundamental_and_encapsulation`, `safetyOnly_breaks_let_compat`.

```lean
-- lean/ToySemType/Results.lean:651-655
theorem safetyOnly_breaks_fundamental_and_encapsulation :
    HasType [.arrow .int .ref] readResultOf0 .int ∧
    SemTyped Recipe.safetyOnly [] castSeven (.arrow .int .ref) ∧
    ¬ SemTyped Recipe.safetyOnly [.arrow .int .ref] readResultOf0 .int ∧
    ¬ Safe (.app (.lam readResultOf0) castSeven, [])

-- lean/ToySemType/Results.lean:672-676
theorem safetyOnly_breaks_let_compat :
    SemTyped Recipe.safetyOnly [.int] (.lt (.var 0) (.num 0)) .int ∧
    SemTyped Recipe.safetyOnly [] (.lam (.num 0)) .int ∧
    ¬ SemTyped Recipe.safetyOnly [] (.app (.lam (.lt (.var 0) (.num 0))) (.lam (.num 0))) .int ∧
    ¬ Safe (.app (.lam (.lt (.var 0) (.num 0))) (.lam (.num 0)), [])
```

* **Unfolded reading / proof idea:** Part (1): `castSeven = λ _. cast 7`, `readResultOf0 = read (f 0)`; from `[]` the link reduces to `read (loc 7)`, stuck. Part (2): client `lt x 0`, library `λ _. 0`; the link reduces to `lt (lam (num 0)) (num 0)`, stuck (comparison of a function). Under `safetyOnly`, an `int`-typed context still forces `var 0` to be a word, but the empty-context library is only required to be safe.
* **Plain claim:** Under the safety-only expression interpretation (`Recipe.safetyOnly`): (1) the library `λ _. cast 7` is semantically typed at `int ⇒ ref`, the syntactically typed client `read (f 0)` is not semantically typed in `[int ⇒ ref]` (the fundamental theorem fails), and their linked program gets stuck from the empty heap (syntactic-client encapsulation fails); (2) the `cast`-free client `lt x 0` is semantically typed at `int` in `[int]` and the `cast`-free library `λ _. 0` is semantically typed at `int`, yet their linked program is not semantically typed and gets stuck (semantic let-compatibility and semantic-client linking fail).
* **Hypothesis ledger:** no hypotheses (a closed statement about concrete terms or models).
* **Non-vacuity witness:** Concrete pairs (`read (f 0)`, `λ _. cast 7`) and (`lt x 0`, `λ _. 0`), empty heap.
* **Prior art / tier basis:**
  * Amin Timany, Robbert Krebbers, Derek Dreyer, Lars Birkedal. "A Logical Approach to Type Soundness." Journal of the ACM 71(6), Article 40, November 2024. DOI 10.1145/3676954. [Establishes the positive ingredient: an expression interpretation that requires reached values to inhabit the type (weakest precondition with the type's interpretation as postcondition). It does not define or refute the ablated recipe of this card; the counterexample here is specific to this package.]
* **Design question:** Rust's safety story rests on unsafe code encapsulated behind safe interfaces: a syntactic type system rejects the unsafe primitive, but a library using it internally can still be semantically well typed, and then every safe client is safe. What is the minimal formal content of semantic typing + adequacy + fundamental theorem, and which tempting shortcuts fail? (The values-in-the-interpretation conjunct is what makes semantic typing compositional.)
* **Non-claims:** see **Boundaries**, item R14.

Basis: execution (Lean kernel check) — the statement(s) above and every witness below build without `sorry` and use no axioms other than `propext` and `Quot.sound` (per-declaration lists in **Evidence**).

#### R15. Dropping Kripke structure breaks monotonicity, the fundamental theorem, and closed encapsulation [`non-kripke-model-breaks-monotonicity-and-fundamental-theorem`]

* **Kind / tier / depth:** counterexample / `T1` / `shallow`.
* **Lean name(s):** `nonKripke_breaks_monotonicity_and_fundamental`, `nonKripke_breaks_closed_encapsulation`.

```lean
-- lean/ToySemType/Results.lean:733-738
theorem nonKripke_breaks_monotonicity_and_fundamental :
    V Recipe.nonKripke (.arrow .ref .int) 1 probeCellZero ∧
    ¬ V Recipe.nonKripke (.arrow .ref .int) 2 probeCellZero ∧
    ¬ V Recipe.std (.arrow .ref .int) 1 probeCellZero ∧
    HasType [.arrow .ref .int] callOnFreshCell .int ∧
    ¬ SemTyped Recipe.nonKripke [.arrow .ref .int] callOnFreshCell .int

-- lean/ToySemType/Results.lean:764-767
theorem nonKripke_breaks_closed_encapsulation :
    HasType [.arrow .ref .int] callOnFreshCell .int ∧
    SemTyped Recipe.nonKripke [] sizeGuardedProbe (.arrow .ref .int) ∧
    ¬ Safe (.app (.lam callOnFreshCell) sizeGuardedProbe, [0])
```

* **Unfolded reading / proof idea:** `V nonKripke (σ ⇒ τ) W e` quantifies only over `W' = W`. At world 1 the only valid reference is `loc 0`, and `probeCellZero (loc 0)` writes `1` into cell 0 so the unsafe branch is skipped; at world 2, `loc 1` is valid and `probeCellZero (loc 1)` from heap `[0, 0]` reads `0` from cell 0 and then reads address 99, stuck. The client `f (alloc 0)` passes a fresh cell, which lives in a strictly larger world.
* **Plain claim:** If the function case quantifies only over the current world (`Recipe.nonKripke`), then `probeCellZero = λ r. (λ _. ifz (read (cast 0)) (read (cast 99)) 0) (write r 1)` is in the interpretation of `ref ⇒ int` at world 1 but not at world 2, the standard (Kripke) model rejects it already at world 1, and the syntactically typed client `f (alloc 0)` is not semantically typed in `[ref ⇒ int]` (the fundamental theorem fails); moreover the closed library `sizeGuardedProbe = ifz (lt size 2) (λ _. 0) probeCellZero` is semantically typed at `ref ⇒ int` in the empty context and its link with `f (alloc 0)` gets stuck from the heap `[0]` (closed encapsulation fails).
* **Hypothesis ledger:** no hypotheses (a closed statement about concrete terms or models).
* **Non-vacuity witness:** World 1 is inhabited (`loc 0`), so the failure does not rest on a vacuous world; witness heaps `[0]`.
* **Prior art / tier basis:**
  * Achim Jung, Jerzy Tiuryn. "A New Characterization of Lambda Definability." Typed Lambda Calculi and Applications (TLCA 1993), LNCS 664, pp. 245-257. Springer, 1993. DOI 10.1007/BFb0037110. [Establishes the positive ingredient: Kripke logical relations over ordered worlds with future-world quantification in the function case (no state). It does not define or refute the ablated recipe of this card; the counterexample here is specific to this package.]
  * Andrew M. Pitts, Ian D. B. Stark. "Operational Reasoning for Functions with Local State." In A. D. Gordon, A. M. Pitts (eds.), Higher Order Operational Techniques in Semantics, pp. 227-273. Cambridge University Press, 1998. Author copy: https://www.cl.cam.ac.uk/~amp12/papers/operfl/operfl.pdf. [Establishes the positive ingredient: Kripke-style operational logical relations for a language with dynamically allocated integer references. It does not define or refute the ablated recipe of this card; the counterexample here is specific to this package.]
  * Amal J. Ahmed, Andrew W. Appel, Roberto Virga. "A Stratified Semantics of General References Embeddable in Higher-Order Logic." Proceedings of the 17th Annual IEEE Symposium on Logic in Computer Science (LICS 2002), pp. 75-86. DOI 10.1109/LICS.2002.1029818. [Establishes the positive ingredient: a world-indexed model of general references with world-extension monotonicity. It does not define or refute the ablated recipe of this card; the counterexample here is specific to this package.]
  * Amal Jamil Ahmed. "Semantics of Types for Mutable State." PhD thesis, Princeton University, November 2004; Princeton Computer Science Technical Report TR-713-04 (https://www.cs.princeton.edu/techreports/2004/713.pdf). [Establishes the positive ingredient: step-indexed possible-worlds models of mutable references with world-extension monotonicity. It does not define or refute the ablated recipe of this card; the counterexample here is specific to this package.]
* **Design question:** Rust's safety story rests on unsafe code encapsulated behind safe interfaces: a syntactic type system rejects the unsafe primitive, but a library using it internally can still be semantically well typed, and then every safe client is safe. What is the minimal formal content of semantic typing + adequacy + fundamental theorem, and which tempting shortcuts fail? (Future-world quantification is necessary once references are allocated dynamically.)
* **Non-claims:** see **Boundaries**, item R15.

Basis: execution (Lean kernel check) — the statement(s) above and every witness below build without `sorry` and use no axioms other than `propext` and `Quot.sound` (per-declaration lists in **Evidence**).

#### R16. Treating every address as valid breaks the fundamental theorem [`any-location-model-breaks-fundamental-theorem`]

* **Kind / tier / depth:** counterexample / `T1` / `shallow`.
* **Lean name(s):** `anyLoc_breaks_fundamental`.

```lean
-- lean/ToySemType/Results.lean:796-798
theorem anyLoc_breaks_fundamental :
    HasType [] derefArg (.arrow .ref .int) ∧
    ¬ SemTyped Recipe.anyLoc [] derefArg (.arrow .ref .int)
```

* **Unfolded reading / proof idea:** Under `anyLoc`, `V anyLoc ref W (loc l)` holds for every `l`, so `derefArg` would have to read any address safely; `read (loc 0)` from `[]` is stuck.
* **Plain claim:** If every address counts as a valid reference (`Recipe.anyLoc`), the syntactically typed `λ r. read r` is not semantically typed at `ref ⇒ int` in the empty context, so the fundamental theorem fails.
* **Hypothesis ledger:** no hypotheses (a closed statement about concrete terms or models).
* **Non-vacuity witness:** Concrete: `λ r. read r`, argument `loc 0`, empty heap.
* **Prior art / tier basis:**
  * Amal Jamil Ahmed. "Semantics of Types for Mutable State." PhD thesis, Princeton University, November 2004; Princeton Computer Science Technical Report TR-713-04 (https://www.cs.princeton.edu/techreports/2004/713.pdf). [Establishes the positive ingredient: possible-worlds models in which the interpretation of a reference type requires the location to be allocated in the current world. It does not define or refute the ablated recipe of this card; the counterexample here is specific to this package.]
  * Amin Timany, Robbert Krebbers, Derek Dreyer, Lars Birkedal. "A Logical Approach to Type Soundness." Journal of the ACM 71(6), Article 40, November 2024. DOI 10.1145/3676954. [Establishes the positive ingredient: the interpretation of `ref A` (Section 5.1) requires the value to be a location together with an invariant that it points to a value of type `A`. It does not define or refute the ablated recipe of this card; the counterexample here is specific to this package.]
* **Design question:** Rust's safety story rests on unsafe code encapsulated behind safe interfaces: a syntactic type system rejects the unsafe primitive, but a library using it internally can still be semantically well typed, and then every safe client is safe. What is the minimal formal content of semantic typing + adequacy + fundamental theorem, and which tempting shortcuts fail? (The interpretation of `ref` must carry the validity invariant; it is also what makes `cast` of an `int` variable semantically untypable.)
* **Non-claims:** see **Boundaries**, item R16.

Basis: execution (Lean kernel check) — the statement(s) above and every witness below build without `sorry` and use no axioms other than `propext` and `Quot.sound` (per-declaration lists in **Evidence**).

#### R17. The syntactic value interpretation cannot express encapsulation [`syntactic-value-interpretation-rejects-encapsulated-library`]

* **Kind / tier / depth:** counterexample / `T1` / `shallow`.
* **Lean name(s):** `synVal_rejects_checkedRead`.

```lean
-- lean/ToySemType/Results.lean:812-815
theorem synVal_rejects_checkedRead :
    (∀ W, V Recipe.std (.arrow .int .int) W checkedRead) ∧
    (∀ τ W, ¬ SynVal τ W checkedRead) ∧
    (∀ τ W, ¬ safeAndIn (SynVal τ) W checkedRead)
```

* **Unfolded reading / proof idea:** `SynVal τ W v ⟺ v.isValue = true ∧ HasTypeStore W [] v τ` (`synVal_iff_isValue_and_hasTypeStore`); `checkedRead` contains `cast`, and every `SynVal` value is `cast`-free (`SynVal.castFree`). `safeAndIn (SynVal τ) W checkedRead` fails because `checkedRead` is itself a value reached in zero steps.
* **Plain claim:** `checkedRead` is in the standard semantic interpretation of `int ⇒ int` at every world, but at no type and no world is it in the store-typed syntactic-typability interpretation `SynVal` (values typable by `HasTypeStore W []`), nor in the expression closure `safeAndIn (SynVal τ)`; so the syntactic-typability interpretation `SynVal` (and its expression closure `safeAndIn (SynVal τ)`) cannot certify this encapsulated library.
* **Hypothesis ledger:** no hypotheses (a closed statement about concrete terms or models).
* **Non-vacuity witness:** Concrete library `checkedRead`, every world and type.
* **Prior art / tier basis:**
  * Andrew K. Wright, Matthias Felleisen. "A Syntactic Approach to Type Soundness." Information and Computation 115(1):38-94, November 1994. DOI 10.1006/inco.1994.1093. (syntactic soundness with store typing for references).
  * Amin Timany, Robbert Krebbers, Derek Dreyer, Lars Birkedal. "A Logical Approach to Type Soundness." Journal of the ACM 71(6), Article 40, November 2024. DOI 10.1145/3676954. Section 3.2 observes informally that syntactic type soundness offers no means to prove that the symbol ADT safely encapsulates assert. Verbatim: “But syntactic type soundness—by restricting attention to syntactically well-typed programs—does not offer us a means to prove this.” (Section 3.2, p. 40:15)
* **Design question:** Rust's safety story rests on unsafe code encapsulated behind safe interfaces: a syntactic type system rejects the unsafe primitive, but a library using it internally can still be semantically well typed, and then every safe client is safe. What is the minimal formal content of semantic typing + adequacy + fundamental theorem, and which tempting shortcuts fail? (The interpretation `SynVal` contains exactly the values that the store-typed syntactic system accepts: `SynVal τ W v` iff `v` is a value with `HasTypeStore W [] v τ`, by `synVal_iff_isValue_and_hasTypeStore`.)
* **Non-claims:** see **Boundaries**, item R17.

Basis: execution (Lean kernel check) — the statement(s) above and every witness below build without `sorry` and use no axioms other than `propext` and `Quot.sound` (per-declaration lists in **Evidence**).

#### R18. Kripke monotonicity [`kripke-monotonicity`]

* **Kind / tier / depth:** theorem / `T0` / `shallow`.
* **Lean name(s):** `V_std_mono`.

```lean
-- lean/ToySemType/Results.lean:26-27
theorem V_std_mono {τ : Ty} {W W' : Nat} {v : Expr} (hW : W ≤ W')
    (h : V Recipe.std τ W v) : V Recipe.std τ W' v
```

* **Unfolded reading / proof idea:** `int`: unchanged; `ref`: `l < W ≤ W'`; arrow: the set of future worlds of `W'` is contained in that of `W` (`W ≤ W' ≤ W''`).
* **Plain claim:** In the standard model, a value in the interpretation of `τ` at world `W` remains in it at every world `W' ≥ W`.
* **Hypothesis ledger:**
  * `hW` — `W ≤ W'`: worlds only grow (allocation appends; there is no deallocation). — **tight**: counterexample `V_std_mono_hyp_tight`.
  * `h` — `V Recipe.std τ W v`: the value is in the interpretation at the smaller world. — **tight**: counterexample `V_std_mono_val_hyp_tight`.
* **Non-vacuity witness:** `loc 0` at `ref`, worlds `1 ≤ 2`; `λ r. read r` at `ref ⇒ int`, worlds `0 ≤ 1`. Lean: `V_std_mono_nonvacuous`.
* **Prior art / tier basis:**
  * Achim Jung, Jerzy Tiuryn. "A New Characterization of Lambda Definability." Typed Lambda Calculi and Applications (TLCA 1993), LNCS 664, pp. 245-257. Springer, 1993. DOI 10.1007/BFb0037110.
  * Andrew M. Pitts, Ian D. B. Stark. "Operational Reasoning for Functions with Local State." In A. D. Gordon, A. M. Pitts (eds.), Higher Order Operational Techniques in Semantics, pp. 227-273. Cambridge University Press, 1998. Author copy: https://www.cl.cam.ac.uk/~amp12/papers/operfl/operfl.pdf.
  * Amal J. Ahmed, Andrew W. Appel, Roberto Virga. "A Stratified Semantics of General References Embeddable in Higher-Order Logic." Proceedings of the 17th Annual IEEE Symposium on Logic in Computer Science (LICS 2002), pp. 75-86. DOI 10.1109/LICS.2002.1029818.
  * Amal Jamil Ahmed. "Semantics of Types for Mutable State." PhD thesis, Princeton University, November 2004; Princeton Computer Science Technical Report TR-713-04 (https://www.cs.princeton.edu/techreports/2004/713.pdf).
* **Design question:** Rust's safety story rests on unsafe code encapsulated behind safe interfaces: a syntactic type system rejects the unsafe primitive, but a library using it internally can still be semantically well typed, and then every safe client is safe. What is the minimal formal content of semantic typing + adequacy + fundamental theorem, and which tempting shortcuts fail? (The property that the function case's future-world quantification buys (contrast the non-Kripke counterexample).)
* **Non-claims:** see **Boundaries**, item R18.

Basis: execution (Lean kernel check) — the statement(s) above and every witness below build without `sorry` and use no axioms other than `propext` and `Quot.sound` (per-declaration lists in **Evidence**).

Verbatim statements of the counterexamples, witnesses, and controls named above:

```lean
-- lean/ToySemType/Results.lean:993-994
theorem V_std_mono_hyp_tight :
    ¬ (1 ≤ 0) ∧ V Recipe.std .ref 1 (.loc 0) ∧ ¬ V Recipe.std .ref 0 (.loc 0)

-- lean/ToySemType/Results.lean:1000-1001
theorem V_std_mono_val_hyp_tight :
    (0 ≤ 1) ∧ ¬ V Recipe.std .ref 0 (.loc 1) ∧ ¬ V Recipe.std .ref 1 (.loc 1)

-- lean/ToySemType/Results.lean:1086-1088
theorem V_std_mono_nonvacuous :
    (1 ≤ 2 ∧ V Recipe.std .ref 1 (.loc 0)) ∧
    (0 ≤ 1 ∧ V Recipe.std (.arrow .ref .int) 0 derefArg)
```

### Modeling bridge

Basis: derived (modeling bridge). None of the following is a Lean theorem. Each item states what the toy omits relative to Rust and how RustBelt-style models (Jung et al. 2018; Jung 2020) address it, so that a reader can judge how far each kernel-checked finding transfers.

1. **Ownership and borrowing.** Here `V std ref W` is duplicable knowledge ("cell `l` is allocated"); there is no notion of who may read or write a cell, and clients and `checkedRead` can touch any allocated cell. RustBelt interprets types as separation-logic predicates in Iris, with distinct owned and shared interpretations.
2. **Invariants on stored data.** Worlds record only the number of allocated cells, so no library whose safety depends on cell contents is semantically typed (`cellBoundRead_not_semTyped`: `cellBoundRead` is not semantically typed at `int ⇒ int`, although `cellBoundRead_callWith7_safe`). Iris invariants and ghost state (used for the symbol ADT of Timany et al. 2024 and throughout RustBelt) express such invariants.
3. **Lifetimes.** None here. RustBelt's lifetime logic models borrows with lifetimes and their expiry.
4. **Deallocation and dangling references.** No `free`, so validity is monotone and Kripke monotonicity (R18) holds. With deallocation, models use ownership of the points-to resource instead of a growing world.
5. **Validity invariants and raw pointers.** In Rust, producing an invalid reference is already undefined behavior (Rust Reference, "Behavior considered undefined"); here undefined behavior is deferred to the dereference. Rust also has raw pointers (no validity invariant; dereference requires `unsafe`), which this toy does not model; integer-to-raw-pointer casts are safe in Rust.
6. **Higher-order store and recursive types.** Cells hold only words. With cells holding functions, the world must describe cell types, making the definition circular; step-indexing (Appel & McAllester 2001; Ahmed 2004) or Iris's later modality breaks the circularity.
7. **Concurrency and data races.** None here. RustBelt handles threads, `Send`/`Sync`, and atomics in Iris.
8. **Data abstraction.** No abstraction mechanism, so library invariants on private state cannot be expressed (see item 2).
9. **Per-library proofs.** RustBelt verifies each unsafe library against a semantic interpretation of its API type; R8 is the toy analogue, and R6/R9 are the toy analogue of the resulting client guarantee.

## Boundaries

### Non-claims (by result)

Each list is self-contained; every Lean name mentioned is a fully proved declaration of this package.


**R1. Adequacy** [`adequacy`]

* Does not state that the values reached are in the value interpretation of `τ` (true by definition but not part of this statement).
* Does not require syntactic closedness `e.closedAt 0 = true`: an expression whose free variables occur only in unreachable code can satisfy `hsem` (`semTyped_nil_open_dead_var`: `ifz 1 (var 0) 0` at `int`). What is excluded is semantic typing only in a non-empty context, without a closing substitution (`adequacy_nil_ctx_hyp_tight`).
* Conversely, safety from the empty heap does not give `hsem`: semantic typing in the empty context quantifies over all worlds and all initial heaps; `ifz size 0 (read (cast 99))` is safe from `[]` but has no semantic type (`sizeZeroOrForged_safe_nil_not_semTyped`).
* Is stated for `Recipe.std` only; the same one-step argument applies to any recipe whose expression closure implies `safeOnly` (e.g. `Recipe.anyLoc`, `Recipe.nonKripke`, `Recipe.safetyOnly`), but that is not stated.
* Says nothing about termination: divergence is safe.
* Depth is definitional: the content of the model lies in the fundamental theorem and in let-compatibility, not here; adequacy alone does not validate a model (see `safetyOnly_semTyped_nil_iff_safe`).
* Applies to the toy language of this package (words modeled as unsigned naturals, a heap of word cells with allocation but no deallocation, one unchecked integer-to-reference cast, no recursion, no ownership, no concurrency); these theorems neither establish nor refute the corresponding claims about Rust, RustBelt-style verification of Rust libraries, or any other real verifier; the modeling-bridge paragraphs under Findings argue the connection separately.

**R2. Fundamental theorem** [`fundamental-theorem`]

* Not a completeness result: semantic typing is strictly more permissive (`checkedRead_not_hasType`, `checkedRead_semTyped`).
* Does not establish progress or preservation for `HasType`; no syntactic invariant of intermediate configurations is claimed.
* The function case of `V` carries the syntactic side condition `b.closedAt 1 = true` (so that the shifting-free substitution is capture-free). Syntactically typed terms satisfy it, but operationally safe abstractions with free variables in dead code are excluded from `V` (`V_std_rejects_open_dead_lam`: `λ x. ifz 0 x y`), so `V` is not a purely extensional realizability predicate.
* The absence of step-indexing relies on this toy's restrictions (word-only store, no recursive types); it does not show step-indexing is unnecessary for richer languages.
* Does not hold for the ablated recipes `Recipe.safetyOnly`, `Recipe.nonKripke`, `Recipe.anyLoc` (see their counterexamples); its status for `Recipe.valuesOnly` is unknown (not examined).
* Applies to the toy language of this package (words modeled as unsigned naturals, a heap of word cells with allocation but no deallocation, one unchecked integer-to-reference cast, no recursion, no ownership, no concurrency); these theorems neither establish nor refute the corresponding claims about Rust, RustBelt-style verification of Rust libraries, or any other real verifier; the modeling-bridge paragraphs under Findings argue the connection separately.

**R3. Syntactic type safety (corollary)** [`syntactic-type-safety-corollary`]

* Does not establish preservation (semantic soundness implies syntactic safety but not preservation).
* Says nothing about programs that use `cast`; for those see the encapsulation principle.
* Its proof depends on the two main results above; it is a corollary, not independent evidence.
* Applies to the toy language of this package (words modeled as unsigned naturals, a heap of word cells with allocation but no deallocation, one unchecked integer-to-reference cast, no recursion, no ownership, no concurrency); these theorems neither establish nor refute the corresponding claims about Rust, RustBelt-style verification of Rust libraries, or any other real verifier; the modeling-bridge paragraphs under Findings argue the connection separately.

**R4. Semantic let-compatibility (linking)** [`semantic-let-compatibility`]

* Covers only call-by-value let-style linking `app (lam c) lib`; substituting a non-value library expression directly into the client (duplicating or dropping its effects) is not covered.
* Does not claim that semantic typing is decidable or mechanically checkable.
* Does not depend on, and does not imply, any syntactic typing of `c` or `lib`.
* Cannot verify a stateful unsafe library whose safety depends on an invariant over the contents of heap cells preserved across calls (for example a stored length bound, or a private monotone counter as in the symbol ADT of Timany et al. 2024): worlds `W : Nat` record only a lower bound on the heap length, and `safeAndIn` quantifies over all heaps of at least that length with arbitrary cell contents. `cellBoundRead_not_semTyped` shows that `cellBoundRead` (a raw read guarded by a bound stored in a private cell) is not semantically typed at its interface type `int ⇒ int` (`¬ SemTyped std [] cellBoundRead (int ⇒ int)`), although it is safe with the client `x 7` (`cellBoundRead_callWith7_safe`). Invariants and ghost state, as in Iris-based models such as RustBelt, are what lift this restriction.
* Imposes no closedness condition on the client `c`, and does not imply an unconditional semantic `lam`-introduction rule: the function case of `V` requires a body closed under one binder (`b.closedAt 1 = true`), so semantic `lam`-introduction needs `b.closedAt (Γ.length + 1) = true` (which the syntactic `lam` rule supplies in `fundamental_hasType_semTyped`). `semTyped_lam_compat_needs_closedAt` shows a client `ifz 1 (var 1) 0` semantically typed at `int` in `[int]` whose abstraction is not semantically typed at `int ⇒ int` in the empty context, while the linked program `(λ. ifz 1 (var 1) 0) 7` is semantically typed; the linked program never places `λ. c` in `V` because call-by-value β-reduction consumes it.
* Applies to the toy language of this package (words modeled as unsigned naturals, a heap of word cells with allocation but no deallocation, one unchecked integer-to-reference cast, no recursion, no ownership, no concurrency); these theorems neither establish nor refute the corresponding claims about Rust, RustBelt-style verification of Rust libraries, or any other real verifier; the modeling-bridge paragraphs under Findings argue the connection separately.

**R5. Linking safety, semantic client** [`linking-safety-semantic-client`]

* Corollary of let-compatibility and adequacy; not independent evidence.
* Covers only call-by-value let-linking `app (lam c) lib` of one library expression, typed in the empty context, into a client whose context is exactly the one library variable of the library's type; textual substitution `c[lib/0]` of a non-value library (which would duplicate or drop its effects), several libraries, and libraries sharing state are not covered.
* Does not say that the client cannot observe or modify the library's cells: the toy has no ownership or abstraction (e.g. `checkedRead` can read any allocated cell, and a client can overwrite any cell it holds a reference to).
* Cannot verify a stateful unsafe library whose safety depends on an invariant over the contents of heap cells preserved across calls (for example a stored length bound, or a private monotone counter as in the symbol ADT of Timany et al. 2024): worlds `W : Nat` record only a lower bound on the heap length, and `safeAndIn` quantifies over all heaps of at least that length with arbitrary cell contents. `cellBoundRead_not_semTyped` shows that `cellBoundRead` (a raw read guarded by a bound stored in a private cell) is not semantically typed at its interface type `int ⇒ int` (`¬ SemTyped std [] cellBoundRead (int ⇒ int)`), although it is safe with the client `x 7` (`cellBoundRead_callWith7_safe`). Invariants and ghost state, as in Iris-based models such as RustBelt, are what lift this restriction.
* Applies to the toy language of this package (words modeled as unsigned naturals, a heap of word cells with allocation but no deallocation, one unchecked integer-to-reference cast, no recursion, no ownership, no concurrency); these theorems neither establish nor refute the corresponding claims about Rust, RustBelt-style verification of Rust libraries, or any other real verifier; the modeling-bridge paragraphs under Findings argue the connection separately.

**R6. Encapsulation principle** [`encapsulation-principle`]

* Does not say that the client cannot observe or modify the library's cells: the toy has no ownership or abstraction (e.g. `checkedRead` can read any allocated cell, and a client can overwrite any cell it holds a reference to).
* Covers only call-by-value let-linking `app (lam c) lib` of one library expression, typed in the empty context, into a client whose context is exactly the one library variable of the library's type; textual substitution `c[lib/0]` of a non-value library (which would duplicate or drop its effects), several libraries, and libraries sharing state are not covered.
* Cannot verify a stateful unsafe library whose safety depends on an invariant over the contents of heap cells preserved across calls (for example a stored length bound, or a private monotone counter as in the symbol ADT of Timany et al. 2024): worlds `W : Nat` record only a lower bound on the heap length, and `safeAndIn` quantifies over all heaps of at least that length with arbitrary cell contents. `cellBoundRead_not_semTyped` shows that `cellBoundRead` (a raw read guarded by a bound stored in a private cell) is not semantically typed at its interface type `int ⇒ int` (`¬ SemTyped std [] cellBoundRead (int ⇒ int)`), although it is safe with the client `x 7` (`cellBoundRead_callWith7_safe`). Invariants and ghost state, as in Iris-based models such as RustBelt, are what lift this restriction.
* Does not cover deallocation or concurrency.
* Applies to the toy language of this package (words modeled as unsigned naturals, a heap of word cells with allocation but no deallocation, one unchecked integer-to-reference cast, no recursion, no ownership, no concurrency); these theorems neither establish nor refute the corresponding claims about Rust, RustBelt-style verification of Rust libraries, or any other real verifier; the modeling-bridge paragraphs under Findings argue the connection separately.

**R7. The encapsulated library is not syntactically typable** [`checked-read-not-syntactically-typable`]

* Only about this `HasType`. Adding the uniform rule `Γ ⊢ a : int ⟹ Γ ⊢ cast a : ref` would be unsound for the standard model (`typing_relation_deriving_cast_of_int_var_unsound` applies to `withCastRootRule`, by `typing_relation_nonvacuous`), but restricted rules with `cast` at the root can be sound (`restrictedCastRule_sound`: `ref :: Γ ⊢ cast 0 : ref` and `Γ ⊢ cast ((λ _. 0) (alloc 0)) : ref`). It is not claimed that no typing rule mentioning `cast` can be sound.
* Applies to the toy language of this package (words modeled as unsigned naturals, a heap of word cells with allocation but no deallocation, one unchecked integer-to-reference cast, no recursion, no ownership, no concurrency); these theorems neither establish nor refute the corresponding claims about Rust, RustBelt-style verification of Rust libraries, or any other real verifier; the modeling-bridge paragraphs under Findings argue the connection separately.

**R8. The encapsulated library is semantically well typed** [`checked-read-semantically-typed`]

* Relative to a model that tracks memory safety and nothing else; in a model with ownership (e.g. RustBelt) reading arbitrary allocated cells would not be justified.
* Says nothing about functional correctness (e.g. that it returns the cell's content).
* The guard is necessary: the unguarded `λ n. read (cast n)` has no semantic type (`uncheckedRead_not_semTyped`).
* `checkedRead` is semantically typed only because it compares against the primitive `size` (the current heap length) on every call and relies on no stored cell contents. Cannot verify a stateful unsafe library whose safety depends on an invariant over the contents of heap cells preserved across calls (for example a stored length bound, or a private monotone counter as in the symbol ADT of Timany et al. 2024): worlds `W : Nat` record only a lower bound on the heap length, and `safeAndIn` quantifies over all heaps of at least that length with arbitrary cell contents. `cellBoundRead_not_semTyped` shows that `cellBoundRead` (a raw read guarded by a bound stored in a private cell) is not semantically typed at its interface type `int ⇒ int` (`¬ SemTyped std [] cellBoundRead (int ⇒ int)`), although it is safe with the client `x 7` (`cellBoundRead_callWith7_safe`). Invariants and ghost state, as in Iris-based models such as RustBelt, are what lift this restriction.
* The single comparison `lt n size` suffices without a lower-bound check only because words are unsigned naturals; with signed integers a two-sided check would be needed.
* Models a global `peek(n)` on the heap rather than a container-scoped `get(i)`: `checkedRead` takes no reference or slice argument and reads any allocated cell.
* Applies to the toy language of this package (words modeled as unsigned naturals, a heap of word cells with allocation but no deallocation, one unchecked integer-to-reference cast, no recursion, no ownership, no concurrency); these theorems neither establish nor refute the corresponding claims about Rust, RustBelt-style verification of Rust libraries, or any other real verifier; the modeling-bridge paragraphs under Findings argue the connection separately.

**R9. Every syntactically typed client of the library is safe** [`checked-read-syntactic-clients-safe`]

* A corollary: its proof composes the encapsulation principle (hence the fundamental theorem, let-compatibility, and adequacy) with `checkedRead_semTyped`; it is not independent evidence.
* Linking is restricted to call-by-value `app (lam c) checkedRead` with the client's only free variable bound to the library.
* Does not say that the client cannot observe or modify the library's cells: the toy has no ownership or abstraction (e.g. `checkedRead` can read any allocated cell, and a client can overwrite any cell it holds a reference to).
* `checkedRead` relies only on the primitive `size`; this result says nothing about libraries whose safety depends on stored cell contents, which the standard model cannot verify (`cellBoundRead_not_semTyped`: `cellBoundRead` is not semantically typed at `int ⇒ int`).
* Applies to the toy language of this package (words modeled as unsigned naturals, a heap of word cells with allocation but no deallocation, one unchecked integer-to-reference cast, no recursion, no ownership, no concurrency); these theorems neither establish nor refute the corresponding claims about Rust, RustBelt-style verification of Rust libraries, or any other real verifier; the modeling-bridge paragraphs under Findings argue the connection separately.

**R10. An unsafe use: stuck and semantically ill typed** [`forged-read-unsafe-and-semantically-ill-typed`]

* Only from the empty heap: from heaps with more than 7 cells it is safe.
* Semantic ill-typedness is stated for the empty context: `read (cast 0)` has no semantic type in `[]` but is semantically typed at `int` in `[ref]`, because a `ref` assumption forces cell 0 to be allocated (`read_cast_zero_semTyped_ref_ctx`).
* Applies to the toy language of this package (words modeled as unsigned naturals, a heap of word cells with allocation but no deallocation, one unchecked integer-to-reference cast, no recursion, no ownership, no concurrency); these theorems neither establish nor refute the corresponding claims about Rust, RustBelt-style verification of Rust libraries, or any other real verifier; the modeling-bridge paragraphs under Findings argue the connection separately.

**R11. `cast` of an `int` variable has no semantic type (impossibility)** [`cast-of-int-variable-has-no-semantic-type`]

* Does not say that uses of `cast` are never semantically typed (`checkedRead_semTyped`), nor that no typing rule mentioning `cast` can be sound: restricted rules with `cast` at the root are sound over the unmodified types (`restrictedCastRule_sound`: `ref :: Γ ⊢ cast 0 : ref`, because a `ref` assumption forces cell 0 to be allocated, and `Γ ⊢ cast ((λ _. 0) (alloc 0)) : ref`, because the argument allocates a cell first). What is refuted is a rule typing `cast` of an argument known only to be a word.
* Escape hatches: the conclusion fails if the closure does not enforce values (`Recipe.safetyOnly`: `cast x` is then semantically typed at every type) or if every address is a valid reference (`Recipe.anyLoc`: `cast x` is then semantically typed at `ref`, but that recipe breaks the fundamental theorem, `anyLoc_breaks_fundamental`).
* Depends on `cast` producing the single reference type `ref`, which supports a safe `read`. A design that separates raw addresses (no validity invariant, no safe dereference) from references is not modeled, and this result gives no obstruction to casting words to such a raw type. (Safe Rust allows integer-to-raw-pointer casts and requires `unsafe` to dereference a raw pointer.)
* Does not exclude sound typing rules for `cast` in richer type systems that constrain the argument (e.g. refinement types restricting it to allocated addresses).
* Applies to the toy language of this package (words modeled as unsigned naturals, a heap of word cells with allocation but no deallocation, one unchecked integer-to-reference cast, no recursion, no ownership, no concurrency); these theorems neither establish nor refute the corresponding claims about Rust, RustBelt-style verification of Rust libraries, or any other real verifier; the modeling-bridge paragraphs under Findings argue the connection separately.

**R11b. Safety does not imply semantic typing** [`cast-literal-safe-but-not-semantically-typed`]

* Safety of `cast n` relies on this machine deferring undefined behavior to `read` and `write` (the cast itself always steps to `loc n`). In Rust, producing a dangling or unaligned reference value is already undefined behavior, even if it is never dereferenced (Rust Reference, 'Behavior considered undefined').
* Under the safety-only closure (`Recipe.safetyOnly`), `cast n` is semantically typed at every type (by `safetyOnly_semTyped_nil_iff_safe` and the first conjunct); the separation depends on the value conjunct of `safeAndIn`.
* Proved directly; it is not derived from `cast_of_int_var_not_semTyped`.
* Applies to the toy language of this package (words modeled as unsigned naturals, a heap of word cells with allocation but no deallocation, one unchecked integer-to-reference cast, no recursion, no ownership, no concurrency); these theorems neither establish nor refute the corresponding claims about Rust, RustBelt-style verification of Rust libraries, or any other real verifier; the modeling-bridge paragraphs under Findings argue the connection separately.

**R12. Dropping safety from the expression closure breaks adequacy** [`values-only-closure-breaks-adequacy`]

* Concerns the partial-correctness closure `valuesIn`, which holds vacuously for executions that get stuck. A total-correctness closure requiring convergence to a value in the interpretation would exclude stuck executions, because the semantics is deterministic (`safe_of_reaches_value`), but it would also reject divergent programs; such a closure is not examined here.
* Does not claim the fundamental theorem fails for `Recipe.valuesOnly` (unknown; not examined).
* Applies to the toy language of this package (words modeled as unsigned naturals, a heap of word cells with allocation but no deallocation, one unchecked integer-to-reference cast, no recursion, no ownership, no concurrency); these theorems neither establish nor refute the corresponding claims about Rust, RustBelt-style verification of Rust libraries, or any other real verifier; the modeling-bridge paragraphs under Findings argue the connection separately.

**R13. The safety-only closure collapses semantic typing to safety** [`safety-only-closure-collapses-typing-to-safety`]

* Only for the empty context. In a non-empty context the context interpretation still requires the substituted values to have the right shape (a word for `int`, an allocated `loc l` for `ref`, a closed abstraction for an arrow type), so semantic typing is not just safety there (`safetyOnly_nil_ctx_hyp_tight`).
* Adequacy holding for this shortcut does not make it a good model: it breaks the fundamental theorem and linking (`safetyOnly_breaks_fundamental_and_encapsulation`, `safetyOnly_breaks_let_compat`).
* Applies to the toy language of this package (words modeled as unsigned naturals, a heap of word cells with allocation but no deallocation, one unchecked integer-to-reference cast, no recursion, no ownership, no concurrency); these theorems neither establish nor refute the corresponding claims about Rust, RustBelt-style verification of Rust libraries, or any other real verifier; the modeling-bridge paragraphs under Findings argue the connection separately.

**R14. Dropping the value part breaks the fundamental theorem, encapsulation, and linking** [`safety-only-closure-breaks-fundamental-theorem-and-linking`]

* Part (1) does not instantiate semantic let-compatibility, because its client is not semantically typed under `Recipe.safetyOnly`; part (2) is the direct counterexample to semantic linking and needs no `cast`.
* Shows failure for this one ablation of the standard recipe, not for every model lacking the value conjunct.
* Applies to the toy language of this package (words modeled as unsigned naturals, a heap of word cells with allocation but no deallocation, one unchecked integer-to-reference cast, no recursion, no ownership, no concurrency); these theorems neither establish nor refute the corresponding claims about Rust, RustBelt-style verification of Rust libraries, or any other real verifier; the modeling-bridge paragraphs under Findings argue the connection separately.

**R15. Dropping Kripke structure breaks monotonicity, the fundamental theorem, and closed encapsulation** [`non-kripke-model-breaks-monotonicity-and-fundamental-theorem`]

* `probeCellZero` itself is not semantically typed under `Recipe.nonKripke` in the empty context, which quantifies over all worlds including world 2 (`probeCellZero_not_semTyped_nonKripke_nil`); closed encapsulation fails through a library that inspects `size` and returns `probeCellZero` only in worlds 0 and 1.
* Adequacy still holds for `Recipe.nonKripke` (its expression closure is `safeAndIn`), but this is not stated.
* Both counterexamples combine a function-typed library with allocation by the client. At types without arrows the value interpretation does not consult `future`, so the two recipes agree there; whether `Recipe.nonKripke` breaks the fundamental theorem in a fragment without `alloc` is not examined.
* Concerns this one non-Kripke variant (the expression interpretation still quantifies over all heaps with at least `W` cells); other non-Kripke designs are not examined.
* "Closed encapsulation fails" refers to a syntactically typed client linked with a closed `nonKripke`-typed library. Closed semantic-client linking still holds under `Recipe.nonKripke`: a client `nonKripke`-typed in `[σ]` linked with a library `nonKripke`-typed at `σ` in the empty context is safe from every heap (`nonKripke_semTyped_client_nil_safe`), unlike under `Recipe.safetyOnly` (`safetyOnly_breaks_let_compat`). What fails for `Recipe.nonKripke` is semantic let-compatibility in a non-empty ambient context (`nonKripke_breaks_open_let_compat`: context `[ref ⇒ int]`, client `f r`, library `alloc 0`).
* Applies to the toy language of this package (words modeled as unsigned naturals, a heap of word cells with allocation but no deallocation, one unchecked integer-to-reference cast, no recursion, no ownership, no concurrency); these theorems neither establish nor refute the corresponding claims about Rust, RustBelt-style verification of Rust libraries, or any other real verifier; the modeling-bridge paragraphs under Findings argue the connection separately.

**R16. Treating every address as valid breaks the fundamental theorem** [`any-location-model-breaks-fundamental-theorem`]

* Relies on `read` and `write` getting stuck on unallocated addresses. With dynamically checked `read`/`write` that return a default or error value instead, this counterexample would not apply; such a semantics is not formalized here.
* Adequacy still holds for `Recipe.anyLoc` (its expression closure is `safeAndIn`), but this is not stated.
* Applies to the toy language of this package (words modeled as unsigned naturals, a heap of word cells with allocation but no deallocation, one unchecked integer-to-reference cast, no recursion, no ownership, no concurrency); these theorems neither establish nor refute the corresponding claims about Rust, RustBelt-style verification of Rust libraries, or any other real verifier; the modeling-bridge paragraphs under Findings argue the connection separately.

**R17. The syntactic value interpretation cannot express encapsulation** [`syntactic-value-interpretation-rejects-encapsulated-library`]

* `SynVal` includes store typing: it admits runtime closures that capture allocated references (`synVal_pos`: `λ _. read (loc 0)` in world 1; `captureRef_safeAndIn_synVal`: `safeAndIn (SynVal (int ⇒ int)) 0 captureRef`, i.e. from every heap, `captureRef = (λ r. λ _. read r) (alloc 5)` never gets stuck and every value it reaches is in `SynVal (int ⇒ int)` at the length of the reached heap). Its rejection of `checkedRead` comes from the absence of any typing rule for `cast` (`SynVal.castFree`), so it rejects every value containing `cast`.
* Does not claim that a `SynVal`-based model fails adequacy or a fundamental theorem for `HasType`; not examined.
* Applies to the toy language of this package (words modeled as unsigned naturals, a heap of word cells with allocation but no deallocation, one unchecked integer-to-reference cast, no recursion, no ownership, no concurrency); these theorems neither establish nor refute the corresponding claims about Rust, RustBelt-style verification of Rust libraries, or any other real verifier; the modeling-bridge paragraphs under Findings argue the connection separately.

**R18. Kripke monotonicity** [`kripke-monotonicity`]

* States monotonicity of the value interpretation only (the expression interpretation is also monotone in `W`, trivially, but this is not stated).
* The proof does not use the expression closure; monotonicity holds for any recipe whose `refOK` is monotone in the world and for which `future W' W''` implies `future W W''` whenever `W ≤ W'`, but that is not stated.
* Relies on the absence of deallocation; with deallocation validity is not monotone.
* Applies to the toy language of this package (words modeled as unsigned naturals, a heap of word cells with allocation but no deallocation, one unchecked integer-to-reference cast, no recursion, no ownership, no concurrency); these theorems neither establish nor refute the corresponding claims about Rust, RustBelt-style verification of Rust libraries, or any other real verifier; the modeling-bridge paragraphs under Findings argue the connection separately.

### Attractive stronger conclusions that are not established

* **Not about Rust.** No result is a theorem about Rust, MIR, RustBelt, or any verifier; see the modeling bridge for what each omission means.
* **Not "no typing rule for `cast` can be sound."** R11 rules out only rules that derive `[int] ⊢ cast (var 0) : τ`. Restricted rules with `cast` at the root are sound for the standard model: `restrictedCastRule_sound` (`ref :: Γ ⊢ cast 0 : ref` and `Γ ⊢ cast ((λ _. 0) (alloc 0)) : ref`).
* **Not "semantic typing equals safety."** Safety of a term does not give semantic typing (R11b, and `sizeZeroOrForged_safe_nil_not_semTyped`: `ifz size 0 (read (cast 99))` is safe from `[]` but has no semantic type in the empty context). Only under the ablated closure `safeOnly` and only in the empty context do the two coincide (R13).
* **Not "adequacy validates a model."** Adequacy holds for `safetyOnly` in the strong form of R13, yet that model breaks the fundamental theorem and linking (R14).
* **Not completeness.** The fundamental theorem (R2) is one-directional: `checkedRead` (in the empty context) and `checkedClient` (in `[int ⇒ int]`) are semantically typed but not syntactically typed (R7, R8, `checkedClient_semTyped_safe_not_hasType`).
* **Not a stateful-library result.** The standard model cannot verify a library whose safety depends on stored cell contents (`cellBoundRead_not_semTyped`: `cellBoundRead` is not semantically typed at `int ⇒ int`), so R4–R9 say nothing about such libraries.

### Escape hatches for the impossibility result (R11)

* Drop `ClosureEnforcesValues` (closure `safeOnly`): `cast x` is semantically typed in `[int]` at **every** type (`cast_of_int_var_semTyped_safetyOnly`).
* Drop `HasInvalidRef` (every address valid, `Recipe.anyLoc`): `cast x` is semantically typed in `[int]` at `ref` (`cast_of_int_var_semTyped_anyLoc_ref`), but still at no `int` or arrow type (`cast_of_int_var_not_semTyped_anyLoc_nonRef` below); and `anyLoc` breaks the fundamental theorem (R16).
* Change the typing judgment: restricted rules that never derive `[int] ⊢ cast (var 0) : τ` can be sound (`restrictedCastRule_sound`; together with the fact that `RestrictedCastRule` derives `[int] ⊢ cast (var 0) : τ` for no `τ`, this is the tightness counterexample `typing_relation_hyp_tight` for `hT`).
* Change the type language: R11 depends on `cast` returning the single type `ref`, whose `read` is safe. A separate raw-address type with no validity invariant is not modeled, and no obstruction to casting words to such a type is shown. Refinement-typed rules (for example, `cast` of a word known to be below `size`) are not excluded.

```lean
-- lean/ToySemType/Results.lean:1407-1410
theorem cast_of_int_var_not_semTyped_anyLoc_nonRef :
    ¬ Recipe.anyLoc.HasInvalidRef ∧
    ¬ SemTyped Recipe.anyLoc [.int] (.cast (.var 0)) .int ∧
    ∀ σ τ, ¬ SemTyped Recipe.anyLoc [.int] (.cast (.var 0)) (.arrow σ τ)
```

### Boundaries of the linking results (R4–R6, R15)

**Semantic let-compatibility needs no closedness of the client, but semantic `lam`-introduction does.** Because the function case of `V` requires `b.closedAt 1 = true`, the rule "`SemTyped std (σ :: Γ) b τ` implies `SemTyped std Γ (lam b) (σ ⇒ τ)`" is false without the side condition `b.closedAt (Γ.length + 1) = true` (which the syntactic `lam` rule supplies inside R2). R4 nonetheless holds with no condition on `c`, because call-by-value β-reduction of `app (lam c) lib` consumes `lam c` and never places it in `V`. R4 therefore does not factor through, and does not imply, an unconditional semantic `lam` rule. Kernel-checked:

```lean
-- lean/ToySemType/Results.lean:1309-1312
theorem semTyped_lam_compat_needs_closedAt :
    SemTyped Recipe.std [.int] (.ifz (.num 1) (.var 1) (.num 0)) .int ∧
    ¬ SemTyped Recipe.std [] (.lam (.ifz (.num 1) (.var 1) (.num 0))) (.arrow .int .int) ∧
    SemTyped Recipe.std [] (.app (.lam (.ifz (.num 1) (.var 1) (.num 0))) (.num 7)) .int
```

**What exactly fails without Kripke structure.** R15's "closed encapsulation fails" concerns a *syntactically* typed client linked with a closed `nonKripke`-typed library. Closed *semantic*-client linking still holds under `Recipe.nonKripke`, because with an empty ambient context there is no closing substitution that must survive the library's allocations. This contrasts with `Recipe.safetyOnly`, under which even closed semantic-client linking fails (`safetyOnly_breaks_let_compat`). What fails under `Recipe.nonKripke` is semantic let-compatibility in a **non-empty** ambient context. Kernel-checked:

```lean
-- lean/ToySemType/Results.lean:1335-1338
theorem nonKripke_semTyped_client_nil_safe {σ τ : Ty} {c lib : Expr}
    (hc : SemTyped Recipe.nonKripke [σ] c τ)
    (hlib : SemTyped Recipe.nonKripke [] lib σ) (h : Heap) :
    Safe (.app (.lam c) lib, h)

-- lean/ToySemType/Results.lean:1356-1360
theorem nonKripke_breaks_open_let_compat :
    SemTyped Recipe.nonKripke [.ref, .arrow .ref .int] (.app (.var 1) (.var 0)) .int ∧
    SemTyped Recipe.nonKripke [.arrow .ref .int] (.alloc (.num 0)) .ref ∧
    ¬ SemTyped Recipe.nonKripke [.arrow .ref .int]
        (.app (.lam (.app (.var 1) (.var 0))) (.alloc (.num 0))) .int
```

### Not examined and unknown

* **unknown (not examined):** whether the fundamental theorem holds for `Recipe.valuesOnly`.
* **not examined:** a total-correctness closure (requiring termination), which would exclude stuck runs by determinism (`safe_of_reaches_value`) but reject divergence.
* **not examined:** whether `Recipe.nonKripke` breaks the fundamental theorem in a fragment without `alloc`; other non-Kripke designs.
* **not examined:** adequacy or a fundamental theorem for a `SynVal`-based model.
* **not formalized (true but not stated):** adequacy for `Recipe.nonKripke` and `Recipe.anyLoc` (their closure is `safeAndIn`); monotonicity of `V` for recipes other than `std`.
* **not formalized:** dynamically checked `read`/`write` that return a default instead of getting stuck (under which R16's counterexample would not apply); deallocation; multiple libraries or shared state in linking; substitution of non-value libraries into clients.
* **Tightness status:** every hypothesis in every card is `tight` with a fully proved counterexample; no hypothesis is labeled `harmless` or `unknown`. One hypothesis is tight but not minimal: in R9, `hc : HasType [int ⇒ int] c τ` can be weakened to `SemTyped std [int ⇒ int] c τ` (R5 with R8; `checkedClient_semTyped_safe_not_hasType`).

### Disproved or withdrawn statements

None. Every stated result in this package is proved as stated; no statement was found false, weakened, or left unproved.


## Evidence

### Kernel-check record

* **Toolchain:** Lean `leanprover/lean4:v4.34.1`, GitHub repository `leanprover/lean4`, tag `v4.34.1` → commit `5045d0056413266e57c625dcd7c365b10e377c52` (the tag ref points directly at this commit; read from the GitHub API on 2026-11-20). Core Lean only; no Mathlib; the Lake project has no `[[require]]`.
* **Build:** `lake build` in `lean/` builds the library `ToySemType` (modules `Syntax`, `Semantics`, `Typing`, `Model`, `Lemmas`, `Programs`, `Concrete`, `Results`, `Examples`) with no errors and no `declaration uses 'sorry'` warnings. No Lean source contains `sorry`, `admit`, `native_decide`, an `axiom` or `opaque` declaration, `implemented_by`, `@[extern]`, `unsafe`, or `debug.skipKernelTC`.
* **Axioms:** `Lean.collectAxioms` over all 553 non-internal declarations of the `ToySemType` modules reports only `Quot.sound`, `propext` (allowed set: `propext`, `Classical.choice`, `Quot.sound`). Per-declaration results are in `audit/axioms.json`.
* **Statement hashes:** for each Lean name referenced by `results.json` (results, counterexamples, non-vacuity witnesses, positive controls), `audit/statements.json` records the SHA-256 of the statement (the Lean `repr` of its type) and of its definition closure (the sorted lines `name : type [:= value]` for every `ToySemType` constant reachable from the statement, following types and non-theorem values; theorem bodies excluded). Changing any definition a statement depends on changes its closure hash.
* **Observation date:** all build, axiom, and hash evidence was produced on 2026-11-20.

Basis: execution (Lean kernel check).


| Lean name (namespace `Toy.SemType`) | Role(s) | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
|---|---|---|---|---|
| `adequacy_semTyped_nil_safe` | adequacy: result | `propext` | `7d20eaebc444d1514c074fbef03fe4fd23b71a9d985746dd17338b73b63f5d1b` | `413f9b919cef458fd1d2e87e2a3ae70641a2c55b26a382a4a9992a249af93443` (77) |
| `fundamental_hasType_semTyped` | fundamental-theorem: result | `Quot.sound`, `propext` | `cdddf1353c86279669d78c89ff1908b59ef5ece292143c2eeded86fa765853b0` | `10812d58fa5d8c4dfa3cab7be2049dbb5e09cb61efe29c358d9d7dca04b2466e` (87) |
| `hasType_closed_safe` | syntactic-type-safety-corollary: result | `Quot.sound`, `propext` | `ed765a3470c9f5801e74a6f5b61e4a90b2a0ca2179f59fc489b1df3ef9481aed` | `a6d51fa177ec37e3f78978900755a2552fdc263f3b9f8e2c2b0ad82b9f4e03cc` (62) |
| `semTyped_let_compat` | semantic-let-compatibility: result | `Quot.sound`, `propext` | `3074f75cfffed8dc6500cd8785ca1ca918ccd4abc1a5cc58874c3e1813191bb2` | `5438f51d5aa089460a273a011e605c8f8b418cd0d902a5bb9bfee9220ba7dd92` (76) |
| `semTyped_client_semTyped_lib_safe` | linking-safety-semantic-client: result | `Quot.sound`, `propext` | `95180e9e97d44be0af33387dcae9dd5bdd8f28f47233fe5ddee4430d3f26bf6d` | `413f9b919cef458fd1d2e87e2a3ae70641a2c55b26a382a4a9992a249af93443` (77) |
| `hasType_client_semTyped_lib_safe` | encapsulation-principle: result | `Quot.sound`, `propext` | `700c3ef1970d064b3052c47a762409d66238fa54a2008e2c01459bc15cfdec6b` | `bc88eeeaf682ec18d150be17b50ca8a7115096ccac3679c189d542c8558c7462` (88) |
| `checkedRead_not_hasType` | checked-read-not-syntactically-typable: result | `propext` | `cd9d5437a34344d2ba45eb6f691091f82b89d96691f5825ad28fbbd6a33cbe3f` | `0d7568706c62e03806160de2e4daf12a2078911094523569277669e772ba1122` (29) |
| `checkedRead_semTyped` | checked-read-semantically-typed: result | `Quot.sound`, `propext` | `266e65e706d7907d07d9c37b7c4bb2d4cc1e11ff8dbed3c7630bb2b21100c9ba` | `8a45e214729be61e98562b0ceff4cf3504b3fa217251a31a13eb2a96cb9196a8` (77) |
| `checkedRead_hasType_clients_safe` | checked-read-syntactic-clients-safe: result | `Quot.sound`, `propext` | `eb9913f20517ea216a4528506b832fc9ae4c8f301e928f3fbd0a63ea08b26dba` | `d68e59194f2e4105bbf9719e86caf433436ca755b17f375a9565f5853c0a46c4` (63) |
| `forgedRead_unsafe_ill_typed` | syntactic-type-safety-corollary: counterexample for hty; forged-read-unsafe-and-semantically-ill-typed: result | `propext` | `b4bb4d05ca3e30fc7c9757e6f51ef4305eabc06367ef6eac6be4c87b31ebe363` | `5b2f5adb38aa1d03a98d84ca9d5d5595d4da89a9329b8449b90629a10ba2c41d` (89) |
| `cast_of_int_var_not_semTyped_of_closureEnforcesValues_of_hasInvalidRef` | cast-of-int-variable-has-no-semantic-type: result | `propext` | `7e438aed47401bdfa9bdd9c35697d8369ca360e25192414028d077985b18977f` | `dd48e85d545bf610e0e23f89b50d7b8c560aa5b3e68c5aaff29d379ec08ac930` (76) |
| `cast_of_int_var_not_semTyped` | cast-of-int-variable-has-no-semantic-type: result | `propext` | `5bc01698ca1d06d2dcfeb336792e9eb852b54c3aaad883ea85c34374dd7cf249` | `5438f51d5aa089460a273a011e605c8f8b418cd0d902a5bb9bfee9220ba7dd92` (76) |
| `typing_relation_deriving_cast_of_int_var_unsound` | cast-of-int-variable-has-no-semantic-type: result | `propext` | `8c164cc9335557d8f60a9b7facdbf9aa55bec9ec24500f285e52d6010f0f9ef9` | `5438f51d5aa089460a273a011e605c8f8b418cd0d902a5bb9bfee9220ba7dd92` (76) |
| `cast_literal_safe_but_not_semTyped` | cast-literal-safe-but-not-semantically-typed: result | `propext` | `e8d6fdb2a419a4fb4bc891d61a7d0dd89d7153a8d98e07f600805be27b9881ab` | `413f9b919cef458fd1d2e87e2a3ae70641a2c55b26a382a4a9992a249af93443` (77) |
| `valuesOnly_adequacy_fails` | values-only-closure-breaks-adequacy: result | `propext` | `9469d048b1f1638fd1194f7af1cc5931720af29b9b2df2b0ebe9869ee1148c2d` | `caf120ded907fd295c1e431b719b52b1db3090d355fdff0def8e55e37cf270c8` (80) |
| `safetyOnly_semTyped_nil_iff_safe` | safety-only-closure-collapses-typing-to-safety: result | `propext` | `e627d8500211e70ab8f6a88c809246fe4dd74f1f213ff3dfac7e2d30e5b087e5` | `505deda52313e60f471d50088c48baf088573c960af78f130dadf3e5aef0c661` (79) |
| `safetyOnly_breaks_fundamental_and_encapsulation` | safety-only-closure-breaks-fundamental-theorem-and-linking: result | `propext` | `6f10c0e4a492c5a92f9b0673449c97418dc3e7a0ca349867b54fa2acc37bd1c5` | `70112c12aeecbc8308f5b35048ac9b08d52438157ee967f5e57bfbea63edcad3` (92) |
| `safetyOnly_breaks_let_compat` | safety-only-closure-breaks-fundamental-theorem-and-linking: result | `Quot.sound`, `propext` | `70e5f6c07c67f33b4716c507aed58156f102067a7904fffbb92ddabbd6f11656` | `505deda52313e60f471d50088c48baf088573c960af78f130dadf3e5aef0c661` (79) |
| `nonKripke_breaks_monotonicity_and_fundamental` | non-kripke-model-breaks-monotonicity-and-fundamental-theorem: result | `Quot.sound`, `propext` | `0e861b2735050a3bd211e4bc8d835982ecf3f0368a9d8ab27f422c36eaffbb88` | `7e8b5da97970de9ed17d748e80c8b66cab69ec33353b7b4e5264b864efcb5e4d` (91) |
| `nonKripke_breaks_closed_encapsulation` | non-kripke-model-breaks-monotonicity-and-fundamental-theorem: result | `Quot.sound`, `propext` | `27f74cf5c8a7308b3147b8c1c1c089abdd1152eb1c8c58d1cd3b7ec96290ceba` | `55a40420809b142518838f938d20231f0cf107ee035b82adc33ac0d0b2dbdfa2` (93) |
| `anyLoc_breaks_fundamental` | any-location-model-breaks-fundamental-theorem: result | `propext` | `f1daf71d38da3a4b82da2e287fe825672c7f20f0f779c7dcbcbf99d487632b61` | `c683fa915ab336a21070e6ebece59fbbac10a68e29cae4d335b14b515f0bb1f9` (89) |
| `synVal_rejects_checkedRead` | syntactic-value-interpretation-rejects-encapsulated-library: result | `Quot.sound`, `propext` | `f33c5149bbc6a1fe72a489dc867e6730d05d179a1670cd12d69388091b1023e8` | `b40f15736debf7c3baae241ecd02f2ec9dbaf37d6dcd5169348ceeea69813acd` (82) |
| `V_std_mono` | kripke-monotonicity: result | `propext` | `ffb4e86fba00b5393eaf21d03102afde20925e2addefff3de0ac454b34da2ae4` | `2cf832032d5a50d61187a5db7359bafecd161b5990d21c82fe5fa4a2888bcb82` (68) |
| `V_std_mono_hyp_tight` | kripke-monotonicity: counterexample for hW | `propext` | `fe00eb00d86ed4dff2ade55fbe3abb0aa951600262defa99f627944ff261d209` | `2cf832032d5a50d61187a5db7359bafecd161b5990d21c82fe5fa4a2888bcb82` (68) |
| `V_std_mono_nonvacuous` | kripke-monotonicity: non-vacuity | `propext` | `7603c1b3eff95e77fbbb96cfc2ca721c9e752301c3eee960221bee91d26cc391` | `24dfd5a3181a217955b4cae1849dd06c17034ad9517f10ba46c7cf03d08e6149` (69) |
| `V_std_mono_val_hyp_tight` | kripke-monotonicity: counterexample for h | `propext` | `b38358073d3fd54909179bed1aa791990b24443803e72c2b58153d9552e19b61` | `2cf832032d5a50d61187a5db7359bafecd161b5990d21c82fe5fa4a2888bcb82` (68) |
| `adequacy_nil_ctx_hyp_tight` | adequacy: counterexample for empty; syntactic-type-safety-corollary: counterexample for empty | `Quot.sound`, `propext` | `63f4cb8033403005eb28c7695b3a8097ba478738961f04e6c945c1fce0cab045` | `bc88eeeaf682ec18d150be17b50ca8a7115096ccac3679c189d542c8558c7462` (88) |
| `adequacy_nonvacuous` | adequacy: non-vacuity | `Quot.sound`, `propext` | `0fccab674ed7c21453903d2d52323f240439fa01cd00c4305219731242e3febe` | `8a45e214729be61e98562b0ceff4cf3504b3fa217251a31a13eb2a96cb9196a8` (77) |
| `adequacy_semTyped_hyp_tight` | adequacy: counterexample for hsem | `propext` | `628bc5d1cc8e58660b40c0757a345670b7d180517c313cc1d2c7e0af2558d394` | `b2706f9f06728515f4c0181a60c90d4987aa3a9b0e89013b1cddca7176d48074` (78) |
| `cast_of_int_var_not_semTyped_nonvacuous` | cast-of-int-variable-has-no-semantic-type: non-vacuity | `propext` | `c17ca5cc511c3a8c9eb30469ff0a448a741355fd27e5ed39ed7a87f5a4007b8e` | `1869852e004c0e6695ab8306af6081fbe9f7582d35f0564bb324cec4504e0a9d` (76) |
| `cast_of_int_var_semTyped_anyLoc_ref` | cast-of-int-variable-has-no-semantic-type: positive control; cast-of-int-variable-has-no-semantic-type: counterexample for hinv | `Quot.sound`, `propext` | `7fdf5c00fedca7d6061682a5625b0921f6521a1ad38ee76047c7c1622568bc02` | `65c63db24faf8f3146ee74757223cc869dc3f69ff67366649f658a0e64919252` (79) |
| `cast_of_int_var_semTyped_safetyOnly` | cast-of-int-variable-has-no-semantic-type: positive control; cast-of-int-variable-has-no-semantic-type: counterexample for hclose | `Quot.sound`, `propext` | `afe5809521f332ac4d4ca956e87f180c102d1794cd84d9226c280dfc2214b45d` | `8b226952321515c5187fff2bbbc55aebe5ae4fd1d0c75e521902626bbf6d8bb7` (79) |
| `checkedRead_applied_semTyped` | checked-read-not-syntactically-typable: non-vacuity; checked-read-semantically-typed: non-vacuity | `Quot.sound`, `propext` | `b2b69295beea3038cdb38e423c84f285dcd2aac152cfd7984594920672839a2a` | `8a45e214729be61e98562b0ceff4cf3504b3fa217251a31a13eb2a96cb9196a8` (77) |
| `checkedRead_client_hyp_tight` | checked-read-syntactic-clients-safe: counterexample for hc | `propext` | `6f69a0652501183db9b94571ddedfe4784422d5f3a54b19562d198ffae122cd9` | `b643847514da771d023220b6933749d69978ce1024a6a2f1e4695891308b52ed` (64) |
| `checkedRead_single_var_ctx_tight` | checked-read-syntactic-clients-safe: counterexample for client | `propext` | `6fe51598fbf245680a32a456edd71a1e81ab38c6cca5984f756b7f4e73d739fb` | `d68e59194f2e4105bbf9719e86caf433436ca755b17f375a9565f5853c0a46c4` (63) |
| `client_hyp_tight` | semantic-let-compatibility: counterexample for hc; linking-safety-semantic-client: counterexample for hc; encapsulation-principle: counterexample for hc | `propext` | `2c48ee8af6b900b0515877417a842e567580d73ce9c4a62143b55d5d6138086f` | `f689ae93e9b13e3e0f50a3b76480a7b1d852e5fb4c5f968e5b42146324622a46` (89) |
| `fundamental_hasType_hyp_tight` | fundamental-theorem: counterexample for hty | `propext` | `4f867e96cbe8462624b3b6fb0c16ec3c4926e51ef461cbd32f704998a54304b1` | `708d55a05d4cf9299f13113bfeba024abeeb1f1067e8e898e8efaa53c9c3d5bb` (88) |
| `fundamental_nonvacuous` | fundamental-theorem: non-vacuity; syntactic-type-safety-corollary: non-vacuity | `propext` | `3d7f193338bdb60a5f2981a1b264ee8ef1ca091e9e0b22d609bd1ea1cddb70cb` | `01bd3ce8dfc3d1e07fc87d3880c4ad3a7e6d12920da4f900ec596685ce80de44` (31) |
| `hasType_client_semTyped_lib_nonvacuous` | encapsulation-principle: non-vacuity; checked-read-syntactic-clients-safe: non-vacuity | `Quot.sound`, `propext` | `ff7709fea43f27a4415900eea27a36d48de4319bfef2c5b5d3edd33b3b1915ea` | `ccbc322b2534cd7c4b143cc752454023fdf9c04bba5911fc3a8d6566d349127e` (89) |
| `lib_hyp_tight` | semantic-let-compatibility: counterexample for hlib; linking-safety-semantic-client: counterexample for hlib; encapsulation-principle: counterexample for hlib | `Quot.sound`, `propext` | `e3d402526c548ad7ef75a97be3c041fcfd0094e873b0403060d67d0fb0f89098` | `b76eaf9a3d2d638a6375158738ccaf2804d4dfbe9efc05854128ba4f06720ecb` (90) |
| `linking_interface_match_tight` | linking-safety-semantic-client: counterexample for matching; encapsulation-principle: counterexample for matching | `Quot.sound`, `propext` | `5daa992d31cf45ac683893215e51d72368429b34b4d6af8229554fdbca685d79` | `bc88eeeaf682ec18d150be17b50ca8a7115096ccac3679c189d542c8558c7462` (88) |
| `linking_lib_nil_ctx_tight` | linking-safety-semantic-client: counterexample for library; encapsulation-principle: counterexample for library | `Quot.sound`, `propext` | `9bfc10fa9398a93d42f56d906c2fa3a82fba60cef96d91889f3084fb43c1b91e` | `bc88eeeaf682ec18d150be17b50ca8a7115096ccac3679c189d542c8558c7462` (88) |
| `linking_single_var_ctx_tight` | linking-safety-semantic-client: counterexample for client; encapsulation-principle: counterexample for client | `propext` | `7a1906b6d757611ba21b74533819d087a10ce3af64ffd29293dbe32b0c8699e5` | `bc88eeeaf682ec18d150be17b50ca8a7115096ccac3679c189d542c8558c7462` (88) |
| `linking_structure_nonvacuous` | linking-safety-semantic-client: non-vacuity; encapsulation-principle: non-vacuity | `propext` | `9ad7c76153351e02c9887b6b0afe183721a645fa3d9aafe69f5521ab04c181c0` | `a2aed376a33bec0b271b701500bd936b8d3c2f3f4b067abf4f118325bc10d5d7` (38) |
| `safetyOnly_nil_ctx_hyp_tight` | safety-only-closure-collapses-typing-to-safety: counterexample for empty | `Quot.sound`, `propext` | `de9c9699d7877a8929337fad94965cf3abc421a5a1d911b633f2422d1100064e` | `505deda52313e60f471d50088c48baf088573c960af78f130dadf3e5aef0c661` (79) |
| `safetyOnly_semTyped_nil_iff_safe_nonvacuous` | safety-only-closure-collapses-typing-to-safety: non-vacuity | `propext` | `b29699f3c64456d09166a11f8eaca6cc07faf1639efdd75fefbfdca3531bf152` | `cbc22c1ed66b62bbe133ceec14e6802faf2b7b9c854030d9357079fd9efdf6f1` (81) |
| `semTyped_let_compat_nonvacuous` | semantic-let-compatibility: non-vacuity; linking-safety-semantic-client: non-vacuity | `Quot.sound`, `propext` | `c35d00e16f31889084bad56fa5ada7952218dcb75c0c6fabaf9f9d4bd59019c5` | `1828fc6e4860a5cacec7b6c9cc6f8b546f800f19d16e78e94aca89624db1eb31` (78) |
| `typing_relation_hyp_tight` | cast-of-int-variable-has-no-semantic-type: counterexample for hT | `propext` | `24d64079fcbe39988dccd5fe229bcaf797283779122f59bbf33053bd24e4b069` | `02c760722de5b30bbb8ac3d588542128d3276330384e7e7a37977a86be2ade79` (80) |
| `typing_relation_nonvacuous` | cast-of-int-variable-has-no-semantic-type: non-vacuity | `propext` | `eea03b690964310a59774831f617f0f8cb9d863dfa1fcadc6ba9a1b8e0da5d15` | `3c0784d2e58d768a100eab675d10e4c2ec3f6c66c04e6c300087895a483b03ed` (29) |

Supporting boundary theorems cited in the cards and in **Boundaries** (hashes recorded in `support/boundary_statements.json`, computed with the same algorithm; these names are not in `audit/statements.json`):

| Lean name | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
|---|---|---|---|
| `V_std_rejects_open_dead_lam` | `propext` | `961bef1691466a3dca05fc571a5be2d7fdadb67a62ff44af8f9d0e71afcf6642` | `2fd64997f5081a55871cd40cff188f980c3951067f1ced26bd126a077788e5ac` (69) |
| `captureRef_safeAndIn_synVal` | `propext` | `6a5357dc7fc5635ad64f370f0b2f87ab696c8683d5a02558e045a33920f6021f` | `f7301286fb22c1505ad3b1bb03ff5861b719395b7712fe19df9b333052600e6a` (68) |
| `cast_of_int_var_not_semTyped_anyLoc_nonRef` | `propext` | `3ff390a6d3ca3da560d955255ae83e13926faf2ed92a241d349966b32a457340` | `b95f8fa68e087dab254d31e60065e81e35b3fa6e17d09fd8b7988a70a9015495` (78) |
| `cellBoundRead_callWith7_safe` | `Quot.sound`, `propext` | `163a131923fdcb337ed59d3e37cafbff6fc1aea87c269b3696d5065badd63b92` | `67fab4b811403fc61b15e29c8339bcd7e1ba2fc17d70f97132978120a670f604` (49) |
| `cellBoundRead_not_semTyped` | `propext` | `3ea7ddf3f91b6c52375ae8929c285c81df6c5abaae3d16799bc8e433acf8532d` | `cbc0ba8c9e8e0627fb13c14a5fe196be8ec119a428881449d5568b8911d8a042` (77) |
| `checkedClient_semTyped_safe_not_hasType` | `Quot.sound`, `propext` | `3559f83cff87ee43a65f854f23da4446e6f347fcc05bb5061871736c16f7301b` | `82f7e4fe439fbe3be40212b091481e38779f90d7d61e343d5d546858fb3bb9a3` (90) |
| `nonKripke_breaks_open_let_compat` | `Quot.sound`, `propext` | `2b5114ed2a12d59701afdef9ca1050f5d3ce82d7e40f4452e2121d07ba0b51cc` | `2497ae5ebc04445831e0108fc73cc7a4319e5cb7a6b9fb1ccd042fec2884b1c7` (77) |
| `nonKripke_semTyped_client_nil_safe` | `Quot.sound`, `propext` | `1525209c98bd6b57205e3a2b456eeba141df2c50a022ce06c54a897e97ebe473` | `21be5872ccf4910d1abee3691b32c130b38bea4fd1a1509c793b65ea0fa71202` (78) |
| `probeCellZero_not_semTyped_nonKripke_nil` | `Quot.sound`, `propext` | `1d9a06b3349b6d3c1d95ca50ce85730cb380e132a7c7199037812587f53ec395` | `c15a45de40303c56a62a6b46a975605d9f13e67dcf18a3f174cb11423c55561d` (79) |
| `read_cast_zero_semTyped_ref_ctx` | `Quot.sound`, `propext` | `fe482910a6d9322314885a1654dab5933d7a390ac8c6a7b6e800f6cc0d800031` | `5438f51d5aa089460a273a011e605c8f8b418cd0d902a5bb9bfee9220ba7dd92` (76) |
| `restrictedCastRule_sound` | `propext` | `f09ff20b7141713d72841c007afc895083341e3f31b94da860c6bd9df58376a5` | `02c760722de5b30bbb8ac3d588542128d3276330384e7e7a37977a86be2ade79` (80) |
| `safe_of_reaches_value` | `propext` | `bd43e00c7d7fc0c26b087b21f4861b4431b50ec68df6b042a8826c0898354f58` | `d5c18eb886f2d8c7375c252f75ada6839f1659fe5fce685f0a912d83e8a36041` (47) |
| `semTyped_lam_compat_needs_closedAt` | `Quot.sound`, `propext` | `c94909d1b262899a1074163771675c738dac9cffeb28a03439f7dfa29a702fc1` | `5438f51d5aa089460a273a011e605c8f8b418cd0d902a5bb9bfee9220ba7dd92` (76) |
| `semTyped_nil_open_dead_var` | `propext` | `67da7f23841942268942832a9054c7e6bb43054a01f838cbd87b2b82200357c7` | `5438f51d5aa089460a273a011e605c8f8b418cd0d902a5bb9bfee9220ba7dd92` (76) |
| `sizeZeroOrForged_safe_nil_not_semTyped` | `propext` | `a5a5c272c63569b82882cabdfe977563370b35f48a5af9f3728d053ac714c9a7` | `50228bc78d5832ff67a948a285933a2519fcdc2f31d731040a0d31080d73698d` (78) |
| `synVal_iff_isValue_and_hasTypeStore` | `propext` | `fd28eae01c4d0f15e69c92caefeef690d6e0b761c58b9556ba983c96201a7f6a` | `f495890c452c0e0c18d886770d229189d831eb82f1379c0f59d812bea93dbf0c` (39) |
| `synVal_pos` | `propext` | `d39208a3c5cf15c07ee952ffbe29de0ed3e511e4f86143adce7130db25a3750a` | `ecebb0cc114c012589d3a4589bad1b3a5df146faacce909d7c15ead516173feb` (41) |
| `uncheckedRead_not_semTyped` | `propext` | `ae26ada3b828a3e314b9d8721931c97890bead5b3b3ea69e503e3b4d9f8440dd` | `719a583532c9bff59532efbad66111ab27b6a6a58de23eea5d9700799848da09` (77) |

### Tier basis: quoted sources

Tiers record prior mechanization, not depth. R11 (`cast-of-int-variable-has-no-semantic-type`), R13 (`safety-only-closure-collapses-typing-to-safety`), and R17 (`syntactic-value-interpretation-rejects-encapsulated-library`) are `T1` because the closest prior statements are informal remarks in Timany et al. 2024 (quoted from the authors' copy of the article; page numbers of the journal version):

* Section 3.2, p. 40:15 (analogue of R11, about the unsafe `assert` feature): “However, seeing as there is no type in MyLang that would ensure that e satisfies this property, assert is an example of an unsafe feature.”
* Section 3.2, p. 40:15 (analogue of R17, about the symbol ADT that uses `assert`): “But syntactic type soundness—by restricting attention to syntactically well-typed programs—does not offer us a means to prove this.”
* Section 4.1, p. 40:16 (background for R1's `definitional` depth and for R13): “This theorem is usually almost trivial to prove, because, as explained above, it is typically more or less baked into the extensional definition of semantic typing.” (The theorem referred to is adequacy.) The safety-only ablation of R13 itself does not appear there.
* The mechanized Theorem 7.2 of that article (“gremlin is Semantically Ill-Typed”, p. 40:52) concerns an abstraction-breaking operator, not a typing rule for the unsafe feature and not a recipe parameterization, so it is not a mechanized form of R11.

The `T0` results restate known theorems. Most restate mechanized theorems: Theorem 6.5 (fundamental theorem, p. 40:44), Theorem 6.6 (adequacy, p. 40:45), Corollary 6.7 (semantic type soundness, p. 40:45), Theorem 7.1 (the symbol ADT is semantically well typed, p. 40:46) of Timany et al. 2024, and the encapsulation results of Jung et al. 2018. R18 (`kripke-monotonicity`, `V_std_mono`) restates the standard world-extension (Kripke) monotonicity property of logical relations for state, as in the works cited on its card (Jung and Tiuryn 1993; Pitts and Stark 1998; Ahmed, Appel and Virga 2002; Ahmed 2004). In each case the prior result is for a different and much richer language than this toy.

### Primary sources

* Amin Timany, Robbert Krebbers, Derek Dreyer, Lars Birkedal. "A Logical Approach to Type Soundness." Journal of the ACM 71(6), Article 40, 75 pages, November 2024. DOI 10.1145/3676954. Authors' copy: https://robbertkrebbers.nl/research/articles/logical_type_soundness.pdf. Coq development: https://gitlab.mpi-sws.org/iris/examples, directory `theories/logrel/F_mu_ref_conc`.
* Ralf Jung, Jacques-Henri Jourdan, Robbert Krebbers, Derek Dreyer. "RustBelt: Securing the Foundations of the Rust Programming Language." Proceedings of the ACM on Programming Languages 2(POPL), Article 66, January 2018. DOI 10.1145/3158154. Coq development: https://gitlab.mpi-sws.org/iris/lambda-rust.
* Ralf Jung. "Understanding and Evolving the Rust Programming Language." PhD thesis, Saarland University, 2020. DOI 10.22028/D291-31946.
* Andrew K. Wright, Matthias Felleisen. "A Syntactic Approach to Type Soundness." Information and Computation 115(1):38–94, November 1994. DOI 10.1006/inco.1994.1093.
* Robin Milner. "A Theory of Type Polymorphism in Programming." Journal of Computer and System Sciences 17(3):348–375, December 1978. DOI 10.1016/0022-0000(78)90014-4.
* Andrew W. Appel, David McAllester. "An Indexed Model of Recursive Types for Foundational Proof-Carrying Code." ACM TOPLAS 23(5):657–683, September 2001. DOI 10.1145/504709.504712.
* Amal Jamil Ahmed. "Semantics of Types for Mutable State." PhD thesis, Princeton University, 2004; Princeton CS Technical Report TR-713-04, https://www.cs.princeton.edu/techreports/2004/713.pdf.
* Amal J. Ahmed, Andrew W. Appel, Roberto Virga. "A Stratified Semantics of General References Embeddable in Higher-Order Logic." LICS 2002, pp. 75–86. DOI 10.1109/LICS.2002.1029818.
* Andrew M. Pitts. "Typed Operational Reasoning." In B. C. Pierce (ed.), Advanced Topics in Types and Programming Languages, Chapter 7, pp. 245–289. MIT Press, 2005. ISBN 978-0-262-16228-9. Author copy: https://www.cl.cam.ac.uk/~amp12/papers/typor/typor.pdf.
* Andrew M. Pitts, Ian D. B. Stark. "Operational Reasoning for Functions with Local State." In A. D. Gordon, A. M. Pitts (eds.), Higher Order Operational Techniques in Semantics, pp. 227–273. Cambridge University Press, 1998. Author copy: https://www.cl.cam.ac.uk/~amp12/papers/operfl/operfl.pdf.
* Achim Jung, Jerzy Tiuryn. "A New Characterization of Lambda Definability." TLCA 1993, LNCS 664, pp. 245–257. DOI 10.1007/BFb0037110.
* Jeremy Siek. "Declarative Semantics for Functional Languages." Archive of Formal Proofs, July 2017. https://www.isa-afp.org/entries/Decl_Sem_Fun_PL.html.
* Yuquan Fu, Carlo Angiuli, Sam Tobin-Hochstadt. "Revisiting Soundness for Occurrence Typing, Semantically." arXiv:2609.16299, 2026 (a semantic type soundness proof with step-indexed logical relations, formalized in Lean).
* The Rust Reference, "Behavior considered undefined", https://doc.rust-lang.org/reference/behavior-considered-undefined.html (rules `undefined.invalid` and `undefined.validity.reference-box`).

For the `T1` ablation results R12–R16, the cited sources establish only the positive ingredient of the standard model; each card's prior-art entries say which ingredient a source establishes and that it does not define or refute the ablated model.


## Revalidation

Requirements: `elan` (so that `lake` uses the toolchain pinned in `lean/lean-toolchain`, `leanprover/lean4:v4.34.1`) and `python3`. No network access is needed after the toolchain is installed.

**Primary check.** From the package directory:

```sh
python3 support/revalidate.py .
```

It copies `lean/` to a temporary directory (the package is not modified) and checks: (1) `lake build` succeeds; (2) no Lean source contains `sorry`, `admit`, `native_decide`, or an `axiom` declaration; (3) every declaration of the `ToySemType` modules depends only on `propext`, `Classical.choice`, `Quot.sound` (via `Lean.collectAxioms`); (4) for every Lean name referenced by `results.json` and every name in `audit/statements.json`, the SHA-256 of the statement (Lean `repr` of its type) and of its definition closure (the sorted `name : type [:= value]` lines of every `ToySemType` constant reachable from the statement through types and non-theorem values; theorem bodies excluded) equals the recorded value. It prints `REVALIDATED` and exits with status 0 iff all checks pass.

**Equivalent manual check** (also covers the supporting boundary theorems in `support/boundary_statements.json`). `lean/RevalidationAudit.lean` is outside the library target; it prints per-declaration axioms and the statement and closure text of every card-referenced name and every supporting boundary theorem:

```sh
cd lean
lake build
lake env lean RevalidationAudit.lean > /tmp/revalidation_audit.out
cd ..
python3 - <<'EOF'
import hashlib, json, re
out = open('/tmp/revalidation_audit.out').read()
a = json.loads(re.search(r'REVALIDATION_AUDIT_JSON (\{.*\})', out).group(1))
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
bad = [d['name'] for d in a['decls'] if set(d['axioms']) - allowed]
print('declarations:', len(a['decls']), 'with disallowed axioms:', bad)
rec = json.load(open('audit/statements.json'))['statements']
rec.update(json.load(open('support/boundary_statements.json'))['statements'])
mism = []
for s in a['stmts']:
    if s.get('missing'):
        mism.append(s['name']); continue
    got = {'statement_sha256': hashlib.sha256(s['type_repr'].encode()).hexdigest(),
           'closure_sha256': hashlib.sha256('\n'.join(s['closure']).encode()).hexdigest(),
           'closure_size': len(s['closure'])}
    if rec.get(s['name']) != got:
        mism.append(s['name'])
print('names checked:', len(a['stmts']), 'mismatches:', mism)
EOF
```

Expected output: no declaration with disallowed axioms and an empty mismatch list. A passing run establishes that the recorded statements, with the recorded definitions, are kernel-checked under the pinned toolchain; it does not re-establish any `derived (modeling bridge)` claim.

**Cheaper targeted checks.** To see whether a change to the Lean sources affects a particular card, rebuild and compare that card's closure hash: an unchanged statement hash with a changed closure hash means a definition the statement depends on has changed, and the card's prose must be re-read against the new definition. Under a different Lean toolchain the `repr`-based hashes may change even when the mathematics does not; in that case re-run the build and axiom checks and compare the statements and definitions textually instead of by hash.
