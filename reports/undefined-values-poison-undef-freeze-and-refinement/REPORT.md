# Undefined values in a toy IR: undef, poison, freeze, and refinement (Lean 4)

## Summary

This package mechanizes in Lean 4 (core library only) three value models for undefined
values in a small first-order expression language over `w`-bit wrapping integers: an
**undef model** (a value is a nonempty set of integers and every use chooses independently),
a **poison model with optional `freeze`** (poison propagates through arithmetic, branching on
poison is UB, and `freeze` turns poison into an arbitrary but fixed integer), and an
**eager reading of uninitialised inputs** (reading one is UB). It proves 22 results about
outcome-set refinement (target first: `RefinesU w tgt src`, `RefinesP w tgt src`) and about
classic rewrites: changing the number of uses of a value, GVN on a branch condition, hoisting
a branch out of a conditional ("loop unswitching"), and the laws of `freeze`. All results are
theorems about the toy models; these theorems neither establish nor refute the corresponding
claims about LLVM IR or Rust, and every connection to them is a separately labelled modeling
bridge under **Findings**.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

The results, each stated for every width `w` unless a bound is given (the plain-language
claim of each card, verbatim):

1. **`refinement-preorder`** (T0, theorem). In the undef model (over environments that bind every variable to a nonempty set) and in the poison(+freeze) model (semP on all expressions, including freeze), at every width w, program refinement - in every admissible environment, either the source may reach UB or every target outcome is a value refining some source value - is reflexive and transitive.

2. **`source-ub-refined-by-anything`** (T0, theorem). Reference point (definitional): in both models, at every width, a source program that may reach UB in every admissible environment (in particular the program ub) is refined by every target program; 'may reach UB' means that at least one of the source's nondeterministic outcomes is UB.

3. **`refinement-congruence`** (T0, theorem). In the undef model (over environments of nonempty sets) and in the poison(+freeze) model, at every width, refinement is a congruence for every construct: if each argument of +, *, the equality test, if, let (bound expression and body) or freeze in the target refines the corresponding argument in the source, the whole target expression refines the whole source expression.

4. **`undef-observational-refinement-not-congruence`** (T1, counterexample). In the undef model (environments of nonempty sets), for every width w ≥ 1 and variables x, y: x observationally refines freeze x (comparing only the integers a program may produce, and UB), but let y := x; y + y does not observationally refine let y := freeze x; y + y; so observational refinement is not a congruence for let.

5. **`merge-uses-sound`** (T0, theorem). At every width, for every expression e (including expressions containing freeze or ub), rewriting e + e to 2 * e is a refinement in the undef model (over environments of nonempty sets) and in the poison(+freeze) model.

6. **`undef-duplicate-use-unsound`** (T0, impossibility). In the undef model (environments of nonempty sets), at every width w ≥ 1 and for every variable x, rewriting 2 * x to x + x is not a refinement: with x bound to {0, 1} the target can produce the odd integer 1, which 2 * x cannot.

7. **`poison-duplicate-freeze-free-use-sound`** (T0, theorem). In the poison(+freeze) model, at every width, for every freeze-free expression e (in particular every variable), rewriting 2 * e to e + e is a refinement; together with merge-uses-sound, both directions are sound for freeze-free e.

8. **`poisonFreeze-duplicate-frozen-operand-unsound`** (T0, impossibility). In the poison + freeze model, at every width w ≥ 1 and for every variable x, rewriting 2 * freeze x to freeze x + freeze x is not a refinement: with x ↦ poison the two freezes may pick 0 and 1, giving the odd integer 1, while every outcome of 2 * freeze x is even.

9. **`poison-gvn-sound`** (T0, theorem). In the poison(+freeze) model (branching on poison is UB), at every width, for all variables x, y and expressions t, e, rewriting if x = y then t else e to if x = y then (let y := x; t) else e is a refinement.

10. **`undef-gvn-unsound`** (T0, impossibility). In the undef model (environments of nonempty sets; branching on an undef value is a nondeterministic choice), for every width w ≥ 1 and distinct variables x ≠ y, the GVN rewrite with then-branch y and else-branch 0 - if x = y then y else 0 to if x = y then (let y := x; y) else 0 - is not a refinement: with x ↦ {0, 1} and y ↦ {1} the comparison may succeed while the later use of x observes 0.

11. **`poison-unswitch-without-freeze-unsound`** (T0, impossibility). In the poison(+freeze) model (branching on poison is UB), for every width w, distinct condition variables c ≠ d, branches a, b and literal else-branch n, rewriting if c then (if d then a else b) else n to if d then (if c then a else n) else (if c then b else n) is not a refinement: with c ↦ 0 and d ↦ poison the source returns n while the target branches on poison.

12. **`undef-unswitch-without-freeze-sound`** (T0, theorem). In the undef model (environments of nonempty sets; branching on an undef value is a nondeterministic choice), at every width, for every outer condition ec, every inner condition ed that reaches UB in no inhabited environment, and all branches a, b, e, rewriting if ec then (if ed then a else b) else e to if ed then (if ec then a else e) else (if ec then b else e) is a refinement; in particular for condition variables c, d (equal or not).

13. **`poisonFreeze-unswitch-with-freeze-sound`** (T0, theorem). In the poison + freeze model, at every width, for every outer condition ec, every inner condition ed that reaches UB in no environment, and every variable t not free in ec, a, b, e, rewriting if ec then (if ed then a else b) else e to let t := freeze ed; if t then (if ec then a else e) else (if ec then b else e) is a refinement; in particular for condition variables c, d with t ≠ c.

14. **`freeze-identity-on-non-poison`** (T0, theorem). In the poison + freeze model, at every width: if no outcome of e is poison in environment ρ then freeze e has exactly the outcomes of e in ρ (a definitional reference point); consequently, if e never yields poison, rewriting freeze e to e is a refinement, and in particular rewriting freeze (freeze e) to freeze e is a refinement (also in the undef model, over environments of nonempty sets).

15. **`freeze-insertion-sound`** (T0, theorem). At every width and for every expression e, rewriting e to freeze e is a refinement in the poison + freeze model and in the undef model (over environments of nonempty sets).

16. **`freeze-removal-unsound`** (T0, impossibility). Rewriting freeze x to x (x a variable) is not a refinement: in the poison + freeze model at every width (with x ↦ poison the target yields poison, which refines no integer), and in the undef model (over environments of nonempty sets) at every width w ≥ 1 (with x ↦ {0, 1} the target's value set is contained in no source singleton).

17. **`frozen-value-used-twice-even`** (T0, theorem). In the poison + freeze model, at every width w and in every environment, let a := freeze x; a + a has at least one outcome and every outcome is an even integer (never poison or UB); whereas with x ↦ poison, freeze x + freeze x has every w-bit integer as an outcome, in particular (for w ≥ 1) an odd one.

18. **`duplicate-freeze-unsound`** (T0, impossibility). In the poison + freeze model, at every width w ≥ 1 and for all variables x, a, duplicating a freeze - rewriting let a := freeze x; a + a to freeze x + freeze x - is not a refinement (with x ↦ poison the target may be odd, the source never is).

19. **`merge-freeze-sound`** (T0, theorem). In the poison + freeze model, at every width, for every expression e and variable a, merging two freezes of the same operand - rewriting freeze e + freeze e to let a := freeze e; a + a - is a refinement.

20. **`poison-refines-eager-uninit`** (T1, theorem). For every width w, eager environment ρ (each input initialized or not) and fixed program e: either the eager-uninitialized evaluation of e (reading an uninitialized input is UB) may reach UB, or every poison(+freeze)-model outcome of e on the same environment read with uninitialized ↦ poison is equal to an eager outcome; in particular the poison(+freeze)-model outcomes refine the eager ones.

21. **`eager-uninit-does-not-refine-poison`** (T1, counterexample). For every width w, with every input uninitialized, the program let y := x; 0 (which reads x and discards it) is UB in the eager-uninitialized reading but returns 0 in the poison reading, so eager outcomes do not refine poison outcomes in general.

22. **`semantics-total`** (T0, theorem). At every width, every expression has at least one outcome in every poison(+freeze)-model environment and in every undef-model environment that binds each variable to a nonempty set; consequently RefinesP and RefinesU are equivalent to the variants that additionally require a nonempty target outcome list, so no refinement result in this package holds because a target has no outcomes.

Read the non-claims before relying on a result: the non-claims shared by all results (`S1`–`S4`: toy language, missing features, no operation creates an invalid value, target-first argument order) and those of each result are listed first under **Boundaries**, followed by the escape hatches of the impossibility results.

## Applicability

**What the results are about.** Every result is a theorem about the Lean definitions in
`lean/ToyUB/` (namespace `Toy.UB`), stated for an arbitrary bit width `w : Nat` unless the
card says otherwise. The definitions form a *toy model*: a first-order expression language
over `w`-bit wrapping integers with `let`, `+`, `*`, an equality test `eq`, `if`, `freeze`,
and an explicit undefined-behaviour construct `ub`, interpreted in three value models:

- the **undef model** (`semU`, refinement `RefinesU`): a value is a nonempty set of `w`-bit
  integers and every use of a value chooses independently from its set; `if` on a set is a
  nondeterministic choice of branch (never UB); `freeze` picks one element;
- the **poison model** and **poison + freeze model** (`semP`, refinement `RefinesP`): a
  value is an integer or `poison`; arithmetic and `eq` propagate `poison`; branching on
  `poison` is UB; `freeze poison` may yield any integer. The poison model is `semP` on
  freeze-free programs; a theorem stated for all expressions under `semP` is called a
  *poison(+freeze) model* result;
- an **eager-uninitialised reading** (`semE`, refinement `RefinesE`): each input is
  initialised (`some v`) or uninitialised (`none`), and reading an uninitialised input is
  immediate UB.

**What the definitions are meant to capture.** The undef and poison models are meant to
capture, in a setting without memory, the per-use nondeterminism of LLVM's `undef`, the
propagation of LLVM's `poison` with UB on a branch condition, and LLVM's `freeze`, as
described in the LLVM 19.1.0 Language Reference and by Lee et al. (PLDI 2017). Refinement is
the per-input, outcome-set refinement of Alive2 (Lopes et al., PLDI 2021, Section 5.2) with
the value refinements of its Figure 4. The eager reading mirrors, for whole integer inputs
only, the Rust Reference (Rust 1.83.0) rule that an integer must not be obtained from uninitialized memory.
None of these correspondences is kernel-checked: each is stated in **Findings** as a separate
`Basis: derived (modeling bridge)` claim with its reasoning.

**Known gaps between the toy and real systems.**

1. *Undef values are sets, not bit patterns.* `USet w := BitVec w → Bool` admits arbitrary
   nonempty subsets of the `w`-bit integers (the power-set reading of Lopes et al., PLDI 2021,
   Figure 2), including sets that do not arise from a pattern of defined and undefined bits.
2. *Branching on undef.* In the undef model, `if` commits to a branch chosen
   nondeterministically and is never UB (`semU_ite_commits_example`). The LLVM 19.1.0
   Language Reference states the rule "Branching on an undefined value is undefined
   behavior", while an example in the same section says undefined `select` (and conditional
   branch) conditions "can go either way". The undef-model results that involve `if` describe
   only the nondeterministic-branch reading. There is no `select` and no `phi`.
3. *No operation creates an invalid value from valid operands.* `+` and `*` wrap modulo
   `2 ^ w`; there are no `nsw`/`nuw` flags, shifts, division or remainder. Invalid values enter
   only through inputs; UB enters only through `ub` or, in the poison model, through branching.
4. *Equality test.* `eq a b` yields `1` or `0` read modulo `2 ^ w`; at width `0` every
   integer is `0`, so `eq` always yields `0` there.
5. *Eager reading.* Inputs are wholly initialised or wholly uninitialised; there are no
   bytes, padding, unions or untyped copies; `let` binds only initialised values; and
   `freeze x` with `x` uninitialised is UB because the read happens first
   (`semE_freeze_uninit_example`). LLVM's `noundef` attribute is not modelled.
6. *Missing features.* No memory, pointers, loads or stores, loops, function calls,
   floating point, or integer types of different widths. "Loop unswitching" is modelled by
   an outer conditional that may skip an inner branch; "GVN" by an equality learned from an
   `if` condition and substituted through a `let`.
7. *Admissible environments.* `RefinesU` quantifies only over environments that bind every
   variable to a nonempty set (`UInhabited`); `RefinesP` quantifies over all environments.
8. *Argument order.* `RefinesU w tgt src` and `RefinesP w tgt src` put the target first:
   rewriting `src` to `tgt` is sound exactly when the statement holds.

**Widths.** Every main result is stated for all `w`; unsoundness results hold for every
`w ≥ 1` (some also at `w = 0`). Fixed-width statements are only definition examples,
tightness counterexamples, non-vacuity instances (width 2 or 3), width-0 controls, and a few
concrete supporting counterexamples at width 2.

**Subjects and how they relate.** The Lean 4 toolchain `leanprover/lean4` `v4.34.1` (commit
`5045d0056413266e57c625dcd7c365b10e377c52`) is the checker: every theorem was elaborated and
kernel-checked with it, using core Lean only (no Mathlib, no other dependencies). Behaviour
under other Lean versions was not examined. The LLVM Language Reference at LLVM 19.1.0 (tag
`llvmorg-19.1.0`, commit `a4bf6cd7cfb1a1421ba92bca9d017b49936c55e4`) is the specification
quoted by the modeling-bridge claims; other LLVM versions were not examined. The papers listed
in `REPORT.json` are prior art that the cards cite; the report interprets them through the toy
model and does not re-verify their results. The Rust Reference at Rust 1.83.0 ("Behavior
considered undefined", identified by its versioned URL) is the source of the rule that the
eager-uninitialised reading mirrors for whole integer inputs; it is cited only on results 20
and 21 (prior art and modeling-bridge claims), and other Rust versions, as well as the behaviour of
any Rust compiler, were not examined. Jung's 2019 blog post is informal prior art cited only on
result 20, for describing uninitialized memory as bytes that may be absent and relating an absent
byte to LLVM's poison; no kernel-checked result depends on it. The post is a web page that has been edited since
publication (its own notes record updates dated 2022-11-17 and 2024-10-18), so its URL and date do
not identify a fixed text. The passages cited appear both in the page as fetched on 2026-11-20 and
in revision `ad96fffd4618ba6e126cc16214a04cf3902f5d99` of the post's source file
(`personal/_posts/2019-07-14-uninit.md`) in the site's public Git repository
(https://git.ralfj.de/web.git), which was the latest revision of that file on that date;
`REPORT.json` records that revision.

## Findings

**Evidence roles.** Each result below is a set of theorems checked by the Lean kernel under
the toolchain named in **Applicability**; this is recorded as
`Basis: execution (Lean kernel check)`. Any statement connecting a result to LLVM, Alive2 or
Rust is a separate claim recorded as `Basis: derived (modeling bridge)`, with its reasoning; it
is not kernel-checked and holds only to the extent that the toy definitions capture the real
semantics (see the gaps listed in **Applicability**). "Proved" in this report never means
"true of LLVM or Rust".

**How to read a card.** *Tier* is `T0` (a known result restated for the toy) or `T1` (folklore
made precise); no result is claimed novel. The *hypothesis ledger* lists every hypothesis of
the stated theorems with its purpose and tightness; `tight` means a named Lean counterexample
proves that all other hypotheses hold and the conclusion fails. *Depth* is `definitional`,
`shallow` or `substantive`. The *non-vacuity witness* is a proved instance satisfying all
hypotheses. For impossibility results, *positive controls* are proved nearby settings where the
conclusion fails (the rewrite becomes sound). Each card's non-claims are listed under
**Boundaries**, together with the non-claims shared by all results.

### Definitions

The definitions below are quoted verbatim from `lean/ToyUB/` (doc comments omitted). An outcome
list `List (Outcome V)` is read as a finite set of possible outcomes: `ub` or a value. Read
informally:

- `OutRef R T S` ("target outcomes `T` refine source outcomes `S`") holds iff the source may
  reach UB (one UB outcome suffices: existential over the source's nondeterministic choices),
  or every target outcome is a value that `R`-refines some source value. It accepts an empty
  target list (`outRef_example_empty_target`); `OutRefNE` does not, and the two coincide for
  every program of this package (result `semantics-total`).
- In the undef model, `USet w` is a membership predicate; `map2 f A B = {f a b | a ∈ A, b ∈ B}`
  with independent choices; `Sub t s` is `t ⊆ s`; `semU` binds a `let` variable to the whole
  set, so its uses still choose independently; `freeze` returns one singleton outcome per
  element; `if` has the `then` outcomes if the condition set contains a nonzero integer and the
  `else` outcomes if it contains `0`.
- In the poison model, `PVal.Refines t s` holds iff `s = poison` or `t = s`; `semP` maps a
  branch on `poison` to `[ub]` and `freeze poison` to one outcome per `w`-bit integer.
- `UBFreeU w e` / `UBFreeP w e`: `e` has no UB outcome in any admissible environment.
- `semE` reads an uninitialised input (`none`) as UB; `toPoisonEnv` maps `none` to `poison`.

#### Syntax and outcomes (`lean/ToyUB/Syntax.lean`)

```lean
abbrev Var := Nat

inductive Expr where
  | var (x : Var)
  | const (n : Nat)
  | add (a b : Expr)
  | mul (a b : Expr)
  | eq (a b : Expr)
  | ite (c t e : Expr)
  | letE (x : Var) (a b : Expr)
  | freeze (a : Expr)
  | ub
  deriving DecidableEq, Repr

def freeIn (x : Var) : Expr → Bool
  | var y => x == y
  | const _ => false
  | add a b => freeIn x a || freeIn x b
  | mul a b => freeIn x a || freeIn x b
  | eq a b => freeIn x a || freeIn x b
  | ite c t e => freeIn x c || freeIn x t || freeIn x e
  | letE y a b => freeIn x a || (x != y && freeIn x b)
  | freeze a => freeIn x a
  | ub => false

def FreezeFree : Expr → Bool
  | var _ => true
  | const _ => true
  | add a b => FreezeFree a && FreezeFree b
  | mul a b => FreezeFree a && FreezeFree b
  | eq a b => FreezeFree a && FreezeFree b
  | ite c t e => FreezeFree c && FreezeFree t && FreezeFree e
  | letE _ a b => FreezeFree a && FreezeFree b
  | freeze _ => false
  | ub => true

inductive Outcome (V : Type) where
  | ub
  | val (v : V)
  deriving DecidableEq, Repr

def isUB : Outcome V → Bool
  | ub => true
  | val _ => false

def LeVal (R : V → V → Prop) : Outcome V → Outcome V → Prop
  | val t, val s => R t s
  | _, _ => False

def MayUB (S : List (Outcome V)) : Prop := ∃ o ∈ S, o.isUB = true

def OutRef (R : V → V → Prop) (T S : List (Outcome V)) : Prop :=
  MayUB S ∨ ∀ o ∈ T, ∃ o' ∈ S, Outcome.LeVal R o o'

def OutRefNE (R : V → V → Prop) (T S : List (Outcome V)) : Prop :=
  MayUB S ∨ ((S ≠ [] → T ≠ []) ∧ ∀ o ∈ T, ∃ o' ∈ S, Outcome.LeVal R o o')

def bind1 (A : List (Outcome α)) (f : α → List (Outcome β)) : List (Outcome β) :=
  A.flatMap fun
    | .ub => [.ub]
    | .val a => f a

def bind2 (A : List (Outcome α)) (B : List (Outcome β)) (f : α → β → List (Outcome γ)) :
    List (Outcome γ) :=
  bind1 A fun a => bind1 B fun b => f a b

def update (ρ : Var → α) (x : Var) (v : α) : Var → α :=
  fun y => if y = x then v else ρ y

def allBV (w : Nat) : List (BitVec w) := (List.range (2 ^ w)).map (BitVec.ofNat w)

def eqBit {w : Nat} (x y : BitVec w) : BitVec w := if x = y then 1#w else 0#w
```

#### Undef model (`lean/ToyUB/Undef.lean`)

```lean
abbrev USet (w : Nat) := BitVec w → Bool

def single (c : BitVec w) : USet w := fun z => decide (z = c)

def map2 (f : BitVec w → BitVec w → BitVec w) (A B : USet w) : USet w :=
  fun z => decide (∃ a b, A a = true ∧ B b = true ∧ f a b = z)

def HasNonzero (C : USet w) : Bool := decide (∃ z, C z = true ∧ z ≠ 0#w)

def Sub (t s : USet w) : Prop := ∀ z, t z = true → s z = true

def Nonempty (A : USet w) : Prop := ∃ z, A z = true

def semU (w : Nat) : (Var → USet w) → Expr → List (Outcome (USet w))
  | ρ, .var x => [.val (ρ x)]
  | _, .const n => [.val (USet.single (BitVec.ofNat w n))]
  | ρ, .add a b => bind2 (semU w ρ a) (semU w ρ b) fun A B => [.val (USet.map2 (· + ·) A B)]
  | ρ, .mul a b => bind2 (semU w ρ a) (semU w ρ b) fun A B => [.val (USet.map2 (· * ·) A B)]
  | ρ, .eq a b => bind2 (semU w ρ a) (semU w ρ b) fun A B => [.val (USet.map2 eqBit A B)]
  | ρ, .ite c t e => bind1 (semU w ρ c) fun C =>
      (if C.HasNonzero then semU w ρ t else []) ++ (if C 0#w then semU w ρ e else [])
  | ρ, .letE x a b => bind1 (semU w ρ a) fun A => semU w (update ρ x A) b
  | ρ, .freeze a => bind1 (semU w ρ a) fun A =>
      (allBV w).filterMap fun v => if A v then some (.val (USet.single v)) else none
  | _, .ub => [.ub]

def UInhabited {w : Nat} (ρ : Var → USet w) : Prop := ∀ x, (ρ x).Nonempty

def RefinesU (w : Nat) (tgt src : Expr) : Prop :=
  ∀ ρ : Var → USet w, UInhabited ρ → OutRef USet.Sub (semU w ρ tgt) (semU w ρ src)

def ObsU {w : Nat} (S : List (Outcome (USet w))) (z : BitVec w) : Prop :=
  ∃ o ∈ S, (match o with | .val A => A z | .ub => false) = true

def ObsRefinesU (w : Nat) (tgt src : Expr) : Prop :=
  ∀ ρ : Var → USet w, UInhabited ρ →
    MayUB (semU w ρ src) ∨
      (¬ MayUB (semU w ρ tgt) ∧ ∀ z, ObsU (semU w ρ tgt) z → ObsU (semU w ρ src) z)
```

#### Poison and poison + freeze models (`lean/ToyUB/Poison.lean`)

```lean
inductive PVal (w : Nat) where
  | poison
  | int (v : BitVec w)
  deriving DecidableEq, Repr

def lift2 (f : BitVec w → BitVec w → BitVec w) : PVal w → PVal w → PVal w
  | int a, int b => int (f a b)
  | _, _ => poison

def Refines : PVal w → PVal w → Prop
  | _, poison => True
  | t, int v => t = int v

def semP (w : Nat) : (Var → PVal w) → Expr → List (Outcome (PVal w))
  | ρ, .var x => [.val (ρ x)]
  | _, .const n => [.val (.int (BitVec.ofNat w n))]
  | ρ, .add a b => bind2 (semP w ρ a) (semP w ρ b) fun u v => [.val (PVal.lift2 (· + ·) u v)]
  | ρ, .mul a b => bind2 (semP w ρ a) (semP w ρ b) fun u v => [.val (PVal.lift2 (· * ·) u v)]
  | ρ, .eq a b => bind2 (semP w ρ a) (semP w ρ b) fun u v => [.val (PVal.lift2 eqBit u v)]
  | ρ, .ite c t e => bind1 (semP w ρ c) fun
      | .poison => [.ub]
      | .int z => if z ≠ 0#w then semP w ρ t else semP w ρ e
  | ρ, .letE x a b => bind1 (semP w ρ a) fun v => semP w (update ρ x v) b
  | ρ, .freeze a => bind1 (semP w ρ a) fun
      | .poison => (allBV w).map fun v => .val (.int v)
      | .int v => [.val (.int v)]
  | _, .ub => [.ub]

def RefinesP (w : Nat) (tgt src : Expr) : Prop :=
  ∀ ρ : Var → PVal w, OutRef PVal.Refines (semP w ρ tgt) (semP w ρ src)
```

#### UB-freedom (`lean/ToyUB/Unswitch.lean`)

```lean
def UBFreeU (w : Nat) (e : Expr) : Prop :=
  ∀ ρ : Var → USet w, UInhabited ρ → ¬ MayUB (semU w ρ e)

def UBFreeP (w : Nat) (e : Expr) : Prop :=
  ∀ ρ : Var → PVal w, ¬ MayUB (semP w ρ e)
```

#### Eager-uninitialised reading (`lean/ToyUB/Uninit.lean`)

```lean
def semE (w : Nat) : (Var → Option (BitVec w)) → Expr → List (Outcome (BitVec w))
  | ρ, .var x => match ρ x with
    | none => [.ub]
    | some v => [.val v]
  | _, .const n => [.val (BitVec.ofNat w n)]
  | ρ, .add a b => bind2 (semE w ρ a) (semE w ρ b) fun u v => [.val (u + v)]
  | ρ, .mul a b => bind2 (semE w ρ a) (semE w ρ b) fun u v => [.val (u * v)]
  | ρ, .eq a b => bind2 (semE w ρ a) (semE w ρ b) fun u v => [.val (eqBit u v)]
  | ρ, .ite c t e => bind1 (semE w ρ c) fun z => if z ≠ 0#w then semE w ρ t else semE w ρ e
  | ρ, .letE x a b => bind1 (semE w ρ a) fun v => semE w (update ρ x (some v)) b
  | ρ, .freeze a => semE w ρ a
  | _, .ub => [.ub]

def toPoisonEnv {w : Nat} (ρ : Var → Option (BitVec w)) : Var → PVal w :=
  fun x => match ρ x with
    | none => .poison
    | some v => .int v

def Outcome.toP {w : Nat} : Outcome (BitVec w) → Outcome (PVal w)
  | .ub => .ub
  | .val v => .val (.int v)

def RefinesE (w : Nat) (tgt src : Expr) : Prop :=
  ∀ ρ : Var → Option (BitVec w), OutRef (fun a b => a = b) (semE w ρ tgt) (semE w ρ src)
```

#### Intended positive and negative examples of the definitions (proved)

The predicates, relations and semantics above have proved examples that they must admit and examples they must reject; the helper functions `bind1`, `bind2`, `update`, `allBV`, `Outcome.isUB` and `PVal.lift2` are exercised through the semantics examples. The examples use two fixed width-2 environments: `ρ01` binds variable `0` to `{0, 1}` and every other variable to `{1}`; `ρP` binds variable `0` to `poison` and every other variable to `1`. A third width-2 environment, `uEmptyD`, binds variable `1` to the empty set and every other variable to `{0}`; it is not inhabited and is used only by `Toy.UB.undef_unswitch_empty_input_target_has_no_outcomes`, where its definition is quoted (see **Verbatim statements of counterexamples, witnesses, controls and supporting theorems**).

```lean
-- lean/ToyUB/Syntax.lean:81
theorem freeIn_example_pos : freeIn 0 (add (var 0) (const 1)) = true

-- lean/ToyUB/Syntax.lean:84-85
theorem freeIn_example_neg :
    freeIn 0 (letE 0 (const 1) (var 0)) = false ∧ freeIn 0 (var 1) = false

-- lean/ToyUB/Syntax.lean:88-89
theorem freezeFree_example_pos :
    FreezeFree (ite (var 0) (add (var 0) (var 0)) (const 0)) = true

-- lean/ToyUB/Syntax.lean:92
theorem freezeFree_example_neg : FreezeFree (add (const 1) (freeze (var 0))) = false

-- lean/ToyUB/Syntax.lean:233-234
theorem eqBit_examples :
    eqBit (1#2) (1#2) = 1#2 ∧ eqBit (1#2) (2#2) = 0#2 ∧ eqBit (0#0) (0#0) = 0#0

-- lean/ToyUB/Syntax.lean:169-170
theorem outRef_example_pos :
    OutRef (fun a b : Nat => a = b) [Outcome.ub, Outcome.val 7] [Outcome.ub]

-- lean/ToyUB/Syntax.lean:174-175
theorem outRef_example_pos_defined :
    OutRef (fun a b : Nat => a = b) [Outcome.val 1] [Outcome.val 1, Outcome.val 2]

-- lean/ToyUB/Syntax.lean:180-182
theorem outRef_example_neg :
    ¬ OutRef (fun a b : Nat => a = b) [Outcome.ub] [Outcome.val 1] ∧
    ¬ OutRef (fun a b : Nat => a = b) [Outcome.val 2] [Outcome.val 1]

-- lean/ToyUB/Syntax.lean:186-188
theorem outRef_example_empty_target :
    OutRef (fun a b : Nat => a = b) [] [Outcome.val 1] ∧
    ¬ OutRefNE (fun a b : Nat => a = b) [] [Outcome.val 1]

-- lean/ToyUB/Syntax.lean:191-194
theorem mayUB_examples :
    MayUB [Outcome.val 1, (Outcome.ub : Outcome Nat)] ∧
    ¬ MayUB [Outcome.val 1, (Outcome.val 2 : Outcome Nat)] ∧
    ¬ MayUB ([] : List (Outcome Nat))

-- lean/ToyUB/Syntax.lean:198-202
theorem leVal_examples :
    Outcome.LeVal (fun a b : Nat => a = b) (.val 1) (.val 1) ∧
    ¬ Outcome.LeVal (fun a b : Nat => a = b) (.val 1) (.val 2) ∧
    ¬ Outcome.LeVal (fun a b : Nat => a = b) .ub .ub ∧
    ¬ Outcome.LeVal (fun a b : Nat => a = b) (.val 1) .ub

-- lean/ToyUB/Undef.lean:70-72
theorem map2_example_pos :
    map2 (· + ·) (fun z : BitVec 2 => z == 0#2 || z == 1#2) (fun z => z == 0#2 || z == 1#2)
      1#2 = true

-- lean/ToyUB/Undef.lean:75-76
theorem map2_example_neg :
    map2 (· * ·) (single 2#2) (fun z : BitVec 2 => z == 0#2 || z == 1#2) 1#2 = false

-- lean/ToyUB/Undef.lean:80-82
theorem sub_examples :
    Sub (single 1#2) (fun z : BitVec 2 => z == 0#2 || z == 1#2) ∧
    ¬ Sub (fun z : BitVec 2 => z == 0#2 || z == 1#2) (single 1#2)

-- lean/ToyUB/Undef.lean:85-87
theorem hasNonzero_examples :
    HasNonzero (fun z : BitVec 2 => z == 0#2 || z == 1#2) = true ∧
    HasNonzero (single 0#2) = false

-- lean/ToyUB/Undef.lean:90-91
theorem nonempty_examples :
    Nonempty (single 1#2) ∧ ¬ Nonempty (fun _ : BitVec 2 => false)

-- lean/ToyUB/Undef.lean:118-119
theorem uInhabited_examples :
    UInhabited (fun _ => USet.single 0#2) ∧ ¬ UInhabited (fun _ => fun _ : BitVec 2 => false)

-- lean/ToyUB/Undef.lean:142-145
theorem obsU_examples :
    ObsU [.val (fun z : BitVec 2 => z == 0#2 || z == 1#2)] 1#2 ∧
    ¬ ObsU [.val (fun z : BitVec 2 => z == 0#2 || z == 1#2)] 2#2 ∧
    ¬ ObsU ([.ub] : List (Outcome (USet 2))) 0#2

-- lean/ToyUB/Undef.lean:158-159
theorem obsRefinesU_examples :
    ObsRefinesU 2 (.const 1) (.const 1) ∧ ¬ ObsRefinesU 2 (.const 2) (.const 1)

-- lean/ToyUB/Undef.lean:176-178
theorem semU_example_pos :
    ∃ o ∈ semU 2 ρ01 (.add (.var 0) (.var 0)),
      (match o with | .val A => A 1#2 | .ub => false) = true

-- lean/ToyUB/Undef.lean:182-184
theorem semU_example_neg :
    ∀ o ∈ semU 2 ρ01 (.letE 1 (.freeze (.var 0)) (.add (.var 1) (.var 1))),
      (match o with | .val A => A 1#2 | .ub => true) = false

-- lean/ToyUB/Undef.lean:188-193
theorem semU_example_branch :
    ¬ MayUB (semU 2 ρ01 (.ite (.var 0) (.const 1) (.const 2))) ∧
    (∃ o ∈ semU 2 ρ01 (.ite (.var 0) (.const 1) (.const 2)),
      Outcome.LeVal USet.Sub (.val (USet.single 1#2)) o) ∧
    (∃ o ∈ semU 2 ρ01 (.ite (.var 0) (.const 1) (.const 2)),
      Outcome.LeVal USet.Sub (.val (USet.single 2#2)) o)

-- lean/ToyUB/Undef.lean:207-210
theorem semU_ite_commits_example :
    (∀ o ∈ semU 2 ρ01 (.ite (.var 0) (.const 1) (.const 0)),
      (match o with | .val A => A 0#2 && A 1#2 | .ub => false) = false) ∧
    ¬ RefinesU 2 (.var 0) (.ite (.var 0) (.const 1) (.const 0))

-- lean/ToyUB/Unswitch.lean:66-67
theorem ubFreeU_examples :
    UBFreeU 2 (.var 0) ∧ UBFreeU 2 (.ite (.var 0) (.const 1) (.const 0)) ∧ ¬ UBFreeU 2 .ub

-- lean/ToyUB/Poison.lean:53
theorem refines_example_pos : Refines (int 3#2) poison ∧ Refines (int 3#2) (int 3#2)

-- lean/ToyUB/Poison.lean:58-59
theorem refines_example_neg : ¬ Refines (poison : PVal 2) (int 3#2) ∧
    ¬ Refines (int 1#2) (int 3#2)

-- lean/ToyUB/Poison.lean:94-96
theorem semP_example_pos :
    semP 2 ρP (.add (.var 0) (.const 1)) = [.val .poison] ∧
    semP 2 ρP (.ite (.add (.var 0) (.const 1)) (.const 1) (.const 2)) = [.ub]

-- lean/ToyUB/Poison.lean:100-102
theorem semP_example_neg :
    ¬ MayUB (semP 2 ρP (.ite (.var 1) (.var 0) (.const 2))) ∧
    (.val .poison) ∉ semP 2 ρP (.freeze (.var 0))

-- lean/ToyUB/Poison.lean:105-107
theorem semP_example_freeze :
    semP 2 ρP (.freeze (.var 0)) = [.val (.int 0#2), .val (.int 1#2), .val (.int 2#2),
      .val (.int 3#2)] ∧ semP 2 ρP (.freeze (.var 1)) = [.val (.int 1#2)]

-- lean/ToyUB/Unswitch.lean:58-60
theorem ubFreeP_examples :
    UBFreeP 2 (.var 0) ∧ UBFreeP 2 (.eq (.var 0) (.var 1)) ∧ ¬ UBFreeP 2 .ub ∧
    ¬ UBFreeP 2 (.ite (.var 0) (.const 1) (.const 0))

-- lean/ToyUB/Uninit.lean:62-64
theorem semE_examples :
    semE 2 (fun _ => some 3#2) (.add (.var 0) (.const 1)) = [.val 0#2] ∧
    semE 2 (fun _ => none) (.mul (.var 0) (.const 0)) = [.ub]

-- lean/ToyUB/Uninit.lean:68-72
theorem toPoisonEnv_examples :
    toPoisonEnv (w := 2) (fun _ => none) 0 = .poison ∧
    toPoisonEnv (w := 2) (fun _ => none) 0 ≠ .int 0#2 ∧
    toPoisonEnv (w := 2) (fun _ => some 1#2) 0 = .int 1#2 ∧
    toPoisonEnv (w := 2) (fun _ => some 1#2) 0 ≠ .poison

-- lean/ToyUB/Uninit.lean:76-78
theorem outcome_toP_examples :
    Outcome.toP (w := 2) .ub = .ub ∧ Outcome.toP (w := 2) (.val 3#2) = .val (.int 3#2) ∧
    Outcome.toP (w := 2) (.val 3#2) ≠ .val .poison

-- lean/ToyUB/Uninit.lean:207-208
theorem refinesE_examples (w : Nat) :
    RefinesE w (.var 0) (.var 0) ∧ ¬ RefinesE w (.var 0) (.const 0)

-- lean/ToyUB/Uninit.lean:81-82
theorem semE_freeze_uninit_example (w : Nat) :
    semE w (fun _ => none) (.freeze (.var 0)) = [.ub]
```

### 1. `refinement-preorder`

- **Kind and tier:** theorem; T0. Reflexivity and transitivity of value-level refinement with UB-permissive sources are standard (Lopes et al., PLDI 2021, Sections 5-5.2; mechanized for LLVM IR in Coq by Zakowski et al., ICFP 2021, Section 5); restated for the toy models.
- **Plain claim:** In the undef model (over environments that bind every variable to a nonempty set) and in the poison(+freeze) model (semP on all expressions, including freeze), at every width w, program refinement - in every admissible environment, either the source may reach UB or every target outcome is a value refining some source value - is reflexive and transitive.
- **Lean statement** (verbatim; proofs omitted): `Toy.UB.refinesU_refl`, `Toy.UB.refinesU_trans`, `Toy.UB.refinesP_refl`, `Toy.UB.refinesP_trans`.

```lean
-- lean/ToyUB/Lemmas.lean:135
theorem refinesU_refl (w : Nat) (e : Expr) : RefinesU w e e

-- lean/ToyUB/Lemmas.lean:139-140
theorem refinesU_trans (w : Nat) {a b c : Expr} (hab : RefinesU w a b) (hbc : RefinesU w b c) :
    RefinesU w a c

-- lean/ToyUB/Lemmas.lean:144
theorem refinesP_refl (w : Nat) (e : Expr) : RefinesP w e e

-- lean/ToyUB/Lemmas.lean:148-149
theorem refinesP_trans (w : Nat) {a b c : Expr} (hab : RefinesP w a b) (hbc : RefinesP w b c) :
    RefinesP w a c
```

- **Reading with key definitions unfolded:** refinesU_refl w e : RefinesU w e e;  refinesU_trans w (hab : RefinesU w (tgt := a) (src := b)) (hbc : RefinesU w (tgt := b) (src := c)) : RefinesU w (tgt := a) (src := c);  the same for RefinesP. Unfolded: RefinesU w tgt src := ∀ ρ, UInhabited ρ → OutRef USet.Sub (semU w ρ tgt) (semU w ρ src); RefinesP w tgt src := ∀ ρ, OutRef PVal.Refines (semP w ρ tgt) (semP w ρ src); OutRef R T S := MayUB S ∨ ∀ o ∈ T, ∃ o' ∈ S, LeVal R o o'.
- **Width dependence:** Generic in w.
- **Hypothesis ledger:**
  - hab: first link of the chain (a refines b). Tightness: **tight (counterexample `Toy.UB.refinesU_trans_needs_hab`, `Toy.UB.refinesP_trans_needs_hab`)**.
  - hbc: second link of the chain (b refines c). Tightness: **tight (counterexample `Toy.UB.refinesU_trans_needs_hbc`, `Toy.UB.refinesP_trans_needs_hbc`)**.
- **Depth:** shallow
- **Non-vacuity witness:** freeze (2*x) refines 2*x, which refines x+x (width 2), in both models. (`Toy.UB.nonvacuity_refinesU_trans`, `Toy.UB.nonvacuity_refinesP_trans`)
- **Supporting theorems** (proved): `Toy.UB.semP_ne_nil`, `Toy.UB.semU_ne_nil`, `Toy.UB.refinesP_iff_outRefNE`, `Toy.UB.refinesU_iff_outRefNE`.
- **Prior art:**
  - Lopes, Lee, Hur, Liu, Regehr. "Alive2: Bounded Translation Validation for LLVM." PLDI 2021, pp. 65-79. DOI 10.1145/3453483.3454030. Section 5 (p. 71) states refinement of functions and notes that it ensures compositionality; Section 5.1 (Figure 4, p. 71) gives value refinement (value-poison: poison is refined by any value; value-undef: an undef value is refined by an equally or more defined one) and final-state refinement (final-state-ub); Section 5.2 (pp. 71-72) extends it to nondeterminism (undef, freeze): every target behaviour must be matched by some source behaviour.
  - Zakowski, Beck, Yoon, Zaichuk, Zaliva, Zdancewic. "Modular, Compositional, and Executable Formal Semantics for LLVM IR." Proc. ACM Program. Lang. 5 (ICFP), Article 67, 2021. DOI 10.1145/3473572. Section 5 (pp. 67:18-67:20) defines and mechanizes in Coq refinement relations for LLVM IR with undef and poison (anything refines poison; under-defined values are refined by inclusion of their concrete-value sets).
- **Design question:** How must refinement between programs with undefined values be defined (value-level, permissive after source UB, aware of nondeterminism) so that it is a preorder and composes through every language construct, and which candidate definitions fail?
- **Non-claims:** listed under **Boundaries** (shared S1, S2, S3, S4, S5, S6, and the non-claims of result 1).

Basis: execution (Lean kernel check) — the theorems above, with every name in the ledger and witness lines, are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — `RefinesU` and `RefinesP` have the shape of Alive2's per-input refinement (Lopes et al., PLDI 2021, Section 5.2: every target behaviour must be matched by a source behaviour, and source UB permits anything) with the value refinements of its Figure 4 (poison is refined by any value; an undef value by a more defined one, here a subset). Reflexivity and transitivity are what let a chain of individually verified rewrites be composed. The correspondence is structural; nothing is derived about the relation implemented by Alive2 or mechanized in Vellvm (Zakowski et al., ICFP 2021).

### 2. `source-ub-refined-by-anything`

- **Kind and tier:** theorem; T0. A definitional reference point: it restates the UB clause of refinement (Lopes et al., PLDI 2021, Section 5.1, final-state-ub, extended to nondeterministic sources in Section 5.2) for the toy.
- **Plain claim:** Reference point (definitional): in both models, at every width, a source program that may reach UB in every admissible environment (in particular the program ub) is refined by every target program; 'may reach UB' means that at least one of the source's nondeterministic outcomes is UB.
- **Lean statement** (verbatim; proofs omitted): `Toy.UB.refinesU_of_src_mayUB`, `Toy.UB.refinesP_of_src_mayUB`, `Toy.UB.refinesU_ub`, `Toy.UB.refinesP_ub`.

```lean
-- lean/ToyUB/Refinement.lean:25-27
theorem refinesU_of_src_mayUB (w : Nat) {src : Expr}
    (h : ∀ ρ : Var → USet w, UInhabited ρ → MayUB (semU w ρ src)) (tgt : Expr) :
    RefinesU w tgt src

-- lean/ToyUB/Refinement.lean:32-33
theorem refinesP_of_src_mayUB (w : Nat) {src : Expr}
    (h : ∀ ρ : Var → PVal w, MayUB (semP w ρ src)) (tgt : Expr) : RefinesP w tgt src

-- lean/ToyUB/Refinement.lean:37
theorem refinesU_ub (w : Nat) (tgt : Expr) : RefinesU w tgt .ub

-- lean/ToyUB/Refinement.lean:41
theorem refinesP_ub (w : Nat) (tgt : Expr) : RefinesP w tgt .ub
```

- **Reading with key definitions unfolded:** refinesU_of_src_mayUB w (h : ∀ ρ, UInhabited ρ → MayUB (semU w ρ src)) tgt : RefinesU w (tgt := tgt) (src := src);  refinesP_of_src_mayUB w (h : ∀ ρ, MayUB (semP w ρ src)) tgt : RefinesP w (tgt := tgt) (src := src);  refinesU_ub w tgt : RefinesU w tgt ub;  refinesP_ub w tgt : RefinesP w tgt ub. MayUB S := ∃ o ∈ S, o.isUB.
- **Width dependence:** Generic in w.
- **Hypothesis ledger:**
  - h (the source may reach UB in every admissible environment): the UB disjunct of OutRef must be available in every environment. Tightness: **tight (counterexample `Toy.UB.refinesU_of_src_mayUB_needs_mayUB`, `Toy.UB.refinesP_of_src_mayUB_needs_mayUB`)**.
- **Depth:** definitional
- **Non-vacuity witness:** x + ub (undef model) and if x then ub else ub (poison(+freeze) model) reach UB in every environment (width 2). (`Toy.UB.nonvacuity_refinesU_of_src_mayUB`, `Toy.UB.nonvacuity_refinesP_of_src_mayUB`)
- **Prior art:**
  - Lopes, Lee, Hur, Liu, Regehr. "Alive2: Bounded Translation Validation for LLVM." PLDI 2021, pp. 65-79. DOI 10.1145/3453483.3454030. Section 5.1 (Figure 4, rule final-state-ub, p. 71): a final state that is undefined is refined by any state; Section 5.2 (pp. 71-72): with nondeterminism, each target behaviour must be refined by some source behaviour.
- **Design question:** How must refinement between programs with undefined values be defined (value-level, permissive after source UB, aware of nondeterminism) so that it is a preorder and composes through every language construct, and which candidate definitions fail?
- **Non-claims:** listed under **Boundaries** (shared S1, S2, S3, S4, S5, S6, and the non-claims of result 2).

Basis: execution (Lean kernel check) — the theorems above, with every name in the ledger and witness lines, are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — This is the toy counterpart of Alive2's rule final-state-ub (Lopes et al., PLDI 2021, Section 5.1, Figure 4) in its per-behaviour form for nondeterministic sources (Section 5.2): a source behaviour that is UB permits any target behaviour. The correspondence holds by comparing definitions; it is not a statement about any tool.

### 3. `refinement-congruence`

- **Kind and tier:** theorem; T0. Compositionality of refinement is known and mechanized for LLVM IR with undef and poison (Zakowski et al., ICFP 2021, Section 5, in Coq); Lopes et al. (PLDI 2021, Section 5) state it for function-level refinement. Here it is restated construct by construct for the toy language.
- **Plain claim:** In the undef model (over environments of nonempty sets) and in the poison(+freeze) model, at every width, refinement is a congruence for every construct: if each argument of +, *, the equality test, if, let (bound expression and body) or freeze in the target refines the corresponding argument in the source, the whole target expression refines the whole source expression.
- **Lean statement** (verbatim; proofs omitted): `Toy.UB.refinesU_congr_add`, `Toy.UB.refinesU_congr_mul`, `Toy.UB.refinesU_congr_eq`, `Toy.UB.refinesU_congr_ite`, `Toy.UB.refinesU_congr_letE`, `Toy.UB.refinesU_congr_freeze`, `Toy.UB.refinesP_congr_add`, `Toy.UB.refinesP_congr_mul`, `Toy.UB.refinesP_congr_eq`, `Toy.UB.refinesP_congr_ite`, `Toy.UB.refinesP_congr_letE`, `Toy.UB.refinesP_congr_freeze`.

```lean
-- lean/ToyUB/Refinement.lean:47-48
theorem refinesU_congr_add (w : Nat) {a a' b b' : Expr} (ha : RefinesU w a' a)
    (hb : RefinesU w b' b) : RefinesU w (.add a' b') (.add a b)

-- lean/ToyUB/Refinement.lean:54-55
theorem refinesU_congr_mul (w : Nat) {a a' b b' : Expr} (ha : RefinesU w a' a)
    (hb : RefinesU w b' b) : RefinesU w (.mul a' b') (.mul a b)

-- lean/ToyUB/Refinement.lean:61-62
theorem refinesU_congr_eq (w : Nat) {a a' b b' : Expr} (ha : RefinesU w a' a)
    (hb : RefinesU w b' b) : RefinesU w (.eq a' b') (.eq a b)

-- lean/ToyUB/Refinement.lean:68-69
theorem refinesU_congr_ite (w : Nat) {c c' t t' e e' : Expr} (hc : RefinesU w c' c)
    (ht : RefinesU w t' t) (he : RefinesU w e' e) : RefinesU w (.ite c' t' e') (.ite c t e)

-- lean/ToyUB/Refinement.lean:76-77
theorem refinesU_congr_letE (w : Nat) (x : Var) {a a' b b' : Expr} (ha : RefinesU w a' a)
    (hb : RefinesU w b' b) : RefinesU w (.letE x a' b') (.letE x a b)

-- lean/ToyUB/Refinement.lean:91-92
theorem refinesU_congr_freeze (w : Nat) {a a' : Expr} (ha : RefinesU w a' a) :
    RefinesU w (.freeze a') (.freeze a)

-- lean/ToyUB/Refinement.lean:99-100
theorem refinesP_congr_add (w : Nat) {a a' b b' : Expr} (ha : RefinesP w a' a)
    (hb : RefinesP w b' b) : RefinesP w (.add a' b') (.add a b)

-- lean/ToyUB/Refinement.lean:106-107
theorem refinesP_congr_mul (w : Nat) {a a' b b' : Expr} (ha : RefinesP w a' a)
    (hb : RefinesP w b' b) : RefinesP w (.mul a' b') (.mul a b)

-- lean/ToyUB/Refinement.lean:113-114
theorem refinesP_congr_eq (w : Nat) {a a' b b' : Expr} (ha : RefinesP w a' a)
    (hb : RefinesP w b' b) : RefinesP w (.eq a' b') (.eq a b)

-- lean/ToyUB/Refinement.lean:120-121
theorem refinesP_congr_ite (w : Nat) {c c' t t' e e' : Expr} (hc : RefinesP w c' c)
    (ht : RefinesP w t' t) (he : RefinesP w e' e) : RefinesP w (.ite c' t' e') (.ite c t e)

-- lean/ToyUB/Refinement.lean:135-136
theorem refinesP_congr_letE (w : Nat) (x : Var) {a a' b b' : Expr} (ha : RefinesP w a' a)
    (hb : RefinesP w b' b) : RefinesP w (.letE x a' b') (.letE x a b)

-- lean/ToyUB/Refinement.lean:144-145
theorem refinesP_congr_freeze (w : Nat) {a a' : Expr} (ha : RefinesP w a' a) :
    RefinesP w (.freeze a') (.freeze a)
```

- **Reading with key definitions unfolded:** e.g. refinesU_congr_letE w x (ha : RefinesU w (tgt := a') (src := a)) (hb : RefinesU w (tgt := b') (src := b)) : RefinesU w (tgt := letE x a' b') (src := letE x a b); analogous for add, mul, eq, ite (three premises), freeze (one premise), and for RefinesP.
- **Width dependence:** Generic in w.
- **Hypothesis ledger:**
  - U: premise ha of refinesU_congr_add: the corresponding argument (target first, source second) is refined. Tightness: **tight (counterexample `Toy.UB.refinesU_congr_add_premises_tight`)**.
  - U: premise hb of refinesU_congr_add: the corresponding argument (target first, source second) is refined. Tightness: **tight (counterexample `Toy.UB.refinesU_congr_add_premises_tight`)**.
  - U: premise ha of refinesU_congr_mul: the corresponding argument (target first, source second) is refined. Tightness: **tight (counterexample `Toy.UB.refinesU_congr_mul_premises_tight`)**.
  - U: premise hb of refinesU_congr_mul: the corresponding argument (target first, source second) is refined. Tightness: **tight (counterexample `Toy.UB.refinesU_congr_mul_premises_tight`)**.
  - U: premise ha of refinesU_congr_eq: the corresponding argument (target first, source second) is refined. Tightness: **tight (counterexample `Toy.UB.refinesU_congr_eq_premises_tight`)**.
  - U: premise hb of refinesU_congr_eq: the corresponding argument (target first, source second) is refined. Tightness: **tight (counterexample `Toy.UB.refinesU_congr_eq_premises_tight`)**.
  - U: premise hc of refinesU_congr_ite: the corresponding argument (target first, source second) is refined. Tightness: **tight (counterexample `Toy.UB.refinesU_congr_ite_premises_tight`)**.
  - U: premise ht of refinesU_congr_ite: the corresponding argument (target first, source second) is refined. Tightness: **tight (counterexample `Toy.UB.refinesU_congr_ite_premises_tight`)**.
  - U: premise he of refinesU_congr_ite: the corresponding argument (target first, source second) is refined. Tightness: **tight (counterexample `Toy.UB.refinesU_congr_ite_premises_tight`)**.
  - U: premise ha of refinesU_congr_letE: the corresponding argument (target first, source second) is refined. Tightness: **tight (counterexample `Toy.UB.refinesU_congr_letE_premises_tight`)**.
  - U: premise hb of refinesU_congr_letE: the corresponding argument (target first, source second) is refined. Tightness: **tight (counterexample `Toy.UB.refinesU_congr_letE_premises_tight`)**.
  - U: premise ha of refinesU_congr_freeze: the corresponding argument (target first, source second) is refined. Tightness: **tight (counterexample `Toy.UB.refinesU_congr_freeze_premises_tight`)**.
  - P: premise ha of refinesP_congr_add: the corresponding argument (target first, source second) is refined. Tightness: **tight (counterexample `Toy.UB.refinesP_congr_add_premises_tight`)**.
  - P: premise hb of refinesP_congr_add: the corresponding argument (target first, source second) is refined. Tightness: **tight (counterexample `Toy.UB.refinesP_congr_add_premises_tight`)**.
  - P: premise ha of refinesP_congr_mul: the corresponding argument (target first, source second) is refined. Tightness: **tight (counterexample `Toy.UB.refinesP_congr_mul_premises_tight`)**.
  - P: premise hb of refinesP_congr_mul: the corresponding argument (target first, source second) is refined. Tightness: **tight (counterexample `Toy.UB.refinesP_congr_mul_premises_tight`)**.
  - P: premise ha of refinesP_congr_eq: the corresponding argument (target first, source second) is refined. Tightness: **tight (counterexample `Toy.UB.refinesP_congr_eq_premises_tight`)**.
  - P: premise hb of refinesP_congr_eq: the corresponding argument (target first, source second) is refined. Tightness: **tight (counterexample `Toy.UB.refinesP_congr_eq_premises_tight`)**.
  - P: premise hc of refinesP_congr_ite: the corresponding argument (target first, source second) is refined. Tightness: **tight (counterexample `Toy.UB.refinesP_congr_ite_premises_tight`)**.
  - P: premise ht of refinesP_congr_ite: the corresponding argument (target first, source second) is refined. Tightness: **tight (counterexample `Toy.UB.refinesP_congr_ite_premises_tight`)**.
  - P: premise he of refinesP_congr_ite: the corresponding argument (target first, source second) is refined. Tightness: **tight (counterexample `Toy.UB.refinesP_congr_ite_premises_tight`)**.
  - P: premise ha of refinesP_congr_letE: the corresponding argument (target first, source second) is refined. Tightness: **tight (counterexample `Toy.UB.refinesP_congr_letE_premises_tight`)**.
  - P: premise hb of refinesP_congr_letE: the corresponding argument (target first, source second) is refined. Tightness: **tight (counterexample `Toy.UB.refinesP_congr_letE_premises_tight`)**.
  - P: premise ha of refinesP_congr_freeze: the corresponding argument (target first, source second) is refined. Tightness: **tight (counterexample `Toy.UB.refinesP_congr_freeze_premises_tight`)**.
- **Depth:** shallow
- **Non-vacuity witness:** 2*x refines x+x, freeze y refines y, and 7 refines ub (width 2, both models): all premises of every congruence theorem can be instantiated by non-trivial refining pairs. (`Toy.UB.nonvacuity_refinesU_congr`, `Toy.UB.nonvacuity_refinesP_congr`)
- **Prior art:**
  - Zakowski, Beck, Yoon, Zaichuk, Zaliva, Zdancewic. "Modular, Compositional, and Executable Formal Semantics for LLVM IR." Proc. ACM Program. Lang. 5 (ICFP), Article 67, 2021. DOI 10.1145/3473572. Section 5 (pp. 67:18-67:20): refinement relations for LLVM IR with undef/poison, mechanized in Coq and lifted compositionally through the semantics, so that program transformations can be proved correct compositionally.
  - Lopes, Lee, Hur, Liu, Regehr. "Alive2: Bounded Translation Validation for LLVM." PLDI 2021, pp. 65-79. DOI 10.1145/3453483.3454030. Section 5 (p. 71): 'The definition above ensures compositionality: if a function's inputs are refined, so are the outputs.'
  - Bhat, Keizer, Hughes, Goens, Grosser. "Verifying Peephole Rewriting in SSA Compiler IRs." ITP 2024, LIPIcs vol. 309, Article 9. DOI 10.4230/LIPIcs.ITP.2024.9 (preprint arXiv:2407.03685). Section 4.1: Lean 4 mechanization that applying a verified peephole rewrite inside an SSA program preserves its denotation (stated for semantic equality); Section 6.1 treats LLVM bitvector rewrites at arbitrary width with poison and UB collapsed into Option.
- **Design question:** How must refinement between programs with undefined values be defined (value-level, permissive after source UB, aware of nondeterminism) so that it is a preorder and composes through every language construct, and which candidate definitions fail?
- **Non-claims:** listed under **Boundaries** (shared S1, S2, S3, S4, S5, S6, and the non-claims of result 3).

Basis: execution (Lean kernel check) — the theorems above, with every name in the ledger and witness lines, are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — Alive2 (Lopes et al., PLDI 2021, Section 5) notes that its refinement ensures compositionality, and Vellvm (Zakowski et al., ICFP 2021, Section 5) mechanizes compositional refinement for LLVM IR with undef and poison. The toy theorems show the same property construct by construct for the toy language only; for LLVM IR the property rests on those sources, not on this package.

### 4. `undef-observational-refinement-not-congruence`

- **Kind and tier:** counterexample; T1. That undef refinement must be judged per value (Lopes et al., PLDI 2021, Section 5.1, value-undef) rather than by comparing produced integers is implicit in the literature; the precise failure of congruence at let is made explicit here.
- **Plain claim:** In the undef model (environments of nonempty sets), for every width w ≥ 1 and variables x, y: x observationally refines freeze x (comparing only the integers a program may produce, and UB), but let y := x; y + y does not observationally refine let y := freeze x; y + y; so observational refinement is not a congruence for let.
- **Lean statement** (verbatim; proofs omitted): `Toy.UB.undef_obsRefines_not_congruence_letE`.

```lean
-- lean/ToyUB/Refinement.lean:171-174
theorem undef_obsRefines_not_congruence_letE (w : Nat) (hw : 1 ≤ w) (x y : Var) :
    ObsRefinesU w (.var x) (.freeze (.var x)) ∧
    ¬ ObsRefinesU w (.letE y (.var x) (.add (.var y) (.var y)))
        (.letE y (.freeze (.var x)) (.add (.var y) (.var y)))
```

- **Reading with key definitions unfolded:** 1 ≤ w → ObsRefinesU w (var x) (freeze (var x)) ∧ ¬ ObsRefinesU w (letE y (var x) (add (var y) (var y))) (letE y (freeze (var x)) (add (var y) (var y)));  ObsRefinesU w tgt src := ∀ ρ, UInhabited ρ → MayUB (semU w ρ src) ∨ (¬ MayUB (semU w ρ tgt) ∧ ∀ z, ObsU (semU w ρ tgt) z → ObsU (semU w ρ src) z).
- **Width dependence:** Generic for all w ≥ 1; at w = 0 the second conjunct fails (Toy.UB.undef_obsRefines_letE_width_zero).
- **Hypothesis ledger:**
  - hw : 1 ≤ w: at width 0 there is only one integer and both let programs produce exactly {0}. Tightness: **tight (counterexample `Toy.UB.undef_obsRefines_not_congruence_letE_needs_width`)**.
- **Depth:** shallow
- **Non-vacuity witness:** w = 2, x = 0, y = 1: the full statement instantiated. (`Toy.UB.nonvacuity_undef_obsRefines_not_congruence_letE`, `Toy.UB.nonvacuity_width_two`)
- **Contrasting controls** (each proved): `Toy.UB.refinesU_congr_letE`, `Toy.UB.undef_obsRefines_letE_width_zero`.
- **Prior art:**
  - Lopes, Lee, Hur, Liu, Regehr. "Alive2: Bounded Translation Validation for LLVM." PLDI 2021, pp. 65-79. DOI 10.1145/3453483.3454030. Section 5.1 (Figure 4, rule value-undef, p. 71) judges undef refinement per value, not by the integers a whole program produces.
- **Design question:** How must refinement between programs with undefined values be defined (value-level, permissive after source UB, aware of nondeterminism) so that it is a preorder and composes through every language construct, and which candidate definitions fail?
- **Non-claims:** listed under **Boundaries** (shared S1, S2, S3, S4, S5, and the non-claims of result 4).

Basis: execution (Lean kernel check) — the theorems above, with every name in the ledger and witness lines, are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — The counterexample suggests that a checker for undef semantics that compares only the integers whole programs can return, forgetting how they are grouped into per-value undef sets, would not be compositional; Alive2 judges undef refinement per value (Lopes et al., PLDI 2021, Section 5.1, rule value-undef). This is an argument by analogy from the toy; nothing is claimed about any tool's implementation.

### 5. `merge-uses-sound`

- **Kind and tier:** theorem; T0. Lee et al. (PLDI 2017, Section 3.1) show that 2*x -> x+x is wrong under undef because it enlarges the outcome set; the reverse direction, which shrinks it, is the implied sound one. Restated for the toy.
- **Plain claim:** At every width, for every expression e (including expressions containing freeze or ub), rewriting e + e to 2 * e is a refinement in the undef model (over environments of nonempty sets) and in the poison(+freeze) model.
- **Lean statement** (verbatim; proofs omitted): `Toy.UB.undef_rewrite_add_self_to_two_mul_sound`, `Toy.UB.poison_rewrite_add_self_to_two_mul_sound`.

```lean
-- lean/ToyUB/Duplication.lean:31-32
theorem undef_rewrite_add_self_to_two_mul_sound (w : Nat) (e : Expr) :
    RefinesU w (.mul (.const 2) e) (.add e e)

-- lean/ToyUB/Duplication.lean:101-102
theorem poison_rewrite_add_self_to_two_mul_sound (w : Nat) (e : Expr) :
    RefinesP w (.mul (.const 2) e) (.add e e)
```

- **Reading with key definitions unfolded:** ∀ w e, RefinesU w (tgt := mul (const 2) e) (src := add e e);  ∀ w e, RefinesP w (tgt := mul (const 2) e) (src := add e e)  (two theorems).
- **Width dependence:** Generic in w.
- **Hypothesis ledger:** the stated theorems have no hypotheses beyond the universally quantified width, variables and expressions.
- **Depth:** shallow
- **Non-vacuity witness:** w = 3 with e = if x then y else freeze y (undef model) and e = freeze x (poison(+freeze) model). (`Toy.UB.nonvacuity_undef_rewrite_add_self_to_two_mul_sound`, `Toy.UB.nonvacuity_poison_rewrite_add_self_to_two_mul_sound`)
- **Prior art:**
  - Lee, Kim, Song, Hur, Das, Majnemer, Regehr, Lopes. "Taming Undefined Behavior in LLVM." PLDI 2017, pp. 633-647. DOI 10.1145/3062341.3062343. Section 3.1 ('Duplicate SSA uses', p. 637): rewriting %y = mul %x, 2 to %y = add %x, %x is wrong when %x is undef because 'we have increased the set of possible outcomes'.
  - Lopes, Menendez, Nagarakatte, Regehr. "Provably Correct Peephole Optimizations with Alive." PLDI 2015. DOI 10.1145/2737924.2737965. Introduces SMT-based verification of LLVM peephole rewrites with the semantics of undef, poison and UB.
  - Bhat, Keizer, Hughes, Goens, Grosser. "Verifying Peephole Rewriting in SSA Compiler IRs." ITP 2024, LIPIcs vol. 309, Article 9. DOI 10.4230/LIPIcs.ITP.2024.9 (preprint arXiv:2407.03685). Section 6.1: Lean 4 proofs of LLVM bitvector peephole rewrites at arbitrary width, with poison and UB collapsed into Option (no undef sets).
- **Design question:** Under which value model is it sound for an optimizer to change the number of uses of a value (2 * e versus e + e), and what is the repair when it is not?
- **Non-claims:** listed under **Boundaries** (shared S1, S2, S3, S4, S5, S6, and the non-claims of result 5).

Basis: execution (Lean kernel check) — the theorems above, with every name in the ledger and witness lines, are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — In LLVM, each use of an `undef` value may observe a different value (LLVM 19.1.0 Language Reference, Undefined Values; Lee et al., PLDI 2017, Section 3.1), as in the toy undef model, and most LLVM instructions return poison when one of their arguments is poison (same document, Poison Values), as in the toy poison model. Merging two uses into one removes choices, which is why the toy rewrite `e + e -> 2 * e` is sound. The bridge covers only wrapping `add`/`mul` without `nsw`/`nuw` flags; it does not establish the soundness of any particular LLVM transformation.

### 6. `undef-duplicate-use-unsound`

- **Kind and tier:** impossibility; T0. Direct restatement of Lee et al. (PLDI 2017, Section 3.1) in the toy undef model.
- **Plain claim:** In the undef model (environments of nonempty sets), at every width w ≥ 1 and for every variable x, rewriting 2 * x to x + x is not a refinement: with x bound to {0, 1} the target can produce the odd integer 1, which 2 * x cannot.
- **Lean statement** (verbatim; proofs omitted): `Toy.UB.undef_rewrite_two_mul_to_add_self_unsound`.

```lean
-- lean/ToyUB/Duplication.lean:64-65
theorem undef_rewrite_two_mul_to_add_self_unsound (w : Nat) (hw : 1 ≤ w) (x : Var) :
    ¬ RefinesU w (.add (.var x) (.var x)) (.mul (.const 2) (.var x))
```

- **Reading with key definitions unfolded:** 1 ≤ w → ¬ RefinesU w (tgt := add (var x) (var x)) (src := mul (const 2) (var x)).
- **Width dependence:** Generic for all w ≥ 1; the rewrite is sound at w = 0 (Toy.UB.undef_rewrite_two_mul_to_add_self_sound_width_zero).
- **Hypothesis ledger:**
  - hw : 1 ≤ w: at width 0 there is only one integer, so every value set is {0}. Tightness: **tight (counterexample `Toy.UB.undef_rewrite_two_mul_to_add_self_unsound_needs_width`)**.
- **Depth:** shallow
- **Non-vacuity witness:** w = 2, x = 0: the statement instantiated. (`Toy.UB.nonvacuity_undef_rewrite_two_mul_to_add_self_unsound`, `Toy.UB.nonvacuity_width_two`)
- **Positive controls** (nearby settings where the conclusion fails, each proved): `Toy.UB.undef_rewrite_two_mul_to_add_self_sound_width_zero`, `Toy.UB.undef_rewrite_two_mul_to_let_freeze_add_self_sound`, `Toy.UB.undef_rewrite_two_mul_to_add_self_sound_at_singleton`, `Toy.UB.poison_rewrite_two_mul_to_add_self_sound_of_freezeFree`. See also the escape hatches under **Boundaries**.
- **Prior art:**
  - Lee, Kim, Song, Hur, Das, Majnemer, Regehr, Lopes. "Taming Undefined Behavior in LLVM." PLDI 2017, pp. 633-647. DOI 10.1145/3062341.3062343. Section 3.1 (p. 637): 'In the original code, the result can be any even number, while in the transformed code the result can be any number.'
  - Lopes, Lee, Hur, Liu, Regehr. "Alive2: Bounded Translation Validation for LLVM." PLDI 2021, pp. 65-79. DOI 10.1145/3453483.3454030. Section 2 repeats the add-versus-multiply-by-two example under undef.
  - Lobo, McIver, Mitenkov, Lee, Sundararajah, Lopes. "Towards Removing Undef Values from LLVM IR." Proc. ACM Program. Lang. 10 (PLDI), Article 172, 2026. DOI 10.1145/3808250. Abstract: the per-use behaviour of undef 'makes even simple algebraic rewrites, such as replacing 2 × y with y + y, unsound in LLVM'.
- **Design question:** Under which value model is it sound for an optimizer to change the number of uses of a value (2 * e versus e + e), and what is the repair when it is not?
- **Non-claims:** listed under **Boundaries** (shared S1, S2, S3, S4, S5, and the non-claims of result 6).

Basis: execution (Lean kernel check) — the theorems above, with every name in the ledger and witness lines, are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — The toy counterexample is the instance, in the undef model, of the example of Lee et al. (PLDI 2017, Section 3.1: rewriting `%y = mul %x, 2` to `%y = add %x, %x` is wrong when `%x` is undef because it increases the set of possible outcomes), repeated by Alive2 (Lopes et al., PLDI 2021, Section 2) and by Lobo et al. (PLDI 2026, abstract). It supports by analogy, but does not prove, that the LLVM rewrite is unsound under `undef`; the LLVM-level claim rests on those sources.

### 7. `poison-duplicate-freeze-free-use-sound`

- **Kind and tier:** theorem; T0. Lee et al. (PLDI 2017, Section 4) replace undef by poison so that all uses of a value agree; that duplicating uses is then sound for deterministic operands is the implied consequence. Restated for the toy.
- **Plain claim:** In the poison(+freeze) model, at every width, for every freeze-free expression e (in particular every variable), rewriting 2 * e to e + e is a refinement; together with merge-uses-sound, both directions are sound for freeze-free e.
- **Lean statement** (verbatim; proofs omitted): `Toy.UB.poison_rewrite_two_mul_to_add_self_sound_of_freezeFree`.

```lean
-- lean/ToyUB/Duplication.lean:181-182
theorem poison_rewrite_two_mul_to_add_self_sound_of_freezeFree (w : Nat) (e : Expr)
    (he : e.FreezeFree = true) : RefinesP w (.add e e) (.mul (.const 2) e)
```

- **Reading with key definitions unfolded:** e.FreezeFree = true → RefinesP w (tgt := add e e) (src := mul (const 2) e).
- **Width dependence:** Generic in w.
- **Hypothesis ledger:**
  - he : e.FreezeFree = true: freeze-free programs are deterministic in the poison model (Toy.UB.semP_freezeFree_singleton), so both evaluations of e agree. Tightness: **tight (counterexample `Toy.UB.poison_rewrite_two_mul_to_add_self_needs_freezeFree`, `Toy.UB.poisonFreeze_rewrite_two_mul_to_add_self_unsound`)**.
- **Depth:** shallow
- **Non-vacuity witness:** e = if x then x + y else ub is freeze-free (and may reach UB). (`Toy.UB.nonvacuity_freezeFree`)
- **Prior art:**
  - Lee, Kim, Song, Hur, Das, Majnemer, Regehr, Lopes. "Taming Undefined Behavior in LLVM." PLDI 2017, pp. 633-647. DOI 10.1145/3062341.3062343. Section 4 (p. 639): the proposed semantics replaces undef by poison and introduces freeze; 'All uses of a given freeze return the same value, but different freezes of a value may return different constants.'
  - Bhat, Keizer, Hughes, Goens, Grosser. "Verifying Peephole Rewriting in SSA Compiler IRs." ITP 2024, LIPIcs vol. 309, Article 9. DOI 10.4230/LIPIcs.ITP.2024.9 (preprint arXiv:2407.03685). Section 6.1: Lean 4 proofs of LLVM bitvector rewrites with poison collapsed into Option.
- **Design question:** Under which value model is it sound for an optimizer to change the number of uses of a value (2 * e versus e + e), and what is the repair when it is not?
- **Non-claims:** listed under **Boundaries** (shared S1, S2, S3, S4, and the non-claims of result 7).

Basis: execution (Lean kernel check) — the theorems above, with every name in the ledger and witness lines, are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — The toy poison model gives each variable one value (an integer or `poison`), so duplicating a use of a freeze-free operand adds no behaviour. Lee et al. (PLDI 2017, Section 3.1) show that the same rewrite, `%y = mul %x, 2` to `%y = add %x, %x`, is wrong when `%x` is undef, and the semantics they propose (Section 4) replaces undef by poison plus freeze. The toy result suggests by analogy, but does not prove, that the rewrite is sound for LLVM values that may be poison but not undef; the toy has no poison-creating operations (no `nsw`/`nuw`), so nothing is said about LLVM's flags.

### 8. `poisonFreeze-duplicate-frozen-operand-unsound`

- **Kind and tier:** impossibility; T0. Restates Lee et al. (PLDI 2017, Section 5.5, 'Pitfall 1: Freeze duplication') in the toy: duplicating a freeze may observe two different values.
- **Plain claim:** In the poison + freeze model, at every width w ≥ 1 and for every variable x, rewriting 2 * freeze x to freeze x + freeze x is not a refinement: with x ↦ poison the two freezes may pick 0 and 1, giving the odd integer 1, while every outcome of 2 * freeze x is even.
- **Lean statement** (verbatim; proofs omitted): `Toy.UB.poisonFreeze_rewrite_two_mul_to_add_self_unsound`.

```lean
-- lean/ToyUB/Duplication.lean:202-204
theorem poisonFreeze_rewrite_two_mul_to_add_self_unsound (w : Nat) (hw : 1 ≤ w) (x : Var) :
    ¬ RefinesP w (.add (.freeze (.var x)) (.freeze (.var x)))
        (.mul (.const 2) (.freeze (.var x)))
```

- **Reading with key definitions unfolded:** 1 ≤ w → ¬ RefinesP w (tgt := add (freeze (var x)) (freeze (var x))) (src := mul (const 2) (freeze (var x))).
- **Width dependence:** Generic for all w ≥ 1; sound at w = 0 (Toy.UB.poisonFreeze_rewrite_two_mul_to_add_self_sound_width_zero).
- **Hypothesis ledger:**
  - hw : 1 ≤ w: at width 0 every integer is 0. Tightness: **tight (counterexample `Toy.UB.poisonFreeze_rewrite_two_mul_to_add_self_unsound_needs_width`)**.
- **Depth:** shallow
- **Non-vacuity witness:** w = 2, x = 0: the statement instantiated. (`Toy.UB.nonvacuity_poisonFreeze_rewrite_two_mul_to_add_self_unsound`, `Toy.UB.nonvacuity_width_two`)
- **Positive controls** (nearby settings where the conclusion fails, each proved): `Toy.UB.poisonFreeze_rewrite_two_mul_to_add_self_sound_width_zero`, `Toy.UB.poison_rewrite_two_mul_to_add_self_sound_of_freezeFree`, `Toy.UB.poisonFreeze_rewrite_two_mul_to_let_freeze_add_self_sound`, `Toy.UB.poisonFreeze_rewrite_two_mul_freeze_sound_at_int`. See also the escape hatches under **Boundaries**.
- **Prior art:**
  - Lee, Kim, Song, Hur, Das, Majnemer, Regehr, Lopes. "Taming Undefined Behavior in LLVM." PLDI 2017, pp. 633-647. DOI 10.1145/3062341.3062343. Section 5.5 ('Pitfall 1: Freeze duplication', p. 641): 'Duplicating freeze instructions is not allowed, since each freeze instruction may return a different value if the input is poison.'
  - LLVM Language Reference Manual, LLVM 19.1.0 release documentation, https://releases.llvm.org/19.1.0/docs/LangRef.html. 'freeze' Instruction: 'All uses of a value returned by the same freeze instruction are guaranteed to always observe the same value, while different freeze instructions may yield different values.'
- **Design question:** Under which value model is it sound for an optimizer to change the number of uses of a value (2 * e versus e + e), and what is the repair when it is not?
- **Non-claims:** listed under **Boundaries** (shared S1, S2, S3, S4, and the non-claims of result 8).

Basis: execution (Lean kernel check) — the theorems above, with every name in the ledger and witness lines, are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — The LLVM 19.1.0 Language Reference states that "different 'freeze' instructions may yield different values", and Lee et al. (PLDI 2017, Section 5.5) state that duplicating freeze instructions is not allowed. The toy rewrite `2 * freeze x -> freeze x + freeze x` creates a second `freeze` of the same operand; the toy shows that this, and not adding a second use of one frozen value (the escape hatch `let a := freeze x; a + a`), breaks soundness. This is an analogy, not a proof about LLVM.

### 9. `poison-gvn-sound`

- **Kind and tier:** theorem; T0. Lee et al. (PLDI 2017, Section 3.3 and Section 5.1) explain that GVN is sound once branching on poison is UB; restated for the toy.
- **Plain claim:** In the poison(+freeze) model (branching on poison is UB), at every width, for all variables x, y and expressions t, e, rewriting if x = y then t else e to if x = y then (let y := x; t) else e is a refinement.
- **Lean statement** (verbatim; proofs omitted): `Toy.UB.poison_gvn_sound`.

```lean
-- lean/ToyUB/GVN.lean:50-52
theorem poison_gvn_sound (w : Nat) (x y : Var) (t e : Expr) :
    RefinesP w (.ite (.eq (.var x) (.var y)) (.letE y (.var x) t) e)
      (.ite (.eq (.var x) (.var y)) t e)
```

- **Reading with key definitions unfolded:** RefinesP w (tgt := ite (eq (var x) (var y)) (letE y (var x) t) e) (src := ite (eq (var x) (var y)) t e).
- **Width dependence:** Generic in w. At w = 0 with integer inputs the test yields 0 and both programs take the else-branch; if x or y is poison, the test is poison and both programs reach UB.
- **Hypothesis ledger:** the stated theorems have no hypotheses beyond the universally quantified width, variables and expressions.
- **Depth:** shallow
- **Non-vacuity witness:** w = 2, then-branch y + freeze y, else-branch y. (`Toy.UB.nonvacuity_poison_gvn_sound`)
- **Supporting theorems** (proved): `Toy.UB.semP_letE_var_var`, `Toy.UB.poisonFreeze_gvn_after_freezing_condition_unsound`.
- **Prior art:**
  - Lee, Kim, Song, Hur, Das, Majnemer, Regehr, Lopes. "Taming Undefined Behavior in LLVM." PLDI 2017, pp. 633-647. DOI 10.1145/3062341.3062343. Section 3.3 (pp. 637-638) shows that GVN needs branch-on-poison to be UB while loop unswitching needs it to be a nondeterministic choice; Section 5.1 (p. 640): 'With the new semantics, GVN becomes sound, since we chose to trigger UB in case of branch on poison value.'
  - LLVM Language Reference Manual, LLVM 19.1.0 release documentation, https://releases.llvm.org/19.1.0/docs/LangRef.html. Poison Values: the condition operand of a br instruction is among the operands for which poison triggers immediate undefined behavior.
  - Kang, Kim, Song, Lee, Park, Shin, Kim, Cho, Choi, Hur, Yi. "Crellvm: Verified Credible Compilation for LLVM." PLDI 2018. DOI 10.1145/3192366.3192377. Validates LLVM's gvn pass (GVN-PRE) with a Coq-verified translation-validation checker.
- **Design question:** Under which value model, and in which order relative to freeze insertion, may an optimizer propagate an equality learned from a branch condition (GVN)?
- **Non-claims:** listed under **Boundaries** (shared S7, S1, S2, S3, S4, and the non-claims of result 9).

Basis: execution (Lean kernel check) — the theorems above, with every name in the ledger and witness lines, are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — Lee et al. (PLDI 2017, Sections 3.3 and 5.1) argue that GVN that propagates an equality learned from a branch condition is sound when branching on poison is UB, and the LLVM 19.1.0 Language Reference lists the condition operand of `br` among the operands on which poison triggers immediate UB. The toy theorem reproduces this argument for integer expressions only; pointers (where provenance matters) and floating point (where `-0.0 == +0.0`) are not modelled, and nothing is claimed about LLVM's GVN pass (validated for LLVM by Crellvm, Kang et al., PLDI 2018).

### 10. `undef-gvn-unsound`

- **Kind and tier:** impossibility; T0. The undef counterpart of the GVN discussion in Lee et al. (PLDI 2017, Section 3.3): when the comparison and a later use may observe different values, equality propagation fails. Restated for the toy undef model.
- **Plain claim:** In the undef model (environments of nonempty sets; branching on an undef value is a nondeterministic choice), for every width w ≥ 1 and distinct variables x ≠ y, the GVN rewrite with then-branch y and else-branch 0 - if x = y then y else 0 to if x = y then (let y := x; y) else 0 - is not a refinement: with x ↦ {0, 1} and y ↦ {1} the comparison may succeed while the later use of x observes 0.
- **Lean statement** (verbatim; proofs omitted): `Toy.UB.undef_gvn_var_branch_distinct_vars_unsound`.

```lean
-- lean/ToyUB/GVN.lean:95-97
theorem undef_gvn_var_branch_distinct_vars_unsound (w : Nat) (hw : 1 ≤ w) (x y : Var) (hxy : x ≠ y) :
    ¬ RefinesU w (.ite (.eq (.var x) (.var y)) (.letE y (.var x) (.var y)) (.const 0))
        (.ite (.eq (.var x) (.var y)) (.var y) (.const 0))
```

- **Reading with key definitions unfolded:** 1 ≤ w → x ≠ y → ¬ RefinesU w (tgt := ite (eq (var x) (var y)) (letE y (var x) (var y)) (const 0)) (src := ite (eq (var x) (var y)) (var y) (const 0)).
- **Width dependence:** Generic for all w ≥ 1; sound at w = 0 (Toy.UB.undef_gvn_sound_width_zero).
- **Hypothesis ledger:**
  - hw : 1 ≤ w: at width 0 the test always yields 0 and both programs take the else-branch. Tightness: **tight (counterexample `Toy.UB.undef_gvn_var_branch_distinct_vars_unsound_needs_width`)**.
  - hxy : x ≠ y: if x = y the comparison is between two uses of one variable and the then-branch is unchanged. Tightness: **tight (counterexample `Toy.UB.undef_gvn_var_branch_distinct_vars_unsound_needs_distinct`)**.
- **Depth:** shallow
- **Non-vacuity witness:** w = 2, x = 0, y = 1: the statement instantiated. (`Toy.UB.nonvacuity_undef_gvn_instance`, `Toy.UB.nonvacuity_undef_gvn`)
- **Positive controls** (nearby settings where the conclusion fails, each proved): `Toy.UB.undef_gvn_sound_width_zero`, `Toy.UB.undef_gvn_sound_of_same_var`, `Toy.UB.undef_gvn_sound_examples_closed_or_x_branch`, `Toy.UB.undef_gvn_with_frozen_operand_sound`. See also the escape hatches under **Boundaries**.
- **Prior art:**
  - Lee, Kim, Song, Hur, Das, Majnemer, Regehr, Lopes. "Taming Undefined Behavior in LLVM." PLDI 2017, pp. 633-647. DOI 10.1145/3062341.3062343. Section 3.3 (pp. 637-638): GVN is unsound if branching on an invalid value is a nondeterministic choice (stated there for poison).
  - LLVM Language Reference Manual, LLVM 19.1.0 release documentation, https://releases.llvm.org/19.1.0/docs/LangRef.html. Undefined Values: 'Branching on an undefined value is undefined behavior. This explains optimizations that depend on branch conditions to construct predicates, such as Correlated Value Propagation and Global Value Numbering.'
- **Design question:** Under which value model, and in which order relative to freeze insertion, may an optimizer propagate an equality learned from a branch condition (GVN)?
- **Non-claims:** listed under **Boundaries** (shared S7, S1, S2, S3, S4, S5, S6, and the non-claims of result 10).

Basis: execution (Lean kernel check) — the theorems above, with every name in the ledger and witness lines, are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — The toy counterexample corresponds to the observation of Lee et al. (PLDI 2017, Section 3.3) that GVN is unsound if branching on an invalid value is a nondeterministic choice. The LLVM 19.1.0 Language Reference instead states "Branching on an undefined value is undefined behavior. This explains optimizations that depend on branch conditions to construct predicates, such as Correlated Value Propagation and Global Value Numbering." Under that rule the source of this counterexample would reach UB, so the toy result is evidence about the nondeterministic-branch reading only, not about LLVM 19.1.0.

### 11. `poison-unswitch-without-freeze-unsound`

- **Kind and tier:** impossibility; T0. Restates Lee et al. (PLDI 2017, Section 3.3): if branching on poison is UB, loop unswitching without freeze can introduce UB when the loop does not run.
- **Plain claim:** In the poison(+freeze) model (branching on poison is UB), for every width w, distinct condition variables c ≠ d, branches a, b and literal else-branch n, rewriting if c then (if d then a else b) else n to if d then (if c then a else n) else (if c then b else n) is not a refinement: with c ↦ 0 and d ↦ poison the source returns n while the target branches on poison.
- **Lean statement** (verbatim; proofs omitted): `Toy.UB.poison_unswitch_without_freeze_distinct_vars_unsound`.

```lean
-- lean/ToyUB/Unswitch.lean:75-78
theorem poison_unswitch_without_freeze_distinct_vars_unsound (w : Nat) (c d : Var) (hcd : c ≠ d)
    (a b : Expr) (n : Nat) :
    ¬ RefinesP w (.ite (.var d) (.ite (.var c) a (.const n)) (.ite (.var c) b (.const n)))
        (.ite (.var c) (.ite (.var d) a b) (.const n))
```

- **Reading with key definitions unfolded:** c ≠ d → ¬ RefinesP w (tgt := ite (var d) (ite (var c) a (const n)) (ite (var c) b (const n))) (src := ite (var c) (ite (var d) a b) (const n)).
- **Width dependence:** Generic in w, including w = 0.
- **Hypothesis ledger:**
  - hcd : c ≠ d: if c = d the inner branch is only reached when the outer one already branched on the same value. Tightness: **tight (counterexample `Toy.UB.poison_unswitch_without_freeze_distinct_vars_unsound_needs_distinct`)**.
- **Depth:** shallow
- **Non-vacuity witness:** w = 2, c = 2, d = 3, branches d and c + d, else-branch 7: the statement instantiated. (`Toy.UB.nonvacuity_poison_unswitch_instance`, `Toy.UB.nonvacuity_poison_unswitch`)
- **Positive controls** (nearby settings where the conclusion fails, each proved): `Toy.UB.poison_unswitch_without_freeze_sound_of_same_var`, `Toy.UB.poisonFreeze_unswitch_with_freeze_sound_of_ubFree`, `Toy.UB.undef_unswitch_without_freeze_sound_of_ubFree`. See also the escape hatches under **Boundaries**.
- **Prior art:**
  - Lee, Kim, Song, Hur, Das, Majnemer, Regehr, Lopes. "Taming Undefined Behavior in LLVM." PLDI 2017, pp. 633-647. DOI 10.1145/3062341.3062343. Section 3.3 (p. 637): loop unswitching 'assumes that branching on poison is not UB, but is rather a non-deterministic choice. Otherwise, if c2 was poison, then loop unswitching would be introducing UB if c was always false'; Section 5.1 (p. 640): 'Freeze can be avoided if the branch on c2 is placed in the loop pre-header (since then the loop is guaranteed to execute at least once).'
  - LLVM Language Reference Manual, LLVM 19.1.0 release documentation, https://releases.llvm.org/19.1.0/docs/LangRef.html. Poison Values: the condition operand of br triggers immediate undefined behavior on poison.
- **Design question:** Under which value model may a branch be hoisted out of a conditional that might not execute it (loop unswitching), what does freeze buy, and what does it not buy?
- **Non-claims:** listed under **Boundaries** (shared S1, S2, S3, S4, and the non-claims of result 11).

Basis: execution (Lean kernel check) — the theorems above, with every name in the ledger and witness lines, are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — This is the toy counterpart of Lee et al. (PLDI 2017, Section 3.3): if branching on poison is UB, hoisting a branch on a condition that the source might never test can introduce UB. The LLVM 19.1.0 Language Reference makes poison in a `br` condition immediate UB. The toy has no loops; the loop is modelled by an outer conditional that may skip the inner branch, so the bridge is an analogy, not a proof about LLVM's loop unswitching.

### 12. `undef-unswitch-without-freeze-sound`

- **Kind and tier:** theorem; T0. Under the nondeterministic-branch reading that loop unswitching assumes (Lee et al., PLDI 2017, Section 3.3, stated there for poison), unswitching is sound; restated for the toy undef model.
- **Plain claim:** In the undef model (environments of nonempty sets; branching on an undef value is a nondeterministic choice), at every width, for every outer condition ec, every inner condition ed that reaches UB in no inhabited environment, and all branches a, b, e, rewriting if ec then (if ed then a else b) else e to if ed then (if ec then a else e) else (if ec then b else e) is a refinement; in particular for condition variables c, d (equal or not).
- **Lean statement** (verbatim; proofs omitted): `Toy.UB.undef_unswitch_without_freeze_sound_of_ubFree`, `Toy.UB.undef_unswitch_without_freeze_sound`.

```lean
-- lean/ToyUB/Unswitch.lean:109-111
theorem undef_unswitch_without_freeze_sound_of_ubFree (w : Nat) (ec ed a b e : Expr)
    (hed : UBFreeU w ed) :
    RefinesU w (.ite ed (.ite ec a e) (.ite ec b e)) (.ite ec (.ite ed a b) e)

-- lean/ToyUB/Unswitch.lean:163-165
theorem undef_unswitch_without_freeze_sound (w : Nat) (c d : Var) (a b e : Expr) :
    RefinesU w (.ite (.var d) (.ite (.var c) a e) (.ite (.var c) b e))
      (.ite (.var c) (.ite (.var d) a b) e)
```

- **Reading with key definitions unfolded:** UBFreeU w ed → RefinesU w (tgt := ite ed (ite ec a e) (ite ec b e)) (src := ite ec (ite ed a b) e);  UBFreeU w ed := ∀ ρ, UInhabited ρ → ¬ MayUB (semU w ρ ed).  Corollary: RefinesU w (ite (var d) (ite (var c) a e) (ite (var c) b e)) (ite (var c) (ite (var d) a b) e).
- **Width dependence:** Generic in w.
- **Hypothesis ledger:**
  - hed : UBFreeU w ed: the target always evaluates ed, the source only when ec is nonzero; UB in ed would be introduced. Tightness: **tight (counterexample `Toy.UB.undef_unswitch_without_freeze_needs_ubFree`)**.
- **Depth:** shallow
- **Non-vacuity witness:** w = 2 with inner condition if d then 1 else 0, outer condition c = x, and branches mentioning both conditions; and the variable corollary with c = 2, d = 3. (`Toy.UB.nonvacuity_undef_unswitch_of_ubFree`, `Toy.UB.nonvacuity_undef_unswitch`)
- **Supporting theorems** (proved): `Toy.UB.undef_unswitch_vars_outRef_all_envs`, `Toy.UB.undef_unswitch_empty_input_target_has_no_outcomes`, `Toy.UB.ubFreeU_examples`.
- **Prior art:**
  - Lee, Kim, Song, Hur, Das, Majnemer, Regehr, Lopes. "Taming Undefined Behavior in LLVM." PLDI 2017, pp. 633-647. DOI 10.1145/3062341.3062343. Section 3.3 (p. 637): loop unswitching assumes that branching on an invalid value is a nondeterministic choice rather than UB.
- **Design question:** Under which value model may a branch be hoisted out of a conditional that might not execute it (loop unswitching), what does freeze buy, and what does it not buy?
- **Non-claims:** listed under **Boundaries** (shared S7, S1, S2, S3, S4, S5, S6, and the non-claims of result 12).

Basis: execution (Lean kernel check) — the theorems above, with every name in the ledger and witness lines, are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — Lee et al. (PLDI 2017, Section 3.3) note that loop unswitching assumes that branching on an invalid value is a nondeterministic choice; the toy undef model adopts that reading and the theorem confirms the rewrite under it. The LLVM 19.1.0 Language Reference does not adopt that reading for `br` on undef, so no conclusion about LLVM follows.

### 13. `poisonFreeze-unswitch-with-freeze-sound`

- **Kind and tier:** theorem; T0. Restates the fix of Lee et al. (PLDI 2017, Section 5.1: 'When a branch is hoisted out of a loop, the condition needs to be frozen') for the toy, with its side conditions made explicit.
- **Plain claim:** In the poison + freeze model, at every width, for every outer condition ec, every inner condition ed that reaches UB in no environment, and every variable t not free in ec, a, b, e, rewriting if ec then (if ed then a else b) else e to let t := freeze ed; if t then (if ec then a else e) else (if ec then b else e) is a refinement; in particular for condition variables c, d with t ≠ c.
- **Lean statement** (verbatim; proofs omitted): `Toy.UB.poisonFreeze_unswitch_with_freeze_sound_of_ubFree`, `Toy.UB.poisonFreeze_unswitch_with_freeze_sound_of_fresh`.

```lean
-- lean/ToyUB/Unswitch.lean:319-325
theorem poisonFreeze_unswitch_with_freeze_sound_of_ubFree (w : Nat) (ec ed : Expr) (t : Var)
    (a b e : Expr) (hed : UBFreeP w ed)
    (htc : ec.freeIn t = false) (hta : a.freeIn t = false)
    (htb : b.freeIn t = false) (hte : e.freeIn t = false) :
    RefinesP w
      (.letE t (.freeze ed) (.ite (.var t) (.ite ec a e) (.ite ec b e)))
      (.ite ec (.ite ed a b) e)

-- lean/ToyUB/Unswitch.lean:415-420
theorem poisonFreeze_unswitch_with_freeze_sound_of_fresh (w : Nat) (c d t : Var) (a b e : Expr)
    (htc : t ≠ c) (hta : a.freeIn t = false) (htb : b.freeIn t = false)
    (hte : e.freeIn t = false) :
    RefinesP w
      (.letE t (.freeze (.var d)) (.ite (.var t) (.ite (.var c) a e) (.ite (.var c) b e)))
      (.ite (.var c) (.ite (.var d) a b) e)
```

- **Reading with key definitions unfolded:** UBFreeP w ed → ec.freeIn t = false → a.freeIn t = false → b.freeIn t = false → e.freeIn t = false → RefinesP w (tgt := letE t (freeze ed) (ite (var t) (ite ec a e) (ite ec b e))) (src := ite ec (ite ed a b) e);  UBFreeP w ed := ∀ ρ, ¬ MayUB (semP w ρ ed).  Corollary (poisonFreeze_unswitch_with_freeze_sound_of_fresh): ec = var c, ed = var d, t ≠ c.
- **Width dependence:** Generic in w.
- **Hypothesis ledger:**
  - hed : UBFreeP w ed: freeze removes poison but not immediate UB (semP w ρ (freeze ub) = [ub]); hoisting an inner condition whose evaluation can reach UB (e.g. one that itself branches on a possibly-poison value) introduces UB. Tightness: **tight (counterexample `Toy.UB.poisonFreeze_unswitch_with_freeze_needs_ubFree`, `Toy.UB.poisonFreeze_unswitch_with_freeze_needs_ubFree_branch`)**.
  - htc : ec.freeIn t = false: the outer condition must still read its own inputs after t is bound. Tightness: **tight (counterexample `Toy.UB.poisonFreeze_unswitch_with_freeze_needs_t_not_free_in_cond`)**.
  - hta : a.freeIn t = false: the branch a must not see the new binding. Tightness: **tight (counterexample `Toy.UB.poisonFreeze_unswitch_with_freeze_needs_t_not_free_in_a`)**.
  - htb : b.freeIn t = false: the branch b must not see the new binding. Tightness: **tight (counterexample `Toy.UB.poisonFreeze_unswitch_with_freeze_needs_t_not_free_in_b`)**.
  - hte : e.freeIn t = false: the branch e must not see the new binding. Tightness: **tight (counterexample `Toy.UB.poisonFreeze_unswitch_with_freeze_needs_t_not_free_in_e`)**.
- **Depth:** shallow
- **Non-vacuity witness:** w = 2 with outer condition x = y, inner condition d = z, t = 4, branches d, c + d, freeze c; all hypotheses hold and the instance is proved. (`Toy.UB.nonvacuity_poisonFreeze_unswitch_of_ubFree`, `Toy.UB.nonvacuity_poisonFreeze_unswitch`)
- **Supporting theorems** (proved): `Toy.UB.ubFreeP_examples`, `Toy.UB.ubFreeP_eq_var`.
- **Prior art:**
  - Lee, Kim, Song, Hur, Das, Majnemer, Regehr, Lopes. "Taming Undefined Behavior in LLVM." PLDI 2017, pp. 633-647. DOI 10.1145/3062341.3062343. Section 5.1 (p. 640): 'When a branch is hoisted out of a loop, the condition needs to be frozen ... By using the freeze instruction, we avoid introducing UB in case c2 is poison and force a non-deterministic choice between the two loops instead.'
  - LLVM Language Reference Manual, LLVM 19.1.0 release documentation, https://releases.llvm.org/19.1.0/docs/LangRef.html. 'freeze' Instruction: 'If the argument is undef or poison, freeze returns an arbitrary, but fixed, value of type ty. Otherwise, this instruction is a no-op and returns the input argument.'
- **Design question:** Under which value model may a branch be hoisted out of a conditional that might not execute it (loop unswitching), what does freeze buy, and what does it not buy?
- **Non-claims:** listed under **Boundaries** (shared S1, S2, S3, S4, and the non-claims of result 13).

Basis: execution (Lean kernel check) — the theorems above, with every name in the ledger and witness lines, are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — This is the toy counterpart of the repair of Lee et al. (PLDI 2017, Section 5.1): freeze the hoisted condition so that a poison condition becomes a nondeterministic choice; the LLVM 19.1.0 Language Reference states that `freeze` of undef or poison returns an arbitrary, but fixed, value. The toy proves the repair for inner conditions that cannot reach UB; for an inner condition that can reach UB, hoisting is unsound even with `freeze` (see the hypothesis ledger). Nothing is derived about LLVM's pass.

### 14. `freeze-identity-on-non-poison`

- **Kind and tier:** theorem; T0. The identity law is the definition of freeze on non-poison values (LLVM 19.1.0 Language Reference, 'freeze' Instruction); the redundant-freeze corollary is the InstCombine folding freeze(freeze(x)) to freeze(x) described by Lee et al. (PLDI 2017, Section 6).
- **Plain claim:** In the poison + freeze model, at every width: if no outcome of e is poison in environment ρ then freeze e has exactly the outcomes of e in ρ (a definitional reference point); consequently, if e never yields poison, rewriting freeze e to e is a refinement, and in particular rewriting freeze (freeze e) to freeze e is a refinement (also in the undef model, over environments of nonempty sets).
- **Lean statement** (verbatim; proofs omitted): `Toy.UB.poisonFreeze_freeze_eq_self_of_no_poison`, `Toy.UB.poisonFreeze_remove_freeze_sound_of_no_poison`, `Toy.UB.poisonFreeze_remove_redundant_freeze_sound`, `Toy.UB.undef_remove_redundant_freeze_sound`.

```lean
-- lean/ToyUB/Freeze.lean:31-32
theorem poisonFreeze_freeze_eq_self_of_no_poison (w : Nat) (ρ : Var → PVal w) (e : Expr)
    (h : Outcome.val PVal.poison ∉ semP w ρ e) : semP w ρ (.freeze e) = semP w ρ e

-- lean/ToyUB/Freeze.lean:263-265
theorem poisonFreeze_remove_freeze_sound_of_no_poison (w : Nat) (e : Expr)
    (h : ∀ ρ : Var → PVal w, Outcome.val PVal.poison ∉ semP w ρ e) :
    RefinesP w e (.freeze e)

-- lean/ToyUB/Freeze.lean:272-273
theorem poisonFreeze_remove_redundant_freeze_sound (w : Nat) (e : Expr) :
    RefinesP w (.freeze e) (.freeze (.freeze e))

-- lean/ToyUB/Freeze.lean:279-280
theorem undef_remove_redundant_freeze_sound (w : Nat) (e : Expr) :
    RefinesU w (.freeze e) (.freeze (.freeze e))
```

- **Reading with key definitions unfolded:** poisonFreeze_freeze_eq_self_of_no_poison w ρ e (h : val poison ∉ semP w ρ e) : semP w ρ (freeze e) = semP w ρ e;  (∀ ρ, val poison ∉ semP w ρ e) → RefinesP w (tgt := e) (src := freeze e);  RefinesP w (tgt := freeze e) (src := freeze (freeze e));  RefinesU w (tgt := freeze e) (src := freeze (freeze e)).
- **Width dependence:** Generic in w.
- **Hypothesis ledger:**
  - h : val poison ∉ semP w ρ e: on poison, freeze returns integers instead. Tightness: **tight (counterexample `Toy.UB.poisonFreeze_freeze_eq_self_needs_no_poison`)**.
  - (corollary) ∀ ρ, val poison ∉ semP w ρ e: removing freeze from a possibly-poison operand reintroduces poison. Tightness: **tight (counterexample `Toy.UB.poisonFreeze_remove_freeze_needs_no_poison`)**.
- **Depth:** shallow (the first statement (the pointwise equality semP w ρ (freeze e) = semP w ρ e) is definitional; the refinement corollaries, in particular the undef-model redundant-freeze theorem, need short non-definitional proofs.)
- **Non-vacuity witness:** x + 1 with x ↦ 1 has no poison outcome (width 2); freeze x + 1 never yields poison; freeze (freeze x) -> freeze x in both models (width 2). (`Toy.UB.nonvacuity_freeze_eq_self`, `Toy.UB.nonvacuity_remove_redundant_freeze`)
- **Prior art:**
  - LLVM Language Reference Manual, LLVM 19.1.0 release documentation, https://releases.llvm.org/19.1.0/docs/LangRef.html. 'freeze' Instruction: 'Otherwise, this instruction is a no-op and returns the input argument.'
  - Lee, Kim, Song, Hur, Das, Majnemer, Regehr, Lopes. "Taming Undefined Behavior in LLVM." PLDI 2017, pp. 633-647. DOI 10.1145/3062341.3062343. Section 6 (p. 642): InstCombine folds freeze(freeze(x)) to freeze(x) and freeze(const) to const.
- **Design question:** Which algebraic laws of freeze (insertion, removal, duplication, merging) can an optimizer rely on in a semantics with poison and freeze?
- **Non-claims:** listed under **Boundaries** (shared S1, S2, S3, S4, S5, S6, and the non-claims of result 14).

Basis: execution (Lean kernel check) — the theorems above, with every name in the ledger and witness lines, are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — The pointwise identity matches the LLVM 19.1.0 Language Reference for `freeze` ("Otherwise, this instruction is a no-op and returns the input argument."), and redundant-freeze elimination matches the InstCombine fold `freeze(freeze(x)) -> freeze(x)` described by Lee et al. (PLDI 2017, Section 6). The never-poison side condition is semantic in the toy; how a compiler establishes it is not modelled.

### 15. `freeze-insertion-sound`

- **Kind and tier:** theorem; T0. Follows from the definition of freeze and of value refinement (poison and undef sets are refined by any of their possible values; Lopes et al., PLDI 2021, Section 5.1); restated for the toy.
- **Plain claim:** At every width and for every expression e, rewriting e to freeze e is a refinement in the poison + freeze model and in the undef model (over environments of nonempty sets).
- **Lean statement** (verbatim; proofs omitted): `Toy.UB.poisonFreeze_insert_freeze_sound`, `Toy.UB.undef_insert_freeze_sound`.

```lean
-- lean/ToyUB/Freeze.lean:59
theorem poisonFreeze_insert_freeze_sound (w : Nat) (e : Expr) : RefinesP w (.freeze e) e

-- lean/ToyUB/Freeze.lean:180
theorem undef_insert_freeze_sound (w : Nat) (e : Expr) : RefinesU w (.freeze e) e
```

- **Reading with key definitions unfolded:** RefinesP w (tgt := freeze e) (src := e);  RefinesU w (tgt := freeze e) (src := e).
- **Width dependence:** Generic in w.
- **Hypothesis ledger:** the stated theorems have no hypotheses beyond the universally quantified width, variables and expressions.
- **Depth:** shallow
- **Non-vacuity witness:** e = if x then y else ub, which may reach UB in some environments (width 2, both models). (`Toy.UB.nonvacuity_insert_freeze`)
- **Supporting theorems** (proved): `Toy.UB.poisonFreeze_gvn_after_freezing_condition_unsound`.
- **Prior art:**
  - LLVM Language Reference Manual, LLVM 19.1.0 release documentation, https://releases.llvm.org/19.1.0/docs/LangRef.html. 'freeze' Instruction and Poison Values: 'It is correct to replace a poison value with an undef value or any value of the type.'
  - Lee, Kim, Song, Hur, Das, Majnemer, Regehr, Lopes. "Taming Undefined Behavior in LLVM." PLDI 2017, pp. 633-647. DOI 10.1145/3062341.3062343. Section 6 (pp. 642-643, paragraphs 'Optimizations' and 'Opportunities for improvement') describes optimizations that freeze blocked in the authors' prototype (lowering a branch on a frozen and/or into two jumps; moving a frozen comparison next to its branch) and notes that GVN does not yet fold equivalent freeze instructions; Section 7.2 (p. 644) reports a benchmark in which jump threading did not kick in because it did not know about freeze.
- **Design question:** Which algebraic laws of freeze (insertion, removal, duplication, merging) can an optimizer rely on in a semantics with poison and freeze?
- **Non-claims:** listed under **Boundaries** (shared S1, S2, S3, S4, S5, S6, and the non-claims of result 15).

Basis: execution (Lean kernel check) — the theorems above, with every name in the ledger and witness lines, are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — The LLVM 19.1.0 Language Reference (Poison Values) states "It is correct to replace a poison value with an undef value or any value of the type", which is what inserting a `freeze` does in the toy. Lee et al. (PLDI 2017, Sections 6 and 7.2) report optimizations that a `freeze` blocked in their prototype; the toy proves only that insertion is a refinement, not that it is free for later optimization.

### 16. `freeze-removal-unsound`

- **Kind and tier:** impossibility; T0. Converse of freeze insertion; follows from the definitions (poison refines no integer; a non-singleton undef set is contained in no singleton). Restated for the toy.
- **Plain claim:** Rewriting freeze x to x (x a variable) is not a refinement: in the poison + freeze model at every width (with x ↦ poison the target yields poison, which refines no integer), and in the undef model (over environments of nonempty sets) at every width w ≥ 1 (with x ↦ {0, 1} the target's value set is contained in no source singleton).
- **Lean statement** (verbatim; proofs omitted): `Toy.UB.poisonFreeze_remove_freeze_unsound`, `Toy.UB.undef_remove_freeze_unsound`.

```lean
-- lean/ToyUB/Freeze.lean:82-83
theorem poisonFreeze_remove_freeze_unsound (w : Nat) (x : Var) :
    ¬ RefinesP w (.var x) (.freeze (.var x))

-- lean/ToyUB/Freeze.lean:205-206
theorem undef_remove_freeze_unsound (w : Nat) (hw : 1 ≤ w) (x : Var) :
    ¬ RefinesU w (.var x) (.freeze (.var x))
```

- **Reading with key definitions unfolded:** ¬ RefinesP w (tgt := var x) (src := freeze (var x));  1 ≤ w → ¬ RefinesU w (tgt := var x) (src := freeze (var x)).
- **Width dependence:** Poison part: every w. Undef part: every w ≥ 1; sound at w = 0 (Toy.UB.undef_remove_freeze_sound_width_zero).
- **Hypothesis ledger:**
  - hw : 1 ≤ w (undef part only): at width 0 every nonempty set is {0}, a singleton. Tightness: **tight (counterexample `Toy.UB.undef_remove_freeze_unsound_needs_width`)**.
- **Depth:** shallow
- **Non-vacuity witness:** w = 2, x = 0: both statements instantiated. (`Toy.UB.nonvacuity_remove_freeze_unsound`, `Toy.UB.nonvacuity_width_two`)
- **Positive controls** (nearby settings where the conclusion fails, each proved): `Toy.UB.poisonFreeze_remove_freeze_sound_of_no_poison`, `Toy.UB.poisonFreeze_remove_redundant_freeze_sound`, `Toy.UB.undef_remove_redundant_freeze_sound`, `Toy.UB.undef_remove_freeze_sound_width_zero`. See also the escape hatches under **Boundaries**.
- **Prior art:**
  - LLVM Language Reference Manual, LLVM 19.1.0 release documentation, https://releases.llvm.org/19.1.0/docs/LangRef.html. 'freeze' Instruction: freeze returns a fixed value on undef or poison, so removing it can re-expose poison or undef.
  - Lee, Kim, Song, Hur, Das, Majnemer, Regehr, Lopes. "Taming Undefined Behavior in LLVM." PLDI 2017, pp. 633-647. DOI 10.1145/3062341.3062343. Section 6 (p. 642): freeze(freeze(x)) is folded to freeze(x).
- **Design question:** Which algebraic laws of freeze (insertion, removal, duplication, merging) can an optimizer rely on in a semantics with poison and freeze?
- **Non-claims:** listed under **Boundaries** (shared S1, S2, S3, S4, S5, and the non-claims of result 16).

Basis: execution (Lean kernel check) — the theorems above, with every name in the ledger and witness lines, are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — In LLVM, `freeze` of undef or poison returns an arbitrary but fixed value (LLVM 19.1.0 Language Reference, 'freeze' Instruction), so removing it can re-expose poison or undef; the toy counterexamples exhibit exactly this. The bridge is by correspondence of definitions only.

### 17. `frozen-value-used-twice-even`

- **Kind and tier:** theorem; T0. Restates the LLVM 19.1.0 Language Reference's freeze example (%z = add i32 %x, %x is even because all uses of %x observe the same value, while two freeze instructions may differ) for the toy.
- **Plain claim:** In the poison + freeze model, at every width w and in every environment, let a := freeze x; a + a has at least one outcome and every outcome is an even integer (never poison or UB); whereas with x ↦ poison, freeze x + freeze x has every w-bit integer as an outcome, in particular (for w ≥ 1) an odd one.
- **Lean statement** (verbatim; proofs omitted): `Toy.UB.poisonFreeze_let_freeze_add_self_nonempty_even`, `Toy.UB.poisonFreeze_freeze_add_freeze_all_values_of_poison`, `Toy.UB.poisonFreeze_freeze_add_freeze_can_be_odd`.

```lean
-- lean/ToyUB/Freeze.lean:307-311
theorem poisonFreeze_let_freeze_add_self_nonempty_even (w : Nat) (x a : Var)
    (ρ : Var → PVal w) :
    semP w ρ (.letE a (.freeze (.var x)) (.add (.var a) (.var a))) ≠ [] ∧
    ∀ o ∈ semP w ρ (.letE a (.freeze (.var x)) (.add (.var a) (.var a))),
      ∃ v : BitVec w, o = .val (.int v) ∧ v.toNat % 2 = 0

-- lean/ToyUB/Freeze.lean:317-320
theorem poisonFreeze_freeze_add_freeze_all_values_of_poison (w : Nat) (x : Var)
    (v : BitVec w) :
    Outcome.val (PVal.int v) ∈
      semP w (fun _ => .poison) (.add (.freeze (.var x)) (.freeze (.var x)))

-- lean/ToyUB/Freeze.lean:114-117
theorem poisonFreeze_freeze_add_freeze_can_be_odd (w : Nat) (hw : 1 ≤ w) (x : Var) :
    ∃ ρ : Var → PVal w, ∃ v : BitVec w,
      Outcome.val (PVal.int v) ∈ semP w ρ (.add (.freeze (.var x)) (.freeze (.var x))) ∧
      v.toNat % 2 = 1
```

- **Reading with key definitions unfolded:** semP w ρ (letE a (freeze (var x)) (add (var a) (var a))) ≠ [] ∧ ∀ o ∈ semP w ρ (letE a (freeze (var x)) (add (var a) (var a))), ∃ v, o = val (int v) ∧ v.toNat % 2 = 0;  ∀ v, val (int v) ∈ semP w (fun _ => poison) (add (freeze (var x)) (freeze (var x)));  1 ≤ w → ∃ ρ v, val (int v) ∈ semP w ρ (add (freeze (var x)) (freeze (var x))) ∧ v.toNat % 2 = 1.
- **Width dependence:** Generic in w; the odd outcome needs w ≥ 1.
- **Hypothesis ledger:**
  - hw : 1 ≤ w (odd outcome only): at width 0 every integer is 0, which is even. Tightness: **tight (counterexample `Toy.UB.poisonFreeze_freeze_add_freeze_can_be_odd_needs_width`)**.
- **Depth:** shallow
- **Non-vacuity witness:** w = 2, where the hypothesis 1 ≤ w holds (1 ≤ 2, stated by Toy.UB.nonvacuity_width_two); with x ↦ poison, let a := freeze x; a + a has the outcome 2, and freeze x + freeze x has an odd outcome. (`Toy.UB.nonvacuity_let_freeze_mem`, `Toy.UB.nonvacuity_width_two`)
- **Prior art:**
  - LLVM Language Reference Manual, LLVM 19.1.0 release documentation, https://releases.llvm.org/19.1.0/docs/LangRef.html. 'freeze' Instruction example: '%z = add i32 %x, %x ; even number because all uses of %x observe the same value' and '%cmp = icmp eq i32 %x, %x2 ; can be true or false'.
  - Lee, Kim, Song, Hur, Das, Majnemer, Regehr, Lopes. "Taming Undefined Behavior in LLVM." PLDI 2017, pp. 633-647. DOI 10.1145/3062341.3062343. Section 4 (p. 639): 'All uses of a given freeze return the same value, but different freezes of a value may return different constants.'
- **Design question:** Which algebraic laws of freeze (insertion, removal, duplication, merging) can an optimizer rely on in a semantics with poison and freeze?
- **Non-claims:** listed under **Boundaries** (shared S1, S2, S3, S4, and the non-claims of result 17).

Basis: execution (Lean kernel check) — the theorems above, with every name in the ledger and witness lines, are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — The toy facts restate the example in the LLVM 19.1.0 Language Reference for `freeze` (`%z = add i32 %x, %x ; even number because all uses of %x observe the same value`, while `%cmp = icmp eq i32 %x, %x2 ; can be true or false` for two separate freezes) and Lee et al. (PLDI 2017, Section 4). The correspondence is by definitions; the toy proves only the toy facts.

### 18. `duplicate-freeze-unsound`

- **Kind and tier:** impossibility; T0. Restates Lee et al. (PLDI 2017, Section 5.5, 'Pitfall 1: Freeze duplication') for the toy.
- **Plain claim:** In the poison + freeze model, at every width w ≥ 1 and for all variables x, a, duplicating a freeze - rewriting let a := freeze x; a + a to freeze x + freeze x - is not a refinement (with x ↦ poison the target may be odd, the source never is).
- **Lean statement** (verbatim; proofs omitted): `Toy.UB.poisonFreeze_duplicate_freeze_unsound`.

```lean
-- lean/ToyUB/Freeze.lean:127-129
theorem poisonFreeze_duplicate_freeze_unsound (w : Nat) (hw : 1 ≤ w) (x a : Var) :
    ¬ RefinesP w (.add (.freeze (.var x)) (.freeze (.var x)))
        (.letE a (.freeze (.var x)) (.add (.var a) (.var a)))
```

- **Reading with key definitions unfolded:** 1 ≤ w → ¬ RefinesP w (tgt := add (freeze (var x)) (freeze (var x))) (src := letE a (freeze (var x)) (add (var a) (var a))).
- **Width dependence:** Generic for all w ≥ 1; sound at w = 0 (Toy.UB.poisonFreeze_duplicate_freeze_sound_width_zero).
- **Hypothesis ledger:**
  - hw : 1 ≤ w: at width 0 every integer is 0. Tightness: **tight (counterexample `Toy.UB.poisonFreeze_duplicate_freeze_unsound_needs_width`)**.
- **Depth:** shallow
- **Non-vacuity witness:** w = 2, x = 0, a = 1: the statement instantiated. (`Toy.UB.nonvacuity_duplicate_freeze_unsound`, `Toy.UB.nonvacuity_width_two`)
- **Positive controls** (nearby settings where the conclusion fails, each proved): `Toy.UB.poisonFreeze_duplicate_freeze_sound_width_zero`, `Toy.UB.poisonFreeze_merge_freeze_sound`, `Toy.UB.poisonFreeze_duplicate_freeze_sound_at_int`. See also the escape hatches under **Boundaries**.
- **Supporting theorems** (proved): `Toy.UB.poisonFreeze_let_freeze_add_self_nonempty_even`, `Toy.UB.poisonFreeze_freeze_add_freeze_can_be_odd`, `Toy.UB.poisonFreeze_duplicate_freeze_of_nonpoison_compound_unsound`.
- **Prior art:**
  - Lee, Kim, Song, Hur, Das, Majnemer, Regehr, Lopes. "Taming Undefined Behavior in LLVM." PLDI 2017, pp. 633-647. DOI 10.1145/3062341.3062343. Section 5.5 ('Pitfall 1: Freeze duplication', p. 641): 'Duplicating freeze instructions is not allowed, since each freeze instruction may return a different value if the input is poison.'
  - LLVM Language Reference Manual, LLVM 19.1.0 release documentation, https://releases.llvm.org/19.1.0/docs/LangRef.html. 'freeze' Instruction: 'different freeze instructions may yield different values'.
- **Design question:** Which algebraic laws of freeze (insertion, removal, duplication, merging) can an optimizer rely on in a semantics with poison and freeze?
- **Non-claims:** listed under **Boundaries** (shared S1, S2, S3, S4, and the non-claims of result 18).

Basis: execution (Lean kernel check) — the theorems above, with every name in the ledger and witness lines, are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — The toy counterexample instantiates Lee et al. (PLDI 2017, Section 5.5: "Duplicating freeze instructions is not allowed, since each freeze instruction may return a different value if the input is poison.") and the LLVM 19.1.0 Language Reference ('different freeze instructions may yield different values'). It supports that statement by analogy; it does not prove it for LLVM.

### 19. `merge-freeze-sound`

- **Kind and tier:** theorem; T0. Lee et al. (PLDI 2017, Section 6) discuss folding equivalent freeze instructions in GVN, with the condition that all uses be replaced; restated for the toy with a generic operand.
- **Plain claim:** In the poison + freeze model, at every width, for every expression e and variable a, merging two freezes of the same operand - rewriting freeze e + freeze e to let a := freeze e; a + a - is a refinement.
- **Lean statement** (verbatim; proofs omitted): `Toy.UB.poisonFreeze_merge_freeze_sound`.

```lean
-- lean/ToyUB/Freeze.lean:158-159
theorem poisonFreeze_merge_freeze_sound (w : Nat) (e : Expr) (a : Var) :
    RefinesP w (.letE a (.freeze e) (.add (.var a) (.var a))) (.add (.freeze e) (.freeze e))
```

- **Reading with key definitions unfolded:** RefinesP w (tgt := letE a (freeze e) (add (var a) (var a))) (src := add (freeze e) (freeze e)).
- **Width dependence:** Generic in w.
- **Hypothesis ledger:** the stated theorems have no hypotheses beyond the universally quantified width, variables and expressions.
- **Depth:** shallow
- **Non-vacuity witness:** e = freeze x, a = 5 (width 2). (`Toy.UB.nonvacuity_merge_freeze`)
- **Supporting theorems** (proved): `Toy.UB.poisonFreeze_partial_merge_freeze_unsound`.
- **Prior art:**
  - Lee, Kim, Song, Hur, Das, Majnemer, Regehr, Lopes. "Taming Undefined Behavior in LLVM." PLDI 2017, pp. 633-647. DOI 10.1145/3062341.3062343. Section 6 (p. 643): 'for GVN to be sound for freeze it has to replace all uses of a given freeze instruction if it wants to replace one of the uses.'
  - LLVM Language Reference Manual, LLVM 19.1.0 release documentation, https://releases.llvm.org/19.1.0/docs/LangRef.html. 'freeze' Instruction: all uses of one freeze observe the same value.
- **Design question:** Which algebraic laws of freeze (insertion, removal, duplication, merging) can an optimizer rely on in a semantics with poison and freeze?
- **Non-claims:** listed under **Boundaries** (shared S1, S2, S3, S4, and the non-claims of result 19).

Basis: execution (Lean kernel check) — the theorems above, with every name in the ledger and witness lines, are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — Lee et al. (PLDI 2017, Section 6) state that for GVN to be sound for freeze it has to replace all uses of a given freeze instruction if it replaces one of them; merging both freezes of the same operand into one shared freeze is the toy counterpart, and the supporting theorem `poisonFreeze_partial_merge_freeze_unsound` shows that merging only some uses is unsound. The bridge is an analogy, not a proof about LLVM's GVN.

### 20. `poison-refines-eager-uninit`

- **Kind and tier:** theorem; T1. That a deferred invalid value (poison) is weaker than an eagerly-UB one is noted informally by Lee et al. (PLDI 2017, Section 9, comparing Firm's 'Bad' value with poison); made precise here for a toy expression language.
- **Plain claim:** For every width w, eager environment ρ (each input initialized or not) and fixed program e: either the eager-uninitialized evaluation of e (reading an uninitialized input is UB) may reach UB, or every poison(+freeze)-model outcome of e on the same environment read with uninitialized ↦ poison is equal to an eager outcome; in particular the poison(+freeze)-model outcomes refine the eager ones.
- **Lean statement** (verbatim; proofs omitted): `Toy.UB.poison_refines_eagerUninit_eq`, `Toy.UB.poison_refines_eagerUninit`.

```lean
-- lean/ToyUB/Uninit.lean:171-172
theorem poison_refines_eagerUninit_eq (w : Nat) (ρ : Var → Option (BitVec w)) (e : Expr) :
    OutRef (fun a b => a = b) (semP w (toPoisonEnv ρ) e) ((semE w ρ e).map Outcome.toP)

-- lean/ToyUB/Uninit.lean:181-182
theorem poison_refines_eagerUninit (w : Nat) (ρ : Var → Option (BitVec w)) (e : Expr) :
    OutRef PVal.Refines (semP w (toPoisonEnv ρ) e) ((semE w ρ e).map Outcome.toP)
```

- **Reading with key definitions unfolded:** OutRef (· = ·) (semP w (toPoisonEnv ρ) e) ((semE w ρ e).map Outcome.toP);  corollary: OutRef PVal.Refines (semP w (toPoisonEnv ρ) e) ((semE w ρ e).map Outcome.toP).
- **Width dependence:** Generic in w.
- **Hypothesis ledger:** the stated theorems have no hypotheses beyond the universally quantified width, variables and expressions.
- **Depth:** shallow
- **Non-vacuity witness:** let y := x; 0 with x uninitialized (width 2): eager UB, poison result 0, and the refinement holds; also if x then 3 else y with x ↦ 1, y uninitialized. (`Toy.UB.nonvacuity_poison_refines_eagerUninit_live`, `Toy.UB.nonvacuity_poison_refines_eagerUninit`)
- **Supporting theorems** (proved): `Toy.UB.semE_spec`, `Toy.UB.dead_read_insertion_poison_sound_eager_unsound`, `Toy.UB.mul_zero_to_branch_eager_sound_poison_unsound`, `Toy.UB.outRef_mono_rel`.
- **Prior art:**
  - Lee, Kim, Song, Hur, Das, Majnemer, Regehr, Lopes. "Taming Undefined Behavior in LLVM." PLDI 2017, pp. 633-647. DOI 10.1145/3062341.3062343. Section 9 (p. 645): 'Firm additionally has the concept of a "Bad" value, the use of which triggers UB. This semantics is stronger than LLVM's poison'.
  - The Rust Reference, Rust 1.83.0, "Behavior considered undefined", https://doc.rust-lang.org/1.83.0/reference/behavior-considered-undefined.html. Under 'Producing an invalid value': 'An integer (i*/u*), floating point value (f*), or raw pointer must be initialized, i.e., must not be obtained from uninitialized memory.' The toy's eager reading mirrors this rule for whole integer inputs only.
  - Jung. "'What The Hardware Does' is not What Your Program Does: Uninitialized Memory." Blog post, 14 July 2019, https://www.ralfj.de/blog/2019/07/14/uninit.html. Informal account of uninitialized memory in the Rust/C abstract machine as bytes that may be absent ('Option<u8>'), relating the absent byte to LLVM's poison.
  - Lobo, McIver, Mitenkov, Lee, Sundararajah, Lopes. "Towards Removing Undef Values from LLVM IR." Proc. ACM Program. Lang. 10 (PLDI), Article 172, 2026. DOI 10.1145/3808250. Proposes a raw byte type and a freezing load so that uninitialized memory in LLVM can be modelled with poison rather than undef (context; not formalized here).
  - Memarian, Gomes, Davis, Kell, Richardson, Watson, Sewell. "Exploring C Semantics and Pointer Provenance." Proc. ACM Program. Lang. 3 (POPL), Article 67, 2019. DOI 10.1145/3290380. Section 1 states that the paper does not address uninitialised values; cited only as contrast.
- **Design question:** Can uninitialized reads be modelled as poison instead of immediate UB, and what does the choice change for a verifier comparing programs under the two readings?
- **Non-claims:** listed under **Boundaries** (shared S8, S9, S10, S1, S2, S3, S4, and the non-claims of result 20).

Basis: execution (Lean kernel check) — the theorems above, with every name in the ledger and witness lines, are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — The eager reading mirrors, for whole integer inputs only, the Rust Reference 1.83.0 rule that an integer 'must not be obtained from uninitialized memory'; the poison reading resembles modelling uninitialized memory as poison (Jung, 2019, informally; Lobo et al., PLDI 2026, for LLVM). The toy theorem says only that, for each fixed program, the poison reading exhibits no behaviour the eager reading forbids. It says nothing about lowering Rust to LLVM IR (`noundef`, padding, `MaybeUninit`) and does not transfer the soundness of rewrites between the readings.

### 21. `eager-uninit-does-not-refine-poison`

- **Kind and tier:** counterexample; T1. The converse direction of poison-refines-eager-uninit; a concrete instance of the Firm-versus-poison remark of Lee et al. (PLDI 2017, Section 9).
- **Plain claim:** For every width w, with every input uninitialized, the program let y := x; 0 (which reads x and discards it) is UB in the eager-uninitialized reading but returns 0 in the poison reading, so eager outcomes do not refine poison outcomes in general.
- **Lean statement** (verbatim; proofs omitted): `Toy.UB.eagerUninit_not_refines_poison`.

```lean
-- lean/ToyUB/Uninit.lean:189-191
theorem eagerUninit_not_refines_poison (w : Nat) :
    ¬ OutRef PVal.Refines ((semE w (fun _ => none) (.letE 1 (.var 0) (.const 0))).map Outcome.toP)
        (semP w (toPoisonEnv fun _ => none) (.letE 1 (.var 0) (.const 0)))
```

- **Reading with key definitions unfolded:** ¬ OutRef PVal.Refines ((semE w (fun _ => none) (letE 1 (var 0) (const 0))).map Outcome.toP) (semP w (toPoisonEnv fun _ => none) (letE 1 (var 0) (const 0))).
- **Width dependence:** Generic in w, including w = 0.
- **Hypothesis ledger:** the stated theorems have no hypotheses beyond the universally quantified width, variables and expressions.
- **Depth:** shallow
- **Non-vacuity witness:** The statement is a concrete counterexample at every width. (`Toy.UB.eagerUninit_not_refines_poison`)
- **Prior art:**
  - Lee, Kim, Song, Hur, Das, Majnemer, Regehr, Lopes. "Taming Undefined Behavior in LLVM." PLDI 2017, pp. 633-647. DOI 10.1145/3062341.3062343. Section 9 (p. 645): Firm's 'Bad' value, 'the use of which triggers UB', is stronger than LLVM's poison.
  - The Rust Reference, Rust 1.83.0, "Behavior considered undefined", https://doc.rust-lang.org/1.83.0/reference/behavior-considered-undefined.html. 'Behavior considered undefined', 'Producing an invalid value' (integers must be initialized).
- **Design question:** Can uninitialized reads be modelled as poison instead of immediate UB, and what does the choice change for a verifier comparing programs under the two readings?
- **Non-claims:** listed under **Boundaries** (shared S8, S9, S10, S1, S2, S3, S4, and the non-claims of result 21).

Basis: execution (Lean kernel check) — the theorems above, with every name in the ledger and witness lines, are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — With the same correspondence as the previous result, the counterexample shows that the eager reading is strictly more UB-prone for a program that reads an uninitialized input and discards it. This is a statement about the toy readings; how Rust or LLVM treat such a read is outside the model.

### 22. `semantics-total`

- **Kind and tier:** theorem; T0. Totality of the outcome semantics is a routine sanity property; stated so that no refinement result can be satisfied by an empty target.
- **Plain claim:** At every width, every expression has at least one outcome in every poison(+freeze)-model environment and in every undef-model environment that binds each variable to a nonempty set; consequently RefinesP and RefinesU are equivalent to the variants that additionally require a nonempty target outcome list, so no refinement result in this package holds because a target has no outcomes.
- **Lean statement** (verbatim; proofs omitted): `Toy.UB.semP_ne_nil`, `Toy.UB.semU_ne_nil`, `Toy.UB.refinesP_iff_outRefNE`, `Toy.UB.refinesU_iff_outRefNE`.

```lean
-- lean/ToyUB/Monotone.lean:324
theorem semP_ne_nil (w : Nat) (e : Expr) : ∀ ρ : Var → PVal w, semP w ρ e ≠ []

-- lean/ToyUB/Monotone.lean:367-368
theorem semU_ne_nil (w : Nat) (e : Expr) :
    ∀ ρ : Var → USet w, UInhabited ρ → semU w ρ e ≠ []

-- lean/ToyUB/Monotone.lean:429-430
theorem refinesP_iff_outRefNE (w : Nat) (tgt src : Expr) :
    RefinesP w tgt src ↔ ∀ ρ : Var → PVal w, OutRefNE PVal.Refines (semP w ρ tgt) (semP w ρ src)

-- lean/ToyUB/Monotone.lean:435-437
theorem refinesU_iff_outRefNE (w : Nat) (tgt src : Expr) :
    RefinesU w tgt src ↔
      ∀ ρ : Var → USet w, UInhabited ρ → OutRefNE USet.Sub (semU w ρ tgt) (semU w ρ src)
```

- **Reading with key definitions unfolded:** semP w ρ e ≠ [];  UInhabited ρ → semU w ρ e ≠ [];  RefinesP w tgt src ↔ ∀ ρ, OutRefNE PVal.Refines (semP w ρ tgt) (semP w ρ src);  RefinesU w tgt src ↔ ∀ ρ, UInhabited ρ → OutRefNE USet.Sub (semU w ρ tgt) (semU w ρ src);  OutRefNE R T S := MayUB S ∨ ((S ≠ [] → T ≠ []) ∧ ∀ o ∈ T, ∃ o' ∈ S, LeVal R o o').
- **Width dependence:** Generic in w.
- **Hypothesis ledger:**
  - UInhabited ρ (undef model): with an empty input set, if on that input has no outcome. Tightness: **tight (counterexample `Toy.UB.undef_unswitch_empty_input_target_has_no_outcomes`)**.
- **Depth:** shallow
- **Non-vacuity witness:** if freeze x then y else ub at width 2 in both models, and the OutRefNE form of 2*x refining x+x. The undef-model environment used (every variable bound to {0}) satisfies UInhabited; that fact is stated as a theorem in Toy.UB.uInhabited_examples (which also shows that the all-empty environment is not inhabited). (`Toy.UB.nonvacuity_semantics_total`)
- **Supporting theorems** (proved): `Toy.UB.uInhabited_examples`.
- **Prior art:**
  - Lopes, Lee, Hur, Liu, Regehr. "Alive2: Bounded Translation Validation for LLVM." PLDI 2021, pp. 65-79. DOI 10.1145/3453483.3454030. Section 5.2 (pp. 71-72): refinement quantifies over target behaviours, so a target with no behaviour would satisfy it vacuously; the toy semantics are shown never to produce that case.
- **Design question:** How must refinement between programs with undefined values be defined (value-level, permissive after source UB, aware of nondeterminism) so that it is a preorder and composes through every language construct, and which candidate definitions fail?
- **Non-claims:** listed under **Boundaries** (shared S1, S2, S3, S4, S5, S6, and the non-claims of result 22).

Basis: execution (Lean kernel check) — the theorems above, with every name in the ledger and witness lines, are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — Alive2's refinement (Lopes et al., PLDI 2021, Section 5.2) quantifies over target behaviours, so a target with no behaviour would satisfy it vacuously; the toy semantics are shown never to produce that case, so no toy refinement result holds vacuously. Beyond this structural correspondence, no claim about a real system is made.

### Verbatim statements of counterexamples, witnesses, controls and supporting theorems

Every other Lean name referenced by a card, with its statement as it appears in the source (proofs omitted), in order of first reference.

#### `Toy.UB.refinesU_trans_needs_hab` (`lean/ToyUB/Tightness.lean`)

```lean
-- lean/ToyUB/Tightness.lean:121-122
theorem refinesU_trans_needs_hab :
    RefinesU 2 (.freeze (.var 0)) (.freeze (.var 0)) ∧ ¬ RefinesU 2 (.var 0) (.freeze (.var 0))
```

#### `Toy.UB.refinesP_trans_needs_hab` (`lean/ToyUB/Tightness.lean`)

```lean
-- lean/ToyUB/Tightness.lean:131-132
theorem refinesP_trans_needs_hab :
    RefinesP 2 (.freeze (.var 0)) (.freeze (.var 0)) ∧ ¬ RefinesP 2 (.var 0) (.freeze (.var 0))
```

#### `Toy.UB.refinesU_trans_needs_hbc` (`lean/ToyUB/Tightness.lean`)

```lean
-- lean/ToyUB/Tightness.lean:115-116
theorem refinesU_trans_needs_hbc :
    RefinesU 2 (.var 0) (.var 0) ∧ ¬ RefinesU 2 (.var 0) (.freeze (.var 0))
```

#### `Toy.UB.refinesP_trans_needs_hbc` (`lean/ToyUB/Tightness.lean`)

```lean
-- lean/ToyUB/Tightness.lean:126-127
theorem refinesP_trans_needs_hbc :
    RefinesP 2 (.var 0) (.var 0) ∧ ¬ RefinesP 2 (.var 0) (.freeze (.var 0))
```

#### `Toy.UB.nonvacuity_refinesU_trans` (`lean/ToyUB/NonVacuity.lean`)

```lean
-- lean/ToyUB/NonVacuity.lean:21-23
theorem nonvacuity_refinesU_trans :
    RefinesU 2 (.freeze (.mul (.const 2) (.var 0))) (.mul (.const 2) (.var 0)) ∧
    RefinesU 2 (.mul (.const 2) (.var 0)) (.add (.var 0) (.var 0))
```

#### `Toy.UB.nonvacuity_refinesP_trans` (`lean/ToyUB/NonVacuity.lean`)

```lean
-- lean/ToyUB/NonVacuity.lean:28-30
theorem nonvacuity_refinesP_trans :
    RefinesP 2 (.freeze (.mul (.const 2) (.var 0))) (.mul (.const 2) (.var 0)) ∧
    RefinesP 2 (.mul (.const 2) (.var 0)) (.add (.var 0) (.var 0))
```

#### `Toy.UB.refinesU_of_src_mayUB_needs_mayUB` (`lean/ToyUB/Tightness.lean`)

```lean
-- lean/ToyUB/Tightness.lean:137
theorem refinesU_of_src_mayUB_needs_mayUB : ¬ ∀ tgt, RefinesU 2 tgt (.freeze (.var 0))
```

#### `Toy.UB.refinesP_of_src_mayUB_needs_mayUB` (`lean/ToyUB/Tightness.lean`)

```lean
-- lean/ToyUB/Tightness.lean:142
theorem refinesP_of_src_mayUB_needs_mayUB : ¬ ∀ tgt, RefinesP 2 tgt (.freeze (.var 0))
```

#### `Toy.UB.nonvacuity_refinesU_of_src_mayUB` (`lean/ToyUB/NonVacuity.lean`)

```lean
-- lean/ToyUB/NonVacuity.lean:34-35
theorem nonvacuity_refinesU_of_src_mayUB :
    ∀ ρ : Var → USet 2, UInhabited ρ → MayUB (semU 2 ρ (.add (.var 0) .ub))
```

#### `Toy.UB.nonvacuity_refinesP_of_src_mayUB` (`lean/ToyUB/NonVacuity.lean`)

```lean
-- lean/ToyUB/NonVacuity.lean:40-41
theorem nonvacuity_refinesP_of_src_mayUB :
    ∀ ρ : Var → PVal 2, MayUB (semP 2 ρ (.ite (.var 0) .ub .ub))
```

#### `Toy.UB.refinesU_congr_add_premises_tight` (`lean/ToyUB/Tightness.lean`)

```lean
-- lean/ToyUB/Tightness.lean:31-33
theorem refinesU_congr_add_premises_tight :
    (RefinesU 2 (.const 0) (.const 0) ∧ ¬ RefinesU 2 (.add (.const 1) (.const 0)) (.add (.const 0) (.const 0))) ∧
    (RefinesU 2 (.const 0) (.const 0) ∧ ¬ RefinesU 2 (.add (.const 0) (.const 1)) (.add (.const 0) (.const 0)))
```

#### `Toy.UB.refinesU_congr_mul_premises_tight` (`lean/ToyUB/Tightness.lean`)

```lean
-- lean/ToyUB/Tightness.lean:38-40
theorem refinesU_congr_mul_premises_tight :
    (RefinesU 2 (.const 1) (.const 1) ∧ ¬ RefinesU 2 (.mul (.const 1) (.const 1)) (.mul (.const 0) (.const 1))) ∧
    (RefinesU 2 (.const 1) (.const 1) ∧ ¬ RefinesU 2 (.mul (.const 1) (.const 1)) (.mul (.const 1) (.const 0)))
```

#### `Toy.UB.refinesU_congr_eq_premises_tight` (`lean/ToyUB/Tightness.lean`)

```lean
-- lean/ToyUB/Tightness.lean:45-47
theorem refinesU_congr_eq_premises_tight :
    (RefinesU 2 (.const 0) (.const 0) ∧ ¬ RefinesU 2 (.eq (.const 1) (.const 0)) (.eq (.const 0) (.const 0))) ∧
    (RefinesU 2 (.const 0) (.const 0) ∧ ¬ RefinesU 2 (.eq (.const 0) (.const 1)) (.eq (.const 0) (.const 0)))
```

#### `Toy.UB.refinesU_congr_ite_premises_tight` (`lean/ToyUB/Tightness.lean`)

```lean
-- lean/ToyUB/Tightness.lean:52-55
theorem refinesU_congr_ite_premises_tight :
    (RefinesU 2 (.const 1) (.const 1) ∧ RefinesU 2 (.const 0) (.const 0) ∧ ¬ RefinesU 2 (.ite (.const 1) (.const 1) (.const 0)) (.ite (.const 0) (.const 1) (.const 0))) ∧
    (RefinesU 2 (.const 1) (.const 1) ∧ RefinesU 2 (.const 0) (.const 0) ∧ ¬ RefinesU 2 (.ite (.const 1) (.const 1) (.const 0)) (.ite (.const 1) (.const 0) (.const 0))) ∧
    (RefinesU 2 (.const 0) (.const 0) ∧ RefinesU 2 (.const 0) (.const 0) ∧ ¬ RefinesU 2 (.ite (.const 0) (.const 0) (.const 1)) (.ite (.const 0) (.const 0) (.const 0)))
```

#### `Toy.UB.refinesU_congr_letE_premises_tight` (`lean/ToyUB/Tightness.lean`)

```lean
-- lean/ToyUB/Tightness.lean:60-62
theorem refinesU_congr_letE_premises_tight :
    (RefinesU 2 (.var 0) (.var 0) ∧ ¬ RefinesU 2 (.letE 0 (.const 1) (.var 0)) (.letE 0 (.const 0) (.var 0))) ∧
    (RefinesU 2 (.const 0) (.const 0) ∧ ¬ RefinesU 2 (.letE 0 (.const 0) (.const 1)) (.letE 0 (.const 0) (.const 0)))
```

#### `Toy.UB.refinesU_congr_freeze_premises_tight` (`lean/ToyUB/Tightness.lean`)

```lean
-- lean/ToyUB/Tightness.lean:67-68
theorem refinesU_congr_freeze_premises_tight :
    (¬ RefinesU 2 (.freeze (.const 1)) (.freeze (.const 0)))
```

#### `Toy.UB.refinesP_congr_add_premises_tight` (`lean/ToyUB/Tightness.lean`)

```lean
-- lean/ToyUB/Tightness.lean:73-75
theorem refinesP_congr_add_premises_tight :
    (RefinesP 2 (.const 0) (.const 0) ∧ ¬ RefinesP 2 (.add (.const 1) (.const 0)) (.add (.const 0) (.const 0))) ∧
    (RefinesP 2 (.const 0) (.const 0) ∧ ¬ RefinesP 2 (.add (.const 0) (.const 1)) (.add (.const 0) (.const 0)))
```

#### `Toy.UB.refinesP_congr_mul_premises_tight` (`lean/ToyUB/Tightness.lean`)

```lean
-- lean/ToyUB/Tightness.lean:80-82
theorem refinesP_congr_mul_premises_tight :
    (RefinesP 2 (.const 1) (.const 1) ∧ ¬ RefinesP 2 (.mul (.const 1) (.const 1)) (.mul (.const 0) (.const 1))) ∧
    (RefinesP 2 (.const 1) (.const 1) ∧ ¬ RefinesP 2 (.mul (.const 1) (.const 1)) (.mul (.const 1) (.const 0)))
```

#### `Toy.UB.refinesP_congr_eq_premises_tight` (`lean/ToyUB/Tightness.lean`)

```lean
-- lean/ToyUB/Tightness.lean:87-89
theorem refinesP_congr_eq_premises_tight :
    (RefinesP 2 (.const 0) (.const 0) ∧ ¬ RefinesP 2 (.eq (.const 1) (.const 0)) (.eq (.const 0) (.const 0))) ∧
    (RefinesP 2 (.const 0) (.const 0) ∧ ¬ RefinesP 2 (.eq (.const 0) (.const 1)) (.eq (.const 0) (.const 0)))
```

#### `Toy.UB.refinesP_congr_ite_premises_tight` (`lean/ToyUB/Tightness.lean`)

```lean
-- lean/ToyUB/Tightness.lean:94-97
theorem refinesP_congr_ite_premises_tight :
    (RefinesP 2 (.const 1) (.const 1) ∧ RefinesP 2 (.const 0) (.const 0) ∧ ¬ RefinesP 2 (.ite (.const 1) (.const 1) (.const 0)) (.ite (.const 0) (.const 1) (.const 0))) ∧
    (RefinesP 2 (.const 1) (.const 1) ∧ RefinesP 2 (.const 0) (.const 0) ∧ ¬ RefinesP 2 (.ite (.const 1) (.const 1) (.const 0)) (.ite (.const 1) (.const 0) (.const 0))) ∧
    (RefinesP 2 (.const 0) (.const 0) ∧ RefinesP 2 (.const 0) (.const 0) ∧ ¬ RefinesP 2 (.ite (.const 0) (.const 0) (.const 1)) (.ite (.const 0) (.const 0) (.const 0)))
```

#### `Toy.UB.refinesP_congr_letE_premises_tight` (`lean/ToyUB/Tightness.lean`)

```lean
-- lean/ToyUB/Tightness.lean:102-104
theorem refinesP_congr_letE_premises_tight :
    (RefinesP 2 (.var 0) (.var 0) ∧ ¬ RefinesP 2 (.letE 0 (.const 1) (.var 0)) (.letE 0 (.const 0) (.var 0))) ∧
    (RefinesP 2 (.const 0) (.const 0) ∧ ¬ RefinesP 2 (.letE 0 (.const 0) (.const 1)) (.letE 0 (.const 0) (.const 0)))
```

#### `Toy.UB.refinesP_congr_freeze_premises_tight` (`lean/ToyUB/Tightness.lean`)

```lean
-- lean/ToyUB/Tightness.lean:109-110
theorem refinesP_congr_freeze_premises_tight :
    (¬ RefinesP 2 (.freeze (.const 1)) (.freeze (.const 0)))
```

#### `Toy.UB.nonvacuity_refinesU_congr` (`lean/ToyUB/NonVacuity.lean`)

```lean
-- lean/ToyUB/NonVacuity.lean:50-52
theorem nonvacuity_refinesU_congr :
    RefinesU 2 (.mul (.const 2) (.var 0)) (.add (.var 0) (.var 0)) ∧
    RefinesU 2 (.freeze (.var 1)) (.var 1) ∧ RefinesU 2 (.const 7) .ub
```

#### `Toy.UB.nonvacuity_refinesP_congr` (`lean/ToyUB/NonVacuity.lean`)

```lean
-- lean/ToyUB/NonVacuity.lean:58-60
theorem nonvacuity_refinesP_congr :
    RefinesP 2 (.mul (.const 2) (.var 0)) (.add (.var 0) (.var 0)) ∧
    RefinesP 2 (.freeze (.var 1)) (.var 1) ∧ RefinesP 2 (.const 7) .ub
```

#### `Toy.UB.semU_mono` (`lean/ToyUB/Monotone.lean`)

Monotonicity of the undef-model semantics in the environment (cited in the non-claims of result 3): if every input set of `ρ'` is a subset of the corresponding input set of `ρ`, the outcomes in `ρ'` refine those in `ρ`.

```lean
-- lean/ToyUB/Monotone.lean:109-111
theorem semU_mono (w : Nat) (e : Expr) :
    ∀ ρ' ρ : Var → USet w, (∀ y, USet.Sub (ρ' y) (ρ y)) →
      OutRef USet.Sub (semU w ρ' e) (semU w ρ e)
```

#### `Toy.UB.semP_mono` (`lean/ToyUB/Monotone.lean`)

Monotonicity of the poison(+freeze)-model semantics in the environment (cited in the non-claims of result 3): if every input of `ρ'` refines the corresponding input of `ρ`, the outcomes in `ρ'` refine those in `ρ`.

```lean
-- lean/ToyUB/Monotone.lean:250-252
theorem semP_mono (w : Nat) (e : Expr) :
    ∀ ρ' ρ : Var → PVal w, (∀ y, PVal.Refines (ρ' y) (ρ y)) →
      OutRef PVal.Refines (semP w ρ' e) (semP w ρ e)
```

#### `Toy.UB.undef_obsRefines_not_congruence_letE_needs_width` (`lean/ToyUB/Tightness.lean`)

```lean
-- lean/ToyUB/Tightness.lean:154-157
theorem undef_obsRefines_not_congruence_letE_needs_width :
    ¬ (ObsRefinesU 0 (.var 0) (.freeze (.var 0)) ∧
        ¬ ObsRefinesU 0 (.letE 1 (.var 0) (.add (.var 1) (.var 1)))
            (.letE 1 (.freeze (.var 0)) (.add (.var 1) (.var 1))))
```

#### `Toy.UB.nonvacuity_undef_obsRefines_not_congruence_letE` (`lean/ToyUB/NonVacuity.lean`)

```lean
-- lean/ToyUB/NonVacuity.lean:68-71
theorem nonvacuity_undef_obsRefines_not_congruence_letE :
    ObsRefinesU 2 (.var 0) (.freeze (.var 0)) ∧
    ¬ ObsRefinesU 2 (.letE 1 (.var 0) (.add (.var 1) (.var 1)))
        (.letE 1 (.freeze (.var 0)) (.add (.var 1) (.var 1)))
```

#### `Toy.UB.nonvacuity_width_two` (`lean/ToyUB/NonVacuity.lean`)

```lean
-- lean/ToyUB/NonVacuity.lean:65
theorem nonvacuity_width_two : 1 ≤ 2
```

#### `Toy.UB.undef_obsRefines_letE_width_zero` (`lean/ToyUB/Refinement.lean`)

```lean
-- lean/ToyUB/Refinement.lean:216-218
theorem undef_obsRefines_letE_width_zero (x y : Var) :
    ObsRefinesU 0 (.letE y (.var x) (.add (.var y) (.var y)))
      (.letE y (.freeze (.var x)) (.add (.var y) (.var y)))
```

#### `Toy.UB.nonvacuity_undef_rewrite_add_self_to_two_mul_sound` (`lean/ToyUB/NonVacuity.lean`)

```lean
-- lean/ToyUB/NonVacuity.lean:86-88
theorem nonvacuity_undef_rewrite_add_self_to_two_mul_sound :
    RefinesU 3 (.mul (.const 2) (.ite (.var 0) (.var 1) (.freeze (.var 1))))
      (.add (.ite (.var 0) (.var 1) (.freeze (.var 1))) (.ite (.var 0) (.var 1) (.freeze (.var 1))))
```

#### `Toy.UB.nonvacuity_poison_rewrite_add_self_to_two_mul_sound` (`lean/ToyUB/NonVacuity.lean`)

```lean
-- lean/ToyUB/NonVacuity.lean:93-94
theorem nonvacuity_poison_rewrite_add_self_to_two_mul_sound :
    RefinesP 3 (.mul (.const 2) (.freeze (.var 0))) (.add (.freeze (.var 0)) (.freeze (.var 0)))
```

#### `Toy.UB.undef_rewrite_two_mul_to_add_self_unsound_needs_width` (`lean/ToyUB/Tightness.lean`)

```lean
-- lean/ToyUB/Tightness.lean:161-162
theorem undef_rewrite_two_mul_to_add_self_unsound_needs_width :
    ¬ ¬ RefinesU 0 (.add (.var 0) (.var 0)) (.mul (.const 2) (.var 0))
```

#### `Toy.UB.nonvacuity_undef_rewrite_two_mul_to_add_self_unsound` (`lean/ToyUB/NonVacuity.lean`)

```lean
-- lean/ToyUB/NonVacuity.lean:75-76
theorem nonvacuity_undef_rewrite_two_mul_to_add_self_unsound :
    ¬ RefinesU 2 (.add (.var 0) (.var 0)) (.mul (.const 2) (.var 0))
```

#### `Toy.UB.undef_rewrite_two_mul_to_add_self_sound_width_zero` (`lean/ToyUB/Duplication.lean`)

```lean
-- lean/ToyUB/Duplication.lean:84-85
theorem undef_rewrite_two_mul_to_add_self_sound_width_zero (x : Var) :
    RefinesU 0 (.add (.var x) (.var x)) (.mul (.const 2) (.var x))
```

#### `Toy.UB.undef_rewrite_two_mul_to_let_freeze_add_self_sound` (`lean/ToyUB/Duplication.lean`)

```lean
-- lean/ToyUB/Duplication.lean:248-249
theorem undef_rewrite_two_mul_to_let_freeze_add_self_sound (w : Nat) (e : Expr) (a : Var) :
    RefinesU w (.letE a (.freeze e) (.add (.var a) (.var a))) (.mul (.const 2) e)
```

#### `Toy.UB.undef_rewrite_two_mul_to_add_self_sound_at_singleton` (`lean/ToyUB/Duplication.lean`)

```lean
-- lean/ToyUB/Duplication.lean:330-332
theorem undef_rewrite_two_mul_to_add_self_sound_at_singleton (w : Nat) (x : Var)
    (ρ : Var → USet w) (v : BitVec w) (hx : ρ x = USet.single v) :
    OutRef USet.Sub (semU w ρ (.add (.var x) (.var x))) (semU w ρ (.mul (.const 2) (.var x)))
```

#### `Toy.UB.semP_freezeFree_singleton` (`lean/ToyUB/Duplication.lean`)

Freeze-free programs are deterministic in the poison(+freeze) model (cited in the hypothesis ledger of result 7): in every environment they have exactly one outcome.

```lean
-- lean/ToyUB/Duplication.lean:124-125
theorem semP_freezeFree_singleton (w : Nat) (e : Expr) (he : e.FreezeFree = true) :
    ∀ ρ : Var → PVal w, ∃ o, semP w ρ e = [o]
```

#### `Toy.UB.poison_rewrite_two_mul_to_add_self_needs_freezeFree` (`lean/ToyUB/Tightness.lean`)

```lean
-- lean/ToyUB/Tightness.lean:220-222
theorem poison_rewrite_two_mul_to_add_self_needs_freezeFree :
    (Expr.freeze (.var 0)).FreezeFree = false ∧
    ¬ RefinesP 2 (.add (.freeze (.var 0)) (.freeze (.var 0))) (.mul (.const 2) (.freeze (.var 0)))
```

#### `Toy.UB.nonvacuity_freezeFree` (`lean/ToyUB/NonVacuity.lean`)

```lean
-- lean/ToyUB/NonVacuity.lean:99-100
theorem nonvacuity_freezeFree :
    (Expr.ite (.var 0) (.add (.var 0) (.var 1)) .ub).FreezeFree = true
```

#### `Toy.UB.poisonFreeze_rewrite_two_mul_to_add_self_unsound_needs_width` (`lean/ToyUB/Tightness.lean`)

```lean
-- lean/ToyUB/Tightness.lean:167-169
theorem poisonFreeze_rewrite_two_mul_to_add_self_unsound_needs_width :
    ¬ ¬ RefinesP 0 (.add (.freeze (.var 0)) (.freeze (.var 0)))
        (.mul (.const 2) (.freeze (.var 0)))
```

#### `Toy.UB.nonvacuity_poisonFreeze_rewrite_two_mul_to_add_self_unsound` (`lean/ToyUB/NonVacuity.lean`)

```lean
-- lean/ToyUB/NonVacuity.lean:80-81
theorem nonvacuity_poisonFreeze_rewrite_two_mul_to_add_self_unsound :
    ¬ RefinesP 2 (.add (.freeze (.var 0)) (.freeze (.var 0))) (.mul (.const 2) (.freeze (.var 0)))
```

#### `Toy.UB.poisonFreeze_rewrite_two_mul_to_add_self_sound_width_zero` (`lean/ToyUB/Duplication.lean`)

```lean
-- lean/ToyUB/Duplication.lean:234-236
theorem poisonFreeze_rewrite_two_mul_to_add_self_sound_width_zero (x : Var) :
    RefinesP 0 (.add (.freeze (.var x)) (.freeze (.var x)))
      (.mul (.const 2) (.freeze (.var x)))
```

#### `Toy.UB.poisonFreeze_rewrite_two_mul_to_let_freeze_add_self_sound` (`lean/ToyUB/Duplication.lean`)

```lean
-- lean/ToyUB/Duplication.lean:293-294
theorem poisonFreeze_rewrite_two_mul_to_let_freeze_add_self_sound (w : Nat) (e : Expr)
    (a : Var) : RefinesP w (.letE a (.freeze e) (.add (.var a) (.var a))) (.mul (.const 2) e)
```

#### `Toy.UB.poisonFreeze_rewrite_two_mul_freeze_sound_at_int` (`lean/ToyUB/Duplication.lean`)

```lean
-- lean/ToyUB/Duplication.lean:350-353
theorem poisonFreeze_rewrite_two_mul_freeze_sound_at_int (w : Nat) (x : Var)
    (ρ : Var → PVal w) (v : BitVec w) (hx : ρ x = .int v) :
    OutRef PVal.Refines (semP w ρ (.add (.freeze (.var x)) (.freeze (.var x))))
      (semP w ρ (.mul (.const 2) (.freeze (.var x))))
```

#### `Toy.UB.nonvacuity_poison_gvn_sound` (`lean/ToyUB/NonVacuity.lean`)

```lean
-- lean/ToyUB/NonVacuity.lean:113-116
theorem nonvacuity_poison_gvn_sound :
    RefinesP 2 (.ite (.eq (.var 0) (.var 1)) (.letE 1 (.var 0) (.add (.var 1) (.freeze (.var 1))))
        (.var 1))
      (.ite (.eq (.var 0) (.var 1)) (.add (.var 1) (.freeze (.var 1))) (.var 1))
```

#### `Toy.UB.semP_letE_var_var` (`lean/ToyUB/GVN.lean`)

```lean
-- lean/ToyUB/GVN.lean:41-42
theorem semP_letE_var_var (w : Nat) (ρ : Var → PVal w) (x y : Var) :
    semP w ρ (.letE y (.var x) (.var y)) = semP w ρ (.var x)
```

#### `Toy.UB.poisonFreeze_gvn_after_freezing_condition_unsound` (`lean/ToyUB/GVN.lean`)

```lean
-- lean/ToyUB/GVN.lean:181-183
theorem poisonFreeze_gvn_after_freezing_condition_unsound (w : Nat) (hw : 1 ≤ w) :
    ¬ RefinesP w (.ite (.freeze (.eq (.var 0) (.var 1))) (.letE 1 (.var 0) (.var 1)) (.const 0))
        (.ite (.freeze (.eq (.var 0) (.var 1))) (.var 1) (.const 0))
```

#### `Toy.UB.undef_gvn_var_branch_distinct_vars_unsound_needs_width` (`lean/ToyUB/Tightness.lean`)

```lean
-- lean/ToyUB/Tightness.lean:174-177
theorem undef_gvn_var_branch_distinct_vars_unsound_needs_width :
    (0 : Var) ≠ 1 ∧
    ¬ ¬ RefinesU 0 (.ite (.eq (.var 0) (.var 1)) (.letE 1 (.var 0) (.var 1)) (.const 0))
        (.ite (.eq (.var 0) (.var 1)) (.var 1) (.const 0))
```

#### `Toy.UB.undef_gvn_var_branch_distinct_vars_unsound_needs_distinct` (`lean/ToyUB/Tightness.lean`)

```lean
-- lean/ToyUB/Tightness.lean:182-185
theorem undef_gvn_var_branch_distinct_vars_unsound_needs_distinct :
    1 ≤ 2 ∧
    ¬ ¬ RefinesU 2 (.ite (.eq (.var 0) (.var 0)) (.letE 0 (.var 0) (.var 0)) (.const 0))
        (.ite (.eq (.var 0) (.var 0)) (.var 0) (.const 0))
```

#### `Toy.UB.nonvacuity_undef_gvn_instance` (`lean/ToyUB/NonVacuity.lean`)

```lean
-- lean/ToyUB/NonVacuity.lean:106-108
theorem nonvacuity_undef_gvn_instance :
    ¬ RefinesU 2 (.ite (.eq (.var 0) (.var 1)) (.letE 1 (.var 0) (.var 1)) (.const 0))
        (.ite (.eq (.var 0) (.var 1)) (.var 1) (.const 0))
```

#### `Toy.UB.nonvacuity_undef_gvn` (`lean/ToyUB/NonVacuity.lean`)

```lean
-- lean/ToyUB/NonVacuity.lean:103
theorem nonvacuity_undef_gvn : 1 ≤ 2 ∧ (0 : Var) ≠ 1
```

#### `Toy.UB.undef_gvn_sound_width_zero` (`lean/ToyUB/GVN.lean`)

```lean
-- lean/ToyUB/GVN.lean:136-138
theorem undef_gvn_sound_width_zero (x y : Var) :
    RefinesU 0 (.ite (.eq (.var x) (.var y)) (.letE y (.var x) (.var y)) (.const 0))
      (.ite (.eq (.var x) (.var y)) (.var y) (.const 0))
```

#### `Toy.UB.undef_gvn_sound_of_same_var` (`lean/ToyUB/GVN.lean`)

```lean
-- lean/ToyUB/GVN.lean:154-156
theorem undef_gvn_sound_of_same_var (w : Nat) (x : Var) :
    RefinesU w (.ite (.eq (.var x) (.var x)) (.letE x (.var x) (.var x)) (.const 0))
      (.ite (.eq (.var x) (.var x)) (.var x) (.const 0))
```

#### `Toy.UB.undef_gvn_sound_examples_closed_or_x_branch` (`lean/ToyUB/GVN.lean`)

```lean
-- lean/ToyUB/GVN.lean:166-170
theorem undef_gvn_sound_examples_closed_or_x_branch :
    RefinesU 2 (.ite (.eq (.var 0) (.var 1)) (.letE 1 (.var 0) (.const 0)) (.const 0))
      (.ite (.eq (.var 0) (.var 1)) (.const 0) (.const 0)) ∧
    RefinesU 2 (.ite (.eq (.var 0) (.var 1)) (.letE 1 (.var 0) (.var 0)) (.const 0))
      (.ite (.eq (.var 0) (.var 1)) (.var 0) (.const 0))
```

#### `Toy.UB.undef_gvn_with_frozen_operand_sound` (`lean/ToyUB/GVN.lean`)

```lean
-- lean/ToyUB/GVN.lean:221-223
theorem undef_gvn_with_frozen_operand_sound (w : Nat) :
    RefinesU w (.letE 2 (.freeze (.var 0)) (.ite (.eq (.var 2) (.var 1)) (.var 2) (.const 0)))
      (.ite (.eq (.var 0) (.var 1)) (.var 1) (.const 0))
```

#### `Toy.UB.poison_unswitch_without_freeze_distinct_vars_unsound_needs_distinct` (`lean/ToyUB/Tightness.lean`)

```lean
-- lean/ToyUB/Tightness.lean:190-193
theorem poison_unswitch_without_freeze_distinct_vars_unsound_needs_distinct :
    ¬ ¬ RefinesP 2
        (.ite (.var 2) (.ite (.var 2) (.const 1) (.const 0)) (.ite (.var 2) (.const 2) (.const 0)))
        (.ite (.var 2) (.ite (.var 2) (.const 1) (.const 2)) (.const 0))
```

#### `Toy.UB.nonvacuity_poison_unswitch_instance` (`lean/ToyUB/NonVacuity.lean`)

```lean
-- lean/ToyUB/NonVacuity.lean:124-127
theorem nonvacuity_poison_unswitch_instance :
    ¬ RefinesP 2
        (.ite (.var 3) (.ite (.var 2) (.var 3) (.const 7)) (.ite (.var 2) (.add (.var 2) (.var 3)) (.const 7)))
        (.ite (.var 2) (.ite (.var 3) (.var 3) (.add (.var 2) (.var 3))) (.const 7))
```

#### `Toy.UB.nonvacuity_poison_unswitch` (`lean/ToyUB/NonVacuity.lean`)

```lean
-- lean/ToyUB/NonVacuity.lean:120
theorem nonvacuity_poison_unswitch : (2 : Var) ≠ 3
```

#### `Toy.UB.poison_unswitch_without_freeze_sound_of_same_var` (`lean/ToyUB/Unswitch.lean`)

```lean
-- lean/ToyUB/Unswitch.lean:93-95
theorem poison_unswitch_without_freeze_sound_of_same_var (w : Nat) (c : Var) (a b e : Expr) :
    RefinesP w (.ite (.var c) (.ite (.var c) a e) (.ite (.var c) b e))
      (.ite (.var c) (.ite (.var c) a b) e)
```

#### `Toy.UB.undef_unswitch_without_freeze_needs_ubFree` (`lean/ToyUB/Unswitch.lean`)

```lean
-- lean/ToyUB/Unswitch.lean:171-174
theorem undef_unswitch_without_freeze_needs_ubFree :
    ¬ UBFreeU 2 .ub ∧
    ¬ RefinesU 2 (.ite .ub (.ite (.const 0) (.const 0) (.const 0)) (.ite (.const 0) (.const 0) (.const 0)))
      (.ite (.const 0) (.ite .ub (.const 0) (.const 0)) (.const 0))
```

#### `Toy.UB.nonvacuity_undef_unswitch_of_ubFree` (`lean/ToyUB/NonVacuity.lean`)

```lean
-- lean/ToyUB/NonVacuity.lean:133-141
theorem nonvacuity_undef_unswitch_of_ubFree :
    UBFreeU 2 (.ite (.var 3) (.const 1) (.const 0)) ∧
    RefinesU 2
      (.ite (.ite (.var 3) (.const 1) (.const 0))
        (.ite (.eq (.var 2) (.var 4)) (.var 3) (.freeze (.var 2)))
        (.ite (.eq (.var 2) (.var 4)) (.add (.var 2) (.var 3)) (.freeze (.var 2))))
      (.ite (.eq (.var 2) (.var 4))
        (.ite (.ite (.var 3) (.const 1) (.const 0)) (.var 3) (.add (.var 2) (.var 3)))
        (.freeze (.var 2)))
```

#### `Toy.UB.nonvacuity_undef_unswitch` (`lean/ToyUB/NonVacuity.lean`)

```lean
-- lean/ToyUB/NonVacuity.lean:164-167
theorem nonvacuity_undef_unswitch :
    RefinesU 2 (.ite (.var 3) (.ite (.var 2) (.var 3) (.freeze (.var 2)))
        (.ite (.var 2) (.add (.var 2) (.var 3)) (.freeze (.var 2))))
      (.ite (.var 2) (.ite (.var 3) (.var 3) (.add (.var 2) (.var 3))) (.freeze (.var 2)))
```

#### `Toy.UB.undef_unswitch_vars_outRef_all_envs` (`lean/ToyUB/Unswitch.lean`)

```lean
-- lean/ToyUB/Unswitch.lean:187-191
theorem undef_unswitch_vars_outRef_all_envs (w : Nat) (c d : Var) (a b e : Expr)
    (ρ : Var → USet w) :
    OutRef USet.Sub
      (semU w ρ (.ite (.var d) (.ite (.var c) a e) (.ite (.var c) b e)))
      (semU w ρ (.ite (.var c) (.ite (.var d) a b) e))
```

#### `Toy.UB.uEmptyD` (`lean/ToyUB/Unswitch.lean`)

The width-2 environment used by the next theorem: variable `1` is bound to the empty set and every other variable to the singleton `{0}`, so it does not satisfy `UInhabited`.

```lean
def uEmptyD : Var → USet 2 := fun v => if v = 1 then (fun _ => false) else USet.single 0#2
```

#### `Toy.UB.undef_unswitch_empty_input_target_has_no_outcomes` (`lean/ToyUB/Unswitch.lean`)

With `c` = variable `0` ↦ `{0}` and `d` = variable `1` ↦ the empty set (environment `uEmptyD`), the source `if c then (if d then 2 else 3) else 1` returns `1`, the unswitched target has no outcome, and `OutRef` accepts the pair.

```lean
-- lean/ToyUB/Unswitch.lean:226-235
theorem undef_unswitch_empty_input_target_has_no_outcomes :
    ¬ UInhabited uEmptyD ∧
    semU 2 uEmptyD
      (.ite (.var 1) (.ite (.var 0) (.const 2) (.const 1)) (.ite (.var 0) (.const 3) (.const 1))) = [] ∧
    (∃ o ∈ semU 2 uEmptyD (.ite (.var 0) (.ite (.var 1) (.const 2) (.const 3)) (.const 1)),
      Outcome.LeVal USet.Sub (.val (USet.single 1#2)) o) ∧
    OutRef USet.Sub
      (semU 2 uEmptyD
        (.ite (.var 1) (.ite (.var 0) (.const 2) (.const 1)) (.ite (.var 0) (.const 3) (.const 1))))
      (semU 2 uEmptyD (.ite (.var 0) (.ite (.var 1) (.const 2) (.const 3)) (.const 1)))
```

#### `Toy.UB.ubFreeU_examples` (`lean/ToyUB/Unswitch.lean`)

```lean
-- lean/ToyUB/Unswitch.lean:66-67
theorem ubFreeU_examples :
    UBFreeU 2 (.var 0) ∧ UBFreeU 2 (.ite (.var 0) (.const 1) (.const 0)) ∧ ¬ UBFreeU 2 .ub
```

#### `Toy.UB.poisonFreeze_unswitch_with_freeze_needs_ubFree` (`lean/ToyUB/Unswitch.lean`)

```lean
-- lean/ToyUB/Unswitch.lean:427-432
theorem poisonFreeze_unswitch_with_freeze_needs_ubFree :
    (Expr.const 0).freeIn 4 = false ∧ ¬ UBFreeP 2 .ub ∧
    ¬ RefinesP 2
      (.letE 4 (.freeze .ub)
        (.ite (.var 4) (.ite (.const 0) (.const 0) (.const 0)) (.ite (.const 0) (.const 0) (.const 0))))
      (.ite (.const 0) (.ite .ub (.const 0) (.const 0)) (.const 0))
```

#### `Toy.UB.poisonFreeze_unswitch_with_freeze_needs_ubFree_branch` (`lean/ToyUB/Unswitch.lean`)

```lean
-- lean/ToyUB/Unswitch.lean:441-446
theorem poisonFreeze_unswitch_with_freeze_needs_ubFree_branch :
    (Expr.const 0).freeIn 4 = false ∧ ¬ UBFreeP 2 (.ite (.var 0) (.const 1) (.const 0)) ∧
    ¬ RefinesP 2
      (.letE 4 (.freeze (.ite (.var 0) (.const 1) (.const 0)))
        (.ite (.var 4) (.ite (.const 0) (.const 0) (.const 0)) (.ite (.const 0) (.const 0) (.const 0))))
      (.ite (.const 0) (.ite (.ite (.var 0) (.const 1) (.const 0)) (.const 0) (.const 0)) (.const 0))
```

#### `Toy.UB.poisonFreeze_unswitch_with_freeze_needs_t_not_free_in_cond` (`lean/ToyUB/Unswitch.lean`)

```lean
-- lean/ToyUB/Unswitch.lean:455-461
theorem poisonFreeze_unswitch_with_freeze_needs_t_not_free_in_cond :
    UBFreeP 2 (.var 3) ∧ (Expr.const 1).freeIn 2 = false ∧ (Expr.const 0).freeIn 2 = false ∧
    (Expr.var 2).freeIn 2 = true ∧
    ¬ RefinesP 2
      (.letE 2 (.freeze (.var 3))
        (.ite (.var 2) (.ite (.var 2) (.const 1) (.const 0)) (.ite (.var 2) (.const 0) (.const 0))))
      (.ite (.var 2) (.ite (.var 3) (.const 1) (.const 0)) (.const 0))
```

#### `Toy.UB.poisonFreeze_unswitch_with_freeze_needs_t_not_free_in_a` (`lean/ToyUB/Unswitch.lean`)

```lean
-- lean/ToyUB/Unswitch.lean:471-476
theorem poisonFreeze_unswitch_with_freeze_needs_t_not_free_in_a :
    UBFreeP 2 (.var 3) ∧ (Expr.var 2).freeIn 4 = false ∧ (Expr.const 0).freeIn 4 = false ∧
    ¬ RefinesP 2
      (.letE 4 (.freeze (.var 3))
        (.ite (.var 4) (.ite (.var 2) (.var 4) (.const 0)) (.ite (.var 2) (.const 0) (.const 0))))
      (.ite (.var 2) (.ite (.var 3) (.var 4) (.const 0)) (.const 0))
```

#### `Toy.UB.poisonFreeze_unswitch_with_freeze_needs_t_not_free_in_b` (`lean/ToyUB/Unswitch.lean`)

```lean
-- lean/ToyUB/Unswitch.lean:486-491
theorem poisonFreeze_unswitch_with_freeze_needs_t_not_free_in_b :
    UBFreeP 2 (.var 3) ∧ (Expr.var 2).freeIn 4 = false ∧ (Expr.const 0).freeIn 4 = false ∧
    ¬ RefinesP 2
      (.letE 4 (.freeze (.var 3))
        (.ite (.var 4) (.ite (.var 2) (.const 0) (.const 0)) (.ite (.var 2) (.var 4) (.const 0))))
      (.ite (.var 2) (.ite (.var 3) (.const 0) (.var 4)) (.const 0))
```

#### `Toy.UB.poisonFreeze_unswitch_with_freeze_needs_t_not_free_in_e` (`lean/ToyUB/Unswitch.lean`)

```lean
-- lean/ToyUB/Unswitch.lean:501-506
theorem poisonFreeze_unswitch_with_freeze_needs_t_not_free_in_e :
    UBFreeP 2 (.var 3) ∧ (Expr.var 2).freeIn 4 = false ∧ (Expr.const 0).freeIn 4 = false ∧
    ¬ RefinesP 2
      (.letE 4 (.freeze (.var 3))
        (.ite (.var 4) (.ite (.var 2) (.const 0) (.var 4)) (.ite (.var 2) (.const 0) (.var 4))))
      (.ite (.var 2) (.ite (.var 3) (.const 0) (.const 0)) (.var 4))
```

#### `Toy.UB.nonvacuity_poisonFreeze_unswitch_of_ubFree` (`lean/ToyUB/NonVacuity.lean`)

```lean
-- lean/ToyUB/NonVacuity.lean:148-157
theorem nonvacuity_poisonFreeze_unswitch_of_ubFree :
    UBFreeP 2 (.eq (.var 3) (.var 5)) ∧ (Expr.eq (.var 0) (.var 1)).freeIn 4 = false ∧
    (Expr.var 3).freeIn 4 = false ∧ (Expr.add (.var 2) (.var 3)).freeIn 4 = false ∧
    (Expr.freeze (.var 2)).freeIn 4 = false ∧
    RefinesP 2
      (.letE 4 (.freeze (.eq (.var 3) (.var 5)))
        (.ite (.var 4) (.ite (.eq (.var 0) (.var 1)) (.var 3) (.freeze (.var 2)))
          (.ite (.eq (.var 0) (.var 1)) (.add (.var 2) (.var 3)) (.freeze (.var 2)))))
      (.ite (.eq (.var 0) (.var 1)) (.ite (.eq (.var 3) (.var 5)) (.var 3) (.add (.var 2) (.var 3)))
        (.freeze (.var 2)))
```

#### `Toy.UB.nonvacuity_poisonFreeze_unswitch` (`lean/ToyUB/NonVacuity.lean`)

```lean
-- lean/ToyUB/NonVacuity.lean:173-175
theorem nonvacuity_poisonFreeze_unswitch :
    (4 : Var) ≠ 2 ∧ (Expr.var 3).freeIn 4 = false ∧ (Expr.add (.var 2) (.var 3)).freeIn 4 = false ∧
    (Expr.freeze (.var 2)).freeIn 4 = false
```

#### `Toy.UB.ubFreeP_examples` (`lean/ToyUB/Unswitch.lean`)

```lean
-- lean/ToyUB/Unswitch.lean:58-60
theorem ubFreeP_examples :
    UBFreeP 2 (.var 0) ∧ UBFreeP 2 (.eq (.var 0) (.var 1)) ∧ ¬ UBFreeP 2 .ub ∧
    ¬ UBFreeP 2 (.ite (.var 0) (.const 1) (.const 0))
```

#### `Toy.UB.ubFreeP_eq_var` (`lean/ToyUB/Unswitch.lean`)

```lean
-- lean/ToyUB/Unswitch.lean:47
theorem ubFreeP_eq_var (w : Nat) (x y : Var) : UBFreeP w (.eq (.var x) (.var y))
```

#### `Toy.UB.poisonFreeze_freeze_eq_self_needs_no_poison` (`lean/ToyUB/Tightness.lean`)

```lean
-- lean/ToyUB/Tightness.lean:227-229
theorem poisonFreeze_freeze_eq_self_needs_no_poison :
    Outcome.val PVal.poison ∈ semP 2 (fun _ => .poison) (.var 0) ∧
    semP 2 (fun _ => .poison) (.freeze (.var 0)) ≠ semP 2 (fun _ => .poison) (.var 0)
```

#### `Toy.UB.poisonFreeze_remove_freeze_needs_no_poison` (`lean/ToyUB/Tightness.lean`)

```lean
-- lean/ToyUB/Tightness.lean:234-236
theorem poisonFreeze_remove_freeze_needs_no_poison :
    ¬ (∀ ρ : Var → PVal 2, Outcome.val PVal.poison ∉ semP 2 ρ (.var 0)) ∧
    ¬ RefinesP 2 (.var 0) (.freeze (.var 0))
```

#### `Toy.UB.nonvacuity_freeze_eq_self` (`lean/ToyUB/NonVacuity.lean`)

```lean
-- lean/ToyUB/NonVacuity.lean:179-180
theorem nonvacuity_freeze_eq_self :
    Outcome.val PVal.poison ∉ semP 2 (fun _ => .int 1#2) (.add (.var 0) (.const 1))
```

#### `Toy.UB.nonvacuity_remove_redundant_freeze` (`lean/ToyUB/NonVacuity.lean`)

```lean
-- lean/ToyUB/NonVacuity.lean:216-220
theorem nonvacuity_remove_redundant_freeze :
    RefinesP 2 (.freeze (.var 0)) (.freeze (.freeze (.var 0))) ∧
    RefinesU 2 (.freeze (.var 0)) (.freeze (.freeze (.var 0))) ∧
    (∀ ρ : Var → PVal 2,
      Outcome.val PVal.poison ∉ semP 2 ρ (.add (.freeze (.var 0)) (.const 1)))
```

#### `Toy.UB.nonvacuity_insert_freeze` (`lean/ToyUB/NonVacuity.lean`)

```lean
-- lean/ToyUB/NonVacuity.lean:184-186
theorem nonvacuity_insert_freeze :
    RefinesP 2 (.freeze (.ite (.var 0) (.var 1) .ub)) (.ite (.var 0) (.var 1) .ub) ∧
    RefinesU 2 (.freeze (.ite (.var 0) (.var 1) .ub)) (.ite (.var 0) (.var 1) .ub)
```

#### `Toy.UB.undef_remove_freeze_unsound_needs_width` (`lean/ToyUB/Tightness.lean`)

```lean
-- lean/ToyUB/Tightness.lean:197-198
theorem undef_remove_freeze_unsound_needs_width :
    ¬ ¬ RefinesU 0 (.var 0) (.freeze (.var 0))
```

#### `Toy.UB.nonvacuity_remove_freeze_unsound` (`lean/ToyUB/NonVacuity.lean`)

```lean
-- lean/ToyUB/NonVacuity.lean:232-233
theorem nonvacuity_remove_freeze_unsound :
    ¬ RefinesP 2 (.var 0) (.freeze (.var 0)) ∧ ¬ RefinesU 2 (.var 0) (.freeze (.var 0))
```

#### `Toy.UB.undef_remove_freeze_sound_width_zero` (`lean/ToyUB/Freeze.lean`)

```lean
-- lean/ToyUB/Freeze.lean:228-229
theorem undef_remove_freeze_sound_width_zero (x : Var) :
    RefinesU 0 (.var x) (.freeze (.var x))
```

#### `Toy.UB.poisonFreeze_freeze_add_freeze_can_be_odd_needs_width` (`lean/ToyUB/Tightness.lean`)

```lean
-- lean/ToyUB/Tightness.lean:203-206
theorem poisonFreeze_freeze_add_freeze_can_be_odd_needs_width :
    ¬ ∃ ρ : Var → PVal 0, ∃ v : BitVec 0,
        Outcome.val (PVal.int v) ∈ semP 0 ρ (.add (.freeze (.var 0)) (.freeze (.var 0))) ∧
        v.toNat % 2 = 1
```

#### `Toy.UB.nonvacuity_let_freeze_mem` (`lean/ToyUB/NonVacuity.lean`)

```lean
-- lean/ToyUB/NonVacuity.lean:239-243
theorem nonvacuity_let_freeze_mem :
    Outcome.val (PVal.int 2#2) ∈ semP 2 ρP (.letE 1 (.freeze (.var 0)) (.add (.var 1) (.var 1))) ∧
    (∃ ρ : Var → PVal 2, ∃ v : BitVec 2,
      Outcome.val (PVal.int v) ∈ semP 2 ρ (.add (.freeze (.var 0)) (.freeze (.var 0))) ∧
      v.toNat % 2 = 1)
```

#### `Toy.UB.poisonFreeze_duplicate_freeze_unsound_needs_width` (`lean/ToyUB/Tightness.lean`)

```lean
-- lean/ToyUB/Tightness.lean:212-214
theorem poisonFreeze_duplicate_freeze_unsound_needs_width :
    ¬ ¬ RefinesP 0 (.add (.freeze (.var 0)) (.freeze (.var 0)))
        (.letE 1 (.freeze (.var 0)) (.add (.var 1) (.var 1)))
```

#### `Toy.UB.nonvacuity_duplicate_freeze_unsound` (`lean/ToyUB/NonVacuity.lean`)

```lean
-- lean/ToyUB/NonVacuity.lean:247-249
theorem nonvacuity_duplicate_freeze_unsound :
    ¬ RefinesP 2 (.add (.freeze (.var 0)) (.freeze (.var 0)))
        (.letE 1 (.freeze (.var 0)) (.add (.var 1) (.var 1)))
```

#### `Toy.UB.poisonFreeze_duplicate_freeze_sound_width_zero` (`lean/ToyUB/Freeze.lean`)

```lean
-- lean/ToyUB/Freeze.lean:145-147
theorem poisonFreeze_duplicate_freeze_sound_width_zero (x a : Var) :
    RefinesP 0 (.add (.freeze (.var x)) (.freeze (.var x)))
      (.letE a (.freeze (.var x)) (.add (.var a) (.var a)))
```

#### `Toy.UB.poisonFreeze_duplicate_freeze_sound_at_int` (`lean/ToyUB/Freeze.lean`)

```lean
-- lean/ToyUB/Freeze.lean:380-383
theorem poisonFreeze_duplicate_freeze_sound_at_int (w : Nat) (x a : Var) (ρ : Var → PVal w)
    (v : BitVec w) (hx : ρ x = .int v) :
    OutRef PVal.Refines (semP w ρ (.add (.freeze (.var x)) (.freeze (.var x))))
      (semP w ρ (.letE a (.freeze (.var x)) (.add (.var a) (.var a))))
```

#### `Toy.UB.poisonFreeze_duplicate_freeze_of_nonpoison_compound_unsound` (`lean/ToyUB/Tightness.lean`)

```lean
-- lean/ToyUB/Tightness.lean:243-246
theorem poisonFreeze_duplicate_freeze_of_nonpoison_compound_unsound :
    (∀ ρ : Var → PVal 2, Outcome.val PVal.poison ∉ semP 2 ρ (.freeze (.var 1))) ∧
    ¬ RefinesP 2 (.add (.freeze (.freeze (.var 1))) (.freeze (.freeze (.var 1))))
        (.letE 5 (.freeze (.freeze (.var 1))) (.add (.var 5) (.var 5)))
```

#### `Toy.UB.nonvacuity_merge_freeze` (`lean/ToyUB/NonVacuity.lean`)

```lean
-- lean/ToyUB/NonVacuity.lean:190-192
theorem nonvacuity_merge_freeze :
    RefinesP 2 (.letE 5 (.freeze (.freeze (.var 0))) (.add (.var 5) (.var 5)))
      (.add (.freeze (.freeze (.var 0))) (.freeze (.freeze (.var 0))))
```

#### `Toy.UB.poisonFreeze_partial_merge_freeze_unsound` (`lean/ToyUB/Freeze.lean`)

```lean
-- lean/ToyUB/Freeze.lean:331-334
theorem poisonFreeze_partial_merge_freeze_unsound (w : Nat) (hw : 1 ≤ w) :
    ¬ RefinesP w
        (.letE 1 (.freeze (.var 0)) (.letE 2 (.freeze (.var 0)) (.eq (.var 1) (.var 2))))
        (.letE 1 (.freeze (.var 0)) (.letE 2 (.freeze (.var 0)) (.eq (.var 2) (.var 2))))
```

#### `Toy.UB.nonvacuity_poison_refines_eagerUninit_live` (`lean/ToyUB/NonVacuity.lean`)

```lean
-- lean/ToyUB/NonVacuity.lean:255-260
theorem nonvacuity_poison_refines_eagerUninit_live :
    semE 2 (fun _ => none) (.letE 1 (.var 0) (.const 0)) = [.ub] ∧
    semP 2 (toPoisonEnv fun _ => none) (.letE 1 (.var 0) (.const 0)) = [.val (.int 0#2)] ∧
    OutRef (fun a b => a = b)
      (semP 2 (toPoisonEnv fun _ => none) (.letE 1 (.var 0) (.const 0)))
      ((semE 2 (fun _ => none) (.letE 1 (.var 0) (.const 0))).map Outcome.toP)
```

#### `Toy.UB.nonvacuity_poison_refines_eagerUninit` (`lean/ToyUB/NonVacuity.lean`)

```lean
-- lean/ToyUB/NonVacuity.lean:197-201
theorem nonvacuity_poison_refines_eagerUninit :
    OutRef PVal.Refines
      (semP 2 (toPoisonEnv fun v => if v = 0 then some 1#2 else none) (.ite (.var 0) (.const 3) (.var 1)))
      ((semE 2 (fun v => if v = 0 then some 1#2 else none) (.ite (.var 0) (.const 3) (.var 1))).map
        Outcome.toP)
```

#### `Toy.UB.semE_spec` (`lean/ToyUB/Uninit.lean`)

```lean
-- lean/ToyUB/Uninit.lean:94-96
theorem semE_spec (w : Nat) (e : Expr) :
    ∀ ρ : Var → Option (BitVec w), semE w ρ e = [.ub] ∨
      ∃ v, semE w ρ e = [.val v] ∧ semP w (toPoisonEnv ρ) e = [.val (.int v)]
```

#### `Toy.UB.dead_read_insertion_poison_sound_eager_unsound` (`lean/ToyUB/Uninit.lean`)

```lean
-- lean/ToyUB/Uninit.lean:219-221
theorem dead_read_insertion_poison_sound_eager_unsound (w : Nat) :
    RefinesP w (.letE 1 (.var 0) (.const 0)) (.const 0) ∧
    ¬ RefinesE w (.letE 1 (.var 0) (.const 0)) (.const 0)
```

#### `Toy.UB.mul_zero_to_branch_eager_sound_poison_unsound` (`lean/ToyUB/Uninit.lean`)

```lean
-- lean/ToyUB/Uninit.lean:237-239
theorem mul_zero_to_branch_eager_sound_poison_unsound (w : Nat) :
    RefinesE w (.ite (.var 0) (.const 0) (.const 0)) (.mul (.var 0) (.const 0)) ∧
    ¬ RefinesP w (.ite (.var 0) (.const 0) (.const 0)) (.mul (.var 0) (.const 0))
```

#### `Toy.UB.outRef_mono_rel` (`lean/ToyUB/Uninit.lean`)

```lean
-- lean/ToyUB/Uninit.lean:157-158
theorem outRef_mono_rel {V : Type} {R R' : V → V → Prop} (hR : ∀ a b, R a b → R' a b)
    {T S : List (Outcome V)} (h : OutRef R T S) : OutRef R' T S
```

#### `Toy.UB.nonvacuity_semantics_total` (`lean/ToyUB/NonVacuity.lean`)

```lean
-- lean/ToyUB/NonVacuity.lean:206-210
theorem nonvacuity_semantics_total :
    semP 2 (fun _ => .poison) (.ite (.freeze (.var 0)) (.var 1) .ub) ≠ [] ∧
    semU 2 (fun _ => USet.single 0#2) (.ite (.freeze (.var 0)) (.var 1) .ub) ≠ [] ∧
    (∀ ρ : Var → PVal 2, OutRefNE PVal.Refines (semP 2 ρ (.mul (.const 2) (.var 0)))
      (semP 2 ρ (.add (.var 0) (.var 0))))
```

#### `Toy.UB.uInhabited_examples` (`lean/ToyUB/Undef.lean`)

```lean
-- lean/ToyUB/Undef.lean:118-119
theorem uInhabited_examples :
    UInhabited (fun _ => USet.single 0#2) ∧ ¬ UInhabited (fun _ => fun _ : BitVec 2 => false)
```

## Boundaries

Non-claims come first: those shared by several results, then those of each result. They record what the results do **not** show.

### Non-claims shared by several results

- **S1** (all results). The language is a toy (first-order expressions over w-bit integers with let, +, *, an equality test, if, freeze and an explicit ub); it is not LLVM IR, Rust MIR, or any production IR, and no result is a theorem about LLVM or Rust.
- **S2** (all results). The models have no memory, pointers, loads/stores, loops, function calls, select/phi, floating point, or integer types of different widths; nothing is shown about those features.
- **S3** (all results). No operation creates an invalid value from valid operands: + and * wrap modulo 2^w (there are no nsw/nuw overflow-poison flags), and there are no shifts, division or remainder. Invalid values enter only through inputs, and UB only through ub or, in the poison model, through branching.
- **S4** (all results). Refinement is written RefinesU w tgt src / RefinesP w tgt src with the target first: rewriting src to tgt is sound exactly when the statement holds. Reading the arguments in the other order inverts the rewrite.
- **S5** (results 1, 2, 3, 4, 5, 6, 10, 12, 14, 15, 16, 22). In the undef model a value is an arbitrary nonempty set of w-bit integers (the power-set reading of undefined values in Lopes et al., PLDI 2021, Figure 2), not a pattern of defined and undefined bits; RefinesU quantifies only over environments that bind every variable to a nonempty set (UInhabited).
- **S6** (results 1, 2, 3, 5, 10, 12, 14, 15, 22: every result with an undef-model statement that covers programs containing if). In the undef model, if commits to a branch at the level of outcomes (with c bound to {0, 1}, if c then 1 else 0 has the two outcomes {1} and {0}, not the single value {0, 1}; Toy.UB.semU_ite_commits_example): it models a conditional branch whose direction is chosen nondeterministically, not a select instruction, and branching on an undef value is never UB. The LLVM 19.1.0 Language Reference states the rule 'Branching on an undefined value is undefined behavior' (while an example discussion in the same section says undefined select and conditional branch conditions 'can go either way'); undef-model results involving if therefore describe the nondeterministic-branch reading only, not LLVM 19.1.0's rule for br.
- **S7** (results 9, 10, 12). The equality test yields 1 or 0 modulo 2^w; at width 0 every integer is 0, so eq a b always yields 0 and if (eq a b) always takes the else-branch (unless an operand reaches UB or, in the poison(+freeze) model, evaluates to poison).
- **S8** (results 20, 21). The eager reading is a toy: each input is wholly initialized or wholly uninitialized, reading an uninitialized input at integer type is immediate UB, let only ever binds initialized values, and freeze is the identity (so freeze x with x uninitialized is UB, because the read happens first; Toy.UB.semE_freeze_uninit_example). There are no bytes, padding, unions or untyped copies.
- **S9** (results 20, 21). Nothing is claimed about lowering Rust to LLVM IR: Rust values passed or returned with LLVM noundef attributes make poison immediate UB at those points (LLVM 19.1.0 Language Reference, noundef), and Rust permits uninitialized bytes in padding and unions (MaybeUninit) without UB; neither is modelled.
- **S10** (results 20, 21). The comparison is per fixed program and environment. It does not transfer the soundness of rewrites between the readings in either direction: inserting a dead read (0 -> let y := x; 0) is sound with poison and unsound eagerly (Toy.UB.dead_read_insertion_poison_sound_eager_unsound), while x * 0 -> if x then 0 else 0 is sound eagerly and unsound with poison (Toy.UB.mul_zero_to_branch_eager_sound_poison_unsound).

### Non-claims of each result

**1. `refinement-preorder`** (also S1, S2, S3, S4, S5, S6):

- Refinement is not antisymmetric on syntax: distinct programs (e.g. x + x and 2 * x in the poison(+freeze) model) refine each other; no partial order on programs is claimed.
- OutRef places no lower bound on the target outcome list (an empty target refines everything; Toy.UB.outRef_example_empty_target). The package's semantics never produce an empty list in an admissible environment, so refinement here coincides with the variant that requires a nonempty target (card semantics-total); a semantics that can produce no outcome would need that variant.
- Nothing is claimed about the refinement relation implemented by any tool.

**2. `source-ub-refined-by-anything`** (also S1, S2, S3, S4, S5, S6):

- A source that reaches UB only in some environments is refined by an arbitrary target only in those environments; that per-environment statement is the definition of OutRef, not a separate result.
- 'May reach UB' is existential over the source's nondeterministic choices (freeze, and branching in the undef model): a single UB-reaching choice in the source permits any target behaviour, as in the per-behaviour formulation of Lopes et al. (PLDI 2021, Section 5.2). No claim is made about refinement notions that permit arbitrary target behaviour only when every source choice reaches UB.
- This is a reference point that holds by definition; it carries no information beyond the definition of OutRef.

**3. `refinement-congruence`** (also S1, S2, S3, S4, S5, S6):

- Congruence is for the package's value-level refinement only. The coarser comparison of produced integers (ObsRefinesU) is not a congruence (card undef-observational-refinement-not-congruence).
- Congruence covers the constructs of this language only; nothing is claimed about memory operations, calls, loops or select.
- The let case relies on monotonicity of the semantics in the environment (Toy.UB.semU_mono, Toy.UB.semP_mono), which holds because no construct can inspect whether a value is poison or how large an undef set is.

**4. `undef-observational-refinement-not-congruence`** (also S1, S2, S3, S4, S5):

- The failure is specific to let: let binds y to the whole value set of x, and the two uses of y in y + y then choose independently, whereas freeze x fixes one integer. Contexts that use their argument once do not separate x from freeze x in this way; no characterization of the contexts that preserve observational refinement is given.
- Value-level refinement (RefinesU) restores congruence for let and every other construct (Toy.UB.refinesU_congr_letE) and correctly rejects freeze x -> x (Toy.UB.undef_remove_freeze_unsound).
- ObsRefinesU is introduced only to exhibit this failure; it is not the package's refinement notion.

**5. `merge-uses-sound`** (also S1, S2, S3, S4, S5, S6):

- Only the pair e + e / 2 * e is covered; nothing is claimed about merging duplicated subexpressions in other contexts (e.g. e * e, or e used by two different operations).
- Expressions are pure and multiplication wraps modulo 2^w. In an IR where e has observable side effects (I/O, volatile accesses, stores) or where multiplication carries overflow-poison flags (mul nsw / mul nuw; note that the literal 2 is negative in signed 2-bit arithmetic), the rewrite is not covered.

**6. `undef-duplicate-use-unsound`** (also S1, S2, S3, S4, S5):

- Shown for a variable operand x; for some other operands (e.g. constants) the rewrite is sound, and no characterization of the operands for which it is sound is given.
- The counterexample involves no branch, so it does not depend on the undef model's nondeterministic-branch rule.

**7. `poison-duplicate-freeze-free-use-sound`** (also S1, S2, S3, S4):

- FreezeFree is syntactic; an expression containing freeze can still be deterministic (e.g. freeze 1), and no semantic characterization of the operands for which the rewrite is sound is given.
- Expressions are pure and multiplication wraps modulo 2^w; side effects and overflow-poison flags (nsw/nuw) are not modelled.

**8. `poisonFreeze-duplicate-frozen-operand-unsound`** (also S1, S2, S3, S4):

- This is the same phenomenon as duplicate-freeze-unsound (2 * freeze x and let a := freeze x; a + a have the same outcomes); the two cards differ only in the source program.
- Shown for e = freeze x; no characterization of the non-freeze-free operands for which 2 * e -> e + e is sound is given.

**9. `poison-gvn-sound`** (also S7, S1, S2, S3, S4):

- Phase ordering: once the comparison is wrapped in freeze the rewrite is unsound. For every w ≥ 1, rewriting if freeze (x = y) then y else 0 to if freeze (x = y) then (let y := x; y) else 0 is not a refinement in the poison + freeze model (x ↦ poison, y ↦ 1: the source yields 0 or 1, the target may yield poison; Toy.UB.poisonFreeze_gvn_after_freezing_condition_unsound). Inserting freeze (sound by itself) removes the UB the GVN argument relies on.
- The rewrite is stated with let y := x; t (which rebinds y), not with syntactic substitution t[y := x]; substitution is not formalized. The two agree for t = y (Toy.UB.semP_letE_var_var), and in general because x denotes a single value in the poison model; this need not hold when y is replaced by an expression that contains freeze.
- Only integer equality is modelled. Nothing is shown for equality on pointers (where equal addresses need not make two pointers interchangeable under provenance-based semantics) or on floating point (where -0.0 == +0.0 although the two values are distinguishable).

**10. `undef-gvn-unsound`** (also S7, S1, S2, S3, S4, S5, S6):

- Shown for the then-branch y and else-branch 0; for other branches (e.g. 0 or x) the rewrite can be sound (Toy.UB.undef_gvn_sound_examples_closed_or_x_branch), and no characterization of the branches for which it fails is given.
- This counterexample depends on the undef model's rule that branching on an undef value is a nondeterministic choice. Under a rule that makes branching on an undefined value UB (as the LLVM 19.1.0 Language Reference states for conditional branches), the source of this counterexample would itself reach UB; that rule is not modelled here. The same document's select semantics states no such rule, and its undef examples say that undefined select conditions 'can go either way'; this package does not model select and claims nothing about equality propagation through select in LLVM.

**11. `poison-unswitch-without-freeze-unsound`** (also S1, S2, S3, S4):

- The toy has no loops; the guarding if c stands in for a loop that may run zero times.

**12. `undef-unswitch-without-freeze-sound`** (also S7, S1, S2, S3, S4, S5, S6):

- UInhabited (every input is a nonempty set) is part of RefinesU. It is not what makes the variable corollary true: the pointwise refinement condition holds even in environments with an empty input set (Toy.UB.undef_unswitch_vars_outRef_all_envs), because then the target has no outcome and OutRef accepts an empty target. What UInhabited guarantees is that every program has at least one outcome (card semantics-total), so the theorem is not satisfied by an empty target.
- Soundness here depends on branching on an undef value being a nondeterministic choice; with LLVM 19.1.0's rule that branching on an undefined value is UB, the poison-model counterexample (card poison-unswitch-without-freeze-unsound) applies instead.

**13. `poisonFreeze-unswitch-with-freeze-sound`** (also S1, S2, S3, S4):

- freeze converts poison into an arbitrary integer but does not suppress immediate undefined behaviour: semP w ρ (freeze ub) = [ub]. Hoisting an inner condition whose own evaluation may reach UB remains unsound even with freeze (Toy.UB.poisonFreeze_unswitch_with_freeze_needs_ubFree, Toy.UB.poisonFreeze_unswitch_with_freeze_needs_ubFree_branch).
- The target replaces the source's possible UB on a poison inner condition by a nondeterministic choice; it refines the source but discards facts a later pass could have derived from that UB (e.g. GVN on the frozen condition; see card poison-gvn-sound).
- The toy has no loops; the guarding if ec stands in for a loop that may run zero times.

**14. `freeze-identity-on-non-poison`** (also S1, S2, S3, S4, S5, S6):

- The first statement is pointwise (one environment); it is a definitional reference point.
- The never-poison condition is semantic and quantifies over all environments; it is not decided by a syntactic check here.

**15. `freeze-insertion-sound`** (also S1, S2, S3, S4, S5, S6):

- Inserting freeze is a refinement in isolation, but it removes poison (and the UB of branching on it) that later rewrites may depend on, so it does not commute with them: GVN on if x = y is sound (card poison-gvn-sound) but GVN on if freeze (x = y) is not (Toy.UB.poisonFreeze_gvn_after_freezing_condition_unsound).
- Nothing is claimed about the cost or code-size effect of inserting freeze.

**16. `freeze-removal-unsound`** (also S1, S2, S3, S4, S5):

- Shown for a variable operand; for operands that are always well defined the rewrite can be sound, and no characterization is given beyond the never-poison condition.

**17. `frozen-value-used-twice-even`** (also S1, S2, S3, S4):

- These are supporting facts for duplicate-freeze-unsound; they do not characterize the full outcome set of let a := freeze x; a + a for every environment (e.g. with x ↦ 0 its only outcome is 0).
- Parity is used only as a convenient invariant distinguishing one frozen value used twice from two frozen values.

**18. `duplicate-freeze-unsound`** (also S1, S2, S3, S4):

- The reverse rewrite (merging two freezes into one let-bound freeze) is sound (card merge-freeze-sound).

**19. `merge-freeze-sound`** (also S1, S2, S3, S4):

- Merging is sound when every use of the eliminated freeze is redirected. Replacing only some uses is unsound: for every w ≥ 1, in let b1 := freeze x; let b2 := freeze x; (b2 = b2), replacing one use of b2 by b1 gives a program that can yield 0 while the source always yields 1 (Toy.UB.poisonFreeze_partial_merge_freeze_unsound).
- The variable a is bound only in the target and is used only in a + a, so no freshness condition is needed in this statement; nothing is claimed for contexts where a is used elsewhere.

**20. `poison-refines-eager-uninit`** (also S8, S9, S10, S1, S2, S3, S4):

- Because eager outcomes never contain poison, the refinement uses only equality of integers (the strict form poison_refines_eagerUninit_eq); the poison clause of PVal.Refines is never exercised.

**21. `eager-uninit-does-not-refine-poison`** (also S8, S9, S10, S1, S2, S3, S4):

- This shows that the eager reading is strictly stronger (more UB) than the poison reading on one program; it does not say that either reading is the right model for any language.

**22. `semantics-total`** (also S1, S2, S3, S4, S5, S6):

- Totality is about the number of outcomes, not termination or absence of UB; programs may still have UB outcomes.
- OutRef itself still accepts an empty target (Toy.UB.outRef_example_empty_target); the equivalence holds for this package's semantics, not for arbitrary outcome lists.

### Escape hatches of the impossibility results

Each impossibility holds only under its stated hypotheses and setting. In the nearby settings below the rewrite becomes sound (each cited theorem is proved), so a design that can establish one of them is not blocked by the impossibility.

**6. `undef-duplicate-use-unsound`.** Escape hatches (each proved): duplicating a single frozen copy, 2 * e -> let a := freeze e; a + a, is a refinement for every e at every width (Toy.UB.undef_rewrite_two_mul_to_let_freeze_add_self_sound); for an input known to be a singleton (well defined, e.g. under a noundef-style precondition) the rewrite is sound pointwise (Toy.UB.undef_rewrite_two_mul_to_add_self_sound_at_singleton); in the poison(+freeze) model the rewrite is sound for freeze-free operands (Toy.UB.poison_rewrite_two_mul_to_add_self_sound_of_freezeFree). Positive controls: `Toy.UB.undef_rewrite_two_mul_to_add_self_sound_width_zero`, `Toy.UB.undef_rewrite_two_mul_to_let_freeze_add_self_sound`, `Toy.UB.undef_rewrite_two_mul_to_add_self_sound_at_singleton`, `Toy.UB.poison_rewrite_two_mul_to_add_self_sound_of_freezeFree`.

**8. `poisonFreeze-duplicate-frozen-operand-unsound`.** Escape hatches (each proved): binding one frozen copy, 2 * e -> let a := freeze e; a + a, is a refinement for every e at every width (Toy.UB.poisonFreeze_rewrite_two_mul_to_let_freeze_add_self_sound); for an input known to be an integer rather than poison (a noundef-style precondition) the rewrite is sound pointwise (Toy.UB.poisonFreeze_rewrite_two_mul_freeze_sound_at_int). Positive controls: `Toy.UB.poisonFreeze_rewrite_two_mul_to_add_self_sound_width_zero`, `Toy.UB.poison_rewrite_two_mul_to_add_self_sound_of_freezeFree`, `Toy.UB.poisonFreeze_rewrite_two_mul_to_let_freeze_add_self_sound`, `Toy.UB.poisonFreeze_rewrite_two_mul_freeze_sound_at_int`.

**10. `undef-gvn-unsound`.** Escape hatch (proved for x = 0, y = 1, x' = 2): freezing the compared operand first, rewriting if x = y then y else 0 to let x' := freeze x; if x' = y then x' else 0, is a refinement at every width (Toy.UB.undef_gvn_with_frozen_operand_sound). The binder x' must not be y. Positive controls: `Toy.UB.undef_gvn_sound_width_zero`, `Toy.UB.undef_gvn_sound_of_same_var`, `Toy.UB.undef_gvn_sound_examples_closed_or_x_branch`, `Toy.UB.undef_gvn_with_frozen_operand_sound`.

**11. `poison-unswitch-without-freeze-unsound`.** Escape hatches: freezing the hoisted condition (proved: Toy.UB.poisonFreeze_unswitch_with_freeze_sound_of_ubFree); the undef model, where branching is a choice (proved: Toy.UB.undef_unswitch_without_freeze_sound_of_ubFree). Not proved here, but the counterexample needs an environment with c ↦ 0 and d ↦ poison, so it says nothing about contexts where the outer condition is known to be nonzero (e.g. a loop known to execute at least once, Lee et al., PLDI 2017, Section 5.1) or where d is known not to be poison. Positive controls: `Toy.UB.poison_unswitch_without_freeze_sound_of_same_var`, `Toy.UB.poisonFreeze_unswitch_with_freeze_sound_of_ubFree`, `Toy.UB.undef_unswitch_without_freeze_sound_of_ubFree`.

**16. `freeze-removal-unsound`.** Escape hatches (each proved): removing freeze from an operand that never yields poison is sound (Toy.UB.poisonFreeze_remove_freeze_sound_of_no_poison), in particular redundant-freeze elimination freeze (freeze e) -> freeze e in both models (Toy.UB.poisonFreeze_remove_redundant_freeze_sound, Toy.UB.undef_remove_redundant_freeze_sound). Positive controls: `Toy.UB.poisonFreeze_remove_freeze_sound_of_no_poison`, `Toy.UB.poisonFreeze_remove_redundant_freeze_sound`, `Toy.UB.undef_remove_redundant_freeze_sound`, `Toy.UB.undef_remove_freeze_sound_width_zero`.

**18. `duplicate-freeze-unsound`.** Escape hatch (proved): for an input known to be an integer rather than poison (a noundef-style precondition), the duplication is sound pointwise (Toy.UB.poisonFreeze_duplicate_freeze_sound_at_int). For a compound operand, 'never yields poison' is not enough: e = freeze y never yields poison, yet duplicating freeze e is unsound at width 2 because the two copies of e may differ (Toy.UB.poisonFreeze_duplicate_freeze_of_nonpoison_compound_unsound). Positive controls: `Toy.UB.poisonFreeze_duplicate_freeze_sound_width_zero`, `Toy.UB.poisonFreeze_merge_freeze_sound`, `Toy.UB.poisonFreeze_duplicate_freeze_sound_at_int`.

### Attractive stronger conclusions that are not established

- **not established — "proved here, therefore sound (or unsound) in LLVM or Rust".** Every result is about the toy models. Connections to LLVM, Alive2 and Rust
  are `derived (modeling bridge)` claims; the gaps listed under **Applicability** (sets instead
  of bit patterns, branching on undef as a choice, no poison-creating operations, no memory,
  `select`, `phi`, loops or calls) can each change the answer.
- **not examined — undef results under a branch-on-undef-is-UB rule.** The LLVM 19.1.0
  Language Reference states that branching on an undefined value is undefined behavior. No
  undef model with that rule is defined here; the results `undef-gvn-unsound` and
  `undef-unswitch-without-freeze-sound`, and every undef-model statement involving `if`,
  describe only the nondeterministic-branch reading.
- **known not to apply — "freeze makes hoisting a branch out of a conditional valid".** It does
  so only when the hoisted condition cannot itself reach UB: the hypotheses `hed : UBFreeP w ed`
  and `hed : UBFreeU w ed` are tight (counterexamples
  `poisonFreeze_unswitch_with_freeze_needs_ubFree` and
  `undef_unswitch_without_freeze_needs_ubFree`), and `freeze` removes poison but not UB
  (`semP w ρ (freeze ub) = [ub]` by the definition of `semP`).
- **known not to apply — "duplicating a freeze is fine when its operand never yields
  poison".** False for compound operands: `e = freeze y` never yields poison, yet duplicating
  `freeze e` is unsound at width 2 because the two copies of `e` may differ
  (`poisonFreeze_duplicate_freeze_of_nonpoison_compound_unsound`). Only the pointwise
  statement for an input bound to an integer is proved
  (`poisonFreeze_duplicate_freeze_sound_at_int`).
- **unknown — further escape hatches for loop unswitching.** Whether hoisting without `freeze`
  is sound when the outer condition is known to be nonzero (a loop known to execute at least
  once; Lee et al., PLDI 2017, Section 5.1) or when the inner condition is known not to be
  poison was considered but not formalized: both need a precondition on environments that
  `RefinesP` does not express. The counterexample of `poison-unswitch-without-freeze-unsound`
  uses `c ↦ 0` and `d ↦ poison`, so it says nothing about those contexts.
- **not examined — rewrite-level transfer between the eager and poison readings.**
  `poison-refines-eager-uninit` is per fixed program; the supporting theorems
  `dead_read_insertion_poison_sound_eager_unsound` and
  `mul_zero_to_branch_eager_sound_poison_unsound` show that soundness of a rewrite transfers
  in neither direction, and no positive transfer criterion is claimed.
- **not examined — refinement notions other than `OutRef`.** In particular a notion that
  permits arbitrary target behaviour only when every source choice reaches UB, and the
  observational notion `ObsRefinesU` beyond the single counterexample of
  `undef-observational-refinement-not-congruence`.

### Hypotheses with `unknown` tightness

None. All 46 hypothesis entries in `results.json` are `tight`, each with a named, fully proved
counterexample stating that all other hypotheses hold and the conclusion fails.

### Disproved or dropped statements

None. All 22 results were proved as stated; no statement was found false and none was left
unproved.

## Evidence

**Kernel-check record.** Toolchain `leanprover/lean4:v4.34.1` (`leanprover/lean4`, tag `v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`); Lake project `lean/` with one library `ToyUB` and no dependencies (core Lean only). Observed 2026-11-20: `lake build` succeeds with no `sorry` warnings; no Lean source contains `sorry`, `admit`, `native_decide`, `axiom` or `opaque` declarations, `implemented_by`, `@[extern]` or `unsafe`; all 490 non-internal declarations of the library depend only on axioms among `propext`, `Classical.choice`, `Quot.sound` (per declaration in `audit/axioms.json`). Every result is `Basis: execution (Lean kernel check)`.

**Statement and closure hashes.** For each Lean name in the fields `lean`, `lean_names`, `nonvacuity_witness_lean`, `positive_control_lean` and hypothesis `counterexample` of `results.json`, `audit/statements.json` records the SHA-256 of the statement and of its definition closure (computed as described under **Revalidation**). The table lists them with the axioms of each theorem; roles are `R` (result), `CE` (tightness counterexample), `NV` (non-vacuity witness), `PC` (positive or contrasting control), `S` (supporting theorem).

| Lean name | Used by (result: role) | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
|---|---|---|---|---|
| `Toy.UB.refinesU_refl` | 1:R | Classical.choice, Quot.sound, propext | `f7f2a4ec0f621bb03ff5a56c2083f2ab1eae93cc9ffebec3a00c3bed67409651` | `6c2fb642f92b904e50efa90d43f4bced91353793c1d197d2fef8a7f1e2d26d4f` (45) |
| `Toy.UB.refinesU_trans` | 1:R | Classical.choice, Quot.sound, propext | `fdb60f2851a69f67101491ccabe73f6278aa4320d6facb5e06cfbe03147b5c59` | `6c2fb642f92b904e50efa90d43f4bced91353793c1d197d2fef8a7f1e2d26d4f` (45) |
| `Toy.UB.refinesP_refl` | 1:R | propext | `a27f15ae0faf315c3ac7bd4b1c04e4463552d2f86f218e2f2f7b5ea4e3280beb` | `d0d68551a59122d2bfccda1215e027af4230dfeaf382fee1d0ba51671ea82b66` (50) |
| `Toy.UB.refinesP_trans` | 1:R | propext | `9019fb2add7896d53f56da21865480471624cbcbf05df9cf033dda074db59fa1` | `d0d68551a59122d2bfccda1215e027af4230dfeaf382fee1d0ba51671ea82b66` (50) |
| `Toy.UB.refinesU_trans_needs_hab` | 1:CE | Classical.choice, Quot.sound, propext | `e73cb6132038ea0ae16a150fb42965ccc4545246cc1a0f7920b3228629aea59e` | `6c2fb642f92b904e50efa90d43f4bced91353793c1d197d2fef8a7f1e2d26d4f` (45) |
| `Toy.UB.refinesP_trans_needs_hab` | 1:CE | Quot.sound, propext | `be5cb035101d96a33bde26e1a01b48b3af5e98a12caae3b07d041b72dea91d9c` | `d0d68551a59122d2bfccda1215e027af4230dfeaf382fee1d0ba51671ea82b66` (50) |
| `Toy.UB.refinesU_trans_needs_hbc` | 1:CE | Classical.choice, Quot.sound, propext | `f34761af2da9385ed91cb00e447d190b53858818e435abd7ca0f1db31b8de978` | `6c2fb642f92b904e50efa90d43f4bced91353793c1d197d2fef8a7f1e2d26d4f` (45) |
| `Toy.UB.refinesP_trans_needs_hbc` | 1:CE | Quot.sound, propext | `ffc25fc56864347f0358c9251ff7fa7a6ddb178cf2106680d8dd5120b0ad3a9a` | `d0d68551a59122d2bfccda1215e027af4230dfeaf382fee1d0ba51671ea82b66` (50) |
| `Toy.UB.nonvacuity_refinesU_trans` | 1:NV | Classical.choice, Quot.sound, propext | `c216dbe70ce832a2f98d5daefeffa135a29c94c383a06b8648283a8525fbb63a` | `6c2fb642f92b904e50efa90d43f4bced91353793c1d197d2fef8a7f1e2d26d4f` (45) |
| `Toy.UB.nonvacuity_refinesP_trans` | 1:NV | Quot.sound, propext | `0a863df69114624855878ed9c450d311a098490fe11ad9861bf61c5e077d1ff3` | `d0d68551a59122d2bfccda1215e027af4230dfeaf382fee1d0ba51671ea82b66` (50) |
| `Toy.UB.semP_ne_nil` | 1:S, 22:R | Quot.sound, propext | `b9db089f859e3118be6d86a0e41434ee7575f0992ad8053f256d064824027d15` | `ac375665ca7c6700ba79f0b8d5c04a7ca8ada29e8f77f812ea20ecdc0921ed18` (40) |
| `Toy.UB.semU_ne_nil` | 1:S, 22:R | Classical.choice, Quot.sound, propext | `f82c06d70416832052502d5c799f6ce07410c4070a36a32bf7d7ccd27f92c876` | `896f3c6cb4bd689957a2fc34d75a015701914c74f7ee429341a9198a380047e2` (36) |
| `Toy.UB.refinesP_iff_outRefNE` | 1:S, 22:R | Quot.sound, propext | `4af521d916e276c43b113dc46af31a5c5251319667544662d7a1798a69c35f4a` | `93c3516a732f88c575e184f9131904b5e848afb8ba3c9eeb7a4db95f6c41f461` (51) |
| `Toy.UB.refinesU_iff_outRefNE` | 1:S, 22:R | Classical.choice, Quot.sound, propext | `eb61c3cb05e69c6144e97035248967808dacfd24712538a881e1f895d3e3fb4a` | `d9b0baea39522029f9fc5db8801d744a458282e23dda54447700794a4196781d` (46) |
| `Toy.UB.refinesU_of_src_mayUB` | 2:R | Classical.choice, Quot.sound, propext | `94f3a8a721d3d16a4161b4b52206e0f8d621829a3e209509c8a665ce7fe04358` | `6c2fb642f92b904e50efa90d43f4bced91353793c1d197d2fef8a7f1e2d26d4f` (45) |
| `Toy.UB.refinesP_of_src_mayUB` | 2:R | propext | `ca7373f110458ea43b1f6c028d0d1dbcbc44c85bccb00be84faf6c51c415925e` | `d0d68551a59122d2bfccda1215e027af4230dfeaf382fee1d0ba51671ea82b66` (50) |
| `Toy.UB.refinesU_ub` | 2:R | Classical.choice, Quot.sound, propext | `a1d05e7b49a38f93e9c58b3f2c2a4add795941d34470b2281671f4ae948977f3` | `6c2fb642f92b904e50efa90d43f4bced91353793c1d197d2fef8a7f1e2d26d4f` (45) |
| `Toy.UB.refinesP_ub` | 2:R | propext | `18e83348ab1ac9a613c419b4a1b4923a81e9e988766bfd03447d8fbf352dcf15` | `d0d68551a59122d2bfccda1215e027af4230dfeaf382fee1d0ba51671ea82b66` (50) |
| `Toy.UB.refinesU_of_src_mayUB_needs_mayUB` | 2:CE | Classical.choice, Quot.sound, propext | `112c8639516e3d305275954197988800263ac1a645353248c31cd5da0ceccd52` | `6c2fb642f92b904e50efa90d43f4bced91353793c1d197d2fef8a7f1e2d26d4f` (45) |
| `Toy.UB.refinesP_of_src_mayUB_needs_mayUB` | 2:CE | Quot.sound, propext | `017b76569ccac239cdda44154f257d5547ebfc6802a0bcfd454b9fd998d5879d` | `d0d68551a59122d2bfccda1215e027af4230dfeaf382fee1d0ba51671ea82b66` (50) |
| `Toy.UB.nonvacuity_refinesU_of_src_mayUB` | 2:NV | Classical.choice, Quot.sound, propext | `e6f8d605e2e948046f9c4a4b17e48e5223a2215b0205a038581a820e533bc8d2` | `ec30a0c22c05a0bdcbba5339174969fd6b7936a583d16e92507a7e8d91d18aec` (38) |
| `Toy.UB.nonvacuity_refinesP_of_src_mayUB` | 2:NV | Quot.sound, propext | `8e54290faaa42922269bc818036cca9733b07dcdd289f5c01ec383bd2f73a687` | `f06a73c7008b4a5cf667e55634283b9d35509971019d69cae8475f5ed684c975` (42) |
| `Toy.UB.refinesU_congr_add` | 3:R | Classical.choice, Quot.sound, propext | `5b16333315319c1841839ede5e59aa1ae2f4e4374cc0d2020e008fbfec172672` | `6c2fb642f92b904e50efa90d43f4bced91353793c1d197d2fef8a7f1e2d26d4f` (45) |
| `Toy.UB.refinesU_congr_mul` | 3:R | Classical.choice, Quot.sound, propext | `c8077cc6dd158011cdb8bed151cb9513205526d7244695f87a50666d66565916` | `6c2fb642f92b904e50efa90d43f4bced91353793c1d197d2fef8a7f1e2d26d4f` (45) |
| `Toy.UB.refinesU_congr_eq` | 3:R | Classical.choice, Quot.sound, propext | `8d851ca0b3a64af4ad35292558164bffeddaa003a7a0a4843df72b3dccdd2d28` | `6c2fb642f92b904e50efa90d43f4bced91353793c1d197d2fef8a7f1e2d26d4f` (45) |
| `Toy.UB.refinesU_congr_ite` | 3:R | Classical.choice, Quot.sound, propext | `d371a3dcce60f5fcdfde429e40c5514696d5b844f663b3c169a966e8793b7bf6` | `6c2fb642f92b904e50efa90d43f4bced91353793c1d197d2fef8a7f1e2d26d4f` (45) |
| `Toy.UB.refinesU_congr_letE` | 3:R, 4:PC | Classical.choice, Quot.sound, propext | `821fbffe2718d55422b08c8351738f4bb72e089f34a63ad354164426b607d021` | `6c2fb642f92b904e50efa90d43f4bced91353793c1d197d2fef8a7f1e2d26d4f` (45) |
| `Toy.UB.refinesU_congr_freeze` | 3:R | Classical.choice, Quot.sound, propext | `9958f6d26721a5c70afdf5c0f9bd461d38a3b6b07c0842f19d3c3b6a12268e02` | `6c2fb642f92b904e50efa90d43f4bced91353793c1d197d2fef8a7f1e2d26d4f` (45) |
| `Toy.UB.refinesP_congr_add` | 3:R | Quot.sound, propext | `f8a3dd42336933acabc7f2ad108b5d92873dc282585ec648ca3a4d0681712b86` | `d0d68551a59122d2bfccda1215e027af4230dfeaf382fee1d0ba51671ea82b66` (50) |
| `Toy.UB.refinesP_congr_mul` | 3:R | Quot.sound, propext | `36b3aa5a318f2ef80404c8c72e312e4bc9f8f42a83a4222073f4b93ed4004464` | `d0d68551a59122d2bfccda1215e027af4230dfeaf382fee1d0ba51671ea82b66` (50) |
| `Toy.UB.refinesP_congr_eq` | 3:R | Quot.sound, propext | `02ca765ecdcb0e714541619f011403d77ce9e14239dae587fdf8054a9f8bcbc5` | `d0d68551a59122d2bfccda1215e027af4230dfeaf382fee1d0ba51671ea82b66` (50) |
| `Toy.UB.refinesP_congr_ite` | 3:R | Quot.sound, propext | `35a4693a0e875232c59640fa0bde4971383b63502755867cae2cc4552508efa0` | `d0d68551a59122d2bfccda1215e027af4230dfeaf382fee1d0ba51671ea82b66` (50) |
| `Toy.UB.refinesP_congr_letE` | 3:R | Quot.sound, propext | `faad8446d3d84c59f1a904f6f3c0f6ae9f424e60bbf90d8acb424a4ead4d2ba6` | `d0d68551a59122d2bfccda1215e027af4230dfeaf382fee1d0ba51671ea82b66` (50) |
| `Toy.UB.refinesP_congr_freeze` | 3:R | Quot.sound, propext | `ddcdf7eccaeb74fd9d4b5f8a596d6376c8e8cc4aa734a21300492189702db483` | `d0d68551a59122d2bfccda1215e027af4230dfeaf382fee1d0ba51671ea82b66` (50) |
| `Toy.UB.refinesU_congr_add_premises_tight` | 3:CE | Classical.choice, Quot.sound, propext | `fcb643b00be6ac45f315022601ed58c400aaa812bf436c7c04be0dcf63d3dd0a` | `6c2fb642f92b904e50efa90d43f4bced91353793c1d197d2fef8a7f1e2d26d4f` (45) |
| `Toy.UB.refinesU_congr_mul_premises_tight` | 3:CE | Classical.choice, Quot.sound, propext | `431833d416dc41fce002b6ff62635825a98ddd50bf53afce312b40ed5904fea8` | `6c2fb642f92b904e50efa90d43f4bced91353793c1d197d2fef8a7f1e2d26d4f` (45) |
| `Toy.UB.refinesU_congr_eq_premises_tight` | 3:CE | Classical.choice, Quot.sound, propext | `64886fbda3603cf672909211fde856d88a7c1c119454d3c68e02f38406ad18db` | `6c2fb642f92b904e50efa90d43f4bced91353793c1d197d2fef8a7f1e2d26d4f` (45) |
| `Toy.UB.refinesU_congr_ite_premises_tight` | 3:CE | Classical.choice, Quot.sound, propext | `082669980693fc2e530642498be48add54a8167b805689aa9e6a6951ad618067` | `6c2fb642f92b904e50efa90d43f4bced91353793c1d197d2fef8a7f1e2d26d4f` (45) |
| `Toy.UB.refinesU_congr_letE_premises_tight` | 3:CE | Classical.choice, Quot.sound, propext | `8cda1985af047e4c513ef5aea4c9fb387ce46e8164578090de3ff50943e1577f` | `6c2fb642f92b904e50efa90d43f4bced91353793c1d197d2fef8a7f1e2d26d4f` (45) |
| `Toy.UB.refinesU_congr_freeze_premises_tight` | 3:CE | Classical.choice, Quot.sound, propext | `44da63a9c56b983b373b516beac28fcce5d0de26ad4eb86bf9c01cac64603b35` | `6c2fb642f92b904e50efa90d43f4bced91353793c1d197d2fef8a7f1e2d26d4f` (45) |
| `Toy.UB.refinesP_congr_add_premises_tight` | 3:CE | propext | `08f86e801d606cc2bc4d71ad86c15870c66576b6ca71425c315f5e2c08c674a5` | `d0d68551a59122d2bfccda1215e027af4230dfeaf382fee1d0ba51671ea82b66` (50) |
| `Toy.UB.refinesP_congr_mul_premises_tight` | 3:CE | propext | `857c8c4359ecb80387f7f4b6bffc5805b6179c5573062d5117921e7921b0c886` | `d0d68551a59122d2bfccda1215e027af4230dfeaf382fee1d0ba51671ea82b66` (50) |
| `Toy.UB.refinesP_congr_eq_premises_tight` | 3:CE | propext | `0a524ab82340021dd6c8a10eeab3767a08c2faf7907d50240aa8f59eaf6f5c54` | `d0d68551a59122d2bfccda1215e027af4230dfeaf382fee1d0ba51671ea82b66` (50) |
| `Toy.UB.refinesP_congr_ite_premises_tight` | 3:CE | propext | `5fec45914d74a6f983488527aac3011461047e5680b0eed67f29a8b61ca279da` | `d0d68551a59122d2bfccda1215e027af4230dfeaf382fee1d0ba51671ea82b66` (50) |
| `Toy.UB.refinesP_congr_letE_premises_tight` | 3:CE | propext | `f33d54b179293545a2d5b59e6a7acb0ef185052b5f9ccba34e2d85998ff244bb` | `d0d68551a59122d2bfccda1215e027af4230dfeaf382fee1d0ba51671ea82b66` (50) |
| `Toy.UB.refinesP_congr_freeze_premises_tight` | 3:CE | propext | `d7990d0ed6c246693447e06e0ab86c968169c017304828a5b62c8ccdad32703c` | `d0d68551a59122d2bfccda1215e027af4230dfeaf382fee1d0ba51671ea82b66` (50) |
| `Toy.UB.nonvacuity_refinesU_congr` | 3:NV | Classical.choice, Quot.sound, propext | `4e635589758959242289334a6483302ba81bee1c82e58a623a53a6b93ccb6410` | `6c2fb642f92b904e50efa90d43f4bced91353793c1d197d2fef8a7f1e2d26d4f` (45) |
| `Toy.UB.nonvacuity_refinesP_congr` | 3:NV | Quot.sound, propext | `86afae340db80ded2581d83fe1527df53c0871d1c2167db1ff933e638a9c3edd` | `d0d68551a59122d2bfccda1215e027af4230dfeaf382fee1d0ba51671ea82b66` (50) |
| `Toy.UB.undef_obsRefines_not_congruence_letE` | 4:R | Classical.choice, Quot.sound, propext | `2ca11738b05796c3f144e82d96f5c0aaf2a623fc25e07dacb206fd5ff64081e4` | `976ccd8a1aed6079df8868a5bd4041b119ca1d58ff7b1f3abc50fd6ba5c7f194` (41) |
| `Toy.UB.undef_obsRefines_not_congruence_letE_needs_width` | 4:CE | Classical.choice, Quot.sound, propext | `401dda145fda1902da34b87ae6737f44cbf9ff26cd3ed4dbba951e62ad9882d1` | `976ccd8a1aed6079df8868a5bd4041b119ca1d58ff7b1f3abc50fd6ba5c7f194` (41) |
| `Toy.UB.nonvacuity_undef_obsRefines_not_congruence_letE` | 4:NV | Classical.choice, Quot.sound, propext | `6910ea09eff73b7d7ae484b2593ead363ec958f6369f08f8b9fba44a792c5ca9` | `976ccd8a1aed6079df8868a5bd4041b119ca1d58ff7b1f3abc50fd6ba5c7f194` (41) |
| `Toy.UB.nonvacuity_width_two` | 4:NV, 6:NV, 8:NV, 16:NV, 17:NV, 18:NV | (none) | `fb4fba56aba9a4fdcc4f042184f3c87036b9138bd59ec91738c9c1b670cd6194` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.UB.undef_obsRefines_letE_width_zero` | 4:PC | Classical.choice, Quot.sound, propext | `367688e492420a9820b8cf1ed94e24e4cd2dbaf8a3f7b360de8c6b30015412cc` | `976ccd8a1aed6079df8868a5bd4041b119ca1d58ff7b1f3abc50fd6ba5c7f194` (41) |
| `Toy.UB.undef_rewrite_add_self_to_two_mul_sound` | 5:R | Classical.choice, Quot.sound, propext | `93a2b9a191c02e71b10039ebe216d006f597efae1025359ef194d0af1d97e1cd` | `6c2fb642f92b904e50efa90d43f4bced91353793c1d197d2fef8a7f1e2d26d4f` (45) |
| `Toy.UB.poison_rewrite_add_self_to_two_mul_sound` | 5:R | Quot.sound, propext | `bdb7d62084c8ee015300e074304d5ceab4e79ebc8e72053800cdaff57f7b59f1` | `d0d68551a59122d2bfccda1215e027af4230dfeaf382fee1d0ba51671ea82b66` (50) |
| `Toy.UB.nonvacuity_undef_rewrite_add_self_to_two_mul_sound` | 5:NV | Classical.choice, Quot.sound, propext | `c1414a43aefc5bcf971ffd02140d378eafeb768260df1a21260ff6bc2a2acd35` | `6c2fb642f92b904e50efa90d43f4bced91353793c1d197d2fef8a7f1e2d26d4f` (45) |
| `Toy.UB.nonvacuity_poison_rewrite_add_self_to_two_mul_sound` | 5:NV | Quot.sound, propext | `9787d5b1309384717d8fa75ef394cc6544ed8c5559d4c6a8791f7ba70f999f0c` | `d0d68551a59122d2bfccda1215e027af4230dfeaf382fee1d0ba51671ea82b66` (50) |
| `Toy.UB.undef_rewrite_two_mul_to_add_self_unsound` | 6:R | Classical.choice, Quot.sound, propext | `b85829ce8e6bd084d29aab6af3854963611ce04fa22e7c6ee926ae9cdbe0962b` | `6c2fb642f92b904e50efa90d43f4bced91353793c1d197d2fef8a7f1e2d26d4f` (45) |
| `Toy.UB.undef_rewrite_two_mul_to_add_self_unsound_needs_width` | 6:CE | Classical.choice, Quot.sound, propext | `28554aa8f3f5b4dd20b8325ef1bce1cc3209c8bd7d7648c7fa54999129226c19` | `6c2fb642f92b904e50efa90d43f4bced91353793c1d197d2fef8a7f1e2d26d4f` (45) |
| `Toy.UB.nonvacuity_undef_rewrite_two_mul_to_add_self_unsound` | 6:NV | Classical.choice, Quot.sound, propext | `14218969ba872542aff8ee29274dbe6e809de04ca5dad7cac71fa66f5d2263b5` | `6c2fb642f92b904e50efa90d43f4bced91353793c1d197d2fef8a7f1e2d26d4f` (45) |
| `Toy.UB.undef_rewrite_two_mul_to_add_self_sound_width_zero` | 6:PC | Classical.choice, Quot.sound, propext | `c060123bf1d5ca7abfd9711cc6a5c8cc5d286a6045da181f81eb3aae935df2b6` | `6c2fb642f92b904e50efa90d43f4bced91353793c1d197d2fef8a7f1e2d26d4f` (45) |
| `Toy.UB.undef_rewrite_two_mul_to_let_freeze_add_self_sound` | 6:PC | Classical.choice, Quot.sound, propext | `ef82fcf681a10a525693587190c09a667dd51841dd4d469bbf9e3fb9d8407530` | `6c2fb642f92b904e50efa90d43f4bced91353793c1d197d2fef8a7f1e2d26d4f` (45) |
| `Toy.UB.undef_rewrite_two_mul_to_add_self_sound_at_singleton` | 6:PC | Classical.choice, Quot.sound, propext | `3c401ff12ae9529f8ecbe84655b126f90732365d997c53af864676d0ab8ac047` | `4e2dcb9d42844c2b141db7d941bd3c0a0c68778ea5fbb65da628dbb4554f8508` (42) |
| `Toy.UB.poison_rewrite_two_mul_to_add_self_sound_of_freezeFree` | 6:PC, 7:R, 8:PC | Quot.sound, propext | `498b867feac54cc056d3d81d18f0f19a050ca0dc5ff0d03687a48cb7d9757051` | `05c27a5ffaeb3aec4db1bb2ee47de66bb136076dc059f75e569a97bbe6fdf271` (53) |
| `Toy.UB.poison_rewrite_two_mul_to_add_self_needs_freezeFree` | 7:CE | Quot.sound, propext | `716bd525cc586f00cd50017eb78ecfa4dc03f68c896c52824fd92fa958d0d83d` | `05c27a5ffaeb3aec4db1bb2ee47de66bb136076dc059f75e569a97bbe6fdf271` (53) |
| `Toy.UB.poisonFreeze_rewrite_two_mul_to_add_self_unsound` | 7:CE, 8:R | Quot.sound, propext | `92bddb9ed1d81d3bf96730b9668deea54af5c6485f4a41737a4b4c62b12d9c74` | `d0d68551a59122d2bfccda1215e027af4230dfeaf382fee1d0ba51671ea82b66` (50) |
| `Toy.UB.nonvacuity_freezeFree` | 7:NV | (none) | `511623294d94154a9d071ad37cb358b58956428ca25335dc4dc1d13e2a206197` | `c9d67f06dac949b40898a0e794f4d6b0a6936b8a299d303cfa8207eeffeb0f11` (19) |
| `Toy.UB.poisonFreeze_rewrite_two_mul_to_add_self_unsound_needs_width` | 8:CE | Quot.sound, propext | `6f48b197b67b8c1fdda2816261f48285938bb4576da1de82b1b1a5aaa744b13c` | `d0d68551a59122d2bfccda1215e027af4230dfeaf382fee1d0ba51671ea82b66` (50) |
| `Toy.UB.nonvacuity_poisonFreeze_rewrite_two_mul_to_add_self_unsound` | 8:NV | Quot.sound, propext | `0ce6777433136fbe1be7785d455652dcbc552a1414c55ccf4d11c197cac4f92d` | `d0d68551a59122d2bfccda1215e027af4230dfeaf382fee1d0ba51671ea82b66` (50) |
| `Toy.UB.poisonFreeze_rewrite_two_mul_to_add_self_sound_width_zero` | 8:PC | Quot.sound, propext | `b5e56a433a9b19c096811dcf815d5bf7311af0551b0f18779075aaad94c107d2` | `d0d68551a59122d2bfccda1215e027af4230dfeaf382fee1d0ba51671ea82b66` (50) |
| `Toy.UB.poisonFreeze_rewrite_two_mul_to_let_freeze_add_self_sound` | 8:PC | Quot.sound, propext | `4465f0ea46d5b8b97122f82c2b74a2cc2687ce6b729fd7f1a1c9edafbc9ee469` | `d0d68551a59122d2bfccda1215e027af4230dfeaf382fee1d0ba51671ea82b66` (50) |
| `Toy.UB.poisonFreeze_rewrite_two_mul_freeze_sound_at_int` | 8:PC | Quot.sound, propext | `ef19aae1b0f95e871255d7a8dc135de5f4eabb7689b9731af73234e1a03c39ce` | `c138bb6ad1bf08a4dd09440461bd2a48b89e446978474d00467772056176054a` (49) |
| `Toy.UB.poison_gvn_sound` | 9:R | Quot.sound, propext | `81fcc5fe579ead5dbffa6f9f9c09257659e6a27a3ef6b265f8d96f2dc2f559ae` | `d0d68551a59122d2bfccda1215e027af4230dfeaf382fee1d0ba51671ea82b66` (50) |
| `Toy.UB.nonvacuity_poison_gvn_sound` | 9:NV | Quot.sound, propext | `293e81aa35fbc1730af726031d475a719d7461c65ce65e365581f30484a1fbdc` | `d0d68551a59122d2bfccda1215e027af4230dfeaf382fee1d0ba51671ea82b66` (50) |
| `Toy.UB.semP_letE_var_var` | 9:S | Quot.sound, propext | `b2ed00898131e5149a7f8d7509b5f7b0a06ad3ff301acde5b41fd53dbd816677` | `ac375665ca7c6700ba79f0b8d5c04a7ca8ada29e8f77f812ea20ecdc0921ed18` (40) |
| `Toy.UB.poisonFreeze_gvn_after_freezing_condition_unsound` | 9:S, 15:S | Quot.sound, propext | `583573fe1491ea5b165866f30cebbe740e38ff1cb2dff92800052fc5612dce80` | `d0d68551a59122d2bfccda1215e027af4230dfeaf382fee1d0ba51671ea82b66` (50) |
| `Toy.UB.undef_gvn_var_branch_distinct_vars_unsound` | 10:R | Classical.choice, Quot.sound, propext | `ca948e38da5856ef6a592c3519436f138bfa7969b3b4df7b24ba676f81c54406` | `6c2fb642f92b904e50efa90d43f4bced91353793c1d197d2fef8a7f1e2d26d4f` (45) |
| `Toy.UB.undef_gvn_var_branch_distinct_vars_unsound_needs_width` | 10:CE | Classical.choice, Quot.sound, propext | `6b815cab37900e102ba681494ddc7cef057fdaf81a96be78cf930a356993aacb` | `6c2fb642f92b904e50efa90d43f4bced91353793c1d197d2fef8a7f1e2d26d4f` (45) |
| `Toy.UB.undef_gvn_var_branch_distinct_vars_unsound_needs_distinct` | 10:CE | Classical.choice, Quot.sound, propext | `e5b12b4f47a5eb0d239b8468722050f143fd17087e81153a31bff59295ab2436` | `6c2fb642f92b904e50efa90d43f4bced91353793c1d197d2fef8a7f1e2d26d4f` (45) |
| `Toy.UB.nonvacuity_undef_gvn_instance` | 10:NV | Classical.choice, Quot.sound, propext | `f744f0ce7092abbca52a6d72cd126d5307f88124310402d652ae8ca0a4f9ca52` | `6c2fb642f92b904e50efa90d43f4bced91353793c1d197d2fef8a7f1e2d26d4f` (45) |
| `Toy.UB.nonvacuity_undef_gvn` | 10:NV | (none) | `661c93b2573fbee445316894b51aeb32f071660db8144ebfcf63c5974e218aea` | `b93196d2b758be3a4b8025e1338ba12e3601f5c9a66ca772e6d632d855d8f28a` (1) |
| `Toy.UB.undef_gvn_sound_width_zero` | 10:PC | Classical.choice, Quot.sound, propext | `45ce89aa95655bcd9ff30e965d4b3357a955b54a64faef59c30260a3af53238c` | `6c2fb642f92b904e50efa90d43f4bced91353793c1d197d2fef8a7f1e2d26d4f` (45) |
| `Toy.UB.undef_gvn_sound_of_same_var` | 10:PC | Classical.choice, Quot.sound, propext | `50ed1756d3bc4a44ba21afc17ff7ebd6b86f8dba24724ba9f26f1e932e276993` | `6c2fb642f92b904e50efa90d43f4bced91353793c1d197d2fef8a7f1e2d26d4f` (45) |
| `Toy.UB.undef_gvn_sound_examples_closed_or_x_branch` | 10:PC | Classical.choice, Quot.sound, propext | `6e4016a4ddaea85160a64098ae410aa6baa93ca43c6c40dddbd0538aae7c36f9` | `6c2fb642f92b904e50efa90d43f4bced91353793c1d197d2fef8a7f1e2d26d4f` (45) |
| `Toy.UB.undef_gvn_with_frozen_operand_sound` | 10:PC | Classical.choice, Quot.sound, propext | `1befac222f7535f863b3e5889afcc57eb82196e60cde1b87458e5c0e0a995f80` | `6c2fb642f92b904e50efa90d43f4bced91353793c1d197d2fef8a7f1e2d26d4f` (45) |
| `Toy.UB.poison_unswitch_without_freeze_distinct_vars_unsound` | 11:R | Quot.sound, propext | `a23c41294e676563fafafd3b565900958a40118c747ad6a4902ac9c7907916b1` | `d0d68551a59122d2bfccda1215e027af4230dfeaf382fee1d0ba51671ea82b66` (50) |
| `Toy.UB.poison_unswitch_without_freeze_distinct_vars_unsound_needs_distinct` | 11:CE | Quot.sound, propext | `1100546c7b66331c6abdfbc4076837fcc4c239e7dc5ba17c9285a2bf060e7cef` | `d0d68551a59122d2bfccda1215e027af4230dfeaf382fee1d0ba51671ea82b66` (50) |
| `Toy.UB.nonvacuity_poison_unswitch_instance` | 11:NV | Quot.sound, propext | `2d0bb843731277d95b03a3aca129e67aedb21a9101aa38e73362cbca9d845192` | `d0d68551a59122d2bfccda1215e027af4230dfeaf382fee1d0ba51671ea82b66` (50) |
| `Toy.UB.nonvacuity_poison_unswitch` | 11:NV | (none) | `7147295e862b3ace217c5397605a5b2127a991051e175689031f97e8036a9dda` | `b93196d2b758be3a4b8025e1338ba12e3601f5c9a66ca772e6d632d855d8f28a` (1) |
| `Toy.UB.poison_unswitch_without_freeze_sound_of_same_var` | 11:PC | Quot.sound, propext | `e8bae9e47a7032bb3d6dadc5442dfee8ddfc717f87f45685933d896d427e79a6` | `d0d68551a59122d2bfccda1215e027af4230dfeaf382fee1d0ba51671ea82b66` (50) |
| `Toy.UB.poisonFreeze_unswitch_with_freeze_sound_of_ubFree` | 11:PC, 13:R | Quot.sound, propext | `f9ab4d4635ac8f9b48b7d2755abebfad5210df2cc60cf848f27fcd5a23f48769` | `278ddc45bf4eae05df96d44114f5ff2bdbf19ff72616feffe36955620b3e5c0f` (54) |
| `Toy.UB.undef_unswitch_without_freeze_sound_of_ubFree` | 11:PC, 12:R | Classical.choice, Quot.sound, propext | `ccfbcdb87a1594c78fe86ba44b5bf33cf516f9b491ac30fa1f36042709f5c7f6` | `6361a81634435ae96c103fc150006dcb9d1e3dc01b84f518a01da37cb8e62e50` (46) |
| `Toy.UB.undef_unswitch_without_freeze_sound` | 12:R | Classical.choice, Quot.sound, propext | `c05978119f4ae2ed30f9dac4bdded7cd781ab7f649632c978f98d71e084f3f54` | `6c2fb642f92b904e50efa90d43f4bced91353793c1d197d2fef8a7f1e2d26d4f` (45) |
| `Toy.UB.undef_unswitch_without_freeze_needs_ubFree` | 12:CE | Classical.choice, Quot.sound, propext | `b3f03f63a3b2a761a3c158e877bab4e4e85bdc5f38da9ca7a7e626cd17df3617` | `6361a81634435ae96c103fc150006dcb9d1e3dc01b84f518a01da37cb8e62e50` (46) |
| `Toy.UB.nonvacuity_undef_unswitch_of_ubFree` | 12:NV | Classical.choice, Quot.sound, propext | `1926679b5793fc7618cb94b7dbad066772edd914edc1b10a1514b16ff1a159e0` | `6361a81634435ae96c103fc150006dcb9d1e3dc01b84f518a01da37cb8e62e50` (46) |
| `Toy.UB.nonvacuity_undef_unswitch` | 12:NV | Classical.choice, Quot.sound, propext | `073d83e03a3f190e7aafe41deca9180022dba032e280ec955a8f7f548d202396` | `6c2fb642f92b904e50efa90d43f4bced91353793c1d197d2fef8a7f1e2d26d4f` (45) |
| `Toy.UB.undef_unswitch_vars_outRef_all_envs` | 12:S | Classical.choice, Quot.sound, propext | `15de9f9cc57ee664ef6c70474bbc0ad01ceed244664b317d9e084ee0785eb6c1` | `4e2dcb9d42844c2b141db7d941bd3c0a0c68778ea5fbb65da628dbb4554f8508` (42) |
| `Toy.UB.undef_unswitch_empty_input_target_has_no_outcomes` | 12:S, 22:CE | Classical.choice, Quot.sound, propext | `4bd5614b61208a2af48ec4a625ad620c7a8ce1e3c3e7f916fbc43ceb9a83b8d2` | `8501987fa210f8113cbf108045a38c482c55d3d15b89220ba03f304980e895e5` (45) |
| `Toy.UB.ubFreeU_examples` | 12:S | Classical.choice, Quot.sound, propext | `d9041ebfd1f57ecfb221f836dd0917573eccbb6f8e8179ec0343ac14de4c2cf8` | `078ba905f7bf082ec3900d004ed97590d7fa733cc60c2178f36dc0407bd22b15` (39) |
| `Toy.UB.poisonFreeze_unswitch_with_freeze_sound_of_fresh` | 13:R | Quot.sound, propext | `bc14fd093c80d843dae011fd28fe8fae3c49725de6820d89584503748ee87ac2` | `01c9c31298077543352a82b194f09a0bac17d73bfc31863020b8f9682fd468f1` (53) |
| `Toy.UB.poisonFreeze_unswitch_with_freeze_needs_ubFree` | 13:CE | propext | `d74623adfd3d938cbef9f15ce4c84e711608a034e1a2434705989ed2f8743511` | `278ddc45bf4eae05df96d44114f5ff2bdbf19ff72616feffe36955620b3e5c0f` (54) |
| `Toy.UB.poisonFreeze_unswitch_with_freeze_needs_ubFree_branch` | 13:CE | propext | `75e66f747b606482dea199e0a395c10f7be550bec66e470443d16dcfff86d25c` | `278ddc45bf4eae05df96d44114f5ff2bdbf19ff72616feffe36955620b3e5c0f` (54) |
| `Toy.UB.poisonFreeze_unswitch_with_freeze_needs_t_not_free_in_cond` | 13:CE | propext | `94fbfd02c6699e92f6cc6aa9907a142e5775b3ff921158f580885eec79f323b9` | `278ddc45bf4eae05df96d44114f5ff2bdbf19ff72616feffe36955620b3e5c0f` (54) |
| `Toy.UB.poisonFreeze_unswitch_with_freeze_needs_t_not_free_in_a` | 13:CE | propext | `88a95f79f117711d8fa9cca6f4e288d320aba2d071203dcfab4c9f86313c8711` | `278ddc45bf4eae05df96d44114f5ff2bdbf19ff72616feffe36955620b3e5c0f` (54) |
| `Toy.UB.poisonFreeze_unswitch_with_freeze_needs_t_not_free_in_b` | 13:CE | propext | `ab92659000087f12672afa159fd0cb77dbc2efbcf7941b461269bcac81c02e97` | `278ddc45bf4eae05df96d44114f5ff2bdbf19ff72616feffe36955620b3e5c0f` (54) |
| `Toy.UB.poisonFreeze_unswitch_with_freeze_needs_t_not_free_in_e` | 13:CE | propext | `e550f1cf34d80cbcf749b5ccd24768d1e281e8a97a3c8400624f7a4ee9b58282` | `278ddc45bf4eae05df96d44114f5ff2bdbf19ff72616feffe36955620b3e5c0f` (54) |
| `Toy.UB.nonvacuity_poisonFreeze_unswitch_of_ubFree` | 13:NV | Quot.sound, propext | `acb032991da6d2d6788ca0f027946080bd34de332d062e27ca61648c679ad159` | `278ddc45bf4eae05df96d44114f5ff2bdbf19ff72616feffe36955620b3e5c0f` (54) |
| `Toy.UB.nonvacuity_poisonFreeze_unswitch` | 13:NV | (none) | `8b0fcfd90cb314b00c51d84a42d20818fe34246d3050218bc3a5b1570b001244` | `f83bcf214193e8e3c4dff8c783147d8d117d44da7de68d903d2c63e1b2f8f633` (19) |
| `Toy.UB.ubFreeP_examples` | 13:S | Quot.sound, propext | `cc03f3a2f38c72f553bd054548e147491af0ecd004bf615c72b02d898fbd217d` | `2b2c9e9c16030e0e116dca863b7bb2e0bf359a35406512eaef7c8e45c57e24ab` (43) |
| `Toy.UB.ubFreeP_eq_var` | 13:S | Quot.sound, propext | `bc9696696a29f0d8e1b2db93dffa279b2051d84d3e9905c10618d6821eef61ca` | `2b2c9e9c16030e0e116dca863b7bb2e0bf359a35406512eaef7c8e45c57e24ab` (43) |
| `Toy.UB.poisonFreeze_freeze_eq_self_of_no_poison` | 14:R | propext | `3202c38a35f3fc892acf1a063cbe812aabc130d798bfe38b7c67bc593c797111` | `ac375665ca7c6700ba79f0b8d5c04a7ca8ada29e8f77f812ea20ecdc0921ed18` (40) |
| `Toy.UB.poisonFreeze_remove_freeze_sound_of_no_poison` | 14:R, 16:PC | propext | `b55c621936083d023d150e209c9c1677df494032a9d97fe55e028183ade1181b` | `d0d68551a59122d2bfccda1215e027af4230dfeaf382fee1d0ba51671ea82b66` (50) |
| `Toy.UB.poisonFreeze_remove_redundant_freeze_sound` | 14:R, 16:PC | Quot.sound, propext | `ec08398bdfb59338922142c6fcb57453246a6429513b58ab29012c726b6fb171` | `d0d68551a59122d2bfccda1215e027af4230dfeaf382fee1d0ba51671ea82b66` (50) |
| `Toy.UB.undef_remove_redundant_freeze_sound` | 14:R, 16:PC | Classical.choice, Quot.sound, propext | `b9688c8694f1e4b889d483a93dad376388202b590c42642143f01bd46bddad9d` | `6c2fb642f92b904e50efa90d43f4bced91353793c1d197d2fef8a7f1e2d26d4f` (45) |
| `Toy.UB.poisonFreeze_freeze_eq_self_needs_no_poison` | 14:CE | Quot.sound, propext | `c092218bf122232d6c4d8592fddc906ef31d37b865683e1630fdde5f4fa83520` | `ac375665ca7c6700ba79f0b8d5c04a7ca8ada29e8f77f812ea20ecdc0921ed18` (40) |
| `Toy.UB.poisonFreeze_remove_freeze_needs_no_poison` | 14:CE | Quot.sound, propext | `6581fa62c0c8637970195f11e8182602a5065eead832f634364277848cffc3b0` | `d0d68551a59122d2bfccda1215e027af4230dfeaf382fee1d0ba51671ea82b66` (50) |
| `Toy.UB.nonvacuity_freeze_eq_self` | 14:NV | propext | `1fb7a3f1ce09b98322d4d8865ac7a2de4aed107892e4d785102f8adc3077dae5` | `ac375665ca7c6700ba79f0b8d5c04a7ca8ada29e8f77f812ea20ecdc0921ed18` (40) |
| `Toy.UB.nonvacuity_remove_redundant_freeze` | 14:NV | Classical.choice, Quot.sound, propext | `d7ff3bcdc46db70b9ff3c650de8ca41842c2feba2464314c54e643b306664a61` | `88a7e1584f47bc01303b591146188c19e96b49c40655319bb16b3e32d053d2a0` (61) |
| `Toy.UB.poisonFreeze_insert_freeze_sound` | 15:R | Quot.sound, propext | `f832c94a90943cc0c87fddbd4d183431ffcda05ec398c031c17c70c5241c600c` | `d0d68551a59122d2bfccda1215e027af4230dfeaf382fee1d0ba51671ea82b66` (50) |
| `Toy.UB.undef_insert_freeze_sound` | 15:R | Classical.choice, Quot.sound, propext | `3be608098987a1cc996d4056dabec656d01eb4499114f441c19b2e0d7d416e7a` | `6c2fb642f92b904e50efa90d43f4bced91353793c1d197d2fef8a7f1e2d26d4f` (45) |
| `Toy.UB.nonvacuity_insert_freeze` | 15:NV | Classical.choice, Quot.sound, propext | `5fb4e87a9085c69a8a9d997baf9cd7ac6fa31bc9db4f6e3d0a97de660cb8e334` | `88a7e1584f47bc01303b591146188c19e96b49c40655319bb16b3e32d053d2a0` (61) |
| `Toy.UB.poisonFreeze_remove_freeze_unsound` | 16:R | Quot.sound, propext | `43ab59d3e45306b4ecf7e2a56ad9853e66854970ddbf54972af031cddae2df33` | `d0d68551a59122d2bfccda1215e027af4230dfeaf382fee1d0ba51671ea82b66` (50) |
| `Toy.UB.undef_remove_freeze_unsound` | 16:R | Classical.choice, Quot.sound, propext | `73dd5542ba6dc9ac23ee375605462feb97906949bb87ddf161fe0dd2135f19b3` | `6c2fb642f92b904e50efa90d43f4bced91353793c1d197d2fef8a7f1e2d26d4f` (45) |
| `Toy.UB.undef_remove_freeze_unsound_needs_width` | 16:CE | Classical.choice, Quot.sound, propext | `41da55c6f95cfc341ea5f250a788021d8911daf5d124c1424a8a700b9ca4d7f6` | `6c2fb642f92b904e50efa90d43f4bced91353793c1d197d2fef8a7f1e2d26d4f` (45) |
| `Toy.UB.nonvacuity_remove_freeze_unsound` | 16:NV | Classical.choice, Quot.sound, propext | `e8b628eebd17134e0a970e72da1f476bd1464362f173888ad3a5d842eb8dc710` | `88a7e1584f47bc01303b591146188c19e96b49c40655319bb16b3e32d053d2a0` (61) |
| `Toy.UB.undef_remove_freeze_sound_width_zero` | 16:PC | Classical.choice, Quot.sound, propext | `fede4121a069f2903c897ab261638f6b5bb19d7067837b022fedd1b53b2e5ae0` | `6c2fb642f92b904e50efa90d43f4bced91353793c1d197d2fef8a7f1e2d26d4f` (45) |
| `Toy.UB.poisonFreeze_let_freeze_add_self_nonempty_even` | 17:R, 18:S | Quot.sound, propext | `1415b4ac90e0cdbc031d31087a94bafc465f84500a75704217c8390c9f56edfa` | `ac375665ca7c6700ba79f0b8d5c04a7ca8ada29e8f77f812ea20ecdc0921ed18` (40) |
| `Toy.UB.poisonFreeze_freeze_add_freeze_all_values_of_poison` | 17:R | Quot.sound, propext | `74227dab91baeb3ee4f4d7771b90fdb198cfac522c22f0c879b6d8e5b346edb6` | `ac375665ca7c6700ba79f0b8d5c04a7ca8ada29e8f77f812ea20ecdc0921ed18` (40) |
| `Toy.UB.poisonFreeze_freeze_add_freeze_can_be_odd` | 17:R, 18:S | Quot.sound, propext | `747ba9abea4aeec361ed9daf09b61e030d227242d887e666879c0a8dde99d133` | `ac375665ca7c6700ba79f0b8d5c04a7ca8ada29e8f77f812ea20ecdc0921ed18` (40) |
| `Toy.UB.poisonFreeze_freeze_add_freeze_can_be_odd_needs_width` | 17:CE | Quot.sound, propext | `80bd7fc3971c57e243934e658faf64b26238c11fee2fa7fccb3e6def672297b9` | `ac375665ca7c6700ba79f0b8d5c04a7ca8ada29e8f77f812ea20ecdc0921ed18` (40) |
| `Toy.UB.nonvacuity_let_freeze_mem` | 17:NV | Quot.sound, propext | `ecdce1040b4eeb19087e5b73794f680dda543056838f9522eb95617eeee50edd` | `17b646de8adfddecabb78f12a20335a1b585603072e1d607d7310456c643c4a0` (41) |
| `Toy.UB.poisonFreeze_duplicate_freeze_unsound` | 18:R | Quot.sound, propext | `08dbb7ff073c15d8c69cdca6bf3efdc773b14630151d12937cd921ae579b244c` | `d0d68551a59122d2bfccda1215e027af4230dfeaf382fee1d0ba51671ea82b66` (50) |
| `Toy.UB.poisonFreeze_duplicate_freeze_unsound_needs_width` | 18:CE | Quot.sound, propext | `bf3276e06314b4fe7ea9d45b992500fcafc5540d7366fe4e5a7f6779c125624d` | `d0d68551a59122d2bfccda1215e027af4230dfeaf382fee1d0ba51671ea82b66` (50) |
| `Toy.UB.nonvacuity_duplicate_freeze_unsound` | 18:NV | Quot.sound, propext | `3d88b281c7ee67535edfc88573ee4353d3a1dcfbc621ccf608f22c941f215539` | `d0d68551a59122d2bfccda1215e027af4230dfeaf382fee1d0ba51671ea82b66` (50) |
| `Toy.UB.poisonFreeze_duplicate_freeze_sound_width_zero` | 18:PC | Quot.sound, propext | `b29a7facc2130ab635b74c51b33688e869d3b39ce70db54e52c875a18638e3e2` | `d0d68551a59122d2bfccda1215e027af4230dfeaf382fee1d0ba51671ea82b66` (50) |
| `Toy.UB.poisonFreeze_merge_freeze_sound` | 18:PC, 19:R | Quot.sound, propext | `31d4cddcbdfc3ad77fbcf55e536ce6b0928e78fce87ce84cbddb772ccd324d17` | `d0d68551a59122d2bfccda1215e027af4230dfeaf382fee1d0ba51671ea82b66` (50) |
| `Toy.UB.poisonFreeze_duplicate_freeze_sound_at_int` | 18:PC | Quot.sound, propext | `c7561d3299a67c74dd59e35fff553e8a83451bc745a97dd60b28f9e516e94c92` | `c138bb6ad1bf08a4dd09440461bd2a48b89e446978474d00467772056176054a` (49) |
| `Toy.UB.poisonFreeze_duplicate_freeze_of_nonpoison_compound_unsound` | 18:S | Quot.sound, propext | `345c8be828455b25755bf79241a9ce205c9ad8647e902a7d62fcdd07ff28b109` | `d0d68551a59122d2bfccda1215e027af4230dfeaf382fee1d0ba51671ea82b66` (50) |
| `Toy.UB.nonvacuity_merge_freeze` | 19:NV | Quot.sound, propext | `fc03815166c990a2f40fca8a5d2802b6528de4bc89bf81a5cda7959b8d89b70d` | `d0d68551a59122d2bfccda1215e027af4230dfeaf382fee1d0ba51671ea82b66` (50) |
| `Toy.UB.poisonFreeze_partial_merge_freeze_unsound` | 19:S | Quot.sound, propext | `a8b5149a5f77cb8ee358bc2ee277feefc8b9b77dca1e624ce20ff95c5208428e` | `d0d68551a59122d2bfccda1215e027af4230dfeaf382fee1d0ba51671ea82b66` (50) |
| `Toy.UB.poison_refines_eagerUninit_eq` | 20:R | Quot.sound, propext | `3f19d32c67ca690c282c273978d5f3307afa1271942efc1bc7ca205b64c42158` | `ea69e4f39d02d27e3f12d0af361afe9fb2dbcec6d2db9f60f573bed491e1af4f` (54) |
| `Toy.UB.poison_refines_eagerUninit` | 20:R | Quot.sound, propext | `e38585dac376648ebf13bb3cf4bbb7be6071ef710187b8e4c302cb3bc55a996d` | `b023163ec58822b8d2828e1294a84c2f5a0f177947aca42fd83d99634795a596` (56) |
| `Toy.UB.nonvacuity_poison_refines_eagerUninit_live` | 20:NV | propext | `2a19cfe49379b4e60d098c540609a4923b1aa6b0a976a034c24e7698788a895e` | `ea69e4f39d02d27e3f12d0af361afe9fb2dbcec6d2db9f60f573bed491e1af4f` (54) |
| `Toy.UB.nonvacuity_poison_refines_eagerUninit` | 20:NV | Quot.sound, propext | `3d35f9660c6c6a0d38e50e7d7d5a8240a098d682ddc343efdeca7ff03cd28356` | `b023163ec58822b8d2828e1294a84c2f5a0f177947aca42fd83d99634795a596` (56) |
| `Toy.UB.semE_spec` | 20:S | Quot.sound, propext | `ce6d3f39e8819ac2096b0998708e7f3bacaa2937f33e7147c31b12a5b1e79b72` | `6a444c28024c5cddfaf14c1dfd83144f24c9958251438e0f147e3525d8531b66` (45) |
| `Toy.UB.dead_read_insertion_poison_sound_eager_unsound` | 20:S | propext | `00ba0c65741ee7d312a9f22be5bafd1db5ba88aa2bc112a30be29931fcc2a534` | `5fc5c3d99831c178120e4f06e1142560c0aed3641894979388df9450971739ac` (55) |
| `Toy.UB.mul_zero_to_branch_eager_sound_poison_unsound` | 20:S | Quot.sound, propext | `a4cf280a1d8e549149ee7311528362797e94f0e212ae62d3dc8975d150cc083e` | `5fc5c3d99831c178120e4f06e1142560c0aed3641894979388df9450971739ac` (55) |
| `Toy.UB.outRef_mono_rel` | 20:S | propext | `35ef316965f0eb6000764d8ed7dcf552c748887fbf97196c0235c8a4c6a7ee38` | `4c255668d4044dbb6026d961856a8d1773f989e9d0ecdcb9fd1d703002bed118` (13) |
| `Toy.UB.eagerUninit_not_refines_poison` | 21:R, 21:NV | propext | `96c144bf5cc1cbe01d5352ac0628e34577814c621971b6862bc5c92247ae6b50` | `b023163ec58822b8d2828e1294a84c2f5a0f177947aca42fd83d99634795a596` (56) |
| `Toy.UB.nonvacuity_semantics_total` | 22:NV | Classical.choice, Quot.sound, propext | `caa48ff715df3ff72c184ec7ca226eababc35307468d4979f442683c989ff2b1` | `537cc12feae2c833b1407bb0cb9b88235cfa19333a9a9668d7de7230c259ed0d` (56) |

150 names carry recorded hashes.

**Other cited names** (definitions, definition examples, supporting theorems and theorems named in prose; existence and axioms are re-checked by `lean/RevalidationAudit.lean`, but no hash is recorded):

| Lean name | Kind | Axioms |
|---|---|---|
| `Toy.UB.Expr` | inductive | (none) |
| `Toy.UB.Expr.FreezeFree` | def | (none) |
| `Toy.UB.Expr.freeIn` | def | (none) |
| `Toy.UB.Expr.freeIn_example_neg` | theorem | (none) |
| `Toy.UB.Expr.freeIn_example_pos` | theorem | (none) |
| `Toy.UB.Expr.freezeFree_example_neg` | theorem | (none) |
| `Toy.UB.Expr.freezeFree_example_pos` | theorem | (none) |
| `Toy.UB.MayUB` | def | (none) |
| `Toy.UB.ObsRefinesU` | def | Classical.choice, Quot.sound, propext |
| `Toy.UB.ObsU` | def | (none) |
| `Toy.UB.OutRef` | def | propext |
| `Toy.UB.OutRefNE` | def | propext |
| `Toy.UB.Outcome` | inductive | (none) |
| `Toy.UB.Outcome.LeVal` | def | propext |
| `Toy.UB.Outcome.isUB` | def | (none) |
| `Toy.UB.Outcome.toP` | def | (none) |
| `Toy.UB.PVal` | inductive | (none) |
| `Toy.UB.PVal.Refines` | def | (none) |
| `Toy.UB.PVal.lift2` | def | propext |
| `Toy.UB.PVal.refines_example_neg` | theorem | (none) |
| `Toy.UB.PVal.refines_example_pos` | theorem | (none) |
| `Toy.UB.RefinesE` | def | propext |
| `Toy.UB.RefinesP` | def | propext |
| `Toy.UB.RefinesU` | def | Classical.choice, Quot.sound, propext |
| `Toy.UB.UBFreeP` | def | propext |
| `Toy.UB.UBFreeU` | def | Classical.choice, Quot.sound, propext |
| `Toy.UB.UInhabited` | def | (none) |
| `Toy.UB.USet` | abbrev | (none) |
| `Toy.UB.USet.HasNonzero` | def | Classical.choice, Quot.sound, propext |
| `Toy.UB.USet.Nonempty` | def | (none) |
| `Toy.UB.USet.Sub` | def | (none) |
| `Toy.UB.USet.hasNonzero_examples` | theorem | Classical.choice, Quot.sound, propext |
| `Toy.UB.USet.map2` | def | Classical.choice, Quot.sound, propext |
| `Toy.UB.USet.map2_example_neg` | theorem | Classical.choice, Quot.sound, propext |
| `Toy.UB.USet.map2_example_pos` | theorem | Classical.choice, Quot.sound, propext |
| `Toy.UB.USet.nonempty_examples` | theorem | (none) |
| `Toy.UB.USet.single` | def | (none) |
| `Toy.UB.USet.sub_examples` | theorem | Quot.sound, propext |
| `Toy.UB.Var` | abbrev | (none) |
| `Toy.UB.allBV` | def | (none) |
| `Toy.UB.bind1` | def | (none) |
| `Toy.UB.bind2` | def | (none) |
| `Toy.UB.eqBit` | def | (none) |
| `Toy.UB.eqBit_examples` | theorem | (none) |
| `Toy.UB.leVal_examples` | theorem | propext |
| `Toy.UB.mayUB_examples` | theorem | (none) |
| `Toy.UB.obsRefinesU_examples` | theorem | Classical.choice, Quot.sound, propext |
| `Toy.UB.obsU_examples` | theorem | (none) |
| `Toy.UB.outRef_example_empty_target` | theorem | propext |
| `Toy.UB.outRef_example_neg` | theorem | propext |
| `Toy.UB.outRef_example_pos` | theorem | propext |
| `Toy.UB.outRef_example_pos_defined` | theorem | propext |
| `Toy.UB.outcome_toP_examples` | theorem | (none) |
| `Toy.UB.refinesE_examples` | theorem | propext |
| `Toy.UB.semE` | def | (none) |
| `Toy.UB.semE_examples` | theorem | (none) |
| `Toy.UB.semE_freeze_uninit_example` | theorem | propext |
| `Toy.UB.semP` | def | propext |
| `Toy.UB.semP_example_freeze` | theorem | propext |
| `Toy.UB.semP_example_neg` | theorem | propext |
| `Toy.UB.semP_example_pos` | theorem | propext |
| `Toy.UB.semP_freezeFree_singleton` | theorem | Quot.sound, propext |
| `Toy.UB.semP_mono` | theorem | Quot.sound, propext |
| `Toy.UB.semU` | def | Classical.choice, Quot.sound, propext |
| `Toy.UB.semU_example_branch` | theorem | Classical.choice, Quot.sound, propext |
| `Toy.UB.semU_example_neg` | theorem | Classical.choice, Quot.sound, propext |
| `Toy.UB.semU_example_pos` | theorem | Classical.choice, Quot.sound, propext |
| `Toy.UB.semU_ite_commits_example` | theorem | Classical.choice, Quot.sound, propext |
| `Toy.UB.semU_mono` | theorem | Classical.choice, Quot.sound, propext |
| `Toy.UB.toPoisonEnv` | def | (none) |
| `Toy.UB.toPoisonEnv_examples` | theorem | (none) |
| `Toy.UB.uEmptyD` | def | (none) |
| `Toy.UB.uInhabited_examples` | theorem | propext |
| `Toy.UB.update` | def | (none) |
| `Toy.UB.ρ01` | def | (none) |
| `Toy.UB.ρP` | def | (none) |

The constructors of the inductive types `Toy.UB.Expr` (`var`, `const`, `add`, `mul`, `eq`, `ite`,
`letE`, `freeze`, `ub`), `Toy.UB.Outcome` (`ub`, `val`) and `Toy.UB.PVal` (`poison`, `int`), which are
quoted with their types under **Definitions** and used throughout the statements, are also
re-checked by `lean/RevalidationAudit.lean`; none uses an axiom.

### Primary sources

Each source below was consulted on 2026-11-20 at the location given; bibliographic data
(title, authors, venue, pages) were checked against the DOI registration metadata (Crossref,
or DataCite for the LIPIcs paper), and the quoted passages against the full text named.

- **LLVM Language Reference Manual, LLVM 19.1.0 release documentation.**
  https://releases.llvm.org/19.1.0/docs/LangRef.html, built from `llvm/docs/LangRef.rst` at
  tag `llvmorg-19.1.0` of `llvm/llvm-project` (commit
  `a4bf6cd7cfb1a1421ba92bca9d017b49936c55e4`); every quotation below was also found in that
  file at that commit. Sections and passages used:
  - *Undefined Values*: "Branching on an undefined value is undefined behavior. This explains
    optimizations that depend on branch conditions to construct predicates, such as Correlated
    Value Propagation and Global Value Numbering."; and, in the example discussion of the same
    section, "undefined 'select' (and conditional branch) conditions can go either way, but
    they have to come from one of the two operands".
  - *Poison Values*: "Most instructions return 'poison' when one of their arguments is
    'poison'."; "It is correct to replace a poison value with an undef value or any value of
    the type."; the list of operands on which poison triggers immediate undefined behavior
    includes "The condition operand of a br instruction" and the parameter and return
    operands in `noundef` positions.
  - *Parameter Attributes, `noundef`*: "If the value representation contains any undefined or
    poison bits, the behavior is undefined."
  - *'freeze' Instruction*: "If the argument is undef or poison, 'freeze' returns an arbitrary,
    but fixed, value of type 'ty'. Otherwise, this instruction is a no-op and returns the input
    argument. All uses of a value returned by the same 'freeze' instruction are guaranteed to
    always observe the same value, while different 'freeze' instructions may yield different
    values."; example lines `%z = add i32 %x, %x ; even number because all uses of %x observe
    the same value` and `%cmp = icmp eq i32 %x, %x2 ; can be true or false`.
- **Lee, Kim, Song, Hur, Das, Majnemer, Regehr, Lopes.** "Taming Undefined Behavior in LLVM."
  PLDI 2017, pp. 633–647. DOI 10.1145/3062341.3062343. Quotations checked in the authors' PDF
  (https://web.ist.utl.pt/nuno.lopes/pubs/undef-pldi17.pdf): Sections 3.1, 3.3, 4, 5.1, 5.5,
  6, 7.2 and 9 as cited on the cards. Page numbers are proceedings pages, counting the first page of
  the 15-page PDF as p. 633.
- **Lopes, Lee, Hur, Liu, Regehr.** "Alive2: Bounded Translation Validation for LLVM." PLDI
  2021, pp. 65–79. DOI 10.1145/3453483.3454030. Checked in the open PDF
  (https://users.cs.utah.edu/~regehr/alive2-pldi21.pdf): Section 5 ("The definition above
  ensures compositionality: if a function's inputs are refined, so are the outputs."),
  Sections 5.1 (Figure 4) and 5.2, Figure 2.
- **Zakowski, Beck, Yoon, Zaichuk, Zaliva, Zdancewic.** "Modular, Compositional, and
  Executable Formal Semantics for LLVM IR." Proc. ACM Program. Lang. 5 (ICFP), Article 67,
  2021. DOI 10.1145/3473572. Article number and the Section 5 heading ("VIR Equivalences and
  Refinement") checked in the authors' PDF
  (https://cambium.inria.fr/~yzakowsk/papers/vellvm-design.pdf).
- **Bhat, Keizer, Hughes, Goens, Grosser.** "Verifying Peephole Rewriting in SSA Compiler
  IRs." ITP 2024, LIPIcs vol. 309, Article 9. DOI 10.4230/LIPIcs.ITP.2024.9 (preprint
  arXiv:2407.03685). Sections 4.1 and 6.1 as cited on the cards.
- **Lopes, Menendez, Nagarakatte, Regehr.** "Provably Correct Peephole Optimizations with
  Alive." PLDI 2015, pp. 22–32. DOI 10.1145/2737924.2737965.
- **Kang, Kim, Song, Lee, Park, Shin, Kim, Cho, Choi, Hur, Yi.** "Crellvm: Verified Credible
  Compilation for LLVM." PLDI 2018, pp. 631–645. DOI 10.1145/3192366.3192377.
- **Lobo, McIver, Mitenkov, Lee, Sundararajah, Lopes.** "Towards Removing Undef Values from
  LLVM IR." Proc. ACM Program. Lang. 10 (PLDI), Article 172, 2026. DOI 10.1145/3808250.
  Article number and the abstract sentence "this property makes even simple algebraic
  rewrites, such as replacing 2 × y with y + y, unsound in LLVM" checked in the authors' PDF
  (https://web.ist.utl.pt/nuno.lopes/pubs/byte-type-pldi26.pdf); the DOI metadata lists no
  article number.
- **Memarian, Gomes, Davis, Kell, Richardson, Watson, Sewell.** "Exploring C Semantics and
  Pointer Provenance." Proc. ACM Program. Lang. 3 (POPL), Article 67, 2019. DOI
  10.1145/3290380. Cited only as contrast (it does not address uninitialised values).
- **The Rust Reference, Rust 1.83.0**, "Behavior considered undefined",
  https://doc.rust-lang.org/1.83.0/reference/behavior-considered-undefined.html: "An integer
  (i*/u*), floating point value (f*), or raw pointer must be initialized, i.e., must not be
  obtained from uninitialized memory."
- **Jung.** "'What The Hardware Does' is not What Your Program Does: Uninitialized Memory."
  Blog post, 14 July 2019, https://www.ralfj.de/blog/2019/07/14/uninit.html; the page carries
  later edits (notes dated 2022-11-17 and 2024-10-18). Read on 2026-11-20 together with its source,
  file `personal/_posts/2019-07-14-uninit.md` at revision
  `ad96fffd4618ba6e126cc16214a04cf3902f5d99` of https://git.ralfj.de/web.git (the latest
  revision of that file on that date). Passages used: "You can think of memory as storing an
  Option<u8> at every location." and "(In LLVM, this None corresponds to poison, which has the
  potential to replace undef entirely.)"

For Bhat et al., Lopes et al. (2015), Kang et al. and Memarian et al., and for the
section-level content of Zakowski et al. beyond its Section 5 heading, only the bibliographic
data were checked on 2026-11-20; the section-level descriptions on their cards were not
re-checked against the full texts on that date. Typographic quotation marks in quoted passages
are normalized to ASCII.

## Revalidation

Requirements: `elan` (so that `lake` uses the toolchain pinned in `lean/lean-toolchain`,
`leanprover/lean4:v4.34.1`) and `python3`. No network access is needed after the toolchain is
installed; the Lean project has no dependencies.

**Primary check (one command).** From the package directory:

```sh
python3 support/revalidate.py .
```

It copies `lean/` to a temporary directory (the package is not modified), runs `lake build`,
rejects any Lean source containing `sorry`, `admit`, `native_decide` or an `axiom`
declaration, and then elaborates an inline audit program that (1) computes, with Lean's
`collectAxioms`, the axioms of every declaration of the `ToyUB` library and fails if any uses
an axiom other than `propext`, `Classical.choice`, `Quot.sound`; and (2) for every Lean name
referenced by `results.json` (fields `lean`, `lean_names`, `nonvacuity_witness_lean`,
`positive_control_lean`, and hypothesis `counterexample`s) recomputes two SHA-256 hashes and
compares them with `audit/statements.json`:

- the **statement hash**: SHA-256 of `toString (repr ci.type)`, the Lean `repr` of the
  declaration's elaborated type;
- the **closure hash**: SHA-256 of the newline-joined, sorted list of entries
  `name : repr(type)` (plus ` := repr(value)` for non-theorems) for every constant of the
  `ToyUB` library reachable from the statement's type through types, definition bodies and
  inductive constructors (theorem bodies excluded). A change to any definition a statement
  depends on therefore changes its closure hash.

It prints `REVALIDATED` and exits with status 0 iff every check passes. Expected output ends
with `ok   axioms (490 declarations)`, `ok   statement hashes (150 hashed names; 0 referenced
names exist but carry no recorded hash)` and `REVALIDATED`.

**Manual equivalent.**

```sh
cd lean
lake build                              # builds library ToyUB; must succeed with no `sorry` warnings
lake env lean RevalidationAudit.lean    # prints `#print axioms` for every name cited in REPORT.md
```

`lean/RevalidationAudit.lean` is outside the library target (it is not built by `lake build`).
It imports `ToyUB` and issues `#print axioms` for every Lean name cited anywhere in
`REPORT.md` or `results.json` (239 names), including the definition examples, the supporting
theorems that carry no recorded hash, and the constructors of `Expr`, `Outcome` and `PVal`;
elaboration fails if any name is missing, and each printed line
must list only (a subset of) `propext`, `Classical.choice`, `Quot.sound`. The recorded
per-declaration axioms are in `audit/axioms.json`.

**Cheaper discriminating checks.** If only the Lean toolchain changes, re-running the primary
check is sufficient: a changed elaboration of any statement or definition shows up as a hash
mismatch even when the build succeeds. If a definition in `lean/ToyUB/` is edited, every card
whose closure includes it is stale; the closure hashes identify which. A passing revalidation
establishes only the kernel-checked statements; it does not re-check any modeling-bridge claim
or citation, which must be re-read against the sources listed under **Evidence**.
