# Fuel-indexed and fixpoint weakest preconditions for partial and total correctness (Lean 4 formalization)

## Summary

This package formalizes, in Lean 4 without Mathlib, how weakest preconditions defined by structural recursion on a fuel counter relate to weakest preconditions defined as greatest and least fixpoints, for partial and total correctness of an abstract small-step transition system. All 14 results are kernel-checked re-derivations (tier `T0`) stated in this vocabulary.

1. **`partial-fuel-equals-gfp`** — For every transition system, postcondition `Q` and state `s`, with no finite-branching, determinism or other assumption, `s` satisfies the partial-correctness fuel weakest precondition `wpFuel S n Q` at **every** fuel `n` if and only if it satisfies the greatest-fixpoint (coinductive) partial-correctness weakest precondition `wpGfp S Q`.
2. **`fixed-fuel-does-not-give-partial-correctness`** — For every fuel `n`, state `n` of `downToStuckSys` (a countdown on `Nat` whose last state is stuck) satisfies `wpFuel downToStuckSys n (fun _ => True)` but not `wpGfp`, so a partial-correctness proof at one fixed fuel is only a bounded-depth check.
3. **`fuel-monotonicity-opposite-directions`** — For fuels `n ≤ m`, `wpFuel S m Q s` implies `wpFuel S n Q s` (more fuel is a stronger partial-correctness claim) while `wpFuelTotal S n Q s` implies `wpFuelTotal S m Q s` (more fuel is a weaker total-correctness claim).
4. **`partial-fuel-n-reading`** — `wpFuel S n Q s` holds exactly when every run prefix from `s` of fewer than `n` steps ends in a state that satisfies `Q` if terminal and has a successor if not; prefixes of `n` or more steps are unconstrained and fuel `0` checks nothing.
5. **`total-fuel-n-reading`** — `wpFuelTotal S n Q s` holds exactly when `wpFuel S n Q s` holds and no run prefix from `s` has exactly `n` steps (so no state satisfies fuel `0`, and a terminal state needs fuel `1`).
6. **`total-fuel-sound-for-lfp`** — For every system (no branching assumption), if `wpFuelTotal S n Q s` holds for some fuel `n`, then `s` satisfies the least-fixpoint total-correctness weakest precondition `wpLfp S Q`, and hence also `wpGfp S Q`.
7. **`total-fuel-complete-under-finite-branching`** — If every non-terminal state reachable from `s` has its successors in a finite list (`FinitelyBranchingFrom S s`), then `wpLfp S Q s` implies `wpFuelTotal S n Q s` for some fuel `n` that depends on `s`; corollaries give `(∃ n, wpFuelTotal S n Q s) ↔ wpLfp S Q s` for globally finitely branching systems, deterministic systems and systems induced by a partial step function, and a König form from `wpGfp S Q s` plus the absence of infinite runs; the local, global finite-branching and König forms each imply the limited principle of omniscience, so they are not constructively provable in this generality.
8. **`unbounded-choice-no-uniform-fuel`** — In `countdownSys` (one countably infinite choice of a countdown length, then a countdown), the state `start` satisfies `wpLfp` and `wpGfp` for `fun _ => True` and has no infinite run, yet no single fuel `n` gives `wpFuelTotal countdownSys n (fun _ => True) start`: without finite branching, total correctness does not yield a fuel bound.
9. **`total-equals-partial-plus-termination`** — For every system (no branching assumption), `wpLfp S Q s ↔ wpGfp S Q s ∧ ¬ HasInfiniteRun S s`; the backward direction needs classical logic (the statement implies Markov's principle).
10. **`divergence-satisfies-every-partial-wp-and-no-total-wp`** — A state from which every run diverges without getting stuck (`AlwaysDiverges`) satisfies every partial-correctness weakest precondition (`wpFuel` at every fuel and `wpGfp`, for every postcondition) and no total-correctness one; a state with some infinite run (`HasInfiniteRun`) satisfies no total-correctness weakest precondition.
11. **`wpgfp-false-is-divergence`** — `wpGfp S (fun _ => False) s` holds exactly when every run from `s` diverges without getting stuck, and `s` satisfies `wpGfp S Q` for every `Q` exactly under the same condition.
12. **`positive-partial-wp-cannot-reject-divergent-state`** — If some state always diverges without getting stuck and a predicate `R` fails there, then `R` equals no positive partial-correctness weakest precondition over the same system and state space (`wpGfp S Q`, `wpFuel S n Q` at a fixed `n`, or `∀ n, wpFuel S n Q`, for any `Q`); in particular the liveness property "every run eventually reaches `P`" is not one whenever an always-diverging state violates it.
13. **`gfp-adequacy`** — `wpGfp S Q s` holds exactly when every finite run prefix from `s` ends in a state that satisfies `Q` if terminal and has a successor if not: greatest-fixpoint partial correctness is a property of finite run prefixes only.
14. **`fixpoint-definitions-adequate`** — Reference point: the impredicative definitions `wpGfp` and `wpLfp` are fixed points of the one-step operator `wpStep S Q`, `wpGfp` contains every post-fixed point (coinduction) and `wpLfp` is contained in every pre-fixed point (induction).

Each result has non-claims that rule out tempting stronger readings; they are listed first under **Boundaries**, card by card, and must be read together with the claims above.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

## Applicability

**What is modeled.** The package is a **toy model**. A `System σ` is an abstract small-step transition relation
`step : σ → σ → Prop` (possibly nondeterministic and infinitely branching) with a predicate `terminal : σ → Prop` of
halted states. It is meant to capture the operational semantics of a program or interpreter as used by a
verification framework that defines its weakest precondition either by structural recursion on a fuel counter
(`wpFuel`, `wpFuelTotal`) or as a fixpoint (`wpGfp`, `wpLfp`). Every result is stated for an arbitrary
`System σ` (or for a concrete toy system used as a counterexample or witness).
Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the
corresponding claims about the fuel-indexed or fixpoint weakest preconditions of any concrete language, interpreter or
verification framework (such as an Iris-style program logic); the `Basis: derived (modeling bridge)` paragraph below
states what a transfer would require.

**Conventions built into the definitions** (each tested by proved positive and negative examples in
`ToyFuelWP.Examples`):

* *Terminal states halt.* Every weakest precondition, every run notion (`Reach`, `HasInfiniteRun`,
  `AlwaysDiverges`, `AllRunsEventually`) and every branching notion (`FinitelyBranching*`, `Deterministic`) looks at
  successors only of non-terminal states; edges leaving terminal states are ignored. The raw helper `CanStep` sees
  such edges, and every use of it is guarded by `¬ S.terminal`.
* *Stuck states are errors.* `Stuck S s := ¬ S.terminal s ∧ ∀ t, ¬ S.step s t`; every weakest precondition rejects a
  reachable stuck state, and `wpLfp` obeys the law of the excluded miracle (`wpLfp_excluded_miracle`).
* *Demonic choice.* Every weakest precondition quantifies over all successors. (`wpStepAngelic` in
  `ToyFuelWP.Boundaries` exists only to show where the partial-correctness equivalence stops.)
* *Implications, not disjunctions.* `wpStep` and `RunEndOk` are written `(terminal → …) ∧ (¬ terminal → …)`. A
  disjunctive adequacy statement for all systems implies excluded middle (`em_of_disjunctive_adequacy`); the price
  is that, without classical logic or a decidable `terminal`, a total-correctness judgement yields only
  `¬¬ terminal` at the end of a run (`wpFuelTotal_propSys_one_iff_not_not`).
* *Fuel accounting.* One unit of fuel per step plus one final check: `wpFuel S 0 Q` is `True`, `wpFuelTotal S 0 Q`
  is `False`, and a terminal state needs total fuel `1`.

**Known gaps to real systems.** No program syntax, heap, concurrency, probabilistic choice, I/O events, traces or
fairness; fuel counts steps of the abstract relation, not loop iterations, calls or any concrete cost; nothing is
stated about an `Option`-returning interpreter `run : Nat → σ → Option σ` (only `ofStepFn`, which turns a partial
step function into a system); `wpStep` has the case structure of the weakest precondition of Iris-style program
logics but is not that operator (Iris tests value-hood computably, puts the recursive occurrence under update and
later modalities, and takes a guarded fixpoint); the greatest fixpoint here is an impredicative union of
post-fixed predicates on states, not interaction trees, the delay monad, step-indexed relations or Lean's
`partial_fixpoint` / `coinductive` facilities. Frameworks with blocking assumptions, miraculous commands, angelic
choice, or "terminal" states that continue are not covered.

Basis: derived (modeling bridge). Reasoning: every theorem quantifies over all `System σ`, so it applies to a
concrete semantics exactly to the extent that the semantics *is* such a relation with the same notions of terminal
and stuck states, the same demonic reading, and a fuel that counts the same steps. Establishing that
correspondence for any particular language, interpreter or framework is a separate argument that this package
does not make or check.

**Toolchain and dependencies.** Lean `leanprover/lean4:v4.34.1` (the toolchain subject in `REPORT.json`), core Lean
only: **no Mathlib**, no `Std` import, no `[[require]]` dependencies. Library `ToyFuelWP`, namespace `Toy.FuelWP`, all
results universe-polymorphic in the state type (`variable {σ : Type u}`) except the constructivity reductions,
which quantify over `σ : Type`.

**Relation among the subjects.** The Lean toolchain is the checker of every theorem. The cited papers are prior art
for the classical results that the cards restate (all results are tier `T0`, re-derivations); the package does not
formalize any of those papers' own systems.

**Modules.**

| module | content |
| :--- | :--- |
| `ToyFuelWP.Defs` | definitions; fixpoint adequacy lemmas; small helper lemmas |
| `ToyFuelWP.Systems` | concrete toy systems and facts about them |
| `ToyFuelWP.Divergence` | divergence and inexpressibility results |
| `ToyFuelWP.Examples` | positive and negative examples for every definition |
| `ToyFuelWP.Counterexamples` | tightness counterexamples, non-vacuity witnesses, positive controls |
| `ToyFuelWP.Boundaries` | results backing non-claims (escape hatches, excluded miracle, quantifier order, angelic contrast) |
| `ToyFuelWP.Constructivity` | reductions showing which statements need classical logic; constructive special cases |
| `ToyFuelWP.Statements` | the general fuel/fixpoint theorems and their corollaries |

## Findings

### Definitions (quoted verbatim from `ToyFuelWP.Defs`)

All definitions live in namespace `Toy.FuelWP` under `universe u` and `variable {σ : Type u}`. Theorems quoted from `section Basic` of `ToyFuelWP.Defs` additionally see `variable {S : System σ} {Q : σ → Prop}`: where such a statement mentions `S` or `Q` without binding it, that variable is an implicit argument. Doc comments are omitted; the sources carry them.

```lean
structure System (σ : Type u) where
  step : σ → σ → Prop
  terminal : σ → Prop

def CanStep (S : System σ) (s : σ) : Prop := ∃ t, S.step s t

def Stuck (S : System σ) (s : σ) : Prop := ¬ S.terminal s ∧ ∀ t, ¬ S.step s t

def wpStep (S : System σ) (Q X : σ → Prop) (s : σ) : Prop :=
  (S.terminal s → Q s) ∧ (¬ S.terminal s → CanStep S s ∧ ∀ t, S.step s t → X t)

def wpFuel (S : System σ) : Nat → (σ → Prop) → σ → Prop
  | 0, _ => fun _ => True
  | n + 1, Q => wpStep S Q (wpFuel S n Q)

def wpFuelTotal (S : System σ) : Nat → (σ → Prop) → σ → Prop
  | 0, _ => fun _ => False
  | n + 1, Q => wpStep S Q (wpFuelTotal S n Q)

def PostFixed (S : System σ) (Q X : σ → Prop) : Prop := ∀ s, X s → wpStep S Q X s

def PreFixed (S : System σ) (Q X : σ → Prop) : Prop := ∀ s, wpStep S Q X s → X s

def wpGfp (S : System σ) (Q : σ → Prop) (s : σ) : Prop :=
  ∃ X : σ → Prop, PostFixed S Q X ∧ X s

def wpLfp (S : System σ) (Q : σ → Prop) (s : σ) : Prop :=
  ∀ X : σ → Prop, PreFixed S Q X → X s

inductive Reach (S : System σ) : σ → Nat → σ → Prop
  | refl (s : σ) : Reach S s 0 s
  | step {s t u : σ} {k : Nat} :
      ¬ S.terminal s → S.step s t → Reach S t k u → Reach S s (k + 1) u

def RunEndOk (S : System σ) (Q : σ → Prop) (t : σ) : Prop :=
  (S.terminal t → Q t) ∧ (¬ S.terminal t → CanStep S t)

def HasInfiniteRun (S : System σ) (s : σ) : Prop :=
  ∃ f : Nat → σ, f 0 = s ∧ ∀ i, ¬ S.terminal (f i) ∧ S.step (f i) (f (i + 1))

def AlwaysDiverges (S : System σ) (s : σ) : Prop :=
  ∀ k t, Reach S s k t → ¬ S.terminal t ∧ CanStep S t

def FinitelyBranchingAt (S : System σ) (t : σ) : Prop :=
  ∃ l : List σ, ∀ u, S.step t u → u ∈ l

def FinitelyBranchingFrom (S : System σ) (s : σ) : Prop :=
  ∀ k t, Reach S s k t → ¬ S.terminal t → FinitelyBranchingAt S t

def FinitelyBranching (S : System σ) : Prop :=
  ∀ t, ¬ S.terminal t → FinitelyBranchingAt S t

def Deterministic (S : System σ) : Prop :=
  ∀ t, ¬ S.terminal t → ∀ u v, S.step t u → S.step t v → u = v

def ofStepFn (next : σ → Option σ) (halted : σ → Prop) : System σ where
  step s t := next s = some t
  terminal := halted

inductive AllRunsEventually (S : System σ) (P : σ → Prop) : σ → Prop
  | now {s : σ} : P s → AllRunsEventually S P s
  | later {s : σ} : ¬ S.terminal s → CanStep S s →
      (∀ t, S.step s t → AllRunsEventually S P t) → AllRunsEventually S P s
```

Unfolded once: `wpStep S Q X s` is `(S.terminal s → Q s) ∧ (¬ S.terminal s → (∃ t, S.step s t) ∧ ∀ t, S.step s t → X t)`; `wpGfp S Q s` is `∃ X, (∀ t, X t → wpStep S Q X t) ∧ X s` (some invariant contains `s`); `wpLfp S Q s` is `∀ X, (∀ t, wpStep S Q X t → X t) → X s`; `RunEndOk S Q t` is `(S.terminal t → Q t) ∧ (¬ S.terminal t → ∃ u, S.step t u)`. Hierarchy of the branching hypotheses (all proved): `Deterministic S → FinitelyBranching S` (`finitelyBranching_of_deterministic`, classical) and `FinitelyBranching S → FinitelyBranchingFrom S s` (`finitelyBranchingFrom_of_finitelyBranching`); both implications are strict (`spinOrExitSys_finitelyBranching_not_deterministic`; `finitelyBranchingFrom_pos_countdown_count` with `finitelyBranching_neg_countdown`, all quoted under Boundaries). The two implications, from `section Basic` of `ToyFuelWP.Defs` (so `S` is an implicit argument):

```lean
-- lean/ToyFuelWP/Defs.lean:372
-- ToyFuelWP.Defs
theorem finitelyBranching_of_deterministic (h : Deterministic S) : FinitelyBranching S

-- lean/ToyFuelWP/Defs.lean:366-367
-- ToyFuelWP.Defs
theorem finitelyBranchingFrom_of_finitelyBranching (h : FinitelyBranching S) (s : σ) :
    FinitelyBranchingFrom S s
```

Every core definition has proved positive and negative examples in `ToyFuelWP.Examples`. Four such pairs, verbatim (the toy systems are quoted in the next subsection):

```lean
-- lean/ToyFuelWP/Examples.lean:123
-- ToyFuelWP.Examples
theorem wpGfp_pos_loop_false : wpGfp loopSys (fun _ => False) ()

-- lean/ToyFuelWP/Examples.lean:147
theorem wpGfp_neg_error_far : ¬ wpGfp downToStuckSys (fun _ => True) 1000

-- lean/ToyFuelWP/Examples.lean:156
theorem wpLfp_pos_countdown : wpLfp countdownSys (fun _ => True) .start

-- lean/ToyFuelWP/Examples.lean:159
theorem wpLfp_neg_loop : ¬ wpLfp loopSys (fun _ => True) ()

-- lean/ToyFuelWP/Examples.lean:301
theorem deterministic_pos_termBranch : Deterministic termBranchSys

-- lean/ToyFuelWP/Examples.lean:304
theorem deterministic_neg_spinOrExit : ¬ Deterministic spinOrExitSys

-- lean/ToyFuelWP/Examples.lean:230
theorem alwaysDiverges_pos_spinOrOut : AlwaysDiverges spinOrOutSys .spin

-- lean/ToyFuelWP/Examples.lean:243
theorem alwaysDiverges_neg_error : ¬ AlwaysDiverges downToStuckSys 0
```

That is: the looping state satisfies the greatest-fixpoint partial-correctness weakest precondition even of `False`, while a run that reaches the stuck state after 1000 steps is rejected; unbounded choice followed by a countdown is totally correct, while the loop is not; a system whose only edges leave terminal states is deterministic, while `spinOrExitSys` (from `spin`, both `spin` and `out` are successors) is not; `spin` in `spinOrOutSys` always diverges, while state `0` of `downToStuckSys` is stuck and does not.

### Concrete toy systems (quoted verbatim from `ToyFuelWP.Systems`)

```lean
def loopSys : System Unit where
  step _ _ := True
  terminal _ := False

def doneSys : System Unit where
  step _ _ := False
  terminal _ := True

def stuckSys : System Unit where
  step _ _ := False
  terminal _ := False

def termLoopSys : System Unit where
  step _ _ := True
  terminal _ := True

def chainSys : System Nat where
  step s t := s = t + 1
  terminal s := s = 0

def downToStuckSys : System Nat where
  step s t := s = t + 1
  terminal _ := False

inductive CD where
  | start
  | count (k : Nat)

inductive CDStep : CD → CD → Prop
  | choose (k : Nat) : CDStep .start (.count k)
  | tick (k : Nat) : CDStep (.count (k + 1)) (.count k)

def countdownSys : System CD where
  step := CDStep
  terminal s := s = .count 0

inductive LO where
  | spin
  | out

def spinOrOutSys : System LO where
  step s t := s = .spin ∧ t = .spin
  terminal s := s = .out

def spinOrExitSys : System LO where
  step s _ := s = .spin
  terminal s := s = .out

def isOut (s : LO) : Prop := s = .out

def spinOrEmitLoopSys : System LO where
  step s t := s = t
  terminal _ := False

inductive LO3 where
  | start
  | spin
  | out

def startSpinOutSys : System LO3 where
  step s t := (s = .start ∧ t = .out) ∨ (s = .spin ∧ t = .spin)
  terminal s := s = .out

def isOut3 (s : LO3) : Prop := s = .out

def termBranchSys : System Bool where
  step _ _ := True
  terminal _ := True

def fanToStuckSys : System CD where
  step := CDStep
  terminal _ := False

def propSys (P : Prop) : System Unit where
  step _ _ := False
  terminal _ := P
```

The partial step function that card 7 turns into a system with `ofStepFn` (`ToyFuelWP.Examples`):

```lean
def predStep : Nat → Option Nat
  | 0 => none
  | k + 1 => some k
```

The angelic contrast operators `wpStepAngelic`, `wpFuelAngelic`, `wpGfpAngelic` (`ToyFuelWP.Boundaries`) and the principles `LimitedPrincipleOfOmniscience`, `MarkovPrinciple` (`ToyFuelWP.Constructivity`) are:

```lean
def wpStepAngelic (S : System σ) (Q X : σ → Prop) (s : σ) : Prop :=
  (S.terminal s → Q s) ∧ (¬ S.terminal s → ∃ t, S.step s t ∧ X t)

def wpFuelAngelic (S : System σ) : Nat → (σ → Prop) → σ → Prop
  | 0, _ => fun _ => True
  | n + 1, Q => wpStepAngelic S Q (wpFuelAngelic S n Q)

def wpGfpAngelic (S : System σ) (Q : σ → Prop) (s : σ) : Prop :=
  ∃ X : σ → Prop, (∀ t, X t → wpStepAngelic S Q X t) ∧ X s

def LimitedPrincipleOfOmniscience : Prop :=
  ∀ B : Nat → Bool, (∃ k, B k = true) ∨ ∀ k, B k = false

def MarkovPrinciple : Prop :=
  ∀ B : Nat → Bool, ¬ (∀ k, B k = false) → ∃ k, B k = true
```

### How to read "verified at fuel `n`"

| mode | fuel-0 value | direction in fuel | a proof at fuel `n` means | what it does **not** mean |
| :--- | :--- | :--- | :--- | :--- |
| partial (`wpFuel`) | `True` | antitone: more fuel is stronger | every run prefix of fewer than `n` steps ends in a state that satisfies `Q` if terminal and has a successor if not | anything about step `n` onwards; at `n = 0` nothing is checked, not even the initial state; partial correctness (`wpGfp`) needs **all** `n` |
| total (`wpFuelTotal`) | `False` | monotone: more fuel is weaker | `wpFuel n Q s` and no run prefix has exactly `n` steps; classically: every run halts error-free in `Q` after fewer than `n` steps (unsatisfiable at `n = 0`; a terminal state needs fuel 1) | that the fuel is minimal; failure at `n` does not refute total correctness (more fuel may succeed); one fuel need not work for all initial states; constructively only `¬¬ terminal` is obtained at the end of a run; the step count is of the abstract relation, not a concrete cost |

Partial correctness: `∀ n, wpFuel` = `wpGfp` for every system. Total correctness: `∃ n, wpFuelTotal` ⇒ `wpLfp`
always, ⇐ under (local) finite branching (with a per-state fuel, by classical reasoning), and fails without it.

### 1. `partial-fuel-equals-gfp`

- **Kind:** characterization
- **Tier:** `T0` — Known result restated in this vocabulary: the greatest fixpoint of an inf-continuous monotone operator is the meet of its finite iterates from the top predicate (the dual Kleene iteration theorem, mechanized for example as Isabelle/HOL inf_continuous_gfp). The package-specific observation is that wpStep, which quantifies universally over successors, satisfies this with no branching assumption.
- **Plain claim:** For every transition system, postcondition Q and state s, with no finite-branching, determinism or other assumption: s satisfies the partial-correctness fuel weakest precondition wpFuel n Q at every fuel n if and only if s satisfies the greatest-fixpoint partial-correctness weakest precondition wpGfp Q. Both directions are separate theorems (wpFuel_of_wpGfp, wpGfp_of_forall_wpFuel); the biconditional forall_wpFuel_iff_wpGfp is derived from them.
- **Depth:** `shallow`
- **Lean statement:**

```lean
-- lean/ToyFuelWP/Statements.lean:28-29
-- ToyFuelWP.Statements
theorem wpFuel_of_wpGfp (S : System σ) (Q : σ → Prop) (s : σ) (h : wpGfp S Q s) (n : Nat) :
    wpFuel S n Q s

-- lean/ToyFuelWP/Statements.lean:37-38
-- ToyFuelWP.Statements
theorem wpGfp_of_forall_wpFuel (S : System σ) (Q : σ → Prop) (s : σ)
    (h : ∀ n, wpFuel S n Q s) : wpGfp S Q s

-- lean/ToyFuelWP/Statements.lean:46-47
-- ToyFuelWP.Statements
theorem forall_wpFuel_iff_wpGfp (S : System σ) (Q : σ → Prop) (s : σ) :
    (∀ n, wpFuel S n Q s) ↔ wpGfp S Q s
```

- **Hypothesis ledger:**
  - `h : wpGfp S Q s (in wpFuel_of_wpGfp)` — the greatest-fixpoint judgement being converted to fuel form; wpFuel_of_wpGfp has no other hypothesis. Tightness: **tight**; counterexample: `stuckSys_not_wpGfp_not_wpFuel_one`.
  - `h : ∀ n, wpFuel S n Q s — every fuel (in wpGfp_of_forall_wpFuel)` — a single fixed fuel only checks run prefixes shorter than that fuel; dropping h (stuckSys) or weakening it to one fixed fuel (downToStuckSys) both break the conclusion. Tightness: **tight**; counterexample: `stuckSys_not_wpGfp_not_wpFuel_one`, `fixed_fuel_wpFuel_not_imp_wpGfp`.
- **Non-vacuity witness:** chainSys from 3 with postcondition (· = 0) (a halting run) and loopSys with postcondition False (a diverging run) satisfy both sides. (`nonvacuity_forall_wpFuel_and_wpGfp`)
- **Logic (`#print axioms`):** wpFuel_of_wpGfp: proved; #print axioms: no axioms; wpGfp_of_forall_wpFuel: proved; #print axioms: no axioms; forall_wpFuel_iff_wpGfp: proved; #print axioms: no axioms.
- **Results backing the non-claims:** `fanToStuckSys_angelic_forall_fuel_not_gfp`, `fixed_fuel_wpFuel_not_imp_wpGfp`.
- **Non-claims:** see Boundaries, card 1.
- **Prior art:**
  - S. Owens, M. O. Myreen, R. Kumar, Y. K. Tan. Functional big-step semantics. ESOP 2016, LNCS 9632, pp. 589–615. doi:10.1007/978-3-662-49498-1_23. Clocked (fuel-indexed) interpreters: evaluation diverges iff it times out for every initial clock value; the HOL4 development (HOL repository, examples/pl-semantics/for/forScript.sml, theorem simple_sem_t_div_iff_sem_t_div) proves this equals a coinductive divergence relation for a deterministic language — the closest mechanized analogue of the 'every fuel = coinductive' direction found.
  - Isabelle/HOL, HOL/Library/Order_Continuity.thy: lemma inf_continuous_gfp (gfp F = (INF i. (F ^^ i) top) for inf-continuous F) and lemma sup_continuous_lfp (lfp F = (SUP i. (F ^^ i) bot) for sup-continuous F) — mechanized Kleene-style iteration theorems; partial-fuel-equals-gfp is the instance for wpStep, which is inf-continuous with no branching assumption, while the least-fixpoint dual needs continuity that fails under unbounded branching.
  - Mathlib, Mathlib/Order/FixedPoints.lean (github.com/leanprover-community/mathlib4, master): OrderHom.lfp / OrderHom.gfp on a complete lattice, defined as the infimum of pre-fixed points / supremum of post-fixed points, with lfp_le, le_gfp, map_lfp, map_gfp and fixedPoints.completeLattice (Knaster–Tarski) — the same impredicative construction as wpLfp / wpGfp, in general form.
  - E. W. Dijkstra and C. S. Scholten. Predicate Calculus and Program Semantics. Springer, 1990. doi:10.1007/978-1-4612-3228-5. Chapter 8 'Equations in predicates and their extreme solutions' (pp. 147–170) and chapter 9 'Semantics of repetitions' (pp. 170–189). The characterization of wlp of a repetition as the weakest (greatest) solution and wp as the strongest (least) solution of the loop equation was verified only through a secondary source (I. M. Rewitzky, Modelling the Algebra of Weakest Preconditions, MSc thesis, Department of Mathematics, University of Cape Town, 1991), not in the book itself.
  - P. Cousot and R. Cousot. Constructive versions of Tarski's fixed point theorems. Pacific Journal of Mathematics 82(1):43–57, 1979. doi:10.2140/pjm.1979.82.43. Fixpoints of monotone maps via transfinite iteration without continuity, contrasted with the ω-iteration that needs continuity.
  - J.-L. Lassez, V. L. Nguyen, E. A. Sonenberg. Fixed point theorems and semantics: a folk tale. Information Processing Letters 14(3):112–116, 1982. doi:10.1016/0020-0190(82)90065-5. On the attribution of the fixed-point theorems used in semantics (bibliographic record verified; content not re-read here).
  - R. Jung, R. Krebbers, J.-H. Jourdan, A. Bizjak, L. Birkedal, D. Dreyer. Iris from the ground up: a modular foundation for higher-order concurrent separation logic. Journal of Functional Programming 28, e20, 2018. doi:10.1017/S0956796818000151. Section 6 defines a weakest precondition with the same case structure as wpStep (a value satisfies the postcondition; otherwise the expression is reducible and every successor satisfies the weakest precondition). It is not the same operator: in the Iris Coq library (iris/program_logic/weakestpre.v, definition wp_pre) value-hood is tested by the computable to_val, the recursive occurrence sits under fancy-update modalities (which quantify existentially over ghost-state updates) and later modalities, and wp is the guarded fixpoint of a contractive function.
  - X. Leroy and H. Grall. Coinductive big-step operational semantics. Information and Computation 207(2):284–304, 2009. doi:10.1016/j.ic.2007.12.004. Coinductive big-step semantics describing diverging as well as terminating evaluations; the accompanying Coq development proves equivalences between big-step and small-step semantics.
  - K. Nakata and T. Uustalu. Trace-based coinductive operational semantics for While. TPHOLs 2009, LNCS 5674, pp. 375–390. doi:10.1007/978-3-642-03359-9_26. Four coinductive trace-based semantics (big-/small-step, relational/functional) for terminating and nonterminating runs, proved equivalent in Coq.
  - L. Xia, Y. Zakowski, P. He, C.-K. Hur, G. Malecha, B. C. Pierce, S. Zdancewic. Interaction trees: representing recursive and impure programs in Coq. Proc. ACM Program. Lang. 4(POPL), article 51, 2020. doi:10.1145/3371119. A coinductive variant of free monads representing possibly nonterminating computations, with equivalence up to weak bisimulation; the coinductive alternative to fuel.
  - V. Capretta. General recursion via coinductive types. Logical Methods in Computer Science 1(2:1), 2005. doi:10.2168/LMCS-1(2:1)2005. The coinductive delay type of partial elements (return / add a step) — a coinductive alternative to fuel for representing possibly nonterminating computations.
  - N. A. Danielsson. Operational semantics using the partiality monad. ICFP 2012, pp. 127–138. doi:10.1145/2364527.2364546. Coinductive partiality monad for total definitional interpreters, in Agda — the coinductive counterpart of a fuel-indexed interpreter.
  - Lean 4 reference manual, recursive definitions: partial_fixpoint (introduced in Lean v4.17.0, leanprover/lean4 pull request 6355) defines functions as least fixpoints of monotone equations in chain-complete partial orders (for example Option-valued functions) and generates a partial-correctness theorem; lattice-theoretic least/greatest-fixpoint predicates (introduced in v4.20.0, pull request 8097; named inductive_fixpoint / coinductive_fixpoint from v4.23.0) use Knaster–Tarski on Prop with (co)induction principles. Source: github.com/leanprover/reference-manual, files Manual/RecursiveDefs/PartialFixpoint.lean and Manual/RecursiveDefs/CoinductivePredicates.lean. This package uses neither; its wpGfp and wpLfp are hand-written impredicative fixpoints.
  - Lean v4.25.0 release notes (github.com/leanprover/reference-manual, Manual/Releases/v4_25_0.lean): pull request leanprover/lean4#10333 introduces a coinductive keyword that defines coinductive predicates with the same syntax as inductive. The pinned toolchain v4.34.1 therefore offers coinductive predicates; this package does not use them, so that its definitions also make sense for a kernel without them.
- **Design question:** A verification framework whose trusted kernel forbids coinductive definitions and general recursion defines its weakest precondition by structural recursion on fuel. For which properties is that the same as the coinductive (greatest-fixpoint) definition, how should 'verified at fuel n' be read, and where do the two differ (total correctness, divergence, liveness)? This card: partial correctness is the same under both definitions provided the fuel statement is proved for all fuels, and this needs no branching assumption.
- Basis: execution (Lean kernel check) — `wpFuel_of_wpGfp`, `wpGfp_of_forall_wpFuel`, `forall_wpFuel_iff_wpGfp`, and every counterexample and witness named above, are theorems checked by the Lean kernel under `leanprover/lean4:v4.34.1` with the axioms listed.
- Basis: derived (modeling bridge) — for a framework whose semantics is faithfully modeled as a `System σ` with the conventions of Applicability and whose fuel counts the same steps: partial correctness is the same under both definitions provided the fuel statement is proved for all fuels, and this needs no branching assumption. Reasoning: the Lean statement is universally quantified over systems (or exhibits a concrete one), so it transfers through such a model; the faithfulness of any particular model is not checked here.
- **Statements of the counterexamples, witnesses and controls named on this card:**

```lean
-- lean/ToyFuelWP/Counterexamples.lean:34-35
-- ToyFuelWP.Counterexamples
theorem stuckSys_not_wpGfp_not_wpFuel_one :
    ¬ wpGfp stuckSys (fun _ => True) () ∧ ¬ wpFuel stuckSys 1 (fun _ => True) ()

-- lean/ToyFuelWP/Counterexamples.lean:24-27
-- ToyFuelWP.Counterexamples
theorem fixed_fuel_wpFuel_not_imp_wpGfp (n : Nat) :
    wpFuel downToStuckSys n (fun _ => True) n ∧
      ¬ (∀ m, wpFuel downToStuckSys m (fun _ => True) n) ∧
      ¬ wpGfp downToStuckSys (fun _ => True) n

-- lean/ToyFuelWP/Counterexamples.lean:42-44
-- ToyFuelWP.Counterexamples
theorem nonvacuity_forall_wpFuel_and_wpGfp :
    ((∀ n, wpFuel chainSys n (fun s => s = 0) 3) ∧ wpGfp chainSys (fun s => s = 0) 3) ∧
      ((∀ n, wpFuel loopSys n (fun _ => False) ()) ∧ wpGfp loopSys (fun _ => False) ())
```

### 2. `fixed-fuel-does-not-give-partial-correctness`

- **Kind:** counterexample
- **Tier:** `T0` — Elementary: an error at distance n is invisible to a check of depth n.
- **Plain claim:** For every fuel n, the state n of downToStuckSys (a countdown on Nat whose last state 0 is stuck) satisfies the partial-correctness fuel weakest precondition wpFuel n (fun _ => True), does not satisfy wpFuel m (fun _ => True) at every fuel m (the statement asserts only that not every fuel m works; that m = n + 1 fails is the separate lemma downToStuckSys_not_wpFuel, used in the proof but not part of the statement), and does not satisfy wpGfp (fun _ => True).
- **Depth:** `shallow`
- **Lean statement:**

```lean
-- lean/ToyFuelWP/Counterexamples.lean:24-27
-- ToyFuelWP.Counterexamples
theorem fixed_fuel_wpFuel_not_imp_wpGfp (n : Nat) :
    wpFuel downToStuckSys n (fun _ => True) n ∧
      ¬ (∀ m, wpFuel downToStuckSys m (fun _ => True) n) ∧
      ¬ wpGfp downToStuckSys (fun _ => True) n
```

- **Supporting lemma used in the proof** (context only; not part of the card's statement, no recorded hash; axioms `Quot.sound`, `propext`):

```lean
-- lean/ToyFuelWP/Systems.lean:277
-- ToyFuelWP.Systems
theorem downToStuckSys_not_wpFuel : ∀ (k : Nat), ¬ wpFuel downToStuckSys (k + 1) (fun _ => True) k
```

- **Hypothesis ledger:** No hypotheses. The only parameter is the fuel `n : Nat`, universally quantified; the system (`downToStuckSys`), the postcondition (`fun _ => True`) and the state (`n`) are fixed by the statement.
- **Non-vacuity witness:** The statement is itself a concrete instance for each n. (`fixed_fuel_wpFuel_not_imp_wpGfp`)
- **Logic (`#print axioms`):** fixed_fuel_wpFuel_not_imp_wpGfp: proved; #print axioms: Quot.sound, propext.
- **Non-claims:** see Boundaries, card 2.
- **Prior art:**
  - S. Owens, M. O. Myreen, R. Kumar, Y. K. Tan. Functional big-step semantics. ESOP 2016, LNCS 9632, pp. 589–615. doi:10.1007/978-3-662-49498-1_23. Clocked (fuel-indexed) interpreters: evaluation diverges iff it times out for every initial clock value; the HOL4 development (HOL repository, examples/pl-semantics/for/forScript.sml, theorem simple_sem_t_div_iff_sem_t_div) proves this equals a coinductive divergence relation for a deterministic language — the closest mechanized analogue of the 'every fuel = coinductive' direction found.
  - A. W. Appel and D. McAllester. An indexed model of recursive types for foundational proof-carrying code. ACM TOPLAS 23(5):657–683, 2001. doi:10.1145/504709.504712. Origin of step-indexed models, in which a natural-number index bounds the number of steps for which a property is observed — the same 'bounded observation' reading as partial-correctness fuel, applied to types rather than weakest preconditions (analogy only).
- **Design question:** A verification framework whose trusted kernel forbids coinductive definitions and general recursion defines its weakest precondition by structural recursion on fuel. For which properties is that the same as the coinductive (greatest-fixpoint) definition, how should 'verified at fuel n' be read, and where do the two differ (total correctness, divergence, liveness)? This card: a partial-correctness result verified at one fixed fuel is only a bounded-depth check.
- Basis: execution (Lean kernel check) — `fixed_fuel_wpFuel_not_imp_wpGfp`, and every counterexample and witness named above, are theorems checked by the Lean kernel under `leanprover/lean4:v4.34.1` with the axioms listed.
- Basis: derived (modeling bridge) — for a framework whose semantics is faithfully modeled as a `System σ` with the conventions of Applicability and whose fuel counts the same steps: a partial-correctness result verified at one fixed fuel is only a bounded-depth check. Reasoning: the Lean statement is universally quantified over systems (or exhibits a concrete one), so it transfers through such a model; the faithfulness of any particular model is not checked here.

### 3. `fuel-monotonicity-opposite-directions`

- **Kind:** theorem
- **Tier:** `T0` — Iterates of a monotone operator from the top predicate decrease and from the bottom predicate increase; restated for the two fuel transformers.
- **Plain claim:** For every transition system, postcondition and state, and fuels n ≤ m: the partial-correctness fuel weakest precondition is antitone (wpFuel m Q s implies wpFuel n Q s, so more fuel is a stronger claim), while the total-correctness fuel weakest precondition is monotone (wpFuelTotal n Q s implies wpFuelTotal m Q s, so more fuel is a weaker claim).
- **Depth:** `shallow`
- **Lean statement:**

```lean
-- lean/ToyFuelWP/Statements.lean:54-55
-- ToyFuelWP.Statements
theorem wpFuel_antitone (S : System σ) (Q : σ → Prop) (s : σ) {n m : Nat} (hnm : n ≤ m)
    (h : wpFuel S m Q s) : wpFuel S n Q s

-- lean/ToyFuelWP/Statements.lean:65-66
-- ToyFuelWP.Statements
theorem wpFuelTotal_monotone (S : System σ) (Q : σ → Prop) (s : σ) {n m : Nat} (hnm : n ≤ m)
    (h : wpFuelTotal S n Q s) : wpFuelTotal S m Q s
```

- **Hypothesis ledger:**
  - `hnm : n ≤ m (in wpFuel_antitone)` — fuel order; reversing it fails because fuel 0 is vacuous for partial correctness. Tightness: **tight**; counterexample: `wpFuel_not_monotone_stuck`.
  - `h : wpFuel S m Q s (in wpFuel_antitone)` — the judgement at the larger fuel. Tightness: **tight**; counterexample: `wpFuel_antitone_drop_h`.
  - `hnm : n ≤ m (in wpFuelTotal_monotone)` — fuel order; reversing it fails because fuel 0 is unsatisfiable for total correctness. Tightness: **tight**; counterexample: `wpFuelTotal_not_antitone_done`.
  - `h : wpFuelTotal S n Q s (in wpFuelTotal_monotone)` — the judgement at the smaller fuel. Tightness: **tight**; counterexample: `wpFuelTotal_monotone_drop_h`.
- **Non-vacuity witness:** 1 ≤ 3 with wpFuel loopSys 3 False (); 4 ≤ 6 with wpFuelTotal chainSys 4 (· = 0) 3. (`nonvacuity_wpFuel_antitone`, `nonvacuity_wpFuelTotal`)
- **Logic (`#print axioms`):** wpFuel_antitone: proved; #print axioms: no axioms; wpFuelTotal_monotone: proved; #print axioms: no axioms.
- **Results backing the non-claims:** `wpFuelTotal_neg_chain_short`, `wpLfp_pos_chain`.
- **Non-claims:** see Boundaries, card 3.
- **Prior art:**
  - E. W. Dijkstra. Guarded commands, nondeterminacy and formal derivation of programs. Communications of the ACM 18(8):453–457, 1975. doi:10.1145/360933.360975. Defines only the total-correctness wp(S, R) — the weakest precondition guaranteeing proper termination in a state satisfying R; no liberal (partial-correctness) counterpart is defined there — and defines the loop by H0(R) = R ∧ ¬BB, Hk(R) = wp(IF, Hk-1(R)) ∨ H0(R), wp(DO, R) = (∃k ≥ 0: Hk(R)), with Hk(R) read as termination after at most k selections — an existentially fuel-indexed total weakest precondition. (Content read in the author's EWD418 transcription, whose abstract matches the published one.)
  - P. Cousot and R. Cousot. Constructive versions of Tarski's fixed point theorems. Pacific Journal of Mathematics 82(1):43–57, 1979. doi:10.2140/pjm.1979.82.43. Fixpoints of monotone maps via transfinite iteration without continuity, contrasted with the ω-iteration that needs continuity.
- **Design question:** A verification framework whose trusted kernel forbids coinductive definitions and general recursion defines its weakest precondition by structural recursion on fuel. For which properties is that the same as the coinductive (greatest-fixpoint) definition, how should 'verified at fuel n' be read, and where do the two differ (total correctness, divergence, liveness)? This card: 'verified at fuel n' means opposite things in the two modes — a lower bound on the depth checked (partial) versus an upper bound on run length (total).
- Basis: execution (Lean kernel check) — `wpFuel_antitone`, `wpFuelTotal_monotone`, and every counterexample and witness named above, are theorems checked by the Lean kernel under `leanprover/lean4:v4.34.1` with the axioms listed.
- Basis: derived (modeling bridge) — for a framework whose semantics is faithfully modeled as a `System σ` with the conventions of Applicability and whose fuel counts the same steps: 'verified at fuel n' means opposite things in the two modes — a lower bound on the depth checked (partial) versus an upper bound on run length (total). Reasoning: the Lean statement is universally quantified over systems (or exhibits a concrete one), so it transfers through such a model; the faithfulness of any particular model is not checked here.
- **Statements of the counterexamples, witnesses and controls named on this card:**

```lean
-- lean/ToyFuelWP/Counterexamples.lean:53-54
-- ToyFuelWP.Counterexamples
theorem wpFuel_not_monotone_stuck :
    ¬ (1 ≤ 0) ∧ wpFuel stuckSys 0 (fun _ => True) () ∧ ¬ wpFuel stuckSys 1 (fun _ => True) ()

-- lean/ToyFuelWP/Counterexamples.lean:69-70
-- ToyFuelWP.Counterexamples
theorem wpFuel_antitone_drop_h :
    1 ≤ 2 ∧ ¬ wpFuel stuckSys 2 (fun _ => True) () ∧ ¬ wpFuel stuckSys 1 (fun _ => True) ()

-- lean/ToyFuelWP/Counterexamples.lean:60-62
-- ToyFuelWP.Counterexamples
theorem wpFuelTotal_not_antitone_done :
    ¬ (1 ≤ 0) ∧ wpFuelTotal doneSys 1 (fun _ => True) () ∧
      ¬ wpFuelTotal doneSys 0 (fun _ => True) ()

-- lean/ToyFuelWP/Counterexamples.lean:79-81
-- ToyFuelWP.Counterexamples
theorem wpFuelTotal_monotone_drop_h :
    1 ≤ 2 ∧ ¬ wpFuelTotal stuckSys 1 (fun _ => True) () ∧
      ¬ wpFuelTotal stuckSys 2 (fun _ => True) ()

-- lean/ToyFuelWP/Counterexamples.lean:104
-- ToyFuelWP.Counterexamples
theorem nonvacuity_wpFuel_antitone : 1 ≤ 3 ∧ wpFuel loopSys 3 (fun _ => False) ()

-- lean/ToyFuelWP/Counterexamples.lean:110
-- ToyFuelWP.Counterexamples
theorem nonvacuity_wpFuelTotal : 4 ≤ 6 ∧ wpFuelTotal chainSys 4 (fun s => s = 0) 3
```

### 4. `partial-fuel-n-reading`

- **Kind:** characterization
- **Tier:** `T0` — Restatement of the bounded-observation reading of clocked / step-indexed partial correctness over run prefixes; it is the fuel-n truncation of the adequacy characterization gfp-adequacy.
- **Plain claim:** For every transition system, fuel n, postcondition Q and state s: wpFuel n Q s holds if and only if every run prefix from s of fewer than n steps (each step taken from a non-terminal state) ends in a state t with RunEndOk S Q t, that is, t satisfies Q if it is terminal and has a successor if it is not; run prefixes of n or more steps are unconstrained.
- **Depth:** `shallow`
- **Lean statement:**

```lean
-- lean/ToyFuelWP/Statements.lean:78-79
-- ToyFuelWP.Statements
theorem wpFuel_iff_forall_reach_lt (S : System σ) (n : Nat) (Q : σ → Prop) (s : σ) :
    wpFuel S n Q s ↔ ∀ k t, k < n → Reach S s k t → RunEndOk S Q t
```

- **Hypothesis ledger:** No hypotheses. The biconditional is stated for an arbitrary system `S`, fuel `n`, postcondition `Q` and state `s`.
- **Non-vacuity witness:** downToStuckSys from 3 satisfies wpFuel at fuel 3 although an error is reachable in 3 steps, and fails it at fuel 4. (`nonvacuity_wpFuel_iff_forall_reach_lt`)
- **Logic (`#print axioms`):** wpFuel_iff_forall_reach_lt: proved; #print axioms: no axioms. RunEndOk is phrased with implications so that the statement is constructive; its disjunctive reading (runEndOk_iff_or; #print axioms: Classical.choice, Quot.sound, propext) is classical.
- **Results backing the non-claims:** `wpFuel_pos_zero_stuck`.
- **Non-claims:** see Boundaries, card 4.
- **Prior art:**
  - A. W. Appel and D. McAllester. An indexed model of recursive types for foundational proof-carrying code. ACM TOPLAS 23(5):657–683, 2001. doi:10.1145/504709.504712. Origin of step-indexed models, in which a natural-number index bounds the number of steps for which a property is observed — the same 'bounded observation' reading as partial-correctness fuel, applied to types rather than weakest preconditions (analogy only).
  - A. J. Ahmed. Semantics of Types for Mutable State. PhD thesis, Princeton University, 2004. Indexed possible-worlds model building on Appel and McAllester's indexed model (analogy only).
  - S. Owens, M. O. Myreen, R. Kumar, Y. K. Tan. Functional big-step semantics. ESOP 2016, LNCS 9632, pp. 589–615. doi:10.1007/978-3-662-49498-1_23. Clocked (fuel-indexed) interpreters: evaluation diverges iff it times out for every initial clock value; the HOL4 development (HOL repository, examples/pl-semantics/for/forScript.sml, theorem simple_sem_t_div_iff_sem_t_div) proves this equals a coinductive divergence relation for a deterministic language — the closest mechanized analogue of the 'every fuel = coinductive' direction found.
  - N. Amin and T. Rompf. Type soundness proofs with definitional interpreters. POPL 2017, pp. 666–679. doi:10.1145/3009837.3009866. Type soundness stated over definitional interpreters (bibliographic record verified; listed as a reference point for interpreter-based semantics, content not re-read here).
  - Iris Coq library, iris/program_logic/adequacy.v (as rendered in the Iris coqdoc): the record adequate s e1 σ1 φ says that every value reached by a finite execution satisfies φ and, for s = NotStuck, that no reachable thread is stuck; wp_adequacy_gen derives adequate from a weakest-precondition proof — the analogue, for a guarded step-indexed weakest precondition, of the finite-run-prefix adequacy here.
- **Design question:** A verification framework whose trusted kernel forbids coinductive definitions and general recursion defines its weakest precondition by structural recursion on fuel. For which properties is that the same as the coinductive (greatest-fixpoint) definition, how should 'verified at fuel n' be read, and where do the two differ (total correctness, divergence, liveness)? This card: the exact meaning of a partial-correctness theorem proved at one fuel.
- Basis: execution (Lean kernel check) — `wpFuel_iff_forall_reach_lt`, and every counterexample and witness named above, are theorems checked by the Lean kernel under `leanprover/lean4:v4.34.1` with the axioms listed.
- Basis: derived (modeling bridge) — for a framework whose semantics is faithfully modeled as a `System σ` with the conventions of Applicability and whose fuel counts the same steps: the exact meaning of a partial-correctness theorem proved at one fuel. Reasoning: the Lean statement is universally quantified over systems (or exhibits a concrete one), so it transfers through such a model; the faithfulness of any particular model is not checked here.
- **Statements of the counterexamples, witnesses and controls named on this card:**

```lean
-- lean/ToyFuelWP/Counterexamples.lean:116-117
-- ToyFuelWP.Counterexamples
theorem nonvacuity_wpFuel_iff_forall_reach_lt :
    wpFuel downToStuckSys 3 (fun _ => True) 3 ∧ ¬ wpFuel downToStuckSys 4 (fun _ => True) 3
```

### 5. `total-fuel-n-reading`

- **Kind:** characterization
- **Tier:** `T0` — Restatement of bounded total correctness (Dijkstra's Hk, up to an index shift) over run prefixes.
- **Plain claim:** For every transition system, fuel n, postcondition Q and state s: wpFuelTotal n Q s holds if and only if wpFuel n Q s holds and no run prefix from s has exactly n steps. In particular no state satisfies wpFuelTotal 0 Q. Read classically (or when terminal is decidable), the right-hand side says that every run from s halts after fewer than n steps, without error, in a state satisfying Q.
- **Depth:** `shallow`
- **Lean statement:**

```lean
-- lean/ToyFuelWP/Statements.lean:97-98
-- ToyFuelWP.Statements
theorem wpFuelTotal_iff_wpFuel_and_no_reach (S : System σ) (n : Nat) (Q : σ → Prop) (s : σ) :
    wpFuelTotal S n Q s ↔ wpFuel S n Q s ∧ ∀ t, ¬ Reach S s n t
```

- **Hypothesis ledger:** No hypotheses. The biconditional is stated for an arbitrary system `S`, fuel `n`, postcondition `Q` and state `s`.
- **Non-vacuity witness:** wpFuelTotal chainSys 4 (· = 0) 3 holds. (`nonvacuity_wpFuelTotal`)
- **Logic (`#print axioms`):** wpFuelTotal_iff_wpFuel_and_no_reach: proved; #print axioms: propext.
- **Results backing the non-claims:** `wpFuelTotal_propSys_one_iff_not_not`, `wpFuelTotal_neg_zero_done`.
- **Non-claims:** see Boundaries, card 5.
- **Prior art:**
  - E. W. Dijkstra. Guarded commands, nondeterminacy and formal derivation of programs. Communications of the ACM 18(8):453–457, 1975. doi:10.1145/360933.360975. Defines only the total-correctness wp(S, R) — the weakest precondition guaranteeing proper termination in a state satisfying R; no liberal (partial-correctness) counterpart is defined there — and defines the loop by H0(R) = R ∧ ¬BB, Hk(R) = wp(IF, Hk-1(R)) ∨ H0(R), wp(DO, R) = (∃k ≥ 0: Hk(R)), with Hk(R) read as termination after at most k selections — an existentially fuel-indexed total weakest precondition. (Content read in the author's EWD418 transcription, whose abstract matches the published one.) Index shift: H0 already covers a loop that terminates after zero selections, whereas wpFuelTotal 0 Q is False and a terminal state needs fuel 1; under the analogy one selection = one step, Hk corresponds to fuel k + 1.
  - S. Owens, M. O. Myreen, R. Kumar, Y. K. Tan. Functional big-step semantics. ESOP 2016, LNCS 9632, pp. 589–615. doi:10.1007/978-3-662-49498-1_23. Clocked (fuel-indexed) interpreters: evaluation diverges iff it times out for every initial clock value; the HOL4 development (HOL repository, examples/pl-semantics/for/forScript.sml, theorem simple_sem_t_div_iff_sem_t_div) proves this equals a coinductive divergence relation for a deterministic language — the closest mechanized analogue of the 'every fuel = coinductive' direction found.
- **Design question:** A verification framework whose trusted kernel forbids coinductive definitions and general recursion defines its weakest precondition by structural recursion on fuel. For which properties is that the same as the coinductive (greatest-fixpoint) definition, how should 'verified at fuel n' be read, and where do the two differ (total correctness, divergence, liveness)? This card: a total-correctness theorem at fuel n is a uniform bound on run length plus partial correctness at fuel n.
- Basis: execution (Lean kernel check) — `wpFuelTotal_iff_wpFuel_and_no_reach`, and every counterexample and witness named above, are theorems checked by the Lean kernel under `leanprover/lean4:v4.34.1` with the axioms listed.
- Basis: derived (modeling bridge) — for a framework whose semantics is faithfully modeled as a `System σ` with the conventions of Applicability and whose fuel counts the same steps: a total-correctness theorem at fuel n is a uniform bound on run length plus partial correctness at fuel n. Reasoning: the Lean statement is universally quantified over systems (or exhibits a concrete one), so it transfers through such a model; the faithfulness of any particular model is not checked here.
- **Statements of the counterexamples, witnesses and controls named on this card:**

```lean
-- lean/ToyFuelWP/Counterexamples.lean:110
-- ToyFuelWP.Counterexamples
theorem nonvacuity_wpFuelTotal : 4 ≤ 6 ∧ wpFuelTotal chainSys 4 (fun s => s = 0) 3
```

### 6. `total-fuel-sound-for-lfp`

- **Kind:** theorem
- **Tier:** `T0` — Finite iterates from the bottom predicate lie below the least fixpoint, and the least fixpoint lies below the greatest; restated for the fuel form.
- **Plain claim:** For every transition system (no branching assumption), postcondition Q and state s: if wpFuelTotal n Q s for some fuel n, then s satisfies the least-fixpoint total-correctness weakest precondition wpLfp Q (wpLfp_of_exists_wpFuelTotal), and therefore also the greatest-fixpoint partial-correctness weakest precondition wpGfp Q (wpGfp_of_wpFuelTotal, derived from the first using that wpLfp Q is a post-fixed point of wpStep Q).
- **Depth:** `shallow`
- **Lean statement:**

```lean
-- lean/ToyFuelWP/Statements.lean:115-116
-- ToyFuelWP.Statements
theorem wpLfp_of_exists_wpFuelTotal (S : System σ) (Q : σ → Prop) (s : σ)
    (h : ∃ n, wpFuelTotal S n Q s) : wpLfp S Q s

-- lean/ToyFuelWP/Statements.lean:125-126
-- ToyFuelWP.Statements
theorem wpGfp_of_wpFuelTotal (S : System σ) (n : Nat) (Q : σ → Prop) (s : σ)
    (h : wpFuelTotal S n Q s) : wpGfp S Q s
```

- **Hypothesis ledger:**
  - `h : ∃ n, wpFuelTotal S n Q s (in wpLfp_of_exists_wpFuelTotal)` — a fuel bound; the theorem has no other hypothesis. Tightness: **tight**; counterexample: `stuckSys_no_total_no_partial`.
  - `h : wpFuelTotal S n Q s (in wpGfp_of_wpFuelTotal)` — the total-correctness judgement at fuel n; the theorem has no other hypothesis. Tightness: **tight**; counterexample: `stuckSys_no_total_no_partial`.
- **Non-vacuity witness:** wpFuelTotal chainSys 4 (· = 0) 3 holds. (`nonvacuity_wpFuelTotal`)
- **Logic (`#print axioms`):** wpLfp_of_exists_wpFuelTotal: proved; #print axioms: no axioms; wpGfp_of_wpFuelTotal: proved; #print axioms: no axioms.
- **Results backing the non-claims:** `loop_finitelyBranching_no_total_fuel`.
- **Non-claims:** see Boundaries, card 6.
- **Prior art:**
  - E. W. Dijkstra. Guarded commands, nondeterminacy and formal derivation of programs. Communications of the ACM 18(8):453–457, 1975. doi:10.1145/360933.360975. Defines only the total-correctness wp(S, R) — the weakest precondition guaranteeing proper termination in a state satisfying R; no liberal (partial-correctness) counterpart is defined there — and defines the loop by H0(R) = R ∧ ¬BB, Hk(R) = wp(IF, Hk-1(R)) ∨ H0(R), wp(DO, R) = (∃k ≥ 0: Hk(R)), with Hk(R) read as termination after at most k selections — an existentially fuel-indexed total weakest precondition. (Content read in the author's EWD418 transcription, whose abstract matches the published one.)
  - P. Cousot and R. Cousot. Constructive versions of Tarski's fixed point theorems. Pacific Journal of Mathematics 82(1):43–57, 1979. doi:10.2140/pjm.1979.82.43. Fixpoints of monotone maps via transfinite iteration without continuity, contrasted with the ω-iteration that needs continuity.
  - G. Nelson. A generalization of Dijkstra's calculus. ACM TOPLAS 11(4):517–561, 1989. doi:10.1145/69558.69559. Generalizes the wp calculus by dropping the law of the excluded miracle, treats recursion by fixpoints, and relates the full wp/wlp semantics to a powerdomain semantics. Contrast: here wpLfp obeys the law of the excluded miracle (wpLfp_excluded_miracle) and every weakest precondition rejects stuck states, so a state without outcomes is an error, not a miracle.
  - Iris Coq library, iris/program_logic/total_weakestpre.v and total_adequacy.v (as rendered in the Iris coqdoc): the total weakest precondition twp is defined as a least fixpoint (bi_least_fixpoint of twp_pre'), and twp_total derives strong normalization sn erased_step from a total-weakest-precondition proof — a mechanized least-fixpoint total weakest precondition in a separation logic.
- **Design question:** A verification framework whose trusted kernel forbids coinductive definitions and general recursion defines its weakest precondition by structural recursion on fuel. For which properties is that the same as the coinductive (greatest-fixpoint) definition, how should 'verified at fuel n' be read, and where do the two differ (total correctness, divergence, liveness)? This card: in total mode a fuel-bounded proof is always sound, for total and hence for partial correctness.
- Basis: execution (Lean kernel check) — `wpLfp_of_exists_wpFuelTotal`, `wpGfp_of_wpFuelTotal`, and every counterexample and witness named above, are theorems checked by the Lean kernel under `leanprover/lean4:v4.34.1` with the axioms listed.
- Basis: derived (modeling bridge) — for a framework whose semantics is faithfully modeled as a `System σ` with the conventions of Applicability and whose fuel counts the same steps: in total mode a fuel-bounded proof is always sound, for total and hence for partial correctness. Reasoning: the Lean statement is universally quantified over systems (or exhibits a concrete one), so it transfers through such a model; the faithfulness of any particular model is not checked here.
- **Statements of the counterexamples, witnesses and controls named on this card:**

```lean
-- lean/ToyFuelWP/Counterexamples.lean:93-95
-- ToyFuelWP.Counterexamples
theorem stuckSys_no_total_no_partial :
    (∀ n, ¬ wpFuelTotal stuckSys n (fun _ => True) ()) ∧
      ¬ wpGfp stuckSys (fun _ => True) () ∧ ¬ wpLfp stuckSys (fun _ => True) ()

-- lean/ToyFuelWP/Counterexamples.lean:110
-- ToyFuelWP.Counterexamples
theorem nonvacuity_wpFuelTotal : 4 ≤ 6 ∧ wpFuelTotal chainSys 4 (fun s => s = 0) 3
```

### 7. `total-fuel-complete-under-finite-branching`

- **Kind:** theorem
- **Tier:** `T0` — Known as continuity of wp under bounded nondeterminism (and its failure under unbounded nondeterminism; Dijkstra 1976, Apt and Plotkin 1986), with Kőnig's lemma behind the König form; restated here with a local finite-branching hypothesis, three corollaries for global finite branching, determinism and interpreter step functions, and the König form.
- **Plain claim:** If every non-terminal state reachable from s has its successors contained in a finite list (FinitelyBranchingFrom S s), then wpLfp Q s implies wpFuelTotal n Q s for some fuel n, which depends on s (exists_wpFuelTotal_of_wpLfp_of_finitelyBranchingFrom). Corollaries: (∃ n, wpFuelTotal n Q s) ↔ wpLfp Q s at every state of a system in which every non-terminal state is finitely branching (FinitelyBranching), in particular of a system in which every non-terminal state has at most one successor (Deterministic), in particular of the system ofStepFn next halted induced by any partial step function next : σ → Option σ; and the König form: if FinitelyBranchingFrom S s, wpGfp Q s and no run from s is infinite, then wpFuelTotal n Q s for some n (derived from the first statement and total-equals-partial-plus-termination).
- **Depth:** `substantive`
- **Lean statement:**

```lean
-- lean/ToyFuelWP/Statements.lean:157-159
-- ToyFuelWP.Statements
theorem exists_wpFuelTotal_of_wpLfp_of_finitelyBranchingFrom (S : System σ) (Q : σ → Prop)
    (s : σ) (hfb : FinitelyBranchingFrom S s) (h : wpLfp S Q s) :
    ∃ n, wpFuelTotal S n Q s

-- lean/ToyFuelWP/Statements.lean:174-175
-- ToyFuelWP.Statements
theorem exists_wpFuelTotal_iff_wpLfp_of_finitelyBranching (S : System σ) (Q : σ → Prop)
    (hfb : FinitelyBranching S) (s : σ) : (∃ n, wpFuelTotal S n Q s) ↔ wpLfp S Q s

-- lean/ToyFuelWP/Statements.lean:182-183
-- ToyFuelWP.Statements
theorem exists_wpFuelTotal_iff_wpLfp_of_deterministic (S : System σ) (Q : σ → Prop)
    (hdet : Deterministic S) (s : σ) : (∃ n, wpFuelTotal S n Q s) ↔ wpLfp S Q s

-- lean/ToyFuelWP/Statements.lean:190-192
-- ToyFuelWP.Statements
theorem exists_wpFuelTotal_iff_wpLfp_ofStepFn (next : σ → Option σ) (halted : σ → Prop)
    (Q : σ → Prop) (s : σ) :
    (∃ n, wpFuelTotal (ofStepFn next halted) n Q s) ↔ wpLfp (ofStepFn next halted) Q s

-- lean/ToyFuelWP/Statements.lean:238-240
-- ToyFuelWP.Statements
theorem exists_wpFuelTotal_of_wpGfp_of_not_hasInfiniteRun_of_finitelyBranchingFrom
    (S : System σ) (Q : σ → Prop) (s : σ) (hfb : FinitelyBranchingFrom S s)
    (hsafe : wpGfp S Q s) (hfin : ¬ HasInfiniteRun S s) : ∃ n, wpFuelTotal S n Q s
```

- **Hypothesis ledger:**
  - `hfb : FinitelyBranchingFrom S s (in exists_wpFuelTotal_of_wpLfp_of_finitelyBranchingFrom)` — lets the fuel bound be a maximum over finitely many successors at each reachable non-terminal state. Tightness: **tight**; counterexample: `countdown_wpLfp_without_uniform_fuel`.
  - `h : wpLfp S Q s (in exists_wpFuelTotal_of_wpLfp_of_finitelyBranchingFrom)` — the total-correctness judgement. Tightness: **tight**; counterexample: `loop_finitelyBranching_no_total_fuel`.
  - `hfb : FinitelyBranching S (in exists_wpFuelTotal_iff_wpLfp_of_finitelyBranching)` — global finite branching at non-terminal states; strictly stronger than FinitelyBranchingFrom S s (finitelyBranchingFrom_pos_countdown_count holds in countdownSys, which is not FinitelyBranching). Tightness: **tight**; counterexample: `countdown_exists_wpFuelTotal_iff_wpLfp_fails`.
  - `hdet : Deterministic S (in exists_wpFuelTotal_iff_wpLfp_of_deterministic)` — at most one successor at every non-terminal state; strictly stronger than FinitelyBranching (spinOrExitSys_finitelyBranching_not_deterministic), so this corollary is a convenience form of the previous one. Tightness: **tight**; counterexample: `countdown_exists_wpFuelTotal_iff_wpLfp_fails`.
  - `hfb : FinitelyBranchingFrom S s (in the König form exists_wpFuelTotal_of_wpGfp_of_not_hasInfiniteRun_of_finitelyBranchingFrom)` — Kőnig's lemma needs finite branching. Tightness: **tight**; counterexample: `countdown_wpLfp_without_uniform_fuel`.
  - `hsafe : wpGfp S Q s (in the König form)` — no error and Q at termination. Tightness: **tight**; counterexample: `stuck_finitelyBranching_no_infinite_run_no_total_fuel`.
  - `hfin : ¬ HasInfiniteRun S s (in the König form)` — termination of every run. Tightness: **tight**; counterexample: `loop_finitelyBranching_no_total_fuel`.
- **Non-vacuity witness:** chainSys from 3 (deterministic, finitely branching, totally correct for (· = 0), no infinite run); the state count 3 of countdownSys, finitely branching locally inside a system that is not globally finitely branching; the predecessor interpreter ofStepFn predStep (· = 0) from 3 (predStep, quoted under Concrete toy systems, maps 0 to none and k + 1 to some k). (`nonvacuity_exists_wpFuelTotal_of_wpLfp_of_finitelyBranchingFrom`, `nonvacuity_exists_wpFuelTotal_iff_wpLfp_corollaries`, `nonvacuity_exists_wpFuelTotal_iff_wpLfp_ofStepFn`, `nonvacuity_koenig_form`)
- **Logic (`#print axioms`):** exists_wpFuelTotal_of_wpLfp_of_finitelyBranchingFrom: proved; #print axioms: Classical.choice, Quot.sound, propext; exists_wpFuelTotal_iff_wpLfp_of_finitelyBranching: proved; #print axioms: Classical.choice, Quot.sound, propext; exists_wpFuelTotal_iff_wpLfp_of_deterministic: proved; #print axioms: Classical.choice, Quot.sound, propext; exists_wpFuelTotal_iff_wpLfp_ofStepFn: proved; #print axioms: Classical.choice, Quot.sound, propext; exists_wpFuelTotal_of_wpGfp_of_not_hasInfiniteRun_of_finitelyBranchingFrom: proved; #print axioms: Classical.choice, Quot.sound, propext. Classical reasoning is necessary, not an artifact of these proofs: exists_wpFuelTotal_of_wpLfp_of_finitelyBranchingFrom, exists_wpFuelTotal_iff_wpLfp_of_finitelyBranching and the König form each imply the limited principle of omniscience (lpo_of_exists_wpFuelTotal_of_wpLfp_of_finitelyBranchingFrom, lpo_of_exists_wpFuelTotal_iff_wpLfp_of_finitelyBranching, lpo_of_koenig_form; #print axioms: propext only), which is not derivable in intuitionistic logic. The obstruction comes from FinitelyBranchingAt asking only for a finite list containing the successors (not an exact successor list) together with undecidable step and terminal predicates; for deterministic systems with decidable terminal states the first statement's conclusion has a proof with no axioms (exists_wpFuelTotal_of_wpLfp_of_deterministic_of_decidable_terminal).
  Evidence: `lpo_of_exists_wpFuelTotal_of_wpLfp_of_finitelyBranchingFrom` (propext), `lpo_of_exists_wpFuelTotal_iff_wpLfp_of_finitelyBranching` (propext), `lpo_of_koenig_form` (propext), `exists_wpFuelTotal_of_wpLfp_of_deterministic_of_decidable_terminal` (none).
- **Results backing the non-claims:** `chainSys_fuel_per_state_not_uniform`, `deterministic_pos_termBranch`, `finitelyBranchingFrom_pos_countdown_count`, `finitelyBranching_neg_countdown`, `spinOrExitSys_finitelyBranching_not_deterministic`.
- **Non-claims:** see Boundaries, card 7.
- **Prior art:**
  - E. W. Dijkstra. Guarded commands, nondeterminacy and formal derivation of programs. Communications of the ACM 18(8):453–457, 1975. doi:10.1145/360933.360975. Defines only the total-correctness wp(S, R) — the weakest precondition guaranteeing proper termination in a state satisfying R; no liberal (partial-correctness) counterpart is defined there — and defines the loop by H0(R) = R ∧ ¬BB, Hk(R) = wp(IF, Hk-1(R)) ∨ H0(R), wp(DO, R) = (∃k ≥ 0: Hk(R)), with Hk(R) read as termination after at most k selections — an existentially fuel-indexed total weakest precondition. (Content read in the author's EWD418 transcription, whose abstract matches the published one.)
  - E. W. Dijkstra. A Discipline of Programming. Prentice-Hall, 1976 (ISBN 0-13-215871-X, seen only in a copyright-page snippet). Contains the chapter 'On nondeterminacy being bounded' (p. 72 per the table of contents). That the book introduces the weakest liberal precondition and states a continuity property for bounded nondeterminism was seen only through secondary sources and text snippets, not at the primary source.
  - K. R. Apt and G. D. Plotkin. Countable nondeterminism and random assignment. Journal of the ACM 33(4):724–767, 1986. doi:10.1145/6490.6494. Abstract: admitting countable (unbounded) nondeterminism results in a lack of continuity of various semantic functions, shown necessary for any semantics satisfying appropriate conditions; total-correctness proofs need countable ordinals.
  - D. Kőnig. Über eine Schlussweise aus dem Endlichen ins Unendliche. Acta Sci. Math. (Szeged) 3(2–3):121–130, 1927 (volume and issue seen only via a secondary record). The infinity lemma (Lemma A): a sequence of finite non-empty sets linked by a relation admits an infinite chain.
  - R.-J. Back and J. von Wright. Refinement Calculus. Springer, 1998. doi:10.1007/978-1-4612-1674-2. Contains a chapter 'Continuity and Executable Statements' (pp. 365–382) and a chapter on fixed points; only titles and pages were verified, not the chapter text.
  - W. H. Hesselink. Programs, Recursion and Unbounded Choice. Cambridge University Press, 1992. doi:10.1017/CBO9780511569784. Publisher's abstract: a complete account of the predicate transformation calculus semantics of sequential programs, including repetitions, recursive procedures, computational induction and unbounded nondeterminacy.
  - Mathlib, Mathlib/Order/KonigLemma.lean (github.com/leanprover-community/mathlib4, master): exists_seq_covby_of_forall_covby_finite and exists_seq_forall_proj_of_forall_finite (Kőnig's infinity lemma) — a mechanized form of the lemma behind the König form of finite-branching completeness.
  - A. Lochbihler. Coinductive. Archive of Formal Proofs, February 2010 (isa-afp.org/entries/Coinductive.html). Abstract: general-purpose coinductive data types (lazy lists, streams, ...) with 'a version of König's lemma as an application for coinductive lists'.
  - D. Larchey-Wendling. Constructive Substitutes for Kőnig's Lemma. TYPES 2024, LIPIcs 336, 2:1–2:23, 2025. doi:10.4230/LIPIcs.TYPES.2024.2 (DataCite record verified), with the Coq artifact github.com/DmxLarchey/Constructive-Konig. Constructive replacements for Kőnig's lemma — relevant to the classical content of the finite-branching completeness statements, which imply the limited principle of omniscience here.
  - B. C. Pierce et al. Software Foundations, Volume 1: Logical Foundations, chapter ImpCEvalFun (softwarefoundations.cis.upenn.edu): theorem ceval_and_ceval_step_coincide — for the deterministic language Imp, the inductive big-step evaluation relation holds iff a fuel-indexed evaluation function returns the final state for some fuel; the deterministic analogue of the 'some fuel = least fixpoint' corollary.
  - D. Bridges, E. Palmgren and H. Ishihara. Constructive Mathematics. Stanford Encyclopedia of Philosophy, substantive revision of 25 August 2022, https://plato.stanford.edu/entries/mathematics-constructive/. Section 1 (Introduction): the limited principle of omniscience (LPO) is not constructively derivable (Kripke models; Bridges and Richman 1987, chapter 7). Section 2 (The Constructive Interpretation of Logic): Markov's principle (MP) is not constructively derivable (a Kripke model; Bridges and Richman 1987, pp. 137–138).
- **Design question:** A verification framework whose trusted kernel forbids coinductive definitions and general recursion defines its weakest precondition by structural recursion on fuel. For which properties is that the same as the coinductive (greatest-fixpoint) definition, how should 'verified at fuel n' be read, and where do the two differ (total correctness, divergence, liveness)? This card: for finitely branching (in particular deterministic, interpreter-induced) semantics, 'verified for some fuel' is exactly total correctness — with the fuel chosen per initial state, and only by classical reasoning in general.
- Basis: execution (Lean kernel check) — `exists_wpFuelTotal_of_wpLfp_of_finitelyBranchingFrom`, `exists_wpFuelTotal_iff_wpLfp_of_finitelyBranching`, `exists_wpFuelTotal_iff_wpLfp_of_deterministic`, `exists_wpFuelTotal_iff_wpLfp_ofStepFn`, `exists_wpFuelTotal_of_wpGfp_of_not_hasInfiniteRun_of_finitelyBranchingFrom`, and every counterexample and witness named above, are theorems checked by the Lean kernel under `leanprover/lean4:v4.34.1` with the axioms listed.
- Basis: derived (modeling bridge) — for a framework whose semantics is faithfully modeled as a `System σ` with the conventions of Applicability and whose fuel counts the same steps: for finitely branching (in particular deterministic, interpreter-induced) semantics, 'verified for some fuel' is exactly total correctness — with the fuel chosen per initial state, and only by classical reasoning in general. Reasoning: the Lean statement is universally quantified over systems (or exhibits a concrete one), so it transfers through such a model; the faithfulness of any particular model is not checked here.
- **Statements of the counterexamples, witnesses and controls named on this card:**

```lean
-- lean/ToyFuelWP/Counterexamples.lean:132-137
-- ToyFuelWP.Counterexamples
theorem countdown_wpLfp_without_uniform_fuel :
    ¬ FinitelyBranchingFrom countdownSys .start ∧ ¬ FinitelyBranching countdownSys ∧
      ¬ Deterministic countdownSys ∧
      wpLfp countdownSys (fun _ => True) .start ∧ wpGfp countdownSys (fun _ => True) .start ∧
      ¬ HasInfiniteRun countdownSys .start ∧
      ¬ ∃ n, wpFuelTotal countdownSys n (fun _ => True) .start

-- lean/ToyFuelWP/Counterexamples.lean:162-166
-- ToyFuelWP.Counterexamples
theorem loop_finitelyBranching_no_total_fuel :
    FinitelyBranching loopSys ∧ FinitelyBranchingFrom loopSys () ∧
      wpGfp loopSys (fun _ => True) () ∧ HasInfiniteRun loopSys () ∧
      ¬ wpLfp loopSys (fun _ => True) () ∧
      ¬ ∃ n, wpFuelTotal loopSys n (fun _ => True) ()

-- lean/ToyFuelWP/Counterexamples.lean:151-154
-- ToyFuelWP.Counterexamples
theorem countdown_exists_wpFuelTotal_iff_wpLfp_fails :
    ¬ FinitelyBranching countdownSys ∧ ¬ Deterministic countdownSys ∧
      ¬ ((∃ n, wpFuelTotal countdownSys n (fun _ => True) .start) ↔
        wpLfp countdownSys (fun _ => True) .start)

-- lean/ToyFuelWP/Counterexamples.lean:174-177
-- ToyFuelWP.Counterexamples
theorem stuck_finitelyBranching_no_infinite_run_no_total_fuel :
    FinitelyBranchingFrom stuckSys () ∧ ¬ HasInfiniteRun stuckSys () ∧
      ¬ wpGfp stuckSys (fun _ => True) () ∧
      ¬ ∃ n, wpFuelTotal stuckSys n (fun _ => True) ()

-- lean/ToyFuelWP/Counterexamples.lean:184-187
-- ToyFuelWP.Counterexamples
theorem nonvacuity_exists_wpFuelTotal_of_wpLfp_of_finitelyBranchingFrom :
    (FinitelyBranchingFrom chainSys 3 ∧ wpLfp chainSys (fun s => s = 0) 3) ∧
      (FinitelyBranchingFrom countdownSys (.count 3) ∧
        wpLfp countdownSys (fun _ => True) (.count 3))

-- lean/ToyFuelWP/Counterexamples.lean:193-194
-- ToyFuelWP.Counterexamples
theorem nonvacuity_exists_wpFuelTotal_iff_wpLfp_corollaries :
    Deterministic chainSys ∧ FinitelyBranching chainSys ∧ wpLfp chainSys (fun s => s = 0) 3

-- lean/ToyFuelWP/Counterexamples.lean:445-447
-- ToyFuelWP.Counterexamples
theorem nonvacuity_exists_wpFuelTotal_iff_wpLfp_ofStepFn :
    Deterministic (ofStepFn predStep (fun s => s = 0)) ∧
      wpLfp (ofStepFn predStep (fun s => s = 0)) (fun s => s = 0) 3

-- lean/ToyFuelWP/Counterexamples.lean:211-213
-- ToyFuelWP.Counterexamples
theorem nonvacuity_koenig_form :
    FinitelyBranchingFrom chainSys 3 ∧ wpGfp chainSys (fun s => s = 0) 3 ∧
      ¬ HasInfiniteRun chainSys 3
```

### 8. `unbounded-choice-no-uniform-fuel`

- **Kind:** counterexample
- **Tier:** `T0` — The random-assignment countdown (x := ?; while x > 0 do x := x - 1) is the standard example of unbounded nondeterminism breaking continuity (Dijkstra 1976; Apt and Plotkin 1986); restated as a fuel counterexample.
- **Plain claim:** In countdownSys (from start choose any k : Nat, then count down to a terminal count 0), the system is not finitely branching from start (not every non-terminal state reachable from start has its successors contained in a finite list), the system is not deterministic, and start satisfies wpLfp (fun _ => True) and wpGfp (fun _ => True) and has no infinite run, yet no fuel n gives wpFuelTotal n (fun _ => True) start.
- **Depth:** `shallow`
- **Lean statement:**

```lean
-- lean/ToyFuelWP/Counterexamples.lean:132-137
-- ToyFuelWP.Counterexamples
theorem countdown_wpLfp_without_uniform_fuel :
    ¬ FinitelyBranchingFrom countdownSys .start ∧ ¬ FinitelyBranching countdownSys ∧
      ¬ Deterministic countdownSys ∧
      wpLfp countdownSys (fun _ => True) .start ∧ wpGfp countdownSys (fun _ => True) .start ∧
      ¬ HasInfiniteRun countdownSys .start ∧
      ¬ ∃ n, wpFuelTotal countdownSys n (fun _ => True) .start
```

- **Hypothesis ledger:** No hypotheses and no parameters: the statement is about one concrete system (`countdownSys`), postcondition (`fun _ => True`) and state (`start`); every conjunct is proved outright.
- **Non-vacuity witness:** The statement is a concrete instance. (`countdown_wpLfp_without_uniform_fuel`)
- **Logic (`#print axioms`):** countdown_wpLfp_without_uniform_fuel: proved; #print axioms: Quot.sound, propext.
- **Results backing the non-claims:** `countdownSys_start_wpLfp`.
- **Non-claims:** see Boundaries, card 8.
- **Prior art:**
  - K. R. Apt and G. D. Plotkin. Countable nondeterminism and random assignment. Journal of the ACM 33(4):724–767, 1986. doi:10.1145/6490.6494. Abstract: admitting countable (unbounded) nondeterminism results in a lack of continuity of various semantic functions, shown necessary for any semantics satisfying appropriate conditions; total-correctness proofs need countable ordinals.
  - T. Nipkow. Hoare logics for recursive procedures and unbounded nondeterminism. CSL 2002, pp. 103–119. doi:10.1007/3-540-45793-3_8; mechanized in the Isabelle Archive of Formal Proofs entry Abstract-Hoare-Logics. Mechanized total correctness in the presence of unbounded nondeterminism (not a continuity-failure theorem).
  - E. W. Dijkstra. A Discipline of Programming. Prentice-Hall, 1976 (ISBN 0-13-215871-X, seen only in a copyright-page snippet). Contains the chapter 'On nondeterminacy being bounded' (p. 72 per the table of contents). That the book introduces the weakest liberal precondition and states a continuity property for bounded nondeterminism was seen only through secondary sources and text snippets, not at the primary source.
  - W. H. Hesselink. Programs, Recursion and Unbounded Choice. Cambridge University Press, 1992. doi:10.1017/CBO9780511569784. Publisher's abstract: a complete account of the predicate transformation calculus semantics of sequential programs, including repetitions, recursive procedures, computational induction and unbounded nondeterminacy.
  - S. Spies, L. Gäher, D. Gratzer, J. Tassarotti, R. Krebbers, D. Dreyer, L. Birkedal. Transfinite Iris: resolving an existential dilemma of step-indexed separation logic. PLDI 2021, pp. 80–95. doi:10.1145/3453483.3454031. Moves the step index of Iris from natural numbers to ordinals to resolve a problem with existential quantification in step-indexed logics (bibliographic record and title verified; details not re-read here) — related to the limits of natural-number fuel under unbounded or existential choice.
- **Design question:** A verification framework whose trusted kernel forbids coinductive definitions and general recursion defines its weakest precondition by structural recursion on fuel. For which properties is that the same as the coinductive (greatest-fixpoint) definition, how should 'verified at fuel n' be read, and where do the two differ (total correctness, divergence, liveness)? This card: with unbounded nondeterminism, fuel-bounded total correctness is incomplete.
- Basis: execution (Lean kernel check) — `countdown_wpLfp_without_uniform_fuel`, and every counterexample and witness named above, are theorems checked by the Lean kernel under `leanprover/lean4:v4.34.1` with the axioms listed.
- Basis: derived (modeling bridge) — for a framework whose semantics is faithfully modeled as a `System σ` with the conventions of Applicability and whose fuel counts the same steps: with unbounded nondeterminism, fuel-bounded total correctness is incomplete. Reasoning: the Lean statement is universally quantified over systems (or exhibits a concrete one), so it transfers through such a model; the faithfulness of any particular model is not checked here.

### 9. `total-equals-partial-plus-termination`

- **Kind:** characterization
- **Tier:** `T0` — Total correctness = partial correctness + termination (wp(S, Q) = wlp(S, Q) ∧ wp(S, true) in the predicate-transformer literature), stated for these fixpoints with termination as the absence of an infinite run.
- **Plain claim:** For every transition system (no branching assumption), postcondition Q and state s: wpLfp Q s holds if and only if wpGfp Q s holds and no run from s is infinite.
- **Depth:** `substantive`
- **Lean statement:**

```lean
-- lean/ToyFuelWP/Statements.lean:198-199
-- ToyFuelWP.Statements
theorem wpLfp_iff_wpGfp_and_not_hasInfiniteRun (S : System σ) (Q : σ → Prop) (s : σ) :
    wpLfp S Q s ↔ wpGfp S Q s ∧ ¬ HasInfiniteRun S s
```

- **Hypothesis ledger:** No hypotheses. The biconditional is stated for an arbitrary system `S`, postcondition `Q` and state `s`; there is no fuel parameter.
- **Non-vacuity witness:** Both sides hold at the countdownSys start state, which is not finitely branching (countdownSys_not_finitelyBranchingAt_start); at loopSys the left side fails while wpGfp holds and an infinite run exists. (`nonvacuity_wpLfp_iff_wpGfp_and_not_hasInfiniteRun`)
- **Logic (`#print axioms`):** wpLfp_iff_wpGfp_and_not_hasInfiniteRun: proved; #print axioms: Classical.choice, Quot.sound, propext. The forward direction has a proof with no axioms (wpGfp_and_not_hasInfiniteRun_of_wpLfp). The backward direction is not constructively provable: the statement implies Markov's principle even restricted to a deterministic system with decidable step and terminal predicates (markov_of_wpLfp_iff_wpGfp_and_not_hasInfiniteRun; #print axioms: no axioms), and Markov's principle is not derivable in intuitionistic logic. Whether more than Markov's principle (for example full dependent choice) is needed is not determined here.
  Evidence: `wpGfp_and_not_hasInfiniteRun_of_wpLfp` (none), `markov_of_wpLfp_iff_wpGfp_and_not_hasInfiniteRun` (none).
- **Non-claims:** see Boundaries, card 9.
- **Prior art:**
  - B. Alpern and F. B. Schneider. Defining liveness. Information Processing Letters 21(4):181–185, 1985. doi:10.1016/0020-0190(85)90056-0. Liveness properties say something good eventually happens; every property is the intersection of a safety property and a liveness property.
  - L. Lamport. Proving the correctness of multiprocess programs. IEEE Transactions on Software Engineering SE-3(2):125–143, 1977. doi:10.1109/TSE.1977.229904. Proofs of safety and liveness properties of concurrent programs (bibliographic record verified; content not re-read here).
  - G. Nelson. A generalization of Dijkstra's calculus. ACM TOPLAS 11(4):517–561, 1989. doi:10.1145/69558.69559. Generalizes the wp calculus by dropping the law of the excluded miracle, treats recursion by fixpoints, and relates the full wp/wlp semantics to a powerdomain semantics. Contrast: here wpLfp obeys the law of the excluded miracle (wpLfp_excluded_miracle) and every weakest precondition rejects stuck states, so a state without outcomes is an error, not a miracle.
  - E. W. Dijkstra and C. S. Scholten. Predicate Calculus and Program Semantics. Springer, 1990. doi:10.1007/978-1-4612-3228-5. Chapter 8 'Equations in predicates and their extreme solutions' (pp. 147–170) and chapter 9 'Semantics of repetitions' (pp. 170–189). The characterization of wlp of a repetition as the weakest (greatest) solution and wp as the strongest (least) solution of the loop equation was verified only through a secondary source (I. M. Rewitzky, Modelling the Algebra of Weakest Preconditions, MSc thesis, Department of Mathematics, University of Cape Town, 1991), not in the book itself.
  - W. H. Hesselink. Programs, Recursion and Unbounded Choice. Cambridge University Press, 1992. doi:10.1017/CBO9780511569784. Publisher's abstract: a complete account of the predicate transformation calculus semantics of sequential programs, including repetitions, recursive procedures, computational induction and unbounded nondeterminacy.
  - Iris Coq library, iris/program_logic/total_weakestpre.v and total_adequacy.v (as rendered in the Iris coqdoc): the total weakest precondition twp is defined as a least fixpoint (bi_least_fixpoint of twp_pre'), and twp_total derives strong normalization sn erased_step from a total-weakest-precondition proof — a mechanized least-fixpoint total weakest precondition in a separation logic.
  - V. Preoteasa. Algebra of Monotonic Boolean Transformers. Archive of Formal Proofs, September 2011 (isa-afp.org/entries/MonoBoolTranAlgebra.html). Abstract: an algebra of monotonic Boolean transformers modelling total correctness, refinement, demonic and angelic choice.
  - W. Guttmann. Algebras for Iteration, Infinite Executions and Correctness of Sequential Computations. Archive of Formal Proofs, October 2021 (isa-afp.org/entries/Correctness_Algebras.html). Abstract: algebras for iteration and infinite executions that unify computation models differing in the fixpoints used for iteration, and correctness statements across models.
  - D. Bridges, E. Palmgren and H. Ishihara. Constructive Mathematics. Stanford Encyclopedia of Philosophy, substantive revision of 25 August 2022, https://plato.stanford.edu/entries/mathematics-constructive/. Section 1 (Introduction): the limited principle of omniscience (LPO) is not constructively derivable (Kripke models; Bridges and Richman 1987, chapter 7). Section 2 (The Constructive Interpretation of Logic): Markov's principle (MP) is not constructively derivable (a Kripke model; Bridges and Richman 1987, pp. 137–138).
- **Design question:** A verification framework whose trusted kernel forbids coinductive definitions and general recursion defines its weakest precondition by structural recursion on fuel. For which properties is that the same as the coinductive (greatest-fixpoint) definition, how should 'verified at fuel n' be read, and where do the two differ (total correctness, divergence, liveness)? This card: the gap between the two notions is exactly termination.
- Basis: execution (Lean kernel check) — `wpLfp_iff_wpGfp_and_not_hasInfiniteRun`, and every counterexample and witness named above, are theorems checked by the Lean kernel under `leanprover/lean4:v4.34.1` with the axioms listed.
- Basis: derived (modeling bridge) — for a framework whose semantics is faithfully modeled as a `System σ` with the conventions of Applicability and whose fuel counts the same steps: the gap between the two notions is exactly termination. Reasoning: the Lean statement is universally quantified over systems (or exhibits a concrete one), so it transfers through such a model; the faithfulness of any particular model is not checked here.
- **Statements of the counterexamples, witnesses and controls named on this card:**

```lean
-- lean/ToyFuelWP/Counterexamples.lean:200-204
-- ToyFuelWP.Counterexamples
theorem nonvacuity_wpLfp_iff_wpGfp_and_not_hasInfiniteRun :
    (wpLfp countdownSys (fun _ => True) .start ∧ wpGfp countdownSys (fun _ => True) .start ∧
        ¬ HasInfiniteRun countdownSys .start) ∧
      (¬ wpLfp loopSys (fun _ => True) () ∧ wpGfp loopSys (fun _ => True) () ∧
        HasInfiniteRun loopSys ())

-- lean/ToyFuelWP/Systems.lean:387-388
-- ToyFuelWP.Systems
theorem countdownSys_not_finitelyBranchingAt_start :
    ¬ FinitelyBranchingAt countdownSys .start
```

### 10. `divergence-satisfies-every-partial-wp-and-no-total-wp`

- **Kind:** theorem
- **Tier:** `T0` — Partial correctness is insensitive to divergence; demonic total correctness rejects every state with an infinite run.
- **Plain claim:** If every run from s diverges without getting stuck (AlwaysDiverges S s: every state reachable from s is non-terminal and can step), then for every postcondition Q and fuel n, s satisfies wpFuel n Q and wpGfp Q and fails wpFuelTotal n Q and wpLfp Q. If merely some run from s is infinite (HasInfiniteRun S s), then s still fails wpFuelTotal n Q and wpLfp Q for every Q and n.
- **Depth:** `shallow`
- **Lean statement:**

```lean
-- lean/ToyFuelWP/Divergence.lean:112-115
-- ToyFuelWP.Divergence
theorem alwaysDiverges_satisfies_every_partial_wp_and_no_total_wp (S : System σ) (s : σ)
    (h : AlwaysDiverges S s) :
    (∀ n Q, wpFuel S n Q s) ∧ (∀ Q, wpGfp S Q s) ∧
      (∀ n Q, ¬ wpFuelTotal S n Q s) ∧ (∀ Q, ¬ wpLfp S Q s)

-- lean/ToyFuelWP/Divergence.lean:122-124
-- ToyFuelWP.Divergence
theorem hasInfiniteRun_refutes_every_total_wp (S : System σ) (s : σ)
    (h : HasInfiniteRun S s) :
    (∀ n Q, ¬ wpFuelTotal S n Q s) ∧ (∀ Q, ¬ wpLfp S Q s)
```

- **Hypothesis ledger:**
  - `h : AlwaysDiverges S s (in alwaysDiverges_satisfies_every_partial_wp_and_no_total_wp)` — no run halts or gets stuck, so no postcondition is ever checked. Tightness: **tight**; counterexample: `done_not_every_partial_wp`.
  - `h : HasInfiniteRun S s (in hasInfiniteRun_refutes_every_total_wp)` — one infinite run is enough to refute demonic total correctness. Tightness: **tight**; counterexample: `done_some_total_wp`.
- **Non-vacuity witness:** loopSys and spinOrOutSys at spin always diverge; spinOrExitSys at spin has an infinite run without always diverging. (`nonvacuity_alwaysDiverges`, `nonvacuity_hasInfiniteRun`)
- **Logic (`#print axioms`):** alwaysDiverges_satisfies_every_partial_wp_and_no_total_wp: proved; #print axioms: no axioms; hasInfiniteRun_refutes_every_total_wp: proved; #print axioms: no axioms.
- **Results backing the non-claims:** `spinOrExitSys_conjugate_ne_wpLfp`.
- **Non-claims:** see Boundaries, card 10.
- **Prior art:**
  - E. W. Dijkstra. Guarded commands, nondeterminacy and formal derivation of programs. Communications of the ACM 18(8):453–457, 1975. doi:10.1145/360933.360975. Defines only the total-correctness wp(S, R) — the weakest precondition guaranteeing proper termination in a state satisfying R; no liberal (partial-correctness) counterpart is defined there — and defines the loop by H0(R) = R ∧ ¬BB, Hk(R) = wp(IF, Hk-1(R)) ∨ H0(R), wp(DO, R) = (∃k ≥ 0: Hk(R)), with Hk(R) read as termination after at most k selections — an existentially fuel-indexed total weakest precondition. (Content read in the author's EWD418 transcription, whose abstract matches the published one.)
  - X. Leroy and H. Grall. Coinductive big-step operational semantics. Information and Computation 207(2):284–304, 2009. doi:10.1016/j.ic.2007.12.004. Coinductive big-step semantics describing diverging as well as terminating evaluations; the accompanying Coq development proves equivalences between big-step and small-step semantics.
  - J. Åman Pohjola, M. O. Myreen, M. Tanaka. A Hoare Logic for Diverging Programs. Archive of Formal Proofs, January 2023 (isa-afp.org/entries/HoareForDivergence.html). Abstract: a While language with output, a total-correctness Hoare logic proved sound and complete, and a new Hoare logic for programs that diverge, also proved sound and complete — a mechanized alternative for stating properties of diverging runs.
  - J. Åman Pohjola, H. Rostedt, M. O. Myreen. Characteristic Formulae for Liveness Properties of Non-Terminating CakeML Programs. ITP 2019, LIPIcs 141, 32:1–32:19. doi:10.4230/LIPIcs.ITP.2019.32 (DataCite record verified). Liveness reasoning for programs that are meant not to terminate (content beyond the title not re-read here).
- **Design question:** A verification framework whose trusted kernel forbids coinductive definitions and general recursion defines its weakest precondition by structural recursion on fuel. For which properties is that the same as the coinductive (greatest-fixpoint) definition, how should 'verified at fuel n' be read, and where do the two differ (total correctness, divergence, liveness)? This card: divergence is exactly where the two modes differ — partial weakest preconditions accept every must-diverging state, total ones reject every may-diverging state.
- Basis: execution (Lean kernel check) — `alwaysDiverges_satisfies_every_partial_wp_and_no_total_wp`, `hasInfiniteRun_refutes_every_total_wp`, and every counterexample and witness named above, are theorems checked by the Lean kernel under `leanprover/lean4:v4.34.1` with the axioms listed.
- Basis: derived (modeling bridge) — for a framework whose semantics is faithfully modeled as a `System σ` with the conventions of Applicability and whose fuel counts the same steps: divergence is exactly where the two modes differ — partial weakest preconditions accept every must-diverging state, total ones reject every may-diverging state. Reasoning: the Lean statement is universally quantified over systems (or exhibits a concrete one), so it transfers through such a model; the faithfulness of any particular model is not checked here.
- **Statements of the counterexamples, witnesses and controls named on this card:**

```lean
-- lean/ToyFuelWP/Counterexamples.lean:223-225
-- ToyFuelWP.Counterexamples
theorem done_not_every_partial_wp :
    ¬ AlwaysDiverges doneSys () ∧ ¬ wpGfp doneSys (fun _ => False) () ∧
      ¬ wpFuel doneSys 1 (fun _ => False) ()

-- lean/ToyFuelWP/Counterexamples.lean:231-233
-- ToyFuelWP.Counterexamples
theorem done_some_total_wp :
    ¬ HasInfiniteRun doneSys () ∧ wpLfp doneSys (fun _ => True) () ∧
      wpFuelTotal doneSys 1 (fun _ => True) ()

-- lean/ToyFuelWP/Counterexamples.lean:238
-- ToyFuelWP.Counterexamples
theorem nonvacuity_alwaysDiverges : AlwaysDiverges loopSys () ∧ AlwaysDiverges spinOrOutSys .spin

-- lean/ToyFuelWP/Counterexamples.lean:243-244
-- ToyFuelWP.Counterexamples
theorem nonvacuity_hasInfiniteRun :
    HasInfiniteRun spinOrExitSys .spin ∧ ¬ AlwaysDiverges spinOrExitSys .spin
```

### 11. `wpgfp-false-is-divergence`

- **Kind:** characterization
- **Tier:** `T0` — Analogue of reading wlp(S, false) as the states from which S cannot terminate, and the instance Q := False of gfp-adequacy; that reading was not located verbatim in a primary source checked.
- **Plain claim:** For every transition system and state s: s satisfies wpGfp (fun _ => False) if and only if every run from s diverges without getting stuck (AlwaysDiverges: every state reachable from s is non-terminal and can step); equivalently, s satisfies wpGfp Q for every postcondition Q.
- **Depth:** `shallow`
- **Lean statement:**

```lean
-- lean/ToyFuelWP/Divergence.lean:131-132
-- ToyFuelWP.Divergence
theorem wpGfp_false_iff_alwaysDiverges (S : System σ) (s : σ) :
    wpGfp S (fun _ => False) s ↔ AlwaysDiverges S s

-- lean/ToyFuelWP/Divergence.lean:140-141
-- ToyFuelWP.Divergence
theorem forall_wpGfp_iff_alwaysDiverges (S : System σ) (s : σ) :
    (∀ Q, wpGfp S Q s) ↔ AlwaysDiverges S s
```

- **Hypothesis ledger:** No hypotheses. Both biconditionals are stated for an arbitrary system `S` and state `s`, with no fuel parameter; `wpGfp_false_iff_alwaysDiverges` fixes the postcondition to `fun _ => False`, and `forall_wpGfp_iff_alwaysDiverges` quantifies over the postcondition inside the statement.
- **Non-vacuity witness:** loopSys and spinOrOutSys at spin. (`nonvacuity_alwaysDiverges`)
- **Logic (`#print axioms`):** wpGfp_false_iff_alwaysDiverges: proved; #print axioms: no axioms; forall_wpGfp_iff_alwaysDiverges: proved; #print axioms: no axioms.
- **Results backing the non-claims:** `alwaysDiverges_neg_spinOrExit`.
- **Non-claims:** see Boundaries, card 11.
- **Prior art:**
  - E. W. Dijkstra. A Discipline of Programming. Prentice-Hall, 1976 (ISBN 0-13-215871-X, seen only in a copyright-page snippet). Contains the chapter 'On nondeterminacy being bounded' (p. 72 per the table of contents). That the book introduces the weakest liberal precondition and states a continuity property for bounded nondeterminism was seen only through secondary sources and text snippets, not at the primary source.
  - E. W. Dijkstra and C. S. Scholten. Predicate Calculus and Program Semantics. Springer, 1990. doi:10.1007/978-1-4612-3228-5. Chapter 8 'Equations in predicates and their extreme solutions' (pp. 147–170) and chapter 9 'Semantics of repetitions' (pp. 170–189). The characterization of wlp of a repetition as the weakest (greatest) solution and wp as the strongest (least) solution of the loop equation was verified only through a secondary source (I. M. Rewitzky, Modelling the Algebra of Weakest Preconditions, MSc thesis, Department of Mathematics, University of Cape Town, 1991), not in the book itself.
  - G. Nelson. A generalization of Dijkstra's calculus. ACM TOPLAS 11(4):517–561, 1989. doi:10.1145/69558.69559. Generalizes the wp calculus by dropping the law of the excluded miracle, treats recursion by fixpoints, and relates the full wp/wlp semantics to a powerdomain semantics. Contrast: here wpLfp obeys the law of the excluded miracle (wpLfp_excluded_miracle) and every weakest precondition rejects stuck states, so a state without outcomes is an error, not a miracle.
- **Design question:** A verification framework whose trusted kernel forbids coinductive definitions and general recursion defines its weakest precondition by structural recursion on fuel. For which properties is that the same as the coinductive (greatest-fixpoint) definition, how should 'verified at fuel n' be read, and where do the two differ (total correctness, divergence, liveness)? This card: a partial-correctness proof of the postcondition False certifies must-divergence without errors, and must-diverging states are exactly those satisfying every partial-correctness weakest precondition.
- Basis: execution (Lean kernel check) — `wpGfp_false_iff_alwaysDiverges`, `forall_wpGfp_iff_alwaysDiverges`, and every counterexample and witness named above, are theorems checked by the Lean kernel under `leanprover/lean4:v4.34.1` with the axioms listed.
- Basis: derived (modeling bridge) — for a framework whose semantics is faithfully modeled as a `System σ` with the conventions of Applicability and whose fuel counts the same steps: a partial-correctness proof of the postcondition False certifies must-divergence without errors, and must-diverging states are exactly those satisfying every partial-correctness weakest precondition. Reasoning: the Lean statement is universally quantified over systems (or exhibits a concrete one), so it transfers through such a model; the faithfulness of any particular model is not checked here.
- **Statements of the counterexamples, witnesses and controls named on this card:**

```lean
-- lean/ToyFuelWP/Counterexamples.lean:238
-- ToyFuelWP.Counterexamples
theorem nonvacuity_alwaysDiverges : AlwaysDiverges loopSys () ∧ AlwaysDiverges spinOrOutSys .spin
```

### 12. `positive-partial-wp-cannot-reject-divergent-state`

- **Kind:** impossibility
- **Tier:** `T0` — Immediate from divergence-satisfies-every-partial-wp-and-no-total-wp (every positive partial-correctness weakest precondition is true at an always-diverging state); the safety/liveness distinction applied to weakest preconditions.
- **Plain claim:** For every transition system S and every predicate R on states: if some state s always diverges without getting stuck (AlwaysDiverges S s) and R fails at s, then no postcondition Q makes the positive partial-correctness weakest precondition wpGfp S Q equal to R on all states, and likewise for wpFuel S n Q at each fixed fuel n and for ∀ n, wpFuel S n Q (not_partial_wp_expressible_of_alwaysDiverges_of_not). The proof uses nothing about R except ¬ R s. Instances: the liveness property AllRunsEventually S P ('every run eventually reaches P') whenever an always-diverging state violates it, and concretely 'every run eventually reaches out' in the two-state spinOrOutSys and in the three-state startSpinOutSys, where the property also holds at a non-output state.
- **Depth:** `shallow`
- **Lean statement:**

```lean
-- lean/ToyFuelWP/Divergence.lean:152-156
-- ToyFuelWP.Divergence
theorem not_partial_wp_expressible_of_alwaysDiverges_of_not (S : System σ)
    (R : σ → Prop) (s : σ) (hdiv : AlwaysDiverges S s) (hviol : ¬ R s) :
    (¬ ∃ Q : σ → Prop, ∀ t, wpGfp S Q t ↔ R t) ∧
      (¬ ∃ (n : Nat) (Q : σ → Prop), ∀ t, wpFuel S n Q t ↔ R t) ∧
      (¬ ∃ Q : σ → Prop, ∀ t, (∀ n, wpFuel S n Q t) ↔ R t)

-- lean/ToyFuelWP/Divergence.lean:172-176
-- ToyFuelWP.Divergence
theorem allRunsEventually_not_partial_wp_of_divergent_violation (S : System σ)
    (P : σ → Prop) (s : σ) (hdiv : AlwaysDiverges S s) (hviol : ¬ AllRunsEventually S P s) :
    (¬ ∃ Q : σ → Prop, ∀ t, wpGfp S Q t ↔ AllRunsEventually S P t) ∧
      (¬ ∃ (n : Nat) (Q : σ → Prop), ∀ t, wpFuel S n Q t ↔ AllRunsEventually S P t) ∧
      (¬ ∃ Q : σ → Prop, ∀ t, (∀ n, wpFuel S n Q t) ↔ AllRunsEventually S P t)

-- lean/ToyFuelWP/Divergence.lean:209-214
-- ToyFuelWP.Divergence
theorem allRunsEventually_isOut_not_partial_wp_expressible :
    (¬ ∃ Q : LO → Prop, ∀ s, wpGfp spinOrOutSys Q s ↔ AllRunsEventually spinOrOutSys isOut s) ∧
      (¬ ∃ (n : Nat) (Q : LO → Prop),
        ∀ s, wpFuel spinOrOutSys n Q s ↔ AllRunsEventually spinOrOutSys isOut s) ∧
      (¬ ∃ Q : LO → Prop,
        ∀ s, (∀ n, wpFuel spinOrOutSys n Q s) ↔ AllRunsEventually spinOrOutSys isOut s)

-- lean/ToyFuelWP/Divergence.lean:306-312
-- ToyFuelWP.Divergence
theorem startSpinOutSys_allRunsEventually_not_partial_wp_expressible :
    (¬ ∃ Q : LO3 → Prop,
        ∀ s, wpGfp startSpinOutSys Q s ↔ AllRunsEventually startSpinOutSys isOut3 s) ∧
      (¬ ∃ (n : Nat) (Q : LO3 → Prop),
        ∀ s, wpFuel startSpinOutSys n Q s ↔ AllRunsEventually startSpinOutSys isOut3 s) ∧
      (¬ ∃ Q : LO3 → Prop,
        ∀ s, (∀ n, wpFuel startSpinOutSys n Q s) ↔ AllRunsEventually startSpinOutSys isOut3 s)
```

- **Hypothesis ledger:**
  - `hdiv : AlwaysDiverges S s (in not_partial_wp_expressible_of_alwaysDiverges_of_not and allRunsEventually_not_partial_wp_of_divergent_violation)` — makes s satisfy every positive partial-correctness weakest precondition. Tightness: **tight**; counterexample: `done_allRunsEventually_false_expressible`.
  - `hviol : ¬ R s (in not_partial_wp_expressible_of_alwaysDiverges_of_not; ¬ AllRunsEventually S P s in the liveness specialization)` — the predicate must fail somewhere that partial correctness cannot see. Tightness: **tight**; counterexample: `loop_allRunsEventually_true_expressible`.
- **Non-vacuity witness:** spinOrOutSys at spin and startSpinOutSys at spin, with R the property 'every run eventually reaches out'; the property holds at out in both systems and at the non-output state start of startSpinOutSys (reached through one step). (`nonvacuity_divergent_violation`, `nonvacuity_allRunsEventually_isOut_nontrivial`, `spinOrOutSys_spin_every_partial_wp_but_never_outputs`)
- **Positive controls (nearby settings where the conclusion fails):** `done_allRunsEventually_false_expressible`, `loop_allRunsEventually_true_expressible`, `allRunsEventually_isOut_iff_not_wpGfp_false`, `startSpinOutSys_wpGfp_iff_allRunsEventually_off_spin`, `allRunsEventually_isOut_iff_wpLfp_isOut`. See the escape hatches under Boundaries.
- **Logic (`#print axioms`):** not_partial_wp_expressible_of_alwaysDiverges_of_not: proved; #print axioms: no axioms; allRunsEventually_not_partial_wp_of_divergent_violation: proved; #print axioms: no axioms; allRunsEventually_isOut_not_partial_wp_expressible: proved; #print axioms: no axioms; startSpinOutSys_allRunsEventually_not_partial_wp_expressible: proved; #print axioms: no axioms.
- **Results backing the non-claims:** `allRunsEventually_isOut_iff_not_wpGfp_false`, `not_wpGfp_not_iff_wpLfp_of_deterministic_of_not_stuck`, `spinOrExitSys_conjugate_ne_wpLfp`, `stuckSys_conjugate_ne_wpLfp`, `spinOrEmitLoopSys_allRunsEventually_not_wp_expressible`, `startSpinOutSys_wpGfp_iff_allRunsEventually_off_spin`, `allRunsEventually_isOut_iff_wpLfp_isOut`.
- **Non-claims:** see Boundaries, card 12.
- **Prior art:**
  - B. Alpern and F. B. Schneider. Defining liveness. Information Processing Letters 21(4):181–185, 1985. doi:10.1016/0020-0190(85)90056-0. Liveness properties say something good eventually happens; every property is the intersection of a safety property and a liveness property.
  - L. Lamport. Proving the correctness of multiprocess programs. IEEE Transactions on Software Engineering SE-3(2):125–143, 1977. doi:10.1109/TSE.1977.229904. Proofs of safety and liveness properties of concurrent programs (bibliographic record verified; content not re-read here).
  - E. M. Clarke and E. A. Emerson. Design and synthesis of synchronization skeletons using branching time temporal logic. Logics of Programs, Lecture Notes in Computer Science, Springer, pp. 52–71. doi:10.1007/BFb0025774 (volume number and year are not given in the DOI record). Branching-time temporal logic, whose operator AF ('on all paths, eventually') is the shape of AllRunsEventually (bibliographic record verified; content not re-read here).
  - D. Kozen. Results on the propositional μ-calculus. Theoretical Computer Science 27(3):333–354, 1983. doi:10.1016/0304-3975(82)90125-6. The propositional μ-calculus, in which eventuality properties such as AF are least fixpoints and safety properties greatest fixpoints (bibliographic record verified; content not re-read here).
  - S. Spies, L. Gäher, D. Gratzer, J. Tassarotti, R. Krebbers, D. Dreyer, L. Birkedal. Transfinite Iris: resolving an existential dilemma of step-indexed separation logic. PLDI 2021, pp. 80–95. doi:10.1145/3453483.3454031. Moves the step index of Iris from natural numbers to ordinals to resolve a problem with existential quantification in step-indexed logics (bibliographic record and title verified; details not re-read here) — related to the limits of natural-number fuel under unbounded or existential choice.
  - J. Åman Pohjola, M. O. Myreen, M. Tanaka. A Hoare Logic for Diverging Programs. Archive of Formal Proofs, January 2023 (isa-afp.org/entries/HoareForDivergence.html). Abstract: a While language with output, a total-correctness Hoare logic proved sound and complete, and a new Hoare logic for programs that diverge, also proved sound and complete — a mechanized alternative for stating properties of diverging runs.
  - J. Åman Pohjola, H. Rostedt, M. O. Myreen. Characteristic Formulae for Liveness Properties of Non-Terminating CakeML Programs. ITP 2019, LIPIcs 141, 32:1–32:19. doi:10.4230/LIPIcs.ITP.2019.32 (DataCite record verified). Liveness reasoning for programs that are meant not to terminate (content beyond the title not re-read here).
- **Design question:** A verification framework whose trusted kernel forbids coinductive definitions and general recursion defines its weakest precondition by structural recursion on fuel. For which properties is that the same as the coinductive (greatest-fixpoint) definition, how should 'verified at fuel n' be read, and where do the two differ (total correctness, divergence, liveness)? This card: a property that fails at some always-diverging state — in particular a liveness obligation violated by divergence — cannot be stated as a single positive partial-correctness weakest precondition over the same state space; the escape hatches (negated partial weakest preconditions, total correctness on suitable systems, domain restriction, instrumented systems) each come with the limits recorded in the non-claims.
- Basis: execution (Lean kernel check) — `not_partial_wp_expressible_of_alwaysDiverges_of_not`, `allRunsEventually_not_partial_wp_of_divergent_violation`, `allRunsEventually_isOut_not_partial_wp_expressible`, `startSpinOutSys_allRunsEventually_not_partial_wp_expressible`, and every counterexample and witness named above, are theorems checked by the Lean kernel under `leanprover/lean4:v4.34.1` with the axioms listed.
- Basis: derived (modeling bridge) — for a framework whose semantics is faithfully modeled as a `System σ` with the conventions of Applicability and whose fuel counts the same steps: a property that fails at some always-diverging state — in particular a liveness obligation violated by divergence — cannot be stated as a single positive partial-correctness weakest precondition over the same state space; the escape hatches (negated partial weakest preconditions, total correctness on suitable systems, domain restriction, instrumented systems) each come with the limits recorded in the non-claims. Reasoning: the Lean statement is universally quantified over systems (or exhibits a concrete one), so it transfers through such a model; the faithfulness of any particular model is not checked here.
- **Statements of the counterexamples, witnesses and controls named on this card:**

```lean
-- lean/ToyFuelWP/Counterexamples.lean:254-259
-- ToyFuelWP.Counterexamples
theorem done_allRunsEventually_false_expressible :
    ¬ AlwaysDiverges doneSys () ∧ ¬ AllRunsEventually doneSys (fun _ => False) () ∧
      (∀ t, wpGfp doneSys (fun _ => False) t ↔ AllRunsEventually doneSys (fun _ => False) t) ∧
      (∀ t, wpFuel doneSys 1 (fun _ => False) t ↔ AllRunsEventually doneSys (fun _ => False) t) ∧
      (∀ t, (∀ n, wpFuel doneSys n (fun _ => False) t) ↔
        AllRunsEventually doneSys (fun _ => False) t)

-- lean/ToyFuelWP/Counterexamples.lean:280-285
-- ToyFuelWP.Counterexamples
theorem loop_allRunsEventually_true_expressible :
    AlwaysDiverges loopSys () ∧ AllRunsEventually loopSys (fun _ => True) () ∧
      (∀ t, wpGfp loopSys (fun _ => True) t ↔ AllRunsEventually loopSys (fun _ => True) t) ∧
      (∀ t, wpFuel loopSys 0 (fun _ => True) t ↔ AllRunsEventually loopSys (fun _ => True) t) ∧
      (∀ t, (∀ n, wpFuel loopSys n (fun _ => True) t) ↔
        AllRunsEventually loopSys (fun _ => True) t)

-- lean/ToyFuelWP/Counterexamples.lean:301-304
-- ToyFuelWP.Counterexamples
theorem nonvacuity_divergent_violation :
    (AlwaysDiverges spinOrOutSys .spin ∧ ¬ AllRunsEventually spinOrOutSys isOut .spin) ∧
      (AlwaysDiverges startSpinOutSys .spin ∧
        ¬ AllRunsEventually startSpinOutSys isOut3 .spin)

-- lean/ToyFuelWP/Counterexamples.lean:311-314
-- ToyFuelWP.Counterexamples
theorem nonvacuity_allRunsEventually_isOut_nontrivial :
    (AllRunsEventually spinOrOutSys isOut .out ∧ ¬ AllRunsEventually spinOrOutSys isOut .spin) ∧
      (¬ isOut3 .start ∧ AllRunsEventually startSpinOutSys isOut3 .start ∧
        ¬ AllRunsEventually startSpinOutSys isOut3 .spin)

-- lean/ToyFuelWP/Divergence.lean:238-240
-- ToyFuelWP.Divergence
theorem spinOrOutSys_spin_every_partial_wp_but_never_outputs :
    (∀ n Q, wpFuel spinOrOutSys n Q .spin) ∧ (∀ Q, wpGfp spinOrOutSys Q .spin) ∧
      ¬ AllRunsEventually spinOrOutSys isOut .spin

-- lean/ToyFuelWP/Boundaries.lean:80-81
-- ToyFuelWP.Boundaries
theorem allRunsEventually_isOut_iff_not_wpGfp_false (s : LO) :
    AllRunsEventually spinOrOutSys isOut s ↔ ¬ wpGfp spinOrOutSys (fun _ => False) s

-- lean/ToyFuelWP/Boundaries.lean:208-209
-- ToyFuelWP.Boundaries
theorem startSpinOutSys_wpGfp_iff_allRunsEventually_off_spin (s : LO3) (hs : s ≠ .spin) :
    wpGfp startSpinOutSys isOut3 s ↔ AllRunsEventually startSpinOutSys isOut3 s

-- lean/ToyFuelWP/Divergence.lean:225-226
-- ToyFuelWP.Divergence
theorem allRunsEventually_isOut_iff_wpLfp_isOut (s : LO) :
    wpLfp spinOrOutSys isOut s ↔ AllRunsEventually spinOrOutSys isOut s
```

### 13. `gfp-adequacy`

- **Kind:** characterization
- **Tier:** `T0` — Standard adequacy of a coinductive safety judgement, with its converse.
- **Plain claim:** For every transition system, postcondition Q and state s: if wpGfp Q s, then every finite run prefix from s ends in a state t with RunEndOk S Q t — t satisfies Q if it is terminal and has a successor if it is not (so no stuck state is reachable and every halted run ends in Q) (wpGfp_adequacy); conversely this property of all finite run prefixes implies wpGfp Q s (wpGfp_of_forall_reach_runEndOk); the biconditional wpGfp_iff_forall_reach_runEndOk is derived from the two.
- **Depth:** `shallow`
- **Lean statement:**

```lean
-- lean/ToyFuelWP/Statements.lean:249-250
-- ToyFuelWP.Statements
theorem wpGfp_adequacy (S : System σ) (Q : σ → Prop) (s : σ) (h : wpGfp S Q s) :
    ∀ k t, Reach S s k t → RunEndOk S Q t

-- lean/ToyFuelWP/Statements.lean:258-259
-- ToyFuelWP.Statements
theorem wpGfp_of_forall_reach_runEndOk (S : System σ) (Q : σ → Prop) (s : σ)
    (h : ∀ k t, Reach S s k t → RunEndOk S Q t) : wpGfp S Q s

-- lean/ToyFuelWP/Statements.lean:267-268
-- ToyFuelWP.Statements
theorem wpGfp_iff_forall_reach_runEndOk (S : System σ) (Q : σ → Prop) (s : σ) :
    wpGfp S Q s ↔ ∀ k t, Reach S s k t → RunEndOk S Q t
```

- **Hypothesis ledger:**
  - `h : wpGfp S Q s (in wpGfp_adequacy)` — the judgement whose meaning is stated; the theorem has no other hypothesis. Tightness: **tight**; counterexample: `wpGfp_adequacy_drop_h`.
  - `h : ∀ k t, Reach S s k t → RunEndOk S Q t (in wpGfp_of_forall_reach_runEndOk)` — every finite run prefix acceptable; the theorem has no other hypothesis. Tightness: **tight**; counterexample: `wpGfp_of_forall_reach_runEndOk_drop_h`.
- **Non-vacuity witness:** chainSys from 3 with postcondition (· = 0), exercising both branches of RunEndOk (the terminal state 0 reached in 3 steps and the non-terminal state 3); loopSys with postcondition False. (`nonvacuity_adequacy`)
- **Logic (`#print axioms`):** wpGfp_adequacy: proved; #print axioms: no axioms; wpGfp_of_forall_reach_runEndOk: proved; #print axioms: no axioms; wpGfp_iff_forall_reach_runEndOk: proved; #print axioms: no axioms.
- **Results backing the non-claims:** `em_of_disjunctive_adequacy`, `runEndOk_iff_or`, `runEndOk_iff_not_stuck`.
- **Non-claims:** see Boundaries, card 13.
- **Prior art:**
  - R. Jung, R. Krebbers, J.-H. Jourdan, A. Bizjak, L. Birkedal, D. Dreyer. Iris from the ground up: a modular foundation for higher-order concurrent separation logic. Journal of Functional Programming 28, e20, 2018. doi:10.1017/S0956796818000151. Section 6 defines a weakest precondition with the same case structure as wpStep (a value satisfies the postcondition; otherwise the expression is reducible and every successor satisfies the weakest precondition). It is not the same operator: in the Iris Coq library (iris/program_logic/weakestpre.v, definition wp_pre) value-hood is tested by the computable to_val, the recursive occurrence sits under fancy-update modalities (which quantify existentially over ghost-state updates) and later modalities, and wp is the guarded fixpoint of a contractive function.
  - Iris Coq library, iris/program_logic/adequacy.v (as rendered in the Iris coqdoc): the record adequate s e1 σ1 φ says that every value reached by a finite execution satisfies φ and, for s = NotStuck, that no reachable thread is stuck; wp_adequacy_gen derives adequate from a weakest-precondition proof — the analogue, for a guarded step-indexed weakest precondition, of the finite-run-prefix adequacy here.
- **Design question:** A verification framework whose trusted kernel forbids coinductive definitions and general recursion defines its weakest precondition by structural recursion on fuel. For which properties is that the same as the coinductive (greatest-fixpoint) definition, how should 'verified at fuel n' be read, and where do the two differ (total correctness, divergence, liveness)? This card: what a greatest-fixpoint partial-correctness proof guarantees operationally.
- Basis: execution (Lean kernel check) — `wpGfp_adequacy`, `wpGfp_of_forall_reach_runEndOk`, `wpGfp_iff_forall_reach_runEndOk`, and every counterexample and witness named above, are theorems checked by the Lean kernel under `leanprover/lean4:v4.34.1` with the axioms listed.
- Basis: derived (modeling bridge) — for a framework whose semantics is faithfully modeled as a `System σ` with the conventions of Applicability and whose fuel counts the same steps: what a greatest-fixpoint partial-correctness proof guarantees operationally. Reasoning: the Lean statement is universally quantified over systems (or exhibits a concrete one), so it transfers through such a model; the faithfulness of any particular model is not checked here.
- **Statements of the counterexamples, witnesses and controls named on this card:**

```lean
-- lean/ToyFuelWP/Counterexamples.lean:331-333
-- ToyFuelWP.Counterexamples
theorem wpGfp_adequacy_drop_h :
    ¬ wpGfp stuckSys (fun _ => True) () ∧
      ¬ (∀ k t, Reach stuckSys () k t → RunEndOk stuckSys (fun _ => True) t)

-- lean/ToyFuelWP/Counterexamples.lean:340-342
-- ToyFuelWP.Counterexamples
theorem wpGfp_of_forall_reach_runEndOk_drop_h :
    ¬ (∀ k t, Reach stuckSys () k t → RunEndOk stuckSys (fun _ => True) t) ∧
      ¬ wpGfp stuckSys (fun _ => True) ()

-- lean/ToyFuelWP/Counterexamples.lean:359-365
-- ToyFuelWP.Counterexamples
theorem nonvacuity_adequacy :
    (wpGfp chainSys (fun s => s = 0) 3 ∧
        (∀ k t, Reach chainSys 3 k t → RunEndOk chainSys (fun s => s = 0) t) ∧
        (Reach chainSys 3 3 0 ∧ chainSys.terminal 0) ∧
        (Reach chainSys 3 0 3 ∧ ¬ chainSys.terminal 3)) ∧
      (wpGfp loopSys (fun _ => False) () ∧
        ∀ k t, Reach loopSys () k t → RunEndOk loopSys (fun _ => False) t)
```

### 14. `fixpoint-definitions-adequate`

- **Kind:** characterization
- **Tier:** `T0` — Knaster–Tarski (Tarski 1955) for the specific monotone operator wpStep.
- **Plain claim:** wpGfp S Q (the union of all post-fixed points of wpStep S Q) is a fixed point of wpStep S Q (wpGfp_unfold) that contains every post-fixed point (wpGfp_coinduction: PostFixed S Q X and X s imply wpGfp S Q s), and wpLfp S Q (the intersection of all pre-fixed points) is a fixed point (wpLfp_unfold) contained in every pre-fixed point (wpLfp_induction: PreFixed S Q X and wpLfp S Q s imply X s); so they are the greatest and the least fixpoints.
- **Depth:** `definitional`
- **Lean statement:**

```lean
-- lean/ToyFuelWP/Defs.lean:256-257
-- ToyFuelWP.Defs
theorem wpGfp_unfold (S : System σ) (Q : σ → Prop) (s : σ) :
    wpGfp S Q s ↔ wpStep S Q (wpGfp S Q) s

-- lean/ToyFuelWP/Defs.lean:251-252
-- ToyFuelWP.Defs, section Basic: `variable {S : System σ} {Q : σ → Prop}`, so S and Q
-- are implicit arguments (full type: ∀ {σ : Type u} {S : System σ} {Q X : σ → Prop},
-- PostFixed S Q X → ∀ {s : σ}, X s → wpGfp S Q s)
theorem wpGfp_coinduction {X : σ → Prop} (hX : PostFixed S Q X) {s : σ} (hs : X s) :
    wpGfp S Q s

-- lean/ToyFuelWP/Defs.lean:277-278
-- ToyFuelWP.Defs
theorem wpLfp_unfold (S : System σ) (Q : σ → Prop) (s : σ) :
    wpLfp S Q s ↔ wpStep S Q (wpLfp S Q) s

-- lean/ToyFuelWP/Defs.lean:272-273
-- ToyFuelWP.Defs, section Basic: `variable {S : System σ} {Q : σ → Prop}`, so S and Q
-- are implicit arguments (full type: ∀ {σ : Type u} {S : System σ} {Q X : σ → Prop},
-- PreFixed S Q X → ∀ {s : σ}, wpLfp S Q s → X s)
theorem wpLfp_induction {X : σ → Prop} (hX : PreFixed S Q X) {s : σ} (hs : wpLfp S Q s) :
    X s
```

- **Hypothesis ledger:**
  - `hX : PostFixed S Q X (in wpGfp_coinduction)` — the coinduction invariant. Tightness: **tight**; counterexample: `wpGfp_coinduction_drop_hX`.
  - `hs : X s (in wpGfp_coinduction)` — the state lies in the invariant. Tightness: **tight**; counterexample: `wpGfp_coinduction_drop_hs`.
  - `hX : PreFixed S Q X (in wpLfp_induction)` — the induction predicate is closed under wpStep. Tightness: **tight**; counterexample: `wpLfp_induction_drop_hX`.
  - `hs : wpLfp S Q s (in wpLfp_induction)` — the state is in the least fixpoint. Tightness: **tight**; counterexample: `wpLfp_induction_drop_hs`.
- **Non-vacuity witness:** X := True is a post-fixed point of wpStep loopSys False holding at (); X := isOut is a non-trivial pre-fixed point of wpStep spinOrOutSys isOut and out satisfies wpLfp spinOrOutSys isOut; wpGfp loopSys False () and wpLfp chainSys (· = 0) 3 hold. (`nonvacuity_coinduction_induction`, `wpGfp_pos_loop_false`, `wpLfp_pos_chain`)
- **Logic (`#print axioms`):** wpGfp_unfold: proved; #print axioms: no axioms; wpGfp_coinduction: proved; #print axioms: no axioms; wpLfp_unfold: proved; #print axioms: no axioms; wpLfp_induction: proved; #print axioms: no axioms.
- **Results backing the non-claims:** `loopSys_wpLfp_ne_wpGfp`.
- **Non-claims:** see Boundaries, card 14.
- **Prior art:**
  - A. Tarski. A lattice-theoretical fixpoint theorem and its applications. Pacific Journal of Mathematics 5(2):285–309, 1955. doi:10.2140/pjm.1955.5.285. The fixed points of a monotone map on a complete lattice form a complete lattice; in particular least and greatest fixed points exist (the source of the impredicative definitions of wpLfp and wpGfp).
  - Mathlib, Mathlib/Order/FixedPoints.lean (github.com/leanprover-community/mathlib4, master): OrderHom.lfp / OrderHom.gfp on a complete lattice, defined as the infimum of pre-fixed points / supremum of post-fixed points, with lfp_le, le_gfp, map_lfp, map_gfp and fixedPoints.completeLattice (Knaster–Tarski) — the same impredicative construction as wpLfp / wpGfp, in general form.
  - P. Cousot and R. Cousot. Constructive versions of Tarski's fixed point theorems. Pacific Journal of Mathematics 82(1):43–57, 1979. doi:10.2140/pjm.1979.82.43. Fixpoints of monotone maps via transfinite iteration without continuity, contrasted with the ω-iteration that needs continuity.
  - Lean 4 reference manual, recursive definitions: partial_fixpoint (introduced in Lean v4.17.0, leanprover/lean4 pull request 6355) defines functions as least fixpoints of monotone equations in chain-complete partial orders (for example Option-valued functions) and generates a partial-correctness theorem; lattice-theoretic least/greatest-fixpoint predicates (introduced in v4.20.0, pull request 8097; named inductive_fixpoint / coinductive_fixpoint from v4.23.0) use Knaster–Tarski on Prop with (co)induction principles. Source: github.com/leanprover/reference-manual, files Manual/RecursiveDefs/PartialFixpoint.lean and Manual/RecursiveDefs/CoinductivePredicates.lean. This package uses neither; its wpGfp and wpLfp are hand-written impredicative fixpoints.
  - Lean v4.25.0 release notes (github.com/leanprover/reference-manual, Manual/Releases/v4_25_0.lean): pull request leanprover/lean4#10333 introduces a coinductive keyword that defines coinductive predicates with the same syntax as inductive. The pinned toolchain v4.34.1 therefore offers coinductive predicates; this package does not use them, so that its definitions also make sense for a kernel without them.
- **Design question:** Reference point: the impredicative definitions used in place of coinductive types are the intended fixpoints.
- Basis: execution (Lean kernel check) — `wpGfp_unfold`, `wpGfp_coinduction`, `wpLfp_unfold`, `wpLfp_induction`, and every counterexample and witness named above, are theorems checked by the Lean kernel under `leanprover/lean4:v4.34.1` with the axioms listed.
- Basis: derived (modeling bridge) — for any semantics faithfully modeled as a `System σ` with the conventions of Applicability: `wpGfp S Q` and `wpLfp S Q` are the greatest and the least fixpoints of the one-step operator `wpStep S Q` (this card involves no fuel). Reasoning: the four Lean statements are universally quantified over systems and postconditions, so they transfer through such a model; the faithfulness of any particular model is not checked here.
- **Statements of the counterexamples, witnesses and controls named on this card:**

```lean
-- lean/ToyFuelWP/Counterexamples.lean:376-378
-- ToyFuelWP.Counterexamples
theorem wpGfp_coinduction_drop_hX :
    (fun _ : Unit => True) () ∧ ¬ PostFixed stuckSys (fun _ => True) (fun _ => True) ∧
      ¬ wpGfp stuckSys (fun _ => True) ()

-- lean/ToyFuelWP/Counterexamples.lean:385-387
-- ToyFuelWP.Counterexamples
theorem wpGfp_coinduction_drop_hs :
    PostFixed stuckSys (fun _ => True) (fun _ => False) ∧ ¬ (fun _ : Unit => False) () ∧
      ¬ wpGfp stuckSys (fun _ => True) ()

-- lean/ToyFuelWP/Counterexamples.lean:394-396
-- ToyFuelWP.Counterexamples
theorem wpLfp_induction_drop_hX :
    wpLfp doneSys (fun _ => True) () ∧ ¬ PreFixed doneSys (fun _ => True) (fun _ => False) ∧
      ¬ (fun _ : Unit => False) ()

-- lean/ToyFuelWP/Counterexamples.lean:403-405
-- ToyFuelWP.Counterexamples
theorem wpLfp_induction_drop_hs :
    PreFixed loopSys (fun _ => True) (fun _ => False) ∧ ¬ wpLfp loopSys (fun _ => True) () ∧
      ¬ (fun _ : Unit => False) ()

-- lean/ToyFuelWP/Counterexamples.lean:412-414
-- ToyFuelWP.Counterexamples
theorem nonvacuity_coinduction_induction :
    (PostFixed loopSys (fun _ => False) (fun _ => True) ∧ (fun _ : Unit => True) ()) ∧
      (PreFixed spinOrOutSys isOut isOut ∧ wpLfp spinOrOutSys isOut .out)

-- lean/ToyFuelWP/Examples.lean:123
-- ToyFuelWP.Examples
theorem wpGfp_pos_loop_false : wpGfp loopSys (fun _ => False) ()

-- lean/ToyFuelWP/Examples.lean:152
-- ToyFuelWP.Examples
theorem wpLfp_pos_chain : wpLfp chainSys (fun s => s = 0) 3
```

## Boundaries

### Non-claims, card by card

**1. `partial-fuel-equals-gfp`**

- Does not say that any single fuel n suffices: for every n there is a state satisfying wpFuel n Q but not wpGfp Q (fixed_fuel_wpFuel_not_imp_wpGfp). Only the quantifier over all fuels gives the equivalence.
- Says nothing about total correctness; the analogous statement for wpFuelTotal and the least fixpoint needs finite branching (see total-fuel-complete-under-finite-branching and unbounded-choice-no-uniform-fuel).
- The no-branching-assumption equivalence relies on the recursive occurrence appearing in wpStep only under universal quantification over successors and under implication, so that iterating from True commutes with the meet over all fuels. It does not extend to one-step operators that place the recursive occurrence under an existential over an infinite set — angelic choice of a successor, existential ghost-state updates as in separation-logic weakest preconditions, or existential stuttering: for the angelic operator wpStepAngelic, the state start of fanToStuckSys satisfies the fuel version at every fuel but not the greatest fixpoint (fanToStuckSys_angelic_forall_fuel_not_gfp).
- wpStep has the case structure of the weakest precondition of Iris-style program logics but is not that operator: Iris tests value-hood computably, wraps the recursive occurrence in update modalities (existential over ghost-state updates) and later modalities, and takes a guarded step-indexed fixpoint. Nothing here is claimed about that operator.
- Proving ∀ n, wpFuel S n Q s does not avoid discovering loop invariants: an induction on fuel for a looping state still has to strengthen the induction hypothesis to an invariant, that is, a post-fixed predicate of wpStep S Q.
- Structural recursion on fuel makes wpFuel S n Q s unfoldable at a concrete numeral n; it does not make the statement ∀ n, wpFuel S n Q s decidable, computable or checkable by evaluation.
- Does not imply that a kernel without coinductive types or partial definitions must use fuel: wpGfp is itself defined in core Lean by impredicative quantification over σ → Prop, with no coinductive type, partial definition or library fixpoint. Fuel is forced only if impredicative quantification over predicates is also unavailable, or if unfolding to a concrete depth is wanted.
- Does not relate wpFuel to interaction-tree equivalences, the delay monad, step-indexed logical relations, Lean's partial_fixpoint or Lean's coinductive predicates; the coinductive side here is a greatest fixpoint of predicates on states, written impredicatively.
- Fuel counts steps of this abstract relation plus one final check; a concrete interpreter that counts fuel differently (per loop iteration, per call) is related only through a re-indexing argument that is not given here.
- Relies on two conventions: terminal states halt (edges leaving them are ignored) and stuck states are errors that every weakest precondition rejects. A framework in which stuck states are allowed (blocking assumptions) or terminal states may continue needs different statements.
- Toy model: an abstract small-step relation with terminal states; no program syntax, heap, concurrency, probabilistic choice, I/O events or traces. These theorems neither establish nor refute the corresponding claims about the fuel-indexed or fixpoint weakest preconditions of any concrete language, interpreter or verification framework (such as an Iris-style program logic). Transfer to a concrete semantics requires a separate modeling argument that this package does not provide.

**2. `fixed-fuel-does-not-give-partial-correctness`**

- The counterexample state depends on n. It does not show a state satisfying wpFuel at every fuel but failing wpGfp; no such state exists (partial-fuel-equals-gfp).
- Uses an infinite-state system (downToStuckSys on Nat) with arbitrarily long error-free prefixes; it does not rule out that a single fixed fuel suffices on finite-state or bounded-depth systems (not formalized here).
- The failure is an error (stuck state), not a postcondition violation; a postcondition violation at distance n behaves the same way but is not separately stated.
- Toy model: an abstract small-step relation with terminal states; no program syntax, heap, concurrency, probabilistic choice, I/O events or traces. These theorems neither establish nor refute the corresponding claims about the fuel-indexed or fixpoint weakest preconditions of any concrete language, interpreter or verification framework (such as an Iris-style program logic). Transfer to a concrete semantics requires a separate modeling argument that this package does not provide.

**3. `fuel-monotonicity-opposite-directions`**

- Failure at a single fuel n means opposite things in the two modes: by antitonicity, ¬ wpFuel S n Q s refutes wpFuel S m Q s for every m ≥ n and refutes wpGfp S Q s (via wpFuel_of_wpGfp); by monotonicity, ¬ wpFuelTotal S n Q s does not refute wpLfp S Q s — a larger fuel may still succeed (wpFuelTotal_neg_chain_short and wpLfp_pos_chain: chainSys from 3 fails at fuel 3 but is totally correct).
- Monotonicity in fuel is not monotonicity in the postcondition; the latter is not stated here.
- Does not say the fuel transformers stabilise at a finite fuel; they need not (fixed-fuel-does-not-give-partial-correctness, unbounded-choice-no-uniform-fuel).
- The statements are about these two transformers with base cases True and False; a fuel semantics with another base case (for example 'out of fuel is an error' in a partial setting) is not covered.
- Toy model: an abstract small-step relation with terminal states; no program syntax, heap, concurrency, probabilistic choice, I/O events or traces. These theorems neither establish nor refute the corresponding claims about the fuel-indexed or fixpoint weakest preconditions of any concrete language, interpreter or verification framework (such as an Iris-style program logic). Transfer to a concrete semantics requires a separate modeling argument that this package does not provide.

**4. `partial-fuel-n-reading`**

- Says nothing about run prefixes of n or more steps: a state verified at fuel n may reach an error or a Q-violation at step n.
- At fuel 0, wpFuel S 0 Q s is identically True and checks nothing — not even whether s itself is stuck or violates Q (wpFuel_pos_zero_stuck); checking the initial state alone needs fuel 1 (one unit of fuel per step plus one final check).
- Does not say anything about termination: diverging states satisfy wpFuel at every fuel.
- Relies on two conventions: terminal states halt (edges leaving them are ignored) and stuck states are errors that every weakest precondition rejects. A framework in which stuck states are allowed (blocking assumptions) or terminal states may continue needs different statements.
- Toy model: an abstract small-step relation with terminal states; no program syntax, heap, concurrency, probabilistic choice, I/O events or traces. These theorems neither establish nor refute the corresponding claims about the fuel-indexed or fixpoint weakest preconditions of any concrete language, interpreter or verification framework (such as an Iris-style program logic). Transfer to a concrete semantics requires a separate modeling argument that this package does not provide.

**5. `total-fuel-n-reading`**

- Failure of wpFuelTotal S n Q s does not mean that s diverges, gets stuck or violates Q; it may only mean that the fuel n is too small. At n = 0 it fails for every state, including a terminal state satisfying Q (wpFuelTotal_neg_zero_done): a terminal state needs fuel 1.
- Because wpStep is written with implications rather than a disjunction on S.terminal, a total-correctness judgement establishes, without classical logic or a decidable terminal predicate, only ¬¬ S.terminal at the end of a bounded run, not S.terminal itself (wpFuelTotal_propSys_one_iff_not_not: in a one-state system without steps whose state is terminal exactly when P holds, wpFuelTotal at fuel 1 is equivalent to ¬¬ P). The operational reading 'halts in a terminal state satisfying Q' is classical.
- The bound is on steps of this abstract relation; it is not a bound on any concrete cost measure.
- Does not give a way to compute the least sufficient fuel.
- Relies on two conventions: terminal states halt (edges leaving them are ignored) and stuck states are errors that every weakest precondition rejects. A framework in which stuck states are allowed (blocking assumptions) or terminal states may continue needs different statements.
- Toy model: an abstract small-step relation with terminal states; no program syntax, heap, concurrency, probabilistic choice, I/O events or traces. These theorems neither establish nor refute the corresponding claims about the fuel-indexed or fixpoint weakest preconditions of any concrete language, interpreter or verification framework (such as an Iris-style program logic). Transfer to a concrete semantics requires a separate modeling argument that this package does not provide.

**6. `total-fuel-sound-for-lfp`**

- The converse of the first statement needs finite branching (total-fuel-complete-under-finite-branching) and fails without it (unbounded-choice-no-uniform-fuel).
- The converse of the second statement fails outright: wpGfp does not imply wpFuelTotal at any fuel (loopSys, loop_finitelyBranching_no_total_fuel).
- Relies on wpFuelTotal, wpLfp and wpGfp sharing the same one-step operator wpStep (demonic choice, terminal states halt, stuck states are errors). In a framework whose total and partial modes treat stuck states differently (for example stuck states blocking, or miraculous, in the partial mode only), total correctness need not imply partial correctness in this form.
- Toy model: an abstract small-step relation with terminal states; no program syntax, heap, concurrency, probabilistic choice, I/O events or traces. These theorems neither establish nor refute the corresponding claims about the fuel-indexed or fixpoint weakest preconditions of any concrete language, interpreter or verification framework (such as an Iris-style program logic). Transfer to a concrete semantics requires a separate modeling argument that this package does not provide.

**7. `total-fuel-complete-under-finite-branching`**

- The fuel bound depends on the initial state: the statement is ∀ s, (… → ∃ n, wpFuelTotal S n Q s), not ∃ n, ∀ s, …. No single fuel need work for all initial states satisfying a precondition, even for a deterministic system: in chainSys every k satisfies wpFuelTotal chainSys (k + 1) (· = 0) k but no single n works for all k (chainSys_fuel_per_state_not_uniform).
- A sequential language whose operational model represents unbounded external input, unbounded nondeterministic allocation or any choice from an infinite set as transition steps is not finitely branching and is not covered (see unbounded-choice-no-uniform-fuel); finite-width choice (for example of an arbitrary 64-bit integer) remains finitely branching.
- Does not say total-fuel completeness is constructively provable in general: it implies the limited principle of omniscience (see logic). Constructive proofs exist under extra decidability, for example deterministic systems with decidable terminal states (exists_wpFuelTotal_of_wpLfp_of_deterministic_of_decidable_terminal).
- Finite branching is sufficient, not necessary: an infinitely branching state whose successors have uniformly bounded fuel also has a fuel bound; no exact characterization of when a fuel bound exists is given beyond ∃ n itself.
- Gives no explicit or computable fuel bound.
- In the König form, termination of every run is assumed, not established; the theorem does not help to prove termination.
- Deterministic constrains only non-terminal states (edges leaving terminal states are ignored, deterministic_pos_termBranch). A concrete interpreter is covered only if it is faithfully modeled as such a system with the same notion of terminal and stuck states.
- Toy model: an abstract small-step relation with terminal states; no program syntax, heap, concurrency, probabilistic choice, I/O events or traces. These theorems neither establish nor refute the corresponding claims about the fuel-indexed or fixpoint weakest preconditions of any concrete language, interpreter or verification framework (such as an Iris-style program logic). Transfer to a concrete semantics requires a separate modeling argument that this package does not provide.

**8. `unbounded-choice-no-uniform-fuel`**

- Shows only that natural-number fuel (∃ n : Nat, wpFuelTotal n) fails to capture total correctness of countdownSys; total correctness of countdownSys is still expressed by the least fixpoint wpLfp (proved here, countdownSys_start_wpLfp), and could be proved with ordinal-indexed fuel or well-founded induction (not formalized here).
- Requires genuinely infinite branching (a choice from all of Nat); bounded-width nondeterminism, such as choosing an arbitrary fixed-width machine integer, is finitely branching, and then total correctness does give a fuel bound per initial state (total-fuel-complete-under-finite-branching).
- Does not say the partial-correctness side fails: partial correctness of this state is still equivalent to wpFuel at every fuel (partial-fuel-equals-gfp).
- Toy model: an abstract small-step relation with terminal states; no program syntax, heap, concurrency, probabilistic choice, I/O events or traces. These theorems neither establish nor refute the corresponding claims about the fuel-indexed or fixpoint weakest preconditions of any concrete language, interpreter or verification framework (such as an Iris-style program logic). Transfer to a concrete semantics requires a separate modeling argument that this package does not provide.

**9. `total-equals-partial-plus-termination`**

- Termination here is the absence of an infinite run; it is not a uniform bound on run length (see unbounded-choice-no-uniform-fuel).
- Relies on demonic quantification over all successors and on stuck states being errors rejected by wpGfp. Under angelic nondeterminism total correctness would need only one terminating run rather than the absence of every infinite run, and if stuck states were blocking or miraculous, wpGfp ∧ ¬ HasInfiniteRun would admit stuck states; neither variant is covered.
- Only the forward direction is constructive; the backward direction needs at least Markov's principle (see logic).
- Says nothing about fairness or other liveness properties.
- Toy model: an abstract small-step relation with terminal states; no program syntax, heap, concurrency, probabilistic choice, I/O events or traces. These theorems neither establish nor refute the corresponding claims about the fuel-indexed or fixpoint weakest preconditions of any concrete language, interpreter or verification framework (such as an Iris-style program logic). Transfer to a concrete semantics requires a separate modeling argument that this package does not provide.

**10. `divergence-satisfies-every-partial-wp-and-no-total-wp`**

- Stuck states are not diverging states: a state that gets stuck (non-terminal, no successor) fails both partial and total weakest preconditions, whereas AlwaysDiverges requires every reachable state to be non-terminal and able to step.
- A state with an infinite run need not satisfy every partial-correctness weakest precondition: if it also has halting or stuck runs, partial correctness still constrains them (spinOrExitSys at spin fails wpGfp spinOrExitSys (fun t => ¬ isOut t), spinOrExitSys_conjugate_ne_wpLfp).
- An infinite run is sufficient, not necessary, for failing every total weakest precondition: a reachable stuck state also suffices.
- Does not say partial correctness is useless; it says partial correctness carries no information about termination.
- All weakest preconditions here quantify over every successor (demonic nondeterminism); nothing is said about angelic (exists-a-successor) transformers.
- Toy model: an abstract small-step relation with terminal states; no program syntax, heap, concurrency, probabilistic choice, I/O events or traces. These theorems neither establish nor refute the corresponding claims about the fuel-indexed or fixpoint weakest preconditions of any concrete language, interpreter or verification framework (such as an Iris-style program logic). Transfer to a concrete semantics requires a separate modeling argument that this package does not provide.

**11. `wpgfp-false-is-divergence`**

- Characterizes must-divergence without getting stuck (AlwaysDiverges), not may-divergence (HasInfiniteRun): a nondeterministic state with both a diverging run and a halting run (spinOrExitSys at spin, alwaysDiverges_neg_spinOrExit) fails wpGfp False.
- Here 'diverges' includes 'never gets stuck': stuck states are safety errors rejected by wpGfp, so a state that never halts because it gets stuck fails wpGfp False. This differs from calculi in which the liberal precondition of a non-terminating or miraculous command for false is true.
- Toy model: an abstract small-step relation with terminal states; no program syntax, heap, concurrency, probabilistic choice, I/O events or traces. These theorems neither establish nor refute the corresponding claims about the fuel-indexed or fixpoint weakest preconditions of any concrete language, interpreter or verification framework (such as an Iris-style program logic). Transfer to a concrete semantics requires a separate modeling argument that this package does not provide.

**12. `positive-partial-wp-cannot-reject-divergent-state`**

- Rules out only a single positive partial-correctness weakest precondition (wpGfp S Q, wpFuel S n Q or ∀ n, wpFuel S n Q). It does not rule out negations or Boolean combinations of partial weakest preconditions: on spinOrOutSys itself, AllRunsEventually spinOrOutSys isOut s holds iff wpGfp spinOrOutSys (fun _ => False) s fails (allRunsEventually_isOut_iff_not_wpGfp_false), and on every deterministic system without stuck states the conjugate ¬ wpGfp S (fun t => ¬ Q t) coincides with wpLfp S Q (not_wpGfp_not_iff_wpLfp_of_deterministic_of_not_stuck; both side conditions are needed, spinOrExitSys_conjugate_ne_wpLfp and stuckSys_conjugate_ne_wpLfp).
- Does not imply that total correctness (wpLfp) expresses AllRunsEventually S P in general: wpLfp spinOrOutSys isOut coincides with the property only because the output state out is terminal (allRunsEventually_isOut_iff_wpLfp_isOut). In a system that reaches P at a non-terminal state and keeps running (spinOrEmitLoopSys), the property is expressed by no wpGfp, wpLfp or wpFuelTotal weakest precondition for any postcondition (spinOrEmitLoopSys_allRunsEventually_not_wp_expressible).
- Quantifies the equivalence over the entire state space. Restricting it to states satisfying a precondition that excludes the always-diverging violating states defeats the impossibility: off the state spin, AllRunsEventually startSpinOutSys isOut3 coincides with wpGfp startSpinOutSys isOut3 (startSpinOutSys_wpGfp_iff_allRunsEventually_off_spin).
- The mechanism is generic, not specific to liveness: every positive partial-correctness weakest precondition is forced true at an always-diverging state, so any predicate false there is inexpressible. In spinOrOutSys no transition enters out and out is terminal, so there the liveness property coincides with spinOrOutSys.terminal and the two-state instance tests halting versus non-halting; startSpinOutSys is the instance in which the output is reached after a step.
- ¬ AllRunsEventually S P s is the negation of an inductive predicate. Reading it as 'some run never reaches P' (extracting a violating run) needs classical reasoning and is not part of any statement here.
- Expressibility is over postconditions on the same state space and the same system. It does not exclude encoding a liveness property as a partial-correctness weakest precondition of a modified system (for example one instrumented with a counter or prophecy that turns bounded liveness into safety).
- Does not say AllRunsEventually is never a partial-correctness weakest precondition: on systems without an always-diverging violating state it may coincide with one (loop_allRunsEventually_true_expressible, done_allRunsEventually_false_expressible).
- Does not cover angelic ('some run eventually') liveness, fairness, or output events on traces.
- Toy model: an abstract small-step relation with terminal states; no program syntax, heap, concurrency, probabilistic choice, I/O events or traces. These theorems neither establish nor refute the corresponding claims about the fuel-indexed or fixpoint weakest preconditions of any concrete language, interpreter or verification framework (such as an Iris-style program logic). Transfer to a concrete semantics requires a separate modeling argument that this package does not provide.

**13. `gfp-adequacy`**

- The statement uses implications (RunEndOk); the disjunctive reading 'either terminal and Q, or non-terminal and extendable' (runEndOk_iff_or) and the reading 'not stuck, and Q if terminal' (runEndOk_iff_not_stuck) are classical. A disjunctive adequacy statement for all systems implies excluded middle (em_of_disjunctive_adequacy).
- Q is guaranteed only at terminal states, not at the intermediate non-terminal states of a run prefix: partial correctness is not a state invariant (in nonvacuity_adequacy the reachable non-terminal state 3 does not satisfy Q = (· = 0)).
- Adequacy is about finite run prefixes; it says nothing about infinite runs (which are unconstrained) or about termination.
- Relative to the abstract relation only; adequacy for a concrete language requires that its operational semantics is the system used here.
- Relies on two conventions: terminal states halt (edges leaving them are ignored) and stuck states are errors that every weakest precondition rejects. A framework in which stuck states are allowed (blocking assumptions) or terminal states may continue needs different statements.
- Toy model: an abstract small-step relation with terminal states; no program syntax, heap, concurrency, probabilistic choice, I/O events or traces. These theorems neither establish nor refute the corresponding claims about the fuel-indexed or fixpoint weakest preconditions of any concrete language, interpreter or verification framework (such as an Iris-style program logic). Transfer to a concrete semantics requires a separate modeling argument that this package does not provide.

**14. `fixpoint-definitions-adequate`**

- Does not assert uniqueness of the fixed point of wpStep S Q: whenever a state can diverge, wpLfp S Q and wpGfp S Q are distinct fixed points (loopSys_wpLfp_ne_wpGfp).
- Reference point justifying the definitions; no general fixpoint theory is developed.
- Toy model: an abstract small-step relation with terminal states; no program syntax, heap, concurrency, probabilistic choice, I/O events or traces. These theorems neither establish nor refute the corresponding claims about the fuel-indexed or fixpoint weakest preconditions of any concrete language, interpreter or verification framework (such as an Iris-style program logic). Transfer to a concrete semantics requires a separate modeling argument that this package does not provide.

### Boundaries common to all cards

* **Toy model.** Everything is about an abstract relation `System σ`; no claim is made about any concrete language,
  interpreter or verification framework (see Applicability for the modeling bridge and its gaps).
* **Conventions.** Terminal states halt; stuck states are errors (no miracles); all transformers are demonic.
  Frameworks with blocking assumptions, miraculous commands, angelic choice, or continuing "terminal" states are
  **known not to apply** without new statements.
* **Fuel accounting.** One unit of fuel per step plus one final check. Other accounting schemes (per loop iteration,
  per call) are related only by a re-indexing argument that is **not examined** here.
* **Per-state fuel.** Every existential fuel bound is chosen per initial state, never uniformly over a precondition
  (`chainSys_fuel_per_state_not_uniform`).
* **Classical content.** The finite-branching completeness statements imply the limited principle of omniscience,
  and "total = partial + termination" implies Markov's principle (`ToyFuelWP.Constructivity`); a kernel restricted
  to constructive reasoning cannot prove them in this generality.
* **No interpreter-level statement.** Nothing is stated about an `Option`-returning `run : Nat → σ → Option σ`
  interpreter (**not examined**).
* **Coinductive alternatives not modeled.** Interaction trees, the delay monad, step-indexed logical relations,
  guarded fixpoints and Lean's `partial_fixpoint` / `coinductive_fixpoint` / `coinductive` predicates appear only as
  prior art (**not examined**).
* **Liveness.** Only `AllRunsEventually` (CTL-style AF over states) is considered; fairness, trace properties and
  output events are **not examined**.

The law of the excluded miracle invoked under Applicability, in the contrast with Nelson's calculus (cards 6, 9 and
11) and under Evidence is the following theorem; it depends on no axioms:

```lean
-- lean/ToyFuelWP/Boundaries.lean:39
-- ToyFuelWP.Boundaries
theorem wpLfp_excluded_miracle (S : System σ) (s : σ) : ¬ wpLfp S (fun _ => False) s
```

### Escape hatches

The impossibility result `positive-partial-wp-cannot-reject-divergent-state` is defeated by each of the following
changes of setting; each is proved in Lean, with its limits:

* **Negated partial weakest preconditions.** On `spinOrOutSys`, `AllRunsEventually spinOrOutSys isOut s` holds iff
  `wpGfp spinOrOutSys (fun _ => False) s` fails (`allRunsEventually_isOut_iff_not_wpGfp_false`). On every
  deterministic system without stuck states, the conjugate `¬ wpGfp S (fun t => ¬ Q t)` coincides with `wpLfp S Q`
  (`not_wpGfp_not_iff_wpLfp_of_deterministic_of_not_stuck`); both side conditions are needed
  (`spinOrExitSys_conjugate_ne_wpLfp`, `stuckSys_conjugate_ne_wpLfp`).
* **Total correctness on suitable systems.** `wpLfp spinOrOutSys isOut` coincides with the liveness property
  (`allRunsEventually_isOut_iff_wpLfp_isOut`) only because the output state is terminal; in `spinOrEmitLoopSys`,
  where the output state keeps running, no `wpGfp`, `wpLfp` or `wpFuelTotal` weakest precondition expresses it
  (`spinOrEmitLoopSys_allRunsEventually_not_wp_expressible`).
* **Domain restriction.** Restricting the equivalence to states other than the always-diverging violating state
  defeats the impossibility: off `spin`, `AllRunsEventually startSpinOutSys isOut3` coincides with
  `wpGfp startSpinOutSys isOut3` (`startSpinOutSys_wpGfp_iff_allRunsEventually_off_spin`).
* **Dropping either hypothesis.** Without an always-diverging state, or without a violation there, the property may
  be a partial weakest precondition (`done_allRunsEventually_false_expressible`,
  `loop_allRunsEventually_true_expressible`).
* **Instrumented systems** (a counter or prophecy turning bounded liveness into safety) are outside the statement,
  which fixes the system and state space; this escape hatch is **not examined** in Lean.

The partial-correctness equivalence `partial-fuel-equals-gfp` is defeated by replacing the demonic one-step operator
with an angelic one: for `wpStepAngelic`, the state `start` of `fanToStuckSys` satisfies the fuel version at every
fuel but not the greatest fixpoint (`fanToStuckSys_angelic_forall_fuel_not_gfp`). The total-correctness completeness
results are defeated by unbounded branching (`countdown_wpLfp_without_uniform_fuel`).

Statements of the results backing the non-claims, escape hatches and `logic` entries:

```lean
-- lean/ToyFuelWP/Boundaries.lean:326-328
-- ToyFuelWP.Boundaries
theorem fanToStuckSys_angelic_forall_fuel_not_gfp :
    (∀ n, wpFuelAngelic fanToStuckSys n (fun _ => True) .start) ∧
      ¬ wpGfpAngelic fanToStuckSys (fun _ => True) .start

-- lean/ToyFuelWP/Counterexamples.lean:24-27
-- ToyFuelWP.Counterexamples
theorem fixed_fuel_wpFuel_not_imp_wpGfp (n : Nat) :
    wpFuel downToStuckSys n (fun _ => True) n ∧
      ¬ (∀ m, wpFuel downToStuckSys m (fun _ => True) n) ∧
      ¬ wpGfp downToStuckSys (fun _ => True) n

-- lean/ToyFuelWP/Examples.lean:91
-- ToyFuelWP.Examples
theorem wpFuelTotal_neg_chain_short : ¬ wpFuelTotal chainSys 3 (fun s => s = 0) 3

-- lean/ToyFuelWP/Examples.lean:152
-- ToyFuelWP.Examples
theorem wpLfp_pos_chain : wpLfp chainSys (fun s => s = 0) 3

-- lean/ToyFuelWP/Examples.lean:56
-- ToyFuelWP.Examples
theorem wpFuel_pos_zero_stuck : wpFuel stuckSys 0 (fun _ => False) ()

-- lean/ToyFuelWP/Boundaries.lean:65-66
-- ToyFuelWP.Boundaries
theorem wpFuelTotal_propSys_one_iff_not_not (P : Prop) :
    wpFuelTotal (propSys P) 1 (fun _ => True) () ↔ ¬¬ P

-- lean/ToyFuelWP/Examples.lean:84
-- ToyFuelWP.Examples
theorem wpFuelTotal_neg_zero_done : ¬ wpFuelTotal doneSys 0 (fun _ => True) ()

-- lean/ToyFuelWP/Counterexamples.lean:162-166
-- ToyFuelWP.Counterexamples
theorem loop_finitelyBranching_no_total_fuel :
    FinitelyBranching loopSys ∧ FinitelyBranchingFrom loopSys () ∧
      wpGfp loopSys (fun _ => True) () ∧ HasInfiniteRun loopSys () ∧
      ¬ wpLfp loopSys (fun _ => True) () ∧
      ¬ ∃ n, wpFuelTotal loopSys n (fun _ => True) ()

-- lean/ToyFuelWP/Boundaries.lean:235-237
-- ToyFuelWP.Boundaries
theorem chainSys_fuel_per_state_not_uniform :
    (∀ k, ∃ n, wpFuelTotal chainSys n (fun s => s = 0) k) ∧
      ¬ ∃ n, ∀ k, wpFuelTotal chainSys n (fun s => s = 0) k

-- lean/ToyFuelWP/Examples.lean:301
-- ToyFuelWP.Examples
theorem deterministic_pos_termBranch : Deterministic termBranchSys

-- lean/ToyFuelWP/Examples.lean:279-280
-- ToyFuelWP.Examples
theorem finitelyBranchingFrom_pos_countdown_count :
    FinitelyBranchingFrom countdownSys (.count 3)

-- lean/ToyFuelWP/Examples.lean:294
-- ToyFuelWP.Examples
theorem finitelyBranching_neg_countdown : ¬ FinitelyBranching countdownSys

-- lean/ToyFuelWP/Examples.lean:315-316
-- ToyFuelWP.Examples
theorem spinOrExitSys_finitelyBranching_not_deterministic :
    FinitelyBranching spinOrExitSys ∧ ¬ Deterministic spinOrExitSys

-- lean/ToyFuelWP/Constructivity.lean:231-234
-- ToyFuelWP.Constructivity
theorem lpo_of_exists_wpFuelTotal_of_wpLfp_of_finitelyBranchingFrom
    (H : ∀ {σ : Type} (S : System σ) (Q : σ → Prop) (s : σ),
      FinitelyBranchingFrom S s → wpLfp S Q s → ∃ n, wpFuelTotal S n Q s) :
    LimitedPrincipleOfOmniscience

-- lean/ToyFuelWP/Constructivity.lean:242-245
-- ToyFuelWP.Constructivity
theorem lpo_of_exists_wpFuelTotal_iff_wpLfp_of_finitelyBranching
    (H : ∀ {σ : Type} (S : System σ) (Q : σ → Prop),
      FinitelyBranching S → ∀ s, (∃ n, wpFuelTotal S n Q s) ↔ wpLfp S Q s) :
    LimitedPrincipleOfOmniscience

-- lean/ToyFuelWP/Constructivity.lean:254-258
-- ToyFuelWP.Constructivity
theorem lpo_of_koenig_form
    (H : ∀ {σ : Type} (S : System σ) (Q : σ → Prop) (s : σ),
      FinitelyBranchingFrom S s → wpGfp S Q s → ¬ HasInfiniteRun S s →
        ∃ n, wpFuelTotal S n Q s) :
    LimitedPrincipleOfOmniscience

-- lean/ToyFuelWP/Constructivity.lean:357-360
-- ToyFuelWP.Constructivity
theorem exists_wpFuelTotal_of_wpLfp_of_deterministic_of_decidable_terminal {σ : Type u}
    (S : System σ) (Q : σ → Prop) (hdet : Deterministic S)
    (hdec : ∀ t, S.terminal t ∨ ¬ S.terminal t) (s : σ) (h : wpLfp S Q s) :
    ∃ n, wpFuelTotal S n Q s

-- lean/ToyFuelWP/Systems.lean:336
-- ToyFuelWP.Systems
theorem countdownSys_start_wpLfp : wpLfp countdownSys (fun _ => True) .start

-- lean/ToyFuelWP/Constructivity.lean:327-328
-- ToyFuelWP.Constructivity
theorem wpGfp_and_not_hasInfiniteRun_of_wpLfp {σ : Type u} (S : System σ) (Q : σ → Prop)
    (s : σ) (h : wpLfp S Q s) : wpGfp S Q s ∧ ¬ HasInfiniteRun S s

-- lean/ToyFuelWP/Constructivity.lean:300-303
-- ToyFuelWP.Constructivity
theorem markov_of_wpLfp_iff_wpGfp_and_not_hasInfiniteRun
    (H : ∀ {σ : Type} (S : System σ) (Q : σ → Prop) (s : σ),
      wpLfp S Q s ↔ wpGfp S Q s ∧ ¬ HasInfiniteRun S s) :
    MarkovPrinciple

-- lean/ToyFuelWP/Boundaries.lean:139-141
-- ToyFuelWP.Boundaries
theorem spinOrExitSys_conjugate_ne_wpLfp :
    ¬ Deterministic spinOrExitSys ∧ (∀ t, ¬ Stuck spinOrExitSys t) ∧
      ¬ wpGfp spinOrExitSys (fun t => ¬ isOut t) .spin ∧ ¬ wpLfp spinOrExitSys isOut .spin

-- lean/ToyFuelWP/Examples.lean:235
-- ToyFuelWP.Examples
theorem alwaysDiverges_neg_spinOrExit : ¬ AlwaysDiverges spinOrExitSys .spin

-- lean/ToyFuelWP/Boundaries.lean:80-81
-- ToyFuelWP.Boundaries
theorem allRunsEventually_isOut_iff_not_wpGfp_false (s : LO) :
    AllRunsEventually spinOrOutSys isOut s ↔ ¬ wpGfp spinOrOutSys (fun _ => False) s

-- lean/ToyFuelWP/Boundaries.lean:129-131
-- ToyFuelWP.Boundaries
theorem not_wpGfp_not_iff_wpLfp_of_deterministic_of_not_stuck (S : System σ) (Q : σ → Prop)
    (hdet : Deterministic S) (hns : ∀ t, ¬ Stuck S t) (s : σ) :
    ¬ wpGfp S (fun t => ¬ Q t) s ↔ wpLfp S Q s

-- lean/ToyFuelWP/Boundaries.lean:155-157
-- ToyFuelWP.Boundaries
theorem stuckSys_conjugate_ne_wpLfp :
    Deterministic stuckSys ∧ Stuck stuckSys () ∧
      ¬ wpGfp stuckSys (fun _ => ¬ True) () ∧ ¬ wpLfp stuckSys (fun _ => True) ()

-- lean/ToyFuelWP/Boundaries.lean:173-181
-- ToyFuelWP.Boundaries
theorem spinOrEmitLoopSys_allRunsEventually_not_wp_expressible :
    (AllRunsEventually spinOrEmitLoopSys isOut .out ∧
        ¬ AllRunsEventually spinOrEmitLoopSys isOut .spin) ∧
      (¬ ∃ Q : LO → Prop,
        ∀ s, wpGfp spinOrEmitLoopSys Q s ↔ AllRunsEventually spinOrEmitLoopSys isOut s) ∧
      (¬ ∃ Q : LO → Prop,
        ∀ s, wpLfp spinOrEmitLoopSys Q s ↔ AllRunsEventually spinOrEmitLoopSys isOut s) ∧
      (¬ ∃ (n : Nat) (Q : LO → Prop),
        ∀ s, wpFuelTotal spinOrEmitLoopSys n Q s ↔ AllRunsEventually spinOrEmitLoopSys isOut s)

-- lean/ToyFuelWP/Boundaries.lean:208-209
-- ToyFuelWP.Boundaries
theorem startSpinOutSys_wpGfp_iff_allRunsEventually_off_spin (s : LO3) (hs : s ≠ .spin) :
    wpGfp startSpinOutSys isOut3 s ↔ AllRunsEventually startSpinOutSys isOut3 s

-- lean/ToyFuelWP/Divergence.lean:225-226
-- ToyFuelWP.Divergence
theorem allRunsEventually_isOut_iff_wpLfp_isOut (s : LO) :
    wpLfp spinOrOutSys isOut s ↔ AllRunsEventually spinOrOutSys isOut s

-- lean/ToyFuelWP/Constructivity.lean:339-342
-- ToyFuelWP.Constructivity
theorem em_of_disjunctive_adequacy
    (H : ∀ (S : System Unit) (Q : Unit → Prop) (s : Unit), wpGfp S Q s →
      ∀ k t, Reach S s k t → (S.terminal t ∧ Q t) ∨ (¬ S.terminal t ∧ CanStep S t)) :
    ∀ P : Prop, P ∨ ¬ P

-- lean/ToyFuelWP/Defs.lean:313-314
-- ToyFuelWP.Defs
theorem runEndOk_iff_or (S : System σ) (Q : σ → Prop) (t : σ) :
    RunEndOk S Q t ↔ (S.terminal t ∧ Q t) ∨ (¬ S.terminal t ∧ CanStep S t)

-- lean/ToyFuelWP/Defs.lean:336-337
-- ToyFuelWP.Defs
theorem runEndOk_iff_not_stuck (S : System σ) (Q : σ → Prop) (t : σ) :
    RunEndOk S Q t ↔ (S.terminal t → Q t) ∧ ¬ Stuck S t

-- lean/ToyFuelWP/Counterexamples.lean:420-421
-- ToyFuelWP.Counterexamples
theorem loopSys_wpLfp_ne_wpGfp :
    wpGfp loopSys (fun _ => True) () ∧ ¬ wpLfp loopSys (fun _ => True) ()
```

### Unknown and not examined

* No hypothesis has tightness `unknown`: every hypothesis of every card is `tight`, with a proved counterexample in
  which all other hypotheses hold and the conclusion fails.
* **unknown:** whether the backward direction of `wpLfp_iff_wpGfp_and_not_hasInfiniteRun` needs more than Markov's
  principle over intuitionistic logic (for example a form of dependent choice). The package proves only that the
  statement implies Markov's principle (`markov_of_wpLfp_iff_wpGfp_and_not_hasInfiniteRun`).
* **not examined:** whether a single fixed fuel gives partial correctness on finite-state or bounded-depth systems
  (the counterexample `fixed_fuel_wpFuel_not_imp_wpGfp` uses an infinite state space).
* **not examined:** an exact characterization of the systems in which a total-correctness fuel bound exists; finite
  branching is sufficient, not necessary.

### Disproved or dropped statements

None. Every statement of the package is proved exactly as stated; no statement was found false, and none was
removed for lack of a proof.

## Evidence

Basis: execution (Lean kernel check). Toolchain `leanprover/lean4:v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52` (the commit of tag `v4.34.1` in `leanprover/lean4`, as reported by the GitHub API and by `lean --githash` of the installed toolchain). Evidence acquired 2026-11-20.

**Axiom audit.** All 439 declarations of the library `ToyFuelWP` were audited with Lean's `collectAxioms`; every one depends on at most `propext`, `Classical.choice` and `Quot.sound` (the per-declaration list is `audit/axioms.json`). No Lean source contains `sorry`, `admit`, `native_decide`, an `axiom` or `opaque` declaration, `implemented_by`, `extern` or `unsafe`.

**Statement hashes.** For each Lean name below, `statement` is the SHA-256 of the Lean `repr` of its type and `closure` the SHA-256 of its definition closure (for every library constant reachable from the type: its name, the `repr` of its type and, unless it is a theorem, the `repr` of its value; sorted, joined by newlines); `size` is the number of closure entries. Values are those in `audit/statements.json`.

| card | Lean name | axioms | statement SHA-256 | closure SHA-256 (size) |
| :--- | :--- | :--- | :--- | :--- |
| 1 (result) | `wpFuel_of_wpGfp` | none | `840eb015ccc62cea29c72dbaad3f098641cf5823300941b42b0716742f7d2de5` | `6121c99ef2fc0c868a8d026c21274ca8ca0854a11e383df9fc4792c56dbcc2f2` (11) |
| 1 (result) | `wpGfp_of_forall_wpFuel` | none | `1653e3e1bca9de45fcecd6fe91b451057a420adb194d15c3f08b964a42247003` | `6121c99ef2fc0c868a8d026c21274ca8ca0854a11e383df9fc4792c56dbcc2f2` (11) |
| 1 (result) | `forall_wpFuel_iff_wpGfp` | none | `8fab44a27000217938b5edd23d030bf7b0f280a6fe341667536668b6e1d206ea` | `6121c99ef2fc0c868a8d026c21274ca8ca0854a11e383df9fc4792c56dbcc2f2` (11) |
| 1 (support) | `stuckSys_not_wpGfp_not_wpFuel_one` | none | `dea9a596edef78530757285aa9a552f68e73197c2750b1ed0edf9812d12a2e42` | `d62ca2b6a35e2ac2ede23f6166af9a9a7e458fc6fd9367cc32d71c01c689edcb` (12) |
| 1 (support) | `fixed_fuel_wpFuel_not_imp_wpGfp` | Quot.sound, propext | `360000882ad8392e1cdf3bdb1bd2172642f5dec7431201aa29fb252048da2e2f` | `c9c3bff59c4f8dc1d5aaf67ce1ad03bd6b74644fce81156e1a6a5e447427f67f` (12) |
| 1 (support) | `nonvacuity_forall_wpFuel_and_wpGfp` | Quot.sound, propext | `1c222787ededdd5bacbe0e83a862bd5ccb431ae4a45ba2fea32fd384668c57d7` | `25d6f82fc4674042ad4fd994c368befb9df32f527c0421ee3d22f1394f3f356c` (13) |
| 2 (result) | `fixed_fuel_wpFuel_not_imp_wpGfp` | Quot.sound, propext | `360000882ad8392e1cdf3bdb1bd2172642f5dec7431201aa29fb252048da2e2f` | `c9c3bff59c4f8dc1d5aaf67ce1ad03bd6b74644fce81156e1a6a5e447427f67f` (12) |
| 3 (result) | `wpFuel_antitone` | none | `3909df84d00b597803276008fd16a424454f85731e07a3ee2f270d902bb61a9a` | `0552b473ba1af861341156260e515f4fba04913c90017c2df64b8bc05e0bbdde` (9) |
| 3 (result) | `wpFuelTotal_monotone` | none | `5b0959bdc59492cbde3f996db825122f2c57b7b7c7118532b159251c8bae87d2` | `0466b86bcd2bd953795bfd719f26fd01429137f4b8e2fae85cb3c4bf31448c4f` (9) |
| 3 (support) | `wpFuel_not_monotone_stuck` | none | `ff1d15b2627f08414c6c6f92a3f40cf4e7297f1d813843beef4f79a931ab6913` | `9aaa08e02a277b9008cc6496317641adf3f097df83cc39bbb8f05452f38eb4ce` (10) |
| 3 (support) | `wpFuel_antitone_drop_h` | none | `73f877c1bb14021e1ba3d279243579dfa1f76c693fcdece7daffca98f09d7cf4` | `9aaa08e02a277b9008cc6496317641adf3f097df83cc39bbb8f05452f38eb4ce` (10) |
| 3 (support) | `wpFuelTotal_not_antitone_done` | none | `8f63ef2a977ea994db4f75719d921dc0969a7f4d3b06b3d5d6f5b49736ceae3e` | `e39d7f0dbb184f20efa03e2681efbc1090ec790b758cf9a8f4347802034775e9` (10) |
| 3 (support) | `wpFuelTotal_monotone_drop_h` | none | `94cbd91bd312c0494c7f7cc3a606dfcb7d51f6a49cc6a2113eb76c262afd8f73` | `a47fe6b0405cc9d98e65c858c369ac428d3f830f4a1011e1274d9ca169dad69d` (10) |
| 3 (support) | `nonvacuity_wpFuel_antitone` | none | `2db8af3d85ae5944217c93465617273aa4d574aa9aad4da99c2ebba67121e3c0` | `a06750f90943438aff19ea958ec2e61006ef8253b108d47e3bf69159db2bfc91` (10) |
| 3 (support) | `nonvacuity_wpFuelTotal` | Quot.sound, propext | `751d97f841589d601b2ee778a02ca7f640f05e1d0cc4358d94d56a9352ee3157` | `cf0a88cb7d50909317706ad8e925198b6cfd142aa89f81a001d7180beeb55c15` (10) |
| 4 (result) | `wpFuel_iff_forall_reach_lt` | none | `11e2a261e41b71ce347e38edad89f65a6292445aab4808a0bf2701043906a6b2` | `e1feb2b1097b92363c768bf4b31f6639abafc40b44d9a5aafe73158b6ffb0329` (13) |
| 4 (support) | `nonvacuity_wpFuel_iff_forall_reach_lt` | Quot.sound, propext | `39818aaf72070ac8e4cf1dc6257cd013fe2933c8ee60bf5b81ee84d618904e65` | `633d9ad9e839ba3e806fcca214209d47ed8fc15f2c7cd5ed38fb02c2054aadd9` (10) |
| 5 (result) | `wpFuelTotal_iff_wpFuel_and_no_reach` | propext | `81fe7b03bf37b8dc8d242b37a8eab0767f25a5fb6c7eae552f62cbf8be5d5d4f` | `2d8c2e885f8f9fd413bee50ce4b8c21bea8cfbf487ca37cb35c8934fd6716c37` (14) |
| 5 (support) | `nonvacuity_wpFuelTotal` | Quot.sound, propext | `751d97f841589d601b2ee778a02ca7f640f05e1d0cc4358d94d56a9352ee3157` | `cf0a88cb7d50909317706ad8e925198b6cfd142aa89f81a001d7180beeb55c15` (10) |
| 6 (result) | `wpLfp_of_exists_wpFuelTotal` | none | `4322b45146c1a852caa45fc52d908f8da170486d4d6d321196ca23d279f0c490` | `ceeb9018a37d4eeafac203484ef96c3e0c21878eca1d21e75ed12dee5baa39d7` (11) |
| 6 (result) | `wpGfp_of_wpFuelTotal` | none | `f5e50bc1ab371bc9bf054f4e724b341d290f8bd11917c103c67f57917890ab02` | `e5423f00071108788dee1535ada128076282ecf7e095d3347dcdeda17ebd9ade` (11) |
| 6 (support) | `stuckSys_no_total_no_partial` | none | `b16876e79cf9c16c08703b019a4bcc485f0edb2d0ccf8ca8b733321b40c7be2d` | `2a73a22e979866f5b15b033b76343b1b0e0310648155b8990ac7118859309234` (14) |
| 6 (support) | `nonvacuity_wpFuelTotal` | Quot.sound, propext | `751d97f841589d601b2ee778a02ca7f640f05e1d0cc4358d94d56a9352ee3157` | `cf0a88cb7d50909317706ad8e925198b6cfd142aa89f81a001d7180beeb55c15` (10) |
| 7 (result) | `exists_wpFuelTotal_of_wpLfp_of_finitelyBranchingFrom` | Classical.choice, Quot.sound, propext | `c28c1bd973045353a6eb40eb7a2550244279e0b5d10e1a579c326201345e98bc` | `2b57e838e2b9f92ddfa382b6370e52db77e65472e4a8b72a6d39e18ba28393be` (16) |
| 7 (result) | `exists_wpFuelTotal_iff_wpLfp_of_finitelyBranching` | Classical.choice, Quot.sound, propext | `f21b633e7ac33aaa1de8e539ac804909d63342969a7fe0d8640f531c5ef2342f` | `d7e0645085d2090c0d585be1c418bec2cac7cc168434a23a2fdd7822ca16d68f` (13) |
| 7 (result) | `exists_wpFuelTotal_iff_wpLfp_of_deterministic` | Classical.choice, Quot.sound, propext | `57ac32ff357b11e59416ce8f6f6363555ddd526a8388c9670cc4db64f8c71e68` | `a565631398e13e079fc9528ad147a1cb7d572face9cca6d400e19d722c4aeddd` (12) |
| 7 (result) | `exists_wpFuelTotal_iff_wpLfp_ofStepFn` | Classical.choice, Quot.sound, propext | `e47051e904b7ae44ac5bbd77cd9ae9718e14cb86e6eaf94311149f62a8419411` | `40401f1e8ac405ae9a011d7d9cd58a44485b41d3371cf268be4519882caff577` (12) |
| 7 (result) | `exists_wpFuelTotal_of_wpGfp_of_not_hasInfiniteRun_of_finitelyBranchingFrom` | Classical.choice, Quot.sound, propext | `5bf0705d1b42fd321c96b848a4f5908deadd45fb7897479b379a16f383cbe54b` | `417758a1903cc71f947ea42ed468578f2a360bd0450249d41f13383e1ef46670` (17) |
| 7 (support) | `countdown_wpLfp_without_uniform_fuel` | Quot.sound, propext | `9acf3acb74d425be59f1aee5d22d7348fa13f84260accb3c78260bdfbfe47a67` | `2a758c74cb14108e0f8c0ea09022666dda01ab3420a15b74da6e3ad138d0b885` (28) |
| 7 (support) | `loop_finitelyBranching_no_total_fuel` | propext | `72af073346283f4e60e7a71131006fa65631d3efc6a4ed51a72516c64ad7c7b2` | `5192c8d253152332eb19963cf1e0ab2a6ebeaae2fdbffbeaecdfac3957309dbc` (21) |
| 7 (support) | `countdown_exists_wpFuelTotal_iff_wpLfp_fails` | Quot.sound, propext | `46b6f97b3910112558166c2605f729edff315291f3e99318c6f02c08b52b0129` | `e4cf17b78245fe0cb4d1784b874ca5dc5cf783f643c2f67081fb65df4bb74105` (21) |
| 7 (support) | `stuck_finitelyBranching_no_infinite_run_no_total_fuel` | none | `6fa4b8a379ca172d8cd25711b2a2137fabfca5f9e91d53154df80236ff8bff5e` | `f6092267d3f5b5ce4c4a85a074bd463e05752b645782642229fa6478e55381e4` (18) |
| 7 (support) | `nonvacuity_exists_wpFuelTotal_of_wpLfp_of_finitelyBranchingFrom` | Classical.choice, Quot.sound, propext | `b6144d5ab970627db5ae25c89450abe5a6ece27743a2203a96574d65cbec27da` | `ad3a4438daa54287281be93879746df1fbccd9e13a953b956fc0d3cf8a29f60d` (21) |
| 7 (support) | `nonvacuity_exists_wpFuelTotal_iff_wpLfp_corollaries` | Classical.choice, Quot.sound, propext | `3b348fc806940e89481e0ee8d78673fa5b8422ec27c1f44fed554bef0807f34b` | `4d21770218d2724b4b34ee3a4bb1915409481155b2c678cbe4479614cfa14f21` (12) |
| 7 (support) | `nonvacuity_exists_wpFuelTotal_iff_wpLfp_ofStepFn` | propext | `e07dea7a5974f011cbbfaabf34c817b04073c6549fb85987b55ab70ee0c58718` | `2504b78f5a97505579774733baf50326454e2cd6736f76d29d0ad201a086e753` (12) |
| 7 (support) | `nonvacuity_koenig_form` | Classical.choice, Quot.sound, propext | `5d3c53bf537296306dee0886e41b71068c57e94583778c99243d52b9452a6a76` | `420d780f4bb1b33ce04db2941de8b09cd7d531c0ea67eea6af967e1e7902d7f6` (15) |
| 8 (result) | `countdown_wpLfp_without_uniform_fuel` | Quot.sound, propext | `9acf3acb74d425be59f1aee5d22d7348fa13f84260accb3c78260bdfbfe47a67` | `2a758c74cb14108e0f8c0ea09022666dda01ab3420a15b74da6e3ad138d0b885` (28) |
| 9 (result) | `wpLfp_iff_wpGfp_and_not_hasInfiniteRun` | Classical.choice, Quot.sound, propext | `39d736a44c9bf068d95b68f4a29c46231cd1a0c9726c0b137c3f0ba9bf8c61ee` | `4152876e4d58a63bc4439825ffe057deea7a1b3b9487e427b2dae91735cfa2e6` (11) |
| 9 (support) | `nonvacuity_wpLfp_iff_wpGfp_and_not_hasInfiniteRun` | Quot.sound, propext | `15d1138d48ac66570e181599f4da67dd7b7ca919d1bada0eca5c75b414f9a7cc` | `456144669c8db7e60fa20228bf098ffeace1e537673dbf68af6bc889db720d5c` (19) |
| 10 (result) | `alwaysDiverges_satisfies_every_partial_wp_and_no_total_wp` | none | `547fb184e193285b2ef1e7cd219c8a78420e89613b245d4d657a0e2882dfc028` | `7b5fc07ef57853aca76bb1c8d23891f53cca99ad0b30a494e67898296cf64491` (19) |
| 10 (result) | `hasInfiniteRun_refutes_every_total_wp` | none | `468da089596e0c89ca0e33b956ec8a8b7a65bce3cda9aa98bdcd0b65a171373f` | `a25a30d399180c25aa676fc1b835d3f59865bc9ce685d3cd908a01ba21ffe84a` (12) |
| 10 (support) | `done_not_every_partial_wp` | none | `fd67f3cc051755d30c75192819aa4fc92f53bb01857ad9433d10a7dbd68e56c5` | `108d7c11a6faa1cf8acc905f89b80a879b3e3e14f5352b117962d006501c7972` (16) |
| 10 (support) | `done_some_total_wp` | none | `85dc643caf6fa512917e0bbf626b48bfca427b5c4b45d1c3bd4db2b83fb1f3ec` | `041288c965b1783e79ac4b882dbae30b3739c52fff9734e1d78f756fd72b4342` (13) |
| 10 (support) | `nonvacuity_alwaysDiverges` | none | `bf1e7b278cf25c107d62048ff68f2fbf12daeba6ea61e1513a3df3154b438afa` | `ab1f06d3f5eb24d675d8b6908edb5389fececa3a2aa99c3b0ab1579cc4172715` (14) |
| 10 (support) | `nonvacuity_hasInfiniteRun` | none | `fa48529c5b37c610dabcd46242b6bf4abf0c163f41458e149796333353f51dfb` | `8edac8ecd7f574eaf5545eba2c87f656fc16911db49ed49c18209c851b6b3b65` (14) |
| 11 (result) | `wpGfp_false_iff_alwaysDiverges` | none | `4f9287a68f4f79c25c0bbf3410cf122ec518fe3ea3557ee9b366b0c1a3fd0f1c` | `cebc798646ad583d7fd6799c9e7702e4a14464fd2e7b908f574f7b9318ba8b32` (12) |
| 11 (result) | `forall_wpGfp_iff_alwaysDiverges` | none | `07d52152c8cad8312dc5437f4f9d8c853a8f6c24a6a3a6f9197e9b828c7fd8a7` | `cebc798646ad583d7fd6799c9e7702e4a14464fd2e7b908f574f7b9318ba8b32` (12) |
| 11 (support) | `nonvacuity_alwaysDiverges` | none | `bf1e7b278cf25c107d62048ff68f2fbf12daeba6ea61e1513a3df3154b438afa` | `ab1f06d3f5eb24d675d8b6908edb5389fececa3a2aa99c3b0ab1579cc4172715` (14) |
| 12 (result) | `not_partial_wp_expressible_of_alwaysDiverges_of_not` | none | `f4354b9bb340b39fb0eb3988da24e33a95c9a0f0a9f5e1ba19107d75f0af104f` | `a96321c8d613acb3fefa62ae83349c3ebfbf35483f9b91e227a33c8c4fc7565f` (15) |
| 12 (result) | `allRunsEventually_not_partial_wp_of_divergent_violation` | none | `c1e068654b42c4d86220587f37d25fa1a90daec850c891167619b673db29bc26` | `bf64ca740e973543c8562a68a8dd232767b875b69499f8f17fc1987474e9d218` (18) |
| 12 (result) | `allRunsEventually_isOut_not_partial_wp_expressible` | none | `91fad745fcc8f00ff3b40ff46b4cbbe0fdac12431e69f6093e993c7d1e2239c6` | `b207bb8197e346d98a17da7e393981bed037829e245d1655918975a8647fdc06` (19) |
| 12 (result) | `startSpinOutSys_allRunsEventually_not_partial_wp_expressible` | none | `3fa8e2f4832c9ac1b102a99dbab08bbf64c380093d9730e1e1f6273f8b77da29` | `566496ce6564d1b5da7cb54afc3a9d14cba521fb2b8c24b88bddd85b60e44a08` (20) |
| 12 (support) | `done_allRunsEventually_false_expressible` | none | `68a4367e09f1e865c3c00d268ad4bd3530024293758f1c4e833e65bb942fb591` | `441c6288ca31bbeb37d8fe4d20a9d9aae0146bda18d2e5624ace3cc20801fc5c` (19) |
| 12 (support) | `loop_allRunsEventually_true_expressible` | none | `60f391b0f5a9a7af06650cbb05945c49a33c664bf274ca60c02c80b19f4eb091` | `a59b392e70d64fdeaadb7167ca565e6ed9db5bce4e15b4df89e1c6c72d7727c7` (19) |
| 12 (support) | `nonvacuity_divergent_violation` | none | `b0a39e054d3c67492ba0edd27f91b41f6f66b3eff5e44f76e128b9ca6a1b0500` | `fd13716c6f97b6058e99ef1e5d3d4f33137cb982cd334523785d4d630aa9978b` (23) |
| 12 (support) | `nonvacuity_allRunsEventually_isOut_nontrivial` | none | `4efdf3194f1b7d541238ecc41ca6077fa233f73055772dc908f2cf596f911007` | `01a68049947127a602815de603536d4d59a9b8bfceae956000ca0ab9ff773cda` (19) |
| 12 (support) | `spinOrOutSys_spin_every_partial_wp_but_never_outputs` | none | `a5b8025637ea3bc77aa28f9f17d7ad514f70367aae5fd6a46dd2c8cd7e22f8e6` | `b207bb8197e346d98a17da7e393981bed037829e245d1655918975a8647fdc06` (19) |
| 12 (support) | `allRunsEventually_isOut_iff_not_wpGfp_false` | none | `5e6f10b451b073cdcf2b80b16fa5931dd69bc9d4ed0da747785460fb56a4b4dc` | `4a55492172490e3a3f3c391b89d1cfa3a4696dce638e73dcb883c4ea5bccd44d` (16) |
| 12 (support) | `startSpinOutSys_wpGfp_iff_allRunsEventually_off_spin` | none | `07f0db025d166c8916b3757c3eb862a220bb8e2b842ab8689cdc5b739a47ecec` | `3524727eae7407abc4ee9345f952480378fe4b3adc555d976696fc9d38c52c7d` (17) |
| 12 (support) | `allRunsEventually_isOut_iff_wpLfp_isOut` | none | `e743f2c29d75444b5c905a2549fcbb9dc598d58d742d1deaa4a30f22d5ffe668` | `a4e893ef3dcbac60d5254fedc61eea63f6603783f532c7f3ccb025f7966c7349` (16) |
| 13 (result) | `wpGfp_adequacy` | none | `60af3305585541b09404c9e978d581dc7475c8b56d31570e7454505d2ea9652a` | `8ca413db7ada1816a1ad32948eeef94392a631386b7a0d66da901fa1c34719ed` (12) |
| 13 (result) | `wpGfp_of_forall_reach_runEndOk` | none | `b07da9e28d5d60aabdd3b99b5b6367ee94c5fed1452f51129d627062e7a2f5fe` | `8ca413db7ada1816a1ad32948eeef94392a631386b7a0d66da901fa1c34719ed` (12) |
| 13 (result) | `wpGfp_iff_forall_reach_runEndOk` | none | `25e7c2e7421b9a762ca7514d46b44f2dc25e7b4056dd05a9efa034fa4a1148e9` | `8ca413db7ada1816a1ad32948eeef94392a631386b7a0d66da901fa1c34719ed` (12) |
| 13 (support) | `wpGfp_adequacy_drop_h` | none | `3c173fbc3f6c5550e76422765a90303c9e72f2c17bbc0dfc5d27f7d22ec9f976` | `eab3d7640b7acfbd66b48688031d9e00d10550b3bc55eb9cbc922fdc67020b03` (13) |
| 13 (support) | `wpGfp_of_forall_reach_runEndOk_drop_h` | none | `f12cd4e616385fd0f4f0cb5e3453ecdc01d649229fd52c03d94a64a91f563217` | `eab3d7640b7acfbd66b48688031d9e00d10550b3bc55eb9cbc922fdc67020b03` (13) |
| 13 (support) | `nonvacuity_adequacy` | Quot.sound, propext | `79dc6c097d65ccafbe4e491e061d6ad1836f331a7db31309cf3908bfeed11afd` | `ddadbde9371f4384b43f53556184ee66ab10021075f2f91a56224f1d8581fa98` (14) |
| 14 (result) | `wpGfp_unfold` | none | `e485a41f9edb00b88beace1ccccb71755eed21d00dfe72b50a66de8f98872695` | `628552982b476a4126064ad33f4f27cd598aec847bd759614296085fcced63aa` (8) |
| 14 (result) | `wpGfp_coinduction` | none | `a1d9b320df4e279f3b3597131c76dd7ace9395ebb2528a4552f50968410d000e` | `628552982b476a4126064ad33f4f27cd598aec847bd759614296085fcced63aa` (8) |
| 14 (result) | `wpLfp_unfold` | none | `1a0272d7fbff8efb2e604096f6e72b9c0995a756b11d0ac76bd91273900159fc` | `e0371add931efee1862f2c8b39e3d2c079de313dd41f583b403987ae8c112a12` (8) |
| 14 (result) | `wpLfp_induction` | none | `49ea3ac13b4252b30df3ed24f3ee0ff5dd3c2a4f6054d78d4d3a64221509b7b0` | `e0371add931efee1862f2c8b39e3d2c079de313dd41f583b403987ae8c112a12` (8) |
| 14 (support) | `wpGfp_coinduction_drop_hX` | none | `b11525767a3c69eb7b8359410c509ff1cf9ce438f976448b2ce013db824404d1` | `d4d131901a5739dc4039825a20d393876b89abaeab132311693690bc7e09a7df` (9) |
| 14 (support) | `wpGfp_coinduction_drop_hs` | none | `849210d4732455a397ace87944779327d27ca7f1dc3fa5598a689d2e2fbc4bc4` | `d4d131901a5739dc4039825a20d393876b89abaeab132311693690bc7e09a7df` (9) |
| 14 (support) | `wpLfp_induction_drop_hX` | none | `a800606ad7664fbdfb330609bab415cab6c39ef6ed9a1932c8751215afc24eeb` | `ef5fc4fced600c8f6f1ff9ee9c4822eabdcaefa1baa9f4b416161412fb0e6fa4` (9) |
| 14 (support) | `wpLfp_induction_drop_hs` | none | `1730753d22ff12c22f52ff938e8eb9ad5ee2d007e577e20ce5b4adaa3e11082f` | `46acbacaefd7926edffb1a51acef5d2da55db0e4526c000d2642df6e06454ce9` (9) |
| 14 (support) | `nonvacuity_coinduction_induction` | none | `63bf6d2a7c2aac0c8acf5e669763c7a2ec1722a2d48e1fc19f9535befcceef99` | `e6e543a016254036c8ed3dde9de6bd23e37c02d34a352abc0f1b576c3a626e1f` (15) |
| 14 (support) | `wpGfp_pos_loop_false` | none | `635b83ba32ebfe93510da805d59f00b7aff7d9a296c256df2ee7e49a22d7c83a` | `e1ca16241ec700721745b59d4da88229da512cd3139be3cad2aee9e82743ed87` (9) |
| 14 (support) | `wpLfp_pos_chain` | Quot.sound, propext | `37cfe27f9093350da84d3808acfc175ecd9b09a4c5182dd6dce7f71c4accafac` | `9617c779f5c7b0af2947c471b7b7d81df3c7633be959a102b2df118b916c3ff9` (9) |

Further declarations referenced by the cards (`logic_evidence_lean`, `boundary_evidence_lean`), checked for existence and axioms but without a recorded hash:

| Lean name | axioms |
| :--- | :--- |
| `fanToStuckSys_angelic_forall_fuel_not_gfp` | Quot.sound, propext |
| `wpFuelTotal_neg_chain_short` | Quot.sound, propext |
| `wpFuel_pos_zero_stuck` | none |
| `wpFuelTotal_propSys_one_iff_not_not` | none |
| `wpFuelTotal_neg_zero_done` | none |
| `chainSys_fuel_per_state_not_uniform` | Quot.sound, propext |
| `deterministic_pos_termBranch` | none |
| `finitelyBranchingFrom_pos_countdown_count` | propext |
| `finitelyBranching_neg_countdown` | Quot.sound, propext |
| `spinOrExitSys_finitelyBranching_not_deterministic` | none |
| `lpo_of_exists_wpFuelTotal_of_wpLfp_of_finitelyBranchingFrom` | propext |
| `lpo_of_exists_wpFuelTotal_iff_wpLfp_of_finitelyBranching` | propext |
| `lpo_of_koenig_form` | propext |
| `exists_wpFuelTotal_of_wpLfp_of_deterministic_of_decidable_terminal` | none |
| `countdownSys_start_wpLfp` | propext |
| `wpGfp_and_not_hasInfiniteRun_of_wpLfp` | none |
| `markov_of_wpLfp_iff_wpGfp_and_not_hasInfiniteRun` | none |
| `countdownSys_not_finitelyBranchingAt_start` | Quot.sound, propext |
| `spinOrExitSys_conjugate_ne_wpLfp` | none |
| `alwaysDiverges_neg_spinOrExit` | none |
| `not_wpGfp_not_iff_wpLfp_of_deterministic_of_not_stuck` | Classical.choice, Quot.sound, propext |
| `stuckSys_conjugate_ne_wpLfp` | none |
| `spinOrEmitLoopSys_allRunsEventually_not_wp_expressible` | none |
| `em_of_disjunctive_adequacy` | none |
| `runEndOk_iff_or` | Classical.choice, Quot.sound, propext |
| `runEndOk_iff_not_stuck` | Classical.choice, Quot.sound, propext |
| `loopSys_wpLfp_ne_wpGfp` | none |

Further declarations quoted in Findings and Boundaries as context only (not referenced by `results.json`, so no hash is recorded); their axioms are those listed in `audit/axioms.json` and printed on the `AXIOMS` lines of `lean/RevalidationAudit.lean`:

| Lean name | axioms |
| :--- | :--- |
| `predStep` | none |
| `finitelyBranching_of_deterministic` | Classical.choice, Quot.sound, propext |
| `finitelyBranchingFrom_of_finitelyBranching` | none |
| `wpGfp_neg_error_far` | Quot.sound, propext |
| `wpLfp_pos_countdown` | propext |
| `wpLfp_neg_loop` | none |
| `deterministic_neg_spinOrExit` | none |
| `alwaysDiverges_pos_spinOrOut` | none |
| `alwaysDiverges_neg_error` | Quot.sound, propext |
| `downToStuckSys_not_wpFuel` | Quot.sound, propext |
| `wpLfp_excluded_miracle` | none |

**Primary sources for prior art** (bibliographic records as cited on the cards; where a card says a claim was seen only through a secondary source, that qualification stands):

- S. Owens, M. O. Myreen, R. Kumar, Y. K. Tan. Functional big-step semantics. ESOP 2016, LNCS 9632, pp. 589–615. doi:10.1007/978-3-662-49498-1_23. Clocked (fuel-indexed) interpreters: evaluation diverges iff it times out for every initial clock value; the HOL4 development (HOL repository, examples/pl-semantics/for/forScript.sml, theorem simple_sem_t_div_iff_sem_t_div) proves this equals a coinductive divergence relation for a deterministic language — the closest mechanized analogue of the 'every fuel = coinductive' direction found.
- Isabelle/HOL, HOL/Library/Order_Continuity.thy: lemma inf_continuous_gfp (gfp F = (INF i. (F ^^ i) top) for inf-continuous F) and lemma sup_continuous_lfp (lfp F = (SUP i. (F ^^ i) bot) for sup-continuous F) — mechanized Kleene-style iteration theorems; partial-fuel-equals-gfp is the instance for wpStep, which is inf-continuous with no branching assumption, while the least-fixpoint dual needs continuity that fails under unbounded branching.
- Mathlib, Mathlib/Order/FixedPoints.lean (github.com/leanprover-community/mathlib4, master): OrderHom.lfp / OrderHom.gfp on a complete lattice, defined as the infimum of pre-fixed points / supremum of post-fixed points, with lfp_le, le_gfp, map_lfp, map_gfp and fixedPoints.completeLattice (Knaster–Tarski) — the same impredicative construction as wpLfp / wpGfp, in general form.
- E. W. Dijkstra and C. S. Scholten. Predicate Calculus and Program Semantics. Springer, 1990. doi:10.1007/978-1-4612-3228-5. Chapter 8 'Equations in predicates and their extreme solutions' (pp. 147–170) and chapter 9 'Semantics of repetitions' (pp. 170–189). The characterization of wlp of a repetition as the weakest (greatest) solution and wp as the strongest (least) solution of the loop equation was verified only through a secondary source (I. M. Rewitzky, Modelling the Algebra of Weakest Preconditions, MSc thesis, Department of Mathematics, University of Cape Town, 1991), not in the book itself.
- P. Cousot and R. Cousot. Constructive versions of Tarski's fixed point theorems. Pacific Journal of Mathematics 82(1):43–57, 1979. doi:10.2140/pjm.1979.82.43. Fixpoints of monotone maps via transfinite iteration without continuity, contrasted with the ω-iteration that needs continuity.
- J.-L. Lassez, V. L. Nguyen, E. A. Sonenberg. Fixed point theorems and semantics: a folk tale. Information Processing Letters 14(3):112–116, 1982. doi:10.1016/0020-0190(82)90065-5. On the attribution of the fixed-point theorems used in semantics (bibliographic record verified; content not re-read here).
- R. Jung, R. Krebbers, J.-H. Jourdan, A. Bizjak, L. Birkedal, D. Dreyer. Iris from the ground up: a modular foundation for higher-order concurrent separation logic. Journal of Functional Programming 28, e20, 2018. doi:10.1017/S0956796818000151. Section 6 defines a weakest precondition with the same case structure as wpStep (a value satisfies the postcondition; otherwise the expression is reducible and every successor satisfies the weakest precondition). It is not the same operator: in the Iris Coq library (iris/program_logic/weakestpre.v, definition wp_pre) value-hood is tested by the computable to_val, the recursive occurrence sits under fancy-update modalities (which quantify existentially over ghost-state updates) and later modalities, and wp is the guarded fixpoint of a contractive function.
- X. Leroy and H. Grall. Coinductive big-step operational semantics. Information and Computation 207(2):284–304, 2009. doi:10.1016/j.ic.2007.12.004. Coinductive big-step semantics describing diverging as well as terminating evaluations; the accompanying Coq development proves equivalences between big-step and small-step semantics.
- K. Nakata and T. Uustalu. Trace-based coinductive operational semantics for While. TPHOLs 2009, LNCS 5674, pp. 375–390. doi:10.1007/978-3-642-03359-9_26. Four coinductive trace-based semantics (big-/small-step, relational/functional) for terminating and nonterminating runs, proved equivalent in Coq.
- L. Xia, Y. Zakowski, P. He, C.-K. Hur, G. Malecha, B. C. Pierce, S. Zdancewic. Interaction trees: representing recursive and impure programs in Coq. Proc. ACM Program. Lang. 4(POPL), article 51, 2020. doi:10.1145/3371119. A coinductive variant of free monads representing possibly nonterminating computations, with equivalence up to weak bisimulation; the coinductive alternative to fuel.
- V. Capretta. General recursion via coinductive types. Logical Methods in Computer Science 1(2:1), 2005. doi:10.2168/LMCS-1(2:1)2005. The coinductive delay type of partial elements (return / add a step) — a coinductive alternative to fuel for representing possibly nonterminating computations.
- N. A. Danielsson. Operational semantics using the partiality monad. ICFP 2012, pp. 127–138. doi:10.1145/2364527.2364546. Coinductive partiality monad for total definitional interpreters, in Agda — the coinductive counterpart of a fuel-indexed interpreter.
- Lean 4 reference manual, recursive definitions: partial_fixpoint (introduced in Lean v4.17.0, leanprover/lean4 pull request 6355) defines functions as least fixpoints of monotone equations in chain-complete partial orders (for example Option-valued functions) and generates a partial-correctness theorem; lattice-theoretic least/greatest-fixpoint predicates (introduced in v4.20.0, pull request 8097; named inductive_fixpoint / coinductive_fixpoint from v4.23.0) use Knaster–Tarski on Prop with (co)induction principles. Source: github.com/leanprover/reference-manual, files Manual/RecursiveDefs/PartialFixpoint.lean and Manual/RecursiveDefs/CoinductivePredicates.lean. This package uses neither; its wpGfp and wpLfp are hand-written impredicative fixpoints.
- Lean v4.25.0 release notes (github.com/leanprover/reference-manual, Manual/Releases/v4_25_0.lean): pull request leanprover/lean4#10333 introduces a coinductive keyword that defines coinductive predicates with the same syntax as inductive. The pinned toolchain v4.34.1 therefore offers coinductive predicates; this package does not use them, so that its definitions also make sense for a kernel without them.
- A. W. Appel and D. McAllester. An indexed model of recursive types for foundational proof-carrying code. ACM TOPLAS 23(5):657–683, 2001. doi:10.1145/504709.504712. Origin of step-indexed models, in which a natural-number index bounds the number of steps for which a property is observed — the same 'bounded observation' reading as partial-correctness fuel, applied to types rather than weakest preconditions (analogy only).
- A. J. Ahmed. Semantics of Types for Mutable State. PhD thesis, Princeton University, 2004. Indexed possible-worlds model building on Appel and McAllester's indexed model (analogy only).
- N. Amin and T. Rompf. Type soundness proofs with definitional interpreters. POPL 2017, pp. 666–679. doi:10.1145/3009837.3009866. Type soundness stated over definitional interpreters (bibliographic record verified; listed as a reference point for interpreter-based semantics, content not re-read here).
- Iris Coq library, iris/program_logic/adequacy.v (as rendered in the Iris coqdoc): the record adequate s e1 σ1 φ says that every value reached by a finite execution satisfies φ and, for s = NotStuck, that no reachable thread is stuck; wp_adequacy_gen derives adequate from a weakest-precondition proof — the analogue, for a guarded step-indexed weakest precondition, of the finite-run-prefix adequacy here.
- E. W. Dijkstra. Guarded commands, nondeterminacy and formal derivation of programs. Communications of the ACM 18(8):453–457, 1975. doi:10.1145/360933.360975. Defines only the total-correctness wp(S, R) — the weakest precondition guaranteeing proper termination in a state satisfying R; no liberal (partial-correctness) counterpart is defined there — and defines the loop by H0(R) = R ∧ ¬BB, Hk(R) = wp(IF, Hk-1(R)) ∨ H0(R), wp(DO, R) = (∃k ≥ 0: Hk(R)), with Hk(R) read as termination after at most k selections — an existentially fuel-indexed total weakest precondition. (Content read in the author's EWD418 transcription, whose abstract matches the published one.) Index shift: H0 already covers a loop that terminates after zero selections, whereas wpFuelTotal 0 Q is False and a terminal state needs fuel 1; under the analogy one selection = one step, Hk corresponds to fuel k + 1.
- G. Nelson. A generalization of Dijkstra's calculus. ACM TOPLAS 11(4):517–561, 1989. doi:10.1145/69558.69559. Generalizes the wp calculus by dropping the law of the excluded miracle, treats recursion by fixpoints, and relates the full wp/wlp semantics to a powerdomain semantics. Contrast: here wpLfp obeys the law of the excluded miracle (wpLfp_excluded_miracle) and every weakest precondition rejects stuck states, so a state without outcomes is an error, not a miracle.
- Iris Coq library, iris/program_logic/total_weakestpre.v and total_adequacy.v (as rendered in the Iris coqdoc): the total weakest precondition twp is defined as a least fixpoint (bi_least_fixpoint of twp_pre'), and twp_total derives strong normalization sn erased_step from a total-weakest-precondition proof — a mechanized least-fixpoint total weakest precondition in a separation logic.
- E. W. Dijkstra. A Discipline of Programming. Prentice-Hall, 1976 (ISBN 0-13-215871-X, seen only in a copyright-page snippet). Contains the chapter 'On nondeterminacy being bounded' (p. 72 per the table of contents). That the book introduces the weakest liberal precondition and states a continuity property for bounded nondeterminism was seen only through secondary sources and text snippets, not at the primary source.
- K. R. Apt and G. D. Plotkin. Countable nondeterminism and random assignment. Journal of the ACM 33(4):724–767, 1986. doi:10.1145/6490.6494. Abstract: admitting countable (unbounded) nondeterminism results in a lack of continuity of various semantic functions, shown necessary for any semantics satisfying appropriate conditions; total-correctness proofs need countable ordinals.
- D. Kőnig. Über eine Schlussweise aus dem Endlichen ins Unendliche. Acta Sci. Math. (Szeged) 3(2–3):121–130, 1927 (volume and issue seen only via a secondary record). The infinity lemma (Lemma A): a sequence of finite non-empty sets linked by a relation admits an infinite chain.
- R.-J. Back and J. von Wright. Refinement Calculus. Springer, 1998. doi:10.1007/978-1-4612-1674-2. Contains a chapter 'Continuity and Executable Statements' (pp. 365–382) and a chapter on fixed points; only titles and pages were verified, not the chapter text.
- W. H. Hesselink. Programs, Recursion and Unbounded Choice. Cambridge University Press, 1992. doi:10.1017/CBO9780511569784. Publisher's abstract: a complete account of the predicate transformation calculus semantics of sequential programs, including repetitions, recursive procedures, computational induction and unbounded nondeterminacy.
- Mathlib, Mathlib/Order/KonigLemma.lean (github.com/leanprover-community/mathlib4, master): exists_seq_covby_of_forall_covby_finite and exists_seq_forall_proj_of_forall_finite (Kőnig's infinity lemma) — a mechanized form of the lemma behind the König form of finite-branching completeness.
- A. Lochbihler. Coinductive. Archive of Formal Proofs, February 2010 (isa-afp.org/entries/Coinductive.html). Abstract: general-purpose coinductive data types (lazy lists, streams, ...) with 'a version of König's lemma as an application for coinductive lists'.
- D. Larchey-Wendling. Constructive Substitutes for Kőnig's Lemma. TYPES 2024, LIPIcs 336, 2:1–2:23, 2025. doi:10.4230/LIPIcs.TYPES.2024.2 (DataCite record verified), with the Coq artifact github.com/DmxLarchey/Constructive-Konig. Constructive replacements for Kőnig's lemma — relevant to the classical content of the finite-branching completeness statements, which imply the limited principle of omniscience here.
- B. C. Pierce et al. Software Foundations, Volume 1: Logical Foundations, chapter ImpCEvalFun (softwarefoundations.cis.upenn.edu): theorem ceval_and_ceval_step_coincide — for the deterministic language Imp, the inductive big-step evaluation relation holds iff a fuel-indexed evaluation function returns the final state for some fuel; the deterministic analogue of the 'some fuel = least fixpoint' corollary.
- D. Bridges, E. Palmgren and H. Ishihara. Constructive Mathematics. Stanford Encyclopedia of Philosophy, substantive revision of 25 August 2022, https://plato.stanford.edu/entries/mathematics-constructive/. Section 1 (Introduction): the limited principle of omniscience (LPO) is not constructively derivable (Kripke models; Bridges and Richman 1987, chapter 7). Section 2 (The Constructive Interpretation of Logic): Markov's principle (MP) is not constructively derivable (a Kripke model; Bridges and Richman 1987, pp. 137–138).
- T. Nipkow. Hoare logics for recursive procedures and unbounded nondeterminism. CSL 2002, pp. 103–119. doi:10.1007/3-540-45793-3_8; mechanized in the Isabelle Archive of Formal Proofs entry Abstract-Hoare-Logics. Mechanized total correctness in the presence of unbounded nondeterminism (not a continuity-failure theorem).
- S. Spies, L. Gäher, D. Gratzer, J. Tassarotti, R. Krebbers, D. Dreyer, L. Birkedal. Transfinite Iris: resolving an existential dilemma of step-indexed separation logic. PLDI 2021, pp. 80–95. doi:10.1145/3453483.3454031. Moves the step index of Iris from natural numbers to ordinals to resolve a problem with existential quantification in step-indexed logics (bibliographic record and title verified; details not re-read here) — related to the limits of natural-number fuel under unbounded or existential choice.
- B. Alpern and F. B. Schneider. Defining liveness. Information Processing Letters 21(4):181–185, 1985. doi:10.1016/0020-0190(85)90056-0. Liveness properties say something good eventually happens; every property is the intersection of a safety property and a liveness property.
- L. Lamport. Proving the correctness of multiprocess programs. IEEE Transactions on Software Engineering SE-3(2):125–143, 1977. doi:10.1109/TSE.1977.229904. Proofs of safety and liveness properties of concurrent programs (bibliographic record verified; content not re-read here).
- V. Preoteasa. Algebra of Monotonic Boolean Transformers. Archive of Formal Proofs, September 2011 (isa-afp.org/entries/MonoBoolTranAlgebra.html). Abstract: an algebra of monotonic Boolean transformers modelling total correctness, refinement, demonic and angelic choice.
- W. Guttmann. Algebras for Iteration, Infinite Executions and Correctness of Sequential Computations. Archive of Formal Proofs, October 2021 (isa-afp.org/entries/Correctness_Algebras.html). Abstract: algebras for iteration and infinite executions that unify computation models differing in the fixpoints used for iteration, and correctness statements across models.
- J. Åman Pohjola, M. O. Myreen, M. Tanaka. A Hoare Logic for Diverging Programs. Archive of Formal Proofs, January 2023 (isa-afp.org/entries/HoareForDivergence.html). Abstract: a While language with output, a total-correctness Hoare logic proved sound and complete, and a new Hoare logic for programs that diverge, also proved sound and complete — a mechanized alternative for stating properties of diverging runs.
- J. Åman Pohjola, H. Rostedt, M. O. Myreen. Characteristic Formulae for Liveness Properties of Non-Terminating CakeML Programs. ITP 2019, LIPIcs 141, 32:1–32:19. doi:10.4230/LIPIcs.ITP.2019.32 (DataCite record verified). Liveness reasoning for programs that are meant not to terminate (content beyond the title not re-read here).
- E. M. Clarke and E. A. Emerson. Design and synthesis of synchronization skeletons using branching time temporal logic. Logics of Programs, Lecture Notes in Computer Science, Springer, pp. 52–71. doi:10.1007/BFb0025774 (volume number and year are not given in the DOI record). Branching-time temporal logic, whose operator AF ('on all paths, eventually') is the shape of AllRunsEventually (bibliographic record verified; content not re-read here).
- D. Kozen. Results on the propositional μ-calculus. Theoretical Computer Science 27(3):333–354, 1983. doi:10.1016/0304-3975(82)90125-6. The propositional μ-calculus, in which eventuality properties such as AF are least fixpoints and safety properties greatest fixpoints (bibliographic record verified; content not re-read here).
- A. Tarski. A lattice-theoretical fixpoint theorem and its applications. Pacific Journal of Mathematics 5(2):285–309, 1955. doi:10.2140/pjm.1955.5.285. The fixed points of a monotone map on a complete lattice form a complete lattice; in particular least and greatest fixed points exist (the source of the impredicative definitions of wpLfp and wpGfp).

## Revalidation

Requirements: `elan` (which installs the toolchain pinned in `lean/lean-toolchain`, `leanprover/lean4:v4.34.1`)
and `python3`. No network access is needed beyond the toolchain download.

**Primary check**, run from the package directory:

```sh
python3 support/revalidate.py .
```

It copies `lean/` to a temporary directory, runs `lake build`, rejects `sorry`, `admit`, `native_decide` and
`axiom` declarations in every Lean source, computes the axioms of every library declaration with Lean's
`collectAxioms` (allowed: `propext`, `Classical.choice`, `Quot.sound`; 439 declarations), and, for every Lean name in
the standard card fields of `results.json` (`lean`, `lean_names`, `nonvacuity_witness_lean`, `positive_control_lean`,
`scope_witnesses_lean`, `corollaries_lean` and the hypotheses' `counterexample`) and every name in
`audit/statements.json` (72 names in this package, all with a recorded hash), checks that the declaration exists and
recomputes the statement hash (SHA-256 of the `repr` of the declaration's type) and the closure hash (SHA-256 of the
sorted lines `name : repr type [:= repr value]` of every library constant reachable from the type, theorem bodies
excluded), comparing them with `audit/statements.json`. It does not read this package's two additional fields
`logic_evidence_lean` and `boundary_evidence_lean` (26 further names, listed under Evidence without a hash): their
axioms are covered by the sweep over all library declarations, and their existence is checked by the manual
equivalent below, whose `lean/RevalidationAudit.lean` lists all 98 referenced names. It prints `REVALIDATED` and
exits with status 0 iff every check passes.

**Manual equivalent** with only `lake` and `python3`, from the package directory. `lean/RevalidationAudit.lean` is
outside the library target; it prints `AXIOMS <name> <axioms>` for every library declaration and `STATEMENT <json>`
(type `repr` and closure lines) for every name referenced by `results.json` in any field (98 names, including
`logic_evidence_lean` and `boundary_evidence_lean`), or `MISSING <name>` if a name does not exist:

```sh
cd lean
lake build
lake env lean RevalidationAudit.lean > /tmp/fuelwp_audit.out
python3 - /tmp/fuelwp_audit.out <<'EOF'
import hashlib, json, sys
rec = json.load(open("../audit/statements.json"))["statements"]
allowed = {"propext", "Classical.choice", "Quot.sound"}
bad = hashed = 0
for line in open(sys.argv[1], encoding="utf-8"):
    if line.startswith("AXIOMS "):
        _, name, axs = line.rstrip("\n").split(" ", 2)
        extra = set(axs.strip("[]").replace(" ", "").split(",")) - allowed - {""}
        if extra:
            print("FAIL axioms", name, extra); bad += 1
    elif line.startswith("MISSING "):
        print("FAIL", line.strip()); bad += 1
    elif line.startswith("STATEMENT "):
        s = json.loads(line[len("STATEMENT "):])
        r = rec.get(s["name"])
        if r is None:
            continue  # referenced name without a recorded hash: existence checked only
        got = (hashlib.sha256(s["type_repr"].encode()).hexdigest(),
               hashlib.sha256("\n".join(s["closure"]).encode()).hexdigest(), len(s["closure"]))
        hashed += 1
        if got != (r["statement_sha256"], r["closure_sha256"], r["closure_size"]):
            print("FAIL hash", s["name"]); bad += 1
print(f"{hashed} statement/closure hashes compared; {bad} failures")
EOF
```

The snippet must print `72 statement/closure hashes compared; 0 failures`. A banned-token scan of the sources:

```sh
grep -rnwE 'sorry|admit|native_decide' --include='*.lean' ToyFuelWP ToyFuelWP.lean
grep -rnE '^\s*(private\s+)?(axiom|opaque)\b' --include='*.lean' ToyFuelWP ToyFuelWP.lean
```

Both commands must print nothing (a match inside a comment would need manual inspection).

**What a passing run establishes.** That the theorems named on the cards are kernel-checked under
`leanprover/lean4:v4.34.1` with only the listed axioms, and that their statements and the definitions they depend on
are byte-for-byte (at the level of Lean `repr`) the ones recorded here. It does not re-establish the modeling bridge
to any real system or the prior-art records. After a toolchain change, the `repr` text, and hence the hashes, may
change even if the mathematics is unchanged; then compare the statements quoted under Findings (verbatim from the cited source lines) instead.

