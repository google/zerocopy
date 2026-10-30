<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Aeneas, Hax, and RefinedRust/Lithium Verification Architecture, Generic Specification Telescopes, and Trace-Preserving Loop Reasoning in Lean 4

## Summary

Rust verification frameworks that target interactive theorem provers or
automated SMT backends must reconcile four competing requirements: a small,
auditable trusted computing base (TCB); compositional reasoning about mutable
borrows and loops without raw heap-frame boilerplate; predictable proof
automation that degrades gracefully into source-located obligations when a
solver fails; and preservation of operational step traces for termination and
constant-time side-channel adequacy.

This report synthesizes primary-source analyses of the `Aeneas` Lean 4 backend
(`AeneasVerif/aeneas` at `70683bd4ab876179a23e5f994d02947b3e5c4f0d` and local
snapshot `8ab2e7e4e47fe73fd5b2a0c061293e00b30013fe`), Cryspen's `hax` Lean 4
backend (`cryspen/hax` at `1ec88cdb2c8e546845e64eb2cd2321b4f58069c4`),
`RefinedRust` (`lgaeher/refinedrust-dev` at
`8a07f4f2e6a499625b4b25e94f0b2ab78592cb52` and PLDI 2024 artifact `be9dc71f`)
together with `RefinedC` (`iris/refinedc` at
`d057583986651a28047164581f05fbee3a83ed9d`), and comparative Rust verification
architectures (`Creusot` at `c4e9770ac1371ac4274bfe02145266d315c2fb86`, `Verus`
at `0141ebc6f14410dfc87fef1da57408578002eb7c`, `Kani` at
`9461e07af7ec929f050aa4192f29363c9be07779`, `Gillian` at
`83d739e83034d71162fb66b569041cf301123df7`, and `RustBelt` / `lambda-rust` at
`186900b2cf948835873281646ce20c7e8f084f17`). It pairs those architectural
findings with two standalone, zero-`sorry` Lean 4.34.1 mechanization probes
(`support/ProbeGeneralSpecAndLithium.lean` and
`support/ProbeTrackedFuncLangAndLoops.lean`) against Anneal's verification
kernel (`joshlf/anneal` at `e75556f57d76d09fd5fc84fc4bfca6a89c3b85e0` / worktree
`42f4571d761b46c7142815f38b69c3781b3555e3`):

- **Aeneas and Cryspen Hax Lean 4 Architecture:** Aeneas translates safe Rust
  via Charon LLBC into pure monadic functions in `Result α` (`.ok`, `.fail`,
  `.div`) equipped with a complete chain-complete partial order (`CCPO`) over
  `FlatOrder .div` and `MonoBind Result`, turning recursive and loop bodies into
  `partial_fixpoint` definitions (`backends/lean/Aeneas/Std/Primitives.lean`,
  lines 50–222). Its weakest-precondition calculus
  (`backends/lean/Aeneas/Std/WP.lean`, lines 9–529) pairs a custom `@[step]`
  (formerly `@[progress]`) tactic engine backed by a persistent `StepGrindState`
  e-graph (`Step.lean`, lines 355–755; `StepStar.lean`, lines 415–895) with a
  `Std.Do.WPMonad` bridge for `mvcgen` and an interaction-tree `DWP`/`DWLP`
  total-versus-partial adequacy taxonomy (`Taxonomy.lean`, lines 1–39). As of
  commit `1ec88cdb2c8e546845e64eb2cd2321b4f58069c4`, Cryspen's `hax` Lean 4
  library unified directly onto `public import Aeneas`, proving `@[step]`
  machine-integer specifications over `partialSpec` (`ITreeWP.dwlp`) using
  `grind`.
- **RefinedRust and Lithium Goal-Directed Type System:** RefinedRust's `radium`
  frontend (`rr_frontend/radium/src/code.rs`, lines 1381–1426) emits an
  identical 7-line Rocq proof script for every Rust function (`rep <-! liRStep;
  liShow`, followed by two-tier `sidecond_solver` and `sidecond_hammer` passes).
  The `Lithium` engine (`theories/refinedrust/lithium/interpreter.v`, lines
  354–976) enforces deterministic, backtracking-free syntax-directed execution
  over a curated grammar of separation-logic connectives, isolating pure side
  conditions behind `SHELVED_SIDECOND` (`proof_state.v`, lines 9–34), caching
  previously proved pure obligations via `CACHED` and join-block preconditions
  via `JCACHED` (`rust_typing/automation/proof_state.v`, lines 63–164), and
  tracking source spans and branch history through `RUST_PROGRAM_POINT` and
  `CASE_DISTINCTION_INFO`.
- **Eliminating Per-Function `Ensures*` TCB Growth
  (`ProbeGeneralSpecAndLithium.lean`):** Anneal's baseline kernel
  (`trusted/lean/Trusted/MirSemantics.lean`, lines 511–777;
  `trusted/rustc-capture/src/proof_gen.rs`, lines 50–376) defines 15 bespoke
  `Ensures*` predicates (`EnsuresEqArg`, `EnsuresMaxAssign`,
  `EnsuresClampAssign`, etc.) and 15 matching `translate_*_spec` unpacking
  theorems in `theory/Anneal/FunctionalTranslation.lean`. Replacing all 15
  shape-specific predicates with a single generic `FnSig` / `FuncSpec` contract
  in `Trusted/` and an inductive `ArgSpec` telescope in `Theory/` collapses the
  15 unpacking theorems into a single 35-line generic soundness theorem
  (`funcSpec_verified`) while discharging `maxAssign`, `clampAssign`, and
  lifetime-Carry `chooseMut` via a single uniform tactic (`by anneal_vcgen`)
  with `ShelvedVC` source-span and branch-path diagnostics (`R-UX-01`,
  `R-UX-02`).
- **Trace-Preserving Functional Translation (`TrackedFuncLang` in
  `ProbeTrackedFuncLangAndLoops.lean`):** Anneal's existing `FuncLang`
  (`FunctionalTranslation.lean`, lines 3768–3791) erases intermediate
  basic-block execution into a single terminal transition emitting `[] : List
  StepObs`, forfeiting step-count and branch-timing adequacy. Upgrading
  `evalSymWith` to `evalSymWithTracked` threads an explicit `List StepObs`
  accumulator emitting `[StepObs.step]` at every basic-block dispatch. Because
  the functional projection $\pi_{\text{tracked}}$ emits exactly the same
  `[StepObs.step]` per step as `MirLang.step`, `evalSymWithTracked_sound` proves
  `ForwardSim MirLang TrackedFuncLang` for all 5 MIR terminators (`return_`,
  `goto`, `switchInt`, `assert`, `call`) with zero trace erasure, yielding exact
  trace lengths (`trackedFuncLang_exact_trace_length_at_steps`) and full
  `Language.SpecOn` adequacy (`trackedFuncLang_adequacy_specOn`).
- **Compositional Loop Invariants, Diamond Join Cutpoints, and Constant-Time
  2-Safety (`ProbeTrackedFuncLangAndLoops.lean`):** Proving `loop_spec_decr_nat`
  and `tracked_loop_spec_decr_nat` by well-founded induction on a natural-number
  ranking measure $m(\sigma)$ allows cyclic MIR bodies such as `sumToNBody`
  (`while i < n { acc += i; i += 1 }`) to be verified with a fuel-free
  precondition ($n \le 1000$, independent of recursion fuel) and exact loop-step
  trace length $n + 2$ (`sumToN_satisfies_fuelFree_specOn`). Combining
  `diamond_join_cutpoint` with a `JCACHED` hypothesis check collapses $k$
  sequential diamond branches from $2^{k+1} - 2$ symbolic states to $2k$
  obligations (`twoDiamondBody_verified_linear`). Finally, `BranchAligned`
  establishes a 2-safety relational bridge
  (`trackedFuncLang_implies_constantTime2Safety`) that proves constant-time
  execution of secret-input functions such as `ctPublicModeXorBody`
  (`ctPublicModeXor_is_constant_time`) directly from `TrackedFuncLang`.

## Applicability

The findings and mechanized probes in this report apply directly to the
following Anneal subsystems and verification workflows:

- **`trusted/lean/Trusted/MirSemantics.lean` and
  `trusted/rustc-capture/src/proof_gen.rs`:** Section 3 provides a drop-in
  replacement for the 15 shape-specific `Ensures*` definitions in
  `Trusted/MirSemantics.lean` (lines 511–777) and the 15 hard-coded structural
  match arms in `proof_gen.rs` (lines 50–376). Adopting `FnSig` and `FuncSpec`
  freezes the trusted function-contract schema in `Trusted/` permanently, moving
  all argument-shape unpacking (`ArgSpec`) into `Theory/`.
- **`theory/Anneal/FunctionalTranslation.lean`:** Section 3 replaces the 15
  bespoke `translate_*_spec` theorems (such as `translate_maxAssignBody_spec` at
  lines 4343–4404, `translate_clampAssignBody_spec` at lines 5277–5365, and
  `translate_chooseMut_spec` at lines 7159–7238) with a single generic
  telescopic bridge (`funcSpec_verified`). Section 4 upgrades `evalSymWith` and
  `FuncLang` (lines 3768–3791, 7414–7463) to `evalSymWithTracked` and
  `TrackedFuncLang`, preserving `[StepObs.step]` observations across forward
  simulation without modifying `Trusted/Refinement.lean` or
  `Trusted/StepResult.lean`.
- **Loop Verification, CFG Join Sharing, and Constant-Time Side-Channel Proofs
  in `theory/Anneal/`:** Section 5 provides the compositional loop-invariant
  rules (`loop_spec_decr_nat` and `tracked_loop_spec_decr_nat`), the diamond CFG
  join-point cutpoint rule (`diamond_join_cutpoint`) with `JCACHED`
  side-condition subsumption, and the `BranchAligned` relational 2-safety bridge
  (`trackedFuncLang_implies_constantTime2Safety`) for verifying loop termination
  and secret-independent execution traces over captured MIR.

## Findings

### 1. Aeneas and Cryspen Hax Lean 4 Verification Architecture

`Basis: primary source inspection of AeneasVerif/aeneas at 70683bd4ab876179a23e5f994d02947b3e5c4f0d and 8ab2e7e4e47fe73fd5b2a0c061293e00b30013fe (plus historical checkpoints 21345f80fa212c596f6437378d7d57984fa2ea77 and ac9f1bc5262a5e4ff1e24ca78617121382202727) and cryspen/hax at 1ec88cdb2c8e546845e64eb2cd2321b4f58069c4.`

#### 1.1 Pure Functional Translation, `Result` CCPO, and Fixed-Point Loops

Aeneas translates safe Rust programs—extracted via Charon into Low-Level Borrow
Calculus (LLBC)—into pure, state-free functional Lean 4 definitions by
eliminating mutable borrows (`&mut T`) through backward functions (prophetic
return tuples that yield updated borrowed values alongside the primary return
value when a borrow ends). Every potentially panicking or diverging Rust
computation is wrapped in the three-valued `Result α` monad in
`backends/lean/Aeneas/Std/Primitives.lean` (lines 50–102):

```lean
inductive Error where
  | assertionFailure : Error
  | integerOverflow : Error
  | divisionByZero : Error
  | arrayOutOfBounds : Error
  | maximumSizeExceeded : Error
  | panic : Error
  | undef : Error
deriving Repr, BEq, DecidableEq

inductive Result (α : Type u) where
  | ok : α → Result α
  | fail : Error → Result α
  | div : Result α
deriving Repr, BEq, DecidableEq

def massert (b : Prop) [Decidable b] : Result Unit :=
  if b then ok () else fail assertionFailure
```

Rather than threading an explicit `fuel : Nat` parameter through generated Lean
functions, Aeneas equips `Result α` with Lean 4's `Order.CCPO` (chain-complete
partial order) and `Order.MonoBind` instances over `FlatOrder Result.div`
(`backends/lean/Aeneas/Std/Primitives.lean`, lines 167–179):

```lean
instance : CCPO (Result α) := inferInstanceAs (CCPO (FlatOrder Result.div))

instance : MonoBind Result where
  bind_mono_left h := by
    cases h
    · exact FlatOrder.rel.bot
    · exact FlatOrder.rel.refl
  bind_mono_right h := by
    cases ‹Result _›
    · exact h _
    · exact FlatOrder.rel.refl
    · exact FlatOrder.rel.refl
```

With `CCPO (Result α)` and `MonoBind Result` in scope, every Rust `while` or
`loop` construct lowers to a tail-recursive continuation over `ControlFlow α β`
(`Continue α` or `Break β`) defined via Lean 4's `partial_fixpoint` mechanism
(`Primitives.lean`, lines 209–222):

```lean
def loop {α β} (body : α → Result (ControlFlow α β)) (x : α) : Result β := do
  match ← body x with
  | .Continue x => loop body x
  | .Break y => ok y
partial_fixpoint
```

#### 1.2 Weakest-Precondition Calculus (`Std.WP`), `predn`, and Coinductive `ITree` Taxonomy

In `backends/lean/Aeneas/Std/WP.lean` (lines 9–65), Aeneas defines its core
total-correctness weakest-precondition transformer `Wp.wp` (`theta`) and Hoare
specification predicate `spec`:

```lean
def wp (e : Result α) (p : α → Prop) : Prop :=
  match e with
  | ok x => p x
  | fail _ => False
  | div => False

abbrev theta := @wp

def spec (e : Result α) (p : α → Prop) : Prop := wp e p
```

Because functional translation of a Rust function with $k$ mutable borrows
produces a Lean function returning a nested product $\alpha_0 \times \alpha_1
\times \dots \times \alpha_k$, naive postconditions `p : (α₀ × α₁ × …) → Prop`
force nested tuple projections `x.1`, `x.2.1`, `x.2.2` into user specifications
and proof states. Aeneas eliminates tuple-projection noise using the recursive
currying combinator `predn` (`Std/WP.lean`, lines 61–65, 127–155):

```lean
@[reducible]
def predn (ty : List (Type u)) : Type u :=
  match ty with
  | [] => Prop
  | a :: ty => a → predn ty
```

Specialized n-ary postcondition wrappers (`pred1`, `pred2`, `pred3`, …) allow
`spec_bind'` (`Std/WP.lean`, lines 142–155) and `qimp_spec_predn` to introduce
destructured variables directly into the local context during monadic bind
stepping without intermediate `Prod.fst`/`Prod.snd` redexes.

In upstream commits through `70683bd4ab876179a23e5f994d02947b3e5c4f0d`, Aeneas
further generalizes its semantic foundation with a coinductive Interaction Tree
(`ITree`) semantics
(`backends/lean/Aeneas/Data/Coinductive/ITreeWP/Taxonomy.lean`, lines 1–39) that
classifies specifications along two orthogonal axes—**Total** (must terminate,
`.div ↦ False`) versus **Partial** (allows divergence, `.div ↦ True`), and
**Demon** (universal over nondeterminism) versus **Angel** (existential over
nondeterminism)—yielding four modalities (`DWP`, `DWLP`, `AWP`, `AWLP`)
connected by `DWP.toPartial` and `dwp_no_loops` (proving that for loop-free
computations, partial correctness implies total correctness).

At the same time, Aeneas registers `Result.instWP` and `WPMonad Result` for Lean
4's `Std.Do.PredTrans` framework (`Std/WP.lean`, lines 447–480):

```lean
instance Result.instWP : Std.Do.WP Result .pure where
  wp x :=
    match x with
    | .ok v => pure v
    | .fail _ | .div => PredTrans.const ⌜False⌝
```

This instance lets users mix Aeneas's `@[step]` tactic with standard Lean 4.34+
`mvcgen` tactics on `Result` blocks.

#### 1.3 Evolution from `@[progress]` to `@[step]` and Persistent `StepGrindState`

Across Aeneas's 2025–2026 development history (`21345f80` → `ac9f1bc5` →
`8ab2e7e4` → `70683bd4`), the primary forward symbolic execution tactic evolved
from `progress` (`@[progress]`) into `step` (`@[step]`) and `step*`
(`backends/lean/Aeneas/Tactic/Step/Init.lean`, lines 20–150; `Step.lean`, lines
355–755; `StepStar.lean`, lines 415–895):

1. **Discrimination-Tree Specification Lookup (`Init.lean`, lines 60–145):**
   User and library theorems tagged with `@[step]` are indexed in a persistent
   `DiscrTree` keyed by the head constant of the monadic scrutinee `f x₁ … xₙ`
   inside `spec (do let y ← f x₁ … xₙ; k y) P` (or raw equality `f x₁ … xₙ = ok
   y`), alongside a `#register_spec_info` side-table recording whether each
   parameter is an input or an output and whether preconditions are pure or
   monadic.
2. **Persistent Incremental `grind` State (`StepGrindState` in `Step.lean`,
   lines 355–420):** Rather than initializing a fresh `Meta.Grind` or `omega`
   context from scratch at every monadic bind step—which incurs $O(N^2)$ context
   re-internalization on functions with $N$ sequential calls—`step*` maintains a
   single `StepGrindState` containing a live `Sym.State` and `Grind.Goal` across
   the entire forward pass (`StepStar.lean`, lines 415–520). Each step
   internalizes only the newly introduced postcondition hypotheses into the
   existing e-graph.
3. **Two-Phase Precondition Discharging (`trySolvePreconditions` in `Step.lean`,
   lines 480–565):** When applying a `@[step]` theorem generates precondition
   goals $P_1, \dots, P_m$, `trySolvePreconditions` first runs a fast pass
   (`grind => lia`) over goals containing no unassigned metavariables, and then
   runs an instantiation pass over remaining goals. Any precondition that cannot
   be closed automatically is left open as a subgoal tagged with the originating
   variable or assertion name (`withMainContext` + synthetic user-facing goal
   tag).
4. **Dead-Branch Pruning at `if`/`match` Splits (`esplitAtSpec` in
   `StepStar.lean`, lines 610–695):** When `step*` encounters an `if c then t
   else e` or `match` scrutinee, `esplitAtSpec` internalizes the branch
   condition (`c` or `¬c`) into a forked copy of `StepGrindState` and queries
   `ss.contradictionProof?`. Infeasible branches (for example, overflow or
   bounds paths contradicted by earlier checks) are pruned immediately before
   symbolic execution descends into their subtrees.

#### 1.4 Machine-Integer Reasoning (`UScalar`, `IScalar`, `scalar_tac`, and `bv_tac`)

In `backends/lean/Aeneas/Std/Scalar/Core.lean` (lines 66–300), Aeneas models
machine integers (`U8`..`U128`, `Usize`, `I8`..`I128`, `Isize`) as thin wrappers
(`UScalar (ty : UScalarTy)` and `IScalar (ty : IScalarTy)`) around `BitVec
ty.numBits`, projecting to `Nat` (`UScalar.val`) or `Int` (`IScalar.val`) for
linear arithmetic and to `BitVec` (`UScalar.bv`) for bitwise operations. To
prevent Lean's kernel `whnf` reducer from unfolding large power-of-two constants
such as $2^{64} - 1$ or $2^{128} - 1$ during unification, maximum bounds
(`U32.max`, `U64.max`, `Usize.max`) are defined via `irreducible_def`, and their
values are exposed selectively to `scalar_tac` and `grind` through
`@[scalar_tac_simps]` and `grind_pattern` lemmas (`Core.lean`, lines 180–295).

For bitwise goals, `bv_tac`
(`backends/lean/Aeneas/Tactic/Solver/BvTac/BvTac.lean`, lines 10–124) runs a
preprocessing pipeline (`bvifyTacSimp` followed by `bvifyTac`) that rewrites
`Nat`/`Int` inequalities and modular arithmetic on `UScalar.val` into pure
`BitVec` propositions before invoking `bv_decide`.

#### 1.5 Unification of Cryspen `hax` onto `Aeneas`

Whereas earlier versions of Cryspen's `hax` maintained a separate Lean 4 monadic
prelude, commit `1ec88cdb2c8e546845e64eb2cd2321b4f58069c4` of `cryspen/hax`
unifies `hax`'s Lean 4 proof library directly onto `Aeneas`. In
`hax-lib/proof-libs/lean/CoreModels/RustPrimitives/Types.lean` (lines 1–13),
`hax` re-exports Aeneas's `Result`, `UScalar`, `IScalar`, and `WP` namespace via
`public import Aeneas`:

```lean
public import Aeneas
open Aeneas.Std

public section
attribute [- simp] Bool.exists_bool

namespace Rust_primitives.Hax
abbrev Tuple0 := Unit
```

In `hax-lib/proof-libs/lean/CoreModels/Spec/RustPrimitives/Arithmetic.lean`
(lines 1–59), `hax` proves `@[step]` theorems for machine-integer operations
over `partialSpec` (`ITreeWP.dwlp`) using `grind`, while
`hax-lib/proof-libs/lean/Hax/Tactic/HaxMvcgen.lean` (lines 19–68) provides
`hax_mvcgen` to decompose `Std.Do.Triple` hypotheses and goals in a saturation
loop.

---

### 2. RefinedRust and Lithium Goal-Directed Proof Engine and Comparative Rust Verifier Landscape

`Basis: primary source inspection of lgaeher/refinedrust-dev at 8a07f4f2e6a499625b4b25e94f0b2ab78592cb52 (and PLDI 2024 artifact be9dc71f), iris/refinedc at d057583986651a28047164581f05fbee3a83ed9d, and comparative inspection of creusot-rs/creusot at c4e9770ac1371ac4274bfe02145266d315c2fb86, verus-lang/verus at 0141ebc6f14410dfc87fef1da57408578002eb7c, model-checking/kani at 9461e07af7ec929f050aa4192f29363c9be07779, GillianPlatform/Gillian at 83d739e83034d71162fb66b569041cf301123df7, and iris/lambda-rust at 186900b2cf948835873281646ce20c7e8f084f17.`

#### 2.1 Radium Uniform Proof Script Generation

RefinedRust's `radium` compiler frontend (`rr_frontend/radium/src/code.rs`,
lines 1381–1426) translates each Rust MIR function into a Rocq typing lemma
whose generated proof script is uniform across all functions, regardless of
their signature, control-flow graph, or borrow structure:

```coq
Proof.
  <fn_name>_prelude.
  rep <-! liRStep; liShow.
  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  <user_tactics_if_any>
  Unshelve. all: print_remaining_sidecond.
Qed.
```

This architecture enforces a strict separation of concerns:

1. **Code generation (`radium`)** never inspects the body of a function to emit
   shape-specific proof steps (`EnsuresMaxAssign`, `EnsuresClampAssign`, etc.);
   it emits only the syntactic MIR body, the user's refinement-type
   specification (`fn_type`), and the fixed 7-line proof script above.
2. **Goal-directed symbolic execution (`rep <-! liRStep; liShow`)** steps
   deterministically through the MIR basic blocks and separation-logic typing
   rules without backtracking, reducing all spatial ownership and borrow
   transfers and shelving pure arithmetic or logical obligations onto Rocq's
   evar shelf.
3. **Two-tier side-condition solving (`sidecond_solver` then
   `sidecond_hammer`)** discharges the shelved pure obligations in bulk after
   symbolic execution completes, printing source-attributed diagnostics
   (`print_remaining_goal` and `print_remaining_sidecond`) for any obligation
   that remains unsolved.

#### 2.2 The Lithium Goal-Directed Interpreter (`liStep`, `Subsume`, `FindInContext`, `LiTactic`)

The core engine underlying both RefinedC (`theories/lithium/interpreter.v`,
lines 354–976) and RefinedRust (`theories/refinedrust/lithium/interpreter.v`,
lines 354–976; `definitions.v`, lines 8–144; `syntax.v`, lines 12–120) is
**Lithium**, a deterministic, fragment-restricted separation-logic interpreter.
Instead of searching over arbitrary Iris tactics (which suffers from exponential
backtracking when framing resources across branches), Lithium restricts typing
rules to a syntax-directed grammar of separation-logic formulas where every
connective has a deterministic introduction or elimination action in `liStep`:

| Lithium Connective | Definition (`definitions.v` / `syntax.v`) | Interpreter Action (`interpreter.v`) |
| :--- | :--- | :--- |
| `⌜P⌝` (`iProp_to_Prop`) | Pure proposition embedded in `iProp` | Left: intro pure hypothesis. Right: call `liSideCond P` to check cache or shelve `P` (`lines 540–558`). |
| `∃ x, P x` / `∀ x, P x` | Existential / universal quantifier | Left `∃`: intro fresh binder. Right `∃`: instantiate with schematic evar `?x` (`lines 405–440`). |
| `P ∗ Q` (`bi_sep`) | Separating conjunction | Left: destruct into context. Right: sequence via `liSep` (`lines 360–395`). |
| `P -∗ Q` (`bi_wand`) | Separating implication | Right: intro spatial premise into context (`liWand`, `lines 396–404`). |
| `FindInContext F P` | Typeclass-driven context query (`find_in_context F (λ x, P x)`) | Scans spatial context for resource matching pattern `F`, binds witness `x`, and continues with `P x` (`liFindInContext`, `lines 475–510`). |
| `Subsume A B P` | Resource subsumption (`subsume A (λ x, B x) (λ x, P x)`) | Matches owned resource `A` against target `B x`, instantiating schematic evars `?x` and leaving continuation `P x` (`lines 511–539`). |
| `case_if c P Q` | Annotated branch split (`CASE_DISTINCTION_INFO`) | Splits goal into two subgoals carrying `CASE_DISTINCTION_INFO` with the branch condition (`liCase`, `lines 441–474`). |
| `LiTactic T P` | Controlled escape hatch (`li_tactic T (λ x, P x)`) | Runs deterministic custom rule `T` to compute witness `x` before resuming `P x` (`liTactic`, `lines 559–575`). |
| `li_vm_compute f x` | Kernel/VM reduction step | Reduces pure functional helper `f x` via `vm_compute` before continuing (`syntax.v`, `lines 85–108`). |
| `li_trace info P` | Execution breadcrumb marker | Pushes `info` (e.g. `RUST_PROGRAM_POINT` or `LAST_RUST_PROGRAM_POINT`) into the proof context (`liTrace`, `lines 576–592`). |

#### 2.3 Shelved Side Conditions (`SHELVED_SIDECOND`), Caching (`CACHED` / `JCACHED`), and Source-Located Diagnostics

Three mechanisms in Lithium and RefinedRust directly address proof-automation
scalability and diagnostic clarity:

1. **Shelving Pure Obligations (`theories/refinedrust/lithium/proof_state.v`,
   lines 9–34):** When `liStep` encounters a pure obligation `⌜P⌝` on the
   right-hand side of a goal, it does not invoke `lia` or `smt` inline (which
   would stall symbolic execution and pollute the spatial context). Instead,
   `liSideCond` invokes `liSidecond_hook P` (`typing/automation.v`, lines
   2114–2150): if `P` is trivially `True` or syntactic reflexivity (`x = x`), it
   closes immediately; otherwise `shelve_sidecond` wraps the current pure
   hypotheses and `P` inside `SHELVED_SIDECOND (P : Prop) : Prop := P` and moves
   the subgoal onto Rocq's evar shelf. After `rep <-! liRStep` finishes the
   entire CFG traversal, `Unshelve. all: sidecond_solver` and `Unshelve. all:
   sidecond_hammer` discharge all shelved pure goals in two tiers.
2. **Side-Condition and Join-Block Caching
   (`rust_typing/automation/proof_state.v`, lines 63–164;
   `typing/program_rules.v`, lines 5056–5100):**
   - `CACHED (P : Prop) : Prop := P`: When a pure side condition `P` is shelved
     along a path, `cache_sidecond` records `H : CACHED P` in the ambient
     context so subsequent occurrences of `P` along the same path are discharged
     in $O(1)$ by context lookup instead of generating duplicate shelved goals.
   - `JCACHED (P : iProp Σ) : iProp Σ := P`: At control-flow join points
     (`type_goto` / `type_goto_precond` in `program_rules.v`, lines 5056–5100),
     evaluating the target basic block's continuation inline at every incoming
     edge would duplicate the downstream CFG across every `if`/`match` diamond.
     RefinedRust records join-block preconditions in `BLOCK_PRECOND` and caches
     their verification under `JCACHED` (`init_jcache`, `enter_jcache`,
     `open_jcache`), verifying the join block once and reducing incoming edges
     to proving the join block's precondition.
3. **Source-Span and Branch-Path Diagnostics
   (`rust_typing/automation/proof_state.v`, lines 20–62, 310–538):** As
   `liRStep` steps through MIR statements and terminators, it updates
   `RUST_PROGRAM_POINT` and `LAST_RUST_PROGRAM_POINT` with the Rust source span
   and records every `switchInt` decision in `CASE_DISTINCTION_INFO`. If either
   a spatial typing step (`print_remaining_goal` / `print_typesystem_goal`) or a
   shelved pure side condition (`print_remaining_sidecond` /
   `print_remaining_shelved_goal`) fails, `liExplain` extracts these markers and
   prints the exact Rust source location, the obligation category (e.g. integer
   overflow, bounds check, or postcondition mismatch), and the sequence of
   branch conditions taken to reach that program point.

#### 2.4 Observation-Trace Decidability (`CheckableObs`)

In `RefinedRust`'s operational adequacy theorem (`refinedrust_adequacy`),
operational traces include external event observations $\kappa \in \text{ List
Obs}$. Whenever the operational semantics or adequacy proof cases on whether an
emitted observation list matches an expected step trace, equality on
observations must be constructively decidable (`EqDecision` in Rocq /
`DecidableEq` in Lean 4) so symbolic evaluation and trace adequacy do not get
stuck on non-computable classical choice. In Anneal's `Trusted/StepResult.lean`,
`StepObs` (`inductive StepObs | step`) derives `DecidableEq`, which Section 4
leverages to keep `TrackedFuncLang` and `evalSymWithTracked` constructive and
dependently typed using only `[propext, Quot.sound]`.

#### 2.5 Comparative Synthesis Across `Creusot`, `Verus`, `Kani`, `Gillian-Rust`, and `RustBelt`

Comparing `Aeneas`, `hax`, and `RefinedRust`/`Lithium` against the broader Rust
verification landscape clarifies which design patterns transfer cleanly to
Anneal's Lean 4 kernel architecture:

| System (Inspected Revision) | Borrow & Memory Model | Loop & CFG Strategy | Proof Automation & Solver Boundary | Key Lesson for Anneal |
| :--- | :--- | :--- | :--- | :--- |
| **Aeneas** (`70683bd4` / `8ab2e7e4`) & **Hax** (`1ec88cdb`) | Pure functional translation via backward functions (`Result α` over `CCPO`) | `loop` via `partial_fixpoint`; `loop.spec_decr_nat` ranking measure (`Std/WP.lean:511`) | `@[step]` / `step*` with persistent `StepGrindState` + `scalar_tac` / `bv_tac` | Eliminate heap-frame boilerplate via pure functional projection; use `loop_spec_decr_nat` for fuel-free loop specs. |
| **RefinedRust** (`8a07f4f2`) & **Lithium** (`d0575839`) | Iris separation logic with prophetic borrows (`&uniq`) and ownership types | `BLOCK_PRECOND` + `JCACHED` join-block caching (`program_rules.v:5056`) | Uniform 7-line script (`rep <-! liRStep`), `SHELVED_SIDECOND`, `CACHED`, `RUST_PROGRAM_POINT` | Never emit per-function proof scripts; shelve pure side conditions with source spans and cache join points. |
| **Creusot** (`c4e9770a`) | Prophetic mutable borrows (`*x` current, `^x` final value) in Pearlite (`creusot/src/backend/place.rs`) | Coma IVL continuation handlers with explicit loop-invariant cutpoints (`clone_map.rs`) | Why3 / SMT VC generation with prophetic resolution at borrow expiration | Prophetic current/final borrow pairs (`*x`, `^x`) match Anneal's `SymArg.mutRef initVal finalVal` (`ArgSpec.mutRef`). |
| **Verus** (`0141ebc6`) | Linear ghost modes (`exec`, `tracked`, `spec`) without heap encoding for safe code | SST `ElaborateLoops` (`source/vir/src/loops.rs`) isolating modified vars and `decreases` | Z3 AIR queries with isolated `by(bit_vector)` and `by(nonlinear_arith)` sub-queries (`bitvector_to_air.rs`) | Keep bitvector (`bv_decide`) and linear integer (`omega`) obligations isolated in distinct side-condition passes. |
| **Kani** (`9461e07a`) | CBMC shadow memory for pointer provenance & byte initialization (`codegen/place.rs`) | Bounded unwinding (`#[kani::unwind(n)]`) or inductive `loop_contracts.rs` | Bit-precise SAT/SMT via CBMC `goto-cc` (`contract.rs`) | Bounded fuel unwinding (`fuel : Nat`) is sound only if paired with a fuel-free inductive loop rule (`loop_spec_decr_nat`). |
| **Gillian-Rust** (`83d739e8`) | Parametric hybrid tree/flat memory model with prophetic borrows (`symex.ml`) | Compositional symbolic summaries at function and loop boundaries | OCaml symbolic engine + Z3; unverified OCaml execution outside Rocq kernel | Anneal achieves Gillian-style symbolic execution inside the Lean 4 kernel by proving `evalSymWithTracked_sound`. |
| **RustBelt / `lambda-rust`** (`186900b2`) | Step-indexed Iris lifetime logic (`&'κ uniq T`, `theories/lifetime/lifetime.v`) | Manual CPS/Iris WP induction in Rocq | Interactive Iris Proof Mode (`iMod`, `iApply`) for unsafe primitives | Lifetime containment (`'a : 'b`) on reborrows can be checked syntactically via `Place.rootLocal` (`SymArg.mutRefFrom`). |

---

### 3. Generic Telescopic Function Contracts and Lithium-Style Diagnostic Shelving in Lean 4

`Basis: primary source inspection of joshlf/anneal at e75556f57d76d09fd5fc84fc4bfca6a89c3b85e0 (worktree 42f4571d761b46c7142815f38b69c3781b3555e3) and Lean 4.34.1 kernel verification of support/ProbeGeneralSpecAndLithium.lean (sha256 65f8af557997769bd43b4ce6eac36b79e1555bd222b75f31a4b439f08016895a).`

#### 3.1 Diagnosis of the `Ensures*` Bottleneck in `Trusted/MirSemantics.lean` and `proof_gen.rs`

In Anneal's baseline repository (`trusted/lean/Trusted/MirSemantics.lean`, lines
511–777), every new combination of immutable scalar arguments (`u32`, `bool`),
mutable reference arguments (`&mut u32`), and return references (`&'a mut u32`)
requires adding a new bespoke specification wrapper inside the trusted computing
base:

1. `Ensures` (1 `u32` → `u32`, lines 511–520)
2. `Ensures2` (2 `u32` → `u32`, lines 526–536)
3. `Ensures3` (3 `u32` → `u32`, lines 543–554)
4. `EnsuresEqArg` (lines 559–563)
5. `EnsuresEqArg2` (lines 568–572)
6. `EnsuresEqArg3` (lines 577–581)
7. `EnsuresPred` (1 `u32` → `bool`, lines 587–596)
8. `EnsuresPred2` (2 `u32` → `bool`, lines 602–612)
9. `EnsuresPred3` (3 `u32` → `bool`, lines 619–630)
10. `EnsuresMut1` (`&mut u32` → `unit`, lines 637–653)
11. `EnsuresMut2` (`&mut u32, &mut u32` → `unit`, lines 661–682)
12. `EnsuresMaxAssign` (`&mut u32, u32` → `unit`, lines 690–708)
13. `EnsuresClampAssign` (`&mut u32, u32, u32` → `unit`, lines 717–736)
14. `EnsuresChooseMut` (`bool, &'a mut u32, &'a mut u32` → `&'a mut u32`, lines
    745–771)
15. `EnsuresChooseMutFirst` (lines 774–777)

Correspondingly, `trusted/rustc-capture/src/proof_gen.rs` (lines 50–376)
contains 15 hard-coded structural match arms (`is_max_assign_fn`,
`is_clamp_assign_fn`, `is_choose_mut_fn`, etc.), and
`theory/Anneal/FunctionalTranslation.lean` repeats a 60–90 line
memory-allocation and `extractSymArgsAux` unpacking proof 15 times
(`translate_maxAssignBody_spec` at lines 4343–4404,
`translate_clampAssignBody_spec` at lines 5277–5365, `translate_chooseMut_spec`
at lines 7159–7238).

#### 3.2 Generic `FnSig` and `FuncSpec` in `Trusted/` vs. Inductive `ArgSpec` Telescopes in `Theory/`

In `support/ProbeGeneralSpecAndLithium.lean` (lines 204–223), we replace all 15
`Ensures*` predicates in `Trusted/` with a single, signature-independent
structure `FnSig` and a single specification predicate `FuncSpec`:

```lean
structure FnSig where
  /-- Well-formedness and user preconditions on the initial machine state. -/
  pre : MirState → Prop
  /-- Relational postcondition between initial and terminal machine states. -/
  post : MirState → MirState → Prop

def FuncSpec (body : Body) (sig : FnSig) : Prop :=
  ∀ s : MirState,
    Language.SpecOn MirLang
      (fun cfg => cfg.body = body ∧ cfg.state = s ∧ sig.pre s)
      (fun _ => True)
      (fun cfg' => cfg'.body = body ∧ sig.post s cfg'.state)
```

All argument-shape and reference-allocation structure moves out of `Trusted/`
into `Theory/` as an inductive specification telescope `ArgSpec`
(`support/ProbeGeneralSpecAndLithium.lean`, lines 502–561) aligned with
`extractSymArgsAux`:

```lean
inductive ArgSpec : Nat → Type where
  | nil (retSpec : Value → List SymArg → MirState → MirState → Prop) : ArgSpec 0
  | val (k : UInt32 → ArgSpec n) : ArgSpec (n + 1)
  | boolVal (k : Bool → ArgSpec n) : ArgSpec (n + 1)
  | mutRef (k : UInt32 → UInt32 → ArgSpec n) : ArgSpec (n + 1)
  | mutRefFrom (idx : Nat) (k : UInt32 → UInt32 → ArgSpec n) : ArgSpec (n + 1)
```

Two recursive functions—`ArgSpec.toPrePostAux` (which interprets an `ArgSpec`
against concrete `MirState` locals and `Memory.alloc` frames to produce a
`Trusted.FnSig`) and `ArgSpec.symPre` / `ArgSpec.symPost` (which interpret the
same `ArgSpec` over pure symbolic `SymArg` lists)—enable a single generic
35-line soundness theorem `funcSpec_verified`
(`support/ProbeGeneralSpecAndLithium.lean`, lines 601–650):

```lean
theorem funcSpec_verified (body : Body) (fuel : Nat) (spec : ArgSpec n)
    (heval : ∀ args, spec.symPre args →
      ∃ ret outArgs, evalSymWith fuel body args = some (ret, outArgs) ∧
        spec.symPost args ret outArgs) :
    FuncSpec body (spec.toFnSig n)
```

Proving `funcSpec_verified` once in `Theory/` eliminates all 15 bespoke
`translate_*_spec` unpacking proofs in `FunctionalTranslation.lean`.

#### 3.3 Lithium-Style `ShelvedVC`, Source-Span Attribution (`R-UX-01`, `R-UX-02`), and Uniform `anneal_vcgen`

To provide RefinedRust/Lithium-style diagnostic localization when a side
condition fails (`R-UX-01`, `R-UX-02`) while keeping generated proof scripts
uniform (`by anneal_vcgen`), `support/ProbeGeneralSpecAndLithium.lean` (lines
244–253, 307–371, 659–684) introduces:

1. **Source-Annotated Shelved Verification Conditions (`ShelvedVC`):** ```lean
   structure SourceSpan where file : String line : Nat col  : Nat snip : String
   deriving DecidableEq, Repr

def ShelvedVC (span : SourceSpan) (branchTrace : List String) (label : String)
(P : Prop) : Prop := P ``` Because `ShelvedVC` is reducible to `P` only when
explicitly unfolded via `unshelve_vcs`, if `anneal_sidecond_solver` fails to
close an obligation, the user's Lean InfoView displays the exact Rust source
file, line, column, source snippet, branch trace (`["if x < y = true"]`), and
obligation kind (`"assertion"`, `"overflow check"`, or `"postcondition"`).
2. **Trace-Collecting Symbolic Verification Condition Generator (`vcgenSym`):**
   `vcgenSym` traverses the MIR CFG symbolically, recording the taken and
   negated branch conditions at every `switchInt` terminator into `branchTrace`
   and wrapping every `Terminator.assert` and terminal postcondition check
   inside `ShelvedVC term.span branchTrace label P`.
3. **Uniform Single-Line Proof Script (`anneal_vcgen`):** ```lean macro
   "anneal_vcgen" : tactic => `(tactic| ( apply funcSpec_verified (fuel := 16);
   intro args hpre; Anneal.Probe.Theory.unpack_sym_args args hpre; refine ⟨_, _,
   rfl, ?_⟩; Anneal.Probe.Theory.unshelve_vcs;
   Anneal.Probe.Theory.anneal_sidecond_solver)) ``` Using `by anneal_vcgen`,
   `support/ProbeGeneralSpecAndLithium.lean` (lines 690–782) verifies
   `maxAssign_verified` (`&mut u32, u32`), `clampAssign_verified` (`&mut u32,
   u32, u32` with preconditions `lo ≤ hi`), and `chooseMut_verified` (`bool, &'a
   mut u32, &'a mut u32 -> &'a mut u32` with lifetime-linked return provenance
   via `RetPlaceGives`) using the exact same one-line proof script.

---

### 4. Trace-Preserving Functional Translation (`TrackedFuncLang`)

`Basis: primary source inspection of theory/Anneal/FunctionalTranslation.lean at e75556f57d76d09fd5fc84fc4bfca6a89c3b85e0 / 42f4571d761b46c7142815f38b69c3781b3555e3 and Lean 4.34.1 kernel verification of support/ProbeTrackedFuncLangAndLoops.lean (sha256 98e7321e53c2b32644b8e62c10275b26234f1c7c4d587f381374995a74b16a66).`

#### 4.1 Why `FuncLang` Erases Traces in Baseline Anneal

In Anneal's baseline `theory/Anneal/FunctionalTranslation.lean` (lines
3768–3791), `FuncLang` defines a single-step transition from `.running (some
(ret, outArgs))` to `.done ret outArgs` that emits the empty observation list
`[] : List StepObs`, while every intermediate MIR basic-block transition maps to
the stutter relation ($\pi(s) = \pi(s')$) in `Refinement.ForwardSim`:

$$\text{MirLang.step}(c) = \text{StepResult.step}([{\tt StepObs.step}], c') \quad\leadsto\quad \pi(c) = \pi(c') \text{ with } \tau_{\text{abs}} = [\,].$$

Because `ForwardSim` in `Trusted/Refinement.lean` ignores `StepObs` on stutter
steps, `FuncLang` loses all information about how many basic-block steps a
function executed, whether two executions took the same number of steps, and
whether control-flow branching depended on secret inputs.

#### 4.2 `evalSymWithTracked`, `TrackedFuncLang`, and Lockstep Forward Simulation

In `support/ProbeTrackedFuncLangAndLoops.lean` (lines 714–962), we eliminate
stutter-step trace erasure by equipping the symbolic evaluator with an explicit
observation-trace accumulator `List StepObs`:

```lean
def evalSymWithTracked (callEnv : CallEnv) :
    Nat → Body → List SymArg → Option (Value × List SymArg × List StepObs)
  | fuel, body, args => do
    let initEnv ← initSymEnv body.argCount args
    let (ret, finalEnv, trace) ← evalSymBlocksTracked callEnv fuel body 0 initEnv []
    let outArgs ← extractSymArgs body.argCount args finalEnv
    some (ret, outArgs, trace)
```

At every basic-block dispatch (`return_`, `goto`, `switchInt`, `assert`, and
resolved `call`), `evalSymBlocksTracked` appends `[StepObs.step]` to the
accumulated trace (`trace ++ [StepObs.step]`). We then define `TrackedFuncState`
and `TrackedFuncLang` (`support/ProbeTrackedFuncLangAndLoops.lean`, lines
771–798) as a trace-emitting operational state machine:

```lean
inductive TrackedFuncState where
  | running (res : Option (Value × List SymArg × List StepObs))
  | done (ret : Value) (outArgs : List SymArg)
  | ub
  deriving DecidableEq

def TrackedFuncLang : Language where
  Config := TrackedFuncState
  Obs := StepObs
  step s :=
    match s with
    | .running (some (ret, outArgs, obs :: restTrace)) =>
      .step [obs] (.running (some (ret, outArgs, restTrace)))
    | .running (some (ret, outArgs, [])) =>
      .terminal
    | .running none => .ub
    | .done _ _ => .terminal
    | .ub => .ub
```

Because `evalSymBlocksTracked` prepends one `StepObs.step` per basic block, its
projection $\pi_{\text{tracked}}(\text{cfg})$ steps in **exact 1-to-1 lockstep**
with `MirLang.step` (`StepResult.step [StepObs.step] (.running (. some nextCfg,
s'' .))`) across all 5 MIR terminators (`return_`, `goto`, `switchInt`,
`assert`, and `call`):

$$\text{If } \pi_{\text{tracked}}(c) = {\tt .running}\;({\tt some}\;(r, \mathit{out}, {\tt StepObs.step} :: \tau)), \text{ then } {\tt TrackedFuncLang.step}(\pi_{\text{tracked}}(c)) = {\tt .step}\;[{\tt StepObs.step}]\;(\pi_{\text{tracked}}(c')).$$

This yields four machine-checked theorems in
`support/ProbeTrackedFuncLangAndLoops.lean` (lines 805–1215), each depending
only on `[propext, Quot.sound]`:

1. **Monotonicity with Exact Trace Preservation (`monotone_π_tracked`, lines
   805–908):** If symbolic evaluation succeeds at fuel $f$ with `(ret, outArgs,
   trace)`, it succeeds at every fuel $f' \ge f$ with the identical `(ret,
   outArgs, trace)`.
2. **Trace-Preserving Forward Simulation (`evalSymWithTracked_sound`, lines
   1029–1170):** ```lean theorem evalSymWithTracked_sound (callEnv : CallEnv)
   (hcallEnv : CallEnvSoundTracked callEnv) : Refinement.ForwardSim MirLang
   TrackedFuncLang (π_tracked callEnv) ```
3. **Exact Operational Trace Length
   (`trackedFuncLang_exact_trace_length_at_steps`, lines 1179–1197):** When
   `evalSymWithTracked` returns `(ret, outArgs, trace)`, executing the
   `TrackedFuncLang` configuration for `trace.length` steps reaches `.running
   (some (ret, outArgs, []))` and emits the exact observation list `trace`.
4. **End-to-End `Language.SpecOn` Adequacy (`trackedFuncLang_adequacy_specOn`,
   lines 1201–1215):** Combines `Refinement.forwardSim_specOn` with
   `evalSymWithTracked_sound` to lift any trace or postcondition property proved
   on `TrackedFuncLang` directly to `Language.SpecOn MirLang` without modifying
   a single line of `Trusted/Refinement.lean`.

---

### 5. Compositional Loop Invariants, Diamond CFG Join Cutpoints, and Constant-Time 2-Safety

`Basis: primary source inspection of Aeneas/Std/WP.lean (lines 494–528), RefinedRust typing/program_rules.v (lines 5056–5100), and Lean 4.34.1 kernel verification of support/ProbeTrackedFuncLangAndLoops.lean (sha256 98e7321e53c2b32644b8e62c10275b26234f1c7c4d587f381374995a74b16a66).`

#### 5.1 Compositional Loop Invariants and Well-Founded Ranking Measures (`loop_spec_decr_nat` and `tracked_loop_spec_decr_nat`)

In `Aeneas/Std/WP.lean` (lines 511–528), Aeneas verifies `while` and `loop`
definitions via `loop.spec_decr_nat`, which requires a loop invariant `inv : α →
Prop`, a postcondition `post : β → Prop`, and a natural-number ranking measure
`measure : α → Nat` that strictly decreases across every `.Continue s'` step.

In Anneal's MIR symbolic evaluator, a loop header at basic block `headerIdx`
iterates through `evalSymBlocks` (or `evalSymBlocksTracked`). Without a loop
invariant rule, verifying a loop requires fixing a concrete constant fuel bound
$F$ and unrolling the loop $F$ times, which fails whenever the iteration count
depends on a symbolic runtime parameter $n$ (or forces an artificial
fuel-dependent precondition $n \le F_{\text{unroll}}$).

In `support/ProbeTrackedFuncLangAndLoops.lean` (lines 1236–1370), we prove both
the untrailed compositional loop rule (`loop_spec_decr_nat`) and the
trace-preserving compositional loop rule (`tracked_loop_spec_decr_nat`) by
strong induction (`Nat.strong_induction_on`) on `measure env`:

```lean
theorem tracked_loop_spec_decr_nat
    (callEnv : CallEnv) (body : Body) (headerIdx : BasicBlockIdx)
    (inv : SymEnv → Prop)
    (post : Value → SymEnv → List StepObs → Prop)
    (measure : SymEnv → Nat)
    (stepFuel : Nat)
    (hstep : ∀ env : SymEnv, inv env →
      (∃ nextEnv iterTrace,
        iterTrace.length ≥ 1 ∧
        measure nextEnv < measure env ∧
        inv nextEnv ∧
        (∀ fuel restRet restEnv totalTrace,
          evalSymBlocksTracked callEnv fuel body headerIdx nextEnv iterTrace =
            some (restRet, restEnv, totalTrace) →
          evalSymBlocksTracked callEnv (stepFuel + fuel) body headerIdx env [] =
            some (restRet, restEnv, totalTrace)) ∧
        (∀ ret finalEnv tailTrace,
          post ret finalEnv tailTrace →
          post ret finalEnv (iterTrace ++ tailTrace))) ∨
      (∃ ret finalEnv exitTrace,
        evalSymBlocksTracked callEnv stepFuel body headerIdx env [] =
          some (ret, finalEnv, exitTrace) ∧
        post ret finalEnv exitTrace)) :
    ∀ (env : SymEnv), inv env →
      ∃ fuel ret finalEnv trace,
        evalSymBlocksTracked callEnv fuel body headerIdx env [] =
          some (ret, finalEnv, trace) ∧
        post ret finalEnv trace
```

Notice that `tracked_loop_spec_decr_nat` existentially quantifies the symbolic
evaluation fuel `∃ fuel` inside the conclusion! Because `MirLang` itself is
unbounded (it does not take a fuel parameter) and `evalSymWithTracked_sound`
holds for any witness `fuel`, existentially quantifying `fuel := stepFuel *
(measure initEnv + 1)` inside the proof means the user's `Language.SpecOn
MirLang` contract is **100% fuel-free**.

To demonstrate this end-to-end on a cyclic MIR CFG,
`support/ProbeTrackedFuncLangAndLoops.lean` (lines 1378–1694) encodes
`sumToNBody`—a 4-block cyclic MIR program with back-edge `bb2 → bb1` computing
$\sum_{i=0}^{n-1} i$ while $i < n$—and proves:

1. `sumToN_verified_via_ranking_measure` (lines 1574–1635): Verifies the loop
   using invariant $2 \cdot \mathit{acc} = i \cdot (i - 1) \wedge i \le n \wedge
   n \le 1000$ and ranking measure $m(\sigma) = n - i$, proving that the
   returned value satisfies $2 \cdot \mathit{ret} = n \cdot (n - 1)$ and the
   emitted trace has exact length $\text{trace.length} = n + 2$.
2. `sumToN_satisfies_fuelFree_specOn` (lines 1656–1694): Bridges the
   ranking-measure proof through `evalSymWithTracked_sound` to establish a
   fuel-free `Language.SpecOn MirLang` theorem over arbitrary symbolic $n \le
   1000$.

#### 5.2 Diamond CFG Join Cutpoints and `JCACHED` Subsumption ($2^{k+1} - 2 \to 2k$)

When a MIR function contains $k$ sequential `if`/`else` diamonds (`bb_0 → (bb_1,
bb_2) → bb_3 → (bb_4, bb_5) → bb_6 …`), naive tree-unrolling symbolic execution
duplicates the continuation at every join block `bb_3`, `bb_6`, …, producing
$2^{k+1} - 2$ symbolic execution states and duplicating identical pure side
conditions across all $2^k$ paths.

In `support/ProbeTrackedFuncLangAndLoops.lean` (lines 1712–1940), we mechanize
RefinedRust's two join-sharing mechanisms:

1. **Compositional Join-Block Cutpoint (`diamond_join_cutpoint`, lines
   1719–1748):** Instead of re-evaluating the continuation from `joinIdx`
   separately in each branch of a diamond, `diamond_join_cutpoint` factors the
   proof through an intermediate join invariant `joinInv : SymEnv → List StepObs
   → Prop`:
   - Both branches of the ` i`-th diamond prove only that their single-step
     transition establishes `joinInv midEnv trace1` ($2$ obligations per
     diamond); and
   - A single continuation proof from `joinIdx` assumes `joinInv midEnv trace1`
     and establishes the final postcondition. Across $k$ sequential diamonds,
     this reduces the number of symbolic branch verification obligations from
     $2^{k+1} - 2$ to $2k$.
2. **Lithium-Style Side-Condition Caching (`JCACHED`, lines 1753–1785):**
   Defining `def JCACHED (P : Prop) : Prop := P` and the `cache_sidecond` /
   `solve_with_jcache` tactics records already-proved pure obligations in the
   local context and discharges duplicate downstream obligations in $O(1)$ by
   exact hypothesis lookup (`assumption`) without re-invoking `omega`. Theorem
   `twoDiamondBody_verified_linear` (lines 1895–1940) verifies a 7-block,
   2-diamond MIR function (`twoDiamondBody`) in $2k = 4$ branch steps using
   `diamond_join_cutpoint` and `JCACHED`.

#### 5.3 Constant-Time 2-Safety Bridge (`BranchAligned` and `trackedFuncLang_implies_constantTime2Safety`)

Cryptographic and security-critical Rust code requires **constant-time
execution**: two runs of a function that agree on public inputs (`pubEq s₁ s₂`)
but differ arbitrarily on secret inputs must produce identical step-observation
traces ($\tau_1 = \tau_2$) and identical terminal step counts. Because baseline
`FuncLang` erases intermediate `StepObs` events, it cannot express or prove
constant-time 2-safety.

In `support/ProbeTrackedFuncLangAndLoops.lean` (lines 1955–2194), we define a
relational 2-safety specification `ConstantTime2Safety` over concrete `MirLang`
configurations and a symbolic alignment predicate `BranchAligned`:

```lean
def ConstantTime2Safety (body : Body)
    (pubEq : MirState → MirState → Prop)
    (pre : MirState → Prop) : Prop :=
  ∀ s1 s2 : MirState,
    pre s1 → pre s2 → pubEq s1 s2 →
    ∃ (N : Nat) (trace : List StepObs) (s1' s2' : MirState),
      StepResult.runSteps MirLang.step N ⟨body, . some ⟨0, 0⟩, s1 .⟩ =
        .step trace ⟨body, . none, s1' .⟩ ∧
      StepResult.runSteps MirLang.step N ⟨body, . some ⟨0, 0⟩, s2 .⟩ =
        .step trace ⟨body, . none, s2' .⟩
```

`BranchAligned callEnv fuel body args1 args2` (lines 1986–2030) holds when two
symbolic argument vectors `args1` and `args2` take identical control-flow edges
at every `switchInt`, `assert`, `goto`, `return_`, and `call` terminator—even
when their scalar data values (`Rvalue.binaryOp .bitXor`, `.add`, `.sub`) differ
on secret inputs. We prove three theorems connecting `BranchAligned` to
`ConstantTime2Safety`:

1. `evalSymTracked_trace_eq_of_branchAligned` (lines 2035–2095): If
   `BranchAligned callEnv fuel body args1 args2` holds, then
   `evalSymWithTracked` succeeds on both `args1` and `args2` with **identical
   observation traces** ($\tau_1 = \tau_2$).
2. `trackedFuncLang_implies_constantTime2Safety` (lines 2101–2145): Lifts
   `BranchAligned` through `evalSymWithTracked_sound` to prove
   `ConstantTime2Safety` on concrete `MirLang` executions.
3. `ctPublicModeXor_is_constant_time` (lines 2165–2194): Verifies that a
   branching MIR function (`ctPublicModeXorBody`) that branches on a public
   `mode : u32` local (`switchInt`) and performs bitwise XOR (`^`) and modular
   addition (`+`) on a secret `key : u32` local satisfies `ConstantTime2Safety`
   with identical 3-step observation traces `[.step, .step, .step]` across all
   secret keys `secret1, secret2 : UInt32`.

## Boundaries

The findings and Lean 4 mechanizations in this report are subject to the
following scope boundaries:

- **Safe and Acyclic-Borrow Subset in `ArgSpec`:** The inductive `ArgSpec`
  telescope in `support/ProbeGeneralSpecAndLithium.lean` covers arbitrary
  combinations of scalar values (`u32`, `bool`), disjoint mutable references
  (`&mut u32`), and lifetime-linked reborrows/returned mutable references
  (`mutRefFrom` / `RetPlaceGives`). Extending `ArgSpec` to nested references to
  references (`&mut &mut T`), raw pointers (`*const T`, `*mut T`) with unsafe
  aliasing, or dynamically sized slices (`&mut [T]`) requires pairing `ArgSpec`
  with explicit region/allocation separation predicates in
  `Trusted/Memory.lean`.
- **Single-Entry Reducible Loops in `tracked_loop_spec_decr_nat`:** The
  compositional loop-invariant rules (`loop_spec_decr_nat` and
  `tracked_loop_spec_decr_nat` in `support/ProbeTrackedFuncLangAndLoops.lean`)
  induction over a single loop header `headerIdx : BasicBlockIdx` with a
  well-founded `Nat` ranking measure. Irreducible multi-entry control-flow
  graphs (created by unstructured `goto`s outside standard Rust `loop`/`while`
  surface syntax) require either a mutual cutpoint map over all cycle headers or
  lexically ordered lexicographic measures (`Prod.Lex`).
- **Instruction-Granular vs. Basic-Block-Granular Leakage:** `TrackedFuncLang`
  preserves `MirLang`'s observation model (`[StepObs.step]` per basic-block
  step, capturing control-flow path and loop-iteration timing). Detecting
  intra-block microarchitectural side channels—such as secret-dependent memory
  addresses in array indexing (`arr[secret]`) or variable-latency hardware
  division (`secret / divisor`)—requires enriching `StepObs` in
  `Trusted/StepResult.lean` with address and operand leakage tags (analogous to
  Jasmin/EasyCrypt and `riscv-coq`'s `LeakageOfInstr`).

## Evidence

### 1. Mechanized Lean 4.34.1 Probes in `support/`

Both standalone Lean 4 probes in `support/` compile cleanly with zero `sorry`
and zero non-standard axioms under Lean 4.34.1 (`lean -j1 -M1024`):

| Support File | SHA-256 Digest | Lines | `sorry` Count | Kernel Axioms |
| :--- | :--- | ---: | ---: | :--- |
| `support/ProbeGeneralSpecAndLithium.lean` | `65f8af557997769bd43b4ce6eac36b79e1555bd222b75f31a4b439f08016895a` | 784 | 0 | `[propext, Classical.choice, Quot.sound]` |
| `support/ProbeTrackedFuncLangAndLoops.lean` | `98e7321e53c2b32644b8e62c10275b26234f1c7c4d587f381374995a74b16a66` | 2,199 | 0 | `[propext, Classical.choice, Quot.sound]` |

#### 1.1 Key Declarations and Theorems in `support/ProbeGeneralSpecAndLithium.lean`

| Symbol | Kind | Lines | Role |
| :--- | :--- | ---: | :--- |
| `Anneal.Probe.Trusted.FnSig` | `structure` | 204–211 | Generic TCB function contract (`pre : MirState → Prop`, `post : MirState → MirState → Prop`) replacing all 15 `Ensures*` definitions. |
| `Anneal.Probe.Trusted.FuncSpec` | `def` | 218–223 | Generic `Language.SpecOn MirLang` wrapper parameterized by `Body` and `FnSig`. |
| `Anneal.Probe.Theory.ShelvedVC` | `def` | 249–253 | Lithium-style shelved verification condition carrying `SourceSpan`, `branchTrace : List String`, and `label : String`. |
| `Anneal.Probe.Theory.vcgenSym` | `def` | 328–371 | Symbolic VC generator collecting branch traces and wrapping assertions and postconditions in `ShelvedVC`. |
| `Anneal.Probe.Theory.evalSymWith_sound` | `theorem` | 436–494 | Forward simulation `ForwardSim MirLang FuncLang` for symbolic evaluation. |
| `Anneal.Probe.Theory.ArgSpec` | `inductive` | 502–514 | Telescopic argument and mutable-reference specification (`nil`, `val`, `boolVal`, `mutRef`, `mutRefFrom`). |
| `Anneal.Probe.Theory.funcSpec_verified` | `theorem` | 601–650 | Generic soundness theorem proving `FuncSpec body (spec.toFnSig n)` from symbolic evaluation of any `ArgSpec n`. |
| `Anneal.Probe.Theory.anneal_vcgen` | `macro` | 674–684 | Uniform single-line tactic discharging `FuncSpec` goals via `funcSpec_verified`, `unpack_sym_args`, `unshelve_vcs`, and `anneal_sidecond_solver`. |
| `Anneal.Probe.Theory.maxAssign_verified` | `theorem` | 709–713 | Verifies `maxAssignBody` (`&mut u32, u32`) via `by anneal_vcgen`. |
| `Anneal.Probe.Theory.clampAssign_verified` | `theorem` | 739–745 | Verifies `clampAssignBody` (`&mut u32, u32, u32`) via `by anneal_vcgen`. |
| `Anneal.Probe.Theory.chooseMut_verified` | `theorem` | 771–777 | Verifies `chooseMutBody` (`bool, &'a mut u32, &'a mut u32 -> &'a mut u32`) with `RetPlaceGives` via `by anneal_vcgen`. |
| `Anneal.Probe.Theory.all_exemplars_verified` | `theorem` | 779–782 | Conjunction packaging `maxAssign_verified`, `clampAssign_verified`, and `chooseMut_verified`. |

#### 1.2 Key Declarations and Theorems in `support/ProbeTrackedFuncLangAndLoops.lean`

| Symbol | Kind | Lines | Kernel Axioms | Role |
| :--- | :--- | ---: | :--- | :--- |
| `Anneal.R2Probe.Theory.evalSymWithTracked` | `def` | 757–763 | — | Trace-accumulating symbolic MIR evaluator emitting `[StepObs.step]` per basic block. |
| `Anneal.R2Probe.Theory.TrackedFuncLang` | `def` | 780–798 | — | Abstract `Language` emitting accumulated `List StepObs` one step at a time. |
| `Anneal.R2Probe.Theory.monotone_π_tracked` | `theorem` | 900–908 | `[propext, Quot.sound]` | Fuel monotonicity preserving exact `(ret, outArgs, trace)` triples. |
| `Anneal.R2Probe.Theory.evalSymWithTracked_sound` | `theorem` | 1029–1170 | `[propext, Quot.sound]` | Lockstep `ForwardSim MirLang TrackedFuncLang (π_tracked callEnv)` across all 5 terminators (`return_`, `goto`, `switchInt`, `assert`, `call`). |
| `Anneal.R2Probe.Theory.trackedFuncLang_exact_trace_length_at_steps` | `theorem` | 1179–1197 | `[propext, Quot.sound]` | Proves `StepResult.runSteps TrackedFuncLang.step trace.length` emits `trace` and reaches `.running (some (ret, outArgs, []))`. |
| `Anneal.R2Probe.Theory.trackedFuncLang_adequacy_specOn` | `theorem` | 1201–1215 | `[propext, Quot.sound]` | Lifts `TrackedFuncLang` specifications to `Language.SpecOn MirLang` via `Refinement.forwardSim_specOn`. |
| `Anneal.R2Probe.Theory.loop_spec_decr_nat` | `theorem` | 1255–1294 | `[propext, Classical.choice, Quot.sound]` | Compositional loop-invariant rule over `evalSymBlocks` via well-founded induction on `measure : SymEnv → Nat`. |
| `Anneal.R2Probe.Theory.tracked_loop_spec_decr_nat` | `theorem` | 1306–1370 | `[propext, Quot.sound]` | Trace-preserving compositional loop-invariant rule over `evalSymBlocksTracked` with existential fuel witness. |
| `Anneal.R2Probe.Theory.sumToN_verified_via_ranking_measure` | `theorem` | 1574–1635 | `[propext, Classical.choice, Quot.sound]` | Verifies cyclic `sumToNBody` ($2 \cdot \mathit{ret} = n(n-1)$ and $\text{trace.length} = n + 2$) via `tracked_loop_spec_decr_nat`. |
| `Anneal.R2Probe.Theory.sumToN_satisfies_fuelFree_specOn` | `theorem` | 1656–1694 | `[propext, Classical.choice, Quot.sound]` | Fuel-free `Language.SpecOn MirLang` theorem for `sumToNBody` over arbitrary $n \le 1000$. |
| `Anneal.R2Probe.Theory.diamond_join_cutpoint` | `theorem` | 1719–1748 | `[propext]` | Compositional CFG join-point cutpoint theorem factoring diamond branches through `joinInv`. |
| `Anneal.R2Probe.Theory.twoDiamondBody_verified_linear` | `theorem` | 1895–1940 | `[propext, Classical.choice, Quot.sound]` | Verifies 2-diamond CFG in $2k = 4$ linear branch obligations using `diamond_join_cutpoint` and `JCACHED`. |
| `Anneal.R2Probe.Theory.evalSymTracked_trace_eq_of_branchAligned` | `theorem` | 2080–2095 | `[propext]` | Proves that `BranchAligned` symbolic executions produce identical `List StepObs` traces ($\tau_1 = \tau_2$). |
| `Anneal.R2Probe.Theory.trackedFuncLang_implies_constantTime2Safety` | `theorem` | 2101–2145 | `[propext, Quot.sound]` | Relational 2-safety bridge proving `ConstantTime2Safety` on `MirLang` from `BranchAligned`. |
| `Anneal.R2Probe.Theory.ctPublicModeXor_is_constant_time` | `theorem` | 2165–2194 | `[propext, Classical.choice, Quot.sound]` | Proves `ConstantTime2Safety` for `ctPublicModeXorBody` across arbitrary secret keys `secret1, secret2 : UInt32`. |

### 2. Primary Repository Source Files Indexed in `support/source-manifest.json`

All repository revisions, file paths, Git blob SHA-1 hashes, and SHA-256 digests
are recorded in `support/source-manifest.json`. The primary inspected files are
summarized below:

| Repository (`Revision`) | File Path | Lines | SHA-256 Digest |
| :--- | :--- | ---: | :--- |
| `AeneasVerif/aeneas` (`70683bd4ab876179a23e5f994d02947b3e5c4f0d`) | `backends/lean/Aeneas/Std/Primitives.lean` | 504 | `ea312dfb113a04126f7d975b934266fc420bd3209a0b14466f6ec76089d93bbb` |
| `AeneasVerif/aeneas` (`70683bd4ab876179a23e5f994d02947b3e5c4f0d`) | `backends/lean/Aeneas/Std/WP.lean` | 807 | `961c52bd79e30b8e8300dde4cbfcd21bdcbf5af039ccab6886d051b29f21af7a` |
| `AeneasVerif/aeneas` (`70683bd4ab876179a23e5f994d02947b3e5c4f0d`) | `backends/lean/Aeneas/Data/Coinductive/ITreeWP/Taxonomy.lean` | 39 | `d570189bcd81ed6e0cc99444252696a09d6a8c341c58a5d4697e39f236998c92` |
| `AeneasVerif/aeneas` (`70683bd4ab876179a23e5f994d02947b3e5c4f0d`) | `backends/lean/Aeneas/Std/Scalar/Core.lean` | 1,295 | `b0be731c1120576222767f7a55b98e45fc8fb90bb45e20e1d3b1e4b0b8d63a70` |
| `AeneasVerif/aeneas` (`70683bd4ab876179a23e5f994d02947b3e5c4f0d`) | `backends/lean/Aeneas/Tactic/Step/Init.lean` | 1,033 | `5398851d97e08e78c467d6501cef098f14441a080e25ed81acc9e3d7668e22aa` |
| `AeneasVerif/aeneas` (`70683bd4ab876179a23e5f994d02947b3e5c4f0d`) | `backends/lean/Aeneas/Tactic/Step/Step.lean` | 2,107 | `13237a6998959d5132016b66e05701e352fa735c3986664f5adcc567b8a5e887` |
| `AeneasVerif/aeneas` (`70683bd4ab876179a23e5f994d02947b3e5c4f0d`) | `backends/lean/Aeneas/Tactic/Step/StepStar.lean` | 1,367 | `8b696721f6270489c32d174ea4f181df1c6cc48cd6f8b00b0c2e26c6587365b0` |
| `AeneasVerif/aeneas` (`70683bd4ab876179a23e5f994d02947b3e5c4f0d`) | `backends/lean/Aeneas/Tactic/Solver/ScalarTac.lean` | 5 | `526d5bdd54b7a44c9eb1d5044330278520b1ade02245288629130537c71fe853` |
| `AeneasVerif/aeneas` (`70683bd4ab876179a23e5f994d02947b3e5c4f0d`) | `backends/lean/Aeneas/Tactic/Solver/BvTac/BvTac.lean` | 267 | `821103978ffa1e4aca5bf7f48fb93135d14eb4454597a3886fc8aa27a7b679e0` |
| `AeneasVerif/aeneas` (`8ab2e7e4e47fe73fd5b2a0c061293e00b30013fe`) | `backends/lean/Aeneas/Std/Primitives.lean` | 260 | `2d635b133be0494284c44f19cb142d0b7944944ae367fb60d4e05a6a67accc53` |
| `AeneasVerif/aeneas` (`8ab2e7e4e47fe73fd5b2a0c061293e00b30013fe`) | `backends/lean/Aeneas/Std/WP.lean` | 529 | `650145cd1d67faaacd633f3cd65a5bb81e818d6d1d71c138f47fe1082a9bc8b3` |
| `AeneasVerif/aeneas` (`8ab2e7e4e47fe73fd5b2a0c061293e00b30013fe`) | `backends/lean/Aeneas/Std/Scalar/Core.lean` | 1,216 | `a75f6ce2f21cabb261dd7b9a8c75bbd3490e3ef6f860d4b32ef9252675c00f42` |
| `AeneasVerif/aeneas` (`8ab2e7e4e47fe73fd5b2a0c061293e00b30013fe`) | `backends/lean/Aeneas/Tactic/Step/Init.lean` | 979 | `864d72434869de4c2780a0f3d4d1d0b9272f1072ef9d489f58fdae3455c65754` |
| `AeneasVerif/aeneas` (`8ab2e7e4e47fe73fd5b2a0c061293e00b30013fe`) | `backends/lean/Aeneas/Tactic/Step/Step.lean` | 1,861 | `f888210e02f89edf15ae7754da1f12fff3146de64367fb65303dd8b1d2538661` |
| `AeneasVerif/aeneas` (`8ab2e7e4e47fe73fd5b2a0c061293e00b30013fe`) | `backends/lean/Aeneas/Tactic/Step/StepStar.lean` | 1,368 | `ee39c653daa656868a962caae80fa0fbc21bb8949b93231cfde178aae8c124d3` |
| `AeneasVerif/aeneas` (`8ab2e7e4e47fe73fd5b2a0c061293e00b30013fe`) | `backends/lean/Aeneas/Tactic/Solver/ScalarTac.lean` | 4 | `601ef1fca04a744f8e60d742091e815afc194e3cbbb293336e0af6c09c9bb799` |
| `AeneasVerif/aeneas` (`8ab2e7e4e47fe73fd5b2a0c061293e00b30013fe`) | `backends/lean/Aeneas/Tactic/Solver/BvTac/BvTac.lean` | 261 | `efdf8ce55fb12519fbf2df7b2a4d8bd493f5982bf28d26f0c23176932de06ab7` |
| `cryspen/hax` (`1ec88cdb2c8e546845e64eb2cd2321b4f58069c4`) | `hax-lib/proof-libs/lean/CoreModels/RustPrimitives/Types.lean` | 13 | `53c6ebc17c5a3778c93ca659a458ab50923ddadc3bb9845fea30f2aa4c731b62` |
| `cryspen/hax` (`1ec88cdb2c8e546845e64eb2cd2321b4f58069c4`) | `hax-lib/proof-libs/lean/CoreModels/Spec/RustPrimitives/Arithmetic.lean` | 59 | `e4b8eb1e01c3d72176708328cec3171d5dca672d71d205bd6bee6034438f3298` |
| `cryspen/hax` (`1ec88cdb2c8e546845e64eb2cd2321b4f58069c4`) | `hax-lib/proof-libs/lean/Hax/Tactic/HaxMvcgen.lean` | 68 | `c8f67a5852f533533379091dc7110e9568e7bc7cc2b8e2f3a77d3524cb1ea3e5` |
| `lgaeher/refinedrust-dev` (`8a07f4f2e6a499625b4b25e94f0b2ab78592cb52`) | `rr_frontend/radium/src/code.rs` | 2,226 | `549c2c49184d07ed5ed92450b66a22357588192cad15d5f268c00a4d72c4cc17` |
| `lgaeher/refinedrust-dev` (`8a07f4f2e6a499625b4b25e94f0b2ab78592cb52`) | `theories/refinedrust/lithium/definitions.v` | 144 | `2611e19aa233e1a090483f5e1902b0a4a42fd21fe1f37296a47b83d0f4df6886` |
| `lgaeher/refinedrust-dev` (`8a07f4f2e6a499625b4b25e94f0b2ab78592cb52`) | `theories/refinedrust/lithium/syntax.v` | 517 | `78e30c4b249b33f2a1175f05a68bae8e89398f5f2e7c79fc67d0b20aa12b44d2` |
| `lgaeher/refinedrust-dev` (`8a07f4f2e6a499625b4b25e94f0b2ab78592cb52`) | `theories/refinedrust/lithium/interpreter.v` | 1,037 | `8b087ff28d73c5b77c21cef1c12222bd4671fee0ed1e7864c391efbb4e5eaa6f` |
| `lgaeher/refinedrust-dev` (`8a07f4f2e6a499625b4b25e94f0b2ab78592cb52`) | `theories/refinedrust/lithium/proof_state.v` | 374 | `e78e54d7f47ac78de592b49798fcaf1806d39bb313811d8e765312135f6fa78e` |
| `lgaeher/refinedrust-dev` (`8a07f4f2e6a499625b4b25e94f0b2ab78592cb52`) | `theories/refinedrust/rust_typing/automation/proof_state.v` | 538 | `5ac0ae5d980b3075f293aa1ca08c763dbb67af0b911584a239015a9cc2ada05f` |
| `lgaeher/refinedrust-dev` (`8a07f4f2e6a499625b4b25e94f0b2ab78592cb52`) | `theories/refinedrust/rust_typing/typing/automation.v` | 2,327 | `beeb059b7cb7e19913fd13006177a553a89339600c45bf84311da8146bd3d19d` |
| `lgaeher/refinedrust-dev` (`8a07f4f2e6a499625b4b25e94f0b2ab78592cb52`) | `theories/refinedrust/rust_typing/base/programs.v` | 4,206 | `ec059962a64aff5e6caf475d6a78cebfbf5f2a476cef52b19ca014cc3feadc89` |
| `lgaeher/refinedrust-dev` (`8a07f4f2e6a499625b4b25e94f0b2ab78592cb52`) | `theories/refinedrust/rust_typing/primitive/functions.v` | 1,735 | `4d4b8b472a56344b2f82f40c25c2ae53e41b0c3e5d7ceb322134183106a0c2dd` |
| `lgaeher/refinedrust-dev` (`8a07f4f2e6a499625b4b25e94f0b2ab78592cb52`) | `theories/refinedrust/rust_typing/typing/program_rules.v` | 6,348 | `2912aa36c4bf4beb4bade6c025077cf0bff25e72fb3ce875882251227e6cc461` |
| `iris/refinedc` (`d057583986651a28047164581f05fbee3a83ed9d`) | `theories/lithium/definitions.v` | 350 | `906be13def247a9ae3e0532807931d2fd4aebf95d560e47692dbd73f5c6a0790` |
| `iris/refinedc` (`d057583986651a28047164581f05fbee3a83ed9d`) | `theories/lithium/syntax.v` | 468 | `239c5c1642a1007b4162ddccef7bcb5845ee931323cfbbab1d31dc6c2f6d4c0a` |
| `iris/refinedc` (`d057583986651a28047164581f05fbee3a83ed9d`) | `theories/lithium/interpreter.v` | 1,201 | `a2319bc9c6bce6e2bfd18663b54e13147c0f61d0424443eeaba64a2b7d783588` |
| `iris/refinedc` (`d057583986651a28047164581f05fbee3a83ed9d`) | `theories/lithium/proof_state.v` | 231 | `da016f282bd0069839d9f5310187f10b75f3bb3b3fb2dacbe46df0cad35c09cb` |
| `joshlf/anneal` (`42f4571d761b46c7142815f38b69c3781b3555e3`) | `trusted/lean/Trusted/Refinement.lean` | 532 | `520d15e91568c05c7d00173e710c0f71e2f9cc2d57a74b74bc4ff47c1501cd5a` |
| `joshlf/anneal` (`42f4571d761b46c7142815f38b69c3781b3555e3`) | `trusted/lean/Trusted/StepResult.lean` | 196 | `7dc7d0a1f30d54a43abe74dc10152ef37636d8b44ac21bbeaf13593919b46147` |
| `joshlf/anneal` (`42f4571d761b46c7142815f38b69c3781b3555e3`) | `trusted/lean/Trusted/MirSemantics.lean` | 872 | `437300dc48754b22d3a1b60cd6bb90a68e0c8a3aad84a6cf3916be6df061b9e3` |
| `joshlf/anneal` (`42f4571d761b46c7142815f38b69c3781b3555e3`) | `trusted/rustc-capture/src/proof_gen.rs` | 388 | `32b33c237ae588d5ff031d39239483e355c9156e4c3fd02f610357096872ffc8` |
| `joshlf/anneal` (`42f4571d761b46c7142815f38b69c3781b3555e3`) | `theory/Anneal/FunctionalTranslation.lean` | 8,315 | `9b40696b6b504a67bc569042df3db5a9e08ac42beab65fb874bb0bac9a595385` |

## Revalidation

To revalidate the mechanized Lean 4.34.1 probes and verify the artifact digests
recorded in `support/source-manifest.json` from the package directory:

```bash
# 1. Verify SHA-256 digests of the two standalone Lean 4 probes:
sha256sum support/ProbeGeneralSpecAndLithium.lean support/ProbeTrackedFuncLangAndLoops.lean

# Expected output:
# 65f8af557997769bd43b4ce6eac36b79e1555bd222b75f31a4b439f08016895a  support/ProbeGeneralSpecAndLithium.lean
# 98e7321e53c2b32644b8e62c10275b26234f1c7c4d587f381374995a74b16a66  support/ProbeTrackedFuncLangAndLoops.lean

# 2. Typecheck both probes in the Lean 4.34.1 kernel with single-thread and memory caps:
~/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean -j1 -M1024 support/ProbeGeneralSpecAndLithium.lean
~/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean -j1 -M1024 support/ProbeTrackedFuncLangAndLoops.lean
```

Revalidate this report when:

1. Anneal modifies `Language.SpecOn` or `ForwardSim` in
   `trusted/lean/Trusted/Refinement.lean`, `StepResult` in
   `trusted/lean/Trusted/StepResult.lean`, or replaces the `Ensures*` family in
   `trusted/lean/Trusted/MirSemantics.lean`.
2. Upstream `AeneasVerif/aeneas` or `cryspen/hax` changes its `Result` monad,
   `Std.WP` calculus, `@[step]` discrimination-tree architecture, or `ITreeWP`
   adequacy hierarchy.
3. Upstream `lgaeher/refinedrust-dev` changes `radium`'s proof-generation
   template (`rr_frontend/radium/src/code.rs`) or Lithium's goal-directed
   stepping and side-condition caching rules (`theories/refinedrust/lithium/`).
