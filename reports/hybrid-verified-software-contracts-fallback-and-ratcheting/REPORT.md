# Hybrid Verified Software: `Option<T>` Contract Semantics, Fallback Isolation, Multi-Producer Racing, and Monotone TCB Ratcheting

## Summary

A hybrid verified software component decouples computing a complex result from verifying its correctness: an unverified (or partially verified) producer emits `(output, witness)` (`Option<(Y, W)>`), and a much smaller trusted or formally verified certificate checker `V : X -> Y -> W -> Bool` filters the result before exposing `Option<Y>` (or falling back to a verified total baseline `F : X -> Y`) inside a larger verified system. Extending translation-validation and certifying-algorithm patterns from compilers and offline solvers to composable runtime software components introduces four structural contract requirements mechanized in [`support/HybridContracts.lean`](support/HybridContracts.lean) (Lean `v4.34.1`, `643` lines, `19` kernel-checked theorems with `0` `sorryAx` and at most `[propext]`):

1. **Soundness vs. Availability Split and `Option` Vacuity (`optionWrap_sound`, `none_always_satisfies_optionContract`, `optionLift_satisfies_dichotomy_while_none_passes`):** Wrapping any arbitrary (even adversarial) producer `P : X -> Option (Y × W)` with a sound checker `V` (`CheckerSound R V`) unconditionally satisfies `OptionContract pre R (fun _ => True)`. However, `OptionContract` cannot distinguish an honest solver from the trivial `fun _ => none` stub (which satisfies `OptionContract` even for `R := fun _ _ => False`), and naive postcondition-dichotomy checks (`OptionLift`) remain satisfied by `Option`-returning contracts unless an explicit `HasSomeWitness` progress obligation or verified fallback enforces non-vacuous execution.
2. **Serial `None`-Cascade Collapse (`optionSeq_eq_none_of_left_or_right`, `optionPipeline_adversarial_none_collapse`, `countSome_optionSeq_le_left`):** Composing `k` hybrid `Option` stages in series makes top-level availability bounded above by the minimum stage availability (`countSome (optionSeq f g) xs <= countSome f xs`), enabling a single broken or adversarial `none`-returning stage to force `0` end-to-end availability across `k - 1` otherwise sound stages.
3. **Stateful Fallback Isolation and Bounded-Fuel Totality (`naive_impure_fallback_state_pollution`, `spinMachine_never_halts`, `isolatedVerifyOrFallback_sound_and_total`):** Wrapping an untrusted producer with a verified fallback (`verify_or_fallback`) recovers total `Y` availability only if the producer cannot pollute shared mutable state, unwind/abort, or diverge prior to certificate checking. When an impure producer mutates state before failing (`badImpureProducer`), even a `100%` sound checker plus a `100%` verified fallback violates the outer post-state invariant; and without a step budget (`spinMachine`), an untrusted producer violates `EffectMask.terminates = true`. Executing the producer against an isolated/snapshot state under explicit step fuel and panic containment (`isolatedVerifyOrFallback`) restores both unconditional soundness and total termination (`EffectMask` `(true, true, true)`).
4. **Multi-Producer Hedging (`raceProducers_sound`, `raceOrFallback_sound_and_total`, `raceProducers_isSome_iff`) and Spec-Preserving TCB Ratcheting (`ratchet_strictly_shrinks_tcb`, `outer_invariant_preserved_across_ratchet`):** Checking a list of heterogeneous untrusted producers against one verified checker preserves soundness regardless of how many producers fail or emit forged witnesses while amplifying availability (`some` iff *at least one* producer succeeds). Along the 4-rung Hybrid Assurance Ladder (`Rung 0` trusted producer -> `Rung 1` TCB checker/fallback -> `Rung 2` verified checker/fallback -> `Rung 3` end-to-end verified direct implementation), upgrading from Rung 1 to Rung 2 to Rung 3 strictly shrinks the Trusted Computing Base (`tcb(3) ⊂ tcb(2) ⊂ tcb(1)`) while preserving outer verified caller proofs verbatim (`outer_invariant_preserved_across_ratchet`).

*Model–system relation note:* The 19 theorems in [`support/HybridContracts.lean`](support/HybridContracts.lean) govern a self-contained mathematical model in pure Lean 4 (`namespace HybridFV`) rather than an extraction of Rust MIR; connections to Anneal's MIR semantics and Rust contracts are explicitly labeled `Basis: derived (modeling bridge)`.

## Applicability

- **Mechanized model (`support/HybridContracts.lean`, `support/lakefile.toml`, `support/lean-toolchain`):** Checked directly under `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) with zero external dependencies (core `Init` only; zero Mathlib; zero `sorryAx`, `Classical.choice`, or `Lean.ofReduceBool`).
- **Anneal specification and MIR operational architecture (`google/zerocopy` at `7527dd2b9ae90b60d2ae8258ffd44bd0ee1e4d82`):** Inspected directly in `anneal/docs/spec-core-and-golden-closure.md` (target architecture for `FnContract`, `EffectMask`, `AssumedContractRealizable`, `SpecEvalVal`, and `CallEdgeStratified`), `anneal/trusted/lean/Trusted/MirSemantics/Boundary.lean` (`WellFormed`, `Behavior`, `Diverges`, `SatisfiesPost`, `BodyVerified`), `anneal/theory/Anneal/Core/SpecRealizability.lean` (`PostconditionDichotomy`, `DichotomyModuloObservation`, `TerminalReturnDichotomy`), and `anneal/THREAT_MODEL.md` (two-surface human audit boundary).
- **Relationship to sibling corpus reports:** Builds on `sound-checker-laws-anchors-allowlists-and-certificates` (one-sided certification soundness `certChecker`), `translation-validation-certifying-compilation-and-pass-refinement-certificates` (pass-level validation relations), and `safety-liveness-decomposition-and-refinement-with-divergence` (divergence observability in trace refinement). Those prior reports analyze static compiler/program checkers or infinite traces; this report addresses runtime software component contracts (`Option<T>` vs. total fallback), stateful mutation/termination hazards inside fallback wrappers, multi-producer racing, and monotone TCB ratcheting across Anneal `FnContract`/`EffectMask` boundaries.

## Findings

### 1. Formal Semantics of `Option<T>` Hybrid Components vs. `Option` Vacuity and Cascades

`Basis: execution (Lean 4 v4.34.1 kernel check)`

Core definitions from [`support/HybridContracts.lean`](support/HybridContracts.lean) (`lines 17-109`):

```lean
def CheckerSound {X : Type u} {Y : Type v} {W : Type w}
    (R : X → Y → Prop) (V : X → Y → W → Bool) : Prop :=
  ∀ x y w, V x y w = true → R x y

def optionWrap {X : Type u} {Y : Type v} {W : Type w}
    (V : X → Y → W → Bool) (P : X → Option (Y × W)) (x : X) : Option Y :=
  match P x with
  | none => none
  | some (y, w) => if V x y w then some y else none

def OptionContract {X : Type u} {Y : Type v}
    (pre : X → Prop) (R : X → Y → Prop) (onNone : X → Prop)
    (f : X → Option Y) : Prop :=
  ∀ x, pre x →
    match f x with
    | none => onNone x
    | some y => R x y
```

1. **Producer-independent soundness (`optionWrap_sound`, lines 47-63, axioms `[]`):** Whenever `CheckerSound R V` holds, `OptionContract pre R (fun _ => True) (optionWrap V P)` holds unconditionally for *every* producer `P : X → Option (Y × W)`. Soundness depends solely on `V`, never on how `P` searches, optimizes, or fails.
2. **Unconstrained `none` permits trivial completeness collapse (`none_always_satisfies_optionContract`, lines 67-71, axioms `[]`):** `fun _ => none` satisfies `OptionContract pre R (fun _ => True)` for *every* `(pre, R)`, including the unsatisfiable postcondition `R := fun _ _ => False`. In adversarial or reward-hacking settings, an unverified producer can emit `none` (or an invalid witness rejected to `none` by `V`) to satisfy safety without doing useful work.
3. **`Option`-vacuity blind spot in dichotomy-based spec checks (`optionLift_satisfies_dichotomy_while_none_passes`, lines 88-97; `const_none_fails_some_witness`, lines 104-107, axioms `[]`):** Under `OptionLift R x r := match r with | none => True | some y => R x y`, any specification `R` that satisfies `PostconditionDichotomy pre R` (`∃ x, pre x ∧ (∃ y_ok, R x y_ok) ∧ (∃ y_bad, ¬ R x y_bad)`) automatically passes `PostconditionDichotomy pre (OptionLift R)`, yet `fun _ => none` remains a valid implementation.
   - `Basis: derived (modeling bridge)` against `google/zerocopy@7527dd2b` (`anneal/theory/Anneal/Core/SpecRealizability.lean`, lines 187-230 & 899-915): `PostconditionDichotomy` and `TerminalReturnDichotomy` prevent constant-return vacuity on `T` by demanding one accepted normal return `v_ok` and one rejected normal return `v_bad` in the same caller memory, so an `Option<T>` contract that checks `R` inside `Some(v)` while allowing `None => true` passes `TerminalReturnDichotomy` even when a stub returns `None` everywhere. Closing that loophole requires either a `HasSomeWitness` runtime/proof witness (`∃ x y, pre x ∧ f x = some y`), an explicit non-trivial `onNone` liveness/domain restriction (`OptionContract pre R onNone` where `onNone x` holds only on documented exceptional inputs), or wrapping `Option<T>` in a total fallback returning `T`.
4. **Serial availability collapse (`optionSeq_eq_none_of_left_or_right`, lines 120-141; `optionPipeline_adversarial_none_collapse`, lines 153-162; `countSome_optionSeq_le_left`, lines 172-191, axioms `[]`):** For any serial composition `optionSeq f g`, the pipeline returns `none` iff either stage fails (`f a = none ∨ ∃ b, f a = some b ∧ g b = none`). On any finite workload `xs`, `countSome (optionSeq f g) xs ≤ countSome f xs`, and inserting a single `none`-returning stage anywhere in an arbitrary-length pipeline collapses end-to-end availability to `0` (`optionPipeline (preStages ++ (fun _ => none) :: postStages) a = none`). By contrast, a total fallback wrapper guarantees `countSome (fun x => some (f x)) xs = xs.length` (`countSome_total_full`, lines 193-201, axioms `[]`).

---

### 2. Fallback Chains, State-Pollution Hazards, and Resource/Termination Containment

`Basis: execution (Lean 4 v4.34.1 kernel check) + source + documentation`

Replacing `Option<T>` with a fallback pattern (`fast_untrusted -> checker -> verified_fallback -> T`) restores total availability only if three side-effect hazards in the untrusted producer are sealed before `checker` rejects or `fallback` executes:

1. **State-Pollution Counterexample (`naive_impure_fallback_state_pollution`, lines 243-259, axioms `[propext]`):** In [`support/HybridContracts.lean`](support/HybridContracts.lean) (`lines 217-259`), `naiveVerifyOrFallbackImpure` passes the post-producer state `st'` into `fallback` when the checker rejects `(y, w)`. Even when `simpleChecker` is `100%` sound (`y = x + 1`) and `pureFallback` is `100%` verified (`spec x st y st' := y = x + st ∧ st' = st`), `badImpureProducer` (`st ↦ st + 1`, returning invalid `(x + 99, 0)`) causes `naiveVerifyOrFallbackImpure` to return `(11, 1)` on `(st = 0, x = 10)`, violating both the return invariant (`11 ≠ 10`) and the state invariant (`1 ≠ 0`).
2. **Non-Termination Counterexample (`spinMachine_never_halts`, lines 280-289, axioms `[]`):** In `MeteredMachine`, an unbounded producer `spinMachine` (`step n := some (n + 1)`, `extract _ := none`) never yields a certificate under any finite step budget (`runFuel spinMachine budget init = none`), breaking caller totality even when `checker` and `fallback` are total.
3. **Constructive Isolation + Metering Theorem (`isolatedVerifyOrFallback_sound_and_total`, lines 299-350, axioms `[]`):**
   ```lean
   def isolatedVerifyOrFallback {S X Y W : Type}
       (V : S → X → Y → W → Bool)
       (isolatedMeteredP : Nat → S → X → ExecOutcome Unit (Y × W))
       (budget : Nat)
       (commitState : S → X → Y → S)
       (fallback : S → X → Y × S)
       (st : S) (x : X) : Y × S :=
     match isolatedMeteredP budget st x with
     | .ok (y, w) () =>
       if V st x y w then (y, commitState st x y) else fallback st x
     | .panicked () => fallback st x
     | .outOfBudget () => fallback st x
   ```
   When the producer executes against an isolated/read-only view of `(st, x)` under a finite step/resource budget `budget` (returning `.panicked ()` or `.outOfBudget ()` without mutating `st`) and `commitState`/`fallback` satisfy `Post`, `isolatedVerifyOrFallback` guarantees `Post st x res.1 res.2` unconditionally across all producer failures, rejections, panics, and timeouts.

`Basis: source + derived (modeling bridge)` against `google/zerocopy@7527dd2b` (`anneal/docs/spec-core-and-golden-closure.md`, lines 58-156; `anneal/trusted/lean/Trusted/MirSemantics/Boundary.lean`, lines 66-100):
- Anneal's Specification Core v2 `FnContract` models effects via three boolean flags `EffectMask := { terminates, noUnwind, noAbort }` (defaulting verified specs to `terminates = true` while defaulting assumed external/unverified contracts to `terminates = false` in `AssumedContractRealizable` so unverified callees cannot trivially derive `False` via divergence).
- Consequently, calling an unverified producer directly inside a `terminates = true, noUnwind = true, noAbort = true` outer Rust function requires **mechanical containment** at the boundary:
  1. *Memory/state isolation:* Read-only borrow `&S` / `&[u8]` (safe Rust without `UnsafeCell` or interior mutability, or separate address space/sandbox) rather than `&mut S`, or explicit copy/rollback prior to `commitState`;
  2. *Unwind/panic containment:* Either statically proving panic-freedom on the producer or isolating via `std::panic::catch_unwind` (with `UnwindSafe` state isolation) or process/Wasm isolation;
  3. *Termination and OOM containment:* Explicit iteration/fuel counter inside the producer for algorithmic loops, paired with fallible allocation (`try_reserve`) or external sandbox memory/time limits when the producer cannot be trusted to check fuel.

---

### 3. Multi-Producer Hedging and the 4-Rung Assurance Ratchet

`Basis: execution (Lean 4 v4.34.1 kernel check)`

1. **Multi-Producer Hedging / Racing (`raceProducers_sound`, `raceOrFallback_sound_and_total`, `raceProducers_isSome_iff`, lines 359-471, axioms `[]`):**
   Given a heterogeneous list `ps : List (X → Option (Y × W))` (e.g., an aggressive vectorized/AI-synthesized candidate followed by a conservative heuristic candidate) gated by one checker `V` and backed by a verified total fallback `F`:
   - `raceProducers` unconditionally preserves `OptionContract pre R (fun _ => True)`, and `raceOrFallback` preserves `TotalContract pre R`.
   - `raceProducers_isSome_iff` proves that `raceProducers V ps x` yields `some _` if and only if *at least one* producer `p ∈ ps` produces a `V`-accepted `(y, w)`. Thus, hedging turns fragile single-producer availability into disjunctive resilience while preserving soundness against arbitrary buggy or adversarial producers in `ps`.
2. **4-Rung Hybrid Assurance Ladder and Spec-Preserving Ratcheting (`ratchet_strictly_shrinks_tcb`, lines 512-555, axioms `[propext]`; `outer_invariant_preserved_across_ratchet`, lines 609-619, axioms `[]`; `totalContract_refines_optionContract`, lines 504-508, axioms `[]`):**

| Rung | Producer Trust Status | Checker & Fallback Status | External Signature | `tcbForRung` Members | When Appropriate |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Rung 0** | In TCB (`producerCode`) | None | `X -> Y` (or `Option Y`) | `{specAndKernel, producerCode}` | Trivial/tiny base functions where producer is smaller than any checker |
| **Rung 1** | **Untrusted** | **In TCB** (`checkerCode`, `fallbackCode`, `isolationHarness`) | `X -> Option Y` or `X -> Y` | `{specAndKernel, isolationHarness, fallbackCode, checkerCode}` | Rapid prototyping, untrusted AI/heuristic/SIMD fast paths behind human-audited tiny checker |
| **Rung 2** | **Untrusted** | **Formally verified** (`CheckerSound`, `TotalContract` proved) | `X -> Option Y` or `X -> Y` | `{specAndKernel, isolationHarness}` | Production systems with intractable/fast heuristic solvers and small verified checkers |
| **Rung 3** | **Formally verified** | Eliminated (zero runtime checking overhead) | `X -> Y` | `{specAndKernel}` | Mature kernels where runtime checking cost or isolation overhead must be zero |

   - `ratchet_strictly_shrinks_tcb` proves strict TCB subset shrinkage across Rungs `1 → 2 → 3` (`tcbForRung 3 ⊂ tcbForRung 2 ⊂ tcbForRung 1`).
   - `outer_invariant_preserved_across_ratchet` proves that any outer system `outer` verified parametrically against `TotalContract pre R` preserves `OuterPost` identically across every Rung `1 → 2 → 3` transition without re-verifying `outer`.
   - `totalContract_refines_optionContract` proves that replacing an `Option Y` hybrid component with a `verifyOrFallback`-wrapped total `Y` implementation (lifted via `some`) refines any `OptionContract` caller while lifting availability to `100%` (`countSome_total_full`).
   - `EffectMask.le` (`effectMask_le_refl`, `effectMask_le_trans`, lines 489-500, axioms `[]`) shows that strengthening a component's effect guarantees (`terminates`, `noUnwind`, `noAbort`) is a reflexive, transitive preorder matching Anneal's `EffectMask` design.

---

### 4. Compositional Contracts for Anneal `FnContract` / `SpecCore`

`Basis: source + documentation + derived` (`google/zerocopy@7527dd2b`, `anneal/docs/spec-core-and-golden-closure.md`, `anneal/THREAT_MODEL.md`)

1. **Mapping hybrid wrappers into `FnContract`:**
   - An **unwrapped `Option<T>` producer+checker** exposes `effects.terminates = false` (or `true` when fuel-metered), `postReturn q out := match decodeOption out.ret with | none => onNone q | some y => R q y`, and requires an external caller fallback or `HasSomeWitness` anti-vacuity gate (`SpecRealizability`).
   - An **isolated `verify_or_fallback` wrapper** exposes a total `T` `FnContract` with `effects = { terminates := true, noUnwind := true, noAbort := true }` and `postReturn q out := R q out.ret`.
2. **Human-Audit Alignment with `THREAT_MODEL.md`:** Anneal's two-surface review model restricts human inspection to **(i) stated specifications** (rendered golden spec closure) and **(ii) the TCB audit log**. Under Hybrid Verified Software:
   - At **Rung 1**, `#[anneal::trusted]` marks the tiny checker + fallback (`checkerCode`, `fallbackCode`) in the TCB audit log while the large solver runs as safe unverified code (or if unverified inside `#[forbid(unsafe_code)]`, needs only `WellFormed` UB-freedom or OS/sandbox isolation — never functional correctness proofs!).
   - At **Rung 2**, verifying the checker removes the checker's functional-correctness `#[anneal::trusted]` waiver from the TCB audit log completely: the auditor inspects only `Spec(x, y)` and the isolation boundary!

## Boundaries

- **Toy-model scope of mechanized theorems:** [`support/HybridContracts.lean`](support/HybridContracts.lean) models pure functions `X -> Option Y`, abstract `ExecOutcome S (Y × W)`, and `MeteredMachine` in Lean 4; it does **not** mechanize Rust MIR operational semantics, memory aliasing, `unsafe` UB, or process-level sandboxing (`not examined` here — those memory-safety and hyperproperty limits require separate modeling over pointer/borrow semantics and multi-trace noninterference).
- **Non-blocking resource/OOM limits in safe Rust:** Even `#![forbid(unsafe_code)]` Rust code can abort on OOM (`alloc::handle_alloc_error`) or overflow the thread stack on deep recursion, violating `EffectMask.noAbort = true` unless allocation is fallible/bounded or the producer runs in an isolated process/Wasm/thread-stack sandbox (`unknown` / depends on runtime harness outside Lean's pure model).
- **Rung 0 vs. Rung 1–3 TCB comparison:** `ratchet_strictly_shrinks_tcb` proves `tcb(3) ⊂ tcb(2) ⊂ tcb(1)` and deliberately does **not** claim `tcb(1) ⊂ tcb(0)`: Rung 1 replaces `producerCode` with `{isolationHarness, fallbackCode, checkerCode}`, which shrinks the TCB only when the checker + fallback + isolation harness are substantially simpler/smaller than the unverified producer.
- **`FnContract` code status in `google/zerocopy@7527dd2b`:** As documented in `anneal/docs/spec-core-and-golden-closure.md`, Specification Core v2 (`FnContract`, 3-bit `EffectMask`, `AssumedContractRealizable`) is documented target architecture alongside the live `Trusted.MirSemantics.Boundary` (`WellFormed`, `Behavior`, `Diverges`, `SatisfiesPost`, `BodyVerified`) and `Anneal.Core.SpecRealizability` code present at `7527dd2b9ae90b60d2ae8258ffd44bd0ee1e4d82`.

## Evidence

- **Standalone Lean 4.34.1 mechanization (preserved in package `support/`):**
  - [`support/HybridContracts.lean`](support/HybridContracts.lean) (`643` lines, SHA-256 `c4e053f343729973d97388602f41f91e15aac946a0e94f05e8ee8749e295f2b2`), paired with [`support/lean-toolchain`](support/lean-toolchain) (`leanprover/lean4:v4.34.1`) and [`support/lakefile.toml`](support/lakefile.toml).
  - Executed directly via `elan run leanprover/lean4:v4.34.1 lean -DElab.async=false HybridContracts.lean` on `2026-11-24` (exit `0`, zero warnings): `17` theorems report `does not depend on any axioms` (`optionWrap_sound`, `none_always_satisfies_optionContract`, `optionLift_satisfies_dichotomy_while_none_passes`, `const_none_fails_some_witness`, `optionSeq_eq_none_of_left_or_right`, `optionPipeline_adversarial_none_collapse`, `countSome_optionSeq_le_left`, `countSome_total_full`, `spinMachine_never_halts`, `isolatedVerifyOrFallback_sound_and_total`, `raceProducers_sound`, `raceOrFallback_sound_and_total`, `raceProducers_isSome_iff`, `effectMask_le_refl`, `effectMask_le_trans`, `totalContract_refines_optionContract`, `outer_invariant_preserved_across_ratchet`), and `2` theorems report `depends on axioms: [propext]` (`naive_impure_fallback_state_pollution`, `ratchet_strictly_shrinks_tcb`). Zero `sorryAx`, `Classical.choice`, `Quot.sound`, or `Lean.ofReduceBool`.
- **Anneal upstream files (`google/zerocopy`, commit `7527dd2b9ae90b60d2ae8258ffd44bd0ee1e4d82`, inspected `2026-11-24`):**
  - `anneal/docs/spec-core-and-golden-closure.md` (`lines 58-156, 185-195`: `EffectMask`, `FnContract`, `AssumedContractRealizable`, `SpecEvalVal`).
  - `anneal/trusted/lean/Trusted/MirSemantics/Boundary.lean` (`lines 66-100, 143-250`: `WellFormed`, `Behavior`, `Diverges`, `SatisfiesPost`, `BodyVerified`).
  - `anneal/theory/Anneal/Core/SpecRealizability.lean` (`lines 187-230, 899-915`: `PostconditionDichotomy`, `DichotomyModuloObservation`, `TerminalReturnDichotomy`).
  - `anneal/THREAT_MODEL.md` (two-surface human audit boundary).

## Revalidation

Run the standalone Lean `v4.34.1` kernel and axiom check from `reports/hybrid-verified-software-contracts-fallback-and-ratcheting/support/`:

```bash
elan run leanprover/lean4:v4.34.1 lean -DElab.async=false HybridContracts.lean
```

Confirm exit status `0`, zero warnings/errors, and that `#print axioms` prints only `does not depend on any axioms` or `depends on axioms: [propext]` across all `19` listed declarations.
