# Hybrid Verified Software Architecture: Minimal `CertifiedGate` Algebra, `Atomic` and Frame-Safety Counterexamples, and Ring-0 vs. Ring-1 Anneal Integration

## Summary

Combining an unverified or partially verified producer `f` with a formally verified checker or certificate verifier `V` into a reusable formal building block does not require separate traits or wrapper families for unary predicates, relational validators, explicit `(Y, W)` certificates, iterative hint loops, incremental streams, and multi-producer portfolios. Primary-source inspection of `google/zerocopy` (`487101d7a5233982e7bd05a1c76e039073ce1702`), an 11-theorem Lean `v4.34.1` mechanization ([`support/HybridArchitecture.lean`](support/HybridArchitecture.lean), `478` lines, `0` `sorryAx`), and `#![forbid(unsafe_code)]` Rust and Miri probes ([`support/hybrid_arch_verify/src/lib.rs`](support/hybrid_arch_verify/src/lib.rs), `473` lines, `rustc 1.102.0-nightly` / `miri 0.1.0`) establish five architectural invariants:

1. **Minimal Unifying Core (`RawOutcome` + `CertifiedGate`) and Four Orthogonal Combinators (`evalGate`, `firstAccepted`, `withFallback`, `foldGate`):** Every containment substrate (pure Lean `partial`, safe Rust `catch_unwind`, in-process `Rung 1.5` Rust, Wasm/RLBox sandboxes, or OS child processes) lowers to one untrusted outcome sum `RawOutcome E Y W` (`.candidate y w | .prodErr e | .trapped`), and every checker lowers to one record `CertifiedGate X Y W Pre Spec` bundling an $O(1)$ pre-traversal witness bound (`wSize w ≤ maxWitness x`) with a decidable predicate `check : X → Y → W → Bool`. Setting `W = Unit` (`maxWitness = 0`) specializes `evalGate` at zero overhead to unary and relational checks; `firstAccepted` lifts `evalGate` over candidate portfolios; `withFallback` discharges total availability directly against `Spec` without requiring `check` completeness; and folding `CertifiedGate` over state transitions unifies interleaved hint loops (`foldHintSteps_preserves_inv`) and prefix-safe incremental streaming (`foldStreamPrefix_all_emitted_valid`).
2. **Pre-Gate Portfolio Drop Bug (`naive_precheck_orelse_drops_valid_backup` vs. `firstAccepted_ok_iff_exists`):** Composing multiple candidate producers via monadic choice *before* checker evaluation (`p1(x).or_else(|| p2(x))` followed by `evalGate`) silently discards a valid backup producer `p2` whenever `p1` returns a syntactically well-typed but invalid `.candidate y_bad w_bad`. Gate-aware `firstAccepted` evaluates `evalGate` per candidate and succeeds if and only if at least one producer in the portfolio emits a gate-accepted candidate.
3. **`Atomic*` `Sync + RefUnwindSafe` TOCTOU Counterexample Against Borrowed `&I` Gates (`test_sync_refunwindsafe_still_allows_atomic_toctou_without_snapshot`):** Although `I: Sync + std::panic::RefUnwindSafe` rejects single-threaded `Cell<T>` and `RefCell<T>` interior mutability, `core::sync::atomic::AtomicU64` (and all `Atomic*` types) implement **both** `Sync` and `RefUnwindSafe` in safe Rust. Under both default Stacked Borrows Miri and `-Zmiri-tree-borrows` (`0` UB), a gate accepting `&AtomicU64` validates `10` before a concurrent thread stores `999`, breaking input-output relational soundness unless the boundary snapshots shared or interior-mutable inputs once into owned `Freeze` storage prior to checking (`snapshot_and_eval`).
4. **Rung 1.5 Frame-Preservation Requirement (`rung15_without_callerMemPreserved_unsound` vs. `rung15_with_callerMemPreserved_sound`):** Proving memory safety (`WellFormedV2`) alone with `postReturn := fun _ _ _ => True` on an in-process `unsafe` producer (`Rung 1.5`) is **unsound** when composed with a verified checker and fallback: the UB-free producer can overwrite mutable `CallerMemory` before returning an invalid candidate, corrupting the state read by `check` and `fallback`. Requiring `CallerMemPreserved` (`postReturn := fun q _ mem' => mem' = q.callerMem`) alongside `EffectMask.le outerMask fMask` restores full soundness and totality while still requiring **zero** functional correctness proof about the producer's return value.
5. **Exact Ring-0 vs. Zero-TCB Ring-1 Split in Anneal (`google/zerocopy@487101d7a523`):** All hybrid combinators, reflective `BoolCertCut` bridges, `Rung 1.5` frame-composition theorems, and joint `(EffectMask.le ∧ AvailabilityRefines)` ratcheting laws (`hybridRefines_trans`) reside in `0`-TCB `anneal/theory/` (`Anneal.Hybrid`). By contrast, supporting external uncaptured `MirAssumedStub` callees requires **four** coordinated Ring-0 (`anneal/trusted/`) additions—not merely flipping `bodyIsExternal` and allowlisting `MirEnvelopeTheoremV2`: (i) reconciling `Contract.EffectMask` (`2` bits) and `SafeContractV2.EffectMaskV2` (`1` bit) onto `Trusted.Framework.EffectMask` (`3` bits); (ii) adding `Body.isExternal : Bool` (`isExternal = true → basicBlocks = []`); (iii) adding operational demonic stub-call stepping (`evalAssumedCall` in `Trusted/MirSemantics/Step.lean`) plus `assumed_stubs` extraction in `trusted/rustc-capture/`; and (iv) admitting model-pinned `MirEnvelopeTheoremV1/V2` in `TrustedBoundary.lean`.

*Model–system relation note:* [`support/HybridArchitecture.lean`](support/HybridArchitecture.lean) mechanizes the core gate algebra, portfolio/streaming combinators, Rung 1.5 memory-frame composition, and `HybridRefines` preorder over pure Lean 4 state/outcome types (`namespace HybridArch`); concrete mappings to `Trusted.MirSemantics.evalStepV2` and Rust runtime semantics are marked `Basis: derived` or executed directly in [`support/hybrid_arch_verify/src/lib.rs`](support/hybrid_arch_verify/src/lib.rs).

## Applicability

- **Anneal and `zerocopy` source baseline (`google/zerocopy` at `487101d7a5233982e7bd05a1c76e039073ce1702`):** Applies to `anneal/trusted/lean/Trusted/{Framework.lean, Framework/Instances.lean, Framework/Bridge.lean, MirAst/Types.lean, MirAst/Terminators.lean, MirAst/Body.lean, MirModel.lean, MirSemantics/{Boundary.lean, Contract.lean, CoreContracts.lean, Step.lean}}`, `anneal/trusted/audit/TrustedBoundary.lean`, `anneal/trusted/rustc-capture/src/{capture.rs, extract.rs}`, `anneal/theory/Anneal/{Framework.lean, Framework/StepWp.lean, Core/SpecRealizability.lean, SafeTwin/Equiv.lean, Generic/OpenSemantics.lean}`, `anneal/docs/{alpha.md, spec-core-and-golden-closure.md, trust-model.md}`, `zerocopy/src/{byte_slice.rs, layout.rs, lib.rs}`, and `zerocopy/proofs/{08_byte_slice_split_at_unchecked, 14_known_layout_and_dst_layout}/`.
- **Lean 4 mechanization ([`support/HybridArchitecture.lean`](support/HybridArchitecture.lean)):** Checked under `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) using core `Init` only (`0` external dependencies, `0` warnings under `-DwarningAsError=true`, `0` `sorryAx`, `0` `._unsafe_rec`, `0` `Lean.ofReduceBool`, axioms strictly within `{propext, Quot.sound}`).
- **Rust and Miri verification suite ([`support/hybrid_arch_verify/`](support/hybrid_arch_verify/Cargo.toml)):** `#![forbid(unsafe_code)]` Rust 2021 crate with zero external dependencies, compiled with `RUSTFLAGS="-D warnings"` (`0` warnings) and executed under `rustc 1.102.0-nightly` / `miri 0.1.0` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, LLVM `23.1.5`) on `x86_64-unknown-linux-gnu` across `--release`, default Stacked Borrows Miri, and `-Zmiri-tree-borrows`.
- **Relationship to sibling corpus reports:** Synthesizes and refines the empirical constraint taxonomy in `hybrid-verified-software-building-block-constraints-and-anneal-integration` (and earlier `hybrid-verified-software-{contracts-fallback-and-ratcheting, hazards-ub-toctou-and-hyperproperties, rust-lean-prototype-and-benchmarks, taxonomy-and-roi-boundaries}` reports) into a single minimal compositional algebra while uncovering three previously unrecorded defects: the pre-gate portfolio `orElse` availability drop, the `AtomicU64: Sync + RefUnwindSafe` borrowed-input TOCTOU bypass, and the `CallerMemPreserved` frame requirement + `evalAssumedCall` operational gap in Anneal's Ring-0/Rung-1.5 integration.

## Findings

### 1. Minimal Core Abstraction (`CertifiedGate`) and Unification of Shapes `S1`–`S6`

`Basis: execution + derived` ([`support/HybridArchitecture.lean`](support/HybridArchitecture.lean), `L24-314`; [`support/hybrid_arch_verify/src/lib.rs`](support/hybrid_arch_verify/src/lib.rs), `L18-219`)

Separating untrusted candidate acquisition (`Iso : X → RawOutcome E Y W`) from verified certification (`CertifiedGate X Y W Pre Spec`) eliminates per-shape checker traits:

```lean
inductive RawOutcome (E Y W : Type) where
  | candidate (y : Y) (w : W)
  | prodErr   (e : E)
  | trapped

inductive HybridErr (E : Type) where
  | producerTrapped
  | producerFailed   (e : E)
  | witnessOversized (actual : Nat) (maxAllowed : Nat)
  | rejectedByChecker

structure CertifiedGate (X Y W : Type) (Pre : X → Prop) (Spec : X → Y → Prop) where
  maxWitness : X → Nat
  wSize      : W → Nat
  check      : X → Y → W → Bool
  sound      : ∀ x y w, Pre x → wSize w ≤ maxWitness x → check x y w = true → Spec x y
```

1. **Built-In $O(1)$ Witness Bound Weakens Checker Proof Burden (`evalGate_sound`, `[propext]`; `evalGate_rejects_oversized_without_check`, `[]`):**
   - `evalGate` checks `Nat.ble (g.wSize w) (g.maxWitness x)` before invoking `g.check x y w`. Any oversized witness (`g.maxWitness x < g.wSize w`) returns `.error (.witnessOversized ...)` in $O(1)$ without executing `g.check`, and `g.sound` may assume `wSize w ≤ maxWitness x` (for example, guaranteeing that fixed-width index arithmetic inside `g.check` cannot overflow).
   - Specializing `W = Unit`, `maxWitness := fun _ => 0`, and `wSize := fun _ => 0` recovers unary predicates (`S1`, ignoring `x`) and witness-free relational validators (`S2`, such as `SliceDstCastGate` in `lib.rs:247-301` mirroring `zerocopy`'s `DstLayout::validate_cast_and_convert_metadata`) with zero extra traits or runtime branches.
2. **Gate-Aware Portfolio Monoid vs. Pre-Gate `orElse` (`naive_precheck_orelse_drops_valid_backup`, `[propext]`; `firstAccepted_sound`, `[propext]`; `firstAccepted_ok_iff_exists`, `[Quot.sound]`):**
   - Combining candidate outcomes before checking (`naivePreGateChoice [.candidate 999 (), .candidate 7 ()]`) commits to `.candidate 999 ()` and fails `evalGate` (`RejectedByChecker`), dropping the valid backup `.candidate 7 ()`.
   - `firstAccepted` evaluates `evalGate g x` lazily across the candidate list and satisfies the exact disjunctive availability biconditional `(∃ y, firstAccepted g x cands = .ok y) ↔ (∃ r ∈ cands, ∃ y, evalGate g x r = .ok y)`.
3. **Dual-Mint `Checked<Y, Spec>` Capability Sealing (`withFallback_total_sound`, `[propext]`):**
   - In Rust (`lib.rs:34-74, 152-163`), `#[repr(transparent)] pub struct Checked<Y, Spec>` keeps its fields private to `gate_core` and admits exactly two internal mint paths: `eval_gate` (`GateSound`) and `with_fallback` (`VerifiedFallback`, proved directly against `Spec` without calling `gate.check`). This retires the `assert!(checker(&I, &fb))` pattern from earlier prototypes, which panics/aborts whenever `gate.check` is sound-but-incomplete on `fb` (`test_portfolio_first_accepted_and_incomplete_checker_fallback`).
4. **Single Stateful Fold Covering `S4` Hint Loops and `S5` Prefix-Safe Streams (`foldHintSteps_preserves_inv`, `[propext]`; `foldStreamPrefix_all_emitted_valid`, `[propext]`):**
   - Iterating `withFallback ∘ evalGate` over `CertifiedGate (S × U) S W` preserves state invariant `Inv` across arbitrary untrusted step hints without exposing mutable state to `pStep` (`S4`).
   - Iterating short-circuiting `evalGate` over `CertifiedGate (S × U) (S × C) W` validates `(nextState, chunk)` *before* emitting `chunk` (`fold_stream_prefix` in `lib.rs:188-211`), guaranteeing `ValidChunk` on every emitted prefix even when a later chunk is rejected or trapped (`S5`).

---

### 2. Two Newly Exposed Soundness Loopholes: `Atomic*` `Sync + RefUnwindSafe` TOCTOU and Rung 1.5 Caller-Memory Pollution

`Basis: execution + source` ([`support/HybridArchitecture.lean`](support/HybridArchitecture.lean), `L317-443`; [`support/hybrid_arch_verify/src/lib.rs`](support/hybrid_arch_verify/src/lib.rs), `L310-369`)

1. **`I: Sync + RefUnwindSafe` Does NOT Prevent Safe-Rust Concurrent TOCTOU on Borrowed `&I` Inputs (`test_sync_refunwindsafe_still_allows_atomic_toctou_without_snapshot`):**
   - Earlier safe-Rust hybrid wrappers constrained borrowed inputs `&I` via `I: Sync + std::panic::RefUnwindSafe` to exclude `Cell<T>`, `RefCell<T>`, and `Mutex<T>`. However, in Rust's `core` library, `AtomicU64` (and all `core::sync::atomic::Atomic*` types) implement **both** `Sync` and `RefUnwindSafe` (`assert_sync_and_ref_unwind_safe::<AtomicU64>()` compiles cleanly under `#![forbid(unsafe_code)]`).
   - Passing `&AtomicU64` as `&G::Input` into `eval_gate` checks `inp.load(Acquire) == 10` (`Ok(Checked(10))`), after which a concurrent safe thread executes `shared.store(999, Release)`—violating the relational invariant `output == current(input)` with `0` UB under both Stacked Borrows and Tree Borrows Miri.
   - **Architectural Resolution (`snapshot_and_eval`, `lib.rs:167-184`):** Borrowed inputs to a relational `CertifiedGate` MUST either have type `Freeze` (zero `UnsafeCell`, excluding `Atomic*`) under single-thread / immutable borrow guarantees, or pass through `snapshot_and_eval`, which executes a single-fetch value copy (`snapshot_once() -> G::Input`) into owned private memory *before* invoking the producer and `eval_gate`.
2. **In-Process `Rung 1.5` (`WellFormed`-Only `unsafe` Producer) Requires `CallerMemPreserved` (`rung15_without_callerMemPreserved_unsound`, `[]`; `rung15_with_callerMemPreserved_sound`, `[propext]`):**
   - In Anneal's `MirProfileV2` (`anneal/trusted/lean/Trusted/Framework/Instances.lean:234-286`), a function body's `Query` includes caller heap/stack allocations `callerMem : CallerMemory` and `.returned` carries post-call `mem : CallerMemory`.
   - `rung15_without_callerMemPreserved_unsound` constructs a total, UB-free producer `badF` (`InProcessBodyContract Pre (fun _ _ _ _ => True) EffectMask.totalNormal badF`) that mutates `mem` (`10 ↦ 0`) and returns bogus output `x + 999`. Even when paired with a `100%`-sound checker `soundCheck` (`y == x + m`) and a `100%`-verified fallback `verifiedFb` (`(x + m, m)`), `rung15Compose` returns `(x + 0, 0)`, falsifying `Post` (`y = x + 10 ∧ m' = 10`).
   - `rung15_with_callerMemPreserved_sound` proves that strengthening `f`'s postcondition solely to the pure frame equality `postRet := fun m _ _ m' => m' = m` (while still proving **nothing** about `f`'s returned candidate `(y, w)`) + `EffectMask.le outerMask fMask` makes in-process `Rung 1.5` composition unconditionally sound and total with zero runtime sandboxing or copy overhead.

---

### 3. Exact Ring-0 vs. Zero-TCB Ring-1 Integration Map in Anneal (`google/zerocopy@487101d7a523`)

`Basis: source + derived` (`google/zerocopy@487101d7a5233982e7bd05a1c76e039073ce1702`)

Auditing the literal definitions across `anneal/trusted/` and `anneal/theory/` separates capabilities achievable with **zero Ring-0 edits** from the exact minimal Ring-0 changes required for external/sandboxed callees:

| Subsystem / Seam | Current Definition on `487101d7a523` | Architectural Resolution (`Ring-1` vs. `Ring-0`) |
| :--- | :--- | :--- |
| **Gate Algebra, `BoolCertCut` & Ratcheting** | `BoolCertCut` (`Anneal/Framework/StepWp.lean:49-131`), `DichotomyModuloObservation` (`SpecRealizability.lean:224`), `SafeTwinQueryEquiv` (`SafeTwin/Equiv.lean:88`). | **`0`-TCB `Ring-1` (`anneal/theory/Anneal/Hybrid.lean`):** Hosts `CertifiedGate`, `evalGate`, `firstAccepted`, `withFallback`, `foldHintSteps`, `foldStreamPrefix`, `certGateCut_sound`, `rung15_with_callerMemPreserved_sound`, and `HybridRefines` (`hybridRefines_trans`, `[]`). |
| **Three Divergent `EffectMask`s** | `Trusted.Framework.EffectMask` (`{terminates, noUnwind, noAbort}`, `Framework.lean:152`); `Contract.EffectMask` (`{terminates, noUnwind}`, `Contract.lean:57`); `EffectMaskV2` (`{allowAbort}`, `Boundary.lean:694`). | **`Ring-0` Unification:** Standardize on `Trusted.Framework.EffectMask`; embed V1 via `{terminates := m.terminates, noUnwind := m.noUnwind, noAbort := true}` and V2 via `{terminates := false, noUnwind := true, noAbort := !m.allowAbort}`. Under `OracleGrade.licenses` (`Framework.lean:81-93`), `terminates = true` in V2 requires `.unbridgedSemantics` today and `.biFaultEquiv` (not `.forwardSim`) once Pass-2 `lean-miri` correspondence lands. |
| **External `MirAssumedStub` Stepping Gap** | `MirProfileV1/V2` set `bodyIsExternal := fun _ => false` (`Instances.lean:218, 275`); `Body` (`Body.lean:95-100`) has no `isExternal` field; `evalStepV2` (`Step.lean:3776`) faults `.unsupported` on all `.call`s; `evalStep` (`Step.lean:4085`) steps only into concrete `calleeBody.basicBlocks`; `extract.rs:2627` & `capture.rs:1975` reject external callees; `TrustedBoundary.lean:7225` rejects `MirEnvelopeTheoremV1/V2`. | **`Ring-0` 4-Part Prerequisite (Phase 2):** (1) Add `Body.isExternal : Bool` (`isExternal = true → basicBlocks = []`); (2) extract allowlisted `assumed_stubs` in `rustc-capture`; (3) add demonic `evalAssumedCall` in `Step.lean` ranging `Choice` over all `(ret, mem')` / `.unwound` / `.aborted` / stuttering-divergence outcomes permitted by `AssumedStub.contract` (non-empty by `StubRealizable`, `Framework.lean:188-197`); (4) allowlist model-pinned `MirEnvelopeTheoremV1/V2` in `TrustedBoundary.lean`. |
| **Profile v2 Intra-Crate Calls & Carriers** | Profile v2 models `Option<T>` (`CoreContracts.lean:481-511`) but rejects intra-crate `.call` (`Step.lean:3776`), `Result<T, E>`, closures, and 0-variant `Infallible` (`Types.lean:154-156`). `Anneal.Generic` (`OpenSemantics.lean:51-145`) has `8` open soundness gaps. | **Phased Realization:** Phase 1 uses `Option<T>` + `#[inline(always)]` monomorphic producer/checker helpers under `UnitTheoremV2` (`0` Ring-0 edits); Phase 2 adds intra-crate `call` to `evalStepV2`; Phase 3 adds `#[repr(transparent)]` `Checked<T, Spec>` erasure and 2-variant `MirTy.result` (keeping `Option`/`Result` signatures at Rung 3 with `isSome`/`isOk = true` rather than `Infallible`). Avoid `Anneal.Generic` trait specs until all 8 `OpenSemantics` gaps close. |

## Boundaries

- **Not examined:**
  - Formal proof of `evalAssumedCall` step simulation against `vendor/lean-miri/` (`Trusted.MirSemantics` Profile v2 currently operates under `OracleGrade.unbridged "mir_profile_v2"`, `Trusted/Framework/Instances.lean:273`).
  - Hardware microarchitectural side channels (`Spectre` branch-target/bounds-check bypass) across in-process Wasm/SFI sandboxes (`known not to apply` without separate OS process or VM page-table isolation).
- **Unknown:**
  - Exact `cargo-anneal` symbolic-execution / WP verification time on merged `#[inline(always)]` `Rung 1.5` producer + checker CFGs as producer loop complexity grows prior to Phase-2 modular intra-crate `TerminatorKind.call` support in Profile v2.
- **Unsupported in `google/zerocopy@487101d7a5233982e7bd05a1c76e039073ce1702`:**
  - Capturing `Result<T, E>`, `core::convert::Infallible` (`Variants::Empty`), closures/`FnPtr`, intra-crate `TerminatorKind.call` in Profile v2, external `MirAssumedStub` callees, or mixed `&` + non-fake `*mut` bodies (`bodyMixesRefsAndRawPtrsV2`, `Boundary.lean:615`).
- **Known not to apply:**
  - Borrowing `&I` under `I: Sync + RefUnwindSafe` does **not** prevent concurrent safe-Rust `Atomic*` TOCTOU without `snapshot_and_eval`.
  - Proving `WellFormedV2` without `CallerMemPreserved` (`mem' = q.callerMem`) on an in-process `Rung 1.5` producer does **not** preserve soundness of `withFallback`.
  - Pre-gate monadic `orElse` over candidate producers does **not** preserve portfolio availability when an earlier producer returns a malformed `.candidate`.

## Evidence

- **Primary source inspection of `google/zerocopy` at `487101d7a5233982e7bd05a1c76e039073ce1702` (inspected `2026-11-27`):**
  - `anneal/trusted/lean/Trusted/Framework.lean` (`L81-93`: `OracleGrade.licenses`; `L110-133`: `ExecutionModel` lacking stub-table parameter in `wellFormed`/`produces`; `L152-198`: `EffectMask`, `FnContract`, `AssumedStub`, `StubRealizable`; `L229-268`: `BodySatisfiesEntry`, `BodySatisfiesStub`; `L405-437`: `EnvelopeTheorem`).
  - `anneal/trusted/lean/Trusted/Framework/Instances.lean` (`L211-286`: `MirProfileV1`, `MirProfileV2`, `bodyIsExternal := fun _ => false`, `mirProfileV2RequiredGaps`) and `Bridge.lean` (`L172-226`: `MirEnvelopeTheoremV1/V2`).
  - `anneal/trusted/lean/Trusted/MirAst/{Body.lean:95-101, Terminators.lean:265-292, Types.lean:154-156, 251-341}` and `Trusted/MirSemantics/{Boundary.lean:605-742, Contract.lean:57-120, CoreContracts.lean:481-511, Step.lean:3742-3800, 4068-4108}`.
  - `anneal/trusted/audit/TrustedBoundary.lean` (`L4003-4010, L7205-7229`: canonical root theorem allowlist) and `anneal/trusted/rustc-capture/src/{capture.rs:1975, extract.rs:2623-2650}`.
  - `anneal/theory/Anneal/{Framework.lean:158-258, Framework/StepWp.lean:49-132, Core/SpecRealizability.lean:187-234, SafeTwin/Equiv.lean:31-77, Generic/OpenSemantics.lean:51-155}`.
  - `zerocopy/src/{byte_slice.rs:214-260, layout.rs:1705-1875, lib.rs:2120-2140}` and `zerocopy/proofs/{README.md, 08_byte_slice_split_at_unchecked/Spec.lean, 14_known_layout_and_dst_layout/Spec.lean}`.
- **Standalone Lean `v4.34.1` mechanization ([`support/HybridArchitecture.lean`](support/HybridArchitecture.lean)):**
  - `478` lines, SHA-256 `a456a51d3e38fcdcebebe52848204e1ea57ed9ea2afe34ea96f3880e53983d12`, paired with [`support/lakefile.toml`](support/lakefile.toml) and [`support/lean-toolchain`](support/lean-toolchain).
  - Executed `2026-11-27` via `elan run leanprover/lean4:v4.34.1 lean -DElab.async=false -DwarningAsError=true HybridArchitecture.lean` (exit `0`, `0` warnings): `3` theorems depend on `[]` axioms (`evalGate_rejects_oversized_without_check`, `rung15_without_callerMemPreserved_unsound`, `hybridRefines_trans`), `7` depend on `[propext]` (`evalGate_sound`, `naive_precheck_orelse_drops_valid_backup`, `firstAccepted_sound`, `withFallback_total_sound`, `foldHintSteps_preserves_inv`, `foldStreamPrefix_all_emitted_valid`, `rung15_with_callerMemPreserved_sound`), and `1` depends on `[Quot.sound]` (`firstAccepted_ok_iff_exists`). Zero `sorryAx` or `Lean.ofReduceBool`.
- **Standalone `#![forbid(unsafe_code)]` Rust and Miri verification suite ([`support/hybrid_arch_verify/`](support/hybrid_arch_verify/Cargo.toml)):**
  - `Cargo.toml` (SHA-256 `bba67cd65d6e460effbf6e2ccf44826a2a33ce8c8dbd313a5e8964ab3d1959a1`), `src/lib.rs` (`473` lines, SHA-256 `9f43e7d8d97696414c0e8b5541c92f3ab1430d865733f508da774fd155d6dc73`).
  - Executed `2026-11-27` under `rustc 1.102.0-nightly` / `miri 0.1.0` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`): `RUSTFLAGS="-D warnings" cargo test --release --offline` (`3 passed; 0 failed; 0 warnings`), `cargo miri test --offline` (`3 passed; 0 failed`, Stacked Borrows), and `MIRIFLAGS="-Zmiri-tree-borrows" cargo miri test --offline` (`3 passed; 0 failed`, Tree Borrows).

## Revalidation

From `reports/hybrid-verified-software-certified-gate-algebra-and-anneal-architecture/support/`:

1. Verify all `11` Lean `v4.34.1` theorems and `#print axioms` footprints (`0` warnings, `0` `sorryAx`):
   ```bash
   elan run leanprover/lean4:v4.34.1 lean -DElab.async=false -DwarningAsError=true HybridArchitecture.lean
   ```
2. Run the Rust release tests and Miri Stacked/Tree Borrows checks in an isolated temporary target directory (so the corpus tree stays clean of `target/` artifacts):
   ```bash
   (cd hybrid_arch_verify && CARGO_TARGET_DIR=/tmp/hybrid_arch_verify_target RUSTFLAGS="-D warnings" cargo test --release --offline && CARGO_TARGET_DIR=/tmp/hybrid_arch_verify_target cargo miri test --offline && CARGO_TARGET_DIR=/tmp/hybrid_arch_verify_target MIRIFLAGS="-Zmiri-tree-borrows" cargo miri test --offline && rm -rf /tmp/hybrid_arch_verify_target)
   ```
3. Re-check Anneal's Ring-0 integration seams on newer `google/zerocopy` revisions by inspecting `Trusted/MirAst/Body.lean` (`isExternal`), `Trusted/MirSemantics/Step.lean` (`evalTerminatorV2` `.call` and external stub stepping), `Trusted/Audit/TrustedBoundary.lean` (`MirEnvelopeTheoremV2`), and `Trusted/MirSemantics/Boundary.lean` (`EffectMaskV2`).
