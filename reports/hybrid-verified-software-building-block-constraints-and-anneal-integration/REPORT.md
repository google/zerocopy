# Hybrid Verified Software Building Blocks: Producer–Checker Constraint Matrix, Isolation Seams, and Anneal Integration

## Summary

Composing an unverified or partially verified producer `f` with a formally verified checker `V` (and optional verified fallback `fb`) into a reusable building block requires aligning six problem-shape variants and three isolation regimes with exact minimal producer and checker constraints. Combining primary-source analysis of `google/zerocopy` (`487101d7a5233982e7bd05a1c76e039073ce1702`), a standalone 11-theorem Lean `v4.34.1` mechanization ([`support/HybridBuildingBlock.lean`](support/HybridBuildingBlock.lean), `445` lines, `0` `sorryAx`), and standalone `#![forbid(unsafe_code)]` Rust and Miri probes ([`support/hybrid_bb_probes/src/lib.rs`](support/hybrid_bb_probes/src/lib.rs), `rustc 1.102.0-nightly` / `miri 0.1.0`) establishes five core results:

1. **Isolation Necessity and Completeness Asymmetry (`unisolated_assumed_stub_leaks_effects`, `contained_stub_with_direct_fallback_total_normal`, `runtime_checked_fallback_requires_v_completeness`):** Wrapping an unisolated `partialAnyExit` (`(false, false, false)`) external producer directly with a total `(true, true, true)` checker and fallback fails outer `EffectMask.totalNormal` across `.unwound`, `.aborted`, and `.diverged` exits. Sealing the producer inside an isolation boundary restores `(true, true, true)` totality **without requiring completeness of `V` on `fb`**, whereas re-checking `fb` via runtime `assert!(V(x, fb(x)))` introduces `.aborted` failures whenever `V` is sound-but-incomplete on `fb`.
2. **Hard Containment Limits of `#![forbid(unsafe_code)]` + `catch_unwind` and Safe Shared-Memory TOCTOU (`test_double_panic_drop_bypasses_catch_unwind`, `test_shared_atomic_toctou_vs_copy_and_verify`):** Even inside `#![forbid(unsafe_code)]`, a safe `Drop` guard that panics while unwinding inside `std::panic::catch_unwind` immediately aborts the host process (`SIGABRT` / non-zero abnormal exit), proving in-process `catch_unwind` cannot establish `noAbort = true`. Under both default Miri (Stacked Borrows) and `-Zmiri-tree-borrows` (`0` UB), concurrent `&AtomicU64` writes defeat naive in-place checks (`10 < 100` -> `999`), whereas RLBox-style single-fetch `copy_and_verify` into capability-sealed `Checked<T, Spec>` prevents post-check mutation.
3. **Witness-Bomb Resource Bounds, Streaming Commit Safety, and Cross-Call Noninterference (`unbounded_witness_checker_fails_totality`, `prechecked_size_capped_checker_total`, `streaming_premature_commit_unsound`, `prefix_checked_streaming_sound`, `stateful_producer_cross_call_leak_despite_sound_checker`):** A sound checker without an $O(1)$ pre-allocation witness cap fails finite-fuel totality on oversized untrusted witnesses; unbuffered streaming leaks invalid prefix chunks before end-of-stream rejection; and a stateful producer behind a sound checker and uniquely determined output spec still leaks secrets across sequential calls via private state poisoning unless reset per call under a fixed step budget.
4. **`Result<T, E>` Availability-Monotone Ratcheting (`resultWrap_sound`, `ratchet_result_preserves_outer_safety_and_availability`) and Rung 1.5 (`WellFormed`-Only `unsafe` Producers):** Ratcheting `Result<T, E>` / `Option<T>` hybrid components preserves outer caller safety and availability whenever `AvailabilityRefines` holds, and Anneal's separation between `WellFormed` (memory/UB safety) and functional postconditions admits a Rung 1.5 architecture where an `unsafe` or SIMD producer proves `WellFormed` only while a verified checker proves functional correctness without runtime sandboxing overhead.
5. **Exact Integration Surface and Blocking Gaps in Anneal (`google/zerocopy@487101d7a523`):** `Trusted.Framework` (`Trusted/Framework.lean`) provides the 3-bit `EffectMask`, `FnContract`, `AssumedStub`/`StubRealizable`, `DisclosedGap`, and `MirEnvelopeTheoremV1/V2` vocabulary, alongside `Option<T>` in Profile v2 (`CoreContracts.lean`) and `BoolCertCut`/`SafeTwin`/`BitTrieLrat`/`LinearArith`/`AiPcc` in `0`-TCB `theory/Anneal/`. However, four concrete codebase gaps block immediate generic combinator verification on `487101d7a523`: `MirProfileV1`/`MirProfileV2` hardcode `bodyIsExternal := (fun _ => false)` and `TrustedBoundary.lean` does not yet admit `MirEnvelopeTheoremV1/V2`; `MirTy` lacks `Result<T, E>`, `FnPtr`/`Closure`, and 0-variant `Infallible` (`enumAdmitted`); Profile v2 forbids intra-crate `TerminatorKind::call` and mixed `&`/`*mut` locals; and `EffectMask` differs across `Trusted.Framework`, `Contract.lean`, and `SafeContractV2`.

*Model–system relation note:* Theorems in [`support/HybridBuildingBlock.lean`](support/HybridBuildingBlock.lean) mechanize an abstract functional and 4-outcome effect model in pure Lean 4 (`namespace HybridBB`) rather than extracting Rust MIR operational steps; mappings to `Trusted.Framework`, `MirSemantics`, and Rust runtime behavior are explicitly marked `Basis: derived` or grounded directly in [`support/hybrid_bb_probes/src/lib.rs`](support/hybrid_bb_probes/src/lib.rs).

## Applicability

- **Anneal and `zerocopy` baseline (`google/zerocopy` at `487101d7a5233982e7bd05a1c76e039073ce1702`):** Applies to `anneal/trusted/lean/Trusted/{Framework.lean, Framework/Instances.lean, Framework/Bridge.lean, MirAst/Types.lean, MirAst/Terminators.lean, MirModel.lean, MirSemantics/{Boundary.lean, Contract.lean, CoreContracts.lean}}`, `anneal/trusted/audit/TrustedBoundary.lean`, `anneal/theory/Anneal/{Framework.lean, Framework/StepWp.lean, SafeTwin/Equiv.lean, Core/SpecRealizability.lean, Generic/{TypeSpec.lean, OpenSemantics.lean}}`, `anneal/docs/{alpha.md, architecture.md, spec-core-and-golden-closure.md, trust-model.md}`, and `zerocopy/src/{byte_slice.rs, layout.rs, lib.rs}`.
- **Mechanized Lean 4 model ([`support/HybridBuildingBlock.lean`](support/HybridBuildingBlock.lean)):** Checked under `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) using core `Init` only (`0` external dependencies, `0` warnings under `-DwarningAsError=true`, `0` `sorryAx`, axioms strictly within `{propext, Quot.sound}`).
- **Rust and Miri probes ([`support/hybrid_bb_probes/`](support/hybrid_bb_probes/Cargo.toml)):** `#![forbid(unsafe_code)]` Rust 2021 crate with zero external crate dependencies, executed under `rustc 1.102.0-nightly` / `miri 0.1.0` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, LLVM `23.1.5`) on `x86_64-unknown-linux-gnu` (`--release --offline`, default Stacked Borrows Miri, and `-Zmiri-tree-borrows`).
- **Relationship to sibling corpus reports:** Extends `hybrid-verified-software-contracts-fallback-and-ratcheting` (`Option<T>` contract algebra and 4-rung TCB ladder), `hybrid-verified-software-hazards-ub-toctou-and-hyperproperties` (`unsafe` Miri bypasses, `Cell` TOCTOU, `TrojanOrd`, and 3 hyperproperty channels), `hybrid-verified-software-rust-lean-prototype-and-benchmarks` (SSSP/Deflate/Anneal prototypes), and `hybrid-verified-software-taxonomy-and-roi-boundaries` (benefit taxonomy and ROI crossovers) by deriving the full problem-shape × substrate constraint matrix, new Lean/Rust failure modes (completeness asymmetry, witness-bomb caps, double-panic aborts, concurrent atomic TOCTOU, streaming commit, cross-call stateful leaks), and concrete `google/zerocopy@487101d7a523` integration requirements.

## Findings

### 1. Problem-Shape and Substrate Taxonomy

`Basis: documentation + source + derived`

Reusable hybrid producer–checker components span six distinct structural patterns (`S1`–`S6`), differing in whether checking requires the input `x`, an auxiliary witness `W`, stepwise loop coupling, or prefix invariants:

| Shape | Producer / Checker Interface | Soundness Condition | Key Structural Hazard | Representative Domains |
| :--- | :--- | :--- | :--- | :--- |
| **`S1` Output-Only Predicate** | `f(x) -> T`; `V(y) -> Bool` | `V(y) = true -> P(y)` | Omits input-output relation (`is_sorted(y)` ignoring input multiset) | Byte-validity checks (`TryFromBytes`), UTF-8/format checks |
| **`S2` Witness-Free Relational** | `f(x) -> T`; `V(x, y) -> Bool` | `V(x, y) = true -> R(x, y)` | Relational non-uniqueness enables covert steganography and non-determinism | `isqrt`, linear residual `Ax == b`, `DstLayout::validate_cast_and_convert_metadata`, `split_at` bounds |
| **`S3` Explicit Witness `(T, W)`** | `f(x) -> (T, W)`; `V(x, y, w) -> Bool` | `V(x, y, w) = true -> R(x, y)` | Witness-bomb DoS (`|w| >> |x|`) and derived-field trust (`I2`) | Farkas/CG (`LinearArith`), LRAT (`BitTrieLrat`), `regalloc2`, SSSP potentials+rank, LZ77+Kraft |
| **`S4` Interleaved Hint Loop** | `h_i = f_step(s_i)`; `V_step(s_i, h_i) -> Option<s_{i+1}>` | `V_step(s, h) = some s' -> Inv(s, s')` | Structural hint drift and shared state mutation between `f_step` and `V_step` | Compiler pass/regalloc oracles, DPLL branching + RUP check, AI-PCC fixpoints |
| **`S5` Streaming / Incremental** | `f` emits `[c_0, c_1, ...]`; `V_step(acc, c_i)` or buffered `V_full` | Every emitted prefix `p` satisfies `PrefixSafe(p)` | Premature unbuffered emission violates invariants before end-of-stream rejection | Streaming decompression, incremental packet/frame demuxers |
| **`S6` Portfolio + Fallback** | `[f_1, ..., f_k]`, `V`, verified `fb` | Isolated `f_i`, sound `V`, directly verified `fb` | `assert!(V(fb))` completeness abort; racing non-determinism across valid outputs | SIMD/AI/heuristic fast paths + verified scalar fallback |

### 2. Minimal Producer vs. Checker Constraint Matrix

`Basis: execution + source + derived` ([`support/HybridBuildingBlock.lean`](support/HybridBuildingBlock.lean), [`support/hybrid_bb_probes/src/lib.rs`](support/hybrid_bb_probes/src/lib.rs))

The minimal constraints required on `f` and `V` depend jointly on the target guarantee `(a)`–`(f)` and the isolation substrate:

| Target Guarantee | In-Process `unsafe` / C / ASM (Unisolated) | In-Process Safe Rust (`#![forbid(unsafe_code)]`) | Isolated Sandbox (Wasm / RLBox / Process) | Minimal Constraints on `V` (and `fb`) |
| :--- | :--- | :--- | :--- | :--- |
| **(a) Memory safety (`WellFormed`)** | Unattainable by post-check alone unless `f` proves `WellFormed` (Rung 1.5) | `#![forbid(unsafe_code)]` across `f` + transitive deps; clean `build.rs`/proc-macros; `copy_and_verify` over `&Cell`/`&Atomic*` | Sandbox enforces SFI/MMU isolation; host copies ABI payload once before checking | `V` (and `fb`) satisfy `WellFormed` unconditionally on arbitrary inputs |
| **(b) Partial correctness (`Some`/`Ok` -> `R`)** | Requires (a) | Owned/snapshot `(x, y, w)` (`Freeze + Sync + RefUnwindSafe`); `catch_unwind` if `noUnwind = true`; **still cannot guarantee `noAbort = true`** | `copy_and_verify` from sandbox memory; map trap/timeout to `None`/`Err` | `CheckerSound` (`V = true -> R`); concrete/law-bound types; panic/abort-free if `noUnwind`/`noAbort` claimed |
| **(c) Total availability (`terminates ∧ noUnwind ∧ noAbort`)** | Requires (a) + termination/abort isolation | Impossible for arbitrary untrusted `f` (`Drop` double-panic, OOM, stack overflow, loops) without static `EffectMask.totalNormal` or `#![no_std]` fallible alloc + fuel | Host fuel + memory limit + watchdog + sandbox reset, paired with verified `fb` | `V` total `(true, true, true)` (`size_capped`); `fb` proved `R(x, fb(x))` directly (avoiding runtime `assert!(V(fb))`) |
| **(d) Determinism** | Requires (a)–(c) | Unique `R` or canonicalized `V`, plus fallback agreement if timeout/panic can switch `f` vs. `fb` | Deterministic instruction/fuel cap (not wall-clock timeout) | `ContractDeterministic` or canonical tie-breaker `Canon(x, y)` |
| **(e) Resource bounds** | OS watchdog only | Cooperative fuel + fallible bounded arena + `-Z emit-stack-sizes`; no forced preemption in-process | Wasm fuel / cgroup `MemoryMax` / rlimit / deadline watchdog | **`V` caps `|w|` in $O(1)$ before allocating/traversing**; worst-case SLA on `fb` |
| **(f) Non-interference** | Unenforceable across shared address space | `#![no_std]` + closed `extern` + ELF `noSyscalls`; total fallback; unique `R`; secret-blind `f` or post-link CT; **per-call state reset** | Separate MMU trust domain (`CR3`/`TTBR0`) against Spectre; fixed budget padding; sandbox state reset | Deterministic `V`, constant-time on secret witnesses, zero witness leakage in `Err(e)` |

### 3. Five New Mechanized Theorems and Empirical Counterexamples

`Basis: execution` ([`support/HybridBuildingBlock.lean`](support/HybridBuildingBlock.lean), [`support/hybrid_bb_probes/src/lib.rs`](support/hybrid_bb_probes/src/lib.rs))

1. **Assumed-Stub Isolation Necessity vs. Direct Fallback (`HybridBuildingBlock.lean:56-147`):**
   - `unisolated_assumed_stub_leaks_effects` (`[]`) exhibits explicit counterexamples where a `partialAnyExit` stub (`(false, false, false)`) behind a `100%`-sound checker `V` and `100%`-correct fallback `fb` violates `EffectMask.totalNormal` via `.unwound`, `.aborted`, and `.diverged`.
   - `contained_stub_with_direct_fallback_total_normal` (`[propext]`) proves that an isolation boundary `Iso` collapsing non-normal producer exits to `.failed` without mutating state `st`, paired with `CheckerSound V` and `∀ st x, pre st x -> post st x (fb st x).1 (fb st x).2`, achieves `EffectMask.totalNormal` `(true, true, true)` without requiring completeness of `V`.
2. **Fallback Runtime-Check Completeness Trap (`runtime_checked_fallback_requires_v_completeness`, `HybridBuildingBlock.lean:171-190`, `[]`):**
   - If a wrapper runtime-checks `fb` via `V` and aborts on `false` (`assert!(V(x, fb(x)))`), a sound-but-incomplete checker (`incompleteV _ x y _ := y == x + 1` against `R _ x y _ := x <= y`) combined with valid fallback `fb _ x := x` reaches `.aborted`, falsifying `noAbort = true`.
3. **Witness-Bomb Resource Exhaustion (`unbounded_witness_checker_fails_totality`, `[]` vs. `prechecked_size_capped_checker_total`, `[Quot.sound]`; `test_witness_bomb_cap_rejects_in_o1`):**
   - Any fuel-bounded checker lacking a witness-size gate returns `.outOfBudget` on witness `B + 1` for any budget `B`; pre-checking `wSize w <= maxSize` in $O(1)$ (`check_witness_bounded` in `lib.rs:182-196`) guarantees `.decided` within `maxSize + 1` steps.
4. **Safe-Rust `Drop` Double-Panic Bypass & Shared-Atomic TOCTOU (`lib.rs:171-180, 254-339`):**
   - `test_double_panic_drop_bypasses_catch_unwind` (executed under `--release --offline`): inside `#![forbid(unsafe_code)]`, a `Drop` impl panicking while unwinding inside `std::panic::catch_unwind` aborts the child process abnormally (`!status.success()`), proving `catch_unwind` cannot contain aborts from safe producers.
   - `test_shared_atomic_toctou_vs_copy_and_verify` (passing `--release`, Stacked Borrows Miri, and `-Zmiri-tree-borrows` with `0` UB): `naive_check_atomic_in_place(&AtomicU64)` passes `< 100` on `10` before a concurrent thread writes `999`; `trust_core::copy_and_verify` (single-fetch `Ordering::Acquire` snapshot into owned private `Checked<u64, Spec>`) defeats concurrent mutation without `unsafe`.
5. **Streaming Premature Commit, Cross-Call Stateful Leaks, and `Result<T, E>` Ratcheting (`HybridBuildingBlock.lean:268-425`):**
   - `streaming_premature_commit_unsound` (`[propext, Quot.sound]`) proves forwarding chunk `[99]` before end-of-stream check `[99, 0]` violates `PrefixSafe [99]`; `prefix_checked_streaming_sound` (`[]`) shows per-chunk `V_step` checking restores prefix safety across arbitrary truncation.
   - `stateful_producer_cross_call_leak_despite_sound_checker` (`[]`) proves a stateful producer behind a sound checker and uniquely determined spec `y = p` still leaks Call 1's `secret` via Call 2's step count; `stateless_reset_plus_unique_budgeted_cross_call_ni` (`[propext]`) closes the channel via per-call state reset, fixed budget, and unique `Spec`.
   - `resultWrap_sound` (`[propext]`) and `ratchet_result_preserves_outer_safety_and_availability` (`[]`) prove that upgrading any `Except E Y` (`Result<Y, E>`) hybrid stage under `AvailabilityRefines` preserves outer caller safety and `.ok` availability verbatim.

### 4. Exact Grounding and Blocking Gaps in Anneal (`google/zerocopy@487101d7a523`)

`Basis: source + derived`

Inspecting `google/zerocopy` at `487101d7a5233982e7bd05a1c76e039073ce1702` identifies the exact assets and missing seams for a first-class hybrid building block:

| Layer / Module | Current State on `487101d7a523` | Exact Gap for Hybrid Building Blocks |
| :--- | :--- | :--- |
| **`Trusted.Framework` (`Trusted/Framework.lean`, `Instances.lean`, `Bridge.lean`)** | Defines 3-bit `EffectMask { terminates, noUnwind, noAbort }`, `FnContract`, `AssumedStub`/`StubRealizable`, `DisclosedGap`, `MirProfileV1/V2`, and `MirEnvelopeTheoremV1/V2`. | `MirProfileV1` (`Instances.lean:218`) and `MirProfileV2` (`Instances.lean:275`) both set `bodyIsExternal := (fun _ => false)`, forcing `stubs = []` (`Anneal.Framework.no_stubs_of_all_local_model`), and `TrustedBoundary.lean:4007, 7205` admits only `{Crate,Unit}Theorem{,V2}`, blocking `MirAssumedStub` and `MirEnvelopeTheoremV1/V2`. |
| **`Contract.lean` vs. `SafeContractV2` (`Boundary.lean`)** | `Trusted.MirSemantics.Contract.EffectMask` has `{terminates, noUnwind}` (no abort); `SafeContractV2.EffectMaskV2` has `{allowAbort}` only. | Three distinct `EffectMask` definitions exist across `Trusted.Framework`, `Contract.lean`, and `Boundary.lean`; Profile v2 lacks `terminates` and `noUnwind` fields in `SafeContractV2`. |
| **`MirTy` & Profile v2 Calls (`Types.lean`, `CoreContracts.lean`, `alpha.md`)** | Profile v2 models non-nested `Option<T>` (`Option::{is_some, is_none, take, unwrap}`), `&[T]`/`&mut [T]`/`*const T`/`*mut T`, and unmodified `<&[u8] as SplitByteSlice>::split_at_unchecked`. | `MirTy` lacks `Result<T, E>`, `FnPtr`/`Closure`, and 0-variant `Infallible` (`enumAdmitted` refuses 0-variant enums at `Types.lean:154`); Profile v2 refuses intra-crate `TerminatorKind::call` and mixed `&`/`*mut` locals (`bodyMixesRefsAndRawPtrsV2`). Generic higher-order wrappers (`verify_opt(f, v)`) cannot be captured verbatim today. |
| **Open-Generic Traits (`Anneal.Generic`)** | `TraitMethodSpec` + `AssumeGuaranteeTraitCall` (`0`-TCB prototype in `theory/Anneal/Generic/`) with 8 documented gaps (`OpenSemantics.lean:51-145`). | Not promoted to `trusted/` and has no Rust attribute (`#[anneal::trait_spec]`) lowering yet. |
| **Reusable `0`-TCB `theory/Anneal/` Modules** | Ships `BoolCertCut`, `SafeTwin` (`SafeTwinQueryEquiv`, `LeakNonInterference`), `BitTrieLrat`, `LinearArith`, `AiPcc`, `SpecRealizability`, and `MirSymExecCall` in `theory/bundle-manifest.json`. | Ready to check reflective certificates (`BoolCertCut`), uniqueness (`ContractDeterministic`), and equivalence (`SafeTwin`) without increasing TCB. |

**Rung 1.5 Discovery (`WellFormed`-Only `unsafe` Producer):** Because Anneal proves `WellFormed` (UB-freedom) even when `postReturn := True` (`BodyVerified` / `BodyVerifiedV2`), an `unsafe` Rust or SIMD fast path can discharge memory safety inside Anneal (Rung 1.5) while delegating functional correctness to a verified checker `V`, eliminating sandbox/IPC overhead without proving functional correctness of the complex fast path.

## Boundaries

- **Not examined:**
  - Formal Lean-to-Rust extraction or equivalence linking [`support/HybridBuildingBlock.lean`](support/HybridBuildingBlock.lean) directly to `Trusted.MirSemantics.evalStepV2` or compiled LLVM machine code.
  - Multi-threaded preemption and weak-memory (`Ordering::Relaxed`/acquire-release fence) models inside Anneal (`Trusted.MirSemantics` models single-threaded execution assuming thread isolation, recorded via `DisclosedGap.callerMemoryThreadIsolation` in `Trusted/Framework/Instances.lean:250`).
  - Hardware transient-execution (Spectre) containment inside in-process Wasm/SFI sandboxes (`known not to apply` without separate MMU/VM trust-domain isolation).
- **Unknown:**
  - Concrete runtime latency and memory overhead of `cargo-anneal` verification when `MirEnvelopeTheoremV2` and `MirAssumedStub` are eventually enabled in `TrustedBoundary.lean` (blocked by current `bodyIsExternal := false` and root allowlist limits).
- **Unsupported in `google/zerocopy@487101d7a523`:**
  - Capturing `Result<T, E>`, `Result<T, Infallible>`, closures/`FnPtr` combinators, intra-crate calls in Profile v2, or mixed `&mut [u8]` + `*mut u8` bodies (`<&mut [u8] as SplitByteSlice>::split_at_unchecked`).
- **Known not to apply:**
  - In-process `#![forbid(unsafe_code)]` + `std::panic::catch_unwind` cannot enforce `EffectMask.noAbort = true` or `terminates = true` against arbitrary safe Rust producers due to `Drop` double-panic aborts, stack overflow, OOM aborts, and unbounded loops.

## Evidence

- **Primary source inspection of `google/zerocopy` at `487101d7a5233982e7bd05a1c76e039073ce1702` (inspected `2026-11-27`):**
  - `anneal/trusted/lean/Trusted/Framework.lean` (`L50-440`: `TerminalOutcome`, `ClaimShape`, `OracleGrade`, `DisclosedGap`, `ExecutionModel`, 3-bit `EffectMask`, `FnContract`, `AssumedStub`, `StubRealizable`, `VerificationEnvelope`, `EnvelopeTheorem`).
  - `anneal/trusted/lean/Trusted/Framework/Instances.lean` (`L139-302`: `MirProfileV1`, `MirProfileV2`, `bodyIsExternal := fun _ => false`, `mirProfileV2RequiredGaps`, `MirAssumedStub`) and `Bridge.lean` (`L172-227`: `MirEnvelopeTheoremV1`, `MirEnvelopeTheoremV2`).
  - `anneal/trusted/audit/TrustedBoundary.lean` (`L3836-4008, L7205-7228`: admitted Pass-1 root allowlist).
  - `anneal/trusted/lean/Trusted/MirAst/Types.lean` (`L154-156, L323-341`: `EnumTagRepr`, `MirTy`), `Trusted/MirSemantics/Boundary.lean` (`L694-741`: `EffectMaskV2`, `SafeContractV2`), `Trusted/MirSemantics/Contract.lean` (`L57-80`), `Trusted/MirSemantics/CoreContracts.lean` (`L481-511`: `Option` ops).
  - `anneal/theory/Anneal/Framework.lean` (`L153-171`: `no_stubs_of_all_local_model`), `Framework/StepWp.lean` (`L49-131`: `BoolCertCut`), `Generic/OpenSemantics.lean` (`L51-155`), `tests/cargo-anneal/tests/profile_v2_e2e.rs` (`L338-374`: verbatim `zerocopy` `split_at_unchecked` pass/refusal).
  - `zerocopy/src/byte_slice.rs` (`L214-260`), `zerocopy/src/layout.rs` (`L1705-1760`: `DstLayout::validate_cast_and_convert_metadata`), `zerocopy/src/lib.rs` (`L2120-2142`: `TryFromBytes::try_ref_from_bytes`).
- **Standalone Lean `v4.34.1` mechanization ([`support/HybridBuildingBlock.lean`](support/HybridBuildingBlock.lean)):**
  - `445` lines, SHA-256 `7ae6b9fa4dae95959f4a4d232c2a7647ea4518196e183916d0a8ac98e36f0a82`, paired with [`support/lean-toolchain`](support/lean-toolchain) and [`support/lakefile.toml`](support/lakefile.toml).
  - Executed `2026-11-27` with `elan run leanprover/lean4:v4.34.1 lean -DElab.async=false -DwarningAsError=true HybridBuildingBlock.lean` (exit `0`, zero warnings): `6` theorems depend on `[]` axioms (`unisolated_assumed_stub_leaks_effects`, `runtime_checked_fallback_requires_v_completeness`, `unbounded_witness_checker_fails_totality`, `prefix_checked_streaming_sound`, `stateful_producer_cross_call_leak_despite_sound_checker`, `ratchet_result_preserves_outer_safety_and_availability`), `3` depend on `[propext]` (`contained_stub_with_direct_fallback_total_normal`, `stateless_reset_plus_unique_budgeted_cross_call_ni`, `resultWrap_sound`), `1` depends on `[Quot.sound]` (`prechecked_size_capped_checker_total`), and `1` depends on `[propext, Quot.sound]` (`streaming_premature_commit_unsound`). Zero `sorryAx` or `Lean.ofReduceBool`.
- **Standalone Rust and Miri probes ([`support/hybrid_bb_probes/`](support/hybrid_bb_probes/Cargo.toml)):**
  - `Cargo.toml` (SHA-256 `54015eecc4d3e4a7a6a3386a92f97f0afc72d3afc4b3c606f37ebed5c0f07431`), `src/lib.rs` (SHA-256 `d9f200ddc80126cce7e45b1b3d0075f40dd5931e9738c132daa95f8976c6dd7a`).
  - Executed `2026-11-27` under `rustc 1.102.0-nightly` / `miri 0.1.0` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`): `cargo test --release --offline`: `4 passed; 0 failed` (including `test_double_panic_drop_bypasses_catch_unwind` verifying child process abnormal abort); `cargo miri test --offline -- --skip test_double_panic_drop_bypasses_catch_unwind`: `3 passed; 0 failed` under both default Stacked Borrows (`9.10s`) and `-Zmiri-tree-borrows` (`8.92s`).
- **Prior literature (`documentation`):** Narayan et al., *RLBox: Retrofitting Fine Grain Isolation in the Firefox Renderer*, USENIX Security 2020 (`tainted<T>` + `copy_and_verify`); Blum & Kannan (J. ACM 1995) and McConnell et al. (CSRev 2011) on certifying algorithms; Leroy (J. Autom. Reason. 2009) and Tristan & Leroy (POPL 2008) on CompCert validators; Gäher et al., *RefinedRust*, PACMPL 8 (PLDI 2024).

## Revalidation

From `reports/hybrid-verified-software-building-block-constraints-and-anneal-integration/support/`:

1. Verify all `11` Lean `v4.34.1` theorems and `#print axioms` output (`0` warnings, `0` `sorryAx`):
   ```bash
   elan run leanprover/lean4:v4.34.1 lean -DElab.async=false -DwarningAsError=true HybridBuildingBlock.lean
   ```
2. Verify all Rust release probes (including `Drop` double-panic abort) and Miri Stacked/Tree Borrows concurrency probes:
   ```bash
   cd hybrid_bb_probes
   cargo test --release --offline
   cargo miri test --offline -- --skip test_double_panic_drop_bypasses_catch_unwind
   MIRIFLAGS="-Zmiri-tree-borrows" cargo miri test --offline -- --skip test_double_panic_drop_bypasses_catch_unwind
   ```
3. Check whether Anneal's blocking gaps on `google/zerocopy` (`Trusted/Framework/Instances.lean`, `TrustedBoundary.lean`, `Trusted/MirAst/Types.lean`, and `Trusted/MirSemantics/Boundary.lean`) have changed on a newer commit by grepping for `bodyIsExternal`, `MirEnvelopeTheoremV2`, `Result`, and `EffectMaskV2`.
