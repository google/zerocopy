# Unsafe Rust audit: `symbolic-domain-target` 0.1.0

## Claim and verdict

| Claim | Exact theorem | Verdict |
|---|---|---|
| SOUND | For the supplied source and every configuration in `Required`, every well-typed safe call `value_or_zero(value: Option<u8>)` is free of Rust undefined behavior. | **PROVED relative to accepted `COMPAT-OPTION-184-186`** |
| RESULT | Under the same quantification, the function returns `0` for `None` and the contained byte for `Some(b)`. | **PROVED relative to accepted `COMPAT-OPTION-184-186`** |

The combined mandatory result is **PROVED relative to `TCB.md` as supplied**, specifically its conspicuous human-accepted compatibility premise `COMPAT-OPTION-184-186`. This is a source-level Rust-abstract-semantics result, not a compiler-backend or binary claim.

Snapshot: the complete supplied `Cargo.toml`, `SUPPORT.md`, `CI.md`, `TCB.md`, `REQUEST.md`, and `src/lib.rs`; edition 2021, `#![no_std]`, `rust-version = "1.84"`, no Cargo dependencies, build script, generator, or generated artifact. No prior audit or tool-derived evidence was used. Audit cutoff: 2026-08-01. Skill identity: supplied `unsafe-rust` package; no revision was provided.

## Required domain and configuration closure

Let `ReleasedStable(r)` retain its literal policy meaning, `T = {x86_64-unknown-linux-gnu, aarch64-apple-darwin, wasm32-unknown-unknown}`, `F = {telemetry off, telemetry on}`, `D = {debug assertions off, debug assertions on}`, and `P` be the symbolic set of all Cargo profiles. `SUPPORT.md` states exactly:

`Required(r,t,f,p,d) = ReleasedStable(r) ∧ 1.84.0 ≤ r ≤ 1.86.0 ∧ t∈T ∧ f∈F ∧ p∈P ∧ d∈D`.

This is a literal normalization, hence equality in both directions; no release or profile enumeration is substituted. `Cargo.toml` supplies only Cargo's lower acceptance bound, while `SUPPORT.md` expressly controls the project promise including its upper cutoff. `CI.md` samples 1.84.0/x86_64/no-feature and 1.86.0/all targets/both features; it is not support-definition or semantic proof evidence.

Actual source-selection axes are empty: neither `telemetry`, `cfg`, target, profile, nor `debug_assertions` occurs in `lib.rs`. There are no allocator, FFI, assembly, concurrency, macro, dependency, panic, arithmetic, generated-code, or linking obligations in the function. The derivation below is syntactically identical across `t,f,p,d`; accepted `COMPAT-OPTION-184-186` supplies the two consumed `Option` propositions parametrically for every `r,t,p,f,d` in `Required`. Therefore each obligation's `Covered = Required`, their pointwise intersection is `Required`, and `Required ⊆ Covered` follows by identity. The cutoff does not enumerate releases and is not used as continuity evidence.

## Boundary, invariant, and obligation coverage

The only language-reachable crate surface is the public safe free function `value_or_zero` (`src/lib.rs:3-12`). There are no public fields, constructors of an owned representation, methods, traits/impls, reexports, macros, hidden items, statics, callbacks, FFI entrypoints, or custom destruction. The sole unsafe operation is `Option::unwrap_unchecked` at line 11. No persistent representation invariant exists. The transient fact `INV-NONNONE` is: after the `if value.is_none() { return 0; }` fallthrough, `value` is not `None`; the branch produces it and line 11 consumes it.

| ID | Obligation and proof | Domain | Status |
|---|---|---|---|
| O1 | `is_none` classifies `None` exactly. This is the accepted preserved base proposition; the true branch returns before line 11. | `Required` | PROVED, TCB-relative |
| O2 | `unwrap_unchecked` is not called on `None`. Reaching line 11 means `is_none()` was false; O1 gives `INV-NONNONE`, exactly discharging the unsafe call's condition. | `Required` | PROVED, TCB-relative |
| O3 | Result: on `None`, O1 takes the branch and returns `0`; on `Some(b)`, O1 falls through and the accepted `unwrap_unchecked(Some(b)) = b` proposition returns `b`. These cases exhaust `Option<u8>`. | `Required` | PROVED, TCB-relative |
| O4 | Configuration closure. Source and control flow are independent of every non-release axis, and the accepted premise covers the complete symbolic release predicate and all stated axes. | `Required` | PROVED, TCB-relative |

The adjacent `SAFETY` comment is adequate: it names the dominating `None` return, derives `Some` at the call, and identifies that fact as `unwrap_unchecked`'s precondition. The proof above exposes the otherwise project-level version/configuration premise. Every normal exit re-establishes the result contract; there is no mutation, unwind point, callback, aliasing, allocation, or retained capability.

## TCB audit log

Log identity: supplied `TCB.md`, reviewed for this audit; disposition **accepted by the authorized human reviewer**.

| ID/category | Exact proposition, identity, scope, consumers | Disposition and limits |
|---|---|---|
| BASE-OPTION-184 / AXIOM | Rust 1.84.0 [`is_none`](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.is_none) says it returns true for `None`; [`unwrap_unchecked`](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_unchecked) returns the contained `Some` value and makes `None` undefined behavior. Base for O1-O3. | Version-matched authoritative base text inspected. |
| COMPAT-OPTION-184-186 / accepted compatibility premise | Without weakening, qualification, or added precondition, preserves exactly: (1) `is_none` is true exactly for `None`; (2) `unwrap_unchecked(Some(v))` returns `v`, and calling it on `None` is UB; for every released stable `r` in the inclusive interval, all supported targets/profiles, either feature state, and either debug-assertion state. Consumers: only O1-O3 and the two verdicts. | **Accepted.** Establishes neither interval membership, Cargo facts, other APIs, backend correctness, nor emitted binaries. Re-audit on any source, interval, base-proposition, feature/target-scope, or disposition change. |

No other compatibility, dependency, implementation, environment, probabilistic, or tool premise is consumed. The selected premise does not assume the in-scope implementation conclusion; it only transports two standard-library contracts across the exact symbolic domain.

## Findings, residual scope, and triggers

All in-scope obligations have complete derivations; there is no `UNPROVED`, `UNSOUND`, `CONTRACT-BROKEN`, proof-documentation, authoritative-documentation, or skill-guidance finding. Broader robustness, binary correctness, backend/linker behavior, and unsupported configurations were not claimed or audited. Re-audit is required if any supplied source or contract changes; `Required` expands or changes; the authoritative base text or accepted TCB disposition changes; generated code, dependencies, or configuration-sensitive code appears; or a new consumer relies on the premise.

Auditor: source-review agent. Independent review: not performed.
