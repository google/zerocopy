# Unsafe Rust audit: supplied `symbolic-domain-target` snapshot

## Claims and verdicts

**Soundness theorem.** For every well-typed safe call to `value_or_zero` in every supported configuration defined below, execution is free of Rust undefined behavior under the documented Rust abstract semantics.

**Soundness verdict: PROVED, relative to accepted TCB entry `COMPAT-OPTION-184-186`.** That qualification is material: the proof consumes both propositions preserved by that entry throughout the complete supported Rust/configuration domain.

**Documented-behavior theorem.** In the same domain, `value_or_zero(None) == 0`, and for every `b: u8`, `value_or_zero(Some(b)) == b`.

**Documented-behavior verdict: PROVED, relative to accepted TCB entry `COMPAT-OPTION-184-186`.** Combined mandatory result: **PROVED relative to `COMPAT-OPTION-184-186`**. No conditional application or binary claim is made.

## Snapshot and supported set

Scope is the complete supplied source snapshot: package `symbolic-domain-target` 0.1.0, edition 2021, `rust-version = "1.84"`, `#![no_std]`, manifest, policy, CI, and TCB files. There are no dependencies, lockfile, build script, generated source, macros, FFI, assembly, allocator selection, concurrency, or prior audit.

`Supported(c)` means: `c` uses a released stable Rust toolchain `r` with `1.84.0 <= r <= 1.86.0`; target is exactly `x86_64-unknown-linux-gnu`, `aarch64-apple-darwin`, or `wasm32-unknown-unknown`; `telemetry` is either disabled or enabled; Cargo profile is arbitrary; and debug assertions are either disabled or enabled. `SUPPORT.md`, including its upper cutoff, is controlling. `Cargo.toml` only supplies Cargo's lower acceptance bound. `CI.md` is sampling evidence and neither defines nor proves support.

This audit uses the policy predicate parametrically; it need not guess or freeze the interval's patch-release membership. Source identity is the supplied files, with an audit cutoff of this review. Unlisted configurations are outside the claimed theorem by the explicit support commitment; no build-time rejection is claimed.

## Boundary, surfaces, and invariant

The sole crate API surface is safe public function `value_or_zero(Option<u8>) -> u8`. It has no public fields, constructors, traits/impls, associated items, reexports, hidden items, statics, callbacks, operators, custom destruction, or configuration-generated variants. The sole unsafe operation is the internal call to `Option::unwrap_unchecked`; there is no public unsafe API and therefore no caller safety obligation.

`INV-BRANCH`: at the unsafe call, the unchanged local `value` is `Some(b)` for some `b`. Its owner is the function's straight-line control flow. The `is_none` check establishes it on the fallthrough edge; no mutation, callback, or other intervening operation can suspend it; `unwrap_unchecked` consumes it.

## Obligation ledger and reconstructed proof

| ID | Exact obligation and derivation | Domain | Status |
|---|---|---|---|
| OBL-1 | `value.is_none()` is true exactly when `value` is `None`. This is the base [`is_none` contract](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.is_none), whose relevant text is “Returns true if the option is a `None` value,” carried over the domain by `COMPAT-OPTION-184-186`. | All `Supported(c)` | PROVED relative to the TCB entry |
| OBL-2 | On fallthrough, the check returned false. By OBL-1 and `Option`'s two variants, `value = Some(b)`. `is_none` only borrowed the by-value local, and no transition follows, establishing `INV-BRANCH`. | All inputs/configurations | PROVED relative to the TCB entry |
| OBL-3 | [`unwrap_unchecked`](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_unchecked) requires non-`None`; its safety text says calling it on `None` is undefined behavior. OBL-2 proves the precondition. `COMPAT-OPTION-184-186` additionally preserves that `unwrap_unchecked(Some(b))` returns `b`. | All fallthrough executions in `Supported(c)` | PROVED relative to the TCB entry |
| OBL-4 | If the check is true, OBL-1 gives `None` and the explicit return yields 0 without unsafe execution. If false, OBL-2/3 give `Some(b)` and result `b`. These exhaustive paths prove the documented result. | All safe inputs/configurations | PROVED relative to the TCB entry |

The derivation is uniform across targets, releases, features, profiles, and assertion states: the source contains no `cfg`, feature use, target branch, assertion, overflow, allocation, or profile-sensitive operation. The accepted TCB proposition expressly quantifies over every supported value of those axes, so their Cartesian product is closed by the same proof.

## TCB audit log

| ID | Disposition | Exact consumed proposition | Consumers / limitations |
|---|---|---|---|
| `COMPAT-OPTION-184-186` | Accepted by the authorized human reviewer | For every released stable `r` in 1.84.0–1.86.0 and all supported targets/profiles/feature/assertion states, Rust preserves: `is_none` is true exactly for `None`; `unwrap_unchecked(Some(v))` returns `v`; calling it on `None` is UB. Base authority is the linked Rust 1.84.0 standard-library documentation. | OBL-1–4 and both verdicts only. It establishes no interval membership, Cargo fact, other API, backend, or binary property. |

No other admitted premise is consumed. Source-level reasoning does not trust a particular compiler backend. Re-audit is required on any source, support-domain, base-contract, feature/target, or human-disposition change.

## Finding DOC-1: adjacent proof is incomplete

**Classification:** implementation obligation PROVED; proof artifact deficient; no UB witness and no defined postcondition refutation. The existing `SAFETY` comment states the branch conclusion and callee precondition, but does not identify the exact `is_none` fact, its domain/TCB basis, the absence of an intervening transition, or the result used for the public postcondition.

Proposed replacement:

```rust
// SAFETY: COMPAT-OPTION-184-186 guarantees throughout the supported domain
// that is_none is true exactly for None. This fallthrough is therefore
// Some(b); value has not been mutated. The same entry guarantees that
// unwrap_unchecked(Some(b)) is defined and returns b.
unsafe { value.unwrap_unchecked() }
```

Minimal resolution is to install equivalent adjacent or canonical proof text. This is documentation debt, not an implementation or API-contract failure.

## Residual scope and attestation

No code was modified, expanded, built, run, or tested; there is no tool-derived proof. Compiler/backend correctness, emitted binaries, non-supported configurations, resource/security properties, and undocumented behavior are excluded. Every source/API, unsafe operation, invariant transition, documented result, and supported configuration class has a disposition. Re-audit on changes to source/contracts, support policy, Rust/std documentation, TCB disposition, generated/build inputs, or newly discovered obligations.
