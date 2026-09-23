# Unsafe Rust audit: complete supplied snapshot

## Claim and verdict

**Source-level soundness — PROVED, relative to accepted TCB entry `COMPAT-OPTION-184-186`.** For the exact supplied source, every well-typed safe call to `value_or_zero` is free of Rust undefined behavior for every supported configuration.

**Documented behavior — PROVED, relative to `COMPAT-OPTION-184-186`.** Every such call returns the contained byte for `Some(v)` and returns zero for `None`.

**Combined mandatory result — PROVED, relative to `COMPAT-OPTION-184-186`.** This qualification is material: no result here applies that entry outside `value_or_zero`, its two named `Option` propositions, or the supported region.

The supported predicate, controlled by `SUPPORT.md:3-21`, is exactly: released stable Rust `r` with `1.84.0 <= r <= 1.86.0`; target in `{x86_64-unknown-linux-gnu, aarch64-apple-darwin, wasm32-unknown-unknown}`; either `telemetry` state; every Cargo profile; and either debug-assertion state. `Cargo.toml:5` supplies Cargo's minimum, not the upper support cutoff. `CI.md` is sampling evidence only and does not narrow this predicate.

## Snapshot, scope, and boundary

Audited source is the complete supplied six-file snapshot (`Cargo.toml`, `SUPPORT.md`, `CI.md`, `TCB.md`, `REQUEST.md`, and `src/lib.rs`); no revision, dependencies, generated artifacts, build script, lockfile, or prior audit was supplied. This was source review only: no target execution, build, test, expansion, or tool-derived proof was used. Edition is 2021 and the crate is `no_std`.

The sole public surface is safe function `value_or_zero(Option<u8>) -> u8` (`src/lib.rs:3-12`). There are no public representation fields, constructors for a crate-owned type, traits or impls, macros, reexports, hidden APIs, callbacks, statics, FFI, or configuration-specific APIs. The sole unsafe operation is the internal `Option::unwrap_unchecked` call at `src/lib.rs:11`; it is not a caller-facing unsafe boundary. No persistent representation invariant exists. The only transient invariant is **BRANCH-SOME**: after the `is_none()` true branch returns, the still-owned `value` is `Some(v)`.

## Authorities and TCB log

Rust 1.84.0 standard-library documentation states that [`is_none`](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.is_none) “Returns `true` if the option is a `None` value.” The version-matched [`unwrap_unchecked`](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_unchecked) contract says it returns the contained `Some` value and that calling it on `None` is undefined behavior.

`TCB.md:3-23` is the accepted human trust decision and the complete additional TCB:

| ID | Disposition | Exact admitted proposition and domain | Consumers |
|---|---|---|---|
| `COMPAT-OPTION-184-186` | accepted | Across the entire supported Rust/target/feature/profile/debug domain, the 1.84.0 base propositions are preserved: `is_none()` is true exactly for `None`; `unwrap_unchecked(Some(v))` returns `v`, while invocation on `None` is UB. | Only soundness and documented-result proofs below |

It admits neither release membership nor Cargo/backend/binary facts. No safe or unsafe dependency, compiler implementation, platform, deployment, or other compatibility premise is consumed. Its stated re-audit trigger is any source, support interval, base-proposition, feature/target-scope, or human-disposition change.

## Obligation ledger and derivation

| ID | Site / exact obligation | Derivation over the supported predicate | Status |
|---|---|---|---|
| O1 | `lib.rs:5-7`: `None` behavior | By `COMPAT-OPTION-184-186`, `is_none()` is true exactly on `None`; the dominating branch returns literal `0`. No unsafe operation executes. | PROVED relative to TCB |
| O2 | `lib.rs:11`: do not call `unwrap_unchecked` on `None` | Reaching line 11 means the true branch did not execute, hence `is_none()` was false. The same TCB proposition yields BRANCH-SOME, so the callee's sole documented UB case is excluded. | PROVED relative to TCB |
| O3 | `lib.rs:11`: `Some(v)` result | BRANCH-SOME and the TCB-preserved postcondition give `unwrap_unchecked(Some(v)) = v`; the function immediately returns it. | PROVED relative to TCB |
| O4 | Safe API, all executions | `Option<u8>` exhausts the `None` case (O1) and `Some(v)` case (O2-O3). Thus every well-typed safe input is UB-free and meets the sole documented result contract. | PROVED relative to TCB |

Configuration closure is parametric, not empirical: the source has no `cfg`, feature use, profile/debug-dependent assertion, target-dependent operation, allocation, panic/unwind branch, concurrency, FFI, generated code, or build-time input. Consequently the same control/data-flow proof applies to every Cartesian combination in `Supported`; `COMPAT-OPTION-184-186` supplies exactly the only version-sensitive semantics. CI contributes no proof.

## Finding: local proof documentation is deficient

**Documentation defect; implementation remains PROVED relative to the TCB.** The `SAFETY` comment at `src/lib.rs:9-10` correctly names the branch fact and callee precondition, but omits the material bridge that `is_none() == false` implies `Some(v)` throughout every supported Rust release, and it does not identify the accepted compatibility premise on which that bridge and the result proof depend.

Proposed replacement:

```rust
// SAFETY: By COMPAT-OPTION-184-186, throughout the supported domain
// `is_none()` is true exactly for `None`. This continuation therefore has
// `value = Some(v)`; the same accepted premise preserves that
// `unwrap_unchecked(Some(v))` is permitted and returns `v`.
unsafe { value.unwrap_unchecked() }
```

This is a proof-artifact repair only; it adds no caller obligation or new contract.

## Residual scope and triggers

Compiler/backend and binary correctness, unsupported toolchains/targets, and undocumented robustness properties are excluded. Re-audit on any source or public-documentation change; change to the supported predicate; change/rejection of `COMPAT-OPTION-184-186` or either cited base contract; addition of dependencies, generated code, configuration branches, unsafe operations, or public surfaces. All in-scope obligations have a disposition; no UB witness or UB-free postcondition refutation is established or needed for the proved theorem.
