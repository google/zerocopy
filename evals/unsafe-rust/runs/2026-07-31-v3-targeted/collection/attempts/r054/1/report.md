# Unsafe Rust Audit: complete supplied snapshot

## Claims and verdicts

| Claim | Exact theorem | Verdict | Certificate and qualification |
|---|---|---|---|
| SOUND | For every well-typed safe call to `value_or_zero` in `Required`, execution is free of Rust undefined behavior under documented Rust abstract semantics. | **PROVED** | OBL-1 and configuration closure below, **relative to accepted TCB entry `COMPAT-OPTION-184-186`**. |
| RESULT | For every such call, `None` returns `0` and `Some(v)` returns `v`. | **PROVED** | OBL-2 below, **relative to accepted TCB entry `COMPAT-OPTION-184-186`**. |

**Combined mandatory result: PROVED**, relative to `target/TCB.md` as supplied. This is a source-level result, not a compiler-backend or binary theorem.

## Snapshot, scope, and contracts

The audited artifact is the exact supplied `Cargo.toml`, `SUPPORT.md`, `CI.md`, `TCB.md`, and `src/lib.rs`; `REQUEST.md` controls this review. It is a Rust-2021 `#![no_std]` library, has no declared dependencies, build script, generated source, macros, FFI, allocator use, concurrency, or mutable state. No prior audit or tool result was reused; the target was not built, run, tested, modified, or expanded.

The complete language-reachable public surface is the safe free function `value_or_zero(Option<u8>) -> u8` (`src/lib.rs:4`). There are no public fields, constructors, traits/impls, methods, hidden items, reexports, unsafe APIs, or configuration-specific APIs. Its documentation is normative: “Returns the contained byte, or zero when `value` is `None`.” Safe callers have no safety precondition. There is no abstraction invariant: the function owns its input and retains no state.

## Required domain and closure

`SUPPORT.md`, expressly identified there as the support commitment, defines

`Required = R × T × F × P × D`, where:

- `R = { released stable r | 1.84.0 <= r <= 1.86.0 }`;
- `T = {x86_64-unknown-linux-gnu, aarch64-apple-darwin, wasm32-unknown-unknown}`;
- `F = {telemetry disabled, telemetry enabled}`;
- `P = every Cargo profile`; and
- `D = {debug assertions disabled, debug assertions enabled}`.

Edition 2021 and the standard library bundled with `r` are fixed additional coordinates. The official version history through 1.86.0 gives the exhaustive release inventory `R = {1.84.0, 1.84.1, 1.85.0, 1.85.1, 1.86.0}` ([1.84.1 section](https://doc.rust-lang.org/1.86.0/releases.html#version-1841-2025-01-30), [1.85.1 section](https://doc.rust-lang.org/1.86.0/releases.html#version-1851-2025-03-18)). Thus the inventory equals the symbolic interval; it is not inferred from endpoints. `Cargo.toml`'s `rust-version = "1.84"` supplies only the stated Cargo minimum and does not erase the upper bound. `CI.md` is sampling evidence only and does not narrow or prove support.

There is no `cfg`, profile-sensitive operation, debug assertion, or use of `telemetry`; every required tuple selects the same function body. The accepted TCB entry explicitly covers both required `Option` propositions for every `r`, target, feature state, profile, and debug-assertion state in `Required`. Therefore each obligation below has `Covered = Required`, their pointwise intersection is `Required`, and `Required ⊆ Covered`. Panic strategy, optimization, overflow checks, target layout, and allocator choice do not enter the derivation.

## Obligation ledger and proof

| ID | Site and exact obligation | Derivation | Status |
|---|---|---|---|
| OBL-1 | `src/lib.rs:5-11`: `unwrap_unchecked` is reached only on `Some`. | If `is_none()` is true, line 6 returns before the unsafe call. If false, AXIOM-OPTION-184 plus COMPAT says the input is not `None`; exhaustive `Option<u8>` variants make it `Some(v)`. COMPAT then permits `unwrap_unchecked(Some(v))` and says it returns `v`. | **PROVED throughout `Required`, relative to COMPAT**. |
| OBL-2 | Documented result for all inputs. | `None`: COMPAT's exact `is_none` proposition selects line 6, returning `0`. `Some(v)`: it selects the fallthrough, and COMPAT's exact unwrap proposition returns `v`. These exhaustive cases also include `Some(0)`. | **PROVED throughout `Required`, relative to COMPAT**. |

The adjacent `SAFETY` comment identifies the dominating `None` return, derives `Some`, and names the callee precondition. Its implementation proof is adequate; the report-level TCB citation supplies the version/configuration applicability. No panic, unwind, destructor, alias, provenance, initialization, or arithmetic obligation remains.

## TCB audit log

**Log identity:** supplied `target/TCB.md`, entry `COMPAT-OPTION-184-186`; human disposition accepted. **Trust policy:** consume only versioned Rust documentation and that exact accepted proposition; no dependency, implementation, backend, platform, or binary premise is admitted.

| ID | Category and exact proposition | Scope/consumer/disposition |
|---|---|---|
| AXIOM-OPTION-184 | Rust 1.84.0 docs state that `is_none` returns true for `None` ([source](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.is_none)); `unwrap_unchecked` returns the contained `Some` value and calling it on `None` is UB ([source](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_unchecked)). | Rust 1.84.0 base propositions; verified authoritative basis for COMPAT. |
| COMPAT-OPTION-184-186 | Preserves, without weakening or added precondition, “`is_none` iff `None`” and “unwrap `Some(v)` to `v`; `None` is UB.” | Exactly `Required`; only OBL-1/2; **accepted by authorized human**. No interval-membership, Cargo, backend, or binary fact is consumed. |

The entry is minimal, non-vacuous, and used only by its named consumers. Re-audit is required on any source, support interval, base proposition, target/feature/profile/debug scope, or disposition change. There are no dependencies or unresolved/rejected premises.

## Findings, residual scope, and attestation

No soundness, contract, proof-documentation, authoritative-documentation, or skill-guidance finding remains. No additional robustness property was requested, and no tool-derived evidence was used.

Excluded from the theorem are unreleased, pre-1.84.0, post-1.86.0, nightly/beta/custom toolchains; other targets or feature names; compiler/backend correctness; emitted binaries; and behavior beyond the documented return value. These are theorem boundaries, not inferred project exclusions. Review must recur if source/API documentation, support policy, Cargo configuration, generated inputs, authoritative pages, or the TCB entry changes.

Attestation: every safe/unsafe surface, obligation, documented result, controlling domain expression, TCB consumer, and required configuration class in the supplied snapshot has a disposition. The verdict follows the required universal coverage certificate, not tests or absence of a counterexample. Audit date: 2026-08-01; independent second review not performed.
