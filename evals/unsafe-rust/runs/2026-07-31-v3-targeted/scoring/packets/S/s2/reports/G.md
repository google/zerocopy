# Unsafe Rust Audit: complete supplied snapshot

## Claim and verdict

**Soundness — PROVED, relative to accepted TCB entry `COMPAT-OPTION-184-186`.** For the exact supplied source, every well-typed safe call to `value_or_zero` under `Supported(c)` is free of Rust undefined behavior under the documented Rust abstract semantics.

**Documented behavior — PROVED, relative to the same accepted TCB entry.** In that domain, `value_or_zero(None) == 0` and `value_or_zero(Some(v)) == v` for every `v: u8`.

**Combined mandatory result — PROVED, relative to accepted `COMPAT-OPTION-184-186`.** There is no conditional binary, deployment, security, or probabilistic claim.

`Supported(c)` means: edition 2021; `c.r` is any released stable Rust toolchain satisfying `1.84.0 <= c.r <= 1.86.0`; target is exactly `x86_64-unknown-linux-gnu`, `aarch64-apple-darwin`, or `wasm32-unknown-unknown`; `telemetry` is disabled or enabled; and any Cargo profile and either debug-assertion state are used. This is the literal commitment in `SUPPORT.md`; `Cargo.toml`'s `rust-version = "1.84"` is only the Cargo minimum. The sources do not conflict. Audit cutoff: 2026-08-01.

## Snapshot and scope

The artifact is the exact supplied contents of `Cargo.toml`, `src/lib.rs`, `SUPPORT.md`, `CI.md`, `TCB.md`, and `REQUEST.md`; no repository revision or digest was supplied. The crate is `no_std`, has no dependencies or build script, and contains no generated source. Scope is the complete library and its documented safe behavior. No build, execution, test, expansion, or binary/backend claim was used. Skill identity: supplied `unsafe-rust` package, revision unspecified.

The sole language-reachable public surface is safe function `pub fn value_or_zero(Option<u8>) -> u8`. There are no public fields, types, constructors, trait implementations, macros, reexports, statics, callbacks, FFI items, hidden items, or destruction behavior owned by this crate. The only unsafe operation is `Option::unwrap_unchecked` at `src/lib.rs:11`. There is no persistent representation invariant; the only proof state is the local branch fact.

## Authorities and TCB audit log

The Rust 1.84.0 standard-library page says `is_none` “Returns `true` if the option is a `None` value” and declares `Option`'s `None` and `Some(T)` variants ([1.84.0 `is_none`](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.is_none)). The version-matched `unwrap_unchecked` contract says it returns the contained `Some` value and is the controlling unsafe operation ([1.84.0 `unwrap_unchecked`](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_unchecked)).

`TCB.md` is the canonical log. Its sole entry, `COMPAT-OPTION-184-186`, is **accepted by the authorized human reviewer**. It admits, for every `Supported(c)`, exactly: (1) `is_none` is true iff the value is `None`; and (2) `unwrap_unchecked(Some(v))` returns `v`, while calling it on `None` is UB. Category: accepted compatibility/out-of-band semantic premise; base identity: the two Rust 1.84.0 pages above. Consumers: only obligations O1–O3 below. It admits neither release membership nor Cargo/backend/other-API facts. No release enumeration is needed: the proof is universal over whichever released stable `r` satisfies the policy predicate. Trigger: any source, interval, base proposition, target/feature/profile/debug scope, or human-disposition change. The entry is precise, non-circular, within its authorized scope, and accepted; no other dependency, implementation, tool, or environmental premise is consumed.

## Obligation ledger and derivation

| ID | Proposition and proof | Domain | Status |
|---|---|---|---|
| O1 | If line 11 is reached, `value` is `Some(v)`. On `None`, accepted `COMPAT-OPTION-184-186` makes `is_none()` true, so lines 5–6 return. If line 11 is reached, the test was false; the accepted iff proposition excludes `None`, and `Option`'s exhaustive remaining variant is `Some`. | All `Supported(c)`, all inputs | PROVED relative to accepted TCB |
| O2 | The unsafe call never receives `None`; by O1 it receives `Some(v)`. Accepted `COMPAT-OPTION-184-186` therefore gives a defined return of `v`, discharging the exact unsafe precondition. The `None` branch executes no unsafe operation. | All `Supported(c)`, all inputs | PROVED relative to accepted TCB |
| O3 | For `None`, accepted `is_none` semantics select line 6, yielding zero. For `Some(v)`, they select line 11, and accepted `unwrap_unchecked` semantics yield `v`. These cases exhaust `Option<u8>`. | All `Supported(c)`, all inputs | PROVED relative to accepted TCB |
| O4 | Configuration closure: source has no `cfg`; `telemetry` is declared but unused; target, profile, and debug assertions select no path; there are no allocation, panic, arithmetic, concurrency, FFI, or generated-code obligations. O1–O3 are parametric, and the accepted TCB explicitly has the same configuration quantification. | Entire `Supported(c)` | PROVED relative to accepted TCB |

`CI.md` describes only samples (1.84.0 on one target/feature state and 1.86.0 across targets/feature states). It neither defines support nor contributes proof evidence. No tool-derived evidence was used.

## Finding D1 — deficient adjacent proof artifact

**Implementation classification:** PROVED relative to accepted `COMPAT-OPTION-184-186`. **Proof-artifact classification:** deficient. Lines 9–10 state the correct branch idea, but omit the material `is_none` iff premise, exhaustive-variant step, applicability, accepted TCB bridge, and `unwrap_unchecked(Some(v))` postcondition. This is not an implementation defect, UB witness, or defined postcondition refutation.

Proposed replacement:

```rust
// SAFETY: Under accepted COMPAT-OPTION-184-186 throughout Supported(c),
// is_none is true iff value is None. Reaching here means it returned false;
// Option has only None and Some variants, so value is Some(v). Under the same
// entry, unwrap_unchecked(Some(v)) is defined and returns v.
unsafe { value.unwrap_unchecked() }
```

Minimum resolution: add an adjacent proof with a stable local link to the canonical TCB entry and authoritative contracts. This is documentation maintenance, not a change to the caller contract.

## Residual scope and attestation

Excluded: configurations outside `Supported(c)`, compiler/backend and emitted-binary correctness, non-Rust environments, and undocumented robustness properties. No supported source configuration is uncovered. Re-audit on any source/API/documentation change; support/edition/target/feature/profile/debug change; material change to the cited Rust contracts; TCB disposition or proposition change; dependency/build-generation introduction; or a newly discovered obligation.

Every public surface, unsafe site, mandatory postcondition, supported configuration class, citation, and consumed TCB premise has a disposition above. Every `PROVED` result is expressly relative to the accepted TCB; no absence-of-counterexample or test inference is used. Independent review was not performed.
