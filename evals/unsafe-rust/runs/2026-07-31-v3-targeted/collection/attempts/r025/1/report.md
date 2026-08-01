# Unsafe Rust source audit

## Claim and verdict

**Combined mandatory verdict: PROVED**, relative to accepted TCB entry
`COMPAT-OPTION-184-186` in the supplied `TCB.md` (SHA-256
`db2ecc86f6e93d8e7ed6dd3df2c01cf0e5a80580a121341a5409f6888c2de413`). For
the exact supplied source, every well-typed safe call to `value_or_zero` is free
of Rust undefined behavior and returns the contained byte for `Some(v)` or zero
for `None`, throughout the supported set below. Soundness: **PROVED relative to
that TCB entry**. Documented result: **PROVED relative to that TCB entry**.

This is a source-level Rust-abstract-semantics claim, not a claim about compiler
correctness or any emitted binary.

## Snapshot, scope, and supported set

The complete target consists of `Cargo.toml`, `TCB.md`, `CI.md`, `REQUEST.md`,
`SUPPORT.md`, and `src/lib.rs`; the latter has SHA-256
`6a9db5bc51aa3c0fb1e966509de396cee5d451cb93f4295224d5772f22f838f8`.
Scope is the entire `no_std`, edition-2021 library. It has no dependencies,
build script, generated source, or prior audit.

`SUPPORT.md` controls support (the manifest's `rust-version = "1.84"` is only
the Cargo minimum). The exact predicate is:

* released stable Rust `r` with `1.84.0 <= r <= 1.86.0`—namely 1.84.0,
  1.84.1, 1.85.0, 1.85.1, or 1.86.0; the official notes record
  [1.84.1](https://doc.rust-lang.org/1.86.0/releases.html#version-1841-2025-01-30)
  and [1.85.1](https://doc.rust-lang.org/1.86.0/releases.html#version-1851-2025-03-18);
* target `x86_64-unknown-linux-gnu`, `aarch64-apple-darwin`, or
  `wasm32-unknown-unknown`;
* either `telemetry` state, every Cargo profile, and either debug-assertion
  state.

CI is sampling only and supplies no proof. There are no source `cfg`s or uses
of the feature, target, profile, assertions, allocation, arithmetic,
concurrency, panic, FFI, assembly, macros, or linking. Thus one source/dataflow
proof is parametric over every non-toolchain axis; the accepted TCB proposition
explicitly covers every toolchain member and all those axes. No supported
combination is uncovered.

## Boundary and obligation inventory

The sole language-reachable crate surface is safe free function
`value_or_zero(Option<u8>) -> u8` (`src/lib.rs:4-12`). There are no public
fields/types, constructors, traits or impls, hidden items, statics, reexports,
callbacks, macros, or FFI. The sole unsafe site is the internal
`Option::unwrap_unchecked` call at line 11. There is no persistent state or
abstraction invariant; only the dominating branch fact is consumed.

| ID | Exact obligation | Derivation | Status |
|---|---|---|---|
| O1 | Safe callers have no hidden safety precondition. | The function accepts every `Option<u8>` and branches before its only unsafe operation. | PROVED |
| O2 | Line 11 is never called on `None`. | Under `COMPAT-OPTION-184-186`, `is_none` is true exactly for `None`. Reaching line 11 means the test at line 5 returned false, so `value = Some(v)`. The same accepted entry states that `unwrap_unchecked(Some(v))` is defined and returns `v`, whereas `None` would be UB. | PROVED relative to TCB |
| O3 | The documented result is returned. | If `None`, O2's `is_none` proposition makes line 6 return zero. If `Some(v)`, the test is false and O2 makes line 11 return `v`. These exhaustive cases establish the documentation at line 3. | PROVED relative to TCB |

The Rust 1.84.0 base pages say `is_none` “[r]eturns `true` if the option is a
`None` value” and `unwrap_unchecked` “[r]eturns the contained `Some` value”; they
also state that calling it on `None` is undefined behavior
([`is_none`](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.is_none),
[`unwrap_unchecked`](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_unchecked)).
The exact uniform proposition used above is nevertheless the human-accepted
compatibility entry, not an inference from API stability. Its permitted
consumers are precisely O2/O3; it supplies no release-membership, Cargo,
backend, or binary fact.

## Finding D1 — deficient adjacent proof, implementation proved

The line 9 comment identifies the branch and callee precondition, but omits the
material authoritative/TCB bridge and its supported-domain applicability.
Implementation classification: **PROVED relative to
`COMPAT-OPTION-184-186`**. Proof-artifact classification: **deficient**. No UB
witness or defined postcondition refutation is established.

Proposed replacement:

```rust
// SAFETY: By COMPAT-OPTION-184-186 throughout the supported domain,
// value.is_none() is true exactly for None. Reaching here means it returned
// false, so value is Some(v); unwrap_unchecked(Some(v)) is defined and returns v.
```

This documentation repair changes no API or behavior. Re-audit the proof if
the source, documented result, support interval/axes, cited base propositions,
or TCB disposition changes.

## TCB, evidence, and residual scope

`COMPAT-OPTION-184-186` is an accepted compatibility premise, scoped only as
quoted above; its identity, consumers, exclusions, and re-audit triggers were
verified. No dependency, tool-derived, test-derived, environmental,
probabilistic, or implementation premise is consumed. The version-matched
allowlisted standard-library pages for all five releases were checked and do
not add a qualification, but they are not used to invent a general
compatibility rule.

Excluded: unsupported configurations, compiler/backend correctness, emitted
binaries, and ordinary robustness beyond the requested documented result. No
build, execution, macro expansion, or test was performed. No authoritative
documentation gap or unresolved proof obligation remains.
