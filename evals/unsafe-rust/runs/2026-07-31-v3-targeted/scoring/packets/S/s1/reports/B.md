# Unsafe Rust audit: complete supplied snapshot

## Claim and verdict

**Soundness — PROVED relative to `TCB.md` / `COMPAT-OPTION-184-186`.** For the exact supplied source, every well-typed safe call to `value_or_zero` is free of Rust undefined behavior in every configuration in `Required` below.

**Documented result — PROVED relative to the same TCB entry.** Every such call returns `0` for `None` and returns `v` for `Some(v)`.

The combined mandatory result is **PROVED**. This is a source-level Rust-abstract-semantics result, not a claim about a compiler backend or emitted binary.

## Snapshot, scope, and boundary

The audited snapshot is the complete supplied `Cargo.toml`, `SUPPORT.md`, `CI.md`, `TCB.md`, `REQUEST.md`, and `src/lib.rs`. It is a Rust-2021 `#![no_std]` library with no dependencies, build script, generated source, or prior audit reused.

The complete language-reachable crate-defined API surface is the safe free function `pub fn value_or_zero(Option<u8>) -> u8` (`src/lib.rs:4-13`). There are no public fields, constructors, types, traits or impls, statics, reexports, macros, hidden items, callbacks, FFI, assembly, allocator operations, or concurrency surfaces. The sole unsafe site is the internal `Option::unwrap_unchecked` call at line 12. There is no persistent representation invariant; the only safety fact is the control-flow-local proposition `value != None` at that call.

## Exact supported domain and closure

Let

* `R = { r | r is a released stable Rust toolchain and 1.84.0 <= r <= 1.86.0 }`;
* `T = {x86_64-unknown-linux-gnu, aarch64-apple-darwin, wasm32-unknown-unknown}`;
* `F = {telemetry disabled, telemetry enabled}`;
* `P` be every Cargo profile; and
* `A = {debug assertions disabled, debug assertions enabled}`.

Then `Required = R × T × F × P × A`, for this source and its version-matched standard library. `SUPPORT.md` is controlling: it says the release predicate is exact and expressly supports every cross-product member. `Cargo.toml`'s `rust-version = "1.84"` is only Cargo's minimum-admission statement, as `SUPPORT.md` itself explains; it agrees with the lower bound and does not erase the upper bound. `default = []` and the sole declared feature establish the two feature states. `CI.md` supplies samples only and neither defines nor proves support.

This preserves `R` symbolically. No finite release inventory is substituted, so no unproved “there were no other patch releases” premise is needed. `COMPAT-OPTION-184-186` quantifies over exactly the same released-stable predicate.

`Covered = Required`. The source contains no `cfg`, feature read, target branch, assertion, arithmetic, panic, profile-sensitive operation, generator, or external component. Thus its control-flow proof is parametric over `T × F × P × A`. The accepted compatibility premise is parametric over `R` and all those axes. Their conjunction covers every cross-product member, establishing `Required ⊆ Covered`. CI endpoints are not used in this certificate.

## Authorities, TCB, and proof ledger

The Rust 1.84.0 documentation says `is_none` “[r]eturns `true` if the option is a `None` value” ([versioned page](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.is_none)). It says `unwrap_unchecked` returns the contained `Some` value and that calling it on `None` is undefined behavior ([versioned page](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_unchecked)). Both exact pages and their version were checked.

`COMPAT-OPTION-184-186` is an accepted human compatibility premise. Its exact consumed proposition is: throughout `Required`, `is_none` is true exactly for `None`; `unwrap_unchecked(Some(v))` returns `v`; and calling it on `None` is UB. Its only consumers here are the following obligations, matching `TCB.md`. It establishes no release inventory, Cargo fact, backend, or binary fact. No other assumption is consumed.

| ID | Obligation and derivation | Status |
|---|---|---|
| O1 | At line 12, `unwrap_unchecked` must receive `Some(v)`. If `is_none()` were true, line 6 returned. On the continuing path it is false; by `COMPAT-OPTION-184-186`, `value` is `Some(v)`. | PROVED over `Required` |
| O2 | Every safe input is covered. `None` takes the first return and executes no unsafe operation. `Some(v)` reaches line 12 with O1 true, and the TCB premise supplies a defined return of `v`. | PROVED over `Required` |
| O3 | The same exhaustive cases return respectively `0` and `v`, exactly the documented behavior. Both executions are UB-free as established by O2. | PROVED over `Required` |
| O4 | Configuration/version closure is the parametric argument above; applicability of every consumed premise contains `Required`. | PROVED |

No test, build, execution, or tool-derived evidence was used.

## Proof-documentation finding

**DOC-01 — local `SAFETY` proof is incomplete as a persistent proof artifact; implementation remains proved.** The comment identifies the branch and callee precondition, but does not identify the semantic premise establishing that `is_none() == false` means `Some`, nor its supported-release applicability. Suggested replacement:

```rust
// SAFETY: COMPAT-OPTION-184-186 guarantees throughout the supported domain
// that is_none() is true exactly for None. The true case returned above, so
// value is Some(v); the same premise guarantees unwrap_unchecked(Some(v))
// is defined and returns v.
```

This is documentation debt, not an implementation, soundness, or behavioral defect.

## Residual scope and triggers

Excluded are configurations outside `Required`, backend/binary correctness, and undocumented robustness properties. Re-audit is required for any source or documentation change; support-domain expansion or reinterpretation; change to either cited standard-library proposition; change or withdrawal of `COMPAT-OPTION-184-186`; or addition of dependencies, generated code, configuration-sensitive code, or API surfaces. Every in-scope obligation and mandatory postcondition has a disposition; there is no unresolved domain or proof remainder.
