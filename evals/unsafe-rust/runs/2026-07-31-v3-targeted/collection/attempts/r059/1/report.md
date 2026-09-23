# Unsafe Rust audit — `symbolic-domain-target`

## Claim and verdicts

For the exact supplied snapshot, every well-typed safe call to `value_or_zero` is free of Rust undefined behavior and returns the contained byte for `Some(v)`, or zero for `None`, throughout supported set **S**, relative to accepted TCB entry **COMPAT-OPTION-184-186**.

- **Soundness: PROVED for S, relative to COMPAT-OPTION-184-186.**
- **Documented result: PROVED for S, relative to COMPAT-OPTION-184-186.**
- **Combined mandatory result: PROVED for S, relative to COMPAT-OPTION-184-186.**
- No binary/backend, deployment, security, probabilistic, or extra robustness claim is made.

These are source-level Rust-abstract-semantics results. The accepted compatibility premise is indispensable and is not a claim that any compiler binary is correct.

## Snapshot and supported domain

The audited snapshot comprises all six supplied target files. SHA-256 identities:

| File | SHA-256 |
|---|---|
| `CI.md` | `d3ff0564c4f96fcf7e9ff2784dbafcf1baa446c4d44cf3f55371e45b1687e46e` |
| `Cargo.toml` | `7e25c6b1489e215d6e4ecdc8b7beea11fc35237b3207fb01e836e6c7b4e818f6` |
| `REQUEST.md` | `161fad09885c67715d35859f24a1c41bd12bcba58c2cd7e1f933670bdda71d21` |
| `SUPPORT.md` | `45ee272e31a71fe28da355624691db55439d234c92ae8be5ce1af460aed4069c` |
| `TCB.md` | `db2ecc86f6e93d8e7ed6dd3df2c01cf0e5a80580a121341a5409f6888c2de413` |
| `src/lib.rs` | `6a9db5bc51aa3c0fb1e966509de396cee5d451cb93f4295224d5772f22f838f8` |

At the 2026-08-01 audit cutoff, **S** is exactly: edition 2021; any released stable Rust `r` with `1.84.0 <= r <= 1.86.0`; target `x86_64-unknown-linux-gnu`, `aarch64-apple-darwin`, or `wasm32-unknown-unknown`; either `telemetry` state; every Cargo profile; and either debug-assertion state. `SUPPORT.md` controls. `Cargo.toml` agrees on the lower bound and edition; its lack of an upper bound is expressly only Cargo admission, not a support conflict. `CI.md` is sample evidence and proves no semantic obligation.

There are no dependencies, build script, generated/expanded artifacts, macros, `cfg` branches, target-specific operations, FFI, assembly, allocation, concurrency, or panic path. The feature is unused. One source implementation therefore applies parametrically to every axis; COMPAT-OPTION-184-186 expressly covers every member of S. No supported combination is uncovered. Releases entering the closed version interval after the cutoff require re-audit.

## Boundary, contracts, and invariants

The complete language-reachable crate surface is the safe public free function `pub fn value_or_zero(Option<u8>) -> u8`. There are no public fields, types, constructors, methods, traits/impls, statics, reexports, hidden items, callbacks, macros, or destruction behavior defined by this crate. The sole unsafe surface is the internal call `value.unwrap_unchecked()`; callers have no safety obligation beyond passing a well-typed `Option<u8>`.

**RESULT-1:** for every input, return `0` if it is `None`; return `v` if it is `Some(v)`. No persistent abstraction invariant exists. The only transient fact is **BRANCH-SOME**: on the fallthrough edge after `is_none()` returned false, the unchanged `value` is `Some(v)` for some `v`.

## Authorities and TCB audit log

The Rust 1.84.0 standard-library page declares `Option<T>` with only `None` and `Some(T)`. Its `is_none` contract says: “Returns `true` if the option is a `None` value.” ([1.84.0 `is_none`](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.is_none)). Its unsafe method says it returns the contained `Some` value and: “Calling this method on `None` is undefined behavior.” ([1.84.0 `unwrap_unchecked`](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_unchecked)).

**COMPAT-OPTION-184-186** is an accepted, authorized human compatibility premise from `TCB.md`. Exact admitted proposition: for every configuration in S, the 1.84.0 base propositions remain unweakened—`is_none` is true exactly for `None`; `unwrap_unchecked(Some(v))` returns `v`; calling it on `None` is UB. Category: out-of-band compatibility premise. Consumers: only SOUND-1 and RESULT-1 below. Limitations: it proves neither S's membership nor Cargo, backend, binary, or other-API facts. Disposition: accepted. Re-audit on any source, interval, base-proposition, target/feature, or disposition change. No other assumption, dependency trust, or tool result is consumed.

## Obligation ledger and derivation

| ID | Obligation | Proof and applicability | Status |
|---|---|---|---|
| SOUND-1 | Every safe input avoids calling `unwrap_unchecked` on `None`. | Complete case split below; local control flow plus COMPAT-OPTION-184-186 over all S. | **PROVED relative to COMPAT-OPTION-184-186** |
| RESULT-1 | Return zero for `None`, contained byte for `Some(v)`. | Same split plus the admitted return proposition, over all S. | **PROVED relative to COMPAT-OPTION-184-186** |

Case `value = None`: COMPAT-OPTION-184-186 makes `is_none()` true. The dominating branch returns literal `0`; the unsafe call is not executed. This proves soundness and the `None` result.

Case `value = Some(v)`: the same premise makes `is_none()` false. `is_none` only borrows the same value, so fallthrough establishes BRANCH-SOME. COMPAT-OPTION-184-186 then supplies both permission and result for `unwrap_unchecked(Some(v))`: the execution has no UB from that call and returns `v`. The two exhaustive `Option` cases prove both universal claims. There is no intervening mutation, callback, unwind, or alternative exit.

## Finding DOC-1 — local proof omits its material authority

- **Classification:** implementation obligations PROVED; proof artifact deficient; maintenance/documentation severity.
- The adjacent `SAFETY` comment identifies the branch conclusion but does not name the exact `is_none` proposition or the accepted compatibility premise needed across S. This does not change the source verdict because the complete reconstruction appears above.
- Proposed replacement:

```rust
// SAFETY: COMPAT-OPTION-184-186 states, over the complete supported
// domain, that is_none is true exactly for None and that
// unwrap_unchecked(Some(v)) returns v. The false branch above, which only
// borrowed this unchanged value, therefore establishes value = Some(v).
unsafe { value.unwrap_unchecked() }
```

No UB witness, UB-free postcondition refutation, authoritative-documentation gap, or skill-guidance gap was established.

## Residual scope and review triggers

Excluded: compiler/backend correctness, emitted binaries, unsupported configurations, and properties not requested. No build, execution, test, macro expansion, or tool-derived proof was used. Re-audit on any source/API/documentation change; support-axis or post-cutoff release change; material change to the cited pages; or weakening, rejection, or broader use of COMPAT-OPTION-184-186.

All in-scope surfaces and obligations have a status; every supported configuration is covered; both mandatory claims expose their accepted TCB dependence. Independent second review was not performed.
