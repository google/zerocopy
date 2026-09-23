# Unsafe Rust audit: complete supplied snapshot

## Claim and verdict

| Claim | Exact theorem | Verdict | Qualification |
|---|---|---|---|
| SOUND | For every `Required` configuration and every well-typed safe call `value_or_zero(value: Option<u8>)`, execution is free of Rust undefined behavior. | **PROVED** | Source-level Rust semantics, relative to accepted TCB entry `COMPAT-OPTION-184-186`. |
| RESULT | In the same domain, `value_or_zero(None) == 0` and `value_or_zero(Some(v)) == v` for every `u8` `v`. | **PROVED** | Relative to the same accepted entry. |

**Combined mandatory result: PROVED**, relative to conspicuous use of `TCB.md` entry `COMPAT-OPTION-184-186`. Scope is the complete supplied crate snapshot and its sole public safe API. This is not a compiler-backend or emitted-binary claim.

## Snapshot and required domain

Audited inputs are `Cargo.toml`, `SUPPORT.md`, `CI.md`, `TCB.md`, `REQUEST.md`, and `src/lib.rs` as supplied. There are no dependencies, build scripts, generators, generated artifacts, macros, FFI, assembly, concurrency, allocation, mutable state, or target-specific source. The crate is edition 2021 and `no_std`.

Preserving the controlling expression rather than inventing a finite release list:

```text
Required(r,t,f,p,d) :=
  ReleasedStableRust(r) && 1.84.0 <= r <= 1.86.0
  && t in {x86_64-unknown-linux-gnu,
           aarch64-apple-darwin,
           wasm32-unknown-unknown}
  && f in {telemetry-off, telemetry-on}
  && p is any Cargo profile
  && d in {debug-assertions-off, debug-assertions-on}.
```

`SUPPORT.md` expressly makes that predicate, including its upper cutoff, the support commitment. `Cargo.toml`'s `rust-version = "1.84"` supplies the compatible lower Cargo admission threshold but does not replace the policy or erase its upper bound. `CI.md` is only a sample and is not used to transform or prove the domain. No enumeration of `ReleasedStableRust` is used: the proof below and the accepted compatibility premise quantify over the symbolic predicate directly.

Configuration selection is source-identical: neither feature nor target appears in a `cfg`; there are no assertions or profile-sensitive arithmetic; and the only unsafe operation's admitted contract explicitly covers every `Required` target, profile, feature, and debug-assertion state. Thus each obligation's `Covered` predicate equals `Required`, establishing `Required ⊆ Covered` without relying on CI samples. The audit cutoff is 2026-08-01; the fixed upper bound makes it non-moving.

## Boundary, invariants, and obligations

The complete language-reachable crate-defined API surface is the safe free function `value_or_zero`. There are no public fields, constructors, types, traits or impls, methods, statics, reexports, hidden items, callbacks, or macro-generated APIs. The internal unsafe consumer is `Option::unwrap_unchecked` at `src/lib.rs:12`. There is no persistent representation invariant; the sole proof fact is the branch-local classification of `value`.

| ID | Proposition | Proof/status |
|---|---|---|
| O1 | The `None` branch returns before the unsafe call. | Direct control flow at lines 6–8; **PROVED** for `Required`. |
| O2 | Every execution reaching line 12 has `value = Some(v)`. | `is_none` is exactly the `None` discriminator by the accepted TCB proposition; negating the taken condition and the two `Option` variants gives `Some(v)`; **PROVED** for `Required`. |
| O3 | Line 12 satisfies `unwrap_unchecked`'s safety precondition and returns `v`. | O2 plus the version-applicable contract below; **PROVED** for `Required`. |
| O4 | Both documented result cases hold. | Exhaustive `None`/`Some(v)` partition and O1/O3; **PROVED** for `Required`. |

The Rust 1.84.0 documentation says `is_none` “Returns `true` if the option is a `None` value” and says, for `unwrap_unchecked`, “Calling this method on `None` is undefined behavior”; it also specifies that a `Some` receiver yields its contained value ([`is_none`](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.is_none), [`unwrap_unchecked`](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_unchecked)). The same method contracts were independently checked in [1.84.1](https://doc.rust-lang.org/1.84.1/std/option/enum.Option.html#method.unwrap_unchecked), [1.85.0](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.unwrap_unchecked), [1.85.1](https://doc.rust-lang.org/1.85.1/std/option/enum.Option.html#method.unwrap_unchecked), and [1.86.0](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.unwrap_unchecked). These checks corroborate but do not purport to enumerate the release interval.

The proof is exhaustive:

- If `value = None`, accepted proposition (1) makes `is_none()` true; line 7 returns `0`, line 12 is unreachable, and both SOUND and RESULT hold.
- If `value = Some(v)`, proposition (1) makes `is_none()` false; line 12 is reached with a non-`None` receiver. Its safety obligation is satisfied, and accepted proposition (2) makes the result `v`. Thus SOUND and RESULT hold.

## TCB audit log

| ID | Category/disposition | Exact consumed proposition and scope | Consumers / trigger |
|---|---|---|---|
| STD-OPTION-184 | Versioned standard-library authority; verified | The two quoted 1.84.0 method contracts above. | Basis for COMPAT; revisit if those pages materially change. |
| COMPAT-OPTION-184-186 | Compatibility premise; **accepted by the authorized human reviewer** | For every `Required` release/configuration, `is_none` is true exactly for `None`; `unwrap_unchecked(Some(v))` returns `v`, while calling it on `None` is UB. It establishes no release-set inventory, Cargo fact, backend, or binary fact. | O2–O4 and both verdicts; triggers exactly as stated in `TCB.md`. |

No other premise, dependency, implementation, tool, deployment, or probabilistic trust is consumed. The accepted entry is not inferred from the sampled version pages; it is the explicit interval-coverage basis authorized by the request.

## Finding DOC-1: local proof artifact is incomplete

**Implementation obligation: PROVED. Proof-artifact classification: deficient.** The existing `SAFETY` comment captures the branch idea but neither names the semantic premise nor its applicability throughout `Required`. The material reconstruction is O2–O3 above. This does not weaken either verdict, but the smallest adequate repair is an adjacent comment such as:

```rust
// SAFETY: By accepted TCB entry COMPAT-OPTION-184-186, for every
// supported configuration is_none() is true exactly for None. The true
// branch returned above, so value is Some(v). The same entry preserves
// unwrap_unchecked's contract: this call is permitted and returns v.
```

No caller-facing contract change is needed. Re-audit after any source, support predicate, method contract, TCB disposition, or configuration-scope change. Outside scope are unsupported toolchains/configurations and binary correctness. No tools, builds, tests, execution, or macro expansion were used as evidence.
