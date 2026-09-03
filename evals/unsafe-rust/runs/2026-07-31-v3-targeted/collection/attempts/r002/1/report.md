# Unsafe Rust Audit: `symbolic-domain-target` complete supplied snapshot

## Claims and verdicts

Let `D` be all tuples `(r,t,f,p,d)` where `r` is a released stable Rust toolchain and `1.84.0 <= r <= 1.86.0`; `t` is `x86_64-unknown-linux-gnu`, `aarch64-apple-darwin`, or `wasm32-unknown-unknown`; `f` is either state of `telemetry`; `p` is any Cargo profile; and `d` is either debug-assertion state.

| Claim | Exact source-level theorem for every configuration in `D` and every well-typed safe call | Verdict |
|---|---|---|
| SOUND | `value_or_zero` executes without Rust undefined behavior | **PROVED relative to accepted TCB entry `COMPAT-OPTION-184-186`** |
| RESULT | `None` returns `0`; `Some(v)` returns `v` | **PROVED relative to accepted TCB entry `COMPAT-OPTION-184-186`** |

**Combined mandatory result: PROVED over exactly `D`, relative to `COMPAT-OPTION-184-186`.** This is an abstract Rust source theorem, not a compiler/backend or emitted-binary theorem.

## Snapshot and scope

The complete supplied package is edition 2021, `#![no_std]`, has no dependencies or build script, and contains one library source file. Relevant SHA-256 identities are: `src/lib.rs` `6a9db5bc51aa3c0fb1e966509de396cee5d451cb93f4295224d5772f22f838f8`; `Cargo.toml` `7e25c6b1489e215d6e4ecdc8b7beea11fc35237b3207fb01e836e6c7b4e818f6`; `SUPPORT.md` `45ee272e31a71fe28da355624691db55439d234c92ae8be5ce1af460aed4069c`; and `TCB.md` `db2ecc86f6e93d8e7ed6dd3df2c01cf0e5a80580a121341a5409f6888c2de413`. `REQUEST.md`, `CI.md`, and every supplied target file were reviewed. Audit cutoff: 2026-08-01. No code was generated, expanded, built, run, or tested; no prior audit was reused.

## Domain recovery and configuration closure

`SUPPORT.md` is explicit that its closed toolchain interval, including the upper cutoff, is the project commitment. Its predicate is crossed with the three enumerated targets, both feature states, every profile, and both debug-assertion states; this is exactly `D`, with no normalization to a finite release inventory. `Cargo.toml`'s `rust-version = "1.84"` is expressly only Cargo's minimum and is consistent with, but does not replace, that policy. `CI.md` lists samples only and supplies neither domain membership nor semantic proof.

The source has no `cfg`, feature-conditioned item, profile-dependent check, arithmetic, target operation, dependency, macro, FFI, assembly, allocation, concurrency, or generated artifact. Its proof is therefore parametric in `t`, `f`, `p`, and `d`. Version coverage is parametric in `r` through the accepted TCB entry, rather than inferred from endpoints or sampled documentation.

For every `c in D`, the proof below covers both valid `Option<u8>` variants. Hence each obligation's `Covered` predicate is `D`; their pointwise intersection is `D`, and `Required = D subseteq Covered = D`. No supported configuration is excluded or unresolved.

## Boundary, invariant, and obligation ledger

The only crate-defined language-reachable API is the safe free function `pub fn value_or_zero(Option<u8>) -> u8`. There are no public fields or types, crate constructors, traits/impls, methods, statics, macros, reexports, hidden items, callbacks, FFI entrypoints, or configuration-specific APIs. The sole unsafe surface is the internal call `value.unwrap_unchecked()`.

The only invariant is transient `FALLTHROUGH-SOME`: from completion of the false `is_none` branch until the consuming unsafe call, the owned, immutable local `value` is `Some(v)`. It is established by the branch and `COMPAT-OPTION-184-186`; no assignment, alias-capable callback, or other operation intervenes.

| Obligation | Required proposition | Derivation and status |
|---|---|---|
| O1 branch classification | `is_none` distinguishes `None` from `Some(v)` | The accepted entry preserves the exact classification throughout `D`. **PROVED** |
| O2 unsafe precondition | the receiver of `unwrap_unchecked` is not `None` | Only fallthrough reaches the call; O1 and unchanged ownership establish `FALLTHROUGH-SOME`. **PROVED** |
| O3 unsafe result | `unwrap_unchecked(Some(v))` returns `v` | The accepted entry preserves this base proposition throughout `D`. **PROVED** |
| O4 documented result | `None -> 0`, `Some(v) -> v` | `None` returns before unsafe; `Some(v)` uses O2/O3. **PROVED** |

The adjacent `SAFETY` comment identifies the dominating return, derives `Some`, and names the callee precondition; it is adequate. Full case proof: for `None`, O1 makes the condition true and the function returns `0` without reaching unsafe code. For `Some(v)`, O1 makes it false; the immutable value remains `Some(v)`; O2 permits the unsafe call and O3 returns `v`. These cases exhaust valid safe inputs, proving UB freedom and the complete documented behavior.

## TCB audit log

**Log identity:** supplied `TCB.md`, SHA-256 above. **Trust policy:** only its authorized, accepted proposition is admitted; no implementation, compiler, dependency, or environmental premise is added.

`COMPAT-OPTION-184-186` is accepted by the authorized human reviewer. Its base authorities are the Rust 1.84.0 [`Option::is_none`](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.is_none) and [`Option::unwrap_unchecked`](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_unchecked) pages. Verified relevant text states: “Returns true if the option is a None value”; “Returns the contained Some value”; and “Calling this method on None is undefined behavior.” The entry admits that the exact classification and `Some(v)` result/`None` UB propositions are preserved, without weakening, for every `r` and configuration in `D`. Consumers are O1–O4 only. It establishes neither interval membership nor Cargo/compiler/backend facts. Re-audit is required for any source, support interval, base proposition, feature/target scope, or human-disposition change. No rejected, pending, unused, or additional entries exist.

## Evidence, findings, and residual scope

No tool-derived evidence was used. **Findings: none.** Every required obligation is proved; there is no documentation gap, unresolved domain, or postcondition failure.

Excluded from this source theorem are invalid values created by out-of-scope unsafe caller behavior, unsupported configurations, compiler/backend correctness, emitted binaries, and deployment properties. Re-audit on any source/API/documentation change, support/configuration expansion, material authoritative-document change, or change to `COMPAT-OPTION-184-186`.

Final attestation: all safe and unsafe surfaces, target files, controlling domain expressions, mandatory postconditions, premise applicability, and TCB consumers have a disposition; `Required subseteq Covered` is established; the verdict does not rely on CI, tests, or absence of a counterexample.
