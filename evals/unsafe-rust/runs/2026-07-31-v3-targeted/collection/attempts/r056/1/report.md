# Focused unsafe-Rust source review

## Claims and verdicts

Audit cutoff: 2026-08-01. `C` is the exact submitted source packet, compiled with Rust/rustc/stdlib 1.80.0 and edition 2021, for every target on which this source and the exact resolved `peer-unsafe-dep` 3.4.5 package resolve, under every ordinary debug or release profile. There are no crate features, `cfg` branches, generators, build scripts, or generated artifacts in the packet.

| Claim | Exact valid use | Soundness verdict |
|---|---|---|
| `force_unreachable` | Every well-typed safe invocation in `C`; there is no caller-side safety precondition. | **UNSOUND** (`F-1`) |
| `delegated_nonzero` | Every invocation in `C` for which the unsafe caller establishes `value != 0` (equivalently, `value` is in `1..=255`); there are no documented ongoing or terminal obligations. | **UNPROVED** (`F-2`) |

These are separate source-level Rust abstract-semantics claims. The first verdict does not imply the second. No binary-, backend-, deployment-, security-, or probabilistic claim is made.

The dependency contract also documents `duplicate_nonzero(value)`'s postcondition “Returns `value`.” Any corresponding claim that `delegated_nonzero(value)` returns its input is **UNPROVED** for the same missing proposition as `F-2`; no UB-free refutation is established, so `CONTRACT-BROKEN` is not justified. No additional robustness property was requested.

## Snapshot, boundary, and configuration coverage

The audited packet comprises `REQUEST.md`, `Cargo.toml`, `lib.rs`, `DEPENDENCY-API.md`, `TCB.md`, and `EVIDENCE.md`. Key SHA-256 identities are `lib.rs` `778d644359b84bc0e519ed7220bfcadfbba578e2c9fd4c474ce742c4b0021ceb`, `Cargo.toml` `57b66359b9447d371fa68a2cfdc04f49176b1a3ce815bb96027b2f76d917d0a7`, `DEPENDENCY-API.md` `6f29bb01be852cc9cf2861d0447ef0b2001350f090ab947866d1495d68a27fc2`, and TCB revision `TCB.md` `86796b85804436595c0f6ffbfa773dac4fce5cbfe28e02223c802a055037d0f4`. The dependency is exactly pinned by `=3.4.5`; that fixes package/version identity but does not prove its unsafe implementation.

The only exported surfaces in the submitted source are the safe free function `force_unreachable` and unsafe free function `delegated_nonzero`. There are no submitted fields, types, constructors, traits/impls, methods, statics, callbacks, macros, reexports, hidden items, FFI surfaces, or state invariants. The dependency is called but not reexported. Its implementation, generated output, prior audit, and binary are inaccessible and excluded from inspection, not silently assumed correct.

The proofs below are parametric over target and profile. The source selects the same statements in every member of `C`; no debug assertion, overflow-dependent expression, target fact, panic mode, allocator, concurrency, or generated-code premise is used. `AXIOM-UU-1` expressly covers all targets/profiles in `C`. The local nonzero dataflow proof is likewise configuration-independent. The unresolved dependency-implementation obligation remains unresolved throughout `C`. No configuration was sampled or tested.

## TCB audit log

TCB ID is the `TCB.md` digest above. Trust policy admits the verified versioned Rust authority but expressly rejects trust in the unavailable third-party unsafe implementation.

| ID | Category/disposition | Exact proposition, scope, and consumer |
|---|---|---|
| `AXIOM-UU-1` | AXIOM / accepted | Rust 1.80.0 `std::hint::unreachable_unchecked`: [“Reaching this function is Undefined Behavior.”](https://doc.rust-lang.org/1.80.0/std/hint/fn.unreachable_unchecked.html#safety) Verified at the exact versioned page; it states no narrower target/profile condition. Applies throughout `C`; consumed by `O-F1`. Re-review if Rust scope or cited contract changes. |
| `UNSAFE-DEP-1` | UNSAFE-DEP / rejected, not consumable | For exact `peer-unsafe-dep` 3.4.5 throughout `C`, every execution of `duplicate_nonzero(v)` with `v != 0` is UB-free and returns `v`. No implementation/audit is supplied, and the human trust decision expressly declines admission. Blocks `O-D2` and the return postcondition. Resolve by recursive source audit or explicit human acceptance of this exact proposition; re-review on dependency identity, contract, feature, target, or profile change. |

There are no SAFE-DEP, tool, implementation, external, environment, or compatibility entries. No tool-derived evidence was supplied or consumed.

## Obligation ledger and proofs

### `O-F1` — `force_unreachable` must be sound for every safe call

At `lib.rs:4`, any caller may enter through a safe, argument-free public function. Control then unconditionally reaches the sole statement, the unsafe call at `lib.rs:6`; there is no branch, check, input, or invariant that can make this site unreachable. By `AXIOM-UU-1`, reaching that call is UB. Thus the well-typed safe invocation `force_unreachable()` is a valid in-scope use whose execution reaches UB, uniformly over `C`. This proves **UNSOUND**.

The line-5 comment, “This site is assumed to be unreachable,” supplies no fact and is circular: the public function entry makes the site reachable. It is therefore a deficient proof artifact as well as an implementation defect.

### `O-D1` — satisfy the dependency's caller precondition

For a valid call of `delegated_nonzero`, its published safety contract at `lib.rs:11-13` gives `value != 0`. Line 17 passes that same, unmodified `u8` to `duplicate_nonzero`. The submitted dependency contract requires exactly `value != 0`. Identity plus the caller fact entails that precondition for every valid wrapper call throughout `C`. **PROVED.** The adjacent comment adequately explains this caller-side step.

### `O-D2` — establish provider implementation soundness

The wrapper's soundness additionally requires every permitted execution of the dependency call, after `O-D1` is satisfied, to be UB-free. A declaration and caller contract constrain valid callers; they do not prove that an unavailable unsafe implementation honors its promise. `UNSAFE-DEP-1` is rejected, and no recursive implementation proof exists. The smallest missing proposition is: “For every `v: u8` with `v != 0` and every configuration in `C`, every execution of exact `peer-unsafe-dep` 3.4.5 `duplicate_nonzero(v)` is free of Rust UB.” Therefore `O-D2`, and hence `delegated_nonzero` soundness, is **UNPROVED**. No valid UB witness is established, so `UNSOUND` is not justified.

The return-equality guarantee separately needs the additional conjunct that every such UB-free execution returns `v`; it is also absent. No proof-comment rewrite alone can close either provider obligation.

## Findings and required resolutions

`F-1` (**UNSOUND**, all of `C`): remove the unconditional unsafe call or replace it with defined behavior such as a safe panic. Merely changing the comment cannot repair the proof. Making a formerly safe API unsafe or changing documented behavior requires compatibility review. Re-audit all uses and all of `force_unreachable` after remediation.

`F-2` (**UNPROVED**, all of `C`): recursively audit the exact dependency implementation over `C`, or obtain authorized acceptance of `UNSAFE-DEP-1` with exact identity and configuration scope. An exact version pin and published unsafe contract are insufficient. Re-audit both soundness and return behavior after resolution.

Residual scope is limited to the unavailable dependency implementation and its omitted artifacts. Review is also triggered by any source/API contract change, Rust version or support-domain change, dependency resolution/contract change, or TCB disposition change. There is no authoritative Rust-documentation gap and no skill-guidance gap identified.
