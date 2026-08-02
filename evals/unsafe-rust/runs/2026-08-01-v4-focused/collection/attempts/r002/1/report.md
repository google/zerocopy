# Focused unsafe-Rust source review

## Claim, snapshot, and domain

The audited artifact is the submitted `lib.rs` for `quantifier-target` 0.1.0, edition 2021, together with `Cargo.toml`, `DEPENDENCY-API.md`, `EVIDENCE.md`, and `TCB.md`. The manifest pins `peer-unsafe-dep = "=3.4.5"`. No dependency implementation, generated output, binary, prior audit, or tool-derived result was supplied or inspected.

Let

`D = {(t,p) | Rust/stdlib = 1.80.0, this source and peer-unsafe-dep 3.4.5 resolve on target t, and p is an ordinary debug or ordinary release profile}`.

This is the controlling `Required` predicate from `REQUEST.md`; it is retained symbolically rather than replaced by an unproved target inventory. There are no `cfg`, feature, generated-source, target, or profile branches in `lib.rs`. Thus its two function bodies are identical throughout `D`. The exact dependency implementation may vary only within the resolution already quantified by `D`; its absence matters to Claim 2. Audit cutoff: this submitted source/evidence snapshot on 2026-08-01.

The complete exported surface is the safe free function `force_unreachable` and unsafe free function `delegated_nonzero`. There are no exported fields, constructors, types, traits/impls, statics, macros, hidden items, callbacks, FFI declarations, or owned representation invariants in the submitted source.

## Verdicts

| Claim | Valid-use domain | Compilation domain | Verdict |
|---|---|---|---|
| C1: every permitted execution of `force_unreachable()` is free of Rust UB | Every well-typed safe invocation; there is no caller safety precondition | `D` | **UNSOUND**, on every member of `D` |
| C2: every permitted execution of `delegated_nonzero(value)` is free of Rust UB | Unsafe invocations with a valid `u8` value satisfying the complete documented obligation `value != 0`, i.e. `value in 1..=255`; no ongoing or terminal obligation is documented | `D` | **UNPROVED** |

## C1 proof and UB certificate

`lib.rs:4` exposes `force_unreachable` as safe. Therefore a safe caller may directly invoke it, and that invocation is a valid in-scope use. Its body has no branch, check, argument, callback, or earlier operation: control reaches the call to `std::hint::unreachable_unchecked()` at `lib.rs:6`.

Accepted TCB entry **AXIOM-UU-180** is the verified Rust 1.80.0 standard-library Safety statement: “Reaching this function is Undefined Behavior.” ([exact versioned page](https://doc.rust-lang.org/1.80.0/std/hint/fn.unreachable_unchecked.html#safety)). The submitted evidence and accepted trust decision give this proposition every-target/ordinary-profile applicability, hence all of `D`.

Thus, for each `(t,p) in D`: (1) a direct safe call is valid; (2) source control flow necessarily executes the unsafe operation; (3) its required proposition, that the call site is unreachable, is false because the invocation reached it; and (4) AXIOM-UU-180 entails UB. This is a complete existential refutation for each configuration, stronger than merely failing a universal proof. The `SAFETY` comment “assumed to be unreachable” supplies no premise and is contradicted by the public safe entry path.

Minimum repair: remove the unchecked operation (for example, use a defined panic path) or establish an actually enforced control-flow invariant before it. Documentation alone cannot impose a hidden precondition on this safe API.

## C2 derivation and smallest gap

For every valid C2 call, `value != 0` holds by the exported unsafe contract at `lib.rs:11-14`. The wrapper passes that same, unchanged `value` to `peer_unsafe_dep::duplicate_nonzero` at `lib.rs:17`. The submitted exact 3.4.5 dependency declaration requires precisely `value != 0`. Therefore the local caller-side safety obligation for the dependency call is proved throughout `D`; the adjacent `SAFETY` comment accurately states this part.

That is not a proof of the unsafe dependency provider. A third-party unsafe call additionally requires the exact implementation to uphold its contract for every valid call. `DEPENDENCY-API.md` expressly says its implementation and generated output are absent and supplies no assertion about its body. `TCB.md` expressly declines any `UNSAFE-DEP` admission for 3.4.5. An exact pin establishes identity, not undocumented implementation correctness.

The smallest missing soundness proposition is:

> For every `(t,p) in D` and every `v in 1..=255`, every permitted execution of the exact resolved `peer-unsafe-dep` 3.4.5 implementation of `duplicate_nonzero(v)` is free of Rust undefined behavior.

Neither source proof nor an accepted TCB entry entails it. No valid UB witness against that implementation is supplied, so **UNSOUND** is not justified; failure of the universal derivation yields **UNPROVED**. Resolution requires either a recursive audit of the exact dependency implementation/generated artifact over `D`, or explicit human acceptance of that precise `UNSAFE-DEP` proposition.

The wrapper documents no result-equals-input postcondition; it only syntactically forwards the callee result. The dependency documentation separately says it returns `value`. That dependency postcondition is also **UNPROVED** for the same missing implementation evidence, though it is not needed to prove the wrapper’s caller-side precondition.

## Obligation and trust closure

| Obligation | Premises/coverage | Status |
|---|---|---|
| O1: safe C1 callers reach no UB | local unconditional call + AXIOM-UU-180, all `D` | Refuted; C1 UNSOUND |
| O2: C2 establishes callee precondition | exported `value != 0` contract + unchanged argument, all `D` | PROVED |
| O3: exact unsafe dependency honors its safety contract | implementation proof or accepted `UNSAFE-DEP` required; neither supplied | UNPROVED; blocks C2 |
| O4: dependency honors “Returns value” | same missing provider evidence | UNPROVED |

TCB revision is the supplied `TCB.md`: AXIOM-UU-180 is accepted; unsafe-dependency, implementation, compatibility, tool, and deployment premises are absent. No testing evidence contributes. Aggregate coverage is all `D` for the C1 refutation and O2, but O3 covers no established region, so `Required subseteq Covered` cannot be certified for C2.

Re-audit is required if either function or its documentation changes; the supported Rust/target/profile predicate changes; the Rust authority changes; the dependency identity, contract, features, implementation, or generated output becomes available or changes; or the TCB trust decision changes.
