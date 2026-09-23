# Focused source-only unsafe Rust review

## Claim, snapshot, and domain

This review covers exactly the supplied `lib.rs`, manifest, request, dependency declaration/contract, evidence, and TCB decision. The crate is edition 2021 and resolves `peer-unsafe-dep` exactly at 3.4.5. No dependency implementation, generated output, binary, prior audit, or tool result was supplied or used.

Let

`D = { Rust/compiler/stdlib 1.80.0 } × { target t | this exact source and peer-unsafe-dep 3.4.5 resolve on t } × { ordinary debug, ordinary release }`.

This is exactly the support expression in `REQUEST.md`, retained symbolically: no target enumeration, exclusion, version extrapolation, or policy merge is performed. The only visible source configuration axis is profile, and neither export is profile- or target-conditional. Any dependency-internal configuration remains inaccessible.

The two exported surfaces are the safe free function `force_unreachable()` and unsafe free function `delegated_nonzero(u8) -> u8`. There are no supplied public fields, constructors, traits/impls, macros, FFI, generated APIs, or invariant-bearing state. Each claim below quantifies independently over all of `D`.

## TCB and evidence disposition

**AXIOM-UU (accepted):** the verified Rust 1.80.0 standard-library Safety section for [`std::hint::unreachable_unchecked`](https://doc.rust-lang.org/1.80.0/std/hint/fn.unreachable_unchecked.html#safety) says, “Reaching this function is Undefined Behavior.” The page is explicitly Rust 1.80.0 and states no narrower target/profile qualification. Consumers: F-OBL-1. Re-audit on a Rust/domain or cited-contract change.

**UNSAFE-DEP-345 (rejected/not admitted):** the proposition that the exact `peer-unsafe-dep` 3.4.5 implementation is UB-free for every documented-valid `duplicate_nonzero` call, and returns its argument, over `D`. The exact pin fixes identity only. `TCB.md` expressly declines implementation trust, and no implementation audit exists. Consumers blocked: D-OBL-2 and D-POST-1. Re-audit if the implementation is supplied/audited or this precise entry is accepted.

No other premise or tool evidence is admitted.

## Claim F — `force_unreachable`

**Theorem:** for every configuration in `D`, every well-typed safe invocation of `force_unreachable()` is free from Rust undefined behavior, with no caller safety precondition.

**Verdict: UNSOUND over `D`, relative only to AXIOM-UU.**

UB certificate (F-OBL-1):

1. `force_unreachable()` is public and safe; therefore `force_unreachable();` is a valid in-scope safe use in every configuration where the crate resolves.
2. Its body has no branch, guard, argument, callback, or prior diverging operation. Calling it necessarily executes `std::hint::unreachable_unchecked()`.
3. That execution makes the callee’s required proposition—its site is not reached—false.
4. AXIOM-UU entails UB when it is reached. Thus this valid use reaches UB. The same source-level derivation is parametric in target and profile, so it covers every member of `D`.

The adjacent comment, “This site is assumed to be unreachable,” supplies no fact and is contradicted by control flow. This is both an implementation defect and a deficient proof artifact, not merely failure to prove a universal claim. Minimum resolution: remove the unconditional unsafe operation (for example, use a defined panic if that is the intended behavior), then audit the changed artifact. A prose precondition cannot repair this safe API.

No additional postcondition claim is needed to establish this verdict; any execution used above contains UB and therefore cannot serve as a defined-behavior postcondition refutation.

## Claim D — `delegated_nonzero`

**Theorem:** for every configuration in `D` and every `value: u8` with `value != 0`, every invocation satisfying that documented caller obligation is free from Rust UB.

**Verdict: UNPROVED over all of `D`.** This is not an `UNSOUND` finding.

Obligation ledger:

- **D-OBL-1 — dependency call precondition: PROVED.** The submitted `duplicate_nonzero` contract requires `value != 0`. The wrapper’s unsafe contract requires the identical predicate, and the source forwards the unchanged `value`. Hence every valid wrapper call satisfies the dependency’s documented caller-side precondition. This proof is parametric over `D`; the local `SAFETY` comment accurately states this limited bridge.
- **D-OBL-2 — callee implementation behavior: UNPROVED.** Soundness additionally requires that exact dependency implementation to avoid UB for every valid call over `D`. Unsafe-API documentation does not prove its implementation honors the promise. The body is unavailable and UNSAFE-DEP-345 is rejected. This is the smallest missing proposition.
- **D-POST-1 — returned value: UNPROVED if `Returns value` is consumed as the delegated result guarantee.** The wrapper returns the callee expression directly, but proving the callee returns its argument requires the rejected proposition. There is no UB-free falsifying execution in the packet, so `CONTRACT-BROKEN` is not established. The wrapper’s narrower structural statement that it delegates to the peer is visible directly in source.

Because D-OBL-2 lacks a derivation in every required case, the certified aggregate `Covered` set for Claim D is empty and `D ⊄ Covered`. Conversely, the packet establishes no particular valid call on which the unavailable dependency reaches UB, so none of the reachability/false-proposition/consequence links needed for an `UNSOUND` certificate exists. Absence of trust is not a counterexample.

Minimum resolution is either a recursive audit of the exact dependency implementation and its configuration closure, or human acceptance of UNSAFE-DEP-345 with the exact soundness and return propositions. Re-review on changes to either source/API contract, Rust or supported domain, dependency identity/features/resolution, the Rust citation, or the TCB disposition.

## Residual scope and combined result

Dependency internals and generated artifacts are inaccessible and intentionally not inferred. Builds, tests, execution, macro expansion, binaries, compiler/backend correctness, and broader robustness are outside this source-level review. Claim F is **UNSOUND**; Claim D soundness and the dependency-derived return guarantee are **UNPROVED**. Therefore there is no combined `PROVED` result.
