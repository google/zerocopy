# Focused unsafe Rust source audit

## Claim, snapshot, and domain

The audited snapshot is the submitted `quantifier-target` 0.1.0 package: `lib.rs`, `Cargo.toml`, `DEPENDENCY-API.md`, `EVIDENCE.md`, and `TCB.md`. The two exported surfaces are the safe function `force_unreachable()` and the unsafe function `delegated_nonzero(u8) -> u8`. No fields, traits, macros, generated artifacts, `cfg`s, features, build scripts, FFI, concurrency, or other public surfaces are supplied. No build or dynamic evidence is used.

Let

`D = { (Rust 1.80.0, target t, profile p) | this exact source and peer-unsafe-dep 3.4.5 resolve on t, and p is an ordinary debug or ordinary release profile }`.

This is exactly the support expression in `REQUEST.md`; it is retained symbolically rather than replaced by a sampled target inventory. `Cargo.toml` fixes edition 2021 and declares `peer-unsafe-dep = "=3.4.5"`; `DEPENDENCY-API.md` confirms that exact resolution. There are no other submitted configuration axes. Thus `Required = D`. The arguments below are parametric in `t` and `p`, so no target enumeration or profile sampling is used.

The TCB for this report is the submitted `TCB.md` (“TCB-SUBMITTED”). Its sole accepted entry is:

- **AXIOM-UU-1 (Rust authority):** for Rust 1.80.0 throughout `D`, reaching `std::hint::unreachable_unchecked` is undefined behavior. The exact official page was opened and independently verified; its Safety section says, “Reaching this function is *Undefined Behavior*.” ([Rust 1.80.0 documentation](https://doc.rust-lang.org/1.80.0/std/hint/fn.unreachable_unchecked.html#safety))

The dependency declaration and submitted documentation establish identity and contract text, not implementation correctness. The human reviewer expressly declined an `UNSAFE-DEP` admission for `peer-unsafe-dep` 3.4.5. There are no compatibility, implementation, tool, or deployment assumptions.

## CLAIM-FORCE — `force_unreachable`

**Exact theorem.** For every configuration in `D` and every well-typed safe invocation of `force_unreachable()`, every permitted execution is free of Rust undefined behavior. Valid use has no input, state, temporal, or caller-side safety precondition because this is a safe API.

**Verdict: UNSOUND throughout `D`, relative to TCB-SUBMITTED.**

Complete existential certificate:

1. **Valid in-scope use:** ordinary safe Rust invokes the exported safe function `force_unreachable()` in any configuration in `D`. The API imposes no precondition, so this invocation is valid.
2. **Reachability:** the function body has no condition or earlier exit; its sole expression evaluates `unsafe { std::hint::unreachable_unchecked() }`. Therefore that invocation reaches the unsafe operation.
3. **False safety proposition:** the operation requires that it not be reached. Step 2 proves the negation for the witness.
4. **UB consequence:** AXIOM-UU-1 directly entails undefined behavior upon reaching it.

The same source-local argument and target/profile-wide axiom cover every member of `D`; optimization level is irrelevant to the source-level UB event. The comment “This site is assumed to be unreachable” supplies no fact and is contradicted by every call. This is both an implementation defect and a deficient proof comment, not merely missing documentation. Because the witness execution contains UB, it establishes no separate UB-free postcondition refutation.

Minimal repair: remove this safe path to `unreachable_unchecked`; for an intentionally callable safe API, use defined behavior such as a panic. Any changed artifact requires a fresh audit.

## CLAIM-DELEGATED — `delegated_nonzero`

**Exact theorem.** For every configuration in `D`, every `value: u8` with `value != 0`, and every unsafe invocation satisfying that sole documented precondition, every permitted execution of `delegated_nonzero(value)` is free of Rust undefined behavior. There are no documented ongoing or terminal caller obligations.

**Verdict: UNPROVED throughout `D`, relative to TCB-SUBMITTED.**

The complete available derivation is:

1. The wrapper contract requires `value != 0`.
2. The submitted contract of exact dependency API `peer_unsafe_dep::duplicate_nonzero` 3.4.5 has the identical caller-side safety precondition.
3. At the only unsafe call, the argument is the unchanged `value`. Therefore every valid wrapper invocation satisfies the dependency call’s caller-side obligation. The adjacent SAFETY comment adequately records this local implication.
4. The wrapper immediately returns the dependency call’s result and contains no other operation that can close the provider-side obligation.

The smallest missing soundness proposition is:

> **DEP-SOUND-1:** For every configuration in `D` and every nonzero `v: u8`, every execution of the exact `peer-unsafe-dep` 3.4.5 implementation of `duplicate_nonzero(v)` is free of Rust undefined behavior.

Neither an exact pin nor the submitted unsafe API declaration proves DEP-SOUND-1. The implementation, generated output, prior audit, and binary are absent, and TCB-SUBMITTED expressly refuses to trust them. Consequently the caller-side obligation has coverage `D`, but the required provider-side obligation has no established covered region; their pointwise conjunction does not establish `Required ⊆ Covered`.

No `UNSOUND` certificate exists: the unavailable body supplies no proved valid execution reaching a false safety proposition. Failure of the universal proof therefore yields `UNPROVED`, not `UNSOUND`.

The dependency documentation also promises “Returns `value`.” If that provider guarantee is treated as a mandatory postcondition of this delegation, the wrapper’s `result == value` postcondition is likewise **UNPROVED**: the additional smallest missing proposition is that every valid, UB-free call to this exact implementation returns its input. There is no UB-free counterexample, so `CONTRACT-BROKEN` is not established.

Minimal resolution: supply and recursively audit the exact dependency implementation and all generated/configuration-specific artifacts, or obtain explicit human acceptance of narrowly stated `UNSAFE-DEP` propositions covering DEP-SOUND-1 (and the return guarantee if consumed) over all of `D`.

## Closure, residual scope, and triggers

For CLAIM-FORCE, the certificate is target- and profile-parametric over `D`. For CLAIM-DELEGATED, the unresolved dependency proposition affects all of `D`; no tested subset can repair it. There is no tool-derived evidence. Binary/backend correctness and targets where the exact package does not resolve are outside this source-level theorem.

Re-audit is required if either exported contract or body changes; Rust/standard-library version or cited semantics changes; the supported target/profile predicate changes; dependency identity, features, documentation, implementation, generated output, or trust disposition changes; or new public/generated surfaces appear.
