# Focused unsafe-Rust source review

## Claim frame and snapshot

This is a source-level review of the two exported functions in the submitted `lib.rs`, relative to Rust 1.80.0 abstract semantics. The inspected snapshot consists of `lib.rs`, `Cargo.toml`, `DEPENDENCY-API.md`, `EVIDENCE.md`, `TCB.md`, and `REQUEST.md`. The manifest selects edition 2021 and pins `peer-unsafe-dep = "=3.4.5"`; the submitted dependency record says that 3.4.5 is the exact resolution. No prior audit, dependency body, generated dependency output, binary, or tool result was supplied or reused.

Define the common compilation predicate

`D(c) := rust(c) = 1.80.0 ∧ edition(c) = 2021 ∧ target(c) is a target on which this source and exact peer-unsafe-dep 3.4.5 resolve ∧ profile(c) ∈ {ordinary debug, ordinary release}`.

This is exactly the support expression in `REQUEST.md`, with the manifest facts conjoined; no target inventory or exclusion replaces it. The target and profile axes remain symbolic. The source has no `cfg`, feature declaration, generator, FFI, assembly, allocator, concurrency, or profile-dependent branch. The proofs below are therefore parametric in every `c` satisfying `D`. Unavailable dependency configuration paths are not excluded; they cause the second claim's gap.

The API inventory is complete for the submitted crate source: one safe public free function, `force_unreachable`, and one unsafe public free function, `delegated_nonzero`; there are no fields, types, traits, impls, macros, callbacks, hidden APIs, reexports, or invariants. The only unsafe operations are their respective calls to `std::hint::unreachable_unchecked` and `peer_unsafe_dep::duplicate_nonzero`.

## TCB and evidence disposition

**AXIOM-UU (accepted):** the supplied Rust 1.80.0 standard-library page was opened and verified. Its Safety section states: “Reaching this function is Undefined Behavior.” The page is versioned 1.80.0 and supplies no narrower target/profile qualification. Per the human trust decision in `TCB.md`, this proposition applies throughout `D`. Source: [`std::hint::unreachable_unchecked`](https://doc.rust-lang.org/1.80.0/std/hint/fn.unreachable_unchecked.html#safety). Consumers: OBL-FU.

**UNSAFE-DEP-PEER (not accepted):** no proposition about the implementation of exact `peer-unsafe-dep` 3.4.5 may be trusted. The exact pin establishes identity only. `TCB.md` expressly rejects such trust, and `DEPENDENCY-API.md` supplies a declaration and contract but no implementation assertion. Consumers: OBL-DN-SOUND and OBL-DN-RETURN.

TCB identity is the submitted `TCB.md`; there are no other admitted implementation, compatibility, tool, or deployment propositions.

## Claim 1 — `force_unreachable`

**Exact claim.** For every `c` satisfying `D` and every well-typed safe call to `force_unreachable()`, the execution is free of Rust undefined behavior. Safe valid use has no caller-side safety precondition.

**Verdict: UNSOUND throughout `D`.**

**Existential certificate (OBL-FU):**

1. In any `c ∈ D`, a safe caller may invoke the exported safe function `force_unreachable()`; this is a valid in-scope use.
2. On entry, the body unconditionally evaluates `std::hint::unreachable_unchecked()`. There is no branch, check, input, or invariant that can prevent reaching it.
3. Thus that valid call reaches the operation. Its required safety proposition—“this function is not reached”—is false.
4. AXIOM-UU entails that reaching it is undefined behavior.

This certificate is source-parametric over target and profile, so every member of `D` is affected. The local comment, “This site is assumed to be unreachable,” supplies no fact and is contradicted by public entry. This is both an implementation defect and a deficient proof artifact, not merely a documentation gap. No separate return-value postcondition is documented, and the UB-containing witness cannot establish `CONTRACT-BROKEN`.

Minimum resolution: remove the reachable unchecked operation (for example, use a defined panic if non-return is intended) or establish non-reachability through an enforced boundary. A prose-only restriction cannot repair a safe API.

## Claim 2 — `delegated_nonzero`

**Exact valid-use domain.** For every `c` satisfying `D` and every call with `value ∈ {1, …, 255}` that observes the unsafe boundary, every permitted execution must be UB-free. The only documented initial obligation is `value != 0`; there are no documented ongoing or terminal obligations.

**Verdict: UNPROVED.**

**Local derivation (OBL-DN-CALLER, proved over all `D`):** the submitted dependency contract requires `value != 0`. A valid wrapper call supplies exactly that fact. The body forwards the same `u8` local, without transition, to `duplicate_nonzero`; therefore the dependency's caller-side precondition holds at the unsafe call. The adjacent safety comment adequately records this local bridge.

**Smallest missing proposition (OBL-DN-SOUND):**

> For exact `peer-unsafe-dep` 3.4.5, every `c ∈ D`, and every nonzero `v: u8`, every permitted execution of `duplicate_nonzero(v)` is free of Rust undefined behavior.

Neither inspected source nor an accepted `UNSAFE-DEP` entry establishes it. Consequently the local caller obligation has coverage `D`, but provider-correctness coverage is established for no member of `D`; aggregate `Required ⊆ Covered` does not close. Absence of the body supplies no valid execution reaching UB, so the certificate for `UNSOUND` also does not close.

The dependency documentation additionally says “Returns `value`.” If that provider guarantee is included as delegated wrapper behavior, **OBL-DN-RETURN is UNPROVED**: syntactically the wrapper returns the callee's result unchanged, but the missing proposition is that every valid call to the exact 3.4.5 implementation returns its input. No UB-free falsifying execution is supplied, so `CONTRACT-BROKEN` is not established.

Minimum resolution: recursively audit the exact dependency implementation, including every path over `D`, or have an authorized reviewer accept precise `UNSAFE-DEP` propositions for UB freedom and any consumed return guarantee. The version pin or published unsafe contract alone is insufficient.

## Closure, residual scope, and triggers

For Claim 1, the refutation covers `D` parametrically. For Claim 2, only the wrapper-to-callee precondition proof covers `D`; the unavailable dependency implementation is the exact unresolved remainder. No tests or tools contribute evidence. Re-audit is required if either function or its documentation changes, `D` changes, Rust or AXIOM-UU changes, dependency identity/contract/implementation evidence changes, or the TCB disposition changes.
