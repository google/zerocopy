# Unsafe Rust V2 Forward-Evaluation Oracle

> **Evaluator-only material.** Never expose this file, its labels, its atoms,
> or its curated authority list to an evaluated agent.

## Purpose and Conditions

This oracle evaluates the exact V2 package against the frozen V1 package and
the frozen V1 core ablation. V2 versus V1 is the primary revision comparison;
V1 versus the core ablation is only a historical bridge.

Every mode has five fresh reports in each condition. Score propositions, not
keywords or preferred report structure. Equivalent explicit reasoning passes.
A material Rust premise passes only when the report verifies applicable
versioned Rust Reference or standard-library text or leaves the result
appropriately unresolved.

## New Generalization Modes

### U — undefined behavior and documented behavior

- **U1:** `classify(0)` reaches `unreachable_unchecked`; a valid safe call
  proves the API `UNSOUND`.
- **U2:** That UB-containing execution does not prove a defined failure to
  panic. It leaves the input-zero panic guarantee `UNPROVED`, and cannot by
  itself establish `CONTRACT-BROKEN`.
- **U3:** `classify(1)` is an independent UB-free execution returning `2`, so
  the normal-return postcondition is `CONTRACT-BROKEN`.

A report commits a hard error if it calls the API sound, uses an observation
from the input-zero execution as a behavioral refutation, claims observations
before or after that UB remain guaranteed, or conflates/misses the independent
input-one refutation.

### D — conflicting and conditional support predicates

- **D1:** State both current published predicates and the disputed regions;
  do not invent precedence. Their differences are `fast` x86_64 on Rust 1.79
  and `fast` aarch64 on Rust 1.80–1.81.
- **D2:** Audit the conservative union while distinguishing that review domain
  from the unresolved actual project promise. The developer toolchain pin and
  sampled CI matrix neither resolve the conflict nor exhaust support.
- **D3:** Prove both source branches over the entire union, parametrically or
  by exhaustive partition. The union is: non-`fast` on both targets for
  1.79–1.82; `fast` x86_64 for 1.79–1.82; and `fast` aarch64 for 1.80–1.82.
  The source is sound over this union even though the controlling project
  predicate remains unresolved.

A report commits a hard error if it silently chooses a policy, calls the union
the recovered project promise, contracts any union region, treats CI or the
developer pin as exhaustive, asserts closure without covering the union, or
promotes project/Cargo policy to a Rust axiom.

### V — exact-version `pointer::add` boundary

- **V1:** `[u8; 0]` has size zero, so `.add(1)` computes a zero-byte offset.
- **V2:** Rust 1.79 still requires start and result within or one-past one
  allocation. Null satisfies neither; the 1.79 safe API is `UNSOUND`.
- **V3:** Rust 1.80 explicitly makes zero-byte offset calls always
  well-defined. With no dereference, the narrow 1.80 source claim is `PROVED`.
- **V4:** Partition the two supported versions and report the combined claim
  `UNSOUND`; never project the 1.80 relaxation backward.

A report commits a hard error if it gives an unproved uniform verdict, applies
later documentation to 1.79, gives either regional verdict incorrectly, or
misses the null safe-call witness or zero-size derivation.

### I — producer premise promoted into a type invariant

- **I1:** Enumerate both producers. `from_writable`'s precondition concerns
  values produced by valid invocations of that constructor; it is not a
  universal `Buffer` invariant.
- **I2:** `overwrite` needs `ptr` valid for writes. `from_static` does not
  establish that fact, so both copies of the local comment fail despite field
  privacy.
- **I3:** The fully safe `Buffer::from_static().overwrite(0)` execution writes
  while the shared reference to the same immutable byte is live for the
  `with_live` call. The Reference immutable-byte rule and `ptr::write` contract
  establish UB; the safe API is `UNSOUND`.

A report commits a hard error if it uses `from_writable` to close all values,
treats privacy as proof that this is the only producer, misses the safe witness,
or stops at vague proof debt despite the direct authoritative UB derivation.

## Corrected V1 Stress Modes

### T — ticket

- **T1:** With debug assertions disabled, `ticket(0)` reaches
  `NonZeroUsize::new_unchecked(0)` and UB; the current safe API is `UNSOUND`.
- **T2:** The same UB execution leaves the always-panic guarantee `UNPROVED`,
  not `CONTRACT-BROKEN`.
- **T3:** A checked `NonZeroUsize::new(id).expect(...)` candidate preserves
  signature, panic behavior, and configuration scope, but remains uncertified
  until implemented and freshly audited.

### C — configuration-dependent character conversion

- **C1:** In compact builds with debug assertions disabled, a surrogate input
  reaches UB. That region is `UNSOUND`; its panic promise is only `UNPROVED`
  from that execution.
- **C2:** The noncompact branch is separately sound and behaviorally correct.
- **C3:** A checked compact conversion can preserve both signatures, behavior,
  and the complete support set, but the unimplemented candidate is not
  `PROVED`.

### H — proof/performance tradeoff

- **H1:** Rust 1.70's `add(0)` contract plus a valid dangling empty slice makes
  the current Rust-1.70+ API `UNSOUND`.
- **H2:** The safe wrapping-iterator candidate preserves source behavior, but
  benchmark compliance remains `UNPROVED` without evidence.
- **H3:** Keep current-source verdict, candidate proof plan, and performance
  evidence separate. The unsound current loop is not an acceptable fallback
  if the candidate misses its benchmark; the candidate is not yet `PROVED`.

For T, C, and H, any proposal laundering or use of a UB-containing execution
as a defined behavioral counterexample is a hard error. An incorrect exact
Rust-version result is also a hard error.

## Unchanged Regression Controls

### A — immutable acceptance target

- **A1:** The literal `Piece` contract is false: `"tail"` is not a direct
  declared field, and the projected array element is not a direct field.
- **A2:** Separate that contract failure from soundness; the shown projection
  reaches a valid `u32`, so no UB counterexample is established.
- **A3:** Do not replace the literal contract with inferred intent or redesign
  an acceptance-only immutable snapshot.

### P — published contract

- **P1:** Prove `Page`'s complete `Block` contract and `first`'s current
  soundness.
- **P2:** Unknown public consumers and implementers prevent weakening the
  published 1.x contract merely because repository search finds only `first`.
- **P3:** Distinguish compatible private/internal simplification from sealing,
  weakening, or removal that needs an authorized 2.0 migration; do not certify
  an unimplemented proposal.

### N — newly implemented snapshot

- **N1:** Freshly derive both safe alias witnesses and report the current
  snapshot `UNSOUND`.
- **N2:** Identify receiver-unbound `'a` return lifetimes, not the presence of
  a raw pointer alone, as the enabling defect.
- **N3:** Repair both accessors with receiver-bound output lifetimes and keep
  the proposal uncertified pending a new exact-source audit.

## Authority Review

Two independent reviews—one by the primary evaluator and one by a separate
authority reviewer—confirmed U, D, V, anchored I, and H before the first report.
The critical retrieved pages and SHA-256 digests were:

| Proposition | Exact official page | Retrieved HTML SHA-256 |
|---|---|---|
| U | `https://doc.rust-lang.org/1.80.0/std/hint/fn.unreachable_unchecked.html` | `555597c0db28f65466dd734a9f57d4aaca8abe7f6e0e256b3f0d64a877529fd3` |
| V pointer 1.79 | `https://doc.rust-lang.org/1.79.0/std/primitive.pointer.html#method.add` | `543e6e9014b30c36af439be6c959ee25c9929d9388b0c21202a656b98e8bac48` |
| V pointer 1.80 and I method routing | `https://doc.rust-lang.org/1.80.0/std/primitive.pointer.html` | `c0f0f02c9ac5c977d5da74d75f712338dea046d6770a3fea5ecb483df7cdae34` |
| V array layout 1.79/1.80 | versioned `reference/type-layout.html#array-layout` | `f1e8382edb288ae23f8a2e654910addf3540f48f635bec80f0242f3c58b4b78c` |
| V null 1.79 | `https://doc.rust-lang.org/1.79.0/std/ptr/fn.null.html` | `e628dc5b620c62dd346190e1e3fab3f0b822620597ff2aafb3214d775b6ae230` |
| V null 1.80 | `https://doc.rust-lang.org/1.80.0/std/ptr/fn.null.html` | `65db72c3d44a2e8134111c91ec0dda1e76f443f2a8a0a5d10f89b5a6d477c049` |
| I UB Reference | `https://doc.rust-lang.org/1.80.0/reference/behavior-considered-undefined.html` | `9f6deb0ebbdddd0362a3406ccb872c84108034c55c7d5b3e124d50b5d2cae9a9` |
| I `ptr::write` | `https://doc.rust-lang.org/1.80.0/std/ptr/fn.write.html` | `f31ae6a889da541592c796e521b7abb18fa4b7a4dc25da32e839d076fe8aeba3` |
| D slice 1.79 | `https://doc.rust-lang.org/1.79.0/std/primitive.slice.html` | `b9a466e18557bae5384d1541b639a95397a296c33e4fb655304b9eb6278043ca` |
| D slice 1.80 | `https://doc.rust-lang.org/1.80.0/std/primitive.slice.html` | `c9665bb0d18c354c73a8098c596feef49b58f23581ec799af851a2d9c60c8bee` |
| D slice 1.81 | `https://doc.rust-lang.org/1.81.0/std/primitive.slice.html` | `d064c2ef6b2a3234b5ef2140ebefc8fe91bf62368a7a77ac63794bdb114bfea4` |
| D slice 1.82 | `https://doc.rust-lang.org/1.82.0/std/primitive.slice.html` | `19f1230aa1d36c1e19eb9077a14bdb12b252d327ec3bab8c1f69d74a636a86ef` |
| H pointer 1.70 | `https://doc.rust-lang.org/1.70.0/std/primitive.pointer.html#method.add` | `84872b7f0bf29f608393be06762820560b65170398f792cc0e69b081864ddf4d` |
| H slice 1.70 | `https://doc.rust-lang.org/1.70.0/std/slice/fn.from_raw_parts.html` | `93388f8e05c06d18ad34fc6edcbd41d1e2bec09d78853e68bc891c2126536e60` |
| H dangling pointer 1.70 | `https://doc.rust-lang.org/1.70.0/std/ptr/struct.NonNull.html#method.dangling` | `ee7d2bc8a4ebe4bb90838ff3c23715494c5d6ae95e828635bdba1587c21b86b6` |

The Reference/std pages are the oracle authorities. Release notes, prior
adjudications, and this oracle are explanatory evidence only.

## Preregistered Gates

The V2 revision passes only if:

- zero V2 reports contain a hard error;
- every atom above passes in all five V2 replicates;
- no V2 report certifies an unimplemented proposal;
- U2, T2, and C1 apply the UB/postcondition rule in all five V2 reports;
- V1–V4 and H1 close exact-version reasoning in all five V2 reports;
- D1–D3 recover and audit the ambiguous union without contraction in all five;
- I1–I3 reject producer-premise promotion in all five; and
- every A, P, and N control atom passes in all five V2 reports.

Report V2–V1 and V1–core differences per mode. Do not pool heterogeneous modes
into one headline theorem. If a gate fails, preserve the run and do not widen
validation or edit the frozen package in place.
