# Focused unsafe-Rust source review

## Claim frame and snapshot

This review covers exactly the submitted `lib.rs` exports in package
`quantifier-target` 0.1.0 (edition 2021), with the manifest's exact dependency
`peer-unsafe-dep = 3.4.5`, the submitted dependency declaration/contract, and
the submitted evidence and trust decision. No dependency implementation,
generated output, binary, source revision/digest, or prior audit was supplied.
No build, execution, expansion, or implementation inference is used.

Let **D** be Rust and standard library 1.80.0, every target on which this exact
source and dependency resolve, and every ordinary debug or release profile.
Both claims are source-level Rust-abstract-semantics claims over D. There are no
source `cfg`s, features, profile-dependent checks, generators, FFI, allocation,
concurrency, or other configuration branches in the submitted crate. Thus the
source reasoning below is parametric over target and profile; the unavailable
dependency implementation is a proof premise gap, not a silently excluded
configuration.

The complete exported surface is the two public free functions. There are no
exported fields, types, traits, macros, statics, hidden items, or generated APIs
in the supplied source, and no invariant-bearing state.

## Evidence and TCB (`TCB.md`, submitted revision)

| ID | Disposition | Exact proposition and scope | Consumer |
|---|---|---|---|
| AXIOM-UU | accepted and independently verified | Rust 1.80.0 documents: “Reaching this function is Undefined Behavior.” The page gives no target/profile qualification, so the supplied policy applies it throughout D. [Versioned Safety section](https://doc.rust-lang.org/1.80.0/std/hint/fn.unreachable_unchecked.html#safety). | FU-1 |
| DEP-CONTRACT | controlling submitted contract, not implementation trust | `peer-unsafe-dep` 3.4.5 declares unsafe `duplicate_nonzero(value: u8) -> u8`; callers must supply `value != 0`, and its documented result is `value`. | DN-1, DN-2 |
| UNSAFE-DEP-PEER | expressly not proposed or accepted | For every configuration in D and every nonzero `u8`, the exact 3.4.5 implementation executes without Rust UB and returns the input value. | Would be required by DN-2 |

No implementation, compatibility, tool, or deployment premise is admitted.
An exact version pin fixes identity but does not prove an unsafe provider's
implementation conforms to its contract.

## Claim 1: `force_unreachable`

**Valid-use domain.** Every well-typed safe call in every configuration in D;
the safe signature permits no caller-side safety precondition.

**Claim.** Every such call and permitted execution is free of Rust UB.

**Verdict: UNSOUND throughout D.** The body has no condition or alternative
path: every invocation reaches `std::hint::unreachable_unchecked()`. FU-1's
only obligation is that this call site not be reached. A well-typed safe caller
can invoke the function, and the body necessarily reaches it. AXIOM-UU then
entails UB. This is a valid in-scope UB witness for every member of D and
refutes the universal soundness claim.

The adjacent comment merely assumes the proposition contradicted by control
flow; it supplies no fact or boundary. This is both an implementation defect
and a deficient proof artifact. The minimal resolution is to remove the
unchecked operation (for example, use defined panic/nonreturning behavior) or
remove the callable safe surface; prose cannot impose a hidden safety
precondition. The summary sentence supplies no ordinary-return postcondition,
and the UB-containing witness is not a `CONTRACT-BROKEN` witness.

## Claim 2: `delegated_nonzero`

**Valid-use domain.** Every call in D whose caller satisfies the complete
published safety condition `value != 0`; `u8` is passed by value, so the
submitted contract creates no ongoing or terminal caller obligation.

**Claim.** Every such call and permitted execution is free of Rust UB.

**Verdict: UNPROVED throughout D.** DN-1, the local call obligation, is proved:
the wrapper passes the unchanged `value`, and its caller contract is literally
the dependency call's submitted precondition. The local `SAFETY` comment
adequately records this implication.

DN-2, provider conformance, is not proved. The smallest missing soundness
proposition is:

> For every configuration in D and every `value: u8` with `value != 0`, the
> exact `peer-unsafe-dep` 3.4.5 implementation of `duplicate_nonzero(value)`
> executes without Rust undefined behavior.

No supplied source or accepted TCB entry establishes that proposition, and the
human trust decision expressly rejects assuming it. Therefore satisfying the
callee's caller precondition proves permission to call, not correctness of the
unavailable unsafe implementation. No UB witness is established, so
`UNSOUND` would be unjustified.

The dependency contract additionally promises that the result equals `value`.
If that result guarantee is treated as incorporated by the wrapper's
“Delegates” documentation, its postcondition verdict is also **UNPROVED**: add
“and returns `value`” to the missing proposition above. There is no independent
UB-free refutation, so `CONTRACT-BROKEN` is not established. Equality is not
needed merely for validity of the returned `u8` and therefore cannot repair or
worsen the soundness proof gap.

## Residual scope and review triggers

Dependency internals, generated artifacts, binaries/backend correctness, and
configurations outside D are not audited. Re-audit both claims if `lib.rs`,
Rust/standard-library version, supported targets/profiles, or the authoritative
Safety text changes. Re-audit the second claim if dependency identity, features,
contract, implementation evidence, or its human TCB disposition changes.

All in-scope obligations have dispositions: FU-1 is disproved; DN-1 is proved;
DN-2 is unproved. No tests or tool-derived evidence contribute to a verdict.
