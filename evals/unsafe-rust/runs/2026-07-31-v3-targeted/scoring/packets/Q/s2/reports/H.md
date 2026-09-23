# Focused source-only unsafe Rust review

## Claim frame and snapshot

Scope is exactly the two exported functions in the supplied `lib.rs`. The
source snapshot consists of the submitted `lib.rs` and manifest, with edition
2021 and the exact requirement `peer-unsafe-dep = "=3.4.5"`. The submitted
dependency record identifies the resolved package as `peer-unsafe-dep` 3.4.5
and supplies its declaration and public contract, but no implementation,
generated output, binary, or prior audit.

Let `C` be: Rust compiler and standard library 1.80.0; every target on which
this exact source and exact dependency resolve; and every ordinary debug or
release profile. There are no source `cfg`s, features, generated artifacts, or
profile-dependent branches in the submitted crate. The source arguments below
are therefore parametric over target and profile. Dependency-side target or
generated variation is inaccessible and is not assumed away.

The only public surfaces are the safe free function `force_unreachable` and
the unsafe free function `delegated_nonzero`; there are no public fields,
constructors, methods, traits, macros, callbacks, or invariant-bearing state.
No build, test, execution, expansion, or tool-derived evidence was used.

Combined result: **UNSOUND** for `force_unreachable`; **UNPROVED** for
`delegated_nonzero`. There is no whole-scope `PROVED` result.

## Claim 1: `force_unreachable`

**Exact claim.** For every configuration in `C`, every well-typed safe
invocation, with no caller-side safety precondition, has no Rust undefined
behavior.

**Verdict: UNSOUND**, throughout `C`.

**Complete refutation.** `lib.rs:4` exports an ordinary safe function with no
arguments or checked branch. Every invocation reaches `lib.rs:6`, which
unconditionally calls `std::hint::unreachable_unchecked`. The independently
opened Rust 1.80.0 standard-library Safety section states: “Reaching this
function is Undefined Behavior.”
([versioned authority](https://doc.rust-lang.org/1.80.0/std/hint/fn.unreachable_unchecked.html#safety)).
Thus a safe program that calls `force_unreachable()` is a valid in-domain use
whose execution reaches undefined behavior. The same source-level derivation
applies on every target/profile in `C`; optimization behavior is irrelevant.

The adjacent comment, “This site is assumed to be unreachable,” proves no
dominating fact and is contradicted by the public safe entry path. This is both
an implementation defect and a missing/false proof artifact. A minimum repair
must remove the reachable `unreachable_unchecked` operation (for example, use a
defined diverging behavior); merely strengthening the comment cannot repair a
safe API. Because the witness contains UB, it does not establish a separate
UB-free documented-postcondition refutation.

## Claim 2: `delegated_nonzero`

**Exact valid-use claim.** For every configuration in `C`, every invocation of
`delegated_nonzero(value)` for which the unsafe caller establishes the complete
documented obligation `value != 0` is free of Rust undefined behavior. No
ongoing or terminal caller obligation is documented.

**Verdict: UNPROVED**, throughout `C`; neither `UNSOUND` nor `PROVED` is
justified by this packet.

**Local derivation and precise gap.** At `lib.rs:14`, valid use gives the local
fact `value != 0`. At `lib.rs:17`, that identical `u8` value is passed directly
to `peer_unsafe_dep::duplicate_nonzero`. The submitted dependency contract's
sole caller-side safety clause is also `value != 0`. Therefore the wrapper's
call-site precondition is completely discharged for every nonzero `u8`, target,
and profile in `C`; the local SAFETY comment accurately records this step.

That step is not a proof of the unsafe dependency implementation. Full
soundness additionally requires the following smallest missing proposition:

> **DEP-IMPL.** For `peer-unsafe-dep` 3.4.5 as exactly resolved, on every target
> and ordinary debug/release profile in `C`, every execution of
> `duplicate_nonzero(v)` with `v != 0` is free of Rust undefined behavior.

No supplied source or universal evidence proves DEP-IMPL, and the human trust
decision expressly declines an `UNSAFE-DEP` assumption for it. The exact pin
fixes package version but does not establish undocumented implementation
correctness. The published unsafe caller contract establishes what this crate
must pass; it does not establish that the unavailable body fulfills its
promise. No valid UB witness is supplied either, so the fail-closed result is
`UNPROVED`, not `UNSOUND`.

The wrapper's Safety section states a precondition, not a result
postcondition. Its summary's “delegates” description is realized syntactically
by the direct call. The dependency separately promises “Returns `value`.” If
same-value return behavior is consumed as a wrapper guarantee, it is also
**UNPROVED**: DEP-IMPL must be strengthened to say that every such call returns
`v` on normal return. There is no independent UB-free refutation, so
`CONTRACT-BROKEN` is not established.

## TCB and coverage ledger

| ID | Proposition and scope | Disposition | Consumers |
|---|---|---|---|
| AXIOM-UR-1 | The quoted Rust 1.80.0 `unreachable_unchecked` Safety proposition, all targets/profiles in `C` | Accepted after direct citation verification | Claim 1 |
| DEP-IMPL | Exact dependency proposition stated above | Expressly not accepted; no implementation evidence | Claim 2 |

Obligation coverage: Claim 1's only unsafe-operation precondition fails on its
public entry path. Claim 2's dependency call precondition is proved, while
dependency implementation soundness remains open. No other local unsafe sites,
state transitions, mandatory unsafe-API postconditions, or configuration
branches appear in the submitted crate.

Residual scope is the unavailable dependency implementation and any of its
target/generated variants. Re-audit is required if either function or its
documentation changes, Rust or the supported domain changes, dependency
identity/contract/features/generated output changes, dependency source or an
accepted audit becomes available, or the TCB trust decision changes.
