# Focused unsafe-Rust source audit

Reviewed 2026-08-01. This report concerns the submitted `lib.rs`, manifest,
dependency contract, evidence policy, and TCB only. It is a source-level review;
no build, execution, expansion, dependency implementation, binary, or prior
audit was inspected.

## Domain, snapshot, and boundary

Let `Dcfg(c)` mean: the compiler and standard library are exactly Rust 1.80.0,
the crate uses edition 2021, the profile is an ordinary debug or release
profile, and the target is one on which this exact source and
`peer-unsafe-dep = 3.4.5` resolve. This is exactly the support expression in
`REQUEST.md:8-11`, with dependency identity fixed by `Cargo.toml:6-7` and
`DEPENDENCY-API.md:3-4`; no target enumeration is inferred. The source contains
no `cfg`, feature, generator, macro, target, or profile branch, so both source
paths below are parametric over every `c` in `Dcfg`. Dependency internals may
still vary and are not silently covered.

The complete exported surface in the submitted source is:

| ID | Surface | Boundary |
|---|---|---|
| API-F | `pub fn force_unreachable()` (`lib.rs:4-7`) | Safe: every well-typed safe call is valid; there is no caller safety obligation. |
| API-D | `pub unsafe fn delegated_nonzero(value: u8) -> u8` (`lib.rs:9-18`) | Unsafe: a call is valid exactly when `value != 0`; no ongoing or terminal obligation is documented. |

There are no representation fields, constructors, traits/impls, callbacks,
reexports, hidden items, generated APIs, or state invariants in the supplied
source. The two calls at `lib.rs:6` and `lib.rs:17` are the complete unsafe-site
inventory.

## Claims and strongest verdicts

| Claim | Exact full valid-use domain | Verdict |
|---|---|---|
| C-F | Every `(c, call)` with `c in Dcfg` and any well-typed safe invocation of `force_unreachable()` | **UNSOUND** |
| C-D | Every `(c, v, state, execution)` with `c in Dcfg`, `v: u8`, `v != 0`, and every permitted execution of `delegated_nonzero(v)` | **UNPROVED** |

### C-F — complete existential UB certificate

1. **Valid use.** `force_unreachable` is exported as a safe, zero-argument
   function. Thus `force_unreachable()` is a valid safe invocation for any
   `c in Dcfg`; the packet states an exact resolved dependency, so the declared
   supported set is not being replaced by an invented configuration.
2. **Reachability.** On entry, the body has no condition or alternative exit:
   its first and only statement calls `std::hint::unreachable_unchecked()`
   (`lib.rs:4-6`). Therefore that call site is reached.
3. **False required proposition.** The callee requires that it not be reached;
   step 2 proves the opposite. The comment “This site is assumed to be
   unreachable” is an unsupported assumption and is directly falsified by the
   safe-call witness.
4. **UB consequence.** The checked Rust 1.80.0 standard-library Safety text
   states: “Reaching this function is Undefined Behavior.”
   ([exact versioned authority](https://doc.rust-lang.org/1.80.0/std/hint/fn.unreachable_unchecked.html#safety)).
   The page identifies Rust 1.80.0 and gives no narrower target/profile
   qualification. Hence the witness reaches UB for every `c in Dcfg`.

This establishes `UNSOUND`, not merely failure to prove. The UB-containing
execution cannot establish a separate contract-broken witness. No broader safe
API behavior was requested. Minimal remediation is to remove
`unreachable_unchecked` (for example, use a defined panic) or introduce a real
compiler-enforced unsafe boundary with a sufficient contract.

### C-D — proved forwarding obligation; smallest missing proposition

The controlling wrapper precondition is exactly `v != 0` (`lib.rs:11-14`). The
submitted dependency contract requires exactly the same proposition
(`DEPENDENCY-API.md:9-12`). For every valid wrapper call, substitution of the
same unchanged `value` into the direct call at `lib.rs:17` therefore proves the
dependency caller-side safety precondition. It also proves the wrapper's stated
delegation behavior: the selected function is called with that same value.
There is no branch, mutation, state invariant, or configuration-dependent
source path. The adjacent comment correctly records this local implication.

That implication is insufficient to prove wrapper soundness. A third-party
unsafe API additionally requires proof that its exact implementation honors its
contract for every valid call. The smallest missing proposition is:

> For every `c in Dcfg` and every `v: u8` with `v != 0`, every permitted
> execution of the exact `peer-unsafe-dep` 3.4.5
> `duplicate_nonzero(v)` implementation is free of Rust undefined behavior.

No supplied fact entails it: `DEPENDENCY-API.md:15-17` says the implementation
and generated output are absent and supplies no body assertion; `TCB.md:5-7`
expressly declines an `UNSAFE-DEP` entry. Absence of such a universal proof does
not prove an executable counterexample, so `UNSOUND` is not justified. The
dependency documentation also says “Returns `value`”; if that provider
postcondition is treated as a wrapper return guarantee, its implementation
proof is missing for the same reason. The wrapper itself does not explicitly
document a return-value postcondition.

Minimal resolution is either a recursive audit proving the proposition over
all `Dcfg`, or human acceptance of that exact proposition as an
`UNSAFE-DEP` TCB entry. An exact version pin freezes identity but supplies
neither result. Replacing the delegation with a locally proved safe operation
would remove this trust requirement.

## Obligation and TCB reconciliation

| Obligation | Status | Basis |
|---|---|---|
| O-F1: do not reach `unreachable_unchecked` | **Refuted** | C-F steps 1-3 |
| O-F2: reaching it entails UB | **Proved** | AXIOM-UU below |
| O-D1: pass nonzero to dependency | **Proved** | Wrapper contract plus unchanged dataflow |
| O-D2: exact unsafe dependency is UB-free for every valid call | **Unproved** | Missing/rejected UNSAFE-DEP proposition |
| O-D3: invoke selected peer with the same value | **Proved** | Direct call expression at `lib.rs:17` |

**TCB-SUBMITTED revision:** the supplied `TCB.md`.

| ID | Category/disposition | Exact proposition and scope | Consumer/trigger |
|---|---|---|---|
| AXIOM-UU | AXIOM, accepted and independently citation-checked | On Rust 1.80.0 across `Dcfg`, reaching `std::hint::unreachable_unchecked` is UB. | O-F2; recheck if Rust version/domain or cited text changes. |
| UNSAFE-DEP-345 | UNSAFE-DEP, rejected/not admitted | The missing O-D2 proposition above. | Blocks C-D; revisit on implementation audit or explicit trust decision. |

No tool-derived evidence or other accepted implementation, compatibility,
deployment, or dependency premise exists. The dependency contract is controlling
API text, not evidence that its unavailable unsafe implementation fulfills it.

## Residual scope and re-audit triggers

Dependency source/generated output, binaries, compiler/backend correctness,
custom profiles, targets outside `Dcfg`, and behavioral properties not stated
above remain unaudited. Re-audit on any source or safety-contract change,
dependency identity/implementation/trust change, Rust or support-domain change,
or newly supplied generated artifact or evidence. Every in-scope surface and
unsafe site has a disposition; C-F has the required existential certificate,
while C-D remains fail-closed at its single explicit missing premise.
