# Focused source-only unsafe Rust review

## Claim frame and results

The audited source is `lib.rs` SHA-256
`778d644359b84bc0e519ed7220bfcadfbba578e2c9fd4c474ce742c4b0021ceb`,
together with the submitted manifest, dependency declaration, evidence policy,
request, and TCB decision. The manifest selects edition 2021 and exactly
`peer-unsafe-dep =3.4.5`. No dependency implementation, generated output,
prior audit, or binary was supplied.

Let **C** be: Rust compiler and standard library exactly 1.80.0; every target
on which this source and that exact dependency resolve; and every ordinary
debug or release profile. These are source-level Rust-abstract-semantics
claims, not compiler-backend or binary claims.

| Exported API | Exact valid uses | Soundness claim and strongest verdict |
|---|---|---|
| `pub fn force_unreachable()` | Every well-typed safe invocation; there is no caller safety precondition. | Every execution of every valid use in C is UB-free: **UNSOUND**, relative to TCB-R1. |
| `pub unsafe fn delegated_nonzero(value: u8) -> u8` | Every invocation whose caller ensures `value != 0`; the contract states no ongoing or terminal obligation. | Every execution of every valid use in C is UB-free: **UNPROVED**, relative to TCB-R1. |

Thus there is no combined `PROVED` result. The conjunction that both exports
are sound is refuted by the first API, while the second API retains its own
`UNPROVED` status.

## API and boundary coverage

The complete exported surface in `lib.rs` is the two public free functions
above. There are no exported fields, constructors, types, traits, methods,
statics, macros, reexports, hidden items, FFI declarations, or generated APIs.
The relevant unsafe consumers are the call to
`std::hint::unreachable_unchecked` and the call across the unsafe dependency
boundary. `#![allow(dead_code)]` only changes linting.

## Proof S1 — `force_unreachable`

1. A direct safe call `force_unreachable()` is a well-typed valid use.
2. On entry, the body has no branch, check, or earlier diverging operation. It
   immediately evaluates `std::hint::unreachable_unchecked()`; therefore that
   site is reached.
3. Verified Rust 1.80.0 standard-library authority states: “Reaching this
   function is Undefined Behavior.”
   ([Safety section](https://doc.rust-lang.org/1.80.0/std/hint/fn.unreachable_unchecked.html#safety)).
4. Consequently the valid safe invocation is a complete in-scope UB witness.

The derivation is parametric over C: neither the source control flow nor the
verified proposition has a target or ordinary-profile qualification. The
existing comment, “This site is assumed to be unreachable,” is circular and
false whenever the exported function is invoked; it proves no precondition.
No comment-only repair can make this safe implementation sound. A resolution
must remove the unchecked operation (for example, use a defined panic) or
enforce an appropriate boundary; a safe API cannot impose a hidden
unreachability obligation on callers.

## Proof S2 — `delegated_nonzero`

For an arbitrary valid call, let the input be `v: u8` with `v != 0`. The
wrapper performs no mutation or conversion and passes that same `v` to
`peer_unsafe_dep::duplicate_nonzero`. The submitted dependency contract's
caller-side requirement is exactly `value != 0`. Thus the wrapper's documented
precondition and unchanged dataflow completely discharge the local unsafe-call
precondition, throughout C. The adjacent safety comment adequately identifies
this local derivation.

That does not prove the unsafe callee's provider obligation. The smallest
missing soundness proposition is:

> For exact `peer-unsafe-dep` 3.4.5, on every configuration in C, for every
> `v: u8` with `v != 0`, every permitted execution of
> `duplicate_nonzero(v)` is free from Rust undefined behavior.

Neither declaration nor documentation proves that implementation theorem. The
implementation is unavailable, and the human trust decision explicitly
declines an `UNSAFE-DEP` admission. Exact pinning fixes identity but not
correctness. Therefore the wrapper claim is `UNPROVED`; no valid UB witness was
supplied, so `UNSOUND` is not justified.

The wrapper itself does not explicitly promise result equality. The submitted
dependency contract separately says it returns `value`; that provider
postcondition is not consumed by S2, but its implementation status is also
`UNPROVED`. Its smallest missing proposition is that every UB-free normal
return for the same domain yields exactly `v`.

## Configuration closure and TCB-R1

There are no declared Cargo features or source `cfg` branches. Target and
profile are the only stated axes. S1 is covered parametrically across them; the
local part of S2 is likewise parametric, but the missing dependency proposition
blocks all of C. No build, execution, test, expansion, or tool-derived evidence
was used.

TCB-R1 contains one accepted entry:

- **AXIOM-UU-1:** for Rust/std 1.80.0 throughout C, reaching
  `unreachable_unchecked` is UB. Identity and wording were independently
  verified at the exact versioned page above. Consumers: S1. Re-audit on a
  Rust version/domain or cited-contract change.

There are no accepted implementation, compatibility, tool, or deployment
entries. The proposed dependency-implementation proposition is deliberately
unavailable/rejected and supports no proof. Re-audit S2 if dependency source is
audited or the exact proposition is explicitly accepted; re-audit either claim
on source, safety-contract, dependency identity, supported-domain, TCB, or Rust
authority changes.
