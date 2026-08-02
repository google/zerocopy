# Focused source-only unsafe Rust review

## Claim frame and domain

Snapshot: the submitted `Cargo.toml`, `lib.rs`, `DEPENDENCY-API.md`,
`EVIDENCE.md`, and `TCB.md`. Scope is the two exported functions and their two
unsafe calls. There are no exported fields, types, traits, implementations,
macros, statics, callbacks, FFI surfaces, conditional items, or generated
artifacts in the packet. No prior audit, dependency implementation, expansion,
binary, or tool result is reused.

Let `T` be exactly the targets on which this source and the resolved
`peer-unsafe-dep` 3.4.5 compile, and let `P = {ordinary debug, ordinary
release}`. The controlling request and manifest give

`C = { (Rust 1.80.0, edition 2021, target t, profile p,
peer-unsafe-dep =3.4.5) | t in T, p in P }`.

This is retained symbolically: no finite target inventory is asserted.
`Required_cfg = C`. There are no source `cfg`s or features to partition. The
manifest's exact version requirement and the submitted resolution statement
establish the dependency version selected; they establish no proposition about
its body. The target predicate and profiles come verbatim from `REQUEST.md`, so
normalization to `C` holds in both directions by definition. The audit cutoff
is 2026-08-01; the supplied policy is static.

For `force_unreachable`, `Required_F` contains every `c in C` and every
well-typed safe invocation and permitted execution of the function. There is
no caller safety precondition. For `delegated_nonzero`, `Required_D` contains
every `c in C`, every `v: u8` with `v != 0`, and every permitted execution of
an unsafe invocation whose documented obligation is satisfied. No ongoing or
terminal caller obligation is documented.

## Authority and trust boundary (`TCB-PACKET-1`)

`AXIOM-UU-180` is accepted exactly as directed by `TCB.md`. The checked Rust
1.80.0 standard-library Safety section says: “Reaching this function is
Undefined Behavior.” It states no target or profile qualification, so the
packet applies it throughout `C`.
[Versioned source](https://doc.rust-lang.org/1.80.0/std/hint/fn.unreachable_unchecked.html#safety).

No `UNSAFE-DEP` proposition for `peer-unsafe-dep` 3.4.5 is accepted; the human
trust decision expressly declines it. No other implementation, compatibility,
tool, environment, or deployment proposition is admitted. The submitted peer
documentation is the caller/provider contract, not evidence that its
unavailable unsafe implementation fulfills that contract.

## Claim F — `force_unreachable`

**Soundness verdict: UNSOUND over all of `Required_F`, relative to
`TCB-PACKET-1`.**

Existential UB certificate (indeed parametric in every `c in C`):

1. **Valid use.** `force_unreachable` is a public safe function with no
   arguments or stated precondition, so a safe call `force_unreachable()` is a
   valid in-scope use.
2. **Reachability.** Once invoked, its body has no check or alternative exit;
   `lib.rs:6` evaluates `std::hint::unreachable_unchecked()`.
3. **False required safety proposition.** The call site is therefore reached.
   The operation requires that it not be reached.
4. **UB consequence.** `AXIOM-UU-180` directly classifies reaching the function
   as undefined behavior.

These facts do not vary with target or profile, and the axiom covers all of
`C`; thus each required configuration has the witness. The line 5 safety
comment merely assumes the proposition disproved by ordinary invocation. It
is not a proof and cannot be repaired with stronger prose: the implementation
must remove the call (for example, use defined panic/divergence) or remove the
safe callable behavior.

The descriptive sentence at line 3 supplies no separate defined-behavior
postcondition. Because the witness execution contains UB, it cannot establish
`CONTRACT-BROKEN`.

## Claim D — `delegated_nonzero`

**Soundness verdict: UNPROVED over `Required_D`, relative to
`TCB-PACKET-1`.**

The complete local call-site derivation is:

1. A valid wrapper use supplies `v != 0` by `lib.rs:13`.
2. Line 17 passes that same `u8` value, without a transition, to
   `duplicate_nonzero`.
3. The submitted peer safety contract requires exactly `value != 0`.
   Therefore the wrapper discharges the peer's caller-side precondition for
   every `v` in `1..=255` and every `c in C`. The local safety comment is
   correct for that obligation.
4. Soundness additionally requires the exact peer implementation to be free
   of UB for every such valid call. Neither the caller precondition nor the
   declaration proves provider correctness.

The smallest missing proposition is:

`DEP-SOUND`: for every `c in C` and `v: u8` with `v != 0`, every permitted
execution of `peer-unsafe-dep` 3.4.5's exact `duplicate_nonzero(v)`
implementation is free of Rust undefined behavior.

The dependency body/generated output is absent, no assertion about its
executions is supplied, and `TCB.md` rejects admission of this proposition.
Consequently the implementation obligation's covered domain is not shown to
contain `Required_D`; `Required_D subseteq Covered_D` cannot be certified.
There is also no valid execution showing that `DEP-SOUND` is false, so the
stronger `UNSOUND` certificate is unavailable.

The peer contract additionally promises to return `value`. That provider
postcondition is likewise unverified for the unavailable implementation. The
wrapper documents delegation but no explicit equality postcondition of its
own. No UB-free postcondition counterexample is supplied, so
`CONTRACT-BROKEN` is not established.

Minimum resolution: submit and recursively audit the exact dependency
implementation and any generated output over `C`, or obtain human acceptance
of a precise `UNSAFE-DEP` entry covering `DEP-SOUND` (and the return guarantee
if it is consumed). An exact version pin alone is insufficient.

## Obligation closure

| ID | Obligation | Status |
|---|---|---|
| F-CALL | `unreachable_unchecked` is not reached | False; complete UB certificate above |
| D-PRE | argument passed to peer is nonzero | Proved for all `Required_D` |
| D-IMPL | valid peer call is UB-free | Unproved: `DEP-SOUND` missing |
| D-RET | peer valid call returns its input | Unproved provider guarantee; not an explicit wrapper postcondition |

Combined result: `force_unreachable` is **UNSOUND**; `delegated_nonzero` is
**UNPROVED**. There is no tool-derived evidence and no binary/backend theorem.
Re-audit on any source or contract change, support-domain change, Rust or cited
documentation change, dependency identity/body/generated-output change, or
new TCB disposition.
