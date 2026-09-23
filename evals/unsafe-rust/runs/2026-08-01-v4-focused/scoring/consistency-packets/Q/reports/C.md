# Focused unsafe-Rust source review

## Snapshot, scope, and domain

Audited at 2026-08-01: the exact supplied `lib.rs` and `Cargo.toml` for
`quantifier-target` 0.1.0, plus the submitted contracts and trust decision in
`DEPENDENCY-API.md`, `EVIDENCE.md`, and `TCB.md`. The manifest selects edition
2021 and exactly `peer-unsafe-dep =3.4.5`. This is only a source-level Rust
abstract-semantics review; no binary, backend, dependency implementation, or
generated artifact was available or claimed.

Let `T = { t | this exact source and peer-unsafe-dep 3.4.5 resolve for target
t under Rust 1.80.0 }`, and `P = {ordinary debug, ordinary release}`. The exact
compilation domain is

`D = {exact supplied source, edition 2021, Rust/stdlib 1.80.0, dependency
resolution peer-unsafe-dep =3.4.5, t in T, p in P}`.

This is the controlling expression from `REQUEST.md`, conjoined only with
identities stated by the manifest; hence the normalization is equality, not an
inferred exclusion. `T` is deliberately retained symbolically. `lib.rs` has no
`cfg`, feature, target, profile, assertion, macro, generated-code, allocator,
FFI, concurrency, or build-script branch. Consequently the source reasoning
below is parametric in `t` and `p`; no target inventory is needed.

The complete exported surface is the safe free function
`force_unreachable()` and unsafe free function `delegated_nonzero(u8) -> u8`.
There are no exported fields, types, traits, methods, statics, macros,
reexports, or hidden items, and no invariant-bearing state.

## Claims and verdicts

| Claim | Exact valid-use theorem over `D` | Verdict |
|---|---|---|
| F | Every well-typed safe call of `force_unreachable()` (no caller safety precondition) is free of Rust UB. | **UNSOUND** |
| D | For every `value: u8` with `value != 0` (the sole initial safety obligation; no ongoing or terminal obligation), every call of `delegated_nonzero(value)` is free of Rust UB. | **UNPROVED** |

For D, the dependency's documented normal-return postcondition, “Returns
`value`,” is also **UNPROVED**, not `CONTRACT-BROKEN`.

## TCB and evidence disposition

`AXIOM-UU-180` is accepted exactly as authorized in `TCB.md`. The opened Rust
1.80.0 standard-library Safety section says: “Reaching this function is
Undefined Behavior.” It states no narrower target/profile qualification:
[`std::hint::unreachable_unchecked`](https://doc.rust-lang.org/1.80.0/std/hint/fn.unreachable_unchecked.html#safety).
It is consumed only by Claim F and applies throughout `D`.

The submitted dependency declaration and caller contract identify the callee
and its precondition; they do not establish its implementation's correctness.
No `UNSAFE-DEP` proposition for `peer-unsafe-dep` 3.4.5 is accepted. The human
trust decision expressly rejects relying on its unavailable implementation.
There are no other admitted implementation, compatibility, tool, deployment,
or probabilistic premises. No tests or tool-derived evidence were supplied or
used.

## Proof and obligation ledger

### Claim F — complete UB certificate

1. **Valid in-scope use.** In every case in `D`, downstream safe code may call
   the public safe function `force_unreachable()`; its type and documentation
   impose no safety precondition.
2. **Reachability.** On entry, lines 4–6 have no check, branch, earlier
   divergence, or caller-controlled condition. The body immediately evaluates
   `std::hint::unreachable_unchecked()`; thus that operation is reached by the
   valid call.
3. **False required proposition.** `AXIOM-UU-180` requires that the function not
   be reached. Step 2 proves the opposite.
4. **UB consequence.** `AXIOM-UU-180` directly entails UB on reaching it.

These local facts are source-identical for every `t in T` and `p in P`, and the
axiom covers that whole domain. Thus each compilation case in `D` has the same
valid safe-call witness. This is an existential refutation, so the verdict is
`UNSOUND`, not merely a failed universal proof. The line-5 comment—“This site
is assumed to be unreachable”—is circular and false for the exported safe
entrypoint; it proves no obligation. There is no defined normal-return
execution from which to certify a separate return postcondition.

### Claim D — local call proof closes; provider proof does not

The controlling wrapper contract requires `value != 0`. The submitted exact
callee contract requires the identical proposition. For every valid wrapper
call, that fact follows directly from the wrapper's unsafe precondition, and
line 17 passes the same `u8` unchanged. Therefore the dependency call's entire
documented caller-side precondition is proved throughout `D`. Lines 15–16
correctly summarize this local implication.

The remaining soundness obligation is not a caller precondition: the selected
dependency implementation must honor its unsafe API contract. The smallest
missing proposition is:

> For the exact resolved implementation of `peer-unsafe-dep` 3.4.5, every
> execution of `duplicate_nonzero(v)` with `v: u8` and `v != 0` is free of Rust
> UB, for every target/profile case in `D`.

Neither inspected source nor an accepted `UNSAFE-DEP` entry proves it. An exact
version pin freezes identity but does not establish this semantic proposition.
Because no dependency body or trusted implementation fact exists, there is
also no proved valid execution reaching a false safety proposition and hence
no `UNSOUND` certificate. Aggregate coverage is therefore incomplete:
`Required_D` is covered for caller-precondition discharge but not for provider
correctness, so `Required_D` is not contained in complete `Covered_D`.

The separate smallest missing postcondition proposition is that every normal,
UB-free valid call to that exact implementation returns `v`. Without it there
is no wrapper result proof; without an independently established UB-free
falsifying execution there is no `CONTRACT-BROKEN` certificate.

## Findings, resolution, and residual scope

- **F-1, implementation defect:** `force_unreachable` exposes unconditional UB
  through safe code. A comment cannot repair it. Replace the unchecked
  operation with defined behavior such as `unreachable!()`/panic, remove the
  entrypoint, or otherwise enforce a sound boundary; then audit the new
  artifact. Changing safe behavior or safety classification requires API
  compatibility review.
- **D-1, missing dependency proof/TCB:** recursively audit the exact 3.4.5
  implementation over `D`, or obtain authorized acceptance of a precise
  `UNSAFE-DEP` entry covering both UB freedom and, if promised, return-value
  correctness. Re-audit after any dependency identity, contract, feature,
  target/profile support, or trust-decision change.

Unavailable and therefore excluded from any affirmative claim are the
dependency implementation/generated output, compiler/backend correctness,
binaries, and deployment behavior. Re-audit is also required for changes to
`lib.rs`, the manifest/domain, Rust version or cited authority, exported
surface, or supplied evidence. Every in-scope obligation has the status above;
the combined two-API soundness result is **F: UNSOUND; D: UNPROVED**.
