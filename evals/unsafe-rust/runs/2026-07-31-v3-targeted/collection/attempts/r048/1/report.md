# Focused unsafe-Rust source audit

## Snapshot, scope, and domain

Audited artifact: the submitted `lib.rs` for `quantifier-target` 0.1.0
(edition 2021), its submitted manifest, dependency contract, evidence packet,
and trust decision. The manifest selects exactly `peer-unsafe-dep` 3.4.5. No
dependency implementation, generated output, lockfile, prior audit, binary, or
tool result was supplied or inspected. Review cutoff: 2026-08-01. This is a
source-level Rust-abstract-semantics review only.

Let

`C = {Rust 1.80.0} × Tresolve × {ordinary debug, ordinary release}`,

where `Tresolve` is exactly the set of targets on which this submitted source
and the submitted exact dependency resolution resolve. This preserves the
request's symbolic target predicate; it is not replaced by an unevidenced
inventory. There are no `cfg`, feature, target, profile, macro, build-script, or
generated-source branches in `lib.rs`. The arguments below are parametric in
every `c ∈ C`: neither source reachability nor the value passed to the peer call
depends on target or profile. Thus those arguments cover all of `C` without
sampling.

The complete exported surface is the two free functions below. There are no
exported fields, types, traits, methods, statics, macros, hidden items, FFI
entrypoints, callbacks, or generated APIs in the submitted source.

## Claims and verdicts

| Claim | Exact valid uses and theorem | Verdict |
|---|---|---|
| `force_unreachable` (`lib.rs:4-7`) | For every `c ∈ C` and every well-typed safe call to this safe, argument-free function (there is no caller safety precondition), the execution is free of Rust UB. | **UNSOUND**, throughout `C`. |
| `delegated_nonzero` (`lib.rs:14-18`) | For every `c ∈ C` and every unsafe call with `value: u8` satisfying the complete documented safety precondition `value != 0`, the execution is free of Rust UB. There are no stated ongoing or terminal caller obligations. | **UNPROVED**, throughout `C`. |

No broader safe-API robustness property was requested. If the peer contract's
“Returns `value`” is treated as a mandatory consumed provider postcondition,
that postcondition is also **UNPROVED**; no UB-free counterexample establishes
`CONTRACT-BROKEN`.

## Proof certificates and obligation ledger

### `force_unreachable`: complete existential UB certificate

1. **Valid in-scope use.** For arbitrary `c ∈ C`, a safe program may call
   `force_unreachable()`; the item is `pub fn`, takes no argument, and exposes
   no unsafe obligation. Such a call is therefore a valid well-typed safe use.
2. **Reachability.** Entry executes the body, whose only statement is the
   unconditional call to `std::hint::unreachable_unchecked()` at `lib.rs:6`.
   There is no branch, return, panic, callback, or dependency operation before
   it. The unsafe operation is reached.
3. **False required proposition.** The call requires that its site not be
   reached. Step 2 proves the opposite. The comment “This site is assumed to be
   unreachable” supplies no fact and is false for every invocation.
4. **UB consequence.** The verified Rust 1.80.0 standard-library Safety text
   states: “Reaching this function is Undefined Behavior.” Therefore the valid
   call reaches UB. The reasoning is source-, target-, and profile-parametric,
   so every member of `C` has this witness.

This satisfies every link required for `UNSOUND`; it is not merely a failed
universal proof. The minimal correction is to remove the unchecked-unreachable
operation (for example, use a defined panic) or move a sufficient, enforced
unreachability obligation to an unsafe API. Rewording the current safety
comment cannot repair the safe implementation.

### `delegated_nonzero`: exact closed and open obligations

- **D1—peer caller precondition: PROVED locally over `C`.** A valid wrapper call
  has `value != 0` by `lib.rs:11-13`. The exact submitted peer contract requires
  precisely `value != 0`. `lib.rs:17` passes the same `u8` without mutation or
  intervening code. Hence the wrapper satisfies the peer call's documented
  caller-side safety precondition. The adjacent comment adequately records
  this local implication.
- **D2—peer provider soundness: UNPROVED over all `C`.** Calling a third-party
  unsafe API also requires establishing that its exact implementation fulfills
  its promise for valid calls. The smallest missing proposition is:
  `for every c ∈ C and every v: u8 with v != 0, peer-unsafe-dep 3.4.5's exact
  duplicate_nonzero(v) implementation executes without Rust UB`.
  Neither declaration nor caller contract proves that implementation theorem.
  The body and prior audit are unavailable, and the submitted human decision
  expressly declines an `UNSAFE-DEP` assumption. Consequently aggregate
  `Covered` for this claim contains no configuration under the admitted
  premises, so `Required = C × {v | v != 0}` is not contained in `Covered`.
- **D3—return guarantee: UNPROVED if in scope.** The wrapper returns the peer
  result unchanged, so the peer implementation's promised `result == value`
  would entail the same result. The missing provider theorem must additionally
  establish that equality. No UB-free falsifying execution was supplied, so
  absence of proof is not `CONTRACT-BROKEN` or `UNSOUND`.

Accepting a precisely scoped `UNSAFE-DEP` entry for D2/D3, recursively auditing
the exact dependency implementation, or replacing the call with a proved
implementation is necessary to close this claim. The local safety comment
cannot establish provider correctness.

## TCB and evidence disposition

- **AXIOM-UU-1 — accepted.** Rust 1.80.0 `std::hint::unreachable_unchecked`
  Safety documentation, independently opened at the exact supplied URL:
  https://doc.rust-lang.org/1.80.0/std/hint/fn.unreachable_unchecked.html#safety.
  Exact consumed proposition: reaching the function is UB. Scope supplied and
  admitted by `EVIDENCE.md`/`TCB.md`: Rust 1.80.0, all targets and ordinary
  profiles. Consumer: the `force_unreachable` certificate.
- **UNSAFE-DEP-PEER-345 — rejected/not admitted.** Proposed proposition would
  be D2 (and D3 if return behavior is claimed) for exact package 3.4.5 over
  `C`. `TCB.md` expressly declines it; it supports no affirmative verdict.
- No implementation, compatibility, tool, environment, deployment, or
  probabilistic premise is admitted. No test or tool evidence contributes.

Re-audit is required if either function or its documentation changes, the Rust
version/domain changes, the peer version/contracts/features/implementation or
trust disposition changes, or generated/configuration-dependent code is added.
