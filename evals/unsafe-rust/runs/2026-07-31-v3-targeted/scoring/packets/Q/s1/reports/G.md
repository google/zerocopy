# Focused unsafe-Rust source review

## Scope, snapshot, and domain

This review covers exactly the two exported free functions in the supplied
`lib.rs`, with the supplied `Cargo.toml`, `DEPENDENCY-API.md`, `EVIDENCE.md`, and
`TCB.md`. No repository revision or dependency implementation was supplied. No
generated target code, tests, tool results, or prior audit are consumed.

For both claims, define:

`Required(C) := C uses Rust and std 1.80.0, edition 2021; resolves
peer-unsafe-dep exactly 3.4.5; targets any target on which this source and that
exact dependency resolve; and uses an ordinary debug or ordinary release
profile.`

This is an exact transcription of `REQUEST.md`; `Cargo.toml` independently
confirms the exact dependency constraint `=3.4.5`. The target set is kept as
the request's symbolic predicate rather than replaced by an unevidenced finite
inventory. There are no target-source `cfg`s, Cargo features, macros,
generators, build scripts, profile branches, or target branches in the supplied
artifact. Thus the inspected call paths are identical for every `C` satisfying
`Required`. There are no exclusions or policy conflicts. The audit cutoff is
the supplied source/evidence packet; no dynamic support policy is present.

The complete exported surface is:

| API | Boundary | Valid-use domain |
|---|---|---|
| `force_unreachable()` | safe free function | every well-typed safe invocation; no caller safety precondition |
| `delegated_nonzero(value: u8) -> u8` | unsafe free function | every invocation with `value != 0`, i.e. `value` in `1..=255`; no ongoing or terminal obligation is documented |

There are no representation fields, constructors, traits, impls, callbacks,
hidden items, reexports, or abstraction invariants in the supplied source.

## TCB and authority

**AXIOM-UU-1 (accepted):** Rust 1.80.0's versioned standard-library Safety
section states: “Reaching this function is *Undefined Behavior*.” The fetched
page identifies rustdoc 1.80.0, and the proposition has no narrower target or
profile qualification. [Official Rust 1.80.0 documentation](https://doc.rust-lang.org/1.80.0/std/hint/fn.unreachable_unchecked.html#safety).
It is consumed only by the `force_unreachable` certificate.

**UNSAFE-DEP-1 (not admitted):** No proposition about the implementation of
`peer-unsafe-dep` 3.4.5 is accepted. `TCB.md` expressly declines that trust.
The exact pin fixes identity but proves neither implementation soundness nor
postcondition correctness. There are no other TCB premises.

## Claim F — `force_unreachable`

**Exact theorem.** For every `C` satisfying `Required`, every well-typed safe
invocation of `force_unreachable()` is free of Rust undefined behavior.

**Verdict: UNSOUND for every `C` satisfying `Required`.** Fix any such `C` and
use the safe call `force_unreachable()` as the witness:

1. **Valid in-scope use:** the function is public and safe, takes no arguments,
   and documents no caller safety condition.
2. **Reachability:** its body has no check, branch, earlier divergence, or
   intervening call; control unconditionally executes
   `std::hint::unreachable_unchecked()`.
3. **False required proposition:** that operation requires its call site not to
   be reached, but step 2 proves that it is reached.
4. **UB consequence:** AXIOM-UU-1 directly classifies reaching the function as
   undefined behavior.

This is a parametric certificate over the entire target/profile predicate, not
a sampled configuration result. The existing safety comment merely assumes
the proposition contradicted by local control flow; it is not a proof.

**Finding F-1 (implementation defect; deficient proof artifact).** No revised
`SAFETY` wording can justify the current body. A minimal sound repair is to use
the safe `unreachable!()` panic or to redesign the surrounding control flow so
an independently proved invariant makes the site unreachable. Any changed
artifact requires a fresh audit. No broader safe-API behavioral postcondition
was requested; the soundness failure is complete without one.

## Claim D — `delegated_nonzero`

**Exact theorem.** For every `C` satisfying `Required` and every `value` in
`1..=255`, every permitted execution of `delegated_nonzero(value)` is free of
Rust undefined behavior.

**Verdict: UNPROVED.** The local caller-side obligation is proved: the wrapper's
unsafe contract requires `value != 0`; the submitted dependency contract places
the identical precondition on `duplicate_nonzero`; and the source passes the
same `value` without modification. This derivation is parametric over all
`Required` configurations, so the adjacent safety comment adequately explains
that limited obligation.

The separate provider-side obligation is not proved. The smallest missing
soundness proposition is:

`DEP-SOUND := for every C satisfying Required and every v in 1..=255, every
permitted execution of peer_unsafe_dep::duplicate_nonzero(v) in exact package
3.4.5 is free of Rust undefined behavior.`

The dependency implementation and generated output are absent, and
UNSAFE-DEP-1 is not admitted. The published caller contract does not establish
`DEP-SOUND`. Therefore no configuration has a complete affirmative derivation,
and `Required ⊆ Covered` cannot be certified. Conversely, the packet supplies
no execution, implementation fact, or other premise proving an existential UB
witness, so `UNSOUND` is not justified.

**Documented behavior.** The source itself proves that the same nonzero value is
passed to the peer function and that the peer's return value is returned. The
submitted peer documentation additionally says it returns `value`. If that
provider guarantee is included as the wrapper's return-value postcondition,
its verdict is **UNPROVED**: the smallest missing proposition is that, for every
`C` and nonzero `v` above, every defined normal return from exact dependency
3.4.5 equals `v`. No UB-free falsifying execution is supplied, so
`CONTRACT-BROKEN` is not justified.

**Finding D-1 (missing dependency proof/TCB premise).** Resolve by recursively
auditing the exact dependency implementation and relevant generated output, or
by an authorized human accepting precise `UNSAFE-DEP` propositions covering
`DEP-SOUND` and any consumed return guarantee over all `Required`
configurations. Strengthening the wrapper's caller contract would not repair
this provider-side gap.

## Coverage, residual scope, and triggers

For Claim F, the existential UB certificate closes for an arbitrary member of
`Required`. For Claim D, the local precondition proof covers all `Required`, but
the necessary provider theorem covers none on the supplied evidence; proof
regions for distinct obligations cannot be unioned. No testing or tool-derived
evidence contributes.

Residual scope is precisely the unavailable dependency implementation,
generated output, and any facts about its executions. Re-audit is required if
either API or its documentation changes; Rust/std, edition, target, profile, or
support policy changes; dependency identity, features, contract, source, or
trust disposition changes; or dependency implementation/generated evidence is
added.
