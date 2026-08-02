# Focused unsafe-Rust audit

## Claims, domain, and verdicts

**Snapshot.** This review covers exactly the submitted `quantifier-target` 0.1.0 source (`lib.rs`, edition-2021 `Cargo.toml`) and the submitted contracts/evidence. The manifest pins `peer-unsafe-dep = "=3.4.5"`; no dependency implementation, generated output, digest, binary, or prior audit was supplied. No source was executed, built, expanded, or edited.

Define `T = {t | this exact source and peer-unsafe-dep 3.4.5 resolve on target t}`, `P = {ordinary debug, ordinary release}`, and

`C = {Rust/compiler/stdlib 1.80.0, edition 2021, target t ∈ T, profile p ∈ P, exact submitted source and dependency resolution}`.

This is the controlling compilation predicate stated by `REQUEST.md`, preserved symbolically rather than replaced by a sampled target inventory. There are no crate features, `cfg` branches, build scripts, or generated sources in the submitted crate. Both source paths are therefore parametric in `t` and `p`; optimization, debug assertions, and overflow checks do not alter either straight-line call. Dependency implementation behavior remains unavailable in every relevant fiber.

| Claim | Exact valid-use domain | Verdict |
|---|---|---|
| `force_unreachable` soundness | For every `c ∈ C`, every well-typed safe invocation in any permitted caller state; there is no caller safety precondition. | **UNSOUND**, in every nonempty configuration fiber of `C`. |
| `delegated_nonzero` soundness | For every `c ∈ C`, every `value: u8` with `value != 0`, and every permitted execution of the unsafe call. That is its sole documented initial obligation; no ongoing or terminal obligation is stated. | **UNPROVED**. |

The claims are separate: the first claim's refutation neither proves nor refutes the second.

## Boundary and contract inventory

The complete submitted crate surface consists of two exported free functions: safe `force_unreachable()` and unsafe `delegated_nonzero(u8) -> u8`. There are no exported fields, types, constructors, traits/impls, methods, macros, statics, callbacks, FFI declarations, hidden items, or crate-generated APIs. No representation invariant exists. The only external unsafe surface consumed is `peer_unsafe_dep::duplicate_nonzero(u8) -> u8`, documented to require a nonzero argument and return that argument.

The unsafe wrapper documents `value != 0` and says it delegates the value. On a normal return, the source establishes only: the dependency was called with the unchanged `value`, and the wrapper returns the dependency's result. Treating the dependency's documented “Returns `value`” as a mandatory provider postcondition does not prove that its unavailable unsafe implementation fulfills it.

## Obligation ledger and proofs

### OBL-FORCE — direct UB certificate

1. `force_unreachable` is public and safe, takes no argument, performs no check or branch, and its body immediately evaluates `std::hint::unreachable_unchecked()` (`lib.rs:4-6`). Thus `force_unreachable()` is a well-typed safe-use witness and invocation reaches that operation for each `c ∈ C`.
2. The checked Rust 1.80.0 standard-library Safety section states: “Reaching this function is Undefined Behavior.” ([versioned authority](https://doc.rust-lang.org/1.80.0/std/hint/fn.unreachable_unchecked.html#safety)). The page is Rust 1.80.0 documentation and states no target or profile qualification; the submitted TCB accepts this proposition over `C`.
3. Therefore the valid safe invocation reaches an executed operation whose exact required proposition—unreachability—is false, and the applicable authority entails UB. This completes the existential `UNSOUND` certificate parametrically for every actual `c ∈ C`.

The adjacent comment, “This site is assumed to be unreachable,” is not a proof: public safe invocation establishes reachability. It also cannot become a hidden safety precondition on a safe API. Minimal resolution is to prevent all safe calls from reaching the operation, replace it with defined behavior, or expose and document a sufficient compiler-enforced unsafe boundary; any changed artifact needs fresh audit.

### OBL-DELEGATE-CALL — dependency caller precondition

For a valid wrapper call, its documented contract gives `value != 0`. Line 17 passes that identical `value` to `duplicate_nonzero`; the submitted dependency contract requires exactly `value != 0`. Hence the local unsafe-call precondition is **PROVED** over all valid inputs and all `C`. The adjacent safety comment accurately records this derivation.

### OBL-DELEGATE-IMPL — dependency provider correctness

Soundness additionally requires: for peer-unsafe-dep 3.4.5, for every `c ∈ C` and every nonzero `v: u8`, every permitted execution of `duplicate_nonzero(v)` is UB-free. If its return contract is included, it must also return `v` on normal return. An unsafe caller contract establishes what callers must do; it does not establish that the third-party unsafe implementation fulfills its provider obligations. The exact pin freezes package/version identity only.

No implementation or recursive audit was supplied, and `TCB.md` expressly rejects trusting it. Consequently no full `delegated_nonzero` case is certified by this packet: the local obligation is covered, but claim-level coverage is the pointwise conjunction with this uncovered provider obligation. The smallest missing proposition is the quantified UB-freedom proposition above (plus return equality for the submitted provider postcondition), established by an audit of the exact implementation/generated artifact or an expressly accepted, equally scoped `UNSAFE-DEP` entry.

This is **UNPROVED**, not `UNSOUND`: the packet supplies no valid execution, dependency body, or asserted executed behavior from which to prove reachability of a violating event and UB. It is not `CONTRACT-BROKEN`: no UB-free execution falsifying return equality is established.

## TCB and evidence audit log

**TCB ID:** submitted `TCB.md`, this snapshot. **Policy:** only verified Rust authority and expressly accepted entries may be consumed; third-party unsafe implementations require recursive audit or accepted `UNSAFE-DEP` trust.

| ID | Category/disposition | Exact proposition, scope, consumer | Identity/channel; trigger |
|---|---|---|---|
| AXIOM-UU | Rust std authority; accepted after direct verification | Reaching `unreachable_unchecked()` is UB, Rust 1.80.0 over `C`; OBL-FORCE | Exact versioned URL above; re-audit on Rust/support or cited text change |
| UNSAFE-DEP-PEER | Proposed premise; expressly not accepted | `duplicate_nonzero(v)` is UB-free for every nonzero `v` over `C` and fulfills its return contract; OBL-DELEGATE-IMPL | peer-unsafe-dep 3.4.5 exact pin; resolve by exact audit or human-accepted entry |

There is no tool-derived evidence. The submitted documentation identifies the unsafe dependency contract but cannot substitute for implementation correctness. No implementation, compatibility, tool, deployment, or probabilistic premise is admitted.

## Closure, residual scope, and triggers

For OBL-FORCE the witness proof is independent of target/profile, so it covers each `C` fiber and refutes soundness there. For `delegated_nonzero`, `Required = C × {v ∈ u8 | v != 0} × permitted executions`; OBL-DELEGATE-CALL covers `Required`, while OBL-DELEGATE-IMPL has no certified region, so `Required ⊄ Covered` and `PROVED` is unavailable.

Unaudited residuals are precisely the dependency implementation/generated output and binary/backend correctness (the latter is outside this source-level claim). Re-audit on changes to either function or its documentation, Rust/support predicate, the cited authority, dependency identity/features/contract/implementation, generated output, or TCB disposition.

**Final result:** `force_unreachable` is **UNSOUND**; `delegated_nonzero` is **UNPROVED**. Every discovered surface, unsafe operation, documented unsafe precondition, dependency postcondition, configuration axis, and trust premise has the disposition above.
