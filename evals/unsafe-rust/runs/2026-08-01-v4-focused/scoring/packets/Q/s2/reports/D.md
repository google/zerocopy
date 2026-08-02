# Focused unsafe-Rust source review

## Claim, snapshot, and domain

Audited snapshot: the submitted `lib.rs`, `Cargo.toml`, dependency contract, evidence policy, and TCB decision. The package is edition 2021 and fixes `peer-unsafe-dep` to exactly 3.4.5. No generated/expanded artifact, dependency body, prior audit, lockfile, build script, feature, conditional source, or test/tool result was supplied or used. This is a Rust-abstract-semantics source claim, not a compiler-binary claim. Audit cutoff: 2026-08-01. TCB log ID: `TCB-SUBMITTED-1`.

Let

`C = {Rust compiler and std 1.80.0} × T_resolve × {ordinary debug, ordinary release}`,

where `T_resolve` is exactly every target on which this source and exact dependency resolve. This is `Required_cfg` by literal transcription of `REQUEST.md`: each member of either set satisfies precisely those three conjuncts, proving both containments and hence equality. Edition 2021, dependency identity 3.4.5, and the submitted source are fixed rather than varying axes. There is no `cfg` or profile-sensitive branch; both proofs below are parametric in target and profile, so no enumeration of `T_resolve` is needed.

For a full case, retain configuration, input, call validity, and permitted execution:

- `R_force(c,e) := c∈C ∧ e is a permitted execution of a well-typed safe call to force_unreachable()`; there is no caller safety precondition.
- `R_delegate(c,v,e) := c∈C ∧ v∈{1,…,255} ∧ e is a permitted execution of delegated_nonzero(v)`; `v != 0` is its sole documented initial safety obligation, with no ongoing or terminal obligation.

## Verdicts

| Claim | Strongest verdict | Certificate or smallest gap |
|---|---|---|
| `force_unreachable` soundness over `R_force` | **UNSOUND**, for every `c∈C` | For each `c`, the safe expression `force_unreachable()` is a valid witness. `lib.rs:4-6` enters the function and unconditionally executes `std::hint::unreachable_unchecked()`. `AXIOM-UU-180` says reaching that function is UB. Thus valid safe use → reachability → false required proposition (“the call site is unreachable”) → UB. |
| `delegated_nonzero` soundness over `R_delegate` | **UNPROVED** | `lib.rs:14-17` passes unchanged `v` to the dependency. From `R_delegate`, `v != 0`, exactly discharging the submitted callee precondition. The remaining smallest missing proposition is: for every `c∈C`, every nonzero `v:u8`, and every permitted execution, `peer-unsafe-dep` 3.4.5's `duplicate_nonzero(v)` is UB-free. Its implementation is unavailable and that proposition has no accepted TCB entry. Absence of this universal proof supplies no UB witness, so `UNSOUND` is not justified. |

The first verdict is profile- and target-independent: the same unconditional call is selected, and the authority applies throughout `C`. The source comment “This site is assumed to be unreachable” proves nothing and is contradicted by every invocation: entry into this zero-argument function dominates the call.

For the second API, the adjacent safety comment adequately proves only the caller-side precondition of the unsafe dependency call. It cannot prove provider correctness. The API's literal description of delegation is established syntactically: line 17 calls the selected function with the unchanged argument and directly yields its normal result. It does not state `result == value`. The dependency documentation separately promises “Returns `value`”; that dependency postcondition is likewise unproved without its implementation or an accepted `UNSAFE-DEP` proposition, is not promoted into the wrapper contract, and is not needed for the wrapper soundness argument.

## Boundary and obligation inventory

The complete exported surface in the supplied source is two public free functions: safe `force_unreachable` and unsafe `delegated_nonzero`. No public fields, types, constructors, methods, trait surfaces/implementations, callbacks, macros/generated APIs, hidden items, FFI, state, or destruction path is present. There is no invariant-bearing representation.

| ID | Site | Exact obligation | Domain | Status |
|---|---|---|---|---|
| O1 | `lib.rs:6` | The `unreachable_unchecked` site is not reached. | Every `R_force` case | **False**; every call reaches it. |
| O2 | `lib.rs:17` | Argument to `duplicate_nonzero` is nonzero. | Every `R_delegate` case | **PROVED**: `v∈{1,…,255}` and unchanged dataflow imply `v != 0`. |
| O3 | dependency call at line 17 | Exact dependency implementation is UB-free for valid calls. | Every `R_delegate` case | **UNPROVED**; `F-DEP`. |
| O4 | wrapper description | Invoke selected peer with `v` and yield its normal result. | Every normally returning `R_delegate` case | **PROVED** directly by line 17; no provider return-value equality inferred. |

For `force_unreachable`, the existential certificate settles soundness while all independent sites above remain inventoried. For `delegated_nonzero`, aggregate `Covered = Covered(O2) ∩ Covered(O3)`; O2 covers all `R_delegate`, but O3 has no established cases, so `Required ⊆ Covered` is not proved.

## TCB and evidence audit

| ID | Category/disposition | Exact proposition, scope, source, consumer |
|---|---|---|
| `AXIOM-UU-180` | AXIOM / accepted by submitted human decision; citation independently verified | Rust 1.80.0 std states: “Reaching this function is Undefined Behavior.” It applies on every required target/profile. Source: [`unreachable_unchecked` Safety](https://doc.rust-lang.org/1.80.0/std/hint/fn.unreachable_unchecked.html#safety). Consumer: O1. Re-audit on Rust version, supported domain, source, or material documentation change. |
| `UNSAFE-DEP-345` | UNSAFE-DEP / expressly rejected, not consumable | Proposed proposition would be the O3 universal provider-correctness statement for exact package 3.4.5. The exact pin establishes identity only. No body, recursive audit, generated output, binary, or out-of-band promise supports it. Consumer blocked: O3. |

No safe-dependency, tool, implementation, compatibility, deployment, or probabilistic premise is admitted. The packet-supplied dependency declaration establishes the caller contract under review, not implementation correctness. No tool-derived evidence exists.

## Findings and resolutions

`F-FORCE` (critical, **UNSOUND**): a public safe API unconditionally executes an operation whose checked contract says reaching it is UB. The local proof artifact is false, not merely incomplete. Minimal resolution: remove the unsafe call and use defined behavior such as a panic, or redesign control flow so a real dominating invariant proves the site unreachable. No truthful `SAFETY` rewrite can validate the current body.

`F-DEP` (**UNPROVED**): provider correctness of third-party unsafe code is hidden trust that the reviewer declined. Resolve by supplying and recursively auditing the exact 3.4.5 implementation for all `C`, or by explicit human acceptance of a precise `UNSAFE-DEP` entry covering O3 (and the dependency's return-equality promise if that promise is to be relied upon). Re-audit both the call contract and provider proof on dependency identity, feature/configuration, or contract change.

Residual scope is exactly the unavailable dependency implementation and its generated/build inputs. Changes to either API/source documentation, Rust/std version, supported targets/profiles, dependency resolution or API, TCB disposition, or newly supplied generated/tool evidence trigger re-audit.
