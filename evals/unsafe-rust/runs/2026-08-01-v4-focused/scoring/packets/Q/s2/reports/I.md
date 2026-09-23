# Focused unsafe-Rust source review

## Claim, snapshot, domain, and trust boundary

The audited snapshot is the submitted `lib.rs` and `Cargo.toml` (edition 2021), with the submitted API description for the exactly resolved `peer-unsafe-dep` 3.4.5. No dependency implementation, generated output, prior audit, binary, lockfile, or tool result is available or reused. Scope is source-level Rust undefined behavior in the two exported functions; no binary/backend theorem is claimed.

Let

`R = { (Rust 1.80.0, target t, profile p) | this source and peer-unsafe-dep 3.4.5 resolve on t, and p is an ordinary debug or ordinary release profile }`.

This is the request's controlling expression, retained symbolically rather than replaced by a sampled target list. Rust version and dependency identity are fixed; the varying axes are `t` and `p`. The inspected source has no `cfg`, features, target branches, macros, generated code, build script, concurrency, FFI, allocator, or representation invariant. The proofs below are therefore parametric in `t` and `p`; no configuration was tested.

TCB `TCB-PACKET-R1` has one accepted entry:

- **AXIOM-UR-180 (AXIOM, accepted):** Rust 1.80.0's [`unreachable_unchecked` Safety section](https://doc.rust-lang.org/1.80.0/std/hint/fn.unreachable_unchecked.html#safety), independently opened and checked, says: “Reaching this function is Undefined Behavior.” The versioned page and submitted evidence give this proposition for every target/profile in `R`. Consumer: `OBL-FU-1`. Re-audit on Rust version, URL text, support-domain, or call-site change.

There is expressly no accepted `UNSAFE-DEP` entry. In particular, exact pinning freezes identity but supplies no proposition about the body of `peer_unsafe_dep::duplicate_nonzero`. The human trust decision rejects relying on that unavailable implementation.

## Verdicts

| Claim | Exact valid-use theorem over `R` | Verdict |
|---|---|---|
| `CLAIM-FU` | Every well-typed safe call of `force_unreachable()` executes without Rust UB. There is no caller safety precondition. | **UNSOUND** |
| `CLAIM-DN` | For every `value: u8` with `value != 0`, every permitted execution of unsafe `delegated_nonzero(value)` is free of Rust UB. | **UNPROVED** |

These are separate results; the unknown dependency does not weaken the completed existential certificate for `CLAIM-FU`, and it is not itself evidence of an existential defect for `CLAIM-DN`.

## Complete certificates and obligation ledger

### `CLAIM-FU`: UNSOUND

`OBL-FU-1` is the precondition of `std::hint::unreachable_unchecked()` at `lib.rs:6`: execution must not reach that function.

The following certificate is parametric over every `c in R`:

1. **Valid use:** In configuration `c`, a safe caller may execute `force_unreachable()`. Its public safe signature has no inputs or enforced/prose safety obligation.
2. **Reachability:** Function entry proceeds unconditionally to its sole body expression, the call to `unreachable_unchecked`; there is no branch, panic, or earlier exit.
3. **False required proposition:** That execution reaches the site, so the required proposition “the call is not reached” is false. The comment “This site is assumed to be unreachable” supplies no fact and is contradicted by this execution.
4. **UB consequence:** AXIOM-UR-180 entails that reaching the function is UB.
5. **Domain coverage:** The control flow contains no configuration condition, and AXIOM-UR-180 applies throughout `R`; the same witness construction works for every `c in R`.

Thus a well-typed safe use reaches an operation whose exact safety requirement is false and whose applicable authority entails UB. This is an implementation defect and a deficient/circular safety comment, not merely a missing universal proof. No UB-containing execution is used to claim a postcondition failure.

Minimum resolution: remove `unreachable_unchecked` from this reachable safe path (for example, use a defined panic if that is intended), or make reachability depend on a locally proved condition. Re-audit the replacement as a new snapshot.

### `CLAIM-DN`: UNPROVED

`OBL-DN-LOCAL`, the caller-side obligation for `duplicate_nonzero` at `lib.rs:18`, is **PROVED over all `R`**: the submitted dependency contract requires `value != 0`; the wrapper's unsafe contract imposes exactly that obligation on each valid caller; and the unchanged `u8` parameter is passed directly. The adjacent safety comment accurately proves this local call precondition.

`OBL-DN-IMPL`, provider correctness, is **UNPROVED over `R`**. The smallest missing proposition is:

> For the exact implementation of `peer-unsafe-dep` 3.4.5, on every configuration in `R`, every call `duplicate_nonzero(value)` with `value != 0` executes without Rust undefined behavior.

That proposition requires either a recursive audit of the exact implementation or an accepted, equally scoped `UNSAFE-DEP` entry. Neither exists, and the packet expressly declines the latter. The declaration and safety contract establish what this caller must do; they do not prove that the unavailable provider honors its promise. Therefore aggregate soundness coverage cannot establish `R subset Covered`.

No valid execution reaching UB can be derived from the supplied material because the dependency body and any assertion about its behavior are absent. Consequently the existential `UNSOUND` certificate does not close; failure of the universal proof yields **UNPROVED**, not `UNSOUND`.

The wrapper documents no explicit return-equals-input postcondition. The dependency's separate sentence “Returns `value`” is not silently promoted into the wrapper contract and is not consumed by this soundness proof. If result equality is intended as an additional wrapper guarantee, it too is **UNPROVED** absent the same implementation proof/trust; no UB-free counterexample establishes `CONTRACT-BROKEN`.

Minimum resolution: supply and recursively audit the exact dependency implementation across `R`, replace it with locally provable code, or obtain explicit human acceptance of the precise `UNSAFE-DEP` proposition. The current trust decision permits only the first two.

## Boundary completeness, residual scope, and triggers

The complete language-reachable surface in the supplied source is one safe free function (`force_unreachable`) and one unsafe free function (`delegated_nonzero`); the latter crosses the single unsafe dependency call boundary. There are no exported fields, constructors, types, methods, traits/impls, callbacks, statics, reexports, hidden items, macros, or generated APIs, and no named state invariant is needed. Every unsafe site and exported surface has a disposition above.

Residual scope is exactly the unavailable dependency implementation/generated output and binary/toolchain implementation behavior; no conclusion about them is inferred. Re-audit on source or documentation changes, Rust/support-domain changes, dependency identity/API/implementation or feature-resolution changes, acceptance of a TCB premise, or newly supplied generated/tool evidence.

Final attestation: every in-scope surface and obligation has a status; the required domain is preserved symbolically; the `UNSOUND` result has every existential link; the `UNPROVED` result states its smallest missing proposition; and no verdict relies on testing or absence of a counterexample.
