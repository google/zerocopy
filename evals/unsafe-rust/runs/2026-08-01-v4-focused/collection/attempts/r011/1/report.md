# Focused unsafe-Rust source audit

## Claims and verdicts

| Claim | Exact theorem | Verdict |
|---|---|---|
| C1 | For every configuration in `D`, every well-typed safe call to `force_unreachable()` is free of Rust undefined behavior. | **UNSOUND** |
| C2 | For every configuration in `D`, every call to `delegated_nonzero(value)` with `value != 0` is free of Rust undefined behavior. There are no ongoing or terminal caller obligations. | **UNPROVED** |

These are separate source-level verdicts relative to TCB revision `TCB.md` SHA-256 `86796b85804436595c0f6ffbfa773dac4fce5cbfe28e02223c802a055037d0f4`. The combined soundness result is **UNSOUND** because C1 has a complete UB witness; C2 independently remains **UNPROVED**.

## Snapshot, scope, and domain

The audited source is `lib.rs` SHA-256 `778d644359b84bc0e519ed7220bfcadfbba578e2c9fd4c474ce742c4b0021ceb`, with `Cargo.toml` SHA-256 `57b66359b9447d371fa68a2cfdc04f49176b1a3ce815bb96027b2f76d917d0a7`. The manifest uses edition 2021 and exactly pins `peer-unsafe-dep = 3.4.5`; the submitted dependency surface confirms that exact resolution. No lockfile or dependency implementation was supplied.

Let `R(t)` mean that this exact source and `peer-unsafe-dep` 3.4.5 resolve for target `t`. The controlling request gives, without normalization or exclusion:

`D = { (Rust/std 1.80.0, edition 2021, target t, profile p) | R(t) and p in {ordinary debug, ordinary release} }`.

This symbolic predicate preserves “every target” without an unjustified finite inventory. The source has no `cfg`, Cargo features, build script, macro-generated API, profile-dependent assertion, target-specific branch, or generated artifact. Consequently each source argument below is parametric in `t` and `p`; the admitted Rust axiom expressly covers all such targets and profiles. No dynamic support policy makes the 2026-08-01 audit cutoff alter `D`.

The complete exported surface is the safe free function `force_unreachable` and unsafe free function `delegated_nonzero`. There are no public fields, constructors, types, methods, traits/impls, callbacks, statics, macros, reexports, hidden items, FFI declarations, or representation invariants in the submitted source. The only external unsafe surface is `peer_unsafe_dep::duplicate_nonzero`.

## Obligation ledger and proofs

### C1 / O1 — `force_unreachable` (`lib.rs:4-7`)

Valid use imposes no safety precondition because the API is safe. For any configuration in `D`, the well-typed call `force_unreachable()` enters its body and, with no branch or earlier operation, executes `std::hint::unreachable_unchecked()`.

The exact Rust 1.80.0 standard-library Safety section says: “Reaching this function is Undefined Behavior.” ([versioned authority](https://doc.rust-lang.org/1.80.0/std/hint/fn.unreachable_unchecked.html#safety)). Thus the operation requires that it not be reached. That proposition is false in this execution. The authority applies throughout `D`, so any member of `D` supplies the complete certificate: valid safe use; unconditional reachability; false required proposition; authoritative UB consequence. C1 is therefore **UNSOUND**, not merely unproved.

The adjacent comment, “This site is assumed to be unreachable,” is circular and false for every invocation; it proves no dominating fact. This is both an implementation defect and a deficient proof artifact. No replacement `SAFETY` comment can repair the current body. Resolution requires removing the reachable operation (for example, using defined behavior) or changing the API boundary and documenting a sufficient compiler-enforced unsafe contract. Either is a new artifact requiring audit.

For O1, the refutation is parametric over all of `D`; no configuration remainder exists.

### C2 / O2 — local caller-side obligation (`lib.rs:15-18`)

Valid use is exactly `value: u8` with `value != 0`. The dependency's submitted unsafe contract has the identical call precondition. The wrapper passes the same `value` directly, so its caller obligation entails the dependency call's caller-side obligation in every configuration in `D`. The adjacent `SAFETY` comment adequately records this local implication.

### C2 / O3 — unsafe dependency provider obligation

Local satisfaction of an unsafe callee's precondition does not establish that its implementation is correct. C2 additionally requires:

> For every `(t,p)` in `D` and every `v: u8` with `v != 0`, every permitted execution of `peer_unsafe_dep::duplicate_nonzero(v)` version 3.4.5 is free of Rust undefined behavior.

This is the smallest missing soundness proposition. The dependency body, generated output, prior audit, and binary are absent; the packet supplies no implementation assertion; and the human expressly declines an `UNSAFE-DEP` admission. An exact pin establishes identity only. Therefore O3 has no covered configuration, aggregate coverage for C2 is the intersection of O2's `D` with O3's unproved region, and `D ⊆ Covered` is not established. No valid execution exhibiting dependency UB is supplied, so the failure of universal proof does not establish an existential refutation. C2 is **UNPROVED**, not `UNSOUND`.

The submitted dependency documentation also says `duplicate_nonzero` returns `value`. The wrapper syntactically returns the dependency's result, but whether that result equals the input is likewise **UNPROVED** without the separate provider proposition that every valid call returns `v`. No UB-free counterexample exists in the packet, so `CONTRACT-BROKEN` is not established. `lib.rs` itself does not expressly promise input/output equality beyond delegation.

Minimum resolution is either a recursive source audit of the exact dependency implementation over all of `D`, or an authorized, precise `UNSAFE-DEP` entry admitting its UB-freedom (and its return-value postcondition if that behavior is claimed). The present trust decision forbids the latter.

## TCB and evidence audit

| Entry | Proposition and scope | Disposition | Consumer |
|---|---|---|---|
| AXIOM-UNREACHABLE-1.80 | Reaching `std::hint::unreachable_unchecked` is UB, for Rust 1.80.0 on every target/profile in `D`; exact URL and quotation above. | Accepted after direct citation verification | O1 |
| Proposed unsafe-dependency trust | The exact 3.4.5 implementation honors its unsafe contract for all valid calls in `D`. | Not proposed or accepted; expressly declined | O3 (blocked) |

There are no other admitted compatibility, implementation, tool, deployment, or dependency propositions. No tests or tool-derived evidence were supplied or used. The accepted axiom's version exactly matches `D`, so no compatibility bridge is needed.

## Residual scope and review triggers

The unavailable dependency implementation and any of its generated output remain unaudited. Binary/compiler-backend correctness, nonordinary profiles, other Rust releases, targets outside `R`, and broader safe-API robustness are outside the stated claims. Re-audit is required for source or contract changes; a Rust/domain/profile change; dependency identity, implementation, features, or trust-disposition changes; or material change to the cited Rust documentation.

All in-scope surfaces and obligations have dispositions. C1's `UNSOUND` certificate is complete across `D`; C2's exact missing implication and absence of an existential certificate are explicit.
