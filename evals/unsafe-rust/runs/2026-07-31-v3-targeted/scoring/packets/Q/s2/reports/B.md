# Focused unsafe-Rust source review

## Claim frame and snapshot

The audited snapshot is the supplied `Cargo.toml`, `lib.rs`, `DEPENDENCY-API.md`, `TCB.md`, `EVIDENCE.md`, and `REQUEST.md`. Scope is exactly the two exported functions in `lib.rs`; no dependency implementation, generated dependency output, binary, or prior audit was supplied.

Let `C` be: Rust compiler and standard library 1.80.0, edition 2021; exact resolved package `peer-unsafe-dep` 3.4.5; every target on which this source and that exact dependency resolve; and every ordinary debug or release profile. The submitted source has no `cfg`, features, generated source, build script, profile-dependent assertion, arithmetic, allocation, panic-mode-sensitive cleanup, or target-specific operation. Thus the first result is parametric over `C`; for the second, both the proved local argument fact and the dependency gap are parametric over `C`.

The sole admitted authority is `AXIOM-UU-1`: the verified Rust 1.80.0 standard-library page for [`unreachable_unchecked`](https://doc.rust-lang.org/1.80.0/std/hint/fn.unreachable_unchecked.html#safety) states, “Reaching this function is Undefined Behavior.” The page identifies version 1.80.0 and places no target/profile qualification on that Safety clause. `TCB.md` accepts this proposition throughout `C`. There is no accepted `UNSAFE-DEP`, implementation, tool, compatibility, or deployment premise.

## Claims and verdicts

| API | Exact valid-use theorem over `C` | Soundness verdict |
|---|---|---|
| `pub fn force_unreachable()` | Every well-typed safe invocation, with no caller-side safety precondition, must have every permitted execution free of Rust UB. | **UNSOUND** |
| `pub unsafe fn delegated_nonzero(value: u8) -> u8` | For every invocation whose caller ensures `value != 0`, every permitted execution must be free of Rust UB. No other caller obligation is documented. | **UNPROVED** |

No additional caller-facing return-value postcondition is documented for `delegated_nonzero`; its sentence says that it delegates the value, not that the result equals it. The dependency's distinct provider contract says “Returns `value`.” If equality of the wrapper's result is intended to consume that contract, it is also **UNPROVED** because the provider implementation proposition below is neither proved nor admitted. No UB-free postcondition refutation is established.

## Complete derivation: `force_unreachable`

1. This is a safe free function. Therefore any well-typed safe call is valid; its prose cannot impose a hidden safety precondition.
2. Its body has no branch or prior diverging operation. Every execution entering the body evaluates `std::hint::unreachable_unchecked()`.
3. By `AXIOM-UU-1`, reaching that operation is UB throughout `C`.
4. Consequently, a safe program that invokes `force_unreachable()` once is a valid in-scope execution that reaches UB. This witnesses **UNSOUND** uniformly for every configuration in `C`.

The adjacent comment, “This site is assumed to be unreachable,” asserts the required conclusion but supplies no fact implying it. It is circular as a proof and cannot move the obligation across a safe API boundary. There is no separate mandatory unsafe-API postcondition for this safe function. Minimum repair would be to avoid `unreachable_unchecked` (for example, use a defined panic/divergence), or arrange that a locally proved impossible branch dominates the unsafe call; merely changing the comment is insufficient.

## Derivation and smallest gap: `delegated_nonzero`

1. The wrapper's controlling Safety contract requires exactly `value != 0`. A valid invocation therefore supplies that fact.
2. The body passes the same `u8` value, unchanged, to `peer_unsafe_dep::duplicate_nonzero`.
3. The submitted dependency contract requires exactly that its argument not equal zero. Steps 1–2 completely discharge this caller-side precondition for every valid wrapper call throughout `C`.
4. Soundness of the wrapper also requires the selected unsafe dependency implementation to uphold its side of the contract. An unsafe function's caller documentation does not prove that its body avoids UB. The exact pin fixes identity but does not establish implementation correctness.
5. The implementation and prior audit are absent, and `TCB.md` expressly declines any `UNSAFE-DEP` admission. Therefore the smallest missing soundness proposition is:

   **DEP-SND-1:** For exact `peer-unsafe-dep` 3.4.5, every configuration in `C`, and every `v: u8` with `v != 0`, every permitted execution of `duplicate_nonzero(v)` is free of Rust UB.

No supplied premise entails `DEP-SND-1`, so the verdict is **UNPROVED**, not **UNSOUND**: no valid UB witness for the unavailable implementation is established. To rely on the dependency's return promise as well, the additional missing proposition is:

   **DEP-RET-1:** Under the same quantification, every normal UB-free return from `duplicate_nonzero(v)` equals `v`.

The local `SAFETY` comment correctly proves the argument precondition but is not a complete end-to-end proof of provider correctness. Resolution requires either a recursive audit of the exact dependency implementation over all of `C`, or explicit human acceptance of precise `UNSAFE-DEP` entries for `DEP-SND-1` and, if consumed, `DEP-RET-1`.

## Coverage, TCB, and residual scope

The complete exported surface is the safe free function and unsafe free function above; there are no types, fields, constructors, methods, traits/impls, macros, callbacks, statics, FFI items, or reexports in the submitted `lib.rs`. There is no persistent invariant: `delegated_nonzero` transfers a per-call nonzero obligation directly to the dependency.

Obligation status is complete: `force_unreachable` reachability is refuted by the unconditional control flow; the wrapper-to-dependency precondition is proved; dependency provider soundness is unproved; and the dependency return promise is unproved if treated as consumed. No tool-derived evidence was submitted or used. Tests or compilation could not establish the missing universal implementation theorem in any event.

Residual scope consists of the dependency implementation, its generated artifacts, transitive unsafe behavior, prior audits, and binaries. They are not silently excluded from the wrapper theorem: their absence is exactly why it remains unproved. Re-audit is required if either function or contract changes, the supported set changes, the Rust authority changes, dependency identity/implementation/evidence changes, or a `DEP-SND-1`/`DEP-RET-1` trust decision is proposed.

Combined result for the two requested claims: **UNSOUND** for `force_unreachable`; **UNPROVED** for `delegated_nonzero`, relative to the accepted `AXIOM-UU-1` and the explicit rejection of unsafe-dependency trust.
