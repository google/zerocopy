# Unsafe Rust source audit

## Claim and verdict

**SOUND-1 — PROVED.** For the supplied `Cargo.toml` and `src/lib.rs`, every well-typed safe call to `value_or_zero` in every configuration admitted by either current policy is free from Rust undefined behavior under the documented abstract semantics of Rust 1.84.0, 1.85.0, and 1.86.0, relative only to accepted `BUILD-MAP-C` below.

**POST-1 — PROVED.** Over the same domain, `value_or_zero(Some(x)) == x` and `value_or_zero(None) == 0`.

**POLICY-IDENTITY — UNPROVED.** No evidence selects Scarlet or Indigo as *the* project promise. This does not weaken SOUND-1: its conservative domain is their union and therefore contains either candidate. The audit does not resolve or replace the published policies.

Snapshot: exactly the supplied manifest, source, two policies, and `TCB.md`; edition 2021, `#![no_std]`, Rust/stdlib versions `V={1.84.0,1.85.0,1.86.0}`. No dependencies, generated artifacts, build scripts, macros producing APIs, FFI, assembly, allocator use, concurrency, or prior audit appear. This was source-only; nothing was built, run, tested, or expanded. Audit cutoff: 2026-08-01.

## Domain and configuration closure

Let `X`, `A`, `W`, `f`, and `h` have the policies' exact meanings, and universally quantify all Cargo profiles and both debug-assertion states. Preserve the controlling predicates:

`S = !f ∨ (f∧t=X∧(!h∨v>=1.85)) ∨ (f∧t=A∧h)` (Scarlet)

`I = !f ∨ (f∧t=X∧(h∨v>=1.86)) ∨ (f∧t=A∧!h∧v>=1.85)` (Indigo).

With the common restrictions `v∈V` and `t∈{X,A,W}`, define conservative `Required=S∪I`. Exact Boolean normalization gives

`Required = !f ∨ (f∧t=X) ∨ (f∧t=A∧(h∨v>=1.85))`.

For `X`, the union contains `(!h∨v>=1.85)∨(h∨v>=1.86)`, which is true because it contains `!h∨h`. For `A`, direct distribution gives `h∨(!h∧v>=1.85)`. Neither predicate admits `(f,t=W)`.

`BUILD-MAP-C` maps the Cargo features and three target triples to the source `cfg` predicates for every exact release/profile. In each release, the Reference says `cfg` conditionally includes its attached construct, and `compile_error!` causes compilation to fail when encountered: [1.84 cfg](https://doc.rust-lang.org/1.84.0/reference/conditional-compilation.html#the-cfg-attribute), [compile_error](https://doc.rust-lang.org/1.84.0/std/macro.compile_error.html); [1.85 cfg](https://doc.rust-lang.org/1.85.0/reference/conditional-compilation.html#the-cfg-attribute), [compile_error](https://doc.rust-lang.org/1.85.0/std/macro.compile_error.html); [1.86 cfg](https://doc.rust-lang.org/1.86.0/reference/conditional-compilation.html#the-cfg-attribute), [compile_error](https://doc.rust-lang.org/1.86.0/std/macro.compile_error.html). Thus `lib.rs:3-4` effectively rejects every `f∧t=W` build. The other two `cfg`s select exactly one function body.

The semantic proof covers

`Covered = !f ∨ (f∧t∈{X,A})`

over all stated versions, `h`, profiles, and debug states. `Required⊆Covered` follows immediately from the normalized formula. `h`, profile, and debug state select no source and affect no proof step. Target affects only the proved rejection; the accepted `X/A` body is identical. The unsupported `(v=1.84,t=A,f,h=false)` compiles but lies outside both policies; rejection is not needed for the theorem.

## Boundary, obligations, and proof

The complete crate-defined public surface is one safe free function, with mutually exclusive bodies: `lib.rs:7-9` when `!f`, and `lib.rs:13-21` when `f`. There are no public fields, constructors, traits/impls, methods, statics, callbacks, reexports, hidden items, or generated APIs. There is no persistent invariant; turbo has only the local fact `L-SOME: value is not None` at line 20.

Version-matched `Option` documentation independently states in each release that `is_none` returns true for `None`, `unwrap_unchecked` returns the contained `Some` value and calling it on `None` is UB, and `unwrap_or` returns the contained value or its default: [1.84 is_none](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.is_none), [unchecked](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_unchecked), [unwrap_or](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_or); [1.85 is_none](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.is_none), [unchecked](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.unwrap_unchecked), [unwrap_or](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.unwrap_or); [1.86 is_none](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.is_none), [unchecked](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.unwrap_unchecked), [unwrap_or](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.unwrap_or). Each page also declares `Option`'s only variants, `None` and `Some`.

| ID | Site/domain | Required proposition and derivation | Status |
|---|---|---|---|
| O-NON | lines 7-9; `!f` | `unwrap_or(0)` has no unsafe precondition and its exact contract yields `x` for `Some(x)`, otherwise `0`. | PROVED |
| O-GUARD | lines 15-20; `f`, accepted `X/A` | If `None`, `is_none()` is true and line 16 returns. Fallthrough therefore implies not `None`; with the two-variant declaration, it is `Some`. The owned local is neither mutated nor exposed between check and call. | PROVED |
| O-UNWRAP | line 20; same domain | `L-SOME` satisfies the unsafe call's exact non-`None` obligation; the call returns the contained byte. | PROVED |

These cases prove UB freedom and POST-1, and their configuration union is `Covered`. No backward-compatibility assumption is used: all three versioned contracts were checked separately. No tool-derived evidence is used.

## TCB audit log

**BUILD-MAP-C — ACCEPTED, conspicuous.** Category: implementation/build-tool premise. Identity, proposition, scope, exclusion list, consumer restriction, approver, and triggers are exactly `TCB.md`. It is consumed only by configuration reachability, mutually exclusive body selection, and effective `f∧W` rejection—not by any Rust semantic or body-correctness step. Rust/std links above are authoritative axioms, not extra implementation assumptions. No other TCB entry is consumed.

## Finding: local proof documentation

**DOC-1 — implementation PROVED; proof comment deficient.** The existing line-19 comment conveys the core branch argument but does not name `unwrap_unchecked`'s exact obligation, the `is_none` contract, or the resulting postcondition. Suggested replacement:

```rust
// SAFETY: `is_none` returns true for `None`; that branch returned, so
// `value` is not `None`, satisfying `unwrap_unchecked`. It returns the
// contained `Some` byte.
unsafe { value.unwrap_unchecked() }
```

This is documentation debt, not an implementation defect or hidden caller obligation.

Residual scope is limited to unsupported configurations and binary/backend correctness. Re-audit on any source, manifest, policy resolution/change, supported version/target/profile axis, relevant Rust documentation, or `BUILD-MAP-C` identity/disposition change. Every in-scope surface, obligation, postcondition, configuration transformation, and consumed premise has a disposition.
