# Unsafe Rust source audit

## Claim and verdict

For the supplied `Cargo.toml` and `src/lib.rs`, every well-typed safe call to `value_or_zero` in every configuration supported by **either** current policy is free of Rust undefined behavior and returns the contained byte for `Some(byte)`, or zero for `None`. This is a source-level claim for Rust/stdlib 1.84.0, 1.85.0, and 1.86.0, relative to the conspicuous accepted premise `BUILD-MAP-C` below.

- **Soundness: PROVED** over the conservative union `U` defined below.
- **Documented return postcondition: PROVED** over `U`.
- **Combined mandatory result: PROVED** over `U`, relative to `BUILD-MAP-C` and the version-matched Rust axioms cited below.
- **Exact project support-policy identity: UNPROVED.** Scarlet and Indigo conflict and no authority selects either. This does not block the source theorem because `U` contains every configuration promised by either policy; calling `U` the audit domain does not create a new support commitment.
- No `UNSOUND` or `CONTRACT-BROKEN` witness exists in the inspected source.

Audit date: 2026-08-01. No build, execution, test, expansion, prior audit, dependency, generated artifact, or binary/backend claim was used. The crate is edition 2021, `no_std`, has no dependencies, and has only the two declared Boolean features.

## Configuration closure

Let `V={1.84.0,1.85.0,1.86.0}`, `X=x86_64-unknown-linux-gnu`, `A=aarch64-unknown-linux-gnu`, `W=wasm32-unknown-unknown`, and `f`,`h` denote `turbo`,`hardened`. The exact conservative audit domain `U = Scarlet ∪ Indigo` is:

| Case | Members of `U` |
|---|---|
| `!f` | every `v∈V`, `t∈{X,A,W}`, and either `h` |
| `f, t=X` | every `v∈V` and either `h` |
| `f, t=A, h` | every `v∈V` |
| `f, t=A, !h` | `v∈{1.85.0,1.86.0}` |
| `f, t=W` | none |

This is an exhaustive Boolean simplification of the two published predicates. All profiles and debug-assertion states are covered parametrically: neither selects or changes any audited expression. `h` likewise selects no source. Version and non-`W` target do not change either function body.

For each exact release, the Reference says an `all` predicate is true when all its predicates are true and a `cfg` attribute retains its item on true and removes it on false: [1.84 predicate](https://doc.rust-lang.org/1.84.0/reference/conditional-compilation.html#conditional-compilation), [1.84 attribute](https://doc.rust-lang.org/1.84.0/reference/conditional-compilation.html#the-cfg-attribute), [1.85 predicate](https://doc.rust-lang.org/1.85.0/reference/conditional-compilation.html#conditional-compilation), [1.85 attribute](https://doc.rust-lang.org/1.85.0/reference/conditional-compilation.html#the-cfg-attribute), [1.86 predicate](https://doc.rust-lang.org/1.86.0/reference/conditional-compilation.html#conditional-compilation), [1.86 attribute](https://doc.rust-lang.org/1.86.0/reference/conditional-compilation.html#the-cfg-attribute). Together with `BUILD-MAP-C`, `f && t=W` retains `compile_error!`; the version-matched macro contract says it causes compilation to fail: [1.84](https://doc.rust-lang.org/1.84.0/std/macro.compile_error.html), [1.85](https://doc.rust-lang.org/1.85.0/std/macro.compile_error.html), [1.86](https://doc.rust-lang.org/1.86.0/std/macro.compile_error.html). Thus the expressly unsupported `turbo+W` combination is effectively rejected for every `v`, `h`, profile, and debug-assertion state; no library artifact reaches the unsafe branch there.

## Boundary, invariants, and obligation ledger

The sole language-reachable crate API is the safe free function `value_or_zero(Option<u8>) -> u8`. Mutually exclusive `#[cfg(not(feature="turbo"))]` and `#[cfg(feature="turbo")]` definitions make exactly one body present. There are no public fields/types/statics, unsafe APIs/traits/impls, callbacks, FFI, exported macros, hidden items, reexports, constructors, generated APIs, or custom destruction. There is no persistent representation invariant.

| ID | Site and exact obligation | Derivation | Status |
|---|---|---|---|
| O1 | safe API has no hidden safety precondition | The input is an owned, valid `Option<u8>`; the fallback uses only safe `unwrap_or`, and the turbo unsafe precondition is discharged by O2. | PROVED on `U` |
| O2 | `unwrap_unchecked` must not receive `None` | On the only path reaching it, `value.is_none()` was false because the true branch returned. `is_none` identifies `None`; therefore this two-variant value is `Some`. No intervening mutation or call occurs before the owned value is consumed. | PROVED for every `f` artifact in `U` |
| O3 | documented return value | If `!f`, `unwrap_or(0)` returns the contained `Some` value or default zero. If `f`, `None` returns zero; otherwise O2 permits `unwrap_unchecked`, which returns the contained `Some` value. | PROVED on `U` |
| O4 | configuration selection/rejection | Versioned `cfg` rules plus accepted `BUILD-MAP-C`; derivation above. | PROVED for the three releases/targets only |

The three standard-library versions have identical material contracts: `is_none` “Returns true if the option is a `None` value”; `unwrap_unchecked` returns the contained `Some` value and calling it on `None` is undefined behavior; `unwrap_or` returns the contained `Some` value or the supplied default. Version-matched sources: [1.84 `is_none`](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.is_none), [`unwrap_unchecked`](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_unchecked), [`unwrap_or`](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_or); [1.85 `is_none`](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.is_none), [`unwrap_unchecked`](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.unwrap_unchecked), [`unwrap_or`](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.unwrap_or); [1.86 `is_none`](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.is_none), [`unwrap_unchecked`](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.unwrap_unchecked), [`unwrap_or`](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.unwrap_or).

The adjacent `SAFETY` comment states the decisive dominating branch fact and is correct. A more contract-explicit replacement would be: “`Option::unwrap_unchecked` requires `self` not be `None`. `is_none()` was false on this path because the true branch returned, so `value` is `Some` and satisfies that requirement; the call returns its contained byte.” This is documentation hardening, not a soundness finding.

## TCB audit log

**`BUILD-MAP-C` is accepted and consumed only for O4.** Its exact scope is the bundled Cargo for Rust 1.84.0/1.85.0/1.86.0, the supplied manifest/source, all supported profiles, the two named feature-to-`cfg` mappings, and the three named target-to-`target_arch` mappings. It admits no Rust semantics, branch correctness, other version, or backend/binary correctness. Human disposition: accepted. Re-audit on any identity, feature, target, manifest/source cfg, or disposition change.

The remaining entries are version-matched `AXIOM`s: the cited Option contracts, conditional-compilation rules, and `compile_error!` contract. No dependency, implementation, external, deployment, probabilistic, or tool premise is consumed. TCB identity is the supplied `TCB.md` snapshot; no broader trust was inferred.

## Residual scope and triggers

Which published policy governs remains deliberately unresolved. Configurations outside `U`, compiler/backend correctness, successful compilation of supported non-rejected cases, and binary behavior are not claimed. Re-audit on source/manifest or policy resolution/change; expansion of versions, targets, features, profiles, or build inputs; change to `BUILD-MAP-C`; or material change to any cited versioned contract.

All in-scope unsafe operations, safe surfaces, postconditions, configurations in `U`, and consumed premises have a disposition. No tool-derived evidence was used.
