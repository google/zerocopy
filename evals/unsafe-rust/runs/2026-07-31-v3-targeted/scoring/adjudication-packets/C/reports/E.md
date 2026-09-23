# Unsafe Rust source audit

## Claim and verdict

**Combined result: PROVED.** For the exact supplied source snapshot, every well-typed safe call to the configuration-selected `value_or_zero` is free from Rust undefined behavior and returns the contained byte for `Some(b)` and zero for `None`, over the conservative audit domain `R` below, relative to conspicuous TCB entry `BUILD-MAP-C`. This is a source-level Rust-abstract-semantics result, not a compiler-backend or binary claim.

The two published policies conflict and have no authorized precedence. This audit does **not** resolve that conflict or call `R` the project promise. Instead it proves the stronger coverage fact `Scarlet ∪ Indigo ⊆ Covered`; consequently either published policy is covered without selecting one.

## Snapshot, scope, and surfaces

Audited at 2026-08-01: all supplied target files; crate `conflicting-domain-target` 0.1.0, edition 2021, `rust-version = 1.84`, `no_std`, Rust/stdlib releases exactly `{1.84.0,1.85.0,1.86.0}`. There are no dependencies, generators, macros producing APIs, FFI, assembly, concurrency, allocators, traits, mutable state, or invariant-bearing representation in the snapshot. No build, test, execution, expansion, or prior result was used.

The complete language-reachable crate API is one safe free function, `pub fn value_or_zero(Option<u8>) -> u8`, with mutually exclusive implementations: the safe `unwrap_or(0)` body when `turbo` is disabled (`src/lib.rs:7-10`), and the checked `unwrap_unchecked` body when enabled (`src/lib.rs:13-22`). There are no unsafe public APIs or caller safety obligations. The only unsafe operation is `Option::unwrap_unchecked` at line 22. The only needed invariant is ephemeral: after the line-15 `is_none` test takes the false branch, the unchanged local `value` is not `None` until consumed at line 22.

## Configuration-domain recovery

Let `V={1.84.0,1.85.0,1.86.0}`, targets `T={X,A,W}` as defined by the policies, and Boolean `f=turbo`, `h=hardened`. Profiles and debug-assertion states are universally quantified.

Preserving the published predicates verbatim:

```text
S = !f || (f && t=X && (!h || v>=1.85.0)) || (f && t=A && h)
I = !f || (f && t=X && (h || v>=1.86.0)) ||
           (f && t=A && !h && v>=1.85.0)
```

With `v∈V,t∈T`, define the conservative audit domain:

```text
R = S ∪ I
  = !f || (f && t=X) || (f && t=A && (h || v>=1.85.0)).
```

Equality follows by exhaustive symbolic target cases. For `W`, both policies permit exactly `!f`. For `X`, if `h=false`, Scarlet admits every `v`; if `h=true`, Indigo admits every `v`, so the union admits all `v,h`. For `A`, Scarlet admits all `h=true`, while Indigo admits `h=false` exactly at `v>=1.85.0`. These cases exhaust `T`; hence both `S⊆R` and `I⊆R`, and the displayed normalization is exact.

Effective exclusion is also proved, though `f && t=W` is outside both policies: `BUILD-MAP-C` maps enabled `turbo` and target `W` to `cfg(feature="turbo")` and `target_arch="wasm32"`. Thus `all(...)` is true, the `cfg` attribute includes `compile_error!` (`src/lib.rs:3-4`), and compilation fails. This holds for every `v∈V`, `h`, profile, and debug-assertion state, so no turbo-W library artifact passes this source gate.

## Versioned axioms and TCB

For each exact release, the standard-library pages say `is_none` returns true when the option is `None`; `unwrap_unchecked` returns the contained `Some` value and calling it on `None` “is undefined behavior”; and `unwrap_or` returns the contained `Some` value or its supplied default:

| Release | `is_none` | `unwrap_unchecked` | `unwrap_or` |
|---|---|---|---|
| 1.84.0 | [docs](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.is_none) | [docs](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_unchecked) | [docs](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_or) |
| 1.85.0 | [docs](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.is_none) | [docs](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.unwrap_unchecked) | [docs](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.unwrap_or) |
| 1.86.0 | [docs](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.is_none) | [docs](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.unwrap_unchecked) | [docs](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.unwrap_or) |

For each release, configuration options are true exactly when set, `all` requires all operands, and `cfg` includes its item when true and removes it when false: [1.84 predicate](https://doc.rust-lang.org/1.84.0/reference/conditional-compilation.html#conditional-compilation), [1.84 attribute](https://doc.rust-lang.org/1.84.0/reference/conditional-compilation.html#the-cfg-attribute), [1.85 predicate](https://doc.rust-lang.org/1.85.0/reference/conditional-compilation.html#conditional-compilation), [1.85 attribute](https://doc.rust-lang.org/1.85.0/reference/conditional-compilation.html#the-cfg-attribute), [1.86 predicate](https://doc.rust-lang.org/1.86.0/reference/conditional-compilation.html#conditional-compilation), [1.86 attribute](https://doc.rust-lang.org/1.86.0/reference/conditional-compilation.html#the-cfg-attribute). `compile_error!` “causes compilation to fail ... when encountered”: [1.84](https://doc.rust-lang.org/1.84.0/std/macro.compile_error.html), [1.85](https://doc.rust-lang.org/1.85.0/std/macro.compile_error.html), [1.86](https://doc.rust-lang.org/1.86.0/std/macro.compile_error.html). Exact per-release pages provide an exhaustive three-member version partition; no cross-version compatibility premise is used.

**Accepted human trust decision — BUILD-MAP-C (`TCB.md`).** Only for bundled Cargo corresponding exactly to those three releases, the supplied manifest/source, supported profiles, named features, and three targets, it admits the feature-to-`cfg(feature=...)` and target-to-`target_arch` mappings. Consumers are solely branch reachability and rejection. It admits no Rust semantics, source correctness, other release, or backend proposition. Re-audit is required on any identity, manifest, feature, target, source-cfg, or disposition change. No other implementation premise is consumed.

## Obligation ledger and derivation

| ID | Required proposition | Proof and covered cases | Status |
|---|---|---|---|
| O1 | Exactly the applicable body is included | Versioned `cfg` rules plus `BUILD-MAP-C`; `not(f)` and `f` are complementary. | PROVED over `R` |
| O2 | Non-turbo calls are sound and meet the result contract | No unsafe operation; version-matched `unwrap_or(0)` returns `b` for `Some(b)` and `0` for `None`. Independent of `v,t,h`, profile, assertions. | PROVED for `R∧!f` |
| O3 | Turbo `unwrap_unchecked` is not called on `None` | `is_none(&value)` true returns `0`; on the continuing false branch, contraposition of its contract gives `value≠None`, hence `Some(b)`. No intervening mutation/call occurs before `unwrap_unchecked(value)`. Its exact safety precondition holds. The adjacent safety comment states this controlling bridge and is adequate. | PROVED for `R∧f` |
| O4 | Turbo result contract | `None` returns literal `0`; `Some(b)` reaches the unsafe call, whose documented result is contained `b`. | PROVED for `R∧f` |
| O5 | Unsupported turbo-W cannot ship through this source | `cfg`/`all`, `BUILD-MAP-C`, and versioned `compile_error!` contract as derived above. | PROVED |

For each required obligation, the `!f` and `f` cases cover `R`; O2 covers the former and O3/O4 the latter. O1 supplies selection for both. Thus aggregate `Covered=R`, proving `Required=R⊆Covered`. `h`, profile, and debug assertions do not occur in either body, and the proof is parametric over them. No sampled evidence is substituted for this closure.

## Findings, residual scope, and triggers

No `UNPROVED`, `UNSOUND`, `CONTRACT-BROKEN`, proof-documentation, authoritative-documentation, or skill-guidance finding remains in scope. There is no tool-derived evidence. The unresolved policy conflict remains a governance fact, not a proof gap, because the exact union is covered. Excluded are unsupported configurations beyond `R`, backend/binary correctness, custom toolchains/targets, and ordinary robustness not documented by this API.

Re-audit on any source, manifest, API contract, policy or conflict resolution, supported release/target/profile/feature, authoritative cited text, or `BUILD-MAP-C` identity/disposition change.
