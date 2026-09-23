# Unsafe Rust source audit

## Claim and verdict

**Artifact.** The exact supplied `Cargo.toml`, `src/lib.rs`, `POLICY-SCARLET.md`, `POLICY-INDIGO.md`, and `TCB.md`; source-only review, cutoff 2026-08-01. No generated code, dependencies, build script, FFI, assembly, allocator, concurrency, or prior audit exists in the supplied snapshot. Nothing was built, expanded, run, or tested.

Let `V={1.84.0,1.85.0,1.86.0}`, `T={X,A,W}` as defined by the policies, and let `f`/`h` denote `turbo`/`hardened`. Define the **conservative audit domain**

`D = { (v,t,f,h,profile,debug_assertions) | v in V, t in T, f,h Boolean, every Cargo profile and either debug-assertion state, and !(f && t=W) }`.

`D` is an audit domain, not a newly selected support policy.

- **Safe-library soundness: PROVED over D**, relative to TCB log below: every well-typed safe call to `value_or_zero` is free of Rust undefined behavior.
- **Documented result: PROVED over D:** `Some(x)` returns `x`; `None` returns zero.
- **Combined mandatory result: PROVED over D.** There is no public unsafe API or additional unsafe-API postcondition.
- **Exact project support predicate: UNPROVED.** Scarlet and Indigo are simultaneously current, conflict, and have no authorized resolution. Nevertheless, every configuration supported by either policy lies in `D`, so this governance gap does not weaken the two code verdicts.

This is a Rust abstract-semantics result, not a backend, binary, or deployment claim.

## Authorities and TCB audit log

The version-matched standard-library contract says `is_none` reports whether the option is `None`, `unwrap_unchecked` returns the contained `Some` value and calling it on `None` is UB, and `unwrap_or` returns the contained value or supplied default: [1.84 `is_none`](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.is_none), [`unwrap_unchecked`](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_unchecked), [`unwrap_or`](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_or); [1.85 `is_none`](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.is_none), [`unwrap_unchecked`](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.unwrap_unchecked), [`unwrap_or`](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.unwrap_or); [1.86 `is_none`](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.is_none), [`unwrap_unchecked`](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.unwrap_unchecked), [`unwrap_or`](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.unwrap_or).

For each release, the Reference defines configuration-option truth, `all`/`not`, and a `cfg` attribute's inclusion/removal effect: [1.84](https://doc.rust-lang.org/1.84.0/reference/conditional-compilation.html#conditional-compilation), [attribute](https://doc.rust-lang.org/1.84.0/reference/conditional-compilation.html#the-cfg-attribute); [1.85](https://doc.rust-lang.org/1.85.0/reference/conditional-compilation.html#conditional-compilation), [attribute](https://doc.rust-lang.org/1.85.0/reference/conditional-compilation.html#the-cfg-attribute); [1.86](https://doc.rust-lang.org/1.86.0/reference/conditional-compilation.html#conditional-compilation), [attribute](https://doc.rust-lang.org/1.86.0/reference/conditional-compilation.html#the-cfg-attribute). The corresponding standard-library macro pages specify compilation failure for `compile_error!`: [1.84](https://doc.rust-lang.org/1.84.0/std/macro.compile_error.html), [1.85](https://doc.rust-lang.org/1.85.0/std/macro.compile_error.html), [1.86](https://doc.rust-lang.org/1.86.0/std/macro.compile_error.html).

| ID | Category/disposition | Exact admitted proposition; scope; consumers |
|---|---|---|
| `AXIOM-OPT-{84,85,86}` | Rust authority, verified | The preceding three `Option` method contracts, only for the matching release; `OBL-N`, `OBL-T`. Recheck if those documents or supported releases change. |
| `AXIOM-CFG-{84,85,86}` | Rust authority, verified | The preceding `cfg` and `compile_error!` semantics, only for the matching release; `OBL-C`. Same trigger. |
| `BUILD-MAP-C` | **OUT-OF-BAND/IMPLEMENTATION, explicitly human-accepted** | Exactly the feature-to-`cfg(feature=...)` and named-target-to-`target_arch` mappings stated in `TCB.md`, for the bundled Cargo of the three releases and supplied manifest/source; consumed only by `OBL-C`. It admits no Rust semantics, branch correctness, other version, or backend correctness. Recheck on every trigger listed in `TCB.md`. |

No other implementation or build-tool premise is consumed. No tool-derived evidence is used.

## Configuration closure

Scarlet and Indigo each allow all non-`turbo` cases and restrict `turbo` to `X` or `A`; hence each predicate is a subset of `D`. Their union need not be declared the policy to establish this containment. `hardened`, profile, and debug assertions select no source here, so the proof is parametric in them.

By `BUILD-MAP-C` and `AXIOM-CFG`, `f && t=W` makes the crate-level `cfg(all(...))` true, retains `compile_error!`, and compilation fails; no library artifact from that combination can ship. For every member of `D`, that item is removed. Exactly one function body remains: `f=false` retains `cfg(not(feature="turbo"))`; `f=true` retains `cfg(feature="turbo")`. This is an exhaustive partition. The source-admitted `v=1.84.0,t=A,f=true,h=false` case is outside both policies but is deliberately covered by `D`; its compilation does not silently make it supported.

## Boundary, invariant, and obligation coverage

The sole language-reachable crate surface is safe `pub fn value_or_zero(Option<u8>)->u8`, with the two mutually exclusive bodies above. There are no public fields, other constructors or methods, traits/impls, statics, reexports, callbacks, exported/generated macros, hidden APIs, or custom destruction. No persistent invariant-bearing state exists.

`INV-LOCAL`: in the `turbo` body, after the `is_none()` branch falls through and until `unwrap_unchecked`, `value` is not `None`. The owned local is not mutated and no call intervenes.

| ID | Proposition and derivation | Domain | Status |
|---|---|---|---|
| `OBL-C` | The preceding `cfg` partition is exhaustive and `turbo+W` is effectively rejected. | `V,T,f,h`, all profiles/debug states | PROVED |
| `OBL-N` | With `f=false`, version-matched `unwrap_or(0)` returns the contained `u8` or zero; it is a safe standard-library call. | `D && !f` | PROVED |
| `OBL-T` | With `f=true`, `is_none()==true` returns zero. Fallthrough means not `None`, establishing `INV-LOCAL` and satisfying `unwrap_unchecked`; that method returns the contained byte. | `D && f` | PROVED |
| `OBL-API` | `OBL-C` partitions `D`; `OBL-N` and `OBL-T` cover both parts with no caller safety precondition. | `D`, all safe inputs | PROVED |

The result guarantee follows in both bodies. No panic/unwind, alias, lifetime, arithmetic, zero-sized, concurrency, target-layout, or allocator obligation remains.

## Findings

### `DOC-1` — adjacent proof is materially incomplete

**Implementation: PROVED; proof artifact: deficient.** The existing comment says only that the `None` case returned. It omits the exact `is_none` proposition, the callee's UB condition, and the returned-value postcondition. A proof-grade replacement is:

```rust
// SAFETY: By AXIOM-OPT for this supported release, `is_none` reports `None`.
// Reaching here therefore means `value` is not `None`, satisfying
// `unwrap_unchecked`; that operation returns the contained byte.
```

No UB witness or defined postcondition refutation is established. Repair is documentation-only; re-audit the local proof if code or cited contracts change.

### `POLICY-1` — exact support identity unresolved

**Status: UNPROVED configuration-policy proposition, not an implementation defect.** The smallest missing fact is an authorized precedence, supersession, or reconciliation rule between Scarlet and Indigo. Publish one to define the exact supported set. Re-audit code only if the resolution admits configurations outside `D`; otherwise revisit the policy statement and containment proof.

## Residual scope and triggers

Configurations outside the three stated releases/targets and binary/backend correctness are excluded. Both-policy-unsupported but source-admitted configurations are not claimed supported, although the one within the stated axes is covered by `D`. Re-audit on source/manifest or public-contract changes; support-policy resolution/expansion; Cargo mapping/TCB disposition changes; Rust-document changes; or any new generated code, dependency, target, feature, or unsafe surface. Independent review was not performed.
