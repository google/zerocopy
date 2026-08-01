# Source-only unsafe-code audit

## Claim and verdict

**Snapshot.** The complete supplied target: `Cargo.toml`, `src/lib.rs`, both policy files, `TCB.md`, and `REQUEST.md`. It is a `no_std`, edition-2021 library with no dependencies, build script, generated code, macros exported by the crate, or prior audit. Review date: 2026-08-01. No build, execution, expansion, or test evidence was used.

Let `V={1.84.0,1.85.0,1.86.0}`, `T={X,A,W}` as defined by the policies, and let `f,h` be the two feature states. Define the **conservative audit domain**, not a newly selected support policy:

`C = V × T × {f=false,true} × {h=false,true} × all Cargo profiles × both debug-assertion states`, restricted by `!(f && t=W)`.

`C` contains the union of Scarlet and Indigo. It additionally contains source-admitted cases neither policy promises (notably `(1.84.0,A,f=true,h=false)`), so proving `C` avoids choosing between the conflicting commitments.

- **Source-level Rust soundness: PROVED** for every library artifact in `C` and every well-typed safe call to `value_or_zero`, relative to the TCB below.
- **Documented postcondition: PROVED** throughout `C`: `Some(b)` returns `b`; `None` returns `0`.
- **Combined mandatory result: PROVED** for every configuration supported by Scarlet **or** Indigo. Which policy is authoritative remains unresolved, but does not limit this theorem because both are subsets of `C`.
- `f && t=W` is effectively rejected before an artifact is produced and is expressly unsupported by both policies. No verdict is asserted for a nonexistent library artifact.
- No compiler-backend, binary, deployment, or future-Rust claim is made.

## Boundary, configuration, and invariant coverage

The sole crate-defined public surface is safe `pub fn value_or_zero(Option<u8>) -> u8`. Its two definitions are selected exclusively by `f`; there are no public fields/types, unsafe APIs/traits/impls, callbacks, FFI, concurrency, allocators, or destruction invariants. The only unsafe operation is the turbo definition's `Option::unwrap_unchecked` call.

For each version, the Reference says a false `cfg` predicate removes the attributed thing; the true case removes the attribute. Its predicate rules give the ordinary `all`/`not` evaluation used here ([1.84](https://doc.rust-lang.org/1.84.0/reference/conditional-compilation.html#the-cfg-attribute), [1.85](https://doc.rust-lang.org/1.85.0/reference/conditional-compilation.html#the-cfg-attribute), [1.86](https://doc.rust-lang.org/1.86.0/reference/conditional-compilation.html#the-cfg-attribute)). With accepted `BUILD-MAP-C`, exactly one function body remains: non-turbo when `f=false`, turbo when `f=true`. When `f && t=W`, the `compile_error!` item remains; each matched standard-library page says it “Causes compilation to fail with the given error message when encountered” ([1.84](https://doc.rust-lang.org/1.84.0/std/macro.compile_error.html), [1.85](https://doc.rust-lang.org/1.85.0/std/macro.compile_error.html), [1.86](https://doc.rust-lang.org/1.86.0/std/macro.compile_error.html)). Thus all policy-excluded wasm-turbo combinations are rejected.

`h`, profile, and debug assertions select no source and affect no arithmetic, panic, layout, or unsafe premise. Target affects only the rejection above. Consequently the body proofs are parametric over those axes and exhaustive over `C`.

**INV-SOME.** In the turbo body, on reaching `unwrap_unchecked`, the unchanged local `value` is not `None`. Its owner is that function activation; `is_none` establishes the branch fact through a shared borrow, the early return discharges the `None` case, and `unwrap_unchecked` immediately consumes the fact.

## Obligation ledger and proofs

| ID | Obligation and derivation | Domain | Status |
|---|---|---|---|
| CFG-1 | Exclusive bodies and wasm rejection, derived above from version-matched cfg/compile-error rules plus `BUILD-MAP-C`. | `C` and rejected `f,W` cases | PROVED |
| SAFE-1 | With `f=false`, `unwrap_or(0)` is safe and its documented behavior returns the contained `Some` value or the supplied default. | all non-turbo `C` | PROVED |
| UNSAFE-1 | With `f=true`, `is_none()==true` returns `0`. Otherwise, `INV-SOME` holds. Version-matched docs state “Returns `true` if the option is a `None` value” and “Calling this method on `None` is undefined behavior”; contraposition of the first discharges the second operation's sole safety condition. `unwrap_unchecked` then returns the contained `Some` byte. | turbo `C` (therefore only `X,A`) | PROVED |
| POST-1 | `None` reaches `0`; `Some(b)` reaches `b`, by `unwrap_or` or the checked turbo partition. These cases exhaust `Option<u8>`. | all `C` | PROVED |

Version-matched Option contracts (including the `unwrap_or` and `unwrap_unchecked` result clauses): [1.84 `is_none`](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.is_none), [`unwrap_unchecked`](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_unchecked), [`unwrap_or`](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_or); [1.85 `is_none`](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.is_none), [`unwrap_unchecked`](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.unwrap_unchecked), [`unwrap_or`](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.unwrap_or); [1.86 `is_none`](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.is_none), [`unwrap_unchecked`](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.unwrap_unchecked), [`unwrap_or`](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.unwrap_or).

## TCB audit log

**TCB identity:** supplied `TCB.md` plus the versioned authoritative axioms listed here.

| ID/category | Exact admitted proposition; scope; disposition | Consumer / trigger |
|---|---|---|
| `BUILD-MAP-C` / accepted build-tool premise | Only the exact Cargo-to-`feature` and target-to-`target_arch` mappings stated in `TCB.md`, for bundled 1.84/1.85/1.86 Cargo and the supplied manifest/source. **It admits no Rust semantics, branch correctness, other-version compatibility, or backend correctness.** | CFG-1; every trigger listed in `TCB.md` |
| `AXIOM-OPT-{84,85,86}` / Rust std | Exact method propositions on the nine version-matched Option links above. Verified, authoritative. | SAFE-1, UNSAFE-1, POST-1; Rust version/docs change |
| `AXIOM-CFG-{84,85,86}` / Rust Reference+std | Exact cfg effects/predicate semantics and `compile_error!` effect on the six version-matched links above. Verified, authoritative. | CFG-1; Rust version/docs or source cfg change |

There are no dependency, implementation, external-specification, environment, probabilistic, or tool-result premises. `BUILD-MAP-C` is applied only to its authorized consumers. No rejected or pending premise is consumed.

## Finding DOC-1 — local proof comment is deficient

**Implementation:** PROVED; **proof artifact:** deficient. The comment says the `None` case returned and concludes `Some`, but omits the material links: `is_none`'s result contract, preservation of `value` across its shared borrow, the exact `unwrap_unchecked` safety clause, and its consumed result guarantee. No UB witness or defined postcondition refutation exists.

Proposed adjacent replacement:

```rust
// SAFETY: `is_none` returns true for `None`; that branch returned.
// It only shared-borrowed `value`, so this unchanged value is not `None`.
// This satisfies `unwrap_unchecked`'s safety condition; it returns the
// contained `Some` byte, preserving this function's postcondition.
```

Minimum resolution is documentation-only; changing behavior or contracts would require a fresh audit.

## Residual scope and re-audit triggers

The unresolved policy precedence is residual governance scope, not uncovered soundness scope. Re-audit on any source/manifest/policy/TCB change; expansion of versions, targets, features, profiles with code-affecting behavior, or accepted configurations; material changes to cited Rust documentation; or addition of dependencies, generated code, FFI, concurrency, or other unsafe operations. Every in-scope operation, safe surface, configuration class, mandatory postcondition, citation, and consumed TCB entry has a disposition; no conclusion relies on testing or absence of a counterexample.
