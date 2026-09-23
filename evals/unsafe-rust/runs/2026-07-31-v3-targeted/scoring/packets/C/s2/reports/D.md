# Unsafe Rust source audit

## Claim and verdict

**Soundness: PROVED. Documented behavior: PROVED. Combined mandatory result: PROVED.** For the exact supplied crate source, every well-typed safe call to the configuration-selected `value_or_zero` is free from Rust undefined behavior and returns the contained byte for `Some(byte)` and `0` for `None`, for every configuration supported by **either** current policy, relative only to the TCB stated below.

This is a source-level Rust-abstract-semantics result, not a compiler/backend or binary-correctness claim. It does not choose between Scarlet and Indigo or declare their union to be project policy. Rather, one proof covers the conservative union, so each candidate policy's complete domain is covered despite the unresolved governance conflict.

## Snapshot, scope, and surfaces

Audited material is the supplied `Cargo.toml`, `src/lib.rs`, both policy files, and `TCB.md`; package `conflicting-domain-target` 0.1.0, edition 2021, Rust/standard-library versions exactly 1.84.0, 1.85.0, and 1.86.0. There are no dependencies, build scripts, supplied generated artifacts, FFI, assembly, concurrency, allocator code, invariant-bearing representation, unsafe declarations/traits/impls/fields, callbacks, or hidden/macro-generated public APIs. No prior audit, expansion, build, test, or tool result was used.

The complete crate-owned API surface is one safe public free function, represented by two mutually exclusive `cfg(feature = "turbo")` definitions with the same signature and documented result. The complete unsafe surface is the turbo definition's single call to `Option::unwrap_unchecked`. The only other macro site is the configuration-rejection `compile_error!`.

## Configuration closure

Let `V={1.84.0,1.85.0,1.86.0}`, targets `X`, `A`, and `W` have the policy meanings, and `f`/`h` denote `turbo`/`hardened`. Without resolving policy precedence, the conservative candidate domain is `U = Indigo ∪ Scarlet`, equivalently (under the common version/target universe):

```text
!f or (f and t = X) or (f and t = A and (h or v >= 1.85.0))
```

Both `h` states, all policy-supported Cargo profiles, and both debug-assertion states are included. `h`, profile, and debug assertions do not occur in either function body, so the proofs are parametric over them. Target and version affect no body; version-matched Option contracts below cover each version. The cases `!f` and `f` exhaust `U`.

The versioned References define `all` by conjunction and say `cfg` “conditionally includes the thing it is attached to based on a configuration predicate”: [1.84 predicate](https://doc.rust-lang.org/1.84.0/reference/conditional-compilation.html#conditional-compilation), [1.84 attribute](https://doc.rust-lang.org/1.84.0/reference/conditional-compilation.html#the-cfg-attribute); [1.85 predicate](https://doc.rust-lang.org/1.85.0/reference/conditional-compilation.html#conditional-compilation), [1.85 attribute](https://doc.rust-lang.org/1.85.0/reference/conditional-compilation.html#the-cfg-attribute); [1.86 predicate](https://doc.rust-lang.org/1.86.0/reference/conditional-compilation.html#conditional-compilation), [1.86 attribute](https://doc.rust-lang.org/1.86.0/reference/conditional-compilation.html#the-cfg-attribute). Each version's `compile_error!` contract says it causes compilation to fail with the given message when encountered: [1.84](https://doc.rust-lang.org/1.84.0/std/macro.compile_error.html), [1.85](https://doc.rust-lang.org/1.85.0/std/macro.compile_error.html), [1.86](https://doc.rust-lang.org/1.86.0/std/macro.compile_error.html).

Therefore, using `BUILD-MAP-C`, `f && t=W` includes and encounters `compile_error!`, so it produces no shippable library artifact. Both policies already expressly exclude that region. When `f` is false exactly the non-turbo definition is included; when true exactly the turbo definition is included.

## Authoritative Option premises

For each exact version, the standard-library page says `is_none` “Returns `true` if the option is a `None` value”; `unwrap_unchecked` returns the contained `Some` value and its Safety section says calling it on `None` is undefined behavior; `unwrap_or` returns the contained value or supplied default: [1.84 `is_none`](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.is_none), [`unwrap_unchecked`](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_unchecked), [`unwrap_or`](https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_or); [1.85 `is_none`](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.is_none), [`unwrap_unchecked`](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.unwrap_unchecked), [`unwrap_or`](https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.unwrap_or); [1.86 `is_none`](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.is_none), [`unwrap_unchecked`](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.unwrap_unchecked), [`unwrap_or`](https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.unwrap_or).

## Obligation ledger and derivations

- **O-NORMAL (all `U` with `!f`): PROVED.** `unwrap_or(0)` is safe and, by its exact version's contract, returns the byte for `Some(byte)` and `0` for `None`. Thus both soundness and the function's documented result hold.
- **O-TURBO-NONE (all `U` with `f`, input `None`): PROVED.** `is_none()` returns true, so the dominating branch returns `0`; the unsafe call is not executed.
- **O-TURBO-SOME (all `U` with `f`, input `Some(byte)`): PROVED.** Reaching the unsafe call means `is_none()` returned false. By contraposition of its `None => true` contract, `value` is not `None`; because `Option` has only `None` and `Some`, it is `Some(byte)`. `is_none` only immutably borrows this owned local, and no operation intervenes, so the fact persists. This discharges `unwrap_unchecked`'s exact safety obligation; its postcondition yields `byte`.
- **O-COVERAGE: PROVED.** `f` partitions `U`; the two `Option` variants partition every input; the four cases above cover all configurations and safe inputs. Target, `h`, profile, and debug-assertion axes do not alter the selected body or derivation.

The adjacent `SAFETY` comment identifies the dominating `None` exit and exact resulting `Some` fact required by `unwrap_unchecked`; for this immediate control-flow/type derivation it is adequate. No caller-side safety condition is hidden.

## TCB audit log

**The only accepted non-Rust premise consumed is `BUILD-MAP-C` from the supplied `TCB.md`.** It admits, only for bundled Cargo corresponding exactly to Rust 1.84.0/1.85.0/1.86.0, the stated mapping from enabled `turbo`/`hardened` features to their `cfg` predicates and from the three exact target triples to `target_arch`. It is consumed only by branch reachability and effective rejection. It admits no Rust semantics, branch correctness, compatibility, backend, or binary proposition. Human disposition: accepted. Re-audit on any listed Cargo/toolchain identity, feature, target, manifest, source-`cfg`, or disposition change.

The versioned Reference/std propositions cited above are authoritative Rust axioms, not extra implementation assumptions. No safe/unsafe dependency, compatibility, tool, external, deployment, or probabilistic premise is consumed.

## Findings, residual scope, and triggers

No implementation, soundness, postcondition, proof-documentation, Rust-documentation, or skill-guidance defect was established. The sole governance issue is that no unique exact project support predicate can be reported until Scarlet/Indigo precedence or supersession is authorized; it does not block the proved conservative-union theorem.

Excluded from the verdict: toolchains or standard libraries outside `V`, targets outside `{X,A,W}`, custom build-tool mappings, configurations outside either policy, compiler/backend/binary correctness, and the rejected `f && W` region (which emits no library). Re-audit on source/manifest changes, policy resolution or scope changes, any consumed Rust-documentation semantic change, or any `BUILD-MAP-C` trigger.

All in-scope unsafe, safe-boundary, behavior, configuration, citation, and TCB obligations have the dispositions above; no tests substitute for proof.
