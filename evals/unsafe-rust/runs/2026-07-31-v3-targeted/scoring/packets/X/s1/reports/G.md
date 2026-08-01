# Unsafe Rust Audit: `cross-axis-target` 0.1.0

## Claim and verdict

This is a source-level audit of the complete supplied crate (`Cargo.toml`, `build.rs`, `src/lib.rs`, `BUILD.md`, `SUPPORT.md`, and `TCB.md`) under Rust/Cargo/stdlib 1.85.1 and the Rust abstract semantics. For every well-typed safe call to `lane_id` in every supported configuration, the soundness claim is absence of Rust undefined behavior; documented behavior is also in scope.

**Overall soundness: UNSOUND (F-1).** The supported region `B = {target=aarch64-unknown-linux-gnu, feature burst enabled, allocator=arena}` is `UNSOUND` in every Cargo profile and either debug-assertion state. The supported complement is `PROVED` relative to TCB-1 and the Rust axioms below.

**Documented behavior:** `PROVED` on the supported complement. In `B`, the documented “Panics when value is zero” postcondition is `UNPROVED`, not `CONTRACT-BROKEN`: the only established zero-input witness contains UB, so it cannot establish a UB-free behavioral refutation. For nonzero inputs in `B`, construction is proved.

**Combined mandatory result: UNSOUND; zero-input panic postcondition UNPROVED in B.** No binary/backend claim is made.

## Snapshot, supported set, and configuration closure

`Required(t,f,a,p,d)` means: the supplied source; edition 2021; Rust, Cargo, and std 1.85.1; `t` in `{x86_64-unknown-linux-gnu, aarch64-unknown-linux-gnu, wasm32-unknown-unknown}`; `f` is either state of `burst`; `a` is `system` or `arena` selected through `FIXTURE_ALLOCATOR` and Cargo/build.rs; `p` is any Cargo profile; and `d` is either debug-assertion state; except `(t=wasm32-unknown-unknown, a=arena)`. `SUPPORT.md` and `BUILD.md` control this predicate. No dependencies or generated source exist; the build script generates only cfg options.

Local build-script dataflow maps an absent selector to `system`, accepts exactly `system|arena`, emits one matching `fixture_allocator` cfg, and panics for non-Unicode or other values. TCB-1 supplies only Cargo’s execution/directive, feature, and target-cfg mappings and the rule that unsuccessful build scripts produce no library compilation. Thus invalid selectors are effectively rejected. A stdout infrastructure failure likewise yields no library compilation, but TCB.md expressly says it is not a successful policy rejection.

For successful accepted builds, the source predicates form the exhaustive partition `B` versus `not(B)`. Profiles and debug assertions affect no source selection or proof fact. The wasm32/arena pair activates `compile_error!`, which [causes compilation to fail](https://doc.rust-lang.org/1.85.1/std/macro.compile_error.html); it is effectively rejected for both feature states, every profile, and either debug-assertion state. The earlier selector checks are inactive under TCB-1’s exactly-one mapping but reject absent, unknown, or simultaneous manually injected selector cfgs. Such direct-rustc builds, all other targets/toolchains, and invented cfgs are outside `Required`.

## Boundary and invariant inventory

The sole downstream surface is safe public `lane_id(u8) -> NonZeroU8`. There are no public fields, unsafe APIs/traits/impls, callbacks, macros, hidden items, mutable state, FFI, concurrency, allocators actually called, or destruction invariants. The only invariant is local: **INV-NZ:** immediately before either `NonZeroU8::new_unchecked(value)`, `value != 0` must hold. Std’s exact contract says [“The value must not be zero” and zero causes UB](https://doc.rust-lang.org/1.85.1/std/num/struct.NonZero.html#method.new_unchecked).

## Obligation ledger and proofs

| ID | Scope | Obligation and derivation | Status |
|---|---|---|---|
| O-1 | build/config | Accepted environment values emit exactly one allocator selector; TCB-1 transfers it and the feature/target cfgs. Invalid environment values panic and TCB-1 prevents library compilation. | PROVED |
| O-2 | excluded wasm32/arena | Accepted `arena` plus wasm32 target makes the cfg predicate true; `#[cfg]` includes the `compile_error!`, so no library artifact is produced. | PROVED |
| O-3 | `not(B)`, `lane_id(0)` | For primitive `u8`, `==` means equality ([Reference](https://doc.rust-lang.org/1.85.1/reference/expressions/operator-expr.html#comparison-operators)). The true consequent executes and later code is skipped ([if expressions](https://doc.rust-lang.org/1.85.1/reference/expressions/if-expr.html)); `panic!` [panics the current thread](https://doc.rust-lang.org/1.85.1/std/macro.panic.html). No unsafe call is reached. | PROVED |
| O-4 | `not(B)`, `lane_id(value != 0)` | The zero branch is skipped; the dominating comparison establishes INV-NZ, satisfying `new_unchecked`. The return is a valid `NonZeroU8` constructed from `value`. | PROVED |
| O-5 | `B`, nonzero input | The cfg-selected early branch calls `new_unchecked(value)`; the call-site input fact satisfies INV-NZ. | PROVED |
| O-6 | `B`, all safe inputs | The same branch performs no check. Safe callers may pass every `u8`, including zero; INV-NZ is not established. | UNSOUND (F-1) |

The fallback safety comment is a correct concise local proof: reaching its call after the zero branch entails nonzero. The special-branch comment is not a proof; neither the type nor any constructor/boundary establishes its assertion.

## Finding F-1 — supported safe call violates `new_unchecked`

- **Status/severity:** critical, `UNSOUND`; proof artifact deficient.
- **Configuration:** `aarch64-unknown-linux-gnu`, `burst`, `arena`, every supported profile/debug-assertion state.
- **Valid witness:** choose `FIXTURE_ALLOCATOR=arena`, enable `burst`, select the supported aarch64 target, then safe code calls `lane_id(0)`. TCB-1 and local build logic select the early cfg block. It executes `unsafe { NonZeroU8::new_unchecked(0) }`; the version-matched std contract explicitly classifies zero as UB.
- **Defect:** “Burst-mode lane identifiers are never zero” reverses no producer contract and is false for the unconstrained safe parameter. A safe API cannot impose this hidden caller obligation.
- **Postcondition classification:** this UB-containing execution proves soundness `UNSOUND` but does not prove the panic guarantee `CONTRACT-BROKEN`; that guarantee remains `UNPROVED` in `B`.
- **Minimum repair:** remove the special path and use the checked constructor, e.g. `NonZeroU8::new(value).expect("lane identifier must be nonzero")`, or add the same unconditional zero check before the unsafe call. After a check, suitable proof text is: “The dominating `value == 0` branch panics; therefore reaching this call establishes `value != 0`, exactly `new_unchecked`’s precondition.” Re-audit the changed snapshot and all cfg regions. This restores the published safe contract; it does not legitimize the old hidden obligation.

## TCB audit log

| ID | Category/disposition | Exact proposition and scope | Consumers / trigger |
|---|---|---|---|
| TCB-1 (`BUILD-MAP-X`) | IMPLEMENTATION, human-accepted | Exactly the Cargo 1.85.1 directive/rerun, unsuccessful-script, `burst`, and three named target-cfg mappings stated in supplied `TCB.md`; successful stdout scope only. It does **not** trust local source correctness, emitted string choice, Rust semantics, backend, or binary. | O-1, O-2, O-6; re-audit on any identity/interface/source/cfg/target/disposition change listed there. |
| AXIOM-NZ | Rust std 1.85.1, authoritative | `NonZero::new_unchecked(n)` requires nonzero and zero causes UB. | O-4–O-6; documentation/toolchain change. |
| AXIOM-CONTROL | Rust Reference 1.85.1, authoritative | Primitive equality and `if` control flow used above; cfg selects attributed source by its predicate. | O-2–O-4, O-6; Reference/toolchain change. |
| AXIOM-PANIC | Rust std 1.85.1, authoritative | Invoked `panic!` panics the current thread. | O-3; documentation/toolchain change. |

No premise widens TCB-1. No selected safe/unsafe dependency or tool-derived evidence is consumed. No tests, builds, execution, expansion, or prior audit were used.

## Residual scope and re-audit triggers

Excluded are unsupported configurations, direct rustc/invented cfg builds, compiler/backend correctness, binaries, deployment behavior, and infrastructure-failed attempts. There is no authoritative-documentation or skill-guidance gap material to the verdict. Re-audit on any source, contract, support policy, Cargo/Rust/std, build environment/interface, target/feature/allocator set, cfg generation, or TCB disposition change.

**Audit date:** 2026-08-01. **Independent review:** not performed.
