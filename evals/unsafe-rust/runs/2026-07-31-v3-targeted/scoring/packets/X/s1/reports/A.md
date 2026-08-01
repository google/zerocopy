# Unsafe Rust source audit: `cross-axis-target` 0.1.0

## Claim, scope, and verdicts

Audit date/cutoff: 2026-08-01. The audited snapshot is exactly the supplied `Cargo.toml`, `build.rs`, `BUILD.md`, `SUPPORT.md`, `TCB.md`, and `src/lib.rs`. No build, execution, test, expansion, or implementation/backend claim is used. The source-level theorem quantifies over every well-typed safe use of the complete crate under Rust/Cargo/stdlib 1.85.1 and every supported configuration below, relative only to TCB revision `BUILD-MAP-X` and the cited Rust 1.85.1 semantics.

| Claim | Verdict | Certificate |
|---|---|---|
| Freedom from Rust UB over the complete supported domain | **UNSOUND** | `F-UB-1`: a valid safe `lane_id(0)` call in a supported reachable configuration executes `new_unchecked(0)`, which its exact std contract declares UB. |
| The documented behavior “Panics when `value` is zero” over the complete supported domain | **UNPROVED** | It is proved on the non-defective supported region. In the defective region the available zero-input witness contains UB, so it cannot certify `CONTRACT-BROKEN`; no independent UB-free refutation was established. |
| Both claims on supported configurations other than `aarch64 + burst + arena` | **PROVED** | Case proof `P-GOOD` and closure below. |

Combined mandatory result: **UNSOUND** for soundness and **UNPROVED** for the zero-input panic guarantee; therefore the complete-crate claim is not `PROVED`.

## Exact domain and configuration closure

Let `T` range over `{x86_64-unknown-linux-gnu, aarch64-unknown-linux-gnu, wasm32-unknown-unknown}`, `B` over both `burst` states, `A` over `{system, arena}`, `P` over every Cargo profile, and `D` over both debug-assertion states. For successful build-script stdout writes,

`Required = Rust/Cargo/stdlib 1.85.1 ∧ T in the listed set ∧ B∈{off,on} ∧ A∈{system,arena} ∧ P arbitrary ∧ D∈{off,on} ∧ ¬(T=wasm32-unknown-unknown ∧ A=arena)`.

This is an exact normalization of `SUPPORT.md`; `Cargo.toml` fixes the package, edition 2021, toolchain floor/equality supplied by policy, library path, build script, and the two feature states. `BUILD.md` and `build.rs` map an absent variable or `system` to `A=system`, and `arena` to `A=arena`. `std::env::var` returns the process value, `NotPresent` for an unset variable, and `NotUnicode` for a non-Unicode value ([Rust 1.85.1 `env::var`](https://doc.rust-lang.org/1.85.1/std/env/fn.var.html)). Local match arms emit exactly one accepted selector or panic. `BUILD-MAP-X` then admits only that Cargo 1.85.1 passes each emitted selector, maps the feature and the three triples to their named cfgs, reruns as stated, and produces no library compilation after an unsuccessful script. This does not trust what the script emits.

The source cfgs form the exhaustive partition

`BAD = Required ∧ T=aarch64-unknown-linux-gnu ∧ B=on ∧ A=arena`

and `GOOD = Required ∧ ¬BAD`. Profiles and debug assertions do not select or alter either implementation, so both proofs are parametric over `P` and `D`. For `GOOD`, the specialized block is absent and the other block is present. Primitive `u8` equality decides `value == 0` ([comparison operators](https://doc.rust-lang.org/1.85.1/reference/expressions/operator-expr.html#comparison-operators)); when true, Rust executes the consequent block ([`if` semantics](https://doc.rust-lang.org/1.85.1/reference/expressions/if-expr.html)), whose `panic!` “Panics the current thread” ([`panic!`](https://doc.rust-lang.org/1.85.1/std/macro.panic.html)). When false, reaching the unsafe call proves `value != 0`. Thus `P-GOOD` covers every `u8`, target, feature, allocator, profile, and assertion state in `GOOD`; `GOOD ⊆ Covered(P-GOOD)`.

Rejected cases are outside `Required` and do not conceal UB:

- `wasm32-unknown-unknown + arena`, with either feature state, selects the unconditional-in-that-case `compile_error!` before a library artifact can be produced. This exactly enforces the sole support-policy exclusion.
- Any Unicode allocator value other than `system` or `arena`, and any non-Unicode value, reaches `panic!` in `build.rs`; by `BUILD-MAP-X`, an unsuccessful script yields no library compilation. A missing value is accepted as `system`.
- Build-script stdout failure is explicitly excluded by `BUILD-MAP-X` and also yields no compilation. Manually invented missing or simultaneous allocator cfgs are outside `BUILD.md`'s theorem; the first two `compile_error!` guards reject them nonetheless.

## Boundary, invariants, and obligation ledger

The complete downstream safe API surface is the public free function `lane_id(u8) -> NonZeroU8`. There are no crate-owned public fields, constructors, traits/impls, callbacks, statics, FFI, reexports, hidden APIs, or exported/generated macros. `burst` and the allocator environment interface are configuration surfaces. The only unsafe operations are the two cfg-complementary `NonZeroU8::new_unchecked(value)` calls.

There is no enforceable abstraction invariant establishing that arguments are nonzero. The sentence “Burst-mode lane identifiers are never zero” is merely a false assertion about an unconstrained safe argument. On `GOOD`, a per-call dominating check establishes the needed fact; it is not a type-wide invariant.

| ID | Obligation and domain | Proof/status |
|---|---|---|
| O-CFG | Recover accepted selectors, cfg reachability, and rejection | Source control flow plus `BUILD-MAP-X`; **PROVED** as above. |
| O-NZ-GOOD | `new_unchecked(value)` requires `value != 0`, on `GOOD` | Zero panics; false branch implies nonzero; **PROVED**. |
| O-NZ-BAD | Same requirement on `BAD` | False for safe input zero; **UNSOUND**, `F-UB-1`. |
| O-PANIC | Zero input panics | **PROVED** on `GOOD`; **UNPROVED** on `BAD` because the execution has UB. |
| O-CLOSE | Aggregate supported-domain coverage | `GOOD` and `BAD` exhaust `Required`; the existential certificate on `BAD` establishes the strongest full-domain verdict. |

## F-UB-1 — supported safe call violates `NonZero`'s contract

- **Status/severity:** **UNSOUND**, implementation defect; adjacent proof comment deficient.
- **Valid in-scope use:** Choose Rust/Cargo 1.85.1, target `aarch64-unknown-linux-gnu`, `burst` enabled, `FIXTURE_ALLOCATOR=arena`, any supported profile/assertion state, and call public safe `lane_id(0)`. `SUPPORT.md` includes this configuration (only wasm+arena is excluded); safe callers have no precondition.
- **Reachability:** `build.rs` emits `fixture_allocator="arena"`; `BUILD-MAP-X` supplies that cfg, `feature="burst"`, and `target_arch="aarch64"`. Therefore the first cfg block is compiled and its unconditional return executes `NonZeroU8::new_unchecked(value)` with zero; the checked complementary block is absent.
- **False safety proposition and UB consequence:** Rust 1.85.1 documents that `new_unchecked` creates without checking, that a zero value “results in undefined behavior,” and requires “The value must not be zero” ([exact `NonZero::new_unchecked` contract](https://doc.rust-lang.org/1.85.1/std/num/struct.NonZero.html#method.new_unchecked)). The reached argument is exactly zero. This closes every existential `UNSOUND` link.
- **Postcondition classification:** this same execution cannot prove `CONTRACT-BROKEN`, because it is not UB-free as a whole.
- **Minimum repair:** perform the zero check in every configuration, then retain only the checked unsafe call (or use safe `NonZeroU8::new` and handle `None`). Suitable adjacent proof: `The preceding value == 0 branch panics, so reaching this call proves value != 0, exactly satisfying new_unchecked's safety requirement.` Re-audit all cfg cases after the change.

## TCB audit log and residual scope

`BUILD-MAP-X` is **accepted** exactly as written in supplied `TCB.md`: Cargo 1.85.1, this manifest/build script/environment/library, all supported profiles, successful-write scope, selector/feature/target propagation, rerun behavior, and halt-on-script-failure. Consumers are only O-CFG and reachability in `F-UB-1`. It admits no build-script source correctness, emitted string, Rust semantics, backend, or binary proposition; none was widened. Re-audit triggers are exactly its listed identity/interface/source/target/disposition changes.

The Rust axioms consumed are the versioned pages cited above, especially the exact `new_unchecked` precondition and UB consequence. There are no third-party dependencies, tool-derived facts, prior reports, tests, external specifications, deployment assumptions, or binary claims. Unsupported/manual cfgs and failed build attempts have only the rejection accounting stated above. Re-audit on any supplied source, support/build contract, Rust/Cargo/stdlib version, cfg/feature/target/profile domain, cited semantic contract, or TCB disposition change.

Auditor: source-review agent. Independent review: not performed.
