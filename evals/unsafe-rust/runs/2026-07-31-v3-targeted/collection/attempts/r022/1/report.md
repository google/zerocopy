# Unsafe Rust Audit: `cross-axis-target` 0.1.0

## Claims and verdicts

**Snapshot.** Complete supplied crate: `Cargo.toml`, `build.rs`, `src/lib.rs`, `BUILD.md`, `SUPPORT.md`, and `TCB.md` (respective SHA-256 prefixes `4668f1a3`, `d7a8e7c5`, `045942a4`, `66c7a294`, `1ca6428c`, `ff6b0c8d`). Review date: 2026-08-01. No generated source, dependencies, prior audit, execution, expansion, build, or test was used. Skill identity: supplied unversioned `unsafe-rust` package.

Let `S` be this source under Cargo/Rust/stdlib 1.85.1, edition 2021, on `x86_64-unknown-linux-gnu`, `aarch64-unknown-linux-gnu`, or `wasm32-unknown-unknown`; `burst` either off or on; allocator `system` or `arena` selected through `BUILD.md`; excluding `wasm32 + arena`; in every Cargo profile and either debug-assertion state. This predicate is fixed by `Cargo.toml`, `BUILD.md`, `SUPPORT.md`, and accepted TCB entry `BUILD-MAP-X`; they do not conflict.

The source-level soundness claim is: every well-typed safe use of the sole public API, and every successful supported build path, is free of Rust UB throughout `S`, relative only to the TCB below.

- **Whole-`S` soundness: UNSOUND (F-01).**
- **Region `B = aarch64 + burst + arena`: UNSOUND** for every profile/debug-assertion state.
- **Region `G = S ∖ B`: PROVED** relative to the stated TCB.
- **Documented behavior:** PROVED on `G`; UNPROVED on `B` for “panics when `value` is zero.” This is not `CONTRACT-BROKEN`: the available zero witness contains UB and therefore is not a defined refutation.
- **Combined mandatory result:** `UNSOUND` and documented zero behavior `UNPROVED` (F-01). No conditional application claim.

## Boundary, contracts, and obligations

The complete language-reachable crate surface is the safe free function `lane_id(u8) -> NonZeroU8`. There are no public fields, custom constructors/types, methods, traits/impls, statics, callbacks, macros/generated APIs, hidden items, FFI, or reexports. The build script is also in scope. The two source occurrences of `new_unchecked` are cfg-exclusive unsafe consumers. There is no persistent custom invariant-bearing representation.

`INV-NZ(v)` is the local proposition `v != 0`, required immediately at either `NonZeroU8::new_unchecked(v)` call. Rust 1.85.1 documents both that zero “results in undefined behavior” and, under Safety, “[The value must not be zero.](https://doc.rust-lang.org/1.85.1/std/num/struct.NonZero.html#method.new_unchecked)”

| ID | Location / exact obligation | Domain and derivation | Status |
|---|---|---|---|
| O-01 | `lib.rs:44`: establish `INV-NZ(value)` | On `G`, the cfg-complement branch executes. Primitive `value == 0` is equality; if true, `panic!` prevents reaching line 44; reaching it therefore implies nonzero. The unsafe call then satisfies its exact precondition and constructs the returned nonzero from `value`. | PROVED |
| O-02 | `lib.rs:31`: establish `INV-NZ(value)` | This branch is exactly `B`. It performs no check. A safe caller may supply every `u8`, including zero. | UNSOUND |
| O-03 | `lane_id(0)` must panic | On `G`, the dominating branch panics. On `B`, O-02 reaches UB; that execution cannot prove or refute a defined postcondition. | PROVED on `G`; UNPROVED on `B` |
| O-04 | configuration/build closure and exclusions | Finite cfg partition plus `BUILD-MAP-X` and the source derivation below. Profiles/debug assertions are parametric: neither selects code or removes a check. | PROVED |

The existing line-30 comment, “Burst-mode lane identifiers are never zero,” is a false assertion, not a proof: `value` crosses a safe public boundary with no restriction. The line-43 comment is adequate because it names the dominating check and same value.

## F-01 — safe zero reaches `new_unchecked`

- **Affected theorem:** safe-library soundness and zero-panic behavior in `B`.
- **Valid UB witness:** use the supported target `aarch64-unknown-linux-gnu`, enable `burst`, select `arena`, choose any profile/debug-assertion state, and safely call `lane_id(0)`. `BUILD-MAP-X` establishes all three active cfg predicates. Lines 24–31 select the first block and call `new_unchecked(0)`. AX-NZ establishes UB. No caller obligation is permitted on this safe API.
- **Proof-artifact classification:** deficient and false. No invariant producer exists.
- **Defined postcondition refutation:** not established; the witness contains UB.
- **Minimum repair:** perform the zero check in all configurations, preferably `NonZeroU8::new(value).expect("lane identifier must be nonzero")`, or use the existing checked branch universally. If retaining unsafe, replacement proof text is: “`value == 0` panics above; reaching this call therefore establishes `value != 0`, the complete `new_unchecked` precondition.” Re-audit all configurations after repair. Removing the documented panic or adding a safe caller restriction would be a public contract change and would not repair soundness.

## Configuration and rejection closure

The relevant axes are exact toolchain/stdlib, three targets, two feature states, two allocator selectors, arbitrary Cargo profile, and debug assertions. There are ten supported target/feature/allocator cells. `B` is one cell; O-01 uniformly covers the other nine. No allocation implementation is used despite the selector names.

For the build interface, [`env::var`](https://doc.rust-lang.org/1.85.1/std/env/fn.var.html) partitions the input into a Unicode value, absent, or non-Unicode error. Absence creates the owned string `system`; [`as_str`](https://doc.rust-lang.org/1.85.1/std/string/struct.String.html#method.as_str), literal/or/wildcard match semantics, and formatting show that exactly `system` or `arena` emits one corresponding cfg line. Other Unicode values and non-Unicode input take `panic!`; stdout failure also cannot yield a library compilation under `BUILD-MAP-X`. The `rustc-check-cfg` line declares values but does not set them, exactly as `BUILD-MAP-X` records.

For accepted selectors, conditional-compilation semantics ([cfg](https://doc.rust-lang.org/1.85.1/reference/conditional-compilation.html#conditional-compilation), [cfg attribute](https://doc.rust-lang.org/1.85.1/reference/conditional-compilation.html#the-cfg-attribute)) give exhaustive complementary `lane_id` bodies. The project-rejected `wasm32 + arena` pair, for either feature/profile/assertion state, activates line 15 and [`compile_error!`](https://doc.rust-lang.org/1.85.1/std/macro.compile_error.html), so no library artifact is produced. Missing or simultaneous allocator cfgs likewise hit lines 3 or 9, but manual invented rustc cfgs are explicitly outside the theorem. A build-script stdout failure is an unsuccessful attempt, not a configuration.

## TCB audit log `TCB-cross-axis-2026-08-01`

Trust policy: only exact Rust 1.85.1 Reference/stdlib propositions and the already authorized `BUILD-MAP-X` may be consumed. Safe caller behavior is adversarial. No dependency, compiler-backend, binary, platform, probabilistic, or new implementation premise is admitted.

| ID / category | Exact consumed proposition; scope | Disposition / consumers / trigger |
|---|---|---|
| BUILD-MAP-X / OUT-OF-BAND build-tool premise | Exactly the Cargo/target-cfg/feature mappings, stdout-success qualification, and halt-on-unsuccessful-script proposition written in supplied `TCB.md`; all `S` build attempts. No claim about build-script source or emitted selector is imported. | Human-accepted; O-02/O-04; every trigger listed in that entry. |
| AX-NZ / AXIOM | Rust 1.85.1 `NonZero::new_unchecked(n)` requires nonzero and is UB for zero. | Verified authoritative text; O-01/O-02; Rust/docs/API change. |
| AX-FLOW / AXIOM | Rust 1.85.1 primitive equality, `if`, `match`, blocks, patterns, and `panic!` semantics used above. | Verified version-matched Reference/stdlib pages listed in the supplied allowlist; O-01/O-03/O-04; toolchain/docs change. |
| AX-CFG / AXIOM | Rust 1.85.1 cfg/cfg-attribute and `compile_error!` semantics used above. | Verified version-matched authority; O-04; toolchain/docs/cfg change. |
| AX-BUILD-SRC / AXIOM | Rust 1.85.1 `env::var`, string, formatting, `println!`, panic, and match behavior used only to derive this script’s selector/output partition. | Verified version-matched authority; O-04; source/toolchain/docs change. |

No entries are pending, rejected, expired, or widened from `TCB.md`; no tool-derived evidence exists.

## Residual scope, gaps, and triggers

Excluded are targets/toolchains outside `S`, direct rustc invocation/invented cfgs, backend or binary correctness, and rejected build attempts. No authoritative-documentation or skill-guidance gap blocked this result. Re-audit on any source/manifest/build/support/TCB change; Rust/Cargo/stdlib or cited-contract change; new target, feature, allocator, profile-sensitive code, generator, dependency, API, or unsafe site; or a change to `BUILD-MAP-X` disposition. Every in-scope obligation has a status; every supported cell is covered; the unsound verdict rests on a source proof, not testing or absence of counterexamples.
