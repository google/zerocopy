# Unsafe Rust audit: `cross-axis-target` supplied snapshot

## Claim and verdict

**Source-soundness claim.** For every well-typed safe use of the complete supplied crate under `Required` below, execution is free of Rust undefined behavior under Rust 1.85.1 abstract semantics, relative only to `BUILD-MAP-X` and the cited Rust axioms.

**Verdict: UNSOUND over the complete supported domain (F-1).** The supported region `aarch64-unknown-linux-gnu + burst + arena` admits the safe call `lane_id(0)`, which reaches an operation documented to have undefined behavior for zero. Soundness is `PROVED` for the complementary supported region, relative to the stated TCB.

**Documented behavior:** `UNPROVED` overall. The nonzero result behavior and the promised zero panic are proved in the complementary region. In the defective region, the only established zero execution contains UB, so it cannot witness `CONTRACT-BROKEN`; the promised panic remains `UNPROVED` there. Build-interface behavior and the required `wasm32 + arena` rejection are `PROVED` relative to `BUILD-MAP-X`.

**Combined mandatory result:** `UNSOUND` soundness / `UNPROVED` documented postconditions. No conditional application claim is requested.

## Snapshot and supported set

The artifact is exactly the supplied `Cargo.toml`, `build.rs`, `src/lib.rs`, `BUILD.md`, `SUPPORT.md`, `TCB.md`, and `REQUEST.md`; no VCS identity, lockfile, dependency, generated source file, or prior audit is supplied. Edition 2021 and Rust/Cargo/stdlib 1.85.1 apply. Audit cutoff: 2026-08-01. Skill identity: supplied unsafe-rust package snapshot. No build, expansion, execution, or test evidence was used.

`Required` is every Cargo build using the supplied manifest and build script, Rust/Cargo 1.85.1, target in `{x86_64-unknown-linux-gnu, aarch64-unknown-linux-gnu, wasm32-unknown-unknown}`, either `burst` state, allocator `system` or `arena`, every Cargo profile, and either debug-assertion state, except `wasm32-unknown-unknown + arena`. Allocator selection is only the `BUILD.md` interface: missing/`system` means `system`; `arena` means `arena`. Invented rustc cfgs and other targets/toolchains are outside the theorem.

Configuration partition is exhaustive: let `S = aarch64 + burst + arena`; all supported library builds are either `S` or `Required \\ S`. Profile and debug-assertion axes are irrelevant because neither controls source and no debug assertion is used.

The build script has no unsafe code. On successful stdout writes, its match maps only `system`/`arena` to one interpolated selector; missing input first becomes `system`; invalid Unicode or any other string panics. `BUILD-MAP-X` supplies only the exact Cargo/env/cfg mapping and the fact that script/write failure yields no library compilation. For an accepted selector, Cargo therefore supplies exactly one value. The first two `compile_error!` guards reject absent/both selectors defensively. `wasm32 + arena` selects the third guard and fails compilation, satisfying the mandated exclusion; invalid environment values fail earlier. Conditional source selection and compilation failure use the Rust 1.85.1 [`cfg`](https://doc.rust-lang.org/1.85.1/reference/conditional-compilation.html#conditional-compilation), [`cfg` attribute](https://doc.rust-lang.org/1.85.1/reference/conditional-compilation.html#the-cfg-attribute), and [`compile_error!`](https://doc.rust-lang.org/1.85.1/std/macro.compile_error.html) contracts.

## Boundary, invariants, and obligations

The sole downstream surface is safe public free function `lane_id(u8) -> NonZeroU8`. There are no public representation fields, traits/impls, exported macros, hidden items, callbacks, FFI, statics, or custom destruction. Its safety invariant is `NZ`: every normally returned `NonZeroU8` contains a nonzero input value. `lane_id` produces `NZ`; `NonZeroU8::new_unchecked` consumes the proposition `value != 0` and establishes the result.

| ID | Site/domain | Exact obligation | Derivation and status |
|---|---|---|---|
| O-1 | `lib.rs:31`, `S` | `value != 0` before `new_unchecked` | For nonzero inputs, immediate. For zero, no check, type restriction, or unsafe caller obligation exists. **UNSOUND** via F-1. |
| O-2 | `lib.rs:44`, `Required \\ S` | `value != 0` before `new_unchecked` | `value == 0` selects the diverging panic branch; normal reach therefore entails inequality. This discharges the exact callee precondition and establishes `NZ`. **PROVED** for both unwind/abort behavior because neither continues to line 44. |
| O-3 | safe `lane_id` surface | all safe inputs avoid UB | O-2 proves the complement; O-1 refutes `S`. **UNSOUND overall**. |
| O-4 | `# Panics` contract | every `value == 0` call panics | Proved in the complement. The `S` zero execution has UB, so no defined refutation is established and the regional/overall result is **UNPROVED**, not `CONTRACT-BROKEN`. |
| O-5 | build/support policy | admitted cfgs are exhaustive; rejected cases produce no library | Source partition above plus `BUILD-MAP-X`; `wasm32 + arena` reaches `compile_error!`. **PROVED**. |

The material Rust 1.85.1 axiom is [`NonZero::new_unchecked`](https://doc.rust-lang.org/1.85.1/std/num/struct.NonZero.html#method.new_unchecked): “This results in undefined behavior if the value is zero”; its Safety clause says “The value must not be zero.” Equality means `PartialEq::eq` ([comparison operators](https://doc.rust-lang.org/1.85.1/reference/expressions/operator-expr.html#comparison-operators)), and an [`if` expression](https://doc.rust-lang.org/1.85.1/reference/expressions/if-expr.html) executes the block selected by its Boolean condition. These premises directly yield O-1/O-2; no backend or optimizer premise is used.

## F-1 — unchecked zero in a supported safe configuration

- **Status/severity:** `UNSOUND`, critical; implementation defective and `lib.rs:30` proof comment false.
- **Witness:** Select supported Rust/Cargo 1.85.1, `aarch64-unknown-linux-gnu`, feature `burst`, allocator `arena`, any profile/debug-assertion state, successful build-script writes; then well-typed safe code calls `lane_id(0)`. `BUILD-MAP-X` makes all three cfg predicates true. Lines 24–32 are retained and lines 34–45 are not. Line 31 executes `NonZeroU8::new_unchecked(0)`, and AXIOM-NZ states that this is UB.
- **Smallest false implication:** “burst-mode lane identifiers” does not imply `value != 0`; `burst` is only a Cargo feature bit and the unrestricted `u8` parameter admits zero. The comment supplies neither a check nor an enforceable caller obligation.
- **Resolution:** remove the special unchecked branch or perform an unconditional zero check before every `new_unchecked` call (prefer a checked safe constructor). A safety-comment edit alone cannot repair a safe API. Re-audit all configuration branches afterward.
- **Compatibility:** the fix enforces the already documented panic and adds no valid caller obligation. Making the function unsafe would be a breaking and unnecessary alternative.

## TCB audit log

| ID/category | Exact proposition, scope, disposition | Consumer / trigger |
|---|---|---|
| `BUILD-MAP-X` / accepted build-tool premise | Exactly the proposition and identity in supplied `TCB.md`, including selector/feature/target mapping and failure-to-no-compilation; accepted by the authorized human. It does **not** trust local source correctness or binaries. | O-1, O-5; every trigger listed in `TCB.md`. |
| `AXIOM-NZ-185` / Rust std authority | The quoted `new_unchecked` precondition and zero-UB result for std 1.85.1; accepted under the request's authority policy. | O-1, O-2; Rust/std or contract change. |
| `AXIOM-CONTROL-185` / Rust Reference authority | Cited equality, `if`, conditional-compilation, attribute, and compile-error semantics for Rust 1.85.1; accepted under the same policy. | O-1, O-2, O-5; toolchain/Reference change. |

No dependency, tool, external-specification, deployment, probabilistic, compiler-backend, or binary-correctness premise is consumed. This does not widen `TCB.md`'s sole accepted human implementation premise.

## Residual scope and review triggers

Unsupported toolchains/targets, invented cfgs, `wasm32 + arena` artifacts (none are produced), invalid allocator inputs, and compiler/backend/binary correctness are outside the source theorem. Build-script write failure also produces no library compilation under the accepted premise. No inaccessible in-scope source or generated artifact was identified.

Re-audit on any supplied source/doc change; Rust/Cargo/stdlib or target-set change; feature, allocator, env, cfg, manifest, profile, or panic-policy change; change to `BUILD-MAP-X` or its human disposition; or change to a cited authoritative contract. Every in-scope obligation above has a disposition; the sole UB witness is source-derived, not test-derived.
