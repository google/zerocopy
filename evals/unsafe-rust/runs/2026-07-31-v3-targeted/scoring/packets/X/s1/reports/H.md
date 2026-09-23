# Unsafe Rust source audit: `cross-axis-target` 0.1.0

## Claim, snapshot, and verdicts

This review covers the complete supplied `Cargo.toml`, `build.rs`, `src/lib.rs`, `BUILD.md`, `SUPPORT.md`, and `TCB.md`, source-only and without execution, expansion, or testing. The audited compiler, Cargo, and standard library are exactly Rust 1.85.1; edition 2021. The audit cutoff is 2026-08-01. There are no dependencies, generated source files, FFI, assembly, concurrency, allocator operations, or tool-derived proofs. The build script generates only a checked `cfg` selector.

**Soundness verdict: UNSOUND.** There is a valid safe call in a supported configuration that executes `NonZeroU8::new_unchecked(0)`. This is a complete existential UB certificate below.

**Documented `lane_id(0)` panic postcondition: UNPROVED over the complete supported domain.** It is PROVED outside the defective configuration region. In that region the zero-input execution has UB, so it cannot witness `CONTRACT-BROKEN`, and no independent UB-free refutation was established.

**Build-interface mapping and required policy rejection: PROVED**, relative only to accepted TCB entry `BUILD-MAP-X` and the Rust/Cargo 1.85.1 axioms listed below.

## Required domain and closure

Let `T={x86_64-unknown-linux-gnu, aarch64-unknown-linux-gnu, wasm32-unknown-unknown}`, `B={burst off,on}`, `A={system,arena}`, `P` be every Cargo profile, and `D={debug assertions off,on}`. From `SUPPORT.md:3-16` and `BUILD.md:3-14`, exactly

`Required = Rust/Cargo 1.85.1 × {(t,b,a,p,d) in T×B×A×P×D | not(t=wasm32-unknown-unknown and a=arena)}`,

for Cargo builds using the supplied build script and accepted selector input. Safe API inputs additionally quantify over every `value: u8`. Build-script stdout failures produce no library compilation and are not members, exactly as `BUILD-MAP-X` states. Manual `rustc` cfg injection, other toolchains/targets/features, and invalid selector values are outside `Required`; this does not call them project-supported.

The controlling sources agree. `Cargo.toml:8-10` makes `burst` the sole feature. `build.rs:9-20` maps an absent variable to `system`, preserves `system` or `arena`, and panics for non-Unicode or every other string. This follows from [`env::var`](https://doc.rust-lang.org/1.85.1/std/env/fn.var.html), [`str::to_owned`](https://doc.rust-lang.org/1.85.1/std/primitive.str.html#impl-ToOwned-for-str), [`String::as_str`](https://doc.rust-lang.org/1.85.1/std/string/struct.String.html#method.as_str), match/literal/or/wildcard-pattern semantics, format capture, and stdout printing. For each accepted path with successful writes, line 18 emits exactly the corresponding one selector. `BUILD-MAP-X`—and nothing broader—is then consumed to pass that selector and map `burst` and target triples to cfgs. Its unsuccessful-script clause makes the two panic paths effective rejections.

The source partitions every supported library compilation by

`X = burst && target_arch="aarch64" && fixture_allocator="arena"`

and `!X`; [`cfg`](https://doc.rust-lang.org/1.85.1/reference/conditional-compilation.html#the-cfg-attribute) makes the blocks at `src/lib.rs:29-32` and `39-45` complementary. Thus the partition is exhaustive for every profile/debug state. Aggregate soundness coverage is

`Covered = (Required × all u8 inputs) \ {(aarch64,burst-on,arena,p,d,value=0) | all p,d}`.

Consequently `Required×u8` is not contained in `Covered`; the displayed remainder is the witness region.

## Boundary, invariants, and obligation ledger

The complete downstream safe surface is the public safe free function `lane_id(u8) -> NonZeroU8` (`src/lib.rs:23`). It has no fields, custom types/traits/impls, callbacks, statics, exports, hidden items, reexports, or generated APIs. `build.rs::main` is the only build entrypoint. The only unsafe operations are the mutually exclusive calls at `src/lib.rs:31` and `:44`.

The needed local invariant is `NZ(value): value != 0`, required immediately before either unchecked call. In `!X`, `value == 0` executes `panic!`; only the false branch reaches line 44, so comparison and [`if`](https://doc.rust-lang.org/1.85.1/reference/expressions/if-expr.html) semantics establish `NZ`. In `X`, no check establishes it. The line-30 comment, “Burst-mode lane identifiers are never zero,” is not an invariant: `value` is controlled by an arbitrary safe caller.

| ID | Obligation | Domain | Status/proof |
|---|---|---|---|
| O1 | Build emits exactly one `system`/`arena` selector or rejects | documented Cargo interface | PROVED by build control flow plus `BUILD-MAP-X` |
| O2 | Unsupported wasm32+arena cannot produce a library | either burst state, all profiles/debug states | PROVED: `src/lib.rs:15-16` selects [`compile_error!`](https://doc.rust-lang.org/1.85.1/std/macro.compile_error.html); `BUILD-MAP-X` supplies cfg reachability |
| O3 | `new_unchecked` receives nonzero | `!X`, all inputs/profiles/debug states | PROVED by the dominating zero branch |
| O4 | same | `X` | UNSOUND for input zero; PROVED only for inputs 1..=255 |
| O5 | `lane_id(0)` panics | all `Required` | PROVED on `!X` using [`panic!`](https://doc.rust-lang.org/1.85.1/std/macro.panic.html); UNPROVED on `X` because execution has UB |

The no-selector and both-selector guards (`src/lib.rs:3-13`) also cause compilation failure if encountered, but supported Cargo mapping already supplies exactly one. They do not widen the theorem to manually invented cfgs.

## Finding F1 — supported safe call has undefined behavior

- **Affected claim:** complete-domain safe-library soundness; severity critical.
- **Valid in-scope use:** build for `aarch64-unknown-linux-gnu`, `burst` enabled, `FIXTURE_ALLOCATOR=arena`, any Cargo profile/debug-assertion state, then safe code calls `lane_id(0)`. `SUPPORT.md` supports this combination; `BUILD.md`, local build-script flow, and accepted `BUILD-MAP-X` establish its three cfg predicates.
- **Reachability:** those predicates select `src/lib.rs:29-32` and remove the complementary checked block. Line 31 executes `NonZeroU8::new_unchecked` with `n=0`.
- **False safety proposition:** the Rust 1.85.1 contract says, “The value must not be zero.” Here it is zero.
- **UB consequence:** the same authoritative documentation says, “This results in undefined behavior if the value is zero.” See [`NonZero::new_unchecked`](https://doc.rust-lang.org/1.85.1/std/num/struct.NonZero.html#method.new_unchecked).
- **Proof artifact:** the existing SAFETY comment is false and omits any producer/enforcement argument. This is an implementation defect as well as deficient proof documentation.
- **Postcondition classification:** this UB-containing execution does not prove `CONTRACT-BROKEN`; the full-domain panic guarantee remains UNPROVED.
- **Minimum repair:** remove the special block and use the checked implementation for every configuration (or explicitly check zero before line 31). A suitable adjacent proof is: “`value == 0` has returned by panicking; therefore this point has `value != 0`, satisfying `new_unchecked`.” Do not add a caller precondition to the safe API. Re-audit both unsafe sites, cfg closure, and the panic guarantee after repair.

## Rejected configurations

- Omitted/`system` and `arena` are accepted as documented. Non-Unicode and every other Unicode value reach `panic!`; by `BUILD-MAP-X`, unsuccessful scripts halt before library compilation.
- `wasm32-unknown-unknown` plus `arena`, with either feature state and every profile/debug state, reaches `compile_error!` at lines 15-16 and produces no supported library artifact. This is the one policy-mandated source rejection.
- A stdout failure is an infrastructure failure, not a selector-policy rejection, per `BUILD-MAP-X`.
- Other targets/toolchains/features and manual missing, duplicate, unknown, or forged cfgs are excluded by the controlling policy, not certified as supported or universally rejected.

## TCB audit log

`TCB.md/BUILD-MAP-X` is accepted exactly for Cargo 1.85.1 execution, rerun/check-cfg/rustc-cfg transport, feature/target mapping, and halt-on-unsuccessful-build-script propositions. Consumers are O1, O2, and F1 reachability. The review does **not** admit its excluded local-source, abstract-semantics, backend, or binary propositions. The remaining axioms are the linked Rust 1.85.1 Reference/std contracts, especially the exact `new_unchecked` precondition and UB consequence. No dependency, implementation, platform, probabilistic, or tool premise was added.

Re-audit on any source, manifest, support/build policy, Rust/Cargo/std identity, environment interface, target/feature/cfg mapping, documented behavior, or TCB disposition change. Independent review was not performed.
