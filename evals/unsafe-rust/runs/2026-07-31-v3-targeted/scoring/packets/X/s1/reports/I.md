# Unsafe Rust source audit: `cross-axis-target`

## Claim and verdict

This review covers the complete supplied crate: `Cargo.toml`, `build.rs`, `src/lib.rs`, `BUILD.md`, `SUPPORT.md`, and `TCB.md`, on the exact supplied source snapshot. The source-level claim is: every well-typed safe use of the public library API is free from Rust undefined behavior for every supported build, relative only to the TCB below.

`Supported(C)` means Rust, Cargo, and standard library 1.85.1; edition 2021; a target in {`x86_64-unknown-linux-gnu`, `aarch64-unknown-linux-gnu`, `wasm32-unknown-unknown`}; either state of feature `burst`; allocator selector `system` or `arena` obtained through `build.rs` as specified by `BUILD.md`; any Cargo profile and either debug-assertion state; excluding `wasm32-unknown-unknown` + `arena`. Build-script stdout writes must succeed for an accepted-selector library compilation. This predicate is fixed by the manifest, `SUPPORT.md`, `BUILD.md`, and accepted `BUILD-MAP-X`; they do not conflict.

- **Complete supported-domain soundness: UNSOUND** (`F-01`).
- **Region `Rbad`: UNSOUND.** `Rbad = Supported(C) && target=aarch64-unknown-linux-gnu && allocator=arena && burst=enabled`, in every profile/debug-assertion state.
- **Region `Supported \\ Rbad`: PROVED** source-sound relative to the stated TCB and Rust 1.85.1 axioms below.
- **Documented `lane_id(0)` panic, complete supported domain: UNPROVED** (`F-01`). It is proved on `Supported \\ Rbad`; the only established contrary execution in `Rbad` contains UB, so it cannot establish `CONTRACT-BROKEN`.
- **Documented build selection/rejection behavior and the required wasm/arena exclusion: PROVED** relative to `BUILD-MAP-X`.

No binary/backend, future-toolchain, security, resource, or manually-invoked-`rustc` claim is made.

## Snapshot, surfaces, and trust boundary

There are no third-party dependencies, generated Rust files, FFI, assembly, unsafe declarations/traits/impls, public fields, macros exported by the crate, callbacks, or invariant-bearing project types. The build script generates only a `fixture_allocator` configuration option. No prior audit or tool-derived evidence was used; the target was not built, run, tested, or expanded.

API/operation inventory:

| ID | Surface/site | Domain | Status |
|---|---|---|---|
| API-01 | safe public `lane_id(u8) -> NonZeroU8`, `src/lib.rs:23` | every compiled supported library | `UNSOUND` via OBL-03 |
| UNSAFE-01 | `NonZeroU8::new_unchecked(value)`, line 31 | exactly `Rbad` | violated for `value=0` |
| UNSAFE-02 | same operation, line 44 | `Supported \\ Rbad` | proved |
| BUILD-01 | environment parsing and cfg emission, `build.rs:3-21` | Cargo builds through documented interface | proved |
| REJECT-01 | three `compile_error!` guards, `src/lib.rs:3-16` | selected cfg combinations | proved as detailed below |

The sole local invariant consumed is **INV-NZ**: at either unsafe call, the argument must be nonzero. It is owned by the immediately dominating control-flow proof; no type-wide or allocator-wide invariant supplies it.

### TCB log (revision: supplied `TCB.md`)

| ID | Category/disposition | Exact consumed proposition | Scope/consumer |
|---|---|---|---|
| BUILD-MAP-X | accepted human build-tool premise | Exactly the Cargo/target/feature/cfg mapping, rebuild behavior, and unsuccessful-build behavior stated in `TCB.md:5-32` | configuration reachability and rejection only |
| AXIOM-NZ-1.85.1 | versioned std axiom | `NonZero::new_unchecked` “results in undefined behavior if the value is zero”; its safety requirement is that the value not be zero | UNSAFE-01/02; [Rust 1.85.1 std](https://doc.rust-lang.org/1.85.1/std/num/struct.NonZero.html#method.new_unchecked) |
| AXIOM-CFG/FLOW/PANIC | versioned Reference/std axioms | `cfg` selects attached source by its predicate; `if` selects its consequent on true; `u8 == 0` tests equality; encountered `compile_error!` prevents compilation; `panic!` panics the current thread | case partition and rejection; [cfg](https://doc.rust-lang.org/1.85.1/reference/conditional-compilation.html#the-cfg-attribute), [if](https://doc.rust-lang.org/1.85.1/reference/expressions/if-expr.html), [comparison](https://doc.rust-lang.org/1.85.1/reference/expressions/operator-expr.html#comparison-operators), [compile_error](https://doc.rust-lang.org/1.85.1/std/macro.compile_error.html), [panic](https://doc.rust-lang.org/1.85.1/std/macro.panic.html) |

`BUILD-MAP-X` is not widened to assert which string this source emits, source correctness, abstract Rust semantics, or backend correctness. Changes to any identity or input named in that entry trigger re-audit.

## Configuration closure and obligation ledger

`build.rs` first emits the rebuild and expected-value declarations. `env::var` then partitions inputs: absence constructs exactly `system`; Unicode `system` and `arena` retain those exact strings; non-Unicode input panics. The following literal/or/wildcard match emits exactly one quoted selector only for `system` or `arena`, and panics for every other Unicode value. Because formatting occurs only after that exact match, no arbitrary value can enter the directive. `BUILD-MAP-X` transfers the emitted selector to the library and makes an unsuccessful script/stdout write produce no library compilation.

For every accepted build, exactly one supported allocator cfg is therefore set. The first two library guards are inactive. On `wasm32` + `arena`, the third guard is active and `compile_error!` prevents a library artifact, satisfying the sole support-policy exclusion. Invalid or non-Unicode environment values are rejected earlier by the script. A stdout infrastructure failure also yields no compilation, but per `TCB.md` is not classified as a successful policy rejection. No/dual/invented selectors from manual `rustc` are outside the theorem; the no/dual cases are nevertheless guarded.

The unsafe implementation has an exhaustive cfg partition:

| Obligation | Exact proposition | Derivation/status |
|---|---|---|
| OBL-01 | supported configuration coverage | `BUILD-MAP-X` plus the three literal cfg axes gives `Rbad` or its exact complement; profile/debug assertions do not occur in source. Proved. |
| OBL-02 | excluded wasm/arena cannot ship | accepted selector reaches the third guard, which causes compilation failure. Proved. |
| OBL-03 | UNSAFE-01 argument is nonzero for every safe call | No check, type restriction, privacy boundary, or caller contract establishes this. False for `value=0`; `UNSOUND`. |
| OBL-04 | UNSAFE-02 argument is nonzero | If `value == 0`, `panic!` executes before the unsafe call. Reaching line 44 therefore entails `value != 0`, satisfying AXIOM-NZ. Proved over the exact complement of `Rbad`. |
| OBL-05 | safe API is sound for all `u8` | OBL-04 proves the complement, but OBL-03 refutes the universal claim. `UNSOUND`. |
| OBL-06 | `lane_id(0)` panics | The dominating zero branch proves it outside `Rbad`. In `Rbad`, the established execution has UB at UNSAFE-01; complete-domain postcondition remains `UNPROVED`, not `CONTRACT-BROKEN`. |

For nonzero inputs in either region, AXIOM-NZ is satisfied. There are no later unsafe consumers or state transitions. This proof is parametric over all profiles, debug-assertion states, and supported targets sharing each cfg case.

## F-01 — unchecked zero in a safe API

- **Status:** `UNSOUND`; implementation defect and deficient local proof comment.
- **Affected claim/configuration:** API-01 in every `Rbad` build.
- **Valid witness:** Build through Cargo 1.85.1 for `aarch64-unknown-linux-gnu`, set `FIXTURE_ALLOCATOR=arena`, enable `burst`, and let stdout writes succeed. These choices are supported, and `BUILD-MAP-X` makes all three cfg predicates at lines 25-27 true. Well-typed safe code calls `lane_id(0)`. The selected block reaches line 31 with `value == 0`; AXIOM-NZ says this is undefined behavior.
- **Defect:** The comment “Burst-mode lane identifiers are never zero” reverses no producer contract and cites no enforced invariant. `value` is the safe caller's unconstrained `u8`; the function documentation actually promises to panic on zero.
- **Postcondition classification:** This UB-containing witness cannot prove an UB-free failure to panic. No independent UB-free refutation is established, so the documented panic is `UNPROVED` in `Rbad`.
- **Minimum repair:** Make the zero check dominate the unsafe call in every configuration (the existing complement branch is sufficient), or use a checked safe constructor with explicit zero-to-panic handling. Replace the comment with the line-identified dominating-check derivation used for OBL-04. Re-audit the changed snapshot across the full cfg partition.

## Residual scope and review triggers

Unsupported combinations are limited to invalid/non-Unicode allocator input, wasm/arena, and manual/invented rustc cfg use as described above; each enforcement or theorem exclusion is explicit. Future Rust/Cargo versions, custom targets, backend/binary behavior, and environmental behavior beyond `BUILD-MAP-X` are excluded.

Re-audit on any source, manifest, support/build documentation, public contract, Rust/Cargo identity, target set, feature, environment interface, emitted cfg, TCB disposition, or relevant authoritative-documentation change. Every in-scope site has a disposition; the complete supported-domain result remains **UNSOUND** until F-01 is repaired and the new snapshot is audited.
