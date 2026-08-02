# Source-only unsafe-code audit

## Claim, domain, and verdicts

This audits exactly the supplied `Cargo.toml`, `build.rs`, `src/lib.rs`, `BUILD.md`, `SUPPORT.md`, and accepted `TCB.md`, under Rust/standard library 1.85.1 and Cargo 1.85.1. No generated file, dependency, test, build, macro expansion, backend, or binary claim is used. Audit cutoff: 2026-08-01.

Write `X`, `A`, and `W` for the three supported targets (x86_64-linux-gnu, aarch64-linux-gnu, and wasm32-unknown-unknown); `b in {0,1}` for `burst`; `a in {system,arena}`; `p in P` for every Cargo profile; and `d in {0,1}` for debug assertions. The controlling full product is

`F = {1.85.1} x {X,A,W} x {0,1} x {system,arena} x P x {0,1}`.

`SUPPORT.md` makes the compilable-library domain

`C = {c in F | not(c.target=W and c.allocator=arena)}`.

No finite enumeration of `P` is inferred. The proofs below are parametric in `p,d`; neither selects inspected source. Build-domain coverage additionally quantifies over every raw environment class and success/failure of each stdout write described below. `BUILD.md` excludes manual rustc, invented cfgs, and build-script override; that exclusion is controlling, not inferred from successful compilation.

* **Whole-crate safe-API soundness: UNSOUND**, relative to accepted `BUILD-MAP-ORDERED` and the quoted Rust axioms below. A supported safe call reaches UB.
* **Documented `lane_id(0)` panic postcondition: UNPROVED** over `C`. It is proved outside the defective configuration, but the only refutation found in that configuration contains UB, so it cannot certify `CONTRACT-BROKEN`.
* **Build mapping/freshness and W/arena rejection: PROVED** for the stated source domain relative to exactly `BUILD-MAP-ORDERED`.

## Complete ordered build relation

Let `R` be the complete line `cargo::rerun-if-env-changed=FIXTURE_ALLOCATOR`, and `S`/`A0` the complete `cargo::rustc-cfg=fixture_allocator="system"`/`"arena"` lines. Rust blocks execute statements sequentially ([Reference](https://doc.rust-lang.org/1.85.1/reference/expressions/block-expr.html): “a block sequentially executes its component non-item declaration statements and then its final optional expression”). Thus every path first attempts `R`, then calls `env::var`, then (only where shown) attempts one allocator line.

`env::var` “Fetches the environment variable `key` from the current process”; it returns `NotPresent` when unset and `NotUnicode` when its value is not valid Unicode ([std](https://doc.rust-lang.org/1.85.1/std/env/fn.var.html)). The fixed name contains neither `=` nor NUL. `as_str` “Extracts a string slice containing the entire `String`” ([std](https://doc.rust-lang.org/1.85.1/std/string/struct.String.html#method.as_str)); match selects the first matching arm after evaluating the scrutinee ([Reference](https://doc.rust-lang.org/1.85.1/reference/expressions/match-expr.html)). These facts make the following raw partition exhaustive.

| Raw class, after successful `R` | Next events in exact order | Completed stdout prefix and exit | Current library |
|---|---|---|---|
| omitted | attempt `S`; success returns | `R,S`, success | cfg `system` |
| Unicode `system` | attempt `S`; success returns | `R,S`, success | cfg `system` |
| Unicode `arena` | attempt `A0`; success returns | `R,A0`, success | cfg `arena`, subject to source rejection |
| Unicode `arena-stop` | attempt `A0`; after success explicit panic | `R,A0`, unsuccessful | none |
| every other Unicode string | explicit panic; no allocator attempt | `R`, unsuccessful | none |
| every non-Unicode value | explicit panic; no allocator attempt | `R`, unsuccessful | none |

There are exactly two write-failure sites. If the `R` write fails, execution panics there: no complete directive is guaranteed (only a possibly incomplete byte prefix) and no environment read occurs. If `S` or `A0` fails, complete prefix `R` (plus a possibly incomplete suffix of that attempted line) precedes the panic; there is no return. On `arena-stop`, failure of `A0` gives the latter prefix; success gives `R,A0` followed by the explicit panic. `println!` “Prints to the standard output, with a newline” and “Panics if writing to `io::stdout` fails” ([std](https://doc.rust-lang.org/1.85.1/std/macro.println.html#panics)); `panic!` “Panics the current thread” ([std](https://doc.rust-lang.org/1.85.1/std/macro.panic.html)). These panics are safe behavior.

The accepted TCB supplies, and this proof consumes only, these propositions: a completed `R` records raw-value freshness; a successful current execution's completed cfg line becomes that exact library cfg, with no retained earlier selector; any write failure or uncaught main-thread panic is unsuccessful and produces/presents no current library; enabling `burst` sets its feature cfg; and the three triples set the named `target_arch` values. Cargo documentation corroborates but does not replace that accepted premise: `rustc-cfg` “tells Cargo to pass the given value to the `--cfg` flag” ([Cargo](https://doc.rust-lang.org/1.85.1/cargo/reference/build-scripts.html#rustc-cfg)), while `rerun-if-env-changed` causes rerun when the named value changes ([Cargo](https://doc.rust-lang.org/1.85.1/cargo/reference/build-scripts.html#rerun-if-env-changed)).

**Freshness challenge.** After successful `arena` in one target directory, changing the raw value to `arena-stop` is a present-to-present change covered by `R`. `BUILD-MAP-ORDERED` therefore forces a rerun before selection. That rerun either fails at `R`, fails at `A0`, or writes both then explicitly panics. Every case is unsuccessful; neither its partial output nor the old arena artifact is a result of the current build. The advertised canary works.

## Directive-to-source closure and exclusion

Conditional compilation compiles parts according to conditions, and a cfg attribute “conditionally includes the thing it is attached to based on a configuration predicate” ([Reference](https://doc.rust-lang.org/1.85.1/reference/conditional-compilation.html#the-cfg-attribute)). Consequently a successful accepted build supplies exactly one allocator cfg, the selected feature state, and the target architecture.

For `W and arena`, the first predicate in `lib.rs` is true for either feature/profile/debug state, so `compile_error!`, which “Causes compilation to fail with the given error message when encountered” ([std](https://doc.rust-lang.org/1.85.1/std/macro.compile_error.html)), rejects compilation. For every other member of `F` it is false, so it rejects nothing. Therefore the source enforces exactly `F ∖ C`; `arena-stop` never reaches this stage. There is no current API for the rejected pair.

For each `c in C`, define

`Q(c) = (burst enabled) and (target=A) and (allocator=arena)`.

The two function-body cfgs are `Q` and `not(Q)`, hence form an exhaustive, disjoint partition. In `Q`, source selects the unconditional `return new_unchecked(value)` block. In `not(Q)`, it selects the block which first compares with zero, panics on equality, and otherwise calls `new_unchecked`. An `if` is a conditional branch and executes its consequent when its Boolean condition is true ([Reference](https://doc.rust-lang.org/1.85.1/reference/expressions/if-expr.html)); `==` is the equality comparison operator ([Reference](https://doc.rust-lang.org/1.85.1/reference/expressions/operator-expr.html#comparison-operators)).

## Unsafe obligation, witness, and exact maximal sound region

The complete language-reachable crate API surface is the safe free function `lane_id(u8) -> NonZeroU8`; there are no public fields, constructors besides it, traits/impls, callbacks, statics, FFI, exported macros, or hidden APIs. `compile_error!` is configuration control. The two `new_unchecked` calls are the only unsafe sites. The owned invariant/obligation is `NZ(value): value != 0` immediately before either call. No caller obligation is permitted because `lane_id` is safe.

`u8` is “The 8-bit unsigned integer type” ([std](https://doc.rust-lang.org/1.85.1/std/primitive.u8.html)); let `U={0,...,255}`. `NonZeroU8::new_unchecked` “Creates a non-zero value without checking whether the value is non-zero” and “The value must not be zero”; zero “results in undefined behavior” ([std](https://doc.rust-lang.org/1.85.1/std/num/struct.NonZero.html#method.new_unchecked)).

The exact maximal sound region of compiled API cases is

`M = {(c,x) in C x U | not(Q(c) and x=0)}`.

**Sufficiency:** if `not Q` and `x=0`, the comparison reaches `panic!` before unsafe code. If `not Q` and `x!=0`, the false branch itself establishes `NZ(x)`. If `Q` and `x!=0`, the input establishes `NZ(x)`. Thus every unsafe call in `M` satisfies its complete safety precondition. Profiles and debug assertions do not alter this derivation.

**Necessity/maximality:** choose any profile/debug state with `(target=A, burst=1, allocator=arena, x=0)`. This configuration belongs to `C`, raw `arena` successfully selects it, and `lane_id(0)` is a well-typed safe use. `Q` selects the first block; it reaches `new_unchecked(0)`, its required proposition is false, and the quoted contract entails UB. Hence every point in `(C x U) ∖ M` is unsound, while every point in `M` was proved sound. This proves both maximality and the existential `UNSOUND` certificate. Over all of `F x U`, `W/arena` has no compiled API; every other case is classified by `M` or its complement.

The special-path comment, “Burst-mode lane identifiers are never zero,” is false for caller-controlled `u8` and supplies neither a check nor an invariant. The ordinary-path comment is adequate: the dominating zero branch makes reaching its unsafe call imply nonzero. Minimal repair: perform the zero check before both cfg branches (or use checked `NonZeroU8::new(value)` and panic on `None`) and replace the false comment with that dominating fact.

For the documented postcondition, zero reaches `panic!` in every `c in C` with `not Q`; it is therefore proved exactly there. In `Q`, the zero execution contains UB. There is no independent UB-free zero execution or equivalent existence proof, so the whole-domain result is `UNPROVED`, not `CONTRACT-BROKEN`.

## TCB log, residual scope, and triggers

* **BUILD-MAP-ORDERED (accepted OUT-OF-BAND/IMPLEMENTATION premise):** exact Cargo/freshness/process-status/feature/target propositions enumerated above; consumers are build reachability and exclusion only. No source correctness is imported.
* **AXIOM-CTRL/CFG/NZ (accepted Rust authority):** only the linked, versioned 1.85.1 propositions quoted above. Rust's UB rule applies inside unsafe blocks too ([Reference](https://doc.rust-lang.org/1.85.1/reference/behavior-considered-undefined.html)).
* No dependency, allocator implementation, generated-code, tool, test, FFI, backend, binary, or deployment premise is consumed. “Allocator” is only this crate's cfg model.

Re-audit on any supplied source/policy/manifest change; Cargo/Rust/stdlib version or TCB disposition change; target, feature, allocator, profile/debug scope change; changed build-output/freshness semantics; or a new API/cfg. Independent review was not performed.
