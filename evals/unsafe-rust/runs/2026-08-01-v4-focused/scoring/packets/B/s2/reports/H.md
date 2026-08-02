# Unsafe Rust audit: supplied `ordered-build-target` snapshot

## Claims, scope, and verdicts

This is a source-only audit of `Cargo.toml`, `build.rs`, `src/lib.rs`, and the supplied build, support, request, and TCB policies, at cutoff 2026-08-01. It covers Rust/Cargo/standard library 1.85.1, the complete supported build interface, the only public safe API, both unsafe operations, the source-enforced exclusion, and the documented panic postcondition. No binary/backend claim is made; nothing was built, run, tested, generated, or expanded.

| Claim | Verdict | Certificate |
|---|---|---|
| Every valid safe `lane_id` call in the required library domain is free of Rust UB. | **UNSOUND** | `SOUND-1` below gives a valid supported zero-input witness reaching documented UB. |
| “Panics when `value` is zero” throughout that domain. | **UNPROVED** | Proved outside `U`; inside `U` the only execution has UB, so it cannot certify `CONTRACT-BROKEN`. |
| Ordered build mapping, rejection, and freshness behavior. | **PROVED relative to accepted `BUILD-MAP-ORDERED`** | Exhaustive raw-value/write-outcome partition `BUILD-1`; freshness proof `BUILD-2`. |
| wasm32/arena is effectively excluded. | **PROVED relative to `BUILD-MAP-ORDERED`** | `CFG-1`: every successful arena selection for wasm32 activates `compile_error!`. |
| Formula `S` below is the exact maximal sound region. | **PROVED relative to the stated TCB** | Positive proof on `S`; UB proof at every point of its complement in the supported domain. |

The combined mandatory result is **UNSOUND; documented postcondition UNPROVED**.

## Required theorem domain and closure

Let `T={x86_64-unknown-linux-gnu, aarch64-unknown-linux-gnu, wasm32-unknown-unknown}`, `B={burst-off,burst-on}`, `A={system,arena}`, `P` be every Cargo profile, and `D={debug-assertions-off,on}`. The policy's full product is

`F = T × B × A × P × D`.

Its exact supported library predicate is

`C = F ∖ {c ∈ F | target(c)=wasm32-unknown-unknown ∧ allocator(c)=arena}`.

This is an equality, not an inferred narrowing: `SUPPORT.md` gives precisely these axes, all their combinations, and exactly that exclusion. `Cargo.toml` fixes Rust 1.85.1/edition 2021 and declares `burst`; `BUILD.md` fixes allocator selection. Profiles and debug assertions never occur in either selected function body, so all proofs below are parametric over `P×D`.

Build-interface `Required` additionally quantifies over every raw `FIXTURE_ALLOCATOR` class (omitted, `system`, `arena`, `arena-stop`, other Unicode, non-Unicode) and success/failure of every attempted stdout write. A current API execution exists only after an accepted selector's successful script exit and successful non-excluded library compilation. For API soundness, `Required=C×{0,…,255}`: `u8` is the “8-bit unsigned integer type” ([`u8`](https://doc.rust-lang.org/1.85.1/std/primitive.u8.html)), and this safe function states no caller precondition.

Closure is exhaustive: `BUILD-1` partitions all build cases; `C` partitions into `U` and `¬U`; inputs partition into zero and nonzero. Each obligation below covers every resulting case, so no sampled configuration substitutes for `Required ⊆ Covered`.

## Authoritative Rust 1.85.1 premises

These are the only Rust semantic axioms consumed:

- **AX-ENV.** `env::var` returns `NotPresent` when “The variable is not set” and `NotUnicode` when its value “is not valid Unicode” ([`var`](https://doc.rust-lang.org/1.85.1/std/env/fn.var.html)); `VarError` has exactly `NotPresent` and `NotUnicode(OsString)` ([`VarError`](https://doc.rust-lang.org/1.85.1/std/env/enum.VarError.html)). `String::as_str` “Extracts a string slice containing the entire `String`” ([`as_str`](https://doc.rust-lang.org/1.85.1/std/string/struct.String.html#method.as_str)). A match chooses “The first arm with a matching pattern” ([match](https://doc.rust-lang.org/1.85.1/reference/expressions/match-expr.html)); literal patterns match their literal and `_` matches any value ([literal](https://doc.rust-lang.org/1.85.1/reference/patterns.html#literal-patterns), [wildcard](https://doc.rust-lang.org/1.85.1/reference/patterns.html#wildcard-pattern)).
- **AX-OUT/PANIC.** `println!` “Panics if writing to `io::stdout` fails” ([`println!`](https://doc.rust-lang.org/1.85.1/std/macro.println.html#panics)); `panic!` “Panics the current thread” ([`panic!`](https://doc.rust-lang.org/1.85.1/std/macro.panic.html)).
- **AX-CFG.** A `cfg` attribute “conditionally includes the thing it is attached to” ([`cfg`](https://doc.rust-lang.org/1.85.1/reference/conditional-compilation.html#the-cfg-attribute)); `compile_error!` “causes compilation to fail with the given error message” ([`compile_error!`](https://doc.rust-lang.org/1.85.1/std/macro.compile_error.html)).
- **AX-CONTROL.** For `if`, a true condition executes the consequent block ([`if`](https://doc.rust-lang.org/1.85.1/reference/expressions/if-expr.html)); `==` is an equality operator ([comparison](https://doc.rust-lang.org/1.85.1/reference/expressions/operator-expr.html#comparison-operators)). Thus the `u8` comparison exactly separates zero from nonzero.
- **AX-NZ.** `NonZero::new_unchecked` “Creates a non-zero integer value without checking”; “This results in undefined behavior if the value is zero” ([`new_unchecked`](https://doc.rust-lang.org/1.85.1/std/num/struct.NonZero.html#method.new_unchecked)). This is also the Reference's UB class “producing an invalid value” ([undefined behavior](https://doc.rust-lang.org/1.85.1/reference/behavior-considered-undefined.html)).

## Ordered build-to-source relation

Write `R` for the complete rerun line and `S`/`A` for complete `system`/`arena` cfg lines. `q(L)` means any byte prefix produced by the failing `println!` for line `L` (possibly empty); regardless of those bytes, the TCB says an unsuccessful execution supplies no current library.

| Raw class and ordered events after entry | Emitted prefix; exit; current result |
|---|---|
| Any raw value; first print fails | `q(R)`; println panic/unsuccessful; no library |
| omitted or Unicode `system`; `R` succeeds; `S` fails | `R,q(S)`; println panic; no library |
| same; both prints succeed | `R,S`; normal return; cfg `fixture_allocator="system"` |
| Unicode `arena`; `R` succeeds; `A` fails | `R,q(A)`; println panic; no library |
| same; both succeed | `R,A`; normal return; cfg `fixture_allocator="arena"` |
| Unicode `arena-stop`; `R` succeeds; `A` fails | `R,q(A)`; println panic; no library |
| same; `A` succeeds | `R,A`; explicit panic; no library |
| other Unicode; `R` succeeds | `R`; explicit panic before allocator print; no library |
| non-Unicode; `R` succeeds | `R`; explicit panic before allocator print; no library |

**BUILD-1.** AX-ENV and the fixed valid key make `env::var`'s result exactly absent, valid-Unicode `String`, or non-Unicode. AX-ENV/match/literals then select exactly the listed source arm. There are only the two `println!` sites in execution order; AX-OUT establishes each failure exit. Falling through `main` is successful. `BUILD-MAP-ORDERED` supplies only the stated Cargo consequences: a successful current script passes its exact cfg; every panic/write-failure exit compiles/presents no current library. Thus even a complete allocator directive in the `arena-stop` prefix has no effect.

**BUILD-2 (freshness).** A successful `arena` run necessarily wrote `R` then `A`. The accepted TCB says that changing the raw present value to `arena-stop` makes that result stale and reruns the script before selection. The rerun has exactly three possibilities above: first print failure; `R` followed by allocator-print failure; or `R,A` followed by explicit panic. All are unsuccessful, and the TCB expressly forbids presenting the old arena library as the current result. The canary therefore rejects under reuse of the same target directory.

**CFG-1.** On a successful arena selector, the TCB maps its emitted cfg exactly and maps the three target triples to their stated `target_arch`. AX-CFG makes `all(target_arch="wasm32", fixture_allocator="arena")` include `compile_error!` for both feature states; AX-CFG then forces compilation failure. Other raw rejection cases never reach current library compilation. The project exclusion is therefore enforced.

The complete successful-output-to-source projection is therefore:

| Emitted allocator cfg | Target/feature | Selected library source/result |
|---|---|---|
| `system` | every `T×B` | no source error; `U` is false; checked block |
| `arena` | x86_64, either feature | no source error; `U` is false; checked block |
| `arena` | aarch64, burst off | no source error; `U` is false; checked block |
| `arena` | aarch64, burst on | no source error; `U` is true; unchecked burst block |
| `arena` | wasm32, either feature | `compile_error!`; no current library artifact |

No other allocator cfg reaches a current compilation. These cases are exhaustive by `BUILD-1` and the TCB's exact feature/target mappings.

## API, obligations, and exact maximal sound region

The entire public surface is safe free function `lane_id(u8)->NonZeroU8`; there are no public fields/types, traits, callbacks, FFI, reexports, hidden items, or generated/macro-generated APIs. `build.rs::main` is the audited build entrypoint. The two cfg-complementary `new_unchecked` calls are the only unsafe operations. The sole invariant consumed/established is that the returned `NonZeroU8` contains a nonzero integer.

Define

`U(c) := burst(c)=on ∧ target(c)=aarch64-unknown-linux-gnu ∧ allocator(c)=arena`.

The exact maximal sound region over the full supported product and every API input is

`S = {(c,v) ∈ C×{0,…,255} | ¬U(c) ∨ v≠0}`.

**Positive proof.** If `U(c)`, AX-CFG includes only the first block; for `v≠0`, AX-NZ's sole safety requirement holds and it constructs the promised nonzero value. If `¬U(c)`, AX-CFG includes only the checked block. At `v=0`, AX-CONTROL reaches `panic!` before unsafe code. At `v≠0`, it skips the panic and the dominating comparison establishes AX-NZ's precondition. These cases cover `S`, independently of profile/debug-assertion state.

**SOUND-1 and maximality.** Choose any profile/debug state, successful raw `arena`, aarch64 target, `burst` enabled, and safe input `0`. This configuration lies in `C`; `0` is a valid `u8`; the public call is valid safe use. `U` includes the unchecked block, which executes `new_unchecked(0)`. AX-NZ says that exact event is UB. Hence the full universal claim is **UNSOUND**. Every point of `(C×u8)\S` has exactly those three cfg facts and `v=0`, so the same proof establishes UB everywhere outside `S`; together with the positive proof, `S` is maximal, not merely a positive remainder.

**Panic postcondition.** For every `c∈C` with `¬U(c)` and `v=0`, the checked branch invokes `panic!`, proving the documented implication. For `U(c),v=0`, execution instead has UB. Under the required whole-execution certificate, that is not a UB-free witness to a broken behavioral contract. Therefore the full postcondition is **UNPROVED**, not `CONTRACT-BROKEN`; its exact unresolved region is `{(c,0)|c∈C∧U(c)}`.

## Finding and proof-artifact assessment

**F-1 (critical implementation defect).** The first safety comment claims burst-mode lane identifiers are never zero, but the safe boundary accepts arbitrary `u8` and establishes no such invariant. The smallest repair is an unconditional zero check before either unsafe call (or a safe checked constructor), preserving the documented panic contract. Re-audit all cfg regions afterward.

The second comment's dominating `value==0` branch does establish the required nonzero fact, so its implementation proof is correct on `¬U`; for proof-grade maintenance it should also name `new_unchecked`'s exact requirement and resulting `NonZeroU8` invariant. The first comment is false, not merely incomplete.

## TCB audit log, evidence, residual scope, and triggers

`BUILD-MAP-ORDERED` is the sole non-Rust admitted premise. Its human disposition is accepted only for Cargo 1.85.1, this exact manifest/build script/environment/library, successful-line interpretation, freshness/no-stale-result behavior, failure status, feature cfg, and target-arch cfg. This report consumes every listed part only in `BUILD-1`, `BUILD-2`, `CFG-1`, and reachability; it does not use it for source correctness. AX-ENV through AX-NZ are exact versioned Rust authority, not implementation trust. There are no dependencies, unsafe dependencies, tool results, tests, prior audits, or additional assumptions.

Excluded/residual scope: compiler/backend correctness, binaries, custom/manual rustc cfgs, overridden build scripts, unsupported targets/toolchains, rejected raw selectors, and wasm32/arena artifacts. Re-audit on any source/manifest/policy/TCB change; Rust/Cargo/stdlib version change; target, feature, allocator, profile, environment, or cfg-domain change; or material authoritative-documentation change.

All in-scope surfaces, raw classes, exits, prefixes, obligations, configuration partitions, mandatory postconditions, TCB consumers, and unresolved regions have dispositions. Independent review was not performed.
