# Unsafe-code audit: supplied ordered-build crate

## Claims, snapshot, and verdicts

Audit cutoff: 2026-08-01. The audited identity is the complete supplied snapshot: `Cargo.toml`, `build.rs`, `src/lib.rs`, `BUILD.md`, `SUPPORT.md`, `TCB.md`, and `REQUEST.md`; Rust/Cargo/stdlib are exactly 1.85.1, edition 2021. There are no dependencies or generated files. No build, execution, expansion, or test evidence was used.

Let `T={X86,A64,Wasm}` denote the three triples in `SUPPORT.md`; `B={off,on}` the `burst` cfg state; `A={system,arena}`; `P` every Cargo profile; and `D={debug_assertions off,on}`. The exact supported library domain is

`R = {1.85.1} × T × B × A × P × D \ {(1.85.1,Wasm,b,arena,p,d)}`.

The allocator coordinate must arise from a successful current build-script run: raw absent or `system` maps to `system`, and raw `arena` maps to `arena`. Rejected raw values and write-failing executions are part of the audited build interface but create no library configuration.

| Claim | Verdict | Certificate |
|---|---|---|
| Ordered selector, rejection, freshness, and wasm/arena exclusion | **PROVED**, relative to `BUILD-MAP-ORDERED` | Exhaustive relation and exclusion proof below |
| Build script and `lane_id` are UB-free for every current library in `R` and every `u8` input | **UNSOUND** | Supported `A64,on,arena,p,d`, input `0`, reaches `new_unchecked(0)` |
| “Panics when `value` is zero” for every `c in R` | **UNPROVED** | Proved when `F(c)` is false; the remaining executions contain UB, so they cannot certify a defined contract refutation |

Here `F(c) := (target=A64 && burst=on && allocator=arena)`. The **exact maximal sound region** over the requested product is

`Smax = {(c,x) in R × u8 | !F(c) || x != 0}`.

Its complement is exactly `{(c,0) | c in R && F(c)}` (all profiles and both debug-assertion states). Thus this is maximal, not merely a positive subset.

## Version-matched Rust axioms

These are the only material Rust propositions consumed:

* AX-ENV: [`env::var`](https://doc.rust-lang.org/1.85.1/std/env/fn.var.html) “Returns an Err if the variable is not present, or if the current value is not valid Unicode.” [`Result`](https://doc.rust-lang.org/1.85.1/std/result/enum.Result.html) represents success as `Ok` or failure as `Err`; [`VarError`](https://doc.rust-lang.org/1.85.1/std/env/enum.VarError.html) distinguishes `NotPresent` and `NotUnicode`.
* AX-ORDER: the [block-expression Reference](https://doc.rust-lang.org/1.85.1/reference/expressions/block-expr.html) says statements are “executed sequentially.” The [match Reference](https://doc.rust-lang.org/1.85.1/reference/expressions/match-expr.html) says values are sequentially compared with arm patterns and the first match is chosen. [Tuple-struct patterns](https://doc.rust-lang.org/1.85.1/reference/patterns.html#tuple-struct-patterns) match tuple-struct and enum-variant values. [`String::as_str`](https://doc.rust-lang.org/1.85.1/std/string/struct.String.html#method.as_str) “Extracts a string slice containing the entire String.” Literal patterns [match the literal's value](https://doc.rust-lang.org/1.85.1/reference/patterns.html#literal-patterns), while the [wildcard](https://doc.rust-lang.org/1.85.1/reference/patterns.html#wildcard-pattern) “matches any value.”
* AX-EXIT: [`println!`](https://doc.rust-lang.org/1.85.1/std/macro.println.html#panics) “Panics if writing to `io::stdout` fails”; [`panic!`](https://doc.rust-lang.org/1.85.1/std/macro.panic.html) “Panics the current thread.” `BUILD-MAP-ORDERED` supplies the process-status consequence.
* AX-CFG: the [conditional-compilation Reference](https://doc.rust-lang.org/1.85.1/reference/conditional-compilation.html#conditional-compilation) defines `all` as true exactly when all predicates are true and `not` as negation. The [`cfg` attribute](https://doc.rust-lang.org/1.85.1/reference/conditional-compilation.html#the-cfg-attribute) includes its attachment when true and removes it when false. [`compile_error!`](https://doc.rust-lang.org/1.85.1/std/macro.compile_error.html) “causes compilation to fail with the given error message when encountered.”
* AX-NZ: Rust 1.85.1 [`NonZero::new_unchecked`](https://doc.rust-lang.org/1.85.1/std/num/struct.NonZero.html#method.new_unchecked) requires: “The value must not be zero”; creating it with zero is undefined behavior. The [UB Reference](https://doc.rust-lang.org/1.85.1/reference/behavior-considered-undefined.html) confirms that unsafe blocks remain subject to the UB rules.
* AX-IF: the [`if` Reference](https://doc.rust-lang.org/1.85.1/reference/expressions/if-expr.html) executes the consequent exactly when its Boolean condition is true; the [comparison-operator Reference](https://doc.rust-lang.org/1.85.1/reference/expressions/operator-expr.html#comparison-operators) gives `==` equality for the `u8` comparison.

## Complete ordered build relation

Write `RERUN`, `CS`, and `CA` for the complete lines at `build.rs:4`, `:8/:12`, and `:15/:18`. `partial(L)` means any bytes produced by a failing attempt to write `L`, possibly none or even a complete-looking line. This deliberately does not assume line-write atomicity.

1. For **every** raw environment state, the first operation attempts `RERUN`. If it fails, the only output is `partial(RERUN)`; `println!` panics before `env::var`, the process is unsuccessful, and no current library is compiled.
2. If `RERUN` succeeds, `env::var` is evaluated and its exhaustive `Result`/match partition is:
   * absent or Unicode `system`: attempt `CS`. Failure yields `[RERUN]+partial(CS)`, panic, and no library. Success yields `[RERUN,CS]`, normal return, and exactly `fixture_allocator="system"` for the current library;
   * Unicode `arena`: the identical two outcomes with `CA`, selecting exactly `arena` only after success;
   * Unicode `arena-stop`: attempt `CA`. A write failure yields `[RERUN]+partial(CA)` and no library. A successful write yields `[RERUN,CA]`, then the explicit panic at `build.rs:19`; despite the complete allocator line, no current library is compiled;
   * every other Unicode value: output `[RERUN]`, then the wildcard-arm panic at `:21`; no allocator write and no library;
   * every non-Unicode value: output `[RERUN]`, then the `NotUnicode` panic at `:24`; no allocator write and no library.

This exhausts the first-write outcome, all three `env::var` result classes, all literal/wildcard subdivisions of `Ok`, and every second-write outcome. Local sequential execution plus AX-ENV/ORDER/EXIT proves the source-side order and exits. Accepted TCB entry `BUILD-MAP-ORDERED` supplies only these consumed Cargo facts: a successfully written rerun line tracks any raw-value change; a cfg line affects the current library only after that script exits successfully; only the current successful run's exact directives are used; an unsuccessful script (including uncaught panic or either write failure) produces no current library and cannot surface a stale one; enabled `burst` and the three target triples set the named cfgs. No source-correctness or Rust-semantic proposition is imported from that entry.

**Freshness witness sequence.** A successful raw `arena` run writes `[RERUN,CA]`, returns, and may produce the arena library. In the same target directory, changing the present raw value to `arena-stop` makes that result stale and reruns the script before selection. The rerun has exactly the three unsuccessful cases above: first write fails; first succeeds and `CA` fails; or both writes succeed and `:19` panics. Therefore the current build is rejected in every case, and the prior arena library is not its result.

## Configuration/source closure and exclusion

For a successful selector run, Cargo supplies exactly one of `system` or `arena`. AX-CFG makes the two `lane_id` bodies complementary:

* `system`, or any X86 configuration, or `burst=off`: only the checked body at `lib.rs:27-32` is selected;
* `A64 + arena + burst=on`: only the unchecked-return body at `:17-20` is selected;
* `Wasm + arena`: independently of `burst`, the cfg on `:3` is true and `compile_error!` makes the current library compilation fail, producing no library artifact;
* `Wasm + system` remains in the checked class.

Thus the required exclusion is effectively and exactly rejected: successful arena selection plus the accepted Wasm target-cfg entails the compile error. No rejected raw class bypasses it, because none creates a current library. Conversely, this source error's predicate is precisely `Wasm && arena`, so it does not enlarge the stated exclusion. Profiles and debug assertions do not occur in any selector or source predicate, giving a parametric proof over `P×D`. Hence the build/exclusion `Covered` predicate contains the complete build-interface domain, and the successful-library projection is exactly `R`.

## API, obligations, and maximal-region proof

The only public surface is safe `lane_id(u8) -> NonZeroU8`; there are no public fields, traits/impls, callbacks, macros, statics, FFI, or hidden APIs. The only unsafe sites are its two cfg-complementary `new_unchecked` calls. The build script contains no unsafe code.

* If `!F(c)` and `x=0`, `value == 0` is true, so `panic!` executes before the unsafe call. This is UB-free and proves the documented panic behavior.
* If `!F(c)` and `x!=0`, the zero branch is skipped; that dominating fact discharges AX-NZ before `lib.rs:32`.
* If `F(c)` and `x!=0`, the direct call at `:19` satisfies AX-NZ.
* If `F(c)` and `x=0`, cfg selection reaches `new_unchecked(0)`. The safe signature imposes no caller precondition, so this is a valid supported safe use; AX-NZ's required proposition is false and the operation has undefined behavior. This proves **UNSOUND**, for every `p,d` in this complement.

The four cases are exhaustive (`F`/`!F`, zero/nonzero). The first three prove every member of `Smax`; the fourth proves every member of its complement unsound, establishing maximality. The existing fast-path comment—“Burst-mode lane identifiers are never zero”—is a false, unenforced premise; the parameter comes directly from adversarial safe code. The checked-path comment is adequate.

For the panic contract, coverage is exactly `{(c,0) | c in R && !F(c)}`. In the uncovered `F(c),0` cases the whole execution contains UB. Consequently there is no UB-free witness here for `CONTRACT-BROKEN`; the strongest contract verdict is **UNPROVED**, alongside the independently certified **UNSOUND** verdict.

## TCB audit, findings, and residual scope

TCB log identity is the supplied `TCB.md`, entry `BUILD-MAP-ORDERED`, disposition accepted by the authorized reviewer. Its exact consumed fragments and consumers are recorded above; its Cargo/toolchain identity is 1.85.1. AX-ENV through AX-IF are versioned Rust authorities, not extra implementation assumptions. No pending, unsafe-dependency, tool, backend, binary, platform-runtime, or probabilistic premise is consumed.

**Finding F-1 (UNSOUND; proof comment deficient):** `src/lib.rs:18-19`, precisely `F(c) && value=0`. Minimum repair is to check zero before every `new_unchecked`, use `NonZeroU8::new(value).expect(...)`, or remove the special unsafe branch. Merely strengthening prose would add an invalid hidden precondition to a safe API. Re-audit all cfg cases and the panic guarantee after repair.

**Finding F-2 (postcondition UNPROVED):** the same region prevents a universal panic proof, but supplies no defined contract-breaking witness. Repair F-1 while retaining a zero-input panic on the fast path.

This is a source-level Rust theorem only. Compiler/backend correctness, produced binaries, manually invented cfgs, direct `rustc`, build-script override, targets/toolchains outside the stated set, and future source or policy are excluded. Re-audit on any source, Rust/Cargo, support domain, raw interface, feature/target cfg, TCB disposition, or cited semantic-contract change.
