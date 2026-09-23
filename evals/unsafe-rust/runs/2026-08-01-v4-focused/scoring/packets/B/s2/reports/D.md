# Unsafe-code audit: `ordered-build-target` supplied snapshot

## Claim, domain, and verdicts

Audit cutoff: 2026-08-01. Scope is every supplied crate file, Cargo 1.85.1/Rust 1.85.1, the build interface and freshness contract, generated cfgs, selected `src/lib.rs`, its sole public safe API, and its documented panic condition. This is a Rust-abstract-semantics source claim, not a backend or binary claim. No build, execution, expansion, test, prior audit, or external dependency result was used.

Write `X`, `A`, and `W` for the three listed target triples (x86_64 GNU/Linux, aarch64 GNU/Linux, and wasm32-unknown-unknown), `F={off,on}` for `burst`, `L={system,arena}`, `P` for every Cargo profile, `D={off,on}` for debug assertions, and `U={0,...,255}`. The full policy product is

`C={X,A,W} x F x L x P x D`.

`SUPPORT.md:9-16` says exactly those members are supported except

`E={c in C | target(c)=W and allocator(c)=arena}`,

so current library configurations are `S=C\E`. Both containments for this normalization follow literally: every tuple admitted by the “every other combination” clause is in `C\E`, and every member of `C\E` has listed axis values and is not the sole exclusion. No enumeration of `P` is assumed.

Full `Required` is the union of (1) all supported Cargo build attempts over the six raw-environment classes below, every possible applicable stdout-success/failure path and relevant prior target-directory state, and (2) every call `lane_id(v)` with `c in S` and `v in U` after a current successful build. `E` and rejected selector attempts have no current API case. Manual rustc, invented cfgs, and build-script override are expressly excluded by `BUILD.md:31-34`.

| Claim | Verdict | Certificate |
|---|---|---|
| Whole-crate safe-API freedom from UB over `S x U` | **UNSOUND** | `F-UB` below supplies a valid supported safe call, reachability, false safety condition, and explicit UB consequence. |
| “`lane_id(value)` panics when `value` is zero” over `S x {0}` | **UNPROVED** | Proved on `S\K`; the remaining `K` executions have UB, so they cannot establish `CONTRACT-BROKEN` and do not prove the postcondition. |
| Exact maximal realized library sound region | **PROVED relative to TCB-ORDERED** | `M=(S x U)\WIT`, proved below; every point in its complement within `S x U` is an UB witness. |
| Ordered build mapping, freshness canary, and target/allocator rejection | **PROVED relative to TCB-ORDERED** | Exhaustive staged relation and exact cfg derivation below. |

Thus the combined mandatory result is **UNSOUND; documented postcondition UNPROVED**, not `PROVED` and not `CONTRACT-BROKEN`.

## Boundary, surfaces, and invariants

`Cargo.toml` selects only `build.rs` and `src/lib.rs`; all supplied files were read. `build.rs::main` is private and contains no unsafe operation. The complete downstream surface is the public **safe** free function `lane_id(u8) -> NonZeroU8`; there are no crate-defined public fields, constructors, traits/impls, statics, callbacks, FFI, reexports, hidden items, or exported/generated macros. Its caller has no safety precondition. The only invariant consumed is `NZ`: the argument to `NonZeroU8::new_unchecked` is nonzero, thereby producing a valid nonzero result. The function boundary must establish `NZ`; `lib.rs:18` does not.

## Complete ordered build relation

Let `R` be the complete line `cargo::rerun-if-env-changed=FIXTURE_ALLOCATOR`, and `CS`/`CA` the complete system/arena `cargo::rustc-cfg` lines. Block statements execute sequentially, and a value scrutinee is evaluated then patterns are compared sequentially until the first match. These checked semantics make the source order literal, not inferred from endpoint output.

1. Cargo runs `build.rs`; `build.rs:4` first attempts `println!(R)`. If it succeeds, complete prefix `[R]` exists and only then is `env::var` called. If it fails, `println!` panics there: no classification or later write is reached and no earlier complete line is guaranteed.
2. With `[R]`, `env::var` and the two matches produce the exhaustive raw partition below. The key literal itself contains neither `=` nor NUL. `Result` has only `Ok`/`Err`; `VarError` has only `NotPresent`/`NotUnicode`; `as_str` preserves the entire Unicode string; literal patterns select exactly their values and `_` every remainder.

| Raw `FIXTURE_ALLOCATOR` class | Reached operation after `[R]` | If that operation succeeds | Explicit/failure exit |
|---|---|---|---|
| omitted | `build.rs:8` attempts `CS` | return success with `[R,CS]` | write failure panics with prior complete prefix `[R]` |
| Unicode `system` | line 12 attempts `CS` | return success with `[R,CS]` | same failure prefix/exit |
| Unicode `arena` | line 15 attempts `CA` | return success with `[R,CA]` | same failure prefix/exit |
| Unicode `arena-stop` | line 18 attempts `CA` | prefix `[R,CA]`, then line 19 explicitly panics | line-18 failure panics first with prior prefix `[R]`; line 19 is not reached |
| every other Unicode value | no allocator write | none | line 21 explicitly panics with `[R]` |
| every non-Unicode value | no allocator write | none | line 24 explicitly panics with `[R]` |

This includes every dynamic stdout failure site: common line 4 and the class-specific lines 8, 12, 15, and 18. A failed `println!` may have written an unspecified byte prefix (possibly a complete-looking attempted line); the table states only already successful complete lines. TCB-ORDERED makes all such executions unsuccessful and prevents any prefix from producing a current library, so no atomic-write premise is consumed. Explicit `panic!` writes no Cargo stdout directive.

3. On exactly the three accepted successful classes, TCB-ORDERED interprets the current two complete lines: `R` establishes freshness tracking and exactly one of `CS`/`CA` passes the corresponding exact `fixture_allocator` key/value cfg to this library, with no selector retained from an earlier run. Every write failure, explicit panic, and `arena-stop` exit is unsuccessful; no current library compilation occurs.
4. TCB-ORDERED also supplies the exact `burst` and target-architecture leaf cfgs. Rust cfg semantics then select source. Define

`K(c) := burst(c)=on and target(c)=A and allocator(c)=arena`.

The first `lane_id` block is present exactly on `K`; the second is present exactly on `not K`, because its predicate is the literal `not(all(...))`. Profiles and debug assertions occur in no selector or safety check, so this partition is parametric over `P x D`.

### Exact exclusion

For a current successful arena selector on `W`, TCB-ORDERED sets both `target_arch="wasm32"` and `fixture_allocator="arena"`; `all` is true, the `cfg` attribute retains `compile_error!`, and that macro fails compilation. Conversely, encountering this source error requires both leaves true, hence exactly `E`; feature state is irrelevant. System-on-`W` and arena on `X`/`A` make at least one leaf false and remove the item. Therefore `Rejected_source=E` in both directions, not merely `E` contained in a sampled rejection. A failed current compilation is no current library/API case. Over the total `C x U`, `E x U` is precisely the no-library region.

### Freshness sequence in one target directory

Take any successful prior arena library build, necessarily on `X` or `A`. Its successful script emitted `[R,CA]`; TCB-ORDERED says a present-to-present raw change from `arena` to `arena-stop` stales that selection and reruns the script before a current library can be selected. On the rerun: line 4 failure rejects immediately; otherwise line 18 failure rejects with `[R]`; otherwise `[R,CA]` is followed by the explicit panic. TCB-ORDERED says every case supplies no current library and never presents the old arena library as this rejected build's result. The freshness canary is therefore effective.

## Unsafe obligations and exact maximal region

Rust 1.85.1 documents `NonZero::new_unchecked`: “The value must not be zero” and “undefined behavior if the value is zero.” Thus each site has exactly obligation `NZ`.

* On `not K`, cfg removes the early-return block. If `v=0`, `==` is equality, the `if` consequent executes `panic!`, and control never reaches line 32. If `v!=0`, the consequent is skipped; reaching line 32 itself proves `NZ`, so the call is permitted and returns a nonzero. This reconstructs and completes the terse line-31 comment.
* On `K`, cfg removes the checked block. Line 19 is reached for every `v`. `v!=0` satisfies `NZ`; `v=0` falsifies it. The line-18 comment's “never zero” is neither type-enforced nor checked and is false for a caller-supplied `u8`.

Let

`WIT={(c,0) | c in S and K(c)}` and `M=(S x U)\WIT`.

`WIT` is nonempty: `A`, burst on, arena is listed and not the wasm exclusion, for every `P,D`; an accepted arena build with successful writes selects it. Calling the public safe `lane_id(0)` is a valid safe use. Cfg makes line 19 reachable; zero falsifies `NZ`; the exact standard-library contract entails UB. This is the complete **UNSOUND** certificate (`F-UB`).

For every member of `M`, either `not K` (the checked proof above covers every `u8`) or `K` and `v!=0` (the unsafe precondition holds); no other unsafe operation exists. Hence `M` is sound. Conversely, every member of `(S x U)\M` is by definition in `WIT` and has the proved UB certificate. Both containments establish equality and maximality, rather than a non-maximal remainder. The complete product partition is therefore: rejected `E x U`, realized-sound `M`, and realized-unsound `WIT`.

For the panic contract, `(S\{c:K(c)}) x {0}` is proved: the equality is true and `panic!` “Panics the current thread.” On `WIT`, the whole execution contains UB, so it cannot be an UB-free postcondition counterexample. No independent UB-free witness exists in this source. The strongest global postcondition verdict is consequently **UNPROVED**, with no `CONTRACT-BROKEN` certificate.

## Obligation ledger and findings

| ID | Obligation | Coverage/status |
|---|---|---|
| O-BUILD | Exhaust raw classes, ordered effects/exits, partial prefixes, Cargo interpretation | All cases proved above relative to TCB-ORDERED |
| O-FRESH | stale arena then arena-stop cannot select old/current library | proved above relative to TCB-ORDERED |
| O-EXCL | reject exactly wasm32/arena | proved in both directions |
| O-NZ-NORMAL | line 32 argument nonzero | proved on `not K` for every `u8` |
| O-NZ-BURST | line 19 argument nonzero | proved only for `K and v!=0`; **UNSOUND** at `v=0` |
| O-PANIC | every zero call panics | proved on `not K`; **UNPROVED** on `K` |

**F-UB (critical implementation defect; deficient proof artifact).** The safe `u8` input is treated as if “burst mode” enforced nonzero. Minimal resolution is to perform the zero check before every cfg-dependent unsafe call, or replace both calls with a checked safe constructor while preserving the documented panic. A valid replacement proof would say: “`new_unchecked` requires nonzero; if `value==0` the preceding `panic!` diverges, so reaching this call proves `value!=0`.” Re-audit all `K`, postcondition, and maximal-region proofs after repair.

## Authority and TCB audit log

**TCB-ORDERED (accepted human decision):** supplied `TCB.md` entry `BUILD-MAP-ORDERED`, Cargo 1.85.1, exact supplied manifest/script/interface/library. Consumed propositions only: required script execution; successful `R` freshness including present-to-present raw changes; exact current successful cfg and no retained selector; no compilation/old-result presentation after unsuccessful script even with complete prefixes; panic as unsuccessful exit; and exact feature/target leaves. No local emission, Rust semantics, source correctness, backend, binary, or compiler-correctness proposition is imported. Owner is the unidentified authorized human; triggers are exactly `TCB.md:43-45`. Cargo's versioned documentation corroborates that Cargo will [“execute it just before building”](https://doc.rust-lang.org/1.85.1/cargo/reference/build-scripts.html#life-cycle-of-a-build-script), treats [stdout `cargo::` lines as instructions](https://doc.rust-lang.org/1.85.1/cargo/reference/build-scripts.html#outputs-of-the-build-script), and [`rustc-cfg` passes its value to `--cfg`](https://doc.rust-lang.org/1.85.1/cargo/reference/build-scripts.html#rustc-cfg); the stronger failure/staleness clauses remain only the expressly accepted TCB proposition.

Checked Rust 1.85.1 axioms, all accepted as version-matched authoritative text:

* Environment/classification: `env::var` says [“The variable is not set” and `NotUnicode` means its “value is not valid Unicode”](https://doc.rust-lang.org/1.85.1/std/env/fn.var.html); [`VarError` has exactly `NotPresent` and `NotUnicode`](https://doc.rust-lang.org/1.85.1/std/env/enum.VarError.html); [`Result` is `Ok(T)` or `Err(E)`](https://doc.rust-lang.org/1.85.1/std/result/enum.Result.html); [`as_str` contains the entire `String`](https://doc.rust-lang.org/1.85.1/std/string/struct.String.html#method.as_str).
* Order/partition: blocks [“sequentially execute”](https://doc.rust-lang.org/1.85.1/reference/expressions/block-expr.html); match uses the [“first arm with a matching pattern”](https://doc.rust-lang.org/1.85.1/reference/expressions/match-expr.html); literal patterns [“match exactly the same value”](https://doc.rust-lang.org/1.85.1/reference/patterns.html#literal-patterns), tuple patterns match enum values, and `_` [“matches any value”](https://doc.rust-lang.org/1.85.1/reference/patterns.html#wildcard-pattern).
* Effects: `println!` [prints stdout with newline and “Panics if writing ... fails”](https://doc.rust-lang.org/1.85.1/std/macro.println.html#panics); [`panic!` “Panics the current thread”](https://doc.rust-lang.org/1.85.1/std/macro.panic.html).
* Cfg: the [conditional-compilation clauses](https://doc.rust-lang.org/1.85.1/reference/conditional-compilation.html#the-cfg-attribute) say an “option is set,” “all ... predicates are true,” `not` inverts, and false cfg means the “thing is removed from the source code.” [`compile_error!` “Causes compilation to fail”](https://doc.rust-lang.org/1.85.1/std/macro.compile_error.html).
* API: `u8::MIN=0` and [`u8::MAX=255`](https://doc.rust-lang.org/1.85.1/std/primitive.u8.html); `==` means [“Equal”](https://doc.rust-lang.org/1.85.1/reference/expressions/operator-expr.html#comparison-operators); a true `if` condition [executes its consequent](https://doc.rust-lang.org/1.85.1/reference/expressions/if-expr.html); and [`new_unchecked` “Creates a non-zero,” requires nonzero, and expressly makes zero UB](https://doc.rust-lang.org/1.85.1/std/num/struct.NonZero.html#method.new_unchecked).

No other TCB entry, dependency contract, tool-derived evidence, environment restriction, or compatibility premise was consumed. Rust/Cargo/toolchain, target/feature policy, script/source/docs, TCB disposition, or panic-contract changes trigger full re-audit. Review attestation is complete except that the audited artifact itself fails O-NZ-BURST and O-PANIC as reported.
