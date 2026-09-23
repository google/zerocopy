# Unsafe Rust audit: complete supplied crate

## Claim, snapshot, and verdicts

Audited snapshot: the supplied `Cargo.toml`, `build.rs`, `src/lib.rs`, `BUILD.md`, `SUPPORT.md`, and `TCB.md`; Rust, std, and Cargo 1.85.1; edition 2021; no dependencies or generated source. Audit cutoff: 2026-08-01. No build, execution, expansion, or test evidence was used.

Let `T={x86_64-unknown-linux-gnu,aarch64-unknown-linux-gnu,wasm32-unknown-unknown}`, `F={off,on}` for `burst`, `A={system,arena}`, `P` be every Cargo profile, and `D={off,on}` for debug assertions. The controlling support expression in `SUPPORT.md` normalizes exactly to

`C = {(t,f,a,p,d) in T×F×A×P×D | not(t=wasm32-unknown-unknown and a=arena)}`.

Both containments are direct: every policy-supported tuple has listed values and is not the sole stated exclusion, hence is in `C`; every member of `C` is one of the expressly supported Cartesian combinations and is not excluded, hence is policy-supported. `P` and `D` remain symbolic; no sampled inventory substitutes for them.

The full required domain is (i) every supported-Cargo build attempt over every raw `FIXTURE_ALLOCATOR` class and every stdout-success/failure path described below, and (ii) every well-typed safe call `lane_id(x)` for `c in C` and every `x:u8`. Build rejection cases do not become library configurations.

Verdicts, relative only to accepted `TCB.md` entry `BUILD-MAP-ORDERED` and the Rust 1.85.1 axioms quoted below:

* **Build-interface contract: PROVED.** The raw partition, operation order, partial prefixes, current-build rejection, selector mapping, and arena-to-arena-stop freshness guarantee hold.
* **Target/allocator exclusion: PROVED.** Every wasm32/arena library attempt fails compilation, independently of feature, profile, and debug assertions; no such tuple is in `C`.
* **Safe-library soundness: UNSOUND.** A supported safe call reaches documented undefined behavior.
* **Documented panic postcondition: UNPROVED overall**, and PROVED on its exact positive region stated below. There is no UB-free counterexample establishing `CONTRACT-BROKEN`.

## Checked authority and TCB

The following are the material Rust axioms, all scoped to 1.85.1.

* `std::env::var` “Fetches the environment variable `key` from the current process” and returns `NotPresent` or `NotUnicode` in the two stated error cases ([`var`](https://doc.rust-lang.org/1.85.1/std/env/fn.var.html)); `VarError` has exactly those variants ([`VarError`](https://doc.rust-lang.org/1.85.1/std/env/enum.VarError.html)). `Result` “represents either success (`Ok`) or failure (`Err`)” ([`Result`](https://doc.rust-lang.org/1.85.1/std/result/enum.Result.html)). `String::as_str` “Extracts a string slice containing the entire `String`” ([`as_str`](https://doc.rust-lang.org/1.85.1/std/string/struct.String.html#method.as_str)).
* A block “sequentially executes its component non-item declaration statements” ([blocks](https://doc.rust-lang.org/1.85.1/reference/expressions/block-expr.html)); a match compares arms until a match and chooses the first matching arm ([match](https://doc.rust-lang.org/1.85.1/reference/expressions/match-expr.html)). Tuple-struct patterns select the named enum variant, literal patterns match equal values, and `_` matches any value ([tuple-struct](https://doc.rust-lang.org/1.85.1/reference/patterns.html#tuple-struct-patterns), [literal](https://doc.rust-lang.org/1.85.1/reference/patterns.html#literal-patterns), [wildcard](https://doc.rust-lang.org/1.85.1/reference/patterns.html#wildcard-pattern)).
* `println!` “Prints to the standard output, with a newline” and “Panics if writing to `io::stdout` fails” ([macro](https://doc.rust-lang.org/1.85.1/std/macro.println.html), [failure](https://doc.rust-lang.org/1.85.1/std/macro.println.html#panics)). `panic!` “Panics the current thread” ([`panic!`](https://doc.rust-lang.org/1.85.1/std/macro.panic.html)). Function calls execute their called body ([calls](https://doc.rust-lang.org/1.85.1/reference/expressions/call-expr.html), [function body](https://doc.rust-lang.org/1.85.1/reference/items/functions.html#function-body)).
* A `cfg` attribute conditionally includes its attached form; a false predicate removes it, while `all` and `not` have their literal Boolean meanings ([conditional compilation](https://doc.rust-lang.org/1.85.1/reference/conditional-compilation.html#conditional-compilation), [`cfg` attribute](https://doc.rust-lang.org/1.85.1/reference/conditional-compilation.html#the-cfg-attribute)). `compile_error!` “Causes compilation to fail with the given error message when encountered” ([`compile_error!`](https://doc.rust-lang.org/1.85.1/std/macro.compile_error.html)). An `if` executes its consequent when its Boolean condition is true ([if](https://doc.rust-lang.org/1.85.1/reference/expressions/if-expr.html)); `==` is the equality comparison used here ([comparisons](https://doc.rust-lang.org/1.85.1/reference/expressions/operator-expr.html#comparison-operators)). `u8` is the 8-bit unsigned integer type, so every input is exactly zero or nonzero ([`u8`](https://doc.rust-lang.org/1.85.1/std/primitive.u8.html)).
* `NonZeroU8::new_unchecked` “Creates a non-zero without checking whether the value is non-zero”; critically, “This results in undefined behavior if the value is zero” and its Safety clause says “The value must not be zero” ([`new_unchecked`](https://doc.rust-lang.org/1.85.1/std/num/struct.NonZero.html#method.new_unchecked)). The general UB inventory also includes producing invalid values ([undefined behavior](https://doc.rust-lang.org/1.85.1/reference/behavior-considered-undefined.html)).

`BUILD-MAP-ORDERED` is accepted exactly as written: current successful directive interpretation; freshness after a successfully written rerun directive; no current or stale library after an unsuccessful build script; feature and listed-target cfg mapping; and uncaught-main-panic status. It does **not** supply emitted strings/order or Rust/source correctness; those are derived here. Cargo documentation independently agrees that `rustc-cfg` passes a value to `--cfg` and `rerun-if-env-changed` reruns when the named value changes ([outputs](https://doc.rust-lang.org/1.85.1/cargo/reference/build-scripts.html#outputs-of-the-build-script), [`rustc-cfg`](https://doc.rust-lang.org/1.85.1/cargo/reference/build-scripts.html#rustc-cfg), [`rerun-if-env-changed`](https://doc.rust-lang.org/1.85.1/cargo/reference/build-scripts.html#rerun-if-env-changed)); these checks do not widen the accepted premise. Cargo feature interpretation is likewise confined to the entry ([features](https://doc.rust-lang.org/1.85.1/cargo/reference/features.html)).

## Complete ordered build relation

Write `R` for `cargo::rerun-if-env-changed=FIXTURE_ALLOCATOR`, `S` for `cargo::rustc-cfg=fixture_allocator="system"`, and `A` for the analogous `"arena"` line. Blocks execute in source order and every `println!` either completes or panics on its write.

1. Every execution first attempts `R`. Failure exits by panic with emitted prefix `[]`; environment classification and all later operations are unreachable. Success leaves prefix `[R]`, then `env::var` is called and the exhaustive `Result`/`VarError` matches classify the raw value.
2. Raw absent: attempt `S`. Raw Unicode `system`: `as_str` yields the whole string, the literal arm matches, and it attempts `S`. Raw Unicode `arena`: analogously attempt `A`. At any such allocator-write failure, the exit is a `println!` panic with prefix `[R]`. At success, the exact prefix is respectively `[R,S]` or `[R,A]`, `main` returns normally, and `BUILD-MAP-ORDERED` passes exactly that allocator cfg to the current library compilation.
3. Raw Unicode `arena-stop`: attempt `A`. Write failure exits unsuccessfully with `[R]`. Write success leaves `[R,A]`; the following explicit `panic!` is necessarily reached and exits unsuccessfully. The emitted allocator prefix is not interpreted into a current compilation under `BUILD-MAP-ORDERED`.
4. Every Unicode value outside `{system,arena,arena-stop}` reaches `_` and explicitly panics with `[R]`; every non-Unicode value reaches `Err(NotUnicode(_))` and explicitly panics with `[R]`. No allocator write is attempted.

Thus the successful outputs are exactly `[R,S]` for absent or `system`, and `[R,A]` for `arena`; unsuccessful prefixes are exactly `[]`, `[R]`, and (only for a fully written `arena-stop` allocator line) `[R,A]`. This accounts for both stdout failure points on every path where the second exists; a write failure is an exit, so no later fact is consumed.

Freshness is ordered, not inferred from an endpoint. A successful `arena` run necessarily wrote `R` before `A`. By the accepted entry, changing the same target directory's raw value to `arena-stop` makes that selection stale and reruns the script before current selection. The rerun either fails writing `R`, fails writing `A`, or writes both then explicitly panics. Every case is unsuccessful, and the entry forbids both a current compilation and presentation of the earlier arena library as the current result. The canary therefore rejects.

## Configuration selection and exclusion

On a successful selector run, the TCB gives exactly one allocator cfg; it also gives `feature="burst"` iff enabled and the exact `target_arch` for each listed target. For wasm32/arena, `all(target_arch="wasm32", fixture_allocator="arena")` is true, so the `cfg` attribute includes `compile_error!`; compilation fails for both feature states and all `P,D`. For every other tuple, that conjunction is false and the item is removed. Partial `arena-stop` output never reaches this stage. This proves effective rejection, rather than merely assuming the policy exclusion.

## API, invariant, and obligation coverage

The only crate public surface is safe `pub fn lane_id(u8)->NonZeroU8`. There are no fields, constructors beyond that function, traits/impls, statics, FFI, callbacks, exported macros, hidden APIs, dependencies, or mutable state. The only unsafe sites are its two configuration-complementary calls to `new_unchecked`. The required local proposition at either call is `NZ(value): value != 0`.

Let `B(c) = (f=on and t=aarch64-unknown-linux-gnu and a=arena)`. The two `cfg` predicates are literally `B` and `not(B)`, so exactly one block exists for every `c in C`; profile and debug state occur in neither selection nor proof.

* If `B(c)`, source calls `new_unchecked(value)` without a check. `NZ` holds exactly when `value!=0`. The comment “Burst-mode lane identifiers are never zero” is false as an invariant: the safe signature admits every `u8`, and no producer or boundary restricts it.
* If `not B(c)`, `value==0` reaches `panic!` before the unsafe call. Otherwise the exhaustive complement is `value!=0`, establishing `NZ`; `new_unchecked` is then permitted. The adjacent second safety comment states the controlling local fact and is correct.

### Exact maximal sound region

Over the requested complete product and inputs, define

`SOUND = {(c,x) in C×u8 | not(B(c) and x=0)}`.

`SOUND` is sound: partition on `B`; in `B`, its formula gives `x!=0`, and outside `B`, zero panics before unsafe while nonzero proves `NZ`. These cases exhaust `SOUND`. It is exact: its complement within `C×u8` is exactly `{(c,0) | c in C and B(c)}` by Boolean algebra. Every such tuple reaches `new_unchecked(0)`, whose checked contract says that is UB. Consequently any strict superset of `SOUND` within `C×u8` contains an unsound tuple; `SOUND` is the unique maximal region. This proof is parametric over every `p in P` and both `d in D`.

The universal soundness claim is therefore **UNSOUND**. A certificate is any supported `c` with aarch64 target, burst on, arena allocator, arbitrary profile/debug state, plus the well-typed safe call `lane_id(0)`: the first cfg block is selected, the unchecked call is executed, its required `value!=0` proposition is false, and its version-matched contract expressly entails UB.

For the documented “Panics when `value` is zero” postcondition, the exact proved region is `{c in C | not B(c)}`: the equality is true and `panic!` is reached before unsafe. In `B`, zero reaches UB instead. An execution containing UB cannot certify `CONTRACT-BROKEN`, and no independent UB-free non-panicking zero execution is established; hence the full postcondition is **UNPROVED**, not `CONTRACT-BROKEN`.

## Findings and remediation

**F-1 — UNSOUND, critical.** `src/lib.rs`'s aarch64/burst/arena safe branch has an unenforced nonzero precondition and a false safety comment. Minimum repair: perform the same zero check on that branch, or use checked `NonZeroU8::new(value)` and panic on `None`; then replace the comment with the actual dominating derivation. Making the safe function unsafe would be a breaking and unnecessary alternative. Re-audit the new snapshot and the panic claim.

**F-2 — postcondition UNPROVED.** The same region prevents a universal panic proof. F-1's checked repair also resolves it; wording alone cannot repair either result.

No tool-derived evidence or additional assumptions were used. Residual scope excludes manual rustc invocation, invented cfgs, overridden build scripts, unlisted targets/toolchains, and binary/backend correctness exactly as the policies require. Re-audit on any source, support product, Cargo/Rust/std identity, build interface, cfg, TCB disposition, or documentation-contract change.
