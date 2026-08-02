# Source-only unsafe-code audit

## Claim, domain, and verdicts

This audits the complete supplied crate snapshot: `Cargo.toml`, `build.rs`,
`src/lib.rs`, and `BUILD.md`, `SUPPORT.md`, and `TCB.md`. The theorem is
source-level Rust 1.85.1/edition 2021 freedom from undefined behavior for every
well-typed safe call to `lane_id`, plus the requested build/rejection and panic
contracts. It is relative only to accepted entry `BUILD-MAP-ORDERED`; no
backend or binary correctness is claimed.

Let

- `T = {x86_64-unknown-linux-gnu, aarch64-unknown-linux-gnu,
  wasm32-unknown-unknown}`;
- `B = {burst off, burst on}`, `A = {system, arena}`;
- `P` be every Cargo profile, `D = {debug assertions off, on}`, and
  `V = {0,...,255}` (the complete `u8` domain);
- `Supported(t,b,a,p,d) := t in T && b in B && a in A && p in P && d in D
  && !(t=wasm32-unknown-unknown && a=arena)`; and
- `C(t,b,a) := t=aarch64-unknown-linux-gnu && b=burst-on && a=arena`.

`SUPPORT.md` states exactly the product above and exactly its wasm/arena
exclusion. `Cargo.toml` fixes Rust 1.85.1, edition 2021, the empty/default or
enabled `burst` feature, and this build script/library. `BUILD.md` makes the
allocator a generated cfg from an accepted raw selector. These sources agree;
normalizing their conjunction gives `Supported` in both directions. Rejected
raw values are required build-interface cases, not extra library
configurations. Profiles and debug assertions do not occur in either library
cfg predicate or in its value test, so the proofs below are parametric in
`p,d`. There are no dependencies or other generated files.

| Claim | Verdict | Certificate |
|---|---|---|
| Ordered raw-selector/build relation, including freshness | **PROVED**, relative to `BUILD-MAP-ORDERED` | Complete path partition below |
| Required wasm32/arena exclusion | **PROVED** | `cfg` plus `compile_error!` proof below |
| Safe-API soundness over `Supported x V` | **UNSOUND** | Every `C && value=0` safe call reaches documented UB |
| Soundness on `M := {(q,value): Supported(q) && (!C(q) || value!=0)}` | **PROVED** | Exhaustive cfg/input partition below |
| “Panics when `value` is zero” over all `Supported` | **UNPROVED**, not `CONTRACT-BROKEN` | Proved for `!C`; the only remaining executions have UB, so they cannot be postcondition counterexamples |

Thus the combined full-domain result is **UNSOUND** for soundness and
**UNPROVED** for the documented panic postcondition.

## Exact ordered build relation

Write `R` for the complete line
`cargo::rerun-if-env-changed=FIXTURE_ALLOCATOR`, `S` for
`cargo::rustc-cfg=fixture_allocator="system"`, and `A` for the analogous
`"arena"` line.

The function body executes its statements in order. First it attempts `R`.
If that write fails, `println!` panics: for every raw environment class the
script exits unsuccessfully before reading/classifying the variable, with no
successfully written complete directive guaranteed (an incomplete byte prefix
of the failing line is immaterial). If `R` succeeds, the complete relation is:

| Raw `FIXTURE_ALLOCATOR` class | Classification and next action | Complete emitted prefix and exit |
|---|---|---|
| omitted | `Err(NotPresent)`; attempt `S` | `R,S`, normal success if the write succeeds; otherwise `R` plus at most an incomplete failing line, `println!` panic |
| Unicode `system` | `Ok`; `as_str`; `"system"` arm; attempt `S` | same two outcomes as omitted |
| Unicode `arena` | `Ok`; `"arena"` arm; attempt `A` | `R,A`, normal success; or `R` plus at most an incomplete failing line, `println!` panic |
| Unicode `arena-stop` | `Ok`; matching arm; attempt `A`, then explicit `panic!` | if write succeeds: `R,A`, explicit panic; if it fails: `R` and `println!` panic before the explicit panic |
| every other Unicode value | `Ok`; wildcard arm | `R`, explicit panic; no allocator write attempted |
| every non-Unicode value | `Err(NotUnicode(_))` | `R`, explicit panic; no allocator write attempted |

These are all raw classes, both stdout sites, all successful paths, all
explicit rejections, and all material complete prefixes. The successful
mapping is exactly `omitted|system -> system` and `arena -> arena`. The
`arena-stop` emitted allocator line never belongs to a successful execution.

The accepted `BUILD-MAP-ORDERED` premise is consumed only as follows: a
successfully written current `R` makes any later raw-value change stale; a
successfully written allocator line is passed as that exact cfg only when the
current script succeeds; current success receives no retained old selector;
any write panic or explicit panic is an unsuccessful process and yields no
current library; Cargo does not substitute an old library after a stale failed
build; and `burst`/the three target triples set the exact named cfgs. Emitted
text and ordering above are proved from source, not assumed by that entry.

Consequently, after a successful `arena` build, `R` necessarily was written.
Changing the same target directory to present value `arena-stop` is the
entry's present-to-present change: Cargo reruns before selecting a library.
The rerun fails at `R`, at `A`, or after successful `A`; every case is
unsuccessful, and neither its prefix nor the prior arena artifact is a result
of the current build. The freshness canary is therefore **PROVED**.

## Version-matched Rust axioms

The following are the material Rust 1.85.1 propositions; Cargo behavior above
comes only from the separately accepted project TCB entry.

- [`env::var`](https://doc.rust-lang.org/1.85.1/std/env/fn.var.html) says:
  “Returns an `Err` if the variable is not present, or if it is not valid
  Unicode.” [`VarError`](https://doc.rust-lang.org/1.85.1/std/env/enum.VarError.html)
  distinguishes `NotPresent` from `NotUnicode(OsString)`.
- [`String::as_str`](https://doc.rust-lang.org/1.85.1/std/string/struct.String.html#method.as_str)
  “Extracts a string slice containing the entire `String`.” The
  [match-expression rule](https://doc.rust-lang.org/1.85.1/reference/expressions/match-expr.html)
  says: “The first arm with a matching pattern is chosen as the branch target
  of the match.” [Literal patterns](https://doc.rust-lang.org/1.85.1/reference/patterns.html#literal-patterns)
  match the literal's value; the [wildcard](https://doc.rust-lang.org/1.85.1/reference/patterns.html#wildcard-pattern)
  “matches any value.”
- [Block expressions](https://doc.rust-lang.org/1.85.1/reference/expressions/block-expr.html)
  “sequentially execute their component non-item declaration statements.”
  [`println!` failure](https://doc.rust-lang.org/1.85.1/std/macro.println.html#panics)
  “Panics if writing to `io::stdout` fails”; [`panic!`](https://doc.rust-lang.org/1.85.1/std/macro.panic.html)
  “Panics the current thread.”
- A [`cfg` attribute](https://doc.rust-lang.org/1.85.1/reference/conditional-compilation.html#the-cfg-attribute)
  includes its attached form iff its predicate is true; if false, “the thing
  is removed from the source code.” [`compile_error!`](https://doc.rust-lang.org/1.85.1/std/macro.compile_error.html)
  “Causes compilation to fail with the given error message when encountered.”
- The [`if` rule](https://doc.rust-lang.org/1.85.1/reference/expressions/if-expr.html)
  executes the consequent when its Boolean condition is true; the
  [comparison rule](https://doc.rust-lang.org/1.85.1/reference/expressions/operator-expr.html#comparison-operators)
  makes `==` a value equality test. The [`u8` page](https://doc.rust-lang.org/1.85.1/std/primitive.u8.html)
  records `MIN = 0` and `MAX = 255`.
- Most importantly, [`NonZero::new_unchecked`](https://doc.rust-lang.org/1.85.1/std/num/struct.NonZero.html#method.new_unchecked)
  states: “This results in undefined behavior if the value is zero.” Its
  Safety clause is: “The value must not be zero.”

## Configuration exclusion and selected source

On target `wasm32-unknown-unknown` after a successful arena selector,
`BUILD-MAP-ORDERED` supplies `target_arch="wasm32"` and exactly
`fixture_allocator="arena"`. Both operands of the source `all(...)` are true,
so the `compile_error!` item is included and compilation fails. This is
independent of `burst`, profile, and debug assertions. Hence the excluded pair
cannot produce a current library. For system on wasm32, and for either
allocator on the two other targets, that predicate is false and this error item
is removed. The project's sole exclusion is exactly enforced.

## API, obligations, and maximal sound region

The only language-reachable crate API is safe free function
`pub fn lane_id(u8) -> NonZeroU8`. There are no public fields, crate-owned
representation, traits/impls, methods, statics, macros, reexports, hidden
items, callbacks, or FFI. There is no persistent invariant; each unsafe call
locally consumes the sole obligation `value != 0`.

The two complementary cfg blocks form an exhaustive partition:

1. If `C`, the first block is included and the `not(all(...))` block removed.
   Every input immediately reaches `new_unchecked(value)`. For `value in
   1..=255`, its sole safety precondition holds. For `value=0`, it is false and
   the cited standard-library contract entails UB.
2. If `!C`, the first block is removed and the second included. At `value=0`,
   equality is true and `panic!` executes before the unsafe call. At every
   `value in 1..=255`, that branch is not taken and the exact same value reaches
   `new_unchecked`, satisfying its safety clause.

This proves every point of
`M = Supported x V intersect (!C or value!=0)`. Conversely,
`(Supported x V) \ M` is exactly `C && value=0`, for every profile and debug
assertion state. Calling this public safe function with zero is a valid
well-typed in-scope use; cfg selection reaches the unsafe call; its required
proposition is false; and the version-matched contract states the UB
consequence. Every omitted point is therefore unsound, proving both the
full-domain **UNSOUND** certificate and the exact maximality of `M`.

For the documented postcondition, every `!C,value=0` execution reaches
`panic!`, so that region is proved. At `C,value=0` the whole execution has UB.
It cannot be a `CONTRACT-BROKEN` witness, which must be UB-free; absent an
independent UB-free witness, the full postcondition is **UNPROVED**.

## Finding and proof-artifact quality

**F-1 (critical, UNSOUND).** The special-path comment, “Burst-mode lane
identifiers are never zero,” is not derived from a check, type, invariant, or
unsafe caller contract. `value` is an unrestricted public `u8`, so zero is a
counterexample. The minimum repair is to validate zero on that path (or remove
the specialization and use the already checked path), then replace the comment
with a proof citing that dominating check and exact value. Changing prose alone
cannot repair the safe API. The ordinary-path comment correctly identifies the
dominating zero branch, though the derivation above supplies its complete
versioned contract basis. Any code repair is a new snapshot requiring re-audit.

## TCB, residual scope, and triggers

TCB log identity is the supplied `TCB.md`, entry `BUILD-MAP-ORDERED`, accepted
for Cargo 1.85.1 and only its stated freshness, process-status, feature, target,
and cfg propositions. Its exclusions (emitted source text/order, Rust
semantics, source correctness, backend, binary) were not widened. No other
assumption, dependency, tool result, test, build, or prior audit was consumed.

Excluded from the theorem are manual `rustc`, invented cfgs, build-script
override, unsupported targets, and binary/backend correctness. Re-audit is
required for any source/policy/manifest change; Cargo/Rust or documentation
change; target, feature, allocator, profile, or environment-interface change;
generated-cfg/build-order change; or altered TCB disposition.

**Final attestation:** every source/API/build/configuration/postcondition
obligation has a disposition; `Required` and `M` are symbolic and closed; the
unsoundness witness is complete; no testing or absence-of-counterexample claim
is used.
