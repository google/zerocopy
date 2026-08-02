# Source-only unsafe-code audit: supplied crate

**Cutoff:** 2026-08-01. **Snapshot:** the complete supplied `Cargo.toml`,
`build.rs`, `src/lib.rs`, `BUILD.md`, `SUPPORT.md`, and `TCB.md`; no generated
source, dependencies, lockfile, tests, or prior audit were supplied or used.
Rust, standard library, edition, and Cargo are exactly 1.85.1, 1.85.1, 2021,
and 1.85.1. This is a Rust-abstract-semantics result, not a compiler-binary or
platform theorem.

## Claims and verdicts

| Claim | Verdict | Certificate |
|---|---|---|
| Every well-typed safe use of the compiled public library is free of Rust UB over the supported domain | **UNSOUND** | F-1 gives a valid supported safe call, reaches `new_unchecked(0)`, falsifies its safety condition, and its contract says the result is UB. |
| `lane_id(value)` “Panics when `value` is zero” | **UNPROVED** | Proved on `not(K)` below. The only failing region executes UB, so it is not a UB-free `CONTRACT-BROKEN` witness. |
| Exact maximal sound API region | **PROVED** relative to `BUILD-MAP-ORDERED` | Both containments and maximality are proved below. |
| Ordered selector/rejection/freshness relation and wasm/arena source exclusion | **PROVED** relative to `BUILD-MAP-ORDERED` | Exhaustive staged relation below. |

The combined mandatory result is therefore **soundness UNSOUND; panic
postcondition UNPROVED**. No design change affects these current-snapshot
verdicts.

## Domain recovery

Let

* `T={x86_64-unknown-linux-gnu,aarch64-unknown-linux-gnu,wasm32-unknown-unknown}`;
* `B={off,on}` be `burst`, `A={system,arena}`, `P` any Cargo profile, `D` either
  debug-assertion state, and `v:u8` any safe API input;
* `C0=T×B×A×P×D`;
* `E(c) := target=wasm32-unknown-unknown ∧ allocator=arena`;
* `S := C0 ∖ E`, the supported compiled-library configurations; and
* `K(c) := burst=on ∧ target=aarch64-unknown-linux-gnu ∧ allocator=arena`.

This is an equality, not a sample: `SUPPORT.md` says “these target triples,”
“both states,” “both allocator models,” “exactly one exclusion,” and “every
other combination,” and explicitly quantifies every profile and both `D`
states. Thus every member of `S` is promised and every promised library
configuration is in `S`; there is no policy conflict. `Cargo.toml` independently
fixes the sole feature and toolchain. Profiles and `D` do not occur in a source
predicate or arithmetic operation, so every proof below is parametric over
their fibers.

The full required cases are (i) every supported Cargo build attempt for each
raw environment class and every possible relevant stdout success/failure
sequence, including required rejection outcomes, and (ii) every safe
`lane_id(v)` execution for `c∈S`. Manual `rustc`, invented cfgs, and build-script
overrides are expressly outside `BUILD.md`.

## Checked semantic authority

These are Rust 1.85.1 axioms, not extra project assumptions:

* [`env::var`](https://doc.rust-lang.org/1.85.1/std/env/fn.var.html) says it
  returns `NotPresent` when “The variable is not set” and `NotUnicode` when the
  value “is not valid Unicode.” [`VarError`](https://doc.rust-lang.org/1.85.1/std/env/enum.VarError.html)
  has exactly those two variants. The fixed key contains neither `=` nor NUL.
* A [block](https://doc.rust-lang.org/1.85.1/reference/expressions/block-expr.html)
  “sequentially executes its component non-item declaration statements,” and a
  [match](https://doc.rust-lang.org/1.85.1/reference/expressions/match-expr.html)
  compares arm patterns sequentially and chooses the first match. [Literal
  patterns](https://doc.rust-lang.org/1.85.1/reference/patterns.html#literal-patterns)
  “match exactly the value created by the literal”; the [wildcard](https://doc.rust-lang.org/1.85.1/reference/patterns.html#wildcard-pattern)
  “matches any value.” [`as_str`](https://doc.rust-lang.org/1.85.1/std/string/struct.String.html#method.as_str)
  extracts a slice containing the entire `String`.
* [`println!`](https://doc.rust-lang.org/1.85.1/std/macro.println.html#panics)
  “Panics if writing to `io::stdout` fails”; [`panic!`](https://doc.rust-lang.org/1.85.1/std/macro.panic.html)
  “Panics the current thread.”
* The [`cfg` attribute](https://doc.rust-lang.org/1.85.1/reference/conditional-compilation.html#the-cfg-attribute)
  conditionally includes its attached form from its predicate; [`all`/`not`](https://doc.rust-lang.org/1.85.1/reference/conditional-compilation.html#conditional-compilation)
  are true when all operands are true / their operand is false.
  [`compile_error!`](https://doc.rust-lang.org/1.85.1/std/macro.compile_error.html)
  “causes compilation to fail with the given error message.”
* The [comparison](https://doc.rust-lang.org/1.85.1/reference/expressions/operator-expr.html#comparison-operators)
  and [`if`](https://doc.rust-lang.org/1.85.1/reference/expressions/if-expr.html)
  rules make `value == 0` select its consequent exactly for zero.
* [`NonZero::new_unchecked`](https://doc.rust-lang.org/1.85.1/std/num/struct.NonZero.html#method.new_unchecked)
  says: “The value must not be zero,” and “This results in undefined behavior
  if the value is zero.”

Cargo's 1.85.1 documentation corroborates, but does not replace, the accepted
Cargo premise: build scripts communicate by `cargo::` lines on stdout
([life cycle](https://doc.rust-lang.org/1.85.1/cargo/reference/build-scripts.html#life-cycle-of-a-build-script));
`rustc-cfg` passes the value to compiler `--cfg`
([outputs](https://doc.rust-lang.org/1.85.1/cargo/reference/build-scripts.html#rustc-cfg));
and `rerun-if-env-changed` reruns when the named value changes
([freshness](https://doc.rust-lang.org/1.85.1/cargo/reference/build-scripts.html#rerun-if-env-changed)).
Process failure, current-output identity, and stale-artifact non-presentation
are consumed only in the narrower wording of accepted `BUILD-MAP-ORDERED`.

## Complete ordered build relation

Write `R` for the complete rerun line, `Sline` for the system cfg line, and
`Aline` for the arena cfg line. A failed `println!` may have emitted an
unspecified fragment `q` of that attempted output; no proof consumes `q`.

1. Every path first attempts `R`. Failure exits by uncaught panic with output
   `q`, performs no environment read, and produces no current library.
   Success leaves the complete prefix `[R]` and only then calls `env::var`.
2. The result partition is exhaustive: absent; Unicode `system`; Unicode
   `arena`; Unicode `arena-stop`; every other Unicode string (including empty);
   and non-Unicode. Absence and `system` next attempt `Sline`; `arena` and
   `arena-stop` next attempt `Aline`. Failure at any such second write exits by
   uncaught panic with `[R]·q` and no current library.
3. Successful absent/`system` writes yield exactly `[R,Sline]`, normal return,
   and exactly cfg `fixture_allocator="system"`. Successful `arena` yields
   exactly `[R,Aline]`, normal return, and exactly cfg
   `fixture_allocator="arena"`. These are the only successful selectors.
4. Successful `arena-stop` writes `[R,Aline]` and then explicitly panics.
   Other-Unicode and non-Unicode explicitly panic with exactly the completed
   directive prefix `[R]`, before attempting any allocator line. By
   `BUILD-MAP-ORDERED`, every unsuccessful process produces no current library
   even if a complete selector line was emitted; no prior selector is retained.

This includes every stdout failure point and every claim-relevant partial
prefix. The raw partition is exact by `env::var`/`VarError`, the four literal
arms, and the wildcard; it creates only the two allocator models.

On a successful selector, `BUILD-MAP-ORDERED` supplies exactly that allocator
cfg, maps `burst` and the three target triples to the named leaf cfgs, and
supplies no old selector. For `E`, the crate-level `all(wasm32,arena)` is true
for both feature states and `compile_error!` fails compilation. Conversely,
within `C0`, that conjunction is true only on `E`; hence the enforced exclusion
equals, rather than merely contains, the policy exclusion. All `S` cases reach
`lane_id` source.

**Freshness certificate.** A successful `arena` build necessarily completed
`R`. In the same target directory, changing the raw value to `arena-stop` is a
present-to-present change. The exact accepted premise therefore makes the old
selection stale and reruns the script before current selection. The rerun
either fails a write or completes `[R,Aline]` and panics; all alternatives are
unsuccessful, compile no current library, and cannot present the old arena
library as the current result.

## API, obligations, and exact maximal sound region

The boundary inventory is complete: the crate exports only the safe free
function `lane_id(u8)->NonZeroU8`. There are no public fields, constructors,
traits/impls, callbacks, FFI, reexports, hidden items, or generated APIs. Its
only unsafe operations are the two cfg-complementary `new_unchecked` calls.
There is no persistent invariant-bearing representation.

Cfg semantics makes the first block present exactly on `K` and the second
present exactly on `not(K)`; these predicates are complements, so exactly one
unsafe call exists in every `S` compilation.

Define

`M := {(c,v) ∈ S×u8 | ¬K(c) ∨ v≠0}`.

**`M` is sound.** If `¬K` and `v=0`, the equality is true and `panic!` is
executed before the unsafe call; panic is not UB. If `¬K` and `v≠0`, that
branch is skipped and the dominating comparison establishes the exact
`new_unchecked` precondition. If `K` and `v≠0`, the input itself establishes
that precondition. These cases exhaust `M`; profile, debug assertions, and
panic strategy do not alter selection or the precondition.

**Maximality/equality.** Inside `S×u8`, Boolean and integer case splitting gives
`(S×u8) ∖ M = {(c,0) | c∈S ∧ K(c)}`. Every such case reaches
`new_unchecked(0)`, whose required proposition is false and whose applicable
contract entails UB. Thus every point in `M` is sound and no point outside it
can be added: `M` is the exact maximal sound region. Over the pre-exclusion
product `C0×u8`, `E×u8` is rejected rather than a compiled API region; the
exact sound-or-rejected region is `(E×u8) ∪ M`.

For the panic postcondition, all `¬K,v=0` cases execute `panic!`. The
`K,v=0` cases instead enter UB. Under whole-execution classification they prove
neither that a panic occurs nor a UB-free failure to panic, so the universal
postcondition is **UNPROVED**, not `CONTRACT-BROKEN`.

## Finding F-1: unchecked zero in the special branch

* **Implementation:** **UNSOUND**; **proof artifact:** false/deficient.
* **Valid use:** successfully build supported `aarch64-unknown-linux-gnu` with
  raw `arena`, `burst` enabled, any profile/debug state, then safe-call
  `lane_id(0)`. Safe callers have no precondition.
* **Reachability:** all three leaves of `K` are true, so the special block calls
  `new_unchecked(0)`.
* **False proposition and consequence:** required `value≠0` is false; the
  version-matched contract explicitly entails UB.
* **Comment defect:** “Burst-mode lane identifiers are never zero” reverses no
  enforced producer contract and is contradicted by the public `u8` input.
* **Minimum repair:** perform the zero check before every cfg-dependent unsafe
  call (or use a checked constructor) and replace the comment with the
  dominating-check derivation. Re-audit `M` and the panic contract. Merely
  changing documentation cannot repair the safe API.

The fallback comment's local fact is correct: its zero branch dominates the
unsafe call. No other implementation or proof finding was found after the
complete surface/configuration inventory; this does not dilute F-1.

## TCB, residual scope, and triggers

The sole admitted project entry is `TCB.md` / **BUILD-MAP-ORDERED**, accepted
for exact Cargo 1.85.1 and only its stated execution, stdout-success,
freshness, process-status, feature, target-cfg, and selector-identity
propositions. Consumers are the staged relation, reachability, freshness, and
exclusion proof above. It supplies no Rust semantics or source correctness and
has not been widened. The Rust links above are authoritative axioms. There are
no dependency, tool-derived, external, probabilistic, deployment, or backend
premises and no test evidence.

Re-audit on any supplied source/policy/manifest change; Rust, std, Cargo, target,
feature, profile, cfg, allocator, environment interface, or TCB change; changed
authoritative wording; or any new public/unsafe surface. All requested source
and build outcomes were audited; binaries, actual compiler correctness,
platform execution, manual cfg injection, and target files not supplied are
outside scope.
