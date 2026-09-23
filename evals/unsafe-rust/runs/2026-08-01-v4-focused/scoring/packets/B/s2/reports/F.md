# Unsafe Rust audit: `ordered-build-target`

## Claim, snapshot, and verdicts

This is a source-only audit of the complete supplied snapshot: `Cargo.toml`,
`build.rs`, `src/lib.rs`, `BUILD.md`, `SUPPORT.md`, `TCB.md`, and `REQUEST.md`.
No build, execution, test, or expansion was used. The theorem is for Rust/Cargo
1.85.1, edition 2021, at the 2026-08-01 cutoff; it makes no backend or binary
claim. `BUILD-MAP-ORDERED` in the supplied `TCB.md` is the accepted TCB
revision. No dependency, tool-result, or additional implementation premise is
consumed.

| Claim | Verdict | Certificate |
|---|---|---|
| Every well-typed safe call to `lane_id` in every supported current library is free of Rust UB | **UNSOUND** | F-01 gives a valid safe call, reachability, false unsafe precondition, and authoritative UB consequence. |
| Documented postcondition “Panics when `value` is zero” over every supported library configuration | **UNPROVED** | Proved outside the exceptional configuration; its only zero execution has UB, so it cannot prove `CONTRACT-BROKEN`. |
| Ordered selector mapping, rejection, and `arena`→`arena-stop` freshness | **PROVED relative to `BUILD-MAP-ORDERED`** | B-01/B-02 below. |
| Required wasm32/arena exclusion | **PROVED** | B-03: the selected source necessarily fails compilation. |

The combined mandatory result is therefore **UNSOUND** for soundness and
**UNPROVED** for the panic postcondition, not `CONTRACT-BROKEN`.

## Exact theorem domain

Let

* `T={x86_64-unknown-linux-gnu,aarch64-unknown-linux-gnu,wasm32-unknown-unknown}`;
* `F={off,on}` be `burst`; `A={system,arena}`; `P` be every Cargo profile; and
  `D={off,on}` be debug assertions;
* `Q = T×F×A×P×D \ { (wasm32-unknown-unknown,f,arena,p,d) }`; and
* `U` be every value of type `u8`.

This is an equality normalization of `SUPPORT.md`: it states exactly those
three targets, both feature and allocator states, every profile and both debug
assertion states, then removes exactly wasm32/arena for either feature. The
manifest fixes Rust 1.85.1/edition 2021 and declares only `burst`. `BUILD.md`
defines allocator selection. There is no policy conflict and no release
interval to extrapolate. Raw environment classes rejected below are build
interface cases, not extra members of `A`. Profiles/debug assertions do not
occur in the source predicates or arithmetic, so the proofs are parametric in
`P,D`.

Write
`C(q) := (F=on ∧ T=aarch64-unknown-linux-gnu ∧ A=arena)`.
The **exact maximal sound region** over the requested full product is

`S = { (q,v) ∈ Q×U | ¬C(q) ∨ v≠0 }`.

The proof of both inclusion and maximality appears under S-01/S-02.

## B-01: complete ordered build relation

Let `R`, `L_s`, and `L_a` denote the newline-terminated rerun, system-cfg, and
arena-cfg lines literally present in `build.rs`. Let `p(X)` mean whatever bytes,
if any, a failed attempt to print `X` emitted; it may be empty or include a
complete line. Its exact bytes are immaterial because the accepted TCB says any
stdout-write failure is an unsuccessful script and supplies no current library.

For **every** raw class, the first event is an attempt to print `R`. If it
fails, execution stops by `println!` panic with output `p(R)`; the environment
is not read, and there is no library. If it succeeds, the remaining exhaustive
relation is:

| Raw `FIXTURE_ALLOCATOR` class | Events after `R`, in order | Output/exit | Current result |
|---|---|---|---|
| omitted | `env::var` gives `NotPresent`; attempt `L_s` | failure: `R+p(L_s)`, write panic; success: `R+L_s`, normal return | none on failure; exactly cfg `fixture_allocator="system"` and library attempt on success |
| Unicode `system` | `Ok`; `as_str`; literal arm; attempt `L_s` | same two outcomes | same |
| Unicode `arena` | `Ok`; `as_str`; literal arm; attempt `L_a` | failure: `R+p(L_a)`, write panic; success: `R+L_a`, normal return | none on failure; exactly cfg `fixture_allocator="arena"` and library attempt on success |
| Unicode `arena-stop` | `Ok`; literal arm; attempt `L_a`; if successful, explicit `panic!` | `R+p(L_a)`, write panic, or `R+L_a`, explicit panic | none in either case |
| every other Unicode value | `Ok`; wildcard arm; explicit `panic!`; no selector attempt | `R`, unsuccessful | none |
| every non-Unicode value | `NotUnicode`; explicit `panic!`; no selector attempt | `R`, unsuccessful | none |

Thus the only normal exits are omitted/system→system and arena→arena, each
after exactly two successful stdout writes. `BUILD-MAP-ORDERED` is consumed
literally: a successful current script gives the library exactly its current
selector directive and no retained selector; an unsuccessful script gives no
current compilation or stale result. It also supplies the requested feature
and target cfg mapping. The source-level ordering/partition follows from the
arms at `build.rs:4-25`; no endpoint-only inference is used.

## B-02: freshness certificate

Assume a successful `arena` build in target directory `X`. Its successful `R`
records the raw variable dependency and its `L_a` selects arena. Changing the
present value to `arena-stop` makes that result stale under
`BUILD-MAP-ORDERED`, so Cargo reruns the script before current selection. The
rerun has exactly three possibilities: first write failure (`p(R)`), second
write failure (`R+p(L_a)`), or both writes followed by the explicit panic
(`R+L_a`). Every possibility exits unsuccessfully. The accepted premise says
none compiles a current library or presents the earlier arena library as this
build's result. The requested reuse sequence therefore rejects exactly as
documented.

## B-03: source exclusion and source selection

On target wasm32 with a successful arena selector, the accepted TCB supplies
both `target_arch="wasm32"` and `fixture_allocator="arena"`. The first cfg in
`src/lib.rs` therefore includes `compile_error!` for either feature, profile,
or debug state, and compilation fails. Hence every and only listed
target/allocator exclusion is effectively rejected; no current library API is
produced.

For every `q∈Q`, cfg processing selects exactly one `lane_id` body:

* if `C(q)`, lines 13-22 include the immediate unchecked return and lines
  24-37 are absent;
* if `¬C(q)`, the first block is absent and the second checks zero before its
  unchecked constructor.

The public safe surface is exactly `pub fn lane_id(u8)->NonZeroU8`. There are no
public fields, unsafe APIs/traits/impls, callbacks, exported macros, hidden
items, FFI, dependencies, or invariant-bearing stored state. The standard
macros are consumers of documented standard behavior, not generated public
surface.

## Unsafe-operation and postcondition ledger

**S-01 (`¬C`).** If `v=0`, the equality test enters `panic!` before unsafe code.
If `v≠0`, the dominating test establishes the sole precondition of
`NonZeroU8::new_unchecked(v)`; it returns a valid nonzero value. The adjacent
safety comment is an adequate local proof. This proves UB freedom for all
`P,D` and proves the zero-panic postcondition.

**S-02 (`C`).** If `v≠0`, the unsafe constructor's sole precondition holds, so
this region is sound. If `v=0`, F-01 proves UB. Since zero/nonzero and
`C/¬C` are exhaustive, every point of `S` is proved sound and every point of
`(Q×U)\S` is proved unsound. Consequently no strict superset of `S` within
`Q×U` is sound: this establishes exact maximality, not merely a positive
remainder.

**POST-01.** The documented implication `v=0 ⇒ lane_id(v) panics` is proved for
`¬C`. For `C,v=0`, the execution reaches UB before a defined return or panic
can be certified. Under the required whole-execution rule, that execution
cannot witness `CONTRACT-BROKEN`; no independent UB-free refutation exists in
this source. The full-product postcondition is therefore `UNPROVED`.

## F-01 — unchecked zero behind a safe API

* **Status:** soundness **UNSOUND**; proof artifact deficient.
* **Valid use:** choose any `p∈P,d∈D`, target aarch64, `burst=on`, allocator
  arena, and call the public safe `lane_id(0)`. This point belongs to `Q×U` and
  requires no caller safety obligation.
* **Reachability:** `C` includes lines 13-22 and the function immediately calls
  `NonZeroU8::new_unchecked(0)`.
* **False proposition:** that unsafe function requires a nonzero argument; zero
  falsifies it.
* **UB consequence:** the exact standard-library contract states that zero
  causes UB, independently confirmed by the Reference invalid-value rule.
* **Proof defect:** “Burst-mode lane identifiers are never zero” reverses no
  enforced constructor invariant and is false for caller-controlled `u8`.
* **Minimum repair:** make a dominating `value==0` panic check apply to the
  exceptional block (or remove that block), then re-audit all cfg cases. Merely
  editing the comment cannot repair the safe API.

## Rust axioms and TCB audit

The material Rust 1.85.1 propositions were checked against these narrowly
scoped authorities:

* [`env::var`](https://doc.rust-lang.org/1.85.1/std/env/fn.var.html) “returns an
  error if the environment variable is not set, or if the value is not valid
  Unicode”; [`String::as_str`](https://doc.rust-lang.org/1.85.1/std/string/struct.String.html#method.as_str)
  “Extracts a string slice containing the entire `String`.”
* [Block expressions](https://doc.rust-lang.org/1.85.1/reference/expressions/block-expr.html)
  sequentially execute component statements; [match](https://doc.rust-lang.org/1.85.1/reference/expressions/match-expr.html)
  “branches on a pattern.” These ground the source order, while `BUILD.md`
  supplies the claimed complete raw partition.
* [`println!`](https://doc.rust-lang.org/1.85.1/std/macro.println.html) “Prints
  to the standard output, with a newline,” and its [panic contract](https://doc.rust-lang.org/1.85.1/std/macro.println.html#panics)
  says it panics if stdout writing fails. [`panic!`](https://doc.rust-lang.org/1.85.1/std/macro.panic.html)
  “Panics the current thread.”
* The [cfg attribute](https://doc.rust-lang.org/1.85.1/reference/conditional-compilation.html#the-cfg-attribute)
  conditionally includes its attached construct according to its predicate;
  [`compile_error!`](https://doc.rust-lang.org/1.85.1/std/macro.compile_error.html)
  “Causes compilation to fail with the given error message when encountered.”
  The [equality operators](https://doc.rust-lang.org/1.85.1/reference/expressions/operator-expr.html#comparison-operators)
  are equality/inequality tests, and an [if expression](https://doc.rust-lang.org/1.85.1/reference/expressions/if-expr.html)
  executes its consequent when its boolean condition is true.
* [`NonZero::new_unchecked`](https://doc.rust-lang.org/1.85.1/std/num/struct.NonZero.html#method.new_unchecked):
  “The value must not be zero” and “This results in undefined behavior if the
  value is zero.” The [Reference](https://doc.rust-lang.org/1.85.1/reference/behavior-considered-undefined.html)
  says producing an invalid value is immediate UB and names `NonZero` as a type
  with a custom valid range.

`BUILD-MAP-ORDERED` is accepted only for: Cargo 1.85.1 execution; successful
rerun-line freshness including present-to-present changes; exact current
successful cfg-line interpretation with no retained selector; no library/stale
result after unsuccessful script exit; main-thread panic as unsuccessful; and
the named feature/target cfgs. Consumers are B-01–B-03 and source reachability.
No claim about emitted strings, source correctness, Rust semantics, backend, or
binary is imported. Its stated trigger—any Cargo/toolchain, manifest, script,
environment, target, source-cfg, or disposition change—requires re-audit;
source/API/docs/support changes likewise do.

## Residual scope and attestation

Manual rustc, invented cfgs, build-script override, unsupported targets, and
rejected raw values producing a library are outside the theorem exactly as
`BUILD.md` states. Rejected build executions and wasm32/arena have no API point
and are not counted as vacuously sound members of `S`. Every discovered build,
configuration, safe-surface, unsafe-operation, and requested postcondition
obligation has a status above; there is no sampled evidence or unresolved
supported configuration remainder.
