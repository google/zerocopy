# Source-only unsafe-code audit

## Claim, domain, and verdicts

Snapshot: the supplied `Cargo.toml`, `BUILD.md`, `SUPPORT.md`, `TCB.md`,
`build.rs`, and `src/lib.rs`; Rust and standard library 1.85.1, edition 2021.
No target was built, run, expanded, or modified. There are no dependencies or
generated source files. The only accepted non-Rust premise is
`BUILD-MAP-ORDERED` in the supplied `TCB.md`.

Let

- `T = {x86_64-unknown-linux-gnu, aarch64-unknown-linux-gnu,
  wasm32-unknown-unknown}`;
- `B = {off,on}` for `burst`, `A = {system,arena}`, `P` be every Cargo
  profile, `D = {off,on}` for debug assertions, and `U = {0,...,255}`;
- `Q = {1.85.1} × T × B × A × P × D`; and
- `L = Q \ {q | target(q)=wasm32-unknown-unknown ∧ allocator(q)=arena}`.

`Q` is the literal product in `SUPPORT.md`; the displayed subtraction is its
sole stated exclusion, so both containments establishing this normalization
follow directly from lines 3–16. Required library/API cases are `L × U`.
Profiles, debug assertions, and their panic strategies remain symbolic: no
source predicate or unsafe precondition depends on them.

**Soundness: UNSOUND** for the complete crate over the required source-level
domain, relative to `BUILD-MAP-ORDERED`. A valid witness is any profile/debug
state with target `aarch64-unknown-linux-gnu`, `burst=on`, allocator `arena`,
and the safe call `lane_id(0)`. This configuration is in `L`. The selected
block at `lib.rs:12–20` executes `NonZeroU8::new_unchecked(0)`. Its safety
condition is false and its exact 1.85.1 contract says this is undefined
behavior (AX-5 below). This completes the existential certificate.

**Documented postcondition: UNPROVED** globally. `lib.rs:8–10` promises that
`lane_id` “Panics when `value` is zero.” This is proved regionally whenever
`C(q) := burst(on) ∧ target=aarch64-unknown-linux-gnu ∧ allocator=arena` is
false: zero enters `lib.rs:28–30` and panics before unsafe code. In the `C`
region, zero instead reaches UB. That refutes soundness but cannot be a
`CONTRACT-BROKEN` witness because the execution is not UB-free as a whole; no
independent UB-free refutation is established.

### Exact maximal sound region

The exact maximal sound subset of the full supported configuration/input
domain is

`M = {(q,v) ∈ L × U | ¬(C(q) ∧ v=0)}`.

Proof of inclusion: if `C` is true and `v≠0`, `lib.rs:12–20` supplies the exact
nonzero precondition to `new_unchecked`. If `C` is false, the complementary
block at lines 22–33 is selected. For `v=0` it panics before the unsafe call;
for `v≠0`, falling through the check establishes the unsafe precondition.
These are the crate's only unsafe operations. Proof of maximality: the
complement of `M` inside `L×U` is exactly every profile/debug fiber satisfying
`C ∧ v=0`; the witness derivation above applies parametrically to every such
fiber. Thus every complement member is unsound and no strict superset within
`L×U` is sound.

## Ordered build-to-source relation

Write `R`, `S`, and `A` for the complete newline-terminated lines
`cargo::rerun-if-env-changed=FIXTURE_ALLOCATOR`,
`cargo::rustc-cfg=fixture_allocator="system"`, and
`cargo::rustc-cfg=fixture_allocator="arena"`. A failing `println!` panics at
that point. The supplied premises do not constrain bytes partially written by
the failing call; below, “prefix” means the exact earlier successfully written
complete directive-line prefix. This byte-level remainder is immaterial because
`BUILD-MAP-ORDERED` forbids a current library compilation after every
unsuccessful exit.

1. `build.rs:4` first attempts `R`. Failure exits by panic, with complete-line
   prefix `[]`; the environment read and all later operations are unreached.
   Success leaves prefix `[R]` and reaches `env::var`.
2. The literal key has neither `=` nor NUL. Rust's documented result therefore
   partitions raw values into omitted → `Err(NotPresent)`, Unicode `s` →
   `Ok(String(s))`, and non-Unicode → `Err(NotUnicode(_))`. `Result` and
   `VarError` each have exactly the variants matched at lines 6–25. `as_str`
   exposes the entire Unicode string; literal patterns match exactly and `_`
   matches every remainder.
3. Omitted and Unicode `system` each attempt `S`; Unicode `arena` attempts
   `A`. Failure of that second write exits at the `println!`, with prefix
   `[R]` (plus unconstrained failed-call bytes). Success leaves respectively
   `[R,S]` or `[R,A]`, then the function returns successfully. These are all
   successful paths, and each attempts exactly one allocator directive.
4. Unicode `arena-stop` attempts `A`. A write failure exits with prefix `[R]`
   and never reaches its explicit panic. A successful write leaves `[R,A]`,
   then line 19 explicitly panics. Unicode values other than the three named
   literals panic at line 21 with prefix `[R]` and never attempt an allocator
   line. Non-Unicode values do likewise at line 24. Together with first-write
   failure, these are every explicit/infrastructure rejection and every
   material exit.
5. Only the two successful prefixes are consumed downstream. By
   `BUILD-MAP-ORDERED`, successful `[R,S]` passes exactly
   `fixture_allocator="system"`; successful `[R,A]` passes exactly
   `fixture_allocator="arena"`. Every failed path produces no current library,
   irrespective of complete or partial stdout already emitted. No later Cargo
   cfg interpretation or library source selection is attributed to an earlier
   exit.

Freshness is closed, including the required sequence. A successful `arena`
build wrote `[R,A]`, so Cargo recorded the raw-variable invalidation rule.
Changing the same target directory's raw value to `arena-stop` is a
present-to-present change; `BUILD-MAP-ORDERED` makes the old selection stale
and reruns the script before current source selection. That run necessarily
ends at the first-write failure, second-write failure, or explicit panic.
The accepted premise says every such outcome compiles no current library and
does not present the prior arena library as the current result.

For a successful current script, the same premise maps `burst` and the three
target triples to their exact cfg leaves. Rust cfg semantics then make
`all(target_arch="wasm32", fixture_allocator="arena")` true exactly for the
stated excluded pair, independent of `burst`, profile, and debug assertions.
The encountered `compile_error!` at `lib.rs:3–4` rejects compilation. Conversely
that predicate is false for every member of `L`, so this error is absent. The
project's target/allocator exclusion is therefore **PROVED effectively
enforced**, and no excluded current library is produced.

## Boundary, invariant, and obligation coverage

The build-script entrypoint is safe Rust. The sole downstream public surface
is safe free function `lane_id(u8) -> NonZeroU8`; there are no public fields,
constructors beyond that function, user-implementable traits, exports, FFI,
statics, or generated/hidden APIs. The two cfg alternatives contain the only
unsafe calls (`lib.rs:19,32`). Invariant `NZ(value): value≠0` must hold at each
call. Lines 28–31 establish it on the ordinary path. The comment at line 18
merely asserts it on the burst path, but a safe `u8` parameter admits zero and
no producer, type, check, or accepted TCB entry establishes `NZ` there.

Obligation dispositions:

- build raw-value partition, operation order, successful outputs, failures,
  freshness, and Cargo interpretation: PROVED relative to `BUILD-MAP-ORDERED`;
- wasm/arena rejection and complementary source selection: PROVED;
- ordinary-path unsafe precondition and zero panic: PROVED;
- burst/aarch64/arena unsafe precondition: UNSOUND at zero, PROVED for nonzero;
- global documented zero-panic guarantee: UNPROVED, region as stated above.

## Rust authority and TCB log

All quotations and links are version 1.85.1 and apply to this exact toolchain.

- **AX-1 (environment/result).** [`env::var`](https://doc.rust-lang.org/1.85.1/std/env/fn.var.html):
  “Returns `VarError::NotPresent`” when unset and “Returns
  `VarError::NotUnicode` if the variable’s value is not valid Unicode.”
  [`VarError`](https://doc.rust-lang.org/1.85.1/std/env/enum.VarError.html) is
  `NotPresent | NotUnicode(OsString)`; [`Result`](https://doc.rust-lang.org/1.85.1/std/result/enum.Result.html)
  is `Ok(T) | Err(E)`. Consumers: build partition.
- **AX-2 (patterns/order).** [`String::as_str`](https://doc.rust-lang.org/1.85.1/std/string/struct.String.html#method.as_str)
  “Extracts a string slice containing the entire `String`.”
  [Literal patterns](https://doc.rust-lang.org/1.85.1/reference/patterns.html#literal-patterns)
  “match exactly the same value as what is created by the literal”; the
  [wildcard](https://doc.rust-lang.org/1.85.1/reference/patterns.html#wildcard-pattern)
  “matches any value.” A [block](https://doc.rust-lang.org/1.85.1/reference/expressions/block-expr.html)
  “sequentially executes its component non-item declaration statements and
  then its final optional expression.” Consumers: exhaustive ordered relation.
- **AX-3 (panic/output).** [`println!`](https://doc.rust-lang.org/1.85.1/std/macro.println.html)
  “Prints to the standard output, with a newline” and [“Panics if writing to
  `io::stdout` fails.”](https://doc.rust-lang.org/1.85.1/std/macro.println.html#panics)
  [`panic!`](https://doc.rust-lang.org/1.85.1/std/macro.panic.html) “Panics the
  current thread.” Consumers: build exits and zero postcondition.
- **AX-4 (selection/rejection).** The [cfg attribute](https://doc.rust-lang.org/1.85.1/reference/conditional-compilation.html#the-cfg-attribute)
  “conditionally includes the thing it is attached to based on a configuration
  predicate”; [`all` and `not`](https://doc.rust-lang.org/1.85.1/reference/conditional-compilation.html#conditional-compilation)
  mean respectively all predicates true and the predicate false.
  [`compile_error!`](https://doc.rust-lang.org/1.85.1/std/macro.compile_error.html)
  “causes compilation to fail with the given error message when encountered.”
  Consumers: exclusion and the complementary lane blocks.
- **AX-5 (integer/unsafe contract).** [`u8`](https://doc.rust-lang.org/1.85.1/std/primitive.u8.html)
  is “The 8-bit unsigned integer type,” with `MIN=0` and `MAX=255`.
  [`NonZero::new_unchecked`](https://doc.rust-lang.org/1.85.1/std/num/struct.NonZero.html#method.new_unchecked):
  “The value must not be zero” and zero “results in undefined behavior.”
  Consumers: `NZ`, witness, and maximal region.

**BUILD-MAP-ORDERED (accepted OUT-OF-BAND/IMPLEMENTATION premise):** exact Cargo
1.85.1 proposition in `TCB.md:8–39`, consumed only for rerun/freshness,
process-status handling, exact current allocator cfg, feature/target cfg, source
selection, and lack of a current/stale artifact after failure. It is not widened
to Rust semantics or source correctness. No other additional premise or tool
evidence is consumed.

## Findings and remediation

**F-1 — UNSOUND safe API.** `lib.rs:18` reverses an unsupported assertion into
the precondition of `new_unchecked`; callers control the safe `u8`. Minimal
repair: perform the zero check on every cfg path (prefer
`NonZeroU8::new(value).expect(...)`) and remove the invalid comment, or change
the API to accept `NonZeroU8` if contract compatibility permits. Re-audit the
new snapshot and its panic behavior.

**F-2 — deficient proof artifact/postcondition.** The line-18 SAFETY comment
does not identify an enforcing fact and the implementation cannot establish the
documented zero panic in that region without first avoiding UB. Repair F-1 and
use adjacent proof text: “`value == 0` panicked above; reaching this call proves
`value != 0`, satisfying `new_unchecked`.” Changing the safe API or panic
contract requires compatibility review.

Residual scope is source-level Rust only; compiler backend, binaries, and
deployment are not claimed. Re-audit on any source, policy, Cargo/Rust,
target/feature/allocator, cfg, TCB-disposition, or authoritative-contract change.
