# V4 Focused Oracle — Ordered, Fallible Build Relation

> **Evaluator-only material.** Never expose this file, its atoms, formulas,
> expected verdicts, hard errors, or authority inventory to a report agent.

## Scoring Rules

Score the proposition of each atom, not its notation or presentation. Accept an
explicit equivalent derivation. Do not infer an omitted build stage, failure
edge, source-selection step, or semantic premise from an endpoint summary.
Failure of an atom is not itself a hard error unless the report also makes the
false affirmative claim identified below.

This fixture deliberately requests a maximal positive region. That request,
not a general audit convention, makes exactness and maximality part of B13.
There is no scoring requirement for incidental diagnostics, exact panic text,
partially written bytes within one failed `println!`, or build-script stdout
which does not affect a current library selection.

## Intended Domain and Build Relation

Let:

```text
R = { Rust and Cargo 1.85.1 }
T = { X = x86_64-unknown-linux-gnu,
      A = aarch64-unknown-linux-gnu,
      W = wasm32-unknown-unknown }
F = { burst-off, burst-on }
L = { system, arena }
P = every Cargo profile supported by the fixture
D = { debug-assertions-off, debug-assertions-on }
I = { i | i is any u8 }

Config(t,f,l,p,d)
  iff t in T and f in F and l in L and p in P and d in D
      and not (t = W and l = arena).

Required = R cross Config cross I.
Q(t,f,l) iff t = A and f = burst-on and l = arena.
```

Both allocator values in `Config` are reachable through the supported Cargo
interface: an omitted selector or `system` selects `system`, and `arena`
selects `arena`. Raw rejected selector values and unsuccessful build attempts
are build-relation cases that must be accounted for, but they do not add a
library configuration to `Required`.

For compactness, use these local operations:

```text
RERUN  = attempt println!("cargo::rerun-if-env-changed=FIXTURE_ALLOCATOR")
READ   = evaluate env::var("FIXTURE_ALLOCATOR")
SYS    = attempt println!("cargo::rustc-cfg=fixture_allocator=\"system\"")
ARENA  = attempt println!("cargo::rustc-cfg=fixture_allocator=\"arena\"")
PANIC  = the selected explicit panic, or the panic caused by a failed println!
RETURN = successful return from main
```

The complete claim-relevant local relation is:

```text
missing:          RERUN -> READ(NotPresent) -> SYS   -> RETURN
Unicode system:   RERUN -> READ(Ok(system)) -> SYS   -> RETURN
Unicode arena:    RERUN -> READ(Ok(arena))  -> ARENA -> RETURN
Unicode arena-stop:
                  RERUN -> READ(Ok(arena-stop)) -> ARENA -> PANIC
other Unicode:    RERUN -> READ(Ok(other)) -> PANIC
non-Unicode:      RERUN -> READ(NotUnicode) -> PANIC
```

Every arrow after a `println!` assumes that write succeeds. If `RERUN` fails,
it panics before `READ`, and no complete earlier directive is required. If
`SYS` or `ARENA` fails, `RERUN` is the material completed prefix and the script
panics before `RETURN` or the explicit `arena-stop` panic. If `ARENA` succeeds
on `arena-stop`, the material completed prefix is `[RERUN, ARENA]`, followed by
the explicit panic. Under exact accepted entry `BUILD-MAP-ORDERED`, every panic is an
unsuccessful script exit and produces no current library compilation,
regardless of completed prefix.

On the three successful selector paths, `BUILD-MAP-ORDERED` interprets the final
allocator line as exactly one matching library cfg. Cargo's accepted feature
and target mappings, followed by the Rust conditional-compilation rules,
select the library source. The `W`/`arena` combination selects
`compile_error!`, so it does not produce a library and is genuinely outside
`Config`. The supported `Q` cell selects the first `lane_id` body and removes
the complementary checked body.

A prior successful `arena` build necessarily completed `RERUN` before
`ARENA`. After the raw selector changes to `arena-stop`, `BUILD-MAP-ORDERED` makes
that prior selection stale, reruns the script, and refuses to present the old
library as the result of the current unsuccessful execution. Thus the
freshness canary is an effective rejection even though its current output
prefix includes the same arena cfg line.

## Expected Source Results

The exact maximal sound region requested by the target is:

```text
SoundRegion = { case in Required | not Q(case) or case.i != 0 }.
```

Outside `Q`, the selected body panics when `i == 0`; reaching
`new_unchecked(i)` therefore implies `i != 0`. Inside `Q`, the selected body
calls `new_unchecked` without a check, so nonzero inputs are sound and zero is
not. The complement of `SoundRegion` within `Required` consists exactly of
`Q` with `i == 0` (for every supported profile and debug-assertion state).

The safe call `lane_id(0)` in any `Q` case reaches
`NonZeroU8::new_unchecked(0)`. Its exact safety proposition is false, and the
Rust 1.85.1 standard-library contract states that zero produces undefined
behavior. Safe-API soundness over all of `Required` is therefore **UNSOUND
relative to `BUILD-MAP-ORDERED`**.

For the documented zero-input panic postcondition:

```text
RequiredPanic = { case in Required | case.i = 0 }
CoveredPanic  = { case in RequiredPanic | not Q(case) }.
```

The regional theorem over `CoveredPanic` is **PROVED relative to
`BUILD-MAP-ORDERED`**. The whole `RequiredPanic` theorem is **UNPROVED**, not
`CONTRACT-BROKEN`: the only missing cases are executions already shown to
contain UB, so their apparent absence of an earlier panic is not a defined
behavioral counterexample.

## Atoms

- **B1 — Exact supported case predicate:** The report states a predicate
  equivalent to `Required`, including Rust/Cargo 1.85.1, all three targets,
  both feature states, both allocator models, every supported Cargo profile,
  both debug-assertion states, every `u8`, and only the `W`/`arena` policy
  exclusion.
  - `scope_basis`: `Cargo.toml`, `SUPPORT.md`, and `BUILD.md`.
  - `dependencies`: none; this is the theorem root.
  - `accepted_alternatives`: symbolic products or a proved equivalent partition; no
  Cartesian enumeration is required.
  - `hard_errors`: omission
  alone fails B1; claiming a whole-domain affirmative result over a contracted
  predicate triggers BH1.

- **B2 — Exhaustive raw-selector partition:** The report proves that the raw
  environment domain is exactly missing, Unicode `system`, Unicode `arena`,
  Unicode `arena-stop`, every other Unicode string, and every non-Unicode
  value, with no seventh `env::var` outcome.
  - `scope_basis`: `BUILD.md`, the
  exact `env::var`/`VarError` contracts, and the outer and inner matches.
  - `dependencies`: independent of B1; it supplies the cases used
  by B3–B7.
  - `accepted_alternatives`: any disjoint exhaustive partition that
  preserves these behaviorally distinct classes.
  - `hard_errors`:
  omission alone fails B2; calling an incomplete partition complete and using
  it for build closure triggers BH2.

- **B3 — Complete system-success trace:** Conditional on its two writes
  succeeding, each of the missing and Unicode-`system` classes follows exactly
  `RERUN -> READ -> SYS -> RETURN`; it emits no arena cfg.
  - `scope_basis`: the
  ordered statements, `env::var`, match/pattern semantics, `String::as_str`,
  and `println!`.
  - `dependencies`: B2 identifies the two raw cases;
  this is a local-source proposition and does not consume Cargo mapping.
  - `accepted_alternatives`: combine the two classes after proving their
  identical trace.
  - `hard_errors`: omission alone fails B3; an
  incompatible endpoint used for closure triggers BH2.

- **B4 — Complete arena-success trace:** Conditional on its two writes
  succeeding, Unicode `arena` follows exactly
  `RERUN -> READ -> ARENA -> RETURN`; it emits no system cfg.
  - `scope_basis`:
  the same local Rust contracts as B3.
  - `dependencies`: B2; this
  trace is the reachability root for B8–B12.
  - `accepted_alternatives`: an
  equivalent state-transition row or prose proof.
  - `hard_errors`:
  omission alone fails B4; an incompatible endpoint used for closure triggers
  BH2.

- **B5 — `arena-stop` partial-prefix exit:** With successful writes, Unicode
  `arena-stop` follows exactly
  `RERUN -> READ -> ARENA -> PANIC`, so `[RERUN, ARENA]` is a completed output
  prefix but the script does not return successfully and, under
  `BUILD-MAP-ORDERED`, produces no current library compilation.
  - `scope_basis`:
  `BUILD.md`, local match/`println!`/`panic!` semantics, and only the exact
  unsuccessful-exit proposition of `BUILD-MAP-ORDERED`.
  - `dependencies`:
  B2; this is distinct from a failed allocator write in B7.
  - `accepted_alternatives`: notation may differ, but both ordered lines, the later panic,
  and no-current-library consequence must appear.
  - `hard_errors`:
  omission alone fails B5; treating the partial arena line as a current
  successful selector triggers BH4.

- **B6 — Pre-allocator rejection traces:** Every other Unicode value and every
  non-Unicode value follows `RERUN -> READ -> PANIC` after a successful rerun
  write, so `[RERUN]` is its completed directive prefix; it attempts no
  allocator cfg and produces no current library compilation under
  `BUILD-MAP-ORDERED`.
  - `scope_basis`: the wildcard and `NotUnicode` arms plus
  the exact build premise.
  - `dependencies`: B2; the two classes may
  share an outcome only after both are accounted for.
  - `accepted_alternatives`:
  separate rows or one proved union.
  - `hard_errors`: omission alone
  fails B6; treating either class as an accepted allocator/configuration
  triggers BH5.

- **B7 — Stdout-failure edges:** The report accounts for failure of every
  claim-relevant `println!`: failed `RERUN` panics before `READ`; failed `SYS`
  or `ARENA` panics with completed prefix `[RERUN]`; and all such unsuccessful
  exits produce no current library compilation under `BUILD-MAP-ORDERED`. It does
  not require atomic line writes or assign meaning to an incomplete line.
  - `scope_basis`: the exact `println!` Panics section, source order,
  `panic!`'s main-thread result, and the accepted process-status proposition.
  - `dependencies`: B3–B5 identify allocator-write sites; B7 is the
  failure completion of those traces.
  - `accepted_alternatives`: a single
  quantified failure rule is preferred and passes if its instantiations are
  readily checkable.
  - `hard_errors`: omission alone fails B7;
  claiming complete build coverage while a material failure edge supplies a
  contrary current artifact triggers BH2 or BH4 as applicable.

- **B8 — Successful Cargo-to-source selector mapping:** Only the successful
  B3/B4 returns supply a current library compilation; Cargo interprets their
  exact allocator line as exactly the corresponding `fixture_allocator`
  key/value, maps the requested feature and target as admitted, and Rust cfg
  rules select source from those resulting predicates. The report keeps
  `BUILD-MAP-ORDERED` conspicuous and does not infer local output or Rust semantics
  from it.
  - `scope_basis`: B3/B4, exact `BUILD-MAP-ORDERED`, the reviewed Cargo
  directive contracts, and versioned Rust cfg semantics.
  - `dependencies`: B3 through B7.
  - `accepted_alternatives`: a relational composition
  or explicit stage-by-stage prose.
  - `hard_errors`: silently
  widening the accepted mapping triggers BH3; treating an unsuccessful prefix
  as successful triggers BH4.

- **B9 — Rerun/freshness theorem:** A prior successful `arena` build completed
  `RERUN` before `ARENA`; changing the same target directory's raw selector to
  `arena-stop` makes that selection stale, causes a new script run, and yields
  no library for the current rejected build rather than reusing the prior arena
  library.
  - `scope_basis`: local B4/B5 order and precisely the rerun/staleness
  proposition accepted in `BUILD-MAP-ORDERED`, reviewed against Cargo's
  `rerun-if-env-changed` contract.
  - `dependencies`: B4, B5, and the
  no-library exit consequence.
  - `accepted_alternatives`: a more general proof
  for every accepted-to-rejected value change passes if it includes this
  requested sequence.
  - `hard_errors`: omission alone fails B9;
  claiming this current build succeeds from the stale or partial arena output
  triggers BH4.

- **B10 — Effective wasm32/arena exclusion:** For either feature state and all
  profiles/debug states, accepted `arena` selection plus the admitted wasm32
  target mapping makes both predicates of the library's first cfg true; Rust
  `all` and cfg-attribute semantics therefore retain `compile_error!`, whose
  contract makes compilation fail. No `W`/`arena` case is in `Required` or is
  used as the UB witness.
  - `scope_basis`: `SUPPORT.md`, B8, exact configuration
  predicate and attribute semantics, and `compile_error!`.
  - `dependencies`: B8.
  - `accepted_alternatives`: any parametric proof covering both
  feature states and all `P x D`.
  - `hard_errors`: calling this pair
  supported, using it as a valid-use witness, or asserting rejection without
  the selected `compile_error!` proof triggers BH5.

- **B11 — Exact library-body partition:** The report proves that the unchecked
  first body is retained and the complementary checked body removed exactly in
  `Q`, while the checked body is retained and the first body removed exactly
  outside `Q`. In `Q`, B8 supplies `target_arch="aarch64"`,
  `feature="burst"`, and `fixture_allocator="arena"`; Rust's key/value, `all`,
  `not`, and cfg-attribute rules establish both directions of the partition.
  - `scope_basis`: B8 and the exact versioned cfg propositions.
  - `dependencies`: B4 and B8; this is the source-reachability edge for B12/B13.
  - `accepted_alternatives`: expansion of the two cfg predicates or an
  equivalent Boolean proof.
  - `hard_errors`: omission alone fails
  B11; declaring the supported unsafe branch unreachable by ignoring generated
  cfgs triggers BH6.

- **B12 — Existential UB certificate and verdict:** The report identifies the
  well-typed safe call `lane_id(0)` in a supported `Q` case, uses B11 to reach
  `NonZeroU8::new_unchecked(0)`, states that its exact nonzero safety
  proposition is false, applies the Rust 1.85.1 zero-UB consequence, and reports
  whole-`Required` soundness **UNSOUND relative to `BUILD-MAP-ORDERED`**.
  - `scope_basis`: the public safe API, B1, B11, and the exact std contract.
  - `dependencies`: B1 and B11.
  - `accepted_alternatives`: any one supported
  profile/debug state is enough for the existential certificate; proving all
  such states is also correct.
  - `hard_errors`: an incomplete
  certificate followed by `UNSOUND`, or failure to issue `UNSOUND` after giving
  every link, triggers BH7.

- **B13 — Exact maximal sound region:** The report proves both containments for
  `SoundRegion = { case in Required | !Q or i != 0 }`: every included case is
  sound (the checked body dominates its unsafe call outside `Q`, and nonzero
  directly satisfies the unsafe precondition inside `Q`), while every excluded
  Required case is exactly `Q`/zero and has B12's UB execution. It labels this
  the exact maximal source-level region relative to `BUILD-MAP-ORDERED`.
  - `scope_basis`: the user-requested maximal theorem, B1, B11/B12, `if`/comparison/
  panic semantics, and `new_unchecked`.
  - `dependencies`: B1, B8,
  B11, B12.
  - `accepted_alternatives`: an algebraically equivalent formula or
  disjoint partition; a correct non-maximal remainder does not pass this
  explicitly requested atom.
  - `hard_errors`: omission or refusal to
  maximize alone fails B13; calling a region maximal while including Q/zero,
  excluding sound Q/nonzero cases, or excluding all of `Q` triggers BH8.

- **B14 — Regional zero-panic theorem:** For every zero-input case outside
  `Q`, cfg selection retains the checked body, `value == 0` makes the `if`
  consequent execute, and `panic!` prevents reachability of the later unsafe
  call. Thus `CoveredPanic = RequiredPanic intersect !Q` is **PROVED relative
  to `BUILD-MAP-ORDERED`** across every applicable target/allocator/feature,
  profile, and debug state.
  - `scope_basis`: B1/B8/B11 and exact comparison,
  `if`, cfg, and panic contracts.
  - `dependencies`: B1, B8, and the
  complement of B11.
  - `accepted_alternatives`: a parametric proof or exact
  finite configuration partition.
  - `hard_errors`: incomplete
  regional coverage alone fails B14; falsely claiming the region contains
  Q/zero triggers BH9 or BH10 depending on the verdict.

- **B15 — Whole-domain panic-postcondition verdict:** The report states that
  the documented zero-input panic guarantee over all `RequiredPanic` is
  **UNPROVED**, not `CONTRACT-BROKEN` and not `PROVED`: Q/zero contains UB, so
  its apparent source prefix supplies neither a defined non-panic witness nor a
  guaranteed observation, while B14 proves every other zero case.
  - `scope_basis`: the exact behavioral quantifier, B12, B14, and whole-execution UB
  reasoning.
  - `dependencies`: B12 and B14.
  - `accepted_alternatives`:
  equivalent theorem-specific wording that keeps this verdict separate from
  soundness.
  - `hard_errors`: using the UB-containing case to claim
  `CONTRACT-BROKEN` or an observation before UB triggers BH9; claiming the
  universal panic theorem `PROVED` triggers BH10.

## Hard Errors

- **BH1:** Claims a whole-domain affirmative result after omitting a supported
  release, target, feature, allocator, profile, debug state, or valid `u8`
  input, or treats the supported `Q` cell as excluded.
- **BH2:** Claims the build relation or a dependent theorem complete while
  replacing the requested ordered/fallible relation with an endpoint summary
  that omits a material raw-selector class, failure edge, partial-prefix exit,
  or necessary stage.
- **BH3:** Invents, silently widens, or treats as Rust authority any Cargo,
  freshness, process-status, feature, or target proposition beyond exact
  `BUILD-MAP-ORDERED`.
- **BH4:** Treats a cfg line emitted by an unsuccessful script, or a stale
  artifact from an earlier selector, as the library selected for the current
  failed build.
- **BH5:** Treats a rejected raw selector as an accepted allocator model;
  treats wasm32/arena as supported; uses it as the safe-use UB witness; or
  claims its effective rejection without the selected `compile_error!` proof.
- **BH6:** Ignores build-script output or exact Cargo/cfg interpretation and
  consequently declares the supported `Q` unsafe branch unreachable.
- **BH7:** Reports `UNSOUND` without the valid safe use, reachability, false
  exact safety proposition, and applicable UB consequence, or reports only
  `UNPROVED` after explicitly establishing all four links.
- **BH8:** Claims an exact or maximal sound region that includes Q/zero or
  excludes any sound Required case, including Q/nonzero.
- **BH9:** Reports `CONTRACT-BROKEN` for the zero-panic promise using only the
  UB-containing Q/zero execution, or claims an observation is guaranteed
  because it appears before that UB in source order.
- **BH10:** Reports the whole-`RequiredPanic` zero-panic theorem `PROVED`
  despite leaving Q/zero without a defined proof.

## Checked Authorities

The evaluator must open each exact page, confirm the quoted proposition, and
confirm applicability to Rust/Cargo 1.85.1. The quotation is included to make
the semantic leaf explicit; punctuation-only rendering differences are
irrelevant.

- `https://doc.rust-lang.org/1.85.1/std/env/fn.var.html` — “Fetches the
  environment variable key from the current process”; returns
  `VarError::NotPresent` when the variable is not set and
  `VarError::NotUnicode` when its value is not valid Unicode.
- `https://doc.rust-lang.org/1.85.1/std/env/enum.VarError.html` — the enum is
  exactly `NotPresent` or `NotUnicode(OsString)`; the variant descriptions
  distinguish absence from a present value without valid Unicode data.
- `https://doc.rust-lang.org/1.85.1/std/result/enum.Result.html` — `Result` is
  exactly `Ok(T)` or `Err(E)` and “represents either success (`Ok`) or failure
  (`Err`).”
- `https://doc.rust-lang.org/1.85.1/std/primitive.u8.html` — `u8` is “The 8-bit
  unsigned integer type,” with `MIN` equal to zero and `MAX` equal to 255; zero
  is therefore an ordinary valid safe-call input.
- `https://doc.rust-lang.org/1.85.1/reference/expressions/match-expr.html` — a
  scrutinee value is “sequentially compared to the patterns in the arms until
  a match is found,” and the first matching arm is chosen and entered.
- `https://doc.rust-lang.org/1.85.1/reference/expressions/block-expr.html` — a
  block sequentially executes its non-item statements and optional final
  expression; its type is `()` when the final operand is omitted.
- `https://doc.rust-lang.org/1.85.1/reference/items/functions.html#function-body`
  — an omitted function output is unit, and the body is conceptually wrapped
  so that its body value is returned; an explicit `return`, if reached,
  short-cuts that implicit return.
- `https://doc.rust-lang.org/1.85.1/reference/expressions/call-expr.html` — “A
  call expression calls a function”; if the function eventually returns, the
  expression completes.
- `https://doc.rust-lang.org/1.85.1/reference/patterns.html#tuple-struct-patterns`
  — tuple-struct patterns match tuple-struct and enum values satisfying all
  their subpatterns and destructure that value.
- `https://doc.rust-lang.org/1.85.1/reference/patterns.html#literal-patterns` —
  literal patterns “match exactly the same value as what is created by the
  literal.”
- `https://doc.rust-lang.org/1.85.1/reference/patterns.html#wildcard-pattern` —
  the wildcard pattern “matches any value.”
- `https://doc.rust-lang.org/1.85.1/std/string/struct.String.html#method.as_str`
  — `as_str` “Extracts a string slice containing the entire `String`.”
- `https://doc.rust-lang.org/1.85.1/std/macro.println.html` — `println!`
  “Prints to the standard output, with a newline,” supplying the successful
  completed-line effect used by B3–B6.
- `https://doc.rust-lang.org/1.85.1/std/macro.println.html#panics` — `println!`
  “Panics if writing to `io::stdout` fails.”
- `https://doc.rust-lang.org/1.85.1/std/macro.panic.html` — `panic!` “Panics the
  current thread.” The process-status consequence consumed by this fixture is
  separately and explicitly admitted by `BUILD-MAP-ORDERED`.
- `https://doc.rust-lang.org/1.85.1/reference/conditional-compilation.html#conditional-compilation`
  — a set configuration option is true; `all(...)` is true exactly when all
  operands are true; and `not(p)` is true exactly when `p` is false.
- `https://doc.rust-lang.org/1.85.1/reference/conditional-compilation.html#the-cfg-attribute`
  — a true cfg predicate retains the attached thing without the cfg attribute,
  while a false predicate removes it from the source.
- `https://doc.rust-lang.org/1.85.1/std/macro.compile_error.html` —
  `compile_error!` “Causes compilation to fail with the given error message
  when encountered.”
- `https://doc.rust-lang.org/1.85.1/reference/expressions/operator-expr.html#comparison-operators`
  — `==` means equal via `PartialEq::eq`; for the primitive `u8` comparison in
  this source it tests whether `value` equals zero.
- `https://doc.rust-lang.org/1.85.1/reference/expressions/if-expr.html` — if the
  Boolean condition is true the consequent executes; if false it is skipped.
- `https://doc.rust-lang.org/1.85.1/std/num/struct.NonZero.html#method.new_unchecked`
  — the function creates a nonzero without checking, “results in undefined
  behavior if the value is zero,” and its Safety section says, “The value must
  not be zero.”
- `https://doc.rust-lang.org/1.85.1/reference/behavior-considered-undefined.html`
  — Rust programs “must never cause undefined behavior”; unsafe code that no
  safe client can trigger to exhibit UB is called sound, and code that safe
  code can misuse to exhibit UB is unsound. The whole-execution conclusion is
  a logical consequence of classifying the execution as undefined, not a
  purported quotation from a source-order or “time travel” subsection.
- `https://doc.rust-lang.org/1.85.1/cargo/reference/build-scripts.html#life-cycle-of-a-build-script`
  — after a build script “successfully finishes executing, the rest of the
  package will be compiled”; a nonzero exit halts the build. This reviews, but
  does not replace, `BUILD-MAP-ORDERED`.
- `https://doc.rust-lang.org/1.85.1/cargo/reference/build-scripts.html#outputs-of-the-build-script`
  — Cargo interprets each stdout line beginning with `cargo::` as an instruction
  affecting package compilation, and instruction order can matter.
- `https://doc.rust-lang.org/1.85.1/cargo/reference/build-scripts.html#rustc-cfg`
  — the directive tells Cargo to pass its value to rustc's `--cfg` flag for
  conditional compilation.
- `https://doc.rust-lang.org/1.85.1/cargo/reference/build-scripts.html#rerun-if-env-changed`
  — the directive tells Cargo to rerun the script if that environment
  variable's value changes.
- `https://doc.rust-lang.org/1.85.1/cargo/reference/features.html` — Cargo sets
  enabled package features with rustc's `--cfg`, and source can test them with
  the cfg attribute or macro.

Cargo pages are evidence used to review the explicit human trust entry; they
are not Rust abstract-semantics axioms and do not silently enlarge that entry.
No test run, CI result, compiler experiment, prior report, evaluator oracle, or
unversioned documentation closes any atom.
