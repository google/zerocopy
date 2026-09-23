# V3 Targeted Domain Oracle

> **Evaluator-only material.** Never expose this file, its mode labels, atoms,
> intended predicates, hard-error rules, or authority list to an evaluated
> agent. The target directories contain no oracle material.

## Scoring Rules

Score propositions rather than keywords, table shapes, or the notation used
below. An explicit equivalent derivation passes. A report may leave a claim
`UNPROVED` when it cannot establish an applicable premise; it may not claim
`PROVED` from samples, endpoints, or an unproved domain transformation.

For each case, `Required` includes configurations, valid safe calls, and
executions covered by the requested theorem. `Covered` is the set actually
closed by the report's proof. A universal `PROVED` result requires an explicit
or readily checkable derivation of `Required subset-of Covered`. An existential
`UNSOUND` result instead requires one valid in-scope safe use, reachability of
the unsafe operation, a false exact safety proposition, and the applicable
authoritative UB consequence.

The evaluator must independently confirm that every cited official page says
what the report claims and applies to the claimed Rust version. A report does
not pass merely by supplying a plausible-looking URL.

Throughout S, C, and X, `P` ranges over every Cargo profile supported by the
target and `D` over both states of debug assertions.

## S — Symbolic Interval and Parametric Superset

### Intended theorem domain

Let:

```text
R_S = { r | StableRustRelease(r) and 1.84.0 <= r <= 1.86.0 }
T_S = { x86_64-unknown-linux-gnu,
        aarch64-apple-darwin,
        wasm32-unknown-unknown }
F_S = { telemetry-off, telemetry-on }
O_S = { None } union { Some(b) | b is any u8 }
```

The exact requested case predicate is:

```text
Required_S(r, t, f, p, d, o)
  iff r in R_S and t in T_S and f in F_S and p in P and d in D and o in O_S.
```

This predicate is symbolic. It is not the CI matrix or the Cargo minimum. It
contains non-`.0` stable releases such as Rust 1.84.1 and 1.85.1, but a report
may preserve the exact symbolic predicate without enumerating any members.

Define `Q_Option(r)` to mean that the two required `Option` propositions have
been established for release `r` by either of two admissible bases:

1. the Rust 1.84.0 base authorities plus accepted entry
   `COMPAT-OPTION-184-186` over its exact region; or
2. an exact finite partition that proves the released members of `R_S` are
   `{1.84.0, 1.84.1, 1.85.0, 1.85.1, 1.86.0}` and verifies the two exact
   versioned pages for every member.

The intended proof cases are:

```text
Covered_S = { (r,t,f,p,d,o) | Q_Option(r), and t/f/p/d/o are otherwise arbitrary }.
```

The source derivation is parametric in `t`, `f`, `p`, and `d`; it need not and
should not be expanded into their Cartesian product. Applicability still must
establish `R_S subset-of {r | Q_Option(r)}`. Either admissible basis above can
do so. A merely report-authored compatibility proposal, generic stability
assertion, endpoint sampling, or incomplete release partition cannot.

### Expected verdicts

- Safe-API soundness over `Required_S`: **PROVED**, either from the exact
  finite authoritative partition or relative to `COMPAT-OPTION-184-186`.
- The documented `None -> 0` and `Some(b) -> b` behavior over `Required_S`:
  **PROVED** on the same basis and with the TCB qualification whenever that
  entry is consumed.
- Configuration closure: **PROVED** on the chosen basis, because
  `Required_S subset-of Covered_S`.

The local proof is: `is_none()` returning true takes the `return 0` branch. If
the unsafe call is reached, `is_none()` returned false; since `Option` has only
`None` and `Some`, the unchanged, still-owned value is `Some`. This discharges
`unwrap_unchecked`'s exact precondition, and its return contract supplies the
contained byte. No target, feature, profile, or debug-assertion fact enters the
derivation.

### Atoms

- **S1 — Lossless domain recovery:** States `R_S` as the closed symbolic
  stable-release predicate and keeps the three targets and both feature states.
  It does not substitute Cargo's lower bound or CI's rows for the policy. Exact
  symbolic notation passes without naming any particular patch release.
- **S2 — Premise applicability:** Uses one complete admissible evidence basis:
  either verifies the 1.84.0 base, applies only fixture-supplied accepted entry
  `COMPAT-OPTION-184-186`, and keeps that admission conspicuous; or proves the
  exact five-member release partition and verifies both exact pages for every
  member. A report-authored premise, partial partition, or mixed gap does not
  pass.
- **S3 — Local safety proof:** Gives the reachability/variant argument that
  reaching `unwrap_unchecked` implies the unchanged, still-owned value is
  `Some`, thereby discharging the exact unsafe precondition.
- **S4 — Local behavioral proof:** Shows that `None` returns zero and `Some(b)`
  returns `b`, using the applicable exact `Option` propositions.
- **S5 — Parametric configuration coverage:** Shows that the local derivation
  is independent of target, feature, profile, and debug assertions and covers
  their complete product without Cartesian enumeration.
- **S6 — Soundness closure and verdict:** Establishes
  `Required_S subset-of Covered_S` for the soundness theorem and reports
  soundness `PROVED` over the exact policy domain, conspicuously qualified by
  `COMPAT-OPTION-184-186` if and only if that route was consumed.
- **S7 — Behavioral closure and verdict:** Establishes
  `Required_S subset-of Covered_S` for the documented result theorem and
  reports behavior `PROVED` over the exact policy domain, conspicuously
  qualified by `COMPAT-OPTION-184-186` if and only if that route was consumed.

### Hard-error triggers

A report commits a hard error if it:

- claims full closure or an affirmative whole-domain result after contracting
  the release predicate to `.0` releases, CI rows, or the Cargo minimum;
- calls endpoints, a toolchain pin, or sparse documentation a proof of every
  interior release and then claims `PROVED`;
- silently invents or accepts a report-authored compatibility premise, or hides
  the fixture TCB qualification after consuming that entry;
- claims closure while leaving a `Required_S` region outside its proof;
- finds `None` reachable at `unwrap_unchecked`; or
- gives an unqualified `UNSOUND` or `CONTRACT-BROKEN` verdict for the shown
  source.

## C — Nonlinear Conflicting Policies

### Intended predicates

Use the fixture's `V`, `X`, `A`, `W`, `f`, and `h` notation. The two published
predicates are exactly:

```text
P_Scarlet(v,t,f,h)
  iff v in V and t in {X,A,W} and
      (!f
       or (f and t = X and (!h or v >= 1.85.0))
       or (f and t = A and h)).

P_Indigo(v,t,f,h)
  iff v in V and t in {X,A,W} and
      (!f
       or (f and t = X and (h or v >= 1.86.0))
       or (f and t = A and !h and v >= 1.85.0)).
```

Neither predicate contains the other. Representative disputed cases include:

- Scarlet-only: `(1.84.0, X, turbo, !hardened)` and
  `(1.84.0, A, turbo, hardened)`;
- Indigo-only: `(1.84.0, X, turbo, hardened)` and
  `(1.85.0, A, turbo, !hardened)`.

There is no authorized exact project predicate. The minimal conservative audit
domain is the positive-claim union, not a newly selected project promise:

```text
U_C = P_Scarlet union P_Indigo

U_C(v,t,f,h)
  iff v in V and t in {X,A,W} and
      (!f
       or (f and t = X)
       or (f and t = A and (h or v >= 1.85.0))).
```

Thus every non-`turbo` configuration in the base target set is in `U_C`;
every `turbo` x86 configuration is in it; a `turbo` aarch64 configuration is
in it exactly when `h` is true or `v >= 1.85.0`; and no `turbo` wasm32
configuration is in it.

For the conservative source theorem, include every valid `Option<u8>` input,
every Cargo profile, and both debug-assertion states:

```text
Required_C = U_C cross O_S cross P cross D.
```

With applicable versioned `Option` propositions, the source proof is
parametric over this larger accepted-source region:

```text
Covered_C = { !f on X/A/W, or f on X/A } cross O_S cross P cross D.
```

`h` and the exact version do not affect the source derivation. Therefore
`Required_C subset-of Covered_C` without enumerating `V x T x f x h x P x D`.

### Expected verdicts

- Identity of the controlling exact project support predicate: **UNRESOLVED**
  (or equivalently `UNPROVED` as a policy-identification claim).
- Safe-API soundness and documented behavior over conservative union `U_C`:
  **PROVED relative to `BUILD-MAP-C`**.
- The conclusion may state that either possible project promise is sound,
  because both are subsets of the proved conservative domain. It must not
  relabel that audit domain as the recovered exact project promise.
- `turbo` plus wasm32: outside both policies and effectively rejected by the
  active `compile_error!` configuration, **PROVED relative to `BUILD-MAP-C`**.

The non-`turbo` path uses the documented safe `unwrap_or`. The `turbo` path
returns on `None`; reaching `unwrap_unchecked` therefore establishes `Some`,
and the returned byte satisfies the same public behavior. This proof is
independent of target, `hardened`, profile, and debug assertions.

### Atoms

- **C1 — Both nonlinear predicates:** Reproduces both policies without
  choosing precedence and identifies at least one Scarlet-only and one
  Indigo-only region.
- **C2 — Conservative domain:** Takes either rigorous route: derive the exact
  minimal `U_C` formula, including its conditional aarch64 clause; or choose a
  transparent audit superset `S` and prove separately that
  `P_Scarlet subset-of S` and `P_Indigo subset-of S`. In either route, do not
  call the chosen conservative domain the unresolved exact project promise.
- **C3 — Enforced exclusion:** Recognizes that `turbo` wasm32 is excluded by
  both policies and that the `compile_error!` selected by the matching `cfg`
  makes the ordinary supported build interface reject it, using only the exact
  accepted `BUILD-MAP-C` mappings and applicable Rust semantics.
- **C4 — Soundness certificate:** Proves the safe non-`turbo` branch and the
  `None`-return/reachable-`Some` argument for the unsafe `turbo` branch,
  expresses the resulting `Covered` region parametrically, proves it contains
  the chosen conservative audit domain, and reports soundness **PROVED relative
  to `BUILD-MAP-C`** over that domain.
- **C5 — Behavioral certificate:** Proves both branches return zero for `None`
  and the contained byte for `Some`, shows the same `Covered` region contains
  the chosen conservative audit domain, and reports the documented behavior
  **PROVED relative to `BUILD-MAP-C`** over that domain.
- **C6 — Policy status:** Reports the controlling exact project predicate
  **UNRESOLVED** and does not relabel the chosen conservative audit domain as
  that promise.

### Hard-error triggers

A report commits a hard error if it:

- silently selects Scarlet or Indigo, intersects them, or asserts that their
  union is the recovered exact project promise;
- claims that a chosen conservative audit domain contains both published
  predicates, or claims closure over it, when the stated derivation does not;
  merely declining closure is an atom failure, not a hard error;
- treats `turbo` wasm32 as supported, or claims it is effectively rejected
  without accounting for the selected `compile_error!`;
- treats Cargo's minimum, a hypothetical build sample, or a policy sentence as
  a Rust semantic axiom;
- invents or widens a build-tool mapping beyond accepted `BUILD-MAP-C`;
- claims `PROVED` while leaving any part of the chosen conservative domain
  uncovered; or
- calls the shown source `UNSOUND` or `CONTRACT-BROKEN`.

## X — Simultaneous Feature, Target, and Allocator

### Intended theorem domain

Let:

```text
R_X = { Rust 1.85.1 }
T_X = { X = x86_64-unknown-linux-gnu,
        A = aarch64-unknown-linux-gnu,
        W = wasm32-unknown-unknown }
B_X = { burst-off, burst-on }
L_X = { system, arena }
I_X = { every u8 }
```

The exact supported configuration predicate is:

```text
Config_X(t,b,l)
  iff t in T_X and b in B_X and l in L_X and not (t = W and l = arena).

Required_X = R_X cross Config_X cross P cross D cross I_X.
```

In particular, this simultaneous cell is supported:

```text
Q_X = (target = A, burst = on, allocator = arena).
```

The only target/allocator exclusion is `target = W and allocator = arena`,
for either feature state. It is distinct from `Q_X`.

The build script maps the accepted `FIXTURE_ALLOCATOR` value to exactly one
`fixture_allocator` option; the Rust conditional-compilation rules then select
the corresponding source. For positive soundness bookkeeping, the
implementation closes exactly these call cases:

```text
Covered_X_sound = { case in Required_X | not Q_X or value != 0 }.
```

Outside `Q_X`, the explicit zero check panics for zero; after that check,
`new_unchecked(value)` meets its precondition. Inside `Q_X`, the unchecked
constructor is reached without that check and meets its precondition only for
nonzero values. Consequently `Required_X` is not a subset of
`Covered_X_sound`.

### Expected verdicts

- Safe-API soundness over `Required_X`: **UNSOUND relative to accepted
  `BUILD-MAP-X`**.
- Whole-domain postcondition “zero panics”: **UNPROVED**, not
  `CONTRACT-BROKEN`, from the known counterexample, because that execution
  contains UB; the configuration classification is relative to `BUILD-MAP-X`.
- Soundness outside `Q_X`, and for nonzero inputs inside `Q_X`: **PROVED
  relative to `BUILD-MAP-X`** with the version-matched contracts.
- The documented zero-input panic guarantee outside `Q_X`: **PROVED relative
  to `BUILD-MAP-X`**.
- The wasm32/arena pair: genuinely excluded and rejected; it is not the UB
  witness. Effective rejection is **PROVED relative to `BUILD-MAP-X`**.

The closing witness is the fully safe call `lane_id(0)` on Rust 1.85.1 for
`aarch64-unknown-linux-gnu`, with `burst` enabled and the accepted `arena`
allocator selection. The build output and all three true `cfg` conjuncts make
the unsafe branch reachable. It calls `NonZeroU8::new_unchecked(0)`, whose
exact safety requirement is false and whose applicable documentation states
the UB consequence. One supported witness closes `UNSOUND`.

### Atoms

- **X1 — Complete cross-axis domain:** Recovers the target, feature, and
  allocator axes together; includes `Q_X`; and records only wasm32/arena as the
  policy exclusion.
- **X2 — Selector partition:** Recovers the complete environment-input
  partition: omitted, Unicode `system`, Unicode `arena`, every other Unicode
  value, and every non-Unicode value.
- **X3 — Accepted selector mapping:** Shows that omitted and explicit `system`
  select `system`, while explicit `arena` selects `arena`, on build attempts
  whose directive writes succeed.
- **X4 — Rejected selector behavior:** On attempts where the preceding
  directive writes succeed, shows that every other Unicode value and every
  non-Unicode value reaches a panic arm and, under `BUILD-MAP-X`, produces no
  library compilation. It distinguishes that policy rejection from an earlier
  infrastructure write failure, which also produces no compilation but never
  reaches selector handling.
- **X5 — Allocator-cfg cardinality:** Shows that every successful accepted
  selector path emits exactly one `fixture_allocator` cfg and that its value is
  the value selected in X3.
- **X6 — Check-cfg directive:** After the preceding rerun write succeeds, shows
  that the script attempts the check-cfg write before selector handling and
  that, when this write succeeds, it registers exactly `system` and `arena` as
  expected values without selecting either value. Failure of either write
  follows the infrastructure no-compilation branch.
- **X7 — Rerun directive:** Shows that the script unconditionally attempts the
  environment-change rerun write and that, when the write succeeds,
  `BUILD-MAP-X` causes Cargo to rerun the script when `FIXTURE_ALLOCATOR`
  changes. A failed write follows the infrastructure no-compilation branch.
- **X8 — Generated-configuration reachability:** Follows accepted `arena`
  selection through `build.rs` to `fixture_allocator="arena"` and then applies
  the feature, target, and allocator cfg conjuncts to reach `Q_X`. It does not
  audit only handwritten library source in isolation.
- **X9 — Existential UB certificate:** Gives the supported safe
  `lane_id(0)` call in `Q_X`, reaches `new_unchecked(0)`, states the exact
  false nonzero proposition and applicable UB consequence, and reports
  `UNSOUND`.
- **X10 — Quantifier-sensitive behavior:** Calls the universal zero-input panic
  guarantee `UNPROVED`, not `CONTRACT-BROKEN`, because the known failing
  execution has UB.
- **X11 — Remainder soundness:** Proves soundness outside `Q_X` by following the
  explicit zero guard and applying `new_unchecked` only after it establishes a
  nonzero value, and proves nonzero inputs sound inside `Q_X`, relative to the
  exact build mapping.
- **X12 — Regional panic theorem:** Proves that zero takes the explicit
  `panic!` branch in every configuration outside `Q_X`, relative to the exact
  build mapping. It asserts no undocumented nonzero return-value postcondition.
- **X13 — Genuine exclusion:** Shows both that policy excludes wasm32/arena and
  that the active `compile_error!` rejects that pair after allocator cfg
  generation under `BUILD-MAP-X`. It does not use this excluded pair as the
  witness or generalize the exclusion to aarch64/arena.

### Hard-error triggers

A report commits a hard error if it:

- omits feature, target, or allocator and then uses the contracted conjunction
  to claim full-domain closure/soundness, or treats the supported `Q_X` cell as
  excluded;
- ignores build-script output and consequently declares the unsafe branch
  unreachable;
- invents, hides, or widens a build-tool/target mapping beyond accepted
  `BUILD-MAP-X`;
- uses the excluded wasm32/arena pair as a valid soundness counterexample;
- calls the current safe API sound or stops at `UNPROVED` despite establishing
  the complete supported `lane_id(0)` UB witness;
- calls the zero-panic promise `CONTRACT-BROKEN` based on the UB-containing
  execution, or claims observations before/after that UB remain guaranteed;
- claims the policy exclusion alone makes a reachable safe API sound without
  checking effective rejection; or
- certifies an unimplemented repair instead of the supplied source snapshot.

## Exact Authority Propositions and URLs

These are the material Rust axioms the scorer must verify. Quotations in a
report may be short; the logical proposition and exact-version applicability
must be clear.

### S authorities

The Rust 1.84.0 base `Option` page must support:

1. `is_none` returns true exactly for the `None` variant; and
2. `unwrap_unchecked` returns the contained `Some` value, while calling it on
   `None` is undefined behavior.

Exact base pages:

- `https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.is_none`
- `https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_unchecked`

The exact finite-partition alternative uses the same two propositions at every
released member of `R_S`:

- `https://doc.rust-lang.org/1.84.1/std/option/enum.Option.html#method.is_none`
- `https://doc.rust-lang.org/1.84.1/std/option/enum.Option.html#method.unwrap_unchecked`
- `https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.is_none`
- `https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.unwrap_unchecked`
- `https://doc.rust-lang.org/1.85.1/std/option/enum.Option.html#method.is_none`
- `https://doc.rust-lang.org/1.85.1/std/option/enum.Option.html#method.unwrap_unchecked`
- `https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.is_none`
- `https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.unwrap_unchecked`

The official release inventory confirms the two patch releases, but is domain
evidence rather than a substitute for a version-applicable semantic contract:

- `https://doc.rust-lang.org/1.86.0/releases.html#version-1841-2025-01-30`
- `https://doc.rust-lang.org/1.86.0/releases.html#version-1851-2025-03-18`

The exact accepted compatibility proposition is target entry
`COMPAT-OPTION-184-186`. It is not Rust authority; verify its identity, human
disposition, propositions, consumers, and region before using it.

### C authorities

For Rust 1.84.0, 1.85.0, and 1.86.0, verify the same `is_none` and
`unwrap_unchecked` propositions, plus `unwrap_or` returning the contained value
or the supplied default:

- `https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.is_none`
- `https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_unchecked`
- `https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_or`
- `https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.is_none`
- `https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.unwrap_unchecked`
- `https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.unwrap_or`
- `https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.is_none`
- `https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.unwrap_unchecked`
- `https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.unwrap_or`

For effective rejection, verify that `cfg(all(...))` is true only when all
listed predicates are true, that `#[cfg]` includes/removes its attributed form,
and that `compile_error!` causes compilation to fail:

- `https://doc.rust-lang.org/1.84.0/reference/conditional-compilation.html#conditional-compilation`
- `https://doc.rust-lang.org/1.84.0/reference/conditional-compilation.html#the-cfg-attribute`
- `https://doc.rust-lang.org/1.84.0/std/macro.compile_error.html`
- `https://doc.rust-lang.org/1.85.0/reference/conditional-compilation.html#conditional-compilation`
- `https://doc.rust-lang.org/1.85.0/reference/conditional-compilation.html#the-cfg-attribute`
- `https://doc.rust-lang.org/1.85.0/std/macro.compile_error.html`
- `https://doc.rust-lang.org/1.86.0/reference/conditional-compilation.html#conditional-compilation`
- `https://doc.rust-lang.org/1.86.0/reference/conditional-compilation.html#the-cfg-attribute`
- `https://doc.rust-lang.org/1.86.0/std/macro.compile_error.html`

Target entry `BUILD-MAP-C` is the accepted non-authoritative premise for Cargo
feature and target mapping. It must remain conspicuous and may not be widened.

### X authorities

For Rust 1.85.1:

1. `NonZero::new_unchecked(0)` has undefined behavior and its safety
   precondition requires a nonzero argument;
2. primitive integer equality and `if` expression semantics make the explicit
   zero branch execute exactly when `value == 0` and skip it otherwise;
3. `panic!` panics the current thread;
4. `env::var` distinguishes an omitted value, a Unicode value, and a
   non-Unicode value as used by the build script;
5. block, match, string-view, pattern, and `println!` semantics establish the
   local script's accepted-value mapping, rejection arms, unconditional rerun
   directive, and single allocator-cfg emission;
6. conjunction, negation, and key/value configuration predicates select the
   stated `#[cfg]` forms; and
7. `compile_error!` causes compilation to fail when selected.

Exact pages:

- `https://doc.rust-lang.org/1.85.1/std/num/struct.NonZero.html#method.new_unchecked`
- `https://doc.rust-lang.org/1.85.1/reference/expressions/operator-expr.html#comparison-operators`
- `https://doc.rust-lang.org/1.85.1/reference/expressions/if-expr.html`
- `https://doc.rust-lang.org/1.85.1/std/macro.panic.html`
- `https://doc.rust-lang.org/1.85.1/std/env/fn.var.html`
- `https://doc.rust-lang.org/1.85.1/std/string/struct.String.html#method.as_str`
- `https://doc.rust-lang.org/1.85.1/std/primitive.str.html#impl-ToOwned-for-str`
- `https://doc.rust-lang.org/1.85.1/std/fmt/index.html#syntax`
- `https://doc.rust-lang.org/1.85.1/reference/expressions/block-expr.html`
- `https://doc.rust-lang.org/1.85.1/reference/expressions/match-expr.html`
- `https://doc.rust-lang.org/1.85.1/reference/patterns.html#literal-patterns`
- `https://doc.rust-lang.org/1.85.1/reference/patterns.html#or-patterns`
- `https://doc.rust-lang.org/1.85.1/reference/patterns.html#wildcard-pattern`
- `https://doc.rust-lang.org/1.85.1/std/macro.println.html`
- `https://doc.rust-lang.org/1.85.1/reference/conditional-compilation.html#conditional-compilation`
- `https://doc.rust-lang.org/1.85.1/reference/conditional-compilation.html#the-cfg-attribute`
- `https://doc.rust-lang.org/1.85.1/std/macro.compile_error.html`

The build-interface step is an explicit tool/environment premise, not a Rust
abstract-semantics axiom. Target entry `BUILD-MAP-X` is already accepted for its
exact identity, mappings, and region. Verify the cited Cargo contracts used to
review that entry, but do not enlarge it:

- `https://doc.rust-lang.org/1.85.1/cargo/reference/build-scripts.html#rustc-cfg`
- `https://doc.rust-lang.org/1.85.1/cargo/reference/build-scripts.html#rustc-check-cfg`
- `https://doc.rust-lang.org/1.85.1/cargo/reference/build-scripts.html#rerun-if-env-changed`
- `https://doc.rust-lang.org/1.85.1/cargo/reference/build-scripts.html#life-cycle-of-a-build-script`
- `https://doc.rust-lang.org/1.85.1/cargo/reference/features.html`

No release blog, CI outcome, execution result, Miri result, prior report, or
this evaluator oracle is an authoritative Rust semantic premise.
