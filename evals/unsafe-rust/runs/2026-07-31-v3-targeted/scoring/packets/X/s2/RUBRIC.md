# Mode X Frozen Blind-Scoring Rubric

> **Evaluator-only material. Never expose this file to a report agent.**

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
