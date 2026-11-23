# rustc_borrowck Polonius CLI Flag Triad, Flow-Sensitive Invariance Separation, Edition 2024 RPIT member_constraints Lattice Resolution, and TwoPhaseBorrow Reservation Semantics

## Summary

Four coupled mechanisms determine how `rustc_borrowck` decides lifetime and aliasing soundness on modern Rust programs—and why subtle CLI defaults, universal-region solver boundaries, opaque-type lattice minimization, and two-phase method-call borrows behave differently across toolchains and verification models:

1. **Nightly `Polonius` CLI Triad (`Off` / `Next` / `Legacy`) Flips Between `1.98.0-nightly` and `1.102.0-nightly` / Upstream `main`:**
   In `rust-lang/rust` upstream `main` (`fde8dfd638478da758f93f0e8d9b74d7907f0c9e`) and `rustc 1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`), `src/bootstrap/src/core/build_steps/compile.rs:1374-1378` exports `CFG_DEFAULT_POLONIUS_NEXT="1"` whenever `builder.config.channel` is `"nightly"` or `"dev"`. Consequently, `Polonius::DEFAULT` in `compiler/rustc_session/src/config.rs:3856-3857` evaluates to `Polonius::Next` (replacing the earlier `#[default] Off` seen in `rustc 1.98.0-nightly` at commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`), and `-Z help` displays `(default: next)` via `POLONIUS_HELP` (`compiler/rustc_session/src/options.rs:2458-2462`). Crucially, `parse_polonius` (`options.rs:1065-1081`) continues to parse **bare** `-Zpolonius` (`None`) and `-Zpolonius=legacy` to `Polonius::Legacy`, `-Zpolonius=next` to `Polonius::Next`, and adds `Some("off") | Some("no") => Polonius::Off`. Running pure NLL (`+stable` parity, e.g., `rustc 1.100.0` at `0ef1bc386059596dada8fb65b50425aab2ea637a`) on post-flip nightlies requires `-Zpolonius=off`, whereas `rustc 1.98.0-nightly` still defaults to `Polonius::Off` and rejects `-Zpolonius=off` with exit code `1` (`incorrect value 'off' for unstable option 'polonius'`).

2. **Strict Three-Way Behavioral Separation (`Off ⊊ Next ⊊ Legacy`) on `flow_sensitive_invariance`:**
   Both `Polonius::Next` and `Polonius::Legacy` localize borrow/loan liveness enough to accept Problem Case #3 patterns such as `HashMap::get` (`E0502` under `Off`) and `HashMap::get_mut` (`E0499` under `Off`). However, `Polonius::Next` rejects flow-sensitive invariance across disjoint branches (`flow_sensitive_invariance<'a, 'b>`, returning `Result<Invariant<'a>, Invariant<'b>>` with a shared `Invariant<'l>(Cell<&'l ()>)` local) with two universal-region errors (`'b: 'a` and `'a: 'b`), whereas `Polonius::Legacy` (`-Zpolonius` / `-Zpolonius=legacy`) accepts it (`rc=0`). Source inspection shows why: `Polonius::Next` replaces only loan liveness (`Borrows::new` in `compiler/rustc_borrowck/src/dataflow.rs:405-410`, backed by `PoloniusContext::compute_loan_liveness` in `nll.rs:151-163` and `polonius/constraints.rs:63-243`), whereas `RegionInferenceContext::solve` (`region_infer/region_context.rs:216-229`) gates `check_polonius_subset_errors` strictly on `.is_legacy_enabled()`. Under `Polonius::Next` and `Polonius::Off`, `check_universal_regions` still solves location-insensitive `ConstraintSccs`, collapsing `'a` (`'?1`) and `'b` (`'?2`) into one SCC (`Invariant` bidirectional `Single(bb2[2])` and `Single(bb3[2])` edges). Separately, our Lean mechanization surfaced why `polonius/liveness.rs:31-42` forces `ConstraintDirection::Forward` on universal regions: allowing backward CFG edges on universal `'a` in `get_or_insert` would propagate return-arm loans back through the `match` split into the `None` arm and destroy Problem Case #3 precision.

3. **Edition 2024 RPIT Auto-Capture and `member_constraints.rs` Choice-Set Lattice Resolution:**
   Under Edition 2024 (`rust-lang/reference` `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `r[type.impl-trait.generic-capture.edition2024]`), `impl Trait` return types on free functions and inherent methods capture all in-scope lifetime parameters by default—rejecting mutation of unreturned borrowed locals (`E0506`) unless narrowed with `use<...>` (`r[type.impl-trait.generic-capture.precise.use]`). Conversely, Edition 2021 rejects hidden-type capture of unmentioned `'a` with `E0700`. In MIR borrowck, `collect_defining_uses` (`region_infer/opaque_types/mod.rs:285-299`) builds each defining use's candidate pool `0 :: captured_arg_regions` with `fr_static` (`'static`) prepended, and `apply_member_constraint` (`opaque_types/member_constraints.rs:59-139`) filters candidates by universal lower bounds (`scc_values.universal_regions_outlived_by`) and `rev_scc_graph.upper_bounds`, discards mutually incomparable candidates (`totally_ordered_subset`), and selects the **minimum** (shortest) comparable candidate via `.reduce(...)`. When `cond { x } else { y }` creates incomparable upper bounds `'a` and `'b` with `use<'a, 'b>`, `totally_ordered_subset` becomes empty and reports `E0700`; adding `where 'a: 'b` picks `'b`, and adding a shared sink `where 'a: 'c, 'b: 'c` picks `'c` rather than `'static`.

4. **`TwoPhaseBorrow` Reservation-vs.-Activation State Machine and Tree Borrows Correspondence:**
   In HIR-to-THIR lowering (`compiler/rustc_mir_build/src/thir/cx/expr.rs:1751-1768`), receiver auto-borrows for `&mut self` method calls carry `AllowTwoPhase::Yes`, producing `BorrowKind::Mut { kind: MutBorrowKind::TwoPhaseBorrow }`. During MIR borrow gathering (`borrow_set.rs:443-569`), each two-phase borrow enters `TwoPhaseActivation::NotActivated` in `pending_activations[temp]` and transitions at its unique downstream consumer use to `ActivatedAt(location)` (populating `activation_map`). `path_utils::is_active` (`path_utils.rs:60-120`) evaluates to `false` inside the dominator diamond `(reserve_location.successor_within_block(), activation_location)`, enabling `MirBorrowckCtxt::check_access_for_conflict` (`lib.rs:1324-1329`) to permit shared reads (`v.push(v.len())`, prior `&v[0]` released before push), while `lib.rs:1347-1375` rejects intervening writes, nested `&mut2` reservations (`E0499`), or post-activation reads (`E0502`), and `check_activations` (`lib.rs:1872-1895`) rejects prior shared borrows still live at `ActivatedAt` (`E0502`). Live Miri `-Zmiri-tree-borrows` runs match this contract: unprotected `&mut2` transitions stay `ReservedFrz`/`ReservedIM` across foreign reads and promote to `Unique` on child write (`rc=0`), whereas function-entry protected `&mut` suffers `ReservedFrz { conflicted: true }` on a foreign read and triggers Undefined Behavior upon child write (`rc=1`).

5. **Kernel-Checked Lean 4 Formalization and Anneal TCB Boundary:**
   All three components are mechanized in a self-contained `1,832`-line Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) artifact (`62` theorems, `55` definitions) compiled under `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` with zero `sorry`, zero `Classical.choice`, zero `Lean.ofReduceBool` (`native_decide`), zero `omega`, zero `bv_decide`, zero `partial def`, and zero `._unsafe_rec` constants across all `117` top-level declarations. Inspecting `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`MirAst.lean:304-320, 608-625`, `MirSemantics.lean:1313`, `driver.rs:25-84`) confirms that Anneal currently erases lifetimes and `BorrowKind` during MIR capture, fails closed on references (`FaultKind.unsupported`), and delegates borrowck option handling to `rustc`'s CLI flags—putting explicit `-Zpolonius` pinning inside Anneal's TCB whenever upgrading beyond `1.98.0-nightly`.

---

## Applicability

This report documents primary-source compiler behavior, differential execution across toolchain eras, and mechanized soundness models for four interrelated `rust-lang/rust` borrow-checker subsystems and their interface to verified MIR capture (`joshlf/anneal`):

- **Upstream compiler source baselines:** `rust-lang/rust` main (`fde8dfd638478da758f93f0e8d9b74d7907f0c9e`), the upstream snapshot `49d734536222bf28bb6d07d885b3a81d145981da` referenced alongside preserved `1.102.0-nightly` / `1.100.0` runs, and the pre-flip `rustc 1.98.0-nightly` tag (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`). All session option definitions (`config.rs`, `options.rs`), bootstrap flags (`compile.rs`), borrowck internals (`nll.rs`, `dataflow.rs`, `lib.rs`, `borrow_set.rs`, `path_utils.rs`, `places_conflict.rs`, `constraints/mod.rs`, `region_infer/*`, `polonius/*`), THIR lowering (`thir/cx/expr.rs`), and Miri Tree Borrows transition rules (`tree_borrows/perms.rs`) were directly read from downloaded upstream files unless explicitly scoped in [Boundaries](#boundaries).
- **Executed compiler & interpreter toolchains (versions distinguished explicitly throughout):**
  - **Live host execution (`2026-11-23`):** `rustc 1.98.0-nightly (14210df0e 2026-05-31)` and `miri 0.1.0 (14210df0e2 2026-05-31)` at commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (LLVM `22.1.6`, host `x86_64-unknown-linux-gnu`). On this toolchain, `Polonius::DEFAULT == Polonius::Off`, so `-Zpolonius=off` is rejected by `parse_polonius` (`rc=1`) and pure NLL is invoked with no `-Zpolonius` flag.
  - **Preserved differential archive (`2026-11-11` / `2026-11-09`):** `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)` at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` and `rustc 1.100.0 (0ef1bc386 2026-11-09)` at `0ef1bc386059596dada8fb65b50425aab2ea637a` (LLVM `23.1.5`, host `x86_64-unknown-linux-gnu`), stored in `support/preserved_1_102_nightly_and_1_100_stable_results.json`. On `1.102.0-nightly`, `CFG_DEFAULT_POLONIUS_NEXT` is active, so default invocation runs `Polonius::Next` and `-Zpolonius=off` selects pure NLL matching `1.100.0` stable.
- **Normative specifications and RFCs:** `rust-lang/reference` (`c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`: `impl Trait` opaque captures and method-call autoref/deref) and `rust-lang/rfcs` (`f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`: RFC 2025 nested method calls / `&mut2`, RFC 2094 NLL, RFC 3498 Edition 2024 lifetime capture rules). Note that `-Zpolonius=next` and `-Zpolonius=legacy` are unstable `-Z` borrow-checker prototypes and therefore governed by `rustc` implementation source rather than `rust-lang/reference`.
- **Lean 4 mechanization & downstream verification consumer:** `leanprover/lean4` tag `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) and `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`). Our Lean model formalizes abstract borrow-region graphs, finite region-preorder member constraints, and a single-borrow two-phase/Tree-Borrows automaton rather than the full `rustc` MIR IR; exact model scope is bounded under [Boundaries](#boundaries).

---

## Findings

### Part I — Nightly `Polonius::DEFAULT == Polonius::Next` Flag Triad and Bootstrap Gates

```text
Basis: source + execution + derived
```

Between `rustc 1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`) and `rustc 1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`) / `rust-lang/rust` upstream `main` (`fde8dfd638478da758f93f0e8d9b74d7907f0c9e`), `rustc_session` changed both the compile-time default of `Polonius` on nightly/dev builds and the accepted option grammar of `-Zpolonius`.

#### Primary-Source Option & Bootstrap Wiring

In `rust-lang/rust` main (`fde8dfd638478da758f93f0e8d9b74d7907f0c9e`), `src/bootstrap/src/core/build_steps/compile.rs:1374-1378` sets compile-time configuration environment variables when building the stage compiler:

```rust
let nightly = builder.config.channel == "nightly" || builder.config.channel == "dev";
if nightly {
    // We want to enable Polonius Alpha and Next Trait Solver by default on nighty
    cargo.env("CFG_DEFAULT_POLONIUS_NEXT", "1");
    cargo.env("CFG_DEFAULT_NEXT_SOLVER_GLOBALLY", "1");
    cargo.env("CFG_DEFAULT_FRONTEND_JOBS", "2");
}
```

In `compiler/rustc_session/src/config.rs:3837-3868`, `Polonius` replaces `#[derive(Default)] #[default] Off` (`rustc 1.98.0-nightly`, `config.rs:3321-3332`) with a compile-time gated `Polonius::DEFAULT`:

```rust
#[derive(Clone, Copy, PartialEq, Hash, Debug)]
pub enum Polonius {
    /// Polonius is disabled, only use NLL.
    Off,
    /// Legacy version, using datalog and the `polonius-engine` crate. Historical value for `-Zpolonius`.
    Legacy,
    /// In-tree prototype, extending the NLL infrastructure.
    Next,
}

impl Polonius {
    pub(crate) const DEFAULT: Self =
        if option_env!("CFG_DEFAULT_POLONIUS_NEXT").is_some() { Self::Next } else { Self::Off };
```

Crucially, `parse_polonius` in `compiler/rustc_session/src/options.rs:1065-1081` (paired with option declaration `polonius: Polonius = (Polonius::default(), parse_polonius, [TRACKED], POLONIUS_HELP)` at `options.rs:2877-2878` and `POLONIUS_HELP` at `options.rs:2458-2462`) preserves historical bare-flag semantics while adding explicit opt-out:

```rust
pub(crate) fn parse_polonius(slot: &mut Polonius, v: Option<&str>) -> bool {
    match v {
        Some("legacy") | None => {
            *slot = Polonius::Legacy;
            true
        }
        Some("next") => {
            *slot = Polonius::Next;
            true
        }
        Some("off") | Some("no") => {
            *slot = Polonius::Off;
            true
        }
        _ => false,
    }
}
```

By contrast, in `rustc 1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `options.rs:910-922, 2536-2537`), `parse_polonius` has no `Some("off") | Some("no")` arm, `options.rs:2537` hardcodes `"enable polonius-based borrow-checker (default: no)"`, and `config.rs:3322-3325` sets `#[default] Off`. Notice the three-way footgun on `1.102.0-nightly` and `main`:

| CLI Invocation | `1.98.0-nightly` (`14210df0e27c`) | `1.102.0-nightly` (`3ef0c22cdb86`) & `main` (`fde8dfd63847`) | `1.100.0` Stable (`0ef1bc386059`) | Rationale / Mechanism |
|---|---|---|---|---|
| *(no flag)* | `Polonius::Off` (`rc=0` on smoke) | **`Polonius::Next`** (`-Z help`: `(default: next)`) | `Polonius::Off` | `CFG_DEFAULT_POLONIUS_NEXT` switches `Polonius::DEFAULT` (`config.rs:3856-3857`) |
| `-Zpolonius=off` / `=no` | **CLI Error (`rc=1`)** (`incorrect value 'off'`) | **`Polonius::Off`** (`+stable` NLL parity) | Rejected (`-Z` unstable) | `Some("off") \| Some("no")` arm added after `1.98.0-nightly` (`options.rs:1075`) |
| `-Zpolonius` *(bare)* | **`Polonius::Legacy`** (`datalog`) | **`Polonius::Legacy`** (`datalog`) | Rejected (`-Z` unstable) | `None` arm retains `Legacy` (`options.rs:1067`), **not** `Polonius::DEFAULT`! |
| `-Zpolonius=next` | `Polonius::Next` | `Polonius::Next` | Rejected (`-Z` unstable) | `Some("next") => Polonius::Next` (`options.rs:1071`) |
| `-Zpolonius=legacy` | `Polonius::Legacy` | `Polonius::Legacy` | Rejected (`-Z` unstable) | `Some("legacy") => Polonius::Legacy` (`options.rs:1067`) |

A caller passing bare `-Zpolonius` on `1.102.0-nightly` expecting to explicitly spell out the nightly default silently switches borrow-checking algorithms from `Polonius::Next` to the Datalog `polonius-engine` backend (`Polonius::Legacy`), whereas omitting `-Zpolonius` runs `Polonius::Next`, and testing pure lexical-SCC/location-insensitive NLL (`+stable` parity) requires `-Zpolonius=off`.

---

### Part II — Three-Way Behavioral Separation (`Off ⊊ Next ⊊ Legacy`) and the Flow-Sensitive Invariance Mechanism

```text
Basis: source + execution + derived
```

#### Why `Off` Rejects Problem Case #3 (`a1`, `a2`) While Both `Next` and `Legacy` Accept

In `compiler/rustc_borrowck/src/polonius/mod.rs` and `nll.rs:126-203`, `-Zpolonius=off`, `-Zpolonius=next`, and `-Zpolonius=legacy` select three distinct combinations of loan-liveness propagation and universal-region constraint checking:

1. **Pure NLL (`Polonius::Off`):** `Borrows::new` (`dataflow.rs:405-410`) calls `calculate_borrows_out_of_scope_at_location`, computing each loan's region via location-insensitive SCC closure in `RegionInferenceContext::solve`. Universal region constraints are checked via `check_universal_regions` (`region_infer/region_context.rs:225, 1340-1361`) over the same location-insensitive graph.
2. **In-tree Localized Prototype (`Polonius::Next`):**
   - `nll::compute_regions` (`nll.rs:151-163`) checks `if let Some(polonius_context) = polonius_context.as_mut()` and calls `polonius_context.compute_loan_liveness(...)`.
   - `LocalizedConstraintGraph::new` (`polonius/constraints.rs:65-96`) partitions `outlives_constraints` into localized point-specific edges `edges[(constraint.sup, point)] += constraint.sub` (`Locations::Single(location)`) and global logical edges `logical_edges[constraint.sup] += constraint.sub` (`Locations::All(_)`).
   - `LocalizedConstraintGraph::traverse` (`constraints.rs:100-243`) starts a per-loan reachability search at `LocalizedNode { region: loan.region, point: location_map.point_from_location(loan.reserve_location) }` and follows: (1) localized `edges` at `node.point`, (2a) **forward** intra-block/inter-block CFG edges whenever `liveness.direction` is `Forward` or `Bidirectional` and `liveness.is_live_at(next_point)`, (2b) **backward** CFG edges ("time-traveling") whenever `liveness.direction` is `Backward` or `Bidirectional` and `liveness.is_live_at(node.point)`, and (3) `logical_edges` at `node.point`.
   - Crucially, `RegionLiveness::new` (`polonius/liveness.rs:31-49`) sets `direction = ConstraintDirection::Forward` whenever `universal_regions.is_universal_region(region)`—even if a universal region appears invariantly inside a type—and otherwise extracts `Forward` (covariant), `Backward` (contravariant), or `Bidirectional` (invariant) from `VarianceExtractor` (`polonius/liveness_constraints.rs:63-81`).
   - `Borrows::new` (`dataflow.rs:408-409`) then uses `PoloniusOutOfScopePrecomputer::compute` instead of NLL's global `regioncx.is_loan_live_at` scope kill computation.
3. **Datalog Engine (`Polonius::Legacy`):** `polonius::legacy::emit_facts` (`nll.rs:137-146`, `polonius/legacy/mod.rs:38-66`) dumps base Datalog facts (`cfg_edge`, `loan_issued_at`, `loan_killed_at`, `subset_base`, `origin_live_on_entry`, `known_placeholder_subset`) and invokes `polonius_engine::Output::compute(polonius_facts, algorithm, false)` (`nll.rs:176-180`, default `"Hybrid"`). Crucially, `RegionInferenceContext::solve` (`region_context.rs:216-229`) branches explicitly on `.is_legacy_enabled()`:

```rust
if infcx.tcx.sess.opts.unstable_opts.polonius.is_legacy_enabled() {
    unsolved_regioncx.check_polonius_subset_errors(
        propagated_outlives_requirements.as_mut(),
        &mut errors_buffer,
        polonius_output.as_ref().expect("Polonius output is unavailable despite `-Z polonius`"),
    );
} else {
    unsolved_regioncx.check_universal_regions(
        propagated_outlives_requirements.as_mut(),
        &mut errors_buffer,
    );
}
```

#### Why `a3_polonius_3way_separator_flow_sensitive_invariance` Separates All Three Modes

Empirical execution confirms exact 3-way separation across `a1` (`HashMap::get`), `a2` (`HashMap::get_mut`), `a3` (`flow_sensitive_invariance`), and controls `a4`/`a5`:

| Case | Description | `Off` (`1.98` def / `1.102` `=off` / `1.100` stable) | `Polonius::Next` (`1.98` `=next` / `1.102` def & `=next`) | `Polonius::Legacy` (`-Zpolonius` & `=legacy`) |
|---|---|---|---|---|
| `a1` | `HashMap::get` Problem Case #3 (`-> &'a str`) | **Err `E0502`** (`rc=1`) | **Ok** (`rc=0`) | **Ok** (`rc=0`) |
| `a2` | `HashMap::get_mut` Problem Case #3 (`-> &'a mut str`) | **Err `E0499`** (`rc=1`) | **Ok** (`rc=0`) | **Ok** (`rc=0`) |
| `a3` | `flow_sensitive_invariance<'a, 'b>` (`Result<Invariant<'a>, Invariant<'b>>`) | **Err** (2 universal errors, `rc=1`) | **Err** (2 universal errors, `rc=1`) | **Ok** (`rc=0`) |
| `a4` | `flow_sensitive_covariant<'a, 'b>` (`Covariant<'l>(&'l ())` control) | **Ok** (`rc=0`) | **Ok** (`rc=0`) | **Ok** (`rc=0`) |
| `a5` | `*q = &mut b; b = 3; *p` backward time-travel control | **Err `E0506`** (`rc=1`) | **Err `E0506`** (`rc=1`) | **Err `E0506`** (`rc=1`) |

In `a3` (`pub fn flow_sensitive_invariance<'a, 'b>(choice: bool) -> Result<Invariant<'a>, Invariant<'b>>`), the body allocates one local `let returned_value = create_invariant();` (existential region `'?11` assigned from `'?4` at `bb0[1]`) and consumes it in two mutually exclusive branches: `if choice { Ok(returned_value) } else { Err(returned_value) }`. Inspecting our captured NLL MIR dump (`probe_polonius_triad_member_constraints_and_two_phase_results.json`, `a3_default_nll`, `flow_sensitive_invariance.-------.nll.0.mir`) reveals the exact constraint graph:

```text
| '?1 ('a) : '?9 and '?9 : '?1 due to BoringNoLocation at All(...)
| '?2 ('b) : '?10 and '?10 : '?2 due to BoringNoLocation at All(...)
| '?4  : '?11 and '?11 : '?4  at Single(bb0[1])   // let returned_value = create_invariant()
| '?11 : '?12                 at Single(bb2[1])   // Ok branch copy/move
| '?5  : '?12 and '?12 : '?5  at Single(bb2[2])   // Ok(returned_value)
| '?5  : '?9  and '?9  : '?5  at Single(bb2[2])   // Ok return type
| '?11 : '?13                 at Single(bb3[1])   // Err branch copy/move
| '?8  : '?13 and '?13 : '?8  at Single(bb3[2])   // Err(returned_value)
| '?7  : '?9  and '?9  : '?7  at Single(bb3[2])   // Err(T=Invariant<'a>) unused variant arg
| '?8  : '?10 and '?10 : '?8  at Single(bb3[2])   // Err return value
```

Notice what happens under the two universal-region checkers:
- Under **`Polonius::Off` and `Polonius::Next`**, `check_universal_regions` evaluates `ConstraintSccs` over all `OutlivesConstraints` without CFG location sensitivity. Because `'?5 <-> '?12`, `'?11 : '?12`, `'?11 : '?13`, `'?8 <-> '?13`, and at `bb2[2]` `'?5 <-> '?9` (`<-> '?1 = 'a`), the location-insensitive solver infers `'1 ('a) = '?2 ('b) = '?4 = '?5 = ... = '?13 = {bb0[0..=1], ..., '?1, '?2}` in the `Inferred Region Values` table! Requiring `'a` to contain `'b` and `'b` to contain `'a` emits two `lifetime may not live long enough` errors (`consider adding the following bound: 'b: 'a` and `'a: 'b`, ending with `help: 'a and 'b must be the same`). Notice `a4` (`Covariant<'l>`) omits the reverse edges `'?12 : '?5` and `'?13 : '?8` (variance is covariant rather than invariant), so `'?1` only has incoming edges (`'?1` stays `{..., '?1}`) and `'a` and `'b` remain disconnected across all three modes!
- Under **`Polonius::Legacy`**, `check_universal_regions` is skipped (`region_context.rs:216-223`) in favor of `check_polonius_subset_errors`. Because `Polonius::Legacy` only propagates `subset(o1, o2, p)` **forward** along `cfg_edge(p, q)` when both `o1` and `o2` are live at `q`, the bidirectional `bb2[2]` edge (`'?1 ('a) <-> '?12` via `'?5, '?9`) exists only along the `Ok` path (`bb2`), whereas the bidirectional `bb3[2]` edge (`'?13 <-> '?2 ('b)` via `'?8, '?10`) exists only along the `Err` path (`bb3`). Because no CFG path connects `bb2` and `bb3`, `'a` never becomes a subset of `'b` at any CFG point, and `Polonius::Legacy` accepts `a3` cleanly.
- Conversely, **`a5`** (`let mut p = &mut a; let q = &mut p; *q = &mut b; b = 3; *p`) verifies why `Polonius::Next` (`polonius/liveness.rs:48`) enables backward CFG propagation on existential invariant regions (`VarianceExtractor` assigns `Bidirectional` to the pointee lifetime `'p` behind `&mut p`): writing `&mut b` through `*q` relates `'b` (`loan` of `b`) to `'p` at `*q = &mut b`, requiring backward time-travel to reach `p`'s prior invariant origin so `E0506` fires before `*p` reads dangling storage. All three backends (`Off`, `Next`, `Legacy`) reject `a5` with `E0506`.

---

### Part III — Edition 2024 RPIT Lifetime Capturing, `use<...>`, and Opaque `member_constraints` Lattice Resolution

```text
Basis: normative + documentation + source + execution + derived
```

#### Edition 2021 vs. Edition 2024 Default Capturing and `use<...>`

Under the normative Rust Reference (`rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `src/types/impl-trait.md:105-120`, `r[type.impl-trait.generic-capture.auto.intro]` and `r[type.impl-trait.generic-capture.edition2024]`) and RFC 3498 (`rust-lang/rfcs@f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`, `text/3498-lifetime-capture-rules-2024.md`), return-position `impl Trait` (RPIT) on free functions and inherent methods shifted across editions:

- **Edition 2021 and earlier:** `fn f<'a, 'b>(x: &'a i32, _y: &'b i32) -> impl Debug` captures neither `'a` nor `'b` because neither appears in the `+ Debug` bounds. Returning `x` fails with `E0700: hidden type for 'impl Debug' captures lifetime that does not appear in bounds` (`b2`, failing across all Polonius modes on both `1.98.0-nightly` and preserved `1.102.0-nightly` / `1.100.0`). Note that RPIT in traits (`impl Trait` in trait methods / trait impls) already captured all in-scope parameters prior to Edition 2024 (`r[type.impl-trait.generic-capture.edition2024]`).
- **Edition 2024:** Every RPIT automatically captures **all** in-scope generic parameters (including both `'a` and `'b`). Consequently, `r = rpit_default(&a, &b)` keeps `b` borrowed for as long as `r` is live (`b1`), rejecting subsequent `b = 3; let _ = (r, b);` with `E0506: cannot assign to 'b' because it is borrowed` even though `_y: &'b i32` is unused in the hidden type!
- **Precise capturing (`use<...>`):** Adding `+ use<'a>` (`r[type.impl-trait.generic-capture.precise.use]`) restricts the opaque type's captured generic arguments strictly to `['a]` (`b3`), allowing `b = 3` (`rc=0` across all 5 modes). Note `b1`/`b2`/`b3` behave identically across `Polonius::{Off, Next, Legacy}` because RPIT parameter capture sets are resolved earlier (during HIR bound-variable resolution) and encoded into the MIR `OpaqueTypeKey`.

#### Primary-Source Algorithm of `member_constraints.rs`

Once a defining use instantiates an opaque type `Opaque<arg_regions>` inside MIR borrowck, hidden-type inference creates existential NLL region variables that must each resolve to one of the captured lifetime arguments or `'static`. `collect_defining_uses` in `compiler/rustc_borrowck/src/region_infer/opaque_types/mod.rs:285-299` builds each defining use's choice list:

```rust
let arg_regions = iter::once(rcx.universal_regions().fr_static)
    .chain(
        opaque_type_key
            .iter_captured_args(infcx.tcx)
            .filter_map(|(_, arg)| arg.as_region())
            .map(Region::as_var),
    )
    .collect();
```

`apply_member_constraint` in `compiler/rustc_borrowck/src/region_infer/opaque_types/member_constraints.rs:59-139` then solves each member constraint `(member_scc, arg_regions)` over the partially ordered universal-region preorder `universal_region_relations`:

1. **Universe guard (`L66-69`):** If `!rcx.max_placeholder_universe_reached(member).is_root()`, bail out conservatively without constraining `member`.
2. **Lower-bound filter (`L74-83`):** Keep only representatives `choice_region = rcx.representative(r).rvid()` such that for every `lower_bound` in `rcx.scc_values.universal_regions_outlived_by(member)`, `outlives(choice_region, lower_bound)` holds.
3. **Upper-bound filter (`L94-97`):** For every `ub` in `rcx.rev_scc_graph.upper_bounds(member)` (requiring `ub: member`), retain `choice_region` only if `outlives(ub, choice_region)` holds.
4. **Total-order projection (`L111-116`):** Filter the remaining `choice_regions` to `totally_ordered_subset`, keeping `r1` iff for every remaining `r2`, `outlives(r1, r2) || outlives(r2, r1)`. This explicitly drops incomparable pairs (`['a, 'b]`) from consideration!
5. **Minimum selection & SCC lifting (`L118-138`):** Reduce `totally_ordered_subset` choosing the **smaller** (shorter) lifetime:
   - `(r1: r2 = true, r2: r1 = false) => r2`
   - `(r1: r2 = false, r2: r1 = true) => r1`
   - `(true, true) => r1.min(r2)` (tie-break by `RegionVid`)
   If empty, return `None` (no SCC update; later `compute_definition_site_hidden_types_from_defining_uses` reports `E0700`); otherwise mutate `rcx.scc_values.add_region(member, rcx.constraint_sccs.scc(min_choice))`.

Five empirical probes (`b4`..`b8`, Edition 2024) exercise every branch of `apply_member_constraint` cleanly across all Polonius modes:

| Case | Opaque Signature & Body | Initial `candidateChoices` | Surviving Admissible Set | `totally_ordered_subset` & Chosen Min | Compiler Result |
|---|---|---|---|---|---|
| `b4` | `if cond { x } else { y }` with `+ use<'a, 'b>` (`'a, 'b` unrelated) | `['static, 'a, 'b]` | **Empty `[]`** (none satisfies both `ub 'a: c` and `ub 'b: c`) | Empty `[]` -> `None` | **Err `E0700`** |
| `b5` | Same as `b4` + `where 'a: 'b` | `['static, 'a, 'b]` | `['b]` (`'a: 'b`, `'b: 'b`, whereas `'a: 'static` & `'b: 'a` fail) | `['b]` -> `'b` | **Ok** (`rc=0`) |
| `b6` | `(x: Cell<&'a str>, _y: Cell<&'b str>) -> impl Sized + use<'a, 'b>` | `['static, 'a, 'b]` | `['a]` (invariant `'member <-> 'a` enforces `lb='a`, `ub='a`) | `['a]` -> `'a` | **Ok** (`rc=0`) |
| `b7` | `(x: &'static str) -> impl Display + use<'a, 'b>` | `['static, 'a, 'b]` | `['static, 'a, 'b]` (only `ub='static`, which outlives every region) | `['static]` (`'a, 'b` incomparable) -> **`'static`** | **Ok** (`rc=0`) |
| `b8` | `if cond { x } else { y }` with `where 'a: 'c, 'b: 'c` + `use<'a, 'b, 'c>`, called on local `&s1, &s2` | `['static, 'a, 'b, 'c]` | `['c]` (only `'c` satisfies both `ub 'a: c` and `ub 'b: c` without `ub 'a: 'static`) | `['c]` -> **`'c`** (verified by non-`'static` local callers) | **Ok** (`rc=0`) |

Two subtleties of `apply_member_constraint` merit emphasis:
- **In `b7` (`x: &'static str`)**, returning `x` into `impl Display` with `&'?r str` imposes only the upper bound `'static: '?r` (`ub = 'static`), with no `'r: 'static` lower bound. Because `'static` outlives `'static`, `'a`, and `'b`, all three candidates pass steps 2 and 3; step 4 (`totally_ordered_subset`, `L111-116`) then discards `'a` and `'b` because they do not compare with each other, leaving `totally_ordered_subset = ['static]` (`'static` outlives every candidate) so step 5 deterministically picks `'static`.
- In `b8` (`call_diamond_with_locals`), passing non-`'static` local borrows `&s1` (`'a`) and `&s2` (`'b`) plus inferred `'c` proves that `b8` succeeded NOT by promoting `'member` to `'static` (`&s1` cannot satisfy `'static`!), nor by widening `'a, 'b` to `'static`, but by resolving `'member` cleanly to `'c` (`['c]` survives `ub='a, 'b`; `'a, 'b, 'static` are rejected by `ub` because neither `'a: 'static` nor `'b: 'a` holds!).

---

### Part IV — `TwoPhaseBorrow` Reservation-vs.-Activation State Machine and Tree Borrows Correspondence

```text
Basis: normative + documentation + source + execution + derived
```

#### Compiler Pipeline: THIR Lowering, MIR `BorrowSet`, Dominator Diamond, and Borrowck Checks

As standardized in RFC 2025 (`rust-lang/rfcs@f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`, `text/2025-nested-method-calls.md`) and triggered by method-call auto-mutable-borrowing (`rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `src/expressions/method-call-expr.md`, `r[expr.method.autoref-deref]`), two-phase borrows allow nested arguments of a `&mut self` method call (e.g., `v.push(v.len())`) to read `self` before the `&mut self` call activates:

1. **THIR construction (`compiler/rustc_mir_build/src/thir/cx/expr.rs:1751-1768`):** Only implicit method-call / overloaded-operator auto-borrows carry `AutoBorrowMutability::Mut { allow_two_phase_borrow: AllowTwoPhase::Yes }`, mapping via `ToBorrowKind::to_borrow_kind` to `BorrowKind::Mut { kind: mir::MutBorrowKind::TwoPhaseBorrow }`. Explicit `&mut v` expressions (`AllowTwoPhase::No` / `hir::Mutability::Mut`) produce `MutBorrowKind::Default` (`expr.rs:1762, 1773`). Note that NLL/built MIR pretty-printers render both as `&mut _1`, as observed in our captured `c1` dumps (`c1_two_phase_shared_read_before_activation_ok.two_phase_shared_read.1-1-000.built.after.mir` and `-------.nll.0.mir`: `_5 = &mut _1; _7 = &_1; _6 = Vec::<usize>::len(move _7); _4 = Vec::<usize>::push(move _5, move _6);`).
2. **MIR `BorrowSet::build` (`compiler/rustc_borrowck/src/borrow_set.rs:443-569`):**
   - `MutBorrowKind::Default` (non-2-phase) initializes `BorrowData.activation_location = TwoPhaseActivation::NotTwoPhase`.
   - `MutBorrowKind::TwoPhaseBorrow` asserts the borrow assigns into a MIR local temporary (`TEMP = &mut place`), registers `BorrowData` with `TwoPhaseActivation::NotActivated` at `reserve_location`, and stores `pending_activations.insert(temp, idx)` (`L453-473`).
   - When `GatherBorrows::visit_local` sees the unique non-store use `is_use()` of `temp` (`L524-569`, e.g., passing `move _5` to `Vec::push`), it asserts the borrow is still `NotActivated` and transitions `activation_location` to `TwoPhaseActivation::ActivatedAt(location)`, recording `activation_map[location].push(borrow_index)`.
3. **Activation-window predicate (`compiler/rustc_borrowck/src/path_utils.rs:60-120`):** `is_active(dominators, borrow_data, location)` returns `true` unconditionally for `NotTwoPhase`, `false` for `NotActivated`, and otherwise uses a **two-query dominator approximation** (`R` -> `A` diamond):
   - If `activation_location.dominates(location, dominators)` -> `true` (active at/after `A`, noting edge-case caveats documented in [Boundaries](#boundaries)).
   - Else if `borrow_data.reserve_location.successor_within_block().dominates(location, dominators)` -> `false` (strictly inside the reservation-to-activation window!).
   - Else -> `true` (conservatively active outside the diamond).
4. **Access-conflict matrix & activation checks (`compiler/rustc_borrowck/src/lib.rs:1307-1375, 1872-1895` and `places_conflict.rs:81-128`):**
   - **Rule A — New Reservation (`Reservation(_)` vs. existing `BorrowKind::Shared`, `lib.rs:1313`):** Starting a two-phase reservation while a prior shared borrow `&v[0]` is in scope is **permitted** (`ControlFlow::Continue(())`).
   - **Rule B — Shared Read While Reserved (`Read(kind)` vs. existing `BorrowKind::Mut`, `lib.rs:1324-1329`):** Reading `v` (`v.len()`, `*r`) does **not** conflict if `!is_active(this.dominators(), borrow, location)` (asserting `borrow.kind.is_two_phase_borrow()`). Once activated, any read fails (`E0502`).
   - **Rule C — Conflicting Write or Second Reservation (`Reservation(_) | Activation(_, _) | Write(_)`, `lib.rs:1347-1375`):** Any mutation (`v.clear()`), nested `&mut2` reservation (`v.push({ v.push(99); 42 })`), or activation overlapping another active/reserved borrow fails immediately (`E0499`/`E0502`), and `reservation_error_reported` records the failure.
   - **Rule D — Delayed Activation Check (`check_activations`, `lib.rs:1872-1895`):** At each `activation_location`, `borrowck` calls `self.access_place(location, (borrow.borrowed_place, span), (Deep, Activation(WriteKind::MutableBorrow(borrow.kind), borrow_index)), ...)` (skipping `activating == borrow_index` at `lib.rs:1295-1305`), rejecting if any prior shared borrow from Rule A is still live in `state` at `A`!

Empirical runs (`c1`..`c6`) verify every rule identically across `Off`, `Next`, `Legacy`, `1.98.0-nightly`, and preserved `1.102.0-nightly` / `1.100.0`:

| Case | Program Shape | Borrowck Result & Diagnostic | Governed Source Rule |
|---|---|---|---|
| `c1` | `v.push(v.len())` | **Ok** (`rc=0`) | `bw0` reserved at `bb3[4]`, `len` read at `bb3[8]` where `!is_active`, activated at `bb4[1]` (`Rule B`) |
| `c2` | `v.push({ v.clear(); 42 })` | **Err `E0499`** (`cannot borrow 'v' as mutable more than once at a time`) | Nested write/reservation while `bw0` is reserved (`Rule C`, `lib.rs:1347`) |
| `c3` | `v.push({ v.push(99); 42 })` | **Err `E0499`** (`cannot borrow 'v' as mutable more than once at a time`) | Nested `Reservation` while `bw0` is reserved (`Rule C`, `lib.rs:1347`) |
| `c4` | `let r = &mut v; let len = v.len(); r.push(len);` | **Err `E0502`** (`cannot borrow 'v' as immutable because it is also borrowed as mutable`) | Explicit `&mut v` sets `TwoPhaseActivation::NotTwoPhase`, so `is_active == true` (`Rule B` rejects) |
| `c5` | `let r = &v[0]; v.push(*r); v.len()` | **Ok** (`rc=0`) | `Reservation` allowed during live shared `r` (`Rule A`, `lib.rs:1313`); `*r` finishes before `ActivatedAt(push)` (`Rule D`) |
| `c6` | `let r = &v[0]; v.push(*r); *r` | **Err `E0502`** (`cannot borrow 'v' as mutable because it is also borrowed as immutable`) | Shared `r` still live at `check_activations` (`Rule D`, `lib.rs:1872-1895`) |

#### Tree Borrows Operational Correspondence under Miri (`-Zmiri-tree-borrows`)

In `src/tools/miri/src/borrow_tracker/tree_borrows/perms.rs:135-233`, Tree Borrows separates **unprotected** two-phase borrows (created at `&mut2` argument reservation with no active function-call protector) from **protected** function-entry `&mut` retags:

- **Unprotected `Reserved` (`protected = false`):** `foreign_read` (`perms.rs:164-170`) leaves both `ReservedFrz` and `ReservedIM` unchanged (`assert!(!protected)`), and `child_write` (`perms.rs:196`) promotes `Reserved -> Unique`. Thus both `tb_two_phase_vec_push_len` (`c1`, stdout `len=4 last=3`) and `tb_two_phase_prior_shared_read` (`c5`, stdout `len=4 last=10`) execute cleanly under Miri `0.1.0` (`-Zmiri-tree-borrows`, `rc=0`).
- **Protected `ReservedFrz` (`protected = true`):** When a function parameter `x: &mut i32` enters with a protector (`tb_protected_mut_foreign_read_ub`), reading through a foreign raw alias `*raw` triggers `ReservedFrz { conflicted: true }` (`perms.rs:161`), and subsequently writing `*x = 99` (`child_write`) hits `ReservedFrz { conflicted: true } if protected => return None` (`perms.rs:193`). Live Miri `-Zmiri-tree-borrows` aborts (`rc=1`) with exact diagnostic: `the accessed tag <309> has state Reserved (conflicted) which forbids this child write access`.

---

### Part V — Kernel-Checked Lean 4 Formalization (`PoloniusTriadMemberConstraintsAndTwoPhaseSoundness.lean`)

```text
Basis: source + derived + execution
```

`support/PoloniusTriadMemberConstraintsAndTwoPhaseSoundness.lean` (`1,832` lines, `71,518` bytes, `62` theorems, `55` definitions, `17` inductives, `8` structures) mechanizes all three subsystems constructively in Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) with zero imports beyond `Init` and zero non-constructive axioms. Its key proven theorems are:

1. **CLI Flag Triad & Era Delta (`Lines 154-245`):** `defaultPoloniusMode`, `parsePoloniusFlag`, `effectivePoloniusMode`, plus theorems `cli_triad_exact_disambiguation` (exhaustive disambiguation on post-`1.98` nightly builds: bare `-Zpolonius` -> `.legacy`, `noFlag` -> `.next`, `-Zpolonius=off`/`no` -> `.off`, pre-`1.98` `-Zpolonius=off` -> `none`), `post199_nightly_off_matches_stable_default`, and `post199_nightly_bare_differs_from_default`.
2. **Localized Reachability Hierarchy, Time-Travel Soundness, and 3-Way Strict Separation (`Lines 247-1029`):**
   - `off_accepts_implies_next_accepts`: Every `OffAccepts sys` system satisfies `NextAccepts sys` (`NextReach` implies `NllSubset`, and universal-pair checking is identical).
   - `next_accepts_implies_legacy_accepts_of_bidir` & `next_accepts_implies_operational_safe_of_bidir`: When all origins carry `.bidir` (existential invariant), `NextAccepts` implies `LegacyAccepts` and `OperationalSafe`.
   - **Witnesses & `polonius_three_way_strict_separation`:**
     - `pc3Graph` (`pc3Graph_not_offAccepts`, `pc3Graph_nextAccepts`, `pc3Graph_legacyAccepts`, `pc3Graph_operationalSafe`): Note an authentic formal discovery—modeling universal origin `0` (`'a`) as `.bidir` would allow return-arm loans to step *backwards* from `(0, 1)` to `(0, 0)` and then forward to `(0, 2)`, making `pc3Graph_nextAccepts` *false*! Setting `pc3Graph.dirOf 0 = .fwd` directly mechanizes `polonius/liveness.rs:32,41-42` (`if is_universal_region { ConstraintDirection::Forward }`), under which `pc3Graph_nextReach_inversion` holds cleanly and both `NextAccepts` and `LegacyAccepts` hold while `OffAccepts` fails.
     - `invarianceGraph` (`invarianceGraph_not_nextAccepts`, `invarianceGraph_not_offAccepts`, `invarianceGraph_legacyAccepts`): Separates `Legacy` (accepts) from both `Next` and `Off` (reject) over disjoint `if`/`else` CFG branches.
     - `polonius_three_way_strict_separation`: Combines both witnesses to prove `¬ (∀ sys, NextAccepts sys → OffAccepts sys)` and `¬ (∀ sys, LegacyAccepts sys → NextAccepts sys)`, alongside `covariantGraph_accepted_by_all_three` (`a4`) and `timeTravelGraph_withBwd_rejects` vs. `timeTravelGraph_noBwd_falsely_accepts` (`a5`: dropping backward invariant liveness unsoundly accepts unsafe mutation!).
3. **RPIT Edition Capture & `member_constraints` Lattice Minimization (`Lines 949-1510`):**
   - `edition2024_rpit_delta_exact`: Proves the exact boolean truth table of `opaqueCapturesAllInScopeLifetimes` across free functions, inherent methods, and trait/impl RPITITs with/without `use<...>` in Edition 2021 vs. 2024.
   - `applyMemberConstraint_sound`: For arbitrary finite `RegionPreorder`, any chosen `m` returned by `applyMemberConstraint rel p = some m` belongs to `0 :: p.argRegions`, outlives every `lb ∈ p.lowerBounds`, and is outlived by every `ub ∈ p.upperBounds`.
   - `applyMemberConstraint_minimal`: Any chosen `m` is outlived by **every** member of `totallyOrderedChoices rel (admissibleChoices rel p)`.
   - `member_constraints_empirical_correspondence`: Verifies concrete instances matching `b4` (`none` -> `E0700`), `b5` (`some 2` = `'b`), `b6` (`some 1` = `'a`), `b7` (`some 0` = `'static` cleanly via `totallyOrderedChoices` discarding incomparable `'a, 'b`), and `b8` (`some 3` = `'c` cleanly via diamond partial order, not `'static`).
4. **`TwoPhaseBorrow` & Unprotected Tree Borrows Correspondence (`Lines 1512-1832`):**
   - `borrowckStep_preserves_invariant` & `borrowckTrace_no_write_or_read_race_when_activated`: Proves by induction over arbitrary finite traces `tr : List TwoPhaseAction` that entering `.activated` guarantees `priorSharedCount = 0 ∧ otherMutActive = false`.
   - `borrowck_step_unprotected_tb_sound`: Step-wise simulation proving that for any borrowck-accepted action on an unprotected two-phase borrow (`isProtected = false`), Tree Borrows never hits UB (`none`), preserves `TBMatchesBorrowck st' tb'` (including freezing `.tbUnique` -> `.tbFrozen` on foreign reads after `.released`), while `protected_foreign_read_then_child_write_is_tb_ub` witnesses `runTBTrace true (.tbReserved false) [.foreignRead, .childWrite] = none`.
   - `twoPhase_empirical_correspondence`: Mechanizes exact trace parity for `c1`..`c6` and Miri protected vs. unprotected runs.

Kernel purity verification (`-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` plus `#print axioms` on all `117` top-level declarations) confirmed exit code `0`, `0` errors/warnings, and `0` uses of `Classical.choice`, `sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler`, or `._unsafe_rec`.

---

### Part VI — Implications for Anneal Verified-`rustc` Capture (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`)

```text
Basis: source + derived
```

Inspecting `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` establishes three concrete boundary interactions with the `rustc_borrowck` findings above:

1. **Erase-Before-Capture (`MirAst.lean:304-320, 608`):** Anneal's MIR syntax `MirTy.ref (mutability : Mutability) (pointee : MirTy)` erases `ty::Region` and `Rvalue.ref (mutability : Mutability) (place : Place)` erases `mir::BorrowKind` (collapsing `Shared`, `Mut { kind: Default }`, and `Mut { kind: TwoPhaseBorrow }` into binary `Mutability`). Consequently, Anneal's Lean semantics has no representation of lifetime parameters, RPIT member constraints, or two-phase activation windows and instead relies wholly on `rustc_borrowck` prior to capture.
2. **Fail-Closed Reference Execution (`MirSemantics.lean:1313`):** In the current operational semantics (`evalRvalue`), unsupported Rvalues and reference/retag operations fall through to `.error .unsupported`. When Anneal later extends `MirSemantics` to execute `&mut` / `&mut2` borrows and retagging (`Use(_, WithRetag::Yes)` per `MirAst.lean:595-597`), unprotected two-phase reservation writes cannot be treated as immediately `Unique` across intervening reads (`v.push(v.len())`), matching the Tree Borrows separation proven in Part IV.
3. **Driver Borrowck Mode Dependence (`trusted/rustc-capture/src/driver.rs:25-84`):** `AnalysisCallbacks::config` pins `COMPILER_VERSION = "1.98.0-nightly (f8a08b688 2026-05-30)"`, and `after_analysis` checks `self.analysis_reached = tcx.dcx().has_errors().is_none()` without inspecting `tcx.sess.opts.unstable_opts.polonius`. On `1.98.0-nightly`, upstream crates invoking `Anneal` without `-Zpolonius` get `Polonius::Off` (`NLL`), whereas bumping Anneal's pinned compiler past the `CFG_DEFAULT_POLONIUS_NEXT` flip will silently run `Polonius::Next` (accepting `a1`/`a2` Problem Case #3 patterns while rejecting `a3`) unless `-Zpolonius=off` vs. `=next` is explicitly enforced in the capture driver or caller flags.

---

## Boundaries

Every limitation and excluded question is tagged explicitly below:

- **[not examined — upstream git commit bisect]:** We confirmed `Polonius::DEFAULT == Polonius::Off` in `rustc 1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`), `Polonius::DEFAULT == Polonius::Next` in `rustc 1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, recorded in `support/preserved_1_102_nightly_and_1_100_stable_results.json`), and `CFG_DEFAULT_POLONIUS_NEXT` in `rust-lang/rust` `main` (`fde8dfd638478da758f93f0e8d9b74d7907f0c9e`), but did not bisect `git log` between `1.98.0` and `1.102.0` to identify the exact PR/commit that toggled the default.
- **[unsupported on local host toolchain — live `+stable` and `1.102.0-nightly` execution]:** Only `rustc 1.98.0-nightly` (`14210df0e27c`) and `miri 0.1.0` (`14210df0e27c`) are installed in the local offline execution environment; `+stable` and `1.102.0-nightly` toolchains were not re-executed live here. Their behavior (`1.102.0-nightly` at `3ef0c22cdb86` and `1.100.0` at `0ef1bc386059` across `a1..a3`, `b1..b6`, `c1..c4`) comes from preserved artifacts (`support/preserved_1_102_nightly_and_1_100_stable_results.json`) paired with direct upstream `main` source inspection (`fde8dfd63847`). Cases added in our expanded live probe (`a4`, `a5`, `b7`, `b8`, `c5`, `c6`, and Miri Tree Borrows) have direct execution on `1.98.0-nightly` (`probe_polonius_triad_member_constraints_and_two_phase_results.json`) and were **not** part of the earlier `1.102.0-nightly`/`1.100.0` preserved archive (**[not examined]** on `1.102.0`/`1.100.0`).
- **[known not to apply beyond checked models — abstraction gap of Lean 4 formalization]:** `PoloniusTriadMemberConstraintsAndTwoPhaseSoundness.lean` formalizes: (i) finite point-indexed borrow/origin graph abstractions rather than full MIR `Body`, projections (`PlaceElem`), `MoveData`, or Datalog `polonius-engine` fixed-point rules (`origin_contains_loan_at` vs. `subset_error` base facts), (ii) finite `RegionPreorder` member-constraint selection rather than placeholder universes (`!max_placeholder_universe_reached(member).is_root()`), type-test obligations, or closure-outlives propagation, and (iii) a single-borrow sequential two-phase automaton rather than multi-borrow aliasing trees or MIR unwinding/early-exit edges where `path_utils::is_active` dominator assumptions (`A` post-dominates `R` ignoring unwind) can misclassify loop/early-exit blocks. Consequently, our Lean theorems establish exact properties of the extracted models (`Off ⊊ Next ⊊ Legacy` witness graphs, `apply_member_constraint` lattice minimization, single-borrow exclusivity + unprotected TB step simulation), **not** end-to-end soundness of `rustc_borrowck`.
- **[not examined — higher-ranked `for<'a>` RPIT / placeholder interactions]:** While `apply_member_constraint` bails out when `!rcx.max_placeholder_universe_reached(member).is_root()` (`member_constraints.rs:66-69`), no empirical HRTB/placeholder `member_constraint` failure test cases were executed (`b1`..`b8` operate solely in `UniverseIndex::ROOT`).
- **[not examined — MIR `-Zpolonius=next` Datalog fact-dump equivalence outside `a1..a5`]:** `-Zdump-mir=nll` and `-Zpolonius` comparison on real crates beyond minimal 5–15 line reproducers (e.g., `zerocopy` proc-macro/unsafe internals) was not run in this study.

---

## Evidence

### Acquisition Timeline and Provenance

- **Upstream source inspection & live probes:** Acquired **`2026-11-23`** on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` / `miri 0.1.0` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`), `rust-lang/rust` main (`fde8dfd638478da758f93f0e8d9b74d7907f0c9e`), `rust-lang/reference` (`c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`), `rust-lang/rfcs` (`f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`), `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`), and Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`).
- **Preserved post-flip nightly / stable differential dataset (`support/preserved_1_102_nightly_and_1_100_stable_results.json`):** Acquired **`2026-11-11`** (`rustc 1.102.0-nightly` at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`) and **`2026-11-09`** (`rustc 1.100.0` at `0ef1bc386059596dada8fb65b50425aab2ea637a`), paired with upstream source snapshot `49d734536222bf28bb6d07d885b3a81d145981da`.

### Primary Source Index

| Subject / Revision | File & Line Range / Symbol | Role |
|---|---|---|
| `rust-lang/rust` (`fde8dfd638478da758f93f0e8d9b74d7907f0c9e`) | `src/bootstrap/src/core/build_steps/compile.rs:1374-1378` (`CFG_DEFAULT_POLONIUS_NEXT`) | `source` |
| `rust-lang/rust` (`fde8dfd638478da758f93f0e8d9b74d7907f0c9e`) | `compiler/rustc_session/src/config.rs:3837-3868` (`Polonius`, `Polonius::DEFAULT`) | `source` |
| `rust-lang/rust` (`fde8dfd638478da758f93f0e8d9b74d7907f0c9e`) | `compiler/rustc_session/src/options.rs:1065-1081, 2458-2462, 2877-2878` (`parse_polonius`, `POLONIUS_HELP`) | `source` |
| `rust-lang/rust` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`) | `compiler/rustc_session/src/config.rs:3321-3344`, `options.rs:910-922, 2536-2537` (`#[default] Off`) | `source` |
| `rust-lang/rust` (`fde8dfd638478da758f93f0e8d9b74d7907f0c9e`) | `compiler/rustc_borrowck/src/nll.rs:114-254` (`compute_regions`, `PoloniusContext::compute_loan_liveness`, `Output::compute`) | `source` |
| `rust-lang/rust` (`fde8dfd638478da758f93f0e8d9b74d7907f0c9e`) | `compiler/rustc_borrowck/src/dataflow.rs:398-412` (`Borrows::new`, `PoloniusOutOfScopePrecomputer`) | `source` |
| `rust-lang/rust` (`fde8dfd638478da758f93f0e8d9b74d7907f0c9e`) | `compiler/rustc_borrowck/src/region_infer/region_context.rs:213-229, 1340-1430` (`check_polonius_subset_errors` vs. `check_universal_regions`) | `source` |
| `rust-lang/rust` (`fde8dfd638478da758f93f0e8d9b74d7907f0c9e`) | `compiler/rustc_borrowck/src/polonius/{mod.rs:145-230, constraints.rs:34-243, liveness.rs:24-57, liveness_constraints.rs:63-82}` | `source` |
| `rust-lang/rust` (`fde8dfd638478da758f93f0e8d9b74d7907f0c9e`) | `compiler/rustc_borrowck/src/polonius/legacy/mod.rs:1-67` (`emit_facts`) | `source` |
| `rust-lang/rust` (`fde8dfd638478da758f93f0e8d9b74d7907f0c9e`) | `compiler/rustc_borrowck/src/constraints/mod.rs:18-114` (`OutlivesConstraintSet`, `ConstraintSccIndex`) | `source` |
| `rust-lang/rust` (`fde8dfd638478da758f93f0e8d9b74d7907f0c9e`) | `compiler/rustc_borrowck/src/region_infer/opaque_types/{mod.rs:285-320, member_constraints.rs:45-139}` (`collect_defining_uses`, `apply_member_constraint`) | `source` |
| `rust-lang/rust` (`fde8dfd638478da758f93f0e8d9b74d7907f0c9e`) | `compiler/rustc_mir_build/src/thir/cx/expr.rs:1751-1777` (`ToBorrowKind`, `MutBorrowKind::TwoPhaseBorrow`) | `source` |
| `rust-lang/rust` (`fde8dfd638478da758f93f0e8d9b74d7907f0c9e`) | `compiler/rustc_borrowck/src/{borrow_set.rs:22-80,443-586, path_utils.rs:60-120, lib.rs:1295-1375,1872-1896, places_conflict.rs:81-239}` | `source` |
| `rust-lang/rust` (`fde8dfd638478da758f93f0e8d9b74d7907f0c9e`) | `src/tools/miri/src/borrow_tracker/tree_borrows/perms.rs:135-233` (`perform_access`, `ReservedFrz`, `ReservedIM`) | `source` |
| `rust-lang/reference` (`c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`) | `src/types/impl-trait.md:59-120`, `src/expressions/method-call-expr.md:21-94` | `normative` |
| `rust-lang/rfcs` (`f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`) | `text/2025-nested-method-calls.md`, `text/2094-nll.md`, `text/3498-lifetime-capture-rules-2024.md` | `documentation` |
| `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`) | `trusted/lean/Trusted/{MirAst.lean:295-320,608-625, MirSemantics.lean:1313}`, `trusted/rustc-capture/src/driver.rs:25-95` | `source` |

### Preserved Support Artifacts (`support/`)

1. `support/probe_polonius_triad_member_constraints_and_two_phase.py` (`execution` harness): Self-contained Python 3 differential runner executing 19 Rust borrowck cases across 5 `-Zpolonius` modes (`nightly_default_no_flag`, `-Zpolonius=off`, `-Zpolonius`, `-Zpolonius=next`, `-Zpolonius=legacy`), optional `--stable-rustc`, 5 MIR/dot/NLL captures (`-Zdump-mir=nll|built`), and 3 Miri `-Zmiri-tree-borrows` tests, scrubbing temporary paths/toolchains deterministically.
2. `support/probe_polonius_triad_member_constraints_and_two_phase_results.json` (`execution` output, `2026-11-23`): Full machine-readable output on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` / `miri 0.1.0` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`), including exact `-Zpolonius=off` rejection, all 19 × 5 exit/error results (`a1..a5`, `b1..b8`, `c1..c6`), NLL/built MIR dumps (`flow_sensitive_invariance` SCC collapse and `two_phase_shared_read` `bw0` issue/call points), and Miri TB UB trace on `<309> Reserved (conflicted)`.
3. `support/preserved_1_102_nightly_and_1_100_stable_results.json` (`execution` output, `2026-11-11` / `2026-11-09`): Preserved differential archive covering `a1..a3`, `b1..b6`, `c1..c4` across `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)` (`Polonius::DEFAULT == Next`, `-Zpolonius=off` accepted) and `rustc 1.100.0 (0ef1bc386 2026-11-09)` (`+stable`), plus `c1` NLL MIR dump (`rustc 1.102.0-nightly`).
4. `support/PoloniusTriadMemberConstraintsAndTwoPhaseSoundness.lean` (`derived` mechanized proofs): `1,832`-line kernel-checked Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) development compiling cleanly with exit code `0` under `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`; per-declaration `#print axioms` audit across all `117` top-level `theorem`/`def` entries confirms zero `Classical.choice`, zero `sorryAx`, zero `Lean.ofReduceBool`, zero `Lean.trustCompiler`, and zero `._unsafe_rec`.

---

## Revalidation

Each claim above can be revalidated cleanly and independently without re-running full research:

1. **Differential `rustc` & Miri execution probe (~25 seconds):**
   ```bash
   python3 reports/rustc-borrowck-polonius-flag-triad-rpit-member-constraints-and-two-phase-borrows/support/probe_polonius_triad_member_constraints_and_two_phase.py \
     --rustc "$(rustup which rustc)" \
     --cargo "$(rustup which cargo)" \
     --out /tmp/polonius_reval.json
   ```
   Pass `--stable-rustc "$(rustup +stable which rustc)"` when a stable toolchain is installed to compare `-Zpolonius=off` against `+stable` in the same run. Inspect `compiler_info.polonius_z_help` and `experiments.a3_polonius_3way_separator_flow_sensitive_invariance.modes` to test whether a future nightly's `Polonius::Next` has closed the `check_polonius_subset_errors` gap (`rc=1 -> 0` on `a3` under `-Zpolonius=next`).

2. **Kernel Lean 4 verification (`v4.34.1`, ~15 seconds):**
   ```bash
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     reports/rustc-borrowck-polonius-flag-triad-rpit-member-constraints-and-two-phase-borrows/support/PoloniusTriadMemberConstraintsAndTwoPhaseSoundness.lean
   ```
   Confirm exit code `0` with no output, and append `#print axioms PoloniusTriadSoundness.<theorem>` to a scratch copy in `/tmp` to re-verify pure axiom cleanliness (`propext`, `Quot.sound` at most; no `Classical.choice` or `sorryAx`).

3. **Targeted upstream source drift checks:**
   - Diff `compiler/rustc_session/src/config.rs` (`Polonius::DEFAULT`), `compiler/rustc_session/src/options.rs` (`parse_polonius`), and `compiler/rustc_borrowck/src/region_infer/region_context.rs` (`if ... polonius.is_legacy_enabled()`) to check if `-Zpolonius=next` gains flow-sensitive universal-region checking (`check_polonius_subset_errors`) or removes `Legacy`.
   - Diff `compiler/rustc_borrowck/src/region_infer/opaque_types/member_constraints.rs` (`apply_member_constraint`) and `compiler/rustc_borrowck/src/path_utils.rs` (`is_active`) to detect changes to RPIT choice minimization or two-phase activation dominance assumptions.
