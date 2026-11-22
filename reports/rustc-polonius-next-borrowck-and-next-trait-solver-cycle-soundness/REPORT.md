# `rustc` `Polonius::Next` Borrow Checking, `rustc_next_trait_solver` Cycle Polarity, and `-Z assumptions-on-binders` Higher-Ranked Soundness

## Summary

Across `rustc` revisions spanning `1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`), `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`), `1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`), and upstream `main` (`342d74463af7dd3018ef6aa04dd5500c2deb5bd1`), `rustc`'s frontend analysis boundary has shifted in three load-bearing ways that directly govern compiler soundness and the Trusted Computing Base (TCB) of any MIR-level verifier such as Anneal (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`):

1. **`Polonius::Next` Is Now the Nightly/Dev Default Borrow Checker via Channel-Gated Bootstrap Environment Variables (`CFG_DEFAULT_POLONIUS_NEXT`), Using an In-Tree `DenseBitSet<usize>` Reachability Graph Instead of Datalog:**
   - Primary-source inspection of `src/bootstrap/src/core/build_steps/compile.rs`, `compiler/rustc_session/src/config.rs`, and `compiler/rustc_session/src/options.rs` establishes that `Polonius::DEFAULT` evaluates `option_env!("CFG_DEFAULT_POLONIUS_NEXT").is_some()`. Stable `1.99.1` builds leave that environment variable unset (`Polonius::Off`, flow-insensitive NLL), whereas `nightly` and `dev` builds (such as `1.102.0-nightly` and `main`) set `CFG_DEFAULT_POLONIUS_NEXT=1` (and, by `1.102.0-nightly`, also `CFG_DEFAULT_NEXT_SOLVER_GLOBALLY=1`), enabling `Polonius::Next` by default.
   - Unlike legacy `-Zpolonius=legacy` (Datalog `polonius-engine`), `Polonius::Next` (`compiler/rustc_borrowck/src/polonius/{mod.rs,constraints.rs,liveness.rs,liveness_constraints.rs}`) packs loan liveness into `LiveLoans { num_points: usize, flat_matrix: DenseBitSet<usize> }` (`bit_index = row.index() + num_points * col.index()`) and runs a lazy per-loan DFS over `LocalizedNode { region: RegionVid, point: PointIndex }` with on-demand `DeferredRegionLiveness` and variance-directed CFG edges (`Forward`, `Backward`, `Bidirectional` for invariant regions to enable loans to "flow back in time" to earlier aliasing constraints).
   - Empirically, `Polonius::Next` accepts NLL Problem Case #3 (`HashMap::get_mut` conditional return), loop-conditional `&mut` return, and conditional slice reborrow-then-mutate (all rejected with `E0499`/`E0503` under `1.98.0-nightly` default, `1.99.1`, and `1.102.0-nightly -Zpolonius=off`), while preserving rejection of aliasing escapes and invariant backward-flow conflicts. On full-crate `google/zerocopy` (`0.8.64`, `907b9175fee081872ec883ca4709e6ad922f8ed0`), `Polonius::Next` adds `+9.21%` median wall time on `1.98.0-nightly` (`4.5021 s` vs `4.1225 s` across 5 trials; `+14.1%` single-trial `1.646 s` vs `1.443 s` on `1.102.0-nightly`), compared to `+237.97%` (`13.9328 s`, `3.38x` slower than NLL and `3.09x` slower than `Polonius::Next`) for Datalog `-Zpolonius=legacy`.
   - Crucially, `compiler/rustc_borrowck/src/polonius/mod.rs:221-258` documents an explicit open soundness `FIXME`: collapsing the two transitive closures of full Polonius into a single graph reachability query interacts subtly with flow-insensitive kills during backward ("time-travel") traversal.

2. **`rustc_next_trait_solver` Prevents Coherence Overlap Soundness Bugs by Never Returning `Err(NoSolution)` for Inductive Cycles in `TypingMode::Coherence` — and Tightened All Unproductive Cycles to Ambiguity in Commit `622fd6a3f80f`:**
   - In `1.98.0-nightly` (`14210df0e27c`), `1.99.1` (`58cf8f9c35b3`), and `49d734536222`, `SearchGraphDelegate::initial_provisional_result` (`compiler/rustc_next_trait_solver/src/solve/search_graph.rs`) implemented an explicit 3-way dispatch: `PathKind::Coinductive -> Certainty::Yes`, `PathKind::Unknown | PathKind::ForcedAmbiguity -> Certainty::overflow(false)`, and `PathKind::Inductive -> Certainty::overflow(false)` under `TypingMode::Coherence` versus `Err(NoSolution)` under all non-coherence modes (`Typeck`, `PostTypeckUntilBorrowck`, `Reflection`, `PostBorrowck`, `PostAnalysis`, `Codegen`, `ErasedNotCoherence`).
   - In commit `622fd6a3f80ff4398db552ed138243c845347298` (`2026-09-22`, `"treat inductive cycles as ambig"`), present in `1.102.0-nightly` (`3ef0c22cdb86`) and `main` (`342d74463af7`), `rustc_next_trait_solver` tightened this further: `eval_ctxt/mod.rs` maps `GoalSource::TypeRelating` to `PathKind::Unknown`, `step_kind_to_nested` never produces `PathKind::Inductive`, and `search_graph.rs:69` sets `PathKind::Inductive => unreachable!()`. Both before and after `622fd6a3f80f`, coherence treats inductive cycles as ambiguity (`Certainty::overflow(false)`), forcing `E0119` overlap rejection on both `impl<T: Loop> Disjoint for T` / `impl Disjoint for u32` and `tests/ui/traits/next-solver/cycles/unproductive-in-coherence.rs`, while typechecking still accepts coinductive recursive auto traits (`struct Rec(Option<Box<Rec>>): Send`) and rejects inductive cycles (`u32: Loop`) with `E0275`.

3. **`-Z assumptions-on-binders=yes` Introduces a Safe-Rust Use-After-Free Soundness Cliff (`rust-lang/rust#25860`), Confirmed Live Under Miri:**
   - Both legacy trait solving and `-Z next-solver=globally` reject `rust-lang/rust#25860` (`fn extend_lifetime<'a, T>(x: &'a T) -> &'static T` via `fn foo<'a, 'b, T>(_: &'a &'b (), v: &'b T) -> &'a T`) with `error: lifetime may not live long enough`.
   - Enabling `-Z assumptions-on-binders=yes` causes `EvalCtxt::enter_forall_with_assumptions` (`eval_ctxt/mod.rs:1427-1448`) and `region_assumptions_for_placeholders_in_universe` (`solver_region_constraints.rs:31-111`) to extract `well_formed_goals` from unverified binder types (`&'static &'a ()`) and insert them as placeholder assumptions, discharging `'a: 'static` without verifying well-formedness in the outer environment. Live execution under `miri 0.1.0 (14210df0e2 2026-05-31)` with `RUSTFLAGS="-Znext-solver=globally -Zassumptions-on-binders=yes"` compiles the 100% safe-Rust program cleanly and fails at runtime with `rc = 1`: `error: Undefined Behavior: constructing invalid value of type &std::string::String: encountered a dangling reference (use-after-free)` (reproducing the `1.102.0-nightly` Miri UAF result verbatim).

4. **Kernel-Checked Lean 4 (`v4.34.1`) Mechanization (`support/PoloniusAndNextSolverCycleSoundness.lean`, 921 lines):**
   - Verified under `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` with exit code `0`, zero unproved goals, zero `Classical.choice`, zero `Lean.ofReduceBool`, and zero forbidden tactics or partial recursion (`#print axioms` reports only `[]`, `[propext]`, or `[propext, Quot.sound]`).
   - Proves three positive soundness/precision theorems (`polonius_sound_and_strictly_more_precise_than_nll`, `coherence_inductive_ambiguity_prevents_overlapping_impls`, `wf_guarded_binder_assumptions_preserve_lifetime_soundness`) and three constructive counterexamples isolating each failure mode (`ce1_omitting_bidirectional_invariant_edge_admits_aliasing_ub`, `ce2_returning_no_solution_for_inductive_cycle_in_coherence_admits_overlapping_impls`, `ce3_unwf_binder_assumption_derives_arbitrary_lifetime_extension_25860`).

---

## Applicability

This report documents the interaction and evolution of `rustc`'s borrow checker (`rustc_borrowck::polonius`) and next-generation trait solver (`rustc_next_trait_solver` / `rustc_type_ir`) across four concrete `rust-lang/rust` revisions, linked to `joshlf/anneal`'s capture boundary, `google/zerocopy`'s compilation profile, and a standalone Lean 4 (`v4.34.1`) formalization:

| Subject | Exact Revision / Tag | Role in This Report |
| :--- | :--- | :--- |
| `rust-lang/rust` (`main`) | `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | Upstream primary-source audit (`polonius/`, `search_graph.rs`, `eval_ctxt/`, `region_constraint.rs`, `options.rs`, `config.rs`, `compile.rs`, `unproductive-in-coherence.rs`). |
| `rust-lang/rust` (`1.102.0-nightly`, `2026-11-11`) | `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | Primary-source audit and reference empirical matrix (`LLVM 23.1.5`) where both `CFG_DEFAULT_POLONIUS_NEXT=1` and `CFG_DEFAULT_NEXT_SOLVER_GLOBALLY=1` are active on nightly (`support/rustc_1_99_1_vs_1_102_0_nightly_reference_matrix.json`). |
| `rust-lang/rust` (`1.99.1` stable) | `58cf8f9c35b355199727627d07ae34a4e2846d67` | Stable release primary-source audit and baseline matrix (`Polonius::Off` default, `-Zpolonius=off` parser support, explicit `TypingMode::Coherence` vs non-coherence `PathKind::Inductive` dispatch, auto-implied `-Znext-solver=globally` for `-Zassumptions-on-binders`). |
| `rust-lang/rust` (`1.98.0-nightly`, `2026-05-31`) | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | Live locally executed toolchain (`rustc 1.98.0-nightly`, `miri 0.1.0`, `LLVM 22.1.6`) running all snippets, Miri `#25860` UAF execution, and 5-trial `zerocopy` stress benchmarks (`support/probe_polonius_and_next_solver_results.json`). |
| `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | MIR capture TCB audit (`trusted/rustc-capture/src/driver.rs`, `trusted/audit/TrustedBoundary.lean`, `THREAT_MODEL.md`, `docs/trust-model.md`). Pins `COMPILER_VERSION = "1.98.0-nightly (f8a08b688 2026-05-30)"`. |
| `google/zerocopy` (`0.8.64`) | `907b9175fee081872ec883ca4709e6ad922f8ed0` | Real-world `#![no_std]` library crate compiled under five borrowck/solver flag configurations (`--no-default-features`, `--emit=metadata`). |
| `leanprover/lean4` (`v4.34.1`) | `5045d0056413266e57c625dcd7c365b10e377c52` | Kernel checking environment for `support/PoloniusAndNextSolverCycleSoundness.lean`. |

### Version-Specific vs. Shared Behaviors

- **Shared across all four `rustc` revisions (`1.98.0-nightly`, `1.99.1`, `1.102.0-nightly`, `main`):**
  - `Polonius::Next` accepts NLL Problem Case #3, loop-conditional `&mut` return, and conditional slice reborrow-then-mutate, while rejecting aliasing `&mut` escapes and invariant backward-flow conflicts (`E0499`/`E0506`).
  - `rustc_next_trait_solver` is enabled in coherence by default (`NextSolverConfig::Coherence` in `1.98.0`/`1.99.1`; `Globally` on nightly in `1.102.0`/`main`) and never returns `Err(NoSolution)` for inductive cycles during `TypingMode::Coherence`, ensuring `E0119` overlap rejection.
  - Both the legacy solver and `-Znext-solver=globally` reject `rust-lang/rust#25860` (`error: lifetime may not live long enough`), whereas enabling `-Zassumptions-on-binders=yes` (with `-Znext-solver=globally`) accepts `#25860` and admits safe-Rust use-after-free caught by Miri.
- **Specific to `1.98.0-nightly` (`14210df0e27c`) vs. `1.99.1` (`58cf8f9c35b3`) vs. `1.102.0-nightly` (`3ef0c22cdb86`) / `main` (`342d74463af7`):**
  1. **CLI flag `-Zpolonius=off`:** Absent in `1.98.0-nightly` (`parse_polonius` accepts only `legacy`/empty/`next`); added by `1.99.1` (`parse_polonius` accepts `legacy`/empty/`off`/`no`/`next`) to allow opting out once nightly builds set `CFG_DEFAULT_POLONIUS_NEXT=1`.
  2. **Nightly channel defaults:** `1.98.0-nightly` defaults to `Polonius::Off` and `NextSolverConfig { coherence: true, globally: false }`. `1.99.1` adds `CFG_DEFAULT_POLONIUS_NEXT=1` on `nightly`/`dev` channels (still `Polonius::Off` on `stable` `1.99.1`). `1.102.0-nightly` enables BOTH `CFG_DEFAULT_POLONIUS_NEXT=1` and `CFG_DEFAULT_NEXT_SOLVER_GLOBALLY=1` on `nightly`/`dev`. `main` additionally sets `CFG_DEFAULT_FRONTEND_JOBS=2`.
  3. **`DeferredRegionLiveness` (`polonius/liveness.rs`):** Absent in `1.98.0-nightly` and `1.99.1`; added by `1.102.0-nightly` and present in `main` to compute region liveness lazily on-demand during loan-graph traversal.
  4. **`SearchGraphDelegate::initial_provisional_result` on `PathKind::Inductive`:** Dispatches on `TypingMode` (`Coherence => Certainty::overflow(false)`, non-coherence `=> Err(NoSolution)`) in `1.98.0-nightly`, `1.99.1`, and `49d734536222`; changed to `PathKind::Inductive => unreachable!()` (treating all unproductive cycles as `PathKind::Unknown` -> `Certainty::overflow(false)`) in commit `622fd6a3f80ff4398db552ed138243c845347298` (`2026-09-22`), effective in `1.102.0-nightly` and `main`.
  5. **`-Zassumptions-on-binders=yes` without explicit `-Znext-solver=globally`:** Panics with an ICE (`rc = 101`) in `1.98.0-nightly` because `config.rs` did not yet auto-enable `NextSolverConfig::Globally`; fixed by `1.99.1` (`compiler/rustc_session/src/config.rs:2710-2720`). Additionally, on `1.98.0-nightly`, `-Znext-solver=globally -Zassumptions-on-binders=yes` overflows (`E0275`) on recursive `Rec: Send`, whereas `1.102.0-nightly` accepts `Rec: Send` under `-Zassumptions-on-binders=yes`.

This report complements `verified-rust-frontend-approaches-trait-solver-polonius-and-thir-lowering` (which surveys frontend crate modularity and certificate architectures for `rustc 1.99.1`) and `borrow-checker-self-referential-views-disjoint-slices-and-polonius-limits` (which focuses on view types and vectorization limits), adding cross-release primary-source diffs (`1.98.0-nightly` -> `1.99.1` -> `1.102.0-nightly` -> `main`), live Miri UAF execution, `zerocopy` compile-time profiling, and constructive Lean 4 soundness and counterexample proofs.

---

## Findings

### 1. `Polonius::Next` Default Activation, `DenseBitSet` Architecture, and Bidirectional Invariant Edges

`Basis: source + execution` (`src/bootstrap/src/core/build_steps/compile.rs`, `compiler/rustc_session/src/{config.rs,options.rs}`, `compiler/rustc_borrowck/src/polonius/{mod.rs,constraints.rs,liveness.rs,liveness_constraints.rs}`, `support/probe_polonius_and_next_solver_results.json`, `support/rustc_1_99_1_vs_1_102_0_nightly_reference_matrix.json`)

#### 1.1 Channel-Gated Default Activation Mechanism

`Polonius::Next` is not switched on by a hardcoded constant in `rustc_session`; instead, `rustc`'s bootstrap driver injects a compile-time environment variable solely on `nightly` and `dev` channels. In `rust-lang/rust` at `3ef0c22cdb86` (`1.102.0-nightly`, `src/bootstrap/src/core/build_steps/compile.rs:1372-1377`) and `342d74463af7` (`main`, `compile.rs:1374-1381`):

```rust
// src/bootstrap/src/core/build_steps/compile.rs:1374-1381 (342d74463af7)
let nightly = builder.config.channel == "nightly" || builder.config.channel == "dev";
if nightly {
    // We want to enable Polonius Alpha and Next Trait Solver by default on nighty
    cargo.env("CFG_DEFAULT_POLONIUS_NEXT", "1");
    cargo.env("CFG_DEFAULT_NEXT_SOLVER_GLOBALLY", "1");
    // Enable 2 threads for the parallel frontend by default on nightly
    cargo.env("CFG_DEFAULT_FRONTEND_JOBS", "2");
}
```

In `1.99.1` (`58cf8f9c35b3`, `compile.rs:1372-1376`), only `CFG_DEFAULT_POLONIUS_NEXT` was set on `nightly`/`dev`, and because `1.99.1` is distributed on the `stable` channel (`channel == "stable"`), its released binary resolves `Polonius::default()` to `Polonius::Off`. `rustc_session` consumes these build-time flags in `compiler/rustc_session/src/config.rs` and renders dynamic help text in `compiler/rustc_session/src/options.rs`:

```rust
// compiler/rustc_session/src/config.rs:3855-3858 (342d74463af7; lines 3808-3811 in 3ef0c22cdb86)
impl Polonius {
    pub(crate) const DEFAULT: Self =
        if option_env!("CFG_DEFAULT_POLONIUS_NEXT").is_some() { Self::Next } else { Self::Off };
}

// compiler/rustc_session/src/options.rs:2458-2462, 2877-2878 (342d74463af7;
// lines 2399-2403, 2817-2818 in 3ef0c22cdb86; line 2756 in 49d734536222)
const POLONIUS_HELP: &str = match Polonius::DEFAULT {
    Polonius::Off => "enable polonius-based borrow-checker (default: no)",
    Polonius::Next => "enable polonius-based borrow-checker (default: next)",
    Polonius::Legacy => panic!("Polonius::Legacy is not a valid default value"),
};
// ...
polonius: Polonius = (Polonius::default(), parse_polonius, [TRACKED], POLONIUS_HELP),
```

Across the five audited `rust-lang/rust` snapshots, the flag surface evolved cleanly:

| Revision | `Polonius::DEFAULT` (Release vs Nightly) | `parse_polonius` Accepted Values | `NextSolverConfig::default()` | `assumptions_on_binders` Auto-Enables `next_solver`? |
| :--- | :--- | :--- | :--- | :--- |
| `1.98.0-nightly` (`14210df0e27c`) | `Off` (even on nightly) | `None`/`legacy`, `next` (**`off` rejected**) | `{ coherence: true, globally: false }` | **No** (bare `-Zassumptions-on-binders=yes` ICEs) |
| `1.99.1` (`58cf8f9c35b3`) | `Off` on stable (`Next` if `CFG_DEFAULT_POLONIUS_NEXT`) | `None`/`legacy`, `next`, `off`/`no` | `{ coherence: true, globally: false }` | **Yes** (`config.rs:2710-2720`) |
| `49d734536222` | `Off` unless `CFG_DEFAULT_POLONIUS_NEXT` | `None`/`legacy`, `next`, `off`/`no` | `{ coherence: true, globally: false }` | **Yes** (`options.rs:2381-2383`) |
| `1.102.0-nightly` (`3ef0c22cdb86`) | `Next` on nightly/dev (`compile.rs:1375`) | `None`/`legacy`, `next`, `off`/`no` | `Globally` on nightly/dev (`compile.rs:1376`) | **Yes** (`options.rs:2430-2432`) |
| `main` (`342d74463af7`) | `Next` on nightly/dev (`compile.rs:1377`) | `None`/`legacy`, `next`, `off`/`no` | `Globally` on nightly/dev (`compile.rs:1378`) | **Yes** (`options.rs:2488-2490`) |

#### 1.2 In-Tree `LiveLoans` Bitset Matrix and `LocalizedConstraintGraph`

Rather than serializing 14 relational tables into the external Datalog `polonius-engine` crate (as `-Zpolonius=legacy` does in `compiler/rustc_borrowck/src/polonius/legacy/`), `Polonius::Next` replaces only the *loan liveness* computation inside `rustc_borrowck`, feeding its output back into NLL's existing active-loan / invalidation dataflow (`compiler/rustc_borrowck/src/polonius/mod.rs:22-28`). Its core data structures in `342d74463af7` and `3ef0c22cdb86` are:

1. **Packed `PointIndex x BorrowIndex` Bitset (`polonius/mod.rs:64-85`):**
   ```rust
   #[derive(Clone)]
   pub(crate) struct LiveLoans {
       num_points: usize,
       // Rows are points, columns are borrows.
       flat_matrix: DenseBitSet<usize>,
   }
   impl LiveLoans {
       pub(crate) fn insert(&mut self, row: PointIndex, col: BorrowIndex) {
           let bit_index = row.index() + self.num_points * col.index();
           self.flat_matrix.insert(bit_index);
       }
   }
   ```
   Storing columns contiguously per loan aligns memory access with the outer per-loan DFS loop (`for (loan_idx, loan) in borrow_set.iter_enumerated()`, `constraints.rs:113`), avoiding sparse hash-map allocations when loan counts are small (single digits in ~90% of benchmark functions per the comment at `mod.rs:68`).

2. **Lazy Localized Graph (`polonius/constraints.rs:34-96`):**
   - Vertices are `LocalizedNode { region: RegionVid, point: PointIndex }`.
   - `edges: FxHashMap<LocalizedNode, SmallVec<[RegionVid; 4]>>` stores `Locations::Single(loc)` outlives constraints (`sup@p -> sub@p`) generated by assignments, reborrows, and calls.
   - `logical_edges: IndexVec<RegionVid, SmallVec<[RegionVid; 4]>>` stores `Locations::All(_)` outlives constraints (`sup -> sub`) without materializing one physical edge per CFG point; they are instantiated on-the-fly at `(logical_succ, node.point)` during DFS (`constraints.rs:235-239`).

3. **Variance-Directed CFG Edges and "Flowing Back in Time" (`polonius/mod.rs:113-123`, `liveness_constraints.rs:12-83`, `constraints.rs:163-233`):**
   - `VarianceExtractor` (`liveness_constraints.rs:30-153`) relates every live local's type to itself via `TypeRelation` (`extractor.relate(value, value)`), mapping region variances to `ConstraintDirection`:
     - `ty::Covariant` -> `ConstraintDirection::Forward` (`O@P1 -> O@P2` along CFG successors when `O` is live at `P2`, `constraints.rs:163-191`);
     - `ty::Contravariant` -> `ConstraintDirection::Backward` (`O@P2 -> O@P1` along CFG predecessors when `O` is live at `P2`, `constraints.rs:203-232`);
     - `ty::Invariant` -> `ConstraintDirection::Bidirectional` (both forward and backward edges; multiple conflicting variances for the same region widen to `Bidirectional` at `liveness_constraints.rs:79`).
   - Universal regions use `ConstraintDirection::Forward` (`liveness.rs:41-42`), while any non-universal region missing variance metadata (e.g., certain promoted/const-generic temporary regions) falls back *conservatively* to `ConstraintDirection::Bidirectional` (`liveness.rs:44-49`) to maximize reachability and preserve soundness.
   - **Why backward edges are mandatory for soundness:** Consider writing `&mut b` through an invariant mutable reference `q: &mut &mut i32` that aliases `p` (`let q = &mut p; *q = &mut b; b = 3; *p`). Typechecking emits the equality constraint `'q_inner == 'p` at the earlier point `P0` (`let q = &mut p`), whereas loan `L_b` is introduced *later* at `P1` (`*q = &mut b`). Without the backward CFG edge `r_q@P1 -> r_q@P0` enabled by invariance (`Bidirectional`), a forward-only traversal starting at `(r_q, P1)` can never return to `P0` to cross `(r_q, P0) -> (r_p, P0)` and detect that `L_b` flows into `p` and is invalidated at `b = 3`.

4. **On-Demand `DeferredRegionLiveness` (`polonius/liveness.rs:63-131`, `polonius/mod.rs:183-209`):**
   - Added between `1.99.1` and `1.102.0-nightly`, `DeferredRegionLiveness` exploits MIR renumbering's 1:1 mapping from each non-universal `RegionVid` to its owning `Local` (`by_region: IndexVec<RegionVid, Option<Local>>`) so region liveness is computed lazily only for regions actually reached by at least one loan during DFS (`DeferredLivenessSource::liveness_for_region`), substantially lowering the compile-time cost of tracking more live locals than NLL.

5. **Known Upstream Kill-vs-Time-Travel Approximation (`polonius/mod.rs:217-262`):**
   - `LoanLivenessVisitor::on_node_traversed` inserts `(node.point, loan)` whenever `is_live` holds (`mod.rs:259-261`). `LocalizedConstraintGraph::traverse` (`constraints.rs:100-243`) does **not** prune kills inside the graph DFS itself; instead, `LiveLoans` is handed off to NLL's downstream `Borrows` kill-aware dataflow. As `mod.rs:221-258` explicitly warns, collapsing the two transitive closures of the Datalog specification into a single reachability graph makes the interaction between kills and backward ("time-travel") edges subtle, leaving an explicit upstream `FIXME: analyze potential unsoundness, possibly in concert with a borrowck implementation in a-mir-formality, fuzzing, or manually crafting counter-examples.`

#### 1.3 Empirical Polonius Borrowck Matrix Across Four Toolchains/Modes

Execution of `support/probe_polonius_and_next_solver.py` on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (`support/probe_polonius_and_next_solver_results.json`) alongside the `1.99.1` vs `1.102.0-nightly (3ef0c22cd 2026-11-11)` reference matrix (`support/rustc_1_99_1_vs_1_102_0_nightly_reference_matrix.json`) confirms 100% behavioral alignment across the precision and soundness test cases:

| Test Case | `1.98.0-nightly` Default (`Off`) | `1.99.1` Default (`Off`) | `1.102.0-nightly` `-Zpolonius=off` | `1.98.0-nightly` `-Zpolonius=next` | `1.102.0-nightly` Default (`Next`) | `-Zpolonius=legacy` (Both) | Diagnostics When Rejected |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :--- |
| `nll_problem_case_3_hashmap` | FAIL | FAIL | FAIL | **PASS** | **PASS** | **PASS** | `E0499` (2x `*map`) |
| `loop_conditional_mut_return` | FAIL | FAIL | FAIL | **PASS** | **PASS** | **PASS** | `E0499` (2x `*v`) |
| `conditional_reborrow_and_mutate_else` | FAIL | FAIL | FAIL | **PASS** | **PASS** | **PASS** | `E0503` + `E0499` (`slice[_]`) |
| `two_phase_borrow_allowed` | PASS | PASS | PASS | PASS | PASS | PASS | — |
| `invariant_backward_loan_must_reject` | FAIL | FAIL | FAIL | FAIL | FAIL | FAIL | `E0499` (`**p`) |
| `invariant_time_travel_through_mut_ref_must_reject` | FAIL | *(not in 1.102 ref)* | *(not in 1.102 ref)* | FAIL | *(not in 1.102 ref)* | FAIL | `E0506` (`b` borrowed via `*q = &mut b`) |
| `aliasing_mut_escape_must_reject` | FAIL | FAIL | FAIL | FAIL | FAIL | FAIL | `E0499` (`*v`) |

#### 1.4 Full-Crate `google/zerocopy` Compile-Time Overhead Profile

Compiling `google/zerocopy` (`0.8.64`, `907b9175fee081872ec883ca4709e6ad922f8ed0`, `--no-default-features --emit=metadata`) across 5 timed trials per configuration on `rustc 1.98.0-nightly` (`support/probe_polonius_and_next_solver_results.json`) vs single-trial runs on `rustc 1.102.0-nightly` (`support/rustc_1_99_1_vs_1_102_0_nightly_reference_matrix.json`):

| Toolchain & Hardware Class | Mode / Flags | Compilation Outcome | Median Wall Time (s) | Mean Wall Time (s) | Delta vs NLL Baseline |
| :--- | :--- | :---: | ---: | ---: | ---: |
| `1.98.0-nightly` (`14210df0e`, 5 trials) | Default (`Polonius::Off`, legacy solver) | `ok` (`rc = 0`) | `4.1225` | `4.1307` | `0.00%` |
| `1.98.0-nightly` (`14210df0e`, 5 trials) | `-Zpolonius=next` | `ok` (`rc = 0`) | `4.5021` | `4.8545` | **`+9.21%`** (mean `+17.52%`) |
| `1.98.0-nightly` (`14210df0e`, 5 trials) | `-Znext-solver=globally` | `ok` (`rc = 0`) | `6.5437` | `6.8958` | `+58.73%` |
| `1.98.0-nightly` (`14210df0e`, 5 trials) | `-Zpolonius=next -Znext-solver=globally` | `ok` (`rc = 0`) | `6.5175` | `7.3607` | `+58.10%` |
| `1.98.0-nightly` (`14210df0e`, 1 trial) | `-Zpolonius=legacy` (Datalog) | `ok` (`rc = 0`) | `13.9328` | `13.9328` | **`+237.97%` (`3.38x`)** |
| `1.102.0-nightly` (`3ef0c22cd`, reference 1 trial) | `-Zpolonius=off` | `ok` (`rc = 0`) | `1.443` | — | `0.00%` |
| `1.102.0-nightly` (`3ef0c22cd`, reference 1 trial) | Default (`Polonius::Next`) | `ok` (`rc = 0`) | `1.646` | — | **`+14.1%`** |
| `1.102.0-nightly` (`3ef0c22cd`, reference 1 trial) | `-Znext-solver=globally` | `ok` (`rc = 0`) | `1.447` | — | `+0.3%` |

Two engineering takeaways emerge immediately:
1. Replacing Datalog `-Zpolonius=legacy` with the in-tree `DenseBitSet<usize>` `LiveLoans` graph cuts full-crate `zerocopy` Polonius overhead by more than an order of magnitude (`+237.97%` -> `+9.21%` median on `1.98.0-nightly`; `+14.1%` on `1.102.0-nightly`).
2. Between `1.98.0-nightly` (`2026-05-31`) and `1.102.0-nightly` (`2026-11-11`), `-Znext-solver=globally` closed a `+58.7%` compile-time gap on `zerocopy`'s trait-heavy code down to near-parity (`1.447 s` vs `1.443 s`), explaining why `compile.rs` promoted `CFG_DEFAULT_NEXT_SOLVER_GLOBALLY=1` to nightly default alongside `Polonius::Next`.

---

### 2. `rustc_next_trait_solver` `SearchGraph` Cycle Polarity and Coherence Ambiguity Soundness

`Basis: source + execution + derived` (`compiler/rustc_next_trait_solver/src/solve/{search_graph.rs,eval_ctxt/mod.rs}`, `compiler/rustc_type_ir/src/search_graph/mod.rs`, `tests/ui/traits/next-solver/cycles/unproductive-in-coherence.rs`, commit `622fd6a3f80ff4398db552ed138243c845347298`)

#### 2.1 The 3-Way `initial_provisional_result` Dispatch in `1.98.0-nightly` / `1.99.1` / `49d734536222`

When `rustc_type_ir::search_graph::SearchGraph` encounters an active cycle head on its evaluation stack (`compiler/rustc_type_ir/src/search_graph/mod.rs:1341`), it queries `Delegate::initial_provisional_result(cx, kind, input)` to seed fixpoint iteration. In `rustc 1.98.0-nightly` (`14210df0e27c`, `search_graph.rs:48-80`), `1.99.1` (`58cf8f9c35b3`, `search_graph.rs:47-81`), and `49d734536222` (`search_graph.rs:42-77`), `SearchGraphDelegate` implemented an explicit `TypingMode`-conditioned 3-way dispatch:

```rust
// compiler/rustc_next_trait_solver/src/solve/search_graph.rs:47-81 (58cf8f9c35b3 / 1.99.1)
fn initial_provisional_result(
    cx: I,
    kind: PathKind,
    input: CanonicalInput<I>,
) -> (QueryResult<I>, AccessedOpaques<I>) {
    match kind {
        PathKind::Coinductive => response_no_constraints(cx, input, Certainty::Yes),
        PathKind::Unknown | PathKind::ForcedAmbiguity => {
            response_no_constraints(cx, input, Certainty::overflow(false))
        }
        // Even though we know these cycles to be unproductive, we still return
        // overflow during coherence. This is both as we are not 100% confident in
        // the implementation yet and any incorrect errors would be unsound there.
        // ...
        // See `tests/ui/traits/next-solver/cycles/unproductive-in-coherence.rs`
        PathKind::Inductive => match input.typing_mode.0 {
            TypingMode::Coherence => {
                response_no_constraints(cx, input, Certainty::overflow(false))
            }
            TypingMode::Typeck { .. }
            | TypingMode::PostTypeckUntilBorrowck { .. }
            | TypingMode::Reflection
            | TypingMode::PostBorrowck { .. }
            | TypingMode::PostAnalysis
            | TypingMode::Codegen
            | TypingMode::ErasedNotCoherence(MayBeErased) => {
                (Err(NoSolution), AccessedOpaques::default())
            }
        },
    }
}
```

Why does coherence treat `PathKind::Inductive` asymmetrically relative to `Typeck` / `Codegen`?
- **In `Typeck` / `Codegen` (positive proving):** A trait obligation `T: Tr` succeeds only on `Ok(Certainty::Yes)`. Returning either `Err(NoSolution)` or `Ok(Certainty::overflow(false))` (ambiguity/overflow) rejects the program — both are *sound* ways to fail an unproductive inductive cycle (such as `trait Loop {} impl<T: Loop> Loop for T {}` queried for `u32: Loop`, which fails with `E0275`). Meanwhile, coinductive auto traits (`struct Rec(Option<Box<Rec>>); Rec: Send`) take `PathKind::Coinductive -> Certainty::Yes` (`eval_ctxt/mod.rs:84, 455`) and succeed.
- **In `TypingMode::Coherence` (negative disjointness proving):** Polarity **flips**! Coherence checks whether two `impl` blocks can overlap by testing whether their intersection obligation is *unprovable* (`Err(NoSolution)`). If `initial_provisional_result` returned `Err(NoSolution)` for an inductive cycle during coherence, coherence would falsely conclude the two `impl`s are disjoint and accept overlapping implementations! Returning `Certainty::overflow(false)` (ambiguity) forces coherence to conservatively assume overlap may occur and reject with `E0119`.

Two concrete Rust programs illustrate this exact boundary (both verified live in `support/probe_polonius_and_next_solver.py`):
1. **Blanket inductive cycle overlap (`inductive_cycle_in_coherence_overlap_rejected`):**
   ```rust
   pub trait Loop {}
   impl<T: Loop> Loop for T {}
   pub trait Disjoint {}
   impl<T: Loop> Disjoint for T {}
   impl Disjoint for u32 {} // ERROR[E0119]: conflicting implementations of trait `Disjoint` for type `u32`
   ```
   Because `u32: Loop` enters an inductive cycle, coherence receives ambiguity (`Certainty::overflow(false)`) rather than `NoSolution`, rejecting the overlap with `E0119` across every solver mode.
2. **Unproductive associated-type normalization cycle (`tests/ui/traits/next-solver/cycles/unproductive-in-coherence.rs`, verified in `coherence_unproductive_assoc_norm_rejected`):**
   ```rust
   pub trait Trait { type Assoc<T: Trait>; }
   pub struct Overflow;
   impl Trait for Overflow { type Assoc<T: Trait> = <T as Trait>::Assoc<Overflow>; }
   pub trait Overlap<T, WfHack> {}
   impl<T: Trait, U: Copy> Overlap<T::Assoc<T>, U> for T {}
   impl<U> Overlap<u32, U> for Overflow {} // ERROR[E0119]
   ```
   Normalizing `<Overflow as Trait>::Assoc<Overflow>` hits an unproductive self-normalization cycle; returning ambiguity keeps the two impls rejected with `E0119`.

#### 2.2 Upstream Tightening in Commit `622fd6a3f80f` (`1.102.0-nightly` & `main`)

Primary-source git history inspection of `compiler/rustc_next_trait_solver/src/solve/search_graph.rs` revealed an important evolution between `1.99.1` (`58cf8f9c35b3`) / `49d734536222` and `1.102.0-nightly` (`3ef0c22cdb86`) / `main` (`342d74463af7`). On `2026-09-22`, commit `622fd6a3f80ff4398db552ed138243c845347298` (`"treat inductive cycles as ambig"`) changed both `eval_ctxt/mod.rs` and `search_graph.rs`:

```rust
// compiler/rustc_next_trait_solver/src/solve/eval_ctxt/mod.rs (commit 622fd6a3f80f;
// later simplified further in step_kind_to_nested at 342d74463af7:436-451)
- GoalSource::TypeRelating => PathKind::Inductive,
+ GoalSource::TypeRelating => PathKind::Unknown,

// compiler/rustc_next_trait_solver/src/solve/search_graph.rs:45-71 (3ef0c22cdb86 & 342d74463af7)
fn initial_provisional_result(
    cx: I,
    kind: PathKind,
    input: I::CanonicalInput,
) -> (QueryResult<I>, AccessedOpaques<I>) {
    match kind {
        PathKind::Coinductive => response_no_constraints(cx, input, Certainty::Yes),
        PathKind::Unknown | PathKind::ForcedAmbiguity => {
            response_no_constraints(cx, input, Certainty::overflow(false))
        }
        // Even though we know some cycles to be unproductive, we still treat them
        // as unknown for now. This is both as we are not 100% confident in the
        // implementation yet and any incorrect errors would be unsound there.
        // ...
        // FIXME(-Znext-solver=coinductive): Long term, we probably do want to
        // return `NoSolution` here. This should happen separately from the
        // stabilization of the new solver.
        PathKind::Inductive => unreachable!(),
    }
}
```

And in `342d74463af7` (`eval_ctxt/mod.rs:436-451`), `step_kind_to_nested` maps `CoinductiveTrait -> PathKind::Coinductive`, `Projection* -> PathKind::Unknown`, and `Misc -> PathKind::ForcedAmbiguity`, ensuring `PathKind::Inductive` is never emitted during solving. The soundness invariant for coherence (`policy(Coherence, cycle) != NoSolution`) is therefore **strictly preserved** — and extended conservatively to non-coherence modes as overflow (`E0275`) rather than `NoSolution` (`E0277`, as seen in `tests/ui/traits/next-solver/overflow/recursive-self-normalization.rs` updated by `622fd6a3f80f`) pending post-stabilization coinductive trait design.

---

### 3. Higher-Ranked Implied-Bounds Soundness Cliff (`-Z assumptions-on-binders=yes` vs. `rust-lang/rust#25860`)

`Basis: source + execution` (`compiler/rustc_next_trait_solver/src/solve/eval_ctxt/{mod.rs,solver_region_constraints.rs}`, `compiler/rustc_type_ir/src/region_constraint.rs`, `support/probe_polonius_and_next_solver_results.json`, `support/rustc_1_99_1_vs_1_102_0_nightly_reference_matrix.json`)

#### 3.1 Root Cause in `rustc_next_trait_solver`

When `-Z assumptions-on-binders=yes` is disabled (the default in `legacy` and `-Z next-solver=globally`), entering a higher-ranked binder (`for<'a>`) introduces placeholders without synthesizing implied region outlives assumptions from unverified types inside the binder, and exiting a canonical goal runs `delegate.leak_check(self.max_input_universe)` (`compiler/rustc_next_trait_solver/src/solve/eval_ctxt/mod.rs:1778-1785`).

When `-Z assumptions-on-binders=yes` is enabled:
1. `EvalCtxt::enter_forall_with_assumptions` (`eval_ctxt/mod.rs:1427-1448`) replaces bound variables with placeholders in a fresh universe `u` and immediately invokes `self.region_assumptions_for_placeholders_in_universe(value.clone(), u, param_env)` followed by `self.delegate.insert_placeholder_assumptions(u, assumptions)`.
2. `region_assumptions_for_placeholders_in_universe` (`solver_region_constraints.rs:31-111`) walks every type `t` in the binder via `RawAssumptions::visit_ty` (`lines 52-63`), calling `well_formed_goals(param_env, t.into())` and packaging all elaborated outlives clauses into `Assumptions::new(...)` (`lines 103-110`).
3. At goal finalization (`eval_ctxt/mod.rs:1773-1777`), `eagerly_handle_placeholders` (`solver_region_constraints.rs:114-145` -> `rustc_type_ir/src/region_constraint.rs:716-747`) runs `pull_region_outlives_constraints_out_of_universe` using those injected placeholder assumptions instead of `leak_check`.
4. **The soundness hole (`rust-lang/rust#25860`):** In `extend_lifetime`:
   ```rust
   static UNIT: &'static &'static () = &&();
   fn foo<'a, 'b, T>(_: &'a &'b (), v: &'b T) -> &'a T { v }
   pub fn extend_lifetime<'a, T>(x: &'a T) -> &'static T {
       let f: fn(_, &'a T) -> &'static T = foo;
       f(UNIT, x)
   }
   ```
   Inside `foo`, `&'a &'b ()` carries the implied bound `'b: 'a`. Coercing `foo` to `fn(&'static &'a (), &'a T) -> &'static T` creates an ill-formed parameter type `&'static &'a ()` whose well-formedness would require `'a: 'static`. Because `UNIT: &'static &'static ()` is covariant in its inner lifetime, passing `UNIT` succeeds whenever `'static: 'a` (always true). Sound `rustc` (`legacy` and `-Znext-solver=globally`) demands proof of `'a: 'static` from the outer environment and fails with `error: lifetime may not live long enough`. Under `-Zassumptions-on-binders=yes`, however, the solver extracts `'a: 'static` from the unverified binder type `&'static &'a ()` as an *assumption* and uses it to discharge the very outlives obligation that should have rejected the coercion!

#### 3.2 Complete 10-Case × 3-Mode Next Trait Solver Matrix & Live Miri `#25860` UAF

Empirical results across `1.98.0-nightly` (`support/probe_polonius_and_next_solver_results.json`, with `assumptions_on_binders` passing `-Znext-solver=globally -Zassumptions-on-binders=yes`) and `1.102.0-nightly` (`support/rustc_1_99_1_vs_1_102_0_nightly_reference_matrix.json`):

| Trait-Solver Case | `1.98` Default | `1.98` `-Znext-solver=globally` | `1.98` `+ -Zassumptions-on-binders=yes` | `1.102` Legacy | `1.102` `-Znext-solver=globally` | `1.102` `-Zassumptions-on-binders=yes` | Key Diagnostic / Note |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :--- |
| `coinductive_auto_send_recursive` | PASS | PASS | **FAIL (`E0275`)** | PASS | PASS | PASS | Early `1.98` `NextGen` region-constraint coinductive overflow fixed by `1.102` |
| `inductive_cycle_in_typeck_rejected` | FAIL (`E0275`) | FAIL (`E0275`) | FAIL (`E0275`) | FAIL (`E0275`) | FAIL (`E0275`) | FAIL (`E0275`) | Overflow evaluating `u32: Loop` |
| `inductive_cycle_in_coherence_overlap_rejected` | FAIL (`E0119`) | FAIL (`E0119`) | FAIL (`E0119`) | FAIL (`E0119`) | FAIL (`E0119`) | FAIL (`E0119`) | Coherence ambiguity blocks `Disjoint` overlap |
| `coherence_unproductive_assoc_norm_rejected` | FAIL (`E0119`) | FAIL (`E0119`) | FAIL (`E0119`) | *(upstream UI test)* | *(upstream UI test)* | *(upstream UI test)* | Matches `unproductive-in-coherence.rs` |
| `hrtb_implied_bounds_assumptions_on_binders` | PASS | PASS | PASS | PASS | PASS | PASS | Well-formed `for<'a> Fn(&'a str) -> &'a str` |
| **`hrtb_lifetime_transmute_25860_must_reject`** | **FAIL** | **FAIL** | **PASS (UNSOUND!)** | **FAIL** | **FAIL** | **PASS (UNSOUND!)** | Both default & `-Znext-solver=globally` reject (`lifetime may not live long enough`); `-Zassumptions-on-binders=yes` compiles UAF! |
| `rpit_defining_use_consistency` | PASS | PASS | PASS | PASS | PASS | PASS | Consistent RPIT hidden type |
| `marker_trait_overlap_allowed` | PASS | PASS | PASS | PASS | PASS | PASS | `#[marker]` permits intentional overlap |
| `deep_assoc_proj_normalization` | PASS | PASS | PASS | PASS | PASS | PASS | 5-level `<Z as Step>::Next` normalization |
| `param_env_rigid_alias_vs_normalization` | PASS | PASS | PASS | PASS | PASS | PASS | Param-env normalized vs rigid alias |

Running the compiled `#25860` reproducer with a dropped `String` under `cargo miri run --offline` (`miri 0.1.0 (14210df0e2 2026-05-31)`, `RUSTFLAGS="-Znext-solver=globally -Zassumptions-on-binders=yes"`) exits with **`rc = 1`** in `0.442 s` and reports verbatim:

```text
error: Undefined Behavior: constructing invalid value of type &std::string::String: encountered a dangling reference (use-after-free)
  --> src/main.rs:18:16
   |
18 |     let _len = dangling.len();
   |                ^^^^^^^^ Undefined Behavior occurred here
   |
   = help: this indicates a bug in the program: it performed an invalid operation, and caused Undefined Behavior
```

This identically reproduces the `1.102.0-nightly` Miri UAF observation in `support/rustc_1_99_1_vs_1_102_0_nightly_reference_matrix.json` (`rc = 1`, `encountered a dangling reference (use-after-free)`), confirming that `#25860` remains an active safe-Rust soundness cliff whenever `-Zassumptions-on-binders=yes` is enabled.

---

### 4. Kernel-Checked Lean 4 (`v4.34.1`) Mechanization and Counterexamples

`Basis: derived + execution` (`support/PoloniusAndNextSolverCycleSoundness.lean`, verified with `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`)

`support/PoloniusAndNextSolverCycleSoundness.lean` (921 lines, 40,563 bytes, zero external imports beyond Lean `Init`) mechanizes all three subsystems using purely structural inductive relations and total recursion, passing:

```bash
lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
  support/PoloniusAndNextSolverCycleSoundness.lean
```

with exit code `0`, zero warnings, zero unproved goals, and zero classical or compiler-reflection axioms:

| Theorem / Counterexample | Line Range | Exact `#print axioms` Output | Formal Meaning |
| :--- | :--- | :--- | :--- |
| `polonius_sound_and_strictly_more_precise_than_nll` | `L313-321` | `[propext]` | `(∀ g, PoloniusAccepts g -> NoAliasingConflict g) ∧ (∀ g, NllAccepts g -> PoloniusAccepts g) ∧ (∃ g, PoloniusAccepts g ∧ ¬ NllAccepts g)` (witnessed by `problemCase3Graph`, `L234-311`). |
| `ce1_omitting_bidirectional_invariant_edge_admits_aliasing_ub` | `L408-437` | `[propext, Quot.sound]` | On `badInvariantGraph` (`L361-376`, modeling `*q = &mut b; b = 3; *p`), dropping `bwdLiveness` makes `PoloniusNoBwdAccepts badInvariantGraph` hold while `¬ PoloniusAccepts badInvariantGraph` and concrete `AliasingConflict badInvariantGraph 0 2` exists. |
| `coherence_inductive_ambiguity_prevents_overlapping_impls` | `L731-749` | `[propext]` | For every `CoherenceCycleSafe` policy (proved for both `rustc1991Policy` and `rustc1102Policy`) and every `CoinductivelyViable` goal `g`, `coherencePermitsBothImpls policy prog fuel g = false`; simultaneously `recSendProg` evaluates to `.yes` and `inductiveOverlapProg` evaluates `≠ .yes` in `TypingMode.typeck`. |
| `ce2_returning_no_solution_for_inductive_cycle_in_coherence_admits_overlapping_impls` | `L751-766` | `[propext]` | Under `unsoundCoherenceNoSolPolicy`, `coherencePermitsBothImpls` returns `true` on `inductiveOverlapProg`, admitting overlapping impls for a `CoinductivelyViable` goal that both `rustc1991Policy` and `rustc1102Policy` reject (`false`). |
| `wf_guarded_binder_assumptions_preserve_lifetime_soundness` | `L869-901` | *(no axioms)* | Every outlives judgment derived under `WfGuardedContext` holds semantically in every `LifetimeEnv` satisfying `outerCtx`, and from `outerCtx = []`, `'a : 'static` (`⟨.rParam 0, .rStatic⟩`) is never derivable. |
| `ce3_unwf_binder_assumption_derives_arbitrary_lifetime_extension_25860` | `L912-921` | *(no axioms)* | Under `unwfBinderContext [] binder25860`, `'a : 'static` is derivable in 1 step (`Derives.assume`), violating `shortLifetimeEnv` (`1 < 100`, dangling reference / UAF). |

#### Proof-Architecture Highlights

1. **Universal Dominance of `Polonius::Next` over Flow-Insensitive NLL (`L194-224`):** By structural induction on `PoloniusReach g l u`, every `PoloniusStep` either leaves `u.region` unchanged (`fwdLiveness`, `bwdLiveness`) or follows a localized/global outlives edge into `NllSubset` (`typeck`, `global`). Hence `PoloniusLiveLoan g l p -> NllLiveLoan g l p` holds universally for *every* `BorrowGraph`, yielding `∀ g, NllAccepts g -> PoloniusAccepts g` without case-splitting on CFG topology.
2. **Constructive `evalGoal` Without `WellFounded.fix` (`L536-570`):** Factoring premise and clause traversal (`evalPremisesWith`, `evalClausesWith`) as structurally recursive combinators over `List`, parameterized by a `stepFn` bound to `evalGoal ... fuel`, makes `evalGoal` structurally recursive on `fuel : Nat` with pure definitional reduction (`rfl` on concrete solver queries) and zero `Classical.choice` dependency (`evalGoal_coherence_never_noSolution_of_viable`, `L655-717`).
3. **Axiom-Free Binder Lifetime Soundness (`L774-921`):** Ordering lifetimes over `Nat` bounded by `staticEnd` yields completely axiom-free (`does not depend on any axioms`) soundness and `#25860` counterexample proofs via `Nat.le_refl`, `Nat.le_trans`, and kernel `decide`.

---

### 5. Implications for Anneal (`joshlf/anneal`) and Drop-In Verified `rustc` TCB Boundaries

`Basis: source + derived` (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`: `trusted/rustc-capture/src/driver.rs:25, 45-47, 75-84, 137`, `trusted/audit/TrustedBoundary.lean:13-105`, `THREAT_MODEL.md:99-106`, `docs/architecture.md:43-54`)

Inspection of `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` establishes three direct TCB requirements at the frontend-to-MIR capture seam:

1. **Upstream Analysis Sits Inside the Capture TCB:** `trusted/rustc-capture/src/driver.rs:75-84` hooks `Callbacks::after_analysis` (which runs *after* `tcx.analysis(())` executes `mir_borrowck`, coherence checking, and trait solving), checks `self.analysis_reached = tcx.dcx().has_errors().is_none()`, and pins the compiler version string (`COMPILER_VERSION = "1.98.0-nightly (f8a08b688 2026-05-30)"`, `driver.rs:25, 45-47`). Anneal's MIR semantics (`Trusted/MirSemantics.lean`) verifies safety and specifications on captured monomorphic `Runtime(PostCleanup)` MIR, relying on `rustc`'s frontend to have rejected ill-typed trait dispatches, overlapping impls (which break monomorphic instance uniqueness), and safe-Rust lifetime/aliasing violations unless re-checked operationally.
2. **Mandatory Unstable-Flag Denylist / Allowlist at Capture Time:** Because `-Zassumptions-on-binders=yes` silently compiles safe-Rust use-after-free (`#25860`) through `after_analysis` with `has_errors().is_none()`, any verified capture driver (`anneal-rustc-capture` or a drop-in verified `rustc` driver) MUST fail closed if unstable soundness-affecting flags — specifically `-Zassumptions-on-binders=yes` (and `-Zunsound-mir-opts`, `-Zunleash-the-miri-inside-of-you`) — are enabled in `config.opts.unstable_opts`.
3. **Channel-Drift Awareness When Bumping `COMPILER_VERSION` Beyond `1.98.0-nightly`:** Upgrading Anneal's pinned nightly past `1.99` automatically flips *both* `Polonius::Next` and `NextSolverConfig::Globally` on by default via `CFG_DEFAULT_POLONIUS_NEXT=1` and `CFG_DEFAULT_NEXT_SOLVER_GLOBALLY=1` (`compile.rs:1374-1378`). Because `Polonius::Next` retains an explicit upstream soundness `FIXME` regarding kills under backward invariant traversal (`polonius/mod.rs:221-258`), a security-conservative capture driver pinned to `1.102+` nightly should explicitly audit or record `sess.opts.unstable_opts.polonius` and `sess.opts.unstable_opts.next_solver` in its `CaptureManifest` / TCB audit log (and consider requiring `-Zpolonius=off` if minimizing borrowck TCB churn, or emitting and checking a Polonius `LiveLoans` fixed-point certificate directly in Lean).

---

## Boundaries

The following scope boundaries and negative-space findings prevent over-generalization:

- **Known not to apply — `Polonius::Next` default on `stable`/`beta` release channels:** Primary-source inspection (`src/bootstrap/src/core/build_steps/compile.rs:1374-1381`) proves `CFG_DEFAULT_POLONIUS_NEXT=1` and `CFG_DEFAULT_NEXT_SOLVER_GLOBALLY=1` are set **only** when `builder.config.channel == "nightly" || builder.config.channel == "dev"`. Stable `rustc 1.99.1` (and any stable/beta build without that env var) continues to default to `Polonius::Off` (NLL) and `NextSolverConfig::Coherence`.
- **Known not to apply — `PathKind::Inductive => Err(NoSolution)` in `1.102.0-nightly` / `main`:** Starting at commit `622fd6a3f80ff4398db552ed138243c845347298` (`2026-09-22`), `rustc_next_trait_solver` no longer dispatches `PathKind::Inductive` on `TypingMode` in `search_graph.rs`; instead `PathKind::Inductive => unreachable!()` and unproductive cycles uniformly produce `Certainty::overflow(false)` (`PathKind::Unknown`). Claims describing `TypingMode::Typeck => Err(NoSolution)` apply strictly to pre-`622fd6a3f80f` revisions (`1.98.0-nightly`, `1.99.1`, `49d734536222`).
- **Known not to apply — Direct linking of Lean formalization to `Trusted.MirSemantics`:** `support/PoloniusAndNextSolverCycleSoundness.lean` is a standalone, self-contained kernel-checked abstraction of `LocalizedConstraintGraph`, `SearchGraph`, and binder outlives rules over Lean `Init`. It does **not** import `joshlf/anneal`'s `Trusted.MirSemantics` or prove end-to-end equivalence with Rust's Tree Borrows / MiniRust operational memory model; its operational soundness theorem (`polonius_sound_and_strictly_more_precise_than_nll`) holds with respect to the modeled `ProvenanceChain` / `AliasingConflict` semantics.
- **Unknown — Completeness of `Polonius::Next`'s single-graph kill approximation under arbitrary invariant time-travel:** As `compiler/rustc_borrowck/src/polonius/mod.rs:221-258` notes verbatim, `Polonius::Next` approximates the two-transitive-closure Datalog specification with a single graph traversal whose backward edges interact subtly with flow-insensitive kills. Whether a subtle borrowck unsoundness counterexample exists in `rustc`'s live `Polonius::Next` implementation (beyond the forward-only missing-edge bug formalized in `ce1`) remains an open upstream research question (`FIXME` in `polonius/mod.rs:257-258`) and was not resolved by exhaustive fuzzing in this investigation.
- **Not examined — `-Zhigher-ranked-assumptions=yes` (coroutine-only auto-trait assumptions) and `rustc` `1.100`/`1.101` intermediate releases:** Empirical probes tested `-Zassumptions-on-binders=yes` (general `for<'a>` binders) and compared `1.98.0-nightly`, `1.99.1`, `1.102.0-nightly`, and `main`. Coroutine-scoped `-Zhigher-ranked-assumptions=yes` soundness, multi-crate incremental compilation caching under `Polonius::Next`, and full crates.io Crater regression statistics were not examined.
- **Unsupported — Bare `-Zassumptions-on-binders=yes` and `-Zpolonius=off` on `rustc 1.98.0-nightly`:** On `1.98.0-nightly (14210df0e)`, `-Zpolonius=off` is rejected by CLI parsing (`parse_polonius` supports only `legacy`/`next`), and `-Zassumptions-on-binders=yes` without explicit `-Znext-solver=globally` triggers a compiler ICE (`rc = 101`). Both constraints were lifted by `1.99.1`.
- **Execution-host asymmetry between `1.98.0-nightly` and `1.102.0-nightly` timings:** Absolute wall-clock timings (`4.12 s` on `1.98.0-nightly` vs `1.44 s` on `1.102.0-nightly` for `zerocopy`) come from distinct host environments and compiler snapshots and must not be compared directly as raw seconds across hosts; only within-host relative ratios (`+9.21%` median / `+14.1%` single-trial for `Polonius::Next`, `+237.97%` for `Polonius::Legacy`, and `+58.73%` -> `+0.3%` for `-Znext-solver=globally`) are meaningful.

---

## Evidence

### 1. Primary-Source Git Citations (All SHAs Resolved Live via GitHub API)

| Repository | Full 40-Hex Commit SHA | File Path & Line Range | Key Symbol / Observation |
| :--- | :--- | :--- | :--- |
| `rust-lang/rust` | `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `src/bootstrap/src/core/build_steps/compile.rs:1374-1381` | Sets `CFG_DEFAULT_POLONIUS_NEXT=1`, `CFG_DEFAULT_NEXT_SOLVER_GLOBALLY=1`, `CFG_DEFAULT_FRONTEND_JOBS=2` when `channel == "nightly" \|\| channel == "dev"`. |
| `rust-lang/rust` | `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `compiler/rustc_session/src/config.rs:1078-1086, 3835-3868` | `NextSolverConfig::default()` (`CFG_DEFAULT_NEXT_SOLVER_GLOBALLY`), `Polonius::DEFAULT` (`CFG_DEFAULT_POLONIUS_NEXT`). |
| `rust-lang/rust` | `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `compiler/rustc_session/src/options.rs:981-982, 1065-1081, 2458-2462, 2488-2490, 2796-2797, 2877-2878` | `parse_polonius`, `POLONIUS_HELP`, `assumptions_on_binders`, `next_solver`, `polonius`. |
| `rust-lang/rust` | `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `compiler/rustc_borrowck/src/polonius/mod.rs:64-85, 113-123, 136-177, 217-262` | `LiveLoans` (`DenseBitSet<usize>`), `ConstraintDirection::{Forward, Backward, Bidirectional}`, `PoloniusContext::compute_loan_liveness`, `LoanLivenessVisitor` + kills/time-travel soundness `FIXME`. |
| `rust-lang/rust` | `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `compiler/rustc_borrowck/src/polonius/constraints.rs:34-96, 100-243` | `LocalizedNode`, `LocalizedConstraintGraph::{new, traverse}`, physical localized edges, lazy `logical_edges`, forward (`L163-191`) & backward (`L203-232`) CFG edges. |
| `rust-lang/rust` | `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `compiler/rustc_borrowck/src/polonius/liveness_constraints.rs:12-153` | `record_live_region_variance`, `VarianceExtractor::record_variance` (`Covariant -> Forward`, `Contravariant -> Backward`, `Invariant -> Bidirectional`). |
| `rust-lang/rust` | `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `compiler/rustc_borrowck/src/polonius/liveness.rs:25-57, 64-131` | `RegionLiveness::new` (conservative `Bidirectional` fallback on missing variance), `DeferredRegionLiveness` lazy per-region liveness. |
| `rust-lang/rust` | `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `compiler/rustc_next_trait_solver/src/solve/search_graph.rs:45-90` | `SearchGraphDelegate::initial_provisional_result` (`PathKind::Inductive => unreachable!()` post-`622fd6a3f80f`). |
| `rust-lang/rust` | `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `compiler/rustc_next_trait_solver/src/solve/eval_ctxt/mod.rs:436-451, 1427-1448, 1773-1785` | `step_kind_to_nested`, `enter_forall_with_assumptions`, `eagerly_handle_placeholders` vs `leak_check`. |
| `rust-lang/rust` | `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `compiler/rustc_next_trait_solver/src/solve/eval_ctxt/solver_region_constraints.rs:31-111` | `region_assumptions_for_placeholders_in_universe` & `RawAssumptions::visit_ty` extracting unverified binder `well_formed_goals`. |
| `rust-lang/rust` | `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `compiler/rustc_type_ir/src/region_constraint.rs:716-747` | `eagerly_handle_placeholders_in_universe` -> `pull_region_outlives_constraints_out_of_universe`. |
| `rust-lang/rust` | `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `tests/ui/traits/next-solver/cycles/unproductive-in-coherence.rs:1-20` | Regression test demonstrating why unproductive normalization cycles must stay ambiguous (`E0119`) in coherence. |
| `rust-lang/rust` | `622fd6a3f80ff4398db552ed138243c845347298` | `compiler/rustc_next_trait_solver/src/solve/{eval_ctxt/mod.rs,search_graph.rs}` | Commit `"treat inductive cycles as ambig"` (`2026-09-22`): maps `GoalSource::TypeRelating => PathKind::Unknown` and changes `PathKind::Inductive => unreachable!()`. |
| `rust-lang/rust` | `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | `src/bootstrap/src/core/build_steps/compile.rs:1372-1377`, `compiler/rustc_session/src/options.rs:2399-2403, 2817-2818`, `compiler/rustc_next_trait_solver/src/solve/search_graph.rs:45-71` | `1.102.0-nightly (2026-11-11)` snapshot: both `Polonius::Next` and `NextSolverConfig::Globally` active on nightly; includes `polonius/liveness.rs` and commit `622fd6a3f80f`. |
| `rust-lang/rust` | `49d734536222bf28bb6d07d885b3a81d145981da` | `compiler/rustc_session/src/options.rs:2381-2383, 2756`, `compiler/rustc_next_trait_solver/src/solve/search_graph.rs:42-77` | Pre-`622fd6a3f80f` snapshot with explicit `TypingMode::Coherence => Certainty::overflow(false)` vs non-coherence `Err(NoSolution)` dispatch. |
| `rust-lang/rust` | `58cf8f9c35b355199727627d07ae34a4e2846d67` | `compiler/rustc_session/src/{config.rs:1022-1029,2710-2720,3626-3641; options.rs:893-894,978-984,2369-2371,2744}`, `compiler/rustc_next_trait_solver/src/solve/search_graph.rs:47-81` | `rustc 1.99.1` stable release: `Polonius::Off` default, `-Zpolonius=off` supported, explicit `TypingMode` inductive dispatch, `-Zassumptions-on-binders` auto-enables `next_solver.globally`. |
| `rust-lang/rust` | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_session/src/options.rs:826, 910-916, 2206-2207, 2536-2537`, `compiler/rustc_next_trait_solver/src/solve/search_graph.rs:48-80` | `rustc 1.98.0-nightly (2026-05-31)` live-executed toolchain: `Polonius::Off` default, no `-Zpolonius=off`, explicit `TypingMode` inductive dispatch, bare `-Zassumptions-on-binders=yes` ICEs without `-Znext-solver=globally`. |
| `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/rustc-capture/src/driver.rs:25, 45-47, 75-84, 137`, `trusted/audit/TrustedBoundary.lean:13-105`, `THREAT_MODEL.md:99-106` | `after_analysis` MIR capture hook, pinned `COMPILER_VERSION`, and TCB boundary specification. |
| `google/zerocopy` | `907b9175fee081872ec883ca4709e6ad922f8ed0` | `zerocopy/src/lib.rs`, `zerocopy/build.rs`, `zerocopy/Cargo.toml` (`0.8.64`) | Full-library compile-time stress target across five borrowck/solver flag combinations (`0` external dependencies under `--no-default-features`). |
| `leanprover/lean4` | `5045d0056413266e57c625dcd7c365b10e377c52` | Tag `v4.34.1` | Standalone Lean 4 kernel checking `support/PoloniusAndNextSolverCycleSoundness.lean`. |

### 2. Preserved Support Artifacts in This Package

All support artifacts are self-contained, path-scrubbed, and preserved directly under `support/`:

1. **`support/probe_polonius_and_next_solver.py`**: Reproducible Python 3 standard-library harness executing all 7 Polonius borrowck snippets (4 modes), all 10 next-trait-solver snippets (3 modes, including `unproductive-in-coherence.rs` and `#25860`), the live `cargo miri run` `#25860` UAF reproducer, and the multi-trial `google/zerocopy` full-crate compile stress check (automatically harvesting `--cfg` flags and `CARGO_*` environment variables via one untimed `cargo check --lib --locked --offline --no-default-features -vv` pass and scrubbing host paths before writing JSON).
2. **`support/probe_polonius_and_next_solver_results.json`**: Complete scrubbed JSON output captured on `2026-11-22` running `support/probe_polonius_and_next_solver.py` against `rustc 1.98.0-nightly (14210df0e 2026-05-31)`, `miri 0.1.0 (14210df0e2 2026-05-31)`, and `google/zerocopy@907b9175fee081872ec883ca4709e6ad922f8ed0` (`5` timed trials per mode plus `1` timed trial of `-Zpolonius=legacy`).
3. **`support/rustc_1_99_1_vs_1_102_0_nightly_reference_matrix.json`**: Scrubbed reference empirical matrix captured on `rustc 1.102.0-nightly (3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1, LLVM 23.1.5)` vs `rustc 1.99.1 (58cf8f9c35b355199727627d07ae34a4e2846d67)` across the 6-case Polonius matrix, 9-case trait-solver matrix, Miri `#25860` UAF (`rc = 1`), and 3-mode `zerocopy` wall-time profile (`1.646 s` vs `1.443 s` vs `1.447 s`).
4. **`support/PoloniusAndNextSolverCycleSoundness.lean`**: 921-line standalone Lean `v4.34.1` formalization and kernel-checked proofs of all 3 positive soundness/precision theorems and all 3 constructive counterexamples, audited with `-DwarningAsError=true` (`exit 0`) and `#print axioms` (`0` `Classical.choice`, `0` `sorryAx`, `0` `Lean.ofReduceBool`).

---

## Revalidation

To revalidate these findings against a newer `rustc` nightly/stable release, a newer `joshlf/anneal` commit, or a newer Lean 4 toolchain, run these four narrow, self-contained checks (total wall time under 60 seconds):

1. **Re-run the empirical `rustc` + `Miri` + `zerocopy` probe suite:**
   ```bash
   python3 support/probe_polonius_and_next_solver.py \
     --rustc rustc --cargo cargo \
     --zerocopy-dir /path/to/zerocopy \
     --trials 5 \
     --out /tmp/reval_polonius_next_solver.json
   ```
   Check specifically:
   - Whether `rustc_default` accepts `nll_problem_case_3_hashmap`, `loop_conditional_mut_return`, and `conditional_reborrow_and_mutate_else` (detecting channel default flips to `Polonius::Next`).
   - Whether `invariant_backward_loan_must_reject`, `invariant_time_travel_through_mut_ref_must_reject`, and `aliasing_mut_escape_must_reject` remain rejected in every Polonius mode (`ok: false`).
   - Whether `inductive_cycle_in_coherence_overlap_rejected` and `coherence_unproductive_assoc_norm_rejected` continue to fail with `E0119` across all solver modes.
   - Whether `hrtb_lifetime_transmute_25860_must_reject` remains rejected under default and `-Znext-solver=globally`, and whether upstream has fixed `#25860` under `-Zassumptions-on-binders=yes` (in which case `probe_3_miri_25860_uaf` will fail at compile time instead of triggering Miri UAF).

2. **Diff the four upstream `rust-lang/rust` control files against `342d74463af7dd3018ef6aa04dd5500c2deb5bd1`:**
   - `src/bootstrap/src/core/build_steps/compile.rs` (search `CFG_DEFAULT_POLONIUS_NEXT` and `CFG_DEFAULT_NEXT_SOLVER_GLOBALLY` to verify whether `stable`/`beta` channels have flipped defaults).
   - `compiler/rustc_borrowck/src/polonius/{mod.rs,constraints.rs,liveness.rs}` (check whether the kills-during-time-travel `FIXME` at `mod.rs:221-258` has been resolved by a two-step traversal or kill-aware reachability).
   - `compiler/rustc_next_trait_solver/src/solve/{search_graph.rs,eval_ctxt/mod.rs}` (check whether `PathKind::Inductive => unreachable!()` has been re-enabled to return `Err(NoSolution)`, and whether `TypingMode::Coherence` still returns `Certainty::overflow(false)`).
   - `compiler/rustc_next_trait_solver/src/solve/eval_ctxt/solver_region_constraints.rs` (check whether `region_assumptions_for_placeholders_in_universe` adds well-formedness guards before inserting placeholder assumptions).

3. **Re-verify the Lean 4 (`v4.34.1`) formalization and axiom boundary:**
   ```bash
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/PoloniusAndNextSolverCycleSoundness.lean
   ```
   Append `#print axioms` for all six theorems in a scratch copy under `/tmp` and confirm every theorem reports only `[]`, `[propext]`, or `[propext, Quot.sound]` (zero `Classical.choice`, `sorryAx`, or `Lean.ofReduceBool`).

4. **Re-check Anneal's capture driver flag policy:**
   Inspect `trusted/rustc-capture/src/driver.rs` in `joshlf/anneal` to confirm `COMPILER_VERSION` and verify whether `AnalysisCallbacks::config` explicitly rejects `-Zassumptions-on-binders=yes` and records active `Polonius` and `NextSolverConfig` modes in its capture provenance metadata.
