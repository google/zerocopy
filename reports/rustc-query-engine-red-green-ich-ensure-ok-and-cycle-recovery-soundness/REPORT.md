# Consolidated `rustc` Query Engine: Modifier Algebra, `QueryMode::EnsureOk` Disk-Deserialization Bypass, Asymmetric ICH Verification, `feedable` Consistency, and Multi-Tier Cycle/Depth-Limit Recovery

## Summary

The `rustc` demand-driven incremental query engine has been consolidated out of the former standalone `rustc_query_system` crate directly into `compiler/rustc_middle/src/{queries.rs, query/, dep_graph/}`, `compiler/rustc_query_impl/src/`, and `compiler/rustc_incremental/src/` across both `rustc 1.98.0-nightly` (`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`) and upstream `rust-lang/rust@342d74463af7dd3018ef6aa04dd5500c2deb5bd1`. Across this six-month window, the query inventory grew from **317 queries** (`14210df0e`) to **330 queries** (`342d74463`), while five structural modifier invariants remained exact across both snapshots:

1. **Modifier Algebra Invariants (`queries.rs`):** `eval_always ∩ cache_on_disk = ∅`; `feedable ∩ no_hash = {crate_for_resolver}` (a single AST-handoff query); `feedable ∩ cache_on_disk` comprises 11 signature/metadata/span queries; `handle_cycle_error` covers exactly 5 queries (`check_representability`, `check_representability_adt_ty`, `variances_of`, `fn_sig`, `layout_of`); `no_force` covers exactly 2 queries (`check_representability`, `check_representability_adt_ty`), strictly a subset of `handle_cycle_error`; and `depth_limit` covers exactly 2 queries (`eval_to_const_value_raw`, `layout_of`).
2. **`QueryMode::EnsureOk` Disk-Deserialization Bypass & Static vs. Dynamic Early Cutoff (`execution.rs:595-665`, `assert_dep_graph.rs:180-207`):** Although `typeck_root` carries `cache_on_disk` (`queries.rs:1253-1256`), calling `tcx.ensure_ok().typeck_root(caller_reused)` invokes `ensure_can_skip_execution`, which marks the node green via `try_mark_green` and returns `None` immediately—bypassing `try_execute_query`, `load_from_disk_or_invoke_provider_green`, and `query-cache.bin` deserialization whenever no downstream query demands `TypeckResults`. When a callee's body mutates without changing its signature (`fn_sig`), dynamic red-green early cutoff marks `caller_reused`'s `typeck_root` and `optimized_mir` green while `#[rustc_clean(cfg = "rev2", loaded_from_disk = "typeck_root")]` fails (`rc = 1`: `` `typeck_root(caller_reused)` should have been loaded from disk but it was not ``), even as static reachability (`#[rustc_if_this_changed(hir_owner)]` -> `#[rustc_then_this_would_need(typeck_root)]`) still reports `OK` along `hir_owner -> fn_sig -> typeck_root`. Moreover, `assert_dep_graph::check_paths` silently returns without checking any annotation when `-C incremental` is omitted (`retained_dep_graph` is `None`, `rc = 0`), even if `-Z query-dep-graph` is supplied.
3. **Asymmetric Incremental Compilation Hash (ICH) Verification (`incremental.rs:95-160`, `execution.rs:521-586`) & Version Divergence:** On a green dependency hit, recomputed non-disk values (`try_value == None`) undergo `incremental_verify_ich` **100% unconditionally** (`verify = true`), whereas disk-loaded `cache_on_disk` green hits verify only a `1/32` slice unless `-Zincremental-verify-ich` is set. Crucially, the two examined revisions differ in how that `1/32` slice is chosen:
   - At `1.98.0-nightly` (`14210df0e`, `execution.rs:523`), disk-loaded verification checks a **static** `1/32` slice (`prev_fingerprint.split().1.as_u64().is_multiple_of(32)`), leaving `31/32` of stable cached entries unverified across arbitrarily many sessions unless `-Zincremental-verify-ich` is enabled.
   - At upstream `342d74463` (`incremental.rs:95-103, 148`), verification is upgraded to a **deterministic 32-session rotating** slice over `key_fingerprint` (`Fingerprint::from(key_fingerprint).to_smaller_hash().as_u64() % 32 == dep_graph_data.session_count() % 32 || incremental_verify_ich`), applied uniformly in both `load_from_disk_or_invoke_provider_green` and `promote_from_disk_inner`. Because `session_count` increments strictly on successful commit (`serialized.rs:834`, `save.rs:33-35`), any ICH failure reproduces deterministically on immediate retry, and every cached key is verified within any 32 consecutive committed sessions.
4. **`feedable` Consistency (`execution.rs:363-401`, `calls.rs:215-273`):** `check_feedable_consistency` unconditionally panics if a `feedable + no_hash` query is recomputed after feeding (`hash_value_fn == None`), and for hashed `feedable` queries asserts `old_hash == new_hash || tcx.dcx().has_errors().is_some()`. Duplicate feeding (`query_feed`) mirrors this split: `bug!` on `no_hash`, `delayed_bug` on hash mismatch.
5. **Multi-Tier Cycle & Depth-Limit Recovery (`execution.rs:38-67, 403-438`, `handle_cycle_error.rs:19-211`):** Unmodified cycles invoke `handle_cycle_error::default` (`E0391` + fatal halt). Custom cycle handlers implement stratified recovery: `variances_of` calls `err.delay_as_bug()` and returns `[ty::Bivariant; n]` so `check_representability` (`no_force`) preserves the full cycle stack and emits `E0072`; `layout_of` rotates `QueryCycle::frames` via `search_for_cycle_permutation` (`VecDeque::rotate_left(1)`) to locate local `ty::Coroutine` frames and emit `E0733` on recursive `async fn`s; `fn_sig` delays the cycle as a bug and synthesizes an error-typed signature of HIR arity. Nested cycle detection is strictly three-tiered (`cycle_handler_nesting == 0` -> query handler; `== 1` -> forced `default`, bypassing custom handlers; `>= 2` -> `delayed_bug("doubly nested cycle error").raise_fatal()`). Both `depth_limit` queries share a single `ImplicitCtxt::query_depth` counter; overflow suggests `Limit(0) => Limit(2)` and `limit => limit * 2`.
6. **Mechanized Soundness & Sharpness (`support/QueryEngineRedGreenIchAndCycleSoundness.lean`):** A standalone Lean `v4.34.1` formalization proves red-green early-cutoff and `QueryMode::EnsureOk` deserialization-skip soundness (`[]` axioms), 32-session rotating plus 100% recomputed-green ICH verification completeness (`[propext]`), `feedable` consistency and `no_force` cycle-stack completeness (`[propext]`), and three constructive sharpness counterexamples (`ce1`–`ce3`), with zero `sorry`, zero `Classical.choice`, zero `omega`/`bv_decide`/`native_decide`, zero `partial def`, and zero `._unsafe_rec` across all 302 compiled declarations.

## Applicability

This report characterizes four precisely pinned, durable subjects and their interaction:

1. **Executed `rustc` toolchain (`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `rustc 1.98.0-nightly (14210df0e 2026-05-31)`, LLVM `22.1.6`, host `x86_64-unknown-linux-gnu`):** All live empirical compiler executions in `support/probe_query_engine_dep_graph_ich_and_cycles.py` (`support/query_engine_probe_results.json`) and the baseline `queries.rs` / `execution.rs` / `plumbing.rs` / `handle_cycle_error.rs` source audit were performed directly against this exact revision.
2. **Upstream `rustc` source cross-check (`rust-lang/rust@342d74463af7dd3018ef6aa04dd5500c2deb5bd1`, dated `2026-11-22`):** Primary-source inspection of `compiler/rustc_middle/src/{queries.rs, query/, dep_graph/, verify_ich.rs}`, `compiler/rustc_query_impl/src/`, and `compiler/rustc_incremental/src/` establishes the current consolidated architecture, 330-query modifier census, `QueryMode::EnsureOk` simplification, and rotating `1/32` `should_verify_loaded_value` implementation.
3. **Anneal trusted compiler capture seam (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`):** Primary-source inspection of `trusted/rustc-capture/src/driver.rs` establishes how Anneal pins `rustc 1.98.0-nightly (f8a08b688 2026-05-30)` (one day prior to our executed `14210df0e` nightly), executes `rustc_driver::run_compiler`, hooks `Callbacks::after_analysis`, and gates capture evidence on `tcx.dcx().has_errors().is_none()` after the `eval_always` `analysis` query. All TCB implications for verified `rustc` / Anneal MIR capture derive from combining this seam with the `rustc` query-engine findings above.
4. **Lean `v4.34.1` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`):** Kernel-checks `support/QueryEngineRedGreenIchAndCycleSoundness.lean` directly with `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`.

### Shared vs. Revision-Specific Behavior

| Mechanism | `1.98.0-nightly` (`14210df0e`) | Upstream HEAD (`342d74463`) | Relationship |
| :--- | :--- | :--- | :--- |
| Crate consolidation (`rustc_query_system` removed) | Absent (`rustc_middle` + `rustc_query_impl`) | Absent (`rustc_middle` + `rustc_query_impl`) | Shared |
| Total queries in `queries.rs` | `317` (`2,748` LOC) | `330` (`2,918` LOC) | +34 added/renamed, -21 removed/renamed |
| `eval_always ∩ cache_on_disk` | `∅` | `∅` | Shared invariant |
| `feedable ∩ no_hash` | `{crate_for_resolver}` | `{crate_for_resolver}` | Shared invariant |
| `handle_cycle_error` / `no_force` / `depth_limit` sets | `5` / `2` / `2` (identical names) | `5` / `2` / `2` (identical names) | Shared invariant |
| `QueryMode` ensure variants | `QueryMode::Ensure { ensure_mode: EnsureMode::{Ok, Done} }` (`execution.rs:569-612`) | `QueryMode::EnsureOk` only (`system.rs:19-24`, `execution.rs:595-626`); `TyCtxtEnsureDone` calls `tcx.$name(key)` directly (`query_api.rs:332-342`) | Simplified in `342d74463` |
| Disk-loaded green ICH sampling | **Static** `1/32`: `prev_fingerprint.split().1.as_u64().is_multiple_of(32)` (`execution.rs:523`) | **Rotating** `1/32`: `Fingerprint::from(key_fingerprint).to_smaller_hash().as_u64() % 32 == session_count() % 32` (`incremental.rs:95-103`) | Upgraded in `342d74463` |
| Disk-promotion ICH sampling (`exec_cache_promotions`) | Delegated to `execute_query_fn(..., QueryMode::Get)` (`plumbing.rs:171`) | Direct `promote_from_disk_inner` calling `should_verify_loaded_value` (`incremental.rs:106-160`) | Refactored in `342d74463` |
| Recomputed non-disk green ICH verification | `100%` unconditional (`verify = true`, `execution.rs:535`) | `100%` unconditional (`verify = true`, `execution.rs:561`) | Shared |
| `variances_of` cycle recovery slice length | `tcx.generics_of(def_id).own_params.len()` (`handle_cycle_error.rs:105`) | `tcx.generics_of(def_id).count()` (`handle_cycle_error.rs:105`) | Fixed parent-generics count in `342d74463` |
| `check_feedable_consistency`, 3-tier nesting, `depth_limit` doubling (`0 -> 2`, `n -> 2n`) | Identical logic | Identical logic | Shared |

Findings about `1.98.0-nightly` execution do not automatically extrapolate to future `rustc` releases without running the narrow revalidation probes in **Revalidation**; similarly, the `342d74463` rotating ICH code was verified by direct primary-source inspection and mechanized proof rather than live execution of a `2026-11-22` `rustc` binary (the host toolchain is `14210df0e`).

## Findings

### 1. Consolidated Query Engine Architecture and VTable Split

Basis: source

In both `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` and `rust-lang/rust@342d74463af7dd3018ef6aa04dd5500c2deb5bd1`, the historical `compiler/rustc_query_system` crate no longer exists. Query definitions, runtime data structures, execution machinery, and incremental persistence are partitioned across three compiler crates:

1. **`compiler/rustc_middle/src/queries.rs` & `query/` & `dep_graph/`:**
   - `queries.rs` declares every query via the `rustc_queries!` procedural macro, which expands into `rustc_with_all_queries!` consumed downstream to generate per-query modules, `TaggedQueryKey<'tcx>`, `QueryVTables<'tcx>`, `QueryArenas<'tcx>`, `Providers`, `ExternProviders`, and the four `TyCtxt` call surfaces (`TyCtxt`, `TyCtxtAt`, `TyCtxtEnsureOk`, `TyCtxtEnsureResult`, `TyCtxtEnsureDone`, plus `TyCtxtFeed` for `feedable` queries; `query_api.rs:9-363`).
   - Compile-time size assertions in `query_api.rs:97-124` bound every 64-bit query key to `size_of::<Key<'static>>() <= 88` bytes and every query return value to `size_of::<Value<'static>>() <= 64` bytes (motivating `arena_cache` for larger values).
   - `query/system.rs:27-90` defines `QueryVTable<'tcx, C>`, holding the boolean modifiers (`eval_always`, `depth_limit`, `feedable`, `cache_on_disk_local`, `separate_provide_extern`), `dep_kind`, `state: QueryState<'tcx, C::Key>` (sharded active-job hash table), `cache: C`, and monomorphized function pointers (`invoke_provider_fn`, `try_load_from_disk_fn`, `hash_value_fn: Option<...>`, `handle_cycle_error_fn`, `format_value`, `create_tagged_key`, `execute_query_fn`). Disk eligibility for a concrete key is governed by a single predicate (`system.rs:87-89`):
     ```rust
     pub fn will_cache_on_disk_for_key(&self, key: C::Key) -> bool {
         self.cache_on_disk_local && (!self.separate_provide_extern || key.as_local_key().is_some())
     }
     ```
     Thus queries carrying both `cache_on_disk` and `separate_provide_extern` (such as `optimized_mir`, `fn_sig`, `variances_of`, `mir_for_ctfe`) cache **only local-crate keys** in `query-cache.bin`; external-crate keys reload from crate metadata (`.rmeta`).
   - `dep_graph/dep_node.rs:168-230` defines `DepKindVTable<'tcx>` indexed by `DepKind`, storing `is_eval_always`, `key_fingerprint_style: KeyFingerprintStyle` (`DefPathHash`, `HirId`, `Unit`, `Opaque`), `force_from_dep_node_fn`, and `promote_from_disk_fn`. Eight non-query `DepKind` entries precede query variants (`dep_kind_vtables.rs:16-97`): `Null`, `Red`, `SideEffect`, `AnonZeroDeps`, `TraitSelect`, `CompileCodegenUnit`, `CompileMonoItem`, and `Metadata`.
2. **`compiler/rustc_query_impl/src/`:**
   - `query_vtables.rs:21-277` (at `342d74463`; previously `plumbing.rs`/`query_impl.rs` at `14210df0e`) stamps out one `QueryVTable` per query and separates `execute_query_incr` vs. `execute_query_non_incr` at `QuerySystem` construction time (`query_vtables.rs:199-203`).
   - `dep_kind_vtables.rs:101-130` builds `DepKindVTable` per query, gating forcing and promotion on key recoverability (`KeyFingerprintStyle::is_maybe_recoverable`, which is `true` for `DefPathHash`, `Unit`, `HirId` and `false` for `Opaque`; `dep_graph/mod.rs:48-55`):
     ```rust
     force_from_dep_node_fn: (can_recover && !is_no_force).then_some(...),
     promote_from_disk_fn: (can_recover && is_cache_on_disk).then_some(...),
     ```
   - `execution.rs` implements active-job locking, parallel `QueryLatch` waiting, `try_execute_query`, `check_feedable_consistency`, `start_query`/`depth_limit_error`, `execute_job_{non_incr,incr}`, `load_from_disk_or_invoke_provider_green`, `ensure_can_skip_execution`, and `force_query_dep_node`.
   - `incremental.rs` (extracted as its own module by `342d74463`) implements `encode_query_values`, `verify_query_key_hashes`, `should_verify_loaded_value`, `promote_from_disk_inner`, and `try_load_from_disk`.
   - `handle_cycle_error.rs` and `job.rs` implement cycle stack extraction (`find_cycle_in_stack`, parallel `break_query_cycle`) and the five specialized cycle handlers plus `default`.
3. **`compiler/rustc_incremental/src/`:**
   - `persist/load.rs` validates `prev_commandline_args_hash == sess.opts.dep_tracking_hash(false)` (`load.rs:45, 93-107`), reconciles work products, enforces `-Zassert-incr-state`, and initializes streaming `GraphEncoder` output into a staging file (`staging_dep_graph_path`).
   - `persist/save.rs` guards persistence on `sess.dcx().has_errors_or_delayed_bugs().is_some()` (`save.rs:33-35`), runs `assert_dep_graph` and `check_clean_annotations`, promotes still-unloaded green `cache_on_disk` values via `exec_cache_promotions`, closes the previous `query-cache.bin` mmap, and writes the new `query-cache.bin` and `dep-graph.bin`.

### 2. Exhaustive Modifier Census and Algebraic Invariants

Basis: source + execution

Programmatically parsing `compiler/rustc_middle/src/queries.rs` via `support/probe_query_engine_dep_graph_ich_and_cycles.py` (`parse_queries_rs`) yields exact modifier counts across both pinned snapshots:

| Modifier | `1.98.0-nightly` (`14210df0e`, 317 queries) | Upstream HEAD (`342d74463`, 330 queries) | Operational Effect |
| :--- | ---: | ---: | :--- |
| `separate_provide_extern` | 114 | 119 | Splits `local_providers` vs. `extern_providers`; restricts `cache_on_disk` to local keys (`system.rs:88`) |
| `cache_on_disk` | 57 | 58 | Encodes result into `query-cache.bin`; enables `try_load_from_disk_fn` and `promote_from_disk_fn` |
| `arena_cache` | 52 | 53 | Allocates provider/disk return value in per-query `TypedArena`, returning `&'tcx T` (or `Option`/`Result` wrapper) |
| `eval_always` | 36 | 38 | Skips `try_mark_green` (`execution.rs:480, 601`) and records deps in `TaskDepsRef::EvalAlways` (feeds depend on `FOREVER_RED_NODE`) |
| `feedable` | 27 | 27 | Generates `TyCtxtFeed::$name`; runs `check_feedable_consistency` on provider completion (`execution.rs:326-328`) |
| `no_hash` | 9 | 10 | Sets `hash_value_fn = None`; `alloc_and_color_node` conservatively marks recomputed nodes red (`graph.rs:809-815`) |
| `handle_cycle_error` | 5 | 5 | Dispatches to `rustc_query_impl::handle_cycle_error::$name` when `cycle_handler_nesting == 0` |
| `no_force` | 2 | 2 | Forces `force_from_dep_node_fn = None` even when key is recoverable (`dep_kind_vtables.rs:117`) |
| `depth_limit` | 2 | 2 | Checks and increments `ImplicitCtxt::query_depth` against `tcx.recursion_limit()` (`execution.rs:424-432`) |

#### Exact Cross-Modifier Intersections (Both Revisions)

1. **`eval_always ∩ cache_on_disk = ∅`:** No query is simultaneously `eval_always` and `cache_on_disk`. Because `execute_job_incr` skips `try_mark_green` whenever `query.eval_always` is true (`execution.rs:480`), disk caching an `eval_always` query would be unreachable dead weight; the empty intersection holds across all 317 (`14210df0e`) and 330 (`342d74463`) queries.
2. **`feedable ∩ no_hash = {crate_for_resolver}` (`queries.rs:2711-2715` at `342d74463`; `2580-2584` at `14210df0e`):** Exactly one query combines `feedable` and `no_hash`—`crate_for_resolver((): ()) -> &'tcx Steal<(rustc_ast::Crate, rustc_ast::AttrVec)>`. Because `check_feedable_consistency` (`execution.rs:375-382`) and `query_feed` (`calls.rs:247-257`) unconditionally panic on recomputing or double-feeding a `no_hash` query, `crate_for_resolver` relies on a strict single-feed-only lifecycle.
3. **`feedable ∩ cache_on_disk` (11 queries in both revisions):**
   - At `342d74463`: `type_of`, `generics_of`, `explicit_item_bounds`, `explicit_item_self_bounds`, `explicit_clauses_of`, `inferred_outlives_of`, `associated_item`, `eval_static_initializer`, `def_span`, `def_ident_span`, `codegen_fn_attrs`.
   - At `14210df0e`: identical except `explicit_clauses_of` was named `explicit_predicates_of`.
4. **`handle_cycle_error` (5 queries) and `no_force` (2 queries):**
   - `handle_cycle_error`: `check_representability`, `check_representability_adt_ty`, `variances_of`, `fn_sig`, `layout_of`.
   - `no_force`: `check_representability` (`queries.rs:594-601`), `check_representability_adt_ty` (`queries.rs:605-609`). Every `no_force` query is also `handle_cycle_error`.
5. **`depth_limit` (2 queries):**
   - `eval_to_const_value_raw` (`queries.rs:1389-1397`, also `cache_on_disk`) and `layout_of` (`queries.rs:1787-1793`, also `handle_cycle_error`).
6. **`no_hash` (10 queries at `342d74463`, 9 at `14210df0e`):**
   - `resolver_for_lowering_raw`, `index_ast` (added between `14210df0e` and `342d74463`, also `eval_always`), `params_in_repr`, `thir_body`, `mir_drops_elaborated_and_const_checked`, `mir_promoted`, `erase_and_anonymize_regions_ty`, `evaluate_root_goal_for_proof_tree_raw`, `crate_for_resolver`, `diagnostic_hir_wf_check`.
   - **MIR Pipeline Modifiers (`342d74463`):** `mir_built` is `feedable` (`Steal<mir::Body>`), `mir_promoted` (`queries.rs:677-683`) and `mir_drops_elaborated_and_const_checked` (`queries.rs:664-667`) are `no_hash` (`Steal<mir::Body>`), whereas `optimized_mir` (`queries.rs:734-738`), `promoted_mir` (`queries.rs:778-782`), `mir_for_ctfe` (`queries.rs:669-675`), and `mir_const_qualif` (`queries.rs:638-642`) are hashed and `cache_on_disk + separate_provide_extern`. Consequently, pre-optimization MIR stages (`mir_promoted`, `mir_drops_elaborated_and_const_checked`) can **never** perform red-green early cutoff upon recomputation (`alloc_and_color_node` colors `value_fingerprint == None` red at `graph.rs:809-815`) and are never serialized into `query-cache.bin`, whereas `optimized_mir` participates in both early cutoff and disk caching.

### 3. Red-Green Early Cutoff, `QueryMode::EnsureOk` Disk-Deserialization Bypass, and Static vs. Dynamic Dependency Reachability

Basis: source + execution + derived

#### Exact Control Flow of `QueryMode::EnsureOk`

In `compiler/rustc_middle/src/query/calls.rs:160-173`, `tcx.ensure_ok().$query(key)` checks the in-memory cache (`try_get_cached`); on a miss, it calls `(query.execute_query_fn)(tcx, DUMMY_SP, key, QueryMode::EnsureOk)`. In incremental mode, `execute_query_incr_inner` (`execution.rs:643-665`) executes:

```rust
let dep_node = DepNode::construct(tcx, query.dep_kind, &key);

if let QueryMode::EnsureOk = mode
    && ensure_can_skip_execution(query, tcx, dep_node)
{
    return None;
}
```

Inside `ensure_can_skip_execution` (`execution.rs:595-626`):
1. If `query.eval_always`, it returns `false` (must execute).
2. Otherwise it invokes `tcx.dep_graph.try_mark_green(tcx, &dep_node)`:
   - If `None` (new node or red dependency), it returns `false`, falling through to `try_execute_query`.
   - If `Some((_, dep_node_index))`, it records the caller's read (`tcx.dep_graph.read_index(dep_node_index)`), logs a profiler cache hit, and returns `true`.
3. Returning `None` from `execute_query_incr_inner` bypasses `try_execute_query` and `load_from_disk_or_invoke_provider_green` completely. Therefore:
   - Neither `(query.try_load_from_disk_fn)(tcx, prev_index)` nor `dep_graph_data.mark_debug_loaded_from_disk(*dep_node)` executes.
   - Even if `query.will_cache_on_disk_for_key(key)` is `true` and the previous session persisted the result into `query-cache.bin`, **no deserialization occurs** during analysis unless a later caller invokes the query in `QueryMode::Get` (or `save_dep_graph` later calls `exec_cache_promotions` to carry the green entry forward into the next session's `query-cache.bin`, `save.rs:76`).
   - Crucially, `save_dep_graph` runs `clean::check_clean_annotations(tcx)` at `save.rs:43` **before** `exec_cache_promotions` at `save.rs:76`, AND `promote_from_disk_inner` (`incremental.rs:106-160`) does not call `mark_debug_loaded_from_disk` anyway!
   - Equally important for `Steal`-based passes: as `calls.rs:83-90, 106-118` warns, `ensure_ok()` does **not** guarantee that a subsequent `QueryMode::Get` call will hit memory; for non-`cache_on_disk` queries, a later `Get` will still execute the provider (under `with_ignore`). Callers that must force execution before stealing a `Steal<mir::Body>` must use `tcx.ensure_done()` (which at `342d74463` delegates directly to `let _ = self.tcx.$name(key);`, `query_api.rs:336-340`).

#### Empirical Demonstration on `rustc 1.98.0-nightly` (`14210df0e`)

Running Suite 2 of `support/probe_query_engine_dep_graph_ich_and_cycles.py` live on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` confirms every piece of this mechanism:

1. **Three-Session Early Cutoff (`session1_rev1` -> `session2_rev2_early_cutoff` -> `session3_rev3_noop_verify_ich`):**
   - `helper_body(x: u32) -> u32` mutates its body (`x.wrapping_add(1)` -> `x.wrapping_add(2).wrapping_mul(5)`) between `rev1` and `rev2` while keeping its signature fixed.
   - `#[rustc_clean(cfg = "rev2", except = "hir_owner,optimized_mir,typeck_root")]` on `helper_body` **passes (`rc = 0`)**: `helper_body`'s `fn_sig`, `generics_of`, `predicates_of`, `type_of`, and `promoted_mir` remain clean (green), while only `hir_owner`, `typeck_root`, and `optimized_mir` become dirty (red).
   - `#[rustc_clean(cfg = "rev2")]` on `caller_reused(x: u32) -> u32 { helper_body(x).wrapping_mul(3) }` and `unrelated_fn` **passes (`rc = 0`)**: `fn_sig(helper_body)` cuts off red propagation so `caller_reused` has zero dirty dep nodes.
   - Session 3 (`rev3`, no-op rebuild with `-Zassert-incr-state=loaded -Zincremental-verify-ich`) **passes (`rc = 0`)** with 5 files hard-linked and 0 copied. Recorded dep-graph totals: `1,112` nodes / `2,767` edges (rev1) -> `1,118` nodes / `2,823` edges (rev2) -> `1,115` nodes / `2,804` edges (rev3). Session cache files on disk: `dep-graph.bin` (`47,391` B), `query-cache.bin` (`4,535` B), `metadata.rmeta` (`2,454` B), `work-products.bin` (`184` B), `<cgu>.o` (`4,464` B), `<session>.lock` (`0` B).
2. **`QueryMode::EnsureOk` Disk-Deserialization Bypass (`ensure_ok_skips_typeck_root_disk_load`):**
   - Adding `loaded_from_disk = "typeck_root"` to `caller_reused`'s `#[rustc_clean(cfg = "rev2", ...)]` attribute fails with **`rc = 1`**:
     ```text
     error: `typeck_root(caller_reused)` should have been loaded from disk but it was not
       --> <TMP>/lib_skip.rs:13:1
        |
     13 | pub fn caller_reused(x: u32) -> u32 {
        | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
     ```
   - Why: `analysis` checks local functions via `tcx.ensure_ok().typeck(id)` (which delegates to `ensure_ok().typeck_root(...)`, `calls.rs:48-52`). Because `fn_sig(helper_body)` was green, `try_mark_green` marks `typeck_root(caller_reused)` green and `ensure_can_skip_execution` returns `true`, returning `None` without touching `query-cache.bin`. Downstream `optimized_mir(caller_reused)` is also green, so nothing ever issues `QueryMode::Get` on `typeck_root(caller_reused)`.
3. **Positive Control (`positive_control_optimized_mir_loaded_from_disk`):**
   - Under `-C opt-level=2`, when `driver` mutates between `rev1` and `rev2` and calls clean `caller_inlined`, MIR optimization of dirty `driver` invokes `QueryMode::Get` on green `optimized_mir(caller_inlined)` to inspect inlining candidates. `#[rustc_clean(cfg = "rev2", loaded_from_disk = "optimized_mir")]` on `caller_inlined` **passes (`rc = 0`)**, demonstrating empirically that `query-cache.bin` deserialization and `mark_debug_loaded_from_disk` do fire for `QueryMode::Get` hits while being genuinely bypassed for `QueryMode::EnsureOk` hits.
4. **Static Reachability vs. Dynamic Early Cutoff & Silent No-Op without `-C incremental`:**
   - On `paths.rs` (`#[rustc_if_this_changed(hir_owner)]` on `body_only_src`, `#[rustc_then_this_would_need(typeck_root)]` on both `calls_src` and `independent_fn`):
     * **With `-Zquery-dep-graph` ONLY (no `-C incremental`):** `rustc` exits **`rc = 0`** with **zero** path diagnostics! In `compiler/rustc_incremental/src/assert_dep_graph.rs:60, 192`, `tcx.dep_graph.retained_dep_graph()` returns `None` when `DepGraph::data` is `None` (`DepGraph::new_disabled()`, `graph.rs:226-228, 245-247`), so `check_paths` executes `let Some(query) = retained_dep_graph else { return };` and silently succeeds without verifying a single annotation.
     * **With `-C incremental=...` AND `-Zquery-dep-graph`:** `rustc` exits **`rc = 1`**, emitting `error: OK` for `calls_src` (confirming a static path `hir_owner(body_only_src) -> fn_sig(body_only_src) -> typeck_root(calls_src)` exists in `RetainedDepGraph::transitive_predecessors` despite dynamic early cutoff!) and `error: no path from \`body_only_src\` to \`typeck_root\`` for `independent_fn`.
5. **Commandline-Hash Full Cache Invalidation (`commandline_hash_mismatch_rejected`):**
   - Rebuilding the `rev3` incremental directory with `-C opt-level=2 -Zassert-incr-state=loaded -Zincremental-info` fails with **`rc = 1`**, logging `[incremental] completely ignoring cache because of differing commandline arguments` (`load.rs:95-107`).

#### Mechanized Soundness & Sharpness

In `support/QueryEngineRedGreenIchAndCycleSoundness.lean`:
- **`ensureOk_green_skip_and_early_cutoff_sound`** (`[]` axioms) proves by structural induction on `MarkedGreen` (`forcedSameHash` + `allDepsGreen`) that under `DepTrackingSound` and `HashCollisionFree`, any non-`eval_always` green query preserves both its semantic value (`currVal q = prevVal q`) and error-freedom (`prevOk q → currOk q`), while `EnsureOkExec` transitions to `EnsureOkOutcome.skippedNoDiskLoad` with `loadedFromDisk = false` regardless of `cacheOnDisk = true` and `diskCache q = some v`.
- **`ce1_static_dep_path_exists_despite_dynamic_fn_sig_cutoff`** (`[propext]`) constructs the concrete 3-node graph `hirOwnerHelper -> fnSigHelper -> typeckRootCaller`, proving simultaneously that `StaticReachable` holds (`OK`), `hirOwnerHelper` mutated (`20 ≠ 10`), `typeckRootCaller` is `cacheOnDisk = true` with `diskCache = some 200`, `MarkedGreen` holds via early cutoff at `fnSigHelper`, and `EnsureOkExec` skips disk deserialization (`loadedFromDisk = false`).

### 4. Asymmetric ICH Verification: `1/32` Rotating Disk Sampling vs. `100%` Non-Disk Recomputed Green Verification

Basis: source + derived

When `execute_job_incr` (`execution.rs:480-498`) marks a non-`eval_always` dep node green, it calls `load_from_disk_or_invoke_provider_green` (`execution.rs:521-586`), which branches sharply depending on whether a value is deserialized from `query-cache.bin` or recomputed in memory:

```rust
let try_value = if query.will_cache_on_disk_for_key(key) {
    (query.try_load_from_disk_fn)(tcx, prev_index)
} else {
    None
};
let (value, verify) = match try_value {
    Some(value) => {
        if std::intrinsics::unlikely(tcx.sess.opts.unstable_opts.query_dep_graph) {
            dep_graph_data.mark_debug_loaded_from_disk(*dep_node)
        }
        let verify = should_verify_loaded_value(tcx, dep_graph_data, dep_node.key_fingerprint);
        (value, verify)
    }
    None => {
        let value = tcx.dep_graph.with_ignore(|| (query.invoke_provider_fn)(tcx, key));
        (value, true)
    }
};
if verify {
    incremental_verify_ich(tcx, dep_graph_data, &value, prev_index, query.hash_value_fn, query.format_value);
}
```

#### Critical Asymmetry and Cross-Revision Evolution

1. **Non-Disk Green Recomputations (`try_value == None`) Verify `100%` Unconditionally:**
   - Every query that is NOT cached on disk for the requested key (all 272 non-`cache_on_disk` queries at `342d74463`, plus external-crate keys of `cache_on_disk + separate_provide_extern` queries, plus any disk miss) runs its provider inside `tcx.dep_graph.with_ignore(...)` (since its previous-session edges were already promoted to the current dep graph by `try_mark_previous_green`) and sets `verify = true` **unconditionally**.
   - `incremental_verify_ich` (`verify_ich.rs:14-35`) computes `new_hash` (`Fingerprint::ZERO` if `hash_result` is `None`) and compares it with `dep_graph_data.prev_value_fingerprint_of(prev_index)`; any mismatch triggers `incremental_verify_ich_failed` (`panic!("Found unstable fingerprints for {dep_node:?}: ...")`), guarded by a thread-local `INSIDE_VERIFY_PANIC` flag to prevent recursive double-panics during debug formatting (`verify_ich.rs:62-85`).
   - Note also: because `no_hash` queries store `Fingerprint::ZERO` in `value_fingerprints` (`graph.rs:817`) and map `hash_result = None` to `Fingerprint::ZERO` (`verify_ich.rs:26`), `incremental_verify_ich` is a vacuous `0 == 0` match for `no_hash` queries if they ever reach a green hit (which only occurs if all of their deps were green, since recomputing a `no_hash` query via `with_task` always colors it red at `graph.rs:809-815`).
2. **Disk-Loaded Green Hits (`try_value == Some(value)`) Verify `1/32` by Default—with a Crucial Upgrade Between `14210df0e` and `342d74463`:**
   - **At `1.98.0-nightly` (`14210df0e`, `execution.rs:515-524`):**
     ```rust
     let prev_fingerprint = dep_graph_data.prev_value_fingerprint_of(prev_index);
     let verify = prev_fingerprint.split().1.as_u64().is_multiple_of(32)
         || tcx.sess.opts.unstable_opts.incremental_verify_ich;
     ```
     Because `prev_fingerprint` is fixed across sessions for an unchanged value, any cached query whose upper 64-bit value-fingerprint half is not divisible by 32 (`31/32 = 96.875%` of entries) is **never** ICH-verified across arbitrarily many incremental rebuilds unless `-Zincremental-verify-ich` is explicitly passed.
   - **At upstream HEAD (`342d74463`, `incremental.rs:95-103`):**
     ```rust
     pub(crate) fn should_verify_loaded_value(
         tcx: TyCtxt<'_>,
         dep_graph_data: &DepGraphData,
         key_fingerprint: PackedFingerprint,
     ) -> bool {
         let hash = Fingerprint::from(key_fingerprint).to_smaller_hash().as_u64();
         hash % 32 == dep_graph_data.session_count() % 32
             || tcx.sess.opts.unstable_opts.incremental_verify_ich
     }
     ```
     Three design refinements combine here:
     1. `to_smaller_hash()` mixes both 64-bit halves of `key_fingerprint` (avoiding skew from `DefPathHash` sharing `StableCrateId` or sequential `HirId`s, `incremental.rs:92-94`).
     2. Comparing `hash % 32 == session_count() % 32` rotates deterministically across all 32 residue classes as `SerializedDepGraph::session_count` advances by `+1` on each committed session (`serialized.rs:834`), guaranteeing full cache coverage every 32 committed sessions.
     3. Because `save_dep_graph` returns early without persisting a new `dep-graph.bin` whenever `has_errors_or_delayed_bugs().is_some()` (`save.rs:33-35`; empirically verified in Suite 3 via `failed_session_dep_graph_persisted = false`), an ICH ICE does not increment `session_count`, so retrying the failing build deterministically re-selects the exact same `1/32` residue class and reproduces the ICE.
     4. The exact same `should_verify_loaded_value` check also executes in `promote_from_disk_inner` (`incremental.rs:148-157`) when `exec_cache_promotions` loads green `cache_on_disk` entries that were skipped by `QueryMode::EnsureOk` during compilation.
3. **Deserialization Dependency Prohibition (`TaskDepsRef::Forbid`):**
   - `try_load_from_disk` (`incremental.rs:162-175`) wraps `on_disk_cache.try_load_query_value(tcx, prev_index)` in `tcx.dep_graph.with_query_deserialization(...)`, which sets `TaskDepsRef::Forbid` (`graph.rs:322-327, 518-521, 1295-1299`). Any attempt by a decoder to invoke a query and record a `read_index` triggers `panic_on_forbidden_read` (`graph.rs:1435-1463`), ensuring deserialization cannot silently mutate the dependency graph or inject cross-session phantom edges.
4. **Key-Hash Collision Verification (`verify_query_key_hashes`):**
   - `incremental.rs:46-80` checks that no two distinct in-memory keys in any query cache map to the same `DepNode`, running only when `-Zincremental-verify-ich` or `cfg!(debug_assertions)` is active. Additionally, `SerializedDepGraph`'s `LazyKindIndex::fingerprint_map` (`serialized.rs:198-219`) panics on duplicate `(DepKind, key_fingerprint)` entries (except `DepKind::SideEffect`) when loading a previous dep graph.

#### Mechanized Proof and Counterexample

In `support/QueryEngineRedGreenIchAndCycleSoundness.lean`:
- **`ich_rotating_32_and_recomputed_green_complete`** (`[propext]`) constructively proves:
  1. For every `session0, keyHash : Nat`, the explicit witness `k = (keyHash % 32 + (32 - session0 % 32)) % 32 < 32` satisfies `shouldVerifyLoaded false (session0 + k) keyHash = true`.
  2. For every non-disk green hit (`diskLoaded = none`), `shouldVerifyGreen` is unconditionally `true` and any hash mismatch (`currHash ≠ prevHash`) yields `IchCheckOutcome.unstableFingerprintIce`.
  3. Enabling `-Zincremental-verify-ich` (`verifyFlag = true`) makes `shouldVerifyGreen` unconditionally `true` for all hits.
  4. Under the `1.98.0-nightly` static predicate `shouldVerifyLoadedStatic198`, `prevValHash = 1` is **never** verified for any `session : Nat`.
- **`ce3_untracked_provider_nondeterminism_caught_by_ich_verify`** (`[propext]`) exhibits a concrete buggy provider (violating `DepTrackingSound`, e.g., sorting by unstable `DefId` as documented at `execution.rs:568-574`) that is erroneously colored green by `MarkedGreen`, immediately caught on non-disk recomputation (`unstableFingerprintIce`), missed in a single non-matching disk-loaded session (`session = 0, keyHash = 5` -> `skipped`), and caught by the rotating check at `k = 5 < 32`.

### 5. `feedable` Consistency and Dependency-Prefix Inheritance

Basis: source + derived

Query feeding (`TyCtxtFeed::$name` -> `calls.rs:215-273` -> `DepGraph::with_feed_task`, `graph.rs:601-664`) allows one query to pre-populate the cache of another query (primarily to break cyclic dependencies such as HIR lowering or const-generic typing):

1. **Prefix Dependency Recording (`graph.rs:641-656`):** When feeding a key not yet in cache, `with_feed_task` copies the **current task's reads recorded up to that instant** (`TaskDepsRef::Allow(deps)` -> `deps.lock().edges()`) as the fed `DepNode`'s dependency list. If the feeder itself is an `eval_always` query (`TaskDepsRef::EvalAlways`), `with_feed_task` attaches `[DepNodeIndex::FOREVER_RED_NODE]` (`graph.rs:647-649`) so the fed node can never be falsely marked green on a subsequent session without its `eval_always` feeder re-running. If called inside `TaskDepsRef::Forbid` (deserialization), `with_feed_task` panics (`graph.rs:651-653`).
2. **Pre-Existing Green Node Guard (`graph.rs:616-639`):** If the fed `DepNode` already existed in the previous session and was already colored green earlier in the current session (possible because the feeding caller has strictly more dependencies than the fed node and may later become red and re-execute), `with_feed_task` immediately runs `incremental_verify_ich` on the newly fed value against the previous green fingerprint before returning the existing `DepNodeIndex`.
3. **Duplicate Feeding Guard (`calls.rs:227-258`):** If `query_feed` finds an existing in-memory cached value `old`:
   - If `hash_value_fn` is `Some(f)`: compares `f(&old)` vs. `f(&value)` and calls `tcx.dcx().delayed_bug(...)` on mismatch (keeping `old`, dooming compilation).
   - If `hash_value_fn` is `None` (`no_hash`, i.e., `crate_for_resolver`): unconditionally calls `bug!("Trying to feed an already recorded value ...")`.
4. **Post-Recomputation Consistency Guard (`execution.rs:326-328, 363-401`):** Inside `try_execute_query`, after executing a `feedable` query provider (`execute_job_incr` / `execute_job_non_incr`) and before `job_guard.complete(...)`, `check_feedable_consistency` inspects `query.cache.lookup(&key)`:
   - If `None`: returns normally.
   - If `Some((cached_value, _))` and `query.hash_value_fn` is `None`: **unconditionally panics** (`"no_hash fed query later has its value computed. Remove \`no_hash\` modifier to allow recomputation."`, `execution.rs:375-382`).
   - If `Some((cached_value, _))` and `query.hash_value_fn` is `Some(f)`: computes `(old_hash, new_hash)` and, if `old_hash != new_hash`, executes:
     ```rust
     assert!(tcx.dcx().has_errors().is_some(), "Computed query value for {:?}({:?}) is inconsistent with fed value, ...", ...);
     ```
     Thus, on an error-free compilation, any recomputation of a previously fed hashed query must agree up to its stable fingerprint; inconsistency is tolerated strictly when compilation is already tainted by emitted errors.

### 6. Multi-Tier Cycle Recovery, `no_force` Cycle-Stack Completeness, and Depth-Limit Overflow

Basis: source + execution + derived

#### Active Job Tracking and Cycle Extraction

In single-threaded mode (`!sync::is_dyn_thread_safe()`), encountering `Entry::Occupied(ActiveKeyStatus::Started(job))` in `try_execute_query` (`execution.rs:336-355`) immediately invokes `find_and_handle_cycle` (`execution.rs:163-176`), which collects all active jobs (`CollectActiveJobsKind::FullNoContention`) and walks `QueryJob::parent` links in `find_cycle_in_stack` (`job.rs:139-172`) to construct `QueryCycle { usage, frames }`. Under the parallel frontend (`sync::is_dyn_thread_safe()`), waiters block on `QueryLatch` condvars (`latch_wait_on`, `execution.rs:179-217`), and the deadlock detector runs `break_query_cycle` (`job.rs:438-450`) to extract one cycle and resume a resumable waiter with `Err(cycle)`.

#### Three-Tier Cycle Nesting Gate (`execution.rs:38-67`)

`handle_cycle` guards against secondary cycles occurring while formatting or recovering from a primary cycle using `tcx.query_system.cycle_handler_nesting: Lock<u8>` (decremented via `defer` on exit):

- **`nesting == 0`:** `nested = false`; builds `error = create_cycle_error(tcx, &cycle, false)` and invokes `(query.handle_cycle_error_fn)(tcx, key, cycle, error)`.
- **`nesting == 1`:** `nested = true`; builds `NestedCycle` via `create_cycle_error(tcx, &cycle, true)` and **unconditionally routes to `handle_cycle_error::default(error)`**, bypassing any custom `handle_cycle_error` handler (`execution.rs:61-64`).
- **`nesting >= 2`:** Immediately halts with `tcx.dcx().delayed_bug("doubly nested cycle error").raise_fatal()` (`execution.rs:50-53`), preventing infinite error-reporting recursion.

#### The Five Custom Cycle Handlers and the Necessity of `no_force`

| Query | Modifiers | Recovery Strategy (`handle_cycle_error.rs`) | Observed Diagnostic (Suite 3, `14210df0e`) |
| :--- | :--- | :--- | :--- |
| All other 325 queries (`default`) | (none) | `err.emit_err().raise_fatal()` (`L19-22`); `create_cycle_error` special-cases `TyAlias`/`TraitAlias` cycles (`L384-408`) | `default_const_cycle_e0391` (`rc=1`, `E0391`); `type_alias_cycle_e0391` (`rc=1`, `E0391`) |
| `variances_of` | `cache_on_disk`, `handle_cycle_error`, `separate_provide_extern` | `err.delay_as_bug()`; allocates `[ty::Bivariant; n]` where `n = generics_of(def_id).count()` (`L98-107`; `.own_params.len()` in `14210df0e`) | Allows compilation to continue past variance cycle into representability check -> `E0072` (no `E0391`) |
| `check_representability` & `check_representability_adt_ty` | `handle_cycle_error`, `no_force` | `check_representability_inner` (`L67-96`) scans `cycle.frames` for `TaggedQueryKey::check_representability(field_id)` (`DefKind::Field`), rotates to lowest `def_span` (`L223-229`), emits `E0072` (`recursive_type_error`) + `raise_fatal()` | `variances_of_delayed_to_e0072` (`rc=1`, `E0072`); `mutual_adt_cycle_e0072_span_rotation` (`rc=1`, `E0072` naming `` `Second` and `First` `` ordered by span line 1 then line 2); identical under `-C incremental` (`rc=1`, `E0072`) |
| `layout_of` | `depth_limit`, `handle_cycle_error` | `err.delay_as_bug()`; calls `search_for_cycle_permutation(&cycle.frames, ...)` (`L110-126`, `VecDeque::rotate_left(1)`) to find a local `ty::Coroutine` frame and emit `E0733`, else falls back to `create_cycle_error(..., false)`; calls `diag.emit_err().raise_fatal()` (`L128-211`) | `layout_of_async_fn_cycle_e0733` (`rc=1`, `E0733`: `recursion in an async fn requires boxing`, naming `ping` -> `pong`) |
| `fn_sig` | `cache_on_disk`, `handle_cycle_error`, `separate_provide_extern` | `guar = err.delay_as_bug()`; reads local HIR `sig.decl.inputs.len()` and returns `EarlyBinder(Binder::dummy(fn(err, ..., err) -> err))` (`L24-47`) | Delays cycle error and returns dummy error signature so downstream typeck can emit primary errors |

**Why `no_force` Is Strictly Necessary (`queries.rs:597-600`, `dep_kind_vtables.rs:117`):**
During incremental `try_mark_previous_green` (`graph.rs:951-997`), when checking whether a dependency `d` of query `q` is green, `rustc` attempts `tcx.try_force_from_dep_node(d, ...)`, which calls `force_query_dep_node(d)` -> `try_execute_query(d)` **while `q` is still inside `try_mark_green` and has not yet pushed its own normal provider call onto the active `QueryJob` stack for the cycle**. If `check_representability` (`LocalDefId`, recoverable via `DefPathHash`) lacked `no_force`, forcing an intermediate field/ADT dep node inside a recursive ADT cycle would enter the cycle with a truncated `QueryCycle::frames` missing outer `DefKind::Field` frames, corrupting or crashing `check_representability_inner`'s `item_and_field_ids` scan (`handle_cycle_error.rs:70-82, 223-228` calls `.unwrap()` on `min_by_key`!). Setting `no_force` forces `DepKindVTable::force_from_dep_node_fn = None` (`dep_kind_vtables.rs:117`), causing `try_mark_previous_green` to return `None` so the full cycle executes top-down with every frame on the active stack.
- Mechanized proof: `feedable_consistency_and_no_force_cycle_stack_sound` (part 3) proves `no_force = true` guarantees both caller and callee remain on `cycleStackAfterDepCheck`; `ce2_forcing_inside_cycle_truncates_active_cycle_frames_without_no_force` (`[]` axioms) constructs the explicit 2-ADT counterfactual showing `adtA ∉ cycleStackAfterDepCheck` when `noForce = false`.
- Frame-rotation completeness: `search_for_cycle_permutation_complete` (`[propext]`) proves that for any predicate `P` satisfied by at least one element of `frames`, iterating `rotateLeft` up to `frames.length - 1` times is guaranteed to bring a `P`-satisfying frame to index `0`.

#### Shared `ImplicitCtxt::query_depth` Counter and `depth_limit` Doubling (`execution.rs:403-438`, `job.rs:178-198`)

Only two queries carry `depth_limit`: `eval_to_const_value_raw` and `layout_of`. Both share a **single** `ImplicitCtxt::query_depth: usize` counter checked in `start_query`:

```rust
if depth_limit && !icx.tcx.recursion_limit().value_within_limit(icx.query_depth) {
    depth_limit_error(icx.tcx, job_id);
}
let icx = ImplicitCtxt {
    query: Some(job_id),
    query_depth: icx.query_depth + if depth_limit { 1 } else { 0 },
    ..*icx
};
```

Upon overflow, `depth_limit_error` computes:
```rust
let suggested_limit = match tcx.recursion_limit() {
    Limit(0) => Limit(2),
    limit => limit * 2,
};
```
and calls `find_dep_kind_root` (`job.rs:178-198`), which walks parent jobs counting **only frames matching the overflowing query's own `TaggedQueryKey` discriminant**. Two empirical behaviors observed live in Suite 3 (`14210df0e`) confirm this exact interplay:
1. **`depth_limit_4_layout_of_doubles_to_8` (`rc = 1`):** `#![recursion_limit = "4"]` on `size_of::<Layer<Layer<Layer<Layer<Layer<Layer<u8>>>>>>>()` overflows `layout_of` and emits `consider increasing the recursion limit by adding a #![recursion_limit = "8"]` (`4 * 2 = 8`) with `note: query depth increased by 4 when computing layout of Layer<Layer<Layer<Layer<Layer<Layer<u8>>>>>>`.
2. **`depth_limit_0_const_eval_special_cases_to_2` (`rc = 1`):** `#![recursion_limit = "0"]` on `pub const C2: usize = 1; pub const C1: usize = C2 + 1; pub type Arr = [u8; C1];` emits `consider increasing the recursion limit by adding a #![recursion_limit = "2"]` (`Limit(0) => Limit(2)`) with `note: query depth increased by 1 when computing layout of usize`. Why `depth increased by 1` on `layout_of(usize)`? Because `eval_to_const_value_raw(C1)` entered at `query_depth == 0` (`0 <= 0`, passing `Limit(0)`), incremented the shared `query_depth` to `1`, and then invoked `layout_of(usize)`, which failed `Limit(0).value_within_limit(1)`! `find_dep_kind_root` counted only `layout_of` frames (`1`), directly exposing that `eval_to_const_value_raw` and `layout_of` share a single cross-query `query_depth` budget.

### 7. Implications for Anneal (`joshlf/anneal@c131b320e`) and Verified-`rustc` Trusted Computing Bases

Basis: source + derived

At `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `trusted/rustc-capture/src/driver.rs` pins `COMPILER_VERSION = "1.98.0-nightly (f8a08b688 2026-05-30)"` (`L25, 45-47`), runs `rustc_driver::run_compiler(&compiler_args, &mut callbacks)` (`L137`), and implements `Callbacks::after_analysis` (`L75-84`) recording `self.analysis_reached = tcx.dcx().has_errors().is_none()` before returning `Compilation::Continue`. Five concrete TCB contracts follow directly from the consolidated `rustc` query engine:

1. **Disable Incremental Disk Cache Reuse (or Force `-Zincremental-verify-ich`) During Trusted MIR Capture:**
   - Because `optimized_mir` (`queries.rs:734-738`) and `mir_for_ctfe` (`queries.rs:669-675`) are `cache_on_disk + separate_provide_extern`, invoking a capture driver with `-C incremental=...` permits deserializing MIR directly from an untrusted/prior `query-cache.bin`.
   - Worse, on `1.98.0-nightly` (`14210df0e` / Anneal's pinned `f8a08b688` era), disk-loaded ICH verification uses the **static `1/32` slice** (`execution.rs:523`), leaving `31/32` of cached MIR bodies unverified on every single build without `-Zincremental-verify-ich`. Even at `342d74463` (rotating `1/32`), a single incremental capture still leaves `31/32` of disk-loaded entries unverified in that session.
   - Therefore, any trusted MIR extraction driver (`anneal-rustc-capture` or verified-`rustc` proof ingestion) must either **forbid `-C incremental`** (running cleanly with `DepGraph::new_disabled()`, ensuring every MIR body is freshly lowered in-session) or explicitly pass `-Zincremental-verify-ich` and verify cache directory provenance.
2. **Capture-Stage Selection Interacts with `no_hash` and `Steal`:**
   - Pre-optimization `Runtime(PostCleanup)` MIR (`mir_drops_elaborated_and_const_checked`, `queries.rs:664-667`) and `mir_promoted` (`queries.rs:677-683`) are `no_hash` and return `&'tcx Steal<mir::Body<'tcx>>`. They are never persisted to `query-cache.bin`, can never be cut off green on recomputation, and will be stolen by `optimized_mir` once codegen/optimization runs.
   - Any callback or verifier pass reading `mir_drops_elaborated_and_const_checked` must **never** rely on `tcx.ensure_ok()` to guarantee a consumer ran before stealing (`calls.rs:83-90`); it must extract before the stealing query or use `tcx.ensure_done()` (`query_api.rs:332-342`).
3. **`eval_always` Guarantee of `Callbacks::after_analysis`:**
   - Because `analysis(())` is marked `eval_always` (`queries.rs:406-412` at `342d74463`; `380-386` at `14210df0e`), `rustc` never skips the top-level analysis driver via red-green memoization. However, `analysis` itself invokes per-item checks (`typeck`, `mir_borrowck`, etc.) via `tcx.ensure_ok()`, which **does** skip provider execution and disk deserialization on green items in incremental mode.
4. **Delayed Cycle Bugs Cannot Produce Silent Clean Captures:**
   - Custom cycle handlers (`variances_of`, `fn_sig`, `layout_of`) call `err.delay_as_bug()` so compilation can continue to emit primary diagnostics (`E0072`, `E0733`).
   - Because Anneal's `after_analysis` returns `Compilation::Continue` (`driver.rs:83`), `rustc_driver::run_compiler` always executes its final `abort_if_errors` check (promoting any un-emitted delayed bug to an ICE/fatal error) before returning to `driver.rs:145-150`, and `save_dep_graph` refuses to persist an incremental session if `has_errors_or_delayed_bugs().is_some()` (`save.rs:33-35`). However, any future `after_analysis` extractor that inspects `tcx` *during* the callback should check `tcx.dcx().has_errors_or_delayed_bugs().is_none()` (not only `has_errors().is_none()`, which misses an un-emitted `delayed_bug` until session teardown) before trusting extracted MIR/types.
5. **Verified-`rustc` Incremental Proof-Cache Design:**
   - A verified incremental compiler or proof cache mirroring `rustc`'s red-green architecture must enforce three explicit hypotheses formalized in `QueryEngineRedGreenIchAndCycleSoundness.lean`:
     (a) `DepTrackingSound` (no untracked nondeterminism such as session-local `DefId` sorting; enforced empirically by `100%` non-disk green ICH verification and rotating/full disk ICH verification),
     (b) `HashCollisionFree` (collision resistance of the fingerprint over canonical IR + proof inputs), and
     (c) `TaskDepsRef::Forbid` during cache deserialization (preventing phantom edges).

## Boundaries

1. **Live Execution of `rust-lang/rust@342d74463af7dd3018ef6aa04dd5500c2deb5bd1` Binary (`not examined`):** All live `rustc` subprocess probes executed against the installed `rustc 1.98.0-nightly (14210df0e 2026-05-31)` binary; `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` was audited by direct primary-source inspection (and programmatic `queries.rs` parsing) rather than building a stage1 compiler binary from source. Consequently, runtime execution of the 32-session rotating `should_verify_loaded_value` loop on a `2026-11-22` nightly binary is `not examined` (though its exact formula `hash % 32 == session_count % 32 || incremental_verify_ich` is directly verified in `incremental.rs:95-103` and formally proved in Lean).
2. **Parallel Frontend (`-Z threads=N`) Deadlock & Cycle-Breaking Runtime (`not examined`):** `job.rs:200-450` (`latch_wait_on`, `break_query_cycle`, `process_cycle`) and concurrent `DepNodeColorMap::try_set_color` CAS races (`graph.rs:1355-1373`, `serialized.rs:979-1024`) were inspected in source, but Suite 2 and Suite 3 executed under single-threaded `rustc` (`-Z threads=1` default). Multi-threaded cycle-breaking nondeterminism and lock-contention schedules are `not examined`.
3. **Deliberate Runtime Triggering of `check_feedable_consistency` Panics, Doubly Nested Cycle ICEs (`nesting >= 2`), and Corrupted-Cache ICH ICEs (`not examined`):** These internal ICE paths require either a custom `rustc_driver` provider bug or mutating binary `query-cache.bin` / `dep-graph.bin` bytes on disk; they were verified from primary source (`execution.rs:38-67, 363-401`, `verify_ich.rs:14-86`) and formalized in Lean rather than injected into a patched compiler binary.
4. **Anneal Exact Pinned Nightly `f8a08b688` vs. Executed `14210df0e` (`known not to apply` to bit-identical binary identity):** Anneal `trusted/rustc-capture/src/driver.rs:25` pins `1.98.0-nightly (f8a08b688 2026-05-30)`, whereas our executed toolchain is `1.98.0-nightly (14210df0e 2026-05-31)` (one day later). While the query-engine architecture is contiguous across that 1-day delta, `anneal-rustc-capture` itself rejects `14210df0e` via its exact `rustc_version_str()` check (`driver.rs:45-47`).
5. **Cryptographic Collision Resistance of SipHash-128 (`unknown` / external assumption):** `QueryEngineRedGreenIchAndCycleSoundness.lean` explicitly parameterizes Theorem 1 (`ensureOk_green_skip_and_early_cutoff_sound`) by `HashCollisionFree S.valHash`. Lean does not prove collision freedom of `rustc`'s 128-bit `StableHasher` (SipHash-128); any real hash collision can cause unsound early cutoff or undetected `feedable` divergence.
6. **Lean Formalization Scope (`known not to apply` as a full Rust compiler extraction proof):** `support/QueryEngineRedGreenIchAndCycleSoundness.lean` is a standalone mathematical model of the query-engine state machine (red-green marking, `EnsureOk`, rotating/unconditional ICH verification, `feedable` checking, `no_force` stack preservation, 3-tier nesting, frame rotation, and depth-limit doubling). It does not import `joshlf/anneal`'s `Trusted.MirSemantics` nor verify the Rust implementation of `rustc_query_impl` at the machine-code level.
7. **Unsupported Diagnostic Combination (`unsupported`):** Passing `#[rustc_if_this_changed]` / `#[rustc_then_this_would_need]` with `-Zquery-dep-graph` alone (omitting `-C incremental`) is silently ignored by `assert_dep_graph::check_paths` (`assert_dep_graph.rs:192`) rather than producing an error—a known hazard when writing incremental dependency regression tests.

## Evidence

All primary evidence was acquired and cross-checked on `2026-11-22`.

### 1. Upstream Primary-Source Locations

#### `rust-lang/rust` at `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (`2026-11-22`)

| File | Line Range / Symbol | Verified Content |
| :--- | :--- | :--- |
| `compiler/rustc_middle/src/queries.rs` | Full file (2,918 LOC); `L241-244` (`hir_owner`), `L406-412` (`analysis`), `L594-609` (`check_representability*`), `L649-683` (`mir_built`/`mir_drops_elaborated_and_const_checked`/`mir_promoted`), `L734-738` (`optimized_mir`), `L1050-1055` (`variances_of`), `L1197-1202` (`fn_sig`), `L1253-1256` (`typeck_root`), `L1389-1397` (`eval_to_const_value_raw`), `L1787-1793` (`layout_of`), `L2711-2715` (`crate_for_resolver`) | `330` total queries; exact modifier counts and intersections parsed programmatically in `support/query_engine_probe_results.json`. |
| `compiler/rustc_middle/src/query/modifiers.rs` | `L1-95` | Normative doc definitions of all 10 query modifiers (`arena_cache`, `cache_on_disk`, `depth_limit`, `desc`, `eval_always`, `feedable`, `handle_cycle_error`, `no_force`, `no_hash`, `separate_provide_extern`). |
| `compiler/rustc_middle/src/query/query_api.rs` | `L9-363` (`define_query_api!`), `L97-124` (key `<= 88 B`, value `<= 64 B` const asserts), `L332-342` (`TyCtxtEnsureDone`) | Macro generation of `TyCtxt`, `TyCtxtAt`, `TyCtxtEnsureOk`, `TyCtxtEnsureResult`, `TyCtxtEnsureDone`, `TyCtxtFeed`, `TaggedQueryKey`, `QueryVTables`, `QueryArenas`. |
| `compiler/rustc_middle/src/query/system.rs` | `L19-24` (`QueryMode`), `L27-90` (`QueryVTable`, `will_cache_on_disk_for_key`), `L104-133` (`QuerySystem`) | `QueryMode::{Get, EnsureOk}`; local-only disk caching for `separate_provide_extern`; `cycle_handler_nesting: Lock<u8>`. |
| `compiler/rustc_middle/src/query/calls.rs` | `L47-119`, `L143-273` (`query_get_at`, `query_ensure_ok`, `query_ensure_result`, `query_feed`) | `ensure_ok` warning for `Steal`; `query_ensure_result` turning `None` skip into `Ok(())`; `query_feed` duplicate handling (`delayed_bug` vs. `bug!` on `no_hash`). |
| `compiler/rustc_middle/src/dep_graph/dep_node.rs` | `L168-230` (`DepKindVTable`) | `is_eval_always`, `key_fingerprint_style`, `force_from_dep_node_fn`, `promote_from_disk_fn`. |
| `compiler/rustc_middle/src/dep_graph/mod.rs` | `L30-56` (`KeyFingerprintStyle`), `L98-119` (`try_force_from_dep_node`) | Recoverable fingerprint styles (`DefPathHash`, `HirId`, `Unit`) vs. `Opaque`. |
| `compiler/rustc_middle/src/dep_graph/graph.rs` | `L188-210` (`FOREVER_RED_NODE`), `L245-247` (`retained_dep_graph`), `L322-327` (`with_query_deserialization`), `L368-405` (`with_task`), `L601-664` (`with_feed_task`), `L708-715` (`session_count`), `L791-835` (`alloc_and_color_node`), `L903-1029` (`try_mark_green`, `try_mark_previous_green`), `L1064-1085` (`exec_cache_promotions`), `L1282-1300` (`TaskDepsRef`), `L1435-1463` (`panic_on_forbidden_read`) | Complete red-green engine, `no_hash` conservative red coloring, `with_feed_task` prefix-edge copying and `FOREVER_RED_NODE` under `EvalAlways`, `TaskDepsRef::Forbid` during deserialization. |
| `compiler/rustc_middle/src/dep_graph/serialized.rs` | `L103-133` (`SerializedDepGraph`), `L183-224` (`LazyKindIndex::fingerprint_map`), `L834` (`session_count.checked_add(1)`), `L960-1025` (`send_and_color`, `send_promoted`) | Streaming dep-graph serialization, duplicate-node panic check, monotonic `session_count` increment on finalize. |
| `compiler/rustc_middle/src/verify_ich.rs` | `L14-86` (`incremental_verify_ich`, `incremental_verify_ich_failed`) | Fingerprint recomputation, `Fingerprint::ZERO` fallback for `None`, `INSIDE_VERIFY_PANIC` reentrancy guard. |
| `compiler/rustc_query_impl/src/dep_kind_vtables.rs` | `L16-97` (`non_query`), `L101-130` (`make_dep_kind_vtable_for_query`) | `(can_recover && !is_no_force).then_some(...)` and `(can_recover && is_cache_on_disk).then_some(...)`. |
| `compiler/rustc_query_impl/src/execution.rs` | `L38-67` (`handle_cycle`), `L279-360` (`try_execute_query`), `L363-401` (`check_feedable_consistency`), `L403-438` (`depth_limit_error`, `start_query`), `L470-515` (`execute_job_incr`), `L521-586` (`load_from_disk_or_invoke_provider_green`), `L595-626` (`ensure_can_skip_execution`), `L643-665` (`execute_query_incr_inner`), `L671-687` (`force_query_dep_node`) | Core query execution, 3-tier nesting, feedable consistency assertion, shared `query_depth` check & doubling, `100%` non-disk green ICH verification, `EnsureOk` disk-load bypass. |
| `compiler/rustc_query_impl/src/incremental.rs` | `L46-80` (`verify_query_key_hashes`), `L95-103` (`should_verify_loaded_value`), `L106-160` (`promote_from_disk_inner`), `L162-175` (`try_load_from_disk`) | Deterministic rotating `1/32` ICH sampling (`hash % 32 == session_count % 32 || incremental_verify_ich`) in both query load and cache promotion; `with_query_deserialization`. |
| `compiler/rustc_query_impl/src/handle_cycle_error.rs` | `L19-22` (`default`), `L24-47` (`fn_sig`), `L49-96` (`check_representability*`), `L98-107` (`variances_of`), `L110-126` (`search_for_cycle_permutation`), `L128-211` (`layout_of`), `L215-296` (`recursive_type_error`), `L346-430` (`create_cycle_error`) | All 5 specialized cycle handlers, span-ordered `E0072` rotation, coroutine `E0733` permutation search, `Alias::{Ty, Trait}` detection. |
| `compiler/rustc_query_impl/src/job.rs` | `L139-172` (`find_cycle_in_stack`), `L178-198` (`find_dep_kind_root`), `L244-450` (parallel deadlock cycle breaker) | Active stack cycle reconstruction and per-discriminant depth root counter. |
| `compiler/rustc_incremental/src/assert_dep_graph.rs` | `L56-101` (`assert_dep_graph`), `L180-207` (`check_paths`) | Line `192` silent return when `retained_dep_graph` is `None`; static `transitive_predecessors` reachability check. |
| `compiler/rustc_incremental/src/persist/clean.rs` | `L38-110` (`BASE_*`, `LABELS_*`), `L127-166` (`check_clean_annotations`), `L318-385` (`assert_dirty`, `assert_clean`, `loaded_from_disk`) | Semantics of `#[rustc_clean(cfg=..., except=..., loaded_from_disk=...)]`. |
| `compiler/rustc_incremental/src/persist/load.rs` | `L35-114` (`load_dep_graph`), `L151-173` (`maybe_assert_incr_state`) | Commandline args hash check (`dep_tracking_hash(false)`), work-product reconciliation, `-Zassert-incr-state`. |
| `compiler/rustc_incremental/src/persist/save.rs` | `L25-90` (`save_dep_graph`) | Early abort on `has_errors_or_delayed_bugs().is_some()` (`L33-35`), ordering of `assert_dep_graph` (`L42`), `check_clean_annotations` (`L43`), and `exec_cache_promotions` (`L76`). |

#### `rust-lang/rust` at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`1.98.0-nightly`, `2026-05-31`)

- `compiler/rustc_middle/src/queries.rs` (2,748 LOC): `317` total queries (`114` `separate_provide_extern`, `57` `cache_on_disk`, `52` `arena_cache`, `36` `eval_always`, `27` `feedable`, `9` `no_hash`, `5` `handle_cycle_error`, `2` `no_force`, `2` `depth_limit`).
- `compiler/rustc_query_impl/src/execution.rs:515-527`: static `1/32` disk-loaded ICH check `prev_fingerprint.split().1.as_u64().is_multiple_of(32) || incremental_verify_ich`; `L569-612`: `EnsureMode::{Ok, Done}`.
- `compiler/rustc_query_impl/src/plumbing.rs:139-174`: `promote_from_disk_inner` delegating to `(query.execute_query_fn)(tcx, DUMMY_SP, key, QueryMode::Get)`.
- `compiler/rustc_query_impl/src/handle_cycle_error.rs:100-107`: `variances_of` using `.own_params.len()`.

#### `joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`

- `trusted/rustc-capture/src/driver.rs:25, 45-47, 75-84, 137-150`: pins `1.98.0-nightly (f8a08b688 2026-05-30)`, executes `rustc_driver::run_compiler`, hooks `Callbacks::after_analysis`, records `tcx.dcx().has_errors().is_none()`, and returns `Compilation::Continue`.

### 2. Live Empirical Probe Artifact (`support/probe_query_engine_dep_graph_ich_and_cycles.py` & `support/query_engine_probe_results.json`)

Executed on `2026-11-22` with `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (`LLVM 22.1.6`, `x86_64-unknown-linux-gnu`), exit code `0`:

| Probe Case | Exit Code | Key Observed Output |
| :--- | ---: | :--- |
| Suite 1 (HEAD `342d74463`) | 0 | `330` queries; `119` `separate_provide_extern`, `58` `cache_on_disk`, `53` `arena_cache`, `38` `eval_always`, `27` `feedable`, `10` `no_hash`, `5` `handle_cycle_error`, `2` `no_force`, `2` `depth_limit` |
| Suite 1 (Executed `14210df0e`) | 0 | `317` queries; `114` `separate_provide_extern`, `57` `cache_on_disk`, `52` `arena_cache`, `36` `eval_always`, `27` `feedable`, `9` `no_hash`, `5` `handle_cycle_error`, `2` `no_force`, `2` `depth_limit` |
| Suite 2: `session1_rev1` | 0 | Clean baseline; `1,112` nodes, `2,767` edges |
| Suite 2: `session2_rev2_early_cutoff` | 0 | `helper_body` dirty only on `{hir_owner, optimized_mir, typeck_root}`; `caller_reused` & `unrelated_fn` 100% clean; `1,118` nodes, `2,823` edges; 5 files hard-linked |
| Suite 2: `session3_rev3_noop_verify_ich` | 0 | Full `-Zincremental-verify-ich` pass; `1,115` nodes, `2,804` edges; cache files: `dep-graph.bin` (`47,391` B), `query-cache.bin` (`4,535` B), `metadata.rmeta` (`2,454` B), `work-products.bin` (`184` B), `<cgu>.o` (`4,464` B) |
| Suite 2: `commandline_hash_mismatch_rejected` | 1 | `[incremental] completely ignoring cache because of differing commandline arguments` + `-Zassert-incr-state=loaded` failure |
| Suite 2: `ensure_ok_skips_typeck_root_disk_load` | 1 | ``error: `typeck_root(caller_reused)` should have been loaded from disk but it was not`` |
| Suite 2: `positive_control_optimized_mir_loaded_from_disk` | 0 | `#[rustc_clean(cfg = "rev2", loaded_from_disk = "optimized_mir")]` passes when dirty caller triggers `QueryMode::Get` |
| Suite 2: `dep_graph_paths_without_incr_silently_skipped` | 0 | Zero diagnostics emitted despite `#[rustc_if_this_changed]` + `#[rustc_then_this_would_need]` + `-Zquery-dep-graph` |
| Suite 2: `dep_graph_paths_with_incr` | 1 | `error: OK` on `calls_src` + ``error: no path from `body_only_src` to `typeck_root` `` on `independent_fn` |
| Suite 3: `default_const_cycle_e0391` | 1 | `error[E0391]: cycle detected when simplifying constant for the type system A` |
| Suite 3: `type_alias_cycle_e0391` | 1 | `error[E0391]: cycle detected when expanding type alias AliasA` |
| Suite 3: `variances_of_delayed_to_e0072` | 1 | `error[E0072]: recursive type Rec has infinite size` (no `E0391`) |
| Suite 3: `variances_of_delayed_to_e0072_incremental` | 1 | Identical `E0072` under `-C incremental`; `failed_session_dep_graph_persisted: false` |
| Suite 3: `mutual_adt_cycle_e0072_span_rotation` | 1 | `error[E0072]: recursive types Second and First have infinite size` (ordered by lowest span) |
| Suite 3: `layout_of_async_fn_cycle_e0733` | 1 | `error[E0733]: recursion in an async fn requires boxing` (`ping` -> `pong`) |
| Suite 3: `depth_limit_4_layout_of_doubles_to_8` | 1 | `error: queries overflow the depth limit!` suggesting `#![recursion_limit = "8"]` (`query depth increased by 4`) |
| Suite 3: `depth_limit_0_const_eval_special_cases_to_2` | 1 | `error: queries overflow the depth limit!` suggesting `#![recursion_limit = "2"]` (`query depth increased by 1 when computing layout of usize`) |

### 3. Kernel-Checked Lean `v4.34.1` Formalization (`support/QueryEngineRedGreenIchAndCycleSoundness.lean`)

Verified on `2026-11-22` with Lean `v4.34.1` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`) using:
```console
lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
  support/QueryEngineRedGreenIchAndCycleSoundness.lean
```
Exit code `0`, zero warnings, zero forbidden tokens (`sorry`, `omega`, `bv_decide`, `native_decide`, `partial`, `Classical`, `deriving Repr`, `_unsafe_rec`), and environment audit confirmed `totalDecls = 302`, `unsafeRecCount = 0`. Exact `#print axioms` output:

| Theorem | Kernel Axioms | Formalized Result |
| :--- | :--- | :--- |
| `ensureOk_green_skip_and_early_cutoff_sound` | `[]` (none) | Red-green early-cutoff value preservation, error-freedom preservation, and `QueryMode::EnsureOk` disk-deserialization skip (`loadedFromDisk = false`) |
| `ich_rotating_32_and_recomputed_green_complete` | `[propext]` | 32-session rotating completeness (`∃ k < 32`), `100%` unconditional verification on non-disk green recomputation, `-Zincremental-verify-ich` full override, and separation from `1.98.0-nightly` static `1/32` |
| `feedable_consistency_and_no_force_cycle_stack_sound` | `[propext]` | `feedable + no_hash` panic, error-free hashed `feedable` biconditional, `no_force` active cycle-stack preservation, 3-tier nesting dispatch, and `∀ L, L < suggestedRecursionLimit L` |
| `search_for_cycle_permutation_complete` | `[propext]` | Completeness of `VecDeque::rotate_left(1)` cyclic permutation search |
| `ce1_static_dep_path_exists_despite_dynamic_fn_sig_cutoff` | `[propext]` | Static reachability (`OK`) coexisting with dynamic `fn_sig` early cutoff and `EnsureOk` disk-load bypass |
| `ce2_forcing_inside_cycle_truncates_active_cycle_frames_without_no_force` | `[]` (none) | Omitting `no_force` drops caller frame from active cycle stack during out-of-band forcing |
| `ce3_untracked_provider_nondeterminism_caught_by_ich_verify` | `[propext]` | Untracked nondeterminism breaks green soundness, caught immediately on non-disk recomputation and within `k < 32` sessions on rotating disk verification |

## Revalidation

To check whether these findings still hold on a newer `rustc` nightly or `rust-lang/rust` commit without repeating the full audit:

1. **Re-run Live Empirical Suites 2 & 3 against any Nightly `rustc` (~5 seconds):**
   ```console
   python3 support/probe_query_engine_dep_graph_ich_and_cycles.py
   ```
   Verify:
   - `session1_rev1.rc == 0`, `session2_rev2_early_cutoff.rc == 0`, `session3_rev3_noop_verify_ich.rc == 0`;
   - `ensure_ok_skips_typeck_root_disk_load.rc == 1` with `` `typeck_root(caller_reused)` should have been loaded from disk but it was not ``, while `positive_control_optimized_mir_loaded_from_disk.rc == 0`;
   - `dep_graph_paths_without_incr_silently_skipped.rc == 0` while `dep_graph_paths_with_incr.rc == 1` with both `error: OK` and `error: no path`;
   - Suite 3 reproduces `E0391` (const & type alias), `E0072` (single, mutual, and incremental), `E0733` (recursive `async fn`), `recursion_limit = "8"`, `recursion_limit = "2"`, and `failed_session_dep_graph_persisted == false`.
2. **Re-run Suite 1 Modifier Census against a Target `rust-lang/rust` Checkout (~0.2 seconds):**
   ```console
   python3 support/probe_query_engine_dep_graph_ich_and_cycles.py \
     --queries-rs /path/to/rust/compiler/rustc_middle/src/queries.rs \
     --queries-rs-rev "$(git -C /path/to/rust rev-parse HEAD)"
   ```
   Check whether the five structural invariants still hold (`eval_always_and_cache_on_disk == []`, `feedable_and_no_hash == ["crate_for_resolver"]`, `no_force_all ⊆ handle_cycle_error_all`, `depth_limit_all == ["eval_to_const_value_raw", "layout_of"]`, and `mir_drops_elaborated_and_const_checked ∈ no_hash_all`).
3. **Narrow Source Diff Checks on Four Load-Bearing Functions:**
   Diff the following narrow regions between `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` and the target commit:
   - `compiler/rustc_query_impl/src/incremental.rs` (`should_verify_loaded_value`, `promote_from_disk_inner`) — check whether the `32` modulus or rotating policy changed.
   - `compiler/rustc_query_impl/src/execution.rs` (`handle_cycle`, `check_feedable_consistency`, `depth_limit_error`, `load_from_disk_or_invoke_provider_green`, `ensure_can_skip_execution`) — check `EnsureOk`, `verify = true` on `None`, and nesting limits.
   - `compiler/rustc_incremental/src/assert_dep_graph.rs` (`check_paths`) — check whether missing `-C incremental` still silently returns on `retained_dep_graph == None`.
   - `joshlf/anneal`'s `trusted/rustc-capture/src/driver.rs` (`after_analysis`, `COMPILER_VERSION`) — check whether Anneal upgraded its pinned `rustc` past `14210df0e` (inheriting rotating `1/32` ICH) or began extracting MIR inside `after_analysis` (where `has_errors_or_delayed_bugs().is_none()` and non-incremental enforcement become mandatory).
4. **Re-verify the Lean `v4.34.1` Mechanization (~1 second):**
   ```console
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/QueryEngineRedGreenIchAndCycleSoundness.lean
   ```
   Confirm exit code `0`, zero warnings, and that `#print axioms` prints only `[]` or `[propext]` for all seven audited theorems.
