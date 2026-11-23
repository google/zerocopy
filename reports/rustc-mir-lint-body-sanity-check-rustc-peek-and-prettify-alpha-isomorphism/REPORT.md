# rustc_mir_transform lint_body (-Zlint-mir) vs. Validator (-Zvalidate-mir), SanityCheck (rustc_peek), and Prettify (ReorderBasicBlocks / ReorderLocals) Alpha-Isomorphism

## Summary

In `rustc_mir_transform`, MIR checking, dataflow testing, and human-readability canonicalization are split across four structurally distinct mechanisms whose command-line surfaces, soundness guarantees, and failure modes diverge sharply from their module names and from one another:

1. **Disjoint invariant partition between `-Zlint-mir` (`lint::lint_body`, `lint.rs`) and `-Zvalidate-mir` (`validate::Validator`, `validate.rs`), neither of which matches Miri or Anneal's `Trusted.MirSemantics.lean` on stack-storage transitions:**
   - `lint_body` (`compiler/rustc_mir_transform/src/lint.rs`) is **not** a `MirPass` or `MirLint` trait object and is absent from `PASS_NAMES`; `-Zmir-enable-passes=+Lint` emits `UnknownPassName` (`warning: MIR pass 'Lint' is unknown and will be ignored`). Instead, `pass_manager::run_passes_inner` invokes `lint_body` unconditionally after every pass and phase change whenever `-Zlint-mir` is active.
   - `Validator` (`validate.rs`, `PassPolicy::optional(true)`) enforces CFG structure, cleanup-block dominance/acyclic parenting, unwind action compatibility (`UnwindAction::{Cleanup, Continue, Terminate}`), phase-gated MIR elements (`Yield`, analysis `Coverage`, async `Drop`), `SwitchInt` target uniqueness, type checking, debuginfo checking, and absence of free regions in `MirPhase::Runtime`. By default it runs only on phase transition to `MirPhase::Runtime(RuntimePhase::Optimized)`; `-Zvalidate-mir` expands it to every pass and phase boundary (except `Analysis(PostCleanup)` at HEAD `5debe6a1244452beced762385f88a51857a915fc` before opaque revelation).
   - `lint_body` checks five properties ignored by both default `rustc` and `-Zvalidate-mir`: (i) `MaybeStorageDead` local use (`use of local _N, which has no storage here`), (ii) syntactic local-granular non-overlapping assignment (`places_conflict_for_assignment`: `dest == src || (dest.local == src.local && !dest.is_indirect() && !src.is_indirect())` on `Use`, `CopyForDeref`, `Repeat`, `Aggregate`, `Cast`, `WrapUnsafeBinder`), (iii) `MaybeStorageLive` before `StorageLive` (`StorageLive(_N) which already has storage here`), (iv) `MaybeStorageLive \ always_live_locals` at `Return` in function-like bodies, and (v) exact `PlaceRef` uniqueness across `Call` destination and `Operand::Move` arguments. Every failure emits `span_delayed_bug` (`rc = 101` at session exit).
   - Empirically across a 14-case `custom_mir!` differential suite on `rustc 1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`), 10 storage/alias defects (`overlap_assign`, `overlap_array_assign`, `overlap_disjoint_tuple_fields`, `use_after_storage_dead`, `double_storage_live_then_write`, `double_storage_live_clobber`, `return_with_live_local`, `call_duplicate_move_arg`, `call_dest_same_field`, and `unreachable_storage_poison`) pass both default compilation and `-Zvalidate-mir` (`rc = 0`) and fail only when `-Zlint-mir` is active (`rc = 101`), 3 permitted patterns (`overlap_binop_same_local`, `double_storage_dead`, `call_dest_field_distinct`) pass all four modes (`rc = 0`), and `validator_bad_unwind_action` (`extern "C"` `Call` with `UnwindContinue`) fails `Validator` (`rc = 101`, `validate.rs:262`) cleanly and independently of `lint_body`. Conversely, `always_storage_live_locals` scans **all** basic blocks including unreachable blocks, so dead code containing `StorageLive`/`StorageDead` poisons start-block liveness for reachable uses (`unreachable_storage_poison`). Neither `Validator` nor `-Zlint-mir` rejects duplicate `StorageDead(_1)`.

2. **Reconciliation with Miri and `joshlf/anneal`'s `Trusted.MirSemantics.lean` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`):**
   - `Trusted.MirSemantics.lean` does not accept `lint_body`-rejected UB silently: `initLocalsLoop`, `evalOperandToSlot`, `writePlace`, and `evalStatement` initialize annotated non-argument locals to `.dead` and fault (`.error .undefined`) on reads or writes of `.dead` locals (`use_after_storage_dead`, `unreachable_storage_poison`). At `Operand.move`, `Trusted.MirSemantics` conservatively sets moved non-ZST locals to `liveUninitSlot` (`deinitMovedPlace = true` alignment).
   - Where `lint_body` diverges from both Miri (`0.1.0`) and `Trusted.MirSemantics.lean` is in **monolithic syntactic rejections vs. two-stage evaluation and overwriting `StorageLive`**: `Trusted.MirSemantics` evaluates RHS before writing LHS (matching Miri `rc = 0` on scalar `u32` `a = Move(a)` and disjoint tuple `t.0 = Move(t.1)`), whereas Miri fails (`rc = 1`) on multi-byte `[u32; 8]` `a = Move(a)` via `copy_nonoverlapping`. Both Miri and `Trusted.MirSemantics` reallocate an already-live local to `Uninit` on a second `StorageLive`, causing delayed uninitialized-read UB when clobbered without a subsequent write (`double_storage_live_clobber`, Miri `rc = 1`) while succeeding if overwritten before use (`double_storage_live_then_write`, Miri `rc = 0`). Crucially, because `-Zvalidate-mir` does **not** invoke `lint_body`, MIR consumers cannot rely on `Validator` alone to rule out storage-liveness or assignment-aliasing bugs.

3. **`SanityCheck` (`sanity_check.rs`, `rustc_peek.rs`) is an enabled-by-default dataflow assertion oracle whose `MirLint` read-only contract leaks `rustc_peek` into a codegen ICE unless halted by `stop_after_dataflow`:**
   - Registered as `&Lint(sanity_check::SanityCheck)` inside `mir_built` (`lib.rs:428` at `5debe6a1244452beced762385f88a51857a915fc`; `lib.rs:413` at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`) right after `SimplifyCfg::Initial`, `SanityCheck` runs `MaybeInitializedPlaces`, `MaybeUninitializedPlaces`, or `MaybeLiveLocals` for items annotated with `#[rustc_mir(rustc_peek_*)]`, emitting `rustc_peek: bit not set` on `0` bits and halting compilation with fatal `stop_after_dataflow ended compilation` when `stop_after_dataflow` is present.
   - Because `SanityCheck` is a read-only `MirLint` and `LowerIntrinsics` does not lower `rustc_peek`, omitting `stop_after_dataflow` OR passing `-Zmir-enable-passes=-SanityCheck` on well-typed calls (`peek_init_without_stop`, `peek_maybe_uninit_with_sanity_check_disabled_codegen_ice`) lets `rustc_peek` survive into `rustc_codegen_ssa`, crashing with `internal compiler error: .../compiler/rustc_codegen_ssa/src/mir/block.rs:1041:37: intrinsic rustc_peek must be overridden by codegen backend, but isn't` (`rc = 101`).

4. **`Prettify` (`ReorderBasicBlocks` and `ReorderLocals`, `prettify.rs`) is an alpha-isomorphism under CFGs without dead basic blocks, but `ReorderBasicBlocks` panics out-of-bounds if unreachable blocks survive (`-Zmir-opt-level=0`):**
   - `ReorderBasicBlocks` and `ReorderLocals` are `PassPolicy::optional(false)` passes declared under `mod prettify : ReorderBasicBlocks, ReorderLocals;` (`PASS_NAMES` rejects `+Prettify` as `UnknownPassName`), scheduled once at the tail of `run_optimization_passes`.
   - `ReorderBasicBlocks` permutes `body.basic_blocks` by reverse postorder (preserving `START_BLOCK = bb0`); `ReorderLocals` fixes `0..=body.arg_count` (`RETURN_PLACE` and arguments) and orders remaining locals by first `context.is_use()` appearance (ignoring standalone `StorageLive`/`StorageDead`, swapping e.g. `_5 <-> _6` and `_9 <-> _10` in multi-branch MIR loops). Compiled with `-O` (`multi_branch_cfg`), `-Zmir-enable-passes=+ReorderBasicBlocks,+ReorderLocals` leaves runtime behavior identical (`PRETTIFY=112`), produces LLVM IR differing only by alpha-renaming of `bbN` block labels, and yields byte-for-byte identical `--crate-type lib --emit=obj` output.
   - However, because `body.basic_blocks.reverse_postorder()` traverses only blocks reachable from `bb0` while `rpo.invert_bijective_mapping()` constructs an `IndexVec` of length `rpo.len()`, any surviving unreachable block causes `rpo.len() < body.basic_blocks.len()`. If a reachable block has index `>= rpo.len()`, `BasicBlockUpdater` panics out-of-bounds: empirically reproduced at `-Zmir-opt-level=0 -Zmir-enable-passes=+ReorderBasicBlocks,+ReorderLocals` with `index out of bounds: the len is 3 but the index is 3` (`rc = 101`).

5. **Pure kernel-checked Lean `v4.34.1` mechanization (`support/MirLintSanityCheckAndPrettifySoundness.lean`, `3,902` LOC, `970` constants):**
   - Mechanizes all four components in pure constructive Lean `v4.34.1` (`[propext]` only, `0` `sorry`, `0` `Classical.choice`, `0` `Quot.sound`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial`, `0` `._unsafe_rec`), proving concrete separation theorems between `Validator` and `lint_body`, universal dataflow soundness (`lint_dataflow_soundness_universal`, `lint_sound_return_dead`), full operational bisimulations (`reorderBlocks_run_equiv`, `reorderLocals_run_equiv`, `prettify_composition_equiv`) alongside the finite `deadBbUnsorted2Body` partial-RPO counterexample (`reorderBlocks_partial_rpo_fails_bijection`), and necessary-and-sufficient backend `rustc_peek` ICE prevention (`sanity_check_stop_prevents_ice_iff`).

## Applicability

This report characterizes the interaction of `rustc_mir_transform` pass management, MIR validation, MIR linting, `rustc_peek` sanity checking, MIR pretty-printing, Miri execution, and `joshlf/anneal` MIR semantics across five pinned subjects:

1. **Upstream `rust-lang/rust` HEAD (`5debe6a1244452beced762385f88a51857a915fc`):** Primary source inspection of `compiler/rustc_mir_transform/src/{lint.rs, sanity_check.rs, prettify.rs, pass_manager.rs, lib.rs, validate.rs, diagnostics.rs}` and `compiler/rustc_mir_dataflow/src/{rustc_peek.rs, impls/storage_liveness.rs}`, plus recursive subtree inventory of `compiler/rustc_mir_transform/src/**` (`97` `.rs` files recursively: `78` directly in `src/`, `4` in `src/coroutine/`, `10` in `src/coverage/`, `2` in `src/coverage/counters/`, `1` in `src/coverage/counters/node_flow/`, `1` in `src/inline/`, `1` in `src/shim/`; `94` files excluding `src/coverage/counters/**`). At `5debe6a1244452beced762385f88a51857a915fc`, `PASS_NAMES` declares **80** pass names (`PassPolicy::Required` vs. `PassPolicy::Optional { enabled_by_default }`, `PassCtx::for_body`), and `run_passes_inner` skips phase-transition validation on `MirPhase::Analysis(AnalysisPhase::PostCleanup)`.
2. **Executed local toolchain `rustc 1.98.0-nightly` / `miri 0.1.0` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, LLVM `22.1.6`, `x86_64-unknown-linux-gnu`):** All live compiler runs, `-Zdump-mir`, `--emit=llvm-ir`, `--emit=obj`, Miri executions (`support/probe_mir_lint_sanity_check_and_prettify.py` -> `support/probe_results.json`), and line-level comparisons against `1.98.0-nightly` sources (`pass_manager_198.rs`, `lib_198.rs`, `rustc_peek_198.rs`). On `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `PASS_NAMES` exposes **77** pass names, `MirPass` uses `is_enabled` / `can_be_overridden` / `is_required` / `Optimizations`, `declare_passes!` includes `EnumSizeOpt` and omits `CheckMutRestriction`, `LintAndRemoveUninhabited`, `MoveElimination`, and `TailCopyToMove`, and `Validator::run_pass` still runs on `Analysis(PostCleanup)` phase transition when `-Zvalidate-mir` is set.
3. **Cross-checked `rustc 1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, built `2026-11-11`, audited tree `49d734536222bf28bb6d07d885b3a81d145981da`):** Independent prior execution of the core `-Zlint-mir` / `-Zvalidate-mir` / `SanityCheck` / `Prettify` / `UnknownPassName` behavior confirmed unchanged surface behavior for `overlap_assign`, `use_after_storage_dead`, `double_storage_live`, `validator_bad_unwind_action`, `rustc_peek` (`peek_init_ok`, `peek_uninit_with_sanity_check_enabled`, `peek_uninit_with_sanity_check_disabled_hits_borrowck`), and `-O` `multi_branch_cfg` equivalence; `lib.rs` line offset for `&Lint(sanity_check::SanityCheck)` shifted modestly across revisions (`:413` in `1.98.0-nightly`, `:423` in `49d734536222bf28bb6d07d885b3a81d145981da`, `:428` in `5debe6a1244452beced762385f88a51857a915fc`).
4. **Anneal Trusted Computing Base (`joshlf/anneal` `c131b320eeeb26ef692e5afd5ec8db49ee518613`):** Inspection of `trusted/lean/Trusted/MirSemantics.lean` (`liveUninitSlot`, `initLocalsLoop`, `evalOperandToSlot`, `writePlace`, `evalStatement`) to determine which MIR defects accepted by `Validator` and rejected by `lint_body` trigger faults vs. succeed silently under Anneal's verified semantics.
5. **Formal Mechanization (`leanprover/lean4` `v4.34.1`, `5045d0056413266e57c625dcd7c365b10e377c52`):** All theorems in `support/MirLintSanityCheckAndPrettifySoundness.lean` (`3,902` lines) apply directly to the finite abstract MIR machine, dataflow analyzer, validator model, permutation structures (`BlockPerm`, `LocalPerm`), and `SanityPolicy` transition system defined inside that module, which faithfully capture the control, storage-liveness, overlap, permutation, and intrinsic-leakage mechanisms audited in upstream `rustc`.

Behavior documented for `1.98.0-nightly` and `1.102.0-nightly` vs. `5debe6a12` is explicitly differentiated wherever pass names, traits (`PassPolicy` vs. `is_required`/`can_be_overridden`), or diagnostic struct locations changed (`errors` vs. `diagnostics`, `rustc_hir::attrs` vs. `rustc_attr_ir`). Because all four components rely on internal compiler flags (`-Zlint-mir`, `-Zvalidate-mir`, `-Zmir-enable-passes`, `-Zmir-opt-level`) and `#![feature(custom_mir, rustc_attrs, core_intrinsics)]`, line offsets and `PASS_NAMES` cardinality can drift across compiler nightlies even when the architectural boundary persists.

## Findings

### 1. Pass Registration, `PassPolicy` / `MirLint` Taxonomy, and `-Zmir-enable-passes` Resolution

`Basis: source + execution`

Across both `rustc 1.98.0-nightly` (`14210df0e`) and upstream HEAD (`5debe6a12`), `compiler/rustc_mir_transform/src/lib.rs` defines the canonical set of CLI-overridable MIR pass names via `declare_passes!`, which uses `pass_names!` to populate `static PASS_NAMES: LazyLock<FxIndexSet<&str>>`:

- Lone structs stringify their struct identifier (`mod sanity_check : SanityCheck;` -> `"SanityCheck"`, `mod validate : Validator;` -> `"Validator"`).
- Comma-separated structs inside one module register multiple distinct pass names (`mod prettify : ReorderBasicBlocks, ReorderLocals;` -> `"ReorderBasicBlocks"` and `"ReorderLocals"`).
- Parameterized enum pass groups register hyphen-joined `$pass.name()` strings (`SimplifyCfg { Initial, ... }` -> `"SimplifyCfg-initial"`, `"DeadStoreElimination-initial"`, etc.). Note that module names (`lint`, `prettify`) are **not** registered.

| Component | Primary Source (`5debe6a12` / `14210df0e`) | Trait / Kind | Registered in `PASS_NAMES`? | Default Policy (`5debe6a12` / `14210df0e`) | Invocation Trigger |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `lint_body` | `lint.rs:15-177` | Free function `fn lint_body` | **No** (`+Lint` warns `UnknownPassName`) | Off unless `-Zlint-mir` | `pass_manager.rs:385-387, 410-416` (`:337-339, 358-364` in `1.98.0`) on `-Zlint-mir` after every executed pass & phase change |
| `Validator` | `validate.rs:31-103` | `impl MirPass for Validator` | Yes (`"Validator"`) | `PassPolicy::optional(true)` (`is_required=true`, `can_be_overridden=true`) | Automatic at `MirPhase::Runtime(Optimized)` transition (`pass_manager.rs:409` / `:357`), plus every pass & non-skipped phase under `-Zvalidate-mir` |
| `SanityCheck` | `sanity_check.rs:5-11` | `impl MirLint` inside `Lint(SanityCheck)` | Yes (`"SanityCheck"`) | `Lint<T>::policy` returns `PassPolicy::optional(true)` (`is_required=true`, `can_be_overridden=true`) | Inside `mir_built` post-`SimplifyCfg::Initial` (`lib.rs:428` / `:413` in `1.98.0`) |
| `ReorderBasicBlocks` | `prettify.rs:19-39` | `impl MirPass` | Yes (`"ReorderBasicBlocks"`) | `PassPolicy::optional(false)` at `5debe6a12` (disabled unless requested via `-Zmir-enable-passes`) | Tail of `run_optimization_passes` (`lib.rs:784` / `:767` in `1.98.0`) under `-Zmir-enable-passes=+ReorderBasicBlocks` |
| `ReorderLocals` | `prettify.rs:47-89` | `impl MirPass` | Yes (`"ReorderLocals"`) | `PassPolicy::optional(false)` | Tail of `run_optimization_passes` (`lib.rs:785` / `:768` in `1.98.0`) under `-Zmir-enable-passes=+ReorderLocals` |

Note carefully how `ReorderBasicBlocks` and `ReorderLocals` are disabled by default: at HEAD (`5debe6a12`), `PassPolicy::optional(false)` (`prettify.rs:23, 51`) causes `should_run_pass` (`pass_manager.rs:270-284`) to return `enabled_by_default = false` unless overridden positively via `-Zmir-enable-passes`. Earlier in `1.98.0-nightly`, `pass_manager_198.rs:94-114, 214-240` split default policy across `is_enabled`, `is_required`, and `can_be_overridden`; HEAD unified these into the two-variant `PassPolicy::{Required, Optional { enabled_by_default }}` enum (`pass_manager.rs:88-99`), enforcing via `bug!("required pass cannot be gated by an opt level")` (`WithMinOptLevel::policy`, `pass_manager.rs:227`) that optimization-level wrappers cannot gate `PassPolicy::Required` passes.

In `pass_manager::run_passes_inner` (`5debe6a12:294-326`; `14210df0e:250-282`), `overridden_passes` (`-Zmir-enable-passes`) is diffed against `*crate::PASS_NAMES`. Unknown names trigger `UnknownPassName` warnings and a `ValidPassNames` note enumerating all valid pass names alphabetically (`77` names on `rustc 1.98.0-nightly`, `80` in `5debe6a12` HEAD after adding `CheckMutRestriction`, `LintAndRemoveUninhabited`, `MoveElimination`, and `TailCopyToMove`, renaming `ImpossiblePredicates` -> `ImpossibleClauses`, and removing `EnumSizeOpt` from `declare_passes!`). In `#[cfg(debug_assertions)]` builds, `run_passes_inner` additionally asserts that every pass slice element is present in `PASS_NAMES`, emitting `struct_bug` (`err.emit_bug()` at HEAD `5debe6a12:324`; `err.emit()` at `14210df0e:280`). When `Lint<T>` wraps `T: MirLint<'tcx>`, `is_mir_dump_enabled()` returns `false` (`pass_manager.rs:201-203` / `:151-153`), suppressing `-Zdump-mir` files around `SanityCheck` and other `MirLint`s.

Executing `rustc --crate-type lib --edition 2024 -Zmir-enable-passes=+Lint,+SanityCheck,+Prettify` on `1.98.0-nightly` (`14210df0e`) produces exit code `0` alongside:

```text
warning: MIR pass `Lint` is unknown and will be ignored
warning: MIR pass `Prettify` is unknown and will be ignored
note: valid MIR pass names are: `AbortUnwindingCalls`, ..., `ReorderBasicBlocks`, `ReorderLocals`, ..., `SanityCheck`, ..., `Validator`
```

No warning is emitted for `SanityCheck`, whereas both `Lint` and `Prettify` are ignored by `-Zmir-enable-passes`. Note also one flag interaction inside `run_passes_inner`: when `new_phase == MirPhase::Runtime(RuntimePhase::Optimized)` (`pass_manager.rs:409` / `:357`), `validate` is forced `true` even when `-Zvalidate-mir` is omitted (compare operator precedence in `pass_manager.rs:403-410` at `5debe6a12` vs. `pass_manager_198.rs:355-358`):
- In `5debe6a12`, `(validate_each && validate_mir && !body.should_skip() && (new_phase != Analysis(PostCleanup))) || new_phase == Runtime(Optimized)` calls `validate_body` at `Runtime(Optimized)` even for `should_skip()` bodies (though `Validator::run_pass` short-circuits on `InstanceKind::Intrinsic | Virtual` and `ty::Error`), whereas `lint_body` gates on `lint_mir & !body.should_skip()`.
- In `1.98.0` (`pass_manager_198.rs:355-357`), `&` (non-short-circuiting bitwise AND over `bool`) instead of `&&` is used in `(validate_each & validate_mir & !body.should_skip())`, and `Analysis(PostCleanup)` is **not** excluded from `-Zvalidate-mir`.

---

### 2. The `lint_body` (`-Zlint-mir`) vs. `Validator` (`-Zvalidate-mir`) Invariant Split and Trust Boundary Implications

`Basis: source + execution + derived + Lean proof`

#### 2.1 Primary-Source Split (`lint.rs` vs. `validate.rs`)

`lint::lint_body` (`compiler/rustc_mir_transform/src/lint.rs:15-177`) opens with an explicit warning about precision vs. soundness: *"This pass statically detects code which has undefined behaviour or is likely to be erroneous. It can be used to locate problems in MIR building or optimizations. It assumes that all code can be executed, so it has false positives."* Its implementation comprises two fixpoint bitset dataflow analyses and three syntactic/local checks, traversed over `traversal::reachable(body)`:

1. **Global storage-annotation scan (`always_storage_live_locals`, `storage_liveness.rs:15-26`):** Iterates over `&*body.basic_blocks` — **all** blocks in `body`, not only reachable blocks — removing any local `l` appearing in `StatementKind::StorageLive(l) | StorageDead(l)` from an initially all-`1` `DenseBitSet<Local>`.
2. **`MaybeStorageLive` & `MaybeStorageDead` fixpoints (`storage_liveness.rs:29-113`):**
   - `MaybeStorageLive`: bottom = all `0` (dead); start block = `always_live_locals ∪ body.args_iter()` (note: `_0` `RETURN_PLACE` is always live whenever unmarked, and if marked `StorageLive`/`StorageDead` it is only live on explicit markers unless in `always_live_locals`). Transfer: `StorageLive(l) => gen_(l)`, `StorageDead(l) => kill(l)`. Join = set union (may-analysis: `1` means storage *might* be live on some path).
   - `MaybeStorageDead`: bottom = all `0` (live); start block = `vars_and_temps_iter() \ always_live_locals` (`_0` and args excluded as trivially always live). Transfer: `StorageLive(l) => kill(l)`, `StorageDead(l) => gen_(l)`. Join = set union (may-analysis: `1` means storage *might* be dead on some path).
3. **Five failure predicates emitting `tcx.sess.dcx().span_delayed_bug` (`lint.rs:54-176`):**
   - **`visit_local` (`lint.rs:76-82`):** If `context.is_use()`, seeks `maybe_storage_dead` *after* primary statement/terminator effect (`seek_after_primary_effect(location)`) and fails (`"use of local {local:?}, which has no storage here"`) if `maybe_storage_dead.contains(local)`. Because storage statements only execute their effect *at* the statement, regular assignments/reads at `loc` see the storage state prior to or unchanged at `loc`.
   - **`StatementKind::Assign((dest, rvalue))` (`lint.rs:87-116`):** Sets `forbid_aliasing = true` for `Rvalue::{Use, CopyForDeref, Repeat, Aggregate, Cast, WrapUnsafeBinder}` and `false` for `Rvalue::{ThreadLocalRef, UnaryOp, BinaryOp, Ref, Reborrow, RawPtr, Discriminant}`. When `true`, `VisitPlacesWith` visits every `src: Place<'tcx>` in `rvalue` and fails (`"encountered `{statement:?}` statement with overlapping memory"`) if `places_conflict_for_assignment(*dest, src)` holds, where:
     ```rust
     fn places_conflict_for_assignment<'tcx>(dest: Place<'tcx>, src: Place<'tcx>) -> bool {
         dest == src || (dest.local == src.local && !dest.is_indirect() && !src.is_indirect())
     }
     ```
     Notice that any two non-indirect projections on the same `dest.local == src.local` — even provably disjoint tuple/struct fields such as `t.0 = Move(t.1)` — trigger `places_conflict_for_assignment`!
   - **`StatementKind::StorageLive(local)` (`lint.rs:118-126`):** Seeks `maybe_storage_live` *before* primary effect (`seek_before_primary_effect(location)`) and fails (`"StorageLive({local:?}) which already has storage here"`) if `maybe_storage_live.contains(*local)`.
   - **`TerminatorKind::Return` (`lint.rs:135-149`):** If `self.is_fn_like`, seeks `maybe_storage_live` *after* primary effect and fails for any `local` in `maybe_storage_live` where `!self.always_live_locals.contains(local)` (`"local {local:?} still has storage when returning from function"`).
   - **`TerminatorKind::Call { args, destination, .. }` (`lint.rs:150-171`):** Inserts `destination.as_ref()` into `FxHashSet<PlaceRef<'tcx>>` and checks `!self.places.insert(place.as_ref())` over each `Operand::Move(place)` in `args`, failing with `"encountered overlapping memory in `Move` arguments to `Call` terminator: ..."`. Notice the **inverse precision bug** relative to `Assign`: `Call` compares **exact `PlaceRef` equality**, so `Call(p.0 = id(Move(p.1)))` passes `-Zlint-mir` while `Call(p = id(Move(p.0)))` has distinct `PlaceRef`s and is not caught by `-Zlint-mir` (`places` hashes `PlaceRef` literally without prefix/projection overlap testing)!
   - Note that **`StatementKind::StorageDead(_)` falls into `_ => {}`** at `lint.rs:127`: double `StorageDead` is never flagged by `lint_body`.

By contrast, `validate::Validator` (`compiler/rustc_mir_transform/src/validate.rs:1-1712`) checks structural, type, unwind, debuginfo, and phase invariants completely orthogonal to stack storage liveness or place-aliasing:
- **`CfgChecker`** (`validate.rs:111-555`): checks `edge` target bounds, cleanup vs. non-cleanup transitions (`src.is_cleanup, bb.is_cleanup, edge_kind`), cleanup unique-parent dominance and cycle freedom (`check_cleanup_control_flow`), `UnwindAction::{Cleanup, Continue, Terminate}` compatibility with `bb.is_cleanup` and `self.can_unwind` (`validate.rs:246-272` — `!self.can_unwind` rejects `UnwindAction::Continue` at line `262`), `SwitchInt` duplicate target integers, phase boundaries (`Yield`, `async drop`, `is_removed_after_analysis()` coverage, `#[rustc_force_inline]`), and under `-Zvalidate-mir && body.phase < Runtime(Initial)`, that `Move` arguments in `Call` are plain locals or box derefs (`validate.rs:436-452`). `StatementKind::{Assign, StorageLive, StorageDead, ...}` all match the empty arm `{}` in `CfgChecker::visit_statement` (`validate.rs:327-334`)!
- **`TypeChecker`** (`validate.rs:561-1686`): validates place projection types, rvalue operand/operator types, copy-on-non-`Copy` types (only when `-Zvalidate-mir` and before `Runtime(Initial)`, `validate.rs:652-662`), intrinsic constraints (`copy_nonoverlapping` pointer types), and ignores `StorageLive(_)`/`StorageDead(_)` (`validate.rs:1587-1588`).
- **`validate_debuginfos`** (`validate.rs:1687+`) and **`has_free_regions`** check (`validate.rs:89-97`).

#### 2.2 Differential 14-Case Matrix (`rustc 1.98.0-nightly`, Miri `0.1.0`, and `Trusted.MirSemantics.lean`)

The bundled probe (`support/probe_mir_lint_sanity_check_and_prettify.py` -> `support/probe_results.json`) compiled all 14 `custom_mir!(dialect = "runtime", phase = "post-cleanup")` cases across four flag profiles (`default`, `-Zvalidate-mir`, `-Zlint-mir`, `-Zvalidate-mir -Zlint-mir`) plus Miri (`miri_bin` with `-Zmiri` sysroot) on the 9 executable binary cases:

| Case (`custom_mir!` Runtime PostCleanup) | Default | `-Zvalidate-mir` | `-Zlint-mir` | Both Flags | Miri `0.1.0` | `Trusted.MirSemantics.lean` (`c131b320e`) | Primary Diagnostic / Mechanism Observed |
| :--- | :---: | :---: | :---: | :---: | :---: | :--- | :--- |
| `overlap_assign` (`a = Move(a)`, `u32`) | `0` | `0` | **`101`** | **`101`** | **`0`** | Returns `42` (evaluates RHS before writing LHS) | `lint.rs:107:34`: `encountered _1 = move _1 statement with overlapping memory` |
| `overlap_array_assign` (`a = Move(a)`, `[u32; 8]`) | `0` | `0` | **`101`** | **`101`** | **`1`** | Multi-byte aggregate copy outside scalar slice; aligns with Miri non-scalar `copy_nonoverlapping` | `lint.rs:107:34` vs. Miri: `Undefined Behavior: copy_nonoverlapping called on overlapping ranges` |
| `overlap_disjoint_tuple_fields` (`t.0 = Move(t.1)`) | `0` | `0` | **`101`** | **`101`** | **`0`** | Succeeds for disjoint fields | `lint.rs:107:34` false positive (`places_conflict_for_assignment` ignores field projections) |
| `overlap_binop_same_local` (`a = a + 1_u32`) | `0` | `0` | **`0`** | **`0`** | **`0`** | Returns `42` | `forbid_aliasing = false` for `Rvalue::BinaryOp` (`lint.rs:97`) |
| `use_after_storage_dead` (`StorageDead(tmp); RET = tmp`) | `0` | `0` | **`101`** | **`101`** | **`1`** | **`.error .undefined`** (`DeadLocal`) | `lint.rs:80:22`: `use of local _1, which has no storage here`; Miri: `accessing a dead local variable` |
| `double_storage_live_then_write` (`StorageLive; StorageLive; tmp=7; RET=tmp`) | `0` | `0` | **`101`** | **`101`** | **`0`** | Returns `7` (`evalStatement .storageLive` resets slot to `liveUninitSlot`, overwritten by `7`) | `lint.rs:121:26`: `StorageLive(_1) which already has storage here` (false positive vs. Miri runtime semantics) |
| `double_storage_live_clobber` (`StorageLive; tmp=99; StorageLive; RET=tmp`) | `0` | `0` | **`101`** | **`101`** | **`1`** | **`.error .undefined`** (reads `.live none` `Uninit` created by second `StorageLive`) | `lint.rs:121:26` vs. Miri: `constructing invalid value of type u32: encountered uninitialized memory` |
| `double_storage_dead` (`StorageDead(tmp); StorageDead(tmp);`) | `0` | `0` | **`0`** | **`0`** | **`0`** | Returns `1` (`setElem?` to `.dead` is idempotent) | `lint.rs:127`: `StorageDead` hits wildcard `_ => {}` |
| `return_with_live_local` (`StorageLive(tmp); RET=tmp; Return`) | `0` | `0` | **`101`** | **`101`** | **`0`** | Returns `7` (frame teardown deallocates locals) | `lint.rs:140:34`: `local _1 still has storage when returning from function` |
| `call_duplicate_move_arg` (`Call(RET = sink(Move(x), Move(x)))`) | `0` | `0` | **`101`** | **`101`** | — | Evaluates call arguments before ABI pass; no duplicate-place check modeled cleanly in library call stub | `lint.rs:163:26`: `encountered overlapping memory in Move arguments to Call terminator` |
| `call_dest_field_distinct` (`Call(p.0 = id(Move(p.1)))`) | `0` | `0` | **`0`** | **`0`** | — | Succeeds cleanly | `lint.rs:155-159`: `PlaceRef` differs (`p.0 != p.1`) |
| `call_dest_same_field` (`Call(p.0 = id(Move(p.0)))`) | `0` | `0` | **`101`** | **`101`** | — | Disallowed by `Call` non-overlap rule if callee mutates destination via `&mut`/return slot | `lint.rs:163:26` (`PlaceRef` equality matches `p.0 == p.0`) |
| `unreachable_storage_poison` (`bb_dead = { StorageLive(tmp); StorageDead(tmp) }`) | `0` | `0` | **`101`** | **`101`** | — | Initializes `_1 := .dead` (`hasStorageAnnotation` scans all blocks) -> faults `.error .undefined` on `bb0[0]` write! | `lint.rs:80:22`: 2 errors (`bb0[0]` and `bb0[1]`); under `-Zvalidate-mir -Zlint-mir`, repeats after phase change & `CheckAlignment`, `CheckNull`, ... |
| `validator_bad_unwind_action` (`extern "C"` + `UnwindContinue()`) | **`101`** | **`101`** | **`101`** | **`101`** | — | ABI unwind check not part of storage liveness | `validate.rs:262:26`: `UnwindAction::Continue in no-unwind function` (at `runtime-optimized` without `-Zvalidate-mir`; at `runtime-post-cleanup` with `-Zvalidate-mir`) |

Three security/verification consequences follow immediately for MIR verification toolchains (including Anneal's MIR extraction and `Trusted.MirSemantics.lean` at `c131b320e`):

1. **Passing `Validator` (`-Zvalidate-mir`) implies ZERO guarantee against dead-local UB or overlapping assignment:** 10 out of 13 non-ABI defects (`use_after_storage_dead`, `overlap_array_assign`, `double_storage_live_clobber`, `unreachable_storage_poison`, etc.) compile cleanly with `rc = 0` under both default `rustc` and `-Zvalidate-mir`. Only `-Zlint-mir` catches them statically.
2. **Unreachable dead blocks containing `StorageLive`/`StorageDead` poison both `-Zlint-mir` AND `Trusted.MirSemantics.lean`:** Because `storage_liveness.rs:15-26` (`always_storage_live_locals`) and `Trusted/MirSemantics.lean:685-692, 773-774` (`hasStorageAnnotation`) both inspect every block syntactically regardless of CFG reachability, an unreachable block containing `StorageLive(tmp); StorageDead(tmp)` forces `tmp` (`_1`) to start `.dead` at function entry. Thus un-simplified `custom_mir!` or optimization artifacts that leave a dead block with storage markers after stripping the dominating `StorageLive` in `bb0` turn reachable assignments into UB (`deadLocal`) under Miri / `Trusted.MirSemantics` and into ICEs (`bb0[0]`, `bb0[1]`) under `-Zlint-mir`, whereas deleting the dead block (`SimplifyCfg`) restores soundness (`sep_unreachable_storage_poison`).
3. **`MirSemantics.lean` vs. `lint.rs` on `double_storage_live_then_write` & scalar `overlap_assign`:** `Trusted/MirSemantics.lean:1376-1390` directly mirrors `rustc_const_eval`'s `storage_live` (`compiler/rustc_const_eval/src/interpret/stack.rs` cited at `MirSemantics.lean:760-767`), transitioning an in-bounds local unconditionally to `liveUninitSlot localTy` (no double-live error unless subsequently read before initialization), and `MirSemantics.lean:1406-1426` evaluates `evalRvalue` strictly before `writePlace` (scalar self-move succeeds, Miri scalar `rc = 0`). Thus `lint_body`'s `double_storage_live` and field-insensitive assignment-aliasing checks are strictly stricter than runtime/Miri UB on scalar locals and clobbered-then-overwritten temporaries, while being unsoundly silent on `DoubleStorageDead` and partially overlapping `Call` projections (`p` vs. `p.0`).

#### 2.3 Mechanized Separation & Dataflow Soundness in Lean `v4.34.1`

`Basis: Lean proof` (`support/MirLintSanityCheckAndPrettifySoundness.lean`)

- **Orthogonality & Concrete Separation (`L1232-L1358`):** `sep_overlap_assign`, `sep_disjoint_fields_overapprox`, `overlap_binop_permitted_everywhere`, `sep_use_after_storage_dead`, `sep_double_storage_live_and_clobber`, `double_storage_dead_permitted_by_lint`, `sep_return_with_live_local`, `sep_call_overlap_and_asymmetry`, `sep_unreachable_storage_poison` (comparing `unreachableStoragePoisonBody` vs. `unreachableStoragePoisonSimplifiedBody`), and `sep_validator_rejects_bad_unwind_while_lint_accepts` (exhibiting `badUnwindBody` where `validateBody = false` and `lintBody = true`). Structurally, `validator_invariant_under_storage_markers` and `validator_invariant_under_self_alias_assign` prove universally that inserting `.storageLive l :: .storageDead l` or `l = .use (.move l)` never flips `validateBlock`.
- **Universal Soundness of `MaybeStorageLive`/`MaybeStorageDead` (`L1360-L2700`):** Defining `LiveSoundAt` ("every operationally `.live` slot has bit `1` in `absLive`") and `DeadSoundAt` ("every operationally `.dead` slot has bit `1` in `absDead`"), we prove base preservation (`liveSoundAt_init`, `deadSoundAt_init`, `stateConsistent_init`), operand/rvalue/write liveness preservation (`evalOperand_preserves_liveness`, `evalRvalue_preserves_liveness`, `writePlace_preserves_liveness`), single-step fixpoint preservation across all statements and CFG edges (`stateConsistent_step`), single-step safety (`step_no_dead_access_or_double_live`), and universal bounded execution safety:
  - `lint_dataflow_soundness_universal`: For **every** closed MIR body (`CfgClosed body`) admitting a checked fixpoint `(ValidStorageFixpoint body liveIn liveOut deadIn deadOut)` and passing `FixpointLintChecked body liveIn deadIn`, **every** `runBody cfg body args fuel` never produces `.ub .deadLocalAccess` and never produces `.ub .doubleStorageLive`.
  - `lint_sound_return_dead`: At every checked `Terminator.ret` of an `isFnLike` body, every local not in `alwaysStorageLiveLocals body` is provably `.dead` (non-live).

---

### 3. `SanityCheck` (`sanity_check.rs`, `rustc_peek.rs`): Rustc's Dataflow Oracle and Intrinsic-Leakage Hazard

`Basis: source + execution + Lean proof`

`compiler/rustc_mir_transform/src/sanity_check.rs:1-11` is an 11-line adapter implementing `crate::MirLint<'tcx> for SanityCheck`, delegating directly to `rustc_mir_dataflow::rustc_peek::sanity_check(tcx, body)`. It is registered **only once** in the MIR compilation pipeline (`lib.rs:428` at `5debe6a12`; `lib.rs:413` at `14210df0e`), wrapped inside `run_passes` for `mir_built` immediately after `&simplify::SimplifyCfg::Initial` — i.e., **before** `mir_promoted`, `PromoteTemps`, borrow checking, drop elaboration, and `LowerIntrinsics`.

Inspecting `compiler/rustc_mir_dataflow/src/rustc_peek.rs:16-251` (`5debe6a12` and `14210df0e` agree line-for-line in algorithm, differing only in import paths `rustc_attr_ir`/`crate::diagnostics` vs. `rustc_hir::attrs`/`crate::errors` and line `167`/`166` intrinsic name matching):

1. `sanity_check` reads `RustcMir(kind)` attributes on `body.source.def_id()` (returning early with `debug!("skipping rustc_peek::SanityCheck ...")` if absent).
2. For each configured dataflow flag (`PeekMaybeInit`, `PeekMaybeUninit`, `PeekLiveness`), it constructs `MoveData` (with `|_| true`), iterates the lattice analysis (`MaybeInitializedPlaces`, `MaybeUninitializedPlaces`, `MaybeLiveLocals`) to fixpoint, and scans every block's terminator for calls to the `rustc_peek` compiler intrinsic (`PeekCall::from_terminator`).
3. Each valid `rustc_peek` call expects an immediately preceding assignment to `call.arg` inside the same basic block (`value_assigned_to_local`), pairing `ByRef` calls with `Rvalue::Ref(_, _, place)` and `ByVal` calls with `Rvalue::Use(Move(place) | Copy(place))` (emitting `PeekMustBePlaceOrRefPlace` / `PeekMustBeNotTemporary` otherwise). Seeking `cursor.seek_before_primary_effect(Location { block: bb, statement_index })`, `analysis.peek_at` checks `state.contains(...)` and emits `PeekBitNotSet` (`error: rustc_peek: bit not set`) if `0`.
4. Finally, if `RustcMirKind::StopAfterDataflow` (`#[rustc_mir(..., stop_after_dataflow)]`) is present, line `42` (identical line in both `5debe6a12` and `14210df0e`) calls `tcx.dcx().emit_fatal(StopAfterDataFlowEndedCompilation)` (`error: stop_after_dataflow ended compilation`).

**Critical interaction with `MirLint` non-mutation and `LowerIntrinsics`:**
Because `SanityCheck` implements `MirLint` (signature `fn run_lint(&self, tcx: TyCtxt<'tcx>, body: &Body<'tcx>)` takes an **immutable** `&Body<'tcx>`), it can **never erase or replace `rustc_peek` call terminators** from the MIR body. Nor does `lower_intrinsics::LowerIntrinsics` lower `sym::rustc_peek` at runtime MIR lowering. Instead, codegen expects intrinsics surviving to `rustc_codegen_ssa` to be lowered by the backend. Our 7 empirical probes on `rustc 1.98.0-nightly` (`14210df0e`) confirm every edge of this state machine:

| Probe Name | Rust Attributes / Body | Flags | Exit Code | Exact Observed Behavior & Failure Phase |
| :--- | :--- | :--- | :---: | :--- |
| `peek_init_ok` | `#[rustc_mir(rustc_peek_maybe_init, stop_after_dataflow)]`, initialized `x: i32`, `rustc_peek(&x)` | `[]` | `1` | Bit is `1` (no `bit not set`); fatal `error: stop_after_dataflow ended compilation` aborts cleanly before borrowck/codegen |
| `peek_init_without_stop` | `#[rustc_mir(rustc_peek_maybe_init)]` **(no `stop_after_dataflow`)**, initialized `x: i32` | `[]` | **`101`** | Bit check passes (`1`), body proceeds through MIR pipeline to codegen and ICEs: `error: internal compiler error: <rustc-src>/compiler/rustc_codegen_ssa/src/mir/block.rs:1041:37: intrinsic rustc_peek must be overridden by codegen backend, but isn't` |
| `peek_uninit_with_sanity_check_enabled` | `#[rustc_mir(rustc_peek_maybe_init, stop_after_dataflow)]`, uninitialized `let x: i32; rustc_peek(&x);` | `[]` | `1` | Emits `error: rustc_peek: bit not set` followed by `error: stop_after_dataflow ended compilation` (`aborting due to 2 previous errors`) |
| `peek_uninit_with_sanity_check_disabled_hits_borrowck` | Same uninitialized body | `["-Zmir-enable-passes=-SanityCheck"]` | `1` | Skips `SanityCheck`; `mir_borrowck` rejects `rustc_peek(&x)` with `error[E0381]: used binding 'x' isn't initialized` (so borrowck happens to mask codegen ICE only because `x` is uninit!) |
| `peek_liveness_dead` | `#[rustc_mir(rustc_peek_liveness, stop_after_dataflow)]`, `x: i32`, `rustc_peek(&x)` | `[]` | `1` | `MaybeLiveLocals` is backward/dead after `&x` temporary; emits `error: rustc_peek: bit not set` + `stop_after_dataflow ended compilation` |
| `peek_maybe_uninit_definitely_init` | `#[rustc_mir(rustc_peek_maybe_uninit, stop_after_dataflow)]`, `x: i32`, `rustc_peek(&x)` | `[]` | `1` | `MaybeUninitializedPlaces` bit is `0` for initialized param `x`; emits `error: rustc_peek: bit not set` + `stop_after_dataflow` |
| `peek_maybe_uninit_with_sanity_check_disabled_codegen_ice` | Same initialized `x: i32` body with `rustc_peek_maybe_uninit` + `stop_after_dataflow` | `["-Zmir-enable-passes=-SanityCheck"]` | **`101`** | Disabling `SanityCheck` disables both the bit check **and** `stop_after_dataflow`! Since `x` is initialized, borrowck passes, `LowerIntrinsics` leaves `rustc_peek` intact, and codegen panics (`rustc_codegen_ssa/src/mir/block.rs:1041:37` ICE) |

In `support/MirLintSanityCheckAndPrettifySoundness.lean` (`L3778-L3900`), `sanity_check_no_erasure`, `sanity_check_stop_prevents_ice_iff`, and `sanity_check_concrete_witnesses` mechanize the exact bi-implication: on any MIR body containing a `rustc_peek` call (`hasPeekInBody body = true`), avoiding `.codegenIntrinsicICE` holds **if and only if** `SanityCheck` is enabled, a `rustc_peek_*` attribute is present, **and** either a peeked dataflow bit is unset or `stop_after_dataflow = true`.

---

### 4. `Prettify` (`ReorderBasicBlocks` & `ReorderLocals`, `prettify.rs`): Alpha-Isomorphism and the Unreachable-Block RPO Panic

`Basis: source + execution + Lean proof`

#### 4.1 Source Algorithm (`prettify.rs:1-151`)

Both passes in `compiler/rustc_mir_transform/src/prettify.rs` return `PassPolicy::optional(false)` (`prettify.rs:23, 51`) and run consecutively at the end of `run_optimization_passes` (`lib.rs:784-785` at `5debe6a12`; `lib.rs:767-768` at `14210df0e`), **outside** the `-O` optimization loop so their CFG/local renumberings cannot perturb earlier pass caches (`lib.rs:783`: `"Cleanup for human readability, off by default."`):

1. **`ReorderBasicBlocks` (`prettify.rs:19-39, 100-113`):**
   - Computes `let rpo: IndexVec<BasicBlock, BasicBlock> = body.basic_blocks.reverse_postorder().iter().copied().collect();`.
   - Early-exits if `rpo.iter().is_sorted()`.
   - Inverts `rpo` (`rpo.invert_bijective_mapping()`), checks `debug_assert_eq!(updater.map[START_BLOCK], START_BLOCK)` (guaranteed when `bb0` is `START_BLOCK` and visited first by reverse postorder), rewrites every terminator successor in the body via `BasicBlockUpdater::visit_terminator` (`terminator.successors_mut(|succ| *succ = self.map[*succ])`), and permutes `body.basic_blocks` in place (`permute(body.basic_blocks.as_mut(), &updater.map)`).
2. **`ReorderLocals` (`prettify.rs:47-89, 115-151`):**
   - Initializes `LocalFinder` with `(0..=body.arg_count)` via `finder.track(local)`, preserving `_0` (`RETURN_PLACE`) and `_1..=_arg_count` in their exact ABI/calling slots.
   - Walks `(bb, bbd)` in `body.basic_blocks.iter_enumerated()` calling `LocalFinder::visit_local`: **only** calls `self.track(l)` when `context.is_use()` (`prettify.rs:132`), explicitly commenting *"Exclude non-uses to keep `StorageLive` from controlling where we put a `Local`, since it might not actually be assigned until much later."*
   - Loops `for local in body.local_decls.indices()` calling `finder.track(local)` so unreferenced locals (debuginfo-only or marker-only locals) still appear in the bijection.
   - Early-exits if `finder.map.iter().is_sorted()`.
   - Builds `LocalUpdater { map: finder.map.invert_bijective_mapping(), tcx }`, checks `debug_assert_eq!(updater.map[local], local)` for `0..=body.arg_count`, calls `updater.visit_body_preserves_cfg(body)` (rewriting `*l = self.map[*l]` everywhere including debug info and `StorageLive`/`StorageDead`), and permutes `body.local_decls`.

#### 4.2 Empirical MIR / LLVM-IR / Object-File Equivalence (`multi_branch_cfg`)

Running `multi_branch_cfg` (`rustc --edition 2024 -O`) on `1.98.0-nightly` (`14210df0e`) with and without `-Zmir-enable-passes=+ReorderBasicBlocks,+ReorderLocals` yields:

- **Pre- vs. post-`ReorderBasicBlocks` MIR (`bb0..bb11`):** Before `ReorderBasicBlocks`, `baseline_runtime_optimized` and `before_reorder_basic_blocks` match byte-for-byte after header normalization (`bb0..bb11`). `ReorderBasicBlocks` preserves `bb0` (`START_BLOCK`) and `bb1`, moves the early-exit block `bb10 -> bb2` (so loop exit follows loop header immediately in RPO), shifts `bb2 -> bb3`, `bb3 -> bb4`, `bb4 -> bb5`, `bb5 -> bb6`, `bb6 -> bb7`, `bb7 -> bb8`, `bb8 -> bb10`, and moves the return block `bb11 -> bb9` ahead of the back-edge tail `bb9 -> bb11`. Every terminator successor updates consistently (e.g., `bb1`'s `switchInt(move _5) -> [0: bb10, otherwise: bb2]` becomes `[0: bb2, otherwise: bb3]`).
- **Pre- vs. post-`ReorderLocals` MIR (`_0.._11`):** Because `_5: bool` had `StorageLive(_5)` before `StorageLive(_6)` in `bb1`, yet `_6 = copy _4` was the **first `is_use()`** ahead of `_5 = Lt(move _6, copy _1)` (and similarly in `bb5`, `StorageLive(_9)` preceded `StorageLive(_10)` while `_10 = copy _4` was the first use ahead of `_9 = Mul(move _10, const 3_i32)`), `ReorderLocals` swaps **`_5 <-> _6`** (`_5: i32, _6: bool`) and swaps **`_9 <-> _10`**, leaving `_0.._4`, `_7`, `_8`, `_11` unchanged (`LocalFinder` comment on `StorageLive` exclusion verified live!). Notice `StorageLive(_6)` now precedes `StorageLive(_5)` in `bb1`, and `_0.._4` remain untouched (`arg_count = 2`).
- **Execution, LLVM IR, and ELF `.o` identity:** Both binaries return `rc = 0`, `stdout = "PRETTIFY=112"`. Raw optimized LLVM IR (`--emit=llvm-ir -O`) differs *solely* in MIR-derived block names (`%bb9.peel42` / `%bb2.us.preheader` / `%bb11` in baseline vs. `%bb11.peel42` / `%bb3.us.preheader` / `%bb9` under Prettify); normalizing `bb\d+` identifiers in first-appearance order (`bbK0..`) yields `llvm_ir_multi_branch_cfg_alpha_identical = true`. Compiling `--crate-type lib --edition 2024 -O --emit=obj` yields `lib_obj_bytes_identical = true` (zero byte difference in emitted ELF object code).

#### 4.3 Critical Crash Precondition — Dead Basic Blocks in `ReorderBasicBlocks`

`Basis: source + execution + Lean proof`

Inspecting `prettify.rs:27-37` (`let rpo = body.basic_blocks.reverse_postorder().iter().copied().collect(); ... invert_bijective_mapping()`) exposes a latent out-of-bounds panic whenever `body` retains unreachable basic blocks before a reachable block with a larger index:
- `reverse_postorder()` performs DFS from `START_BLOCK` (`bb0`) and therefore omits unreachable blocks, producing `rpo.len() = |Reachable(body)| < body.basic_blocks.len()`.
- `IndexVec::invert_bijective_mapping()` allocates a vector of length `rpo.len()`, whose valid indices are `0 .. rpo.len() - 1`.
- Consequently, any reachable terminator targeting a block `bb_k` with `k >= rpo.len()` indexes `self.map[bb_k]` out of bounds inside `BasicBlockUpdater::visit_terminator` (`prettify.rs:111`).

Our empirical reproduction (`dead_bb_unsorted_opt0_prettify` in `probe_results.json`) constructs the 4-block `custom_mir!` body `bb0 -> Goto(bb3)`, dead `bb1 -> 99`, `bb2 -> x`, `bb3 -> Goto(bb2)`. Reachable blocks from `bb0` in RPO are `[bb0, bb3, bb2]` (`rpo.len() = 3 < 4`). Compiling with default optimization (`-O0` default MIR opt level >= 2) runs `SimplifyCfg::Final` (via `WithMinOptLevel(1, ...)`, `lib.rs:771`), removing dead `bb1` and renumbering `bb2, bb3` into `0..3` so Prettify succeeds (`rc = 0`). Compiling with **`-Zmir-opt-level=0 -Zmir-enable-passes=+ReorderBasicBlocks,+ReorderLocals`** bypasses `SimplifyCfg::Final`, leaving `bb1` unreachable and **`bb3` at index `3`**, immediately crashing `rustc` (`rc = 101`):

```text
thread 'rustc' (...) panicked at <rustc-src>/compiler/rustc_index/src/slice.rs:194:20:
index out of bounds: the len is 3 but the index is 3
```

Our Lean `v4.34.1` mechanization (`support/MirLintSanityCheckAndPrettifySoundness.lean`) proves:
- **`reorderBlocks_run_equiv`** (`L2949`) and **`reorderBlocks_step_sim`** (`L2826`): For any `CfgClosed body` and total bijection `σ : BlockPerm body.blocks.length` fixing `0` (`σ.fix_zero`), `runBody cfg (reorderBlocksBody σ body) args fuel = runBody cfg body args fuel` across all evaluation configurations, inputs, and fuel bounds.
- **`reorderLocals_run_equiv`** (`L3716`) and **`reorderLocals_step_sim`** (`L3482`): For any `LocalsInBounds body` with `body.argCount < body.locals.length` and bijection `τ : LocalPerm body.locals.length body.argCount` fixing `0..=body.argCount` (`τ.fix_prefix`), `runBody cfg (reorderLocalsBody τ body) args fuel = runBody cfg body args fuel`, crucially relying on `hasStorageMarker_reorderLocals` (`L3109`) and `initLocals_reorderLocals` (`L3143`) so `always_storage_live_locals` classification is preserved identically at entry.
- **`prettify_composition_equiv`** (`L3748`): Exact sequential bisimulation for `ReorderLocals ∘ ReorderBasicBlocks`, matching `lib.rs:784-785`.
- **`reorderBlocks_partial_rpo_fails_bijection`** (`L3771`): Formalizes the 4-block `deadBbUnsorted2Body` counterexample proving `[0, 3, 2].length ≠ 4` and `listGet [0, 3, 2] 3 = none`, directly witnessing why the `CfgClosed` / full-bijection hypothesis of `reorderBlocks_run_equiv` fails on non-reachable-pruned MIR.

## Boundaries

1. **`Unknown` / not exercised directly on a custom-built `rustc` binary with `debug_assertions` enabled:** The `#[cfg(debug_assertions)]` check in `pass_manager.rs:313-326` (`5debe6a12`) / `:269-282` (`14210df0e`) asserting `used_passes ⊆ PASS_NAMES` was inspected in primary source (including the `err.emit_bug()` vs. `err.emit()` change), not executed on a locally compiled `debug_assertions` `rustc` stage-1 compiler (our executed toolchain `14210df0e` is a release nightly).
2. **`Unsupported` / Miri non-executable library signatures:** Three `Call`-terminator probes (`call_duplicate_move_arg`, `call_dest_field_distinct`, `call_dest_same_field`), `unreachable_storage_poison`, and `validator_bad_unwind_action` target ABI/terminator diagnostics verified across all four `rustc` flag profiles (`--crate-type lib`); `unreachable_storage_poison` in Miri was cross-checked via `Trusted.MirSemantics.lean` and inspection of `stack.rs`, not separately executed inside a `miri` binary driver wrapper (`run_miri = False` in the probe harness). Similarly, `call_duplicate_move_arg`'s aliasing semantics in downstream LLVM `noalias` codegen was not executed through Miri (`call` ABI UB is callee/signature-dependent).
3. **`Known not to apply` across field projections or `DoubleStorageDead` for `-Zlint-mir`:** `-Zlint-mir` is **neither sound nor complete** as a general MIR UB oracle: it falsely rejects disjoint tuple-field moves (`t.0 = Move(t.1)`), scalar self-moves (`a = Move(a)`), dead-block storage markers (`unreachable_storage_poison`), live-at-return locals, and overwritten double `StorageLive`s, while **silently accepting** (`rc = 0`) duplicate `StorageDead`, `BinaryOp` self-writes, `extern "C"` `UnwindContinue` without `Validator`, and `Call` partial-place aliasing such as `Call(p = id(Move(p.0)))` (due to `FxHashSet<PlaceRef>` exact equality in `lint.rs:154-161`).
4. **`Known not to apply` when dead blocks remain in `ReorderBasicBlocks`:** `ReorderBasicBlocks` is only a total permutation (and thus an alpha-isomorphism) when every block in `body.basic_blocks` is reachable from `bb0` (guaranteed after `SimplifyCfg::Final` at `mir-opt-level >= 1`). Under `-Zmir-opt-level=0`, unreachable blocks whose removal is skipped trigger out-of-bounds panics when any reachable target block index `>= |Reachable(body)|` (`dead_bb_unsorted_opt0_prettify`), whereas unsorted reachable blocks with `|Reachable| == len` remain covered.
5. **LLVM `bbN` label normalization scope in `Prettify`:** Although compiled ELF `.o` bytes for `multi_branch_cfg` (`--crate-type lib -O --emit=obj`) are byte-for-byte identical, `--emit=llvm-ir` retains MIR-block-numbered suffix labels (`bb2.us.preheader` vs. `bb3.us.preheader`), so textual LLVM IR equality requires alpha-normalization of compiler-generated basic-block names, and binaries compiled with debuginfo / DWARF line/local indices can reflect renumbered MIR locals in debug metadata (`LocalUpdater` visits debug info via `visit_body_preserves_cfg`).
6. **`Not examined` in this package:** Other `rustc_mir_transform` lints (`known_panics_lint.rs`, `lint_tail_expr_drop_order.rs`, `check_packed_ref.rs`, `check_alignment.rs`, `check_null.rs`, `check_enums.rs`, `check_mut_restriction.rs`) and non-MIR dataflow attributes (`#[rustc_regions]`, NLL UI harnesses) were inspected only to confirm how they register in `lib.rs`; their individual lint predicates belong to their own file analyses.

## Evidence

### Primary Source Anchors

| Subject | Commit SHA | File Path & Symbols / Line Ranges | Role |
| :--- | :--- | :--- | :--- |
| `rust-lang/rust` HEAD | `5debe6a1244452beced762385f88a51857a915fc` | `compiler/rustc_mir_transform/src/lint.rs:15-177` (`lint_body`, `Lint`, `fail` with `span_delayed_bug`, `places_conflict_for_assignment`, `VisitPlacesWith`, `MaybeStorageLive`, `MaybeStorageDead`, `Call` `FxHashSet<PlaceRef>`) | `source` |
| `rust-lang/rust` HEAD | `5debe6a1244452beced762385f88a51857a915fc` | `compiler/rustc_mir_transform/src/sanity_check.rs:5-11` (`SanityCheck` `MirLint` impl) | `source` |
| `rust-lang/rust` HEAD | `5debe6a1244452beced762385f88a51857a915fc` | `compiler/rustc_mir_dataflow/src/rustc_peek.rs:16-251` (`sanity_check`, `sanity_check_via_rustc_peek`, `PeekCall::from_terminator`, `RustcPeekAt`, `StopAfterDataFlowEndedCompilation`) | `source` |
| `rust-lang/rust` HEAD | `5debe6a1244452beced762385f88a51857a915fc` | `compiler/rustc_mir_transform/src/prettify.rs:15-151` (`ReorderBasicBlocks`, `ReorderLocals`, `permute`, `BasicBlockUpdater`, `LocalFinder`, `LocalUpdater`) | `source` |
| `rust-lang/rust` HEAD | `5debe6a1244452beced762385f88a51857a915fc` | `compiler/rustc_mir_transform/src/pass_manager.rs:86-233, 256-420` (`PassPolicy`, `MirPass`, `MirLint`, `Lint<T>`, `WithMinOptLevel`, `should_run_pass`, `run_passes_inner`, `UnknownPassName`, `#[cfg(debug_assertions)]` `emit_bug`) | `source` |
| `rust-lang/rust` HEAD | `5debe6a1244452beced762385f88a51857a915fc` | `compiler/rustc_mir_transform/src/lib.rs:96-214, 428, 784-785` (`declare_passes!`, `PASS_NAMES` = 80 passes, `Lint(SanityCheck)` in `mir_built`, `ReorderBasicBlocks`, `ReorderLocals` in `run_optimization_passes`) | `source` |
| `rust-lang/rust` HEAD | `5debe6a1244452beced762385f88a51857a915fc` | `compiler/rustc_mir_transform/src/validate.rs:31-103, 246-272, 327-452, 651-665, 1587-1687` (`Validator`, `CfgChecker`, `check_unwind_edge`, `TypeChecker`, `validate_debuginfos`) | `source` |
| `rust-lang/rust` HEAD | `5debe6a1244452beced762385f88a51857a915fc` | `compiler/rustc_mir_dataflow/src/impls/storage_liveness.rs:15-113` (`always_storage_live_locals`, `MaybeStorageLive`, `MaybeStorageDead`) | `source` |
| `rust-lang/rust` HEAD | `5debe6a1244452beced762385f88a51857a915fc` | `compiler/rustc_mir_transform/src/diagnostics.rs:77-87` (`UnknownPassName`, `ValidPassNames`) | `source` |
| `rust-lang/rust` HEAD | `5debe6a1244452beced762385f88a51857a915fc` | `compiler/rustc_mir_transform/src/**` directory inventory: `78` (`src`) + `4` (`coroutine`) + `10` (`coverage`) + `2` (`coverage/counters`) + `1` (`coverage/counters/node_flow`) + `1` (`inline`) + `1` (`shim`) = `97` `.rs` files (`94` outside `coverage/counters`) | `source` |
| `rust-lang/rust` `1.98.0-nightly` | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_mir_transform/src/{lib.rs, pass_manager.rs}` (`77` `PASS_NAMES`, `Optimizations::{Suppressed, Allowed}`, `MirPass::{is_enabled, can_be_overridden, is_required}`, `:413` `SanityCheck`, `:767-768` `Prettify`); `rustc_peek.rs:166` | `source` + `execution` |
| `rust-lang/rust` `1.102.0-nightly` | `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` / `49d734536222bf28bb6d07d885b3a81d145981da` | Prior cross-checked observation of `-Zmir-enable-passes`, `SanityCheck` `rustc_peek`, `custom_mir!` lint vs. validator separation, and `multi_branch_cfg` Prettify equivalence | `execution` |
| `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/lean/Trusted/MirSemantics.lean:748-785, 934-960, 1319-1427` (`liveUninitSlot`, `initLocalsLoop`, `evalOperandToSlot` with conservative move deinit, `writePlace`, `evalStatement`) | `source` |

### Preserved Execution Artifacts & Formal Proofs (`support/`)

1. **`support/probe_mir_lint_sanity_check_and_prettify.py`** (`826` lines) and **`support/probe_results.json`** (`82,239` bytes):
   - Executed live on `2026-11-23` against `rustc 1.98.0-nightly (14210df0e 2026-05-31)` / `miri 0.1.0` / LLVM `22.1.6`.
   - Captures:
     - `pass_flag_resolution_probe`: `rc = 0`, `valid_pass_names_count = 77`, confirming `Lint` and `Prettify` warn `UnknownPassName` while `SanityCheck`, `ReorderBasicBlocks`, `ReorderLocals`, and `Validator` resolve cleanly.
     - `lint_body_vs_validator_vs_miri`: full matrix over 14 `custom_mir!` programs x 4 flag profiles + 9 Miri executions.
     - `sanity_check_rustc_peek`: all 7 `#[rustc_mir(rustc_peek_*)]` compiler invocations including `rustc_codegen_ssa` ICEs on leaked `rustc_peek` calls.
     - `prettify_reorder_probe`: `-Zdump-mir=ReorderBasicBlocks|ReorderLocals|runtime-optimized`, `--emit=llvm-ir -O`, `--emit=obj -O`, binary execution (`PRETTIFY=112`), and the `dead_bb_unsorted_opt0_prettify` out-of-bounds RPO ICE (`rc = 101`) vs. default (`rc = 0`).

2. **`support/MirLintSanityCheckAndPrettifySoundness.lean`** (`3,902` lines, `174,864` bytes):
   - Kernel-checked with Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) under `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`, exiting with code `0` and zero warnings/errors.
   - Programmatic environment audit over all **970** constants in the compiled module confirmed:
     - `UNSAFE_REC_COUNT = 0` (`0` `._unsafe_rec` constants)
     - `UNSAFE_OR_PARTIAL_COUNT = 0` (`0` `unsafe` or `partial` definitions)
     - `ALL_AXIOMS_USED = [propext]` (`0` `Classical.choice`, `0` `Quot.sound`, `0` `sorryAx`, `0` `Lean.ofReduceBool`, `0` `Lean.trustCompiler`)
     - Source-token scan confirmed `0` uses of `sorry`, `omega`, `bv_decide`, `native_decide`, `Classical.choice`, `partial def`, or `deriving` (all custom equality helpers written explicitly).
   - Key proved theorems:
     - Separation witnesses & structural validator invariance (`L1232-L1358`): `sep_overlap_assign`, `sep_disjoint_fields_overapprox`, `overlap_binop_permitted_everywhere`, `sep_use_after_storage_dead`, `sep_double_storage_live_and_clobber`, `double_storage_dead_permitted_by_lint`, `sep_return_with_live_local`, `sep_call_overlap_and_asymmetry`, `sep_unreachable_storage_poison`, `sep_validator_rejects_bad_unwind_while_lint_accepts`, `validator_invariant_under_storage_markers`, `validator_invariant_under_self_alias_assign`.
     - Dataflow soundness (`L1360-L2700`): `liveSoundAt_init`, `deadSoundAt_init`, `stateConsistent_init`, `stateConsistent_step`, `step_no_dead_access_or_double_live`, `lint_sound_no_dead_or_double_live_runFrom`, `lint_dataflow_soundness_universal`, `lint_sound_return_dead`.
     - `ReorderBasicBlocks` & `ReorderLocals` bisimulation & dead-block counterexample (`L2726-L3776`): `initLocals_reorderBlocks`, `reorderBlocks_step_sim`, `reorderBlocks_runFrom_equiv`, `reorderBlocks_run_equiv`, `hasStorageMarker_reorderLocals`, `initLocals_reorderLocals`, `evalOperand_reorderLocals`, `evalRvalue_reorderLocals`, `writePlace_reorderLocals`, `reorderLocals_step_sim`, `reorderLocals_runFrom_equiv`, `reorderLocals_run_equiv`, `prettify_composition_equiv`, `reorderBlocks_partial_rpo_fails_bijection`.
     - `SanityCheck` intrinsic leakage characterization (`L3827-L3900`): `sanity_check_no_erasure`, `sanity_check_stop_prevents_ice_iff`, `sanity_check_concrete_witnesses`.

## Revalidation

To revalidate the empirical compiler behavior and Lean `v4.34.1` mechanization on a target toolchain or newer `rust-lang/rust` commit:

1. **Re-run the full differential `rustc` / Miri probe** (requires nightly `rustc` and optional `miri` component):

   ```console
   python3 support/probe_mir_lint_sanity_check_and_prettify.py
   ```

   Inspect the generated `support/probe_results.json` to check:
   - Whether `PASS_NAMES` still rejects `Lint` and `Prettify` while accepting `SanityCheck`, `ReorderBasicBlocks`, `ReorderLocals`, and `Validator`.
   - Whether all 10 `-Zlint-mir` defects still pass default compilation and `-Zvalidate-mir` (`rc = 0`) and fail `-Zlint-mir` (`rc = 101`).
   - Whether `-Zmir-opt-level=0 -Zmir-enable-passes=+ReorderBasicBlocks,+ReorderLocals` still panics at `reverse_postorder()` length mismatch on `dead_bb_unsorted2`.
   - Whether disabling `SanityCheck` on `rustc_peek_maybe_uninit` + `stop_after_dataflow` still ICEs in `rustc_codegen_ssa`.

2. **Quick CLI spot-check for dead-block RPO panic and flag partition** without Python harness setup:

   ```console
   rustc +nightly --crate-type lib --edition 2024 -Zmir-opt-level=0 -Zmir-enable-passes=+ReorderBasicBlocks,+ReorderLocals dead_bb.rs
   rustc +nightly --crate-type lib --edition 2024 -Zvalidate-mir -Zmir-enable-passes=+Lint,+SanityCheck,+Prettify empty.rs
   ```

3. **Kernel-check the Lean `v4.34.1` formalization standalone** (expects Lean `v4.34.1` binary):

   ```console
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/MirLintSanityCheckAndPrettifySoundness.lean
   ```

   Confirm exit code `0`, zero warnings/errors, and that importing the compiled `.olean` with `Lean.collectAxioms` / `Environment.constants` yields `ALL_AXIOMS_USED=[propext]`, `UNSAFE_REC_COUNT=0`, and `UNSAFE_OR_PARTIAL_COUNT=0`.

4. **Check primary-source drift** before trusting line numbers or pass policies on newer `rust-lang/rust` revisions:

   - Diff `compiler/rustc_mir_transform/src/{lint.rs, sanity_check.rs, prettify.rs, pass_manager.rs, lib.rs, validate.rs}` and `compiler/rustc_mir_dataflow/src/{rustc_peek.rs, impls/storage_liveness.rs}` against `5debe6a1244452beced762385f88a51857a915fc` — checking specifically whether `lint_body` has been promoted into `Validator` or `SanityCheck`, whether `LowerIntrinsics` gained `sym::rustc_peek` lowering, and whether `ReorderBasicBlocks::run_pass` fixed `rpo.len() < body.basic_blocks.len()` handling for unreachable blocks.
