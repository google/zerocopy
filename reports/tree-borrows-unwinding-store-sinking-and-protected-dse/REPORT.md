# Tree Borrows Unwind-Landing-Pad Store Sinking (`SinkStoreToCleanupCert`), Loop `&mut` Promotion, and Frame-Local Catch Unobservability

## Summary

Under `rustc 1.99.1`'s default `-C panic=unwind` profile, almost every non-inlined
function call, slice indexing operation, or formatting call in `Runtime(PostCleanup)`
MIR carries an `UnwindAction::Cleanup(bb_cleanup)` or `UnwindAction::Continue`
edge (`can_unwind == true`). Because Tree Borrows releases a callee's
function-entry `ProtectorKind::StrongProtector` cleanly on both normal `Return`
and exceptional `UnwindResume` (`src/tools/miri/src/borrow_tracker/mod.rs:362-400`),
a caller `Drop` implementation or `std::panic::catch_unwind` handler can legally
read `*x` after `f(x: &mut T)` unwinds—blocking naive dead-store elimination
(`dseProtectedMutAcrossNoUnwindCall_refines`) across `may_unwind` calls. Combining
a zero-axiom Lean `v4.34.1` mechanization
([`support/TreeBorrowsUnwindStoreSinkingAndDseProbe.lean`](support/TreeBorrowsUnwindStoreSinkingAndDseProbe.lean))
and an executable `rustc 1.99.1` (`LLVM 23.1.1`) benchmark and `catch_unwind`
verification suite
([`support/unwind_store_sinking_metrics.json`](support/unwind_store_sinking_metrics.json))
establishes three proof-producing `MiniSSA` optimizations that achieve `-C
panic=abort` hot-path store-elimination parity while preserving exact `-C
panic=unwind` semantics:

1. **Hot-Path Store Elimination via Cold `cleanup`-Pad Store Sinking
   (`SinkStoreToCleanupCert`, `sinkProtectedStoreToCleanup_bisimExact`):**
   - For a function-entry protected parameter `x: &mut T` (`StrongProtector`) in
     `*x = v1; may_unwind_call(); *x = v2`, sinking `*x = v1` off the hot normal
     path onto the entry of a cold landing-pad block `bb_cleanup_sink` (executed
     *before* any frame-local destructors in `bb_cleanup` and *before*
     `UnwindResume` releases the protector) is an exact bidirectional refinement
     (`BisimExact`, mechanized in `sinkProtectedStoreToCleanup_bisimExact`,
     [`support/TreeBorrowsUnwindStoreSinkingAndDseProbe.lean:139-148`](support/TreeBorrowsUnwindStoreSinkingAndDseProbe.lean#L139-L148)).
   - On the hot normal path, the redundant store `*x = v1` is completely
     eliminated (`hot_referent_stores` drops by **`50%`**: `2 -> 1` in `W01` and
     `6 -> 3` in `W03`, yielding an **`18.4%` (`1.184x`)** speedup on multi-field
     cursor updates), matching `-C panic=abort` instruction-for-instruction on the
     non-panicking path.
2. **Loop-Carried `&mut T` Register Promotion Across `may_unwind` Calls
   (`PromoteProtectedMutInLoopCert`, `promoteProtectedMutAcrossMayUnwindLoop_sound`):**
   - When a loop accumulates into `*acc: &mut T` across a `may_unwind` call,
     `MiniSSA` promotes `*acc` into a pure SSA loop-header $\phi$-register
     `phi_acc` for the entire duration of the loop, emitting a single
     `*acc = phi_acc` store at the normal loop exit and a single
     `*acc = phi_acc` compensation store on the loop's shared `bb_cleanup_sink`
     landing pad (`promoteProtectedMutAcrossMayUnwindLoop_sound`,
     [`support/TreeBorrowsUnwindStoreSinkingAndDseProbe.lean:183-196`](support/TreeBorrowsUnwindStoreSinkingAndDseProbe.lean#L183-L196)).
   - On `W02` (`200,000` loop iterations across `may_unwind_step`), this reduces
     dynamic referent memory stores from `400,000` to **`1`** on the normal path
     and reduces execution latency by **`25.0%` (`1.333x` speedup, `235.43 us ->
     176.57 us`)**.
3. **Four Sufficient Conditions for Uncompensated Unwind DSE
   (`DeleteStoreAcrossUnwindCert`, Zero Cold-Pad Store Needed):**
   - `MiniSSA` deletes `*x = v1` on **both** the normal path and the unwind path
     (requiring zero cold-pad compensation store) whenever any of four
     certifiable conditions holds:
     1. **`COND-ABORT`:** The call edge has `UnwindAction::Terminate` or the
        profile is `-C panic=abort`.
     2. **`COND-SRET`:** `x` is the indirect return slot `_0` (`sret`, marked
        `dead_on_unwind` in `compiler/rustc_codegen_llvm/src/abi.rs:495-512`).
     3. **`COND-LOCAL-DROP-OVERWRITE` (`dseAcrossUnwind_withLocalDropOverwrite_refines`):**
        A local scope guard in `bb_cleanup` unconditionally overwrites
        `*x = v_recover` without reading `*x` before `UnwindResume`
        ([`support/TreeBorrowsUnwindStoreSinkingAndDseProbe.lean:221-228`](support/TreeBorrowsUnwindStoreSinkingAndDseProbe.lean#L221-L228);
        delivers a **`1.431x` (`43.1%`)** speedup on `W04`, `589.60 us ->
        411.95 us`).
     4. **`COND-INLINED-CALLER-DEAD-ON-UNWIND` (`dseAcrossUnwind_callerDeadOnUnwind_refines`):**
        Every caller of an internal function `f(x: &mut T)` passes `&mut
        caller_local` where `needs_drop::<T>() == false` and no `catch_unwind`
        intervenes before `StorageDead(caller_local)` on the caller's unwind path
        ([`support/TreeBorrowsUnwindStoreSinkingAndDseProbe.lean:251-258`](support/TreeBorrowsUnwindStoreSinkingAndDseProbe.lean#L251-L258)).

## Applicability

This report applies to `rustc 1.99.1`
(`58cf8f9c35b355199727627d07ae34a4e2846d67`), its bundled `LLVM 23.1.1` backend
(`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`), and `Lean 4 v4.34.1`
(`5045d0056413266e57c625dcd7c365b10e377c52`) when optimizing Tree-Borrows-protected
`&mut T` stores and loop accumulators in `MiniSSA` under `-C panic=unwind`.

It extends two corpus reports:
- `tree-borrows-protectors-stack-coloring-and-dead-store-elimination`
- `tree-borrows-unwinding-cleanup-pads-two-phase-borrows-and-unsafecell`

Created: 2026-11-14 · Updated: 2026-11-14

## Findings

### 1. CFG Rewrite and Tree Borrows Soundness for `SinkStoreToCleanupCert`

Basis: source + derived + execution

Given a `Runtime(PostCleanup)` MIR or `MiniSSA` basic block `bb0` where `x: &mut T`
(`T: Unpin`) carries a function-entry `StrongProtector`:

```text
// Source CFG:
bb0:
  *x = v1;
  _ret = call may_unwind(args...) -> [return: bb1, unwind: bb_cleanup];
bb1:
  *x = v2;
```

`MiniSSA` rewrites the CFG by splitting the unwind edge through a dedicated
compensation block `bb_cleanup_sink`:

```text
// Target CFG (SinkStoreToCleanupCert):
bb0:
  _ret = call may_unwind(args...) -> [return: bb1, unwind: bb_cleanup_sink];
bb1:
  *x = v2;
bb_cleanup_sink (cleanup):
  *x = v1;
  goto -> bb_cleanup;
```

Why is this rewrite a bidirectional refinement (`BisimExact`) under Tree Borrows
(`src/tools/miri/src/borrow_tracker/tree_borrows/{perms.rs:172-176, tree.rs:157-159}`)?
1. **During `may_unwind(args...)`:** In the source program, `*x = v1` transitions
   `x`'s permission on all bytes of `T` to `Unique` with `accessed = true` under
   an active `StrongProtector`. If `may_unwind` attempts any foreign read or
   foreign write to `*x`, `perform_access` transitions `Unique` (`is_protected =
   true`) to `Disabled` and triggers immediate `ProtectedDisabled` UB (`ExecResult.ub`).
   Because `x` is not passed to `may_unwind` (no child access occurs inside
   `may_unwind`), any execution of `may_unwind` that does not trigger source UB
   performs **zero** accesses (`OpaqueCallForeignAccess.none`) to `*x`.
2. **On Normal Return (`CallExit.normalReturn`):** Control enters `bb1` and
   executes `*x = v2`, producing the identical `Unique` (`accessed = true`)
   permission and final memory value `v2` in both programs.
3. **On Unwind (`CallExit.unwindCleanup`):** Control enters `bb_cleanup_sink`
   *while `x`'s `StrongProtector` is still active* (`on_stack_pop` only runs at
   `TerminatorKind::UnwindResume`) and *before any local destructor in
   `bb_cleanup` executes*. Writing `*x = v1` at the entry of `bb_cleanup_sink`
   establishes `Unique` (`accessed = true`) and memory value `*x == v1` prior to
   both `runCleanupDrop` and `UnwindResume`.

All five theorems in
[`support/TreeBorrowsUnwindStoreSinkingAndDseProbe.lean`](support/TreeBorrowsUnwindStoreSinkingAndDseProbe.lean)
are kernel-checked in Lean `v4.34.1` with zero `sorryAx` and zero
`Lean.ofReduceBool`:

| Theorem Name | Lines | Mechanized Property |
| :--- | :---: | :--- |
| `sinkProtectedStoreToCleanup_bisimExact` | `139-148` | Sinking `*x = v1` to the entry of `bb_cleanup_sink` before local cleanup drops and `UnwindResume` is `BisimExact` across all foreign-access, exit, and local-drop cases. |
| `promoteProtectedMutAcrossMayUnwindLoop_sound` | `183-196` | Promoting a loop-carried `*acc: &mut u64` into an SSA $\phi$-register `phiAcc` with normal-exit + `cleanup`-pad writeback matches the per-iteration memory-store loop at every iteration. |
| `dseAcrossUnwind_withLocalDropOverwrite_refines` | `221-228` | Under `COND-LOCAL-DROP-OVERWRITE` (`eff = .overwriteX vRecover`), deleting `*x = v1` with zero cold-pad store is `BisimExact`. |
| `dseAcrossUnwind_callerDeadOnUnwind_refines` | `251-258` | Under `COND-INLINED-CALLER-DEAD-ON-UNWIND` (`!callerNeedsDrop && !callerCatchesUnwind`), deleting `*x = v1` preserves all caller-observable states. |
| `sinkAfterReadingCleanupDrop_rejected` | `271-273` | `checkSinkStoreToCleanupCert` rejects sinking `*x = v1` past a local destructor in `bb_cleanup` that reads `*x` (`cleanupDropEffect = .readX`). |

### 2. Quantitative Store-Elimination and Latency Metrics (`rustc 1.99.1`)

Basis: execution

Table 2 summarizes the hot-path referent store counts, cold `cleanup`-pad
referent store counts, and `200,000`-iteration execution latencies from
[`support/run_unwind_store_sinking_bench.py`](support/run_unwind_store_sinking_bench.py)
([`support/unwind_store_sinking_metrics.json`](support/unwind_store_sinking_metrics.json)):

| Workload | Transformation | `-C panic=unwind` Hot Stores | `-C panic=unwind` Cold Stores | `-C panic=abort` Hot Stores | Unopt Latency (`us`) | Sunk/DSE Latency (`us`) | Speedup (`catch_unwind` Verified) |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: | :---: |
| **`W01` (`*x = v1; call(); *x = v2`)** | `SinkStoreToCleanupCert` | `2 -> 1` (`-50%`) | `0 -> 1` | `1` | `413.23` | `446.15` (DropGuard) / `413.0` (CFG) | `1.00x` (`-50%` hot stores) |
| **`W02` (`for i { *acc += call(i) }`)** | `PromoteProtectedMutInLoopCert` | `2/iter -> 1 exit` | `0 -> 1` | `1` | `235.43` | **`176.57`** | **`1.333x` (`+33.3%`)** |
| **`W03` (`Cursor { pos, rem, flags }`)** | `SinkStoreToCleanupCert` (3 fields) | `6 -> 3` (`-50%`) | `0 -> 3` | `3` | `557.29` | **`470.71`** | **`1.184x` (`+18.4%`)** |
| **`W04` (`RollbackGuard` overwrite)** | `DeleteStoreAcrossUnwindCert` | `2 -> 1` (`-50%`) | `1 -> 1` (`+0`) | `1` | `589.60` | **`411.95`** | **`1.431x` (`+43.1%`)** |

## Boundaries

1. **Ordering Relative to Frame-Local Destructors in `bb_cleanup` (`known not to apply` if sunk after drop):**
   - If the current function frame contains a local scope guard `g` dropped in
     `bb_cleanup` whose `Drop::drop` reads `*x` (through an interior shared
     reference or raw pointer derived from `x`), the sunk store `*x = v1` **must**
     execute at the entry of `bb_cleanup_sink` *before* `Drop::drop(&mut g)` runs
     (`sunkBeforeCleanupDrops = true`, enforced by `sinkAfterReadingCleanupDrop_rejected`).
2. **Shared References Inside `may_unwind` (`known not to apply`):**
   - If `x: &mut T` is reborrowed and passed as an argument to `may_unwind(&*x)`,
     then `may_unwind` performs a child read of `*x` during the call, so `*x = v1`
     is live on the normal path and is not a dead store.

## Evidence

1. **Compiler and Miri Source Coordinates (`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`):**
   - `src/tools/miri/src/borrow_tracker/tree_borrows/perms.rs:172-176` and
     `tree.rs:157-159` (`ProtectedDisabled` UB on foreign access to accessed
     `Unique` under `StrongProtector`).
   - `src/tools/miri/src/borrow_tracker/mod.rs:362-400` (`on_stack_pop`
     protector release at `Return` and `UnwindResume`).
   - `compiler/rustc_codegen_llvm/src/abi.rs:495-512` (`dead_on_unwind` on `sret`).
2. **Lean `v4.34.1` Mechanization (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`):**
   - [`support/TreeBorrowsUnwindStoreSinkingAndDseProbe.lean`](support/TreeBorrowsUnwindStoreSinkingAndDseProbe.lean)
     (zero `sorryAx`, zero `Lean.ofReduceBool`).
3. **Executable Benchmark Script and Preserved Dataset:**
   - [`support/run_unwind_store_sinking_bench.py`](support/run_unwind_store_sinking_bench.py)
   - [`support/unwind_store_sinking_metrics.json`](support/unwind_store_sinking_metrics.json)

## Revalidation

```bash
anneal-lean-run --mode file --concurrency 4 -- lake env lean \
  reports/tree-borrows-unwinding-store-sinking-and-protected-dse/support/TreeBorrowsUnwindStoreSinkingAndDseProbe.lean
python3 reports/tree-borrows-unwinding-store-sinking-and-protected-dse/support/run_unwind_store_sinking_bench.py
```
