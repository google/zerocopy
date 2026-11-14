# Tree Borrows Two-Stage Protectors, `StorageLive`/`StorageDead` Stack-Slot Coloring, and Dead-Store Elimination in `Runtime(PostCleanup)` MIR

## Summary

`Runtime(PostCleanup)` MIR in `rustc 1.99.1`
(`58cf8f9c35b355199727627d07ae34a4e2846d67`) governs memory lifetimes through
two orthogonal mechanisms: **interprocedural function-entry protectors** on
reference parameters (`RetagKind::FnEntry` -> `ProtectorKind::StrongProtector`
in Tree Borrows, lowered to LLVM `noalias` + `nofree` + `dereferenceable` +
`writable`) and **intra-function lexical/temporary storage markers**
(`StatementKind::StorageLive(_loc)` and `StatementKind::StorageDead(_loc)`,
lowered to `llvm.lifetime.start.p0` and `llvm.lifetime.end.p0`). Combining
compiler source inspection, a Lean `v4.34.1` mechanization with zero `sorryAx`
and zero `Lean.ofReduceBool`
([`support/TreeBorrowsStackColoringAndDseProbe.lean`](support/TreeBorrowsStackColoringAndDseProbe.lean)),
a 12-test `Runtime(PostCleanup)` MIR and Miri (`0.1.0`, `3ef0c22cdb`) litmus
suite, and a 6-workload `LLVM 23.1.1` `StackColoring` / `DSE` ablation
([`support/storagedead_and_stackcoloring_results.json`](support/storagedead_and_stackcoloring_results.json))
establishes four design invariants for `MiniSSA` and `MiniMach`:

1. **Exact Separation of `StrongProtector` Deallocation Blocking vs.
   `StorageDead` Local Deallocation (`tree.rs:522-611`):**
   - In Miri (`src/tools/miri/src/borrow_tracker/tree_borrows/tree.rs:522-611`
     and `compiler/rustc_const_eval/src/interpret/stack.rs:588-611`),
     `StorageDead(_loc)` invokes `deallocate_local`, which issues a
     `Dealloc` write access on `_loc`'s backing stack `AllocId` and scans the
     allocation's borrow tree for any node carrying an active
     `ProtectorKind::StrongProtector` with `perm.accessed == true` and
     `!perm.permission.is_cell()` (`tree.rs:572-583`).
   - Consequently, a local stack variable cannot be deallocated by
     `StorageDead(_loc)` while a `StrongProtector` reference to its interior is
     actively protecting an accessed byte (triggering `TransitionError::ProtectedDealloc`
     UB), whereas once any callee frame has popped (`on_stack_pop` ->
     `release_protector` -> `end_call` in `borrow_tracker/mod.rs:362-400`),
     `StorageDead(_loc)` immediately destroys the stack `AllocId`.
2. **Soundness of Pre-`StorageDead` Dead-Store Elimination (`DSE`) vs.
   Protected `&mut T` `DSE` (`dseBeforeStorageDead_refines`,
   `dseProtectedMutAcrossNoUnwindCall_refines`):**
   - **Pre-`StorageDead` Local `DSE`:** Deleting a store `_loc = v_dead`
     immediately preceding `StorageDead(_loc)` is unconditionally sound even
     when a raw pointer `*const T` to `_loc` has escaped into another variable
     or integer (`T05` in [`support/run_storagedead_and_stackcoloring_probe.py`](support/run_storagedead_and_stackcoloring_probe.py)).
     Because `StorageDead(_loc)` transitions `b.live` to `false`, any subsequent
     dereference through the dangling raw pointer is immediate Undefined
     Behavior (`readViaRawPtr bFinal = .ub`) in both the unoptimized and
     DSE-optimized executions (`dseBeforeStorageDead_refines`,
     [`support/TreeBorrowsStackColoringAndDseProbe.lean:119-131`](support/TreeBorrowsStackColoringAndDseProbe.lean#L119-L131)).
   - **Protected `&mut T` `DSE` Across `nounwind` Calls:** For a function
     parameter `x: &mut T` (`T: Unpin`) protected by a `StrongProtector`,
     deleting the first store in `*x = v1; foo(); *x = v2` is sound **if and
     only if** `foo()` cannot unwind to a caller frame that reads `*x` (or the
     store is compensated on the `cleanup` edge). When `foo()` is `nounwind` (or
     does not unwind), `*x = v1` transitions `x` to `Unique` (`accessed = true`),
     so any foreign read or foreign write to `*x` inside `foo()` transitions `x`
     to `Disabled` and triggers immediate `ProtectedDisabled` UB
     (`perms.rs:172-176`, `tree.rs:157-159`, mechanized in
     `dseProtectedMutAcrossNoUnwindCall_refines`,
     [`support/TreeBorrowsStackColoringAndDseProbe.lean:225-231`](support/TreeBorrowsStackColoringAndDseProbe.lean#L225-L231)).
3. **Physical Stack-Slot Coloring (`StackColoring`) Under PNVI-ae-udi / Strict
   Provenance (`danglingPtr_cannot_alias_reused_stack_slot`,
   `stackColoring_disjoint_refines`):**
   - When `_loc1` (`AllocId = id1`) and `_loc2` (`AllocId = id2`, `id1 != id2`)
     have disjoint `StorageLive`..`StorageDead` live ranges, assigning both
     locals the same physical frame address `[rsp + off]` (`sharedAddr`) refines
     the source operational semantics even when the program observes integer
     addresses via `.addr()` / `expose_provenance` (`T04`, where
     `addr1 == addr2` is a valid non-deterministic address choice after `id1` is
     deallocated).
   - Because pointer provenance tracks `AllocId` independently of `PhysAddr`, a
     dangling pointer `⟨sharedAddr, id1⟩` to dead `_loc1` cannot read or mutate
     live `_loc2` (`⟨sharedAddr, id2⟩`): dereferencing `⟨sharedAddr, id1⟩`
     evaluates to `.ub` (`danglingPtr_cannot_alias_reused_stack_slot`,
     [`support/TreeBorrowsStackColoringAndDseProbe.lean:177-183`](support/TreeBorrowsStackColoringAndDseProbe.lean#L177-L183)).
4. **Empirical Well-Bracketedness at `Runtime(PostCleanup)` MIR and `4.01x`
   Stack-Frame Compression from `StackColoring`:**
   - Across all 12 litmus functions compiled at `-Zmir-opt-level=0`
     (`Runtime(PostCleanup)` MIR), including regression patterns for historic
     MIR-opt `StorageDead` miscompilations (`#98112`, `#106364`, `#111502`),
     `orphan_storage_dead_locals` is **`0` (`12 / 12` well-bracketed)**, and
     Miri `-Zmiri-tree-borrows` passes **`12 / 12` (`0` UB)** (while Stacked
     Borrows fails `T07`, confirming Tree Borrows' `ReservedFrz { conflicted:
     true }` advantage for read-only aliased `&mut T`).
   - Across the 6 stack-intensive benchmark functions in
     [`support/storagedead_and_stackcoloring_results.json`](support/storagedead_and_stackcoloring_results.json),
     `DSE` reduces cumulative stack frame size from `6,512 B` (`-O0`) to `4,752 B`
     (`-O3 -Cllvm-args=-no-stack-coloring`, eliminating `568 B` in `s03` and
     `104 B` in `s05`), and `StorageLive`/`StorageDead`-driven `StackColoring`
     further compresses cumulative stack frames from `4,752 B` to **`1,184 B`
     (`4.01x` reduction, `5.50x` vs. `-O0`)**, shrinking
     `s04_inlined_8x128b_temporaries` by **`8.00x` (`1,088 B -> 136 B`)** and
     `s01_disjoint_4x512b_buffers` by **`4.00x` (`2,080 B -> 520 B`)** while
     cutting `-O3` `.text` size by `14.1%` (`6,118 B -> 5,255 B`).

## Applicability

This report applies to `rustc 1.99.1`
(`58cf8f9c35b355199727627d07ae34a4e2846d67`), its bundled `LLVM 23.1.1` backend
(`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`), Miri `0.1.0`
(`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`), and `Lean 4 v4.34.1`
(`5045d0056413266e57c625dcd7c365b10e377c52`) when lowering `Runtime(PostCleanup)`
MIR locals, `StorageLive`/`StorageDead` markers, `Mem2Reg`/`SROA`, `DSE`, and
`StackColoring` in `MiniSSA` and `MiniMach`.

It extends three corpus reports:
- `tree-borrows-two-stage-protector-release-and-reborrow-contracts`
- `rust-allocation-provenance-and-stack-lifetime-semantics`
- `rust-aliasing-models-stacked-tree-minirust-and-llvm-attributes`

Created: 2026-11-14 · Updated: 2026-11-14

## Findings

### 1. How `rustc 1.99.1` Partitions Locals into SSA `Operand` vs. Stack `Place` and Lowers `StorageLive` / `StorageDead`

Basis: source + execution

In `compiler/rustc_codegen_ssa/src/mir/analyze.rs:17-56`, `non_ssa_locals`
classifies every `mir::Local` in a `Runtime(PostCleanup)` MIR body into one of
four `LocalKind` states (`analyze.rs:58-67`):
- `LocalKind::ZST`: zero-sized locals (`layout.is_zst()`), which never allocate
  stack memory;
- `LocalKind::Unused`: scalar or `ScalarPair` locals neither defined nor used;
- `LocalKind::SSA(DefLocation)`: scalar or `ScalarPair` locals with a **single
  definition** (`DefLocation::Argument`, `DefLocation::Assignment(loc)`, or
  `DefLocation::CallReturn { call, target }`) that **strictly dominates** every
  non-mutating `Copy`/`Move`/`Inspect` use (`analyze.rs:226`) and has **zero**
  address-taking or sub-place mutating uses (`Store`, `SetDiscriminant`,
  `AsmOutput`, `Borrow`, `RawBorrow`, `Projection`, `SharedBorrow`,
  `FakeBorrow` at `analyze.rs:236-251`);
- `LocalKind::Memory`: all aggregates with `BackendRepr::Memory`, multi-assignment
  scalars, non-dominating uses, or borrowed/projected locals.

In `compiler/rustc_codegen_ssa/src/mir/statement.rs:72-85`, `StorageLive(local)`
and `StorageDead(local)` are complete no-ops on `LocalKind::SSA` (`LocalRef::Operand`
/ `LocalRef::PendingOperand`) and emit `cg_place.storage_live(bx)`
(`llvm.lifetime.start.p0`) and `cg_place.storage_dead(bx)`
(`llvm.lifetime.end.p0`) exclusively for `LocalRef::Place` and
`LocalRef::UnsizedPlace`.

In Miri (`compiler/rustc_const_eval/src/interpret/stack.rs:476-611`),
`push_stack_frame_done` computes `always_storage_live_locals(&body)`—the bitset
of locals that lack explicit `StorageLive` / `StorageDead` statements (including
`_0` `RETURN_PLACE` and function arguments `_1..=_n`)—and marks them live for
the entire frame. All other locals transition from `LocalValue::Dead` to
`LocalValue::Live` on `StatementKind::StorageLive(local)` (deallocating any
previous backing allocation if `StorageLive` is executed repeatedly in a loop,
`stack.rs:576-578`) and back to `LocalValue::Dead` (calling
`self.deallocate_ptr(ptr, None, MemoryKind::Stack)` at `stack.rs:608`) on
`StatementKind::StorageDead(local)`.

### 2. Well-Bracketedness of `StorageLive` / `StorageDead` at `Runtime(PostCleanup)` MIR vs. Higher `mir-opt` Levels

Basis: source + execution

Historical `rust-lang/rust` miscompilations involving `StorageDead` (`#98112`,
`#106364`, `#111502`) were caused by optional `mir-opt` passes (such as old
`PromoteTemps` / `DestinationPropagation` / `Inline` / `ReferencePropagation`
interactions) moving a reference use across an existing `StorageDead(_loc)` or
splitting control-flow paths without preserving `StorageLive` dominance.
Evaluating the 12-function litmus suite in
[`support/run_storagedead_and_stackcoloring_probe.py`](support/run_storagedead_and_stackcoloring_probe.py)
at `Runtime(PostCleanup)` MIR (`-Zmir-opt-level=0`) confirms that mandatory
pre-codegen MIR lowering preserves well-bracketed storage lifetimes across all
12 cases:

| Litmus Function | Pattern Tested | `StorageLive` Stmts | `StorageDead` Stmts | Orphan `StorageDead` Locals | Miri Tree Borrows | Miri Stacked Borrows |
| :--- | :--- | ---: | ---: | ---: | :--- | :--- |
| `t01_issue_98112_match_scrutinee_temp` | `#98112` match scrutinee temporary borrow | `6` | `6` | `0` | `PASS` | `PASS` |
| `t02_issue_106364_nested_scope_reborrow` | `#106364` nested block reborrow across `StorageDead` | `6` | `6` | `0` | `PASS` | `PASS` |
| `t03_issue_111502_loop_inlined_storage` | `#111502` loop body + `#[inline(always)]` callee | `12` | `15` | `0` | `PASS` | `PASS` |
| `t04_disjoint_scopes_addr_observation` | Disjoint scopes observing `.as_ptr().addr()` | `32` | `32` | `0` | `PASS` | `PASS` |
| `t05_dangling_raw_ptr_past_storagedead` | Raw pointer surviving `StorageDead` after dead store | `8` | `8` | `0` | `PASS` | `PASS` |
| `t06_protected_mut_dse_across_call` | Protected `&mut u64` dead store overwritten after call | `4` | `4` | `0` | `PASS` | `PASS` |
| `t07_protected_reserved_foreign_read_then_child_read` | Protected `ReservedFrz` foreign read + child read | `7` | `7` | `0` | **`PASS`** (`conflicted: true` allows child read) | **`FAIL`** (SB pops `Unique` on foreign read) |
| `t08_loop_repeated_storagelive_storagedead` | Loop re-executing `StorageLive`/`StorageDead` 8 times | `24` | `27` | `0` | `PASS` | `PASS` |
| `t09_multi_exit_storagedead` | Early `return` with multi-path `StorageDead` cleanup | `13` | `17` | `0` | `PASS` | `PASS` |
| `t10_local_subslice_reborrow_sroa` | Sub-slice `&mut arr[1..3]` local reborrow | `25` | `25` | `0` | `PASS` | `PASS` |
| `t11_safe_slot_reuse_with_raw_ptr_within_live_range` | Raw pointer writes inside disjoint live scopes | `16` | `16` | `0` | `PASS` | `PASS` |
| `t12_two_stage_protector_and_local_storagedead` | Callee two-stage protector release before caller `StorageDead` | `10` | `10` | `0` | `PASS` | `PASS` |

**Syntactic/Dataflow Well-Formedness Check for `MiniSSA` (`checkWellBracketedStorage`):**
Before `MiniSSA` lowers `StorageLive(_loc)` / `StorageDead(_loc)` into
stack-slot liveness intervals for `StackColoring` and pre-`StorageDead` `DSE`,
it runs a linear forward dataflow check over `body.basic_blocks`:
1. Every local $\ell \in \text{always\_storage\_live\_locals}$ has interval
   $[bb_0, \text{Return/UnwindResume}]$ and is excluded from intra-function
   slot sharing.
2. For every other non-SSA local $\ell$, every CFG path from `bb0` to a read,
   write, borrow, or `StorageDead(\ell)` must pass through a `StorageLive(\ell)`
   with no intervening `StorageDead(\ell)`. If any local fails this check (for
   example, in hand-written custom MIR), `MiniSSA` conservatively widens
   $\ell$'s live range to the entire function frame (`always_live`), preserving
   unconditional soundness without rejecting valid MIR.

### 3. Four Mechanized Soundness Theorems for `DSE`, `StackColoring`, and `Mem2Reg`

Basis: source + execution + derived

[`support/TreeBorrowsStackColoringAndDseProbe.lean`](support/TreeBorrowsStackColoringAndDseProbe.lean)
mechanizes the four refinement obligations in Lean `v4.34.1` (`0` `sorryAx`, `0`
`Lean.ofReduceBool`):

1. **Pre-`StorageDead` Dead-Store Elimination (`dseBeforeStorageDead_refines`,
   L119–131):**
   When stack block `b` is live (`b.live = true`) and a store `storeLocal b
   vDead` is immediately followed by `storageDead`, `storageDead` checks the
   exact Tree Borrows `StrongProtector` condition (`b.accessed && perm != .cell`,
   matching `tree.rs:572-583`) which is invariant under `b.value := vDead`, and
   sets `bFinal.live := false`. Any subsequent read through a surviving dangling
   raw pointer `readViaRawPtr bFinal` returns `.ub` in both programs, so
   `obsAfterStorageDead (storageDead b)` refines `obsAfterStorageDead
   (seqStoreThenStorageDead b vDead)`.
2. **Dangling-Pointer Isolation Across Reused Physical Stack Slots
   (`danglingPtr_cannot_alias_reused_stack_slot` and
   `stackColoring_disjoint_refines`, L177–194):**
   When `StackColoring` assigns disjointly live locals `_loc1` (`id1`) and
   `_loc2` (`id2`, `id1 != id2`) the same physical stack offset `sharedAddr =
   [rsp + off]`, pointer values retain their logical allocation provenance
   `PtrVal { addr, allocId }`. Even though `p1.addr == p2.addr == sharedAddr` is
   observable via `.addr()`, dereferencing the dangling pointer `p1 =
   ⟨sharedAddr, id1⟩` after `StorageDead(_loc1)` and `StorageLive(_loc2)` hits
   `p.allocId == id1 -> .ub`, while dereferencing `p2 = ⟨sharedAddr, id2⟩`
   evaluates to `.ok val2`.
3. **Protected `&mut T` `DSE` Across `nounwind` Calls
   (`dseProtectedMutAcrossNoUnwindCall_refines`, L225–231):**
   In `*x = v1; foo_nounwind(); *x = v2`, writing `*x = v1` transitions `x`'s
   Tree Borrows state to `Unique` with `accessed = true` under
   `StrongProtector`. During `foo_nounwind()`, any foreign read or foreign write
   to `*x` transitions `Unique` to `Disabled` (`perms.rs:172-176`) and triggers
   immediate `ProtectedDisabled` UB (`tree.rs:157-159`). In the sole defined
   execution (`OpaqueCallAction.noForeignAccess`), `*x = v2` overwrites `v1`
   without `v1` ever being observed.
4. **`Mem2Reg` / `SROA` `BisimExact` Promotion Criterion (`mem2reg_bisimExact`,
   L253–258):**
   When `isPromotableToSSA u = true` (`!hasAddressTakenRef &&
   !hasAddressTakenRawPtr && !hasSubSliceProjection && !escapedTagToMemory`),
   promoting a stack-allocated local into SSA registers is an exact step-by-step
   state bisimulation (`rfl`).

### 4. Empirical Stack-Frame and Code-Size Impact of `StackColoring` and `DSE` in `LLVM 23.1.1`

Basis: execution

[`support/run_storagedead_and_stackcoloring_probe.py`](support/run_storagedead_and_stackcoloring_probe.py)
measures stack-frame allocation (`subq $IMM, %rsp` with `-Cno-redzone=yes` so the
128-byte x86-64 leaf red zone does not mask frame sizes), instruction counts,
and `.text` section size across 6 stack-heavy benchmarks under 5 configurations:

| Configuration | Flags | `.text` Bytes | Sum Frame (`B`) | `s01` (`4x512B`) | `s02` (`6x256B` match) | `s03` (`512B` dead store) | `s04` (`8x128B` inlined) | `s05` (`&mut 256B` DSE) | `s06` (`2x256B` loop) |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `C0_O0_no_coloring_no_dse` | `-Copt-level=0` | `5,049` | `6,512` | `2,184` | `1,752` | `568` | `1,288` | `104` | `616` |
| `C1_O3_no_stack_coloring` | `-Copt-level=3 -Cllvm-args=-no-stack-coloring` | `6,118` | `4,752` | `2,080` | `1,056` | `0` | `1,088` | `0` | `528` |
| `C2_O3_full_stack_coloring_and_dse` | `-Copt-level=3` | `5,255` | **`1,184`** | **`520`** (`4.00x`) | **`264`** (`4.00x`) | **`0`** | **`136`** (`8.00x`) | **`0`** | **`264`** (`2.00x`) |
| `C3_Oz_no_stack_coloring` | `-Copt-level=z -Cllvm-args=-no-stack-coloring` | `1,713` | `4,752` | `2,080` | `1,056` | `0` | `1,088` | `0` | `528` |
| `C4_Oz_full_stack_coloring_and_dse` | `-Copt-level=z` | `1,603` | **`1,184`** | **`520`** (`4.00x`) | **`264`** (`4.00x`) | **`0`** | **`136`** (`8.00x`) | **`0`** | **`264`** (`2.00x`) |

Key quantitative takeaways:
- **Pre-`StorageDead` and Protected-`&mut` `DSE` (`C0 -> C1`):** Completely
  eliminates the `568 B` dead frame and `32` dead store instructions in
  `s03_dead_local_512b_stores_before_storagedead` (`34 -> 2` instructions) and
  removes two redundant `256 B` stores on `dst: &mut [u64; 32]` in
  `s05_protected_mut_256b_redundant_stores` (`60 -> 34` instructions).
- **`StorageLive`/`StorageDead` `StackColoring` (`C1 -> C2` and `C3 -> C4`):**
  Compresses cumulative stack frames by **`4.01x` (`4,752 B -> 1,184 B`)** at
  both `-O3` and `-Oz`, and reduces `-O3` `.text` code size by **`14.1%`
  (`6,118 B -> 5,255 B`)** because reusing a single `[rsp + offset]` base slot
  across sequential scopes eliminates large `disp32` `[rsp + 0x400]` displacement
  encodings in favor of compact `disp8` `[rsp + 0x08]` addressing.

## Boundaries

1. **Protected `&mut T` `DSE` Across Potentially Unwinding Calls (`can_unwind == true`):**
   - **Known not to apply without unwind compensation:** Theorem
     `dseProtectedMutAcrossNoUnwindCall_refines` applies only when the
     intervening call cannot unwind to a caller frame that observes `*x`. When a
     call may unwind (`UnwindAction::Cleanup` / `UnwindAction::Continue`) and
     the caller catches the panic or runs a `Drop` implementation that reads the
     referent of `x`, eliding `*x = v1` before the call is **unsound** unless
     `*x = v1` is sunk onto the `cleanup` landing pad before `UnwindResume`.
     (The companion report
     `tree-borrows-unwinding-cleanup-pads-two-phase-borrows-and-unsafecell`
     mechanizes this exact boundary.)
2. **May-Dangle Destructors (`#[may_dangle]`) and `StorageDead` Ordering:**
   - **Requires dereference-site rather than drop-entry liveness checks:** As
     established in
     `rustc-drop-elaboration-unwind-landing-pads-and-extensible-mir-semantics`,
     `StorageDead` for a borrowed local can precede `Drop` of a wrapper struct
     carrying `#[may_dangle]`. `StackColoring` remains sound because the
     `#[may_dangle]` destructor is forbidden from dereferencing the dead inner
     reference.

## Evidence

1. **Lean `v4.34.1` Mechanization (`0` `sorryAx`, `0` `Lean.ofReduceBool`):**
   - File:
     [`support/TreeBorrowsStackColoringAndDseProbe.lean`](support/TreeBorrowsStackColoringAndDseProbe.lean)
   - Verified theorems: `dseBeforeStorageDead_refines`,
     `danglingPtr_cannot_alias_reused_stack_slot`,
     `stackColoring_disjoint_refines`,
     `dseProtectedMutAcrossNoUnwindCall_refines`, and `mem2reg_bisimExact`.
2. **12-Test `Runtime(PostCleanup)` MIR Audit, Miri Litmus Suite, and 6-Workload
   `StackColoring`/`DSE` Ablation:**
   - Script:
     [`support/run_storagedead_and_stackcoloring_probe.py`](support/run_storagedead_and_stackcoloring_probe.py)
   - Dataset:
     [`support/storagedead_and_stackcoloring_results.json`](support/storagedead_and_stackcoloring_results.json)
3. **`rustc 1.99.1` and Miri Source Coordinates (`58cf8f9c35b355199727627d07ae34a4e2846d67`):**
   - `compiler/rustc_codegen_ssa/src/mir/analyze.rs:17-272` (`non_ssa_locals`,
     `LocalKind`, `LocalAnalyzer`)
   - `compiler/rustc_codegen_ssa/src/mir/statement.rs:72-85` (`StorageLive` /
     `StorageDead` codegen)
   - `compiler/rustc_const_eval/src/interpret/stack.rs:476-611`
     (`push_stack_frame_done`, `storage_live_dyn`, `storage_dead`,
     `deallocate_local`)
   - `src/tools/miri/src/borrow_tracker/tree_borrows/tree.rs:522-611`
     (`Tree::dealloc` and `StrongProtector` check)

## Revalidation

1. **Re-verify the Lean `v4.34.1` Mechanization:**
   ```bash
   anneal-lean-run --mode file --concurrency 4 -- \
     ~/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean \
     reports/tree-borrows-protectors-stack-coloring-and-dead-store-elimination/support/TreeBorrowsStackColoringAndDseProbe.lean
   ```
2. **Re-run the `Runtime(PostCleanup)` MIR Audit, Miri Suite, and `StackColoring` Ablation:**
   ```bash
   python3 reports/tree-borrows-protectors-stack-coloring-and-dead-store-elimination/support/run_storagedead_and_stackcoloring_probe.py
   ```
