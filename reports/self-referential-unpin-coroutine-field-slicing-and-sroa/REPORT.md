# Self-Referential (`!Unpin`) Coroutine Frame Field-Slicing (`PinFieldSplitCert`), Interior-Pointer `SROA`, and Unresumed Child-Future `MemCpyOpt`

## Summary

In `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`), every `async fn`,
`async` block, and `async gen` coroutine is assigned `hir::Movability::Static`
and unconditionally excluded from auto-implementing `core::marker::Unpin`
(`compiler/rustc_trait_selection/src/traits/select/candidate_assembly.rs:818-830`).
When a coroutine holds even one self-referential borrow across a suspension point
(for example, `let r = &mut hdr;` over a `32 B` local array `hdr: [u64; 4]` in
`B02_buffered_stream_parse`), `StateTransform` stores `r` inside the coroutine
frame (`((*(_1.0: &mut Coroutine)) as variant#3).1 = &mut ((*(_1.0)) as
variant#3).0`), causing whole-allocation `SROA` to abort on the entire `80 B`–`144 B`
coroutine stack frame. Combining compiler source analysis of
`compiler/rustc_mir_transform/src/coroutine/{layout.rs,mod.rs}`, a zero-axiom
Lean `v4.34.1` mechanization
([`support/CoroutinePinFieldSplitAndSroaProbe.lean`](support/CoroutinePinFieldSplitAndSroaProbe.lean)),
and a 9-kernel `rustc 1.99.1` (`LLVM 23.1.1`) benchmark suite
([`support/coroutine_pin_sroa_results.json`](support/coroutine_pin_sroa_results.json))
establishes four governing results for `MiniSSA` and `MiniMach`:

1. **Field-Disjoint Coroutine Interior-Pointer Provenance Analysis
   (`PinFieldSplitCert`, `checkPinFieldSplitCert`):**
   - `StateTransform` (`coroutine/layout.rs:53-71, 234-290, 333-442`) records
     every suspension-live local in `CoroutineLayout { field_tys, variant_fields,
     storage_conflicts }`, where `storage_conflicts: BitMatrix<CoroutineSavedLocal,
     CoroutineSavedLocal>` tracks which saved locals can ever be `StorageLive`
     simultaneously (and therefore never share physical byte offsets across
     variants).
   - `MiniSSA` partitions `CoroutineSavedLocal` into $\mathcal{F}_{\text{pinned}}$
     (fields whose address is taken via `Rvalue::Ref` or `Rvalue::RawPtr` inside
     the coroutine body, plus any field $k$ with
     `storage_conflicts.contains(pinned_field, k)` or `!field_tys[k].ty.is_freeze()`)
     and $\mathcal{F}_{\text{scalar}}$ (all remaining non-address-taken,
     `Freeze`, conflict-disjoint fields).
2. **Exact Bisimulation of Inlined Driver and Standalone `Future::poll` Frame
   Slicing (`pinFieldSplit_inlinedDriver_bisimExact`,
   `pinFieldSplit_standalonePoll_bisimExact`):**
   - **Inlined Driver Loop (`Case 1`):** When a caller or task driver allocates
     the coroutine on its stack and polls it in a loop, splitting `_coro` into a
     fixed-address pinned stack allocation `_coro_pinned` containing only
     $\mathcal{F}_{\text{pinned}}$ and pure SSA loop-header $\phi$-registers for
     $\mathcal{F}_{\text{scalar}}$ (including the coroutine discriminant,
     scalars, and the interior pointer `r_ptr` pointing to `_coro_pinned`) is
     an exact state bisimulation (`BisimExact`, mechanized in
     `pinFieldSplit_inlinedDriver_bisimExact`,
     [`support/CoroutinePinFieldSplitAndSroaProbe.lean:159-180`](support/CoroutinePinFieldSplitAndSroaProbe.lean#L159-L180)).
     When `r_ptr` has a single statically known base `&mut _coro_pinned` with
     constant element indices, forwarding `*r_ptr` to `_coro_pinned` renders
     `_coro_pinned` itself non-escaping and promotes the remaining array elements
     to registers (`0 B` stack frame).
   - **Standalone Un-Inlined `Future::poll(self: Pin<&mut Self>, cx)` (`Case 2`):**
     Within a single `poll` invocation before inlining, promoting any
     $f_j \in \mathcal{F}_{\text{scalar}}$ to an SSA register across internal
     basic blocks and child `poll` calls—writing back to `(*self).f_j` only at
     `Return(Pending | Ready)` and `UnwindResume` exits—is `BisimExact` under
     Tree Borrows per-byte permissions (`pinFieldSplit_standalonePoll_bisimExact`,
     [`support/CoroutinePinFieldSplitAndSroaProbe.lean:208-212`](support/CoroutinePinFieldSplitAndSroaProbe.lean#L208-L212)).
3. **`UnresumedMoveIsRelocatable` for Nested `!Unpin` Child Futures
   (`unresumedCoroutine_memcpyElision_refines`):**
   - Although every `async fn` child future type has `Movability::Static`
     (`!Unpin`), a newly constructed child future starts in state `0`
     (`CoroutineArgs::UNRESUMED`, `coroutine/mod.rs:29-32`) before any statement
     of its body has executed, and therefore contains **zero** active
     self-referential pointers (`selfRefTarget = none`).
   - Consequently, `MiniSSA`'s destination-passing (`MemCpyOpt`) pass can
     construct an `Unresumed` `!Unpin` child future directly in-place inside its
     parent coroutine variant field `((*_1.0) as variant#v).child`, eliding the
     temporary stack slot and `memcpy` (`unresumedCoroutine_memcpyElision_refines`,
     [`support/CoroutinePinFieldSplitAndSroaProbe.lean:254-258`](support/CoroutinePinFieldSplitAndSroaProbe.lean#L254-L258)).
4. **Closing the `80 B -> 32 B / 0 B` Gap on `B02_buffered_stream_parse` and
   Outperforming Stock `-O3` on Nested `!Unpin` Codecs:**
   - At stage `T3b` (`two-round SROA + JumpThreading + GVN + MemCpyOpt`),
     `B02_buffered_stream_parse` (`C01_B02`) shrinks from **`80 B` (`118`
     instructions, `545.52 us`)** to **`48 B` (`32 B` pinned `hdr` + `16 B` call
     alignment, `68` instructions, `341.06 us`, `1.60x` speedup)** with
     `PinFieldSplit` alone, and to **`0 B` (`83` instructions, `147.09 us`,
     `3.71x` speedup)** once single-base interior pointer forwarding is applied.
   - On `C02_codec` (`32 B` scratch array + `6` scalar fields) and `C03_nested`
     (two sequentially awaited `!Unpin` child futures with self-referential
     buffers), stock `rustc 1.99.1 -Copt-level=3` (`LLVM 23.1.1`) fails to
     scalarize the coroutine frames, leaving **`104 B` (`737.95 us`)** and
     **`88 B` (`1,380.33 us`)** stack frames even at `-O3`, whereas
     `PinFieldSplit` + interior-pointer forwarding achieves **`0 B` stack frame**
     and **`4.77x` (`154.79 us`)** and **`9.34x` (`147.86 us`)** speedups at `-O3`.

## Applicability

This report applies to `rustc 1.99.1`
(`58cf8f9c35b355199727627d07ae34a4e2846d67`), its bundled `LLVM 23.1.1` backend
(`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`), and `Lean 4 v4.34.1`
(`5045d0056413266e57c625dcd7c365b10e377c52`) when designing `MiniSSA` aggregate
scalar replacement (`SROA`), `MemCpyOpt`, and `HybridTrace` proof certificates
for `Runtime(PostCleanup)` coroutine state machines.

It extends three corpus reports:
- `rustc-statetransform-coroutines-async-gen-and-pin-mir-semantics`
- `coroutine-state-machine-optimization-and-hybridtrace-scaling`
- `tree-borrows-protectors-stack-coloring-and-dead-store-elimination`

Created: 2026-11-14 · Updated: 2026-11-14

## Findings

### 1. Why `Movability::Static` and Self-Referential Field Pointers Block Whole-Frame `SROA`

Basis: source + execution

In `compiler/rustc_trait_selection/src/traits/select/candidate_assembly.rs:818-830`,
`rustc` determines `Unpin` for `ty::Coroutine(coroutine_def_id, _)` solely from
`tcx.coroutine_movability(coroutine_def_id)`:
- `hir::Movability::Movable` (`gen` blocks without self-borrows): unconditionally
  implements `Unpin` via `BuiltinCandidate`;
- `hir::Movability::Static` (all `async fn`, `async` blocks, and `async gen`
  blocks): suppresses the `AutoImplCandidate` for `Unpin`, making every `async`
  coroutine type `!Unpin` regardless of whether its body actually borrows a
  local across `.await`.

In `compiler/rustc_mir_transform/src/coroutine/layout.rs:82-183`,
`locals_live_across_suspend_points` computes for `!movable` coroutines
(`layout.rs:120-133`):

```rust
if !movable {
    borrowed_locals_cursor.seek_before_primary_effect(loc);
    live_locals.union(borrowed_locals_cursor.get());
}
```

Every local that has been borrowed prior to a `Yield` terminator and remains
`StorageLive` at that `Yield` is added to `CoroutineSavedLocals`, and
`compute_storage_conflicts` (`layout.rs:234-290`) builds the symmetric bit
matrix `storage_conflicts: BitMatrix<CoroutineSavedLocal, CoroutineSavedLocal>`
recording all pairs of saved locals that can be `StorageLive` at the same program
point.

When an `async fn` creates a self-referential borrow `let r = &mut hdr;` live
across `.await`, `StateTransform` (`coroutine/mod.rs:137-159`) rewrites `hdr` to
`((*(_1.0: &mut Coroutine)) as variant#3).0` and `r` to
`((*(_1.0: &mut Coroutine)) as variant#3).1`, emitting:

```text
((*(_1.0: &mut Coroutine)) as variant#3).1 = &mut ((*(_1.0: &mut Coroutine)) as variant#3).0;
```

When `Future::poll` is inlined into its caller driver (`let fut = pin!(...);
drive_to_completion(fut, &mut cx)`), the address of field `0` of the caller's
coroutine stack allocation `_coro` is stored into memory (into field `1` of
`_coro` itself). Whole-allocation `SROA` (`NORM-04` `Mem2Reg_NonEscapingSlot`)
sees an address-taken pointer to `_coro` written to memory and aborts promotion
of the entire `_coro` allocation—forcing all pure scalar fields (`discriminant`,
loop counters, accumulators, and child `StepYield` futures) to be loaded and
stored from stack memory on every `.await` transition.

### 2. Static Field-Slicing Algorithm and `PinFieldSplitCert` Verification Conditions

Basis: source + derived + execution

Given a coroutine body and its `CoroutineLayout` at `Runtime(PostCleanup)` MIR,
`MiniSSA` computes the minimal pinned field closure $\mathcal{F}_{\text{pinned}}
\subseteq \text{CoroutineSavedLocal}$ in three deterministic steps:

1. **Direct Address-Taken Seed ($\mathcal{F}_{\text{addr}}$):** Scan all
   statements in the `Runtime(PostCleanup)` MIR body of `Future::poll` and
   `drop_in_place` for `Rvalue::Ref(_, _, place)` and `Rvalue::RawPtr(_, place)`
   rooted at `_1.0` (`SELF_ARG`). If `place` projects through
   `Downcast(_, v) -> Field(f, _)` (without an intervening `Deref` after `_1.0`),
   add `saved_local = variant_fields[v][f]` to $\mathcal{F}_{\text{addr}}$.
   (If `_1.0` itself is address-taken at root level without a variant field
   projection—aside from passing `Pin<&mut Self>` to `poll` before inlining—then
   $\mathcal{F}_{\text{pinned}}$ defaults to all saved fields.)
2. **`UnsafeCell` and Storage-Conflict Closure ($\mathcal{F}_{\text{pinned}}$):**
   Define:
   $$\mathcal{F}_{\text{pinned}} = \mathcal{F}_{\text{addr}} \cup \{s \mid \neg\text{is\_freeze}(\text{field\_tys}[s])\} \cup \{s \mid \exists a \in \mathcal{F}_{\text{addr}},\, \neg\text{storage\_conflicts}[a, s]\}$$
   Wait: note the polarity of `CoroutineLayout.storage_conflicts` in
   `coroutine/layout.rs:63-66, 275-289`! In `rustc`, `storage_conflicts[a, b] ==
   true` means `a` and `b` are simultaneously `StorageLive` and therefore
   **cannot share physical byte offsets** in the coroutine layout (their byte
   ranges are guaranteed disjoint!). Conversely, when `storage_conflicts[a, b]
   == false`, the layout algorithm is permitted to **overlap** `a` and `b` in
   the same physical union bytes across different suspension variants!
   Therefore, a candidate scalar field $s$ has a **strictly disjoint physical
   byte range** from every address-taken field $a \in \mathcal{F}_{\text{addr}}$
   if and only if either:
   - `storage_conflicts.contains(a, s) == true` (so `rustc_abi` places `a` and
     `s` at non-overlapping byte offsets), or
   - verified directly from `TyAndLayout::for_variant` byte offsets:
     $[\text{off}(a), \text{off}(a) + \text{size}(a)) \cap [\text{off}(s), \text{off}(s) + \text{size}(s)) = \emptyset$.
3. **Promotable Scalar Partition ($\mathcal{F}_{\text{scalar}}$):** Every saved
   field $s \notin \mathcal{F}_{\text{pinned}}$ has `is_freeze == true`, is
   never address-taken (`isAddressTaken == false`), and occupies bytes strictly
   disjoint from all address-taken fields (`conflictsWithPinned == false` in
   `CoroutineFieldMeta`,
   [`support/CoroutinePinFieldSplitAndSroaProbe.lean:38-64`](support/CoroutinePinFieldSplitAndSroaProbe.lean#L38-L64)).

In [`support/CoroutinePinFieldSplitAndSroaProbe.lean`](support/CoroutinePinFieldSplitAndSroaProbe.lean),
all four soundness and negative-rejection theorems are mechanized in Lean
`v4.34.1` with zero `sorryAx` and zero `Lean.ofReduceBool`:

| Theorem Name | Lines | Mechanized Property |
| :--- | :---: | :--- |
| `pinFieldSplit_inlinedDriver_bisimExact` | `159-180` | Splitting `_coro` into fixed-address `PinnedSlot` ($\mathcal{F}_{\text{pinned}}$) and SSA `SsaRegs` ($\mathcal{F}_{\text{scalar}}$) preserves all `*r_ptr` writes and loop results across arbitrary `yieldVals` lists. |
| `pinFieldSplit_standalonePoll_bisimExact` | `208-212` | Promoting $f_j \in \mathcal{F}_{\text{scalar}}$ to SSA registers inside standalone `Future::poll` across child `poll` calls with exit writeback is `BisimExact`. |
| `unresumedCoroutine_memcpyElision_refines` | `254-258` | A `!Unpin` child coroutine in state `0` (`Unresumed`) has `selfRefTarget = none`, so destination-passing (`MemCpyOpt`) into the parent frame refines temporary construction + `memcpy`. |
| `overlappingStorageConflict_split_rejected` | `272-275` | `checkPinFieldSplitCert` returns `false` whenever a candidate promoted field shares byte offsets (`conflictsWithPinned = true`) with a pinned field. |

### 3. Quantitative Benchmark Results Across `!Unpin` Coroutine Workloads (`rustc 1.99.1`)

Basis: execution

Executing [`support/run_coroutine_pin_sroa_bench.py`](support/run_coroutine_pin_sroa_bench.py)
(`50,000` iterations per workload in `rustc 1.99.1`, `LLVM 23.1.1`, recorded in
[`support/coroutine_pin_sroa_results.json`](support/coroutine_pin_sroa_results.json))
compares unsplit `!Unpin` coroutines against `PinFieldSplit` across `T0` (`-O0`),
`T3b` (two-round `SROA + JumpThreading + GVN + MemCpyOpt`), and `T4` (`-O3`):

| Workload | Variant | `T0` Frame (`B`) | `T3b` Frame (`B`) | `T4` (`-O3`) Frame (`B`) | `T3b` Insts | `T3b` Latency (`us`) | `T4` (`-O3`) Latency (`us`) | Checksum Match |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: | ---: | :---: |
| **`C01` (`B02_buffered_stream_parse`)** | Unsplit (`let r = &mut hdr`) | `376` | `80` | `0` | `118` | `545.52` | `747.75` | `328944192220905660` |
| **`C01` (`B02_buffered_stream_parse`)** | `PinFieldSplit` (`32 B` `hdr` pinned) | `584` | **`48`** | `0` | **`68`** | **`341.06` (`1.60x`)** | `295.51` (`2.53x`) | `328944192220905660` |
| **`C01` (`B02_buffered_stream_parse`)** | `PinFieldSplit` + Ptr Forwarding (`0 B`) | `360` | **`0`** | **`0`** | `83` | **`147.09` (`3.71x`)** | **`114.14` (`6.55x`)** | `328944192220905660` |
| **`C02` (`framed_codec_varint`)** | Unsplit (`32 B` buf + `6` scalars) | `440` | `112` | `104` | `151` | `605.70` | `737.95` | `10708165096584094032` |
| **`C02` (`framed_codec_varint`)** | `PinFieldSplit` + Ptr Forwarding | `424` | **`24`** | **`0`** | **`103`** | **`203.56` (`2.98x`)** | **`154.79` (`4.77x`)** | `10708165096584094032` |
| **`C03` (`nested_unresumed_child`)** | Unsplit (2 nested `!Unpin` futures) | `408` | `144` | `88` | `74` | `996.94` | `1,380.33` | `10837232548311377167` |
| **`C03` (`nested_unresumed_child`)** | `PinFieldSplit` + `UnresumedMemCpyOpt` | `392` | **`128`** | **`0`** | **`74`** | **`885.57` (`1.13x`)** | **`147.86` (`9.34x`)** | `10837232548311377167` |
| **`C04` (`ring_window_checksum`)** | Unsplit (`64 B` ring + cursors) | `456` | `112` | `0` | `75` | `386.12` | `229.80` | `18446744073709501615` |
| **`C04` (`ring_window_checksum`)** | `PinFieldSplit` + Ptr Forwarding | `360` | **`0`** | **`0`** | **`52`** | **`132.39` (`2.92x`)** | **`135.53` (`1.70x`)** | `18446744073709501615` |

## Boundaries

1. **Escaping Root `Pin<&mut Coroutine>` or Dynamic Union-Overlapping Variants
   (`known not to apply`):**
   - If a coroutine passes `&mut ((*(_1.0)) as variant#v).0` (`hdr`) to an
     external opaque function whose pointer may be stored in heap/global state or
     indexed by an unknown runtime offset, `hdr` itself must remain in the
     fixed-address `PinnedSlot` (`32 B` in `C01_B02_split_32b`, `48 B` total
     driver stack frame with `16 B` call alignment) and cannot be reduced to `0 B`
     registers, though all sibling fields in $\mathcal{F}_{\text{scalar}}$ still
     promote to SSA registers.
2. **Moving a Coroutine After First `Future::poll` (`known not to apply`):**
   - `UnresumedMoveIsRelocatable` (`unresumedCoroutine_memcpyElision_refines`)
     applies **strictly** when the child coroutine is in state `0`
     (`CoroutineArgs::UNRESUMED`) before any `poll` call. Once `Future::poll`
     has been called at least once (`stateDiscr >= 3`), relocating the child
     coroutine invalidates `selfRefTarget` (`relocateCoro` returns `none`).

## Evidence

1. **Compiler Source Coordinates (`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`):**
   - `compiler/rustc_trait_selection/src/traits/select/candidate_assembly.rs:818-830`
     (`Movability::Static` suppression of `Unpin` auto-trait candidate).
   - `compiler/rustc_mir_transform/src/coroutine/layout.rs:53-183, 234-290, 333-442`
     (`LivenessInfo`, `locals_live_across_suspend_points`, `compute_storage_conflicts`,
     `compute_layout`).
   - `compiler/rustc_mir_transform/src/coroutine/mod.rs:17-52, 137-205`
     (`StateTransform`, `UNRESUMED = 0`, `RETURNED = 1`, `POISONED = 2`).
2. **Lean `v4.34.1` Mechanization (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`):**
   - [`support/CoroutinePinFieldSplitAndSroaProbe.lean`](support/CoroutinePinFieldSplitAndSroaProbe.lean)
     (zero `sorryAx`, zero `Lean.ofReduceBool`).
3. **Executable Benchmark Script and Preserved Dataset:**
   - [`support/run_coroutine_pin_sroa_bench.py`](support/run_coroutine_pin_sroa_bench.py)
   - [`support/coroutine_pin_sroa_results.json`](support/coroutine_pin_sroa_results.json)

## Revalidation

```bash
anneal-lean-run --mode file --concurrency 4 -- lake env lean \
  reports/self-referential-unpin-coroutine-field-slicing-and-sroa/support/CoroutinePinFieldSplitAndSroaProbe.lean
python3 reports/self-referential-unpin-coroutine-field-slicing-and-sroa/support/run_coroutine_pin_sroa_bench.py
```
