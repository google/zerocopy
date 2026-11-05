<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Empirical `rustc` `Runtime(PostCleanup)` MIR Probes and Lean 4 Reflection vs. Symbolic Execution Scaling

## Summary

This report provides primary-source and empirical execution evidence answering
two architectural questions for Anneal's MIR verification pipeline:

1. **What exact MIR representations reach `MirPhase::Runtime(RuntimePhase::PostCleanup)`
   across the next five Rust construct families?**
   Using `support/postcleanup_constructs_specimen.rs` and
   `support/probe_postcleanup_constructs.py` across `rustc` `nightly-2026-03-19`
   (`1.96.0-nightly`, `fd0c901b00ee1e08a250039cdb90258603497e20`) and
   `nightly-2026-05-31` (`1.98.0-nightly`,
   `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`), we establish the exact
   statement, rvalue, projection, and control-flow structures emitted for:
   - `while` loops and `Range` iterator `for` loops (including `StorageLive` /
     `StorageDead` scoping across loop back-edges),
   - disjoint multi-field mutable borrows, nested reborrows, two-phase mutable
     borrows (`MutBorrowKind::TwoPhaseBorrow`), and raw pointer projections,
   - multi-variant payload enum construction (`AggregateKind::Adt`) and pattern
     matching (`Rvalue::Discriminant`, `SwitchInt`, `ProjectionElem::Downcast`),
   - array and slice indexing, pattern sub-slicing (`ConstantIndex`,
     `Subslice`), `UnOp::PtrMetadata`, `RawPtrKind::FakeForPtrMetadata`, and
     unlowered `slice::len` calls, and
   - drop elaboration (`ElaborateDrops`), compiler-synthesized stack boolean
     drop flags, `TerminatorKind::Drop`, `is_cleanup` basic blocks, and
     `TerminatorKind::UnwindResume`.

2. **How do Stage 3 Lean 4 verification architectures and `MirState` local
   environment representations scale in proof term size, elaboration time, and
   kernel WHNF checking time?**
   Using `support/ReflectionVsSymExecBench.lean` and
   `support/run_lean_scaling_bench.py` across `leanprover/lean4:v4.28.0-rc1`
   (`3b0f2862196c6a8af9eb0025ee650252694013dd`), `leanprover/lean4:v4.28.0`
   (`7e01a1bf5c70fc6167d49c345d3bf80596e9a79b`), and `leanprover/lean4:v4.34.1`
   (`5045d0056413266e57c625dcd7c365b10e377c52`), we compare:
   - **Architecture A (Unjoined Tree-Unrolled Small-Step Deduction):** scales as
     $\Theta(2^K)$ on $K$-diamond CFGs, reaching `2,022,167` unfolded proof tree
     nodes (`9.54 s` tactic execution on `v4.34.1`, `11.47 s` on `v4.28.0`) at
     $K = 8$ and failing Lean's default `maxHeartbeats = 200,000` at $K \ge 8$.
   - **Architecture B (Block-Modular Symbolic Execution via `execNormal_join` +
     Canonicalized State):** restores linear $\Theta(K)$ scaling on $K$-diamond
     CFGs (`33,217` tree nodes, `138.5 ms` tactic execution, `31.2 ms` kernel
     checking at $K = 10$ on `v4.34.1`), provided dead branch temporaries are
     canonicalized to `none` via `StorageDead` before each join point. On
     straight-line $N$-block chains, however, tactic deduction still constructs
     large proof terms (`3,162` DAG objects / `847,801` tree nodes and `2.99 s`
     tactic execution at $N = 128$ on `v4.34.1`).
   - **Architecture C (Total Computational Reflection via `checkBodySym` +
     `checkBodySym_sound`):** produces a **constant-size proof term** (`30` DAG
     objects / `59` tree nodes) across all $K \in \{1, \dots, 10\}$ and
     $N \in \{16, \dots, 128\}$, eliminating tactic execution (`0 ms`) and
     verifying $K = 10$ diamonds in `40.6 ms` kernel checking (`88.3 ms` total)
     and $N = 128$ chains in `265.0 ms` kernel checking (`630.0 ms` total) on
     `v4.34.1` (`5.17x` faster total time than Architecture B at $N = 128$).
   - **Environment Representation Pitfall (`ClosureLocals` vs. `ListLocals`):**
     Anneal's current `MirState.locals : Nat → Option MirVal` with
     `updateLocal locals target val := fun i => if i == target then val else locals i`
     accumulates $N$ nested lambda closures across $N$ assignments, causing
     $\Theta(N^2)$ kernel WHNF reduction (`13.0 ms -> 56.6 ms -> 214.0 ms ->
     1,010.0 ms` for $N \in \{20, 50, 100, 200\}$ on `v4.34.1`) and failing
     Lean's default `maxRecDepth = 512` at $N = 200$. Replacing it with a
     spine-strict `List (Option MirVal)` reduces eagerly in $\Theta(N \cdot L)$
     (`22.0 ms -> 46.6 ms -> 94.2 ms -> 256.0 ms` on `v4.34.1`, `8.16x` faster
     elaboration and `3.95x` faster kernel checking at $N = 200$, and `5.00x`
     faster kernel checking on `v4.28.0`) while succeeding within default
     recursion limits.

## Applicability

- **Subjects and pinned revisions:**
  - `rust-lang/rust` (`nightly-2026-03-19` / `1.96.0-nightly`, commit
    `fd0c901b00ee1e08a250039cdb90258603497e20`, LLVM `22.1.0`,
    `x86_64-unknown-linux-gnu`) — pinned in `joshlf/anneal`'s `flake.nix`.
  - `rust-lang/rust` (`nightly-2026-05-31` / `1.98.0-nightly`, commit
    `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, LLVM `22.1.6`,
    `x86_64-unknown-linux-gnu`).
  - `leanprover/lean4` (`v4.28.0-rc1`, commit
    `3b0f2862196c6a8af9eb0025ee650252694013dd`, and `v4.28.0`, commit
    `7e01a1bf5c70fc6167d49c345d3bf80596e9a79b`, `x86_64-unknown-linux-gnu`) —
    pinned in `joshlf/anneal`'s `lean-toolchain`.
  - `leanprover/lean4` (`v4.34.1`, commit
    `5045d0056413266e57c625dcd7c365b10e377c52`, `x86_64-unknown-linux-gnu`).
  - `joshlf/anneal` (commit `572f1e80580daa4b052ce5646bb675484d9bb957`,
    specifically `trusted/rustc-capture/src/extract.rs`,
    `trusted/lean/Trusted/MirAst.lean`, and
    `trusted/lean/Trusted/MirSemantics.lean`).
- **Pass-pipeline and flag conditions:**
  - All Part 1 findings apply to `MirPhase::Runtime(RuntimePhase::PostCleanup)`
    (phase index `3-2`, immediately after `run_runtime_cleanup_passes` in
    `compiler/rustc_mir_transform/src/lib.rs`), which `anneal-rustc-capture`
    extracts via `tcx.mir_drops_elaborated_and_const_checked(def_id)`.
  - Where behavior differs under `-Z mir-preserve-ub` or in
    `MirPhase::Runtime(RuntimePhase::Optimized)` (`-O`, phase index `3-3`), the
    exact pass responsible is identified.

## Findings

### Finding 1: Exact `rustc` Pass Pipeline Leading to `Runtime(PostCleanup)` and the Two Effects of `-Z mir-preserve-ub`

`Basis: source, execution, derived`

In `compiler/rustc_mir_transform/src/lib.rs` (lines 569–670 of commit
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`), `mir_drops_elaborated_and_const_checked`
transitions a `mir::Body` from `MirPhase::Analysis(AnalysisPhase::Initial)` to
`MirPhase::Runtime(RuntimePhase::PostCleanup)` through three pass groups:

1. **`run_analysis_cleanup_passes` ($\to$ `Analysis(PostCleanup)`, phase `2-2`):**
   `ImpossiblePredicates`, `CleanupPostBorrowck`, `RemoveNoopLandingPads`,
   `SimplifyCfg::PostAnalysis`, and `Derefer`.
   - `CleanupPostBorrowck` (`compiler/rustc_mir_transform/src/cleanup_post_borrowck.rs`,
     lines 32–63) deletes `AscribeUserType`, `FakeRead`, `BackwardIncompatibleDropHint`,
     and `Retag`, replaces `BorrowKind::Fake(_)` assignments with `StatementKind::Nop`,
     and lowers `CastKind::PointerCoercion( ClosureFnPointer | UnsafeFnPointer |
     ReifyFnPointer | MutToConstPointer | ArrayToPointer )` to `CastKind::PtrToPtr`
     or `CastKind::FnPtrToPtr`.
2. **`run_runtime_lowering_passes` ($\to$ `Runtime(Initial)`, phase `3-1`):**
   `CriticalCallEdges` (`AddCallGuards` in `1.96.0-nightly`),
   `PostAnalysisNormalize`, `Subtyper`, `ElaborateDrops`,
   `Lint(CheckDropRecursion)`, `AbortUnwindingCalls`, `AddMovesForPackedDrops`,
   (`AddRetag` in `1.96.0-nightly` when `-Z mir-emit-retag` is set),
   `EraseDerefTemps`, `ElaborateBoxDerefs`, `coroutine::StateTransform`, and
   `Lint(KnownPanicsLint)`.
3. **`run_runtime_cleanup_passes` ($\to$ `Runtime(PostCleanup)`, phase `3-2`):**
   `LowerIntrinsics`, `RemovePlaceMention`, and `SimplifyCfg::PreOptimizations`,
   followed by clearing `decl.local_info = ClearCrossCrate::Clear` for all
   locals.

Across the entire compiler (`compiler/rustc_mir_transform/src/`), the unstable
flag `-Z mir-preserve-ub` is consulted in only two places:

- `RemovePlaceMention::is_enabled` (`remove_place_mention.rs`, line 11) returns
  `!sess.opts.unstable_opts.mir_preserve_ub`. By default, `RemovePlaceMention`
  erases every `StatementKind::PlaceMention(place)` to `Nop` before
  `Runtime(PostCleanup)`. With `-Z mir-preserve-ub`, `PlaceMention` statements
  generated for `match` scrutinees and `let _ = place;` bindings survive into
  `Runtime(PostCleanup)` (`2` in `range_for_loop_sum`, `2` in
  `construct_and_match_packet`, and `1` in `array_and_slice_ops`, vs. `0` under
  default flags across both `1.96.0-nightly` and `1.98.0-nightly`).
- `CfgSimplifier::new` (`simplify.rs`, lines 129–130 and 306–328) sets
  `preserve_switch_reads = matches!(body.phase, MirPhase::Built | MirPhase::Analysis(_))
  || tcx.sess.opts.unstable_opts.mir_preserve_ub`. When `false`,
  `SimplifyCfg::PreOptimizations` collapses a `SwitchInt` whose targets are all
  identical into a `Goto`; when `true` (`-Z mir-preserve-ub`), the `SwitchInt`
  is retained to preserve any UB from reading an uninitialized discriminant.

---

### Finding 2: Loop Topologies and `StorageLive` / `StorageDead` Lifecycle Across Back-Edges

`Basis: source, execution, derived`

In `Runtime(PostCleanup)`, both `while` loops and `for x in 0..n` iterator loops
compile to irreducible-free natural loops with a single `goto` back-edge from
the loop latch to the loop header, and exhibit two distinct storage-lifecycle
regimes:

1. **Loop-carried locals vs. per-iteration temporaries (`while_loop_sum`):**
   - Outer accumulators (`_2` for `acc`, `_3` for `i`) execute `StorageLive`
     once in the entry block `bb0` (lines 34, 36) and `StorageDead` once in the
     exit block `bb5` (lines 98, 99); they are **not** re-allocated across loop
     iterations.
   - Loop-condition temporaries (`_6: bool`, `_7: usize`, `_8: usize`) are
     allocated with `StorageLive` inside the loop header `bb1` (lines 43–46)
     before `switchInt(move _6) -> [0: bb5, otherwise: bb2]`. Because `bb1`
     branches before deallocating `_7`, `_8`, and `_6`, `rustc` emits duplicate
     `StorageDead` statements along both outgoing branches: `StorageDead(_8);
     StorageDead(_7);` at the entry of `bb2` (lines 53–54) and at the entry of
     `bb5` (lines 90–91), and `StorageDead(_6)` at the end of the latch `bb4`
     (line 85) before `goto -> bb1` as well as in `bb5` (line 95). Syntactically,
     `while_loop_sum` contains `14` `StorageLive` statements and `17`
     `StorageDead` statements, but along every dynamic execution trace every
     `StorageLive(local)` is paired 1-to-1 with a `StorageDead(local)` before
     the back-edge `bb4 -> bb1` fires.
   - Inner block-scoped bindings (`let step = i ^ 1` in `_9`) execute
     `StorageLive(_9)` at `bb2` (line 55) and `StorageDead(_9)` at the latch
     `bb4` (line 84) on every iteration.

2. **Desugared `Range<usize>` iterator loops (`range_for_loop_sum`):**
   - `0..n` is constructed in `bb0` as an ADT aggregate
     `_5 = std::ops::Range::<usize> { start: const 0_usize, end: move _6 }`
     and passed to `<Range<usize> as IntoIterator>::into_iter(move _5) ->
     [return: bb1, unwind continue]`.
   - In `bb1`, the iterator state `_7` (`debug iter => _7`) is initialized once
     (`StorageLive(_7); _7 = move _4; goto -> bb2`).
   - On each iteration at header `bb2`, `_12 = &mut _7; _11 = &mut (*_12);`
     borrows the iterator mutably and calls
     `_10 = <Range<usize> as Iterator>::next(move _11) -> [return: bb3, unwind continue]`.
   - `bb3` extracts `_13 = discriminant(_10)` and branches via
     `switchInt(move _13) -> [0: bb6, 1: bb5, otherwise: bb4]`, where `bb4` is
     `unreachable;`, `bb6` (`None`) exits and drops storage for `_12, _10, _9,
     _7, _4, _3, _2`, and `bb5` (`Some`) extracts the payload via a downcast
     field projection `_15 = copy ((_10 as Some).0: usize)` before jumping from
     latch `bb7` back to `bb2` (`bb7 -> bb2`).

---

### Finding 3: Disjoint Field Borrows, Nested Reborrows, Preservation of `MutBorrowKind::TwoPhaseBorrow`, and `WithRetag` Evolution

`Basis: source, execution, derived`

Inspecting Family 2 (`disjoint_field_borrows`, `nested_reborrow`,
`two_phase_method_borrow`, `raw_ptr_projections`) across `1.96.0-nightly` and
`1.98.0-nightly` reveals four critical invariants for Stage 1 capture and
Stage 2 semantics:

1. **Two-step reborrow lowering for explicit `&mut` bindings:**
   In `disjoint_field_borrows` and `nested_reborrow`, `let a: &mut u64 = &mut p.0`
   is lowered in `Runtime(PostCleanup)` into a temporary borrow followed by an
   explicit deref-reborrow:
   ```text
   StorageLive(_2);
   StorageLive(_3);
   _3 = &mut ((*_1).0: u64);
   _2 = &mut (*_3);
   StorageDead(_3);
   ```
   Notice that `_3` is immediately marked `StorageDead(_3)` while `_2` remains
   live! This proves that `StorageDead(_3)` on a reference temporary does **not**
   invalidate a reference `_2` reborrowed from `*_3`; only the stack slot
   holding the pointer `_3` is deallocated.

2. **`BorrowKind::Mut { kind: MutBorrowKind::TwoPhaseBorrow }` survives intact in
   `Runtime(PostCleanup)`:**
   In `compiler/rustc_mir_build/src/thir/cx/expr.rs` (lines 1457–1470), method
   receiver autorefs with `AllowTwoPhase::Yes` emit
   `BorrowKind::Mut { kind: MutBorrowKind::TwoPhaseBorrow }`. Neither
   `CleanupPostBorrowck` (`cleanup_post_borrowck.rs`, lines 32–63, which only
   strips `BorrowKind::Fake(_)`) nor any pass in `run_runtime_lowering_passes`
   or `run_runtime_cleanup_passes` modifies `MutBorrowKind::TwoPhaseBorrow`.
   Consequently, in `two_phase_method_borrow` (`v.push(v.len())`), `bb0` in
   `Runtime(PostCleanup)` executes:
   ```text
   StorageLive(_3);
   _3 = &mut (*_1);
   StorageLive(_4);
   StorageLive(_5);
   _5 = &(*_1);
   _4 = TwoPhaseReceiver::len(move _5) -> [return: bb1, unwind continue];
   ```
   followed in `bb1` by `_2 = TwoPhaseReceiver::push(move _3, move _4)`. Here
   the mutable borrow `_3` is reserved in `bb0`, a shared borrow `_5 = &(*_1)`
   is taken and consumed by `TwoPhaseReceiver::len` while `_3` is live, and `_3`
   is activated when moved into `TwoPhaseReceiver::push` in `bb1`.
   - **MIR pretty-printer masking pitfall:** In `compiler/rustc_middle/src/mir/pretty.rs`
     (lines 1165–1171), `BorrowKind::Mut { .. }` formats all mutable borrow
     kinds—`Default`, `TwoPhaseBorrow`, and `ClosureCapture`—as the identical
     string `"mut "`. Textual `-Z dump-mir` parsers therefore cannot distinguish
     two-phase borrows from standard mutable borrows at `Runtime(PostCleanup)`,
     whereas `anneal-rustc-capture` (inspecting the typed `mir::Body` AST) must
     match `BorrowKind::Mut { kind: MutBorrowKind::Default | MutBorrowKind::TwoPhaseBorrow }`
     and allow shared borrows of `*_1` between a `TwoPhaseBorrow`'s reservation
     and activation.

3. **Compiler evolution between `1.96.0-nightly` and `1.98.0-nightly`
   (`StatementKind::Retag` $\to$ `Rvalue::Use(Operand, WithRetag)`):**
   In `nightly-2026-03-19` (`1.96.0-nightly`), `Rvalue::Use(Operand)` had a
   single field and retags were represented as standalone `StatementKind::Retag`
   statements emitted by `AddRetag` under `-Z mir-emit-retag`. By
   `nightly-2026-05-31` (`1.98.0-nightly`), `AddRetag` was removed and replaced
   by `Rvalue::Use(Operand, WithRetag)` (`compiler/rustc_middle/src/mir/pretty.rs`,
   lines 1146–1149). When `InstSimplify` (`compiler/rustc_mir_transform/src/instsimplify.rs`,
   lines 159–166) simplifies `_3 = &mut (*_1)` in `Runtime(Optimized)`, it
   explicitly checks `BorrowKind::Mut { kind: MutBorrowKind::TwoPhaseBorrow }`:
   converting `nested_reborrow` (`MutBorrowKind::Default`) into `_3 = copy _1`
   (`WithRetag::Yes`), while converting `two_phase_method_borrow`
   (`MutBorrowKind::TwoPhaseBorrow`) into `_3 = no_retag copy _1`
   (`WithRetag::No`).

4. **Raw pointer field projections (`Rvalue::RawPtr`):**
   In `raw_ptr_projections`, `&raw const (*p).1` and `&raw mut (*m).0` lower
   directly to single-statement assignments `_3 = &raw const ((*_1).1: u32)`
   (`Rvalue::RawPtr(RawPtrKind::Const, (*_1).1)`) and
   `_4 = &raw mut ((*_2).0: u64)` (`Rvalue::RawPtr(RawPtrKind::Mut, (*_2).0)`),
   creating no intermediate reference temporaries.

---

### Finding 4: Payload Enums Use `AggregateKind::Adt` (Not `SetDiscriminant`) in `Runtime(PostCleanup)`

`Basis: source, execution, derived`

A stale doc comment on `RuntimePhase::Initial` in
`compiler/rustc_middle/src/mir/syntax.rs` (lines 123–133 of commit
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`) claims that `Rvalue::Aggregate` is
disallowed for all `AggregateKind`s except `Array` in `Runtime` MIR and that
`StatementKind::SetDiscriminant` is introduced instead. Both the MIR validator
(`compiler/rustc_mir_transform/src/validate.rs`, lines 1015–1096) and empirical
`Runtime(PostCleanup)` dumps of `construct_and_match_packet` refute that comment:

- Constructing `Packet::Empty`, `Packet::Val(x)`, and `Packet::Pair(a, b)` in
  `Runtime(PostCleanup)` emits single-statement `Rvalue::Aggregate` assignments
  with `AggregateKind::Adt(def_id, variant_idx, args, None, None)`:
  - `bb3`: `_5 = Packet::Empty;` (`VariantIdx(0)`, 0 operands)
  - `bb2`: `_5 = Packet::Val(move _6);` (`VariantIdx(1)`, 1 operand)
  - `bb1`: `_5 = Packet::Pair(move _7, move _8);` (`VariantIdx(2)`, 2 operands)
- Across the entire `rustc_mir_transform` crate, `StatementKind::SetDiscriminant`
  is emitted **only** by coroutine state-machine lowering
  (`coroutine::StateTransform` in `coroutine.rs`, line 370), coroutine clone
  shims (`shim.rs`, line 773), and `#[custom_mir]`—never for ordinary Rust enum
  construction.
- Pattern-matching on `Packet` in `bb4` evaluates `_9 = discriminant(_5)`
  (`Rvalue::Discriminant(_5)` of type `isize`), branches via
  `switchInt(move _9) -> [0: bb8, 1: bb7, 2: bb6, otherwise: bb5]` (where `bb5`
  contains `unreachable;`), and extracts variant payloads in `bb6` and `bb7` via
  `ProjectionElem::Downcast` followed by `ProjectionElem::Field`:
  - `bb7`: `_10 = copy ((_5 as Val).0: u64);`
  - `bb6`: `_11 = copy ((_5 as Pair).0: u32); _12 = copy ((_5 as Pair).1: u32);`

---

### Finding 5: Array and Slice Indexing, `UnOp::PtrMetadata`, `RawPtrKind::FakeForPtrMetadata`, and Unlowered `slice::len` Calls

`Basis: source, execution, derived`

Inspecting `array_and_slice_ops` and `compiler/rustc_mir_build/src/builder/expr/as_place.rs`
(lines 668–724, `len_of_slice_or_array`) establishes that `Rvalue::Len` no
longer exists in `rustc` (`1.96.0-nightly` or `1.98.0-nightly`). Instead, length
extraction and indexing split into four distinct cases in `Runtime(PostCleanup)`:

| Operation in `array_and_slice_ops` | `Runtime(PostCleanup)` MIR Lowering | `Runtime(Optimized)` (`-O`) Lowering |
| :--- | :--- | :--- |
| Fixed-size array index `arr[i]` (`_1: &[u64; 4]`) | Compile-time constant length `const 4_usize`: `_7 = Lt(copy _6, const 4_usize); assert(move _7, ..., const 4_usize, copy _6) -> [success: bb1, unwind continue];` followed by `_5 = copy (*_1)[_6];` (`[Deref, Index(_6)]`). | Identical constant bounds check + `(*_1)[_4]`. |
| Shared slice index `slice[i]` (`_2: &[u64]`) | Direct `UnOp::PtrMetadata` on the `Copy` shared reference: `_10 = PtrMetadata(copy _2); _11 = Lt(copy _9, copy _10); assert(move _11, ...) -> [success: bb2, ...];` followed by `_8 = copy (*_2)[_9];`. | Identical `PtrMetadata(copy _2)` + `(*_2)[_4]`. |
| Mutable slice index `mut_slice[i]` (`_3: &mut [u64]`) | Two-step fake raw pointer cast + `PtrMetadata` (because `&mut [u64]` is not `Copy`): `_16 = &raw const (fake) (*_3); _17 = PtrMetadata(move _16); _18 = Lt(copy _15, copy _17); assert(move _18, ...);` where `&raw const (fake)` is `Rvalue::RawPtr(RawPtrKind::FakeForPtrMetadata, *_3)`. | Identical `_16 = &raw const (fake) (*_3); _17 = PtrMetadata(move _16);`. |
| Slice pattern `match slice { [head, rest @ .., tail] => ... }` | Length check `_21 = PtrMetadata(copy _2); _23 = Ge(move _20, const 2_usize); switchInt(move _23) -> [0: bb5, otherwise: bb6]`, followed in `bb6` by `ProjectionElem::ConstantIndex` and `ProjectionElem::Subslice`: `_24 = &(*_2)[0 of 2]` (`offset: 0, min_length: 2, from_end: false`), `_25 = &(*_2)[1:-1]` (`from: 1, to: 1, from_end: true`), and `_26 = &(*_2)[-1 of 2]` (`offset: 1, min_length: 2, from_end: true`). | Identical `ConstantIndex` and `Subslice` projections. |
| Explicit method call `rest.len()` (`core::slice::<impl [u64]>::len`) | Remains an unlowered `TerminatorKind::Call`: `_31 = core::slice::<impl [u64]>::len(move _32) -> [return: bb8, unwind continue];` because `LowerSliceLenCalls` (`lower_slice_len.rs`, lines 10–66) is only scheduled in `run_optimization_passes` (`lib.rs`, line 699). | Inlined/lowered by `LowerSliceLenCalls` to `_31 = PtrMetadata(move _25)`. |

---

### Finding 6: Drop Elaboration, Stack Boolean Drop Flags, and Unwind Cleanup Topologies

`Basis: source, execution, derived`

In `conditional_move_and_unwind` (where `d1: DropTracked` is conditionally moved
into `consume_tracked(d1)` when `cond` is `true` before calling `may_unwind()`,
while `d2: DropTracked` remains live until function exit), `ElaborateDrops`
(`compiler/rustc_mir_transform/src/elaborate_drops.rs`, lines 400–455) transforms
the CFG at `Runtime(Initial)` / `Runtime(PostCleanup)` into `16` basic blocks
(`12` normal blocks and `4` `is_cleanup` blocks `bb11`, `bb12`, `bb14`, `bb15`):

1. **Synthesized stack boolean drop flag (`_18: bool`):**
   - For `d2` (`_6`), whose initialization status is statically known at every
     program point, `ElaborateDrops` allocates **no** drop flag: `bb8` drops `_6`
     unconditionally on the normal return path (`drop(_6) -> [return: bb9, unwind: bb15]`),
     and `bb11 (cleanup)` drops `_6` unconditionally on the unwind path from
     `consume_tracked` / `may_unwind` (`drop(_6) -> [return: bb15, unwind terminate(cleanup)]`).
   - For `d1` (`_4`), which is conditionally moved in `bb2`, `ElaborateDrops`
     synthesizes a stack local `let mut _18: bool;` without a `StorageLive` or
     `StorageDead` annotation:
     - `bb0` initializes `_18 = const false;` at function entry (`Location::START`)
       and sets `_18 = const true;` immediately before `_4 = DropTracked(move _5);`.
     - `bb2` (the `cond == true` branch that moves `_4`) sets `_18 = const false;`
       immediately before `_11 = move _4;`.
     - On normal exit after `drop(_6)` completes (`bb9`), `switchInt(copy _18) ->
       [0: bb10, otherwise: bb13]` tests the drop flag: if `_18 != 0`, `bb13`
       executes `drop(_4) -> [return: bb10, unwind: bb12]` before `bb10` sets
       `_18 = const false; StorageDead(_4); return;`.
     - On unwind (`bb15 (cleanup)`), `switchInt(copy _18) -> [0: bb12, otherwise: bb14]`
       tests the same flag: if `_18 != 0`, `bb14 (cleanup)` executes
       `drop(_4) -> [return: bb12, unwind terminate(cleanup)]`, and `bb12 (cleanup)`
       terminates the unwind ramp with `resume;` (`TerminatorKind::UnwindResume`).
2. **Double-panic protection (`UnwindAction::Terminate(Reason::Cleanup)`):**
   Every `drop(...)` inside an `is_cleanup` block (`bb11` and `bb14`) carries
   `unwind terminate(cleanup)` rather than `unwind: bb...`, enforcing Rust's
   no-double-unwind abort invariant directly in the `TerminatorKind::Drop`
   unwind action.

---

### Finding 7: Stage 3 Verification Architecture Scaling — Unjoined Tree Deduction ($\Theta(2^K)$) vs. Block-Modular Join ($\Theta(K)$) vs. Total Reflection ($\Theta(1)$ Proof Term)

`Basis: execution, derived`

Executing `support/ReflectionVsSymExecBench.lean` via `support/run_lean_scaling_bench.py`
(`anneal-lean-run --mode file --concurrency 2`) across `v4.28.0-rc1`
(`3b0f2862196c6a8af9eb0025ee650252694013dd`), `v4.28.0`
(`7e01a1bf5c70fc6167d49c345d3bf80596e9a79b`), and `v4.34.1`
(`5045d0056413266e57c625dcd7c365b10e377c52`) yields the following empirical
scaling measurements on $K$-diamond CFGs and $N$-block straight-line chains:

#### Table 1: $K$-Diamond CFG Scaling Across Architectures A, B, and C (`v4.34.1` and `v4.28.0`)

| Architecture & Benchmark | Diamonds $K$ | DAG Objects (`Expr.numObjs`) | Unfolded Tree Nodes | `v4.34.1` Tactic + Elab (`ms`) | `v4.34.1` Kernel Typecheck (`ms`) | `v4.28.0` Tactic + Elab (`ms`) | `v4.28.0` Kernel Typecheck (`ms`) |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| **Arch A (Unjoined, canonical locals)** `archA_diamond1` | 1 | 216 | 3,963 | 19.28 | 2.53 | 22.16 | 3.87 |
| **Arch A (Unjoined, canonical locals)** `archA_diamond2` | 2 | 291 | 12,575 | 56.92 | 4.73 | 315.90 | 7.17 |
| **Arch A (Unjoined, canonical locals)** `archA_diamond4` | 4 | 445 | 78,647 | 388.10 | 10.30 | 678.72 | 15.00 |
| **Arch A (Unjoined, canonical locals)** `archA_diamond6` | 6 | 597 | 412,055 | 1,927.02 | 15.00 | 2,537.48 | 25.80 |
| **Arch A (Unjoined, canonical locals)** `archA_diamond8` | 8 | 749 | 2,022,167 | 9,562.86 | 24.10 | 11,500.70 | 36.40 |
| **Arch A (Unjoined, canonical locals)** `archA_diamond10` | 10 | — | $>8,000,000$ | **Timeout** (`>200k` hb) | — | **Timeout** (`>200k` hb) | — |
| **Arch A (Unjoined, uncanonicalized dead temp)** `archA_uncanon1` | 1 | 223 | 3,955 | 19.78 | 2.73 | 276.88 | 4.22 |
| **Arch A (Unjoined, uncanonicalized dead temp)** `archA_uncanon2` | 2 | 372 | 13,343 | 56.94 | 6.00 | 323.42 | 10.50 |
| **Arch A (Unjoined, uncanonicalized dead temp)** `archA_uncanon4` | 4 | 1,194 | 90,791 | 369.04 | 31.50 | 702.00 | 57.00 |
| **Arch A (Unjoined, uncanonicalized dead temp)** `archA_uncanon6` | 6 | 4,354 | 501,959 | 2,002.31 | 153.00 | 2,668.78 | 291.00 |
| **Arch B (`execNormal_join` + `StorageDead` canon)** `archB_diamond1` | 1 | 196 | 2,329 | 9.08 | 2.46 | 264.85 | 4.06 |
| **Arch B (`execNormal_join` + `StorageDead` canon)** `archB_diamond2` | 2 | 254 | 4,609 | 16.75 | 5.07 | 283.39 | 7.04 |
| **Arch B (`execNormal_join` + `StorageDead` canon)** `archB_diamond4` | 4 | 374 | 10,033 | 37.36 | 9.39 | 304.38 | 14.80 |
| **Arch B (`execNormal_join` + `StorageDead` canon)** `archB_diamond6` | 6 | 492 | 16,609 | 63.85 | 14.10 | 342.63 | 24.60 |
| **Arch B (`execNormal_join` + `StorageDead` canon)** `archB_diamond8` | 8 | 610 | 24,337 | 95.64 | 21.50 | 369.68 | 34.70 |
| **Arch B (`execNormal_join` + `StorageDead` canon)** `archB_diamond10` | 10 | 728 | 33,217 | 138.52 | 31.20 | 439.43 | 50.80 |
| **Arch C (Total Reflection `checkBodySym_sound`)** `archC_diamond1` | 1 | **30** | **59** | 5.80 | 2.86 | 258.64 | 5.77 |
| **Arch C (Total Reflection `checkBodySym_sound`)** `archC_diamond2` | 2 | **30** | **59** | 8.12 | 5.00 | 261.50 | 8.59 |
| **Arch C (Total Reflection `checkBodySym_sound`)** `archC_diamond4` | 4 | **30** | **59** | 16.00 | 12.40 | 268.90 | 19.00 |
| **Arch C (Total Reflection `checkBodySym_sound`)** `archC_diamond6` | 6 | **30** | **59** | 25.00 | 18.10 | 282.10 | 28.30 |
| **Arch C (Total Reflection `checkBodySym_sound`)** `archC_diamond8` | 8 | **30** | **59** | 35.70 | 26.10 | 295.20 | 43.80 |
| **Arch C (Total Reflection `checkBodySym_sound`)** `archC_diamond10` | 10 | **30** | **59** | 47.70 | 40.60 | 310.40 | 60.50 |

#### Table 2: Straight-Line $N$-Block Chain Scaling — Architecture B vs. Architecture C (`v4.34.1` and `v4.28.0`)

| Architecture & Benchmark | Chain Blocks $N$ | DAG Objects (`Expr.numObjs`) | Unfolded Tree Nodes | `v4.34.1` Tactic + Elab (`ms`) | `v4.34.1` Kernel Typecheck (`ms`) | `v4.28.0` Tactic + Elab (`ms`) | `v4.28.0` Kernel Typecheck (`ms`) |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| **Arch B (Per-Step Tactic Deduction)** `archB_chain16` | 16 | 474 | 20,121 | 99.83 | 8.95 | 376.42 | 15.50 |
| **Arch B (Per-Step Tactic Deduction)** `archB_chain32` | 32 | 858 | 64,633 | 272.11 | 24.80 | 586.57 | 40.00 |
| **Arch B (Per-Step Tactic Deduction)** `archB_chain64` | 64 | 1,626 | 227,385 | 862.90 | 70.90 | 1,272.73 | 118.00 |
| **Arch B (Per-Step Tactic Deduction)** `archB_chain128` | 128 | 3,162 | 847,801 | 2,996.25 | 258.00 | 3,736.89 | 418.00 |
| **Arch C (Total Reflection `checkBodySym_sound`)** `archC_chain16` | 16 | **30** | **59** | 15.70 | 9.12 | 271.10 | 17.10 |
| **Arch C (Total Reflection `checkBodySym_sound`)** `archC_chain32` | 32 | **30** | **59** | 37.60 | 24.50 | 298.70 | 44.20 |
| **Arch C (Total Reflection `checkBodySym_sound`)** `archC_chain64` | 64 | **30** | **59** | 112.00 | 77.30 | 383.00 | 119.00 |
| **Arch C (Total Reflection `checkBodySym_sound`)** `archC_chain128` | 128 | **30** | **59** | 365.00 | 265.00 | 662.00 | 438.00 |

Three structural conclusions follow directly from Tables 1 and 2:

1. **Why state canonicalization via `StorageDead` is mandatory at join points:**
   In `archA_diamondK` (where `StorageDead(1)` clears the branch-local temporary
   `local 1` to `none` on both arms), Lean's post-elaboration `share common exprs`
   pass can hash-cons identical continuation subtrees into `749` DAG objects at
   $K = 8$, even though the elaborator still constructs all `2,022,167` tree
   nodes in `9.56 s`. In `archA_uncanonK` (where `StorageDead(1)` is omitted so
   `local 1` retains different dead values along the $2^K$ paths), `share common exprs`
   **cannot** share the continuation subtrees: DAG size explodes (`223 -> 372 ->
   1,194 -> 4,354` at $K = 6$) and kernel type-checking time increases by
   **$10.2\times$** at $K = 6$ (`153.0 ms` vs. `15.0 ms` on `v4.34.1`, and
   `291.0 ms` vs. `25.8 ms` on `v4.28.0`).
2. **Why `execNormal_join` solves diamond blowup but still incurs tactic-tree
   overhead on long blocks:**
   Architecture B (`execNormal_diamond_step`, derived from `execNormal_join_eq`)
   adds exactly `59` DAG objects per diamond (`374 -> 492 -> 610 -> 728` for
   $K \in \{4, 6, 8, 10\}$), reducing $K = 8$ verification time from `9,639.6 ms`
   (Architecture A) to `117.1 ms` on `v4.34.1` (**$82.3\times$ speedup**).
   However, on straight-line chains (`archB_chain128`), applying constructor/step
   lemmas $N$ times embeds the state and CFG at every step (`3,162` DAG objects,
   `847,801` tree nodes) and spends `2,993.5 ms` in tactic execution on `v4.34.1`
   (`3,476.9 ms` on `v4.28.0`).
3. **Why Total Computational Reflection (`checkBodySym_sound`) dominates on
   decidable fragments:**
   Architecture C discharges every benchmark instance with a single 30-DAG-object
   application `checkBodySym_sound fuel cfg initState rfl`, reducing $N = 128$
   total verification time from `3,260.0 ms` (Architecture B) to `630.0 ms` on
   `v4.34.1` (**$5.17\times$ speedup**) and from `4,160.4 ms` to `1,100.0 ms` on
   `v4.28.0` (**$3.78\times$ speedup**).

---

### Finding 8: The Closure-Environment Kernel WHNF Pitfall (`Nat → Option Val` vs. `List (Option Val)`)

`Basis: source, execution, derived`

In `joshlf/anneal` (`trusted/lean/Trusted/MirSemantics.lean`, lines 89–114 at
commit `572f1e80580daa4b052ce5646bb675484d9bb957`), `MirState.locals` is
currently defined as a function `Nat → Option MirVal` updated via:

```lean
def updateLocal (locals : Nat → Option MirVal) (target : LocalIdx) (val : Option MirVal) :
    Nat → Option MirVal :=
  fun i => if i == target then val else locals i
```

Because a lambda abstraction `fun i => ...` is already in Weak Head Normal Form
(WHNF), Lean 4's kernel reducer (`lean::type_checker::whnf`) **never** simplifies
inside `updateLocal` when constructing `MirState`. After $N$ statement
executions, `s.locals` is a chain of $N$ nested lambda closures. Reading a
function argument or outer local initialized at function entry (`local 0`) at
step $k$ must beta-reduce and evaluate `if 0 == target_j` across all $k$ nested
closures, resulting in $\sum_{k=1}^{N} k = \Theta(N^2)$ kernel WHNF steps and an
$O(N)$-deep call stack inside the C++ kernel reducer.

By contrast, representing `MirState.locals` as a spine-strict `List (Option Val)`
of length $L$ (matching `local_decls.len()`) reconstructs the $L$-element list
spine at each update, bounding lookup depth by $L$ independent of step count $N$.

#### Table 3: Kernel WHNF Scaling — `ClosureLocals` (`Nat → Option Nat`) vs. `ListLocals` (`List (Option Nat)`) Over $L = 16$ Locals

| Representation & Theorem | Assignments $N$ | Default `maxRecDepth = 512` | `v4.34.1` Elab (`ms`) | `v4.34.1` Kernel Typecheck (`ms`) | `v4.28.0` Elab (`ms`) | `v4.28.0` Kernel Typecheck (`ms`) |
| :--- | ---: | :--- | ---: | ---: | ---: | ---: |
| **`ClosureLocals` (`Nat → Option Nat`)** `env_closure_20` | 20 | Pass | 30.60 | 13.00 | 284.80 | 20.70 |
| **`ClosureLocals` (`Nat → Option Nat`)** `env_closure_50` | 50 | Pass | 131.00 | 56.60 | 430.00 | 108.00 |
| **`ClosureLocals` (`Nat → Option Nat`)** `env_closure_100` | 100 | Pass | 495.01 | 214.00 | 831.00 | 424.00 |
| **`ClosureLocals` (`Nat → Option Nat`)** `env_closure_200` | 200 | **FAIL (`maxRecDepth`)** | 1,911.09 | 1,010.00 | 2,483.00 | 1,590.00 |
| **`ListLocals` (`List (Option Nat)`)** `env_list_20` | 20 | Pass | 23.96 | 22.00 | 275.90 | 27.20 |
| **`ListLocals` (`List (Option Nat)`)** `env_list_50` | 50 | Pass | 58.85 | 46.60 | 315.90 | 66.90 |
| **`ListLocals` (`List (Option Nat)`)** `env_list_100` | 100 | Pass | 118.02 | 94.20 | 381.00 | 155.00 |
| **`ListLocals` (`List (Option Nat)`)** `env_list_200` | 200 | **Pass** | **234.08** | **256.00** | **515.00** | **318.00** |

Doubling $N$ from $50 \to 100 \to 200$ under `ClosureLocals` multiplies kernel
type-checking time by **$3.78\times$** and **$4.72\times$** on `v4.34.1` (and
**$3.93\times$** and **$3.75\times$** on `v4.28.0`—textbook $\Theta(N^2)$), and
at $N = 200$ `ClosureLocals` fails outright under Lean's default
`maxRecDepth = 512` (`error: maximum recursion depth has been reached`). Under
spine-strict `ListLocals`, doubling $N$ from $50 \to 100 \to 200$ multiplies
kernel type-checking time by **$2.02\times$** and **$2.72\times$** on `v4.34.1`
(and **$2.32\times$** and **$2.05\times$** on `v4.28.0`—$\Theta(N)$ linear) and
succeeds under default `maxRecDepth = 512`.

## Boundaries

1. **Universal quantification over mathematical inputs requires combining
   Architectures B and C:**
   Architecture C (`checkBodySym_sound` via `rfl`) directly discharges concrete
   and finite-state abstract execution paths (including diamond joins over
   arbitrary boolean branch conditions when branch effects on live locals match
   or are abstracted). When a function's postcondition depends on arbitrary
   arithmetic relations over unbounded inputs (or loop invariants with
   unbounded trip counts), Stage 3 should use **hybrid reflection + modular cut
   rules**: run computational block/diamond reduction (`lowerBody` /
   `execBlockSym`) inside basic blocks and across simple diamonds, and invoke
   `execNormal_join` at loop headers and user-specified cut points where a Lean
   proof discharges the verification condition over symbolic `MirVal` terms.
2. **List-indexed basic block lookup at large block counts ($B \ge 128$):**
   In `ReflectionVsSymExecBench.lean`, `getBlock : List BasicBlock → Nat → Option BasicBlock`
   traverses the block list linearly in the block index (`O(B)` per block transition,
   yielding `O(N * B)` across an $N$-block chain). For functions with $>100$
   basic blocks, representing the lowered block table as a balanced binary trie
   (pos/bit-indexed tree) or `Array` reduces per-block lookup from $O(B)$ to
   $O(\log B)$ in kernel WHNF reduction.
3. **Target-architecture specificity of `PtrMetadata` types:**
   For slices (`&[T]`, `&mut [T]`, `*const [T]`), `UnOp::PtrMetadata` produces
   `usize`. For trait objects (`&dyn Trait`), `UnOp::PtrMetadata` produces a
   vtable pointer (`DynMetadata<dyn Trait>`), which is outside the slice/array
   scope of Finding 5.

## Evidence

- **Primary compiler sources (`rust-lang/rust`, commit `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):**
  - `compiler/rustc_mir_transform/src/lib.rs` (lines 569–710): pass pipeline
    definitions for `run_analysis_cleanup_passes`,
    `run_runtime_lowering_passes`, `run_runtime_cleanup_passes`, and
    `run_optimization_passes`.
  - `compiler/rustc_mir_transform/src/cleanup_post_borrowck.rs` (lines 32–63):
    post-borrowck erasure of `BorrowKind::Fake(_)` and pointer-coercion cast
    lowering.
  - `compiler/rustc_mir_transform/src/remove_place_mention.rs` (lines 1–27) and
    `compiler/rustc_mir_transform/src/simplify.rs` (lines 128–135, 305–328):
    exact behavior of `-Z mir-preserve-ub`.
  - `compiler/rustc_mir_build/src/thir/cx/expr.rs` (lines 1457–1470),
    `compiler/rustc_middle/src/mir/pretty.rs` (lines 1146–1171), and
    `compiler/rustc_mir_transform/src/instsimplify.rs` (lines 159–166):
    emission, pretty-printer formatting, and `WithRetag::No` optimization of
    `MutBorrowKind::TwoPhaseBorrow`.
  - `compiler/rustc_middle/src/mir/syntax.rs` (lines 123–133) vs.
    `compiler/rustc_mir_transform/src/validate.rs` (lines 1015–1096): validation
    of `AggregateKind::Adt` in `Runtime(PostCleanup)`.
  - `compiler/rustc_mir_build/src/builder/expr/as_place.rs` (lines 668–724) and
    `compiler/rustc_mir_transform/src/lower_slice_len.rs` (lines 10–66):
    lowering of array/slice lengths to `UnOp::PtrMetadata` and
    `RawPtrKind::FakeForPtrMetadata`, and deferred lowering of `slice::len`.
  - `compiler/rustc_mir_transform/src/elaborate_drops.rs` (lines 400–455):
    synthesis of stack `bool` drop flags and `is_cleanup` unwind blocks.
- **Primary Anneal sources (`joshlf/anneal`, commit `572f1e80580daa4b052ce5646bb675484d9bb957`):**
  - `trusted/rustc-capture/src/extract.rs` (lines 55–432): current Stage 1 MIR
    extraction coverage and fail-closed rejection points.
  - `trusted/lean/Trusted/MirSemantics.lean` (lines 89–165): `MirState.locals`
    and `updateLocal` closure representation.
- **Reproducible package artifacts (`support/`):**
  - `support/postcleanup_constructs_specimen.rs`: self-contained Rust specimen
    defining 9 probe functions across all 5 construct families.
  - `support/probe_postcleanup_constructs.py`: automated driver that compiles
    `support/postcleanup_constructs_specimen.rs` across `nightly-2026-03-19` and
    `nightly-2026-05-31` under default flags, `-Z mir-preserve-ub`, and `-O`,
    asserts 15 structural invariants, and writes
    `support/postcleanup_constructs_results.json`.
  - `support/postcleanup_constructs_results.json`: complete parsed counts,
    locals, basic blocks, back-edges, and raw MIR dumps for all 9 specimen
    functions across both `rustc` toolchains and all 4 dump modes.
  - `support/ReflectionVsSymExecBench.lean`: self-contained, zero-`sorry` Lean 4
    benchmark file implementing `ExecNormal`, `ExecPath`, `execNormal_branch_split`,
    `execNormal_join`, `execNormal_diamond_step`, `checkBodySym`,
    `checkBodySym_sound`, and the `ClosureLocals` vs. `ListLocals` kernel WHNF
    benchmarks.
  - `support/run_lean_scaling_bench.py`: automated driver executing
    `support/ReflectionVsSymExecBench.lean` and boundary probes via
    `anneal-lean-run --mode file --concurrency 2` across `v4.28.0-rc1`,
    `v4.28.0`, and `v4.34.1`, writing `support/lean_scaling_results.json`.
  - `support/lean_scaling_results.json`: complete per-theorem `dag_objs`,
    `tree_nodes`, `tactic_execution_ms`, `elaboration_ms`, `type_checking_ms`,
    and boundary probe diagnostics across all three Lean 4 toolchains.

## Revalidation

Run both verification scripts from the package directory:

```bash
python3 support/probe_postcleanup_constructs.py
python3 support/run_lean_scaling_bench.py
```

Or run the standalone Lean 4 benchmark file directly under `anneal-lean-run`:

```bash
anneal-lean-run --mode file --concurrency 2 -- \
  elan run leanprover/lean4:v4.28.0 lean -Dprofiler=true -Dprofiler.threshold=1 \
  support/ReflectionVsSymExecBench.lean

anneal-lean-run --mode file --concurrency 2 -- \
  elan run leanprover/lean4:v4.34.1 lean -Dprofiler=true -Dprofiler.threshold=1 \
  support/ReflectionVsSymExecBench.lean
```

Revalidate this report when:
- `joshlf/anneal` upgrades its pinned `rustc` nightly beyond `1.98.0-nightly`
  (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`) or changes its captured MIR phase
  from `MirPhase::Runtime(RuntimePhase::PostCleanup)`.
- `joshlf/anneal` upgrades its pinned Lean 4 toolchain beyond `v4.34.1`
  (`5045d0056413266e57c625dcd7c365b10e377c52`) or refactors `MirState.locals` in
  `trusted/lean/Trusted/MirSemantics.lean`.
