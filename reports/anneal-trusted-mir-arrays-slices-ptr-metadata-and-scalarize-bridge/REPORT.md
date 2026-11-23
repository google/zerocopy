# Bounded Arrays `[T; N]`, Wide-Pointer Slices `&[T]` / `*const [T]`, `UnOp::PtrMetadata`, `LowerSliceLenCalls`, `GVN` Metadata Folding, and Certified `SliceScalarize` + `ArrayScalarize` Reduction Into `Anneal`'s `Trusted.MirSemantics`

## Summary

In `Anneal`'s unmodified `mirProfileVersion = 1` TCB (`Trusted/MirAst.lean` and `Trusted/MirSemantics.lean`, `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`), `MirTy` admits only booleans, fixed/pointer-width integers, `.unit`, `.never`, fieldless `.enum`, `.tuple`, `.ref`, and `.rawPtr`—with `UnOp.ptrMetadata` halting as `.error .unsupported`, `ProjectionElem` lacking `Index` / `ConstantIndex` / `Subslice`, `Rvalue` lacking `Aggregate(Array)` / `Repeat` / `Unsize`, and `TerminatorKind.assert` (`BoundsCheck`) unsupported. Across `google/zerocopy@a68641199cdfa99f96cb62f0cde921c9d36bfb22` (`0.8.64`, `rustc 1.102.0-nightly`, `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `4,859` `Runtime(PostCleanup)` MIR bodies and `4,507` `Runtime(Optimized)` MIR bodies; `support/zerocopy_arrays_slices_index_subslice_and_ptrmetadata_census.json`), live MIR dumps confirm that `Rvalue::Len` has been completely removed from `rustc_middle::mir::syntax` in favor of `UnOp::PtrMetadata`: `LowerSliceLenCalls` (`compiler/rustc_mir_transform/src/lower_slice_len.rs`) rewrites `16 / 4,482` `zerocopy` crate bodies, driving `UnOp::PtrMetadata` from `3 -> 49` (`+46`), array-to-slice `PointerCoercion::Unsize` from `0 -> 12`, and `AggregateKind::RawPtr` from `0 -> 51` in `Runtime(Optimized)` MIR while leaving `4` dynamic `AssertKind::BoundsCheck` + `ProjectionElem::Index` sites (`DstLayout::for_repr_c_struct` in `src/layout.rs:1153` and `hash_name` in `src/util/macro_util.rs:479`).

Directly importing unmodified `Trusted.MirAst` and `Trusted.MirSemantics` with zero surrogate AST or `Val` types (`support/AnnealTrustedMirArraysSlicesPtrMetadataAndScalarize.lean`, `36210` lines, `1939606` bytes, SHA-256 `c65c6f526870a0b48a6993f3c60fdd1fd21fb5e5e1471e63e7cb8aa265f341be`), the mechanized development `VrustcFormal.F1_15` establishes five core kernel-checked theorems, eleven sharpness counterexamples (`CE1`–`CE11`), and an end-to-end 4-pass compilation witness executing directly inside unmodified `Trusted.MirSemantics`:

1. **Exact conservative extension `M_arrslice` over unmodified `Trusted.MirAst.Program` (`arrSlice_conservative_extension_exact`).** Conservatively extending `Trusted.MirSemantics` with fixed-size internal array locals `.array elemTy len` (`0 ≤ len ≤ 64`), wide-pointer slice views `.sliceView elemTy` carrying `(backing ∈ {.dangling, .arrayLocal a}, start, len)` with `start + len < 2^64`, array construction (`aggregateArray`, `repeatArray` evaluating its operand even at `len = 0`), `unsizeArrayToSlice`, `sliceFromRawParts` (`NonNull::dangling()`), `subslice` (`fromEnd = false` and `fromEnd = true`), `ptrMetadata`, `sliceLenCall`, `boundsCheckArray` / `boundsCheckSlice`, and constant/dynamic element reads and writes preserves 1-step lockstep execution (`evalStepArrSlice (embedBaseProgram p) c (embedArrSliceState s) = liftStepResultArrSlice (evalStep p c s)`) and exact bidirectional (`↔`) semantic equivalence across `WellFormed`, `Behavior`, `ReachesResult (.fault k)`, `Diverges`, and `SatisfiesPost` for every unmodified `Trusted.MirAst.Program`. `Basis: execution (Lean kernel)`
2. **Bidirectional soundness of `LowerSliceLenCalls` & intra-block `GVN` `PtrMetadata(Unsize)` folding (`lowerSliceLenCalls_and_gvnPtrMetadata_sound_bidirectional_iff`).** Replacing `Terminator.sliceLenCall dst sliceLoc target` with `Stmt.ptrMetadata dst sliceLoc` + `goto target` (`checkLowerSliceLenCalls`) and constant-folding `ptrMetadata dst sLoc -> dst = const len_usize` across any intra-block `unsizeArrayToSlice sLoc arrLoc` window free of intervening writes or storage transitions on `sLoc` (`checkGvnFoldPtrMetadata`) both preserve full `FullSemanticEquivArrSlice pSrc pTgt` (`↔` across all five verification judgments, proved strictly under `[propext]` with `0` `Quot.sound` and `0` `Classical.choice`). `Basis: source + execution (Lean kernel)`
3. **Wide-pointer dangling metadata validity vs. dereference UB, `BoundsCheck` precedence, and `Subslice` composition (`danglingSlice_metadata_valid_deref_ub_and_boundsCheck_precedes_deref`).** Matching live native + Miri Stacked/Tree Borrows behavior (`E3-90` Probe 3, where `ptr::metadata(ptr::slice_from_raw_parts(NonNull::<u32>::dangling().as_ptr(), 100))` returns `100` cleanly while `(*raw)[0]` faults immediate UB): (i) `ptrMetadata` on any live `.dangling` slice of length `len < 2^64` succeeds and writes `len_usize`; (ii) `readSliceElem` on any `.dangling` slice deterministically faults `.fault .undefined` for all `idx < 2^64`; (iii) `boundsCheckSlice` branches on `idx < sv.len` without dereferencing or faulting on `.dangling` backing; and (iv) sequential from-start subslices `(f₁, t₁)` then `(f₂, t₂)` compose additively to `(f₁ + f₂, f₁ + t₂)` while preserving `backing` and `start' + len' < 2^64`. `Basis: execution (Miri + Lean kernel)`
4. **Zero-block-split `SliceScalarize` + `SwitchInt`-dispatched `ArrayScalarize` reducing 100% into unmodified `Trusted.MirSemantics` (`arraySliceScalarize_reduces_to_trusted_mir`).** Any finite `ArrSliceOptTrace` certified by `checkArrSliceToTrustedMir trace pSrc pMir = true` first eliminates all `.sliceView` locals in a body via 4 base locals `(liveLoc, tagLoc, startLoc, lenLoc)` + 5 scratch locals with **zero basic-block splits** (encoding subslice/index bounds and `.dangling` tag traps via branchless `BinOp.subUnchecked` underflow gadgets), and then eliminates each `.array elemTy len` local into `liveLoc` + `elem_0 .. elem_{len-1}` + scratch locals + trailing `SwitchInt` dispatch & `.unreachable` trap blocks while preserving all original `BasicBlockId`s `0 .. B - 1`. Both `applySliceScalarize_sound` (`Slice3d`) and `applyArrayScalarize_sound` (`Slice4c`) are proved strictly under `[propext]`, and the full trace lowers `M_arrslice` bidirectionally (`↔`) into unmodified `Trusted.MirSemantics` with `0` `Classical.choice`. `Basis: execution (Lean kernel)`
5. **Vertical pipeline composition, eleven sharpness witnesses (`CE1`–`CE11`), Stage 5 blind specification audit (`PASS`), and 6-gate multi-kernel replay (`arraySlicePipeline_then_optPipeline_vc_transport`).** Composing `checkArrSliceToTrustedMir` with any downstream `FullSemanticEquivBase pMir pOpt` (such as `F1-5`–`F1-9` MIR optimizations) transports all five verification judgments bidirectionally (`↔`) onto `pOpt`. All `26` public theorems (`23 / 26` strictly `[propext]`, `3 / 26` `[propext, Quot.sound]`, `0` `Classical.choice`, `0` `sorryAx`, `AUDIT_MAP1 total=2224 pub=933 priv=1291 bad=0`, `pub_surface_clean = true`) compile on `Lean v4.34.1` (`-M4096 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`) in **`308.8763 s` / `2060.48 MB` RSS**, pass unmodified `TrustedBoundary.lean` `"preflight"` (`ok = true`) and Pass 1 `"audit"` (`replayedDeclarations = 3805`, `reachableDeclarations = 4707`, `axioms = ["propext", "Quot.sound"]`, `replay = true`), compile on `Lean v4.35.0` in **`255.918 s` / `2000.66 MB` RSS**, export via `lean4export 3.1.0` (`1369294` NDJSON lines, `71853391` bytes), and pass independent Rust external kernel verification under `nanoda_bin 0.4.19` (`3147` declarations in **`30.9984 s` / `124.65 MB` RSS`, negative `permitted_axioms: []` control rejected at `rc = 1`). `Basis: execution`

## Applicability

- **Primary formal verification target (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, citing `rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd`):** Unmodified `Trusted.MirAst.Program` and `Trusted.MirSemantics` (`mirProfileVersion = 1`, `pointerWidthBits = 64`), providing an untrusted, 0-TCB-addition `theory/` lowering bridge that compiles bounded internal arrays `[T; N]`, wide-pointer slice views `&[T]` / `*const [T]`, `UnOp::PtrMetadata`, `LowerSliceLenCalls`, `GVN` metadata folding, `ConstantIndex`, `Subslice`, and `BoundsCheck` + `Index` accesses directly into Anneal's base trusted MIR evaluator.
- **Upstream compiler source & live execution census:** `rust-lang/rust@49d734536222bf28bb6d07d885b3a81d145981da` (`compiler/rustc_mir_transform/src/{lower_slice_len.rs, gvn.rs}`, `compiler/rustc_middle/src/mir/syntax.rs`) and `rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`rustc 1.102.0-nightly` + `miri 0.1.0`, `2026-11-11`, `LLVM 23.1.5`) evaluated on `google/zerocopy@a68641199cdfa99f96cb62f0cde921c9d36bfb22` (`0.8.64`) and targeted native + Miri Stacked/Tree Borrows probes (`support/zerocopy_arrays_slices_index_subslice_and_ptrmetadata_census.json`).
- **Independent Lean 4 kernel, exporter, and external Rust verifier pins:** `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`), `leanprover/lean4@eb6cafb7290e8bd5f2937522d8d804f58f02bafc` (`v4.35.0`), `leanprover/lean4export@5a9a355dc6c5fd82b69058d433e2ae2e8dfbf8fe` (`3.1.0`), and `ammkrn/nanoda_lib@f55114afa24efe39e007f62d31b7e8ac4243f2a6` (`0.4.19`).
- **Intended consumers:** Proof engineers verifying `zerocopy` byte-order array constants, `hash_name` `[u8; 16]` indexing loops, slice length/bounds-check idioms, and slice pattern matching (`ConstantIndex` / `Subslice`) without expanding Anneal's trusted kernel surface, as well as compiler engineers auditing `LowerSliceLenCalls` and `GVN` `PtrMetadata` folding.

## Findings

### 1. First-Customer `zerocopy 0.8.64` Array, Slice, `LowerSliceLenCalls`, & `PtrMetadata` Census (`E3-90`)

`Basis: execution (support/zerocopy_arrays_slices_index_subslice_and_ptrmetadata_census.json) + source (rust-lang/rust@49d734536222bf28bb6d07d885b3a81d145981da, google/zerocopy@a68641199cdfa99f96cb62f0cde921c9d36bfb22)`

Compiling `zerocopy 0.8.64` (`src/lib.rs`) with `rustc 1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`) at `-Copt-level=2` across `Runtime(PostCleanup)`, `LowerSliceLenCalls` (before/after), and `Runtime(Optimized)` establishes the exact shape of array, slice, and wide-pointer metadata operations in modern `rustc` MIR:

| MIR Metric (`google/zerocopy@a68641199cdfa99f96cb62f0cde921c9d36bfb22`, `0.8.64`) | `Runtime(PostCleanup)` | `Runtime(Optimized)` | Net Delta (`PostCleanup -> Optimized`) |
| :--- | :---: | :---: | :---: |
| Total MIR bodies dumped | `4,859` | `4,507` | `-352` |
| Legacy `Rvalue::Len` (removed from `rustc_middle::mir::syntax`) | `0` | `0` | `0` |
| Unlowered `core::slice::<impl [T]>::len` `Call` terminators | `22` | `0` | `-22` (`100%` lowered) |
| `Rvalue::UnaryOp(UnOp::PtrMetadata, ...)` | `3` | `49` | `+46` (`16.3x`) |
| `Rvalue::Repeat([op; N])` (`[0_u8; 4/8/16]`, `[u8::MAX; 4/8/16]`) | `18` | `1` | `-17` (const-folded into consts, `hash_name` `[0_u8; 16]` retained) |
| `PointerCoercion::Unsize` (`&[T; N] -> &[T]`, array-to-slice) | `0` | `12` | `+12` (inlined `byteorder::*` `Hash::hash`) |
| `PointerCoercion::Unsize` (`&T -> &dyn fmt::Debug`) | `19` | `19` | `0` |
| `Rvalue::Aggregate(AggregateKind::RawPtr, [data, meta])` | `0` | `51` | `+51` (inlined `slice::from_raw_parts{,_mut}`) |
| `ProjectionElem::Index` (`(*slice)[idx]` / `arr[idx]`) | `4` | `4` | `0` |
| `AssertKind::BoundsCheck` terminators | `4` | `4` | `0` |

Key architectural findings from `E3-90` (`support/zerocopy_arrays_slices_index_subslice_and_ptrmetadata_census.json`):

1. **Complete replacement of `Rvalue::Len` by `UnOp::PtrMetadata`:** In `rustc 1.102.0-nightly` (`compiler/rustc_middle/src/mir/syntax.rs:1363-1488`), `Rvalue::Len` no longer exists. Slice length queries emitted during pattern-match MIR building (`for_repr_c_struct`, `hash_name`) appear immediately as `UnOp::PtrMetadata` in `PostCleanup` (`3` sites), while explicit `.len()` method calls (`22` sites across `16` `zerocopy` functions: `IntoBytes-write_to`, `IntoBytes-write_to_prefix`, `IntoBytes-write_to_suffix`, `TryFromBytes-try_read_from_suffix`, `byte_slice-SplitByteSlice-split_at`, `byte_slice-{impl#8}-split_at_unchecked`, `layout-{impl#4}-for_repr_c_struct`, `ref-{impl#0}-sized_from`, `ref-{impl#1}-sized_from_prefix`, `ref-{impl#1}-sized_from_suffix`, `ref-{impl#3}-from_prefix`, `ref-{impl#4}-from_bytes_with_elems`, `ref-{impl#5}-from_prefix_with_elems`, `try_read_from`, `util-copy_unchecked`, `util-macro_util-hash_name`) are rewritten by `LowerSliceLenCalls` (`lower_slice_len.rs`) from two-block `Call` terminators into intra-block `_dst = PtrMetadata(move _slice); goto -> bb_next`, and inlining `slice::len` / `PtrInner::meta` expands `UnOp::PtrMetadata` to `49` sites in `Runtime(Optimized)` MIR.
2. **Surviving bounds-checked array & slice loops in `zerocopy`:** Exactly `4` `AssertKind::BoundsCheck` + `ProjectionElem::Index` sites survive full `-Copt-level=2` MIR optimization across `zerocopy`: `1` slice-indexing site in `DstLayout::for_repr_c_struct` (`src/layout.rs:1153`: `_7 = PtrMetadata(copy _3); _10 = Lt(copy _9, copy _7); assert(move _10, ...) -> bb3; _8 = copy (*_3)[_9]`) and `3` slice/array indexing sites in `util::macro_util::hash_name` (`src/util/macro_util.rs:479`, indexing both input `&str`/`&[u8]` and local `_5 = [const 0_u8; 16]`).
3. **Slice pattern matching (`ConstantIndex` & `Subslice`) and `NonNull::dangling()` wide pointers (`E3-90` Probes 2–3):**
   - `let [head, mid @ .., tail] = slice` lowers to `Ge(PtrMetadata(copy _1), 2) -> switchInt`, followed by `(*_1)[0 of 2]` (`ConstantIndex { offset: 0, min_length: 2, from_end: false }`), `&(*_1)[1:-1]` (`Subslice { from: 1, to: 1, from_end: true }`), `PtrMetadata(mid)`, and `(*_1)[-1 of 2]` (`ConstantIndex { offset: 1, min_length: 2, from_end: true }`), executing identically (`S0=(0,0,0) S1=(0,0,0) S2=(10,0,20) S5=(1,3,5)`) natively and under Miri Stacked Borrows and `-Zmiri-tree-borrows`.
   - `ptr::slice_from_raw_parts(NonNull::<u32>::dangling().as_ptr(), 100)`: reading `ptr::metadata(raw)` returns `NONZERO_META=100` (`rc = 0` natively, Miri SB, and Miri TB), whereas dereferencing `unsafe { (*raw)[0] }` passes the `0 < 100` `BoundsCheck` (`Lt(0, PtrMetadata(raw))`) and then faults immediate UB (`attempting to access 4 bytes, but got 0x4[noalloc] which is a dangling pointer`, `rc = 1` in Miri SB/TB, `SIGSEGV` `rc = -11` natively).

Verbatim `LowerSliceLenCalls` before/after MIR excerpt from `DstLayout::for_repr_c_struct` (`src/layout.rs:1153`, `support/zerocopy_arrays_slices_index_subslice_and_ptrmetadata_census.json`):

```mir
// MIR for `layout::<impl at <tmp>/zerocopy/src/layout.rs:877:1: 877:15>::for_repr_c_struct` before LowerSliceLenCalls

fn layout::<impl at <tmp>/zerocopy/src/layout.rs:877:1: 877:15>::for_repr_c_struct(_1: Option<NonZero<usize>>, _2: Option<NonZero<usize>>, _3: &[layout::DstLayout]) -> layout::DstLayout {
    debug repr_align => _1;
    debug repr_packed => _2;
    debug fields => _3;
    let mut _0: layout::DstLayout;
    let mut _4: layout::DstLayout;
    let mut _5: std::option::Option<std::num::NonZero<usize>>;
    let _7: ();
    let mut _8: ();
    let mut _9: bool;
    let mut _10: usize;
    let mut _11: usize;
    let mut _12: &[layout::DstLayout];
    let _14: usize;
    let mut _15: usize;
    let mut _16: bool;
    let mut _17: layout::DstLayout;
    let mut _18: layout::DstLayout;
    let mut _19: layout::DstLayout;
    let mut _20: std::option::Option<std::num::NonZero<usize>>;
    let mut _21: !;
    let _22: ();
    let mut _23: !;
    let mut _24: layout::DstLayout;
    let mut _25: layout::DstLayout;
    scope 1 {
        debug layout => _4;
        let mut _6: usize;
        scope 2 {
            debug i => _6;
            scope 3 {
                scope 4 {
                    debug field => _13;
                }
                scope 5 {
                    let _13: layout::DstLayout;
                }
            }
        }
    }

    bb0: {
        StorageLive(_4);
        StorageLive(_5);
        _5 = copy _1;
        _4 = layout::DstLayout::new_zst(move _5) -> [return: bb1, unwind continue];
    }

    bb1: {
        StorageDead(_5);
        StorageLive(_6);
        _6 = const 0_usize;
        StorageLive(_7);
```

```mir
// MIR for `layout::<impl at <tmp>/zerocopy/src/layout.rs:877:1: 877:15>::for_repr_c_struct` after LowerSliceLenCalls

fn layout::<impl at <tmp>/zerocopy/src/layout.rs:877:1: 877:15>::for_repr_c_struct(_1: Option<NonZero<usize>>, _2: Option<NonZero<usize>>, _3: &[layout::DstLayout]) -> layout::DstLayout {
    debug repr_align => _1;
    debug repr_packed => _2;
    debug fields => _3;
    let mut _0: layout::DstLayout;
    let mut _4: layout::DstLayout;
    let mut _5: std::option::Option<std::num::NonZero<usize>>;
    let _7: ();
    let mut _8: ();
    let mut _9: bool;
    let mut _10: usize;
    let mut _11: usize;
    let mut _12: &[layout::DstLayout];
    let _14: usize;
    let mut _15: usize;
    let mut _16: bool;
    let mut _17: layout::DstLayout;
    let mut _18: layout::DstLayout;
    let mut _19: layout::DstLayout;
    let mut _20: std::option::Option<std::num::NonZero<usize>>;
    let mut _21: !;
    let _22: ();
    let mut _23: !;
    let mut _24: layout::DstLayout;
    let mut _25: layout::DstLayout;
    scope 1 {
        debug layout => _4;
        let mut _6: usize;
        scope 2 {
            debug i => _6;
            scope 3 {
                scope 4 {
                    debug field => _13;
                }
                scope 5 {
                    let _13: layout::DstLayout;
                }
            }
        }
    }

    bb0: {
        StorageLive(_4);
        StorageLive(_5);
        _5 = copy _1;
        _4 = layout::DstLayout::new_zst(move _5) -> [return: bb1, unwind continue];
    }

    bb1: {
        StorageDead(_5);
        StorageLive(_6);
        _6 = const 0_usize;
        StorageLive(_7);
```

---

### 2. Operational Semantics of `M_arrslice` Conservatively Extending `Trusted.MirSemantics`

`Basis: execution (Lean kernel, support/AnnealTrustedMirArraysSlicesPtrMetadataAndScalarize.lean)`

`VrustcFormal.F1_15` defines `M_arrslice` directly over unmodified `Trusted.MirAst` and `Trusted.MirSemantics` (`prelude`, `import Trusted.MirAst`, `import Trusted.MirSemantics`), reusing base `Val`, `MirTy`, `LocalSlot`, `Query`, `TerminalOut`, `FaultKind`, `evalBinOp`, `evalUnOp`, `evalConstLit`, `evalSwitchBranches`, and `evalBoolSwitchBranches` verbatim without modification.

#### 2.1 `ArrSliceProgram` AST, Runtime Slots (`ArrSliceSlot`), and Wide-Pointer `SliceViewVal`

- **Local declarations (`ArrSliceLocalDecl`):**
  - `.base (ty : MirTy)` — any base `Trusted.MirAst.MirTy` (`isSupportedScalarOrUnitTy` in signature slots `0 .. argumentCount` and internal base locals).
  - `.array (elemTy : MirTy) (len : Nat)` — internal fixed-size array `[elemTy; len]` (`idx > argumentCount`, `isSupportedScalarOrUnitTy elemTy`, `0 ≤ len ≤ 64`).
  - `.sliceView (elemTy : MirTy)` — internal wide-pointer slice view `&[elemTy]` / `*const [elemTy]` (`idx > argumentCount`, `isSupportedScalarOrUnitTy elemTy`).
- **Wide-pointer slice representation (`SliceViewVal`):** Carries `(backing : SliceBacking, start : Nat, len : Nat)` where `SliceBacking` is either `.dangling` (modeling `NonNull::dangling()` raw slices with no allocation provenance) or `.arrayLocal (arrLoc : LocalId)` (referencing internal array local `arrLoc`). Every reachable initialized `SliceViewVal` maintains the inductive `usize` span invariant `sv.start + sv.len < 2^64` (`maxUsize`).
- **Runtime slot lattice (`ArrSliceSlot`):**
  - `.baseSlot (s : LocalSlot)` — 1-for-1 base `Trusted.MirSemantics` slot.
  - `.arrDead` / `.liveArray (elems : List (Option Val))` — per-element initialization tracking (`initElemOptVal elemTy` initializes `.unit` and 1-variant ZST `.enum` slots to `some v` immediately upon entry / `StorageLive`, and non-ZST scalars to `none`, matching `Trusted.MirSemantics.liveUninitSlot` 1-for-1).
  - `.sliceDead` / `.liveSlice (view : Option SliceViewVal)` — tracks dead storage vs. live uninitialized (`none`) vs. live initialized wide pointer (`some sv`).

Exact `evalSubsliceVal` and `evalSliceConstRelIdx` definitions (`support/AnnealTrustedMirArraysSlicesPtrMetadataAndScalarize.lean`):

```lean
/-- Pure subslice bounds & view calculation (`ProjectionElem::Subslice`). -/
noncomputable def evalSubsliceVal (sv : SliceViewVal)
    (fromIdx toIdx : Nat) (fromEnd : Bool) : Except FaultKind SliceViewVal :=
  if !Nat.blt (sv.start + sv.len) maxUsize then
    .error .unsupported
  else if !fromEnd then
    if Nat.ble fromIdx toIdx && Nat.ble toIdx sv.len then
      .ok { backing := sv.backing, start := sv.start + fromIdx, len := toIdx - fromIdx }
    else
      .error .undefined
  else
    if Nat.ble (fromIdx + toIdx) sv.len then
      .ok {
        backing := sv.backing
        start := sv.start + fromIdx
        len := sv.len - (fromIdx + toIdx)
      }
    else
      .error .undefined

/-- Pure relative-index calculation for `ProjectionElem::ConstantIndex`. -/
noncomputable def evalSliceConstRelIdx (len offset minLen : Nat)
    (fromEnd : Bool) : Except FaultKind Nat :=
  if !Nat.ble minLen len then
    .error .undefined
  else if !fromEnd then
    if Nat.blt offset len then .ok offset else .error .undefined
  else
    if Nat.blt 0 offset && Nat.ble offset len then
      .ok (len - offset)
    else
      .error .undefined
```

Key operational rules enforced in `evalArrSliceStmt` and `evalArrSliceTerm`:

- **Zero-length `repeatArray` operand evaluation (`CE7`):** `.repeatArray arrLocal op` evaluates `op` via `evalArrSliceTypedOperand` *before* checking `len` or replicating `v` `len` times, so `[uninit_u32; 0]` deterministically faults `.fault .undefined` just as in Rust MIR, whereas `[42_u32; 4]` populates all 4 slots cleanly.
- **Conservative element move deinitialization (`CE6`):** `.readArrayConst dst arr idx true` resets `elems[idx]` to `initElemOptVal elemTy` (`none` for non-ZST scalars, `some .unit` for ZSTs), faulting `.fault .undefined` on a second move of a `u32` element while permitting repeated moves out of `[(); 3]`.
- **Dangling metadata validity vs. dereference & post-`StorageDead` UB (`Theorem 3`, `CE3`, `CE5`):** `.ptrMetadata dst sLoc` reads `sv.len` without inspecting `sv.backing` or array liveness (succeeding on both `.dangling` slices of length `100` and slices whose backing array was killed by `StorageDead`), whereas `.readSliceElem` and `.readSliceConst` check slice bounds *first* and then require `sv.backing = .arrayLocal arrLoc` with `arrLoc` currently `.liveArray elems` (faulting `.fault .undefined` on `.dangling` or `.arrDead`).
- **`BoundsCheck` precedes dereference (`Theorem 3`, `CE1`):** `.boundsCheckSlice sLoc idxOp inBoundsBb panicBb` evaluates `idxOp` and branches to `if idx < sv.len then inBoundsBb else panicBb` without dereferencing `sv.backing`.

---

### 3. Four-Pass Certified Lowering Pipeline Into Unmodified `Trusted.MirSemantics`

`Basis: execution (Lean kernel, support/AnnealTrustedMirArraysSlicesPtrMetadataAndScalarize.lean)`

#### 3.1 Pass 1 (`LowerSliceLenCalls`) & Pass 2 (`GvnFoldPtrMetadata`)

```lean
/-! ### Pass 1: `LowerSliceLenCalls` (`compiler/rustc_mir_transform/src/lower_slice_len.rs`) -/

/-- Replace `sliceLenCall dst sliceLoc target` in block `(bodyId, bbIdx)` with
`ptrMetadata dst sliceLoc` followed by `goto target`. -/
noncomputable def applyLowerSliceLenCalls (bodyId : DefId)
    (bbIdx : BasicBlockId) (pSrc : ArrSliceProgram) :
    Option ArrSliceProgram :=
  match Trusted.MirSemantics.getElem? pSrc.bodies bodyId with
  | none => none
  | some body =>
    match Trusted.MirSemantics.getElem? body.basicBlocks bbIdx with
    | none => none
    | some bb =>
      match bb.terminator with
      | .sliceLenCall dst sliceLoc target =>
        let bbTgt : ArrSliceBlock := {
          bb with
          statements := bb.statements ++ [.ptrMetadata dst sliceLoc]
          terminator := .baseTerm (.goto target)
        }
        match setElem? body.basicBlocks bbIdx bbTgt with
        | none => none
        | some bbsTgt =>
          match setElem? pSrc.bodies bodyId { body with basicBlocks := bbsTgt } with
          | none => none
          | some bodiesTgt => some { pSrc with bodies := bodiesTgt }
      | _ => none

noncomputable def checkLowerSliceLenCalls (bodyId : DefId)
    (bbIdx : BasicBlockId) (pSrc pTgt : ArrSliceProgram) : Bool :=
  match applyLowerSliceLenCalls bodyId bbIdx pSrc with
  | some pOut => arrSliceProgramEq pOut pTgt
  | none => false

/-! ### Pass 2: `GvnFoldPtrMetadata` (`compiler/rustc_mir_transform/src/gvn.rs` + `E3-85`) -/

/-- Whether `stmt` may write or alter the storage state of `sliceLocal`. -/
noncomputable def stmtModifiesSlice (sliceLocal : LocalId) :
    ArrSliceStmt → Bool
  | .baseStmt (.storageLive id) | .baseStmt (.storageDead id) =>
    Nat.beq id sliceLocal
  | .unsizeArrayToSlice s _ | .sliceFromRawParts s _ | .subslice s _ _ _ _ =>
    Nat.beq s sliceLocal
  | _ => false

/-- Intra-block `GVN` constant-folding of `ptrMetadata dst sliceLocal` to
`const len_usize` when preceded by `unsizeArrayToSlice sliceLocal arrLocal`
with no intervening mutation or storage transition of `sliceLocal`. -/
noncomputable def applyGvnFoldPtrMetadata (bodyId : DefId)
    (bbIdx : BasicBlockId) (unsizeIdx metaIdx : Nat)
    (pSrc : ArrSliceProgram) : Option ArrSliceProgram :=
  if !Nat.blt unsizeIdx metaIdx then
    none
  else
    match Trusted.MirSemantics.getElem? pSrc.bodies bodyId with
    | none => none
    | some body =>
      match Trusted.MirSemantics.getElem? body.basicBlocks bbIdx with
      | none => none
      | some bb =>
        match Trusted.MirSemantics.getElem? bb.statements unsizeIdx,
            Trusted.MirSemantics.getElem? bb.statements metaIdx with
        | some (.unsizeArrayToSlice sLoc arrLoc),
          some (.ptrMetadata dstLoc sLoc') =>
          if !Nat.beq sLoc sLoc' then
            none
          else
            match Trusted.MirSemantics.getElem? body.locals arrLoc,
                Trusted.MirSemantics.getElem? body.locals sLoc,
                Trusted.MirSemantics.getElem? body.locals dstLoc with
            | some (.array aTy len), some (.sliceView sTy), some (.base dstTy) =>
              if !(MirTy.beq aTy sTy) || !Nat.ble len 64 ||
                  !(MirTy.beq dstTy usizeTy) then
                none
              else
                let between :=
                  (bb.statements.drop (unsizeIdx + 1)).take (metaIdx - unsizeIdx - 1)
                if between.any (stmtModifiesSlice sLoc) then
                  none
                else
                  let foldedStmt : ArrSliceStmt :=
                    mkAssignUse dstLoc (usizeConst len)
                  match setElem? bb.statements metaIdx foldedStmt with
                  | none => none
                  | some stmtsTgt =>
                    match setElem? body.basicBlocks bbIdx
                        { bb with statements := stmtsTgt } with
                    | none => none
                    | some bbsTgt =>
                      match setElem? pSrc.bodies bodyId
                          { body with basicBlocks := bbsTgt } with
                      | none => none
                      | some bodiesTgt => some { pSrc with bodies := bodiesTgt }
            | _, _, _ => none
        | _, _ => none

noncomputable def checkGvnFoldPtrMetadata (bodyId : DefId)
    (bbIdx : BasicBlockId) (unsizeIdx metaIdx : Nat)
    (pSrc pTgt : ArrSliceProgram) : Bool :=
  match applyGvnFoldPtrMetadata bodyId bbIdx unsizeIdx metaIdx pSrc with
  | some pOut => arrSliceProgramEq pOut pTgt
  | none => false
```

- **`applyLowerSliceLenCalls`:** Rewrites `bb.terminator = .sliceLenCall dst sliceLoc target` into `bb.statements ++ [.ptrMetadata dst sliceLoc]` followed by `.baseTerm (.goto target)`. Because `evalArrSliceStmt (.ptrMetadata ...)` followed by `evalArrSliceTerm (.goto target)` performs the exact same type, liveness, write, and block-jump transition as `evalArrSliceTerm (.sliceLenCall ...)`, Pass 1 is a stuttering bisimulation (`1` step -> `2` steps on the lowered terminator, `1`-to-`1` everywhere else).
- **`applyGvnFoldPtrMetadata`:** When `bb.statements[unsizeIdx] = .unsizeArrayToSlice sLoc arrLoc` (`arrLoc : [aTy; len]`, `len ≤ 64`), `bb.statements[metaIdx] = .ptrMetadata dstLoc sLoc` (`unsizeIdx < metaIdx`), and no statement in `(unsizeIdx, metaIdx)` satisfies `stmtModifiesSlice sLoc`, rewrites `bb.statements[metaIdx]` to `dstLoc = const len_usize`. Because `M_arrslice` enters every basic block strictly at `stmtIdx = 0`, any execution reaching `metaIdx` in `bb` must have executed `unsizeIdx` in the same visit to `bb` and preserved `frame.locals[sLoc] = .liveSlice (some { backing := .arrayLocal arrLoc, start := 0, len := len })` across `(unsizeIdx, metaIdx)`.

#### 3.2 Pass 3 (`SliceScalarize`): Zero-Block-Split Elimination of All `.sliceView` Locals

`applySliceScalarize plan pSrc` eliminates every `.sliceView` local in `body` simultaneously **without splitting or adding a single basic block** (`0` extra blocks):

1. **Static backing table (`SliceBackingEntry`):** Each `.sliceView` local `sLoc` (`sLoc > argumentCount`) has an entry `(sLoc, optArr)` where `optArr = none` denotes a purely `.dangling` slice and `optArr = some arrLoc` denotes a slice that dynamically holds either `.dangling` (`tag = 0`) or a view into `arrLoc` (`tag = 1`).
2. **Component & scratch allocation:** Replaces `.sliceView` declarations in `0 .. base - 1` with `.base .unit` tombstones, appends `4` base locals per slice entry `k` at `off = base + 4 * k` (`liveLoc : ()`, `tagLoc : usize`, `startLoc : usize`, `lenLoc : usize`), and appends `5` body-wide scratch locals `(scrTag, scrA, scrB, scrIdx : usize, scrCond : bool)`.
3. **Branchless `BinOp.subUnchecked` UB gadgets:** Every runtime UB check in `subslice`, `readSliceElem`, and `readSliceConst` lowers into straight-line `Trusted.MirAst` arithmetic using unsigned `BinOp.subUnchecked` (which faults `.fault .undefined` in `Trusted.MirSemantics.evalBinOp` iff `lhs < rhs`):
   - **Subslice (`fromEnd = false`, `fromIdx ≤ toIdx`):** `scrA = lenLoc -_uchk toIdx` faults `.undefined` iff `sv.len < toIdx`; `scrIdx = startLoc +_uchk fromIdx` cannot overflow because `sv.start + fromIdx ≤ sv.start + sv.len < 2^64`; `scrB = const (toIdx - fromIdx)`. Moreover, reading `srcS` into `(scrTag, scrIdx, scrB)` *before* writing `dstS` makes self-aliasing `dstS = srcS` (`s = &s[1..3]`) exact!
   - **Subslice (`fromEnd = true`):** `scrB = lenLoc -_uchk (fromIdx + toIdx)` faults `.undefined` iff `sv.len < fromIdx + toIdx`, and sets `len' = sv.len - (fromIdx + toIdx)`.
   - **Dynamic `readSliceElem` & constant `readSliceConst`:**

```lean
/-- Lower a block terminator under `SliceScalarize`, appending prefix
statements into the same basic block (`0` new basic blocks added). -/
noncomputable def lowerTermForSlices (entries : List SliceBackingEntry)
    (base : Nat) : ArrSliceTerm → List ArrSliceStmt × ArrSliceTerm
  | .boundsCheckSlice sLoc idxOp inBoundsBb panicBb =>
    let scrBase := base + 4 * entries.length
    let scrTag := scrBase
    let scrIdx := scrBase + 3
    let scrCond := scrBase + 4
    match findSliceEntry entries sLoc with
    | some (k, _) =>
      let off := base + 4 * k
      ([ mkLivenessCheckStmt off,
         mkAssignUse scrTag (.copy { localId := off + 1, projection := [] }),
         mkAssignUse scrIdx idxOp,
         mkLtUsize scrCond
           (.move { localId := scrIdx, projection := [] })
           (.copy { localId := off + 3, projection := [] }) ],
       .baseTerm (.switchInt (.move { localId := scrCond, projection := [] })
         { branches := [(BitVec.ofNat 128 1, inBoundsBb)], otherwise := panicBb }))
    | none => ([], .baseTerm .unsupported)
  | .readSliceElem dst sLoc idxOp nextBb =>
    let scrBase := base + 4 * entries.length
    let scrTag := scrBase
    let scrA := scrBase + 1
    let scrB := scrBase + 2
    let scrIdx := scrBase + 3
    match findSliceEntry entries sLoc with
    | some (k, optArr) =>
      let off := base + 4 * k
      let pre : List ArrSliceStmt := [
        mkLivenessCheckStmt off,
        mkAssignUse scrTag (.copy { localId := off + 1, projection := [] }),
        mkAssignUse scrIdx idxOp,
        mkSubUncheckedUsize scrA
          (.copy { localId := off + 3, projection := [] }) (usizeConst 1),
        mkSubUncheckedUsize scrB
          (.move { localId := scrA, projection := [] })
          (.copy { localId := scrIdx, projection := [] }),
        mkSubUncheckedUsize scrB
          (.move { localId := scrTag, projection := [] }) (usizeConst 1)
      ]
      match optArr with
      | some arrLoc =>
        (pre ++ [mkAddUncheckedUsize scrIdx
          (.copy { localId := off + 2, projection := [] })
          (.copy { localId := scrIdx, projection := [] })],
         .readArrayElem dst arrLoc
           (.move { localId := scrIdx, projection := [] }) nextBb)
      | none => (pre, .baseTerm .unreachable)
    | none => ([], .baseTerm .unsupported)
  | .readSliceConst dst sLoc offset minLen fromEnd nextBb =>
    let scrBase := base + 4 * entries.length
    let scrTag := scrBase
    let scrA := scrBase + 1
    let scrB := scrBase + 2
    let scrIdx := scrBase + 3
    match findSliceEntry entries sLoc with
    | some (k, optArr) =>
      let off := base + 4 * k
      let preHead : List ArrSliceStmt := [
        mkLivenessCheckStmt off,
        mkAssignUse scrTag (.copy { localId := off + 1, projection := [] }),
        mkSubUncheckedUsize scrA
          (.copy { localId := off + 3, projection := [] }) (usizeConst minLen)
      ]
      let relStmts : List ArrSliceStmt :=
        if !fromEnd then
          [ mkSubUncheckedUsize scrA
              (.copy { localId := off + 3, projection := [] }) (usizeConst 1),
            mkSubUncheckedUsize scrB
              (.move { localId := scrA, projection := [] }) (usizeConst offset),
            mkAssignUse scrIdx (usizeConst offset) ]
        else
          if Nat.beq offset 0 then
            [mkImmediateUbStmt scrA]
          else
            [mkSubUncheckedUsize scrIdx
              (.copy { localId := off + 3, projection := [] }) (usizeConst offset)]
      let tagChk : List ArrSliceStmt := [
        mkSubUncheckedUsize scrB
          (.move { localId := scrTag, projection := [] }) (usizeConst 1)
      ]
      match optArr with
      | some arrLoc =>
        (preHead ++ relStmts ++ tagChk ++
          [mkAddUncheckedUsize scrIdx
            (.copy { localId := off + 2, projection := [] })
            (.copy { localId := scrIdx, projection := [] })],
         .readArrayElem dst arrLoc
           (.move { localId := scrIdx, projection := [] }) nextBb)
      | none => (preHead ++ relStmts ++ tagChk, .baseTerm .unreachable)
    | none => ([], .baseTerm .unsupported)
  | other => ([], other)
```

   Notice how `scrA = lenLoc -_uchk 1` followed by `scrB = move scrA -_uchk idx` faults `.fault .undefined` iff `sv.len == 0` or `idx ≥ sv.len` (`idx >= sv.len`), and `scrB = move scrTag -_uchk 1` then faults `.fault .undefined` iff `tag == 0` (`.dangling`)! When `optArr = some arrLoc` (`tag == 1`), execution computes `effIdx = startLoc +_uchk idx` and transitions directly into `.readArrayElem dst arrLoc (move scrIdx) nextBb`; when `optArr = none`, `tag` is invariantly `0`, so `scrTag -_uchk 1` already faults `.fault .undefined` before `.unreachable`.

#### 3.3 Pass 4 (`ArrayScalarize`): Per-Array Scalarization With Trailing `SwitchInt` Dispatch

Once all `.sliceView` locals in `body` have been eliminated by `SliceScalarize`, `applyArrayScalarize ⟨defId, arrLocal⟩` eliminates an internal `.array elemTy len` local (`0 ≤ len ≤ 64`):

- **Component & scratch locals (`base := body.locals.length`):** Tombstones `body.locals[arrLocal]` to `.base .unit`, appends `base + 0 : .unit` (`liveLoc`), `base + 1 .. base + len : elemTy` (`elem_0 .. elem_{len-1}`), and `4 + len` scratch locals (`faultUsize`, `idxScr`, `condScr`, `valScr`, and `opScr_0 .. opScr_{len-1}`).
- **Exact left-to-right operand & liveness fault ordering:**
  - `aggregateArray arrLocal ops`: evaluates `ops` left-to-right into `opScr_0 .. opScr_{len-1}`, then runs `mkLivenessCheckStmt base` (faulting `.undefined` if `arrLocal` is dead), then moves `opScr_i -> elem_i`.
  - `repeatArray arrLocal op`: evaluates `op` into `valScr` (even when `len = 0`!), runs `mkLivenessCheckStmt base`, and copies `valScr` into `elem_0 .. elem_{len-1}`.
  - `readArrayConst` / `writeArrayConst`: directly copies/moves `elem_idx` (or faults via `mkImmediateUbStmt` when `idx ≥ len`).
  - `boundsCheckArray`: evaluates `idxOp` after `mkLivenessCheckStmt base`, computes `condScr = idx < len`, and switches via `.switchInt`.
  - `readArrayElem` / `writeArrayElem`: evaluates operands (`idxOp`, plus `valOp` for writes) and `mkLivenessCheckStmt base`, then dispatches via `.switchInt (move idxScr)` over `len` appended 1-statement arm blocks `buildReadArrayArms` / `buildWriteArrayArms` (`arm_k -> goto nextBb`) with `otherwise := trapBb` (`.unreachable`, faulting `.fault .undefined` on any out-of-bounds `idx ≥ len`). Because all dispatch and trap blocks are appended at indices `≥ body.basicBlocks.length`, all original basic-block IDs `0 .. B - 1` remain invariant.
- **Projection to unmodified `Trusted.MirAst.Program`:** Once all `.sliceView` and `.array` locals are eliminated, `unembedBaseProgram pFlat = some pOut` unwraps every declaration, statement, and terminator into an unmodified `Trusted.MirAst.Program` (`pMir`), validated by `checkArrSliceToTrustedMir trace pSrc pMir = true`.

---

### 4. Five Core Mechanized Theorems, 11-Slice Proof Architecture, & Axiom Profile

`Basis: execution (Lean kernel, support/AnnealTrustedMirArraysSlicesPtrMetadataAndScalarize.lean)`

#### 4.1 Verbatim Part III Theorem Statements (`VrustcFormal.F1_15`)

All five Part III theorem statements are locked byte-for-byte against frozen statement `SHA-256 381d5f87b9d29e34125a834581e58becc4d7ab2e5edf4406953bd4fafacd8434` and proved with `0` `sorry` and `0` `Classical.choice`:

```lean
theorem arrSlice_conservative_extension_exact
    (p : Program) :
    (∀ (c : Choice) (s : State),
      evalStepArrSlice (embedBaseProgram p) c (embedArrSliceState s) =
        liftStepResultArrSlice (evalStep p c s)) ∧
    (∀ q : Query,
      (WellFormedArrSlice (embedBaseProgram p) q ↔ WellFormed p q) ∧
      (∀ out : TerminalOut,
        BehaviorArrSlice (embedBaseProgram p) q out ↔ Behavior p q out) ∧
      (∀ k : FaultKind,
        ReachesResultArrSlice (embedBaseProgram p) q (.fault k) ↔
          ReachesResult p q (.fault k)) ∧
      (DivergesArrSlice (embedBaseProgram p) q ↔ Diverges p q) ∧
      (∀ post : TerminalOut → Prop,
        SatisfiesPostArrSlice (embedBaseProgram p) q post ↔
          SatisfiesPost p q post)) 

/-- **Theorem 2 (`lowerSliceLenCalls_and_gvnPtrMetadata_sound_bidirectional_iff`):**
Both `LowerSliceLenCalls` (`checkLowerSliceLenCalls`) and intra-block `GVN`
`PtrMetadata(Unsize)` constant folding (`checkGvnFoldPtrMetadata`) preserve
full bidirectional semantic equivalence `FullSemanticEquivArrSlice pSrc pTgt`. -/
theorem lowerSliceLenCalls_and_gvnPtrMetadata_sound_bidirectional_iff :
    (∀ (bodyId : DefId) (bbIdx : BasicBlockId) (pSrc pTgt : ArrSliceProgram),
      checkLowerSliceLenCalls bodyId bbIdx pSrc pTgt = true →
      FullSemanticEquivArrSlice pSrc pTgt) ∧
    (∀ (bodyId : DefId) (bbIdx : BasicBlockId) (unsizeIdx metaIdx : Nat)
        (pSrc pTgt : ArrSliceProgram),
      checkGvnFoldPtrMetadata bodyId bbIdx unsizeIdx metaIdx pSrc pTgt = true →
      FullSemanticEquivArrSlice pSrc pTgt) 

/-- **Theorem 3 (`danglingSlice_metadata_valid_deref_ub_and_boundsCheck_precedes_deref`):**
Universal algebraic and operational laws of wide-pointer slices in `M_arrslice`:
1. **Dangling Slice Metadata Validity vs. Dereference UB:** On any live
   `.dangling` slice of length `len < 2^64` with live `usize` destination `dst`,
   `ptrMetadata dst sLoc` succeeds and writes `len : usize` independently of
   any array slot, whereas `readSliceElem` on a `.dangling` slice
   deterministically faults `.fault .undefined` (Part IV `CE8` additionally
   witnesses `.dangling` `readSliceConst` UB).
2. **`BoundsCheck` Precedes Dereference:** On any live slice `(backing, start,
   len)` (including `.dangling`) and `usize` index `idx < 2^64`,
   `boundsCheckSlice` jumps to `inBoundsBb` iff `idx < len` and to `panicBb`
   iff `idx ≥ len` without touching `backing`.
3. **Exact `Subslice` Composition Law:** Chaining two valid from-start
   `evalSubsliceVal` calls `(from₁, to₁, false)` then `(from₂, to₂, false)`
   equals a single `evalSubsliceVal` `(from₁ + from₂, from₁ + to₂, false)`
   preserving `backing` and `start' + len' < 2^64` (Part IV `CE8` additionally
   witnesses out-of-bounds `evalSubsliceVal` `.error .undefined`). -/
theorem danglingSlice_metadata_valid_deref_ub_and_boundsCheck_precedes_deref :
    (∀ (body : ArrSliceBody) (frame : ArrSliceFrame) (cm : CallerMemory)
        (dst sLoc : LocalId) (elemTy : MirTy) (len : Nat) (optOld : Option Val),
      Nat.blt len maxUsize = true →
      Trusted.MirSemantics.getElem? body.locals dst = some (.base usizeTy) →
      Trusted.MirSemantics.getElem? body.locals sLoc = some (.sliceView elemTy) →
      Trusted.MirSemantics.getElem? frame.locals sLoc =
        some (.liveSlice (some { backing := .dangling, start := 0, len := len })) →
      Trusted.MirSemantics.getElem? frame.locals dst = some (.baseSlot (.live optOld)) →
      ∃ slots' : List ArrSliceSlot,
        evalArrSliceStmt body frame cm (.ptrMetadata dst sLoc) =
          stepStmtNext frame cm slots' ∧
        Trusted.MirSemantics.getElem? slots' dst =
          some (.baseSlot (.live (some (.scalar ⟨.isize, false, BitVec.ofNat 128 len⟩))))) ∧
    (∀ (body : ArrSliceBody) (bb : ArrSliceBlock) (frame : ArrSliceFrame)
        (cm : CallerMemory) (dst sLoc : LocalId) (elemTy : MirTy)
        (start len idx : Nat) (nextBb : BasicBlockId),
      Nat.blt idx maxUsize = true →
      Trusted.MirSemantics.getElem? body.locals dst = some (.base elemTy) →
      Trusted.MirSemantics.getElem? body.locals sLoc = some (.sliceView elemTy) →
      Trusted.MirSemantics.getElem? frame.locals sLoc =
        some (.liveSlice (some { backing := .dangling, start := start, len := len })) →
      bb.terminator = .readSliceElem dst sLoc (usizeConst idx) nextBb →
      evalArrSliceTerm body bb frame cm = .fault .undefined) ∧
    (∀ (body : ArrSliceBody) (bb : ArrSliceBlock) (frame : ArrSliceFrame)
        (cm : CallerMemory) (sLoc : LocalId) (elemTy : MirTy)
        (sv : SliceViewVal) (idx : Nat) (inBoundsBb panicBb : BasicBlockId),
      Nat.blt idx maxUsize = true →
      Trusted.MirSemantics.getElem? body.locals sLoc = some (.sliceView elemTy) →
      Trusted.MirSemantics.getElem? frame.locals sLoc =
        some (.liveSlice (some sv)) →
      bb.terminator = .boundsCheckSlice sLoc (usizeConst idx) inBoundsBb panicBb →
      evalArrSliceTerm body bb frame cm =
        jumpArrSliceBlock frame cm frame.locals
          (if Nat.blt idx sv.len then inBoundsBb else panicBb)) ∧
    (∀ (sv : SliceViewVal) (f₁ t₁ f₂ t₂ : Nat),
      Nat.blt (sv.start + sv.len) maxUsize = true →
      f₁ ≤ t₁ → t₁ ≤ sv.len → f₂ ≤ t₂ → t₂ ≤ t₁ - f₁ →
      ∃ sv₁ sv₂ : SliceViewVal,
        evalSubsliceVal sv f₁ t₁ false = .ok sv₁ ∧
        evalSubsliceVal sv₁ f₂ t₂ false = .ok sv₂ ∧
        evalSubsliceVal sv (f₁ + f₂) (f₁ + t₂) false = .ok sv₂ ∧
        sv₂.backing = sv.backing ∧
        sv₂.start + sv₂.len < maxUsize) 

/-- **Theorem 4 (`arraySliceScalarize_reduces_to_trusted_mir`):**
Any finite `ArrSliceOptTrace` certified by
`checkArrSliceToTrustedMir trace pSrc pMir = true` produces an unmodified
`Trusted.MirAst.Program` (`pMir`) whose unmodified `Trusted.MirSemantics`
judgments (`WellFormed`, `Behavior`, `ReachesResult (.fault k)`, `Diverges`,
and `SatisfiesPost`) are bidirectionally equivalent (`↔`) to `M_arrslice` on
`pSrc`. -/
theorem arraySliceScalarize_reduces_to_trusted_mir
    (trace : ArrSliceOptTrace) (pSrc : ArrSliceProgram) (pMir : Program)
    (hLower : checkArrSliceToTrustedMir trace pSrc pMir = true) :
    (∀ q : Query, WellFormedArrSlice pSrc q ↔ WellFormed pMir q) ∧
    (∀ q : Query, ∀ out : TerminalOut,
      BehaviorArrSlice pSrc q out ↔ Behavior pMir q out) ∧
    (∀ q : Query, ∀ k : FaultKind,
      ReachesResultArrSlice pSrc q (.fault k) ↔
        ReachesResult pMir q (.fault k)) ∧
    (∀ q : Query, DivergesArrSlice pSrc q ↔ Diverges pMir q) ∧
    (∀ q : Query, ∀ post : TerminalOut → Prop,
      SatisfiesPostArrSlice pSrc q post ↔ SatisfiesPost pMir q post) 

/-- **Theorem 5 (`arraySlicePipeline_then_optPipeline_vc_transport`):**
Vertical composition: any certified `ArrSliceOptTrace` lowering `pSrc` into
unmodified `Trusted.MirAst.Program` `pMir` followed by any certified
`Trusted.MirSemantics` optimization equivalence `FullSemanticEquivBase pMir pOpt`
transports all five `M_arrslice` verification judgments bidirectionally (`↔`)
onto unmodified `Trusted.MirSemantics` on `pOpt`. -/
theorem arraySlicePipeline_then_optPipeline_vc_transport
    (trace : ArrSliceOptTrace) (pSrc : ArrSliceProgram) (pMir pOpt : Program)
    (hLower : checkArrSliceToTrustedMir trace pSrc pMir = true)
    (hOpt : FullSemanticEquivBase pMir pOpt) :
    (∀ q : Query, WellFormedArrSlice pSrc q ↔ WellFormed pOpt q) ∧
    (∀ q : Query, ∀ out : TerminalOut,
      BehaviorArrSlice pSrc q out ↔ Behavior pOpt q out) ∧
    (∀ q : Query, ∀ k : FaultKind,
      ReachesResultArrSlice pSrc q (.fault k) ↔
        ReachesResult pOpt q (.fault k)) ∧
    (∀ q : Query, DivergesArrSlice pSrc q ↔ Diverges pOpt q) ∧
    (∀ q : Query, ∀ post : TerminalOut → Prop,
      SatisfiesPostArrSlice pSrc q post ↔ SatisfiesPost pOpt q post) 
```

#### 4.2 Modular 11-Slice Proof Architecture (`33077` Slice Lines -> `36210` Stitched Lines)

To keep kernel elaboration fast, deterministic, and Pass-1-pure under `-M4096 -DElab.async=false`, the proof was engineered across `11` standalone `TrustedBoundary.lean`-preflighted proof slices (`33077` lines alongside `F1_15_Base.lean`) and stitched into `support/AnnealTrustedMirArraysSlicesPtrMetadataAndScalarize.lean` (`36210` lines, `1939606` bytes, `byte_exact_reconstruction == true`, `0` non-private inserted declarations):

| Slice Module | Lines | Decls | Proof Responsibility |
| :--- | :---: | :---: | :--- |
| `F1_15_Common.lean` | `3317` | `201` | Structural equality reflection (`programEq_eq`, `arrSliceProgramEq_eq`, `mirTy_beq_eq`), `BitVec`/`usize` arithmetic helpers, constructive determinism (`divergesBase_iff_no_terminal_or_fault`), and bounded-stutter simulation (`fullSemanticEquivArrSlice_of_fwd_stutter_sim`, `0` `Classical.choice`). |
| `Slice1_ConservativeExt_And_SliceLaws.lean` | `850` | `20` | 1-step lockstep (`evalStepArrSlice_embedBaseProgram`), `initStateArrSlice_embedBaseProgram`, `unembedBaseProgram_eq_embed`, **Theorem 1** (`arrSlice_conservative_extension_exact`), and **Theorem 3** (`danglingSlice_metadata_valid_deref_ub_and_boundsCheck_precedes_deref`). |
| `Slice2_LowerSliceLen_And_GvnPtrMetadata.lean` | `2918` | `36` | Pass 1 (`applyLowerSliceLenCalls_sound`) & Pass 2 (`applyGvnFoldPtrMetadata_sound` intra-block non-interfering `unsizeArrayToSlice -> ptrMetadata` constant folding), discharging **Theorem 2** (`lowerSliceLenCalls_and_gvnPtrMetadata_sound_bidirectional_iff`, strictly `[propext]`). |
| `Slice3a_SliceScalarizeHelpers.lean` | `2559` | `99` | `SliceScalarize` context unpacking (`applySliceScalarize_unpack`), `findSliceEntry` uniqueness/indexing invariants, tombstoned local-table typing, and `PrefixBaseAgree` preservation lemmas. |
| `Slice3b_SliceScalarizeGadgets.lean` | `2620` | `78` | Straight-line 0-block-split execution lemmas for `mkLivenessCheckStmt`, `mkImmediateUbStmt`, `mkSubUncheckedUsize`, `mkAddUncheckedUsize`, `mkLtUsize`, `mkStorageLiveRange`, and `mkStorageDeadRange`. |
| `Slice3c_SliceScalarizeStmts.lean` | `5004` | `65` | Forward `1`-to-`1+` simulation for all `lowerStmtForSlices` arms (`unsizeArrayToSlice`, `sliceFromRawParts`, self-aliasing-safe `subslice` for both `fromEnd = false` and `fromEnd = true`, `ptrMetadata`, and storage markers). |
| `Slice3d_SliceScalarizeSound.lean` | `3185` | `25` | Terminator simulation for `lowerTermForSlices` (`boundsCheckSlice`, `readSliceElem`, `readSliceConst` across `.dangling` and `.arrayLocal` backings) and full Pass 3 soundness (`applySliceScalarize_sound`, strictly `[propext]`). |
| `Slice4a_ArrayScalarizeHelpers.lean` | `4151` | `141` | `ArrayScalarize` context unpacking (`applyArrayScalarize_unpack`), `ArraySimRel` (`elem_0 .. elem_{len-1}` + liveness + scratch layout), `mkEvalOpsToArrScratch`, `mkMoveArrScratchToElems`, `mkCopyValToElems`, and `SwitchInt` arm lookup (`buildReadArrayArms`, `buildWriteArrayArms`). |
| `Slice4b_ArrayScalarizeStmts.lean` | `4934` | `49` | Forward `1`-to-`1+` simulation for all `lowerStmtForArray` arms (`aggregateArray`, `repeatArray` including `len = 0` operand evaluation, `arrayLivenessCheck`, `readArrayConst` copy/move deinit, `writeArrayConst`, and storage markers). |
| `Slice4c_ArrayScalarizeSound.lean` | `3271` | `32` | Terminator simulation for `lowerTermForArray` (`boundsCheckArray`, `readArrayElem`, `writeArrayElem` with trailing `SwitchInt` dispatch + `.unreachable` trap blocks) and full Pass 4 soundness (`applyArrayScalarize_sound`, strictly `[propext]`). |
| `Slice5_TraceAndPipeline.lean` | `268` | `13` | Finite trace induction (`applyArrSliceOptTrace_sound`), **Theorem 4** (`arraySliceScalarize_reduces_to_trusted_mir`), and **Theorem 5** (`arraySlicePipeline_then_optPipeline_vc_transport`). |

Notably, **both** core scalarization soundness theorems—`applySliceScalarize_sound` (`Slice3d`, `13,368` lines across `Slice3a`–`Slice3d`) and `applyArrayScalarize_sound` (`Slice4c`, `12,356` lines across `Slice4a`–`Slice4c`)—as well as Theorem 2 (`Slice2`) and Theorem 3 (`Slice1`) depend **strictly on `[propext]` alone** (`0` `Quot.sound`, `0` `Classical.choice`), with `Quot.sound` entering only via `funext` on `List.map` congruence in `embedBaseProgram` / `unembedBaseProgram` (`Slice1` and `Slice5`).

#### 4.3 Complete Public Theorem Inventory & Axiom Profile (`26` Theorems)

Every single one of the `26` public theorems depends exclusively on `["propext", "Quot.sound"]` (`23 / 26` strictly `[propext]`, `3 / 26` `[propext, Quot.sound]`, `0` `Classical.choice`, `0` `sorryAx`, `0` `_unsafe_rec`):

| # | Public Theorem | Lean 4 Kernel Axioms | Role |
| :---: | :--- | :--- | :--- |
| `1` | `VrustcFormal.F1_15.arrSlice_conservative_extension_exact` | `[propext, Quot.sound]` | Part III Core Theorem 1 |
| `2` | `VrustcFormal.F1_15.lowerSliceLenCalls_and_gvnPtrMetadata_sound_bidirectional_iff` | `[propext]` | Part III Core Theorem 2 |
| `3` | `VrustcFormal.F1_15.danglingSlice_metadata_valid_deref_ub_and_boundsCheck_precedes_deref` | `[propext]` | Part III Core Theorem 3 |
| `4` | `VrustcFormal.F1_15.arraySliceScalarize_reduces_to_trusted_mir` | `[propext, Quot.sound]` | Part III Core Theorem 4 |
| `5` | `VrustcFormal.F1_15.arraySlicePipeline_then_optPipeline_vc_transport` | `[propext, Quot.sound]` | Part III Core Theorem 5 |
| `6` | `VrustcFormal.F1_15.reachesArrSlice_head` | `[propext]` | Part IV Bounded-Fuel Adequacy / Determinism Lemma |
| `7` | `VrustcFormal.F1_15.reachesArrSlice_head_det` | `[propext]` | Part IV Bounded-Fuel Adequacy / Determinism Lemma |
| `8` | `VrustcFormal.F1_15.execFuelArrSlice_sound` | `[propext]` | Part IV Bounded-Fuel Adequacy / Determinism Lemma |
| `9` | `VrustcFormal.F1_15.execArrSlice_sound` | `[propext]` | Part IV Bounded-Fuel Adequacy / Determinism Lemma |
| `10` | `VrustcFormal.F1_15.execFuelArrSlice_done_det` | `[propext]` | Part IV Bounded-Fuel Adequacy / Determinism Lemma |
| `11` | `VrustcFormal.F1_15.positiveCanaryArrSlice_of_exec` | `[propext]` | Part IV Bounded-Fuel Adequacy / Determinism Lemma |
| `12` | `VrustcFormal.F1_15.negativeCanaryArrSlice_of_exec` | `[propext]` | Part IV Bounded-Fuel Adequacy / Determinism Lemma |
| `13` | `VrustcFormal.F1_15.reachesBase_head` | `[propext]` | Part IV Bounded-Fuel Adequacy / Determinism Lemma |
| `14` | `VrustcFormal.F1_15.execFuelBase_sound` | `[propext]` | Part IV Bounded-Fuel Adequacy / Determinism Lemma |
| `15` | `VrustcFormal.F1_15.execBase_sound` | `[propext]` | Part IV Bounded-Fuel Adequacy / Determinism Lemma |
| `16` | `VrustcFormal.F1_15.ce1_bounds_check_precedes_ub_and_unchecked_oob_faults_in_trusted_mir` | `[propext]` | Part IV Sharpness Counterexample / End-to-End Lowering Witness |
| `17` | `VrustcFormal.F1_15.ce2_constant_index_and_subslice_lower_to_trusted_mir` | `[propext]` | Part IV Sharpness Counterexample / End-to-End Lowering Witness |
| `18` | `VrustcFormal.F1_15.ce3_dangling_slice_metadata_ok_and_deref_ub_in_trusted_mir` | `[propext]` | Part IV Sharpness Counterexample / End-to-End Lowering Witness |
| `19` | `VrustcFormal.F1_15.ce4_lower_slice_len_and_gvn_fold_ptr_metadata` | `[propext]` | Part IV Sharpness Counterexample / End-to-End Lowering Witness |
| `20` | `VrustcFormal.F1_15.ce5_dead_array_borrow_and_post_storage_dead_slice_deref_ub` | `[propext]` | Part IV Sharpness Counterexample / End-to-End Lowering Witness |
| `21` | `VrustcFormal.F1_15.ce6_double_move_scalar_ub_vs_zst_array_ok` | `[propext]` | Part IV Sharpness Counterexample / End-to-End Lowering Witness |
| `22` | `VrustcFormal.F1_15.ce7_repeat_zero_evaluates_operand_and_repeat_four_ok` | `[propext]` | Part IV Sharpness Counterexample / End-to-End Lowering Witness |
| `23` | `VrustcFormal.F1_15.ce8_subslice_oob_faults_ub` | `[propext]` | Part IV Sharpness Counterexample / End-to-End Lowering Witness |
| `24` | `VrustcFormal.F1_15.ce9_storage_dead_live_resets_slice_to_uninit` | `[propext]` | Part IV Sharpness Counterexample / End-to-End Lowering Witness |
| `25` | `VrustcFormal.F1_15.ce10_end_to_end_4pass_pipeline_executes_in_unmodified_trusted_mir` | `[propext]` | Part IV Sharpness Counterexample / End-to-End Lowering Witness |
| `26` | `VrustcFormal.F1_15.ce11_static_guards_oob_unscalarized_slice_and_clobbered_gvn` | `[propext]` | Part IV Sharpness Counterexample / End-to-End Lowering Witness |

---

### 5. Eleven Sharpness Counterexamples (`CE1`–`CE11`) & End-to-End 4-Pass `Trusted.MirSemantics` Witness

`Basis: execution (Lean kernel, support/AnnealTrustedMirArraysSlicesPtrMetadataAndScalarize.lean)`

Part IV (`0` `sorry`, verified byte-for-byte against the frozen specification) establishes deterministic bounded-fuel adequacy (`execArrSlice_sound`, `positiveCanaryArrSlice_of_exec`, `negativeCanaryArrSlice_of_exec`, `execBase_sound`) and eleven kernel-checked witnesses:

| Witness Theorem | Concrete Program / Scenario | Exact Kernel-Checked Property |
| :--- | :--- | :--- |
| `ce1_bounds_check_precedes_ub_and_unchecked_oob_faults_in_trusted_mir` | `[10, 20, 30, 40]` (`[u32; 4]`) checked vs. unchecked OOB | Checked `boundsCheckArray` returns `30_u32` at `idx = 2` and routes `idx = 4` cleanly to `panicBb` (`999_u32`), whereas unchecked `readArrayElem` at `idx = 4` faults `.fault .undefined` BOTH in `M_arrslice` AND after `ArrayScalarize` in unmodified `Trusted.MirSemantics`. |
| `ce2_constant_index_and_subslice_lower_to_trusted_mir` | `let [head, mid @ .., tail] = &[1, 2, 3, 4, 5]` (`E3-90` Probe 2) | Unsizes `[1..5]`, reads `head = slice[0 of 2]` (`1`), forms `mid = slice[1..-1]` (`fromEnd = true`), reads `PtrMetadata(mid)` (`3`), reads `tail = slice[-1 of 2]` (`5`), lowers via `[.sliceScalarize, .arrayScalarize]` into unmodified `Trusted.MirSemantics`, and evaluates to `9_usize`. |
| `ce3_dangling_slice_metadata_ok_and_deref_ub_in_trusted_mir` | `slice_from_raw_parts(NonNull::dangling(), 100)` (`E3-90` Probe 3) | Lowered via `SliceScalarize` (`backing = none`) into unmodified `Trusted.MirSemantics`: `ptrMetadata` returns `100_usize`, whereas `readSliceElem` at `idx = 0` faults `.fault .undefined` in BOTH `M_arrslice` and `Trusted.MirSemantics`. |
| `ce4_lower_slice_len_and_gvn_fold_ptr_metadata` | `unsize([u32; 4])` + `sliceLenCall` | Certifies `checkLowerSliceLenCalls` followed by `checkGvnFoldPtrMetadata`, folding `slice.len()` to `const 4_usize` and returning `4_usize`. |
| `ce5_dead_array_borrow_and_post_storage_dead_slice_deref_ub` | Dead `[u32; 4]` borrow & post-`StorageDead` slice read | `unsizeArrayToSlice` on a dead array faults `.fault .undefined`, and `StorageDead(arr)` after `unsizeArrayToSlice` causes subsequent `readSliceElem` to fault `.fault .undefined`. |
| `ce6_double_move_scalar_ub_vs_zst_array_ok` | `[u32; 2]` vs. `[(); 3]` double `readArrayConst(..., isMove := true)` | Moving `arr[0] : u32` twice faults `.fault .undefined` (`deinitMovedPlace`), whereas moving `zst_arr[2] : ()` twice succeeds and returns `.unit`. |
| `ce7_repeat_zero_evaluates_operand_and_repeat_four_ok` | `[uninit_u32; 0]` vs. `[42_u32; 4]` | `repeatArray` at `len = 0` still evaluates `copy uninit_u32` and faults `.fault .undefined`, while `[42_u32; 4]` initializes all 4 elements and reads `42_u32` at index `3`. |
| `ce8_subslice_oob_faults_ub` | `subslice(len=4, 2..5, false)` & `subslice(len=4, 2..-3, true)` | Out-of-bounds `subslice` faults `.fault .undefined` for both `fromEnd = false` (`toIdx > len`) and `fromEnd = true` (`fromIdx + toIdx > len`). |
| `ce9_storage_dead_live_resets_slice_to_uninit` | `StorageLive 1; sliceFromRawParts 1 10; StorageDead 1; StorageLive 1; ptrMetadata` | `StorageDead` + `StorageLive` resets `.sliceView` to `.liveSlice none` (`Uninit`), causing `ptrMetadata` to fault `.fault .undefined`. |
| `ce10_end_to_end_4pass_pipeline_executes_in_unmodified_trusted_mir` | `witness::arr_slice_4pass_pipeline` (`[10, 20, 30, 40]`, `slice.len()`, `boundsCheckSlice`, `slice[idx]`) | Certifies all 4 passes `[.lowerSliceLenCalls 0 0, .gvnFoldPtrMetadata 0 0 1 2, .sliceScalarize ⟨0, [⟨3, some 2⟩]⟩, .arrayScalarize ⟨0, 2⟩]` via `checkArrSliceToTrustedMir ... = true`, and executes `progCe10TrustedMir : Trusted.MirAst.Program` directly in unmodified `Trusted.MirSemantics.evalStep` (`idx = 2 -> 30_u32`, `idx = 5 -> 999_u32`). |
| `ce11_static_guards_oob_unscalarized_slice_and_clobbered_gvn` | `progCe11OobLocal`, `progCe10EndToEndSrc`, `progCe11ClobberedGvn` | Verifies fail-closed `none` rejection on (1) out-of-bounds `LocalId` `5` in `applyArrayScalarize`, (2) unscalarized `.sliceView` local remaining before `applyArrayScalarize`, and (3) `sliceFromRawParts` clobbering `sLoc` inside an `applyGvnFoldPtrMetadata` window. |

---

### 6. Six-Gate Multi-Kernel, `TrustedBoundary.lean` Pass 1, & Blind Specification Audit Results

`Basis: execution (support/multi_kernel_verification_summary.json)`

Prior to freezing (`SHA-256 381d5f87b9d29e34125a834581e58becc4d7ab2e5edf4406953bd4fafacd8434`), a Stage 2 blind specification audit caught and resolved three subtle specification edge cases (`StorageDead 0` / out-of-bounds `StorageDead` fallback in `evalArrSliceStmt`, `isSupportedScalarOrUnitTy` checking on unbacked `.sliceView` tombstones in `checkSliceBackingEntriesLoop`, and `!Nat.blt body.argumentCount body.locals.length` in `applySliceScalarize`). Following proof completion, an independent Stage 5 blind specification audit inspected `F1_15_..._Stmt.frozen.lean` (`L1–3148`), unmodified `Trusted/{MirAst,MirSemantics}.lean`, and `E3-90` under strict isolation (`0` proof files read), returning **`PASS` (`0` soundness bugs, `0` vacuities, `0` TCB misalignments)**.

The stitched single-file proof `support/AnnealTrustedMirArraysSlicesPtrMetadataAndScalarize.lean` (`36210` lines, `1939606` bytes, `0` CRLF bytes, `0` disallowed Unicode/bidi characters, `byte_exact_reconstruction == true`) passed all six multi-kernel verification gates:

| Gate | Checker / Tool | Configuration / Flags | Result | Wall Time | Peak RSS | Key Metrics |
| :---: | :--- | :--- | :---: | :---: | :---: | :--- |
| **1** | `Lean v4.34.1` (`5045d005`) | `-M4096 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` | `rc = 0` | `308.8763 s` | `2060.48 MB` | `0` errors, `0` warnings, `.olean` `50186128` B |
| **2** | `#print axioms` + `env.constants.map₁` audit | All `26` public theorems + frozen-vs-proof public surface diff | `rc = 0` | `3.5867 s` | `1619.63 MB` | `23 / 26` strictly `[propext]`, `3 / 26` `[propext, Quot.sound]`, `0` `Classical.choice`; `total=2224`, `pub=933`, `priv=1291`, `bad=0`, `pub_surface_clean=true` |
| **3a** | `TrustedBoundary.lean` `"preflight"` (pos) | Unmodified `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` | `rc = 0` | `20.5407 s` | `788.7 MB` | `ok = true` on `Anneal.F1_15_Proof` |
| **3b** | `TrustedBoundary.lean` `"preflight"` (neg) | Frozen statement file containing Part III `sorry`s | `rc = 1` | `13.5889 s` | — | Rejected fail-closed: `policy:unsupported syntax kind Lean.Parser.Tactic.tacticSorry` |
| **3c** | `TrustedBoundary.lean` Pass 1 `"audit"` | `axioms: [["Quot.sound", "Init.Prelude"], ["propext", "Init.Core"]]` (`0` `Classical.choice`) | `rc = 0` | `506.3832 s` | `951.06 MB` | `ok = true`, `replay = true`, `kernelDeclarations = 1324`, `replayedDeclarations = 3805`, `reachableDeclarations = 4707`, `checkedAlternateProofs = 0`, `compilerOnlyNames = 281`, `axioms = ["propext", "Quot.sound"]` |
| **4** | `Lean v4.35.0` (`eb6cafb7`) | `-M4096 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` | `rc = 0` | `255.918 s` | `2000.66 MB` | Cross-version kernel check clean (`0` warnings) |
| **5** | `lean4export 3.1.0` (`5a9a355d`) | Exporting all `26` `VrustcFormal.F1_15.*` public theorems | `rc = 0` | `226.7053 s` | — | `1369294` NDJSON lines (`71853391` B) |
| **6a** | `nanoda_bin 0.4.19` (`f55114af`) (pos) | `permitted_axioms: ["propext", "Quot.sound"]`, `unpermitted_axiom_hard_error: true` | `rc = 0` | `30.9984 s` | `124.65 MB` | `Checked 3147 declarations with no typechecker errors` |
| **6b** | `nanoda_bin 0.4.19` (`f55114af`) (neg) | `permitted_axioms: []`, `unpermitted_axiom_hard_error: true` | `rc = 1` | `8.0808 s` | — | Rejected fail-closed: `export file declares unpermitted axiom "propext"` |

## Boundaries

Every theorem in `VrustcFormal.F1_15` is exact within the thirteen explicitly audited Honest-Scope boundaries below (`B1`–`B13`); constructs outside this fragment fail closed (`.error .unsupported`, `.fault .unsupported`, or `none`) rather than approximating semantics:

1. **B1 — Per-array static length cap (`0 <= len <= 64`).** `isSupportedArrSliceLocalDecl`, `applyGvnFoldPtrMetadata`, `checkSliceBackingEntriesLoop`, and `applyArrayScalarize` bound internal array lengths to `0 <= len <= 64`, covering `zerocopy`'s observed runtime `[u8; 4]`, `[u8; 8]`, `[u8; 16]` (`byteorder` `ZERO`/`MAX_VALUE`, `util::macro_util::hash_name`) and `[u32; 3]` while keeping scalarized local counts and `SwitchInt` dispatch arms linear; arrays with `N > 64` fail closed.
2. **B2 — Flat scalar / unit / `!` / fieldless-enum element types (`isSupportedScalarOrUnitTy`).** Element types `elemTy` of `.array` and `.sliceView` locals must satisfy `Trusted.MirSemantics.isSupportedScalarOrUnitTy` (booleans, fixed/pointer-width integers, `.unit`, `.never`, and admitted fieldless `.enum`). Nested arrays (`[[T; M]; N]`), tuple elements, pointer/reference elements, and payload-ADT elements (such as `&[layout::DstLayout]` in `DstLayout::for_repr_c_struct`, before struct/enum flattening via `F1-11` / `F1-14`) fail closed.
3. **B3 — Internal local arrays & slice views only (`idx > argumentCount`, empty `callerMem`).** Signature slots `0 .. argumentCount` are restricted to `.base ty` (`arrSliceParamBaseTys?`), and `initStateArrSlice` inherits `q.callerMem.allocations.isEmpty` from `Trusted.MirSemantics`. Functions accepting or returning caller-memory-backed `&[u8]`, `&mut [u8]`, `&str`, or by-value `[T; N]` across ABI boundaries (`FromBytes::read_from_bytes`, `IntoBytes::as_bytes`, `hash_name(_1: &str)`) require `CallerMemory` / raw-pointer allocation modeling.
4. **B4 — Read-only slice views (`&[T]` / `*const [T]`); no mutable slice writes (`&mut [T]` / `*mut [T]`).** `M_arrslice` models shared/const slice reads (`readSliceElem`, `readSliceConst`), `subslice`, `ptrMetadata`, and `boundsCheckSlice` alongside direct array mutations (`writeArrayConst`, `writeArrayElem`), but omits mutable slice element writes `(*mut_slice)[idx] = val`, bulk `copy_nonoverlapping` (`IntoBytes::write_to_prefix`), and Stacked/Tree Borrows aliasing tracking between coexisting views.
5. **B5 — At most one static backing array local per `.sliceView` local (`SliceBackingEntry`).** Each `.sliceView` local in `SliceScalarize` is statically assigned either `none` (strictly `.dangling`) or `some arrLocal` (dynamically `.dangling` at `tag = 0` or `arrLocal` at `tag = 1`). Control-flow joins where a single `.sliceView` local dynamically aliases two distinct array locals `arr₁ != arr₂` fail closed in `checkStmtForSlices`.
6. **B6 — `NonNull::dangling()` raw slices only in `sliceFromRawParts`; no general `Aggregate(RawPtr)` or pointer/transmute casts.** `sliceFromRawParts` models `ptr::slice_from_raw_parts(NonNull::dangling(), len)`, excluding general `Rvalue::Aggregate(RawPtr, [data_ptr, meta])` over live memory pointers (`51` sites in `zerocopy` optimized MIR), `CastKind::{PtrToPtr, Transmute}` (`&str -> &[u8]` or `[u8; 16] -> i128` in `hash_name`), and `ConstValue::Indirect` wide-pointer constants.
7. **B7 — Array-to-slice unsizing (`&[T; N] -> &[T]`) only; excludes `dyn Trait` & custom struct-tail DSTs.** `unsizeArrayToSlice` covers `PointerCoercion::Unsize` from `[T; N]` to `[T]` (`12` sites in `zerocopy` optimized MIR), excluding `dyn Trait` vtable unsizing (`19` `&dyn fmt::Debug` sites) and custom struct-tail DST metadata (`KnownLayout::pointer_to_metadata` in `split_at.rs`).
8. **B8 — Structured first-order `M_arrslice` forms vs. arbitrary `Place.projection` chains & raw `Assert` terminators.** Array/slice operations are represented as dedicated `M_arrslice` statements/terminators rather than nested `ProjectionElem::{Deref, Field, Index, ConstantIndex, Subslice}` lists or raw `TerminatorKind.assert` (`.baseTerm (.assert ...)` faults `.unsupported`). Ingesting raw `rustc` MIR (`Lt` + `assert(BoundsCheck)` + `(*_3)[_14]`) requires a front-end syntax recognizer lowering into `M_arrslice` (composing with `F1-11`'s `TerminatorKind.assert` bridge).
9. **B9 — Single-frame execution & `slice::len` call lowering only.** Inheriting `Trusted.MirSemantics`'s single-frame model, `.baseTerm (.call ...)` and `.baseTerm .unwindResume` fault `.unsupported`, and `boundsCheckArray` / `boundsCheckSlice` branch to an intra-body `panicBb` rather than unwinding across frames. Only `core::slice::<impl [T]>::len` (`sliceLenCall`) is lowered directly; general interprocedural calls compose via `F1-10` (`MirInline` / `TerminatorKind.call`).
10. **B10 — Intra-block non-interfering `GvnFoldPtrMetadata` window only.** Pass 2 folds `ptrMetadata dst sLoc` to `usizeConst len` when preceded in the same basic block (`unsizeIdx < metaIdx`) by `unsizeArrayToSlice sLoc arrLoc` with no intervening `stmtModifiesSlice sLoc`. Cross-block dominator GVN, copy-propagated slice locals, and `PtrMetadata` folding across `subslice` or `sliceFromRawParts` are left to `SliceScalarize` (and downstream `F1-6` / `F1-7` scalar GVN/CopyProp) rather than folded in Pass 2.
11. **B11 — Staged pass ordering (`LowerSliceLenCalls -> SliceScalarize -> ArrayScalarize`).** `SliceScalarize` rejects unlowered `sliceLenCall` terminators and eliminates all `.sliceView` locals in a body in one pass; `ArrayScalarize` rejects bodies with remaining `.sliceView` locals (`CE11`) and eliminates one `arrLocal` per trace step.
12. **B12 — Conservative `Operand.move` element deinitialization (`deinitMovedPlace = true`).** Matching `Trusted.MirSemantics`, moving a non-ZST scalar/enum element via `readArrayConst ... true` resets that element slot to `none` (`CE6`), a sound over-approximation of upstream `rustc_const_eval` / Miri on `Copy` scalars.
13. **B13 — 64-bit `usize` target & MIR profile v1 (`pointerWidthBits == 64`, `mirProfileVersion == 1`).** Fixes `usize`/`isize` width at 64 bits (`maxUsize = 2^64`); 16-bit and 32-bit target layouts fail closed with `.fault .unsupported`.

## Evidence

- `support/AnnealTrustedMirArraysSlicesPtrMetadataAndScalarize.lean` — `36210`-line (`1939606` bytes) zero-`sorry` Lean 4 proof module (`SHA-256 c65c6f526870a0b48a6993f3c60fdd1fd21fb5e5e1471e63e7cb8aa265f341be`), byte-for-byte faithful to frozen theorem-statement `SHA-256 381d5f87b9d29e34125a834581e58becc4d7ab2e5edf4406953bd4fafacd8434` with `0` non-private inserted declarations, `pub_surface_clean = true`, and `0` `Classical.choice`.
- `support/AnnealTrustedMirArraysSlicesPtrMetadataAndScalarize.frozen.sha256` — SHA-256 digests locking the frozen statement specification and stitched completed proof module.
- `support/multi_kernel_verification_summary.json` (`SHA-256 792a9fd99c256f9b9d03bb12aa1ff2434dcc65506a268d285b7882eb6eb0eaae`) — Complete 6-gate multi-kernel verification receipts (`Lean v4.34.1` `-M4096`, `#print axioms` + `AUDIT_MAP1`, `TrustedBoundary.lean` `"preflight"` pos/neg + Pass 1 `"audit"` with `0` `Classical.choice`, `Lean v4.35.0`, `lean4export 3.1.0`, and `nanoda_bin 0.4.19` pos/neg).
- `support/zerocopy_arrays_slices_index_subslice_and_ptrmetadata_census.json` (`SHA-256 a1c9d727adb6004b1a3da8b328c207f137bd98921e0a6a8a14f74c886f6df8cd`) — Live `rustc 1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`) + `miri 0.1.0` array, slice, `LowerSliceLenCalls`, `UnOp::PtrMetadata`, `ConstantIndex`, `Subslice`, and `NonNull::dangling()` wide-pointer census across `google/zerocopy@a68641199cdfa99f96cb62f0cde921c9d36bfb22` (`0.8.64`).

## Revalidation

1. **Synchronous `Lean v4.34.1` & Unmodified `TrustedBoundary.lean` Pass 1 Audit (`-M4096`):**
   Check out `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, compile `Trusted/MirAst.lean`, `Trusted/MirSemantics.lean`, `Trusted.lean`, and `theory/Anneal/MirWp.lean` with `Lean v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`), then compile `support/AnnealTrustedMirArraysSlicesPtrMetadataAndScalarize.lean` with:
   `lean -M4096 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` (`rc = 0`, `0` warnings).
   Run `#print axioms` over all `26` public `VrustcFormal.F1_15.*` theorems (`23 / 26` strictly `[propext]`, `3 / 26` `[propext, Quot.sound]`, `0` `Classical.choice`, `AUDIT_MAP1 bad = 0`) and run `trusted/audit/TrustedBoundary.lean` in `"preflight"` mode (verifying `ok = true` on `support/AnnealTrustedMirArraysSlicesPtrMetadataAndScalarize.lean` and `rc = 1` rejection on the frozen `sorry` statement) and `"audit"` mode with `axioms = [["Quot.sound", "Init.Prelude"], ["propext", "Init.Core"]]` (`rc = 0`, `ok = true`, `replay = true`, `3805` replayed declarations).
2. **Cross-Version `Lean v4.35.0` & External Rust Kernel Replay (`nanoda_bin 0.4.19`):**
   Compile `Trusted/MirAst.lean`, `Trusted/MirSemantics.lean`, and `support/AnnealTrustedMirArraysSlicesPtrMetadataAndScalarize.lean` on `Lean v4.35.0` (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`) with `-M4096 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` (`rc = 0`), export all `26` public `VrustcFormal.F1_15.*` theorems via `leanexport` (`leanprover/lean4export@5a9a355dc6c5fd82b69058d433e2ae2e8dfbf8fe`, `3.1.0`), and check the resulting NDJSON export with `nanoda_bin` (`ammkrn/nanoda_lib@f55114afa24efe39e007f62d31b7e8ac4243f2a6`, `0.4.19`) under `permitted_axioms: ["propext", "Quot.sound"]` (`rc = 0`, `3147` declarations checked) and `permitted_axioms: []` (`rc = 1`, rejecting `"propext"`).
3. **First-Customer `zerocopy` MIR & Miri Probe Revalidation:**
   Check out `google/zerocopy@a68641199cdfa99f96cb62f0cde921c9d36bfb22` (`0.8.64`) and compile `src/lib.rs` with `rustc 1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`) using `--edition=2021 --crate-name zerocopy --crate-type lib --cfg feature="alloc" --cfg feature="std" --cfg feature="simd" --cfg feature="simd-nightly" --cfg feature="float-nightly" -Copt-level=2 -Zdump-mir="runtime-post-cleanup | LowerSliceLenCalls | runtime-optimized"` to reproduce the census archived in `support/zerocopy_arrays_slices_index_subslice_and_ptrmetadata_census.json`.
