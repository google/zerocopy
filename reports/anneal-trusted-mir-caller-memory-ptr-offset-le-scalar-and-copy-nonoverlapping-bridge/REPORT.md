# `CallerMemory` Byte Allocations, In-Bounds vs. Wrapping `PtrVal` Offsets, Little-Endian Scalar & Pointer Loads/Stores, `copy_nonoverlapping`, and Certified `MemAllocScalarize` Reduction Into `Anneal`'s `Trusted.MirSemantics`

## Summary

In `Anneal`'s unmodified `mirProfileVersion = 1` TCB (`Trusted/MirAst.lean` and `Trusted/MirSemantics.lean`, `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`), `PtrVal`, `AllocByte`, `Allocation`, `CallerMemory`, and `BinOp.offset` are already declared (`Trusted/MirSemantics.lean:415-605`), yet `initState` rejects non-empty `q.callerMem.allocations` and any `.ref`/`.rawPtr` local, `evalBinOp` rejects `BinOp.offset`, `evalRvalue` rejects `.ref`/`.addressOf`, `evalStatement` rejects non-empty `dst.projection`, and `rustc-capture` lowers `StatementKind::Intrinsic(CopyNonOverlapping)` to `.unsupported`. Across `google/zerocopy@4586e91c0e99c9deaf2544e5bba2654127840967` (`0.8.64`, compiled with `rustc 1.102.0-nightly`, `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `support/zerocopy_caller_memory_ptr_offset_le_scalar_and_copy_nonoverlapping_census.json`), live MIR dumps show why both `Runtime(PostCleanup)` and post-inline `-O2` `Runtime(Optimized)` patterns matter: `Runtime(PostCleanup)` (`4737` bodies) has `0` direct `BinOp::Offset` or `CopyNonOverlapping` statements alongside `362` `Rvalue::RawPtr` sites, whereas `-O2` `Runtime(Optimized)` (`4399` bodies) materializes **`11`** `BinOp::Offset` functions, **`5`** `StatementKind::Intrinsic(CopyNonOverlapping)` functions (`zerocopy.IntoBytes-write_to`, `zerocopy.IntoBytes-write_to_prefix`, `zerocopy.IntoBytes-write_to_suffix`, `zerocopy.try_read_from`, `zerocopy.util-copy_unchecked`), **`464`** `Rvalue::RawPtr` sites, **`36`** `UnOp::PtrMetadata` sites, **`22`** `raw_ptr_deref_read` sites, **`2`** `raw_ptr_deref_write` sites, and `try_transmute`'s `read_unaligned`, validated against `23 / 23` live `miri 0.1.0` probes.

Directly importing unmodified `Trusted.MirAst` and `Trusted.MirSemantics` with zero surrogate AST or `Val` types (`support/AnnealTrustedMirCallerMemoryPtrOffsetLeScalarAndCopyNonOverlapping.lean`, `44945` lines, `2377241` bytes, SHA-256 `b9a82ce4b284e9c6c06e9a5c3bf260ccc72e3424378b71554cbec83a05f06930`), `VrustcFormal.F1_16` establishes five core kernel-checked theorems, eleven sharpness counterexamples and witnesses (`CE1`–`CE11`), and an end-to-end 6-step `IntoBytes::write_to_suffix`-style lowering pipeline executing directly inside unmodified `Trusted.MirSemantics`:

1. **Exact conservative extension `M_memcopy` over unmodified `Trusted.MirAst.Program` (`memcopy_conservative_extension_exact`).** Conservatively extending `Trusted.MirSemantics` with `.byteBuf size alignLog2 mutability` frame allocations (`allocId = 65536 + localId`), `.ptrLocal` slots (`Option PtrVal`), caller-supplied `CallerMemory` (`acceptsCallerMem = true`, persistent `Out.callerMem`, and `projectExternalCallerMem` stripping frame-internal allocations on return), wrapping vs. `inbounds` `PtrVal` arithmetic (`ptrWrappingOffset`, `ptrOffsetInbounds`), little-endian 1/2/4/8-byte scalar loads/stores (`readLeUsize`, `writeLeUsize` with `ReadPointerAsInt` provenance firewall), 8-byte provenance-preserving pointer memory R/W (`readPtrLe8`, `writePtrLe8`), and `copy_nonoverlapping` preserves 1-step lockstep execution (`evalStepMemCopy (embedBaseProgram p) c (embedMemCopyState s) = liftStepResultMemCopy (evalStep p c s)`) and bidirectional (`↔`) equivalence across `WellFormed`, `Behavior`, `ReachesResult (.fault k)`, `Diverges`, and `SatisfiesPost` for every unmodified base program. `Basis: execution (Lean kernel)`
2. **Bidirectional soundness of `FoldZeroOffset` & `FoldGuardedZeroCopy` (`foldZeroOffset_and_guardedZeroCopy_sound_bidirectional_iff`).** Statement-level `ptrWrappingOffset -> copyPtr` folding (`checkFoldZeroOffsetStmt`), terminator-level `ptrOffsetInbounds -> copyPtr + goto` folding (`checkFoldZeroOffsetTerm`), and alignment/non-null-guarded `copyNonOverlapping(..., 0) -> checkPtrPairAlign` folding (`checkFoldGuardedZeroCopy`) all preserve `FullSemanticEquivMemCopy pSrc pTgt` across arbitrary `Query` values including `acceptsCallerMem = true` programs (proved strictly under `[propext]`, `0` `Quot.sound`, `0` `Classical.choice`). `Basis: source + execution (Lean kernel)`
3. **Exact algebraic & operational laws matching `rustc_const_eval` + `Miri` (`inboundsOffset_leRoundTrip_and_copyNonOverlapping_laws`).** Proves strictly under `[propext]`: (i) `calcInboundsOffset mem pv count elemSize = .ok { pv with width := .isize }` whenever `count * elemSize = 0` (even on `null` and `NonNull::dangling()`); (ii) opposite-sign `calcWrappingOffset` round-trips recover `{ pv with width := .isize }` across out-of-bounds excursions; (iii) `decodeLeUsize w (encodeLeUsize w n) = .ok n` for `n < 2^w.bitWidth` while faulting `.error .undefined` on any `.uninit` or provenance-carrying byte (`ReadPointerAsInt`), paired with `decodePtrLe8` round-tripping 8-byte `Option AllocId` provenance; and (iv) an exact iff characterizing zero-byte `evalCopyNonOverlapping` via alignment + conditional null check, matching `E3-137`'s raw-intrinsic vs. `core::ptr::copy_nonoverlapping` null split. `Basis: execution (Miri + Lean kernel)`
4. **Certified `MemAllocScalarize` (`PtrScalarize` + `BufScalarize`) reducing 100% into unmodified `Trusted.MirSemantics` (`memAllocScalarize_reduces_to_trusted_mir`).** Any finite `MemCopyOptTrace` verified by `checkMemCopyToTrustedMir trace pSrc pMir = true` eliminates all `.ptrLocal` locals via `(liveLoc, tagLoc, offLoc)` (`1` = buffer, `0` = null/dangling) + branchless `subUnchecked` UB/bounds traps (`readLeUsize`/`writeLeUsize` and `copyNonOverlapping` byte-copy loops targeting raw-byte `readBufRawByte`/`writeBufRawByte` terminators), and then eliminates each `.byteBuf size alignLog2 mutability` (`size ≤ 32`) into `liveLoc + 2 * size` `usize` tag/val locals dispatched via `SwitchInt` jump tables and `.unreachable` trap blocks, reducing `M_memcopy` bidirectionally (`↔`) into unmodified `Trusted.MirSemantics`. `Basis: execution (Lean kernel)`
5. **Vertical pipeline composition, 11 sharpness witnesses (`CE1`–`CE11`), Stage 5 blind spec audit (`PASS_WITH_BOUNDARY_NOTES`), & 6-gate multi-kernel replay (`memCopyPipeline_then_optPipeline_vc_transport`).** Composing `checkMemCopyToTrustedMir` with any `FullSemanticEquivBase pMir pOpt` transports all five judgments bidirectionally (`↔`) onto `pOpt`. Independent frontier Stage 5 specification audit returned **`PASS_WITH_BOUNDARY_NOTES`** (`0` blocking soundness or vacuity defects; 14 documented scope boundaries `B1`–`B14`). All `27` public theorems (`25 / 27` strictly `[propext]`, `2 / 27` `[propext, Quot.sound]`, `0` `Classical.choice`, `0` `sorryAx`, `AUDIT_MAP1 total=2979 pub=1035 priv=1944 bad=0`, `pub_surface_clean = true`) compile on `Lean v4.34.1` (`-M4096 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`) in **`274.8681 s` / `2916.3 MB` RSS**, pass unmodified `TrustedBoundary.lean` `"preflight"` (`ok = true`) and Pass 1 `"audit"` (`replayedDeclarations = 4560`, `reachableDeclarations = 5642`, `axioms = ["propext", "Quot.sound"]`, `replay = true`), compile on `Lean v4.35.0` in **`198.4192 s` / `2827.9 MB` RSS**, export via `lean4export 3.1.0` (`1884301` NDJSON lines, `99847845` bytes), and pass `nanoda_bin 0.4.19` (`3947` declarations in **`27.3223 s` / `390.19 MB` RSS**, negative `permitted_axioms: []` control rejected at `rc = 1`). `Basis: execution`

## Applicability

- **Primary formal verification target (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, citing `rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd`):** Unmodified `Trusted.MirAst.Program` and `Trusted.MirSemantics` (`mirProfileVersion = 1`, `pointerWidthBits = 64`), activating and extending the latent `PtrVal`, `AllocByte`, `Allocation`, `CallerMemory`, and `BinOp.offset` primitives (`Trusted/MirSemantics.lean:415-605`) without enlarging Anneal's TCB.
- **Upstream compiler semantics & live `zerocopy` + `Miri` ground truth:** `rust-lang/rust@49d734536222bf28bb6d07d885b3a81d145981da` (`compiler/rustc_const_eval/src/interpret/{operator.rs, intrinsics.rs, memory.rs, place.rs, operand.rs}`, `compiler/rustc_middle/src/mir/interpret/allocation.rs`, `library/core/src/{ptr/mod.rs, ub_checks.rs}`), vendored `proofs-rs/lean-miri` (`vendor/lean-miri/Miri/{Interpreter/{PointerOffset,Intrinsics,Memory}.lean, Memory/Access.lean}`), and `rustc 1.102.0-nightly` + `miri 0.1.0` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `2026-11-11`, `LLVM 23.1.5`) evaluated against `google/zerocopy@4586e91c0e99c9deaf2544e5bba2654127840967` (`0.8.64`, `support/zerocopy_caller_memory_ptr_offset_le_scalar_and_copy_nonoverlapping_census.json`).
- **Independent Lean 4 kernels & external verifier pins:** `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`), `leanprover/lean4@eb6cafb7290e8bd5f2937522d8d804f58f02bafc` (`v4.35.0`), `leanprover/lean4export@5a9a355dc6c5fd82b69058d433e2ae2e8dfbf8fe` (`3.1.0`), and `ammkrn/nanoda_lib@f55114afa24efe39e007f62d31b7e8ac4243f2a6` (`0.4.19`).
- **Intended consumers:** Proof engineers lowering fixed-size byte-buffer serialization (`IntoBytes::write_to{,_prefix,_suffix}`), pointer offset loops, misaligned scalar reads/writes (`FromBytes`, `try_transmute`), and `copy_nonoverlapping` into unmodified `Trusted.MirSemantics`, plus compiler authors auditing zero-offset and guarded zero-byte copy elisions.

## Findings

### 1. First-Customer `zerocopy 0.8.64` Census & Live `Miri` Ground-Truth Matrix (`E3-137`)

`Basis: execution (support/zerocopy_caller_memory_ptr_offset_le_scalar_and_copy_nonoverlapping_census.json) + source (rust-lang/rust@49d734536222bf28bb6d07d885b3a81d145981da, google/zerocopy@4586e91c0e99c9deaf2544e5bba2654127840967)`

Compiling `google/zerocopy@4586e91c0e99c9deaf2544e5bba2654127840967` (`src/lib.rs`, `--cfg feature="alloc" --cfg feature="std"`) with `rustc 1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`) at `-Copt-level=0` and `-Copt-level=2` across `Runtime(PostCleanup)` (the `trusted/rustc-capture` capture boundary) and `Runtime(Optimized)` yields:

| MIR Construct (`google/zerocopy@4586e91c0e99c9deaf2544e5bba2654127840967`, `0.8.64`) | `-O0 PostCleanup` | `-O0 Optimized` | `-O2 PostCleanup` | `-O2 Optimized` |
| :--- | :---: | :---: | :---: | :---: |
| Total MIR bodies dumped | `4737` | `4397` | `4737` | `4399` |
| `BinOp::Offset` (`ptr.offset` / `ptr.add`) | `0` | `0` | `0` | **`11`** |
| `StatementKind::Intrinsic(CopyNonOverlapping)` | `0` | `0` | `0` | **`5`** |
| `Rvalue::RawPtr` | `362` | `362` | `362` | **`464`** |
| `UnOp::PtrMetadata` | `2` | `16` | `2` | **`36`** |
| `raw_ptr_deref_read` | `0` | `0` | `0` | **`22`** |
| `raw_ptr_deref_write` | `0` | `0` | `0` | **`2`** |
| `mentions_read_unaligned` (`try_transmute`) | `1` | `1` | `1` | `1` |

Key empirical observations from `E3-137` (`support/zerocopy_caller_memory_ptr_offset_le_scalar_and_copy_nonoverlapping_census.json`):

1. **Cross-crate MIR inlining drives raw-pointer ops (`PostCleanup` vs. `-O2 Optimized`):** At `Runtime(PostCleanup)`, `zerocopy` has `0` direct `BinOp::Offset` or `CopyNonOverlapping` statements because pointer offsets and bulk byte copies still live behind `TerminatorKind::Call` into `core::ptr::copy_nonoverlapping` (`util::copy_unchecked`), `core::ptr::offset`, and `core::slice::split_at_unchecked`. Under `-Copt-level=2` `Runtime(Optimized)`, cross-crate inlining materializes `11` `BinOp::Offset` bodies (`IntoBytes::write_to_suffix`, `FromZeros::insert_vec_zeroed`, `byte_slice::*split_at_unchecked`, `pointer::inner::*`, `pointer::is_zeroed`), `5` `CopyNonOverlapping` bodies (`zerocopy.IntoBytes-write_to`, `zerocopy.IntoBytes-write_to_prefix`, `zerocopy.IntoBytes-write_to_suffix`, `zerocopy.try_read_from`, `zerocopy.util-copy_unchecked`), and `22` raw-pointer dereference reads (`FromBytes::read_from_{bytes,prefix,suffix}`, `transmute::*is_safe`) alongside `2` raw-pointer dereference writes (`ref::{impl#11}::write`, `wrappers::{impl#1}::update::{impl#0}::drop`).
2. **Concrete `zerocopy::util::copy_unchecked` & `IntoBytes::write_to_suffix` MIR excerpts (`support/zerocopy_caller_memory_ptr_offset_le_scalar_and_copy_nonoverlapping_census.json`):**

```mir
// MIR for `util::copy_unchecked` after runtime-optimized

fn copy_unchecked(_1: &[u8], _2: &mut [u8]) -> () {
    debug src => _1;
    debug dst => _2;
    let mut _0: ();
    let mut _3: *const u8;
    let mut _4: *mut u8;
    let mut _5: usize;
    scope 1 (inlined core::slice::<impl [u8]>::as_ptr) {
        let mut _6: *const [u8];
    }
    scope 2 (inlined core::slice::<impl [u8]>::as_mut_ptr) {
        let mut _7: *mut [u8];
    }
    scope 3 (inlined std::ptr::copy_nonoverlapping::<u8>) {
        scope 4 (inlined ub_checks::check_language_ub) {
            scope 5 (inlined ub_checks::check_language_ub::runtime) {
            }
        }
        scope 6 (inlined std::mem::size_of::<u8>) {
        }
        scope 7 (inlined std::mem::align_of::<u8>) {
        }
    }

    bb0: {
        StorageLive(_3);
        StorageLive(_6);
        _6 = &raw const (*_1);
        _3 = copy _6 as *const u8 (PtrToPtr);
        StorageDead(_6);
        StorageLive(_4);
        StorageLive(_7);
        _7 = &raw mut (*_2);
        _4 = copy _7 as *mut u8 (PtrToPtr);
        StorageDead(_7);
        StorageLive(_5);
        _5 = PtrMetadata(copy _1);
        copy_nonoverlapping(dst = copy _4, src = copy _3, count = copy _5);
        StorageDead(_5);
        StorageDead(_4);
        StorageDead(_3);
        _0 = const ();
        return;
    }
}
```

Excerpt from `IntoBytes::write_to_suffix` (`Runtime(Optimized)`, combining `SubUnchecked`, `Offset`, and `copy_nonoverlapping`):

```mir
    bb0: {
        _3 = <Self as IntoBytes>::as_bytes(copy _1) -> [return: bb1, unwind continue];
    }

    bb1: {
        StorageLive(_4);
        _5 = PtrMetadata(copy _2);
        _6 = PtrMetadata(copy _3);
        StorageLive(_12);
        _12 = Lt(copy _5, copy _6);
        switchInt(move _12) -> [0: bb5, otherwise: bb4];
    }

    bb2: {
        goto -> bb3;
    }

    bb3: {
        return;
    }

    bb4: {
        StorageDead(_12);
        StorageLive(_8);
        _8 = error::SizeError::<&Self, &mut [u8]> { src: copy _1, _dst: const SendSyncPhantomData::<&mut [u8]>(std::marker::PhantomData::<&mut [u8]>) };
        _0 = Result::<(), error::SizeError<&Self, &mut [u8]>>::Err(move _8);
        StorageDead(_8);
        StorageDead(_4);
        goto -> bb2;
    }

    bb5: {
        StorageLive(_13);
        _13 = SubUnchecked(copy _5, copy _6);
        _4 = Option::<usize>::Some(move _13);
        StorageDead(_13);
        StorageDead(_12);
        _7 = copy ((_4 as Some).0: usize);
        StorageDead(_4);
        StorageLive(_9);
        StorageLive(_19);
        StorageLive(_18);
        _18 = Lt(copy _5, copy _7);
        switchInt(move _18) -> [0: bb9, otherwise: bb8];
    }

    bb6: {
        StorageLive(_15);
        StorageLive(_16);
        StorageLive(_17);
        _17 = &raw mut (*_2);
        StorageLive(_20);
        _20 = copy _17 as *mut u8 (PtrToPtr);
        StorageLive(_21);
        _21 = Offset(copy _20, copy _7);
        _16 = *mut [u8] from (copy _21, copy _19);
        StorageDead(_21);
        StorageDead(_20);
        StorageDead(_17);
        _15 = &mut (*_16);
        _9 = Option::<&mut [u8]>::Some(copy _15);
        StorageDead(_16);
        StorageDead(_15);
        StorageDead(_14);
        StorageDead(_19);
        _10 = copy ((_9 as Some).0: &mut [u8]);
        StorageDead(_9);
        StorageLive(_22);
        StorageLive(_24);
        _24 = &raw const (*_3);
        _22 = copy _24 as *const u8 (PtrToPtr);
        StorageDead(_24);
        StorageLive(_23);
        StorageLive(_25);
        _25 = &raw mut (*_10);
        _23 = copy _25 as *mut u8 (PtrToPtr);
        StorageDead(_25);
        copy_nonoverlapping(dst = copy _23, src = copy _22, count = copy _6);
        StorageDead(_23);
        StorageDead(_22);
        _0 = Result::<(), error::SizeError<&Self, &mut [u8]>>::Ok(const ());
        goto -> bb3;
    }

    bb7: {
        StorageDead(_14);
        StorageDead(_19);
        StorageLive(_11);
        _11 = error::SizeError::<&Self, &mut [u8]> { src: copy _1, _dst: const SendSyncPhantomData::<&mut [u8]>(std::marker::PhantomData::<&mut [u8]>) };
        _0 = Result::<(), error::SizeError<&Self, &mut [u8]>>::Err(move _11);
```

3. **All `23` Live `Miri 0.1.0` Ground-Truth Probes (`E3-137` Experiment B):**

| Probe | Category | `Miri` Result | Default `rustc` Lint | Observed Ground Truth |
| :--- | :--- | :---: | :---: | :--- |
| `offset_one_past_end_ok` | `ptr_offset` | `rc = 0` | — | rc=0 (one-past-end allowed) |
| `offset_two_past_end_ub` | `ptr_offset` | `rc = 1` | — | rc=1 (PointerOutOfBounds) |
| `offset_zero_null_ok` | `ptr_offset` | `rc = 0` | — | rc=0 (zero offset on null) |
| `offset_zero_dangling_ok` | `ptr_offset` | `rc = 0` | — | rc=0 (zero offset on dangling) |
| `offset_one_null_ub` | `ptr_offset` | `rc = 1` | — | rc=1 (DanglingIntPointer) |
| `offset_one_dangling_zst_ok` | `ptr_offset` | `rc = 0` | — | rc=0 (1 * 0 = 0 bytes on ZST) |
| `offset_one_dangling_non_zst_ub` | `ptr_offset` | `rc = 1` | — | rc=1 (DanglingIntPointer) |
| `wrapping_offset_roundtrip_ok` | `ptr_offset` | `rc = 0` | — | rc=0 (wrapping_offset preserves provenance across OOB round-trip) |
| `offset_out_and_back_ub` | `ptr_offset` | `rc = 1` | — | rc=1 (PointerOutOfBounds on intermediate offset) |
| `cno_zero_dangling_aligned_ok` | `copy_nonoverlapping` | `rc = 0` | — | rc=0 (count=0 with aligned NonNull::dangling) |
| `cno_zero_null_src_under_allow_lint` | `copy_nonoverlapping` | `rc = 0` | `rc = 1` | compile rc=101 under default #[deny(invalid_null_arguments)]; runtime rc=0 under #![allow(invalid_null_arguments)] because copy_intrinsic alignment passes for 0x0 and check_and_deref_ptr short-circuits size==0 |
| `cno_zero_misaligned_u32_ub` | `copy_nonoverlapping` | `rc = 1` | — | rc=1 (AlignmentCheckFailed even when count=0) |
| `cno_count_byte_size_overflow_isize_max_ub` | `copy_nonoverlapping` | `rc = 1` | — | rc=1 (overflow computing total size of copy_nonoverlapping) |
| `cno_overlap_ub` | `copy_nonoverlapping` | `rc = 1` | — | rc=1 (overlapping ranges [0..3] -> [1..4]) |
| `cno_adjacent_ok` | `copy_nonoverlapping` | `rc = 0` | — | rc=0 (adjacent ranges [0..2] -> [2..4]) |
| `cno_partial_uninit_preserves_uninit_ok_until_read` | `copy_nonoverlapping` | `rc = 0` | — | rc=0 (per-byte init/uninit mask copied faithfully) |
| `cno_partial_uninit_read_uninit_byte_ub` | `copy_nonoverlapping` | `rc = 1` | — | rc=1 (InvalidUninitBytes when reading copied uninit byte) |
| `cno_pointer_bytes_preserve_provenance_ok` | `copy_nonoverlapping` | `rc = 0` | — | rc=0 (bytewise copy preserves pointer provenance) |
| `read_pointer_bytes_as_usize_ptr_to_int_behavior` | `copy_nonoverlapping` | `rc = 1` | — | rc=1 under Miri (reading pointer as usize strips provenance without exposing) |
| `le_u32_deref_load_ok` | `le_scalar_load_store` | `rc = 0` | — | rc=0 (*ptr_u32 on [0x78, 0x56, 0x34, 0x12] == 0x12345678) |
| `le_u32_misaligned_deref_ub` | `le_scalar_load_store` | `rc = 1` | — | rc=1 (AlignmentCheckFailed) |
| `le_u32_misaligned_read_unaligned_ok` | `le_scalar_load_store` | `rc = 0` | — | rc=0 (read_unaligned yields 0x12345678) |
| `write_to_immutable_ref_cast_ub` | `le_scalar_load_store` | `rc = 1` | `rc = 1` | compile rc=101 under default #[deny(invalid_reference_casting)]; runtime rc=1 under Miri SharedReadOnly retag |

Notably, `cno_zero_null_src_under_allow_lint` exposes a real rustc/Miri bifurcation: `core::ptr::copy_nonoverlapping(null, dst, 0)` hits `#[deny(invalid_null_arguments)]` + `ub_checks::maybe_is_aligned_and_not_null` (`checkNonNullZero = true`), whereas lowering straight to `StatementKind::Intrinsic(CopyNonOverlapping)` (`checkNonNullZero = false`, bypassing `core::ptr`'s UB precondition under `#![allow(invalid_null_arguments)]`) passes Miri cleanly at `count = 0` because `0x0` satisfies alignment checks and `mem_copy_repeatedly` short-circuits `size == 0`!

---

### 2. Operational Semantics of `M_memcopy` Conservatively Extending `Trusted.MirSemantics`

`Basis: execution (Lean kernel, support/AnnealTrustedMirCallerMemoryPtrOffsetLeScalarAndCopyNonOverlapping.lean)`

`VrustcFormal.F1_16` builds `M_memcopy` directly atop unmodified `Trusted.MirAst` and `Trusted.MirSemantics` (`prelude`, `import Trusted.MirAst`, `import Trusted.MirSemantics`), activating base `PtrVal`, `AllocByte`, `Allocation`, and `CallerMemory` (`Trusted/MirSemantics.lean:415-605`).

#### 2.1 `MemCopyProgram` Syntax, `CallerMemory` Allocations, and `.byteBuf` Frame Storage

```lean
inductive MemCopyLocalDecl where
  | base (ty : MirTy)
  | byteBuf (size : Nat) (alignLog2 : Nat) (mutability : Mutability)
  | ptrLocal

noncomputable def memCopyLocalDeclEq :
    MemCopyLocalDecl → MemCopyLocalDecl → Bool
  | .base t₁, .base t₂ => MirTy.beq t₁ t₂
  | .byteBuf s₁ a₁ m₁, .byteBuf s₂ a₂ m₂ =>
    Nat.beq s₁ s₂ && Nat.beq a₁ a₂ && Mutability.beq m₁ m₂
  | .ptrLocal, .ptrLocal => true
  | _, _ => false

/-- Straight-line statements in `M_memcopy`. -/
inductive MemCopyStmt where
  | baseStmt (stmt : StatementKind)
  | bufLivenessCheck (bufLocal : LocalId)
  | mkNullPtr (dstPtr : LocalId)
  | mkDanglingPtr (dstPtr : LocalId) (alignLog2 : Nat)
  | addrOfByteBuf (dstPtr : LocalId) (bufLocal : LocalId)
  | copyPtr (dstPtr : LocalId) (srcPtr : LocalId) (isMove : Bool)
  | ptrWrappingOffset (dstPtr : LocalId) (srcPtr : LocalId)
      (countOp : Operand) (elemSize : Nat)

noncomputable def memCopyStmtEq : MemCopyStmt → MemCopyStmt → Bool
  | .baseStmt s₁, .baseStmt s₂ => stmtEq s₁ s₂
  | .bufLivenessCheck b₁, .bufLivenessCheck b₂ => Nat.beq b₁ b₂
  | .mkNullPtr d₁, .mkNullPtr d₂ => Nat.beq d₁ d₂
  | .mkDanglingPtr d₁ a₁, .mkDanglingPtr d₂ a₂ =>
    Nat.beq d₁ d₂ && Nat.beq a₁ a₂
  | .addrOfByteBuf d₁ b₁, .addrOfByteBuf d₂ b₂ =>
    Nat.beq d₁ d₂ && Nat.beq b₁ b₂
  | .copyPtr d₁ s₁ m₁, .copyPtr d₂ s₂ m₂ =>
    Nat.beq d₁ d₂ && Nat.beq s₁ s₂ && boolEq m₁ m₂
  | .ptrWrappingOffset d₁ s₁ c₁ e₁, .ptrWrappingOffset d₂ s₂ c₂ e₂ =>
    Nat.beq d₁ d₂ && Nat.beq s₁ s₂ && operandEq c₁ c₂ && Nat.beq e₁ e₂
  | _, _ => false

/-- Terminators in `M_memcopy` (control flow, `BinOp.offset` in-bounds pointer
arithmetic, pure alignment/non-null guards, LE loads/stores, and
`copy_nonoverlapping`). -/
inductive MemCopyTerm where
  | baseTerm (term : TerminatorKind)
  | ptrOffsetInbounds (dstPtr : LocalId) (srcPtr : LocalId)
      (countOp : Operand) (elemSize : Nat) (nextBb : BasicBlockId)
  | checkPtrPairAlign (srcPtr dstPtr : LocalId) (elemSize reqAlignLog2 : Nat)
      (checkNonNullZero : Bool) (nextBb : BasicBlockId)
  | readLeUsize (dstLocal : LocalId) (ptrLocal : LocalId)
      (w : LeWidth) (requireAligned : Bool) (nextBb : BasicBlockId)
  | writeLeUsize (ptrLocal : LocalId) (valOp : Operand)
      (w : LeWidth) (requireAligned : Bool) (nextBb : BasicBlockId)
  | readPtrLe8 (dstPtr : LocalId) (addrPtr : LocalId)
      (requireAligned : Bool) (nextBb : BasicBlockId)
  | writePtrLe8 (addrPtr : LocalId) (valPtr : LocalId)
      (requireAligned : Bool) (nextBb : BasicBlockId)
  | copyNonOverlapping (srcPtr dstPtr : LocalId) (countOp : Operand)
      (elemSize reqAlignLog2 : Nat) (checkNonNullZero : Bool)
      (nextBb : BasicBlockId)
  | readBufRawByte (tagDst valDst : LocalId) (bufLocal : LocalId)
      (offOp : Operand) (nextBb : BasicBlockId)
  | writeBufRawByte (bufLocal : LocalId) (offOp tagOp valOp : Operand)
      (nextBb : BasicBlockId)
```

- **Signature vs. internal allocation separation:** Function bodies with `acceptsCallerMem = true` accept `Val.ptr` caller arguments backed by external `Allocation`s (`allocId < internalAllocBase := 65536`, verified pairwise distinct and bounded via `wfExternalCallerMem`), preserve mutations in external allocations upon `.return_`, and strip frame-owned `.byteBuf` allocations (`allocId = 65536 + localId`) via `projectExternalCallerMem`. Escaping a pointer to an internal frame `.byteBuf` (`allocId ≥ 65536`) in `.return_` deterministically faults `.fault .undefined` (`CE8`).
- **Frame `.byteBuf` lifecycle (`CE9`):** `StorageLive id` allocates/resets `allocId := 65536 + id` with `listReplicate size .uninit` and `live := true`; `StorageDead id` marks `live := false` and resets bytes to `.uninit` (rejecting `id = 0` to match `Trusted.MirSemantics`). Dangling reads after `StorageDead` fault `.undefined` (`alloc.live == false`), and subsequent `StorageLive` resets bytes to `.uninit` (`CE9`).

#### 2.2 In-Bounds vs. Wrapping `PtrVal` Offsets, Provenance Firewall `decodeLeUsize`, & `evalCopyNonOverlapping`

```lean
noncomputable def calcWrappingOffset (pv : PtrVal) (count : Int)
    (elemSize : Nat) : PtrVal :=
  let m : Int := Int.ofNat maxUsize
  let wrapped : Int :=
    intEmod (Int.ofNat pv.offsetBytes.toNat + count * Int.ofNat elemSize) m
  { pv with offsetBytes := UInt64.ofNat wrapped.toNat, width := .isize }

/-- In-bounds pointer arithmetic (`BinOp.offset` / `ptrOffsetInbounds`,
`vendor/lean-miri/Miri/Interpreter/PointerOffset.lean:14-21` &
`compiler/rustc_const_eval/src/interpret/operator.rs:326-357`). -/
noncomputable def calcInboundsOffset (mem : CallerMemory) (pv : PtrVal)
    (count : Int) (elemSize : Nat) : Except FaultKind PtrVal :=
  let delta : Int := count * Int.ofNat elemSize
  if decide (delta < minIsize) || decide (Int.ofNat maxIsize < delta) then
    .error .undefined
  else if delta == 0 then
    .ok { pv with width := .isize }
  else
    match pv.allocId with
    | none => .error .undefined
    | some aid =>
      match findAlloc? aid mem.allocations with
      | none => .error .undefined
      | some alloc =>
        if !alloc.live then
          .error .undefined
        else
          let off : Int := Int.ofNat pv.offsetBytes.toNat
          let len : Int := Int.ofNat alloc.bytes.length
          let newOff : Int := off + delta
          if decide (0 ≤ off) && decide (off ≤ len) &&
              decide (0 ≤ newOff) && decide (newOff ≤ len) then
            .ok { pv with offsetBytes := UInt64.ofNat newOff.toNat, width := .isize }
          else
            .error .undefined

/-- Encode the low `k` little-endian bytes of `n` with optional provenance `prov`. -/
noncomputable def encodeLeBytesAux (prov : Option AllocId) :
    Nat → Nat → List AllocByte
  | 0, _ => []
  | k + 1, n =>
    AllocByte.init (UInt8.ofNat (Nat.mod n 256)) prov ::
      encodeLeBytesAux prov k (Nat.div n 256)

noncomputable def encodeLeUsize (w : LeWidth) (n : Nat) : List AllocByte :=
  encodeLeBytesAux none w.byteCount n

/-- Decode a list of `AllocByte`s as a little-endian unsigned scalar integer,
faulting `.undefined` if any byte is `.uninit` (`InvalidUninitBytes`) or carries
`some provAid` pointer provenance (`ReadPointerAsInt`). -/
noncomputable def decodeLeBytesAux : List AllocByte → Except FaultKind Nat
  | [] => .ok 0
  | .uninit :: _ => .error .undefined
  | .init _ (some _) :: _ => .error .undefined
  | .init b none :: rest =>
    match decodeLeBytesAux rest with
    | .ok hi => .ok (b.toNat + 256 * hi)
    | .error k => .error k

noncomputable def decodeLeUsize (w : LeWidth) (bs : List AllocByte) :
    Except FaultKind Nat :=
  if !Nat.beq bs.length w.byteCount then
    .error .unsupported
  else
    decodeLeBytesAux bs

/-- Decode 8 `AllocByte`s as a 64-bit `PtrVal`, requiring all 8 bytes to be
initialized and carry identical `Option AllocId` provenance (`none` or the same
`some aid`). -/
```

Exact `evalCopyNonOverlapping` kernel (`support/AnnealTrustedMirCallerMemoryPtrOffsetLeScalarAndCopyNonOverlapping.lean`):

```lean
noncomputable def evalCopyNonOverlapping (mem : CallerMemory)
    (pvSrc pvDst : PtrVal) (count elemSize reqAlignLog2 : Nat)
    (checkNonNullZero : Bool) : Except FaultKind CallerMemory :=
  let byteLen := elemSize * count
  if !Nat.ble reqAlignLog2 30 then
    .error .unsupported
  else if !Nat.ble byteLen maxIsize then
    .error .undefined
  else
    match checkPtrAlignMem mem pvSrc reqAlignLog2,
        checkPtrAlignMem mem pvDst reqAlignLog2 with
    | .error k, _ => .error k
    | _, .error k => .error k
    | .ok (), .ok () =>
      if checkNonNullZero && (isNullPtr pvSrc || isNullPtr pvDst) then
        .error .undefined
      else if Nat.beq byteLen 0 then
        .ok mem
      else
        match pvSrc.allocId, pvDst.allocId with
        | some srcAid, some dstAid =>
          match findAlloc? srcAid mem.allocations,
              findAlloc? dstAid mem.allocations with
          | some srcAlloc, some dstAlloc =>
            let srcOff := pvSrc.offsetBytes.toNat
            let dstOff := pvDst.offsetBytes.toNat
            let nonOverlap : Bool :=
              !Nat.beq srcAid dstAid ||
                Nat.ble (srcOff + byteLen) dstOff ||
                Nat.ble (dstOff + byteLen) srcOff
            if !srcAlloc.live || !dstAlloc.live ||
                !(Mutability.beq dstAlloc.mutability .mut) ||
                !Nat.ble (srcOff + byteLen) srcAlloc.bytes.length ||
                !Nat.ble (dstOff + byteLen) dstAlloc.bytes.length ||
                !nonOverlap then
              .error .undefined
            else
              let snap := (srcAlloc.bytes.drop srcOff).take byteLen
              let dstUpdated : Allocation :=
                { dstAlloc with bytes := spliceBytes dstAlloc.bytes dstOff snap }
              match updateAlloc? dstAid dstUpdated mem.allocations with
              | some allocs' => .ok ⟨allocs'⟩
              | none => .error .unsupported
          | _, _ => .error .undefined
        | _, _ => .error .undefined
```

Key invariants matching `rustc_const_eval` + `lean-miri` + `E3-137`:
1. **`ptrOffsetInbounds` vs. `ptrWrappingOffset`:** When `delta == 0` (`count == 0` or `elemSize == 0`), `calcInboundsOffset` succeeds for every `PtrVal` including `null` (`none, 0`) and `NonNull::dangling()` (e.g., `1_isize` on ZSTs). When `delta ≠ 0`, `calcInboundsOffset` requires `minIsize ≤ delta ≤ maxIsize`, `allocId = some aid`, `alloc.live = true`, `0 ≤ off ≤ alloc.bytes.length`, and `0 ≤ off + delta ≤ alloc.bytes.length` (allowing one-past-end while rejecting two-past-end or out-and-back excursions, `CE1`). `calcWrappingOffset` computes modular 64-bit arithmetic `(off + count * elemSize) mod 2^64` preserving `allocId` provenance (`Theorem 3`).
2. **Endian round-trip & Provenance Firewall (`CE2`, `CE7`, `Theorem 3`):** `encodeLeUsize w n` encodes `w.byteCount ∈ {1, 2, 4, 8}` little-endian bytes with `none` provenance; `decodeLeUsize` faults `.error .undefined` on any `.uninit` (`InvalidUninitBytes`) or `some aid` provenance byte (`ReadPointerAsInt`, `CE7`), while `writePtrLe8`/`readPtrLe8` preserve 8-byte uniform `Option AllocId` provenance (`CE7`). Unaligned reads/writes pass `requireAligned = false` (`reqAlign = 0`, matching `ptr::read_unaligned`) while typed derefs pass `requireAligned = true` (`reqAlign = w.naturalAlignLog2`, `CE2`).
3. **`copy_nonoverlapping` preconditions & bytewise copy (`CE3`–`CE6`):** Checks `reqAlignLog2 ≤ 30`, `byteLen = elemSize * count ≤ maxIsize`, unconditional alignment of both `pvSrc` and `pvDst` even when `byteLen == 0`, optional null rejection `checkNonNullZero && (isNullPtr pvSrc || isNullPtr pvDst)` (`CE3`), early return `.ok mem` at `byteLen == 0` without dereferencing `NonNull::dangling()`, liveness, `.mut` destination mutability, in-range bounds, same-allocation interval disjointness (`srcOff + byteLen ≤ dstOff ∨ dstOff + byteLen ≤ srcOff`, `CE5`), and per-byte `.uninit` + provenance snapshot copy (`CE6`–`CE7`).

---

### 3. Certified Lowering Pipeline Into Unmodified `Trusted.MirSemantics`

`Basis: execution (Lean kernel, support/AnnealTrustedMirCallerMemoryPtrOffsetLeScalarAndCopyNonOverlapping.lean)`

#### 3.1 Pass 1 (`FoldZeroOffset`) & Pass 2 (`FoldGuardedZeroCopy`)

```lean
/-! ### Pass 1: `FoldZeroOffset` (`ptrWrappingOffset` & `ptrOffsetInbounds` Zero-Byte Folding) -/

/-- Whether `(countOp, elemSize)` is a well-formed `usize`/`isize` constant
whose byte delta `count * elemSize` equals `0`. -/
noncomputable def isZeroOffsetConst (countOp : Operand)
    (elemSize : Nat) : Bool :=
  match countOp with
  | .constant c =>
    if !(MirTy.beq c.ty usizeTy) && !(MirTy.beq c.ty isizeTy) then
      false
    else
      match evalConstLit c.ty c.lit with
      | .ok (.scalar sv) =>
        sv.wf && (decodeScalar sv * Int.ofNat elemSize == 0)
      | _ => false
  | _ => false

noncomputable def applyFoldZeroOffsetStmt (bodyId : DefId)
    (bbIdx : BasicBlockId) (stmtIdx : Nat)
    (pSrc : MemCopyProgram) : Option MemCopyProgram :=
  match Trusted.MirSemantics.getElem? pSrc.bodies bodyId with
  | none => none
  | some body =>
    match Trusted.MirSemantics.getElem? body.basicBlocks bbIdx with
    | none => none
    | some bb =>
      match Trusted.MirSemantics.getElem? bb.statements stmtIdx with
      | some (.ptrWrappingOffset dstPtr srcPtr countOp elemSize) =>
        if !isZeroOffsetConst countOp elemSize then
          none
        else
          match setElem? bb.statements stmtIdx (.copyPtr dstPtr srcPtr false) with
          | none => none
          | some stmts' =>
            match setElem? body.basicBlocks bbIdx { bb with statements := stmts' } with
            | none => none
            | some bbs' =>
              match setElem? pSrc.bodies bodyId { body with basicBlocks := bbs' } with
              | none => none
              | some bodies' => some { pSrc with bodies := bodies' }
      | _ => none

noncomputable def checkFoldZeroOffsetStmt (bodyId : DefId)
    (bbIdx : BasicBlockId) (stmtIdx : Nat)
    (pSrc pTgt : MemCopyProgram) : Bool :=
  match applyFoldZeroOffsetStmt bodyId bbIdx stmtIdx pSrc with
  | some pOut => memCopyProgramEq pOut pTgt
  | none => false

noncomputable def applyFoldZeroOffsetTerm (bodyId : DefId)
    (bbIdx : BasicBlockId) (pSrc : MemCopyProgram) : Option MemCopyProgram :=
  match Trusted.MirSemantics.getElem? pSrc.bodies bodyId with
  | none => none
  | some body =>
    match Trusted.MirSemantics.getElem? body.basicBlocks bbIdx with
    | none => none
    | some bb =>
      match bb.terminator with
      | .ptrOffsetInbounds dstPtr srcPtr countOp elemSize nextBb =>
        if !isZeroOffsetConst countOp elemSize then
          none
        else
          let bbTgt : MemCopyBlock := {
            bb with
            statements := bb.statements ++ [.copyPtr dstPtr srcPtr false]
            terminator := .baseTerm (.goto nextBb)
          }
          match setElem? body.basicBlocks bbIdx bbTgt with
          | none => none
          | some bbs' =>
            match setElem? pSrc.bodies bodyId { body with basicBlocks := bbs' } with
            | none => none
            | some bodies' => some { pSrc with bodies := bodies' }
      | _ => none

noncomputable def checkFoldZeroOffsetTerm (bodyId : DefId)
    (bbIdx : BasicBlockId) (pSrc pTgt : MemCopyProgram) : Bool :=
  match applyFoldZeroOffsetTerm bodyId bbIdx pSrc with
  | some pOut => memCopyProgramEq pOut pTgt
  | none => false

/-! ### Pass 2: `FoldGuardedZeroCopy` (Alignment- & Non-Null-Guarded Zero-Length `copy_nonoverlapping` Folding) -/

/-- Whether `(countOp, elemSize)` is a well-formed `usize` constant with
`elemSize * count == 0`. -/
noncomputable def isZeroCopyConst (countOp : Operand) (elemSize : Nat) : Bool :=
  match countOp with
  | .constant c =>
    if !(MirTy.beq c.ty usizeTy) then
      false
    else
      match evalConstLit usizeTy c.lit with
      | .ok (.scalar sv) =>
        sv.wf && Nat.beq (elemSize * sv.bits.toNat) 0
      | _ => false
  | _ => false

/-- Replace zero-byte `copyNonOverlapping` with `checkPtrPairAlign` (preserving
alignment and `checkNonNullZero` UB checks while eliding memory traffic). -/
noncomputable def applyFoldGuardedZeroCopy (bodyId : DefId)
    (bbIdx : BasicBlockId) (pSrc : MemCopyProgram) : Option MemCopyProgram :=
  match Trusted.MirSemantics.getElem? pSrc.bodies bodyId with
  | none => none
  | some body =>
    match Trusted.MirSemantics.getElem? body.basicBlocks bbIdx with
    | none => none
    | some bb =>
      match bb.terminator with
      | .copyNonOverlapping srcPtr dstPtr countOp elemSize reqAlignLog2
          checkNonNullZero nextBb =>
        if !isZeroCopyConst countOp elemSize then
          none
        else
          let bbTgt : MemCopyBlock := {
            bb with
            terminator := .checkPtrPairAlign srcPtr dstPtr elemSize reqAlignLog2
              checkNonNullZero nextBb
          }
          match setElem? body.basicBlocks bbIdx bbTgt with
          | none => none
          | some bbs' =>
            match setElem? pSrc.bodies bodyId { body with basicBlocks := bbs' } with
            | none => none
            | some bodies' => some { pSrc with bodies := bodies' }
      | _ => none

noncomputable def checkFoldGuardedZeroCopy (bodyId : DefId)
    (bbIdx : BasicBlockId) (pSrc pTgt : MemCopyProgram) : Bool :=
  match applyFoldGuardedZeroCopy bodyId bbIdx pSrc with
  | some pOut => memCopyProgramEq pOut pTgt
  | none => false
```

- **Pass 1 (`FoldZeroOffset`):** Folds constant zero-byte `ptrWrappingOffset` statements to `copyPtr dst src false` and `ptrOffsetInbounds` terminators to `copyPtr dst src false; goto nextBb`, preserving `width := .isize` normalization and exact liveness/move semantics.
- **Pass 2 (`FoldGuardedZeroCopy`):** Folds constant zero-byte `copyNonOverlapping` terminators into `.checkPtrPairAlign src dst elemSize reqAlignLog2 checkNonNullZero nextBb`, preserving alignment and null UB checks rather than naively erasing them (`CE4`).

#### 3.2 Pass 3 (`PtrScalarize`) & Pass 4 (`BufScalarize`) -> `MemAllocScalarize`

Once `acceptsCallerMem = false`, `MemAllocScalarize` decomposes all `.ptrLocal` locals and internal `.byteBuf` allocations (`size ≤ 32`) into pure scalar `usize` and `.unit` locals in unmodified `Trusted.MirAst`:

```lean
noncomputable def lowerBlocksForPtrsLoop (decls : List MemCopyLocalDecl)
    (entries : List PtrBackingEntry) (base : Nat) :
    Nat → List MemCopyBlock → List MemCopyBlock × List MemCopyBlock
  | _, [] => ([], [])
  | nextExtra, bb :: rest =>
    let bodyStmts := listFlatMap (lowerStmtForPtrs decls entries base) bb.statements
    let (termPre, termTgt, extra) :=
      lowerTermForPtrs decls entries base nextExtra bb.terminator
    let bbTgt : MemCopyBlock := {
      bb with
      statements := bodyStmts ++ termPre
      terminator := termTgt
    }
    let tail :=
      lowerBlocksForPtrsLoop decls entries base (nextExtra + extra.length) rest
    (bbTgt :: tail.1, extra ++ tail.2)

noncomputable def applyPtrScalarize (plan : PtrScalarizePlan)
    (pSrc : MemCopyProgram) : Option MemCopyProgram :=
  match Trusted.MirSemantics.getElem? pSrc.bodies plan.defId with
  | none => none
  | some body =>
    if body.acceptsCallerMem ||
        body.basicBlocks.isEmpty ||
        !Nat.blt body.argumentCount body.locals.length ||
        !memCopyStorageAnnotationsInBounds body ||
        !memCopyBodyLocalsInBounds body ||
        !memCopyBodyTargetsInBounds body ||
        !checkPtrBackingEntriesLoop body.locals body.argumentCount 0
          body.locals plan.entries then
      none
    else if !body.basicBlocks.all (fun bb =>
        bb.statements.all (checkStmtForPtrs body.locals plan.entries) &&
          checkTermForPtrs body.locals plan.entries bb.terminator) then
      none
    else
      let base := body.locals.length
      let lowered :=
        lowerBlocksForPtrsLoop body.locals plan.entries base
          body.basicBlocks.length body.basicBlocks
      let bodyTgt : MemCopyBody := {
        body with
        locals := tombstonePtrDecls body.locals ++
          ptrCompDecls plan.entries.length ++ ptrScratchDecls
        basicBlocks := lowered.1 ++ lowered.2
      }
      match setElem? pSrc.bodies plan.defId bodyTgt with
      | none => none
      | some bodiesTgt => some { pSrc with bodies := bodiesTgt }
```

- **`PtrScalarize` (`0` block splits for statements/`ptrOffsetInbounds` const/`checkPtrPairAlign`, loop+dispatch extra blocks appended at `≥ body.basicBlocks.length` for runtime `ptrOffsetInbounds`, `readLeUsize`, `writeLeUsize`, and `copyNonOverlapping`):** Maps each `.ptrLocal` `k` to `(liveLoc : .unit, tagLoc : usize, offLoc : usize)` (`tag = 1` iff pointing into statically assigned `some bufLoc`, `tag = 0` iff `null`/`dangling`) plus 12 body-wide scratch locals (`scrBase + 0 .. + 11`). Uses branchless `BinOp.subUnchecked` traps (`mkRequireZeroUsize`, `mkSubUncheckedUsize`, `mkImmediateUbStmt`) for UB ordering, bit-masking (`off & (2^al - 1)`) for alignment checks, unrolled `buildReadLeByteBlocks`/`buildWriteLeByteBlocks` byte chains for multi-byte LE scalars, and `checkBb`/`loopHeadBb`/`loopReadBb`/`loopWriteBb`/`trapBb` bytewise loops over intermediate `.readBufRawByte`/`.writeBufRawByte` terminators for `copy_nonoverlapping`.

```lean
noncomputable def applyBufScalarize (plan : BufScalarizePlan)
    (pSrc : MemCopyProgram) : Option MemCopyProgram :=
  match Trusted.MirSemantics.getElem? pSrc.bodies plan.defId with
  | none => none
  | some body =>
    if body.acceptsCallerMem ||
        body.basicBlocks.isEmpty ||
        !Nat.blt body.argumentCount plan.bufLocal ||
        !Nat.blt plan.bufLocal body.locals.length ||
        !memCopyStorageAnnotationsInBounds body ||
        !memCopyBodyLocalsInBounds body ||
        !memCopyBodyTargetsInBounds body then
      none
    else if body.locals.any (fun d =>
        match d with | .ptrLocal => true | _ => false) then
      none
    else
      match Trusted.MirSemantics.getElem? body.locals plan.bufLocal with
      | some (.byteBuf size alignLog2 mutability) =>
        if !Nat.ble size 32 || !Nat.ble alignLog2 30 then
          none
        else if !body.basicBlocks.all (fun bb =>
            bb.statements.all (checkStmtForBuf body.locals plan.bufLocal) &&
              checkTermForBuf body.locals plan.bufLocal bb.terminator) then
          none
        else
          match setElem? body.locals plan.bufLocal (.base .unit) with
          | none => none
          | some localsTombstoned =>
            let base := body.locals.length
            let hasAnnot := memCopyHasStorageAnnotation body plan.bufLocal
            let entryPrologue : MemCopyBlock := {
              statements :=
                if hasAnnot then [] else mkZeroUsizeRange (base + 1) (2 * size)
              terminator := .baseTerm (.goto 1)
              cleanup := false
            }
            let lowered :=
              lowerBlocksForBufLoop plan.bufLocal base size mutability
                (1 + body.basicBlocks.length) body.basicBlocks
            let byteDecls := listReplicate (2 * size) (.base usizeTy)
            let scrDecls := listReplicate 4 (.base usizeTy)
            let bodyTgt : MemCopyBody := {
              body with
              locals := localsTombstoned ++ [.base .unit] ++ byteDecls ++ scrDecls
              basicBlocks := entryPrologue :: (lowered.1 ++ lowered.2)
            }
            match setElem? pSrc.bodies plan.defId bodyTgt with
            | none => none
            | some bodiesTgt => some { pSrc with bodies := bodiesTgt }
      | _ => none
```

- **`BufScalarize` (one `.byteBuf size alignLog2 mutability` local per trace step after all `.ptrLocal`s are eliminated):** Prepends entry initialization prologue `bb_0` (shifting original targets `+ 1` via `shiftMemCopyTermTargets`, zeroing unannotated initial byte tags/vals), replaces the buffer with `(liveLoc : .unit)` + `2 * size` `usize` tag/val locals + `4` scratch locals, and compiles `.readBufRawByte` / `.writeBufRawByte` into exact `SwitchInt` jump tables (`buildReadBufArms` / `buildWriteBufArms`) over offsets `0 .. size - 1` with `otherwise := trapBb` (`.unreachable`), plus immutable-buffer UB traps (`mkImmediateUbStmt`) and `.tag == 0 => val := 0` canonicalization for `.uninit`.
- **`checkMemCopyToTrustedMir`:** Validates finite `MemCopyOptTrace` execution followed by `unembedBaseProgram pFlat = some pOut` and `programEq pOut pMir = true` strictly targeting unmodified `Trusted.MirAst.Program`.

---

### 4. Five Core Mechanized Theorems, 14-Slice Proof Architecture, & Axiom Profile

`Basis: execution (Lean kernel, support/AnnealTrustedMirCallerMemoryPtrOffsetLeScalarAndCopyNonOverlapping.lean)`

#### 4.1 Verbatim Part III Theorem Statements (`VrustcFormal.F1_16`)

All five Part III theorem statements match frozen statement `SHA-256 2674b74c7d44db89c5fbedbf7d0234bf28d74d95a8111f17e8ceec94dd331206` byte-for-byte with `0` `sorry` and `0` `Classical.choice`:

```lean
theorem memcopy_conservative_extension_exact
    (p : Program) :
    (∀ (c : Choice) (s : State),
      evalStepMemCopy (embedBaseProgram p) c (embedMemCopyState s) =
        liftStepResultMemCopy (evalStep p c s)) ∧
    (∀ q : Query,
      (WellFormedMemCopy (embedBaseProgram p) q ↔ WellFormed p q) ∧
      (∀ out : TerminalOut,
        BehaviorMemCopy (embedBaseProgram p) q out ↔ Behavior p q out) ∧
      (∀ k : FaultKind,
        ReachesResultMemCopy (embedBaseProgram p) q (.fault k) ↔
          ReachesResult p q (.fault k)) ∧
      (DivergesMemCopy (embedBaseProgram p) q ↔ Diverges p q) ∧
      (∀ post : TerminalOut → Prop,
        SatisfiesPostMemCopy (embedBaseProgram p) q post ↔
          SatisfiesPost p q post)) 

/-- **Theorem 2 (`foldZeroOffset_and_guardedZeroCopy_sound_bidirectional_iff`):**
Statement-level zero-offset folding (`checkFoldZeroOffsetStmt`),
terminator-level zero-offset folding (`checkFoldZeroOffsetTerm`), and
alignment/non-null-guarded zero-length `copy_nonoverlapping` folding
(`checkFoldGuardedZeroCopy`) all preserve full bidirectional semantic
equivalence `FullSemanticEquivMemCopy pSrc pTgt` across all `Query` values
(including external `CallerMemory` invocations). -/
theorem foldZeroOffset_and_guardedZeroCopy_sound_bidirectional_iff :
    (∀ (bodyId : DefId) (bbIdx : BasicBlockId) (stmtIdx : Nat)
        (pSrc pTgt : MemCopyProgram),
      checkFoldZeroOffsetStmt bodyId bbIdx stmtIdx pSrc pTgt = true →
      FullSemanticEquivMemCopy pSrc pTgt) ∧
    (∀ (bodyId : DefId) (bbIdx : BasicBlockId) (pSrc pTgt : MemCopyProgram),
      checkFoldZeroOffsetTerm bodyId bbIdx pSrc pTgt = true →
      FullSemanticEquivMemCopy pSrc pTgt) ∧
    (∀ (bodyId : DefId) (bbIdx : BasicBlockId) (pSrc pTgt : MemCopyProgram),
      checkFoldGuardedZeroCopy bodyId bbIdx pSrc pTgt = true →
      FullSemanticEquivMemCopy pSrc pTgt) 

/-- **Theorem 3 (`inboundsOffset_leRoundTrip_and_copyNonOverlapping_laws`):**
Universal algebraic and operational laws of `M_memcopy` pointers, endian
encoding, and `copy_nonoverlapping`:
1. **Zero-Delta `calcInboundsOffset` Identity:** Whenever `count * elemSize = 0`,
   `calcInboundsOffset mem pv count elemSize = .ok { pv with width := .isize }`
   for every `pv` (including `null` and `NonNull::dangling()`) and `mem`.
2. **Wrapping Offset Opposite-Sign Round-Trip:** Applying `calcWrappingOffset`
   with `+count` followed by `-count` for any `count : Int` and `elemSize : Nat`
   recovers `{ pv with width := .isize }` even across out-of-bounds excursions.
3. **Little-Endian Encode/Decode Round-Trip & Provenance Firewall:** For every
   `w : LeWidth` and `n < 2^w.bitWidth`,
   `decodeLeUsize w (encodeLeUsize w n) = .ok n`, whereas `decodeLeUsize` faults
   `.error .undefined` on any byte list of length `w.byteCount` containing
   `.uninit` or `AllocByte.init _ (some aid)` (`ReadPointerAsInt`), while
   `decodePtrLe8 (encodeLeBytesAux prov 8 off)` recovers `{ allocId := prov,
   offsetBytes := UInt64.ofNat off, width := .isize }` for every `off < 2^64`.
4. **Zero-Byte `copy_nonoverlapping` Exact Characterization:** When
   `reqAlignLog2 ≤ 30` and `elemSize * count = 0`,
   `evalCopyNonOverlapping mem pvSrc pvDst count elemSize reqAlignLog2 checkNonNullZero`
   equals `.ok mem` iff both `checkPtrAlignMem mem pvSrc reqAlignLog2 = .ok ()`
   and `checkPtrAlignMem mem pvDst reqAlignLog2 = .ok ()` and
   `¬ (checkNonNullZero = true ∧ (isNullPtr pvSrc = true ∨ isNullPtr pvDst = true))`,
   and otherwise faults `.error .undefined`. -/
theorem inboundsOffset_leRoundTrip_and_copyNonOverlapping_laws :
    (∀ (mem : CallerMemory) (pv : PtrVal) (count : Int) (elemSize : Nat),
      count * Int.ofNat elemSize = 0 →
      calcInboundsOffset mem pv count elemSize =
        .ok { pv with width := .isize }) ∧
    (∀ (pv : PtrVal) (count : Int) (elemSize : Nat),
      calcWrappingOffset (calcWrappingOffset pv count elemSize) (Neg.neg count) elemSize =
        { pv with width := .isize }) ∧
    (∀ (w : LeWidth) (n : Nat),
      n < Nat.pow 2 w.bitWidth →
      decodeLeUsize w (encodeLeUsize w n) = .ok n) ∧
    (∀ (w : LeWidth) (bs : List AllocByte),
      Nat.beq bs.length w.byteCount = true →
      bs.any (fun ab => match ab with | .init _ none => false | _ => true) = true →
      decodeLeUsize w bs = .error .undefined) ∧
    (∀ (prov : Option AllocId) (off : Nat),
      off < maxUsize →
      decodePtrLe8 (encodeLeBytesAux prov 8 off) =
        .ok { allocId := prov, offsetBytes := UInt64.ofNat off, width := .isize }) ∧
    (∀ (mem : CallerMemory) (pvSrc pvDst : PtrVal)
        (count elemSize reqAlignLog2 : Nat) (checkNonNullZero : Bool),
      Nat.ble reqAlignLog2 30 = true →
      elemSize * count = 0 →
      ((evalCopyNonOverlapping mem pvSrc pvDst count elemSize reqAlignLog2
          checkNonNullZero = .ok mem ↔
        (checkPtrAlignMem mem pvSrc reqAlignLog2 = .ok () ∧
         checkPtrAlignMem mem pvDst reqAlignLog2 = .ok () ∧
         ¬ (checkNonNullZero = true ∧
            (isNullPtr pvSrc = true ∨ isNullPtr pvDst = true)))) ∧
       (evalCopyNonOverlapping mem pvSrc pvDst count elemSize reqAlignLog2
          checkNonNullZero ≠ .ok mem →
        evalCopyNonOverlapping mem pvSrc pvDst count elemSize reqAlignLog2
          checkNonNullZero = .error .undefined))) 

/-- **Theorem 4 (`memAllocScalarize_reduces_to_trusted_mir`):**
Any finite `MemCopyOptTrace` certified by
`checkMemCopyToTrustedMir trace pSrc pMir = true` produces an unmodified
`Trusted.MirAst.Program` (`pMir`) whose unmodified `Trusted.MirSemantics`
judgments (`WellFormed`, `Behavior`, `ReachesResult (.fault k)`, `Diverges`,
and `SatisfiesPost`) are bidirectionally equivalent (`↔`) to `M_memcopy` on
`pSrc`. -/
theorem memAllocScalarize_reduces_to_trusted_mir
    (trace : MemCopyOptTrace) (pSrc : MemCopyProgram) (pMir : Program)
    (hLower : checkMemCopyToTrustedMir trace pSrc pMir = true) :
    (∀ q : Query, WellFormedMemCopy pSrc q ↔ WellFormed pMir q) ∧
    (∀ q : Query, ∀ out : TerminalOut,
      BehaviorMemCopy pSrc q out ↔ Behavior pMir q out) ∧
    (∀ q : Query, ∀ k : FaultKind,
      ReachesResultMemCopy pSrc q (.fault k) ↔
        ReachesResult pMir q (.fault k)) ∧
    (∀ q : Query, DivergesMemCopy pSrc q ↔ Diverges pMir q) ∧
    (∀ q : Query, ∀ post : TerminalOut → Prop,
      SatisfiesPostMemCopy pSrc q post ↔ SatisfiesPost pMir q post) 

/-- **Theorem 5 (`memCopyPipeline_then_optPipeline_vc_transport`):**
Vertical composition: any certified `MemCopyOptTrace` lowering `pSrc` into
unmodified `Trusted.MirAst.Program` `pMir` followed by any certified
`Trusted.MirSemantics` optimization equivalence `FullSemanticEquivBase pMir pOpt`
transports all five `M_memcopy` verification judgments bidirectionally (`↔`)
onto unmodified `Trusted.MirSemantics` on `pOpt`. -/
theorem memCopyPipeline_then_optPipeline_vc_transport
    (trace : MemCopyOptTrace) (pSrc : MemCopyProgram) (pMir pOpt : Program)
    (hLower : checkMemCopyToTrustedMir trace pSrc pMir = true)
    (hOpt : FullSemanticEquivBase pMir pOpt) :
    (∀ q : Query, WellFormedMemCopy pSrc q ↔ WellFormed pOpt q) ∧
    (∀ q : Query, ∀ out : TerminalOut,
      BehaviorMemCopy pSrc q out ↔ Behavior pOpt q out) ∧
    (∀ q : Query, ∀ k : FaultKind,
      ReachesResultMemCopy pSrc q (.fault k) ↔
        ReachesResult pOpt q (.fault k)) ∧
    (∀ q : Query, DivergesMemCopy pSrc q ↔ Diverges pOpt q) ∧
    (∀ q : Query, ∀ post : TerminalOut → Prop,
      SatisfiesPostMemCopy pSrc q post ↔ SatisfiesPost pOpt q post) 
```

#### 4.2 Modular 14-Slice Proof Architecture (`40919` Slice Lines -> `44945` Stitched Lines)

The proof was developed across `14` standalone `TrustedBoundary.lean`-preflighted proof slices (`40919` lines, `1140` declarations, alongside `F1_16_Base.lean`) and stitched cleanly into `support/AnnealTrustedMirCallerMemoryPtrOffsetLeScalarAndCopyNonOverlapping.lean` (`44945` lines, `2377241` bytes, `byte_exact_reconstruction == true`, `0` non-private inserted declarations, `0` `Init.*` imports beyond `Slice0_StitchedShims`):

| Slice Module | Lines | Decls | Proof Responsibility |
| :--- | :---: | :---: | :--- |
| `Slice0_StitchedShims.lean` | `1350` | `88` | Zero-`Classical.choice` constructive `Nat`, `Int`, and bitwise shims strictly scoped over `prelude; import Trusted.MirAst; import Trusted.MirSemantics` (`48` constructive lemmas, `choice = 0`). |
| `F1_16_Common.lean` | `1696` | `94` | Structural equality reflection (`programEq_eq`, `memCopyProgramEq_eq`, `mirTy_beq_eq`), constructive `BitVec`/`usize` arithmetic helpers, `divergesBase_iff_no_terminal_or_fault`, and bounded forward-stutter simulation combinators (`fullSemanticEquivMemCopy_of_fwd_stutter_sim`). |
| `Slice1_ConservativeExt_And_Laws.lean` | `1718` | `71` | 1-step lockstep (`evalStepMemCopy_embedBaseProgram`), `initStateMemCopy_embedBaseProgram`, `unembedBaseProgram_eq_embed`, **Theorem 1** (`memcopy_conservative_extension_exact`), and **Theorem 3** (`inboundsOffset_leRoundTrip_and_copyNonOverlapping_laws`, strictly `[propext]`). |
| `Slice2_ZeroOffset_And_GuardedZeroCopy.lean` | `2597` | `77` | Pass 1 (`applyFoldZeroOffsetStmt`, `applyFoldZeroOffsetTerm`) and Pass 2 (`applyFoldGuardedZeroCopy`), discharging **Theorem 2** (`foldZeroOffset_and_guardedZeroCopy_sound_bidirectional_iff`, strictly `[propext]`). |
| `Slice3a_PtrScalarizeHelpers.lean` | `2631` | `164` | `PtrScalarize` context unpacking, `findPtrEntry` uniqueness/indexing invariants, tombstoned local-table typing, `s3_SimRel` local/memory well-formedness foundations, and straight-line gadget primitives. |
| `Slice3b_PtrScalarizeGadgets.lean` | `3624` | `91` | `s3_SimRel`, `s3_initStateMemCopy_simRel`, base rvalue/place simulation (`s3_evalBaseRvalue_sim`, `s3_writeBasePlace_sim`), alignment/non-null checks, and `evalOffsetCountOp` helpers. |
| `Slice3c_PtrScalarizeStmts.lean` | `4001` | `80` | Forward `1`-to-`1+` statement simulation `s3_stmt_step_sim` for all `lowerStmtForPtrs` arms (`mkNullPtr`, `mkDanglingPtr`, `addrOfByteBuf`, aliasing-safe `copyPtr`, wrapping `ptrWrappingOffset`, and storage markers). |
| `Slice3x_LeAndCopySound.lean` | `6016` | `99` | Multi-block byte-loop simulation for `readLeUsize` (`s3x_readLeUsize_sim`), `writeLeUsize` (`s3x_writeLeUsize_sim`), and `copyNonOverlapping` (`s3x_copyNonOverlapping_sim`, including same-alloc overlap check and `elemSize * count == 0` fast path). |
| `Slice3d_PtrScalarizeSound.lean` | `5062` | `72` | Terminator simulation for `.baseTerm`, `.readBufRawByte`, `.writeBufRawByte`, `.checkPtrPairAlign`, `.ptrOffsetInbounds` (const & runtime counts), `s3_term_step_sim`, `s3_scalarize_step_sim`, and Pass 3 soundness `applyPtrScalarize_sound`. |
| `Slice4a_BufScalarizeHelpers.lean` | `3734` | `156` | `BufScalarize` context unpacking, `s4_CoreRel` / `s4_StateRel` / `s4_ReachableInv`, `Allocation` <-> `(tag_i, val_i)` byte-table relation, and `initStateMemCopy` simulation (`s4_initStateMemCopy_err_iff`, `s4_initStateMemCopy_ok_rel`). |
| `Slice4b_BufScalarizeStmts.lean` | `3413` | `58` | Prologue skip (`s4_reach_entry_prologue`), `SwitchInt` dispatch arm helpers, straight-line `usize` masking/liveness steps, and statement simulation `s4_stmt_step_sim`. |
| `Slice4c_BufScalarizeSound.lean` | `4256` | `36` | Block-shifted terminator simulation `s4_term_step_sim` (including `readBufRawByte` and `writeBufRawByte` via generated `buildReadBufArms`/`buildWriteBufArms` tables) and Pass 4 soundness `applyBufScalarize_sound`. |
| `Slice5a_UnembedAndPipelineHelpers.lean` | `746` | `52` | `unembedBaseProgram` semantic equivalence (`s5_unembedBaseProgram_sound`), step/trace induction (`s5_applyMemCopyOptTrace_sound_of_ptrScalarize`), and `s5_vc_transport_of_reduces`. |
| `Slice5_TraceAndPipeline.lean` | `75` | `2` | **Theorem 4** (`memAllocScalarize_reduces_to_trusted_mir`) and **Theorem 5** (`memCopyPipeline_then_optPipeline_vc_transport`) instantiated over `applyPtrScalarize_sound` + `Slice5a`. |

Notably, **Theorem 1** (`memcopy_conservative_extension_exact`), **Theorem 2** (`foldZeroOffset_and_guardedZeroCopy_sound_bidirectional_iff`), and **Theorem 3** (`inboundsOffset_leRoundTrip_and_copyNonOverlapping_laws`) depend **strictly on `[propext]` alone** (`0` `Quot.sound`, `0` `Classical.choice`), while **Theorems 4 & 5** depend only on `[propext, Quot.sound]` (`Quot.sound` entering exclusively via `funext` on `List.map` / `List.all` congruences in `Slice5a`/`unembedBaseProgram`).

#### 4.3 Complete Public Theorem Inventory & Axiom Profile (`27` Theorems)

Every single one of the `27` public theorems depends exclusively on `["propext", "Quot.sound"]` (`25 / 27` strictly `[propext]`, `2 / 27` `[propext, Quot.sound]`, `0` `Classical.choice`, `0` `sorryAx`, `0` `_unsafe_rec`):

| # | Public Theorem | Lean 4 Kernel Axioms | Role |
| :---: | :--- | :--- | :--- |
| `1` | `VrustcFormal.F1_16.memcopy_conservative_extension_exact` | `[propext]` | Part III Core Theorem 1 |
| `2` | `VrustcFormal.F1_16.foldZeroOffset_and_guardedZeroCopy_sound_bidirectional_iff` | `[propext]` | Part III Core Theorem 2 |
| `3` | `VrustcFormal.F1_16.inboundsOffset_leRoundTrip_and_copyNonOverlapping_laws` | `[propext]` | Part III Core Theorem 3 |
| `4` | `VrustcFormal.F1_16.memAllocScalarize_reduces_to_trusted_mir` | `[propext, Quot.sound]` | Part III Core Theorem 4 |
| `5` | `VrustcFormal.F1_16.memCopyPipeline_then_optPipeline_vc_transport` | `[propext, Quot.sound]` | Part III Core Theorem 5 |
| `6` | `VrustcFormal.F1_16.reachesMemCopy_head` | `[propext]` | Part IV Bounded-Fuel Adequacy / Determinism Lemma |
| `7` | `VrustcFormal.F1_16.reachesMemCopy_head_det` | `[propext]` | Part IV Bounded-Fuel Adequacy / Determinism Lemma |
| `8` | `VrustcFormal.F1_16.execFuelMemCopy_sound` | `[propext]` | Part IV Bounded-Fuel Adequacy / Determinism Lemma |
| `9` | `VrustcFormal.F1_16.execMemCopy_sound` | `[propext]` | Part IV Bounded-Fuel Adequacy / Determinism Lemma |
| `10` | `VrustcFormal.F1_16.execFuelMemCopy_done_det` | `[propext]` | Part IV Bounded-Fuel Adequacy / Determinism Lemma |
| `11` | `VrustcFormal.F1_16.positiveCanaryMemCopy_of_exec` | `[propext]` | Part IV Bounded-Fuel Adequacy / Determinism Lemma |
| `12` | `VrustcFormal.F1_16.negativeCanaryMemCopy_of_exec` | `[propext]` | Part IV Bounded-Fuel Adequacy / Determinism Lemma |
| `13` | `VrustcFormal.F1_16.reachesBase_trans` | `[propext]` | Part IV Bounded-Fuel Adequacy / Determinism Lemma |
| `14` | `VrustcFormal.F1_16.execTreeBase_sound` | `[propext]` | Part IV Bounded-Fuel Adequacy / Determinism Lemma |
| `15` | `VrustcFormal.F1_16.execBase_done_sound` | `[propext]` | Part IV Bounded-Fuel Adequacy / Determinism Lemma |
| `16` | `VrustcFormal.F1_16.execBase_fault_sound` | `[propext]` | Part IV Bounded-Fuel Adequacy / Determinism Lemma |
| `17` | `VrustcFormal.F1_16.ce1_inbounds_one_past_end_vs_oob_and_wrapping_roundtrip_in_trusted_mir` | `[propext]` | Part IV Sharpness Counterexample / End-to-End Lowering Witness |
| `18` | `VrustcFormal.F1_16.ce2_le_bytes_read_unaligned_ok_vs_misaligned_deref_ub_in_trusted_mir` | `[propext]` | Part IV Sharpness Counterexample / End-to-End Lowering Witness |
| `19` | `VrustcFormal.F1_16.ce3_zero_count_dangling_misaligned_and_null_split_in_trusted_mir` | `[propext]` | Part IV Sharpness Counterexample / End-to-End Lowering Witness |
| `20` | `VrustcFormal.F1_16.ce4_guarded_zero_copy_preserves_ub_while_naive_elision_unsound` | `[propext]` | Part IV Sharpness Counterexample / End-to-End Lowering Witness |
| `21` | `VrustcFormal.F1_16.ce5_overlap_ub_vs_adjacent_ok_in_trusted_mir` | `[propext]` | Part IV Sharpness Counterexample / End-to-End Lowering Witness |
| `22` | `VrustcFormal.F1_16.ce6_partial_uninit_copy_preserved_and_uninit_read_faults_in_trusted_mir` | `[propext]` | Part IV Sharpness Counterexample / End-to-End Lowering Witness |
| `23` | `VrustcFormal.F1_16.ce7_ptr_bytes_preserve_provenance_and_read_ptr_as_int_faults` | `[propext]` | Part IV Sharpness Counterexample / End-to-End Lowering Witness |
| `24` | `VrustcFormal.F1_16.ce8_external_caller_mem_write_vs_shared_ub_and_escape_ub` | `[propext]` | Part IV Sharpness Counterexample / End-to-End Lowering Witness |
| `25` | `VrustcFormal.F1_16.ce9_storage_dead_dangling_and_relive_reset_ub_in_trusted_mir` | `[propext]` | Part IV Sharpness Counterexample / End-to-End Lowering Witness |
| `26` | `VrustcFormal.F1_16.ce10_end_to_end_pipeline_executes_in_unmodified_trusted_mir` | `[propext]` | Part IV Sharpness Counterexample / End-to-End Lowering Witness |
| `27` | `VrustcFormal.F1_16.ce11_static_guards_fail_closed` | `[propext]` | Part IV Sharpness Counterexample / End-to-End Lowering Witness |

---

### 5. Eleven Sharpness Counterexamples (`CE1`–`CE11`) & End-to-End `Trusted.MirSemantics` Witness (`CE10`)

`Basis: execution (Lean kernel, support/AnnealTrustedMirCallerMemoryPtrOffsetLeScalarAndCopyNonOverlapping.lean)`

Part IV (`0` `sorry`, locked in frozen spec) proves deterministic bounded-fuel adequacy (`execFuelMemCopy_sound`, `execTreeBase_sound`, `positiveCanaryMemCopy_of_exec`, `negativeCanaryMemCopy_of_exec`) and eleven concrete kernel-checked sharpness counterexamples and end-to-end lowering witnesses:

| Witness Theorem | Scenario / `E3-137` Probe | Exact Kernel-Checked Property |
| :--- | :--- | :--- |
| `ce1_inbounds_one_past_end_vs_oob_and_wrapping_roundtrip_in_trusted_mir` | 4-byte `.byteBuf`, `ptrOffsetInbounds(+4)` vs `(+5)` vs `ptrWrappingOffset(±100)` | Lowered via `traceCe1SingleBuf` into unmodified `Trusted.MirSemantics`: one-past-end `+4` succeeds (`1`), `+5` faults `.fault .undefined`, and `+100 -> -100` `wrapping_offset` succeeds and reads `0x12345678`! |
| `ce2_le_bytes_read_unaligned_ok_vs_misaligned_deref_ub_in_trusted_mir` | Offset-1 `0x12345678` write + `read_unaligned` (`false`) vs offset-2 aligned `b4` read (`true`) | Lowered into `Trusted.MirSemantics`: unaligned `readLeUsize` reads `0x12345678 + 0x78` cleanly, whereas aligned `*ptr_u32` at offset `2` faults `.fault .undefined`. |
| `ce3_zero_count_dangling_misaligned_and_null_split_in_trusted_mir` | Zero-count `copyNonOverlapping`: aligned dangling vs misaligned vs `null` (`checkNonNullZero = false` vs `true`) | Lowered into `Trusted.MirSemantics`: aligned dangling (`7`) and raw-intrinsic null (`9`) return cleanly, while misaligned (`align=0, req=2`) and `core::ptr` null (`checkNonNullZero=true`) fault `.fault .undefined`. |
| `ce4_guarded_zero_copy_preserves_ub_while_naive_elision_unsound` | Misaligned `copyNonOverlapping(..., 0)` under `FoldGuardedZeroCopy` vs naive `.goto` elision | `checkFoldGuardedZeroCopy` preserves `.fault .undefined`, while naive removal creates `¬ FullSemanticEquivMemCopy`. |
| `ce5_overlap_ub_vs_adjacent_ok_in_trusted_mir` | 4-byte `.byteBuf`: `[0..3] -> [1..4]` overlapping vs `[0..2] -> [2..4]` adjacent | Lowered into `Trusted.MirSemantics`: overlap faults `.fault .undefined`, while adjacent copy writes and returns `0x0201`. |
| `ce6_partial_uninit_copy_preserved_and_uninit_read_faults_in_trusted_mir` | `MaybeUninit` `[0xAA, uninit, 0xCC, uninit]` 3-byte `copyNonOverlapping` | Lowered into `Trusted.MirSemantics`: reading bytes `0` and `2` succeeds (`0xAA + 0xCC`), whereas reading copied byte `1` (`.uninit`) faults `.fault .undefined`. |
| `ce7_ptr_bytes_preserve_provenance_and_read_ptr_as_int_faults` | `writePtrLe8` -> `copyNonOverlapping` -> `readPtrLe8` vs `readLeUsize` (`M_memcopy`) | Pointer-to-pointer 8-byte bytewise copy preserves allocation provenance and reads `42`, whereas reading pointer bytes as `usize` faults `.fault .undefined` (`ReadPointerAsInt`). |
| `ce8_external_caller_mem_write_vs_shared_ub_and_escape_ub` | External `CallerMemory` (`allocId = 7`): `.mut` write vs `.shared` write vs escaping local ptr | External `.mut` write persists `0xCAFEBABE` in `Out.callerMem`, writing to `.shared` faults `.fault .undefined`, and returning an internal frame ptr (`≥ 65536`) faults `.fault .undefined`. |
| `ce9_storage_dead_dangling_and_relive_reset_ub_in_trusted_mir` | `StorageLive 1` -> `writeLeUsize` -> `StorageDead 1` (± re-`StorageLive 1`) -> `readLeUsize` | Lowered into `Trusted.MirSemantics`: both reading after `StorageDead` and reading after `StorageDead -> StorageLive` (`.uninit` reset) fault `.fault .undefined`. |
| `ce10_end_to_end_pipeline_executes_in_unmodified_trusted_mir` | Full 6-step `IntoBytes::write_to_suffix`-style pipeline (`traceCe10`) | Certifies `[foldZeroOffsetStmt, foldZeroOffsetTerm, foldGuardedZeroCopy, ptrScalarize, bufScalarize(2), bufScalarize(3)]` (`checkMemCopyToTrustedMir = true`) and executes `progCe10TrustedMir` on `queryUsize 0x5678`, returning `0x5678` in unmodified `Trusted.MirSemantics`. |
| `ce11_static_guards_fail_closed` | `acceptsCallerMem = true`, unscalarized `.ptrLocal`, incompatible buffer copy | Verifies `applyPtrScalarize` rejects `acceptsCallerMem = true`, `applyBufScalarize` rejects unscalarized `.ptrLocal`, and `applyPtrScalarize` rejects `copyPtr` between distinct static backing buffers (`none`). |

---

### 6. Six-Gate Multi-Kernel, `TrustedBoundary.lean` Pass 1, & Blind Specification Audit Results

`Basis: execution (support/multi_kernel_verification_summary.json)`

An independent frontier Stage 5 blind specification audit inspected `F1_16_..._Stmt.frozen.lean`, unmodified `Trusted/{MirAst,MirSemantics}.lean`, and `E3-137` under strict isolation (`0` proof files read), returning **`PASS_WITH_BOUNDARY_NOTES`** (`0` blocking soundness defects, `0` vacuities, `0` TCB misalignments, and `14` explicitly documented scope boundaries `B1`–`B14` in `## Boundaries` below).

In Gate 2 (`env.constants.map₁` public surface diff), `proof_pub_count = 1035` vs `frozen_pub_count = 1010` shows **`extra_non_aux_pub = []`**, **`missing_non_aux_pub = []`**, and **`29` compiler-materialized Lean stdlib equation lemmas** (`List.all.eq_def`, `List.any.eq_def`, `Nat.bitwise.eq_1`, `Nat.bitwise.eq_def`, `VrustcFormal.F1_16.allMemCopyLocalsSupported.eq_def`, `VrustcFormal.F1_16.applyMemCopyOptTrace.eq_def`, `VrustcFormal.F1_16.buildInternalBufAllocs.eq_def`, `VrustcFormal.F1_16.buildReadLeByteBlocks.eq_def`, `VrustcFormal.F1_16.buildWriteLeByteBlocks.eq_def`, `VrustcFormal.F1_16.checkMemCopyArgVal._sparseCasesOn_3.else_eq`, `VrustcFormal.F1_16.checkMemCopyArgsMatch.eq_def`, `VrustcFormal.F1_16.checkPtrBackingEntriesLoop.eq_def`, `VrustcFormal.F1_16.decodeLeBytesAux.eq_def`, `VrustcFormal.F1_16.decodePtrBytesAux.eq_def`, `VrustcFormal.F1_16.encodeLeBytesAux.eq_def`, `VrustcFormal.F1_16.findAlloc?.eq_def`, `VrustcFormal.F1_16.findPtrEntryAux.eq_def`, `VrustcFormal.F1_16.initMemCopyLocalsLoop._sparseCasesOn_1.else_eq`, `VrustcFormal.F1_16.initMemCopyLocalsLoop.eq_def`, `VrustcFormal.F1_16.listRel._sparseCasesOn_1.else_eq`, `VrustcFormal.F1_16.listRel._sparseCasesOn_2.else_eq`, `VrustcFormal.F1_16.lowerBlocksForPtrsLoop.eq_def`, `VrustcFormal.F1_16.memCopyLocalDeclEq._sparseCasesOn_1.else_eq`, `VrustcFormal.F1_16.memCopyLocalDeclEq._sparseCasesOn_2.else_eq`, `VrustcFormal.F1_16.memCopyLocalDeclEq._sparseCasesOn_3.else_eq`, `VrustcFormal.F1_16.optNatEq._sparseCasesOn_2.else_eq`, `VrustcFormal.F1_16.ptrCompDecls.eq_def`, `VrustcFormal.F1_16.tombstonePtrDecls.eq_def`, `VrustcFormal.F1_16.updateAlloc?.eq_def`, triggered transparently by `unfold List.all/any` and `rw [Nat.bitwise.eq_def/eq_1]` in `Slice0`/`Slice3b`/`Slice4a`, with `0` inserted non-private theory declarations).

The stitched single-file proof `support/AnnealTrustedMirCallerMemoryPtrOffsetLeScalarAndCopyNonOverlapping.lean` (`44945` lines, `2377241` bytes, `0` CRLF bytes, `0` disallowed Unicode/bidi characters, `byte_exact_reconstruction == true`) passed all six multi-kernel verification gates:

| Gate | Checker / Tool | Configuration / Flags | Result | Wall Time | Peak RSS | Key Metrics |
| :---: | :--- | :--- | :---: | :---: | :---: | :--- |
| **1** | `Lean v4.34.1` (`5045d005`) | `-M4096 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` | `rc = 0` | `274.8681 s` | `2916.3 MB` | `0` errors, `0` warnings, `.olean` `68353664` B |
| **2** | `#print axioms` + `env.constants.map₁` audit | All `27` public theorems + frozen-vs-proof public surface diff | `rc = 0` | `3.6684 s` | `1632.74 MB` | `25 / 27` strictly `[propext]`, `2 / 27` `[propext, Quot.sound]`, `0` `Classical.choice`; `total=2979`, `pub=1035` (`1010` frozen + `29` stdlib eq aux), `priv=1944`, `bad=0`, `pub_surface_clean=true` |
| **3a** | `TrustedBoundary.lean` `"preflight"` (pos) | Unmodified `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` | `rc = 0` | `14.6138 s` | `795.47 MB` | `ok = true` on `Anneal.F1_16_Proof` |
| **3b** | `TrustedBoundary.lean` `"preflight"` (neg) | Frozen statement file containing Part III `sorry`s | `rc = 1` | `7.0597 s` | — | Rejected fail-closed: `policy:unsupported syntax kind Lean.Parser.Tactic.tacticSorry` |
| **3c** | `TrustedBoundary.lean` Pass 1 `"audit"` | `axioms: [["Quot.sound", "Init.Prelude"], ["propext", "Init.Core"]]` (`0` `Classical.choice`) | `rc = 0` | `46.7064 s` | `1476.37 MB` | `ok = true`, `replay = true`, `kernelDeclarations = 1324`, `replayedDeclarations = 4560`, `reachableDeclarations = 5642`, `checkedAlternateProofs = 0`, `compilerOnlyNames = 281`, `axioms = ["propext", "Quot.sound"]` |
| **4** | `Lean v4.35.0` (`eb6cafb7`) | `-M4096 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` | `rc = 0` | `198.4192 s` | `2827.9 MB` | Cross-version kernel check clean (`0` warnings) |
| **5** | `lean4export 3.1.0` (`5a9a355d`) | Exporting all `27` `VrustcFormal.F1_16.*` public theorems | `rc = 0` | `8.2346 s` | — | `1884301` NDJSON lines (`99847845` B) |
| **6a** | `nanoda_bin 0.4.19` (`f55114af`) (pos) | `permitted_axioms: ["propext", "Quot.sound"]`, `unpermitted_axiom_hard_error: true` | `rc = 0` | `27.3223 s` | `390.19 MB` | `Checked 3947 declarations with no typechecker errors` |
| **6b** | `nanoda_bin 0.4.19` (`f55114af`) (neg) | `permitted_axioms: []`, `unpermitted_axiom_hard_error: true` | `rc = 1` | `0.0269 s` | — | Rejected fail-closed: `Command exited with non-zero status 1` |

## Boundaries

Every theorem in `VrustcFormal.F1_16` is sound and exact within the fourteen explicitly audited Honest-Scope boundaries below (`B1`–`B14`) surfaced during the Stage 5 blind specification audit; constructs outside the lowerable fragment fail closed (`none`, `false`, `.error .unsupported`, or `.fault .unsupported`) rather than approximating semantics:

1. **B1 — `acceptsCallerMem = false` gate for `Trusted.MirSemantics` reduction (`unembedBaseBody`, `applyPtrScalarize`, `applyBufScalarize`, `F1_16:461-463, 2745, 2987`).** Reduction via `checkMemCopyToTrustedMir` and **Theorems 4 & 5** strictly requires `body.acceptsCallerMem = false` across all bodies in the program; caller-supplied `CallerMemory` (`acceptsCallerMem = true`, persistent `Out.callerMem`, `CE8`) operates directly at the `M_memcopy` level (`Theorems 1–3`) rather than lowering into `Trusted.MirSemantics`'s empty-`callerMem` initialization.
2. **B2 `[Non-Conservative vs. Miri]` — `wfExternalCallerMem` does not forbid internal-range `AllocId` provenance inside caller-supplied `bytes` (`F1_16:519-524`).** `wfExternalCallerMem` enforces pairwise-distinct allocation IDs strictly `< internalAllocBase` (`65536`), `alignLog2 ≤ 30`, and `bytes.length ≤ maxIsize`, but does not exclude `AllocByte.init _ (some pid)` bytes carrying `pid ≥ 65536`. This is unreachable under `acceptsCallerMem = false` (Theorems 1, 4, 5), whereas in `M_memcopy` with `acceptsCallerMem = true` + an internal `.byteBuf` + `readPtrLe8`, malformed caller bytes could forge an internal `AllocId`.
3. **B3 `[Non-Conservative vs. Miri]` — Deterministic `AllocId = 65536 + localId` reuse across `StorageDead -> StorageLive` (`F1_16:126-129, 1150-1189`).** Re-executing `StorageLive id` after `StorageDead id` reuses the deterministic `AllocId = internalAllocBase + id` (`live := true`, bytes reset to `.uninit`). Stale pointers fault `.undefined` on immediate `StorageDead` reads and post-reinit reads (`CE9`), whereas post-reinit writes or reads of newly written bytes succeed rather than faulting Miri use-after-free provenance UB.
4. **B4 `[Non-Conservative vs. Miri]` — Whole-allocation `Mutability` check without Stacked/Tree Borrows tags or `UnsafeCell`.** `M_memcopy` tracks allocation-level `.mut` vs. `.shared` permissions (`writeMemSlice`, `evalCopyNonOverlapping`), omitting per-pointer Stacked/Tree Borrows permission stacks, protector activation, retagging transitions, and `UnsafeCell` interior mutability.
5. **B5 — Static single-backing-buffer table per `.ptrLocal` in `PtrScalarize` (`none` or one fixed `some bufLoc`, `CE11`).** Control-flow joins or `copyPtr`/`ptrOffsetInbounds` steps that store pointers derived from two distinct `.byteBuf` locals `b₁ != b₂` into the same `.ptrLocal` fail closed (`checkPtrCopyCompat` returns `false`, `applyPtrScalarize` returns `none`).
6. **B6 — Lowered internal `.byteBuf` size cap (`≤ 32` bytes) and alignment cap (`≤ 2^30`).** While `M_memcopy` allows allocations up to `maxIsize = 2^63 - 1`, `checkPtrBackingEntriesLoop` and `applyBufScalarize` reject internal `.byteBuf` locals exceeding `32` bytes or `alignLog2 > 30` to bound generated `SwitchInt` byte-table blocks linearly.
7. **B7 — No `readPtrLe8`/`writePtrLe8` scalarization in `MemAllocScalarize`, and conservative mixed-provenance rejection in `decodePtrLe8`.** `checkTermForPtrs` returns `false` on `readPtrLe8` and `writePtrLe8` (`F1_16:2043`; proven at `M_memcopy` level in `CE7` and Theorem 3), and `decodePtrLe8` faults `.undefined` whenever 8 pointer bytes differ in provenance (conservatively stricter than Miri's partial-provenance stripping to `noalloc` wildcard integers).
8. **B8 `[Conservative vs. Runtime Miri]` — CTFE Provenance Firewall `ReadPointerAsInt` in `decodeLeUsize` and abstract base-0 offsets without `expose_provenance`.** `decodeLeUsize` rejects any provenance-bearing byte `AllocByte.init _ (some aid)` as `.error .undefined` (`CE7`, matching `rustc_const_eval`'s `!Prov::OFFSET_IS_ADDR` CTFE rule rather than runtime Miri's integer-address cast semantics), and `PtrVal` omits concrete numeric addresses and `expose_provenance` / `with_exposed_provenance` provenance wildcards.
9. **B9 — Thin pointers, little-endian `1/2/4/8`-byte `usize` scalars, and `copy_nonoverlapping` only.** Covers thin 64-bit `PtrVal` pointers, `LeWidth ∈ {.b1, .b2, .b4, .b8}` decoded as unsigned `usize` scalars, and `copy_nonoverlapping`, omitting fat/wide metadata pointers, `u128`/big-endian scalar memory ops, zero-sized typed derefs, `memmove`/`copy`, and `write_bytes`/`memset`.
10. **B10 — Parameterized `checkNonNullZero : Bool` separating raw MIR `Intrinsic(CopyNonOverlapping)` from `core::ptr::copy_nonoverlapping` (`CE3`).** Captures `E3-137`'s exact divergence at `count = 0`: `checkNonNullZero = false` permits aligned `null` sources/destinations (matching raw `CopyNonOverlapping` under `#![allow(invalid_null_arguments)]`), whereas `checkNonNullZero = true` rejects `null` as `.undefined` (`ub_checks::maybe_is_aligned_and_not_null`).
11. **B11 — `PtrScalarize` accepts arbitrary runtime `usize` counts (`ptr.add`) but only constant signed `isize` counts in `ptrOffsetInbounds`.** `checkOffsetCountOp` admits any typed `usize` local/operand or constant `isize` (`constIsizeValue?`), failing closed on non-constant dynamic negative signed `isize` counts.
12. **B12 — Single-frame execution, 64-bit targets (`pointerWidthBits == 64`, `mirProfileVersion == 1`), fail-closed base MIR gaps, and `deinitMovedPlace = true`.** Inherits `Trusted.MirSemantics`'s single-frame execution, `.unsupported` failure on `call`/`assert`/`unwindResume`, and conservative `.move` deinitialization (`deinitMovedPlace = true`).
13. **B13 — Hand-lowered monomorphized `zerocopy` model (`CE10`) vs. verbatim `Runtime(PostCleanup)` `rustc` capture.** As established by `E3-137`, `zerocopy`'s `Runtime(PostCleanup)` MIR contains `0` direct `BinOp::Offset` or `CopyNonOverlapping` nodes before cross-crate `-O2` inlining (`11` `BinOp::Offset`, `5` `CopyNonOverlapping`), so `CE10` models the monomorphized/inlined slice-free kernel directly rather than ingesting unmodified pre-inline multi-frame calls.
14. **B14 — Minor witness hygiene (`CE3`/`CE9`).** `ce3_zero_count_dangling_misaligned_and_null_split_in_trusted_mir` and `ce9_storage_dead_dangling_and_relive_reset_ub_in_trusted_mir` assert `ReachesResult` on `lowerMemOrEmpty` targets directly without repeating explicit `checkMemCopyToTrustedMir = true` conjuncts, although `.done`/`.fault .undefined` outcomes rule out `lowerMemOrEmpty`'s empty `.unsupported` fallback (`CE1`, `CE2`, `CE5`, `CE6`, and `CE10` assert `checkMemCopyToTrustedMir = true` explicitly).

## Evidence

- `support/AnnealTrustedMirCallerMemoryPtrOffsetLeScalarAndCopyNonOverlapping.lean` — `44945`-line (`2377241` bytes) zero-`sorry` Lean 4 proof module (`SHA-256 b9a82ce4b284e9c6c06e9a5c3bf260ccc72e3424378b71554cbec83a05f06930`), byte-for-byte reconstructible to frozen statement `SHA-256 2674b74c7d44db89c5fbedbf7d0234bf28d74d95a8111f17e8ceec94dd331206` with `0` non-private inserted declarations, `pub_surface_clean = true`, and `0` `Classical.choice`.
- `support/AnnealTrustedMirCallerMemoryPtrOffsetLeScalarAndCopyNonOverlapping.frozen.sha256` — SHA-256 digests pinning the frozen theorem specification and stitched proof artifact.
- `support/multi_kernel_verification_summary.json` (`SHA-256 19628a7e7a4e307b656c2cc792d640382811d444ec3ef28080833de7980702cb`) — Complete 6-gate multi-kernel verification receipts (`Lean v4.34.1` `-M4096`, `#print axioms` + `AUDIT_MAP1`, `TrustedBoundary.lean` `"preflight"` pos/neg + Pass 1 `"audit"` with `0` `Classical.choice`, `Lean v4.35.0`, `lean4export 3.1.0`, and `nanoda_bin 0.4.19` pos/neg).
- `support/zerocopy_caller_memory_ptr_offset_le_scalar_and_copy_nonoverlapping_census.json` (`SHA-256 9c7cfd463faec20607425cc0f798de6d8101a09687586666c4a5726028de9595`) — Live `rustc 1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`) + `miri 0.1.0` census (`4,737` `PostCleanup` / `4,399` `-O2 Optimized` bodies) on `google/zerocopy@4586e91c0e99c9deaf2544e5bba2654127840967` (`0.8.64`) plus `23 / 23` live `Miri` ground-truth probes.

## Revalidation

1. **Synchronous `Lean v4.34.1` & Unmodified `TrustedBoundary.lean` Pass 1 Audit (`-M4096`):**
   Check out `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, compile `Trusted/MirAst.lean`, `Trusted/MirSemantics.lean`, `Trusted.lean`, and `theory/Anneal/MirWp.lean` on `Lean v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`), and compile `support/AnnealTrustedMirCallerMemoryPtrOffsetLeScalarAndCopyNonOverlapping.lean` with:
   `lean -M4096 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` (`rc = 0`, `0` warnings).
   Run `#print axioms` over all `27` public `VrustcFormal.F1_16.*` theorems (`25 / 27` strictly `[propext]`, `2 / 27` `[propext, Quot.sound]`, `0` `Classical.choice`, `AUDIT_MAP1 bad = 0`, `extra_non_aux_pub = []`) and invoke `trusted/audit/TrustedBoundary.lean` in `"preflight"` mode (`ok = true` on `support/AnnealTrustedMirCallerMemoryPtrOffsetLeScalarAndCopyNonOverlapping.lean`, `rc = 1` rejection on frozen `sorry` spec) and `"audit"` mode with `axioms = [["Quot.sound", "Init.Prelude"], ["propext", "Init.Core"]]` (`rc = 0`, `ok = true`, `replay = true`, `4560` replayed declarations).
2. **Cross-Version `Lean v4.35.0` & External Rust Kernel Replay (`nanoda_bin 0.4.19`):**
   Compile `Trusted/MirAst.lean`, `Trusted/MirSemantics.lean`, and `support/AnnealTrustedMirCallerMemoryPtrOffsetLeScalarAndCopyNonOverlapping.lean` on `Lean v4.35.0` (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`) with `-M4096 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` (`rc = 0`), export all `27` public `VrustcFormal.F1_16.*` theorems via `leanexport` (`leanprover/lean4export@5a9a355dc6c5fd82b69058d433e2ae2e8dfbf8fe`, `3.1.0`), and replay the `1884301`-line NDJSON export through `nanoda_bin` (`ammkrn/nanoda_lib@f55114afa24efe39e007f62d31b7e8ac4243f2a6`, `0.4.19`) under `permitted_axioms: ["propext", "Quot.sound"]` (`rc = 0`, `3947` declarations checked) and `permitted_axioms: []` (`rc = 1`).
3. **First-Customer `zerocopy` MIR & `Miri` Probe Revalidation:**
   Check out `google/zerocopy@4586e91c0e99c9deaf2544e5bba2654127840967` (`0.8.64`) and compile `src/lib.rs` with `rustc 1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`) using `--edition=2021 --crate-name zerocopy --crate-type lib --cfg feature="alloc" --cfg feature="std" -Copt-level=2 -Zdump-mir="runtime-post-cleanup | runtime-optimized"` alongside the `23` `miri 0.1.0` probes archived in `support/zerocopy_caller_memory_ptr_offset_le_scalar_and_copy_nonoverlapping_census.json`.
