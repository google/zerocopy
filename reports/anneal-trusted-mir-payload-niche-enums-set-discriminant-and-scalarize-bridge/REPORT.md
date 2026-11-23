# Payload-Bearing & Wrapping-Niche Enums, `SetDiscriminant` Write-Order UB, `UnreachableEnumBranching`, and Certified `EnumScalarize` Reduction Directly Into `Anneal`'s `Trusted.MirSemantics`

## Summary

In `Anneal`'s unmodified `mirProfileVersion = 1` TCB (`Trusted/MirAst.lean` and `Trusted/MirSemantics.lean`, `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`), `MirTy.enum` admits only fieldless enums (`EnumTagRepr.{zeroSized, scalar}`), leaving payload-bearing Rust enums, uninhabited variants (`!`), `ProjectionElem::Downcast` + `Field`, `StatementKind::SetDiscriminant`, `Rvalue::Aggregate(Adt)`, and niche-encoded tag layouts (`rustc_abi::TagEncoding::Niche`, including modular wrap-around `WrappingRange` niches such as `[254..=0]`) outside the base trusted operational semantics. Across `google/zerocopy@d3362d9a657e2f943d25a0812f7b13b93e60af4d` (`0.8.64`, `rustc 1.102.0-nightly`, `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `4,859` `Runtime(PostCleanup)` MIR bodies and `4,505` `Runtime(Optimized)` MIR bodies; `support/zerocopy_payload_niche_enums_and_unreachable_branching_census.json`), live `-Zprint-type-sizes` and MIR dumps measure `40` `src/` enum declarations, `26` crate-monomorphized enum layouts (`17` `Direct`, `5` `Niche`, `2` `Single`, `2` `StructOrSingle`), `105` downstream generic enum instantiations (`46` `Direct`, `14` `Niche`, `9` `Single`, `36` `StructOrSingle`), `614` `Rvalue::Discriminant` reads, `1,081` downcast field projections, `63` enum `AggregateKind::Adt` constructors, and `45 / 4,482` crate bodies semantically rewritten by `UnreachableEnumBranching` (`switchInt` arms `2,633 -> 2,654`, `unreachable` terminators `514 -> 522`), including `FromBytes::{read_from_bytes, read_from_prefix, read_from_suffix}` redirecting uninhabited `ConvertError::Validity(!)` arms directly to `unreachable`.

Directly importing unmodified `Trusted.MirAst` and `Trusted.MirSemantics` with zero surrogate AST or `Val` types (`support/AnnealTrustedMirPayloadEnumsNicheTagSetDiscriminantAndScalarize.lean`, `23485` lines, `1157255` bytes, SHA-256 `c8569e4b0199ea5a7da011018b1c70803e9b389f24c92ee9b2864acda1827755`), the mechanized development `VrustcFormal.F1_14` establishes five core kernel-checked theorems, eleven sharpness counterexamples (`CE1`–`CE11`), and an end-to-end compilation witness lowering `Option<NonZeroU32>` and `Result<u32, !>` directly into unmodified `Trusted.MirSemantics`:

1. **Exact conservative extension `M_enum` over unmodified `Trusted.MirAst.Program` (`enum_conservative_extension_exact`).** Conservatively extending `Trusted.MirSemantics` with `WrappingRange128`, `AdtTagLayout.{empty, single, direct, niche}`, structured runtime slots `EnumSlot.{baseSlot, enumDead, liveEmpty, liveSingle, liveDirect, liveNiche}`, and the enum operations `setDiscriminant`, `assignField`, `readField`, `aggregateEnum`, `discriminantDirect`, and `switchDiscr`—grounded directly in vendored `proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a` (`Miri/ABI/WrappingRange.lean:14-71`, `Miri/Interpreter/Discriminant.lean:62-169`) and `rust-lang/rust@49d734536222bf28bb6d07d885b3a81d145981da` (`compiler/rustc_const_eval/src/interpret/discriminant.rs`, `compiler/rustc_mir_transform/src/unreachable_enum_branching.rs:18-173`)—preserves 1-step lockstep execution (`evalStepEnum (embedBaseProgram p) c (embedEnumState s) = liftStepResultEnum (evalStep p c s)`) and exact bidirectional (`↔`) semantic equivalence across `WellFormed`, `Behavior`, `ReachesResult (.fault k)`, `Diverges`, and `SatisfiesPost` for every unmodified `Trusted.MirAst.Program`. `Basis: execution (Lean kernel)`
2. **Exact modular wrapping-niche partition & `SetDiscriminant(untagged)` write-order UB characterization (`wrappingNiche_partition_and_writeOrder_iff`).** For every admitted `.niche` layout (`adtEnumDefAdmitted ed = true`, covering full-width ranges such as `Option<NonZeroU32>`, niche-before-untagged ranges, and wrap-around untagged-before-niche ranges such as `[254..=0]` in `Option<HighU8>`): (i) `tagValidRange` is the exact disjoint union of the `k` modular niche tags `[nStartBits .._M nStartBits + k - 1]` and `untaggedFieldValidRange`; (ii) `writeAdtDiscriminant` on any inhabited niche variant `v ∈ [nStart, nLast]` decodes back to `.ok v`; and (iii) `writeAdtDiscriminant` on `untaggedVariant` succeeds iff `nicheBits = some bits` already fits `tagW` and satisfies `wrappingRangeContains uRange bits = true`, deterministically faulting `.error .undefined` (`InvalidNichedEnumVariantWritten` / `InvalidUninitBytes`) whenever `nicheBits = none` (`Uninit`) or holds a niche tag or out-of-range value. `Basis: source + execution (Lean kernel)`
3. **Bidirectional soundness of `UnreachableEnumBranching` (`unreachableEnumBranching_sound_bidirectional_iff`).** Every program transformation certified by `checkUnreachableEnumBranching bodyId pSrc pTgt = true`—redirecting uninhabited, undeclared, and duplicate `SwitchTargets` arms to an appended non-cleanup `.unreachable` block `unreachBb := body.basicBlocks.length`, preserving overflowing branch constants verbatim so `.fault .unsupported` timing is invariant, and promoting at most one remaining uncovered inhabited discriminant from `otherwise` into `branches` with `otherwise := unreachBb`—preserves full `FullSemanticEquivEnum pSrc pTgt` (`↔` across `WellFormedEnum`, `BehaviorEnum`, exact `.fault k`, `DivergesEnum`, and `SatisfiesPostEnum`) with zero `enumHasStorageAnnotation` flips. `Basis: source + execution (Lean kernel)`
4. **Branchless straight-line `EnumScalarize` lowering directly into unmodified `Trusted.MirSemantics` (`enumScalarizeTrace_reduces_to_trusted_mir`).** Any finite `EnumScalarizeTrace` certified by `checkEnumScalarizeToTrustedMir trace pSrc pMir = true` eliminates every internal `.adtEnum` local (`enumLocal > argumentCount`) into flat `Trusted.MirSemantics.isSupportedScalarOrUnitTy` locals, lowering `WrappingRange128` validity checks and `SetDiscriminant(untagged)` write-order UB into a **2-statement branchless straight-line gadget `mkWrappingRangeCheckStmts`** (`scratchDiff = sub valOp (const r.start)`; `scratchGuard = subUnchecked (const ((r.end_ - r.start) mod 2^tagW)) (move scratchDiff)`), lowering `.direct` tags via `Trusted.MirAst.MirTy.enum`, and lowering `.niche` `switchDiscr` via trailing dispatch blocks `buildNicheDispatchArms` at `>= B` while keeping all original entry `BasicBlockId`s `0 .. B - 1` invariant. The resulting unmodified `Trusted.MirAst.Program` (`pMir`) is bidirectionally equivalent (`↔`) under unmodified `Trusted.MirSemantics` to `M_enum` on `pSrc` via constructive forward stuttering simulation (`fullSemanticEquivEnum_of_fwd_stutter_sim`) with `0` `Classical.choice`. `Basis: execution (Lean kernel)`
5. **Vertical pipeline composition, eleven sharpness witnesses (`CE1`–`CE11`), and 6-gate multi-kernel audit (`enumPipeline_then_optPipeline_vc_transport`).** Composing `UnreachableEnumBranching`, `EnumScalarizeTrace`, and any downstream `FullSemanticEquivBase pMir pOpt` transports `M_enum` verification conditions bidirectionally (`↔`) onto unmodified `Trusted.MirSemantics` on `pOpt`. All `26` public theorems (`22 / 26` strictly `[propext]`, `4 / 26` `[propext, Quot.sound]`, `0` `Classical.choice`, `0` `sorryAx`, `AUDIT_MAP1 total=2086 pub=868 priv=1218 bad=0`) compile on `Lean v4.34.1` (`-M4096 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`) in **`105.2149 s` / `1447.99 MB` RSS**, pass unmodified `TrustedBoundary.lean` `"preflight"` (`ok=true`) and Pass 1 `"audit"` (`replayedDeclarations = 3667`, `reachableDeclarations = 4553`, `axioms = ["propext", "Quot.sound"]`, `replay = true`), compile on `Lean v4.35.0` in **`109.7549 s` / `1396.66 MB` RSS**, export via `lean4export 3.1.0` (`1111816` NDJSON lines, `58632267` bytes), and pass independent Rust external kernel verification under `nanoda_bin 0.4.19` (`3096` declarations in **`6.5171 s` / `119.0 MB` RSS**, with negative `permitted_axioms: []` control rejected at `rc = 1`). `Basis: execution`

## Applicability

- **Primary formal verification target (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, citing `rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd` and `proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`):** Unmodified `Trusted.MirAst.Program` and `Trusted.MirSemantics` (`mirProfileVersion = 1`, `pointerWidthBits = 64`), establishing an untrusted, 0-TCB-addition `theory/` lowering bridge that compiles payload-bearing, uninhabited-variant, and unsigned-integer wrapping-niche internal enum locals directly into Anneal's existing base MIR semantics.
- **Upstream compiler source & live execution census:** `rust-lang/rust@49d734536222bf28bb6d07d885b3a81d145981da` (`compiler/rustc_const_eval/src/interpret/discriminant.rs`, `compiler/rustc_mir_transform/src/unreachable_enum_branching.rs:18-173`) and `rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`rustc 1.102.0-nightly`, `2026-11-11`, `LLVM 23.1.5`) evaluated on `google/zerocopy@d3362d9a657e2f943d25a0812f7b13b93e60af4d` (`0.8.64`, `--cfg feature="alloc"/"std"/"simd"/"simd-nightly"/"float-nightly"` plus a downstream generic instantiation crate exercising `FromBytes`, `TryFromBytes`, `ConvertError`, `CastError`, `TryReadError`, `Ptr`, and `SizeInfo`).
- **Independent Lean 4 kernel, exporter, and external Rust verifier pins:** `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`), `leanprover/lean4@eb6cafb7290e8bd5f2937522d8d804f58f02bafc` (`v4.35.0`), `leanprover/lean4export@5a9a355dc6c5fd82b69058d433e2ae2e8dfbf8fe` (`3.1.0`), and `ammkrn/nanoda_lib@f55114afa24efe39e007f62d31b7e8ac4243f2a6` (`0.4.19`).
- **Intended consumers:** Proof engineers extending `Anneal` to verify real `zerocopy` functions involving `Option`, `Result`, `ConvertError`, `SizeInfo`, and uninhabited `!` error branches without enlarging `trusted/lean/Trusted/MirAst.lean` or `trusted/lean/Trusted/MirSemantics.lean`, and compiler-verification engineers checking MIR enum lowering, `SetDiscriminant` UB ordering, and `UnreachableEnumBranching` soundness.

## Findings

### 1. First-Customer `zerocopy 0.8.64` Payload/Niche Enum & `UnreachableEnumBranching` Census

`Basis: execution (support/zerocopy_payload_niche_enums_and_unreachable_branching_census.json) + source (rust-lang/rust@49d734536222bf28bb6d07d885b3a81d145981da, google/zerocopy@d3362d9a657e2f943d25a0812f7b13b93e60af4d)`

Compiling `zerocopy 0.8.64` (`src/lib.rs`) with `rustc 1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`) under `-Zdump-mir="analysis-post-cleanup | UnreachableEnumBranching | runtime-optimized" -Zprint-type-sizes` alongside a downstream generic instantiation driver reveals how payload-bearing enums, niche tags, uninhabited `!` variants, and `UnreachableEnumBranching` behave on real systems Rust code.

#### 1.1 Source Declarations and Complete `-Zprint-type-sizes` Layout Census

Static inspection of `zerocopy/src/` identifies `40` `enum` declarations spanning zero-variant marker types (`BigEndian`, `LittleEndian`, `Shared`, `Exclusive`, `Aligned`, `Unaligned`, `Uninit`, `Initialized`, `Safe`, `BecauseExclusive`, `BecauseImmutable`, `CastSized`, `TransmuteRefMut*`, etc.), fieldless C-like enums (`byteorder::Order`, `layout::CastType`, `layout::MetadataCastError`, `pointer::invariant::ValidityKind`), and payload-bearing generic enums (`error::ConvertError<A, S, V>`, `layout::SizeInfo<E = usize>`, `CastParamsInner`). Under `-Zprint-type-sizes`, monomorphization exposes `Direct`, `Niche`, `Single`, and `StructOrSingle` layouts across `zerocopy` itself and downstream generic instantiations:

| Scope (`google/zerocopy@d3362d9a657e2f943d25a0812f7b13b93e60af4d`, `0.8.64`) | Total Monomorphized Enum/ADT Entries | `Direct` Tag | `Niche` Tag | `Single` | `StructOrSingle` |
| :--- | :---: | :---: | :---: | :---: | :---: |
| `zerocopy` crate monomorphized (`src/lib.rs`) | `26` | `17` | `5` | `2` | `2` |
| Downstream generic instantiations (`--extern zerocopy`) | `105` | `46` | `14` | `9` | `36` |

Complete `-Zprint-type-sizes` inventory for all `26` monomorphized enum/ADT entries inside `zerocopy` (`src/lib.rs`):

| Monomorphized Type (`zerocopy` crate) | Size (B) | Align (B) | Variants | Discriminant (B) | `TagEncoding` |
| :--- | :---: | :---: | :---: | :---: | :---: |
| `std::option::Option<layout::SizeInfo<std::num::NonZero<usize>>>` | `40` | `8` | `2` | `8` | `Direct` |
| `layout::SizeInfo` | `32` | `8` | `2` | `niche/none` | `Niche` |
| `layout::SizeInfo<std::num::NonZero<usize>>` | `32` | `8` | `2` | `niche/none` | `Niche` |
| `std::option::Option<i128>` | `32` | `16` | `2` | `16` | `Direct` |
| `std::option::Option<layout::TrailingSliceLayout>` | `32` | `8` | `2` | `niche/none` | `Niche` |
| `<layout::cast_from::CastFrom<Dst> as pointer::cast::Project<Src, Dst>>::project::CastParamsInner` | `24` | `8` | `3` | `8` | `Direct` |
| `std::result::Result<(usize, usize), layout::MetadataCastError>` | `24` | `8` | `2` | `1` | `Direct` |
| `std::option::Option<i64>` | `16` | `8` | `2` | `8` | `Direct` |
| `std::option::Option<isize>` | `16` | `8` | `2` | `8` | `Direct` |
| `std::option::Option<usize>` | `16` | `8` | `2` | `8` | `Direct` |
| `std::mem::alignment::AlignmentEnum` | `8` | `8` | `64` | `8` | `Direct` |
| `std::option::Option<i32>` | `8` | `4` | `2` | `4` | `Direct` |
| `std::option::Option<std::num::NonZero<usize>>` | `8` | `8` | `2` | `niche/none` | `Niche` |
| `std::option::Option<i16>` | `4` | `2` | `2` | `2` | `Direct` |
| `std::option::Option<i8>` | `2` | `1` | `2` | `1` | `Direct` |
| `byteorder::Order` | `1` | `1` | `2` | `1` | `Direct` |
| `layout::CastType` | `1` | `1` | `2` | `1` | `Direct` |
| `layout::MetadataCastError` | `1` | `1` | `2` | `1` | `Direct` |
| `pointer::invariant::ValidityKind` | `1` | `1` | `4` | `1` | `Direct` |
| `std::cmp::Ordering` | `1` | `1` | `3` | `1` | `Direct` |
| `std::option::Option<std::cmp::Ordering>` | `1` | `1` | `2` | `niche/none` | `Niche` |
| `std::result::Result<(), std::fmt::Error>` | `1` | `1` | `2` | `1` | `Direct` |
| `error::AllocError` | `0` | `1` | `0` | `niche/none` | `StructOrSingle` |
| `std::fmt::Error` | `0` | `1` | `0` | `niche/none` | `StructOrSingle` |
| `std::result::Result<!, error::AllocError>` | `0` | `1` | `1` | `niche/none` | `Single` |
| `std::result::Result<!, std::fmt::Error>` | `0` | `1` | `1` | `niche/none` | `Single` |

Complete `-Zprint-type-sizes` inventory for all `14` `Niche` and `9` `Single` downstream generic instantiations (`--extern zerocopy`):

| Monomorphized Type (Downstream Generic Probe) | Size (B) | Align (B) | Variants | Discriminant (B) | `TagEncoding` |
| :--- | :---: | :---: | :---: | :---: | :---: |
| `zerocopy::layout::SizeInfo` | `32` | `8` | `2` | `niche/none` | `Niche` |
| `zerocopy::layout::SizeInfo<std::num::NonZero<usize>>` | `32` | `8` | `2` | `niche/none` | `Niche` |
| `std::result::Result<!, zerocopy::ConvertError<zerocopy::AlignmentError<zerocopy::Ptr<'_, [u8], (zerocopy::invariant::Shared, zerocopy::invariant::Aligned, zerocopy::invariant::Safe)>, [u8; 4]>, zerocopy::SizeError<zerocopy::Ptr<'_, [u8], (zerocopy::invariant::Shared, zerocopy::invariant::Aligned, zerocopy::invariant::Safe)>, [u8; 4]>, !>>` | `24` | `8` | `1` | `niche/none` | `Single` |
| `std::result::Result<!, zerocopy::ConvertError<zerocopy::AlignmentError<zerocopy::Ptr<'_, [u8], (zerocopy::invariant::Shared, zerocopy::invariant::Aligned, zerocopy::invariant::Safe)>, bool>, zerocopy::SizeError<zerocopy::Ptr<'_, [u8], (zerocopy::invariant::Shared, zerocopy::invariant::Aligned, zerocopy::invariant::Safe)>, bool>, !>>` | `24` | `8` | `1` | `niche/none` | `Single` |
| `std::result::Result<!, zerocopy::ConvertError<zerocopy::AlignmentError<zerocopy::Ptr<'_, [u8], (zerocopy::invariant::Shared, zerocopy::invariant::Aligned, zerocopy::invariant::Safe)>, u32>, zerocopy::SizeError<zerocopy::Ptr<'_, [u8], (zerocopy::invariant::Shared, zerocopy::invariant::Aligned, zerocopy::invariant::Safe)>, u32>, !>>` | `24` | `8` | `1` | `niche/none` | `Single` |
| `std::result::Result<&bool, zerocopy::ConvertError<zerocopy::AlignmentError<&[u8], bool>, zerocopy::SizeError<&[u8], bool>, zerocopy::ValidityError<&[u8], bool>>>` | `24` | `8` | `2` | `niche/none` | `Niche` |
| `std::result::Result<&u32, zerocopy::ConvertError<zerocopy::AlignmentError<&[u8], u32>, zerocopy::SizeError<&[u8], u32>, !>>` | `24` | `8` | `2` | `niche/none` | `Niche` |
| `std::result::Result<bool, zerocopy::ConvertError<!, zerocopy::SizeError<&[u8], bool>, zerocopy::ValidityError<&[u8], bool>>>` | `24` | `8` | `2` | `niche/none` | `Niche` |
| `std::result::Result<zerocopy::Ptr<'_, [u8; 4], (zerocopy::invariant::Shared, zerocopy::invariant::Aligned, zerocopy::invariant::Initialized)>, zerocopy::ConvertError<zerocopy::AlignmentError<zerocopy::Ptr<'_, [u8], (zerocopy::invariant::Shared, zerocopy::invariant::Aligned, zerocopy::invariant::Safe)>, [u8; 4]>, zerocopy::SizeError<zerocopy::Ptr<'_, [u8], (zerocopy::invariant::Shared, zerocopy::invariant::Aligned, zerocopy::invariant::Safe)>, [u8; 4]>, !>>` | `24` | `8` | `2` | `niche/none` | `Niche` |
| `std::result::Result<zerocopy::Ptr<'_, bool, (zerocopy::invariant::Shared, zerocopy::invariant::Aligned, zerocopy::invariant::Initialized)>, zerocopy::ConvertError<zerocopy::AlignmentError<zerocopy::Ptr<'_, [u8], (zerocopy::invariant::Shared, zerocopy::invariant::Aligned, zerocopy::invariant::Safe)>, bool>, zerocopy::SizeError<zerocopy::Ptr<'_, [u8], (zerocopy::invariant::Shared, zerocopy::invariant::Aligned, zerocopy::invariant::Safe)>, bool>, !>>` | `24` | `8` | `2` | `niche/none` | `Niche` |
| `std::result::Result<zerocopy::Ptr<'_, u32, (zerocopy::invariant::Shared, zerocopy::invariant::Aligned, zerocopy::invariant::Initialized)>, zerocopy::ConvertError<zerocopy::AlignmentError<zerocopy::Ptr<'_, [u8], (zerocopy::invariant::Shared, zerocopy::invariant::Aligned, zerocopy::invariant::Safe)>, u32>, zerocopy::SizeError<zerocopy::Ptr<'_, [u8], (zerocopy::invariant::Shared, zerocopy::invariant::Aligned, zerocopy::invariant::Safe)>, u32>, !>>` | `24` | `8` | `2` | `niche/none` | `Niche` |
| `std::option::Option<zerocopy::Ptr<'_, [u8], (zerocopy::invariant::Exclusive, zerocopy::invariant::Unaligned, zerocopy::invariant::Initialized)>>` | `16` | `8` | `2` | `niche/none` | `Niche` |
| `std::option::Option<zerocopy::PtrInner<'_, [u8]>>` | `16` | `8` | `2` | `niche/none` | `Niche` |
| `std::result::Result<u32, zerocopy::SizeError<&[u8], u32>>` | `16` | `8` | `2` | `niche/none` | `Niche` |
| `std::option::Option<std::num::NonZero<usize>>` | `8` | `8` | `2` | `niche/none` | `Niche` |
| `std::option::Option<std::ptr::NonNull<u8>>` | `8` | `8` | `2` | `niche/none` | `Niche` |
| `std::option::Option<zerocopy::Ptr<'_, u32, (zerocopy::invariant::Shared, zerocopy::invariant::Aligned, zerocopy::invariant::Initialized)>>` | `8` | `8` | `2` | `niche/none` | `Niche` |
| `std::result::Result<&u32, !>` | `8` | `8` | `1` | `niche/none` | `Single` |
| `std::result::Result<u32, !>` | `4` | `4` | `1` | `niche/none` | `Single` |
| `zerocopy::util::transmute_unchecked::Transmute<zerocopy::Unalign<u32>, u32>` | `4` | `4` | `1` | `niche/none` | `Single` |
| `std::mem::MaybeUninit<bool>` | `1` | `1` | `1` | `niche/none` | `Single` |
| `std::result::Result<!, zerocopy::layout::MetadataCastError>` | `1` | `1` | `1` | `niche/none` | `Single` |
| `std::result::Result<(), !>` | `0` | `1` | `1` | `niche/none` | `Single` |

Two architectural implications stand out immediately from these layout tables:

1. **Unsigned-integer niches (`Option<NonZero<usize>>`, `Option<NonZero<u32>>`) and `Direct` / `Single` payload enums (`Option<usize>`, `Result<(usize, usize), MetadataCastError>`, `Result<u32, !>`, `Result<!, AllocError>`, `CastParamsInner`) map cleanly onto scalarized flat locals** in `VrustcFormal.F1_14`.
2. **Pointer-carried niches (`Option<PtrInner<'_, [u8]>>`, `Option<Ptr<'_, ...>>`, `Result<&u32, ConvertError<..., !>>`) and nested struct/enum niches (`layout::SizeInfo`, `Option<TrailingSliceLayout>`) form the exact boundary (`B3`–`B4`)** motivating future integration with Anneal's pointer/memory model once `Trusted.MirSemantics` models non-null references and multi-level struct projection.

#### 1.2 MIR Enum Operation Counts (`Runtime(PostCleanup)` vs. `Runtime(Optimized)`)

Scanning all dumped MIR bodies across `zerocopy 0.8.64` quantifies the exact prevalence of every enum construct in `Runtime(PostCleanup)` versus `Runtime(Optimized)`:

| MIR Metric (`zerocopy 0.8.64`, `rustc 1.102.0-nightly`) | `Runtime(PostCleanup)` | `Runtime(Optimized)` | Net Delta (`PostCleanup -> Optimized`) |
| :--- | :---: | :---: | :---: |
| Total MIR bodies dumped | `4,859` | `4,505` | `-354` |
| `StatementKind::SetDiscriminant` | `0` | `0` | `0` |
| `Rvalue::Discriminant` | `614` | `563` | `-51` |
| `AggregateKind::Adt` (enum constructors) | `63` | `66` | `+3` |
| Downcast field projections (`(_x as Variant).f`) | `1,081` | `586` | `-495` |
| `TerminatorKind::SwitchInt` | `1,117` | `995` | `-122` |
| `SwitchInt` total explicit arms | `2,842` | `2,208` | `-634` |
| `TerminatorKind::Unreachable` | `544` | `160` | `-384` |

An important empirical finding—reconfirming our earlier `E3-17` measurement (`0` `SetDiscriminant` across `4,663` post-cleanup / `4,302` optimized bodies)—is why `SetDiscriminant` appears `0` times in `zerocopy`'s `Runtime(PostCleanup)` MIR despite `63` enum constructors and `614` discriminant reads: `rustc`'s MIR builder lowers standard Rust enum struct/tuple construction expressions directly into monolithic `Rvalue::Aggregate(AggregateKind::Adt(...))`, reserving `StatementKind::SetDiscriminant` for `Aggregate` deaggregation (late MIR `DestProp`/`DataflowConstProp`/codegen preparation), coroutine generator state transitions, and explicit `custom_mir!` / unsized-rvalue construction. Modeling **both** `EnumStmt.aggregateEnum` (the dominant `PostCleanup` form) and `EnumStmt.assignField` + `EnumStmt.setDiscriminant` (the deaggregated form where write-order UB arises) ensures our semantics and scalarization pass cover both unmodified `PostCleanup` MIR and deaggregated MIR seamlessly.

#### 1.3 `UnreachableEnumBranching` Pass Impact on Real `zerocopy` Functions

Comparing MIR immediately before and after `UnreachableEnumBranching` (`compiler/rustc_mir_transform/src/unreachable_enum_branching.rs:18-173`) across `zerocopy 0.8.64`:

| Corpus | Bodies Checked | Bodies Semantically Modified | `switchInt` (`before -> after`) | `switchInt` Arms (`before -> after`) | `unreachable` Terminators (`before -> after`) |
| :--- | :---: | :---: | :---: | :---: | :---: |
| `zerocopy` crate (`src/lib.rs`) | `4,482` | `45` | `1,041 -> 1,041` | `2,633 -> 2,654` (`+21`) | `514 -> 522` (`+8`) |
| Downstream generic instantiations | `2` (`use_generic_enums`) | `1` | `17 -> 17` | `46 -> 47` (`+1`) | `3 -> 3` (`0`) |

Notice why `switchInt` arms *increase* (`2,633 -> 2,654`, `+21`) when `UnreachableEnumBranching` runs: whenever a `switchInt` over an enum discriminant omits one inhabited variant in `branches` (routing it through `otherwise`) and prunes the remaining uninhabited variants, `rustc`'s `UnreachableEnumBranching` (`unreachable_enum_branching.rs:134-169`) **promotes** the sole remaining uncovered inhabited discriminant into an explicit `(lastDiscr, targets.otherwise)` branch and rewrites `otherwise` to an `unreachable` basic block. That exact transformation—simultaneously redirecting uninhabited arms to `unreachable` and promoting the last remaining inhabited variant from `otherwise` into `branches`—is mirrored verbatim in `applyUnreachableEnumBranchingBlock`.

First `20` of the `45` `zerocopy` MIR bodies semantically modified by `UnreachableEnumBranching` (`support/zerocopy_payload_niche_enums_and_unreachable_branching_census.json`):

| Modified MIR Body (`zerocopy 0.8.64`) | `switchInt` | Arms (`before -> after`) | `unreachable` (`before -> after`) | Source Anchor / Kind |
| :--- | :---: | :---: | :---: | :--- |
| `FromBytes-read_from_bytes` | `2 -> 2` | `7 -> 7` | `2 -> 2` | monomorphized MIR item |
| `FromBytes-read_from_prefix` | `2 -> 2` | `7 -> 7` | `2 -> 2` | monomorphized MIR item |
| `FromBytes-read_from_suffix` | `2 -> 2` | `7 -> 7` | `2 -> 2` | monomorphized MIR item |
| `IntoBytes-write_to_suffix` | `2 -> 2` | `4 -> 6` | `0 -> 1` | monomorphized MIR item |
| `error-{impl#13}-display_verbose_extras` | `15 -> 15` | `42 -> 43` | `1 -> 1` | `zerocopy/src/error.rs:436` |
| `impls-tuples-_-{impl#1031}-is_safe` | `43 -> 43` | `108 -> 108` | `23 -> 23` | `zerocopy/src/util/macros.rs:128` |
| `impls-tuples-_-{impl#1124}-is_safe` | `45 -> 45` | `113 -> 113` | `24 -> 24` | `zerocopy/src/util/macros.rs:128` |
| `impls-tuples-_-{impl#116}-is_safe` | `13 -> 13` | `33 -> 33` | `8 -> 8` | `zerocopy/src/util/macros.rs:128` |
| `impls-tuples-_-{impl#11}-is_safe` | `3 -> 3` | `8 -> 8` | `3 -> 3` | `zerocopy/src/util/macros.rs:128` |
| `impls-tuples-_-{impl#1221}-is_safe` | `47 -> 47` | `118 -> 118` | `25 -> 25` | `zerocopy/src/util/macros.rs:128` |
| `impls-tuples-_-{impl#1322}-is_safe` | `49 -> 49` | `123 -> 123` | `26 -> 26` | `zerocopy/src/util/macros.rs:128` |
| `impls-tuples-_-{impl#1427}-is_safe` | `51 -> 51` | `128 -> 128` | `27 -> 27` | `zerocopy/src/util/macros.rs:128` |
| `impls-tuples-_-{impl#149}-is_safe` | `15 -> 15` | `38 -> 38` | `9 -> 9` | `zerocopy/src/util/macros.rs:128` |
| `impls-tuples-_-{impl#186}-is_safe` | `17 -> 17` | `43 -> 43` | `10 -> 10` | `zerocopy/src/util/macros.rs:128` |
| `impls-tuples-_-{impl#227}-is_safe` | `19 -> 19` | `48 -> 48` | `11 -> 11` | `zerocopy/src/util/macros.rs:128` |
| `impls-tuples-_-{impl#24}-is_safe` | `5 -> 5` | `13 -> 13` | `4 -> 4` | `zerocopy/src/util/macros.rs:128` |
| `impls-tuples-_-{impl#272}-is_safe` | `21 -> 21` | `53 -> 53` | `12 -> 12` | `zerocopy/src/util/macros.rs:128` |
| `impls-tuples-_-{impl#2}-is_safe` | `1 -> 1` | `3 -> 3` | `2 -> 2` | `zerocopy/src/util/macros.rs:128` |
| `impls-tuples-_-{impl#321}-is_safe` | `23 -> 23` | `58 -> 58` | `13 -> 13` | `zerocopy/src/util/macros.rs:128` |
| `impls-tuples-_-{impl#374}-is_safe` | `25 -> 25` | `63 -> 63` | `14 -> 14` | `zerocopy/src/util/macros.rs:128` |

Additional concrete `zerocopy` functions exercising niche `Option`/`Result` layouts and uninhabited `!` error variants (`ConvertError<..., !>`) include `FromBytes::mut_from_bytes` (`zerocopy/src/lib.rs:4781`), `FromBytes::mut_from_bytes_with_elems` (`zerocopy/src/lib.rs:5323`), `FromBytes::ref_from_bytes` (`zerocopy/src/lib.rs:4491`), `FromBytes::ref_from_bytes_with_elems` (`zerocopy/src/lib.rs:5049`), `FromBytes::{mut_from, mut_from_prefix, mut_from_suffix, ref_from, ref_from_prefix, ref_from_suffix}`, `FromZeros::insert_vec_zeroed` (`zerocopy/src/lib.rs:4137`), `TryFromBytes::{try_mut_from_bytes, try_mut_from_bytes_with_elems, try_ref_from_bytes, try_ref_from_bytes_with_elems, try_read_from_prefix, try_read_from_suffix}` (`zerocopy/src/lib.rs:2113,2439,2757,3081,3424,3513`), and `byteorder::Order::fmt` (`zerocopy/src/byteorder.rs:102`).

Verbatim before/after MIR excerpt from `FromBytes::read_from_bytes` (`support/zerocopy_payload_niche_enums_and_unreachable_branching_census.json`, showing `bb3` redirecting uninhabited `ConvertError::Validity(!)` arm `2: bb4` -> `2: bb2` `unreachable`):

```mir
// MIR for `FromBytes::read_from_bytes` before UnreachableEnumBranching

fn FromBytes::read_from_bytes(_1: &[u8]) -> Result<Self, error::SizeError<&[u8], Self>> {
    debug source => _1;
    let mut _0: std::result::Result<Self, error::SizeError<&[u8], Self>>;
    let mut _2: std::result::Result<r#ref::def::Ref<&[u8], wrappers::Unalign<Self>>, error::ConvertError<error::AlignmentError<&[u8], wrappers::Unalign<Self>>, error::SizeError<&[u8], wrappers::Unalign<Self>>, !>>;
    let mut _3: &[u8];
    let mut _4: isize;
    let mut _5: isize;
    let _6: r#ref::def::Ref<&[u8], wrappers::Unalign<Self>>;
    let mut _7: Self;
    let mut _8: wrappers::Unalign<Self>;
    let mut _9: &r#ref::def::Ref<&[u8], wrappers::Unalign<Self>>;
    let _10: &r#ref::def::Ref<&[u8], wrappers::Unalign<Self>>;
    let _11: error::SizeError<&[u8], wrappers::Unalign<Self>>;
    let mut _12: error::SizeError<&[u8], Self>;
    let mut _13: error::SizeError<&[u8], wrappers::Unalign<Self>>;
    let mut _14: !;
    let _15: !;
    let mut _16: !;
    scope 1 {
        debug r => _6;
    }
    scope 2 {
        debug e => _11;
    }
    scope 3 {
        debug i => const ZeroSized: !;
    }

    bb0: {
        _3 = copy _1;
        _2 = r#ref::<impl r#ref::def::Ref<&[u8], wrappers::Unalign<Self>>>::sized_from(move _3) -> [return: bb1, unwind continue];
    }

    bb1: {
        _5 = discriminant(_2);
        switchInt(move _5) -> [0: bb7, 1: bb3, otherwise: bb2];
    }

    bb2: {
        unreachable;
    }

    bb3: {
        _4 = discriminant(((_2 as Err).0: error::ConvertError<error::AlignmentError<&[u8], wrappers::Unalign<Self>>, error::SizeError<&[u8], wrappers::Unalign<Self>>, !>));
```

```mir
// MIR for `FromBytes::read_from_bytes` after UnreachableEnumBranching

fn FromBytes::read_from_bytes(_1: &[u8]) -> Result<Self, error::SizeError<&[u8], Self>> {
    debug source => _1;
    let mut _0: std::result::Result<Self, error::SizeError<&[u8], Self>>;
    let mut _2: std::result::Result<r#ref::def::Ref<&[u8], wrappers::Unalign<Self>>, error::ConvertError<error::AlignmentError<&[u8], wrappers::Unalign<Self>>, error::SizeError<&[u8], wrappers::Unalign<Self>>, !>>;
    let mut _3: &[u8];
    let mut _4: isize;
    let mut _5: isize;
    let _6: r#ref::def::Ref<&[u8], wrappers::Unalign<Self>>;
    let mut _7: Self;
    let mut _8: wrappers::Unalign<Self>;
    let mut _9: &r#ref::def::Ref<&[u8], wrappers::Unalign<Self>>;
    let _10: &r#ref::def::Ref<&[u8], wrappers::Unalign<Self>>;
    let _11: error::SizeError<&[u8], wrappers::Unalign<Self>>;
    let mut _12: error::SizeError<&[u8], Self>;
    let mut _13: error::SizeError<&[u8], wrappers::Unalign<Self>>;
    let mut _14: !;
    let _15: !;
    let mut _16: !;
    scope 1 {
        debug r => _6;
    }
    scope 2 {
        debug e => _11;
    }
    scope 3 {
        debug i => const ZeroSized: !;
    }

    bb0: {
        _3 = copy _1;
        _2 = r#ref::<impl r#ref::def::Ref<&[u8], wrappers::Unalign<Self>>>::sized_from(move _3) -> [return: bb1, unwind continue];
    }

    bb1: {
        _5 = discriminant(_2);
        switchInt(move _5) -> [0: bb7, 1: bb3, otherwise: bb2];
    }

    bb2: {
        unreachable;
    }

    bb3: {
        _4 = discriminant(((_2 as Err).0: error::ConvertError<error::AlignmentError<&[u8], wrappers::Unalign<Self>>, error::SizeError<&[u8], wrappers::Unalign<Self>>, !>));
```

---

### 2. Wrapping Niche Arithmetic & `SetDiscriminant` Write-Order UB (`E3-17` Empirical Grounding)

`Basis: source (proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a, rust-lang/rust@49d734536222bf28bb6d07d885b3a81d145981da) + execution`

Real `rustc` enum layouts exhibit three subtle semantic phenomena that naive non-wrapping or tag-only enum models get wrong. Each was empirically probed on live `rustc 1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`) and Miri before formalizing `VrustcFormal.F1_14`:

1. **Wrap-around `WrappingRange` tags (`start > end_`).** When an untagged variant's niche field has a valid range reaching the top of its integer width—such as a `u8` scalar restricted to `[254..=255]` (`HighU8`) inside `Option<HighU8>` or a 3-variant enum whose niche tags wrap across `255 -> 0`—`rustc_abi::WrappingRange` represents the combined valid tag range with `start > end_` (e.g., `[254..=0]` for `Option<HighU8>`, or `[255..=0]` across wrap-around). On live `rustc 1.102.0-nightly` + Miri (`miri_rc = 0`), a 1-byte `u8` niche enum with edge untagged variant produces `SZ_INNER=1 SZ_EDGE=1 SZ_MIDDLE=2 SZ_OPT2_BOOL=1 EDGE_BYTES=(255, 1..254, 0) CLASS=(10, 20, 30)`, and LLVM lowers the wrap-around discriminant classification via modular addition (`leal 2(%rdi), %eax` followed by unsigned range test). Crucially, placing the untagged variant *between* two niche variants (`untaggedVariant ∈ [nicheStartVariant, nicheLastVariant]`) disables niche optimization in `rustc` (`SZ_MIDDLE = 2`, explicit 2-byte `Direct` tag) because `TagEncoding::Niche` encodes niche variants as a single contiguous index interval `niche_variants = start..=end` mapped linearly modulo $2^{\text{tagW}}$ from `niche_start` (`vendor/lean-miri/Miri/Interpreter/Discriminant.lean:141-149`). `adtEnumDefAdmitted` enforces `!(Nat.ble nStart untagged && Nat.ble untagged nLast)` (`CE6`).
2. **`SetDiscriminant` write-order UB (`InvalidNichedEnumVariantWritten`).** In `compiler/rustc_const_eval/src/interpret/discriminant.rs` and `vendor/lean-miri/Miri/Interpreter/Discriminant.lean:158-168`, executing `StatementKind::SetDiscriminant(place, variant_index)` on a `TagEncoding::Niche` enum has asymmetric semantics:
   - If `variant_index ∈ [nStart, nLast]` (a niche variant), `SetDiscriminant` **writes** the niche bit pattern `((variant_index - nStart) + nicheStartBits) mod 2^tagW` into the niche scalar location (overwriting whatever payload previously lived there).
   - If `variant_index == untaggedVariant`, `SetDiscriminant` writes **nothing**—instead, it **reads and decodes** the existing niche scalar and triggers immediate UB (`InvalidNichedEnumVariantWritten` or `InvalidUninitBytes`) unless the payload field was *already* written with a valid bit pattern in `untaggedFieldValidRange`!
   Live Miri confirms this contrast sharply:
   - Writing `(_x as Some).0 = NonZeroU8` *before* `SetDiscriminant(_x, Some)`: native `-O` exits `rc = 0`, Miri exits `rc = 0`.
   - Executing `SetDiscriminant(_x, Some)` *before* writing `(_x as Some).0`: native `-O` silently exits `rc = 0`, whereas Miri halts with `rc = 1`:
     `error: Undefined Behavior: trying to set discriminant of a std::option::Option<std::num::NonZero<u8>> to the niched variant, but the value does not match`.
   - Reading an invalid niche hole byte (`0x03` in `Option<bool>`): native `-O` silently exits `rc = 0`, whereas Miri halts with `rc = 1`:
     `error: Undefined Behavior: enum value has invalid tag: 0x03`.
3. **Stale-niche overwrite aliasing (`CE2`).** Because a niche variant's tag physically aliases the `nicheFieldIdx` scalar of `untaggedVariant`, writing `(_x as Some).0 = 42; SetDiscriminant(_x, Some); SetDiscriminant(_x, None)` destroys the `42` stored in the niche carrier by overwriting it with `0`. A subsequent `SetDiscriminant(_x, Some)` without rewriting `(_x as Some).0` therefore encounters `0 ∉ [1..=2^32 - 1]` and deterministically triggers `.fault .undefined` both in `M_enum` and after lowering to unmodified `Trusted.MirSemantics`.

---

### 3. Operational Semantics of `M_enum` Conservatively Extending `Trusted.MirSemantics`

`Basis: execution (Lean kernel, support/AnnealTrustedMirPayloadEnumsNicheTagSetDiscriminantAndScalarize.lean)`

`VrustcFormal.F1_14` defines `M_enum` strictly on top of unmodified `Trusted.MirAst` and `Trusted.MirSemantics` (importing only `Trusted.MirAst` and `Trusted.MirSemantics` with `prelude`), preserving all base scalar values (`Val`), types (`MirTy`), `LocalSlot`, `Query`, `TerminalOut`, `FaultKind`, `evalBinOp`, `evalUnOp`, `evalConstLit`, `evalSwitchBranches`, and `evalBoolSwitchBranches` verbatim.

#### 3.1 Wrapping Ranges, Modular Partition Admission (`checkNicheRangePartition`), and `adtEnumDefAdmitted`

- **`WrappingRange128` (`start end_ : BitVec 128`):** `wrappingRangeContains r v` matches `Miri.ABI.WrappingRange.contains` (`WrappingRange.lean:39-44`) bit-for-bit:
  - If `r.start.toNat ≤ r.end_.toNat` (non-wrapping): `r.start.toNat ≤ v.toNat ∧ v.toNat ≤ r.end_.toNat`.
  - If `r.start.toNat > r.end_.toNat` (wrap-around): `r.start.toNat ≤ v.toNat ∨ v.toNat ≤ r.end_.toNat`.
- **Modular arithmetic helpers:** `subTruncBits w a b := truncateBits w (a - b)` and `addTruncBits w a b := truncateBits w (a + b)` match `Size.truncate (a - b)` and `Size.truncate (a + b)` in `Miri/ABI/WrappingRange.lean:80` and `Miri/Interpreter/Discriminant.lean:87,141`.
- **Exact $O(1) + O(k)$ modular partition check (`checkNicheRangePartition`):** Rejects `k = 0`, `k >= 2^tagW`, or `k > 64`, verifies `nStartBits`, `tagRange`, and `uRange` fit in `tagW`, checks via `checkNicheTagsDisjoint` that every niche tag `(nStartBits + i) mod 2^tagW` (`0 <= i < k`) lies in `tagRange` and outside `uRange`, and verifies that `tagRange` is the exact contiguous modular union of the `k` niche tags and `uRange` across all three `rustc` layout geometries (`fullCase`, `nicheBeforeUntagged`, `untaggedBeforeNiche`):

```lean
noncomputable def checkNicheRangePartition (tagW : IntWidth) (k : Nat)
    (nicheStartBits : BitVec 128)
    (tagValidRange untaggedRange : WrappingRange128) : Bool :=
  let m := Nat.pow 2 tagW.bitWidth
  if Nat.beq k 0 || !Nat.blt k m || !Nat.ble k 64 then
    false
  else if !(truncateBits tagW nicheStartBits == nicheStartBits) ||
      !wrappingRangeFitsWidth tagW tagValidRange ||
      !wrappingRangeFitsWidth tagW untaggedRange then
    false
  else if !checkNicheTagsDisjoint tagW nicheStartBits tagValidRange untaggedRange k then
    false
  else
    let kBits := BitVec.ofNat 128 k
    let oneBits := BitVec.ofNat 128 1
    let nicheAfterLast := addTruncBits tagW nicheStartBits kBits
    let nicheLastBits := addTruncBits tagW nicheStartBits (BitVec.ofNat 128 (k - 1))
    let uAfterEnd := addTruncBits tagW untaggedRange.end_ oneBits
    let fullCase :=
      (tagValidRange.start == BitVec.ofNat 128 0) &&
        (tagValidRange.end_ == maxUnsignedBits tagW) &&
        (untaggedRange.start == nicheAfterLast) &&
        (uAfterEnd == nicheStartBits)
    let nicheBeforeUntagged :=
      (tagValidRange.start == nicheStartBits) &&
        (untaggedRange.start == nicheAfterLast) &&
        (tagValidRange.end_ == untaggedRange.end_) &&
        !wrappingRangeContains tagValidRange uAfterEnd
    let untaggedBeforeNiche :=
      (tagValidRange.start == untaggedRange.start) &&
        (nicheStartBits == uAfterEnd) &&
        (tagValidRange.end_ == nicheLastBits) &&
        !wrappingRangeContains tagValidRange nicheAfterLast
    fullCase || nicheBeforeUntagged || untaggedBeforeNiche
```

- **Additional `adtEnumDefAdmitted` invariants for `.niche`:**
  - `ed.variants.length < 2^32`, `nStart <= nLast < ed.variants.length`, `untagged < ed.variants.length`, and `untagged ∉ [nStart, nLast]` (`CE6`).
  - `checkAllInhabitedVariantsCoveredByNiche`: every variant `v` is either `untagged`, in `[nStart, nLast]`, or uninhabited (`CE11` rejects extra uncovered inhabited variants outside `{untagged} ∪ [nStart, nLast]`).
  - `checkNicheVariantsZst`: every variant in `[nStart, nLast]` carries exclusively inhabited ZST fields (`isZstBaseTy`, i.e., `.unit` or admitted `.zeroSized` 1-variant fieldless `.enum`; `CE11` witnesses `.unit` ZST niche payload lowering).
  - `untagged` is inhabited (`!variantIsUninhabited uVd`) and its `nicheField` has unsigned integer type `.int tagW false`.

#### 3.2 `EnumProgram` AST, Runtime Slots (`EnumSlot`), and Small-Step Rules

`EnumProgram` extends `Program` with `enumDefs : List AdtEnumDef`, `EnumLocalDecl.{base ty, adtEnum eIdx}`, `EnumStmt.{baseStmt, setDiscriminant, assignField, readField, aggregateEnum, discriminantDirect}`, and `EnumTerminator.{baseTerm, switchDiscr}`. Canonical embedding `embedBaseProgram : Program → EnumProgram` maps `enumDefs := []` and wraps every base local, statement, and terminator, with exact partial inverse `unembedBaseProgram : EnumProgram → Option Program` (`unembedBaseProgram_eq_embed : unembedBaseProgram pFlat = some pOut → pFlat = embedBaseProgram pOut`).

Runtime slots `EnumSlot` track exact liveness, tag validity, and field-granular initialization:

| `EnumSlot` Constructor | Layout | State Carried | Initialization at Entry / `StorageLive` (`liveUninitEnumSlot`) |
| :--- | :--- | :--- | :--- |
| `.baseSlot s` | `.base ty` | Exact `Trusted.MirSemantics.LocalSlot` (`.dead` / `.live optVal`) | `.baseSlot (liveUninitSlot ty)` (or `.dead` if storage-annotated) |
| `.enumDead` | `.adtEnum eIdx` | Dead storage (`LocalValue::Dead`) | Entry when `enumHasStorageAnnotation body idx = true`, or after `StorageDead` |
| `.liveEmpty` | `.empty` | Live 0-variant enum | `.liveEmpty` |
| `.liveSingle fs` | `.single` | `fs : List (Option Val)` per field of `vd₀` | `vd₀.fields.map initFieldOptVal` (`some .unit` / ZST enum `some (.enumVal ety 0)`, scalars `none`) |
| `.liveDirect tag vfs` | `.direct tagW tagS` | `tag : Option Nat` (`none` = `Uninit`), `vfs : List (List (Option Val))` | `tag := none`, per-variant `vd.fields.map initFieldOptVal` |
| `.liveNiche nicheBits extras` | `.niche ...` | `nicheBits : Option (BitVec 128)` (shared carrier), `extras : List (Option Val)` (`f ≠ nicheField` of `untagged`) | `nicheBits := none`, `initNicheExtraFieldsAux nicheField 0 uVd.fields` |

Exact `decodeNicheVariant` semantics matching `vendor/lean-miri/Miri/Interpreter/Discriminant.lean:127-156`:

```lean
noncomputable def decodeNicheVariant (ed : AdtEnumDef)
    (tagW : IntWidth) (untagged nStart nLast : Nat)
    (nStartBits : BitVec 128) (tagRange : WrappingRange128) :
    Option (BitVec 128) → Except FaultKind Nat
  | none => .error .undefined
  | some bits =>
    if truncateBits tagW bits != bits then
      .error .unsupported
    else if !wrappingRangeContains tagRange bits then
      .error .undefined
    else
      let rel := subTruncBits tagW bits nStartBits
      let span := nLast - nStart
      let idx :=
        if Nat.ble rel.toNat span then
          nStart + rel.toNat
        else
          untagged
      match Trusted.MirSemantics.getElem? ed.variants idx with
      | none => .error .unsupported
      | some vd =>
        if variantIsUninhabited vd then
          .error .undefined
        else
          .ok idx
```

Key operational semantics rules in `evalEnumStmt` and `evalEnumTerminator`:

- **`readAdtDiscriminant`:** On `.enumDead` or `.empty` (`.liveEmpty`), returns `.error .undefined`. On `.single`, faults `.undefined` if `vd₀` is uninhabited, else returns truncated `vd₀.discrVal`. On `.direct`, faults `.undefined` if `tag = none` or `variants[v]` is uninhabited, else returns truncated `vd.discrVal`. On `.niche`, delegates to `decodeNicheVariant` and returns truncated `vd.discrVal`.
- **`writeAdtDiscriminant` (`SetDiscriminant`):** Checks `v < variants.length`, `slot ≠ .enumDead` (else `.undefined`), and `!variantIsUninhabited vd` (else `.undefined`, `CE4`). On `.single`, is a no-op for `v = 0`. On `.direct`, sets `tag := some v`. On `.niche`: writes `some (addTruncBits tagW (BitVec.ofNat 128 (v - nStart)) nStartBits)` for `v ∈ [nStart, nLast]`; for `v == untagged`, invokes `decodeNicheVariant` and returns `.ok (.liveNiche nicheBits extras)` iff `actual == untagged`, otherwise `.error .undefined` (`CE1`, `CE2`).
- **`writeAdtField` (`assignField`):** Fails closed to `.unsupported` if `rvalueMentionsLocal localId rval`. Evaluates `rval` first (preserving operand fault ordering before destination `DeadLocal` checks), then writes into the field; for `.niche` with `v == untagged` and `f == nicheField`, checks `wrappingRangeContains uRange sv.bits` and faults `.fault .undefined` on out-of-range niche values (`CE3`).
- **`readAdtField` (`readField`):** Rejects `dstLocal == srcLocal` (`CE8`). On `.niche` with `v == untagged` and `f == nicheField`, checks `nicheBits = some bits` and `wrappingRangeContains uRange bits` (faulting `.fault .undefined` when reading `Some`'s payload from a `None` niche tag, `CE7`), and resets `nicheBits := none` when `isMove = true` (conservative field move deinitialization).
- **`aggregateEnum`:** Rejects self-aliasing (`ops.any (stmtMentionsLocalOperand dstLocal)`). Evaluates `ops` left-to-right via `evalAggregateEnumOperands` against `vd.fields` *before* checking `slots₁[dstLocal] != .enumDead` (`CE8`) and `!variantIsUninhabited vd`, then writes all fields via `writeAdtFieldsSeq` and commits the discriminant via `writeAdtDiscriminant`.
- **`discriminantDirect` vs. `switchDiscr`:** `EnumStmt.discriminantDirect` supports `.empty`, `.single`, and `.direct` layouts (failing closed to `.unsupported` on `.niche`), while `EnumTerminator.switchDiscr discrDst enumLocal targets` fuses discriminant read, `writeEnumBasePlace` into `discrDst`, and `evalSwitchBranches` across all four layouts including `.niche`.

---

### 4. Certified Lowering Architecture: `UnreachableEnumBranching` & `EnumScalarize`

`Basis: execution (Lean kernel, support/AnnealTrustedMirPayloadEnumsNicheTagSetDiscriminantAndScalarize.lean)`

#### 4.1 Pass A: `applyUnreachableEnumBranching` & `checkUnreachableEnumBranching`

Matching `compiler/rustc_mir_transform/src/unreachable_enum_branching.rs:52-172` (`rust-lang/rust@49d734536222bf28bb6d07d885b3a81d145981da`), `applyUnreachableEnumBranching pSrc bodyId`:

1. Verifies all `pSrc.enumDefs` are admitted (`adtEnumDefAdmitted`), `body.basicBlocks` is non-empty, and `enumBodyTargetsInBounds body = true` (ensuring no pre-existing jump can alias the newly appended trap block).
2. Appends a single fresh non-cleanup trap block `trapBb := { statements := [], terminator := .baseTerm .unreachable, cleanup := false }` at `unreachBb := body.basicBlocks.length`. Because `trapBb.statements = []`, `enumHasStorageAnnotation` is **strictly invariant** for every local (`unreachableEnumBranching_body_annotations_eq`), preventing the dead-block `StorageDead` UB-erasure hazard.
3. Rewrites every non-cleanup `.switchDiscr discrDst enumLocal targets` block whose enum `ed` is admitted and satisfies `allSwitchCasesFitWidth ed.discrWidth targets.branches`:
   - Computes `allowed₀ := inhabitedDiscrSet ed.discrWidth ed.variants` (collecting truncated `BitVec 128` discriminants of all inhabited variants, uniformly pruning uninhabited `.single` variants as well).
   - Runs `pruneEnumBranches ed.discrWidth unreachBb allowed₀ targets.branches`: redirects any in-width branch whose `caseBits` is not in `remaining` (uninhabited, undeclared, or duplicate) to `unreachBb`, while leaving overflowing branch constants (`truncateBits discrW caseBits != caseBits`) untouched so `evalSwitchBranches` still faults `.unsupported` identically if reached.
   - Finalizes `targets'`:
     - `remaining = []` (every inhabited discriminant already matched in `branches₁`): sets `otherwise := unreachBb`.
     - `remaining = [lastDiscr]` (exactly one inhabited discriminant left for `otherwise`): appends `(lastDiscr, targets.otherwise)` to `branches₁` and sets `otherwise := unreachBb` (matching `rustc`'s `+21` arm increase observed on `zerocopy 0.8.64`).
     - `remaining` has `>= 2` discriminants: keeps `otherwise := targets.otherwise`.

#### 4.2 Pass B: `applyEnumScalarize`, Component Layout, and Straight-Line Gadgets

`applyEnumScalarize plan pSrc` eliminates a single internal `.adtEnum` local `plan.enumLocal` (`body.argumentCount < plan.enumLocal < body.locals.length`) in `pSrc.bodies[plan.defId]`:

1. **Static guards:** Checks `pSrc.enumDefs.all adtEnumDefAdmitted`, `enumStorageAnnotationsInBounds body`, `enumBodyLocalsInBounds body` (crucial guard `CE11` preventing any pre-existing out-of-bounds `LocalId >= base` from aliasing appended component locals), `enumBodyTargetsInBounds body` (preventing any pre-existing jump from aliasing appended `.niche` dispatch blocks `>= B`), `body.locals[plan.enumLocal] = some (.adtEnum eIdx)`, and per-block `checkStmtForEnumLocal` + `checkTermForEnumLocal`.
2. **Component local allocation (`scalarizedEnumComponentTys ed`, appended at `base := body.locals.length`):** Replaces `body.locals[plan.enumLocal]` with a dummy `.base .unit` slot and appends `compTys.map EnumLocalDecl.base`:

| Layout | Appended Component Locals Starting at `base := body.locals.length` |
| :--- | :--- |
| `.empty` | `base + 0`: `livenessLocal : .unit`, `base + 1`: `faultScratchU32 : .int .i32 false` |
| `.single` | `base + 0`: `livenessLocal`, `base + 1`: `faultScratchU32`, `base + 2 ..`: `vd₀.fields` (payload), followed by `vd₀.fields` (aggregate scratch) |
| `.direct tagW tagS` | `base + 0`: `livenessLocal`, `base + 1`: `faultScratchU32`, `base + 2`: `tagLocal : .enum (directTagEnumTy ed tagW tagS)`, followed by `flattenAllVariantFieldTys ed` (per-variant payload at `base + 3 + directVariantFieldOffset ed.variants v + f`), followed by `flattenAllVariantFieldTys ed` (aggregate scratch) |
| `.niche tagW ...` | `base + 0`: `livenessLocal`, `base + 1`: `faultScratchU32`, `base + 2`: `nicheLocal : .int tagW false`, `base + 3`: `scrDiff : .int tagW false`, `base + 4`: `scrGuard : .int tagW false`, `base + 5 ..`: `nicheExtraFieldTysAux nicheField 0 uVd.fields` (`extraFields` of `untagged`), followed by `flattenAllVariantFieldTys ed` (per-variant aggregate scratch, including ZST niche variants) |

3. **Three 0-block-split straight-line gadgets in unmodified `Trusted.MirAst`:**
   - **`mkLivenessCheckStmt liveLoc` (`1` statement):** `liveLoc = copy liveLoc` (`.unit`). When `liveLoc` is `.live (some .unit)`, steps as an exact state identity; when `liveLoc` is `.dead`, faults `.fault .undefined` (`DeadLocal`), enforcing liveness uniformly even on 0-field variants and `.empty` enums.
   - **`mkImmediateUbStmt faultScratch` (`1` statement):** `faultScratch = 0_u32 -_uchk 1_u32` (`.binaryOp .subUnchecked`). Deterministically underflows unsigned `u32` in unmodified `Trusted.MirSemantics.evalBinOp`, raising `.fault .undefined` on uninhabited-variant writes, empty-enum reads, and `UninhabitedEnumVariantRead`.
   - **`mkWrappingRangeCheckStmts tagW scrDiff scrGuard valOp r` (`2` statements, ZERO basic-block splits):**

```lean
noncomputable def mkWrappingRangeCheckStmts (tagW : IntWidth)
    (scratchDiff scratchGuard : LocalId) (valOp : Operand)
    (r : WrappingRange128) : List EnumStmt :=
  let startC : Operand :=
    .constant { ty := .int tagW false, lit := .scalar (truncateBits tagW r.start) }
  let spanBits := subTruncBits tagW r.end_ r.start
  let spanC : Operand :=
    .constant { ty := .int tagW false, lit := .scalar spanBits }
  let pDiff : Place := { localId := scratchDiff, projection := [] }
  let pGuard : Place := { localId := scratchGuard, projection := [] }
  [ .baseStmt (.assign pDiff (.binaryOp .sub valOp startC)),
    .baseStmt (.assign pGuard (.binaryOp .subUnchecked spanC (.move pDiff))) ]
```

   **Why this 2-statement gadget is exact for BOTH non-wrapping and wrap-around `WrappingRange128`:** For any `tagW`-bit unsigned integer $v$ and any `tagW`-fitting wrapping range $r = [s..=e]$ with modular span $\Delta = (e - s) \bmod 2^W$:
   $$v \in_{\text{wrap}} [s..=e] \iff ((v - s) \bmod 2^W) \le \Delta \iff \Delta -_{\text{uchk}} ((v - s) \bmod 2^W) \text{ does not underflow.}$$
   Statement 1 computes $d = (v - s) \bmod 2^W$ using wrapping `BinOp.sub` (also faulting `.fault .undefined` immediately if `valOp` is `Uninit` or `DeadLocal`). Statement 2 computes $\Delta -_{\text{uchk}} d$ using `BinOp.subUnchecked` (moving `scrDiff` so no stale scratch state leaks), succeeding iff $d \le \Delta$ and deterministically faulting `.fault .undefined` iff $d > \Delta$. This single 2-statement gadget handles **all** niche range checks in `assignField`, `readField`, `setDiscriminant(untagged)` write-order UB, `aggregateEnum`, and `switchDiscr` without splitting a single basic block mid-sequence.

4. **Statement lowering (`lowerEnumStmt`, `0` block splits):**
   - `StorageLive plan.enumLocal` / `StorageDead plan.enumLocal`: expands to `StorageLive`/`StorageDead` on `plan.enumLocal` plus all `compCount` appended locals `base .. base + compCount - 1`, preserving `enumHasStorageAnnotation` lockstep between `plan.enumLocal` and every appended component local.
   - `setDiscriminant plan.enumLocal v`: emits `mkLivenessCheckStmt` + (`mkImmediateUbStmt` if uninhabited; else no-op for `.single`, `tagLocal = const (.enumVal tagEty v)` for `.direct`, `mkWrappingRangeCheckStmts uRange` on `nicheLocal` for `.niche` `untagged`, or `nicheLocal = const tagBits` for `.niche` `v ∈ [nStart, nLast]`).
   - `assignField plan.enumLocal v f rval`: evaluates `rval` into a scratch local first (preserving operand-before-`DeadLocal` fault order), executes `mkLivenessCheckStmt`, checks `mkWrappingRangeCheckStmts uRange` if writing `.niche` `untagged.nicheField`, and moves the scratch local into the target payload local.
   - `readField dst plan.enumLocal v f isMove`: executes `mkLivenessCheckStmt`, checks `mkWrappingRangeCheckStmts uRange` when reading `.niche` `untagged.nicheField` (`CE7`), and copies/moves the target payload local into `dst` (or writes constant ZST for ZST niche fields).
   - `aggregateEnum plan.enumLocal v ops`: executes `mkEvalOpsToScratch` (emitting `StorageLive` + `assign` per operand left-to-right), then `mkLivenessCheckStmt`, then `mkImmediateUbStmt` if uninhabited, else moves evaluated scratch locals into payload locals (`mkMoveScratchToPayload` / `mkMoveScratchToNicheUntagged` with `uRange` check on `nicheField`) and writes the tag/niche constant.
   - `discriminantDirect dst plan.enumLocal`: executes `mkLivenessCheckStmt`, then `mkImmediateUbStmt` (`.empty` or uninhabited `.single`), `dst = const vd₀.discrVal` (inhabited `.single`), or `dst = .discriminant tagLocal` (`.direct`).

5. **Terminator lowering (`lowerEnumBlock`, preserving entry `BasicBlockId`s `0 .. B - 1`):**
   - Non-target terminators and `.switchDiscr` on `eLoc ≠ plan.enumLocal` are preserved verbatim after lowered statements.
   - `.switchDiscr discrDst plan.enumLocal targets`:
     - `.empty`: appends `[mkLivenessCheckStmt, mkImmediateUbStmt]` (`0` aux blocks).
     - `.single`: appends `[mkLivenessCheckStmt, mkImmediateUbStmt]` if uninhabited, else `[mkLivenessCheckStmt, discrDst = const vd₀.discrVal]` + `.switchInt (copy discrDst) targets` (`0` aux blocks).
     - `.direct`: appends `[mkLivenessCheckStmt, discrDst = .discriminant tagLocal]` + `.switchInt (copy discrDst) targets` (`0` aux blocks).
     - `.niche`: appends `[mkLivenessCheckStmt] ++ mkWrappingRangeCheckStmts tagRange (copy nicheLocal) ++ [scrDiff = sub (copy nicheLocal) nStartBits]` and terminates with `.switchInt (move scrDiff) { branches := arms.1, otherwise := auxBase + k }`, emitting `k + 1` trailing auxiliary dispatch blocks at `auxBase .. auxBase + k` (where `auxBase >= B`): for `0 <= i < k`, arm `auxBase + i` decodes niche variant `nStart + i` (`unreachable` if uninhabited, else assigns `discrDst = const vd.discrVal` and switches on `targets`); arm `auxBase + k` decodes `untagged` (`discrDst = const uVd.discrVal` + `.switchInt (copy discrDst) targets`). Because auxiliary blocks are strictly appended at indices `>= B`, every original block `0 .. B - 1` keeps its exact `BasicBlockId`.

6. **Elimination of `enumDefs` and `unembedBaseProgram`:** When `applyEnumScalarize` eliminates the *last* remaining `.adtEnum` local across all bodies (`!bodies'.any bodyHasAdtEnumDecl`), it clears `enumDefs := []`, making `unembedBaseProgram pFlat = some pOut` succeed and certifying `checkEnumScalarizeToTrustedMir trace pSrc pMir = true`.

---

### 5. Five Core Mechanized Theorems, Modular Proof Architecture, & Axiom Profile

`Basis: execution (Lean kernel, support/AnnealTrustedMirPayloadEnumsNicheTagSetDiscriminantAndScalarize.lean)`

#### 5.1 Verbatim Part III Theorem Statements (`VrustcFormal.F1_14`)

All five Part III theorem statements are locked byte-for-byte against frozen statement `SHA-256 3fcdb71f48be7fcfdb6d20ad6bd766ef8a15e99f98d7dc93003e09c6d6ee0a58` and proved with `0` `sorry` and `0` `Classical.choice`:

```lean
theorem enum_conservative_extension_exact
    (p : Program) :
    (∀ (c : Choice) (s : State),
      evalStepEnum (embedBaseProgram p) c (embedEnumState s) =
        liftStepResultEnum (evalStep p c s)) ∧
    (∀ q : Query,
      (WellFormedEnum (embedBaseProgram p) q ↔ WellFormed p q) ∧
      (∀ out : TerminalOut,
        BehaviorEnum (embedBaseProgram p) q out ↔ Behavior p q out) ∧
      (∀ k : FaultKind,
        ReachesResultEnum (embedBaseProgram p) q (.fault k) ↔
          ReachesResult p q (.fault k)) ∧
      (DivergesEnum (embedBaseProgram p) q ↔ Diverges p q) ∧
      (∀ post : TerminalOut → Prop,
        SatisfiesPostEnum (embedBaseProgram p) q post ↔
          SatisfiesPost p q post)) 

/-- **Theorem 2 (`wrappingNiche_partition_and_writeOrder_iff`):**
For any `ed : AdtEnumDef` with `adtEnumDefAdmitted ed = true` and niche layout
`ed.layout = .niche tagW untagged nStart nLast nStartBits tagRange nicheField uRange`:
1. **Exact Modular Partition:** For every `tagW`-bit scalar `bits`
   (`truncateBits tagW bits = bits`), `wrappingRangeContains tagRange bits = true`
   holds iff EITHER `Nat.ble (subTruncBits tagW bits nStartBits).toNat (nLast - nStart)`
   (a niche variant tag) OR `wrappingRangeContains uRange bits = true` (a valid
   `untagged` payload), and the two cases are mutually exclusive.
2. **Niche Tag Round-Trip:** For every inhabited niche variant `v` with
   `nStart ≤ v ≤ nLast`, `writeAdtDiscriminant ed v (.liveNiche b extras)` steps
   to `.ok sl'` whose `decodeNicheVariant` decodes back to `.ok v`.
3. **Exact `SetDiscriminant(untagged)` Write-Order UB Characterization:**
   `writeAdtDiscriminant ed untagged (.liveNiche nicheBits extras)` succeeds
   (is `.ok _`) iff `nicheBits = some bits` with `truncateBits tagW bits = bits`
   and `wrappingRangeContains uRange bits = true`; whenever `nicheBits = none`
   (`Uninit`) or `nicheBits = some bits` encodes any niche variant `v ∈ [nStart, nLast]`
   (or lies outside `tagRange` with `truncateBits tagW bits = bits`),
   `writeAdtDiscriminant` deterministically returns `.error .undefined`
   (`InvalidNichedEnumVariantWritten` / `InvalidUninitBytes`). -/
theorem wrappingNiche_partition_and_writeOrder_iff
    (ed : AdtEnumDef) (tagW : IntWidth)
    (untagged nStart nLast : Nat) (nStartBits : BitVec 128)
    (tagRange : WrappingRange128) (nicheField : Nat)
    (uRange : WrappingRange128)
    (hAdm : adtEnumDefAdmitted ed = true)
    (hLay : ed.layout = .niche tagW untagged nStart nLast nStartBits
      tagRange nicheField uRange) :
    (∀ bits : BitVec 128,
      truncateBits tagW bits = bits →
      ((wrappingRangeContains tagRange bits = true ↔
          (Nat.ble (subTruncBits tagW bits nStartBits).toNat (nLast - nStart) = true ∨
            wrappingRangeContains uRange bits = true)) ∧
       ¬ (Nat.ble (subTruncBits tagW bits nStartBits).toNat (nLast - nStart) = true ∧
            wrappingRangeContains uRange bits = true))) ∧
    (∀ (v : Nat) (vd : VariantDef) (b : Option (BitVec 128))
        (extras : List (Option Val)),
      nStart ≤ v → v ≤ nLast →
      Trusted.MirSemantics.getElem? ed.variants v = some vd →
      variantIsUninhabited vd = false →
      ∃ bits' : BitVec 128,
        writeAdtDiscriminant ed v (.liveNiche b extras) =
          .ok (.liveNiche (some bits') extras) ∧
        decodeNicheVariant ed tagW untagged nStart nLast nStartBits tagRange
          (some bits') = .ok v) ∧
    (∀ (nicheBits : Option (BitVec 128)) (extras : List (Option Val)),
      ((∃ sl' : EnumSlot,
          writeAdtDiscriminant ed untagged (.liveNiche nicheBits extras) = .ok sl') ↔
        (∃ bits : BitVec 128,
          nicheBits = some bits ∧
          truncateBits tagW bits = bits ∧
          wrappingRangeContains uRange bits = true)) ∧
      ((nicheBits = none ∨
        ∃ bits : BitVec 128,
          nicheBits = some bits ∧
          truncateBits tagW bits = bits ∧
          wrappingRangeContains uRange bits = false) →
        writeAdtDiscriminant ed untagged (.liveNiche nicheBits extras) =
          .error .undefined)) 

/-- **Theorem 3 (`unreachableEnumBranching_sound_bidirectional_iff`):**
Any transformation certified by `checkUnreachableEnumBranching bodyId pSrc pTgt = true`
preserves full bidirectional semantic equivalence `FullSemanticEquivEnum pSrc pTgt`. -/
theorem unreachableEnumBranching_sound_bidirectional_iff
    (bodyId : DefId) (pSrc pTgt : EnumProgram)
    (hCheck : checkUnreachableEnumBranching bodyId pSrc pTgt = true) :
    FullSemanticEquivEnum pSrc pTgt 

/-- **Theorem 4 (`enumScalarizeTrace_reduces_to_trusted_mir`):**
Any finite `EnumScalarizeTrace` certified by
`checkEnumScalarizeToTrustedMir trace pSrc pMir = true` produces an unmodified
`Trusted.MirAst.Program` (`pMir`) whose unmodified `Trusted.MirSemantics`
judgments (`WellFormed`, `Behavior`, `ReachesResult (.fault k)`, `Diverges`, and
`SatisfiesPost`) are bidirectionally equivalent (`↔`) to `M_enum` on `pSrc`. -/
theorem enumScalarizeTrace_reduces_to_trusted_mir
    (trace : EnumScalarizeTrace) (pSrc : EnumProgram) (pMir : Program)
    (hLower : checkEnumScalarizeToTrustedMir trace pSrc pMir = true) :
    (∀ q : Query, WellFormedEnum pSrc q ↔ WellFormed pMir q) ∧
    (∀ q : Query, ∀ out : TerminalOut,
      BehaviorEnum pSrc q out ↔ Behavior pMir q out) ∧
    (∀ q : Query, ∀ k : FaultKind,
      ReachesResultEnum pSrc q (.fault k) ↔
        ReachesResult pMir q (.fault k)) ∧
    (∀ q : Query, DivergesEnum pSrc q ↔ Diverges pMir q) ∧
    (∀ q : Query, ∀ post : TerminalOut → Prop,
      SatisfiesPostEnum pSrc q post ↔ SatisfiesPost pMir q post) 

/-- **Theorem 5 (`enumPipeline_then_optPipeline_vc_transport`):**
Vertical composition: `UnreachableEnumBranching` followed by `EnumScalarizeTrace`
into unmodified `Trusted.MirAst.Program` `pMir` followed by any certified
`Trusted.MirSemantics` optimization pipeline `FullSemanticEquivBase pMir pOpt`
transports `M_enum` verification conditions on `pSrc` bidirectionally (`↔`) onto
unmodified `Trusted.MirSemantics` on `pOpt`. -/
theorem enumPipeline_then_optPipeline_vc_transport
    (bodyId : DefId) (trace : EnumScalarizeTrace)
    (pSrc pBranched : EnumProgram) (pMir pOpt : Program)
    (hBranch : checkUnreachableEnumBranching bodyId pSrc pBranched = true)
    (hLower : checkEnumScalarizeToTrustedMir trace pBranched pMir = true)
    (hOpt : FullSemanticEquivBase pMir pOpt) :
    (∀ q : Query, WellFormedEnum pSrc q ↔ WellFormed pOpt q) ∧
    (∀ q : Query, ∀ out : TerminalOut,
      BehaviorEnum pSrc q out ↔ Behavior pOpt q out) ∧
    (∀ q : Query, ∀ k : FaultKind,
      ReachesResultEnum pSrc q (.fault k) ↔
        ReachesResult pOpt q (.fault k)) ∧
    (∀ q : Query, DivergesEnum pSrc q ↔ Diverges pOpt q) ∧
    (∀ q : Query, ∀ post : TerminalOut → Prop,
      SatisfiesPostEnum pSrc q post ↔ SatisfiesPost pOpt q post) 
```

#### 5.2 Modular 11-Slice Proof Architecture & Simulation Invariant (`ScalarizeSimRel`)

To keep kernel elaboration deterministic and Pass-1-pure under `-M4096 -DElab.async=false`, the proof was developed across `11` standalone `TrustedBoundary.lean`-preflighted slices (`19945` lines, `381` private helper declarations) and stitched into `support/AnnealTrustedMirPayloadEnumsNicheTagSetDiscriminantAndScalarize.lean` (`23485` total lines, `591` total declarations including Part I–IV, `0` duplicate declaration names, `byte_exact_reconstruction == true`):

| Slice Module | Lines | Decls | Proof Responsibility |
| :--- | :---: | :---: | :--- |
| `F1_14_Common.lean` | `1578` | `122` | Structural equality reflection (`programEq_eq`, `enumProgramEq_eq`, `mirTy_beq_eq`), `BitVec`/list helpers, constructive determinism (`divergesBase_iff_no_terminal_or_fault`, `wellFormedBase_iff_no_fault`), and `fullSemanticEquivEnum_of_fwd_stutter_sim` (`0` `Classical.choice`). |
| `Slice1_ConservativeExt.lean` | `747` | `27` | 1-step lockstep (`evalStepEnum_embedBaseProgram`), `initStateEnum_embedBaseProgram_clean`, `unembedBaseProgram_eq_embed`, and **Theorem 1** (`enum_conservative_extension_exact_slice1`). |
| `Slice2_NicheAndUnreachableBranching.lean` | `2656` | `68` | Modular `WrappingRange128` partition arithmetic, niche tag round-trip, `SetDiscriminant(untagged)` write-order UB (**Theorem 2**: `wrappingNiche_partition_and_writeOrder_iff_slice2`), and `UnreachableEnumBranching` soundness (**Theorem 3**: `unreachableEnumBranching_sound_bidirectional_iff_slice2`). |
| `Slice3a_ScalarizeGadgets.lean` | `712` | `24` | Straight-line gadget execution lemmas (`eval_mkLivenessCheckStmt_{live,dead}`, `eval_mkImmediateUbStmt`, `evalBinOp_unsigned_sub_eq`, `exec_mkWrappingRangeCheckStmts_copy`, `exec_mkWrappingRangeCheckStmts_move`). |
| `Slice3b_ScalarizeMultiStep.lean` | `2593` | `28` | Base-prefix agreement (`evalEnumPrimitiveOperand_agree`, `evalEnumBaseRvalue_agree`, `writeEnumBasePlace_agree`), multi-step `mkStorageLiveRange`/`mkStorageDeadRange`/`mkEvalOpsToScratch`/`mkMoveScratchToPayload`/`mkMoveScratchToNicheUntagged`, and `.niche` dispatch arm lemmas (`buildNicheDispatchArms_evalSwitch`, `buildNicheDispatchArms_block_lookup`). |
| `Slice3c_ScalarizeInitAndInvariant.lean` | `2753` | `47` | `ScalarizeCtx`, `applyEnumScalarize_unpack`, `PrefixSlotsAgree`, `SlotMatchesComp`, `ScalarizeStateRel`, `scalarize_initStateEnum_simRel`, and `directTagEnumTy_readDiscr`. |
| `Slice3d1_ScalarizeHelpersAndBaseSim.lean` | `3127` | `40` | `DirectTagInhabitedInv`, `ScalarizeSimRel`, `SimStepResult`, `s3d_offTarget_step_sim`, `s3d_baseStmt_sim`, `s3d_nonEnumLocal_stmt_sim`, and `s3d_discriminantDirect_enumLocal_sim`. |
| `Slice3d2a_SetDiscrAndAssignField.lean` | `1900` | `7` | Forward `1`-to-`1+` simulation for `EnumStmt.setDiscriminant` (`s3d2_setDiscriminant_enumLocal_sim`) and `EnumStmt.assignField` (`s3d2_assignField_enumLocal_sim`) across `.empty`, `.single`, `.direct`, and `.niche`. |
| `Slice3d2b_ReadFieldAndAggregate.lean` | `2413` | `8` | Forward `1`-to-`1+` simulation for `EnumStmt.readField` (`s3d2b_readField_enumLocal_sim`) and two-phase `EnumStmt.aggregateEnum` (`s3d2b_aggregateEnum_enumLocal_sim`) across all four layouts. |
| `Slice3d2c_TerminatorAndSound.lean` | `1347` | `7` | Terminator simulation (`s3d2c_terminator_sim` covering `.baseTerm`, off-target `.switchDiscr`, and target `.switchDiscr` across `.empty`/`.single`/`.direct`/`.niche`), `scalarize_step_sim`, and single-step `applyEnumScalarize_sound`. |
| `Slice4_TraceAndPipeline.lean` | `119` | `3` | Finite trace induction (`applyEnumScalarizeTrace_sound`), **Theorem 4** (`enumScalarizeTrace_reduces_to_trusted_mir_slice4`), and **Theorem 5** (`enumPipeline_then_optPipeline_vc_transport_slice4`). |

Central to the soundness of `EnumScalarize` (`Slice3c`–`Slice3d2c`) is the simulation relation `ScalarizeSimRel ctx s₁ s₂ := ScalarizeStateRel ctx s₁ s₂ ∧ DirectTagInhabitedInv ctx s₁`:

- **`ScalarizeStateRel`:** Relates off-target frames by exact equality (`f₂ = f₁`) and target-body frames (`f₁.defId = plan.defId`) by: (i) identical `blockIdx` (`f₂.blockIdx = f₁.blockIdx`), (ii) statement index mapping `f₂.stmtIdx = (listFlatMap lowerFn (bb.statements.take f₁.stmtIdx)).length` (`f₁.stmtIdx <= bb.statements.length`), (iii) `PrefixSlotsAgree base plan.enumLocal f₁.locals f₂.locals` (every local `j < base` with `j ≠ plan.enumLocal` is identical in `f₁` and `f₂`), and (iv) `SlotMatchesComp ctx.ed base ctx.compTys sl f₂.locals` (relating `f₁.locals[plan.enumLocal] = some sl` to the flat component locals `base + 0 .. base + compTys.length - 1` in `f₂.locals`, including liveness sync on `base + 0`, live fault/range scratch slots, exact `.direct` tag-local correspondence with `directTagEnumTy`, and exact `.niche` shared-carrier + `extraFields` correspondence).
- **`DirectTagInhabitedInv`:** Establishes that for any reachable `.liveDirect (some v) vfs` slot, `variants[v]` is inhabited (`variantIsUninhabited vd = false`), ensuring that `directTagEnumTy_readDiscr` (which reads `Trusted.MirAst.MirTy.enum` without consulting `variantIsUninhabited`) agrees 1-for-1 with `readAdtDiscriminant`.
- **Constructive `0`-`Classical.choice` stuttering bisimulation (`fullSemanticEquivEnum_of_fwd_stutter_sim`):** Because `evalStepEnum` is deterministic (`ValidChoiceEnum p s c ↔ c = 0`), any forward `1`-to-`1+` stuttering simulation on `evalStepEnum pSrc 0 s₁` (producing either immediate/multi-step matching `.done out`, immediate/multi-step matching `.fault k`, or a `>= 1`-step reachability chain `ReachesPlusEnum pOut s₂ s₂'` restoring `ScalarizeSimRel`) yields **bidirectional (`↔`)** equivalence across `WellFormedEnum`, `BehaviorEnum`, `ReachesResultEnum (.fault k)`, `DivergesEnum` (constructive bounded-fuel `stepChainFromEnum`), and `SatisfiesPostEnum` without invoking `Classical.choice`.

#### 5.3 Complete Public Theorem Inventory & Axiom Profile (`26` Theorems)

Every single one of the `26` public theorems depends exclusively on `["propext", "Quot.sound"]` (`22 / 26` strictly `[propext]`, `4 / 26` `[propext, Quot.sound]`, `0` `Classical.choice`, `0` `sorryAx`, `0` `_unsafe_rec`; `Quot.sound` enters only via `funext` on `List.map`/`List.all`/`List.any` congruence in `Slice1` and `Slice2`):

| # | Public Theorem | Lean 4 Kernel Axioms | Role |
| :---: | :--- | :--- | :--- |
| `1` | `VrustcFormal.F1_14.enum_conservative_extension_exact` | `[propext, Quot.sound]` | Part III Core Theorem 1 |
| `2` | `VrustcFormal.F1_14.wrappingNiche_partition_and_writeOrder_iff` | `[propext]` | Part III Core Theorem 2 |
| `3` | `VrustcFormal.F1_14.unreachableEnumBranching_sound_bidirectional_iff` | `[propext, Quot.sound]` | Part III Core Theorem 3 |
| `4` | `VrustcFormal.F1_14.enumScalarizeTrace_reduces_to_trusted_mir` | `[propext, Quot.sound]` | Part III Core Theorem 4 |
| `5` | `VrustcFormal.F1_14.enumPipeline_then_optPipeline_vc_transport` | `[propext, Quot.sound]` | Part III Core Theorem 5 |
| `6` | `VrustcFormal.F1_14.reachesEnum_head` | `[propext]` | Part IV Bounded-Fuel Adequacy / Determinism Lemma |
| `7` | `VrustcFormal.F1_14.reachesEnum_head_det` | `[propext]` | Part IV Bounded-Fuel Adequacy / Determinism Lemma |
| `8` | `VrustcFormal.F1_14.execFuelEnum_sound` | `[propext]` | Part IV Bounded-Fuel Adequacy / Determinism Lemma |
| `9` | `VrustcFormal.F1_14.execEnum_sound` | `[propext]` | Part IV Bounded-Fuel Adequacy / Determinism Lemma |
| `10` | `VrustcFormal.F1_14.execFuelEnum_done_det` | `[propext]` | Part IV Bounded-Fuel Adequacy / Determinism Lemma |
| `11` | `VrustcFormal.F1_14.positiveCanaryEnum_of_exec` | `[propext]` | Part IV Bounded-Fuel Adequacy / Determinism Lemma |
| `12` | `VrustcFormal.F1_14.negativeCanaryEnum_of_exec` | `[propext]` | Part IV Bounded-Fuel Adequacy / Determinism Lemma |
| `13` | `VrustcFormal.F1_14.reachesBase_head` | `[propext]` | Part IV Bounded-Fuel Adequacy / Determinism Lemma |
| `14` | `VrustcFormal.F1_14.execFuelBase_sound` | `[propext]` | Part IV Bounded-Fuel Adequacy / Determinism Lemma |
| `15` | `VrustcFormal.F1_14.execBase_sound` | `[propext]` | Part IV Bounded-Fuel Adequacy / Determinism Lemma |
| `16` | `VrustcFormal.F1_14.ce1_niche_set_discriminant_write_order_ub_vs_valid` | `[propext]` | Part IV Sharpness Counterexample / Lowering Witness |
| `17` | `VrustcFormal.F1_14.ce2_stale_niche_overwrite_faults_in_enum_and_trusted_mir` | `[propext]` | Part IV Sharpness Counterexample / Lowering Witness |
| `18` | `VrustcFormal.F1_14.ce3_wrapping_niche_accepts_254_and_rejects_100` | `[propext]` | Part IV Sharpness Counterexample / Lowering Witness |
| `19` | `VrustcFormal.F1_14.ce4_uninhabited_write_and_empty_read_fault_ub` | `[propext]` | Part IV Sharpness Counterexample / Lowering Witness |
| `20` | `VrustcFormal.F1_14.ce5_unreachable_enum_branching_prunes_err_never` | `[propext]` | Part IV Sharpness Counterexample / Lowering Witness |
| `21` | `VrustcFormal.F1_14.ce6_middle_untagged_variant_in_niche_range_rejected` | `[propext]` | Part IV Sharpness Counterexample / Lowering Witness |
| `22` | `VrustcFormal.F1_14.ce7_downcast_read_some_on_none_faults_ub` | `[propext]` | Part IV Sharpness Counterexample / Lowering Witness |
| `23` | `VrustcFormal.F1_14.ce8_dead_enum_aggregate_ub_and_self_read_rejected` | `[propext]` | Part IV Sharpness Counterexample / Lowering Witness |
| `24` | `VrustcFormal.F1_14.ce9_storage_dead_live_resets_enum_to_uninit` | `[propext]` | Part IV Sharpness Counterexample / Lowering Witness |
| `25` | `VrustcFormal.F1_14.ce10_end_to_end_pipeline_executes_in_unmodified_trusted_mir` | `[propext]` | Part IV Sharpness Counterexample / Lowering Witness |
| `26` | `VrustcFormal.F1_14.ce11_stage2_guards_oob_local_zst_niche_and_uncovered_variant` | `[propext]` | Part IV Sharpness Counterexample / Lowering Witness |

---

### 6. Eleven Sharpness Counterexamples (`CE1`–`CE11`) & End-to-End `Trusted.MirSemantics` Witness

`Basis: execution (Lean kernel, support/AnnealTrustedMirPayloadEnumsNicheTagSetDiscriminantAndScalarize.lean)`

Part IV (`0` `sorry`, verified verbatim against the frozen statement file) provides deterministic bounded-fuel adequacy (`execFuelEnum_sound`, `positiveCanaryEnum_of_exec`, `negativeCanaryEnum_of_exec`, `execFuelBase_sound`) and eleven executable kernel-checked sharpness theorems ruling out vacuous specifications, dropped UB checks, and missing static guards:

| Witness Theorem | Concrete Program / Descriptor | Exact Kernel-Checked Property |
| :--- | :--- | :--- |
| `ce1_niche_set_discriminant_write_order_ub_vs_valid` | `Option<NonZeroU32>` (`optNonZeroU32Def`) | `SetDiscriminant(_1, 1)` *before* `(_1 as Some).0 = 42` reaches `.fault .undefined` (`InvalidNichedEnumVariantWritten`), whereas writing `(_1 as Some).0 = 42` first and `SetDiscriminant(_1, 1)` second is `WellFormedEnum` and returns `42_u32`. |
| `ce2_stale_niche_overwrite_faults_in_enum_and_trusted_mir` | `Option<NonZeroU32>` lowered via `[⟨0, 1⟩]` | Writing `Some(42)`, switching to `None` (`SetDiscriminant(_1, 0)` overwriting the shared niche carrier to `0`), then calling `SetDiscriminant(_1, 1)` faults `.fault .undefined` BOTH in `M_enum` AND after `checkEnumScalarizeToTrustedMir` in unmodified `Trusted.MirSemantics` (`progCe2LoweredMir`). |
| `ce3_wrapping_niche_accepts_254_and_rejects_100` | `Option<HighU8>` (`tagRange = [254..=0]`, `uRange = [254..=255]`) | `adtEnumDefAdmitted optWrappingHighU8Def = true`; writing `254_u8` + `SetDiscriminant(1)` + `switchDiscr` returns `254_u8`, while writing out-of-range `100_u8` faults `.fault .undefined`. |
| `ce4_uninhabited_write_and_empty_read_fault_ub` | `Result<u32, !>` & `enum Void {}` | `SetDiscriminant(_1, 1)` (`Err(!)`) on `Result<u32, !>` and `discriminantDirect` on `Void` both fault `.fault .undefined`. |
| `ce5_unreachable_enum_branching_prunes_err_never` | `Result<u32, !>` with `Err(1) -> bb2, otherwise -> bb1` | `checkUnreachableEnumBranching 0 progCe5ResultSrc progCe5ResultBranched = true`; redirects `Err(1)` to `unreachBb = 3`, promotes `Ok(0) -> bb1`, sets `otherwise = 3`, and preserves return value `77_u32`. |
| `ce6_middle_untagged_variant_in_niche_range_rejected` | `badMiddleUntaggedDef` (`untagged = 1`, `nStart = 0`, `nLast = 2`) | `adtEnumDefAdmitted badMiddleUntaggedDef = false` (matches `E3-17` `SZ_MIDDLE = 2` non-niche layout). |
| `ce7_downcast_read_some_on_none_faults_ub` | `Option<NonZeroU32>` set to `None`, then `readField 0 1 1 0 false` | Reading `(_1 as Some).0` when the niche holds `0` (`None`) faults `.fault .undefined` and `¬ WellFormedEnum`. |
| `ce8_dead_enum_aggregate_ub_and_self_read_rejected` | `progCe8DeadAggregate` & `progCe8SelfReadField` | `AggregateEnum` into a storage-annotated dead enum local faults `.fault .undefined` (`DeadLocal`), and self-aliasing `readField 1 1 ...` fails closed to `.fault .unsupported`. |
| `ce9_storage_dead_live_resets_enum_to_uninit` | `progCe9StorageReset` | `StorageLive 1; AggregateEnum 1 1 [9]; StorageDead 1; StorageLive 1; switchDiscr` resets the niche carrier to `Uninit` (`none`), causing `switchDiscr` to fault `.fault .undefined`. |
| `ce10_end_to_end_pipeline_executes_in_unmodified_trusted_mir` | `Option<NonZeroU32>` + `Result<u32, !>` (`witness::opt_nonzero_and_result_never`) | Certifies `checkUnreachableEnumBranching` AND 2-step `checkEnumScalarizeToTrustedMir [⟨0, 2⟩, ⟨0, 3⟩]` into unmodified `Trusted.MirAst.Program` (`progCe10TrustedMir`), then executes unmodified `Trusted.MirSemantics.evalStep` to return `99_u32` on `x = 0` (`None`) and `42_u32` on `x = 42` (`Some(42)`). |
| `ce11_stage2_guards_oob_local_zst_niche_and_uncovered_variant` | `progCe11OobLocal`, `optUnitNonZeroU32Def`, `badUncoveredInhabitedNicheDef` | Verifies (1) out-of-bounds `LocalId` (`_2` when `locals.length = 2`) is rejected by `applyEnumScalarize = none`; (2) `.unit`-payload niche variant `None(())` lowers cleanly via `checkEnumScalarizeToTrustedMir` and returns `.unit` in unmodified `Trusted.MirSemantics`; (3) extra uncovered inhabited variant outside `{untagged} ∪ [nStart, nLast]` is rejected by `adtEnumDefAdmitted = false`. |

#### 6.1 End-to-End Walkthrough of `CE10` (`witness::opt_nonzero_and_result_never`)

`progCe10EndToEndSrc` demonstrates the complete multi-enum vertical pipeline in action on a single 9-block (`bb0`–`bb8`) function taking `x : u32` (`_1`) and manipulating two simultaneous internal `.adtEnum` locals (`_2 : Option<NonZeroU32>`, `.niche .i32`; `_3 : Result<u32, !>`, `.direct .i8`):

1. `bb0` branches on `x == 0`: if `0`, `bb1` sets `_2` to `None` via `setDiscriminant 2 0`; else `bb2` constructs `Some(x)` via deaggregated `assignField 2 1 0 (copy _1)` followed by `setDiscriminant 2 1` (exercising write-order validity).
2. `bb3` executes `switchDiscr 4 2` on the niche enum `_2`: `None` (`0`) jumps to `bb4` (`_3 = Ok(99)` via `aggregateEnum 3 0 [99]`); `Some` jumps to `bb5` (`_6 = move (_2 as Some).0`; `_3 = Ok(move _6)`).
3. `bb6` executes `switchDiscr 5 3` on `Result<u32, !>` with dead `Err(1) -> bb8` and `otherwise -> bb7` (`_0 = move (_3 as Ok).0; return`).
4. **Pass A (`applyUnreachableEnumBranching`):** Appends `bb9 := unreachable`, redirects `Err(1)` in `bb6` from `bb8` to `bb9`, promotes `Ok(0) -> bb7`, and rewrites `otherwise` to `bb9`.
5. **Pass B (`applyEnumScalarizeTrace [⟨0, 2⟩, ⟨0, 3⟩]`):** First scalarizes `_2` (`Option<NonZeroU32>`) into `livenessLocal`, `faultScratchU32`, `nicheLocal`, `scrDiff`, `scrGuard`, and scratch locals plus 2 trailing dispatch blocks for `bb3`; second scalarizes `_3` (`Result<u32, !>`) into `livenessLocal`, `faultScratchU32`, `tagLocal : .enum (directTagEnumTy ...)`, payload locals, and scratch locals, clearing `enumDefs := []` so `unembedBaseProgram` yields an unmodified `Trusted.MirAst.Program` (`progCe10TrustedMir`).
6. **Execution in unmodified `Trusted.MirSemantics.evalStep`:** `ce10_end_to_end_pipeline_executes_in_unmodified_trusted_mir` kernel-checks that `progCe10TrustedMir` evaluates `queryU32 0` to `99_u32` and `queryU32 42` to `42_u32`, while Theorem 5 (`enumPipeline_then_optPipeline_vc_transport`) universally lifts those and every other `u32` input (`0 .. 2^32 - 1`) bidirectionally back to `progCe10EndToEndSrc`.

---

### 7. Six-Gate Multi-Kernel & `TrustedBoundary.lean` Pass 1 Verification Results

`Basis: execution (support/multi_kernel_verification_summary.json)`

The stitched single-file proof `support/AnnealTrustedMirPayloadEnumsNicheTagSetDiscriminantAndScalarize.lean` (`23485` lines, `1157255` bytes, `0` CRLF bytes, `0` disallowed Unicode/bidi control characters, byte-exact reconstruction against frozen statement SHA-256 `3fcdb71f48be7fcfdb6d20ad6bd766ef8a15e99f98d7dc93003e09c6d6ee0a58`) passed all six verification gates:

| Gate | Checker / Tool | Configuration / Flags | Result | Wall Time | Peak RSS | Key Metrics |
| :---: | :--- | :--- | :---: | :---: | :---: | :--- |
| **1** | `Lean v4.34.1` (`5045d005`) | `-M4096 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` | `rc = 0` | `105.2149 s` | `1447.99 MB` | `0` errors, `0` warnings, `.olean` `39726952` B |
| **2** | `#print axioms` + `env.constants.map₁` audit | All `26` public theorems + full constant table inspection | `rc = 0` | `6.9069 s` | `1623.73 MB` | `22 / 26` strictly `[propext]`, `4 / 26` `[propext, Quot.sound]`, `0` `Classical.choice`; `total=2086`, `pub=868`, `priv=1218`, `bad=0` |
| **3a** | `TrustedBoundary.lean` `"preflight"` (pos) | Unmodified `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` | `rc = 0` | `14.4578 s` | `793.75 MB` | `ok = true` on `Anneal.F1_14_Proof` |
| **3b** | `TrustedBoundary.lean` `"preflight"` (neg) | Frozen statement file containing Part III `sorry`s | `rc = 1` | `11.075 s` | — | Rejected fail-closed: `policy:unsupported syntax kind Lean.Parser.Tactic.tacticSorry` |
| **3c** | `TrustedBoundary.lean` Pass 1 `"audit"` | `axioms: [["Quot.sound", "Init.Prelude"], ["propext", "Init.Core"]]` (`0` `Classical.choice`) | `rc = 0` | `22.1136 s` | `916.11 MB` | `ok = true`, `replay = true`, `kernelDeclarations = 1324`, `replayedDeclarations = 3667`, `reachableDeclarations = 4553`, `checkedAlternateProofs = 0`, `compilerOnlyNames = 281`, `axioms = ["propext", "Quot.sound"]` |
| **4** | `Lean v4.35.0` (`eb6cafb7`) | `-M4096 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` | `rc = 0` | `109.7549 s` | `1396.66 MB` | Cross-version kernel check clean (`0` warnings) |
| **5** | `lean4export 3.1.0` (`5a9a355d`) | Exporting all `26` `VrustcFormal.F1_14.*` public theorems | `rc = 0` | `8.2481 s` | — | `1111816` NDJSON lines (`58632267` B) |
| **6a** | `nanoda_bin 0.4.19` (`f55114af`) (pos) | `permitted_axioms: ["propext", "Quot.sound"]`, `unpermitted_axiom_hard_error: true` | `rc = 0` | `6.5171 s` | `119.0 MB` | `Checked 3096 declarations with no typechecker errors` |
| **6b** | `nanoda_bin 0.4.19` (`f55114af`) (neg) | `permitted_axioms: []`, `unpermitted_axiom_hard_error: true` | `rc = 1` | `0.0233 s` | — | Rejected fail-closed: `export file declares unpermitted axiom "propext"` |

## Boundaries

Every theorem in `VrustcFormal.F1_14` is exact within the explicitly delimited fragment below; constructs outside these eight boundaries fail closed (`.error .unsupported`, `.fault .unsupported`, `adtEnumDefAdmitted = false`, or `applyEnumScalarize = none`) rather than approximating semantics:

1. **B1 — Internal non-address-taken `.adtEnum` locals & base-typed signature slots.** `isSupportedEnumLocalDecl` restricts signature slots `0 .. body.argumentCount` (return place `_0` and parameters `_1 .. _argumentCount`) to `.base ty` (`isSupportedScalarOrUnitTy`) so `Query` and `TerminalOut` match unmodified `Trusted.MirSemantics` identically. Internal locals `idx > body.argumentCount` may hold admitted `.adtEnum eIdx` values, and `checkStmtForEnumLocal` / `checkTermForEnumLocal` forbid taking references or raw pointers (`Rvalue.ref`, `Rvalue.addressOf`) to scalarized enum locals or referencing them via base-statement `ProjectionElem` projections. Address-taken enums and enum-valued function signatures require either in-memory byte-layout modeling or ABI-level wrapper scalarization across call boundaries.
2. **B2 — Structured variant-slot model (`EnumSlot`) vs. byte-level variant overlap & `Aggregate` padding reset.** `M_enum` models `.direct` variant payloads as disjoint per-variant field arrays `variantFields : List (List (Option Val))` and `.niche` enums as a shared `nicheBits : Option (BitVec 128)` carrier plus `extraFields` for `untaggedVariant` (since niche-tagged variants carry exclusively ZST fields). It does not model raw byte-level union overlap between distinct `.direct` variants' payload bytes, transmuting or reading raw padding bytes, or `Rvalue::Aggregate` deinitializing unmentioned padding/inactive variant bytes beyond `StorageDead` + `StorageLive` resets.
3. **B3 — Depth-1 scalar, unit, and fieldless-enum variant payloads.** `adtEnumDefAdmitted` requires every field of every variant (`vd.fields`) to satisfy `Trusted.MirSemantics.isSupportedScalarOrUnitTy` (booleans, fixed-width/pointer-width integers, `.unit`, and admitted fieldless `.enum`, plus `.never` solely for marking uninhabited variants via `variantIsUninhabited`). Nested payload-bearing enums (such as `Result<T, ConvertError<A, S, V>>` before inner-enum flattening), multi-field struct/tuple fields (such as `layout::SizeInfo` containing `TrailingSliceLayout`), arrays, slices, and reference/pointer fields are not directly representable in `VariantDef.fields` without prior structural flattening or a richer `MirAst` profile.
4. **B4 — Single unsigned-integer niche carrier (`1 <= k <= 64`, `untaggedVariant ∉ [nStart, nLast]`), excluding pointer/reference niches.** `adtEnumDefAdmitted` restricts `.niche` layouts to a single unsigned integer carrier `.int tagW false` at `untaggedVariant.fields[nicheFieldIdx]`, at most `64` contiguous niche variants (`1 <= k <= 64`, `k < 2^tagW`), `untaggedVariant` strictly outside `[nStart, nLast]`, and all niche variants carrying exclusively inhabited ZST fields (`isZstBaseTy`). Consequently, pointer- and reference-carried niche enums that appear frequently in `zerocopy`'s downstream instantiations—such as `Option<NonNull<T>>`, `Option<&T>`, `Option<Ptr<'_, T, ...>>`, `Option<PtrInner<'_, [u8]>>`, and `Result<&u32, ConvertError<...>>`—as well as signed integer niches (`Option<Ordering>` when represented as signed `i8`), `bool`-carrier niches (`Option<bool>` without re-encoding `bool` as unsigned `u8` with `uRange = [0..=1]`), and multi-niche layouts are outside `.niche` admission until pointer provenance / non-null validity is modeled in `Trusted.MirSemantics`.
5. **B5 — Fused `EnumTerminator.switchDiscr` & standalone `.niche` `Rvalue::Discriminant` rejection.** While `.empty`, `.single`, and `.direct` enums support both standalone `EnumStmt.discriminantDirect dst src` and fused `EnumTerminator.switchDiscr dst src targets`, `.niche` enums intentionally fail closed (`.fault .unsupported` in `evalEnumStmt`, rejected by `checkStmtForEnumLocal`) on standalone `discriminantDirect` and must dispatch through fused `EnumTerminator.switchDiscr`. This reflects the MIR lowering geometry: scalarizing a `.niche` discriminant into a detached scalar local without an immediately following `switchInt` requires splitting the enclosing basic block mid-sequence, whereas lowering fused `switchDiscr` appends trailing 2-statement dispatch arms `buildNicheDispatchArms` at indices `>= B` with zero mid-block splits.
6. **B6 — Intra-procedural, non-unwinding, 64-bit `mirProfileVersion = 1` fragment.** Inheriting unmodified `Trusted.MirSemantics`, `M_enum` enforces `pointerWidthBits == 64`, `mirProfileVersion == 1`, `callerMem.allocations.isEmpty`, and fails closed (`.fault .unsupported`) on `.call`, `.assert`, `.unwindResume`, and `.return_` in `bb.cleanup = true`. Multi-function call stacks, panic/unwind cleanup pads, and inlining compose vertically with `VrustcFormal.F1_14` only when lowered into the base fragment (as proved by `enumPipeline_then_optPipeline_vc_transport` for downstream `FullSemanticEquivBase` pipelines).
7. **B7 — Conservative field-move deinitialization, self-aliasing rejection, & `AggregateEnum` fault ordering.** Moving a non-ZST payload field via `readField dst src v f true` immediately resets that field (or `nicheBits` for `untagged.nicheField`) to `initFieldOptVal fTy` (`none`), matching `Trusted.MirSemantics` local-move deinitialization. `evalEnumStmt` explicitly rejects self-aliasing (`rvalueMentionsLocal localId rval` in `assignField`, `dstLocal == srcLocal` in `readField`, and `ops.any (stmtMentionsLocalOperand dstLocal)` in `aggregateEnum`) as `.fault .unsupported`. In `aggregateEnum`, operand list `ops` is evaluated left-to-right *before* destination `DeadLocal` and uninhabited-variant checks, matching the lowered `mkEvalOpsToScratch` -> `mkLivenessCheckStmt` -> `mkImmediateUbStmt` execution order exactly.
8. **B8 — Monomorphic `UnreachableEnumBranching` & uniform uninhabited-`Single` tightening.** `applyUnreachableEnumBranching` operates on concrete, monomorphic `AdtEnumDef` descriptors (without generic `ParamEnv` layout queries, so polymorphic `Result<Self, ConvertError<..., !>>` bodies must be monomorphized or have their concrete `AdtEnumDef` instantiated before applying Pass A). Additionally, `inhabitedDiscrSet` uniformly prunes uninhabited variants across `.empty`, `.single`, and `.multiple` layouts (tightening `rustc`'s `unreachable_enum_branching.rs:52-78` uniformly to uninhabited `.single` enums as well) and explicitly guards `enumBodyTargetsInBounds` + empty `trapBb.statements` so `enumHasStorageAnnotation` can never flip.

## Evidence

- `support/AnnealTrustedMirPayloadEnumsNicheTagSetDiscriminantAndScalarize.lean` — `23485`-line (`1157255` bytes) zero-`sorry` Lean 4 proof module (`SHA-256 c8569e4b0199ea5a7da011018b1c70803e9b389f24c92ee9b2864acda1827755`), byte-for-byte faithful to frozen theorem-statement `SHA-256 3fcdb71f48be7fcfdb6d20ad6bd766ef8a15e99f98d7dc93003e09c6d6ee0a58` with `0` non-private inserted declarations and `0` `Classical.choice`.
- `support/AnnealTrustedMirPayloadEnumsNicheTagSetDiscriminantAndScalarize.frozen.sha256` — SHA-256 digests locking the frozen statement specification and stitched completed proof module.
- `support/multi_kernel_verification_summary.json` (`SHA-256 2873013bd123f5b26c1779108c07a8e047e2e1191a41b3b4b520986f8b07169a`) — Complete 6-gate multi-kernel verification receipts (`Lean v4.34.1` `-M4096`, `#print axioms` + `AUDIT_MAP1`, `TrustedBoundary.lean` `"preflight"` pos/neg + Pass 1 `"audit"` with `0` `Classical.choice`, `Lean v4.35.0`, `lean4export 3.1.0`, and `nanoda_bin 0.4.19` pos/neg).
- `support/zerocopy_payload_niche_enums_and_unreachable_branching_census.json` (`SHA-256 91be62313c1341d2e7f3d3f07f56d823214c0ce7d927fd1821e08bef62a5f5a9`) — Live `rustc 1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`) payload/niche enum layout (`-Zprint-type-sizes`), `Runtime(PostCleanup)` / `Runtime(Optimized)` MIR enum operation, and `UnreachableEnumBranching` before/after diff census across `google/zerocopy@d3362d9a657e2f943d25a0812f7b13b93e60af4d` (`0.8.64`).

## Revalidation

1. **Synchronous `Lean v4.34.1` & Unmodified `TrustedBoundary.lean` Pass 1 Audit (`-M4096`):**
   Check out `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, compile `Trusted/MirAst.lean`, `Trusted/MirSemantics.lean`, `Trusted.lean`, and `theory/Anneal/MirWp.lean` with `Lean v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`), then compile `support/AnnealTrustedMirPayloadEnumsNicheTagSetDiscriminantAndScalarize.lean` with:
   `lean -M4096 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` (`rc = 0`, `0` warnings).
   Run `#print axioms` over all `26` public `VrustcFormal.F1_14.*` theorems (`22 / 26` strictly `[propext]`, `4 / 26` `[propext, Quot.sound]`, `0` `Classical.choice`, `AUDIT_MAP1 bad = 0`) and run `trusted/audit/TrustedBoundary.lean` in `"preflight"` mode (verifying `ok = true` on `support/AnnealTrustedMirPayloadEnumsNicheTagSetDiscriminantAndScalarize.lean` and `rc = 1` rejection on the frozen `sorry` statement) and `"audit"` mode with `axioms = [["Quot.sound", "Init.Prelude"], ["propext", "Init.Core"]]` (`rc = 0`, `ok = true`, `replay = true`).
2. **Cross-Version `Lean v4.35.0` & External Rust Kernel Replay (`nanoda_bin 0.4.19`):**
   Compile `Trusted/MirAst.lean`, `Trusted/MirSemantics.lean`, and `support/AnnealTrustedMirPayloadEnumsNicheTagSetDiscriminantAndScalarize.lean` on `Lean v4.35.0` (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`) with `-M4096 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` (`rc = 0`), export all `26` public `VrustcFormal.F1_14.*` theorems via `leanexport` (`leanprover/lean4export@5a9a355dc6c5fd82b69058d433e2ae2e8dfbf8fe`, `3.1.0`), and check the resulting NDJSON export with `nanoda_bin` (`ammkrn/nanoda_lib@f55114afa24efe39e007f62d31b7e8ac4243f2a6`, `0.4.19`) under `permitted_axioms: ["propext", "Quot.sound"]` (`rc = 0`, `3096` declarations checked) and `permitted_axioms: []` (`rc = 1`, rejecting `"propext"`).
3. **First-Customer `zerocopy` MIR Census Revalidation:**
   Check out `google/zerocopy@d3362d9a657e2f943d25a0812f7b13b93e60af4d` (`0.8.64`) and compile `src/lib.rs` with `rustc 1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`) using `--edition=2021 --crate-name zerocopy --crate-type lib --cfg feature="alloc" --cfg feature="std" --cfg feature="simd" --cfg feature="simd-nightly" --cfg feature="float-nightly" -Zdump-mir="analysis-post-cleanup | UnreachableEnumBranching | runtime-optimized" -Zprint-type-sizes` to reproduce the layout, MIR operation, and `UnreachableEnumBranching` counts archived in `support/zerocopy_payload_niche_enums_and_unreachable_branching_census.json`.
