#!/usr/bin/env python3
"""Standalone empirical probe for 24-revision rustc MIR scaling and zero-build.rs dialect adapters:
1. Four-tier 2.54-year / 24-revision scaling census (`rust-lang/rust` `1.78.0` -> `1.102.0-nightly`)
   across compiler releases, narrow capture-driver API breaks, `mir/syntax.rs` & `mir/mod.rs` AST
   schema mutations (classified by `Runtime(PostCleanup)` reachability), and operational runtime
   MIR semantic transitions.
2. Live zero-`build.rs`, zero-external-proc-macro multi-version `rustc_private` compilation matrix
   comparing `#![feature(cfg_version)]`, `#![feature(cfg_accessible)]`, and explicit manifest-mapped
   `--cfg anneal_mir_dialect="..."` adapter modules across installed `rustup` toolchains.
3. Companion `--sysroot` capability-flag single-file `TrunkCapture` driver and glob-shadowed
   `cfg_accessible` probe (`--extra-sysroot LABEL=PATH`), recording compile latency, binary size,
   and `-Zmir-preserve-ub` execution.

Stdlib-only Python 3.10+; all temporary clones and builds execute inside `tempfile.TemporaryDirectory()`.
"""

from __future__ import annotations

import argparse
from datetime import datetime
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time

STABLE_RELEASES = [f"1.{m}.0" for m in range(78, 101)]
NIGHTLY_PIN = ("1.102.0-nightly", "3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1")
INTRA_NIGHTLY_PIN = ("1.102.0-nightly-2026-11-19", "6905905bb7727fd0f9223f5fdc9ad4e62236d5a2")

MIR_DECLS = [
    ("Body", r"pub struct Body<'tcx>"),
    ("BasicBlockData", r"pub struct BasicBlockData<'tcx>"),
    ("LocalDecl", r"pub struct LocalDecl<'tcx>"),
    ("StatementKind", r"pub enum StatementKind<'tcx>"),
    ("Rvalue", r"pub enum Rvalue<'tcx>"),
    ("Operand", r"pub enum Operand<'tcx>"),
    ("ProjectionElem", r"pub enum ProjectionElem<"),
    ("TerminatorKind", r"pub enum TerminatorKind<"),
    ("CastKind", r"pub enum CastKind\b"),
    ("BinOp", r"pub enum BinOp\b"),
    ("UnOp", r"pub enum UnOp\b"),
    ("NullOp", r"pub enum NullOp<|pub enum NullOp\b"),
    ("UnwindAction", r"pub enum UnwindAction\b"),
    ("AssertKind", r"pub enum AssertKind<"),
    ("NonDivergingIntrinsic", r"pub enum NonDivergingIntrinsic<"),
    ("RetagKind", r"pub enum RetagKind\b"),
    ("WithRetag", r"pub enum WithRetag\b"),
    ("RuntimeChecks", r"pub enum RuntimeChecks\b"),
]

# Verified causal commit registry (validated dynamically against cloned rust-lang/rust repo)
VERIFIED_TIER2_BREAKS = [
    {
        "id": "T2-01",
        "transition": "1.78.0 -> 1.79.0",
        "subsurface": "(c) TyKind",
        "summary": "TyKind::RawPtr(TypeAndMut<I>) split into RawPtr(I::Ty, Mutability) + TyKind::Pat(I::Ty, I::Pat) added",
        "commit": "7be0dbe77292de955da02fe1de1626bdd2e4cc0a",
        "extra_commits": ["84acfe86dec370028987c205e7ba32cc5796d9b0"],
        "affects_minimal_scalar_adt_driver": True,
    },
    {
        "id": "T2-02",
        "transition": "1.79.0 -> 1.80.0",
        "subsurface": "(c) TyKind",
        "summary": "TyKind::FnPtr(PolyFnSig) -> FnPtr(Binder<I, FnSig<I>>) and Alias(AliasKind, ..) -> Alias(AliasTyKind, AliasTy<I>)",
        "commit": "3bcdf3058ef3eaef5042661cf8301acfbcddce65",
        "extra_commits": [],
        "affects_minimal_scalar_adt_driver": False,
    },
    {
        "id": "T2-03",
        "transition": "1.80.0 -> 1.81.0",
        "subsurface": "(e) GlobalAlloc",
        "summary": "GlobalAlloc::Function(Instance<'tcx>) tuple variant -> struct variant Function { instance, unique }",
        "commit": "41b98da42d0500e38b9dd85c82110ba177ac4de1",
        "extra_commits": [],
        "affects_minimal_scalar_adt_driver": True,
    },
    {
        "id": "T2-04",
        "transition": "1.81.0 -> 1.82.0",
        "subsurface": "(c)/(e) TyKind & GlobalAlloc",
        "summary": "TyKind::FnPtr split into (Binder<I, FnSigTys<I>>, FnHeader<I>); GlobalAlloc::Function removed `unique` field",
        "commit": "c4717cc9d15d30e08f03f51845c950175979bcc4",
        "extra_commits": ["5cab8ae4a4a033acb25d629871deb24db19b638b"],
        "affects_minimal_scalar_adt_driver": True,
    },
    {
        "id": "T2-05",
        "transition": "1.82.0 -> 1.83.0",
        "subsurface": "(a)/(e) RunCompiler & GlobalAlloc",
        "summary": "RunCompiler<'a, 'b> -> RunCompiler<'a>; GlobalAlloc::VTable Option<PolyExistentialTraitRef> -> &List<PolyExistentialPredicate>",
        "commit": "072bf482c98d0f33d8456c6000babf315b63e104",
        "extra_commits": ["018ba0528fa5d22712397e520351295f8582a525"],
        "affects_minimal_scalar_adt_driver": False,
    },
    {
        "id": "T2-06",
        "transition": "1.83.0 -> 1.84.0",
        "subsurface": "(c)/(d) TypingEnv & rustc_abi extraction",
        "summary": "rustc_target::abi extracted to extern crate rustc_abi (Abi -> BackendRepr, Aggregate -> Memory); ParamEnvAnd replaced by TypingEnv / PseudoCanonicalInput in tcx.layout_of",
        "commit": "10721909f29024ba56a9ce667da8652a99a04784",
        "extra_commits": [
            "236fe33345072e6363560fd2b535a10947af86f7",
            "7086dd83cca1cf694c7bd171efbf262fa8ffb4aa",
            "9cba14b95bb07a5b31ed1aac2bf4eadd248232da",
        ],
        "affects_minimal_scalar_adt_driver": True,
    },
    {
        "id": "T2-07",
        "transition": "1.84.0 -> 1.85.0",
        "subsurface": "(a)/(c)/(d) Callbacks::after_analysis, Variants::Empty, TyKind::UnsafeBinder",
        "summary": "Callbacks::after_analysis & after_expansion changed third param from &'tcx Queries<'tcx> to TyCtxt<'tcx>; Variants::Empty added for 0-variant enums; TyKind::UnsafeBinder added",
        "commit": "3b02a3309e12906a455eb128a0aa74c6a6afc932",
        "extra_commits": [
            "b795264daa2d411fa232a3de51cc4b0ef8c86a33",
            "e023590de407f417e0f3da675a372eca7acf60c6",
            "9a1c5eb5b385adb3cd04af0049cbf5c225cefdc3",
        ],
        "affects_minimal_scalar_adt_driver": True,
    },
    {
        "id": "T2-08",
        "transition": "1.85.0 -> 1.86.0",
        "subsurface": "(a)/(f) RunCompiler removal -> run_compiler",
        "summary": "rustc_driver::RunCompiler struct removed and replaced by rustc_driver::run_compiler(&[String], &mut (dyn Callbacks + Send)); Callbacks::after_crate_root_parsing(&mut ast::Crate)",
        "commit": "a77776cc1d7c599f4ff9355ffe01bad2e2b5bbad",
        "extra_commits": [],
        "affects_minimal_scalar_adt_driver": True,
    },
    {
        "id": "T2-09",
        "transition": "1.86.0 -> 1.87.0",
        "subsurface": "(d) BackendRepr & LayoutData",
        "summary": "BackendRepr::Uninhabited removed (moved to LayoutData.uninhabited: bool); BackendRepr::Vector renamed to SimdVector",
        "commit": "7ba3d7b54e7688f6f1a0fd22fe274ee7b06fea3e",
        "extra_commits": ["aac65f562b3e9351d4a4336c270ce13c130de467"],
        "affects_minimal_scalar_adt_driver": True,
    },
    {
        "id": "T2-10",
        "transition": "1.88.0 -> 1.89.0",
        "subsurface": "(d) LayoutData.align & Variants::Multiple.tag_field",
        "summary": "LayoutData.align changed from AbiAndPrefAlign to AbiAlign (removing preferred align); Variants::Multiple.tag_field changed from usize to FieldIdx",
        "commit": "2e1965831526407bada7abec631d7b7e9f6cbc7d",
        "extra_commits": ["ee9901e65c78f70b93dab5bd1e04bd77273b7c40"],
        "affects_minimal_scalar_adt_driver": True,
    },
    {
        "id": "T2-11",
        "transition": "1.89.0 -> 1.90.0",
        "subsurface": "(e) ConstValue::Slice & GlobalAlloc::TypeId",
        "summary": "ConstValue::Slice { data: ConstAllocation, meta } changed to Slice { alloc_id: AllocId, meta }; GlobalAlloc::TypeId { ty } added",
        "commit": "9ff071219bca913e45235568defadd5ab840c50a",
        "extra_commits": ["486ffda9dcd0d4ef0a09d81e6ce5f241e77526a1"],
        "affects_minimal_scalar_adt_driver": True,
    },
    {
        "id": "T2-12",
        "transition": "1.91.0 -> 1.92.0",
        "subsurface": "(c) TyKind::Dynamic & TyKind::Bound",
        "summary": "TyKind::Dynamic dropped DynKind (3-tuple -> 2-tuple); TyKind::Bound changed DebruijnIndex -> BoundVarIndexKind",
        "commit": "26f3337d4eda0ba22b615744fda0185d0ee344b1",
        "extra_commits": [],
        "affects_minimal_scalar_adt_driver": False,
    },
    {
        "id": "T2-13",
        "transition": "1.93.0 -> 1.94.0",
        "subsurface": "(a)/(d) catch_with_exit_code -> ExitCode & FieldsShape::Arbitrary",
        "summary": "rustc_driver::catch_with_exit_code return type changed from i32 to std::process::ExitCode; FieldsShape::Arbitrary memory_index replaced by inverse in_memory_order; BackendRepr::ScalableVector added",
        "commit": "6d36c8a5fc4dd9ad3a4cf95ca31ecdc7f06bafc1",
        "extra_commits": ["b31ee3af9c67c777143c0b6707a4439c78391b69"],
        "affects_minimal_scalar_adt_driver": True,
    },
    {
        "id": "T2-14",
        "transition": "1.95.0 -> 1.96.0",
        "subsurface": "(c)/(d) TyKind::Alias & BackendRepr::SimdScalableVector",
        "summary": "TyKind::Alias(AliasTyKind, AliasTy<I>) collapsed to Alias(AliasTy<I>); BackendRepr::ScalableVector -> SimdScalableVector",
        "commit": "cf96c5fa87f6805a382d4c6a9082c9777a404b5f",
        "extra_commits": ["db5e2dc248fe5bb26f70d7baec46a3bca9fa3e1d"],
        "affects_minimal_scalar_adt_driver": False,
    },
    {
        "id": "T2-15",
        "transition": "1.96.0 -> 1.97.0",
        "subsurface": "(d) Variants::Multiple.variants",
        "summary": "Variants::Multiple.variants changed element type from LayoutData<FieldIdx, VariantIdx> to VariantLayout<FieldIdx>",
        "commit": "1162bdc1f3fe4a85f6b1d217578f40669c43aeb5",
        "extra_commits": ["0569574938af400dfbfd88fea5a402a52f4cb4cf"],
        "affects_minimal_scalar_adt_driver": True,
    },
    {
        "id": "T2-16",
        "transition": "1.97.0 -> 1.98.0",
        "subsurface": "(c) TyKind::Alias(IsRigid, AliasTy<I>)",
        "summary": "TyKind::Alias gained IsRigid marker field: Alias(AliasTy<I>) -> Alias(IsRigid, AliasTy<I>)",
        "commit": "3dbe96a5a1b3e0e9cf8b9f0db1e7e4a5af58bf08",
        "extra_commits": [],
        "affects_minimal_scalar_adt_driver": False,
    },
    {
        "id": "T2-17",
        "transition": "1.98.0 -> 1.99.0",
        "subsurface": "(c)/(d) TyKind::FnDef Binder & BackendRepr::ScalarPair",
        "summary": "TyKind::FnDef wrapped GenericArgs in Binder<I, I::GenericArgs>; BackendRepr::ScalarPair(Scalar, Scalar) -> struct ScalarPair { a, b, b_offset }",
        "commit": "8fb83aba335e79dfb6843ec40c21b37f5f85a772",
        "extra_commits": ["2efdc665a7809236738262ea13e5e3f1db204fd4"],
        "affects_minimal_scalar_adt_driver": True,
    },
    {
        "id": "T2-18",
        "transition": "1.99.0 -> 1.100.0",
        "subsurface": "(e) Scalar::Ptr NonZero<u8>",
        "summary": "mir::interpret::Scalar::Ptr(Pointer<Prov>, u8) changed pointer-size field to NonZero<u8>",
        "commit": "d802d17e292ff782d346e0353af3a37dcb5ca12f",
        "extra_commits": [],
        "affects_minimal_scalar_adt_driver": True,
    },
    {
        "id": "T2-19",
        "transition": "1.100.0 -> 1.102.0-nightly",
        "subsurface": "(a)/(d) compiler_entrypoint & LayoutData.align: Align",
        "summary": "rustc_driver::run_compiler renamed to compiler_entrypoint; LayoutData.align changed from AbiAlign (.abi) to Align (+ repr_c: bool)",
        "commit": "c39fbc44eb0f296a7ad161eee642e8bcd2a82235",
        "extra_commits": ["81330f91e512e79001654f32843633dc21c42117"],
        "affects_minimal_scalar_adt_driver": True,
    },
]

# Tier 4 genuine operational runtime MIR semantic changes across 1.78.0 -> 1.102.0-nightly
VERIFIED_TIER4_SEMANTIC_DELTAS = [
    {
        "id": "T4-01",
        "transition": "1.78.0 -> 1.79.0",
        "category": "operator_and_provenance",
        "summary": "Three-way integer comparison `BinOp::Cmp` (-1/0/+1 `Ordering`) + `CastKind::PointerExposeProvenance`/`PointerWithExposedProvenance` + unified `NullOp::UbChecks`",
        "commit": "3da115a93b782796e3d267266b4241e5258f1fef",
        "extra_commits": [
            "989660c3e6efc1c5eb2e822f68863df7d06cbcb4",
            "61775304200826b412f18fc87218161fb8a0dc5c",
        ],
    },
    {
        "id": "T4-02",
        "transition": "1.79.0 -> 1.80.0",
        "category": "operator_and_pointer_offset",
        "summary": "`Rvalue::CheckedBinaryOp` folded into `Rvalue::BinaryOp(AddWithOverflow|SubWithOverflow|MulWithOverflow)` + `UnOp::PtrMetadata` + `offset`/`offset_from` permits 0-byte offset on arbitrary dangling/null pointers + `Drop` always evaluates place",
        "commit": "95c0e5c6a86ca467b0fb7043bd56dee82418ac5f",
        "extra_commits": [
            "459ce3f6bb5d8827835ed9b9f916eb189420b38a",
            "5c33a5690de89587b645fb0e7b657fe545e4d0e8",
            "86a933a5743afe4117fdde5bdf04ba1baa634715",
        ],
    },
    {
        "id": "T4-03",
        "transition": "1.80.0 -> 1.81.0",
        "category": "storage_lifecycle_and_shift_ub",
        "summary": "`StorageLive` on an already-live local changed from Immediate UB to storage refresh (deallocate + reallocate uninit); signed negative shift offsets defined via `rem_euclid`; `offset_from` allows equal addresses across allocations; `TerminatorKind::TailCall`",
        "commit": "9b05e154f39f1a413ebc09c8f1dd751f991b3bba",
        "extra_commits": [
            "669a40006bf3494b0d320fb77bf39cc19a6c5bc4",
            "f6c377c350d7946881449daac2039a09b1734b46",
            "484152d562f6babaacb3fae08cc5f70ee550e9ee",
        ],
    },
    {
        "id": "T4-04",
        "transition": "1.81.0 -> 1.82.0",
        "category": "provenance_and_intrinsics",
        "summary": "`raw_eq` on bytes carrying pointer provenance relaxed from UB to defined at runtime (`const-eval` still errors); `raw_eq` enforces alignment check; `UbChecks` evaluated per defining crate rather than caller crate",
        "commit": "f97aba2271baf1876940b42cc68f1b60ac97bf98",
        "extra_commits": [
            "e17be955bbd5c0fa6e95805a2cb96946262cd75b",
            "7ea2981605ef13f713f42e877c4c31b059cb1ebe",
        ],
    },
    {
        "id": "T4-05",
        "transition": "1.82.0 -> 1.83.0",
        "category": "typed_copy_padding_and_provenance",
        "summary": "Typed copies strip pointer provenance on non-pointer scalar subfields (`reset_provenance`) and `Box<ZST>` validity updated for zero-sized allocation rules",
        "commit": "cbdcbf0d6a586792c5e0a0b8965a3179bac56120",
        "extra_commits": ["05ffd446a9b2d2c67c450bea4180eb4790939e07"],
    },
    {
        "id": "T4-06",
        "transition": "1.84.0 -> 1.85.0",
        "category": "nonoverlapping_swap_ub",
        "summary": "`typed_swap_nonoverlapping` detects aliasing/overlap UB even for scalar immediates (previously skipped overlap check on non-memory scalar path)",
        "commit": "335f7f59c1a4ffa0483f936a905b25f2f58c0263",
        "extra_commits": [],
    },
    {
        "id": "T4-07",
        "transition": "1.85.0 -> 1.86.0",
        "category": "float_nondeterminism_and_unsafe_binders",
        "summary": "Operational `f32`/`f64` `minnum`/`maxnum` NaN payload/sign made non-deterministic; `WrapUnsafeBinder`/`UnwrapUnsafeBinder` operational semantics added; slice indexing lowered via `PtrMetadata`",
        "commit": "d98270b07a04178b019d8317d146eb3dd1afface",
        "extra_commits": [
            "fc1a9186dcdad111fd99ddd38bd961a8a205c380",
            "057313b7a607513d6c1aa82e454e2370025f3b9a",
        ],
    },
    {
        "id": "T4-08",
        "transition": "1.90.0 -> 1.91.0",
        "category": "call_aliasing_and_fn_align",
        "summary": "In-place `Move` call arguments and return-place aliasing made UB when passing identical/overlapping locals; function allocations no longer carry spurious alignment in Miri/CTFE",
        "commit": "ece1397e3ff40e7f8a411981844a8214659da970",
        "extra_commits": [
            "7dfbc0ac1435b76bce4b6baf1ce1b3f7080538e1",
            "78bdd86c676a4e08849677c351591db3564d87e8",
            "f554c79ef819cbc0f9983d0d5306cd7a9bfea6d8",
        ],
    },
    {
        "id": "T4-09",
        "transition": "1.91.0 -> 1.92.0",
        "category": "deinit_removal_and_aggregate_init",
        "summary": "`StatementKind::Deinit` and `Rvalue::Len` removed from runtime MIR (`write_uninit` lowered differently); overlapping aggregate field initialization fixed; `ProjectionElem::Subtype` -> `CastKind::Subtype`",
        "commit": "b7c2b3dc80e03dbbde6ff869c1f975c036703590",
        "extra_commits": [
            "53b91ea87fe4b430c33bd22dfdaaa6289bf9466a",
            "8ecda4b7f866d77d4a87c5b5bc601d4078841093",
            "aa5a21450a070fdea66a07d3cab3b69e6735c328",
        ],
    },
    {
        "id": "T4-10",
        "transition": "1.92.0 -> 1.93.0",
        "category": "offset_of_and_scalar_pair_padding",
        "summary": "`NullOp::OffsetOf` removed and lowered to explicit compile-time constant sums; writing a `ScalarPair` resets uninitialized padding across the full destination range",
        "commit": "72444372ae6900792ae53bec89c2ab442d589a71",
        "extra_commits": ["324e47ba2b3d2f211e4125d0b6c8fe3ceee35e91"],
    },
    {
        "id": "T4-11",
        "transition": "1.93.0 -> 1.94.0",
        "category": "nullary_op_to_operand_runtime_checks",
        "summary": "`Rvalue::NullaryOp` eliminated (`SizeOf`/`AlignOf` folded to constants; `RuntimeChecks` moved into `Operand::RuntimeChecks`)",
        "commit": "1a227bd47ff200975f4afb287ec725861ab8b87a",
        "extra_commits": ["6319bee585561a078de4a0f8d07d567ce69cf12c"],
    },
    {
        "id": "T4-12",
        "transition": "1.94.0 -> 1.95.0",
        "category": "box_init_and_padding_copy",
        "summary": "`Rvalue::ShallowInitBox` removed in favor of `write_via_move` / `write_box_via_move` intrinsics; typed copies with padding preserve byte-level mem-to-mem representation",
        "commit": "6d4b1b38e76c0858c8e98f89afa37535261749ca",
        "extra_commits": [
            "93d45480aa6db1009ebf67b845d8e9b995f46f56",
            "635bacf46627409cb4569b93d38bdf23282966f3",
        ],
    },
    {
        "id": "T4-13",
        "transition": "1.96.0 -> 1.97.0",
        "category": "implicit_retagging_semantics",
        "summary": "`StatementKind::Retag` removed; `Rvalue::Use(op, WithRetag::Yes|No)` makes typed copies implicitly retag references/boxes unless marked `WithRetag::No`",
        "commit": "e402c1edf047a23b0cfef40c6097d1caa294050b",
        "extra_commits": ["c6befd82cea3ce6322ec7384c10cdfe9dd2fd957"],
    },
    {
        "id": "T4-14",
        "transition": "1.98.0 -> 1.99.0",
        "category": "call_eval_order_and_box_deref_ub",
        "summary": "`TerminatorKind::Call` operational order flipped to evaluate `destination` place BEFORE `func` and `args`; `CastKind::BoxDerefTransmute` makes invalid-`Box<T>` deref cast immediate UB; cast inputs and dereferenced pointers validated",
        "commit": "752a91064f4297df39b7215bd9ba30bdd8145661",
        "extra_commits": [
            "fcf68f21cf2f50e824bc4054ca4f46f0dd8ce42f",
            "b3724b650ef1fc5fcdf348e4077e68715596f888",
            "14d28b13c77ecc83458f26cfff5cd4b56b852d29",
        ],
    },
    {
        "id": "T4-15",
        "transition": "1.99.0 -> 1.100.0",
        "category": "never_type_and_infallible_alias",
        "summary": "Never type `!` stabilized (`!`-fallback on all editions) and `core::convert::Infallible = !` aliased (flipping observable runtime `TypeId::of::<Infallible>() == TypeId::of::<!>()` from `false` to `true`)",
        "commit": "cfc82ebbfc6098a18fa09457e6f966cc237577bb",
        "extra_commits": [
            "e7769602aca3770e8d8ea55716becb22e839a579",
            "dd132214ed3e2415da4292fec21f564f4496baa5",
        ],
    },
    {
        "id": "T4-16",
        "transition": "1.100.0 -> 1.102.0-nightly",
        "category": "union_padding_copy_overlap_and_inline_asm_order",
        "summary": "Newly constructed unions explicitly reset padding bytes to `Uninit`; `copy_nonoverlapping` checks overlap even when `src` is fully `Uninit`; `write_bytes` checks alignment; `InlineAsm` destination places evaluated before inputs; `Box<T>` inner wrapper changed from `Unique<T>` to `BoxRaw<T>`",
        "commit": "e7007d3aaaa6a6ca1bcd95f1f10c9411693a3628",
        "extra_commits": [
            "50871c88373cb15c35226246bcbee10ce5712691",
            "50031dfd7825adc0da3918230a141971ac578bf7",
            "834e5b6caa3a365dc242d61425308c25b3af9b5e",
            "5d260fd3da7b0165d6365adab12746bfc389d913",
        ],
    },
]


# Prototype multi-dialect source (`src/dialect.rs` + `src/main.rs`)
DIALECT_RS = r'''//! Narrow compiler-dialect adapter isolating 15 months of `rustc_private` drift.

use rustc_abi::TyAndLayout;
use rustc_driver::Callbacks;
use rustc_middle::mir::interpret::Scalar;
use rustc_middle::mir::{
    CastKind, Operand, ProjectionElem, Rvalue, StatementKind, TerminatorKind,
};
use rustc_middle::ty::Ty;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RetagMode {
    ImplicitYes,
    ExplicitNo,
    LegacySeparateStmt,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GotoSummary {
    Plain { target_bb: usize },
    WithUnrollHints { target_bb: usize, hint_count: usize },
}

pub fn run_driver_and_exit(f: impl FnOnce()) -> std::process::ExitCode {
    #[cfg(anneal_mir_dialect = "mir_1_91_93")]
    {
        let code: i32 = rustc_driver::catch_with_exit_code(f);
        if code == 0 {
            std::process::ExitCode::SUCCESS
        } else {
            std::process::ExitCode::from(1)
        }
    }
    #[cfg(not(anneal_mir_dialect = "mir_1_91_93"))]
    {
        rustc_driver::catch_with_exit_code(f)
    }
}

pub fn invoke_driver(args: &[String], callbacks: &mut (dyn Callbacks + Send)) {
    #[cfg(anneal_mir_dialect = "mir_1_102_nightly")]
    {
        rustc_driver::compiler_entrypoint(args, callbacks);
    }
    #[cfg(not(anneal_mir_dialect = "mir_1_102_nightly"))]
    {
        rustc_driver::run_compiler(args, callbacks);
    }
}

pub fn layout_abi_align_bytes<'tcx>(layout: &TyAndLayout<'tcx, Ty<'tcx>>) -> u64 {
    #[cfg(anneal_mir_dialect = "mir_1_102_nightly")]
    {
        layout.align.bytes()
    }
    #[cfg(not(anneal_mir_dialect = "mir_1_102_nightly"))]
    {
        layout.align.abi.bytes()
    }
}

pub fn scalar_ptr_size_bytes(scalar: Scalar) -> Option<u8> {
    match scalar {
        Scalar::Int(_) => None,
        #[cfg(any(
            anneal_mir_dialect = "mir_1_100",
            anneal_mir_dialect = "mir_1_102_nightly",
        ))]
        Scalar::Ptr(_, nz_sz) => Some(nz_sz.get()),
        #[cfg(not(any(
            anneal_mir_dialect = "mir_1_100",
            anneal_mir_dialect = "mir_1_102_nightly",
        )))]
        Scalar::Ptr(_, sz) => Some(sz),
    }
}

pub fn extract_rvalue_use<'a, 'tcx>(
    rv: &'a Rvalue<'tcx>,
) -> Option<(&'a Operand<'tcx>, RetagMode)> {
    match rv {
        #[cfg(any(
            anneal_mir_dialect = "mir_1_91_93",
            anneal_mir_dialect = "mir_1_94_96",
        ))]
        Rvalue::Use(op) => Some((op, RetagMode::LegacySeparateStmt)),
        #[cfg(not(any(
            anneal_mir_dialect = "mir_1_91_93",
            anneal_mir_dialect = "mir_1_94_96",
        )))]
        Rvalue::Use(op, with_retag) => {
            let mode = match with_retag {
                rustc_middle::mir::WithRetag::Yes => RetagMode::ImplicitYes,
                rustc_middle::mir::WithRetag::No => RetagMode::ExplicitNo,
            };
            Some((op, mode))
        }
        _ => None,
    }
}

pub fn is_legacy_retag_stmt(kind: &StatementKind<'_>) -> bool {
    #[cfg(any(
        anneal_mir_dialect = "mir_1_91_93",
        anneal_mir_dialect = "mir_1_94_96",
    ))]
    {
        matches!(kind, StatementKind::Retag(_, _))
    }
    #[cfg(not(any(
        anneal_mir_dialect = "mir_1_91_93",
        anneal_mir_dialect = "mir_1_94_96",
    )))]
    {
        let _ = kind;
        false
    }
}

pub fn is_box_deref_transmute(ck: &CastKind) -> bool {
    #[cfg(any(
        anneal_mir_dialect = "mir_1_99",
        anneal_mir_dialect = "mir_1_100",
        anneal_mir_dialect = "mir_1_102_nightly",
    ))]
    {
        matches!(ck, CastKind::BoxDerefTransmute)
    }
    #[cfg(not(any(
        anneal_mir_dialect = "mir_1_99",
        anneal_mir_dialect = "mir_1_100",
        anneal_mir_dialect = "mir_1_102_nightly",
    )))]
    {
        let _ = ck;
        false
    }
}

pub fn is_phantom_deref<V, T>(elem: &ProjectionElem<V, T>) -> bool {
    #[cfg(any(
        anneal_mir_dialect = "mir_1_100",
        anneal_mir_dialect = "mir_1_102_nightly",
    ))]
    {
        matches!(elem, ProjectionElem::PhantomDeref)
    }
    #[cfg(not(any(
        anneal_mir_dialect = "mir_1_100",
        anneal_mir_dialect = "mir_1_102_nightly",
    )))]
    {
        let _ = elem;
        false
    }
}

pub fn classify_goto(term: &TerminatorKind<'_>) -> Option<GotoSummary> {
    match term {
        #[cfg(anneal_mir_dialect = "mir_1_102_nightly")]
        TerminatorKind::Goto { target, loop_hint_attrs } => {
            if loop_hint_attrs.is_empty() {
                Some(GotoSummary::Plain { target_bb: target.as_usize() })
            } else {
                Some(GotoSummary::WithUnrollHints {
                    target_bb: target.as_usize(),
                    hint_count: loop_hint_attrs.len(),
                })
            }
        }
        #[cfg(not(anneal_mir_dialect = "mir_1_102_nightly"))]
        TerminatorKind::Goto { target } => {
            Some(GotoSummary::Plain { target_bb: target.as_usize() })
        }
        _ => None,
    }
}
'''

MAIN_RS = r'''#![feature(rustc_private)]
#![deny(unexpected_cfgs)]

extern crate rustc_abi;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;

pub mod dialect;

// Fail-closed compile-time check: require a single known `anneal_mir_dialect`.
#[cfg(not(any(
    anneal_mir_dialect = "mir_1_91_93",
    anneal_mir_dialect = "mir_1_94_96",
    anneal_mir_dialect = "mir_1_97_98",
    anneal_mir_dialect = "mir_1_99",
    anneal_mir_dialect = "mir_1_100",
    anneal_mir_dialect = "mir_1_102_nightly",
)))]
compile_error!("exactly one known `--cfg anneal_mir_dialect=\"...\"` must be passed");

use rustc_driver::{Callbacks, Compilation};
use rustc_interface::interface;
use rustc_middle::mir::{Rvalue, StatementKind};
use rustc_middle::ty::{TyCtxt, TypingEnv};

struct CaptureCallbacks {
    bodies: usize,
    bbs: usize,
    uses_implicit_yes: usize,
    uses_explicit_no: usize,
    uses_legacy: usize,
    legacy_retag_stmts: usize,
    box_deref_casts: usize,
    gotos_plain: usize,
    gotos_hinted: usize,
    return_ty_sizes: Vec<u64>,
    return_ty_aligns: Vec<u64>,
    ext_crates: usize,
}

impl Callbacks for CaptureCallbacks {
    fn after_analysis<'tcx>(
        &mut self,
        _compiler: &interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> Compilation {
        if tcx.dcx().has_errors().is_some() {
            return Compilation::Stop;
        }
        self.ext_crates = tcx.crates(()).len();
        if let Some(&first_cnum) = tcx.crates(()).first() {
            let _src = tcx.used_crate_source(first_cnum);
        }
        let typing_env = TypingEnv::fully_monomorphized();
        for local_def_id in tcx.hir_body_owners() {
            let steal_body = tcx.mir_drops_elaborated_and_const_checked(local_def_id);
            let body = steal_body.borrow();
            self.bodies += 1;
            self.bbs += body.basic_blocks.len();
            let ret_ty = body.local_decls[rustc_middle::mir::RETURN_PLACE].ty;
            if let Ok(layout) = tcx.layout_of(typing_env.as_query_input(ret_ty)) {
                self.return_ty_sizes.push(layout.size.bytes());
                self.return_ty_aligns.push(dialect::layout_abi_align_bytes(&layout));
            }
            for bb in body.basic_blocks.iter() {
                for stmt in &bb.statements {
                    if dialect::is_legacy_retag_stmt(&stmt.kind) {
                        self.legacy_retag_stmts += 1;
                    }
                    if let StatementKind::Assign(assign) = &stmt.kind {
                        let (place, rv) = &**assign;
                        for elem in place.projection.iter() {
                            let _ = dialect::is_phantom_deref(&elem);
                        }
                        if let Some((_op, mode)) = dialect::extract_rvalue_use(rv) {
                            match mode {
                                dialect::RetagMode::ImplicitYes => self.uses_implicit_yes += 1,
                                dialect::RetagMode::ExplicitNo => self.uses_explicit_no += 1,
                                dialect::RetagMode::LegacySeparateStmt => self.uses_legacy += 1,
                            }
                        }
                        if let Rvalue::Cast(ck, _, _) = rv {
                            if dialect::is_box_deref_transmute(ck) {
                                self.box_deref_casts += 1;
                            }
                        }
                    }
                }
                if let Some(term) = &bb.terminator {
                    if let Some(g) = dialect::classify_goto(&term.kind) {
                        match g {
                            dialect::GotoSummary::Plain { .. } => self.gotos_plain += 1,
                            dialect::GotoSummary::WithUnrollHints { .. } => self.gotos_hinted += 1,
                        }
                    }
                }
            }
        }
        Compilation::Stop
    }
}

fn main() -> std::process::ExitCode {
    let args: Vec<String> = std::env::args().collect();
    let mut cb = CaptureCallbacks {
        bodies: 0,
        bbs: 0,
        uses_implicit_yes: 0,
        uses_explicit_no: 0,
        uses_legacy: 0,
        legacy_retag_stmts: 0,
        box_deref_casts: 0,
        gotos_plain: 0,
        gotos_hinted: 0,
        return_ty_sizes: Vec::new(),
        return_ty_aligns: Vec::new(),
        ext_crates: 0,
    };
    let _ = dialect::scalar_ptr_size_bytes;
    let code = dialect::run_driver_and_exit(|| {
        dialect::invoke_driver(&args, &mut cb);
    });
    if code != std::process::ExitCode::SUCCESS {
        return code;
    }
    println!(
        "{{\"bodies\":{},\"bbs\":{},\"uses_implicit_yes\":{},\"uses_explicit_no\":{},\"uses_legacy\":{},\"legacy_retag_stmts\":{},\"box_deref_casts\":{},\"gotos_plain\":{},\"gotos_hinted\":{},\"return_ty_sizes\":{:?},\"return_ty_aligns\":{:?},\"ext_crates\":{}}}",
        cb.bodies,
        cb.bbs,
        cb.uses_implicit_yes,
        cb.uses_explicit_no,
        cb.uses_legacy,
        cb.legacy_retag_stmts,
        cb.box_deref_casts,
        cb.gotos_plain,
        cb.gotos_hinted,
        cb.return_ty_sizes,
        cb.return_ty_aligns,
        cb.ext_crates,
    );
    std::process::ExitCode::SUCCESS
}
'''

CARGO_TOML = r'''[package]
name = "anneal-multi-dialect-capture-proto"
version = "0.1.0"
edition = "2021"
publish = false

[dependencies]

[lints.rust]
unexpected_cfgs = { level = "deny", check-cfg = [
    'cfg(anneal_mir_dialect, values("mir_1_91_93", "mir_1_94_96", "mir_1_97_98", "mir_1_99", "mir_1_100", "mir_1_102_nightly"))',
] }
'''

SAMPLE_CRATE_RS = r'''#![allow(dead_code)]
extern crate alloc;
use alloc::boxed::Box;

pub struct Wrapper<'a> {
    pub r: &'a u64,
}

pub fn deref_box_and_loop(b: Box<u64>, w: &Wrapper<'_>, n: u64) -> u64 {
    let mut acc = *b + *w.r;
    let mut i = 0;
    while i < n {
        acc = acc.wrapping_add(i);
        i += 1;
    }
    acc
}
'''


def git(repo: str, *args: str, check: bool = True) -> str:
    p = subprocess.run(["git", "-C", repo, *args], text=True, capture_output=True, check=False)
    if check and p.returncode != 0:
        raise RuntimeError(f"git {' '.join(args)} failed: {p.stderr}")
    return p.stdout


def clean_env(extra: dict[str, str] | None = None) -> dict[str, str]:
    env = os.environ.copy()
    env.pop("RUSTUP_TOOLCHAIN", None)
    env.pop("LD_LIBRARY_PATH", None)
    env.pop("RUSTC_OVERRIDE_VERSION_STRING", None)
    env.pop("RUSTFLAGS", None)
    if extra:
        env.update(extra)
    return env


def extract_brace_block(src: str, header_regex: str) -> str | None:
    m = re.search(header_regex, src, re.MULTILINE)
    if not m:
        return None
    idx = src.find("{", m.start())
    if idx == -1:
        return None
    depth = 0
    in_line_comment = False
    for i in range(idx, len(src)):
        ch = src[i]
        if in_line_comment:
            if ch == "\n":
                in_line_comment = False
            continue
        if ch == "/" and i + 1 < len(src) and src[i + 1] == "/":
            in_line_comment = True
            continue
        if ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
            if depth == 0:
                return src[m.start() : i + 1]
    return None


def parse_top_level_items(block: str | None) -> list[str] | None:
    if not block:
        return None
    idx = block.find("{")
    body = block[idx + 1 : -1]
    body = re.sub(r"//[^\n]*", "", body)
    body = re.sub(r"/\*.*?\*/", "", body, flags=re.DOTALL)
    for _ in range(5):
        body = re.sub(r"#\[(?:[^\[\]]|\[[^\]]*\])*\]", "", body)
    items = []
    cur = []
    depth = 0
    for ch in body:
        if ch in "({[<":
            depth += 1
            cur.append(ch)
        elif ch in ")}]>":
            depth = max(0, depth - 1)
            cur.append(ch)
        elif ch == "," and depth == 0:
            s = " ".join("".join(cur).split()).strip()
            if s:
                items.append(s)
            cur = []
        else:
            cur.append(ch)
    s = " ".join("".join(cur).split()).strip()
    if s:
        items.append(s)
    return items


def classify_tier3_delta_runtime_reachability(decl_name: str, delta: dict) -> dict:
    """Classify each AST schema mutation into Runtime(PostCleanup)-reachable vs pre-runtime/metadata."""
    if decl_name in ("Body", "BasicBlockData"):
        return {
            "reachable_in_runtime_postcleanup": False,
            "reason": "Metadata/coverage/debuginfo struct fields on Body/BasicBlockData; zero operational MIR control/dataflow impact.",
        }
    added = delta.get("added", [])
    removed = delta.get("removed", [])
    combined = " ".join(added + removed)
    if decl_name == "StatementKind" and "Coverage" in combined and len(added) == 1 and len(removed) == 1:
        return {
            "reachable_in_runtime_postcleanup": False,
            "reason": "Coverage statement payload wrapper/formatting refactor; non-operational instrumentation.",
        }
    if decl_name == "StatementKind" and "BackwardIncompatibleDropHint" in combined:
        return {
            "reachable_in_runtime_postcleanup": False,
            "reason": "Replaced with Nop in CleanupPostBorrowck (rustc_mir_transform/src/cleanup_post_borrowck.rs:36) before Runtime(PostCleanup).",
        }
    if decl_name == "ProjectionElem" and added == ["PhantomDeref"] and not removed:
        return {
            "reachable_in_runtime_postcleanup": False,
            "reason": "Pre-borrowck reborrow placeholder; ICEs if present after borrowck (rustc_const_eval/src/interpret/projection.rs:414-415).",
        }
    if decl_name == "TerminatorKind" and all("async_fut" in s or "drop: Option<BasicBlock>" in s for s in added + removed):
        return {
            "reachable_in_runtime_postcleanup": True,
            "operational_in_runtime_postcleanup": False,
            "reason": "Struct-variant field change on TerminatorKind::Drop breaks exhaustive pattern matching in capture drivers, though Drop.drop is asserted None in runtime MIR (step.rs:654-657).",
        }
    if decl_name == "TerminatorKind" and "loop_hint_attrs" in combined:
        return {
            "reachable_in_runtime_postcleanup": True,
            "operational_in_runtime_postcleanup": False,
            "reason": "Struct-variant field addition on TerminatorKind::Goto breaks `{ target }` destructuring in capture drivers, though ignored operationally (step.rs:563).",
        }
    return {
        "reachable_in_runtime_postcleanup": True,
        "operational_in_runtime_postcleanup": True,
        "reason": "Construct or variant signature reachable in MirPhase::Runtime(RuntimePhase::PostCleanup).",
    }


def run_part1_git_census(repo_url: str) -> dict:
    t0 = time.time()
    with tempfile.TemporaryDirectory() as tmp:
        repo = os.path.join(tmp, "rust")
        subprocess.run(
            ["git", "clone", "--filter=blob:none", "--no-checkout", repo_url, repo],
            check=True,
        )
        for _, nsha in (NIGHTLY_PIN, INTRA_NIGHTLY_PIN):
            subprocess.run(
                ["git", "-C", repo, "fetch", "--filter=blob:none", "origin", nsha],
                check=True,
            )

        revisions = []
        for rel in STABLE_RELEASES:
            sha = git(repo, "rev-parse", f"{rel}^{{commit}}").strip()
            dt = git(repo, "show", "-s", "--format=%cI", sha).strip()
            revisions.append({"release": rel, "sha": sha, "commit_date": dt, "channel": "stable"})

        n_label, n_sha = NIGHTLY_PIN
        n_dt = git(repo, "show", "-s", "--format=%cI", n_sha).strip()
        revisions.append({"release": n_label, "sha": n_sha, "commit_date": n_dt, "channel": "nightly"})

        in_label, in_sha = INTRA_NIGHTLY_PIN
        in_dt = git(repo, "show", "-s", "--format=%cI", in_sha).strip()
        intra_nightly_entry = {"release": in_label, "sha": in_sha, "commit_date": in_dt, "channel": "nightly"}

        # Compute exact horizon duration
        d_start = datetime.fromisoformat(revisions[0]["commit_date"])
        d_end = datetime.fromisoformat(revisions[-1]["commit_date"])
        horizon_days = (d_end - d_start).total_seconds() / 86400.0
        horizon_years = horizon_days / 365.25
        num_transitions = len(revisions) - 1  # 23 transitions across 24 points

        # Extract Tier 3 MIR AST snapshots across all 24 points
        mir_snapshots = {}
        for entry in revisions:
            rel, sha = entry["release"], entry["sha"]
            combined = ""
            for p in (
                "compiler/rustc_middle/src/mir/syntax.rs",
                "compiler/rustc_middle/src/mir/mod.rs",
            ):
                txt = git(repo, "show", f"{sha}:{p}", check=False)
                if txt:
                    combined += "\n" + txt
            snap = {}
            for decl_name, pat in MIR_DECLS:
                snap[decl_name] = parse_top_level_items(extract_brace_block(combined, pat))
            mir_snapshots[rel] = snap

        tier3_transitions = []
        total_tier3_type_deltas = 0
        total_tier3_reachable_deltas = 0
        total_tier3_operational_deltas = 0

        for i in range(num_transitions):
            old_e, new_e = revisions[i], revisions[i + 1]
            old_rel, new_rel = old_e["release"], new_e["release"]
            s_old, s_new = mir_snapshots[old_rel], mir_snapshots[new_rel]
            deltas = {}
            for decl_name, _ in MIR_DECLS:
                a, b = s_old.get(decl_name), s_new.get(decl_name)
                if a != b:
                    if a is None:
                        d_obj = {"change": "added_type", "added": b, "removed": []}
                    elif b is None:
                        d_obj = {"change": "removed_type", "added": [], "removed": a}
                    else:
                        rem = [x for x in a if x not in b]
                        add = [x for x in b if x not in a]
                        # Ignore pure trailing-comma formatting noise (`Coverage(CoverageKind)` vs `Coverage( CoverageKind, )`)
                        norm_rem = [re.sub(r"\s+|,\s*(?=\))", "", x) for x in rem]
                        norm_add = [re.sub(r"\s+|,\s*(?=\))", "", x) for x in add]
                        if norm_rem == norm_add:
                            continue
                        d_obj = {
                            "change": "mutated",
                            "old_count": len(a),
                            "new_count": len(b),
                            "removed": rem,
                            "added": add,
                        }
                    reach = classify_tier3_delta_runtime_reachability(decl_name, d_obj)
                    d_obj.update(reach)
                    deltas[decl_name] = d_obj
                    total_tier3_type_deltas += 1
                    if reach.get("reachable_in_runtime_postcleanup"):
                        total_tier3_reachable_deltas += 1
                    if reach.get("operational_in_runtime_postcleanup"):
                        total_tier3_operational_deltas += 1

            tier3_transitions.append(
                {
                    "transition": f"{old_rel} -> {new_rel}",
                    "old_sha": old_e["sha"],
                    "new_sha": new_e["sha"],
                    "delta_count": len(deltas),
                    "deltas": deltas,
                }
            )

        # Dynamically verify every cited commit SHA in VERIFIED_TIER2_BREAKS and VERIFIED_TIER4_SEMANTIC_DELTAS exists in rust-lang/rust
        verified_commits = {}
        all_shas = set()
        for item in VERIFIED_TIER2_BREAKS + VERIFIED_TIER4_SEMANTIC_DELTAS:
            all_shas.add(item["commit"])
            all_shas.update(item.get("extra_commits", []))
        for csha in sorted(all_shas):
            meta = git(repo, "show", "-s", "--format=%H|%cI|%s", csha).strip()
            full_h, c_dt, subj = meta.split("|", 2)
            verified_commits[csha] = {"sha": full_h, "date": c_dt, "subject": subj}

        t2_total = len(VERIFIED_TIER2_BREAKS)
        t2_minimal = sum(1 for x in VERIFIED_TIER2_BREAKS if x["affects_minimal_scalar_adt_driver"])
        t4_total = len(VERIFIED_TIER4_SEMANTIC_DELTAS)

        non_comment_dialect_loc = sum(
            1
            for l in DIALECT_RS.splitlines()
            if l.strip() and not l.strip().startswith("//")
        )

        rates = {
            "horizon_days": round(horizon_days, 2),
            "horizon_years": round(horizon_years, 4),
            "stable_minor_releases": len(STABLE_RELEASES),
            "total_points_measured": len(revisions),
            "adjacent_transitions": num_transitions,
            "tier1_releases": {
                "count": len(revisions),
                "transitions": num_transitions,
                "releases_per_year": round(num_transitions / horizon_years, 2),
            },
            "tier2_driver_api_breaks": {
                "total_events_across_6_subsurfaces": t2_total,
                "events_affecting_minimal_capture_driver": t2_minimal,
                "breaks_per_transition_full": round(t2_total / num_transitions, 3),
                "breaks_per_transition_minimal": round(t2_minimal / num_transitions, 3),
                "breaks_per_year_full": round(t2_total / horizon_years, 2),
                "breaks_per_year_minimal": round(t2_minimal / horizon_years, 2),
            },
            "tier3_mir_ast_schema_deltas": {
                "total_declaration_mutations": total_tier3_type_deltas,
                "runtime_postcleanup_reachable_mutations": total_tier3_reachable_deltas,
                "runtime_postcleanup_operational_mutations": total_tier3_operational_deltas,
                "transitions_with_any_ast_delta": sum(1 for t in tier3_transitions if t["delta_count"] > 0),
                "deltas_per_transition_total": round(total_tier3_type_deltas / num_transitions, 3),
                "deltas_per_transition_reachable": round(total_tier3_reachable_deltas / num_transitions, 3),
                "deltas_per_year_total": round(total_tier3_type_deltas / horizon_years, 2),
                "deltas_per_year_reachable": round(total_tier3_reachable_deltas / horizon_years, 2),
            },
            "tier4_operational_semantic_deltas": {
                "total_events": t4_total,
                "deltas_per_transition": round(t4_total / num_transitions, 3),
                "deltas_per_year": round(t4_total / horizon_years, 2),
            },
            "adapter_loc_scaling": {
                "prototype_dialect_rs_non_comment_loc": non_comment_dialect_loc,
                "prototype_toolchains_spanned": 10,
                "prototype_minor_cycles_spanned": 12,  # 1.91 .. 1.102
                "measured_adapter_loc_per_minor_release": round(non_comment_dialect_loc / 12.0, 2),
                "estimated_24_release_adapter_loc": round((non_comment_dialect_loc / 12.0) * num_transitions),
            },
        }

        return {
            "elapsed_seconds": round(time.time() - t0, 2),
            "revisions": revisions,
            "intra_nightly_revision": intra_nightly_entry,
            "rates": rates,
            "tier2_breaks": VERIFIED_TIER2_BREAKS,
            "tier3_transitions": tier3_transitions,
            "tier4_semantic_deltas": VERIFIED_TIER4_SEMANTIC_DELTAS,
            "verified_commits": verified_commits,
        }


def run_part2_live_matrix() -> dict:
    # 2A. cfg(version) truth table + spoofing + mid-cycle nightly hazards
    cfg_ver_toolchains = [
        "1.78.0",
        "1.80",
        "1.84.0",
        "1.93.1",
        "1.96.0",
        "1.99.1",
        "1.100.0",
        "stable",
        "stage1",
        "nightly-2026-02-07",
        "nightly-2026-02-23",
        "nightly-2026-04-12",
        "nightly",
        "nightly-2026-11-20",
    ]
    cfg_ver_src = """#![feature(cfg_version)]
fn main() {
    println!(
        "{{\\"v1_78\\":{},\\"v1_84\\":{},\\"v1_95\\":{},\\"v1_97\\":{},\\"v1_99_1\\":{},\\"v1_100\\":{},\\"v1_100_0\\":{},\\"v1_102\\":{}}}",
        cfg!(version("1.78")),
        cfg!(version("1.84")),
        cfg!(version("1.95")),
        cfg!(version("1.97")),
        cfg!(version("1.99.1")),
        cfg!(version("1.100")),
        cfg!(version("1.100.0")),
        cfg!(version("1.102")),
    );
}
"""
    cfg_version_results = []
    with tempfile.TemporaryDirectory() as tmp:
        src = os.path.join(tmp, "cfg_ver.rs")
        Path(src).write_text(cfg_ver_src)
        for idx, tc in enumerate(cfg_ver_toolchains):
            env = clean_env({"RUSTC_BOOTSTRAP": "1"})
            vv = subprocess.check_output(["rustup", "run", tc, "rustc", "-vV"], env=env, text=True).strip()
            headline = vv.splitlines()[0]
            out_bin = os.path.join(tmp, f"cv_{idx}")
            p = subprocess.run(
                ["rustup", "run", tc, "rustc", "--edition=2021", src, "-o", out_bin],
                env=env,
                text=True,
                capture_output=True,
            )
            vals = json.loads(subprocess.check_output([out_bin], text=True).strip()) if p.returncode == 0 else None
            cfg_version_results.append(
                {"toolchain": tc, "rustc_version": headline, "rc": p.returncode, "evaluations": vals}
            )

        # Spoofing tests via RUSTC_OVERRIDE_VERSION_STRING on 1.100.0
        spoof_results = []
        for ov in ["1.78.0-custom", "1.999.0", "0.0.0", "non-semver-custom"]:
            env = clean_env({"RUSTC_BOOTSTRAP": "1", "RUSTC_OVERRIDE_VERSION_STRING": ov})
            out_bin = os.path.join(tmp, "cv_spoof")
            p = subprocess.run(
                ["rustup", "run", "1.100.0", "rustc", "--edition=2021", src, "-o", out_bin],
                env=env,
                text=True,
                capture_output=True,
            )
            vals = json.loads(subprocess.check_output([out_bin], text=True).strip())
            spoof_results.append({"override_env": ov, "evaluations_on_1_100_0": vals})

        # Mid-cycle live rustc_private hazard on nightly-2026-04-12 (1.97.0-nightly pre-WithRetag)
        # + -Z assume-incomplete-release counter-failure on nightly (1.102.0-nightly)
        midcycle_src = """#![feature(rustc_private, cfg_version)]
extern crate rustc_middle;
use rustc_middle::mir::{Operand, Rvalue};
pub fn extract_use<'a, 'tcx>(rv: &'a Rvalue<'tcx>) -> Option<&'a Operand<'tcx>> {
    match rv {
        #[cfg(version("1.97"))]
        Rvalue::Use(op, _retag) => Some(op),
        #[cfg(not(version("1.97")))]
        Rvalue::Use(op) => Some(op),
        _ => None,
    }
}
"""
        entry_102_src = """#![feature(rustc_private, cfg_version)]
extern crate rustc_driver;
#[cfg(version("1.102"))]
pub fn entry(args: &[String], cb: &mut (dyn rustc_driver::Callbacks + Send)) {
    rustc_driver::compiler_entrypoint(args, cb);
}
#[cfg(not(version("1.102")))]
pub fn entry(args: &[String], cb: &mut (dyn rustc_driver::Callbacks + Send)) {
    rustc_driver::run_compiler(args, cb);
}
"""
        mid_f = os.path.join(tmp, "midcycle.rs")
        Path(mid_f).write_text(midcycle_src)
        ent_f = os.path.join(tmp, "ent102.rs")
        Path(ent_f).write_text(entry_102_src)

        midcycle_probes = []
        for tc in ["nightly-2026-02-07", "nightly-2026-04-12", "nightly-2026-05-31", "stable", "nightly"]:
            env = clean_env({"RUSTC_BOOTSTRAP": "1"})
            p = subprocess.run(
                ["rustup", "run", tc, "rustc", "--crate-type=lib", "--edition=2021", mid_f, "-o", os.path.join(tmp, "m.rlib")],
                env=env,
                text=True,
                capture_output=True,
            )
            errs = [l for l in p.stderr.splitlines() if "error" in l]
            midcycle_probes.append({"toolchain": tc, "rc": p.returncode, "errors": errs})

        assume_incomplete_probes = []
        for extra_flags in [[], ["-Z", "assume-incomplete-release"]]:
            for tc in ["stable", "nightly"]:
                env = clean_env({"RUSTC_BOOTSTRAP": "1"})
                p = subprocess.run(
                    ["rustup", "run", tc, "rustc", "--crate-type=lib", "--edition=2021", *extra_flags, ent_f, "-o", os.path.join(tmp, "e.rlib")],
                    env=env,
                    text=True,
                    capture_output=True,
                )
                errs = [l for l in p.stderr.splitlines() if "error" in l]
                assume_incomplete_probes.append(
                    {"toolchain": tc, "flags": extra_flags, "rc": p.returncode, "errors": errs}
                )

    # 2B. cfg_accessible live matrix across 4 rustc-dev toolchains
    cfg_acc_cases = [
        (
            "external_module_type_present",
            """#![feature(rustc_private, cfg_accessible)]
extern crate rustc_abi;
#[cfg_accessible(rustc_abi::TyAndLayout)]
pub fn ok() -> u8 { 1 }
""",
        ),
        (
            "external_fn_compiler_entrypoint",
            """#![feature(rustc_private, cfg_accessible)]
extern crate rustc_driver;
#[cfg_accessible(rustc_driver::compiler_entrypoint)]
pub fn has_new_entry() -> u8 { 1 }
""",
        ),
        (
            "external_enum_variant_box_deref_transmute",
            """#![feature(rustc_private, cfg_accessible)]
extern crate rustc_middle;
#[cfg_accessible(rustc_middle::mir::CastKind::BoxDerefTransmute)]
pub fn has_bdt() -> u8 { 1 }
""",
        ),
        (
            "external_enum_variant_phantom_deref",
            """#![feature(rustc_private, cfg_accessible)]
extern crate rustc_middle;
#[cfg_accessible(rustc_middle::mir::ProjectionElem::PhantomDeref)]
pub fn has_phantom() -> u8 { 1 }
""",
        ),
        (
            "external_missing_intermediate_module",
            """#![feature(rustc_private, cfg_accessible)]
extern crate rustc_middle;
#[cfg_accessible(rustc_middle::nonexistent_submodule::Item)]
pub fn has_sub() -> u8 { 1 }
""",
        ),
        (
            "local_crate_enum_variant",
            """#![feature(cfg_accessible)]
pub enum LocalEnum { Present }
#[cfg_accessible(LocalEnum::Present)]
pub fn has_local() -> u8 { 1 }
""",
        ),
        (
            "struct_field_synthetic",
            """#![feature(cfg_accessible)]
pub struct MyStruct { pub field: u32 }
#[cfg_accessible(MyStruct::field)]
pub fn has_field() -> u8 { 1 }
""",
        ),
        (
            "enum_variant_field_goto_loop_hint_attrs",
            """#![feature(rustc_private, cfg_accessible)]
extern crate rustc_middle;
#[cfg_accessible(rustc_middle::mir::TerminatorKind::Goto::loop_hint_attrs)]
pub fn has_loop_hints() -> u8 { 1 }
""",
        ),
        (
            "inherent_method_tyctxt_mir_query",
            """#![feature(rustc_private, cfg_accessible)]
extern crate rustc_middle;
#[cfg_accessible(rustc_middle::ty::TyCtxt::mir_drops_elaborated_and_const_checked)]
pub fn has_query() -> u8 { 1 }
""",
        ),
        (
            "cfg_not_negation_attempt",
            """#![feature(rustc_private, cfg_accessible)]
extern crate rustc_driver;
#[cfg(not(cfg_accessible(rustc_driver::compiler_entrypoint)))]
pub fn fallback_entry() -> u8 { 0 }
""",
        ),
        (
            "match_arm_position_attempt",
            """#![feature(rustc_private, cfg_accessible)]
extern crate rustc_middle;
pub fn arm_test(ck: rustc_middle::mir::CastKind) -> u8 {
    match ck {
        #[cfg_accessible(rustc_middle::mir::CastKind::BoxDerefTransmute)]
        rustc_middle::mir::CastKind::BoxDerefTransmute => 1,
        _ => 0,
    }
}
""",
        ),
    ]

    cfg_accessible_results = []
    with tempfile.TemporaryDirectory() as tmp:
        for case_name, code in cfg_acc_cases:
            src = os.path.join(tmp, f"{case_name}.rs")
            Path(src).write_text(code)
            per_tc = {}
            for tc in ["nightly-2026-05-31", "1.99.1", "stable", "nightly"]:
                env = clean_env({"RUSTC_BOOTSTRAP": "1"})
                p = subprocess.run(
                    ["rustup", "run", tc, "rustc", "--crate-type=lib", "--edition=2021", src, "-o", os.path.join(tmp, "ca.rlib")],
                    env=env,
                    text=True,
                    capture_output=True,
                )
                errs = [l.strip() for l in p.stderr.splitlines() if "error" in l]
                per_tc[tc] = {"rc": p.returncode, "errors": errs[:3]}
            cfg_accessible_results.append({"case": case_name, "results": per_tc})

    # 2C. Explicit `--cfg anneal_mir_dialect="..."` prototype across all 10 `rustc-dev` toolchains + Cargo builds on stable & nightly
    dialect_matrix = [
        ("nightly-2025-08-20", "mir_1_91_93"),
        ("nightly-2025-11-23", "mir_1_91_93"),
        ("nightly-2026-02-07", "mir_1_94_96"),
        ("nightly-2026-04-12", "mir_1_94_96"),
        ("nightly-2026-05-31", "mir_1_97_98"),
        ("nightly-2026-06-01", "mir_1_97_98"),
        ("1.99.1", "mir_1_99"),
        ("stable", "mir_1_100"),
        ("nightly", "mir_1_102_nightly"),
        ("nightly-2026-11-13", "mir_1_102_nightly"),
    ]
    check_cfg = 'cfg(anneal_mir_dialect, values("mir_1_91_93", "mir_1_94_96", "mir_1_97_98", "mir_1_99", "mir_1_100", "mir_1_102_nightly"))'

    proto_runs = []
    cargo_runs = []
    negative_guard_runs = []

    with tempfile.TemporaryDirectory() as tmp:
        pkg_dir = Path(tmp) / "proto_pkg"
        (pkg_dir / "src").mkdir(parents=True)
        (pkg_dir / "Cargo.toml").write_text(CARGO_TOML)
        (pkg_dir / "src" / "dialect.rs").write_text(DIALECT_RS)
        (pkg_dir / "src" / "main.rs").write_text(MAIN_RS)
        sample_rs = Path(tmp) / "sample.rs"
        sample_rs.write_text(SAMPLE_CRATE_RS)

        for idx, (tc, dialect) in enumerate(dialect_matrix):
            # Intentionally pass hostile `RUSTC_OVERRIDE_VERSION_STRING="1.78.0-hostile"` to prove `--cfg` immunity!
            env = clean_env(
                {
                    "RUSTC_BOOTSTRAP": "1",
                    "RUSTC_OVERRIDE_VERSION_STRING": "1.78.0-hostile",
                }
            )
            sysroot = subprocess.check_output(
                ["rustup", "run", tc, "rustc", "--print", "sysroot"],
                env=clean_env({"RUSTC_BOOTSTRAP": "1"}),
                text=True,
            ).strip()
            vv = subprocess.check_output(
                ["rustup", "run", tc, "rustc", "-vV"],
                env=clean_env({"RUSTC_BOOTSTRAP": "1"}),
                text=True,
            ).strip()
            headline = vv.splitlines()[0]
            sha_line = next((l.split(": ", 1)[1] for l in vv.splitlines() if l.startswith("commit-hash: ")), "")

            bin_out = Path(tmp) / f"driver_{idx}"
            comp = subprocess.run(
                [
                    f"{sysroot}/bin/rustc",
                    "--edition=2021",
                    "-D",
                    "warnings",
                    f"--check-cfg={check_cfg}",
                    "--cfg",
                    f'anneal_mir_dialect="{dialect}"',
                    "-L",
                    f"{sysroot}/lib",
                    f"-Clink-arg=-Wl,-rpath,{sysroot}/lib",
                    str(pkg_dir / "src" / "main.rs"),
                    "-o",
                    str(bin_out),
                ],
                env=env,
                text=True,
                capture_output=True,
            )
            exec_json = None
            exec_rc = None
            if comp.returncode == 0:
                run_p = subprocess.run(
                    [
                        str(bin_out),
                        "--crate-type=lib",
                        "--edition=2021",
                        "--sysroot",
                        sysroot,
                        str(sample_rs),
                        "--out-dir",
                        str(tmp),
                    ],
                    env=clean_env(),
                    text=True,
                    capture_output=True,
                )
                exec_rc = run_p.returncode
                if run_p.returncode == 0:
                    exec_json = json.loads(run_p.stdout.strip())
            proto_runs.append(
                {
                    "toolchain": tc,
                    "rustc_version": headline,
                    "commit_sha": sha_line,
                    "dialect": dialect,
                    "compile_rc": comp.returncode,
                    "exec_rc": exec_rc,
                    "captured_mir_metrics": exec_json,
                }
            )

        # Full `cargo build --offline` verification on `stable` (1.100.0) and `nightly` (1.102.0-nightly)
        for tc, dialect in [("stable", "mir_1_100"), ("nightly", "mir_1_102_nightly")]:
            sysroot = subprocess.check_output(
                ["rustup", "run", tc, "rustc", "--print", "sysroot"],
                env=clean_env({"RUSTC_BOOTSTRAP": "1"}),
                text=True,
            ).strip()
            target_dir = Path(tmp) / f"cargo_target_{tc}"
            rustflags = f'--cfg anneal_mir_dialect="{dialect}" -L {sysroot}/lib -Clink-arg=-Wl,-rpath,{sysroot}/lib -D warnings'
            c_env = clean_env(
                {
                    "RUSTC_BOOTSTRAP": "1",
                    "RUSTC": f"{sysroot}/bin/rustc",
                    "RUSTFLAGS": rustflags,
                }
            )
            cp = subprocess.run(
                [
                    f"{sysroot}/bin/cargo",
                    "build",
                    "--offline",
                    "--manifest-path",
                    str(pkg_dir / "Cargo.toml"),
                    "--target-dir",
                    str(target_dir),
                ],
                env=c_env,
                text=True,
                capture_output=True,
            )
            built_bin = target_dir / "debug" / "anneal-multi-dialect-capture-proto"
            run_p = subprocess.run(
                [
                    str(built_bin),
                    "--crate-type=lib",
                    "--edition=2021",
                    "--sysroot",
                    sysroot,
                    str(sample_rs),
                    "--out-dir",
                    str(tmp),
                ],
                env=clean_env(),
                text=True,
                capture_output=True,
            )
            cargo_runs.append(
                {
                    "toolchain": tc,
                    "dialect": dialect,
                    "cargo_build_rc": cp.returncode,
                    "binary_exec_rc": run_p.returncode,
                    "captured_mir_metrics": json.loads(run_p.stdout.strip()) if run_p.returncode == 0 else None,
                }
            )

        # Negative fail-closed tests: (1) missing `--cfg`, (2) typoed `--cfg anneal_mir_dialect="mir_1_100_typo"`
        stable_sr = subprocess.check_output(
            ["rustup", "run", "stable", "rustc", "--print", "sysroot"],
            env=clean_env({"RUSTC_BOOTSTRAP": "1"}),
            text=True,
        ).strip()
        for label, extra_cfg in [
            ("missing_dialect_cfg", []),
            ("typo_dialect_cfg", ["--cfg", 'anneal_mir_dialect="mir_1_100_typo"']),
        ]:
            np = subprocess.run(
                [
                    f"{stable_sr}/bin/rustc",
                    "--edition=2021",
                    f"--check-cfg={check_cfg}",
                    *extra_cfg,
                    str(pkg_dir / "src" / "main.rs"),
                    "--crate-type=bin",
                    "--emit=metadata",
                    "-o",
                    os.path.join(tmp, "neg.rmeta"),
                ],
                env=clean_env({"RUSTC_BOOTSTRAP": "1"}),
                text=True,
                capture_output=True,
            )
            errs = [l.strip() for l in np.stderr.splitlines() if "error" in l]
            negative_guard_runs.append({"case": label, "rc": np.returncode, "errors": errs})

    return {
        "cfg_version_truth_table": cfg_version_results,
        "cfg_version_override_spoofing": spoof_results,
        "cfg_version_midcycle_rustc_private_probes": midcycle_probes,
        "cfg_version_assume_incomplete_release_probes": assume_incomplete_probes,
        "cfg_accessible_matrix": cfg_accessible_results,
        "explicit_dialect_10_compiler_runs": proto_runs,
        "explicit_dialect_cargo_builds": cargo_runs,
        "explicit_dialect_fail_closed_guards": negative_guard_runs,
        "prototype_loc": {
            "dialect_rs_total_lines": len(DIALECT_RS.splitlines()),
            "dialect_rs_non_empty_non_comment_loc": sum(
                1 for l in DIALECT_RS.splitlines() if l.strip() and not l.strip().startswith("//")
            ),
            "main_rs_total_lines": len(MAIN_RS.splitlines()),
            "main_rs_non_empty_non_comment_loc": sum(
                1 for l in MAIN_RS.splitlines() if l.strip() and not l.strip().startswith("//")
            ),
        },
    }



CFG_ACCESSIBLE_GLOB_SHADOW_CASES = {
    "type_path_rustc_abi": """#![feature(rustc_private, cfg_accessible)]
#![allow(dead_code)]
extern crate rustc_driver;
extern crate rustc_abi;
#[cfg_accessible(rustc_abi::Size)]
const WITNESS: bool = true;
fn main() { println!("compiled"); }
""",
    "negated_cfg_accessible_invalid": """#![feature(rustc_private, cfg_accessible)]
extern crate rustc_driver;
#[cfg(not(cfg_accessible(rustc_driver::run_compiler)))]
fn check() -> bool { false }
fn main() {}
""",
    "fn_compiler_entrypoint": """#![feature(rustc_private, cfg_accessible)]
#![allow(dead_code)]
extern crate rustc_driver;
mod fallback { pub const PRESENT: bool = false; }
mod probe {
    pub use super::fallback::*;
    #[cfg_accessible(rustc_driver::compiler_entrypoint)]
    pub const PRESENT: bool = true;
}
fn main() { println!("present={}", probe::PRESENT); }
""",
    "enum_variant_retag": """#![feature(rustc_private, cfg_accessible)]
#![allow(dead_code)]
extern crate rustc_driver;
extern crate rustc_middle;
mod fallback { pub const PRESENT: bool = false; }
mod probe {
    pub use super::fallback::*;
    #[cfg_accessible(rustc_middle::mir::StatementKind::Retag)]
    pub const PRESENT: bool = true;
}
fn main() { println!("present={}", probe::PRESENT); }
""",
    "enum_variant_box_deref_transmute": """#![feature(rustc_private, cfg_accessible)]
#![allow(dead_code)]
extern crate rustc_driver;
extern crate rustc_middle;
mod fallback { pub const PRESENT: bool = false; }
mod probe {
    pub use super::fallback::*;
    #[cfg_accessible(rustc_middle::mir::CastKind::BoxDerefTransmute)]
    pub const PRESENT: bool = true;
}
fn main() { println!("present={}", probe::PRESENT); }
""",
    "enum_struct_field_loop_hint_attrs": """#![feature(rustc_private, cfg_accessible)]
#![allow(dead_code)]
extern crate rustc_driver;
extern crate rustc_middle;
mod fallback { pub const PRESENT: bool = false; }
mod probe {
    pub use super::fallback::*;
    #[cfg_accessible(rustc_middle::mir::TerminatorKind::Goto::loop_hint_attrs)]
    pub const PRESENT: bool = true;
}
fn main() { println!("present={}", probe::PRESENT); }
""",
}

MULTI_ERA_CAPABILITY_DRIVER_RS = r"""#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;

use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def::DefKind;
use rustc_interface::interface::Compiler;
use rustc_middle::mir::{Rvalue, StatementKind, TerminatorKind};
use rustc_middle::ty::TyCtxt;

struct TrunkCapture;

#[cfg(dialect_use_has_with_retag)]
fn classify_rvalue(rv: &Rvalue<'_>) -> (&'static str, bool) {
    match rv {
        Rvalue::Use(_, wr) => ("Use", format!("{wr:?}") == "Yes"),
        Rvalue::BinaryOp(_, _) => ("BinaryOp", false),
        Rvalue::Ref(_, _, _) => ("Ref", false),
        _ => ("Other", false),
    }
}

#[cfg(not(dialect_use_has_with_retag))]
fn classify_rvalue(rv: &Rvalue<'_>) -> (&'static str, bool) {
    match rv {
        Rvalue::Use(_) => ("Use", false),
        Rvalue::BinaryOp(_, _) => ("BinaryOp", false),
        Rvalue::Ref(_, _, _) => ("Ref", false),
        _ => ("Other", false),
    }
}

#[cfg(dialect_has_stmt_retag)]
fn is_stmt_retag(kind: &StatementKind<'_>) -> bool {
    matches!(kind, StatementKind::Retag(_, _))
}

#[cfg(not(dialect_has_stmt_retag))]
fn is_stmt_retag(_kind: &StatementKind<'_>) -> bool {
    false
}

fn classify_terminator(kind: &TerminatorKind<'_>) -> &'static str {
    match kind {
        TerminatorKind::Goto { target: _, .. } => "Goto",
        TerminatorKind::Return => "Return",
        TerminatorKind::SwitchInt { .. } => "SwitchInt",
        TerminatorKind::Assert { .. } => "Assert",
        TerminatorKind::Call { .. } => "Call",
        _ => "OtherTerm",
    }
}

impl Callbacks for TrunkCapture {
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        if tcx.dcx().has_errors().is_some() {
            return Compilation::Stop;
        }
        let ver = rustc_interface::util::rustc_version_str().unwrap_or("unknown");
        let crate_count = tcx.crates(()).len();
        let mut fn_summaries = Vec::new();
        for local_def in tcx.hir_body_owners() {
            if matches!(tcx.def_kind(local_def), DefKind::Fn | DefKind::AssocFn) {
                let name = tcx.def_path_str(local_def);
                let body = tcx.mir_drops_elaborated_and_const_checked(local_def).borrow();
                let mut assign_cnt = 0usize;
                let mut retag_cnt = 0usize;
                let mut terms = Vec::new();
                for bb in body.basic_blocks.iter() {
                    for stmt in &bb.statements {
                        if is_stmt_retag(&stmt.kind) {
                            retag_cnt += 1;
                        }
                        if let StatementKind::Assign(pair) = &stmt.kind {
                            let (_, rv) = &**pair;
                            assign_cnt += 1;
                            let (_, wr) = classify_rvalue(rv);
                            if wr {
                                retag_cnt += 1;
                            }
                        }
                    }
                    if let Some(term) = &bb.terminator {
                        terms.push(classify_terminator(&term.kind));
                    }
                }
                fn_summaries.push(format!(
                    "{{\"fn\":\"{}\",\"bbs\":{},\"assigns\":{},\"retags\":{},\"terms\":{:?}}}",
                    name,
                    body.basic_blocks.len(),
                    assign_cnt,
                    retag_cnt,
                    terms
                ));
            }
        }
        fn_summaries.sort();
        println!(
            "TRUNK_JSON={{\"rustc_version_str\":\"{}\",\"used_crates\":{},\"bodies\":[{}]}}",
            ver,
            crate_count,
            fn_summaries.join(",")
        );
        Compilation::Continue
    }
}

#[cfg(dialect_entrypoint_fn)]
fn invoke_driver(args: &[String], cb: &mut TrunkCapture) {
    rustc_driver::compiler_entrypoint(args, cb);
}

#[cfg(all(not(dialect_entrypoint_fn), dialect_run_compiler_fn))]
fn invoke_driver(args: &[String], cb: &mut TrunkCapture) {
    rustc_driver::run_compiler(args, cb);
}

#[cfg(all(not(dialect_entrypoint_fn), not(dialect_run_compiler_fn)))]
fn invoke_driver(args: &[String], cb: &mut TrunkCapture) {
    let _ = rustc_driver::RunCompiler::new(args, cb).run();
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mut cb = TrunkCapture;
    invoke_driver(&args, &mut cb);
}
"""

SAMPLE_CAPABILITY_TARGET_RS = """
pub fn clamp_u32(x: u32, lo: u32, hi: u32) -> u32 {
    if x < lo {
        lo
    } else if x > hi {
        hi
    } else {
        x
    }
}

pub fn borrow_roundtrip(r: &mut u32) -> u32 {
    *r = r.wrapping_add(1);
    *r
}
"""


def infer_capability_cfgs(vv_head: str, commit_date: str) -> list[str]:
    """Select capability `--cfg` flags from explicit compiler release/date metadata."""
    cfgs: list[str] = []
    # `Rvalue::Use(_, WithRetag)` replaced `StatementKind::Retag` on 2026-05-02 (rustc 1.97.0)
    m = re.search(r"rustc 1\.(\d+)\.(\d+)(?:-([a-z0-9.]+))?", vv_head)
    minor = int(m.group(1)) if m else 0
    chan = (m.group(3) or "stable") if m else "stable"
    if minor < 97 or (minor == 97 and chan == "nightly" and commit_date < "2026-05-02"):
        cfgs.append("--cfg=dialect_has_stmt_retag")
    else:
        cfgs.append("--cfg=dialect_use_has_with_retag")
    # `compiler_entrypoint` replaced `run_compiler` on 2026-10-02 (rustc 1.102.0-nightly)
    if minor >= 102 and commit_date >= "2026-10-02":
        cfgs.append("--cfg=dialect_entrypoint_fn")
    elif minor >= 86:
        cfgs.append("--cfg=dialect_run_compiler_fn")
    return cfgs


def run_part3_capability_sysroot_probe(extra_sysroots: list[str]) -> dict:
    """Run the single-file capability-flag driver & glob-shadowed cfg_accessible probe on explicit sysroots."""
    sysroots: list[tuple[str, str]] = []
    for spec in extra_sysroots:
        if "=" not in spec:
            raise ValueError(f"Expected LABEL=PATH for --extra-sysroot, got {spec!r}")
        lbl, path = spec.split("=", 1)
        sysroots.append((lbl, path))

    if not sysroots:
        # Discover installed rustc-dev sysroots from rustup without hardcoding workstation paths
        for tc in ["nightly-2026-02-07", "nightly-2026-04-12", "nightly-2026-05-31", "stable", "nightly"]:
            p = subprocess.run(
                ["rustup", "run", tc, "rustc", "--print", "sysroot"],
                env=clean_env({"RUSTC_BOOTSTRAP": "1"}),
                text=True,
                capture_output=True,
            )
            if p.returncode == 0:
                sr = p.stdout.strip()
                if (Path(sr) / "lib" / "rustlib").exists():
                    sysroots.append((tc, sr))

    env = clean_env({"RUSTC_BOOTSTRAP": "1"})
    for k in ["DYLD_LIBRARY_PATH", "RUSTC", "RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER"]:
        env.pop(k, None)

    out: dict[str, object] = {"cfg_accessible": {}, "seven_era_driver": []}
    with tempfile.TemporaryDirectory() as tmp_str:
        tmp = Path(tmp_str)
        for cname, csrc in CFG_ACCESSIBLE_GLOB_SHADOW_CASES.items():
            cfile = tmp / f"ca_{cname}.rs"
            cfile.write_text(csrc, encoding="utf-8")
            per_sr: dict[str, object] = {}
            for lbl, sr in sysroots:
                rustc = Path(sr) / "bin" / "rustc"
                bpath = tmp / f"ca_{cname}_{lbl}"
                cp = subprocess.run(
                    [
                        str(rustc),
                        "--edition=2021",
                        "--sysroot",
                        sr,
                        "-L",
                        f"{sr}/lib",
                        f"-Clink-arg=-Wl,-rpath,{sr}/lib",
                        str(cfile),
                        "-o",
                        str(bpath),
                    ],
                    env=env,
                    capture_output=True,
                    text=True,
                )
                entry: dict[str, object] = {"rc": cp.returncode}
                if cp.returncode == 0:
                    rp = subprocess.run([str(bpath)], env=env, capture_output=True, text=True)
                    entry["stdout"] = rp.stdout.strip()
                else:
                    entry["stderr_head"] = [
                        re.sub(r"/tmp/tmp[a-zA-Z0-9_]+", "/tmp/<scratch>", l)
                        for l in cp.stderr.splitlines()
                        if l.strip()
                    ][:4]
                per_sr[lbl] = entry
            out["cfg_accessible"][cname] = per_sr

        drv_rs = tmp / "multi_era_driver.rs"
        drv_rs.write_text(MULTI_ERA_CAPABILITY_DRIVER_RS, encoding="utf-8")
        sample_rs = tmp / "sample_target.rs"
        sample_rs.write_text(SAMPLE_CAPABILITY_TARGET_RS, encoding="utf-8")

        driver_runs: list[dict[str, object]] = []
        for lbl, sr in sysroots:
            rustc = Path(sr) / "bin" / "rustc"
            vv_lines = subprocess.run(
                [str(rustc), "-vV"], env=env, capture_output=True, text=True, check=True
            ).stdout.strip().splitlines()
            vv_head = vv_lines[0]
            cdate = next((l.split(": ", 1)[1] for l in vv_lines if l.startswith("commit-date: ")), "9999-99-99")
            cfgs = infer_capability_cfgs(vv_head, cdate)
            drv_bin = tmp / f"driver_{lbl}"
            t0 = time.monotonic()
            cp = subprocess.run(
                [
                    str(rustc),
                    "--edition=2021",
                    "-O",
                    "--sysroot",
                    sr,
                    "-L",
                    f"{sr}/lib",
                    f"-Clink-arg=-Wl,-rpath,{sr}/lib",
                    *cfgs,
                    str(drv_rs),
                    "-o",
                    str(drv_bin),
                ],
                env=env,
                capture_output=True,
                text=True,
            )
            compile_ms = round((time.monotonic() - t0) * 1000.0, 1)
            rec: dict[str, object] = {
                "toolchain": lbl,
                "vv_head": vv_head,
                "cfgs": cfgs,
                "compile_rc": cp.returncode,
                "compile_ms": compile_ms,
            }
            if cp.returncode == 0:
                rec["binary_bytes"] = drv_bin.stat().st_size
                out_rlib = tmp / f"libsample_{lbl}.rlib"
                rp = subprocess.run(
                    [
                        str(drv_bin),
                        "--edition=2021",
                        "--crate-type=lib",
                        "--sysroot",
                        sr,
                        "-Zmir-preserve-ub",
                        "-Copt-level=2",
                        str(sample_rs),
                        "-o",
                        str(out_rlib),
                    ],
                    env=env,
                    capture_output=True,
                    text=True,
                )
                rec["run_rc"] = rp.returncode
                trunk_lines = [
                    l.removeprefix("TRUNK_JSON=")
                    for l in rp.stdout.splitlines()
                    if l.startswith("TRUNK_JSON=")
                ]
                if trunk_lines:
                    rec["trunk_json"] = json.loads(trunk_lines[0])
            else:
                rec["compile_err"] = cp.stderr.splitlines()[:10]
            driver_runs.append(rec)
        out["seven_era_driver"] = driver_runs
    return out


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--repo-url",
        default="https://github.com/rust-lang/rust.git",
        help="Git URL or local repository path for rust-lang/rust blobless clone",
    )
    parser.add_argument(
        "--census-only",
        action="store_true",
        help="Run only Part 1 (24-revision Git scaling census)",
    )
    parser.add_argument(
        "--matrix-only",
        action="store_true",
        help="Run only Parts 2 and 3 (live rustc_private conditional-compilation matrices)",
    )
    parser.add_argument(
        "--extra-sysroot",
        action="append",
        default=[],
        metavar="LABEL=PATH",
        help="Explicit rustc+rustc-dev sysroot(s) for Part 3 capability-flag driver probe",
    )
    parser.add_argument(
        "--out",
        default=str(Path(__file__).with_name("probe_mir_scaling_and_cfg_matrix.json")),
        help="Path to write JSON output",
    )
    args = parser.parse_args()

    payload: dict[str, object] = {
        "schema": "rustc-mir-scaling-and-cfg-matrix-v1",
        "generated_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    }
    if not args.matrix_only:
        payload["part1_four_tier_scaling_census"] = run_part1_git_census(args.repo_url)
    if not args.census_only:
        payload["part2_multi_version_rustc_private_matrix"] = run_part2_live_matrix()
        payload["part3_seven_era_capability_driver_and_glob_shadowing"] = (
            run_part3_capability_sysroot_probe(args.extra_sysroot)
        )

    out_path = Path(args.out)
    out_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {out_path} ({out_path.stat().st_size} bytes)")


if __name__ == "__main__":
    main()
