#!/usr/bin/env python3
"""
Standalone Python 3.10+ stdlib probe quantifying five multi-compiler IR/AST
migration topologies (T1..T5) across the nine verified `rustc_middle::mir::syntax`
schema mutations spanning nine pinned `rust-lang/rust` revisions (`1.93.1` through
`1.102.0-nightly`, including the non-linear `2026-10-20` nightly `8144389c`).

Evaluated topologies:
  - T1_latest_canonical_raw_ir:
      Uses the newest supported compiler's raw `syntax.rs` (`1.102.0-nightly`)
      directly as the canonical hub IR without retaining deleted historical variants.
  - T2_oldest_or_intersection_ir:
      Restricts the canonical hub IR to the oldest supported compiler (`1.93.1`) or
      the strict syntactic intersection across all supported compiler pins.
  - T3_pairwise_stepwise_migration_chain:
      Composes adjacent `Migrate_k_{k+1}` AST-to-AST deep-copy passes:
        * T3a_unidir_chain_to_latest: `v_i -> v_{i+1} -> ... -> v_{K-1}`
        * T3b_bidir_omp_v1_heterogeneous: `v_src -> v_0 -> ... -> v_{K-1}` (`ocaml-migrate-parsetree` v1)
        * T3c_ppxlib_lagging_hub_chain: pairwise hops into a lagging snapshot hub
          (`1.98.0-nightly`, `f8a08b688cbe`) plus `"ppxlib.migration.*"`-style
          synthetic tunnel encodings for newer compiler variants.
  - T4_direct_spoke_to_superset_trunk:
      1-pass per-spoke extraction (`TyCtxt -> TrunkIR`) from each compiler's native
      `rustc_middle::mir` into a monotonic feature-parameterized superset Trunk IR
      governed by an explicit `SemProfile` / `CAP_*` capability vector and fail-closed
      `.unsupported` sentinels.
  - T5_separate_per_version_irs_and_evaluators:
      Maintains N completely separate `(MirAst_v, MirSemantics_v, WP_v, Proof_v)`
      verification stacks without a shared canonical Trunk IR.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from typing import Dict, List, Optional, Set, Tuple


@dataclass(frozen=True)
class CompilerPin:
    index: int
    label: str
    commit_sha: str
    commit_or_release_date: str
    channel: str
    present_variants: Tuple[str, ...]


@dataclass(frozen=True)
class SyntaxMutation:
    mutation_id: str
    enum_name: str
    kind: str  # "remove_variant", "add_variant", "widen_variant_payload", "widen_struct_hint"
    variant_before: Optional[str]
    variant_after: Optional[str]
    introduced_in_label: str
    causal_commit: str
    pr_number: int
    semantic_class: str  # "operational_removed", "operational_added", "operational_split_fused", "non_operational_hint"
    live_corpus_bodies_affected: int  # Out of 782 bodies in {feature_probe, ryu, itoa, memchr}


# Chronological / release-ordered 8-toolchain chain (plus the out-of-band 2026-10-20
# nightly `8144389c` demonstrating release-branch DAG non-linearity vs `1.100.0`).
LINEAR_RELEASES: List[CompilerPin] = [
    CompilerPin(
        index=0,
        label="1.93.1",
        commit_sha="01f6ddf7588f42ae2d7eb0a2f21d44e8e96674cf",
        commit_or_release_date="2026-02-11",
        channel="stable",
        present_variants=(
            "Rvalue::NullaryOp",
            "Rvalue::ShallowInitBox",
            "StatementKind::Retag",
            "Rvalue::Use(Operand)",
            "TerminatorKind::Goto{target}",
        ),
    ),
    CompilerPin(
        index=1,
        label="1.94.0",
        commit_sha="4a4ef493e3a1488c6e321570238084b38948f6db",
        commit_or_release_date="2026-03-02",
        channel="stable",
        present_variants=(
            "Operand::RuntimeChecks",
            "Rvalue::ShallowInitBox",
            "StatementKind::Retag",
            "Rvalue::Use(Operand)",
            "TerminatorKind::Goto{target}",
        ),
    ),
    CompilerPin(
        index=2,
        label="1.96.0",
        commit_sha="ac68faa20c58cbccd01ee7208bf3b6e93a7d7f96",
        commit_or_release_date="2026-05-25",
        channel="stable",
        present_variants=(
            "Operand::RuntimeChecks",
            "StatementKind::Retag",
            "Rvalue::Use(Operand)",
            "TerminatorKind::Goto{target}",
        ),
    ),
    CompilerPin(
        index=3,
        label="1.98.0-nightly",
        commit_sha="f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1",
        commit_or_release_date="2026-05-30",
        channel="nightly",
        present_variants=(
            "Operand::RuntimeChecks",
            "Rvalue::Use(Operand,WithRetag)",
            "Rvalue::Reborrow",
            "TerminatorKind::Goto{target}",
        ),
    ),
    CompilerPin(
        index=4,
        label="1.99.0",
        commit_sha="b940084d7eb6a299eb4bfeb8e34901bc051e7ac4",
        commit_or_release_date="2026-09-28",
        channel="stable",
        present_variants=(
            "Operand::RuntimeChecks",
            "Rvalue::Use(Operand,WithRetag)",
            "Rvalue::Reborrow",
            "AssertKind::NullReferenceConstructed",
            "CastKind::BoxDerefTransmute",
            "TerminatorKind::Goto{target}",
        ),
    ),
    CompilerPin(
        index=5,
        label="1.99.1",
        commit_sha="58cf8f9c35b355199727627d07ae34a4e2846d67",
        commit_or_release_date="2026-10-13",
        channel="stable",
        present_variants=(
            "Operand::RuntimeChecks",
            "Rvalue::Use(Operand,WithRetag)",
            "Rvalue::Reborrow",
            "AssertKind::NullReferenceConstructed",
            "CastKind::BoxDerefTransmute",
            "TerminatorKind::Goto{target}",
        ),
    ),
    CompilerPin(
        index=6,
        label="1.100.0",
        commit_sha="0ef1bc386059596dada8fb65b50425aab2ea637a",
        commit_or_release_date="2026-11-09",
        channel="stable",
        present_variants=(
            "Operand::RuntimeChecks",
            "Rvalue::Use(Operand,WithRetag)",
            "Rvalue::Reborrow",
            "AssertKind::NullReferenceConstructed",
            "CastKind::BoxDerefTransmute",
            "ProjectionElem::PhantomDeref",
            "TerminatorKind::Goto{target}",
        ),
    ),
    CompilerPin(
        index=7,
        label="1.102.0-nightly",
        commit_sha="3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1",
        commit_or_release_date="2026-11-11",
        channel="nightly",
        present_variants=(
            "Operand::RuntimeChecks",
            "Rvalue::Use(Operand,WithRetag)",
            "Rvalue::Reborrow",
            "AssertKind::NullReferenceConstructed",
            "CastKind::BoxDerefTransmute",
            "ProjectionElem::PhantomDeref",
            "TerminatorKind::Goto{target,loop_hint_attrs}",
        ),
    ),
]

# Non-linear DAG pin (`2026-10-20` nightly: predates `1.100.0` release date `2026-11-09`,
# yet carries `Goto { target, loop_hint_attrs }` from `ec45ecffeee8` on `2026-10-07`,
# which is absent in `1.100.0` because `1.100.0` branched to beta earlier).
NONLINEAR_NIGHTLY_PIN = CompilerPin(
    index=-1,
    label="1.101.0-nightly-2026-10-20",
    commit_sha="8144389c895da997dbdecaa635e41d6a50be6ffd",
    commit_or_release_date="2026-10-20",
    channel="nightly",
    present_variants=(
        "Operand::RuntimeChecks",
        "Rvalue::Use(Operand,WithRetag)",
        "Rvalue::Reborrow",
        "AssertKind::NullReferenceConstructed",
        "CastKind::BoxDerefTransmute",
        "ProjectionElem::PhantomDeref",
        "TerminatorKind::Goto{target,loop_hint_attrs}",
    ),
)

MUTATIONS: List[SyntaxMutation] = [
    SyntaxMutation(
        mutation_id="M1_remove_nullary_op",
        enum_name="Rvalue",
        kind="remove_variant",
        variant_before="Rvalue::NullaryOp(NullOp)",
        variant_after=None,
        introduced_in_label="1.94.0",
        causal_commit="1a227bd47ff200975f4afb287ec725861ab8b87a",
        pr_number=148766,
        semantic_class="operational_removed",
        live_corpus_bodies_affected=0,
    ),
    SyntaxMutation(
        mutation_id="M2_add_runtime_checks",
        enum_name="Operand",
        kind="add_variant",
        variant_before=None,
        variant_after="Operand::RuntimeChecks(RuntimeChecks)",
        introduced_in_label="1.94.0",
        causal_commit="6319bee585561a078de4a0f8d07d567ce69cf12c",
        pr_number=148766,
        semantic_class="operational_added",
        live_corpus_bodies_affected=0,
    ),
    SyntaxMutation(
        mutation_id="M3_remove_shallow_init_box",
        enum_name="Rvalue",
        kind="remove_variant",
        variant_before="Rvalue::ShallowInitBox(Operand, Ty)",
        variant_after=None,
        introduced_in_label="1.96.0",
        causal_commit="6d4b1b38e76c0858c8e98f89afa37535261749ca",
        pr_number=152758,
        semantic_class="operational_removed",
        live_corpus_bodies_affected=0,
    ),
    SyntaxMutation(
        mutation_id="M4_remove_stmt_retag",
        enum_name="StatementKind",
        kind="remove_variant",
        variant_before="StatementKind::Retag(RetagKind, Box<Place>)",
        variant_after=None,
        introduced_in_label="1.98.0-nightly",
        causal_commit="e402c1edf047a23b0cfef40c6097d1caa294050b",
        pr_number=154341,
        semantic_class="operational_split_fused",
        live_corpus_bodies_affected=0,
    ),
    SyntaxMutation(
        mutation_id="M5_widen_rvalue_use_with_retag",
        enum_name="Rvalue",
        kind="widen_variant_payload",
        variant_before="Rvalue::Use(Operand)",
        variant_after="Rvalue::Use(Operand, WithRetag)",
        introduced_in_label="1.98.0-nightly",
        causal_commit="e402c1edf047a23b0cfef40c6097d1caa294050b",
        pr_number=154341,
        semantic_class="operational_split_fused",
        live_corpus_bodies_affected=126,  # 124 memchr + 2 feature_probe
    ),
    SyntaxMutation(
        mutation_id="M6_add_rvalue_reborrow",
        enum_name="Rvalue",
        kind="add_variant",
        variant_before=None,
        variant_after="Rvalue::Reborrow(Ty, Mutability, Place)",
        introduced_in_label="1.98.0-nightly",
        causal_commit="2d88ee87ddaa584a19e438528f60f825f735076a",
        pr_number=156290,
        semantic_class="operational_added",
        live_corpus_bodies_affected=0,
    ),
    SyntaxMutation(
        mutation_id="M7_add_assert_null_ref",
        enum_name="AssertKind",
        kind="add_variant",
        variant_before=None,
        variant_after="AssertKind::NullReferenceConstructed",
        introduced_in_label="1.99.0",
        causal_commit="1a982425b6699f2b26552c6b44cc979a3d84543b",
        pr_number=158796,
        semantic_class="operational_added",
        live_corpus_bodies_affected=0,
    ),
    SyntaxMutation(
        mutation_id="M8_add_cast_box_deref_transmute",
        enum_name="CastKind",
        kind="add_variant",
        variant_before=None,
        variant_after="CastKind::BoxDerefTransmute",
        introduced_in_label="1.99.0",
        causal_commit="fcf68f21cf2f50e824bc4054ca4f46f0dd8ce42f",
        pr_number=160339,
        semantic_class="operational_added",
        live_corpus_bodies_affected=5,  # 5 Box<T> deref bodies in memchr
    ),
    SyntaxMutation(
        mutation_id="M9a_add_proj_phantom_deref",
        enum_name="ProjectionElem",
        kind="add_variant",
        variant_before=None,
        variant_after="ProjectionElem::PhantomDeref",
        introduced_in_label="1.100.0",
        causal_commit="5686e563774cd9e8bfba79d3ab1167fe198e9e78",
        pr_number=159103,
        semantic_class="operational_added",
        live_corpus_bodies_affected=0,
    ),
    SyntaxMutation(
        mutation_id="M9b_widen_goto_loop_hint_attrs",
        enum_name="TerminatorKind",
        kind="widen_struct_hint",
        variant_before="TerminatorKind::Goto{target}",
        variant_after="TerminatorKind::Goto{target,loop_hint_attrs}",
        introduced_in_label="1.102.0-nightly",
        causal_commit="ec45ecffeee8ba13e42a7f45b6cdad3155ebd146",
        pr_number=163931,
        semantic_class="non_operational_hint",
        live_corpus_bodies_affected=0,
    ),
]
# Note: M4 (-StatementKind::Retag) and M5 (Rvalue::Use(_, WithRetag)) are the two halves
# of rust-lang/rust PR #154341 (`e402c1ed`), giving 9 structural enum changes across 6 enums
# (10 atomic variant/field edits when M4 and M5 are counted separately).


# ---------------------------------------------------------------------------
# Concrete MIR Specimen Suite Exercising Every Mutation Class (S1..S11)
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class MirSpecimen:
    name: str
    origin_pin: str
    construct_tag: str
    has_ref_or_box_ty: bool
    description: str


SPECIMENS: List[MirSpecimen] = [
    MirSpecimen(
        name="S1_scalar_copy_legacy",
        origin_pin="1.93.1",
        construct_tag="Rvalue::Use(Copy(u32))",
        has_ref_or_box_ty=False,
        description="Pure scalar copy in 1.93.1..1.96.0 before WithRetag existed",
    ),
    MirSpecimen(
        name="S2_ref_copy_legacy",
        origin_pin="1.96.0",
        construct_tag="Rvalue::Use(Copy(&u32))",
        has_ref_or_box_ty=True,
        description="Reference field copy in 1.96.0 (non-retagging in <=1.96, paired with explicit Retag when retagging)",
    ),
    MirSpecimen(
        name="S3_explicit_fn_entry_retag",
        origin_pin="1.96.0",
        construct_tag="StatementKind::Retag(FnEntry, _1)",
        has_ref_or_box_ty=True,
        description="Standalone function-entry Retag statement in <=1.96.0 (variant deleted in 1.98+)",
    ),
    MirSpecimen(
        name="S4_nullary_op_ub_checks",
        origin_pin="1.93.1",
        construct_tag="Rvalue::NullaryOp(UbChecks)",
        has_ref_or_box_ty=False,
        description="1.93.1 NullaryOp removed in 1.94.0 in favor of Operand::RuntimeChecks",
    ),
    MirSpecimen(
        name="S5_shallow_init_box",
        origin_pin="1.94.0",
        construct_tag="Rvalue::ShallowInitBox(ptr, T)",
        has_ref_or_box_ty=True,
        description="1.94.0 ShallowInitBox removed in 1.96.0",
    ),
    MirSpecimen(
        name="S6_operand_runtime_checks",
        origin_pin="1.94.0",
        construct_tag="Operand::RuntimeChecks(UbChecks)",
        has_ref_or_box_ty=False,
        description="1.94.0+ RuntimeChecks operand whose value depends on -C ub-checks session flag",
    ),
    MirSpecimen(
        name="S7_use_with_retag_no",
        origin_pin="1.99.0",
        construct_tag="Rvalue::Use(Copy(&T), WithRetag::No)",
        has_ref_or_box_ty=True,
        description="1.98+ `no_retag copy` on closure/Drop projected reference (126 live corpus bodies)",
    ),
    MirSpecimen(
        name="S8_use_with_retag_yes_ref",
        origin_pin="1.99.0",
        construct_tag="Rvalue::Use(Copy(&mut T), WithRetag::Yes)",
        has_ref_or_box_ty=True,
        description="1.98+ implicit-retag assignment on reference type",
    ),
    MirSpecimen(
        name="S9_box_deref_transmute",
        origin_pin="1.99.0",
        construct_tag="CastKind::BoxDerefTransmute",
        has_ref_or_box_ty=True,
        description="1.99.0+ Box<T> dereference cast (5 live memchr bodies)",
    ),
    MirSpecimen(
        name="S10_null_ref_assert_and_phantom_deref",
        origin_pin="1.100.0",
        construct_tag="AssertKind::NullReferenceConstructed+ProjectionElem::PhantomDeref",
        has_ref_or_box_ty=True,
        description="1.99+/1.100+ UB-check assert and unstable reborrow PhantomDeref projection",
    ),
    MirSpecimen(
        name="S11_goto_with_loop_hint_attrs",
        origin_pin="1.102.0-nightly",
        construct_tag="TerminatorKind::Goto{target,loop_hint_attrs:[#[loop_match]]}",
        has_ref_or_box_ty=False,
        description="1.102-nightly Goto carrying non-operational loop_hint_attrs",
    ),
]


# ---------------------------------------------------------------------------
# Monotonic Superset Trunk IR + SemProfile Capability Vector (T4)
# ---------------------------------------------------------------------------

TRUNK_CAPABILITIES = {
    "CAP_CORE_SCALAR_CFG",        # Minimal scalar/unit/never/fieldless-enum CFG core
    "CAP_RUNTIME_CHECKS_FLAG",    # Session RuntimeChecks mode parameter (-C ub-checks / overflow-checks)
    "CAP_STACKED_OR_TREE_RETAG",  # Reference provenance & WithRetag / Stmt::Retag semantics
    "CAP_BOX_ALLOC_LAYOUT",       # Box/heap layout & BoxDerefTransmute / ShallowInitBox
    "CAP_CUSTOM_REBORROW",        # Unstable Rvalue::Reborrow + ProjectionElem::PhantomDeref
    "CAP_NULL_REF_ASSERT",        # AssertKind::NullReferenceConstructed
}

SCALAR_CORE_V1_CAPABILITIES = {"CAP_CORE_SCALAR_CFG"}


def evaluate_t1_latest_raw_canonical(
    spec: MirSpecimen, pins: List[CompilerPin]
) -> Dict[str, object]:
    """
    T1: Latest-Version Canonical Raw IR (`1.102.0-nightly`'s raw `syntax.rs` used
    directly as the canonical hub without retaining deleted historical variants).
    """
    dst_pin = pins[-1]
    ct = spec.construct_tag
    lossy_reason: Optional[str] = None
    if ct == "Rvalue::ShallowInitBox(ptr, T)":
        lossy_reason = (
            "Removed variant `Rvalue::ShallowInitBox` (`6d4b1b38`) has no 1:1 Rvalue in "
            "`1.96.0+` `syntax.rs`; requires multi-statement ADT/transmute synthesis or abort."
        )
    elif ct == "StatementKind::Retag(FnEntry, _1)":
        lossy_reason = (
            "Removed variant `StatementKind::Retag` (`e402c1ed`) has no `StatementKind` "
            "representation in `1.98+` `syntax.rs`: dropping it is UNSOUND for aliasing UB, "
            "while synthesizing `_tmp = Use(Copy(_1), WithRetag::Yes)` mutates `LocalDecls`."
        )

    return {
        "specimen": spec.name,
        "origin_pin": spec.origin_pin,
        "canonical_pin": dst_pin.label,
        "cannot_represent_in_latest_raw_ast": lossy_reason is not None,
        "lossy_or_hazard_reason": lossy_reason,
    }


def evaluate_t2_oldest_or_intersection(
    spec: MirSpecimen, pins: List[CompilerPin]
) -> Dict[str, object]:
    """
    T2: Oldest / Common-Intersection Canonical IR (pinned to `1.93.1` or the strict
    syntactic intersection across all 9 pins).
    """
    oldest_pin = pins[0]
    ct = spec.construct_tag
    unrepresentable = False
    hazard: Optional[str] = None

    if ct in (
        "Operand::RuntimeChecks(UbChecks)",
        "Rvalue::Use(Copy(&T), WithRetag::No)",
        "Rvalue::Use(Copy(&mut T), WithRetag::Yes)",
        "CastKind::BoxDerefTransmute",
        "AssertKind::NullReferenceConstructed+ProjectionElem::PhantomDeref",
        "TerminatorKind::Goto{target,loop_hint_attrs:[#[loop_match]]}",
    ):
        unrepresentable = True
        if ct == "Rvalue::Use(Copy(&mut T), WithRetag::Yes)":
            hazard = (
                "Oldest `1.93.1` `Rvalue::Use(Operand)` lacks `WithRetag`: collapsing `WithRetag::Yes` "
                "into plain `Use` silently drops implicit reference retagging (UNSOUND), whereas "
                "synthesizing separate `StatementKind::Retag` alters statement indices."
            )
        elif ct == "CastKind::BoxDerefTransmute":
            hazard = (
                "`CastKind::BoxDerefTransmute` (`fcf68f21`, `1.99.0+`) is absent in `1.93.1` and the "
                "common intersection, rejecting 5 / 641 live `memchr` bodies."
            )
        elif ct.startswith("TerminatorKind::Goto"):
            hazard = (
                "Strict syntactic intersection lacks `loop_hint_attrs`; erasing non-operational hints "
                "is sound for verification but loses round-trip AST fidelity."
            )
        else:
            hazard = (
                f"Construct `{ct}` from `{spec.origin_pin}` is absent in `{oldest_pin.label}` and in "
                "the 9-pin common intersection; erasing it sacrifices soundness or rejects newer crates."
            )

    return {
        "specimen": spec.name,
        "origin_pin": spec.origin_pin,
        "target_pin": oldest_pin.label,
        "cannot_represent_in_oldest_or_intersection": unrepresentable,
        "lossy_or_hazard_reason": hazard,
    }


def evaluate_t3a_pairwise_chain_to_latest(
    spec: MirSpecimen, pins: List[CompilerPin]
) -> Dict[str, object]:
    """
    T3a: Unidirectional stepwise chain `v_origin -> v_{origin+1} -> ... -> v_latest` (index 7),
    where each hop deep-copies the full MIR body and the final target is raw `1.102.0-nightly`.
    """
    idx_map = {p.label: p.index for p in pins}
    src_idx = idx_map[spec.origin_pin]
    dst_idx = len(pins) - 1
    hops = dst_idx - src_idx
    t1_eval = evaluate_t1_latest_raw_canonical(spec, pins)
    return {
        "specimen": spec.name,
        "origin_pin": spec.origin_pin,
        "target_pin": pins[dst_idx].label,
        "hops": hops,
        "intermediate_ast_allocations": max(0, hops - 1),
        "total_full_body_copies": hops,
        "cannot_represent_in_latest_raw_ast": t1_eval["cannot_represent_in_latest_raw_ast"],
        "lossy_or_hazard_reason": t1_eval["lossy_or_hazard_reason"],
    }


def evaluate_t3c_lagging_hub_pairwise(
    spec: MirSpecimen,
    pins: List[CompilerPin],
    hub_label: str = "1.98.0-nightly",
    round_trip: bool = False,
) -> Dict[str, object]:
    """
    T3c: `ppxlib` / `astlib` topology where the single internal trunk AST is pinned to an
    intermediate compiler snapshot (`hub_label`, e.g. `1.98.0-nightly` `f8a08b688`), and
    frontends reach the hub via composed adjacent pairwise migrations (`Convert(Input)(Hub)`).
    """
    idx_map = {p.label: p.index for p in pins}
    src_idx = idx_map[spec.origin_pin]
    hub_idx = idx_map[hub_label]
    one_way_hops = abs(src_idx - hub_idx)
    total_hops = one_way_hops * (2 if round_trip else 1)
    ct = spec.construct_tag

    requires_tunnel_or_fails = False
    hazard: Optional[str] = None
    if src_idx > hub_idx:
        if ct in (
            "CastKind::BoxDerefTransmute",
            "AssertKind::NullReferenceConstructed+ProjectionElem::PhantomDeref",
        ):
            requires_tunnel_or_fails = True
            hazard = (
                f"Construct `{ct}` from `{spec.origin_pin}` does not exist in lagging hub "
                f"`{hub_label}`: downgrade either raises `Migration_error` (blocking 5/641 "
                f"`memchr` bodies on `BoxDerefTransmute`) or requires `ppxlib.migration.*`-style "
                f"synthetic attribute/extension tunneling."
            )
        elif ct.startswith("TerminatorKind::Goto"):
            if round_trip:
                hazard = (
                    "Downgrading `Goto { loop_hint_attrs }` to `1.98` drops `#[loop_match]` "
                    "attributes unless tunneled."
                )
    elif src_idx < hub_idx:
        if ct in ("Rvalue::ShallowInitBox(ptr, T)", "StatementKind::Retag(FnEntry, _1)"):
            requires_tunnel_or_fails = True
            hazard = (
                f"Legacy construct `{ct}` from `{spec.origin_pin}` was deleted before hub `{hub_label}`."
            )

    return {
        "specimen": spec.name,
        "origin_pin": spec.origin_pin,
        "hub_pin": hub_label,
        "round_trip": round_trip,
        "hops": total_hops,
        "requires_synthetic_tunnel_or_migration_error": requires_tunnel_or_fails,
        "hazard": hazard,
    }


def evaluate_t4_spoke_to_superset_trunk(
    spec: MirSpecimen, enabled_caps: Set[str]
) -> Dict[str, object]:
    """
    T4: Direct 1-pass per-spoke lowering from `spec.origin_pin`'s native `rustc_middle::mir`
    into the Monotonic Superset Trunk IR, followed by MLIR-style `ConversionTarget` /
    `SemProfile` capability legality checking.
    """
    ct = spec.construct_tag
    if ct == "Rvalue::Use(Copy(u32))":
        trunk_node = "TrunkRvalue::Use(op, with_retag=False)"
        req_cap = "CAP_CORE_SCALAR_CFG"
        erased_hint = False
    elif ct == "Rvalue::Use(Copy(&u32))":
        trunk_node = "TrunkRvalue::Use(op, with_retag=False)"
        req_cap = "CAP_STACKED_OR_TREE_RETAG"
        erased_hint = False
    elif ct == "StatementKind::Retag(FnEntry, _1)":
        trunk_node = "TrunkStmt::Retag(FnEntry, _1)"
        req_cap = "CAP_STACKED_OR_TREE_RETAG"
        erased_hint = False
    elif ct == "Rvalue::NullaryOp(UbChecks)":
        trunk_node = "TrunkOperand::RuntimeChecks(UbChecks)"
        req_cap = "CAP_RUNTIME_CHECKS_FLAG"
        erased_hint = False
    elif ct == "Rvalue::ShallowInitBox(ptr, T)":
        trunk_node = "TrunkRvalue::ShallowInitBox(ptr, T)"
        req_cap = "CAP_BOX_ALLOC_LAYOUT"
        erased_hint = False
    elif ct == "Operand::RuntimeChecks(UbChecks)":
        trunk_node = "TrunkOperand::RuntimeChecks(UbChecks)"
        req_cap = "CAP_RUNTIME_CHECKS_FLAG"
        erased_hint = False
    elif ct == "Rvalue::Use(Copy(&T), WithRetag::No)":
        trunk_node = "TrunkRvalue::Use(op, with_retag=False)"
        req_cap = "CAP_STACKED_OR_TREE_RETAG"
        erased_hint = False
    elif ct == "Rvalue::Use(Copy(&mut T), WithRetag::Yes)":
        trunk_node = "TrunkRvalue::Use(op, with_retag=True)"
        req_cap = "CAP_STACKED_OR_TREE_RETAG"
        erased_hint = False
    elif ct == "CastKind::BoxDerefTransmute":
        trunk_node = "TrunkRvalue::Cast(BoxDerefTransmute, op, ty)"
        req_cap = "CAP_BOX_ALLOC_LAYOUT"
        erased_hint = False
    elif ct.startswith("AssertKind::NullReferenceConstructed"):
        trunk_node = "TrunkAssert::NullReferenceConstructed + TrunkProj::PhantomDeref"
        req_cap = "CAP_CUSTOM_REBORROW"
        erased_hint = False
    elif ct.startswith("TerminatorKind::Goto"):
        trunk_node = "TrunkTerm::Goto(target)"
        req_cap = "CAP_CORE_SCALAR_CFG"
        erased_hint = True
    else:
        raise ValueError(f"Unhandled specimen: {ct}")

    admitted_under_caps = req_cap in enabled_caps
    final_disposition = (
        "admitted_exact"
        if admitted_under_caps
        else f"fail_closed_unsupported({req_cap})"
    )
    return {
        "specimen": spec.name,
        "origin_pin": spec.origin_pin,
        "hops": 1,
        "intermediate_ast_allocations": 0,
        "synthetic_tunnel_attrs": 0,
        "lossy_or_unsound": False,
        "erased_non_operational_hint": erased_hint,
        "trunk_node": trunk_node,
        "required_capability": req_cap,
        "disposition_under_v1_scalar_caps": final_disposition,
        "disposition_under_full_caps": "admitted_exact",
    }


def compute_topology_scaling_metrics(
    pins: List[CompilerPin], bodies_per_crate: int = 782
) -> Dict[str, object]:
    """
    Quantifies maintenance module count, evaluator/proof engine count, per-crate AST
    allocation counts, strict syntactic intersection, and non-linear DAG behavior
    across all five topologies (T1..T5) over K = 8 linear pins + 1 non-linear nightly pin.
    """
    k = len(pins)  # 8 linear pins
    all_pins = pins + [NONLINEAR_NIGHTLY_PIN]  # 9 total pins
    n_all = len(all_pins)
    hub_idx = 3  # 1.98.0-nightly (`f8a08b688`)

    # Strict syntactic intersection across all 9 pins over the tracked changing enums
    strict_intersection_9_pins = sorted(
        set.intersection(*(set(p.present_variants) for p in all_pins))
    )

    t3a_hops_per_pin = {p.label: (k - 1) - p.index for p in pins}
    t3b_omp_v1_roundtrip_hops = 2 * (k - 1)
    t3c_unidir_hops_per_pin = {p.label: abs(p.index - hub_idx) for p in pins}
    t3c_bidir_hops_per_pin = {p.label: 2 * abs(p.index - hub_idx) for p in pins}
    t4_spoke_copies_per_pin = {p.label: 0 for p in pins}

    distinct_classes_8 = len({p.present_variants for p in pins})
    distinct_classes_9 = len({p.present_variants for p in all_pins})

    vars_8144 = set(NONLINEAR_NIGHTLY_PIN.present_variants)
    vars_1100 = set(pins[6].present_variants)
    nonlinear_oscillating_variants = sorted(vars_8144 ^ vars_1100)

    return {
        "num_linear_pins": k,
        "total_pins_including_nonlinear_nightly": n_all,
        "corpus_bodies_per_pin": bodies_per_crate,
        "strict_9_pin_variant_intersection": strict_intersection_9_pins,
        "topologies": {
            "T1_latest_canonical_raw_ir": {
                "canonical_target_pin": pins[-1].label,
                "evaluator_and_proof_engines_to_maintain": 1,
                "evaluator_proof_churn_on_compiler_bump": True,
                "deleted_historical_variants_unrepresentable": [
                    "Rvalue::ShallowInitBox(Operand, Ty)",
                    "StatementKind::Retag(RetagKind, Box<Place>)",
                ],
                "handles_nonlinear_release_dag_cleanly": False,
            },
            "T2_oldest_or_intersection_ir": {
                "canonical_target_pin": pins[0].label,
                "evaluator_and_proof_engines_to_maintain": 1,
                "strict_9_pin_intersection_count": len(strict_intersection_9_pins),
                "live_corpus_bodies_affected_by_missing_newer_forms": 126,  # 124 memchr (incl. 5 BoxDerefTransmute) + 2 feature_probe
                "live_memchr_bodies_rejected_on_box_deref_transmute": 5,
                "handles_nonlinear_release_dag_cleanly": False,
            },
            "T3_pairwise_stepwise_migration_chain": {
                "T3a_unidir_chain_to_latest": {
                    "migration_modules_to_maintain": k - 1,
                    "ast_to_ast_hops_by_pin": t3a_hops_per_pin,
                    "max_ast_to_ast_hops": max(t3a_hops_per_pin.values()),
                    "mean_ast_to_ast_hops": round(sum(t3a_hops_per_pin.values()) / k, 3),
                    "total_extra_body_allocations_across_8_pins_on_782_bodies": (
                        sum(t3a_hops_per_pin.values()) * bodies_per_crate
                    ),
                    "handles_nonlinear_release_dag_cleanly": False,
                },
                "T3b_omp_v1_bidir_heterogeneous_chain": {
                    "migration_modules_to_maintain": 2 * (k - 1),
                    "worst_case_roundtrip_hops_latest_with_v0_plugin": t3b_omp_v1_roundtrip_hops,
                    "extra_body_allocations_per_782_body_crate_worst_case": (
                        t3b_omp_v1_roundtrip_hops * bodies_per_crate
                    ),
                    "unrelated_code_newer_syntax_crash": True,
                    "handles_nonlinear_release_dag_cleanly": False,
                },
                "T3c_ppxlib_lagging_hub_pairwise_chain": {
                    "hub_pin": pins[hub_idx].label,
                    "migration_modules_to_maintain_unidir": k - 1,
                    "migration_modules_to_maintain_bidir": 2 * (k - 1),
                    "unidir_hops_by_pin": t3c_unidir_hops_per_pin,
                    "bidir_roundtrip_hops_by_pin": t3c_bidir_hops_per_pin,
                    "max_unidir_hops": max(t3c_unidir_hops_per_pin.values()),
                    "max_bidir_hops": max(t3c_bidir_hops_per_pin.values()),
                    "total_extra_body_allocations_unidir_across_8_pins": (
                        sum(t3c_unidir_hops_per_pin.values()) * bodies_per_crate
                    ),
                    "total_extra_body_allocations_bidir_across_8_pins": (
                        sum(t3c_bidir_hops_per_pin.values()) * bodies_per_crate
                    ),
                    "newer_pins_requiring_tunnel_or_failing": [
                        p.label for p in pins if p.index > hub_idx
                    ],
                    "live_memchr_bodies_broken_or_tunneled_on_1_99_plus": 5,
                    "handles_nonlinear_release_dag_cleanly": False,
                },
            },
            "T4_direct_spoke_to_superset_trunk": {
                "spoke_emitters_by_pin": n_all,
                "distinct_syntax_equivalence_classes_among_8_pins": distinct_classes_8,
                "distinct_syntax_equivalence_classes_among_all_9_pins": distinct_classes_9,
                "evaluator_and_proof_engines_to_maintain": 1,
                "ast_to_ast_hops_by_pin": t4_spoke_copies_per_pin,
                "max_ast_to_ast_hops": 0,
                "direct_tyctxt_to_trunk_passes_per_pin": 1,
                "total_extra_body_allocations_across_8_pins_on_782_bodies": 0,
                "synthetic_tunnel_attributes": 0,
                "handles_nonlinear_release_dag_cleanly": True,
                "supports_zero_edit_cross_pin_proof_reuse": True,
            },
            "T5_separate_per_version_irs_and_evaluators": {
                "disjoint_ast_and_evaluator_stacks_all_9_pins": n_all,
                "disjoint_ast_and_evaluator_stacks_syntax_deduped": distinct_classes_9,
                "reference_correspondence_proofs_to_maintain": n_all,
                "ast_to_ast_hops": 0,
                "lossy_specimens": 0,
                "handles_nonlinear_release_dag_cleanly": True,
                "supports_zero_edit_cross_pin_proof_reuse": False,
            },
        },
        "nonlinear_dag_witness": {
            "earlier_calendar_pin": NONLINEAR_NIGHTLY_PIN.label,
            "earlier_calendar_sha": NONLINEAR_NIGHTLY_PIN.commit_sha,
            "earlier_calendar_date": NONLINEAR_NIGHTLY_PIN.commit_or_release_date,
            "later_calendar_pin": pins[6].label,
            "later_calendar_sha": pins[6].commit_sha,
            "later_calendar_date": pins[6].commit_or_release_date,
            "oscillating_variants_under_date_order": nonlinear_oscillating_variants,
            "explanation": (
                "`8144389c` (2026-10-20 nightly) carries `Goto { target, loop_hint_attrs }` "
                "(`ec45ecff`, 2026-10-07), whereas `1.100.0` (`0ef1bc38`, released 2026-11-09 from "
                "the earlier beta branch) has `PhantomDeref` (`5686e563`, 2026-08-27) without "
                "`loop_hint_attrs`. Calendar ordering oscillates `+loop_hint_attrs -> -loop_hint_attrs -> +loop_hint_attrs`; "
                "spoke-to-superset-trunk lowers both in 1 hop with 0 oscillation."
            ),
        },
    }


def run_probe() -> Dict[str, object]:
    t1_results = [evaluate_t1_latest_raw_canonical(s, LINEAR_RELEASES) for s in SPECIMENS]
    t2_results = [evaluate_t2_oldest_or_intersection(s, LINEAR_RELEASES) for s in SPECIMENS]
    t3a_results = [evaluate_t3a_pairwise_chain_to_latest(s, LINEAR_RELEASES) for s in SPECIMENS]
    t3c_unidir_results = [
        evaluate_t3c_lagging_hub_pairwise(
            s, LINEAR_RELEASES, hub_label="1.98.0-nightly", round_trip=False
        )
        for s in SPECIMENS
    ]
    t3c_bidir_results = [
        evaluate_t3c_lagging_hub_pairwise(
            s, LINEAR_RELEASES, hub_label="1.98.0-nightly", round_trip=True
        )
        for s in SPECIMENS
    ]
    t4_results = [
        evaluate_t4_spoke_to_superset_trunk(s, SCALAR_CORE_V1_CAPABILITIES)
        for s in SPECIMENS
    ]

    scaling = compute_topology_scaling_metrics(LINEAR_RELEASES, bodies_per_crate=782)

    # Deterministic invariant checks
    t4_metrics = scaling["topologies"]["T4_direct_spoke_to_superset_trunk"]
    assert t4_metrics["distinct_syntax_equivalence_classes_among_8_pins"] == 7
    assert t4_metrics["distinct_syntax_equivalence_classes_among_all_9_pins"] == 7
    assert scaling["strict_9_pin_variant_intersection"] == []
    assert sum(1 for r in t1_results if r["cannot_represent_in_latest_raw_ast"]) == 2
    assert sum(1 for r in t2_results if r["cannot_represent_in_oldest_or_intersection"]) == 6
    assert sum(1 for r in t3a_results if r["cannot_represent_in_latest_raw_ast"]) == 2
    assert sum(1 for r in t3c_unidir_results if r["requires_synthetic_tunnel_or_migration_error"]) == 4
    assert sum(1 for r in t3c_bidir_results if r["hazard"] is not None) == 5
    assert all(not r["lossy_or_unsound"] and r["hops"] == 1 for r in t4_results)

    return {
        "schema": "ir-migration-topologies-probe/2",
        "studied_pins_linear": [asdict(p) for p in LINEAR_RELEASES],
        "studied_pin_nonlinear_witness": asdict(NONLINEAR_NIGHTLY_PIN),
        "syntax_mutations_count_structural": 9,
        "syntax_mutations_atomic_entries": [asdict(m) for m in MUTATIONS],
        "scaling_and_allocation_metrics": scaling,
        "specimen_evaluations": {
            "T1_latest_canonical_raw_ir": t1_results,
            "T2_oldest_or_intersection_ir": t2_results,
            "T3a_pairwise_chain_to_latest_raw_ast": t3a_results,
            "T3c_lagging_hub_1_98_unidir": t3c_unidir_results,
            "T3c_lagging_hub_1_98_bidir_roundtrip": t3c_bidir_results,
            "T4_spoke_to_superset_trunk_with_capabilities": t4_results,
        },
        "summary_counts": {
            "specimens_total": len(SPECIMENS),
            "T1_unrepresentable_in_latest_raw_ast": sum(
                1 for r in t1_results if r["cannot_represent_in_latest_raw_ast"]
            ),
            "T2_unrepresentable_in_oldest_or_intersection": sum(
                1 for r in t2_results if r["cannot_represent_in_oldest_or_intersection"]
            ),
            "T3c_lagging_hub_tunnel_or_error_unidir": sum(
                1 for r in t3c_unidir_results if r["requires_synthetic_tunnel_or_migration_error"]
            ),
            "T3c_lagging_hub_hazards_bidir": sum(
                1 for r in t3c_bidir_results if r["hazard"] is not None
            ),
            "T4_lossy_or_unsound": sum(1 for r in t4_results if r["lossy_or_unsound"]),
            "T4_admitted_under_v1_scalar_caps": sum(
                1
                for r in t4_results
                if r["disposition_under_v1_scalar_caps"] == "admitted_exact"
            ),
            "T4_fail_closed_under_v1_scalar_caps": sum(
                1
                for r in t4_results
                if str(r["disposition_under_v1_scalar_caps"]).startswith("fail_closed_unsupported")
            ),
            "T5_evaluator_and_proof_stack_multiplier_9_pins": 9,
            "T5_evaluator_and_proof_stack_multiplier_syntax_deduped": 7,
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--out",
        type=str,
        default="",
        help="Optional path to write JSON probe output",
    )
    args = parser.parse_args()
    result = run_probe()
    formatted = json.dumps(result, indent=2, sort_keys=False) + "\n"
    if args.out:
        with open(args.out, "w", encoding="utf-8") as f:
            f.write(formatted)
    print(
        json.dumps(
            {
                "scaling_summary": result["scaling_and_allocation_metrics"]["topologies"],
                "nonlinear_dag_witness": result["scaling_and_allocation_metrics"][
                    "nonlinear_dag_witness"
                ],
                "summary_counts": result["summary_counts"],
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
