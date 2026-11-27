#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for `ci/check_mir_differential.py`."""

from __future__ import annotations

from contextlib import ExitStack, contextmanager, redirect_stderr, redirect_stdout
import hashlib
import io
import json
import os
from pathlib import Path
import shutil
import signal
import stat
import subprocess
import sys
import tempfile
import time
from typing import Any
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_mir_differential as cmd  # noqa: E402
import perf_tracking  # noqa: E402


_UNSET = object()

_SCRUBBED_TOOL_ENV_KEYS = (
    "CARGO",
    "RUSTC",
    "RUSTDOC",
    "CARGO_HOME",
    "CARGO_TARGET_DIR",
    "RUSTC_WRAPPER",
    "RUSTC_WORKSPACE_WRAPPER",
    "CARGO_BUILD_RUSTC_WRAPPER",
    "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER",
    "RUSTFLAGS",
    "CARGO_ENCODED_RUSTFLAGS",
    "ANNEAL_CAPTURE",
    "ANNEAL_MVP_CAPTURE",
    "ANNEAL_CLI",
    "ANNEAL_MVP_CLI",
    "ANNEAL_AUDITOR",
    "ANNEAL_LEAN",
    "ANNEAL_MVP_LEAN",
    "ANNEAL_SYSROOT",
    "ANNEAL_TEST_RUST_SYSROOT",
    "ANNEAL_MVP_SYSROOT",
    "ANNEAL_TEST_INSTALL_ROOT",
    "ANNEAL_MIRI_SYSROOT",
    "ANNEAL_DIFF_CACHE_DIR",
)


@contextmanager
def _patch_clean_tool_env(overrides: dict[str, str] | None = None):
    """Patch `os.environ` after scrubbing ambient toolchain/build overrides."""
    with mock.patch.dict(os.environ, {}, clear=False):
        for key in _SCRUBBED_TOOL_ENV_KEYS:
            os.environ.pop(key, None)
        if overrides:
            os.environ.update(overrides)
        yield


@contextmanager
def _patch_subprocess_exec(
    *, side_effect: Any = _UNSET, return_value: Any = _UNSET
):
    """Patch both `subprocess.run` and `_run_subcommand_process_group`."""
    mock_kwargs: dict[str, Any] = {}
    if side_effect is not _UNSET:
        mock_kwargs["side_effect"] = side_effect
    if return_value is not _UNSET:
        mock_kwargs["return_value"] = return_value
    mock_fn = mock.Mock(**mock_kwargs)

    def _pg_proxy(
        args: list[str],
        *,
        cwd: Path,
        env: dict[str, str],
        timeout_secs: float,
    ) -> Any:
        return mock_fn(
            args,
            cwd=cwd,
            env=env,
            capture_output=True,
            text=True,
            timeout=timeout_secs,
            check=False,
        )

    with (
        mock.patch("subprocess.run", new=mock_fn),
        mock.patch.object(
            cmd, "_run_subcommand_process_group", side_effect=_pg_proxy
        ),
    ):
        yield mock_fn


def _sample_diff_report(*, unsound: int = 0, killed: int = 5, total: int = 5) -> dict:
    cases = [
        {
            "id": "arith_u32_wrapping_add",
            "source": "src/arith_pass.rs",
            "function": "u32_wrapping_add",
            "category": "arith",
            "expected": "pass",
            "allow_conservative_unsupported": False,
            "kernel_checked": True,
            "miri": {
                "kind": "returned",
                "value": {"kind": "int", "int_kind": "u32", "bits": "4"},
            },
            "lean": {
                "kind": "returned",
                "value": {"kind": "int", "int_kind": "u32", "bits": "4"},
            },
            "verdict": {
                "kind": "agree_value",
                "value": {"kind": "int", "int_kind": "u32", "bits": "4"},
            },
        },
        {
            "id": "ub_div_zero_u32",
            "source": "src/ub_corpus.rs",
            "function": "div_zero_u32",
            "category": "ub",
            "expected": "ub",
            "allow_conservative_unsupported": False,
            "kernel_checked": True,
            "miri": {
                "kind": "undefined_behavior",
                "detail": "error: Undefined Behavior: dividing by zero",
            },
            "lean": {"kind": "undefined_behavior", "detail": "undefined"},
            "verdict": (
                {"kind": "unsound_missed_fault"}
                if unsound > 0
                else {"kind": "agree_undefined_behavior"}
            ),
        },
        {
            "id": "unsup_diverging_abort_call",
            "source": "src/unsupported_controls.rs",
            "function": "abort_control",
            "category": "unsupported_control",
            "expected": "unsupported_control",
            "allow_conservative_unsupported": True,
            "kernel_checked": False,
            "miri": {"kind": "abnormal_abort", "detail": "aborted"},
            "lean": {"kind": "unsupported", "detail": "unsupported"},
            "verdict": {
                "kind": "sound_conservative_abstraction",
                "miri": {"kind": "abnormal_abort", "detail": "aborted"},
                "lean_detail": "unsupported",
            },
        },
    ]
    return {
        "schema": "anneal-differential-run/v1",
        "alpha_notice": cmd.ALPHA_NOTICE,
        "mir_dialect": "profile_v1",
        "manifest_path": "tests/corpora/differential/profile_v1/manifest.toml",
        "capture_bin_source": "env_anneal_capture",
        "capture_bin_sha256": "c" * 64,
        "prebuilt_overlay": "staged:26/29",
        "legs": [
            "miri",
            "lean_step_core_captured",
            "lean_wp_kernel_single_block",
        ],
        "metrics": {
            "compared_count": 3,
            "pass_agreed_count": 1,
            "ub_agreed_count": 0 if unsound > 0 else 1,
            "conservative_unsupported_count": 1,
            "kernel_checked_pass_count": 1,
            "kernel_checked_ub_count": 0 if unsound > 0 else 1,
            "unsound_missed_fault_count": unsound,
            "value_mismatch_count": 0,
            "unexpected_conservative_count": 0,
            "leg_divergence_count": 0,
        },
        "red_flags_passed": 0 if unsound > 0 else 7,
        "red_flag_error": "unsound fault present" if unsound > 0 else None,
        "cases": cases,
        "mutant_check": {
            "total_mutants": total,
            "killed_mutants": killed,
            "killed_pct": (killed * 100.0 / total) if total else 0.0,
            "results": [],
            "synthetic_lean_probes": [
                {
                    "probe_id": "probe_move_deinit_ignored",
                    "description": "synthetic move-deinit check",
                    "passed": True,
                    "expected_kill_verdict": "UnsoundMissedFault",
                    "actual_verdict": "UnsoundMissedFault",
                }
            ],
        },
    }


def _sample_ir_ty(gen_ty: tuple[str, ...]) -> dict[str, Any]:
    tag = gen_ty[0]
    if tag in ("bool", "char", "ordering", "unit"):
        return {"kind": tag}
    if tag in ("int", "overflow_pair"):
        width, signed = cmd._GEN_INT_TO_IR[gen_ty[1]]
        return {"kind": tag, "width": width, "signed": signed}
    if tag == "enum":
        ekind = gen_ty[1]
        exp_w, exp_s, exp_discrs = cmd._GEN_ENUM_IR_SPEC[ekind]
        return {
            "kind": "enum",
            "id": 1,
            "discr_width": exp_w,
            "discr_signed": exp_s,
            "tag_repr": {"kind": "scalar", "width": exp_w, "signed": exp_s},
            "discriminants": list(exp_discrs),
        }
    raise AssertionError(f"unexpected gen_ty {gen_ty!r}")


def _sample_format_rust_ret_payload(val: dict[str, Any]) -> str:
    vk = val["kind"]
    if vk == "unit":
        return "UNIT"
    if vk == "bool":
        return f"BOOL:{'true' if val['value'] else 'false'}"
    if vk == "char":
        return f"CHAR:{val['scalar']}"
    if vk == "ordering":
        return f"ORDERING:{val['value']}"
    if vk == "int":
        return f"INT:{val['int_kind']}:{val['bits']}"
    if vk == "overflow_pair":
        return f"OVF:{val['int_kind']}:{val['bits']}:{'true' if val['overflow'] else 'false'}"
    raise AssertionError(f"unsupported return val {val!r}")


def _sample_format_lean_payload(outcome: dict[str, Any]) -> str:
    ok = outcome["kind"]
    if ok == "returned":
        val = outcome["value"]
        vk = val["kind"]
        if vk == "unit":
            return "RETURNED:UNIT"
        if vk == "bool":
            return f"RETURNED:BOOL:{'true' if val['value'] else 'false'}"
        if vk == "char":
            return f"RETURNED:CHAR:{val['scalar']}"
        if vk == "ordering":
            return f"RETURNED:ORDERING:{val['value']}"
        if vk == "int":
            ik = val["int_kind"]
            w, s = cmd._GEN_INT_TO_IR[ik]
            return f"RETURNED:INT:{w}:{'s' if s else 'u'}:{val['bits']}"
        if vk == "overflow_pair":
            ik = val["int_kind"]
            w, s = cmd._GEN_INT_TO_IR[ik]
            return (
                f"RETURNED:OVF:{w}:{'s' if s else 'u'}:{val['bits']}:"
                f"{'true' if val['overflow'] else 'false'}"
            )
    if ok == "undefined_behavior":
        prefix = "Trusted.MirSemantics.FaultKind.undefined ("
        if outcome["detail"].startswith(prefix) and outcome["detail"].endswith(")"):
            return f"FAULT:undefined:{outcome['detail'][len(prefix):-1]}"
        return "FAULT:undefined"
    if ok == "unsupported":
        return "FAULT:unsupported"
    if ok == "out_of_fuel":
        return "OUT_OF_FUEL"
    if ok == "unwound":
        return "UNWOUND"
    if ok == "abnormal_abort":
        return "ABORTED"
    if ok == "init_unsupported":
        return "INIT_UNSUPPORTED"
    raise AssertionError(f"unsupported lean outcome {outcome!r}")


def _sample_mir_eval_raw_json(
    outcome: dict[str, Any], *, body_id: int, identity: str
) -> str:
    ok = outcome["kind"]
    if ok == "returned":
        val = outcome["value"]
        vk = val["kind"]
        if vk == "unit":
            rv: dict[str, Any] = {"kind": "unit"}
        elif vk == "bool":
            rv = {"kind": "bool", "value": val["value"]}
        elif vk == "char":
            rv = {"kind": "char", "value": chr(val["scalar"])}
        elif vk == "ordering":
            rv = {"kind": "ordering", "value": val["value"].capitalize()}
        elif vk == "int":
            w, s = cmd._GEN_INT_TO_IR[val["int_kind"]]
            rv = {"kind": "scalar", "value": {"width": w, "signed": s, "bits": val["bits"]}}
        elif vk == "overflow_pair":
            w, s = cmd._GEN_INT_TO_IR[val["int_kind"]]
            rv = {
                "kind": "tuple",
                "value": [
                    {"kind": "scalar", "value": {"width": w, "signed": s, "bits": val["bits"]}},
                    {"kind": "bool", "value": val["overflow"]},
                ],
            }
        else:
            raise AssertionError(f"unsupported mir_eval return {val!r}")
        raw_out: dict[str, Any] = {
            "kind": "returned",
            "value": {"kind": "returned", "ret": rv},
        }
    elif ok == "undefined_behavior":
        raw_out = {"kind": "fault", "value": {"kind": "undefined", "reason": outcome["detail"]}}
    elif ok == "unsupported":
        raw_out = {"kind": "fault", "value": {"kind": "unsupported", "reason": outcome["detail"]}}
    elif ok == "out_of_fuel":
        raw_out = {"kind": "out_of_fuel"}
    elif ok == "unwound":
        raw_out = {"kind": "returned", "value": {"kind": "unwound"}}
    elif ok == "abnormal_abort":
        raw_out = {"kind": "aborted"}
    else:
        raise AssertionError(f"unsupported mir_eval outcome {outcome!r}")
    return json.dumps(
        {"body_id": body_id, "identity": identity, "outcome": raw_out}
    )


def _sample_capture_refusal(
    fn_name: str, reason: str = "unsupported intrinsic"
) -> tuple[str, str]:
    raw = json.dumps(
        {
            "status": "unsupported",
            "diagnostics": ["1 required obligations are unsupported"],
            "unsupported": [
                {
                    "def_id": 1,
                    "path": f"fuzz_batch::{fn_name}",
                    "reason": reason,
                }
            ],
        }
    )
    return (
        f"capture unsupported: 1 required obligations are unsupported ({raw})",
        raw,
    )


def _sample_leg_evidence(
    case_id: str,
    fn_name: str,
    *,
    miri: dict[str, Any],
    lean: dict[str, Any],
    rustc: dict[str, Any] | None = None,
    mir_eval: dict[str, Any] | None = None,
    capture_rejected: str | None = None,
    capture_refusal_json: str | None = None,
    capture_body: dict[str, Any] | None = None,
    move_reinit_evidence: dict[str, Any] | None = None,
) -> dict[str, Any]:
    ev: dict[str, Any] = {}
    if miri["kind"] == "returned":
        ev["miri_evidence"] = (
            f"ANNEAL_MIRI_RUN:{case_id}:{fn_name}|"
            f"ANNEAL_MIRI_CASE:{case_id}:{_sample_format_rust_ret_payload(miri['value'])}"
        )
    elif miri["kind"] != "tool_error":
        mtag = {
            "undefined_behavior": "UB",
            "abnormal_abort": "ABORT",
            "panic": "PANIC",
            "unsupported": "UNSUPPORTED",
        }[miri["kind"]]
        ev["miri_evidence"] = f"ANNEAL_MIRI_RUN:{case_id}:{fn_name}|{mtag}|{miri['detail']}"
    if capture_rejected is not None:
        ev["capture_refusal_json"] = (
            capture_refusal_json
            if capture_refusal_json is not None
            else _sample_capture_refusal(fn_name)[1]
        )
    if capture_rejected is None and lean["kind"] != "tool_error":
        if move_reinit_evidence is not None:
            ev["lean_probe_line"] = move_reinit_evidence["lean_probe_line"]
        else:
            assert capture_body is not None, "Lean evidence fixture requires capture_body"
            ev["lean_probe_line"] = (
                f"ANNEAL_LEAN_CASE:{case_id}:BODY|{capture_body['body_id']}|"
                f"{capture_body['fn_identity']}|MR0:{_sample_format_lean_payload(lean)}"
            )
    if rustc is not None and rustc["kind"] != "tool_error":
        if rustc["kind"] == "returned":
            ev["rustc_evidence"] = (
                f"ANNEAL_RUSTC_RUN:{case_id}:{fn_name}|"
                f"ANNEAL_RUSTC_CASE:{case_id}:{_sample_format_rust_ret_payload(rustc['value'])}"
            )
        else:
            rtag = {"abnormal_abort": "ABORT", "panic": "PANIC"}[rustc["kind"]]
            ev["rustc_evidence"] = f"ANNEAL_RUSTC_RUN:{case_id}:{fn_name}|{rtag}|{rustc['detail']}"
    if (
        capture_rejected is None
        and mir_eval is not None
        and mir_eval["kind"] != "tool_error"
        and capture_body is not None
    ):
        ev["mir_eval_body_id"] = capture_body["body_id"]
        ev["mir_eval_raw_json"] = _sample_mir_eval_raw_json(
            mir_eval,
            body_id=capture_body["body_id"],
            identity=capture_body["fn_identity"],
        )
    return ev


def _sample_move_reinit_evidence(
    case_id: str,
    fn_name: str,
    param_tys: list[tuple[str, ...]] | int = 0,
    ret_ty: tuple[str, ...] = ("int", "u32"),
    body_id: int = 0,
) -> dict[str, Any]:
    if isinstance(param_tys, int):
        param_ir_tys = [{"kind": "int", "width": "i32", "signed": False}] * param_tys
    else:
        param_ir_tys = [_sample_ir_ty(t) for t in param_tys]
    arg_count = len(param_ir_tys)
    enum_ty = {
        "kind": "enum",
        "id": 1,
        "discr_width": "i16",
        "discr_signed": True,
        "tag_repr": {"kind": "scalar", "width": "i16", "signed": True},
        "discriminants": ["0", "7"],
    }
    const_enum = {
        "kind": "constant",
        "ty": enum_ty,
        "lit": {"kind": "scalar", "bits": "0"},
    }
    slot = arg_count + 1
    tmp_slot = arg_count + 2
    local_tys = [_sample_ir_ty(ret_ty)] + param_ir_tys + [enum_ty, enum_ty]
    blocks = [
        {
            "statements": [
                {
                    "kind": "assign",
                    "local": slot,
                    "value": {
                        "kind": "use",
                        "operand": const_enum,
                        "with_retag": True,
                    },
                },
                {
                    "kind": "assign",
                    "local": tmp_slot,
                    "value": {
                        "kind": "use",
                        "operand": {"kind": "move", "local": slot},
                        "with_retag": True,
                    },
                },
                {
                    "kind": "assign",
                    "local": slot,
                    "value": {
                        "kind": "use",
                        "operand": {"kind": "copy", "local": tmp_slot},
                        "with_retag": True,
                    },
                },
                {
                    "kind": "assign",
                    "local": 0,
                    "value": {
                        "kind": "discriminant",
                        "place": {"local": slot, "projection": []},
                    },
                },
            ],
            "terminator": {"kind": "ret"},
        }
    ]
    fn_identity = f"crate::{fn_name}"
    sha = cmd._canonical_capture_body_sha256(
        fn_identity, arg_count, local_tys, blocks
    )
    return {
        "body_id": body_id,
        "fn_identity": fn_identity,
        "local_slot": slot,
        "arg_count": arg_count,
        "local_tys": local_tys,
        "blocks": blocks,
        "total_steps": 5,
        "init_step": {"step": 0, "block": 0, "stmt": 0},
        "move_step": {"step": 1, "block": 0, "stmt": 1},
        "reinit_step": {"step": 2, "block": 0, "stmt": 2},
        "read_step": {"step": 3, "block": 0, "stmt": 3},
        "lean_probe_line": (
            f"ANNEAL_LEAN_CASE:{case_id}:BODY|{body_id}|{fn_identity}|"
            f"MR1|{slot}|5|0,0,0|1,0,1|2,0,2|3,0,3:RETURNED:INT:i32:u:7"
        ),
        "capture_body_sha256": sha,
    }


def _sample_capture_body(
    fn_name: str,
    param_tys: list[tuple[str, ...]],
    ret_ty: tuple[str, ...],
    *,
    body_id: int = 0,
    mr_ev: dict[str, Any] | None = None,
) -> dict[str, Any]:
    if mr_ev is not None:
        return {
            "body_id": mr_ev["body_id"],
            "fn_identity": mr_ev["fn_identity"],
            "arg_count": mr_ev["arg_count"],
            "local_tys": mr_ev["local_tys"],
            "blocks": mr_ev["blocks"],
            "capture_body_sha256": mr_ev["capture_body_sha256"],
        }
    fn_identity = f"crate::{fn_name}"
    local_tys = [_sample_ir_ty(ret_ty)] + [_sample_ir_ty(p) for p in param_tys]
    blocks = [{"statements": [], "terminator": {"kind": "ret"}}]
    sha = cmd._canonical_capture_body_sha256(
        fn_identity, len(param_tys), local_tys, blocks
    )
    return {
        "body_id": body_id,
        "fn_identity": fn_identity,
        "arg_count": len(param_tys),
        "local_tys": local_tys,
        "blocks": blocks,
        "capture_body_sha256": sha,
    }


def _with_mir_eval_leg(report: dict[str, Any]) -> dict[str, Any]:
    out = json.loads(json.dumps(report))
    if "anneal_mir_eval_captured" not in out["legs"]:
        out["legs"].append("anneal_mir_eval_captured")
    for c in out["cases"]:
        if c.get("capture_rejected") is None:
            c["mir_eval"] = dict(c["lean"])
            if "capture_body" in c:
                le = c.setdefault("leg_evidence", {})
                le["mir_eval_body_id"] = c["capture_body"]["body_id"]
                le["mir_eval_raw_json"] = _sample_mir_eval_raw_json(
                    c["mir_eval"],
                    body_id=c["capture_body"]["body_id"],
                    identity=c["capture_body"]["fn_identity"],
                )
    return out


def _sample_fuzz_report(
    *,
    unsound: int = 0,
    authority_disagree: int = 0,
    spurious_ub: int = 0,
    admitted_ub: int = 0,
    admission_rate: float = 1.0,
    reported_min_rate: float = 0.90,
    ub_ratio: float = 0.20,
    max_stmts: int = 6,
    fuel: int = 1500,
) -> dict:
    seed = 20261124
    cats = [cmd._expected_fuzz_case_category(seed, i, ub_ratio) for i in range(32)]
    n_safe = sum(1 for c in cats if c == "safe_admitted")
    n_bound = sum(1 for c in cats if c == "boundary_edge_case")
    n_ub = sum(1 for c in cats if c == "targeted_ub_probe")
    n_scope = sum(1 for c in cats if c == "scope_control")
    elig_total = n_safe + n_bound
    admitted_target = int(round(elig_total * admission_rate))
    cases: list[dict[str, Any]] = []

    rem_unsound = unsound
    rem_disagree = authority_disagree
    rem_spurious = spurious_ub
    rem_adm_ub = admitted_ub
    admitted_so_far = 0
    move_reinit_so_far = 0

    ret_7 = {
        "kind": "returned",
        "value": {"kind": "int", "int_kind": "u32", "bits": "7"},
    }
    ret_8 = {
        "kind": "returned",
        "value": {"kind": "int", "int_kind": "u32", "bits": "8"},
    }
    ret_0 = {
        "kind": "returned",
        "value": {"kind": "int", "int_kind": "u32", "bits": "0"},
    }

    for i, cat in enumerate(cats):
        case_id = f"fuzz_s{seed}_c{i:04d}"
        fn_name = f"fuzz_case_{i:04d}"
        capture_rej: str | None = None
        capture_rej_json: str | None = None
        disc_gap: str | None = None
        if cat in ("safe_admitted", "boundary_edge_case"):
            if rem_adm_ub > 0:
                rem_adm_ub -= 1
                miri: dict[str, Any] = {
                    "kind": "undefined_behavior",
                    "detail": "dividing by zero",
                }
                rustc: dict[str, Any] | None = None
                rustc_st = "ignored_due_to_miri_ub"
                if rem_unsound > 0:
                    rem_unsound -= 1
                    agreement = "unsound_accept_critical"
                    lean: dict[str, Any] = dict(ret_0)
                else:
                    agreement = "bi_fault_equiv_agreement"
                    lean = {
                        "kind": "undefined_behavior",
                        "detail": "Trusted.MirSemantics.FaultKind.undefined",
                    }
                is_spurious = False
            elif rem_unsound > 0:
                rem_unsound -= 1
                miri = {"kind": "abnormal_abort", "detail": "abort"}
                rustc = {"kind": "abnormal_abort", "detail": "abort"}
                rustc_st = "agreed"
                lean = dict(ret_0)
                agreement = "unsound_accept_critical"
                is_spurious = False
            elif rem_disagree > 0:
                rem_disagree -= 1
                miri = dict(ret_7)
                rustc = dict(ret_8)
                rustc_st = "disagreement"
                lean = dict(ret_7)
                agreement = "authority_disagreement"
                is_spurious = False
            elif rem_spurious > 0:
                rem_spurious -= 1
                miri = dict(ret_7)
                rustc = dict(ret_7)
                rustc_st = "agreed"
                lean = {
                    "kind": "undefined_behavior",
                    "detail": "Trusted.MirSemantics.FaultKind.undefined (spurious)",
                }
                agreement = "conservative_over_approx_forward_sim_only"
                is_spurious = True
            elif admitted_so_far < admitted_target:
                admitted_so_far += 1
                miri = dict(ret_7)
                rustc = dict(ret_7)
                rustc_st = "agreed"
                lean = dict(ret_7)
                agreement = "bi_fault_equiv_agreement"
                is_spurious = False
            else:
                miri = dict(ret_7)
                rustc = dict(ret_7)
                rustc_st = "agreed"
                capture_rej, capture_rej_json = _sample_capture_refusal(fn_name)
                lean = {"kind": "unsupported", "detail": capture_rej}
                agreement = "conservative_over_approx_forward_sim_only"
                disc_gap = "unbridged_semantics"
                is_spurious = False
            exercised_mr = (
                agreement == "bi_fault_equiv_agreement"
                and miri["kind"] != "undefined_behavior"
                and move_reinit_so_far < 8
            )
            if exercised_mr:
                move_reinit_so_far += 1
        elif cat == "targeted_ub_probe":
            rustc = None
            miri = {"kind": "undefined_behavior", "detail": "div by zero"}
            lean = {
                "kind": "undefined_behavior",
                "detail": "Trusted.MirSemantics.FaultKind.undefined",
            }
            agreement = "bi_fault_equiv_agreement"
            is_spurious = False
            rustc_st = "ignored_due_to_miri_ub"
            exercised_mr = False
        else:
            rustc = {"kind": "abnormal_abort", "detail": "abort"}
            miri = {"kind": "abnormal_abort", "detail": "abort"}
            lean = {
                "kind": "unsupported",
                "detail": "Trusted.MirSemantics.FaultKind.unsupported",
            }
            agreement = "conservative_over_approx_forward_sim_only"
            disc_gap = "unbridged_semantics"
            is_spurious = False
            rustc_st = "agreed"
            exercised_mr = False

        _, case_args, prog_sha, param_tys, ret_ty, exp_case_fuel = (
            cmd._expected_fuzz_case_details(
                seed, i, max_stmts, ub_ratio, default_fuel=fuel
            )
        )
        mr_ev = (
            _sample_move_reinit_evidence(
                case_id,
                fn_name,
                param_tys,
                ret_ty,
                body_id=i,
            )
            if exercised_mr
            else None
        )
        cap_body = (
            _sample_capture_body(
                fn_name,
                param_tys,
                ret_ty,
                body_id=i,
                mr_ev=mr_ev,
            )
            if capture_rej is None
            else None
        )
        leg_ev = _sample_leg_evidence(
            case_id,
            fn_name,
            miri=miri,
            lean=lean,
            rustc=rustc,
            capture_rejected=capture_rej,
            capture_refusal_json=capture_rej_json,
            capture_body=cap_body,
            move_reinit_evidence=mr_ev,
        )
        cases.append(
            {
                "case_id": case_id,
                "fn_name": fn_name,
                "master_seed": seed,
                "case_index": i,
                "category": cat,
                "args": case_args,
                "program_sha256": prog_sha,
                "fuel": exp_case_fuel,
                **({"capture_body": cap_body} if cap_body is not None else {}),
                "capture_rejected": capture_rej,
                "leg_evidence": leg_ev,
                "exercised_move_reinit": exercised_mr,
                **(
                    {"move_reinit_evidence": mr_ev}
                    if mr_ev is not None
                    else {}
                ),
                "rustc": rustc,
                "miri": miri,
                "lean": lean,
                "evaluation": {
                    "agreement": agreement,
                    **({"disclosed_gap": disc_gap} if disc_gap is not None else {}),
                    "is_spurious_lean_ub": is_spurious,
                    "rustc_status": {"status": rustc_st},
                    "detail": "ok",
                },
            }
        )

    bi_equiv = sum(
        1
        for c in cases
        if c["evaluation"]["agreement"] == "bi_fault_equiv_agreement"
    )
    cons_over = sum(
        1
        for c in cases
        if c["evaluation"]["agreement"]
        == "conservative_over_approx_forward_sim_only"
        and not c["evaluation"]["is_spurious_lean_ub"]
    )
    rustc_agreed = sum(
        1
        for c in cases
        if c["evaluation"]["rustc_status"]["status"] == "agreed"
    )
    rustc_ignored = sum(
        1
        for c in cases
        if c["evaluation"]["rustc_status"]["status"] == "ignored_due_to_miri_ub"
    )
    rustc_disagreed = sum(
        1
        for c in cases
        if c["evaluation"]["rustc_status"]["status"] == "disagreement"
    )
    ub_agreed = sum(
        1
        for c in cases
        if c["category"] == "targeted_ub_probe"
        and c["evaluation"]["agreement"] == "bi_fault_equiv_agreement"
        and c["miri"]["kind"] == "undefined_behavior"
    )
    disc_gaps: dict[str, int] = {}
    for c in cases:
        g = c["evaluation"].get("disclosed_gap")
        if g is not None:
            disc_gaps[g] = disc_gaps.get(g, 0) + 1
    actual_rate = admitted_so_far / float(elig_total) if elig_total else 0.0
    gate_err = (
        "P0 soundness failure"
        if unsound > 0
        else (
            "authority failure"
            if authority_disagree > 0
            else (
                "spurious Lean UB failure"
                if spurious_ub > 0
                else (
                    "generator safety invariant failure"
                    if admitted_ub > 0
                    else (
                        "admission rate too low"
                        if actual_rate < reported_min_rate
                        else None
                    )
                )
            )
        )
    )
    return {
        "schema": "anneal-differential-fuzz/v1",
        "alpha_notice": cmd.ALPHA_NOTICE,
        "mir_dialect": "profile_v1",
        "seed": seed,
        "max_stmts": max_stmts,
        "ub_ratio": ub_ratio,
        "fuel": fuel,
        "capture_bin_source": "env_anneal_capture",
        "capture_bin_sha256": "c" * 64,
        "prebuilt_overlay": "staged:26/29",
        "legs": ["rustc_compiled", "miri", "lean_step_core_captured"],
        "min_admission_rate": reported_min_rate,
        "metrics": {
            "total_cases": 32,
            "safe_admitted_cases": n_safe,
            "boundary_edge_cases": n_bound,
            "targeted_ub_probes": n_ub,
            "scope_control_cases": n_scope,
            "admission_eligible_cases": elig_total,
            "admitted_cases": admitted_so_far,
            "admission_rate": actual_rate,
            "bi_fault_equiv_count": bi_equiv,
            "ub_probes_agreed_count": ub_agreed,
            "conservative_over_approx_count": cons_over,
            "spurious_lean_ub_count": spurious_ub,
            "admitted_authority_ub_count": admitted_ub,
            "unsound_accept_count": unsound,
            "authority_disagreement_count": authority_disagree,
            "move_reinit_exercised_count": move_reinit_so_far,
            "disclosed_gaps": disc_gaps,
            "rustc_agreed_count": rustc_agreed,
            "rustc_ignored_ub_count": rustc_ignored,
            "rustc_disagreement_count": rustc_disagreed,
            "wall_clock_sec": 12.5,
        },
        "gate_error": gate_err,
        "cases": cases,
    }


class CheckMirDifferentialTests(unittest.TestCase):
    def setUp(self) -> None:
        stack = ExitStack()
        self.addCleanup(stack.close)
        stack.enter_context(_patch_clean_tool_env())

    def test_detail_and_perf_metrics_validate_against_perf_tracking(self) -> None:
        diff = _sample_diff_report()
        detail = cmd.build_semantic_detail_report(
            diff_report=diff,
            mir_eval_status={"executed": False, "passed": None},
            repo="google/zerocopy",
            branch="main",
            commit_sha="a" * 40,
            commit_unix_ts=1_780_000_000,
            environment_profile={"os": "linux", "arch": "x86_64"},
        )
        self.assertEqual(detail["schema"], "anneal-semantic-detail/v1")
        self.assertEqual(detail["alpha_notice"], cmd.ALPHA_NOTICE)
        self.assertEqual(detail["trust_tier"], "candidate:mir_semantics")
        self.assertEqual(detail["known_bugs"], [])
        diff_ev = detail["evidence_blocks"]["differential_oracle"]
        self.assertEqual(diff_ev["capture_bin_source"], "env_anneal_capture")
        self.assertEqual(diff_ev["capture_bin_sha256"], "c" * 64)
        self.assertEqual(diff_ev["prebuilt_overlay"], "staged:26/29")
        self.assertEqual(detail["differential_runs"][0]["capture_bin_source"], "env_anneal_capture")
        self.assertEqual(detail["differential_runs"][0]["prebuilt_overlay"], "staged:26/29")
        self.assertTrue(cmd.report_passes(detail))

        perf = cmd.build_perf_metrics_snippet(diff)
        self.assertEqual(perf["differential_oracle.litmus.compared_count"], 3)
        self.assertEqual(
            perf["differential_oracle.litmus.kernel_checked_pass_count"], 1
        )
        self.assertEqual(perf["differential_oracle.litmus.kernel_checked_ub_count"], 1)
        self.assertEqual(
            perf["differential_oracle.litmus.unexpected_conservative_count"], 0
        )
        self.assertEqual(perf["differential_oracle.mutants.killed_pct"], 100.0)
        self.assertEqual(perf["differential_oracle.red_flags.passed_count"], 7)

        full_perf_record = {
            "schema": perf_tracking.RECORD_SCHEMA,
            "commit": {
                "sha": "a" * 40,
                "short_sha": "a" * 12,
                "timestamp": "2026-11-23T06:00:00Z",
                "unix_ts": 1_780_000_000,
                "subject": "Differential oracle telemetry",
                "branch": "main",
            },
            "environment": {
                "profile": "linux-x86_64",
                "os": "Linux",
                "arch": "x86_64",
                "cpu_model": "Test CPU",
                "vcpu_count": 4,
                "ram_total_kib": 16_000_000,
                "lean_version": "4.34.1",
                "rustc_version": "rustc 1.98.0-nightly",
            },
            "sampling": {
                "verify_repeats": 1,
                "aggregation": "single",
            },
            "metrics": perf,
        }
        validated = perf_tracking.validate_record(full_perf_record)
        self.assertEqual(validated["metrics"], perf)
        for metric_id in perf:
            desc = perf_tracking.describe_metric(metric_id)
            self.assertEqual(desc["category"], "differential_oracle")

    def test_rejects_empty_cases_missing_mutants_and_unsound_fault(self) -> None:
        bad_unsound = cmd.build_semantic_detail_report(
            diff_report=_sample_diff_report(unsound=1),
            mir_eval_status={"executed": False, "passed": None},
            repo="google/zerocopy",
            branch="main",
            commit_sha="b" * 40,
            commit_unix_ts=1_780_000_000,
            environment_profile={"os": "linux"},
        )
        self.assertFalse(cmd.report_passes(bad_unsound))
        self.assertEqual(len(bad_unsound["known_bugs"]), 1)

        bad_mutant = cmd.build_semantic_detail_report(
            diff_report=_sample_diff_report(killed=4, total=5),
            mir_eval_status={"executed": False, "passed": None},
            repo="google/zerocopy",
            branch="main",
            commit_sha="b" * 40,
            commit_unix_ts=1_780_000_000,
            environment_profile={"os": "linux"},
        )
        self.assertFalse(cmd.report_passes(bad_mutant))

        missing_mutants = _sample_diff_report()
        missing_mutants["mutant_check"] = None
        detail_no_mutants = cmd.build_semantic_detail_report(
            diff_report=missing_mutants,
            mir_eval_status={"executed": False, "passed": None},
            repo="google/zerocopy",
            branch="main",
            commit_sha="b" * 40,
            commit_unix_ts=1_780_000_000,
            environment_profile={"os": "linux"},
        )
        self.assertFalse(cmd.report_passes(detail_no_mutants, require_mutants=True))
        self.assertTrue(cmd.report_passes(detail_no_mutants, require_mutants=False))

        empty_cases = cmd.build_semantic_detail_report(
            diff_report=_sample_diff_report(),
            mir_eval_status={"executed": False, "passed": None},
            repo="google/zerocopy",
            branch="main",
            commit_sha="b" * 40,
            commit_unix_ts=1_780_000_000,
            environment_profile={"os": "linux"},
        )
        empty_cases["differential_runs"][0]["cases"] = []
        self.assertFalse(cmd.report_passes(empty_cases))

    def test_maybe_run_mir_eval_manifest_absent_vs_present(self) -> None:
        status, bin_path = cmd.maybe_run_mir_eval_manifest(None)
        self.assertFalse(status["executed"])
        self.assertIsNone(status["passed"])
        self.assertIsNone(bin_path)

        with tempfile.TemporaryDirectory() as tmpd:
            repo = Path(tmpd)
            mir_dir = repo / "tools" / "anneal-mir-eval"
            mir_dir.mkdir(parents=True)
            manifest = mir_dir / "Cargo.toml"
            manifest.write_text("[package]\nname='anneal-mir-eval'\n", encoding="utf-8")
            fake_target = mir_dir / "target" / "debug"
            fake_target.mkdir(parents=True)
            (fake_target / "anneal-mir-eval").write_text("", encoding="utf-8")
            clean_bin = repo / "clean-bin"
            clean_bin.mkdir()
            for tool in ("cargo", "rustc"):
                tp = clean_bin / tool
                tp.write_text("#!/bin/sh\n", encoding="utf-8")
                tp.chmod(0o755)

            def _artifact_stdout(
                exe_path: Path, manifest_path_str: str | None = None
            ) -> str:
                return (
                    json.dumps(
                        {
                            "reason": "compiler-artifact",
                            "manifest_path": manifest_path_str
                            or str(manifest.resolve()),
                            "target": {
                                "kind": ["bin"],
                                "name": "anneal-mir-eval",
                            },
                            "profile": {"test": False},
                            "executable": str(exe_path),
                        }
                    )
                    + "\n"
                )

            def _mock_cargo_for(exe_path: Path | None = None):
                def _side_effect(args: list[str], **_kwargs: Any) -> mock.Mock:
                    if "build" in args:
                        out_exe = exe_path
                        if out_exe is None:
                            td = Path(args[args.index("--target-dir") + 1])
                            out_exe = td / "debug" / "anneal-mir-eval"
                            out_exe.parent.mkdir(parents=True, exist_ok=True)
                            out_exe.write_bytes(b"mir-eval-bytes")
                        mp_str = (
                            args[args.index("--manifest-path") + 1]
                            if "--manifest-path" in args
                            else str(manifest.resolve())
                        )
                        return mock.Mock(
                            returncode=0,
                            stdout=_artifact_stdout(out_exe, mp_str),
                            stderr="",
                        )
                    return mock.Mock(returncode=0, stdout="", stderr="")

                return _side_effect

            with (
                _patch_clean_tool_env({"PATH": str(clean_bin)}),
                _patch_subprocess_exec(side_effect=_mock_cargo_for()) as run_mock,
            ):
                status2, bin_path2 = cmd.maybe_run_mir_eval_manifest(manifest)
            self.assertTrue(status2["executed"])
            self.assertTrue(status2["passed"])
            assert bin_path2 is not None
            self.assertEqual(os.lstat(bin_path2).st_nlink, 1)
            self.assertIn(".anneal-isolated-bins", str(bin_path2))
            self.assertEqual(bin_path2.read_bytes(), b"mir-eval-bytes")
            self.assertEqual(run_mock.call_count, 2)
            for call_args, _ in [(c.args[0], c.kwargs) for c in run_mock.call_args_list]:
                priv_td = Path(call_args[call_args.index("--target-dir") + 1])
                self.assertNotEqual(priv_td, (mir_dir / "target").resolve())
                self.assertFalse(priv_td.exists())

            # Workspace-member layout still stages the binary cleanly into a
            # fresh private target dir (never reusing `<repo>/target`).
            (repo / "Cargo.toml").write_text(
                '[workspace]\nmembers = ["tools/anneal-mir-eval"]\n',
                encoding="utf-8",
            )
            ws_target = repo / "target" / "debug"
            ws_target.mkdir(parents=True)
            ws_bin = ws_target / "anneal-mir-eval"
            ws_bin.write_text("", encoding="utf-8")
            with (
                _patch_clean_tool_env({"PATH": str(clean_bin)}),
                _patch_subprocess_exec(side_effect=_mock_cargo_for()) as ws_run_mock,
            ):
                status_ws, bin_ws = cmd.maybe_run_mir_eval_manifest(manifest)
            self.assertTrue(status_ws["passed"], status_ws)
            assert bin_ws is not None
            self.assertIn(".anneal-isolated-bins", str(bin_ws))
            self.assertEqual(os.lstat(bin_ws).st_nlink, 1)
            for call in ws_run_mock.call_args_list:
                call_args, call_kwargs = call.args[0], call.kwargs
                self.assertIn("--target-dir", call_args)
                priv_td = Path(call_args[call_args.index("--target-dir") + 1])
                self.assertNotEqual(priv_td, (repo / "target").resolve())
                self.assertFalse(priv_td.exists())
                self.assertNotIn("CARGO_TARGET_DIR", call_kwargs.get("env") or {})

            sym_cargo = repo / "sym-cargo"
            os.symlink("/usr/bin/env", sym_cargo)
            with (
                _patch_clean_tool_env(
                    {"PATH": str(clean_bin), "CARGO": str(sym_cargo)}
                ),
                _patch_subprocess_exec() as sym_cargo_mock,
            ):
                with self.assertRaisesRegex(ValueError, "symlink"):
                    cmd.maybe_run_mir_eval_manifest(manifest)
                sym_cargo_mock.assert_not_called()

            sym_rustc = repo / "sym-rustc"
            os.symlink("/usr/bin/env", sym_rustc)
            with (
                _patch_clean_tool_env(
                    {"PATH": str(clean_bin), "RUSTC": str(sym_rustc)}
                ),
                _patch_subprocess_exec() as sym_rustc_mock,
            ):
                with self.assertRaisesRegex(ValueError, "symlink"):
                    cmd.maybe_run_mir_eval_manifest(manifest)
                sym_rustc_mock.assert_not_called()

            caller_bin = repo / "caller-bin"
            caller_bin.mkdir()
            caller_cargo = caller_bin / "cargo-custom"
            caller_cargo.write_text("#!/bin/sh\n", encoding="utf-8")
            caller_rustc = caller_bin / "rustc-custom"
            caller_rustc.write_text("#!/bin/sh\n", encoding="utf-8")
            rustup_proxy_dir = repo / "rustup-proxy-bin"
            rustup_proxy_dir.mkdir()
            (rustup_proxy_dir / "rustup").write_text("#!/bin/sh\n", encoding="utf-8")
            os.symlink("rustup", rustup_proxy_dir / "cargo")
            os.symlink("rustup", rustup_proxy_dir / "rustc")
            with (
                _patch_clean_tool_env(
                    {"PATH": str(rustup_proxy_dir), "RUSTC": "rustc"}
                ),
                _patch_subprocess_exec() as bare_rustc_mock,
            ):
                with self.assertRaisesRegex(ValueError, "symlink"):
                    cmd.maybe_run_mir_eval_manifest(manifest)
                bare_rustc_mock.assert_not_called()

            evil_rustc_dir = repo / "evil-rustc-bin"
            evil_rustc_dir.mkdir()
            os.symlink("/usr/bin/env", evil_rustc_dir / "rustc")
            (evil_rustc_dir / "cargo").write_text("#!/bin/sh\n", encoding="utf-8")
            with (
                _patch_clean_tool_env({"PATH": str(evil_rustc_dir)}),
                _patch_subprocess_exec() as path_rustc_mock,
            ):
                with self.assertRaisesRegex(ValueError, "symlink"):
                    cmd.maybe_run_mir_eval_manifest(manifest)
                path_rustc_mock.assert_not_called()

            seen_manifest_envs: list[dict[str, str]] = []

            def _capture_env_cargo(args: list[str], **kwargs: Any) -> mock.Mock:
                seen_manifest_envs.append(dict(kwargs.get("env") or {}))
                return _mock_cargo_for()(args, **kwargs)

            caller_anchor_cwd = repo / "caller-anchor"
            caller_anchor_cwd.mkdir()
            rel_bin_dir = caller_anchor_cwd / "rel-bin"
            rel_bin_dir.mkdir()
            rel_cargo = rel_bin_dir / "cargo-custom"
            rel_cargo.write_text("#!/bin/sh\n", encoding="utf-8")
            rel_rustc = rel_bin_dir / "rustc-custom"
            rel_rustc.write_text("#!/bin/sh\n", encoding="utf-8")
            prev_cwd_inner = Path.cwd()
            try:
                os.chdir(caller_anchor_cwd)
                with (
                    _patch_clean_tool_env(
                        {
                            "PATH": str(clean_bin),
                            "CARGO": "./rel-bin/cargo-custom",
                            "RUSTC": "./rel-bin/rustc-custom",
                        }
                    ),
                    _patch_subprocess_exec(side_effect=_capture_env_cargo),
                ):
                    status_rel_cmds, _ = cmd.maybe_run_mir_eval_manifest(manifest)
                self.assertTrue(status_rel_cmds["passed"], status_rel_cmds)
                self.assertEqual(len(seen_manifest_envs), 2)
                for env_seen in seen_manifest_envs:
                    staged_cargo = Path(env_seen["CARGO"])
                    staged_rustc = Path(env_seen["RUSTC"])
                    self.assertNotEqual(staged_cargo, rel_cargo.resolve())
                    self.assertNotEqual(staged_rustc, rel_rustc.resolve())
                    self.assertIn(".anneal-isolated-bins", str(staged_cargo))
                    self.assertIn(".anneal-isolated-bins", str(staged_rustc))
                    self.assertEqual(staged_cargo.name, "cargo")
                    self.assertEqual(staged_rustc.name, "rustc")

                # Parent traversal (`..`) in `CARGO`, `RUSTC`, `CARGO_HOME`,
                # cache roots, or `--anneal-diff-bin` must fail closed.
                with (
                    _patch_clean_tool_env(
                        {
                            "PATH": str(clean_bin),
                            "CARGO": "../caller-bin/cargo-custom",
                        }
                    ),
                    _patch_subprocess_exec() as no_exec,
                ):
                    with self.assertRaisesRegex(ValueError, "parent traversal"):
                        cmd.maybe_run_mir_eval_manifest(manifest)
                    no_exec.assert_not_called()
                with (
                    _patch_clean_tool_env(
                        {
                            "PATH": str(clean_bin),
                            "RUSTC": "../caller-bin/rustc-custom",
                        }
                    ),
                    _patch_subprocess_exec() as no_exec,
                ):
                    with self.assertRaisesRegex(ValueError, "parent traversal"):
                        cmd.maybe_run_mir_eval_manifest(manifest)
                    no_exec.assert_not_called()
            finally:
                os.chdir(prev_cwd_inner)

            # Missing `compiler-artifact` record fails closed even on rc == 0.
            empty_ok = mock.Mock(returncode=0, stdout="", stderr="")
            with (
                _patch_clean_tool_env({"PATH": str(clean_bin)}),
                _patch_subprocess_exec(return_value=empty_ok),
            ):
                status_no_json, bin_no_json = cmd.maybe_run_mir_eval_manifest(manifest)
            self.assertTrue(status_no_json["executed"])
            self.assertFalse(status_no_json["passed"])
            self.assertIsNone(bin_no_json)

            # `cargo test` and `cargo build` pass finite timeouts and convert
            # `TimeoutExpired` into failed manifest status cleanly.
            slow_cargo = repo / "slow-cargo.sh"
            slow_cargo.write_text("#!/bin/sh\nsleep 2\n", encoding="utf-8")
            slow_cargo.chmod(0o755)
            with _patch_clean_tool_env(
                {
                    "PATH": str(clean_bin),
                    "CARGO": str(slow_cargo),
                    "RUSTC": str(caller_rustc),
                }
            ):
                st_timeout_test, bin_timeout_test = cmd.maybe_run_mir_eval_manifest(
                    manifest, skip_tests=False, timeout_secs=0.05
                )
                st_timeout_build, bin_timeout_build = cmd.maybe_run_mir_eval_manifest(
                    manifest, skip_tests=True, timeout_secs=0.05
                )
            self.assertTrue(st_timeout_test["executed"])
            self.assertFalse(st_timeout_test["passed"])
            self.assertIn("cargo test timed out", st_timeout_test["error"])
            self.assertIsNone(bin_timeout_test)
            self.assertTrue(st_timeout_build["executed"])
            self.assertFalse(st_timeout_build["passed"])
            self.assertIn("cargo build timed out", st_timeout_build["error"])
            self.assertIsNone(bin_timeout_build)

            # Ambient `.cargo` / `rust-toolchain.toml` overrides fail closed
            # pre-Cargo, and wrapper env overrides are stripped while CLI
            # `--config` resets `build.rustc-wrapper`.
            (mir_dir / ".cargo").mkdir()
            (mir_dir / ".cargo" / "config.toml").write_text(
                '[build]\nrustc-wrapper = "/bin/false"\n',
                encoding="utf-8",
            )
            with (
                _patch_clean_tool_env({"PATH": str(clean_bin)}),
                _patch_subprocess_exec() as cfg_mock,
            ):
                with self.assertRaisesRegex(ValueError, r"\.cargo"):
                    cmd.maybe_run_mir_eval_manifest(manifest)
                cfg_mock.assert_not_called()
            shutil.rmtree(mir_dir / ".cargo")

            # Symlinked or hardlinked ancestor `Cargo.toml` fails closed
            # pre-Cargo.
            outside_anc_toml = repo / "outside-anc-Cargo.toml"
            outside_anc_toml.write_text(
                '[workspace]\nmembers = ["mir-eval"]\n', encoding="utf-8"
            )
            anc_ws_dir = repo / "anc-ws"
            anc_ws_dir.mkdir()
            anc_toml = anc_ws_dir / "Cargo.toml"
            sub_pkg_dir = anc_ws_dir / "subpkg"
            sub_pkg_dir.mkdir()
            sub_manifest = sub_pkg_dir / "Cargo.toml"
            sub_manifest.write_text(
                '[package]\nname = "anneal-mir-eval"\nversion = "0.1.0"\n',
                encoding="utf-8",
            )
            os.symlink(outside_anc_toml, anc_toml)
            try:
                with (
                    _patch_clean_tool_env({"PATH": str(clean_bin)}),
                    _patch_subprocess_exec() as anc_mock,
                ):
                    with self.assertRaisesRegex(
                        ValueError, "ancestor Cargo.toml must not be a symlink"
                    ):
                        cmd.maybe_run_mir_eval_manifest(sub_manifest)
                    anc_mock.assert_not_called()
            finally:
                anc_toml.unlink()
            os.link(outside_anc_toml, anc_toml)
            try:
                with (
                    _patch_clean_tool_env({"PATH": str(clean_bin)}),
                    _patch_subprocess_exec() as anc_mock,
                ):
                    with self.assertRaisesRegex(
                        ValueError, "ancestor Cargo.toml must not be a hardlink"
                    ):
                        cmd.maybe_run_mir_eval_manifest(sub_manifest)
                    anc_mock.assert_not_called()
            finally:
                anc_toml.unlink()

            seen_wrap_calls: list[
                tuple[list[str], dict[str, str], float | None]
            ] = []

            def _record_wrap_cargo(args: list[str], **kwargs: Any) -> mock.Mock:
                seen_wrap_calls.append(
                    (
                        list(args),
                        dict(kwargs.get("env") or {}),
                        kwargs.get("timeout"),
                    )
                )
                return _mock_cargo_for()(args, **kwargs)

            with _patch_clean_tool_env(
                {
                    "PATH": str(clean_bin),
                    "CARGO": str(caller_cargo),
                    "RUSTC": str(caller_rustc),
                    "RUSTC_WRAPPER": "/tmp/evil-wrapper",
                    "CARGO_BUILD_RUSTC_WRAPPER": "/tmp/evil-build-wrapper",
                }
            ):
                with _patch_subprocess_exec(side_effect=_record_wrap_cargo):
                    st_wrap, _ = cmd.maybe_run_mir_eval_manifest(manifest)
            self.assertTrue(st_wrap["passed"], st_wrap)
            self.assertEqual(len(seen_wrap_calls), 2)
            for w_args, w_env, w_timeout in seen_wrap_calls:
                self.assertIn('build.rustc-wrapper=""', w_args)
                self.assertIn('build.rustc-workspace-wrapper=""', w_args)
                self.assertNotIn("RUSTC_WRAPPER", w_env)
                self.assertNotIn("CARGO_BUILD_RUSTC_WRAPPER", w_env)
                self.assertEqual(w_timeout, cmd.MIR_EVAL_MANIFEST_TIMEOUT_SECS)

            fail_proc = mock.Mock(returncode=101, stdout="", stderr="assertion failed")
            with (
                _patch_clean_tool_env({"PATH": str(clean_bin)}),
                _patch_subprocess_exec(return_value=fail_proc),
            ):
                status3, bin_path3 = cmd.maybe_run_mir_eval_manifest(manifest)
            self.assertTrue(status3["executed"])
            self.assertFalse(status3["passed"])
            self.assertIsNone(bin_path3)

            rel_target_bin = mir_dir / "rel-target" / "nested" / "debug"
            rel_target_bin.mkdir(parents=True)
            (rel_target_bin / "anneal-mir-eval").write_text("", encoding="utf-8")
            abs_target_dir = repo / "abs-target"
            (abs_target_dir / "debug").mkdir(parents=True)
            (abs_target_dir / "debug" / "anneal-mir-eval").write_text(
                "", encoding="utf-8"
            )
            outside_cwd = repo / "outside-cwd"
            outside_cwd.mkdir()
            prev_cwd = Path.cwd()
            try:
                os.chdir(outside_cwd)
                rel_exe = (
                    mir_dir.resolve()
                    / "rel-target"
                    / "nested"
                    / "debug"
                    / "anneal-mir-eval"
                )
                with (
                    _patch_clean_tool_env(
                        {"PATH": str(clean_bin), "CARGO_TARGET_DIR": "rel-target/nested"}
                    ),
                    _patch_subprocess_exec(side_effect=_mock_cargo_for()),
                ):
                    status_rel, bin_rel = cmd.maybe_run_mir_eval_manifest(manifest)
                self.assertTrue(status_rel["passed"], status_rel)
                assert bin_rel is not None
                self.assertNotEqual(bin_rel, rel_exe)
                self.assertIn(".anneal-isolated-bins", str(bin_rel))
                self.assertEqual(os.lstat(bin_rel).st_nlink, 1)

                sym_target_dir = repo / "sym-target-dir"
                os.symlink(abs_target_dir, sym_target_dir)
                for bad_td in (
                    str(sym_target_dir),
                    str(sym_target_dir / "nested" / "sub"),
                ):
                    with (
                        _patch_clean_tool_env(
                            {"PATH": str(clean_bin), "CARGO_TARGET_DIR": bad_td}
                        ),
                        _patch_subprocess_exec(
                            side_effect=_mock_cargo_for(
                                sym_target_dir / "debug" / "anneal-mir-eval"
                            ),
                        ) as sym_run_mock,
                    ):
                        with self.assertRaises(ValueError):
                            cmd.maybe_run_mir_eval_manifest(manifest)
                        sym_run_mock.assert_not_called()

                file_target_dir = repo / "regular-target-file"
                file_target_dir.write_text("", encoding="utf-8")
                with (
                    _patch_clean_tool_env(
                        {
                            "PATH": str(clean_bin),
                            "CARGO_TARGET_DIR": str(file_target_dir / "sub"),
                        }
                    ),
                    _patch_subprocess_exec(
                        side_effect=_mock_cargo_for(abs_target_dir / "debug" / "anneal-mir-eval"),
                    ) as file_run_mock,
                ):
                    with self.assertRaises(ValueError):
                        cmd.maybe_run_mir_eval_manifest(manifest)
                    file_run_mock.assert_not_called()

                abs_exe = abs_target_dir / "debug" / "anneal-mir-eval"
                with (
                    _patch_clean_tool_env(
                        {
                            "PATH": str(clean_bin),
                            "CARGO_TARGET_DIR": str(abs_target_dir),
                        }
                    ),
                    _patch_subprocess_exec(side_effect=_mock_cargo_for()),
                ):
                    status_abs, bin_abs = cmd.maybe_run_mir_eval_manifest(manifest)
                self.assertTrue(status_abs["passed"], status_abs)
                assert bin_abs is not None
                self.assertNotEqual(bin_abs, abs_exe)
                self.assertIn(".anneal-isolated-bins", str(bin_abs))

                # When `CARGO_TARGET_DIR` is unset, a poisoned default
                # `<manifest_dir>/target` symlink must also fail before `cargo`.
                poison_dir = repo / "poison-crate"
                poison_dir.mkdir()
                poison_manifest = poison_dir / "Cargo.toml"
                poison_manifest.write_text(
                    "[package]\nname='anneal-mir-eval'\n", encoding="utf-8"
                )
                os.symlink(abs_target_dir, poison_dir / "target")
                with (
                    _patch_clean_tool_env({"PATH": str(clean_bin)}),
                    _patch_subprocess_exec() as default_run_mock,
                ):
                    with self.assertRaises(ValueError):
                        cmd.maybe_run_mir_eval_manifest(poison_manifest)
                    default_run_mock.assert_not_called()

                # Built executables outside the active target dir must fail.
                escaped_bin = repo / "escaped" / "anneal-mir-eval"
                escaped_bin.parent.mkdir()
                escaped_bin.write_text("", encoding="utf-8")
                with (
                    _patch_clean_tool_env({"PATH": str(clean_bin)}),
                    _patch_subprocess_exec(side_effect=_mock_cargo_for(escaped_bin)),
                ):
                    with self.assertRaisesRegex(
                        ValueError, "escaped expected Cargo target directory"
                    ):
                        cmd.maybe_run_mir_eval_manifest(manifest)

                with (
                    _patch_clean_tool_env(
                        {
                            "PATH": str(clean_bin),
                            "CARGO_TARGET_DIR": str(abs_target_dir),
                        }
                    ),
                    _patch_subprocess_exec(side_effect=_mock_cargo_for(escaped_bin)),
                ):
                    with self.assertRaisesRegex(
                        ValueError, "escaped expected Cargo target directory"
                    ):
                        cmd.maybe_run_mir_eval_manifest(manifest)

                # Symlinked `manifest_path` in Cargo compiler-artifact JSON must
                # fail closed.
                sym_manifest_dir = repo / "sym-manifest-dir"
                os.symlink(mir_dir, sym_manifest_dir)
                sym_artifact = json.dumps(
                    {
                        "reason": "compiler-artifact",
                        "manifest_path": str(sym_manifest_dir / "Cargo.toml"),
                        "target": {"kind": ["bin"], "name": "anneal-mir-eval"},
                        "profile": {"test": False},
                        "executable": str(abs_exe),
                    }
                )
                self.assertIsNone(
                    cmd._extract_built_executable(
                        sym_artifact, "anneal-mir-eval", manifest.resolve()
                    )
                )
            finally:
                os.chdir(prev_cwd)

    def test_main_rejects_symlink_anneal_root_and_outputs(self) -> None:
        with tempfile.TemporaryDirectory() as tmpd:
            root = Path(tmpd)
            anneal_dir = root / "anneal"
            anneal_dir.mkdir()
            sym_anneal = root / "anneal_sym"
            os.symlink(anneal_dir, sym_anneal)
            with self.assertRaises(ValueError):
                cmd.main(["--anneal-root", str(sym_anneal), "--allow-unknown-git"])

            out_json = root / "detail.json"
            perf_json = root / "perf.json"
            perf_rec_json = root / "perf-record.json"
            sample = _sample_diff_report()
            sample_fuzz = _sample_fuzz_report()

            with (
                mock.patch.object(
                    cmd,
                    "maybe_run_mir_eval_manifest",
                    return_value=({"executed": False, "passed": None}, None),
                ),
                mock.patch.object(cmd, "run_anneal_diff", return_value=(0, sample)),
                mock.patch.object(
                    cmd, "run_anneal_fuzz", return_value=(0, sample_fuzz)
                ),
            ):
                with self.assertRaises(RuntimeError):
                    cmd.main(["--anneal-root", str(anneal_dir)])

                bad_src_rc = cmd.main(
                    [
                        "--anneal-root",
                        str(anneal_dir),
                        "--allow-unknown-git",
                        "--expect-capture-source",
                        "explicit",
                    ]
                )
                self.assertEqual(bad_src_rc, 1)

                rc = cmd.main(
                    [
                        "--anneal-root",
                        str(anneal_dir),
                        "--allow-unknown-git",
                        "--branch",
                        "pr-test-branch",
                        "--expect-capture-source",
                        "env_anneal_capture",
                        "--output",
                        str(out_json),
                        "--perf-metrics-out",
                        str(perf_json),
                        "--perf-record-out",
                        str(perf_rec_json),
                    ]
                )
            self.assertEqual(rc, 0)
            written_detail = json.loads(out_json.read_text(encoding="utf-8"))
            written_perf = json.loads(perf_json.read_text(encoding="utf-8"))
            written_rec = json.loads(perf_rec_json.read_text(encoding="utf-8"))
            self.assertEqual(written_detail["schema"], cmd.DETAIL_SCHEMA)
            self.assertEqual(written_detail["branch"], "pr-test-branch")
            self.assertEqual(
                written_perf["differential_oracle.litmus.compared_count"], 3
            )
            self.assertEqual(
                written_perf["differential_oracle.fuzz.total_cases_count"], 32
            )
            self.assertEqual(
                written_perf["differential_oracle.fuzz.unsound_accept_count"], 0
            )
            perf_tracking.validate_record(written_rec)
            self.assertEqual(written_rec["commit"]["branch"], "pr-test-branch")

            sym_out = root / "sym.json"
            os.symlink(out_json, sym_out)
            with self.assertRaises(ValueError):
                cmd.main(
                    [
                        "--anneal-root",
                        str(anneal_dir),
                        "--allow-unknown-git",
                        "--output",
                        str(sym_out),
                    ]
                )

    def test_outside_cwd_anchors_relative_cli_and_env_paths_and_rejects_symlinks(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as tmpd:
            repo_root = Path(tmpd).resolve()
            anneal_dir = repo_root / "anneal"
            (anneal_dir / "target" / "debug").mkdir(parents=True)
            (anneal_dir / "corpora").mkdir(parents=True)
            (repo_root / "tools" / "eval").mkdir(parents=True)

            diff_bin = anneal_dir / "target" / "debug" / "anneal-diff"
            diff_bin.write_text("", encoding="utf-8")
            capture_bin = anneal_dir / "target" / "debug" / "anneal-rustc-capture"
            capture_bin.write_text("", encoding="utf-8")
            manifest_file = anneal_dir / "corpora" / "manifest.toml"
            manifest_file.write_text("schema_version = 1\n", encoding="utf-8")
            mir_eval_bin = repo_root / "tools" / "eval" / "anneal-mir-eval"
            mir_eval_bin.write_text("", encoding="utf-8")
            mir_eval_manifest = repo_root / "tools" / "eval" / "Cargo.toml"
            mir_eval_manifest.write_text(
                "[package]\nname = 'anneal-mir-eval'\n", encoding="utf-8"
            )
            (repo_root / "tools" / "eval" / "target" / "debug").mkdir(parents=True)
            (
                repo_root / "tools" / "eval" / "target" / "debug" / "anneal-mir-eval"
            ).write_text("", encoding="utf-8")
            scripts_dir = repo_root / "scripts"
            scripts_dir.mkdir(parents=True)
            for sname in ("cargo", "rustc", "cargo-wrap", "rustc-wrap"):
                sp = scripts_dir / sname
                sp.write_text("#!/bin/sh\n", encoding="utf-8")
                sp.chmod(0o755)

            sample = _with_mir_eval_leg(_sample_diff_report())
            sample_fuzz = _with_mir_eval_leg(_sample_fuzz_report())
            recorded_calls: list[
                tuple[list[str], Path, dict[str, str], int, int, int]
            ] = []

            def fake_subprocess_run(
                args: list[str],
                *,
                cwd: Path | None = None,
                env: dict[str, str] | None = None,
                **kwargs: object,
            ) -> mock.Mock:
                if args and (
                    Path(args[0]).name in ("git", "rustc", "lean")
                    or "--version" in args
                ):
                    return mock.Mock(returncode=1, stdout="", stderr="")
                if len(args) >= 2 and args[1] == "test":
                    return mock.Mock(returncode=0, stdout="", stderr="")
                if len(args) >= 2 and args[1] == "build":
                    priv_td = Path(args[args.index("--target-dir") + 1])
                    built_exe = priv_td / "debug" / "anneal-mir-eval"
                    built_exe.parent.mkdir(parents=True, exist_ok=True)
                    built_exe.write_bytes(b"mir-eval-bytes")
                    mp_str = (
                        args[args.index("--manifest-path") + 1]
                        if "--manifest-path" in args
                        else str(mir_eval_manifest.resolve())
                    )
                    return mock.Mock(
                        returncode=0,
                        stdout=json.dumps(
                            {
                                "reason": "compiler-artifact",
                                "manifest_path": mp_str,
                                "target": {
                                    "kind": ["bin"],
                                    "name": "anneal-mir-eval",
                                },
                                "profile": {"test": False},
                                "executable": str(built_exe),
                            }
                        )
                        + "\n",
                        stderr="",
                    )
                recorded_calls.append(
                    (
                        list(args),
                        Path(cwd) if cwd else Path.cwd(),
                        dict(env or {}),
                        stat.S_IMODE(os.lstat(args[0]).st_mode),
                        stat.S_IMODE(os.lstat(Path(args[0]).parent).st_mode),
                        os.lstat(args[0]).st_nlink,
                    )
                )
                payload = sample_fuzz if "fuzz" in args else sample
                return mock.Mock(
                    returncode=0, stdout=json.dumps(payload), stderr=""
                )

            prev_cwd = Path.cwd()
            try:
                os.chdir(repo_root)
                with (
                    mock.patch.dict(
                        os.environ,
                        {
                            "ANNEAL_CAPTURE": "anneal/target/debug/anneal-rustc-capture",
                            "ANNEAL_MIRI_SYSROOT": "rel-miri-sysroot",
                            "ANNEAL_DIFF_CACHE_DIR": "rel-diff-cache",
                            "CARGO_TARGET_DIR": "rel-cargo-target",
                            "CARGO": "./scripts/cargo-wrap",
                            "RUSTC": "./scripts/rustc-wrap",
                            "PATH": str(scripts_dir),
                        },
                        clear=False,
                    ),
                    _patch_subprocess_exec( side_effect=fake_subprocess_run
                    ),
                ):
                    rc = cmd.main(
                        [
                            "--anneal-root",
                            "anneal",
                            "--anneal-diff-bin",
                            "anneal/target/debug/anneal-diff",
                            "--manifest",
                            "anneal/corpora/manifest.toml",
                            "--capture-bin",
                            "anneal/target/debug/anneal-rustc-capture",
                            "--mir-eval-bin",
                            "tools/eval/anneal-mir-eval",
                            "--cache-root",
                            "rel-cache/diff",
                            "--output",
                            "rel-out/detail.json",
                            "--perf-metrics-out",
                            "rel-out/perf.json",
                            "--perf-record-out",
                            "rel-out/perf-record.json",
                            "--branch",
                            "rel-branch",
                            "--allow-unknown-git",
                        ]
                    )
                self.assertEqual(rc, 0)
                self.assertEqual(len(recorded_calls), 2)
                diff_args, diff_cwd, diff_env, diff_mode, diff_dir_mode, diff_nlink = (
                    recorded_calls[0]
                )
                fuzz_args, fuzz_cwd, fuzz_env, fuzz_mode, fuzz_dir_mode, fuzz_nlink = (
                    recorded_calls[1]
                )
                self.assertEqual(diff_cwd, anneal_dir)
                self.assertEqual(fuzz_cwd, anneal_dir)
                for exe_str, mode, dir_mode, nlink in (
                    (diff_args[0], diff_mode, diff_dir_mode, diff_nlink),
                    (fuzz_args[0], fuzz_mode, fuzz_dir_mode, fuzz_nlink),
                ):
                    self.assertNotEqual(exe_str, str(diff_bin))
                    self.assertIn(".anneal-isolated-bins", exe_str)
                    self.assertEqual(mode, 0o555)
                    self.assertEqual(dir_mode, 0o555)
                    self.assertEqual(nlink, 1)
                    self.assertFalse(Path(exe_str).exists())
                self.assertEqual(
                    diff_args[diff_args.index("--manifest") + 1],
                    str(manifest_file),
                )
                staged_captures: list[Path] = []
                staged_mir_evals: list[Path] = []
                for call_args in (diff_args, fuzz_args):
                    cap_path = Path(
                        call_args[call_args.index("--capture-bin") + 1]
                    )
                    self.assertNotEqual(cap_path, capture_bin)
                    self.assertIn(".anneal-isolated-bins", str(cap_path))
                    self.assertTrue(
                        cap_path.name.startswith("anneal-rustc-capture-")
                    )
                    staged_captures.append(cap_path)
                    me_path = Path(call_args[call_args.index("--mir-eval-bin") + 1])
                    self.assertNotEqual(me_path, mir_eval_bin)
                    self.assertIn(".anneal-isolated-bins", str(me_path))
                    self.assertTrue(me_path.name.startswith("anneal-mir-eval-"))
                    staged_mir_evals.append(me_path)
                    self.assertEqual(
                        call_args[call_args.index("--cache-root") + 1],
                        str(repo_root / "rel-cache" / "diff"),
                    )
                self.assertEqual(staged_captures[0], staged_captures[1])
                self.assertFalse(staged_captures[0].exists())
                self.assertEqual(staged_mir_evals[0], staged_mir_evals[1])
                self.assertFalse(staged_mir_evals[0].exists())
                staged_env_caps: list[Path] = []
                for call_env in (diff_env, fuzz_env):
                    env_cap = Path(call_env["ANNEAL_CAPTURE"])
                    self.assertNotEqual(env_cap, capture_bin)
                    self.assertIn(".anneal-isolated-bins", str(env_cap))
                    self.assertTrue(
                        env_cap.name.startswith("anneal-rustc-capture-")
                    )
                    staged_env_caps.append(env_cap)
                    self.assertEqual(
                        call_env["ANNEAL_MIRI_SYSROOT"],
                        str(repo_root / "rel-miri-sysroot"),
                    )
                    self.assertEqual(
                        call_env["ANNEAL_DIFF_CACHE_DIR"],
                        str(repo_root / "rel-diff-cache"),
                    )
                    self.assertEqual(
                        call_env["CARGO_TARGET_DIR"],
                        str(repo_root / "rel-cargo-target"),
                    )
                    self.assertEqual(
                        call_env["CARGO"], str(repo_root / "scripts" / "cargo-wrap")
                    )
                self.assertEqual(staged_env_caps[0], staged_env_caps[1])
                self.assertFalse(staged_env_caps[0].exists())
                self.assertTrue((repo_root / "rel-out" / "detail.json").is_file())
                self.assertTrue((repo_root / "rel-out" / "perf.json").is_file())
                self.assertTrue(
                    (repo_root / "rel-out" / "perf-record.json").is_file()
                )

                # Direct `run_anneal_diff` and `run_anneal_fuzz` calls with
                # relative `Path` objects also anchor against `caller_cwd`.
                recorded_calls.clear()
                with (
                    _patch_clean_tool_env(
                        {
                            "CARGO": "./scripts/cargo-wrap",
                            "RUSTC": "./scripts/rustc-wrap",
                            "PATH": str(scripts_dir),
                            "ANNEAL_CAPTURE": "anneal/target/debug/anneal-rustc-capture",
                        }
                    ),
                    _patch_subprocess_exec(side_effect=fake_subprocess_run),
                ):
                    rc_direct, _ = cmd.run_anneal_diff(
                        anneal_root=Path("anneal"),
                        manifest=Path("anneal/corpora/manifest.toml"),
                        capture_bin=Path("anneal/target/debug/anneal-rustc-capture"),
                        mir_eval_bin=Path("tools/eval/anneal-mir-eval"),
                        cache_root=Path("rel-cache/direct"),
                        self_check_oracle=False,
                        anneal_diff_bin=None,
                    )
                    rc_fuzz_direct, _ = cmd.run_anneal_fuzz(
                        anneal_root=Path("anneal"),
                        capture_bin=Path("anneal/target/debug/anneal-rustc-capture"),
                        mir_eval_bin=Path("tools/eval/anneal-mir-eval"),
                        cache_root=Path("rel-cache/direct-fuzz"),
                        seed=20261124,
                        cases=32,
                        max_stmts=6,
                        ub_ratio=0.20,
                        min_admission_rate=0.90,
                        anneal_diff_bin=None,
                    )
                self.assertEqual(rc_direct, 0)
                self.assertEqual(rc_fuzz_direct, 0)
                direct_args, direct_cwd, direct_env, _, _, _ = recorded_calls[0]
                direct_fuzz_args, direct_fuzz_cwd, direct_fuzz_env, _, _, _ = (
                    recorded_calls[1]
                )
                self.assertEqual(direct_cwd, anneal_dir)
                self.assertEqual(direct_fuzz_cwd, anneal_dir)
                raw_cargo = str(repo_root / "scripts" / "cargo-wrap")
                for c_args, c_env in (
                    (direct_args, direct_env),
                    (direct_fuzz_args, direct_fuzz_env),
                ):
                    self.assertEqual(c_args[0], c_env["CARGO"])
                    self.assertNotEqual(c_args[0], raw_cargo)
                    self.assertIn(".anneal-isolated-bins", c_args[0])
                    self.assertEqual(Path(c_args[0]).name, "cargo")
                direct_env_cap = Path(direct_fuzz_env["ANNEAL_CAPTURE"])
                self.assertNotEqual(direct_env_cap, capture_bin)
                self.assertIn(".anneal-isolated-bins", str(direct_env_cap))
                self.assertTrue(
                    direct_env_cap.name.startswith("anneal-rustc-capture-")
                )
                self.assertFalse(direct_env_cap.exists())
                self.assertEqual(
                    direct_args[direct_args.index("--manifest") + 1],
                    str(manifest_file),
                )
                for c_args, c_env in (
                    (direct_args, direct_env),
                    (direct_fuzz_args, direct_fuzz_env),
                ):
                    self.assertIn("--target-dir", c_args)
                    self.assertLess(
                        c_args.index("--target-dir"), c_args.index("--")
                    )
                    priv_td = Path(c_args[c_args.index("--target-dir") + 1])
                    self.assertNotEqual(priv_td, anneal_dir / "target")
                    self.assertFalse(priv_td.exists())
                    self.assertNotIn("CARGO_TARGET_DIR", c_env)
                self.assertEqual(
                    direct_args[direct_args.index("--cache-root") + 1],
                    str(repo_root / "rel-cache" / "direct"),
                )
                direct_cap = Path(
                    direct_fuzz_args[
                        direct_fuzz_args.index("--capture-bin") + 1
                    ]
                )
                self.assertNotEqual(direct_cap, capture_bin)
                self.assertIn(".anneal-isolated-bins", str(direct_cap))
                self.assertTrue(
                    direct_cap.name.startswith("anneal-rustc-capture-")
                )
                self.assertFalse(direct_cap.exists())
                direct_me = Path(
                    direct_fuzz_args[
                        direct_fuzz_args.index("--mir-eval-bin") + 1
                    ]
                )
                self.assertNotEqual(direct_me, mir_eval_bin)
                self.assertIn(".anneal-isolated-bins", str(direct_me))
                self.assertTrue(direct_me.name.startswith("anneal-mir-eval-"))
                self.assertFalse(direct_me.exists())
                self.assertEqual(
                    direct_fuzz_args[
                        direct_fuzz_args.index("--cache-root") + 1
                    ],
                    str(repo_root / "rel-cache" / "direct-fuzz"),
                )

                # Relative `--mir-eval-manifest` resolves against `repo_root`,
                # and missing relative manifests return `rc == 1` cleanly.
                recorded_calls.clear()
                with (
                    _patch_clean_tool_env({"PATH": str(scripts_dir)}),
                    _patch_subprocess_exec(side_effect=fake_subprocess_run),
                ):
                    os.environ.pop("CARGO_TARGET_DIR", None)
                    rc_eval = cmd.main(
                        [
                            "--anneal-root",
                            "anneal",
                            "--anneal-diff-bin",
                            "anneal/target/debug/anneal-diff",
                            "--mir-eval-manifest",
                            "tools/eval/Cargo.toml",
                            "--branch",
                            "rel-branch",
                            "--allow-unknown-git",
                        ]
                    )
                    rc_missing_eval = cmd.main(
                        [
                            "--anneal-root",
                            "anneal",
                            "--anneal-diff-bin",
                            "anneal/target/debug/anneal-diff",
                            "--mir-eval-manifest",
                            "tools/eval/missing-Cargo.toml",
                            "--allow-unknown-git",
                        ]
                    )
                self.assertEqual(rc_eval, 0)
                self.assertEqual(rc_missing_eval, 1)
                unwanted_eval_bin = str(
                    repo_root
                    / "tools"
                    / "eval"
                    / "target"
                    / "debug"
                    / "anneal-mir-eval"
                )
                self.assertEqual(len(recorded_calls), 2)
                for eval_args, _, _, _, _, _ in recorded_calls:
                    staged_eval = Path(
                        eval_args[eval_args.index("--mir-eval-bin") + 1]
                    )
                    self.assertNotEqual(str(staged_eval), unwanted_eval_bin)
                    self.assertTrue(
                        staged_eval.name.startswith("anneal-mir-eval-")
                    )
                    # `main()` cleans its temporary staging directory on exit.
                    self.assertFalse(staged_eval.exists())

                # Symlinked `CARGO_TARGET_DIR` (direct or ancestor) must fail
                # closed before `run_anneal_diff` or `run_anneal_fuzz` invokes
                # `cargo run`.
                sym_cargo_td = repo_root / "sym-cargo-target"
                os.symlink(repo_root / "tools", sym_cargo_td)
                for bad_cargo_td in (
                    "sym-cargo-target",
                    "sym-cargo-target/nested/out",
                    str(sym_cargo_td / "nested"),
                ):
                    with (
                        mock.patch.dict(
                            os.environ,
                            {"CARGO_TARGET_DIR": bad_cargo_td},
                            clear=False,
                        ),
                        _patch_subprocess_exec( side_effect=fake_subprocess_run
                        ) as cargo_run_mock,
                    ):
                        with self.assertRaises(ValueError):
                            cmd.run_anneal_diff(
                                anneal_root=Path("anneal"),
                                manifest=None,
                                capture_bin=None,
                                mir_eval_bin=None,
                                cache_root=None,
                                self_check_oracle=False,
                            )
                        with self.assertRaises(ValueError):
                            cmd.run_anneal_fuzz(
                                anneal_root=Path("anneal"),
                                capture_bin=None,
                                mir_eval_bin=None,
                                cache_root=None,
                                seed=1,
                                cases=4,
                                max_stmts=2,
                                ub_ratio=0.0,
                                min_admission_rate=0.90,
                            )
                        cargo_run_mock.assert_not_called()

                # Reject symlinks on relative CLI paths (including lexical
                # `nonexistent/../sym` and symlinked ancestor directories
                # `sym-dir/...`) before running child commands.
                sym_file = repo_root / "sym-target"
                os.symlink(diff_bin, sym_file)
                sym_dir = repo_root / "sym-dir"
                os.symlink(diff_bin.parent, sym_dir)
                for flag in (
                    "--anneal-diff-bin",
                    "--manifest",
                    "--capture-bin",
                    "--mir-eval-bin",
                    "--mir-eval-manifest",
                    "--cache-root",
                    "--output",
                    "--perf-metrics-out",
                    "--perf-record-out",
                ):
                    for rel_sym in (
                        "sym-target",
                        "missing-parent/../sym-target",
                        f"sym-dir/{diff_bin.name}",
                        str(sym_dir / diff_bin.name),
                        f"sym-dir/../{diff_bin.parent.name}/{diff_bin.name}",
                    ):
                        with self.subTest(flag=flag, rel_sym=rel_sym):
                            with self.assertRaises(ValueError):
                                cmd.main(
                                    [
                                        "--anneal-root",
                                        "anneal",
                                        flag,
                                        rel_sym,
                                        "--allow-unknown-git",
                                    ]
                                )
            finally:
                os.chdir(prev_cwd)

    def test_stage2_fuzz_report_validation_and_failure_gates(self) -> None:
        diff = _sample_diff_report()
        fuzz_ok = _sample_fuzz_report()
        detail_ok = cmd.build_semantic_detail_report(
            diff_report=diff,
            fuzz_report=fuzz_ok,
            mir_eval_status={"executed": False, "passed": None},
            repo="google/zerocopy",
            branch="main",
            commit_sha="a" * 40,
            commit_unix_ts=1_780_000_000,
            environment_profile={"os": "linux", "arch": "x86_64"},
        )
        self.assertTrue(cmd.report_passes(detail_ok, require_fuzz=True))
        self.assertIn("differential_fuzz", detail_ok["evidence_blocks"])

        detail_unsound = cmd.build_semantic_detail_report(
            diff_report=diff,
            fuzz_report=_sample_fuzz_report(unsound=1),
            mir_eval_status={"executed": False, "passed": None},
            repo="google/zerocopy",
            branch="main",
            commit_sha="a" * 40,
            commit_unix_ts=1_780_000_000,
            environment_profile={"os": "linux", "arch": "x86_64"},
        )
        self.assertFalse(cmd.report_passes(detail_unsound, require_fuzz=True))
        self.assertEqual(len(detail_unsound["known_bugs"]), 1)

        detail_low_admit = cmd.build_semantic_detail_report(
            diff_report=diff,
            fuzz_report=_sample_fuzz_report(admission_rate=0.50),
            mir_eval_status={"executed": False, "passed": None},
            repo="google/zerocopy",
            branch="main",
            commit_sha="a" * 40,
            commit_unix_ts=1_780_000_000,
            environment_profile={"os": "linux", "arch": "x86_64"},
        )
        self.assertFalse(cmd.report_passes(detail_low_admit, require_fuzz=True))

        # Spurious Lean UB must fail closed and populate known_bugs.
        detail_spurious_ub = cmd.build_semantic_detail_report(
            diff_report=diff,
            fuzz_report=_sample_fuzz_report(spurious_ub=1, admission_rate=0.95),
            mir_eval_status={"executed": False, "passed": None},
            repo="google/zerocopy",
            branch="main",
            commit_sha="a" * 40,
            commit_unix_ts=1_780_000_000,
            environment_profile={"os": "linux", "arch": "x86_64"},
        )
        self.assertFalse(
            cmd.report_passes(detail_spurious_ub, require_fuzz=True)
        )
        self.assertEqual(len(detail_spurious_ub["known_bugs"]), 1)

        # Admitted-category Miri UB must fail closed and populate known_bugs.
        detail_admitted_ub = cmd.build_semantic_detail_report(
            diff_report=diff,
            fuzz_report=_sample_fuzz_report(admitted_ub=1, admission_rate=0.95),
            mir_eval_status={"executed": False, "passed": None},
            repo="google/zerocopy",
            branch="main",
            commit_sha="a" * 40,
            commit_unix_ts=1_780_000_000,
            environment_profile={"os": "linux", "arch": "x86_64"},
        )
        self.assertFalse(
            cmd.report_passes(detail_admitted_ub, require_fuzz=True)
        )
        self.assertEqual(len(detail_admitted_ub["known_bugs"]), 1)

        # Verify each individual metric count guard in `report_passes` fails
        # closed independently even when `gate_error=None` and `known_bugs=[]`.
        for count_key in (
            "unsound_accept_count",
            "authority_disagreement_count",
            "spurious_lean_ub_count",
            "admitted_authority_ub_count",
        ):
            isolated = json.loads(json.dumps(detail_ok))
            isolated["known_bugs"] = []
            isolated["evidence_blocks"]["differential_fuzz"]["gate_error"] = None
            isolated["evidence_blocks"]["differential_fuzz"][count_key] = 1
            self.assertFalse(
                cmd.report_passes(isolated, require_fuzz=True),
                f"expected report_passes to reject nonzero {count_key} with gate_error=None",
            )

        # Verify anti-vacuity floors on `rustc_compiled` leg, `move_reinit`,
        # and `targeted_ub_probes` / `ub_probes_agreed_count`.
        no_rustc_leg = json.loads(json.dumps(detail_ok))
        no_rustc_leg["evidence_blocks"]["differential_fuzz"]["legs"] = [
            "miri",
            "lean_step_core_captured",
        ]
        self.assertFalse(cmd.report_passes(no_rustc_leg, require_fuzz=True))
        self.assertTrue(
            cmd.report_passes(
                no_rustc_leg, require_fuzz=True, fuzz_require_rustc_leg=False
            )
        )

        no_move_reinit = json.loads(json.dumps(detail_ok))
        no_move_reinit["evidence_blocks"]["differential_fuzz"][
            "move_reinit_exercised_count"
        ] = 0
        self.assertFalse(cmd.report_passes(no_move_reinit, require_fuzz=True))

        no_ub_probes = json.loads(json.dumps(detail_ok))
        no_ub_probes["evidence_blocks"]["differential_fuzz"][
            "targeted_ub_probes"
        ] = 0
        self.assertFalse(
            cmd.report_passes(
                no_ub_probes, require_fuzz=True, fuzz_ub_ratio=0.20
            )
        )
        self.assertTrue(
            cmd.report_passes(
                no_ub_probes, require_fuzz=True, fuzz_ub_ratio=0.0
            )
        )
        detail_zero_ub_default = cmd.build_semantic_detail_report(
            diff_report=diff,
            fuzz_report=_sample_fuzz_report(ub_ratio=0.0),
            mir_eval_status={"executed": False, "passed": None},
            repo="google/zerocopy",
            branch="main",
            commit_sha="a" * 40,
            commit_unix_ts=1_780_000_000,
            environment_profile={"os": "linux", "arch": "x86_64"},
        )
        self.assertEqual(
            detail_zero_ub_default["evidence_blocks"]["differential_fuzz"][
                "ub_ratio"
            ],
            0.0,
        )
        self.assertTrue(
            cmd.report_passes(detail_zero_ub_default, require_fuzz=True)
        )

        # CLI `fuzz_min_admission_rate` floor overrides a lower reported
        # `min_admission_rate` inside the fuzz JSON payload.
        detail_spoofed_floor = cmd.build_semantic_detail_report(
            diff_report=diff,
            fuzz_report=_sample_fuzz_report(
                admission_rate=0.80, reported_min_rate=0.50
            ),
            mir_eval_status={"executed": False, "passed": None},
            repo="google/zerocopy",
            branch="main",
            commit_sha="a" * 40,
            commit_unix_ts=1_780_000_000,
            environment_profile={"os": "linux", "arch": "x86_64"},
        )
        self.assertFalse(
            cmd.report_passes(
                detail_spoofed_floor,
                require_fuzz=True,
                fuzz_min_admission_rate=0.90,
            )
        )

        # `--fuzz-ub-ratio` outside `0.0..=0.85` and `--fuzz-max-stmts` outside
        # `1..=20` fail closed before execution.
        with tempfile.TemporaryDirectory() as tmpd:
            anneal_dir = Path(tmpd) / "anneal"
            anneal_dir.mkdir()
            for bad_args in (
                ["--fuzz-ub-ratio", "0.95"],
                ["--fuzz-max-stmts", "0"],
                ["--fuzz-max-stmts", "21"],
            ):
                with self.assertRaises(ValueError):
                    cmd.main(
                        [
                            "--anneal-root",
                            str(anneal_dir),
                            "--allow-unknown-git",
                            *bad_args,
                        ]
                    )

    def test_child_subprocesses_strip_actions_and_github_credentials(
        self,
    ) -> None:
        loader_env = {
            "LD_PRELOAD": "/tmp/evil.so",
            "LD_AUDIT": "/tmp/evil-audit.so",
            "LD_LIBRARY_PATH": "/tmp/evil-lib",
            "DYLD_INSERT_LIBRARIES": "/tmp/evil.dylib",
            "DYLD_LIBRARY_PATH": "/tmp/evil-dyld",
            "GLIBC_TUNABLES": "glibc.malloc.check=1",
            "BASH_ENV": "/tmp/evil-bash-env.sh",
        }
        secret_env = {
            "ACTIONS_CACHE_URL": "https://results-receiver.actions.example/cache/",
            "ACTIONS_ID_TOKEN_REQUEST_TOKEN": "oidc-secret-token",
            "ACTIONS_ID_TOKEN_REQUEST_URL": "https://vstoken.actions.example/",
            "ACTIONS_RESULTS_URL": "https://results-receiver.actions.example/",
            "ACTIONS_RUNTIME_TOKEN": "runtime-secret-token",
            "ACTIONS_RUNTIME_URL": "https://pipelines.actions.example/",
            "GH_TOKEN": "ghs_secret_cli_token",
            "GITHUB_TOKEN": "ghs_secret_actions_token",
            "ANNEAL_BENIGN_TEST_VAR": "kept-value",
        }
        self.assertEqual(
            frozenset(cmd._STRIPPED_CHILD_ENV_VARS),
            frozenset(secret_env.keys()) - {"ANNEAL_BENIGN_TEST_VAR"},
        )

        with tempfile.TemporaryDirectory() as tmpd:
            root = Path(tmpd).resolve()
            anneal_dir = root / "anneal"
            (anneal_dir / "target" / "debug").mkdir(parents=True)
            diff_bin = anneal_dir / "target" / "debug" / "anneal-diff"
            diff_bin.write_text("", encoding="utf-8")

            eval_dir = root / "tools" / "eval"
            (eval_dir / "target" / "debug").mkdir(parents=True)
            eval_manifest = eval_dir / "Cargo.toml"
            eval_manifest.write_text(
                "[package]\nname = 'anneal-mir-eval'\n", encoding="utf-8"
            )
            (eval_dir / "target" / "debug" / "anneal-mir-eval").write_text(
                "", encoding="utf-8"
            )

            sample = _with_mir_eval_leg(_sample_diff_report())
            sample_fuzz = _with_mir_eval_leg(_sample_fuzz_report())
            seen_envs: list[tuple[list[str], dict[str, str] | None]] = []

            def spy_subprocess_run(
                args: list[str],
                *,
                env: dict[str, str] | None = None,
                **kwargs: object,
            ) -> mock.Mock:
                seen_envs.append((list(args), None if env is None else dict(env)))
                if args and args[0] == "git":
                    if "rev-parse" in args and "--abbrev-ref" in args:
                        return mock.Mock(returncode=0, stdout="main\n", stderr="")
                    if "rev-parse" in args:
                        return mock.Mock(
                            returncode=0, stdout=("a" * 40) + "\n", stderr=""
                        )
                    return mock.Mock(
                        returncode=0, stdout="1780000000\n", stderr=""
                    )
                if args and "--version" in args:
                    return mock.Mock(
                        returncode=0, stdout="tool 1.0.0\n", stderr=""
                    )
                if len(args) >= 2 and args[1] == "test":
                    return mock.Mock(returncode=0, stdout="", stderr="")
                if len(args) >= 2 and args[1] == "build":
                    priv_td = Path(args[args.index("--target-dir") + 1])
                    built_exe = priv_td / "debug" / "anneal-mir-eval"
                    built_exe.parent.mkdir(parents=True, exist_ok=True)
                    built_exe.write_bytes(b"mir-eval-bytes")
                    mp_str = (
                        args[args.index("--manifest-path") + 1]
                        if "--manifest-path" in args
                        else str(eval_manifest.resolve())
                    )
                    return mock.Mock(
                        returncode=0,
                        stdout=json.dumps(
                            {
                                "reason": "compiler-artifact",
                                "manifest_path": mp_str,
                                "target": {
                                    "kind": ["bin"],
                                    "name": "anneal-mir-eval",
                                },
                                "profile": {"test": False},
                                "executable": str(built_exe),
                            }
                        )
                        + "\n",
                        stderr="",
                    )
                payload = sample_fuzz if "fuzz" in args else sample
                return mock.Mock(
                    returncode=0, stdout=json.dumps(payload), stderr=""
                )

            fake_bin = root / "fake-bin"
            fake_bin.mkdir()
            for tool in ("cargo", "rustc", "lean"):
                p = fake_bin / tool
                p.write_text("", encoding="utf-8")
                p.chmod(0o755)
            path_tail = (
                f"{fake_bin}{os.pathsep}{os.environ['PATH']}"
                if os.environ.get("PATH")
                else str(fake_bin)
            )
            patched_env = dict(secret_env)
            patched_env.update(loader_env)
            patched_env["PATH"] = path_tail
            with (
                mock.patch.dict(os.environ, patched_env, clear=False),
                _patch_subprocess_exec( side_effect=spy_subprocess_run),
            ):
                os.environ.pop("CARGO", None)
                os.environ.pop("RUSTC", None)
                os.environ.pop("ANNEAL_LEAN", None)
                os.environ.pop("CARGO_TARGET_DIR", None)
                built_env = cmd._build_child_env(root)
                self.assertEqual(built_env.get("ANNEAL_BENIGN_TEST_VAR"), "kept-value")
                for secret_key in (*cmd._STRIPPED_CHILD_ENV_VARS, *loader_env.keys()):
                    self.assertFalse(
                        secret_key in built_env,
                        f"_build_child_env leaked {secret_key}",
                    )

                rc = cmd.main(
                    [
                        "--anneal-root",
                        str(anneal_dir),
                        "--anneal-diff-bin",
                        str(diff_bin),
                        "--mir-eval-manifest",
                        str(eval_manifest),
                    ]
                )
            self.assertEqual(rc, 0)
            # Covers git (3), cargo test/build (2), anneal-diff run/fuzz (2),
            # and rustc/lean version probes (2).
            self.assertGreaterEqual(len(seen_envs), 9)
            saw_fuzz = False
            saw_diff = False
            for sub_args, sub_env in seen_envs:
                self.assertIsNotNone(
                    sub_env,
                    f"subprocess {sub_args!r} inherited raw os.environ",
                )
                assert sub_env is not None
                self.assertEqual(
                    sub_env.get("ANNEAL_BENIGN_TEST_VAR"), "kept-value"
                )
                for secret_key in (*cmd._STRIPPED_CHILD_ENV_VARS, *loader_env.keys()):
                    self.assertFalse(
                        secret_key in sub_env,
                        f"subprocess {sub_args!r} leaked {secret_key}",
                    )
                if "fuzz" in sub_args:
                    saw_fuzz = True
                if "run" in sub_args and "--json" in sub_args:
                    saw_diff = True
            self.assertTrue(saw_diff)
            self.assertTrue(saw_fuzz)

    def test_artifact_manifest_and_missing_mir_eval_and_hex_provenance(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as tmpd:
            manifest = Path(tmpd) / "Cargo.toml"
            manifest.write_text("[package]\nname='x'\n", encoding="utf-8")
            exe = Path(tmpd) / "anneal-mir-eval"
            exe.write_text("", encoding="utf-8")
            no_manifest_line = json.dumps(
                {
                    "reason": "compiler-artifact",
                    "target": {"kind": ["bin"], "name": "anneal-mir-eval"},
                    "profile": {"test": False},
                    "executable": str(exe),
                }
            )
            self.assertIsNone(
                cmd._extract_built_executable(
                    no_manifest_line, "anneal-mir-eval", manifest.resolve()
                )
            )

        detail_missing_eval = cmd.build_semantic_detail_report(
            diff_report=_sample_diff_report(),
            mir_eval_status={"executed": False, "passed": False},
            repo="google/zerocopy",
            branch="main",
            commit_sha="a" * 40,
            commit_unix_ts=1_780_000_000,
            environment_profile={"os": "linux"},
        )
        self.assertFalse(cmd.report_passes(detail_missing_eval))

    def test_nonvirtual_workspace_default_members_selection(self) -> None:
        with tempfile.TemporaryDirectory() as tmpd:
            root = Path(tmpd).resolve()
            root_manifest = root / "Cargo.toml"
            member_dir = root / "tools" / "anneal-mir-eval"
            member_dir.mkdir(parents=True)
            member_manifest = member_dir / "Cargo.toml"
            member_manifest.write_text(
                '[package]\nname = "anneal-mir-eval"\nversion = "0.1.0"\n',
                encoding="utf-8",
            )
            other_dir = root / "tools" / "other-eval"
            other_dir.mkdir(parents=True)
            other_manifest = other_dir / "Cargo.toml"
            other_manifest.write_text(
                '[package]\nname = "other-eval"\nversion = "0.1.0"\n',
                encoding="utf-8",
            )
            excl_dir = root / "tools" / "excluded-eval"
            excl_dir.mkdir(parents=True)
            excl_manifest = excl_dir / "Cargo.toml"
            excl_manifest.write_text(
                '[package]\nname = "excl-eval"\nversion = "0.1.0"\n',
                encoding="utf-8",
            )
            target_bin = root / "target" / "debug" / "anneal-mir-eval"
            target_bin.parent.mkdir(parents=True)
            target_bin.write_text("", encoding="utf-8")

            def _artifact(manifest: Path) -> str:
                return json.dumps(
                    {
                        "reason": "compiler-artifact",
                        "manifest_path": str(manifest),
                        "target": {"kind": ["bin"], "name": "anneal-mir-eval"},
                        "profile": {"test": False},
                        "executable": str(target_bin),
                    }
                )

            # Package + workspace with explicit `default-members` permits the
            # selected default member while excluding unselected members,
            # excluded dirs, and `"."` when omitted from `default-members`.
            root_manifest.write_text(
                '[package]\nname = "root"\nversion = "0.1.0"\n'
                '[workspace]\nmembers = ["tools/*"]\n'
                'exclude = ["tools/excluded-eval"]\n'
                'default-members = ["tools/anneal-mir-eval"]\n',
                encoding="utf-8",
            )
            self.assertEqual(
                cmd._extract_built_executable(
                    _artifact(member_manifest), "anneal-mir-eval", root_manifest
                ),
                target_bin,
            )
            self.assertIsNone(
                cmd._extract_built_executable(
                    _artifact(other_manifest), "anneal-mir-eval", root_manifest
                )
            )
            self.assertIsNone(
                cmd._extract_built_executable(
                    _artifact(excl_manifest), "anneal-mir-eval", root_manifest
                )
            )
            self.assertIsNone(
                cmd._extract_built_executable(
                    _artifact(root_manifest), "anneal-mir-eval", root_manifest
                )
            )

            # Including `"."` alongside a member in `default-members` permits
            # both root and selected member manifests.
            root_manifest.write_text(
                '[package]\nname = "root"\nversion = "0.1.0"\n'
                '[workspace]\nmembers = ["tools/*"]\n'
                'default-members = [".", "tools/anneal-mir-eval"]\n',
                encoding="utf-8",
            )
            self.assertEqual(
                cmd._extract_built_executable(
                    _artifact(root_manifest), "anneal-mir-eval", root_manifest
                ),
                target_bin,
            )
            self.assertEqual(
                cmd._extract_built_executable(
                    _artifact(member_manifest), "anneal-mir-eval", root_manifest
                ),
                target_bin,
            )

            # Package + workspace without `default-members` targets only root.
            root_manifest.write_text(
                '[package]\nname = "root"\nversion = "0.1.0"\n'
                '[workspace]\nmembers = ["tools/*"]\n',
                encoding="utf-8",
            )
            self.assertEqual(
                cmd._extract_built_executable(
                    _artifact(root_manifest), "anneal-mir-eval", root_manifest
                ),
                target_bin,
            )
            self.assertIsNone(
                cmd._extract_built_executable(
                    _artifact(member_manifest), "anneal-mir-eval", root_manifest
                )
            )

            # Explicit empty `default-members` rejects all manifests.
            root_manifest.write_text(
                '[package]\nname = "root"\nversion = "0.1.0"\n'
                '[workspace]\nmembers = ["tools/*"]\ndefault-members = []\n',
                encoding="utf-8",
            )
            self.assertIsNone(
                cmd._extract_built_executable(
                    _artifact(root_manifest), "anneal-mir-eval", root_manifest
                )
            )
            self.assertIsNone(
                cmd._extract_built_executable(
                    _artifact(member_manifest), "anneal-mir-eval", root_manifest
                )
            )

    def test_virtual_workspace_manifest_and_mutually_exclusive_mir_eval_flags(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as tmpd:
            root = Path(tmpd).resolve()
            anneal_dir = root / "anneal"
            anneal_dir.mkdir()

            vws_manifest = root / "Cargo.toml"
            vws_manifest.write_text(
                '[workspace]\nresolver = "2"\nmembers = ["tools/*"]\n'
                'exclude = ["tools/excluded-eval"]\n',
                encoding="utf-8",
            )
            member_dir = root / "tools" / "anneal-mir-eval"
            member_dir.mkdir(parents=True)
            member_manifest = member_dir / "Cargo.toml"
            member_manifest.write_text(
                '[package]\nname = "anneal-mir-eval"\nversion = "0.1.0"\n',
                encoding="utf-8",
            )
            excl_dir = root / "tools" / "excluded-eval"
            excl_dir.mkdir(parents=True)
            excl_manifest = excl_dir / "Cargo.toml"
            excl_manifest.write_text(
                '[package]\nname = "anneal-mir-eval"\nversion = "0.1.0"\n',
                encoding="utf-8",
            )
            target_bin = root / "target" / "debug" / "anneal-mir-eval"
            target_bin.parent.mkdir(parents=True)
            target_bin.write_text("", encoding="utf-8")

            member_artifact = json.dumps(
                {
                    "reason": "compiler-artifact",
                    "manifest_path": str(member_manifest),
                    "target": {"kind": ["bin"], "name": "anneal-mir-eval"},
                    "profile": {"test": False},
                    "executable": str(target_bin),
                }
            )
            self.assertEqual(
                cmd._extract_built_executable(
                    member_artifact, "anneal-mir-eval", vws_manifest
                ),
                target_bin,
            )

            excluded_artifact = json.dumps(
                {
                    "reason": "compiler-artifact",
                    "manifest_path": str(excl_manifest),
                    "target": {"kind": ["bin"], "name": "anneal-mir-eval"},
                    "profile": {"test": False},
                    "executable": str(target_bin),
                }
            )
            self.assertIsNone(
                cmd._extract_built_executable(
                    excluded_artifact, "anneal-mir-eval", vws_manifest
                )
            )
            other_member_dir = root / "tools" / "other-eval"
            other_member_dir.mkdir(parents=True)
            other_manifest = other_member_dir / "Cargo.toml"
            other_manifest.write_text(
                '[package]\nname = "other"\nversion = "0.1.0"\n',
                encoding="utf-8",
            )
            dup_stdout = (
                member_artifact
                + "\n"
                + json.dumps(
                    {
                        "reason": "compiler-artifact",
                        "manifest_path": str(other_manifest),
                        "target": {"kind": ["bin"], "name": "anneal-mir-eval"},
                        "profile": {"test": False},
                        "executable": str(root / "target" / "debug" / "other"),
                    }
                )
            )
            self.assertIsNone(
                cmd._extract_built_executable(
                    dup_stdout, "anneal-mir-eval", vws_manifest
                )
            )

            caller_root = root
            caller_scripts = caller_root / "scripts"
            caller_scripts.mkdir(parents=True)
            for script_name in (
                "cargo",
                "rustc",
                "cargo-wrap",
                "rustc-wrap",
                "rustdoc-wrap",
            ):
                script_file = caller_scripts / script_name
                script_file.write_text("#!/bin/sh\n", encoding="utf-8")
                script_file.chmod(0o755)

            def _vws_cargo_side_effect(
                args: list[str], **_kwargs: Any
            ) -> mock.Mock:
                if "build" in args:
                    priv_td = Path(args[args.index("--target-dir") + 1])
                    built_exe = priv_td / "debug" / "anneal-mir-eval"
                    built_exe.parent.mkdir(parents=True, exist_ok=True)
                    built_exe.write_bytes(b"vws-bytes")
                    staged_ws_dir = Path(args[args.index("--manifest-path") + 1]).parent
                    mp_str = str(
                        staged_ws_dir / "tools" / "anneal-mir-eval" / "Cargo.toml"
                    )
                    return mock.Mock(
                        returncode=0,
                        stdout=json.dumps(
                            {
                                "reason": "compiler-artifact",
                                "manifest_path": mp_str,
                                "target": {
                                    "kind": ["bin"],
                                    "name": "anneal-mir-eval",
                                },
                                "profile": {"test": False},
                                "executable": str(built_exe),
                            }
                        )
                        + "\n",
                        stderr="",
                    )
                return mock.Mock(returncode=0, stdout="", stderr="")

            with (
                _patch_clean_tool_env({"PATH": str(caller_scripts)}),
                _patch_subprocess_exec(side_effect=_vws_cargo_side_effect),
            ):
                status_vws, bin_vws = cmd.maybe_run_mir_eval_manifest(
                    vws_manifest
                )
            self.assertTrue(status_vws["passed"], status_vws)
            assert bin_vws is not None
            self.assertIn(".anneal-isolated-bins", str(bin_vws))
            self.assertEqual(os.lstat(bin_vws).st_nlink, 1)

            with (
                mock.patch.object(
                    cmd, "maybe_run_mir_eval_manifest"
                ) as run_manifest_mock,
                mock.patch.object(cmd, "run_anneal_diff") as run_diff_mock,
            ):
                with self.assertRaises(SystemExit) as ctx:
                    cmd.main(
                        [
                            "--anneal-root",
                            str(anneal_dir),
                            "--mir-eval-manifest",
                            str(member_manifest),
                            "--mir-eval-bin",
                            str(target_bin),
                            "--allow-unknown-git",
                        ]
                    )
                self.assertEqual(ctx.exception.code, 2)
                run_manifest_mock.assert_not_called()
                run_diff_mock.assert_not_called()

            # `maybe_run_mir_eval_manifest` anchors caller tool/cache overrides
            # against `caller_cwd`, strips `CARGO_TARGET_DIR` + wrappers, and
            # isolates Cargo builds into a fresh private target directory.
            (caller_root / "rel-cargo-home").mkdir()
            sub_dir = root / "sub-dir"
            sub_dir.mkdir()
            anchored_target_bin = (
                member_manifest.resolve().parent
                / "rel-cargo-target"
                / "debug"
                / "anneal-mir-eval"
            )
            anchored_target_bin.parent.mkdir(parents=True)
            anchored_target_bin.write_text("", encoding="utf-8")
            recorded_manifest_envs: list[tuple[list[str], Path, dict[str, str]]] = []

            def _anchored_cargo_side_effect(
                args: list[str],
                *,
                cwd: Path | None = None,
                env: dict[str, str] | None = None,
                **_kwargs: object,
            ) -> mock.Mock:
                recorded_manifest_envs.append(
                    (list(args), Path(cwd) if cwd else Path.cwd(), dict(env or {}))
                )
                if len(args) >= 2 and args[1] == "build":
                    priv_td = Path(args[args.index("--target-dir") + 1])
                    built_exe = priv_td / "debug" / "anneal-mir-eval"
                    built_exe.parent.mkdir(parents=True, exist_ok=True)
                    built_exe.write_bytes(b"anchored-bytes")
                    mp_str = (
                        args[args.index("--manifest-path") + 1]
                        if "--manifest-path" in args
                        else str(member_manifest.resolve())
                    )
                    return mock.Mock(
                        returncode=0,
                        stdout=json.dumps(
                            {
                                "reason": "compiler-artifact",
                                "manifest_path": mp_str,
                                "target": {"kind": ["bin"], "name": "anneal-mir-eval"},
                                "profile": {
                                    "test": False
                                },
                                "executable": str(built_exe),
                            }
                        )
                        + "\n",
                        stderr="",
                    )
                return mock.Mock(returncode=0, stdout="", stderr="")

            prev_cwd = Path.cwd()
            try:
                os.chdir(sub_dir)
                with (
                    _patch_subprocess_exec() as no_exec,
                    self.assertRaisesRegex(ValueError, "parent traversal"),
                ):
                    cmd.maybe_run_mir_eval_manifest(
                        Path(os.path.relpath(member_manifest, sub_dir))
                    )
                no_exec.assert_not_called()

                os.chdir(caller_root)
                with (
                    mock.patch.dict(
                        os.environ,
                        {
                            "CARGO": "./scripts/cargo-wrap",
                            "RUSTC": "./scripts/rustc-wrap",
                            "RUSTDOC": "./scripts/rustdoc-wrap",
                            "RUSTC_WRAPPER": "./scripts/clippy-wrap",
                            "RUSTC_WORKSPACE_WRAPPER": "sccache",
                            "CARGO_HOME": "./rel-cargo-home",
                            "XDG_CACHE_HOME": "./rel-xdg-cache",
                            "CARGO_TARGET_DIR": "./rel-cargo-target",
                            "PATH": f"./toolchain/bin{os.pathsep}/usr/bin",
                            "LD_LIBRARY_PATH": f"./lib{os.pathsep}/usr/lib",
                        },
                        clear=False,
                    ),
                    _patch_subprocess_exec(side_effect=_anchored_cargo_side_effect),
                ):
                    rel_manifest = Path(os.path.relpath(member_manifest, caller_root))
                    st_anchor, bin_anchor = cmd.maybe_run_mir_eval_manifest(rel_manifest)
            finally:
                os.chdir(prev_cwd)

            self.assertTrue(st_anchor["passed"], st_anchor)
            assert bin_anchor is not None
            self.assertNotEqual(bin_anchor, anchored_target_bin)
            self.assertIn(".anneal-isolated-bins", str(bin_anchor))
            self.assertEqual(len(recorded_manifest_envs), 2)
            for call_args, call_cwd, call_env in recorded_manifest_envs:
                self.assertNotEqual(call_cwd, member_manifest.resolve().parent)
                self.assertEqual(call_cwd.name, "anneal-mir-eval")
                if os.name == "posix" and sys.platform.startswith("linux"):
                    self.assertTrue(str(call_cwd).startswith("/proc/self/fd/"))
                self.assertEqual(
                    call_args[call_args.index("--manifest-path") + 1],
                    str(call_cwd / "Cargo.toml"),
                )
                self.assertEqual(call_args[0], call_env["CARGO"])
                self.assertNotEqual(
                    call_args[0], str(caller_root / "scripts" / "cargo-wrap")
                )
                self.assertIn(".anneal-isolated-bins", call_args[0])
                self.assertEqual(Path(call_args[0]).name, "cargo")
                self.assertNotEqual(
                    call_env["RUSTC"],
                    str(caller_root / "scripts" / "rustc-wrap"),
                )
                self.assertIn(".anneal-isolated-bins", call_env["RUSTC"])
                self.assertEqual(Path(call_env["RUSTC"]).name, "rustc")
                self.assertEqual(
                    call_env["RUSTDOC"], str(caller_root / "scripts" / "rustdoc-wrap")
                )
                self.assertNotIn("RUSTC_WRAPPER", call_env)
                self.assertNotIn("RUSTC_WORKSPACE_WRAPPER", call_env)
                self.assertNotEqual(
                    call_env["CARGO_HOME"], str(caller_root / "rel-cargo-home")
                )
                if os.name == "posix" and sys.platform.startswith("linux"):
                    self.assertTrue(
                        call_env["CARGO_HOME"].startswith("/proc/self/fd/")
                    )
                self.assertEqual(
                    call_env["XDG_CACHE_HOME"], str(caller_root / "rel-xdg-cache")
                )
                self.assertNotIn("CARGO_TARGET_DIR", call_env)
                priv_td = Path(call_args[call_args.index("--target-dir") + 1])
                self.assertNotEqual(
                    priv_td, member_manifest.resolve().parent / "rel-cargo-target"
                )
                self.assertFalse(priv_td.exists())
                path_parts = call_env["PATH"].split(os.pathsep)
                self.assertEqual(path_parts[0], str(Path(call_env["RUSTC"]).parent))
                self.assertEqual(path_parts[1], str(Path(call_env["CARGO"]).parent))
                self.assertNotIn(str(caller_scripts), path_parts)
                self.assertNotIn(str(caller_root / "toolchain" / "bin"), path_parts)
                self.assertNotIn("./toolchain/bin", path_parts)
                self.assertNotIn("LD_LIBRARY_PATH", call_env)

            # Explicit `--commit-sha` / `--commit-unix-ts` / `--branch`
            # populate telemetry without `--allow-unknown-git` even outside git.
            out_rev = root / "rev-detail.json"
            perf_rev = root / "rev-perf-record.json"
            explicit_sha = "A" * 40
            with mock.patch.object(
                cmd, "run_anneal_diff", return_value=(0, _sample_diff_report())
            ):
                rc_rev = cmd.main(
                    [
                        "--anneal-root",
                        str(anneal_dir),
                        "--no-fuzz",
                        "--branch",
                        "ci-main",
                        "--commit-sha",
                        explicit_sha,
                        "--commit-unix-ts",
                        "1785000123",
                        "--output",
                        str(out_rev),
                        "--perf-record-out",
                        str(perf_rev),
                    ]
                )
            self.assertEqual(rc_rev, 0)
            detail_rev = json.loads(out_rev.read_text(encoding="utf-8"))
            self.assertEqual(detail_rev["branch"], "ci-main")
            self.assertEqual(detail_rev["commit_sha"], "a" * 40)
            self.assertEqual(detail_rev["commit_unix_ts"], 1785000123)
            rec_rev = json.loads(perf_rev.read_text(encoding="utf-8"))
            self.assertEqual(rec_rev["commit"]["sha"], "a" * 40)
            self.assertEqual(rec_rev["commit"]["unix_ts"], 1785000123)
            self.assertEqual(rec_rev["commit"]["branch"], "ci-main")

            # Invalid or unpaired `--commit-sha` / `--commit-unix-ts` fails
            # closed.
            for bad_flags in (
                ["--commit-sha", "not-a-sha"],
                ["--commit-unix-ts", "-1"],
                ["--commit-sha", "a" * 40],
                ["--commit-unix-ts", "1785000123"],
            ):
                with self.assertRaises(SystemExit) as bad_ctx:
                    cmd.main(
                        ["--anneal-root", str(anneal_dir), *bad_flags]
                    )
                self.assertEqual(bad_ctx.exception.code, 2)
            with self.assertRaisesRegex(ValueError, "provided together"):
                cmd._git_metadata(anneal_dir, commit_sha_override="a" * 40)
            with self.assertRaisesRegex(ValueError, "provided together"):
                cmd._git_metadata(anneal_dir, commit_unix_ts_override=1785000123)

            # `_collect_environment` probes the suite-selected `ToolchainEnv`
            # rustc and Lean executables across explicit overrides and
            # install-root/cache fallbacks.
            (anneal_dir / "trusted" / "lean").mkdir(parents=True, exist_ok=True)
            (anneal_dir / "trusted" / "lean" / "lean-toolchain").write_text(
                "leanprover/lean4:v4.34.1\n", encoding="utf-8"
            )
            sys_root = root / "sys-a"
            (sys_root / "bin").mkdir(parents=True)
            (sys_root / "lib").mkdir(parents=True)
            (sys_root / "lib" / "libprobe.so").write_bytes(b"probe-lib")
            (sys_root / "bin" / "rustc").write_text("", encoding="utf-8")
            mvp_lean = root / "mvp-lean"
            mvp_lean.write_text("", encoding="utf-8")
            inst_root = root / "inst-root"
            (inst_root / "rust" / "bin").mkdir(parents=True)
            (inst_root / "rust" / "lib").mkdir(parents=True)
            (inst_root / "rust" / "bin" / "rustc").write_text("", encoding="utf-8")
            (inst_root / "lean" / "bin").mkdir(parents=True)
            (inst_root / "lean" / "bin" / "lean").write_text("", encoding="utf-8")
            xdg_cache = root / "xdg-cache"
            xdg_lean = (
                xdg_cache / "anneal" / "toolchain" / "v1" / "lean" / "bin" / "lean"
            )
            xdg_lean.parent.mkdir(parents=True)
            xdg_lean.write_text("", encoding="utf-8")

            probed: list[tuple[list[str], str, bytes | None]] = []

            def _probe_side_effect(
                args: list[str],
                *,
                env: dict[str, str] | None = None,
                **_kwargs: object,
            ) -> mock.Mock:
                ld_path = (env or {}).get("LD_LIBRARY_PATH", "")
                staged_bytes = None
                if ld_path:
                    cand = Path(ld_path) / "libprobe.so"
                    if cand.is_file():
                        staged_bytes = cand.read_bytes()
                probed.append((list(args), ld_path, staged_bytes))
                return mock.Mock(returncode=0, stdout=f"{args[0]} 1.0.0\n", stderr="")

            with mock.patch("subprocess.run", side_effect=_probe_side_effect):
                with mock.patch.dict(
                    os.environ,
                    {
                        "RUSTC": "/ambient/rustc",
                        "ANNEAL_SYSROOT": str(sys_root),
                        "ANNEAL_MVP_LEAN": str(mvp_lean),
                    },
                    clear=True,
                ):
                    env1 = cmd._collect_environment(anneal_dir, caller_cwd=root)
                self.assertEqual(env1["rustc_version"], f"{sys_root / 'bin' / 'rustc'} 1.0.0")
                self.assertEqual(env1["lean_version"], f"{mvp_lean} 1.0.0")
                self.assertTrue(probed[0][1])
                self.assertNotIn(str(sys_root / "lib"), probed[0][1])
                self.assertEqual(probed[0][2], b"probe-lib")

                probed.clear()
                with mock.patch.dict(
                    os.environ,
                    {
                        "ANNEAL_TEST_INSTALL_ROOT": str(inst_root),
                    },
                    clear=True,
                ):
                    env2 = cmd._collect_environment(anneal_dir, caller_cwd=root)
                self.assertEqual(
                    env2["rustc_version"],
                    f"{inst_root / 'rust' / 'bin' / 'rustc'} 1.0.0",
                )
                self.assertEqual(
                    env2["lean_version"],
                    f"{inst_root / 'lean' / 'bin' / 'lean'} 1.0.0",
                )

                probed.clear()
                with mock.patch.dict(
                    os.environ,
                    {
                        "XDG_CACHE_HOME": str(xdg_cache),
                    },
                    clear=True,
                ):
                    env3 = cmd._collect_environment(anneal_dir, caller_cwd=root)
                self.assertEqual(env3["lean_version"], f"{xdg_lean} 1.0.0")

        docs_text = (
            Path(__file__).resolve().parent.parent / "docs" / "perf-tracking.md"
        ).read_text(encoding="utf-8")
        self.assertIn(
            'One of `"ms"`, `"KiB"`, `"B"`, `"count"`, `"%"`.', docs_text
        )
        self.assertIn("differential_oracle.fuzz.", docs_text)
        self.assertIn("anneal-diff fuzz --json", docs_text)

    def test_rejects_inconsistent_or_truncated_fuzz_cases(self) -> None:
        truncated = _sample_fuzz_report()
        truncated["cases"] = truncated["cases"][:1]
        with self.assertRaisesRegex(ValueError, "total_cases"):
            cmd.build_semantic_detail_report(
                diff_report=_sample_diff_report(),
                mir_eval_status={"executed": False, "passed": None},
                repo="google/zerocopy",
                branch="main",
                commit_sha="a" * 40,
                commit_unix_ts=1_780_000_000,
                environment_profile={"os": "linux"},
                fuzz_report=truncated,
            )

        bad_schema = _sample_fuzz_report()
        bad_schema["schema"] = "wrong/v1"
        with self.assertRaisesRegex(ValueError, "schema"):
            cmd.validate_fuzz_report(bad_schema)

        missing_id = _sample_fuzz_report()
        del missing_id["cases"][0]["case_id"]
        with self.assertRaisesRegex(ValueError, "case_id"):
            cmd.validate_fuzz_report(missing_id)

        bool_metric = _sample_fuzz_report()
        bool_metric["metrics"]["unsound_accept_count"] = False
        with self.assertRaisesRegex(ValueError, "unsound_accept_count"):
            cmd.validate_fuzz_report(bool_metric)

        forged_unsound = _sample_fuzz_report()
        forged_cb = forged_unsound["cases"][2]["capture_body"]
        forged_unsound["cases"][2]["lean"] = {
            "kind": "returned",
            "value": {"kind": "int", "int_kind": "u32", "bits": "0"},
        }
        forged_unsound["cases"][2]["leg_evidence"]["lean_probe_line"] = (
            f"ANNEAL_LEAN_CASE:{forged_unsound['cases'][2]['case_id']}:"
            f"BODY|{forged_cb['body_id']}|{forged_cb['fn_identity']}|MR0:"
            "RETURNED:INT:i32:u:0"
        )
        forged_unsound["cases"][2]["evaluation"]["agreement"] = (
            "unsound_accept_critical"
        )
        forged_unsound["metrics"]["bi_fault_equiv_count"] -= 1
        forged_unsound["metrics"]["ub_probes_agreed_count"] -= 1
        with self.assertRaisesRegex(ValueError, "unsound_accept_count"):
            cmd.validate_fuzz_report(forged_unsound)

        # Forged per-case `evaluation.agreement` (Miri returns 7, Lean returns
        # 8, but `agreement` still claims `bi_fault_equiv_agreement` with
        # matching aggregate counters) is rejected by leg-outcome derivation.
        forged_label = _sample_fuzz_report()
        forged_label["cases"][0]["lean"] = {
            "kind": "returned",
            "value": {"kind": "int", "int_kind": "u32", "bits": "8"},
        }
        with self.assertRaisesRegex(ValueError, "derive 'unsound_accept_critical'"):
            cmd.validate_fuzz_report(forged_label)

        # Forged `rustc` disagreement masked as `agreed` and missing `mir_eval`
        # on an active 4-leg run also fail closed.
        forged_rustc = _sample_fuzz_report()
        forged_rustc["cases"][0]["rustc"] = {
            "kind": "returned",
            "value": {"kind": "int", "int_kind": "u32", "bits": "99"},
        }
        with self.assertRaisesRegex(ValueError, "derive 'authority_disagreement'"):
            cmd.validate_fuzz_report(forged_rustc)

        missing_mir_eval = _sample_fuzz_report()
        missing_mir_eval["legs"].append("anneal_mir_eval_captured")
        with self.assertRaisesRegex(ValueError, "mir_eval"):
            cmd.validate_fuzz_report(missing_mir_eval)

        # Duplicate `case_id` / `case_index` (repeating case 0 at slot 1) must
        # fail closed rather than satisfying aggregate case gates.
        dup_case = _sample_fuzz_report()
        dup_case["cases"][1] = dict(dup_case["cases"][0])
        with self.assertRaisesRegex(ValueError, "duplicate"):
            cmd.validate_fuzz_report(dup_case)

        # Malformed returned `MirValue` payloads (unknown kind, unmasked `u8`
        # bits, surrogate `char`, or missing fields) must fail closed even when
        # repeated identically across all legs.
        for bad_val, pattern in (
            ({"kind": "bogus"}, "MirValue"),
            ({"kind": "int", "int_kind": "u8", "bits": "256"}, "out of u8"),
            ({"kind": "int", "int_kind": "u8", "bits": "01"}, "non-canonical"),
            ({"kind": "char", "scalar": 0xD800}, "Unicode scalar"),
            ({"kind": "unit", "extra": 1}, "extra keys"),
        ):
            bad_ret = _sample_fuzz_report()
            bad_ret["cases"][0]["rustc"] = {"kind": "returned", "value": bad_val}
            bad_ret["cases"][0]["miri"] = {"kind": "returned", "value": bad_val}
            bad_ret["cases"][0]["lean"] = {"kind": "returned", "value": bad_val}
            with self.assertRaisesRegex(ValueError, pattern):
                cmd.validate_fuzz_report(bad_ret)

        # Mismatched capture SHA-256 across `run` and `fuzz` must fail closed.
        mismatched_fuzz = _sample_fuzz_report()
        mismatched_fuzz["capture_bin_sha256"] = "d" * 64
        detail_mismatch = cmd.build_semantic_detail_report(
            diff_report=_sample_diff_report(),
            mir_eval_status={"executed": False, "passed": None},
            repo="google/zerocopy",
            branch="main",
            commit_sha="a" * 40,
            commit_unix_ts=1_780_000_000,
            environment_profile={"os": "linux"},
            fuzz_report=mismatched_fuzz,
        )
        self.assertFalse(cmd.report_passes(detail_mismatch, require_fuzz=True))

        # `max_stmts < 4` relaxes the `>= 16` move/reinit floor, while
        # `max_stmts >= 4` enforces it.
        low_budget = _sample_fuzz_report(max_stmts=3)
        for c in low_budget["cases"]:
            c["exercised_move_reinit"] = False
            c.pop("move_reinit_evidence", None)
        low_budget["metrics"]["move_reinit_exercised_count"] = 0
        detail_low_budget = cmd.build_semantic_detail_report(
            diff_report=_sample_diff_report(),
            mir_eval_status={"executed": False, "passed": None},
            repo="google/zerocopy",
            branch="main",
            commit_sha="a" * 40,
            commit_unix_ts=1_780_000_000,
            environment_profile={"os": "linux"},
            fuzz_report=low_budget,
        )
        self.assertTrue(cmd.report_passes(detail_low_budget, require_fuzz=True))

        four_budget = _sample_fuzz_report(max_stmts=4)
        for c in four_budget["cases"]:
            c["exercised_move_reinit"] = False
            c.pop("move_reinit_evidence", None)
        four_budget["metrics"]["move_reinit_exercised_count"] = 0
        detail_four_budget = cmd.build_semantic_detail_report(
            diff_report=_sample_diff_report(),
            mir_eval_status={"executed": False, "passed": None},
            repo="google/zerocopy",
            branch="main",
            commit_sha="a" * 40,
            commit_unix_ts=1_780_000_000,
            environment_profile={"os": "linux"},
            fuzz_report=four_budget,
        )
        self.assertFalse(cmd.report_passes(detail_four_budget, require_fuzz=True))

        # Non-finite `NaN`/`Inf`, `None`, `bool`, or out-of-range values in
        # `min_admission_rate`, `admission_rate`, or `ub_ratio` fail closed.
        for bad_rate in (float("nan"), float("inf"), None, True, -0.01, 1.01):
            nan_floor = _sample_fuzz_report()
            nan_floor["min_admission_rate"] = bad_rate
            with self.assertRaisesRegex(ValueError, "min_admission_rate"):
                cmd.validate_fuzz_report(nan_floor)

            tampered_detail = cmd.build_semantic_detail_report(
                diff_report=_sample_diff_report(),
                mir_eval_status={"executed": False, "passed": None},
                repo="google/zerocopy",
                branch="main",
                commit_sha="a" * 40,
                commit_unix_ts=1_780_000_000,
                environment_profile={"os": "linux"},
                fuzz_report=_sample_fuzz_report(),
            )
            tampered_detail["evidence_blocks"]["differential_fuzz"][
                "min_admission_rate"
            ] = bad_rate
            self.assertFalse(
                cmd.report_passes(
                    tampered_detail,
                    require_fuzz=True,
                    fuzz_min_admission_rate=0.90,
                )
            )
            tampered_adm = cmd.build_semantic_detail_report(
                diff_report=_sample_diff_report(),
                mir_eval_status={"executed": False, "passed": None},
                repo="google/zerocopy",
                branch="main",
                commit_sha="a" * 40,
                commit_unix_ts=1_780_000_000,
                environment_profile={"os": "linux"},
                fuzz_report=_sample_fuzz_report(),
            )
            tampered_adm["evidence_blocks"]["differential_fuzz"][
                "admission_rate"
            ] = bad_rate
            self.assertFalse(cmd.report_passes(tampered_adm, require_fuzz=True))
            if bad_rate is not None:
                self.assertFalse(
                    cmd.report_passes(
                        cmd.build_semantic_detail_report(
                            diff_report=_sample_diff_report(),
                            mir_eval_status={"executed": False, "passed": None},
                            repo="google/zerocopy",
                            branch="main",
                            commit_sha="a" * 40,
                            commit_unix_ts=1_780_000_000,
                            environment_profile={"os": "linux"},
                            fuzz_report=_sample_fuzz_report(),
                        ),
                        require_fuzz=True,
                        fuzz_min_admission_rate=bad_rate,  # type: ignore[arg-type]
                    )
                )

        with self.assertRaisesRegex(ValueError, "non-finite JSON constant"):
            cmd._reject_json_constant("NaN")

        # `capture_rejected` with `capture_body` or non-`unsupported` Lean fails
        # closed.
        bad_cap_rej_body = _sample_fuzz_report()
        bad_cap_rej_body["cases"][0]["capture_rejected"] = "rejected"
        with self.assertRaisesRegex(ValueError, "capture-rejected"):
            cmd.validate_fuzz_report(bad_cap_rej_body)

        bad_cap_rej = _sample_fuzz_report()
        bad_cap_rej["cases"][0]["capture_rejected"] = "rejected"
        bad_cap_rej["cases"][0].pop("capture_body", None)
        with self.assertRaisesRegex(ValueError, "non-unsupported"):
            cmd.validate_fuzz_report(bad_cap_rej)

        # Claimed `capture_rejected` refusals must carry valid, case-bound
        # `capture_refusal_json` matching `capture_rejected` and `lean.detail`.
        low_adm_valid = _sample_fuzz_report(admission_rate=0.50)
        verified_low = cmd.validate_fuzz_report(low_adm_valid)
        self.assertGreater(
            verified_low["disclosed_gaps"]["unbridged_semantics"], 1
        )

        rej_indices = [
            idx
            for idx, c in enumerate(low_adm_valid["cases"])
            if c.get("capture_rejected") is not None
        ]
        assert len(rej_indices) >= 2
        i_a, i_b = rej_indices[0], rej_indices[1]

        forged_cap_rej = json.loads(json.dumps(low_adm_valid))
        forged_cap_rej["cases"][i_a]["capture_rejected"] = "forged"
        forged_cap_rej["cases"][i_a]["lean"]["detail"] = "forged"
        forged_cap_rej["cases"][i_a]["leg_evidence"].pop(
            "capture_refusal_json", None
        )
        with self.assertRaisesRegex(ValueError, "capture_refusal_json"):
            cmd.validate_fuzz_report(forged_cap_rej)

        reused_cap_rej = json.loads(json.dumps(low_adm_valid))
        reused_cap_rej["cases"][i_a]["capture_rejected"] = reused_cap_rej[
            "cases"
        ][i_b]["capture_rejected"]
        reused_cap_rej["cases"][i_a]["lean"]["detail"] = reused_cap_rej[
            "cases"
        ][i_b]["lean"]["detail"]
        reused_cap_rej["cases"][i_a]["leg_evidence"][
            "capture_refusal_json"
        ] = reused_cap_rej["cases"][i_b]["leg_evidence"][
            "capture_refusal_json"
        ]
        with self.assertRaisesRegex(ValueError, "not bound to"):
            cmd.validate_fuzz_report(reused_cap_rej)

        empty_unsup_rej = json.loads(json.dumps(low_adm_valid))
        bad_raw = json.dumps(
            {
                "status": "unsupported",
                "diagnostics": ["1 unsupported"],
                "unsupported": [],
            }
        )
        bad_reason = f"capture unsupported: 1 unsupported ({bad_raw})"
        empty_unsup_rej["cases"][i_a]["capture_rejected"] = bad_reason
        empty_unsup_rej["cases"][i_a]["lean"]["detail"] = bad_reason
        empty_unsup_rej["cases"][i_a]["leg_evidence"][
            "capture_refusal_json"
        ] = bad_raw
        with self.assertRaisesRegex(ValueError, "case-bound `unsupported`"):
            cmd.validate_fuzz_report(empty_unsup_rej)

        # Mislabeled per-case `disclosed_gap` or stale `metrics.disclosed_gaps`
        # must fail closed.
        sc_idx = next(
            idx
            for idx, c in enumerate(_sample_fuzz_report()["cases"])
            if c["category"] == "scope_control"
        )
        bad_gap_case = _sample_fuzz_report()
        bad_gap_case["cases"][sc_idx]["evaluation"]["disclosed_gap"] = (
            "fuel_exhausted"
        )
        with self.assertRaisesRegex(ValueError, "disclosed_gap"):
            cmd.validate_fuzz_report(bad_gap_case)

        missing_gap_case = _sample_fuzz_report()
        missing_gap_case["cases"][sc_idx]["evaluation"].pop(
            "disclosed_gap", None
        )
        with self.assertRaisesRegex(ValueError, "disclosed_gap"):
            cmd.validate_fuzz_report(missing_gap_case)

        bad_gaps_metric = _sample_fuzz_report()
        bad_gaps_metric["metrics"]["disclosed_gaps"] = {"fuel_exhausted": 1}
        with self.assertRaisesRegex(ValueError, "disclosed_gaps"):
            cmd.validate_fuzz_report(bad_gaps_metric)

        # `expected_seed` and `expected_cases` bind the report to CLI flags.
        with self.assertRaisesRegex(ValueError, "requested 99"):
            cmd.validate_fuzz_report(_sample_fuzz_report(), expected_seed=99)
        with self.assertRaisesRegex(ValueError, "requested 64"):
            cmd.validate_fuzz_report(_sample_fuzz_report(), expected_cases=64)
        with self.assertRaisesRegex(ValueError, "requested 8"):
            cmd.validate_fuzz_report(
                _sample_fuzz_report(), expected_max_stmts=8
            )
        with self.assertRaisesRegex(ValueError, "ub_ratio"):
            cmd.validate_fuzz_report(
                _sample_fuzz_report(), expected_ub_ratio=0.05
            )
        missing_fuel = _sample_fuzz_report()
        missing_fuel.pop("fuel", None)
        with self.assertRaisesRegex(ValueError, "fuel"):
            cmd.validate_fuzz_report(missing_fuel)
        for bad_fuel in (True, 0, -5):
            invalid_fuel = _sample_fuzz_report()
            invalid_fuel["fuel"] = bad_fuel
            with self.assertRaisesRegex(ValueError, "fuel"):
                cmd.validate_fuzz_report(invalid_fuel)
        with self.assertRaisesRegex(ValueError, "requested 500"):
            cmd.validate_fuzz_report(_sample_fuzz_report(), expected_fuel=500)
        custom_fuel_detail = cmd.build_semantic_detail_report(
            diff_report=_sample_diff_report(),
            mir_eval_status={"executed": False, "passed": None},
            repo="google/zerocopy",
            branch="main",
            commit_sha="a" * 40,
            commit_unix_ts=1_780_000_000,
            environment_profile={"os": "linux"},
            fuzz_report=_sample_fuzz_report(fuel=777),
            fuzz_expected_fuel=777,
        )
        self.assertEqual(
            custom_fuel_detail["evidence_blocks"]["differential_fuzz"]["fuel"],
            777,
        )
        self.assertTrue(
            cmd.report_passes(
                custom_fuel_detail, require_fuzz=True, fuzz_expected_fuel=777
            )
        )
        self.assertFalse(
            cmd.report_passes(
                custom_fuel_detail, require_fuzz=True, fuzz_expected_fuel=1500
            )
        )
        no_fuel_detail = json.loads(json.dumps(custom_fuel_detail))
        no_fuel_detail["evidence_blocks"]["differential_fuzz"].pop("fuel", None)
        self.assertFalse(cmd.report_passes(no_fuel_detail, require_fuzz=True))
        mislabeled_cat = _sample_fuzz_report()
        mislabeled_cat["cases"][2]["category"] = "safe_admitted"
        mislabeled_cat["metrics"]["targeted_ub_probes"] -= 1
        mislabeled_cat["metrics"]["safe_admitted_cases"] += 1
        mislabeled_cat["metrics"]["admission_eligible_cases"] += 1
        mislabeled_cat["metrics"]["admitted_authority_ub_count"] += 1
        mislabeled_cat["metrics"]["ub_probes_agreed_count"] -= 1
        with self.assertRaisesRegex(
            ValueError, "deterministic campaign category"
        ):
            cmd.validate_fuzz_report(mislabeled_cat)
        self.assertFalse(
            cmd.report_passes(
                detail_low_budget,
                require_fuzz=True,
                fuzz_expected_max_stmts=6,
            )
        )

        for bad_argv in (
            ["--fuzz-cases", "0", "--allow-unknown-git"],
            ["--fuzz-cases", str(1 << 64), "--allow-unknown-git"],
            ["--fuzz-fuel", "0", "--allow-unknown-git"],
            ["--fuzz-fuel", str(1 << 64), "--allow-unknown-git"],
            ["--fuzz-seed", "-1", "--allow-unknown-git"],
            ["--fuzz-seed", str(1 << 64), "--allow-unknown-git"],
            ["--fuzz-min-admission-rate", "nan", "--allow-unknown-git"],
            ["--fuzz-min-admission-rate", "1.2", "--allow-unknown-git"],
        ):
            with (
                mock.patch.object(cmd, "maybe_run_mir_eval_manifest") as m_eval,
                mock.patch.object(cmd, "run_anneal_diff") as m_diff,
                self.assertRaises(ValueError),
            ):
                cmd.main(bad_argv)
            m_eval.assert_not_called()
            m_diff.assert_not_called()

        # Pointer-width host bounds also reject values above 32-bit
        # `usize::MAX`.
        for bad_32_flag in ("--fuzz-cases", "--fuzz-fuel"):
            with (
                mock.patch("struct.calcsize", return_value=4),
                mock.patch.object(cmd, "maybe_run_mir_eval_manifest") as m_eval,
                mock.patch.object(cmd, "run_anneal_diff") as m_diff,
                self.assertRaisesRegex(ValueError, str((1 << 32) - 1)),
            ):
                cmd.main([bad_32_flag, str(1 << 32), "--allow-unknown-git"])
            m_eval.assert_not_called()
            m_diff.assert_not_called()

    def test_move_reinit_evidence_and_requested_mir_eval_gates_fail_closed(
        self,
    ) -> None:
        # 1. Tampered or unverified `exercised_move_reinit` claims fail closed.
        missing_ev = _sample_fuzz_report()
        del missing_ev["cases"][0]["move_reinit_evidence"]
        with self.assertRaisesRegex(ValueError, "move_reinit_evidence"):
            cmd.validate_fuzz_report(missing_ev)

        stray_ev = _sample_fuzz_report()
        stray_ev["cases"][0]["exercised_move_reinit"] = False
        stray_ev["metrics"]["move_reinit_exercised_count"] -= 1
        with self.assertRaisesRegex(ValueError, "exercised_move_reinit=False"):
            cmd.validate_fuzz_report(stray_ev)

        copy_only_ev = _sample_fuzz_report()
        ev0 = copy_only_ev["cases"][0]["move_reinit_evidence"]
        ev0["blocks"][0]["statements"][1]["value"]["operand"]["kind"] = "copy"
        ev0["capture_body_sha256"] = cmd._canonical_capture_body_sha256(
            ev0["fn_identity"], ev0["arg_count"], ev0["local_tys"], ev0["blocks"]
        )
        copy_only_ev["cases"][0]["capture_body"]["capture_body_sha256"] = ev0[
            "capture_body_sha256"
        ]
        with self.assertRaisesRegex(ValueError, "Operand::Move"):
            cmd.validate_fuzz_report(copy_only_ev)

        zst_ev = _sample_fuzz_report()
        ev_z = zst_ev["cases"][0]["move_reinit_evidence"]
        ev_z["local_tys"][ev_z["local_slot"]]["tag_repr"] = {
            "kind": "zero_sized"
        }
        ev_z["capture_body_sha256"] = cmd._canonical_capture_body_sha256(
            ev_z["fn_identity"], ev_z["arg_count"], ev_z["local_tys"], ev_z["blocks"]
        )
        zst_ev["cases"][0]["capture_body"]["capture_body_sha256"] = ev_z[
            "capture_body_sha256"
        ]
        with self.assertRaisesRegex(ValueError, "not non-ZST"):
            cmd.validate_fuzz_report(zst_ev)

        bad_sha = _sample_fuzz_report()
        bad_sha["cases"][0]["move_reinit_evidence"]["capture_body_sha256"] = (
            "0" * 64
        )
        with self.assertRaisesRegex(ValueError, "capture_body_sha256"):
            cmd.validate_fuzz_report(bad_sha)

        bad_probe = _sample_fuzz_report()
        bad_probe["cases"][0]["move_reinit_evidence"]["lean_probe_line"] = (
            "ANNEAL_LEAN_CASE:other:BODY|0|crate::fuzz_case_0000|MR0:RETURNED:INT:i32:u:7"
        )
        with self.assertRaisesRegex(ValueError, "lean_probe_line"):
            cmd.validate_fuzz_report(bad_probe)

        bad_cfg = _sample_fuzz_report()
        ev_c = bad_cfg["cases"][0]["move_reinit_evidence"]
        # Move read into an unreachable block 1.
        read_stmt = ev_c["blocks"][0]["statements"].pop()
        ev_c["blocks"].append(
            {"statements": [read_stmt], "terminator": {"kind": "ret"}}
        )
        ev_c["read_step"] = {"step": 3, "block": 1, "stmt": 0}
        ev_c["lean_probe_line"] = (
            f"ANNEAL_LEAN_CASE:fuzz_s20261124_c0000:BODY|{ev_c['body_id']}|"
            f"{ev_c['fn_identity']}|MR1|{ev_c['local_slot']}|5|"
            "0,0,0|1,0,1|2,0,2|3,1,0:RETURNED:INT:i32:u:7"
        )
        ev_c["capture_body_sha256"] = cmd._canonical_capture_body_sha256(
            ev_c["fn_identity"], ev_c["arg_count"], ev_c["local_tys"], ev_c["blocks"]
        )
        bad_cfg["cases"][0]["capture_body"]["capture_body_sha256"] = ev_c[
            "capture_body_sha256"
        ]
        bad_cfg["cases"][0]["leg_evidence"]["lean_probe_line"] = ev_c[
            "lean_probe_line"
        ]
        with self.assertRaisesRegex(ValueError, "CFG blocks"):
            cmd.validate_fuzz_report(bad_cfg)

        # Forged summary without witness summaries fails `report_passes`.
        forged_detail = cmd.build_semantic_detail_report(
            diff_report=_sample_diff_report(),
            fuzz_report=_sample_fuzz_report(),
            mir_eval_status={"executed": False, "passed": None},
            repo="google/zerocopy",
            branch="main",
            commit_sha="a" * 40,
            commit_unix_ts=1_780_000_000,
            environment_profile={"os": "linux", "arch": "x86_64"},
        )
        forged_detail["evidence_blocks"]["differential_fuzz"][
            "move_reinit_witnesses"
        ] = []
        self.assertFalse(cmd.report_passes(forged_detail, require_fuzz=True))

        # 2. Requested `anneal_mir_eval_captured` leg is enforced end-to-end.
        with self.assertRaisesRegex(ValueError, "anneal_mir_eval_captured"):
            cmd.validate_fuzz_report(_sample_fuzz_report(), expect_mir_eval=True)
        with self.assertRaisesRegex(ValueError, "anneal_mir_eval_captured"):
            cmd.build_semantic_detail_report(
                diff_report=_sample_diff_report(),
                fuzz_report=_sample_fuzz_report(),
                mir_eval_status={"executed": True, "passed": True},
                repo="google/zerocopy",
                branch="main",
                commit_sha="a" * 40,
                commit_unix_ts=1_780_000_000,
                environment_profile={"os": "linux", "arch": "x86_64"},
                expect_mir_eval=True,
            )

        diff_4 = _sample_diff_report()
        diff_4["legs"].append("anneal_mir_eval_captured")
        for c in diff_4["cases"]:
            c["mir_eval"] = dict(c["lean"])
        fuzz_4 = _with_mir_eval_leg(_sample_fuzz_report())
        detail_4 = cmd.build_semantic_detail_report(
            diff_report=diff_4,
            fuzz_report=fuzz_4,
            mir_eval_status={"executed": True, "passed": True},
            repo="google/zerocopy",
            branch="main",
            commit_sha="a" * 40,
            commit_unix_ts=1_780_000_000,
            environment_profile={"os": "linux", "arch": "x86_64"},
            expect_mir_eval=True,
        )
        self.assertTrue(
            cmd.report_passes(detail_4, require_fuzz=True, require_mir_eval=True)
        )
        dropped_fuzz = json.loads(json.dumps(detail_4))
        dropped_fuzz["evidence_blocks"]["differential_fuzz"]["legs"] = [
            "rustc_compiled",
            "miri",
            "lean_step_core_captured",
        ]
        self.assertFalse(
            cmd.report_passes(
                dropped_fuzz, require_fuzz=True, require_mir_eval=True
            )
        )

        # CLI `main()` fails when `--mir-eval-bin` is requested but fuzz drops
        # Leg 3.
        with tempfile.TemporaryDirectory() as tmpd:
            root = Path(tmpd)
            anneal_dir = root / "anneal"
            anneal_dir.mkdir()
            mir_eval_bin = root / "anneal-mir-eval"
            mir_eval_bin.write_text("#!/bin/sh\n", encoding="utf-8")
            with (
                mock.patch.object(
                    cmd, "run_anneal_diff", return_value=(0, diff_4)
                ),
                mock.patch.object(
                    cmd, "run_anneal_fuzz", return_value=(0, _sample_fuzz_report())
                ),
                mock.patch.object(
                    cmd,
                    "_git_metadata",
                    return_value=("main", "a" * 40, 1_780_000_000),
                ),
                mock.patch.object(
                    cmd,
                    "_collect_environment",
                    return_value={"os": "linux", "arch": "x86_64"},
                ),
            ):
                with self.assertRaisesRegex(
                    ValueError, "anneal_mir_eval_captured"
                ):
                    cmd.main(
                        [
                            "--anneal-root",
                            str(anneal_dir),
                            "--mir-eval-bin",
                            str(mir_eval_bin),
                            "--no-self-check-oracle",
                        ]
                    )

            # Post-capture Lean `ToolError` (keeping `capture_body` + Leg-3
            # `mir_eval`) must emit failure reports & perf telemetry cleanly
            # rather than crashing `validate_fuzz_report`.
            post_cap_err = _with_mir_eval_leg(_sample_fuzz_report())
            pc0 = post_cap_err["cases"][0]
            pc0["lean"] = {
                "kind": "tool_error",
                "detail": "Lean fuzz probe failed (exit 1)",
            }
            pc0["evaluation"]["agreement"] = "authority_disagreement"
            pc0["leg_evidence"].pop("lean_probe_line", None)
            if pc0.get("exercised_move_reinit"):
                pc0["exercised_move_reinit"] = False
                pc0.pop("move_reinit_evidence", None)
                post_cap_err["metrics"]["move_reinit_exercised_count"] -= 1
            post_cap_err["metrics"]["admitted_cases"] -= 1
            post_cap_err["metrics"]["admission_rate"] = (
                post_cap_err["metrics"]["admitted_cases"]
                / post_cap_err["metrics"]["admission_eligible_cases"]
            )
            post_cap_err["metrics"]["bi_fault_equiv_count"] -= 1
            post_cap_err["metrics"]["authority_disagreement_count"] += 1
            post_cap_err["gate_error"] = "authority failure"

            out_json = root / "detail.json"
            perf_json = root / "perf_metrics.json"
            rec_json = root / "perf_record.json"
            with (
                mock.patch.object(
                    cmd, "run_anneal_diff", return_value=(0, diff_4)
                ),
                mock.patch.object(
                    cmd, "run_anneal_fuzz", return_value=(1, post_cap_err)
                ),
                mock.patch.object(
                    cmd,
                    "_git_metadata",
                    return_value=("main", "a" * 40, 1_780_000_000),
                ),
                mock.patch.object(
                    cmd,
                    "_collect_environment",
                    return_value={"os": "linux", "arch": "x86_64"},
                ),
                mock.patch("builtins.print"),
            ):
                rc_err = cmd.main(
                    [
                        "--anneal-root",
                        str(anneal_dir),
                        "--mir-eval-bin",
                        str(mir_eval_bin),
                        "--no-self-check-oracle",
                        "--output",
                        str(out_json),
                        "--perf-metrics-out",
                        str(perf_json),
                        "--perf-record-out",
                        str(rec_json),
                    ]
                )
            self.assertEqual(rc_err, 1)
            written_detail = json.loads(out_json.read_text(encoding="utf-8"))
            self.assertEqual(
                written_detail["evidence_blocks"]["differential_fuzz"][
                    "authority_disagreement_count"
                ],
                1,
            )
            self.assertEqual(
                written_detail["evidence_blocks"]["differential_fuzz"][
                    "mir_eval_verified_count"
                ],
                32,
            )
            self.assertTrue(perf_json.is_file())
            self.assertTrue(rec_json.is_file())

            # Pre-capture Lean `ToolError` without `capture_body` also passes
            # when `mir_eval` is a `ToolError`, but fails if forged non-error
            # `mir_eval` claims execution without `capture_body`.
            pre_cap_err = json.loads(json.dumps(post_cap_err))
            pre0 = pre_cap_err["cases"][0]
            pre0.pop("capture_body", None)
            with self.assertRaisesRegex(ValueError, "mir_eval_body_id"):
                cmd.validate_fuzz_report(pre_cap_err, expect_mir_eval=True)
            pre0["mir_eval"] = {
                "kind": "tool_error",
                "detail": "missing capture metadata",
            }
            pre0["leg_evidence"].pop("mir_eval_body_id", None)
            pre0["leg_evidence"].pop("mir_eval_raw_json", None)
            cmd.validate_fuzz_report(pre_cap_err, expect_mir_eval=True)


        # Enum return values (arbitrary or known enum kinds) are forbidden on
        # Stage-2 return outcomes even when repeated identically across all
        # legs, while valid enum values in `args` still pass validation.
        for bad_enum in (
            {
                "kind": "enum",
                "enum_type": "X",
                "variant": "Y",
                "variant_index": 999,
            },
            {
                "kind": "enum",
                "enum_type": "GenSignedTag",
                "variant": "Zero",
                "variant_index": 1,
            },
        ):
            enum_ret = _sample_fuzz_report()
            enum_ret["cases"][0]["rustc"] = {
                "kind": "returned",
                "value": bad_enum,
            }
            enum_ret["cases"][0]["miri"] = {
                "kind": "returned",
                "value": bad_enum,
            }
            enum_ret["cases"][0]["lean"] = {
                "kind": "returned",
                "value": bad_enum,
            }
            with self.assertRaisesRegex(ValueError, "enum return"):
                cmd.validate_fuzz_report(enum_ret)
        with self.assertRaisesRegex(ValueError, "invalid `enum` value"):
            cmd._validate_mir_value(
                {
                    "kind": "enum",
                    "enum_type": "GenSignedTag",
                    "variant": "Zero",
                    "variant_index": 99,
                },
                "arg",
                allow_enum=True,
            )

        # Reused or tampered per-case `args` fail deterministic campaign checks
        # even when `case_id`, `fn_name`, `case_index`, and `category` match.
        reused_args = _sample_fuzz_report()
        reused_args["cases"][1]["args"] = list(reused_args["cases"][0]["args"])
        with self.assertRaisesRegex(ValueError, "deterministic campaign inputs"):
            cmd.validate_fuzz_report(reused_args)

        missing_args = _sample_fuzz_report()
        del missing_args["cases"][0]["args"]
        with self.assertRaisesRegex(ValueError, "missing `args`"):
            cmd.validate_fuzz_report(missing_args)

        # Reused, forged, or missing `program_sha256` / `source` /
        # `capture_body_sha256` / `capture_fn_identity` must fail closed even
        # when `case_id`, `fn_name`, `category`, and `args` match.
        reused_prog_sha = _sample_fuzz_report()
        reused_prog_sha["cases"][1]["program_sha256"] = reused_prog_sha["cases"][0][
            "program_sha256"
        ]
        with self.assertRaisesRegex(ValueError, "duplicate `program_sha256`"):
            cmd.validate_fuzz_report(reused_prog_sha)

        forged_prog_sha = _sample_fuzz_report()
        forged_prog_sha["cases"][1]["program_sha256"] = "f" * 64
        with self.assertRaisesRegex(ValueError, "deterministic campaign digest"):
            cmd.validate_fuzz_report(forged_prog_sha)

        missing_prog_sha = _sample_fuzz_report()
        del missing_prog_sha["cases"][0]["program_sha256"]
        with self.assertRaisesRegex(ValueError, "program_sha256"):
            cmd.validate_fuzz_report(missing_prog_sha)

        forged_source = _sample_fuzz_report()
        forged_source["cases"][0]["source"] = "pub fn tampered() {}"
        with self.assertRaisesRegex(ValueError, "source"):
            cmd.validate_fuzz_report(forged_source)

        # Reused, forged, or missing `capture_body` / `leg_evidence` and
        # inconsistent `shrink_trace` / `shrink_verification` must fail closed.
        reused_exec_digest = _sample_fuzz_report()
        reused_exec_digest["cases"][1]["capture_body"] = dict(
            reused_exec_digest["cases"][0]["capture_body"]
        )
        with self.assertRaisesRegex(ValueError, "capture_body.fn_identity"):
            cmd.validate_fuzz_report(reused_exec_digest)

        tampered_blocks = _sample_fuzz_report()
        tampered_blocks["cases"][1]["capture_body"]["blocks"].append(
            {"statements": [], "terminator": {"kind": "ret"}}
        )
        with self.assertRaisesRegex(ValueError, "capture_body_sha256"):
            cmd.validate_fuzz_report(tampered_blocks)

        bad_cap_fn = _sample_fuzz_report()
        bad_cap_fn["cases"][1]["capture_body"]["fn_identity"] = "crate::fuzz_case_0000"
        with self.assertRaisesRegex(ValueError, "fn_identity"):
            cmd.validate_fuzz_report(bad_cap_fn)

        bad_ret_ty = _sample_fuzz_report()
        bad_ret_ty["cases"][1]["capture_body"]["local_tys"][0] = {"kind": "unit"}
        cb1 = bad_ret_ty["cases"][1]["capture_body"]
        cb1["capture_body_sha256"] = cmd._canonical_capture_body_sha256(
            cb1["fn_identity"], cb1["arg_count"], cb1["local_tys"], cb1["blocks"]
        )
        with self.assertRaisesRegex(ValueError, "expected return type"):
            cmd.validate_fuzz_report(bad_ret_ty)

        bad_param_ty = _sample_fuzz_report()
        bad_param_ty["cases"][1]["capture_body"]["local_tys"][1] = {"kind": "bool"}
        cb1p = bad_param_ty["cases"][1]["capture_body"]
        cb1p["capture_body_sha256"] = cmd._canonical_capture_body_sha256(
            cb1p["fn_identity"], cb1p["arg_count"], cb1p["local_tys"], cb1p["blocks"]
        )
        with self.assertRaisesRegex(ValueError, "expected param type"):
            cmd.validate_fuzz_report(bad_param_ty)

        missing_cap_body = _sample_fuzz_report()
        del missing_cap_body["cases"][1]["capture_body"]
        with self.assertRaisesRegex(ValueError, "capture_body"):
            cmd.validate_fuzz_report(missing_cap_body)

        mismatched_mr_binding = _sample_fuzz_report()
        mismatched_mr_binding["cases"][0]["capture_body"]["body_id"] = 999
        mismatched_mr_binding["cases"][0]["leg_evidence"]["lean_probe_line"] = (
            mismatched_mr_binding["cases"][0]["leg_evidence"][
                "lean_probe_line"
            ].replace(":BODY|0|", ":BODY|999|", 1)
        )
        with self.assertRaisesRegex(ValueError, "case capture binding"):
            cmd.validate_fuzz_report(mismatched_mr_binding)

        # Outcomes copied from another case while retaining valid capture_body
        # fail `leg_evidence` verification on every active leg.
        reused_miri = _sample_fuzz_report()
        reused_miri["cases"][1]["leg_evidence"]["miri_evidence"] = reused_miri[
            "cases"
        ][0]["leg_evidence"]["miri_evidence"]
        with self.assertRaisesRegex(ValueError, "miri_evidence"):
            cmd.validate_fuzz_report(reused_miri)

        bad_miri_val = _sample_fuzz_report()
        bad_miri_val["cases"][1]["leg_evidence"]["miri_evidence"] = (
            "ANNEAL_MIRI_RUN:fuzz_s20261124_c0001:fuzz_case_0001|"
            "ANNEAL_MIRI_CASE:fuzz_s20261124_c0001:INT:u32:999"
        )
        with self.assertRaisesRegex(ValueError, "disagrees with `miri` value"):
            cmd.validate_fuzz_report(bad_miri_val)

        reused_lean = _sample_fuzz_report()
        reused_lean["cases"][1]["leg_evidence"]["lean_probe_line"] = reused_lean[
            "cases"
        ][0]["leg_evidence"]["lean_probe_line"]
        with self.assertRaisesRegex(ValueError, "lean_probe_line"):
            cmd.validate_fuzz_report(reused_lean)

        reused_rustc = _sample_fuzz_report()
        reused_rustc["cases"][1]["leg_evidence"]["rustc_evidence"] = reused_rustc[
            "cases"
        ][0]["leg_evidence"]["rustc_evidence"]
        with self.assertRaisesRegex(ValueError, "rustc_evidence"):
            cmd.validate_fuzz_report(reused_rustc)

        bad_me_body = _with_mir_eval_leg(_sample_fuzz_report())
        bad_me_body["cases"][1]["leg_evidence"]["mir_eval_body_id"] = 999
        with self.assertRaisesRegex(ValueError, "mir_eval_body_id"):
            cmd.validate_fuzz_report(bad_me_body, expect_mir_eval=True)

        bad_me_raw = _with_mir_eval_leg(_sample_fuzz_report())
        cb1_me = bad_me_raw["cases"][1]["capture_body"]
        bad_me_raw["cases"][1]["leg_evidence"]["mir_eval_raw_json"] = json.dumps(
            {
                "body_id": cb1_me["body_id"],
                "identity": cb1_me["fn_identity"],
                "outcome": {
                    "kind": "returned",
                    "value": {
                        "kind": "returned",
                        "ret": {
                            "kind": "scalar",
                            "value": {"width": "i32", "signed": False, "bits": "999"},
                        },
                    },
                },
            }
        )
        with self.assertRaisesRegex(ValueError, "mir_eval_raw_json"):
            cmd.validate_fuzz_report(bad_me_raw, expect_mir_eval=True)

        # Emitted JSON belonging to another function body or missing identity
        # must fail closed even when the outcome matches.
        for bad_trace_patch in (
            {"body_id": 0},
            {"body_id": False},
            {"identity": "crate::fuzz_case_0000"},
            {"drop": ("body_id", "identity")},
        ):
            mismatched_me = _with_mir_eval_leg(_sample_fuzz_report())
            trace_obj = json.loads(
                mismatched_me["cases"][1]["leg_evidence"]["mir_eval_raw_json"]
            )
            if "drop" in bad_trace_patch:
                for k in bad_trace_patch["drop"]:
                    trace_obj.pop(k, None)
            else:
                trace_obj.update(bad_trace_patch)
            mismatched_me["cases"][1]["leg_evidence"]["mir_eval_raw_json"] = (
                json.dumps(trace_obj)
            )
            with self.assertRaisesRegex(ValueError, "mir_eval_raw_json"):
                cmd.validate_fuzz_report(mismatched_me, expect_mir_eval=True)

        # Non-returning `SafeAdmitted`/`BoundaryEdgeCase` cases (even when all
        # legs agree on panic/unwound) must NOT count toward `admitted_cases`.
        panic_admitted = _sample_fuzz_report()
        c0 = panic_admitted["cases"][0]
        assert c0["category"] == "safe_admitted"
        panic_out = {"kind": "panic", "detail": "panicked"}
        unwound_out = {
            "kind": "unwound",
            "detail": "Trusted.MirModel.TerminalOut.unwound",
        }
        c0["rustc"] = dict(panic_out)
        c0["miri"] = dict(panic_out)
        c0["lean"] = dict(unwound_out)
        c0["evaluation"]["agreement"] = "bi_fault_equiv_agreement"
        c0["evaluation"]["rustc_status"] = {"status": "agreed"}
        if c0.get("exercised_move_reinit"):
            c0["exercised_move_reinit"] = False
            c0.pop("move_reinit_evidence", None)
            panic_admitted["metrics"]["move_reinit_exercised_count"] -= 1
        c0["leg_evidence"] = _sample_leg_evidence(
            c0["case_id"],
            c0["fn_name"],
            miri=panic_out,
            lean=unwound_out,
            rustc=panic_out,
            capture_body=c0["capture_body"],
        )
        with self.assertRaisesRegex(ValueError, "admitted_cases"):
            cmd.validate_fuzz_report(panic_admitted)

        panic_admitted["metrics"]["admitted_cases"] -= 1
        panic_admitted["metrics"]["admission_rate"] = (
            panic_admitted["metrics"]["admitted_cases"]
            / panic_admitted["metrics"]["admission_eligible_cases"]
        )
        panic_admitted["min_admission_rate"] = 1.0
        cmd.validate_fuzz_report(panic_admitted)
        panic_detail = cmd.build_semantic_detail_report(
            diff_report=_sample_diff_report(),
            mir_eval_status={"executed": False, "passed": None},
            repo="google/zerocopy",
            branch="main",
            commit_sha="a" * 40,
            commit_unix_ts=1_780_000_000,
            environment_profile={"os": "linux"},
            fuzz_report=panic_admitted,
        )
        self.assertFalse(cmd.report_passes(panic_detail, require_fuzz=True))

        # Inconsistent, non-preserving, or unverified shrink traces fail closed.
        def _make_shrink_failing_report(
            *,
            preserve_sig: bool = True,
            admitted_ub: bool = False,
            preserve_admitted_ub: bool = True,
        ) -> dict[str, Any]:
            if admitted_ub:
                rep = _sample_fuzz_report(admitted_ub=1)
                fail_idx = next(
                    i
                    for i, c in enumerate(rep["cases"])
                    if c["category"] in ("safe_admitted", "boundary_edge_case")
                    and c["miri"]["kind"] == "undefined_behavior"
                )
            else:
                rep = _sample_fuzz_report(unsound=1)
                fail_idx = next(
                    i
                    for i, c in enumerate(rep["cases"])
                    if c["evaluation"]["agreement"] == "unsound_accept_critical"
                )
            fc = rep["cases"][fail_idx]
            _, _, _, param_tys, ret_ty, _ = cmd._expected_fuzz_case_details(
                rep["seed"],
                fail_idx,
                rep["max_stmts"],
                rep["ub_ratio"],
                default_fuel=rep["fuel"],
            )
            min_src = f"pub unsafe fn {fc['fn_name']}(p0: u32) -> u32 {{ p0 }}"
            min_args = [{"kind": "int", "int_kind": "u32", "bits": "0"}]
            min_sha = hashlib.sha256(min_src.encode("utf-8")).hexdigest()
            if admitted_ub:
                sv_miri = (
                    dict(fc["miri"])
                    if preserve_admitted_ub
                    else {"kind": "returned", "value": {"kind": "int", "int_kind": "u32", "bits": "0"}}
                )
                sv_lean = (
                    dict(fc["lean"])
                    if preserve_admitted_ub
                    else {"kind": "returned", "value": {"kind": "int", "int_kind": "u32", "bits": "0"}}
                )
                sv_rustc = (
                    None
                    if preserve_admitted_ub
                    else {
                        "kind": "returned",
                        "value": {"kind": "int", "int_kind": "u32", "bits": "0"},
                    }
                )
                sv_agree = "bi_fault_equiv_agreement"
                sv_rustc_st = "ignored_due_to_miri_ub" if preserve_admitted_ub else "agreed"
            else:
                sv_miri = (
                    dict(fc["miri"])
                    if preserve_sig
                    else {"kind": "returned", "value": {"kind": "int", "int_kind": "u32", "bits": "0"}}
                )
                sv_lean = dict(fc["lean"]) if preserve_sig else dict(sv_miri)
                sv_rustc = dict(fc["rustc"]) if preserve_sig else dict(sv_miri)
                sv_agree = (
                    "unsound_accept_critical"
                    if preserve_sig
                    else "bi_fault_equiv_agreement"
                )
                sv_rustc_st = (
                    fc["evaluation"]["rustc_status"]["status"]
                    if preserve_sig
                    else "agreed"
                )
            sv_cb = _sample_capture_body(
                fc["fn_name"], [("int", "u32")], ret_ty, body_id=0
            )
            sv_le = _sample_leg_evidence(
                fc["case_id"],
                fc["fn_name"],
                miri=sv_miri,
                lean=sv_lean,
                rustc=sv_rustc,
                capture_body=sv_cb,
            )
            fc["shrink_trace"] = {
                "original_nodes": 5,
                "shrunk_nodes": 2,
                "steps_evaluated": 3,
                "oracle_runs": 2,
                "cache_hits": 1,
                "converged_1_minimal": True,
                "minimized_source": min_src,
                "minimized_args": min_args,
            }
            fc["shrink_verification"] = {
                "fn_name": fc["fn_name"],
                "args": min_args,
                "program_sha256": min_sha,
                "fuel": fc["fuel"],
                "capture_body": sv_cb,
                "rustc": sv_rustc,
                "miri": sv_miri,
                "lean": sv_lean,
                "leg_evidence": sv_le,
                "evaluation": {
                    "agreement": sv_agree,
                    "is_spurious_lean_ub": False,
                    "rustc_status": {"status": sv_rustc_st},
                    "detail": "ok",
                },
            }
            return rep

        valid_shrink = _make_shrink_failing_report(preserve_sig=True)
        cmd.validate_fuzz_report(valid_shrink)
        valid_detail = cmd.build_semantic_detail_report(
            diff_report=_sample_diff_report(),
            mir_eval_status={"executed": False, "passed": None},
            repo="google/zerocopy",
            branch="main",
            commit_sha="a" * 40,
            commit_unix_ts=1_780_000_000,
            environment_profile={"os": "linux"},
            fuzz_report=valid_shrink,
        )
        self.assertIsNotNone(
            valid_detail["evidence_blocks"]["differential_fuzz"]["failing_cases"][0][
                "shrink_trace"
            ]
        )

        stray_shrink = _sample_fuzz_report()
        stray_shrink["cases"][0]["shrink_trace"] = valid_shrink["cases"][0].get(
            "shrink_trace"
        ) or {
            "original_nodes": 2,
            "shrunk_nodes": 1,
            "steps_evaluated": 1,
            "oracle_runs": 1,
            "cache_hits": 0,
            "converged_1_minimal": False,
            "minimized_source": "pub fn fuzz_case_0000() {}",
            "minimized_args": [],
        }
        with self.assertRaisesRegex(ValueError, "non-shrinkable"):
            cmd.validate_fuzz_report(stray_shrink)

        bad_nodes = _make_shrink_failing_report()
        bad_nodes["cases"][0]["shrink_trace"]["shrunk_nodes"] = 99
        with self.assertRaisesRegex(ValueError, "node bounds"):
            cmd.validate_fuzz_report(bad_nodes)

        bad_steps = _make_shrink_failing_report()
        bad_steps["cases"][0]["shrink_trace"]["steps_evaluated"] = 99
        with self.assertRaisesRegex(ValueError, "steps_evaluated"):
            cmd.validate_fuzz_report(bad_steps)

        no_verif = _make_shrink_failing_report()
        del no_verif["cases"][0]["shrink_verification"]
        with self.assertRaisesRegex(ValueError, "shrink_verification"):
            cmd.validate_fuzz_report(no_verif)

        bad_fn_min = _make_shrink_failing_report()
        bad_fn_min["cases"][0]["shrink_trace"]["minimized_source"] = "pub fn other() {}"
        with self.assertRaisesRegex(ValueError, "missing function"):
            cmd.validate_fuzz_report(bad_fn_min)

        drift_sig = _make_shrink_failing_report(preserve_sig=False)
        with self.assertRaisesRegex(ValueError, "failure signature"):
            cmd.validate_fuzz_report(drift_sig)

        with self.assertRaisesRegex(ValueError, "failure signature"):
            cmd.build_semantic_detail_report(
                diff_report=_sample_diff_report(),
                mir_eval_status={"executed": False, "passed": None},
                repo="google/zerocopy",
                branch="main",
                commit_sha="a" * 40,
                commit_unix_ts=1_780_000_000,
                environment_profile={"os": "linux"},
                fuzz_report=drift_sig,
            )

        # Admitted-category Miri UB (`admitted_authority_ub`) must permit and
        # validate `shrink_trace` + `shrink_verification`, while rejecting drift
        # to a non-UB outcome.
        admitted_ub_shrink = _make_shrink_failing_report(
            admitted_ub=True, preserve_admitted_ub=True
        )
        cmd.validate_fuzz_report(admitted_ub_shrink)
        admitted_ub_detail = cmd.build_semantic_detail_report(
            diff_report=_sample_diff_report(),
            mir_eval_status={"executed": False, "passed": None},
            repo="google/zerocopy",
            branch="main",
            commit_sha="a" * 40,
            commit_unix_ts=1_780_000_000,
            environment_profile={"os": "linux"},
            fuzz_report=admitted_ub_shrink,
        )
        self.assertEqual(
            len(admitted_ub_detail["evidence_blocks"]["differential_fuzz"]["failing_cases"]),
            1,
        )
        self.assertIsNotNone(
            admitted_ub_detail["evidence_blocks"]["differential_fuzz"]["failing_cases"][0][
                "shrink_verification"
            ]
        )

        admitted_ub_drift = _make_shrink_failing_report(
            admitted_ub=True, preserve_admitted_ub=False
        )
        with self.assertRaisesRegex(ValueError, "failure signature"):
            cmd.validate_fuzz_report(admitted_ub_drift)

        bad_sv_fuel = _make_shrink_failing_report(admitted_ub=True)
        for fc in bad_sv_fuel["cases"]:
            if fc.get("shrink_verification") is not None:
                fc["shrink_verification"]["fuel"] = fc["fuel"] + 1
                break
        with self.assertRaisesRegex(ValueError, "shrink_verification.fuel"):
            cmd.validate_fuzz_report(bad_sv_fuel)

        # Missed `TargetedUbProbe` cases (Miri failing to hit UB or Lean
        # conservatively refusing a UB probe) retain shrink traces & reproducers
        # when preserving the missed-probe signature, and reject drift.
        for miss_mode in ("non_ub", "conservative"):
            ub_miss_rep = _sample_fuzz_report()
            ub_idx = next(
                i
                for i, c in enumerate(ub_miss_rep["cases"])
                if c["category"] == "targeted_ub_probe"
            )
            uc = ub_miss_rep["cases"][ub_idx]
            ret_0 = {"kind": "returned", "value": {"kind": "int", "int_kind": "u32", "bits": "0"}}
            if miss_mode == "non_ub":
                uc["miri"] = dict(ret_0)
                uc["lean"] = dict(ret_0)
                uc["rustc"] = dict(ret_0)
                uc["evaluation"]["rustc_status"] = {"status": "agreed"}
                ub_miss_rep["metrics"]["ub_probes_agreed_count"] -= 1
                ub_miss_rep["metrics"]["rustc_agreed_count"] += 1
                ub_miss_rep["metrics"]["rustc_ignored_ub_count"] -= 1
            else:
                uc["lean"] = {
                    "kind": "unsupported",
                    "detail": "Trusted.MirSemantics.FaultKind.unsupported",
                }
                uc["evaluation"]["agreement"] = "conservative_over_approx_forward_sim_only"
                uc["evaluation"]["disclosed_gap"] = "unbridged_semantics"
                ub_miss_rep["metrics"]["ub_probes_agreed_count"] -= 1
                ub_miss_rep["metrics"]["bi_fault_equiv_count"] -= 1
                ub_miss_rep["metrics"]["conservative_over_approx_count"] += 1
                gaps = ub_miss_rep["metrics"].setdefault("disclosed_gaps", {})
                gaps["unbridged_semantics"] = gaps.get("unbridged_semantics", 0) + 1
            uc["leg_evidence"] = _sample_leg_evidence(
                uc["case_id"],
                uc["fn_name"],
                miri=uc["miri"],
                lean=uc["lean"],
                rustc=uc["rustc"],
                capture_body=uc["capture_body"],
            )
            _, _, _, _, ret_ty, _ = cmd._expected_fuzz_case_details(
                ub_miss_rep["seed"],
                ub_idx,
                ub_miss_rep["max_stmts"],
                ub_miss_rep["ub_ratio"],
                default_fuel=ub_miss_rep["fuel"],
            )
            min_src = f"pub unsafe fn {uc['fn_name']}(p0: u32) -> u32 {{ p0 }}"
            min_args = [{"kind": "int", "int_kind": "u32", "bits": "0"}]
            min_sha = hashlib.sha256(min_src.encode("utf-8")).hexdigest()
            sv_cb = _sample_capture_body(
                uc["fn_name"], [("int", "u32")], ret_ty, body_id=0
            )
            sv_le = _sample_leg_evidence(
                uc["case_id"],
                uc["fn_name"],
                miri=uc["miri"],
                lean=uc["lean"],
                rustc=uc["rustc"],
                capture_body=sv_cb,
            )
            uc["shrink_trace"] = {
                "original_nodes": 5,
                "shrunk_nodes": 2,
                "steps_evaluated": 3,
                "oracle_runs": 2,
                "cache_hits": 1,
                "converged_1_minimal": True,
                "minimized_source": min_src,
                "minimized_args": min_args,
            }
            uc["shrink_verification"] = {
                "fn_name": uc["fn_name"],
                "args": min_args,
                "program_sha256": min_sha,
                "fuel": uc["fuel"],
                "capture_body": sv_cb,
                "rustc": None if uc["rustc"] is None else dict(uc["rustc"]),
                "miri": dict(uc["miri"]),
                "lean": dict(uc["lean"]),
                "leg_evidence": sv_le,
                "evaluation": {
                    "agreement": uc["evaluation"]["agreement"],
                    **(
                        {"disclosed_gap": uc["evaluation"]["disclosed_gap"]}
                        if "disclosed_gap" in uc["evaluation"]
                        else {}
                    ),
                    "is_spurious_lean_ub": False,
                    "rustc_status": dict(uc["evaluation"]["rustc_status"]),
                    "detail": "ok",
                },
            }
            cmd.validate_fuzz_report(ub_miss_rep)
            miss_detail = cmd.build_semantic_detail_report(
                diff_report=_sample_diff_report(),
                mir_eval_status={"executed": False, "passed": None},
                repo="google/zerocopy",
                branch="main",
                commit_sha="a" * 40,
                commit_unix_ts=1_780_000_000,
                environment_profile={"os": "linux"},
                fuzz_report=ub_miss_rep,
            )
            failing_ub = [
                fc
                for fc in miss_detail["evidence_blocks"]["differential_fuzz"][
                    "failing_cases"
                ]
                if fc["id"] == uc["case_id"]
            ]
            self.assertEqual(len(failing_ub), 1)
            self.assertIsNotNone(failing_ub[0]["shrink_trace"])

            # Drifting `shrink_verification` to agreeing UB must fail closed.
            drifted_ub = json.loads(json.dumps(ub_miss_rep))
            duc = drifted_ub["cases"][ub_idx]
            sv = duc["shrink_verification"]
            sv["rustc"] = None
            sv["miri"] = {"kind": "undefined_behavior", "detail": "div by zero"}
            sv["lean"] = {
                "kind": "undefined_behavior",
                "detail": "Trusted.MirSemantics.FaultKind.undefined",
            }
            sv["evaluation"] = {
                "agreement": "bi_fault_equiv_agreement",
                "is_spurious_lean_ub": False,
                "rustc_status": {"status": "ignored_due_to_miri_ub"},
                "detail": "ok",
            }
            sv["leg_evidence"] = _sample_leg_evidence(
                duc["case_id"],
                duc["fn_name"],
                miri=sv["miri"],
                lean=sv["lean"],
                rustc=sv["rustc"],
                capture_body=sv["capture_body"],
            )
            with self.assertRaisesRegex(ValueError, "failure signature"):
                cmd.validate_fuzz_report(drifted_ub)

        # Per-case effective `fuel` validation: `ScopeControl` loop variants are
        # capped at `min(default_fuel, 40)` both above and below `40`, and
        # mismatched/missing case-level `fuel` fails closed.
        loop_scope_idx = next(
            i
            for i in range(64)
            if cmd._expected_fuzz_case_details(
                20261124, i, 6, 0.20, default_fuel=1500
            )[5]
            == 40
        )
        self.assertEqual(
            cmd._expected_fuzz_case_details(
                20261124, loop_scope_idx, 6, 0.20, default_fuel=18
            )[5],
            18,
        )
        small_fuel_rep = _sample_fuzz_report(fuel=18)
        self.assertEqual(small_fuel_rep["cases"][loop_scope_idx]["fuel"], 18)
        cmd.validate_fuzz_report(small_fuel_rep, expected_fuel=18)

        mismatched_case_fuel = _sample_fuzz_report(fuel=1500)
        self.assertEqual(mismatched_case_fuel["cases"][loop_scope_idx]["fuel"], 40)
        mismatched_case_fuel["cases"][loop_scope_idx]["fuel"] = 1500
        with self.assertRaisesRegex(ValueError, "expected effective fuel"):
            cmd.validate_fuzz_report(mismatched_case_fuel)

        missing_case_fuel = _sample_fuzz_report(fuel=1500)
        del missing_case_fuel["cases"][0]["fuel"]
        with self.assertRaisesRegex(ValueError, "invalid or missing `fuel`"):
            cmd.validate_fuzz_report(missing_case_fuel)

        missing_rustc_rep = _sample_fuzz_report(fuel=1500)
        missing_rustc_rep["cases"][0]["rustc"] = None
        with self.assertRaisesRegex(ValueError, "missing `rustc` outcome"):
            cmd.validate_fuzz_report(missing_rustc_rep)

        # Shared golden vectors tying Python's regenerated
        # `(category, arg_count, program_sha256)` directly to Rust
        # `gen.rs::golden_program_digests_match_validator_mirror`.
        for seed, max_stmts, ub_ratio, idx, exp_cat, exp_sha, exp_argc in (
            (20261124, 6, 0.20, 0, "safe_admitted", "e2fd491696d6681001803da57fdb27583286c5f63c65c3a5aa2ab78b3f4ba25c", 5),
            (20261124, 6, 0.20, 1, "boundary_edge_case", "1336e54688c1a79fc73cfcab3fb9728864384b5e6eeb6187906d138efeb10509", 2),
            (20261124, 6, 0.20, 2, "targeted_ub_probe", "6ce98615e3c587ef8276dca58c32b0384cd7b2005f2dd4d8afacbcc0e8f0b4e8", 2),
            (20261124, 6, 0.20, 3, "scope_control", "5a9874d0bb7a05f49ee57b82aa7dc57a31d241059ce7bebf691c102317c866d4", 1),
            (20261125, 1, 0.0, 1, "boundary_edge_case", "408a8e8c9a4b4eda02d74bc79eedf7b8818f1bae5f78607eeda328e31ffb9612", 2),
            (9001, 3, 0.85, 1, "boundary_edge_case", "bb5fe843aaae862ab016b85c57a740bb4e1675f3662ac8cb543f5d25de4422cd", 4),
            (314159, 12, 0.20, 0, "safe_admitted", "9953702f5c9b04428987a0edb8a728d22013b258135df008dc6cd5a331694eaa", 3),
        ):
            cat, args, sha = cmd._expected_fuzz_case_spec(
                seed, idx, max_stmts, ub_ratio
            )
            self.assertEqual((cat, len(args), sha), (exp_cat, exp_argc, exp_sha))

    def test_bare_command_resolution_rejects_symlinks_and_allows_rustup_proxy(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as tmpd:
            root = Path(tmpd).resolve()
            anneal_dir = root / "anneal"
            anneal_dir.mkdir()
            mir_dir = root / "eval"
            (mir_dir / "target" / "debug").mkdir(parents=True)
            manifest = mir_dir / "Cargo.toml"
            manifest.write_text(
                '[package]\nname = "anneal-mir-eval"\nversion = "0.1.0"\n',
                encoding="utf-8",
            )
            built_bin = mir_dir / "target" / "debug" / "anneal-mir-eval"
            built_bin.write_text("", encoding="utf-8")

            clean_bin = root / "clean-bin"
            clean_bin.mkdir()
            real_cargo = clean_bin / "cargo"
            real_cargo.write_text("", encoding="utf-8")
            real_cargo.chmod(0o755)
            real_rustc = clean_bin / "rustc"
            real_rustc.write_text("", encoding="utf-8")
            real_rustc.chmod(0o755)
            real_lean = clean_bin / "lean"
            real_lean.write_text("", encoding="utf-8")
            real_lean.chmod(0o755)

            # An unused earlier symlinked PATH directory (no matching binary)
            # must be skipped, just like Debian/Ubuntu `/bin -> usr/bin`.
            unused_sym_dir = root / "unused-sym-dir"
            os.symlink(root / "anneal", unused_sym_dir)

            artifact_stdout = (
                json.dumps(
                    {
                        "reason": "compiler-artifact",
                        "manifest_path": str(manifest),
                        "target": {"kind": ["bin"], "name": "anneal-mir-eval"},
                        "profile": {"test": False},
                        "executable": str(built_bin),
                    }
                )
                + "\n"
            )
            diff_payload = json.dumps(_sample_diff_report())
            fuzz_payload = json.dumps(_sample_fuzz_report())
            seen_invocations: list[list[str]] = []

            def _mock_exec(args: list[str], **_kwargs: Any) -> mock.Mock:
                seen_invocations.append(list(args))
                if "build" in args:
                    priv_td = Path(args[args.index("--target-dir") + 1])
                    out_exe = priv_td / "debug" / "anneal-mir-eval"
                    out_exe.parent.mkdir(parents=True, exist_ok=True)
                    out_exe.write_bytes(b"bare-mir-eval")
                    mp_str = (
                        args[args.index("--manifest-path") + 1]
                        if "--manifest-path" in args
                        else str(manifest.resolve())
                    )
                    return mock.Mock(
                        returncode=0,
                        stdout=json.dumps(
                            {
                                "reason": "compiler-artifact",
                                "manifest_path": mp_str,
                                "target": {
                                    "kind": ["bin"],
                                    "name": "anneal-mir-eval",
                                },
                                "executable": str(out_exe),
                            }
                        )
                        + "\n",
                        stderr="",
                    )
                if "fuzz" in args:
                    return mock.Mock(
                        returncode=0, stdout=fuzz_payload, stderr=""
                    )
                if "run" in args and "--json" in args:
                    return mock.Mock(
                        returncode=0, stdout=diff_payload, stderr=""
                    )
                if "--version" in args:
                    return mock.Mock(
                        returncode=0, stdout="tool 1.2.3\n", stderr=""
                    )
                return mock.Mock(returncode=0, stdout="", stderr="")

            with (
                _patch_clean_tool_env(
                    {"PATH": f"{unused_sym_dir}{os.pathsep}{clean_bin}"}
                ),
                _patch_subprocess_exec(side_effect=_mock_exec),
            ):
                status, exe = cmd.maybe_run_mir_eval_manifest(
                    manifest, skip_tests=True
                )
                assert exe is not None
                self.assertIn(".anneal-isolated-bins", str(exe))
                self.assertEqual(os.lstat(exe).st_nlink, 1)
                self.assertEqual(exe.read_bytes(), b"bare-mir-eval")
                self.assertIsNone(status["passed"])
                cmd.run_anneal_diff(
                    anneal_root=anneal_dir,
                    manifest=None,
                    capture_bin=None,
                    mir_eval_bin=None,
                    cache_root=None,
                    self_check_oracle=False,
                )
                cmd.run_anneal_fuzz(
                    anneal_root=anneal_dir,
                    capture_bin=None,
                    mir_eval_bin=None,
                    cache_root=None,
                    seed=20261124,
                    cases=8,
                    max_stmts=6,
                    ub_ratio=0.2,
                    min_admission_rate=0.9,
                )
                env_info = cmd._collect_environment(anneal_dir)
                self.assertEqual(env_info["rustc_version"], "tool 1.2.3")
                self.assertEqual(env_info["lean_version"], "tool 1.2.3")
                with mock.patch.dict(
                    os.environ,
                    {"CARGO": "cargo", "RUSTC": "rustc"},
                    clear=False,
                ):
                    built_env = cmd._build_child_env(root)
                    self.assertEqual(built_env["CARGO"], str(real_cargo))
                    self.assertEqual(built_env["RUSTC"], str(real_rustc))
            for idx_call in (0, 1, 2):
                self.assertNotEqual(seen_invocations[idx_call][0], str(real_cargo))
                self.assertIn(".anneal-isolated-bins", seen_invocations[idx_call][0])
                self.assertEqual(Path(seen_invocations[idx_call][0]).name, "cargo")
            self.assertEqual(seen_invocations[3][0], str(real_rustc))
            self.assertEqual(seen_invocations[4][0], str(real_lean))

            # Unset `CARGO`/`RUSTC` resolve `-> rustup` proxies to validated
            # toolchain binaries before invoking Cargo or
            # `_collect_environment`; symlinked/hardlinked
            # `HOME/.rustup/settings.toml` or resolved toolchain executables
            # fail closed.
            rustup_bin = root / "rustup-bin"
            rustup_bin.mkdir()
            real_rustup = rustup_bin / "rustup"
            real_rustup.write_text("", encoding="utf-8")
            real_rustup.chmod(0o755)
            os.symlink("rustup", rustup_bin / "cargo")
            os.symlink("rustup", rustup_bin / "rustc")
            rustup_tc_bin = root / "rustup-toolchain" / "bin"
            rustup_tc_bin.mkdir(parents=True)
            resolved_tc_cargo = rustup_tc_bin / "cargo"
            resolved_tc_rustc = rustup_tc_bin / "rustc"
            for exe in (resolved_tc_cargo, resolved_tc_rustc):
                exe.write_text("", encoding="utf-8")
                exe.chmod(0o755)
            clean_home = root / "clean-rustup-home"
            (clean_home / ".rustup").mkdir(parents=True)
            settings_toml = clean_home / ".rustup" / "settings.toml"
            settings_toml.write_text('version = "12"\n', encoding="utf-8")

            seen_invocations.clear()
            rustup_seen_envs: list[dict[str, str]] = []
            which_calls: list[list[str]] = []

            def _mock_rustup_exec(args: list[str], **kwargs: Any) -> Any:
                rustup_seen_envs.append(dict(kwargs.get("env") or {}))
                if len(args) >= 3 and args[1] == "which":
                    which_calls.append(list(args))
                    if args[2] == "cargo":
                        return mock.Mock(
                            returncode=0,
                            stdout=f"{resolved_tc_cargo}\n",
                            stderr="",
                        )
                    if args[2] == "rustc":
                        return mock.Mock(
                            returncode=0,
                            stdout=f"{resolved_tc_rustc}\n",
                            stderr="",
                        )
                return _mock_exec(args, **kwargs)

            with (
                _patch_clean_tool_env(
                    {
                        "PATH": f"{rustup_bin}{os.pathsep}{root / 'rogue-ambient-dir'}",
                        "HOME": str(clean_home),
                        "RUSTUP_HOME": "/tmp/evil-rustup-home",
                        "RUSTUP_TOOLCHAIN": "evil-nightly",
                    }
                ),
                _patch_subprocess_exec(side_effect=_mock_rustup_exec),
            ):
                cmd.maybe_run_mir_eval_manifest(manifest, skip_tests=True)
                env_rustup = cmd._collect_environment(anneal_dir)
            cargo_calls = [a for a in seen_invocations if "build" in a]
            ver_calls = [a for a in seen_invocations if "--version" in a]
            self.assertGreaterEqual(len(which_calls), 3)
            for wc in which_calls:
                self.assertNotEqual(wc[0], str(real_rustup))
                self.assertIn(".anneal-isolated-bins", wc[0])
                self.assertEqual(Path(wc[0]).name, "rustup")
            self.assertEqual(len(cargo_calls), 1)
            self.assertNotEqual(cargo_calls[0][0], str(resolved_tc_cargo))
            self.assertIn(".anneal-isolated-bins", cargo_calls[0][0])
            self.assertEqual(Path(cargo_calls[0][0]).name, "cargo")
            self.assertIn(
                f'target."cfg(all())".linker=',
                " ".join(cargo_calls[0]),
            )
            self.assertEqual(len(ver_calls), 1)
            self.assertNotEqual(ver_calls[0][0], str(resolved_tc_rustc))
            self.assertIn(".anneal-isolated-bins", ver_calls[0][0])
            self.assertEqual(Path(ver_calls[0][0]).name, "rustc")
            self.assertEqual(env_rustup["rustc_version"], "tool 1.2.3")
            self.assertEqual(env_rustup["lean_version"], "unknown")
            for child_e in rustup_seen_envs:
                self.assertEqual(child_e.get("RUSTUP_HOME"), "/tmp/evil-rustup-home")
                self.assertEqual(child_e.get("RUSTUP_TOOLCHAIN"), "evil-nightly")
            # Confirm Cargo child env stages immutable real binaries and
            # drops poisoned ambient PATH entries.
            build_env = next(
                e
                for e in rustup_seen_envs
                if e.get("CARGO") == cargo_calls[0][0]
            )
            self.assertNotEqual(build_env.get("RUSTC"), str(resolved_tc_rustc))
            self.assertIn(".anneal-isolated-bins", build_env.get("RUSTC", ""))
            self.assertEqual(Path(build_env["RUSTC"]).name, "rustc")
            self.assertNotIn("rogue-ambient-dir", build_env.get("PATH", ""))

            # Symlinked `HOME/.rustup` or symlinked/hardlinked `settings.toml`
            # fails closed for rustup proxies before invoking any subprocess.
            sym_home = root / "sym-rustup-home"
            sym_home.mkdir()
            evil_rustup_target = root / "evil-rustup-target"
            evil_rustup_target.mkdir()
            os.symlink(evil_rustup_target, sym_home / ".rustup")
            bad_settings_home = root / "bad-settings-home"
            (bad_settings_home / ".rustup").mkdir(parents=True)
            evil_settings = root / "evil-settings.toml"
            evil_settings.write_text('default_toolchain = "evil"\n', encoding="utf-8")
            os.symlink(evil_settings, bad_settings_home / ".rustup" / "settings.toml")
            hard_settings_home = root / "hard-settings-home"
            (hard_settings_home / ".rustup").mkdir(parents=True)
            os.link(evil_settings, hard_settings_home / ".rustup" / "settings.toml")
            for bad_home, pat in (
                (sym_home, "symlink"),
                (bad_settings_home, "symlink"),
                (hard_settings_home, "hardlink"),
            ):
                with (
                    _patch_clean_tool_env(
                        {"PATH": str(rustup_bin), "HOME": str(bad_home)}
                    ),
                    _patch_subprocess_exec() as no_exec,
                ):
                    with self.assertRaisesRegex(ValueError, pat):
                        cmd.maybe_run_mir_eval_manifest(manifest, skip_tests=True)
                    with self.assertRaisesRegex(ValueError, pat):
                        cmd.run_anneal_diff(
                            anneal_root=anneal_dir,
                            manifest=None,
                            capture_bin=None,
                            mir_eval_bin=None,
                            cache_root=None,
                            self_check_oracle=False,
                        )
                    with self.assertRaisesRegex(ValueError, pat):
                        cmd._collect_environment(anneal_dir)
                    no_exec.assert_not_called()

            # `rustup which` returning a symlinked or hardlinked toolchain
            # binary fails closed before running Cargo.
            sym_tc_cargo = root / "sym-tc-cargo"
            os.symlink(resolved_tc_cargo, sym_tc_cargo)

            def _mock_bad_rustup_which(args: list[str], **_kwargs: Any) -> Any:
                if len(args) >= 3 and args[1] == "which" and args[2] == "cargo":
                    return mock.Mock(
                        returncode=0, stdout=f"{sym_tc_cargo}\n", stderr=""
                    )
                return _mock_exec(args, **_kwargs)

            with (
                _patch_clean_tool_env(
                    {"PATH": str(rustup_bin), "HOME": str(clean_home)}
                ),
                _patch_subprocess_exec(side_effect=_mock_bad_rustup_which),
            ):
                with self.assertRaisesRegex(ValueError, "symlink"):
                    cmd.maybe_run_mir_eval_manifest(manifest, skip_tests=True)

            with (
                _patch_clean_tool_env(
                    {"PATH": str(rustup_bin), "CARGO": "cargo"}
                ),
                _patch_subprocess_exec() as no_exec,
            ):
                with self.assertRaisesRegex(ValueError, "symlink"):
                    cmd.maybe_run_mir_eval_manifest(manifest, skip_tests=True)
                no_exec.assert_not_called()

            # Symlinked `rustup` target, non-rustup symlink, symlinked PATH
            # entry containing `cargo`, and missing `cargo` in PATH all fail
            # closed before `subprocess.run`.
            bad_rustup_dir = root / "bad-rustup"
            bad_rustup_dir.mkdir()
            os.symlink(real_rustup, bad_rustup_dir / "rustup")
            os.symlink("rustup", bad_rustup_dir / "cargo")

            evil_sym_dir = root / "evil-sym"
            evil_sym_dir.mkdir()
            os.symlink(real_cargo, evil_sym_dir / "cargo")
            os.symlink(real_lean, evil_sym_dir / "lean")

            sym_path_dir = root / "sym-path-dir"
            os.symlink(clean_bin, sym_path_dir)

            empty_dir = root / "empty-dir"
            empty_dir.mkdir()

            # Hardlinked `cargo`, `rustc`, and sibling `rustup` proxies must all
            # fail closed (both on `PATH` and via separator paths) before any
            # subprocess invocation.
            hard_src = root / "hard-src-bin"
            hard_src.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            hard_src.chmod(0o755)
            hard_cargo_dir = root / "hard-cargo-bin"
            hard_cargo_dir.mkdir()
            os.link(hard_src, hard_cargo_dir / "cargo")
            (hard_cargo_dir / "rustc").write_text("#!/bin/sh\n", encoding="utf-8")
            (hard_cargo_dir / "rustc").chmod(0o755)

            hard_rustc_dir = root / "hard-rustc-bin"
            hard_rustc_dir.mkdir()
            (hard_rustc_dir / "cargo").write_text("#!/bin/sh\n", encoding="utf-8")
            (hard_rustc_dir / "cargo").chmod(0o755)
            os.link(hard_src, hard_rustc_dir / "rustc")

            hard_rustup_dir = root / "hard-rustup-bin"
            hard_rustup_dir.mkdir()
            os.link(hard_src, hard_rustup_dir / "rustup")
            os.symlink("rustup", hard_rustup_dir / "cargo")
            os.symlink("rustup", hard_rustup_dir / "rustc")

            for bad_path in (
                str(bad_rustup_dir),
                str(evil_sym_dir),
                str(hard_cargo_dir),
                str(hard_rustc_dir),
                str(hard_rustup_dir),
                f"{sym_path_dir}{os.pathsep}{clean_bin}",
                str(empty_dir),
                "",
            ):
                with (
                    _patch_clean_tool_env({"PATH": bad_path}),
                    _patch_subprocess_exec() as no_exec,
                ):
                    with self.assertRaises(ValueError):
                        cmd.maybe_run_mir_eval_manifest(
                            manifest, skip_tests=True
                        )
                    with self.assertRaises(ValueError):
                        cmd.run_anneal_diff(
                            anneal_root=anneal_dir,
                            manifest=None,
                            capture_bin=None,
                            mir_eval_bin=None,
                            cache_root=None,
                            self_check_oracle=False,
                        )
                    with self.assertRaises(ValueError):
                        cmd.run_anneal_fuzz(
                            anneal_root=anneal_dir,
                            capture_bin=None,
                            mir_eval_bin=None,
                            cache_root=None,
                            seed=20261124,
                            cases=8,
                            max_stmts=6,
                            ub_ratio=0.2,
                            min_admission_rate=0.9,
                        )
                    no_exec.assert_not_called()

            with _patch_clean_tool_env(
                {"PATH": str(rustup_bin), "CARGO": "cargo"}
            ):
                with self.assertRaisesRegex(ValueError, "symlink"):
                    cmd._build_child_env(root)

            with _patch_clean_tool_env(
                {"PATH": str(rustup_bin), "RUSTC": "rustc"}
            ):
                with self.assertRaisesRegex(ValueError, "symlink"):
                    cmd._build_child_env(root)

            for env_key, rel_hard in (
                ("CARGO", "./hard-cargo-bin/cargo"),
                ("RUSTC", "./hard-rustc-bin/rustc"),
            ):
                with _patch_clean_tool_env(
                    {"PATH": str(clean_bin), env_key: rel_hard}
                ):
                    with self.assertRaisesRegex(ValueError, "hardlink"):
                        cmd._build_child_env(root)

            # Unset `lean` on PATH pointing to a hardlinked multiplexer (e.g.
            # `elan`) falls back without executing the hardlinked binary.
            hard_lean_dir = root / "hard-lean-bin"
            hard_lean_dir.mkdir()
            (hard_lean_dir / "rustc").write_text("#!/bin/sh\n", encoding="utf-8")
            os.link(hard_src, hard_lean_dir / "lean")
            with (
                _patch_clean_tool_env(
                    {"PATH": str(hard_lean_dir), "ELAN_HOME": str(root / "no-elan")}
                ),
                _patch_subprocess_exec(
                    return_value=mock.Mock(returncode=0, stdout="tool 1.2.3\n", stderr=""),
                ) as lean_fb_mock,
            ):
                env_hard_lean = cmd._collect_environment(anneal_dir)
            self.assertEqual(env_hard_lean["lean_version"], "unknown")
            lean_fb_mock.assert_called_once()
            self.assertEqual(
                lean_fb_mock.call_args.args[0][0],
                str(hard_lean_dir / "rustc"),
            )

            with (
                _patch_clean_tool_env({"PATH": str(evil_sym_dir)}),
                _patch_subprocess_exec() as no_exec,
            ):
                with self.assertRaisesRegex(ValueError, "symlink"):
                    cmd._collect_environment(anneal_dir)
                no_exec.assert_not_called()

            with (
                _patch_clean_tool_env(
                    {"PATH": str(clean_bin), "ANNEAL_LEAN": "evil-lean"}
                ),
                _patch_subprocess_exec() as no_exec,
            ):
                os.symlink(real_lean, clean_bin / "evil-lean")
                with self.assertRaisesRegex(ValueError, "symlink"):
                    cmd._collect_environment(anneal_dir)
                no_exec.assert_not_called()

            # Child executable overrides (`ANNEAL_LEAN`, `ANNEAL_MVP_LEAN`,
            # `ANNEAL_CAPTURE`, `ANNEAL_CLI`, `ANNEAL_AUDITOR`) must reject
            # symlinked leaves and symlinked parent dirs before launching.
            sym_exec_leaf = root / "sym-exec-leaf"
            os.symlink(real_lean, sym_exec_leaf)
            sym_exec_dir = root / "sym-exec-dir"
            os.symlink(clean_bin, sym_exec_dir)
            for exec_var in (
                "ANNEAL_LEAN",
                "ANNEAL_MVP_LEAN",
                "ANNEAL_CAPTURE",
                "ANNEAL_MVP_CAPTURE",
                "ANNEAL_CLI",
                "ANNEAL_MVP_CLI",
                "ANNEAL_AUDITOR",
            ):
                for bad_exec in (
                    str(sym_exec_leaf),
                    "sym-exec-leaf",
                    str(sym_exec_dir / "lean"),
                    "sym-exec-dir/lean",
                ):
                    prev_cwd = Path.cwd()
                    try:
                        os.chdir(root)
                        with (
                            _patch_clean_tool_env(
                                {"PATH": str(clean_bin), exec_var: bad_exec}
                            ),
                            _patch_subprocess_exec() as no_exec,
                        ):
                            with self.assertRaisesRegex(ValueError, "symlink"):
                                cmd._build_child_env(root)
                            with self.assertRaisesRegex(ValueError, "symlink"):
                                cmd.run_anneal_diff(
                                    anneal_root=anneal_dir,
                                    manifest=None,
                                    capture_bin=None,
                                    mir_eval_bin=None,
                                    cache_root=None,
                                    self_check_oracle=False,
                                )
                            with self.assertRaisesRegex(ValueError, "symlink"):
                                cmd.run_anneal_fuzz(
                                    anneal_root=anneal_dir,
                                    capture_bin=None,
                                    mir_eval_bin=None,
                                    cache_root=None,
                                    seed=20261124,
                                    cases=8,
                                    max_stmts=6,
                                    ub_ratio=0.2,
                                    min_admission_rate=0.9,
                                )
                            no_exec.assert_not_called()
                    finally:
                        os.chdir(prev_cwd)

            # `ANNEAL_LEAN` and `ANNEAL_MVP_LEAN` in `_build_child_env` must
            # reject hardlinks and resolve/validate bare `PATH` tokens before
            # launching `anneal-diff` (unlike Cargo-built Rust binaries).
            hard_lean = root / "hard-lean"
            os.link(real_lean, hard_lean)
            os.link(real_lean, clean_bin / "hard-path-lean")
            path_nlink1_lean = clean_bin / "path-clean-lean"
            path_nlink1_lean.write_text("#!/bin/sh\n", encoding="utf-8")
            prev_cwd = Path.cwd()
            try:
                os.chdir(root)
                with _patch_clean_tool_env(
                    {"PATH": str(clean_bin), "ANNEAL_LEAN": "path-clean-lean"}
                ):
                    resolved_env = cmd._build_child_env(root)
                self.assertEqual(
                    resolved_env["ANNEAL_LEAN"], str(path_nlink1_lean)
                )

                for lean_var in ("ANNEAL_LEAN", "ANNEAL_MVP_LEAN"):
                    for bad_lean, err_pat in (
                        (str(hard_lean), "hardlink"),
                        ("hard-lean", "hardlink"),
                        ("hard-path-lean", "hardlink"),
                        ("evil-lean", "symlink"),
                    ):
                        with (
                            _patch_clean_tool_env(
                                {"PATH": str(clean_bin), lean_var: bad_lean}
                            ),
                            _patch_subprocess_exec() as no_exec,
                        ):
                            with self.assertRaisesRegex(ValueError, err_pat):
                                cmd._build_child_env(root)
                            with self.assertRaisesRegex(ValueError, err_pat):
                                cmd.run_anneal_diff(
                                    anneal_root=anneal_dir,
                                    manifest=None,
                                    capture_bin=None,
                                    mir_eval_bin=None,
                                    cache_root=None,
                                    self_check_oracle=False,
                                )
                            with self.assertRaisesRegex(ValueError, err_pat):
                                cmd.run_anneal_fuzz(
                                    anneal_root=anneal_dir,
                                    capture_bin=None,
                                    mir_eval_bin=None,
                                    cache_root=None,
                                    seed=20261124,
                                    cases=8,
                                    max_stmts=6,
                                    ub_ratio=0.2,
                                    min_admission_rate=0.9,
                                )
                            no_exec.assert_not_called()
            finally:
                os.chdir(prev_cwd)

    def test_r30_body_binding_dialect_subject_and_targeted_ub_invariants(
        self,
    ) -> None:
        # 1. Cross-body Lean probe binding (`BODY|<body_id>|<fn_identity>|`)
        #    rejects missing `BODY|`, wrong `body_id`, or wrong `fn_identity`
        #    even when Miri and Lean both return identical scalar values.
        diff = _sample_diff_report()
        fuzz_ok = _sample_fuzz_report()
        c0 = fuzz_ok["cases"][0]
        assert c0["miri"] == c0["lean"]
        c0_cb = c0["capture_body"]

        missing_body = json.loads(json.dumps(fuzz_ok))
        missing_body["cases"][0]["exercised_move_reinit"] = False
        missing_body["cases"][0].pop("move_reinit_evidence", None)
        missing_body["metrics"]["move_reinit_exercised_count"] -= 1
        missing_body["cases"][0]["leg_evidence"]["lean_probe_line"] = (
            f"ANNEAL_LEAN_CASE:{c0['case_id']}:MR0:RETURNED:INT:i32:u:7"
        )
        with self.assertRaisesRegex(ValueError, "lean_probe_line"):
            cmd.validate_fuzz_report(missing_body)

        wrong_body_id = json.loads(json.dumps(fuzz_ok))
        wrong_body_id["cases"][0]["exercised_move_reinit"] = False
        wrong_body_id["cases"][0].pop("move_reinit_evidence", None)
        wrong_body_id["metrics"]["move_reinit_exercised_count"] -= 1
        wrong_body_id["cases"][0]["leg_evidence"]["lean_probe_line"] = (
            f"ANNEAL_LEAN_CASE:{c0['case_id']}:BODY|{c0_cb['body_id'] + 99}|"
            f"{c0_cb['fn_identity']}|MR0:RETURNED:INT:i32:u:7"
        )
        with self.assertRaisesRegex(ValueError, "lean_probe_line"):
            cmd.validate_fuzz_report(wrong_body_id)

        wrong_fn_ident = json.loads(json.dumps(fuzz_ok))
        wrong_fn_ident["cases"][0]["exercised_move_reinit"] = False
        wrong_fn_ident["cases"][0].pop("move_reinit_evidence", None)
        wrong_fn_ident["metrics"]["move_reinit_exercised_count"] -= 1
        wrong_fn_ident["cases"][0]["leg_evidence"]["lean_probe_line"] = (
            f"ANNEAL_LEAN_CASE:{c0['case_id']}:BODY|{c0_cb['body_id']}|"
            f"rust-path-v1::other_fn|MR0:RETURNED:INT:i32:u:7"
        )
        with self.assertRaisesRegex(ValueError, "lean_probe_line"):
            cmd.validate_fuzz_report(wrong_fn_ident)

        # 2. Fuzz report `mir_dialect` must be `"profile_v1"` and match Stage-1
        #    before combining metrics or building semantic-detail reports.
        for bad_dialect in (None, "profile_v2", "mir_raw"):
            bad_fuzz_dialect = json.loads(json.dumps(fuzz_ok))
            if bad_dialect is None:
                bad_fuzz_dialect.pop("mir_dialect", None)
            else:
                bad_fuzz_dialect["mir_dialect"] = bad_dialect
            with self.assertRaisesRegex(ValueError, "mir_dialect"):
                cmd.validate_fuzz_report(bad_fuzz_dialect)
            with self.assertRaisesRegex(ValueError, "mir_dialect"):
                cmd.build_perf_metrics_snippet(
                    diff, fuzz_report=bad_fuzz_dialect
                )
            with self.assertRaisesRegex(ValueError, "mir_dialect"):
                cmd.build_semantic_detail_report(
                    diff_report=diff,
                    fuzz_report=bad_fuzz_dialect,
                    mir_eval_status={"executed": False, "passed": None},
                    repo="google/zerocopy",
                    branch="main",
                    commit_sha="a" * 40,
                    commit_unix_ts=1_780_000_000,
                    environment_profile={"os": "linux", "arch": "x86_64"},
                )

        bad_stage1_dialect = json.loads(json.dumps(diff))
        bad_stage1_dialect["mir_dialect"] = "profile_v2"
        with self.assertRaisesRegex(ValueError, "mir_dialect"):
            cmd.build_perf_metrics_snippet(
                bad_stage1_dialect, fuzz_report=fuzz_ok
            )

        # 3. `build_perf_record_from_snippet` subject includes Stage 2 iff fuzz
        #    metrics are present.
        stage1_only_rec = cmd.build_perf_record_from_snippet(
            cmd.build_perf_metrics_snippet(diff),
            branch="main",
            commit_sha="a" * 40,
            commit_unix_ts=1_780_000_000,
            environment_profile={"os": "linux", "arch": "x86_64"},
        )
        self.assertEqual(
            stage1_only_rec["commit"]["subject"],
            "Stage-1 differential oracle telemetry",
        )
        stage1_and_2_rec = cmd.build_perf_record_from_snippet(
            cmd.build_perf_metrics_snippet(diff, fuzz_report=fuzz_ok),
            branch="main",
            commit_sha="a" * 40,
            commit_unix_ts=1_780_000_000,
            environment_profile={"os": "linux", "arch": "x86_64"},
        )
        self.assertEqual(
            stage1_and_2_rec["commit"]["subject"],
            "Stage-1 and Stage-2 differential oracle telemetry",
        )

        # 4. Partial `TargetedUbProbe` coverage (where
        #    `ub_probes_agreed_count < targeted_ub_probes`) must fail
        #    `report_passes` even with `gate_error=None` and agreed >= 1.
        detail_ok = cmd.build_semantic_detail_report(
            diff_report=diff,
            fuzz_report=fuzz_ok,
            mir_eval_status={"executed": False, "passed": None},
            repo="google/zerocopy",
            branch="main",
            commit_sha="a" * 40,
            commit_unix_ts=1_780_000_000,
            environment_profile={"os": "linux", "arch": "x86_64"},
        )
        self.assertGreater(
            detail_ok["evidence_blocks"]["differential_fuzz"][
                "targeted_ub_probes"
            ],
            1,
        )
        partial_ub = json.loads(json.dumps(detail_ok))
        partial_ub["evidence_blocks"]["differential_fuzz"][
            "gate_error"
        ] = None
        partial_ub["evidence_blocks"]["differential_fuzz"][
            "ub_probes_agreed_count"
        ] = 1
        self.assertFalse(cmd.report_passes(partial_ub, require_fuzz=True))

    def test_r31_cargo_run_pins_target_dir_over_ambient_cargo_config(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as tmpd:
            root = Path(tmpd).resolve()
            anneal_dir = root / "anneal"
            (anneal_dir / ".cargo").mkdir(parents=True)
            (anneal_dir / "Cargo.toml").write_text(
                '[workspace]\nmembers = ["tests/differential"]\n',
                encoding="utf-8",
            )
            (anneal_dir / ".cargo" / "config.toml").write_text(
                '[build]\ntarget-dir = "/tmp/ambient-evil-target"\n',
                encoding="utf-8",
            )
            clean_bin = root / "bin"
            clean_bin.mkdir()
            (clean_bin / "cargo").write_text("#!/bin/sh\n", encoding="utf-8")
            (clean_bin / "rustc").write_text("#!/bin/sh\n", encoding="utf-8")

            seen_cmds: list[tuple[list[str], dict[str, str], int, list[str]]] = []
            diff_json = json.dumps(_sample_diff_report())
            fuzz_json = json.dumps(_sample_fuzz_report())

            def _mock_run(args: list[str], **kwargs: Any) -> mock.Mock:
                td_arg = Path(args[args.index("--target-dir") + 1])
                td_mode = os.lstat(td_arg).st_mode & 0o777
                td_contents = [p.name for p in td_arg.iterdir()]
                seen_cmds.append(
                    (
                        list(args),
                        dict(kwargs.get("env") or {}),
                        td_mode,
                        td_contents,
                    )
                )
                if "fuzz" in args:
                    return mock.Mock(returncode=0, stdout=fuzz_json, stderr="")
                return mock.Mock(returncode=0, stdout=diff_json, stderr="")

            # `cargo run` fallback must fail closed on ambient `.cargo`
            # directories and `rust-toolchain*` files before running.
            with (
                mock.patch.dict(
                    os.environ, {"PATH": str(clean_bin)}, clear=False
                ),
                _patch_subprocess_exec() as no_exec,
            ):
                os.environ.pop("CARGO", None)
                os.environ.pop("RUSTC", None)
                os.environ.pop("CARGO_TARGET_DIR", None)
                with self.assertRaisesRegex(ValueError, "ambient.*\\.cargo"):
                    cmd.run_anneal_diff(
                        anneal_root=anneal_dir,
                        manifest=None,
                        capture_bin=None,
                        mir_eval_bin=None,
                        cache_root=None,
                        self_check_oracle=False,
                    )
                with self.assertRaisesRegex(ValueError, "ambient.*\\.cargo"):
                    cmd.run_anneal_fuzz(
                        anneal_root=anneal_dir,
                        capture_bin=None,
                        mir_eval_bin=None,
                        cache_root=None,
                        seed=20261124,
                        cases=32,
                        max_stmts=6,
                        ub_ratio=0.20,
                        min_admission_rate=0.90,
                    )
                no_exec.assert_not_called()

            shutil.rmtree(anneal_dir / ".cargo")
            ambient_tc = anneal_dir / "rust-toolchain.toml"
            ambient_tc.write_text('[toolchain]\nchannel = "nightly"\n', encoding="utf-8")
            with (
                mock.patch.dict(
                    os.environ, {"PATH": str(clean_bin)}, clear=False
                ),
                _patch_subprocess_exec() as no_exec,
            ):
                os.environ.pop("CARGO", None)
                os.environ.pop("RUSTC", None)
                os.environ.pop("CARGO_TARGET_DIR", None)
                with self.assertRaisesRegex(
                    ValueError, "ambient.*rust-toolchain"
                ):
                    cmd.run_anneal_diff(
                        anneal_root=anneal_dir,
                        manifest=None,
                        capture_bin=None,
                        mir_eval_bin=None,
                        cache_root=None,
                        self_check_oracle=False,
                    )
                with self.assertRaisesRegex(
                    ValueError, "ambient.*rust-toolchain"
                ):
                    cmd.run_anneal_fuzz(
                        anneal_root=anneal_dir,
                        capture_bin=None,
                        mir_eval_bin=None,
                        cache_root=None,
                        seed=20261124,
                        cases=32,
                        max_stmts=6,
                        ub_ratio=0.20,
                        min_admission_rate=0.90,
                    )
                no_exec.assert_not_called()

            ambient_tc.unlink()
            poisoned_ws_target = anneal_dir / "target" / "debug"
            poisoned_ws_target.mkdir(parents=True)
            (poisoned_ws_target / "anneal-diff").write_text(
                "#!/bin/sh\necho FORGED\n", encoding="utf-8"
            )
            with (
                mock.patch.dict(
                    os.environ, {"PATH": str(clean_bin)}, clear=False
                ),
                _patch_subprocess_exec(side_effect=_mock_run),
            ):
                os.environ.pop("CARGO", None)
                os.environ.pop("RUSTC", None)
                os.environ.pop("CARGO_TARGET_DIR", None)
                rc1, _ = cmd.run_anneal_diff(
                    anneal_root=anneal_dir,
                    manifest=None,
                    capture_bin=None,
                    mir_eval_bin=None,
                    cache_root=None,
                    self_check_oracle=False,
                )
                rc2, _ = cmd.run_anneal_fuzz(
                    anneal_root=anneal_dir,
                    capture_bin=None,
                    mir_eval_bin=None,
                    cache_root=None,
                    seed=20261124,
                    cases=32,
                    max_stmts=6,
                    ub_ratio=0.20,
                    min_admission_rate=0.90,
                )
            self.assertEqual((rc1, rc2), (0, 0))
            self.assertEqual(len(seen_cmds), 2)
            seen_priv_tds: list[Path] = []
            for sub_args, sub_env, td_mode, td_contents in seen_cmds:
                self.assertIn("--target-dir", sub_args)
                td_idx = sub_args.index("--target-dir")
                self.assertLess(td_idx, sub_args.index("--"))
                priv_td = Path(sub_args[td_idx + 1])
                seen_priv_tds.append(priv_td)
                self.assertNotEqual(priv_td, anneal_dir / "target")
                self.assertFalse(priv_td.is_relative_to(anneal_dir / "target"))
                if os.name == "posix":
                    self.assertEqual(td_mode, 0o700)
                self.assertEqual(td_contents, [])
                self.assertFalse(priv_td.exists())
                self.assertNotIn("CARGO_TARGET_DIR", sub_env)
                self.assertNotEqual(sub_env.get("CARGO"), str(clean_bin / "cargo"))
                self.assertNotEqual(sub_env.get("RUSTC"), str(clean_bin / "rustc"))
                self.assertIn(".anneal-isolated-bins", sub_env.get("CARGO", ""))
                self.assertIn(".anneal-isolated-bins", sub_env.get("RUSTC", ""))
                self.assertEqual(Path(sub_env["CARGO"]).name, "cargo")
                self.assertEqual(Path(sub_env["RUSTC"]).name, "rustc")
            self.assertNotEqual(seen_priv_tds[0], seen_priv_tds[1])

            # Pre-populated ambient `CARGO_TARGET_DIR` is never reused for
            # `cargo run` (each invocation gets a fresh private target dir).
            explicit_td = root / "explicit-target"
            (explicit_td / "debug").mkdir(parents=True)
            (explicit_td / "debug" / "anneal-diff").write_text(
                "#!/bin/sh\necho FORGED\n", encoding="utf-8"
            )
            seen_cmds.clear()
            with (
                mock.patch.dict(
                    os.environ,
                    {
                        "PATH": str(clean_bin),
                        "CARGO_TARGET_DIR": str(explicit_td),
                    },
                    clear=False,
                ),
                _patch_subprocess_exec(side_effect=_mock_run),
            ):
                os.environ.pop("CARGO", None)
                os.environ.pop("RUSTC", None)
                cmd.run_anneal_fuzz(
                    anneal_root=anneal_dir,
                    capture_bin=None,
                    mir_eval_bin=None,
                    cache_root=None,
                    seed=20261124,
                    cases=32,
                    max_stmts=6,
                    ub_ratio=0.20,
                    min_admission_rate=0.90,
                )
            self.assertEqual(len(seen_cmds), 1)
            fuzz_args, fuzz_env, _, fuzz_contents = seen_cmds[0]
            fuzz_td = Path(fuzz_args[fuzz_args.index("--target-dir") + 1])
            self.assertNotEqual(fuzz_td, explicit_td)
            self.assertFalse(fuzz_td.is_relative_to(explicit_td))
            self.assertEqual(fuzz_contents, [])
            self.assertNotIn("CARGO_TARGET_DIR", fuzz_env)
            self.assertFalse(fuzz_td.exists())

            # Empty `CARGO_TARGET_DIR=""` also uses fresh private target dirs
            # without leaking `CARGO_TARGET_DIR`.
            seen_cmds.clear()
            with (
                mock.patch.dict(
                    os.environ,
                    {
                        "PATH": str(clean_bin),
                        "CARGO_TARGET_DIR": "",
                    },
                    clear=False,
                ),
                _patch_subprocess_exec(side_effect=_mock_run),
            ):
                os.environ.pop("CARGO", None)
                os.environ.pop("RUSTC", None)
                rc3, _ = cmd.run_anneal_diff(
                    anneal_root=anneal_dir,
                    manifest=None,
                    capture_bin=None,
                    mir_eval_bin=None,
                    cache_root=None,
                    self_check_oracle=False,
                )
                rc4, _ = cmd.run_anneal_fuzz(
                    anneal_root=anneal_dir,
                    capture_bin=None,
                    mir_eval_bin=None,
                    cache_root=None,
                    seed=20261124,
                    cases=32,
                    max_stmts=6,
                    ub_ratio=0.20,
                    min_admission_rate=0.90,
                )
            self.assertEqual((rc3, rc4), (0, 0))
            self.assertEqual(len(seen_cmds), 2)
            for sub_args, sub_env, _, _ in seen_cmds:
                priv_td = Path(sub_args[sub_args.index("--target-dir") + 1])
                self.assertNotEqual(priv_td, anneal_dir / "target")
                self.assertFalse(priv_td.exists())
                self.assertNotIn("CARGO_TARGET_DIR", sub_env)

            # `maybe_run_mir_eval_manifest` treats empty `CARGO_TARGET_DIR=""`
            # as unset instead of passing `--target-dir .`.
            mir_pkg = root / "tools" / "anneal-mir-eval"
            mir_pkg.mkdir(parents=True)
            mir_manifest = mir_pkg / "Cargo.toml"
            mir_manifest.write_text(
                '[package]\nname = "anneal-mir-eval"\nversion = "0.1.0"\n',
                encoding="utf-8",
            )
            mir_target_dbg = mir_pkg / "target" / "debug"
            mir_target_dbg.mkdir(parents=True)
            mir_exe = mir_target_dbg / "anneal-mir-eval"
            mir_exe.write_text("", encoding="utf-8")

            def _mock_mir_eval_cargo(args: list[str], **kwargs: Any) -> mock.Mock:
                seen_cmds.append((list(args), dict(kwargs.get("env") or {})))
                if "build" in args:
                    priv_td = Path(args[args.index("--target-dir") + 1])
                    built_exe = priv_td / "debug" / "anneal-mir-eval"
                    built_exe.parent.mkdir(parents=True, exist_ok=True)
                    built_exe.write_bytes(b"mir-eval-fresh")
                    mp_str = (
                        args[args.index("--manifest-path") + 1]
                        if "--manifest-path" in args
                        else str(mir_manifest)
                    )
                    art = json.dumps(
                        {
                            "reason": "compiler-artifact",
                            "manifest_path": mp_str,
                            "target": {"name": "anneal-mir-eval", "kind": ["bin"]},
                            "executable": str(built_exe),
                        }
                    )
                    return mock.Mock(returncode=0, stdout=art + "\n", stderr="")
                return mock.Mock(returncode=0, stdout="", stderr="")

            seen_cmds.clear()
            with (
                mock.patch.dict(
                    os.environ,
                    {
                        "PATH": str(clean_bin),
                        "CARGO_TARGET_DIR": "",
                    },
                    clear=False,
                ),
                _patch_subprocess_exec(side_effect=_mock_mir_eval_cargo),
            ):
                os.environ.pop("CARGO", None)
                os.environ.pop("RUSTC", None)
                status_empty, bin_empty = cmd.maybe_run_mir_eval_manifest(mir_manifest)
            self.assertTrue(status_empty["passed"], status_empty)
            assert bin_empty is not None
            self.assertNotEqual(bin_empty, mir_exe.resolve())
            self.assertIn(".anneal-isolated-bins", str(bin_empty))
            self.assertEqual(os.lstat(bin_empty).st_nlink, 1)
            self.assertEqual(len(seen_cmds), 2)
            for sub_args, sub_env in seen_cmds:
                priv_td = Path(sub_args[sub_args.index("--target-dir") + 1])
                self.assertNotEqual(priv_td, (mir_pkg / "target").resolve())
                self.assertFalse(priv_td.exists())
                self.assertNotIn("CARGO_TARGET_DIR", sub_env)

            # Poisoned `CARGO_TARGET_DIR` is never passed/reused in
            # `maybe_run_mir_eval_manifest`.
            seen_cmds.clear()
            with (
                mock.patch.dict(
                    os.environ,
                    {
                        "PATH": str(clean_bin),
                        "CARGO_TARGET_DIR": str(explicit_td),
                    },
                    clear=False,
                ),
                _patch_subprocess_exec(side_effect=_mock_mir_eval_cargo),
            ):
                os.environ.pop("CARGO", None)
                os.environ.pop("RUSTC", None)
                st_me, bin_me = cmd.maybe_run_mir_eval_manifest(mir_manifest)
            self.assertTrue(st_me["passed"], st_me)
            assert bin_me is not None
            for sub_args, sub_env in seen_cmds:
                priv_td = Path(sub_args[sub_args.index("--target-dir") + 1])
                self.assertNotEqual(priv_td, explicit_td)
                self.assertFalse(priv_td.is_relative_to(explicit_td))
                self.assertFalse(priv_td.exists())
                self.assertNotIn("CARGO_TARGET_DIR", sub_env)

    def test_leg3_hardlinks_cargo_home_runners_and_unshrunk_reproducers(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as tmpd:
            root = Path(tmpd).resolve()
            anneal_dir = root / "anneal"
            anneal_dir.mkdir(parents=True)
            (anneal_dir / "Cargo.toml").write_text(
                '[workspace]\nmembers = ["tests/differential"]\n',
                encoding="utf-8",
            )
            clean_bin = root / "bin"
            clean_bin.mkdir()
            (clean_bin / "cargo").write_text("#!/bin/sh\n", encoding="utf-8")
            (clean_bin / "rustc").write_text("#!/bin/sh\n", encoding="utf-8")

            # 1. Hardlinked Leg 3 inputs (`--mir-eval-bin`,
            #    `--mir-eval-manifest`, `compiler-artifact.manifest_path`) fail
            #    closed, while Cargo `nlink == 2` outputs isolate cleanly.
            mir_pkg = root / "tools" / "anneal-mir-eval"
            mir_pkg.mkdir(parents=True)
            mir_manifest = mir_pkg / "Cargo.toml"
            mir_manifest.write_text(
                '[package]\nname = "anneal-mir-eval"\nversion = "0.1.0"\n',
                encoding="utf-8",
            )
            hard_manifest = root / "hard-mir-Cargo.toml"
            os.link(mir_manifest, hard_manifest)

            mir_dbg = mir_pkg / "target" / "debug"
            mir_deps = mir_dbg / "deps"
            mir_deps.mkdir(parents=True)
            dep_exe = mir_deps / "anneal_mir_eval-deadbeef"
            dep_exe.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            mir_exe = mir_dbg / "anneal-mir-eval"
            os.link(dep_exe, mir_exe)

            hard_pre = root / "hard-prebuilt-mir-eval"
            os.link(dep_exe, hard_pre)

            with (
                mock.patch.dict(
                    os.environ, {"PATH": str(clean_bin)}, clear=False
                ),
                _patch_subprocess_exec() as no_exec,
            ):
                os.environ.pop("CARGO", None)
                os.environ.pop("RUSTC", None)
                os.environ.pop("CARGO_TARGET_DIR", None)
                with self.assertRaisesRegex(ValueError, "hardlink"):
                    cmd.maybe_run_mir_eval_manifest(hard_manifest)
                with self.assertRaisesRegex(ValueError, "hardlink"):
                    cmd.main(
                        [
                            "--anneal-root",
                            str(anneal_dir),
                            "--mir-eval-manifest",
                            str(hard_manifest),
                        ]
                    )
                with self.assertRaisesRegex(ValueError, "hardlink"):
                    cmd.main(
                        [
                            "--anneal-root",
                            str(anneal_dir),
                            "--mir-eval-bin",
                            str(hard_pre),
                        ]
                    )
                with self.assertRaisesRegex(ValueError, "hardlink"):
                    cmd.run_anneal_diff(
                        anneal_root=anneal_dir,
                        manifest=None,
                        capture_bin=None,
                        mir_eval_bin=hard_pre,
                        cache_root=None,
                        self_check_oracle=False,
                    )
                with self.assertRaisesRegex(ValueError, "hardlink"):
                    cmd.run_anneal_fuzz(
                        anneal_root=anneal_dir,
                        capture_bin=None,
                        mir_eval_bin=hard_pre,
                        cache_root=None,
                        seed=20261124,
                        cases=8,
                        max_stmts=6,
                        ub_ratio=0.2,
                        min_admission_rate=0.9,
                    )
                no_exec.assert_not_called()

            bad_art = json.dumps(
                {
                    "reason": "compiler-artifact",
                    "manifest_path": str(hard_manifest),
                    "target": {"name": "anneal-mir-eval", "kind": ["bin"]},
                    "executable": str(mir_exe),
                }
            )
            self.assertIsNone(
                cmd._extract_built_executable(
                    bad_art, "anneal-mir-eval", mir_manifest.resolve()
                )
            )
            hard_manifest.unlink()
            hard_pre.unlink()

            # Valid Cargo `nlink == 2` output with `<profile>/deps/` match
            # isolates under `target/.anneal-isolated-bins/` with `nlink == 1`.
            rogue_src = root / "rogue-outside-bin"
            rogue_src.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")

            def _mock_mir_eval_build(mode: str):
                def _inner(args: list[str], **_kwargs: Any) -> mock.Mock:
                    if "build" in args:
                        priv_td = Path(args[args.index("--target-dir") + 1])
                        priv_dbg = priv_td / "debug"
                        (priv_dbg / "deps").mkdir(parents=True, exist_ok=True)
                        built_exe = priv_dbg / "anneal-mir-eval"
                        if mode == "deps":
                            partner = priv_dbg / "deps" / "anneal_mir_eval-dep"
                            partner.write_bytes(b"#!/bin/sh\nexit 0\n")
                            os.link(partner, built_exe)
                        elif mode == "build_out":
                            out_dir = (
                                priv_dbg
                                / "build"
                                / "anneal-mir-eval"
                                / "fc8c452eb2335b08"
                                / "out"
                            )
                            out_dir.mkdir(parents=True, exist_ok=True)
                            out_exe = out_dir / "anneal_mir_eval"
                            out_exe.write_bytes(b"#!/bin/sh\nexit 0\n")
                            os.link(out_exe, built_exe)
                        else:
                            os.link(rogue_src, built_exe)
                        mp_str = (
                            args[args.index("--manifest-path") + 1]
                            if "--manifest-path" in args
                            else str(mir_manifest)
                        )
                        art = json.dumps(
                            {
                                "reason": "compiler-artifact",
                                "manifest_path": mp_str,
                                "target": {
                                    "name": "anneal-mir-eval",
                                    "kind": ["bin"],
                                },
                                "executable": str(built_exe),
                            }
                        )
                        return mock.Mock(
                            returncode=0, stdout=art + "\n", stderr=""
                        )
                    return mock.Mock(returncode=0, stdout="", stderr="")

                return _inner

            with (
                mock.patch.dict(
                    os.environ, {"PATH": str(clean_bin)}, clear=False
                ),
                _patch_subprocess_exec(
                    side_effect=_mock_mir_eval_build("deps")
                ),
            ):
                os.environ.pop("CARGO", None)
                os.environ.pop("RUSTC", None)
                os.environ.pop("CARGO_TARGET_DIR", None)
                ok_st, isolated_bin = cmd.maybe_run_mir_eval_manifest(
                    mir_manifest
                )
            self.assertTrue(ok_st["passed"], ok_st)
            assert isolated_bin is not None
            self.assertEqual(os.lstat(isolated_bin).st_nlink, 1)
            self.assertIn(".anneal-isolated-bins", str(isolated_bin))

            # Cargo 1.100+ `build/<pkg>/<hash>/out/<stem>` hardlink layout
            # also isolates cleanly.
            with (
                mock.patch.dict(
                    os.environ, {"PATH": str(clean_bin)}, clear=False
                ),
                _patch_subprocess_exec(
                    side_effect=_mock_mir_eval_build("build_out")
                ),
            ):
                os.environ.pop("CARGO", None)
                os.environ.pop("RUSTC", None)
                os.environ.pop("CARGO_TARGET_DIR", None)
                ok_new_st, isolated_new_bin = cmd.maybe_run_mir_eval_manifest(
                    mir_manifest
                )
            self.assertTrue(ok_new_st["passed"], ok_new_st)
            assert isolated_new_bin is not None
            self.assertEqual(os.lstat(isolated_new_bin).st_nlink, 1)

            # Unverified `nlink == 2` binary outside Cargo `deps/` fails closed.
            with (
                mock.patch.dict(
                    os.environ, {"PATH": str(clean_bin)}, clear=False
                ),
                _patch_subprocess_exec(
                    side_effect=_mock_mir_eval_build("rogue")
                ),
            ):
                os.environ.pop("CARGO", None)
                os.environ.pop("RUSTC", None)
                os.environ.pop("CARGO_TARGET_DIR", None)
                with self.assertRaisesRegex(
                    ValueError, "hardlinked outside Cargo deps"
                ):
                    cmd.maybe_run_mir_eval_manifest(mir_manifest)

            # Isolation must compute the filename digest in one pass over
            # the copied bytes (never re-reading or matching a stale pass).
            race_src = mir_dbg / "deps" / "anneal_mir_eval-racehash"
            race_src.write_bytes(b"#!/bin/sh\necho first\n")
            mir_exe.unlink()
            os.link(race_src, mir_exe)
            orig_open = open
            mutated = False

            def _racing_open(file: object, mode: str = "r", *a: object, **kw: object):
                nonlocal mutated
                f = orig_open(file, mode, *a, **kw)
                if (
                    file == mir_exe.resolve()
                    and mode == "rb"
                    and not mutated
                ):
                    mutated = True

                    class _RacingReader:
                        def __init__(self, inner: object) -> None:
                            self._inner = inner

                        def __enter__(self) -> "_RacingReader":
                            self._inner.__enter__()  # type: ignore[union-attr]
                            return self

                        def __exit__(self, *args: object) -> bool | None:
                            return self._inner.__exit__(*args)  # type: ignore[union-attr]

                        def fileno(self) -> int:
                            return self._inner.fileno()  # type: ignore[union-attr]

                        def seek(self, *_args: object) -> int:
                            raise AssertionError("two-pass seek must not occur")

                        def read(self, n: int = -1) -> bytes:
                            data = self._inner.read(n)  # type: ignore[union-attr]
                            if data:
                                # Overwrite partner bytes mid-stream; dest must
                                # still carry the exact digest of copied bytes.
                                with orig_open(race_src, "r+b") as pf:
                                    pf.write(b"#!/bin/sh\necho raced\n")
                            return data

                    return _RacingReader(f)
                return f

            with mock.patch("builtins.open", side_effect=_racing_open):
                raced_bin = cmd._materialize_cargo_built_executable(
                    mir_exe.resolve(), mir_manifest.parent / "target", "anneal-mir-eval"
                )
            import hashlib as _hashlib

            copied_sha16 = _hashlib.sha256(raced_bin.read_bytes()).hexdigest()[:16]
            self.assertEqual(raced_bin.name, f"anneal-mir-eval-{copied_sha16}")
            self.assertEqual(os.lstat(raced_bin).st_nlink, 1)

            # 2. `$CARGO_HOME/config{,.toml}` runner/build overrides, symlinks,
            #    and hardlinks fail pre-Cargo, while `[source]` vendor config
            #    passes and `CARGO_TARGET_*_RUNNER` env vars are stripped.
            ext_ch = root / "ext-cargo-home"
            ext_ch.mkdir()
            vendor_dir = root / "vendor"
            vendor_dir.mkdir()
            sym_ch = root / "sym-cargo-home"
            os.symlink(ext_ch, sym_ch)

            with (
                mock.patch.dict(
                    os.environ,
                    {"PATH": str(clean_bin), "CARGO_HOME": str(sym_ch)},
                    clear=False,
                ),
                _patch_subprocess_exec() as no_exec,
            ):
                os.environ.pop("CARGO", None)
                os.environ.pop("RUSTC", None)
                os.environ.pop("CARGO_TARGET_DIR", None)
                with self.assertRaisesRegex(ValueError, "symlink"):
                    cmd.maybe_run_mir_eval_manifest(mir_manifest)
                with self.assertRaisesRegex(ValueError, "symlink"):
                    cmd.run_anneal_diff(
                        anneal_root=anneal_dir,
                        manifest=None,
                        capture_bin=None,
                        mir_eval_bin=None,
                        cache_root=None,
                        self_check_oracle=False,
                    )
                with self.assertRaisesRegex(ValueError, "symlink"):
                    cmd.run_anneal_fuzz(
                        anneal_root=anneal_dir,
                        capture_bin=None,
                        mir_eval_bin=None,
                        cache_root=None,
                        seed=20261124,
                        cases=8,
                        max_stmts=6,
                        ub_ratio=0.2,
                        min_admission_rate=0.9,
                    )
                no_exec.assert_not_called()

            for poisoned_cfg in (
                '[target.x86_64-unknown-linux-gnu]\nrunner = "/bin/false"\n',
                '[target.\'cfg(all())\']\nrunner = "/bin/false"\n',
                '[build]\nrustc-wrapper = "/bin/false"\n',
            ):
                cfg_file = ext_ch / "config.toml"
                cfg_file.write_text(poisoned_cfg, encoding="utf-8")
                with (
                    mock.patch.dict(
                        os.environ,
                        {"PATH": str(clean_bin), "CARGO_HOME": str(ext_ch)},
                        clear=False,
                    ),
                    _patch_subprocess_exec() as no_exec,
                ):
                    os.environ.pop("CARGO", None)
                    os.environ.pop("RUSTC", None)
                    os.environ.pop("CARGO_TARGET_DIR", None)
                    with self.assertRaisesRegex(
                        ValueError, "disallowed section"
                    ):
                        cmd.maybe_run_mir_eval_manifest(mir_manifest)
                    with self.assertRaisesRegex(
                        ValueError, "disallowed section"
                    ):
                        cmd.run_anneal_diff(
                            anneal_root=anneal_dir,
                            manifest=None,
                            capture_bin=None,
                            mir_eval_bin=None,
                            cache_root=None,
                            self_check_oracle=False,
                        )
                    with self.assertRaisesRegex(
                        ValueError, "disallowed section"
                    ):
                        cmd.run_anneal_fuzz(
                            anneal_root=anneal_dir,
                            capture_bin=None,
                            mir_eval_bin=None,
                            cache_root=None,
                            seed=20261124,
                            cases=8,
                            max_stmts=6,
                            ub_ratio=0.2,
                            min_admission_rate=0.9,
                        )
                    no_exec.assert_not_called()
                cfg_file.unlink()

            # Fallback `$HOME/.cargo` (when `CARGO_HOME` is unset) must also
            # validate ancestors against symlinks and traversal pre-Cargo.
            real_home = root / "real-home"
            real_home.mkdir()
            sym_home = root / "sym-home"
            os.symlink(real_home, sym_home)
            with (
                mock.patch.dict(
                    os.environ,
                    {"PATH": str(clean_bin), "HOME": str(sym_home)},
                    clear=False,
                ),
                _patch_subprocess_exec() as no_exec,
            ):
                os.environ.pop("CARGO_HOME", None)
                os.environ.pop("CARGO", None)
                os.environ.pop("RUSTC", None)
                os.environ.pop("CARGO_TARGET_DIR", None)
                with self.assertRaisesRegex(ValueError, "symlink"):
                    cmd.maybe_run_mir_eval_manifest(mir_manifest)
                with self.assertRaisesRegex(ValueError, "symlink"):
                    cmd.run_anneal_diff(
                        anneal_root=anneal_dir,
                        manifest=None,
                        capture_bin=None,
                        mir_eval_bin=None,
                        cache_root=None,
                        self_check_oracle=False,
                    )
                with self.assertRaisesRegex(ValueError, "symlink"):
                    cmd.run_anneal_fuzz(
                        anneal_root=anneal_dir,
                        capture_bin=None,
                        mir_eval_bin=None,
                        cache_root=None,
                        seed=20261124,
                        cases=8,
                        max_stmts=6,
                        ub_ratio=0.2,
                        min_admission_rate=0.9,
                    )
                no_exec.assert_not_called()

            # Even when `CARGO_HOME` is explicitly set cleanly, an unsafe
            # symlink or `..`-traversal `HOME` must still fail closed pre-exec
            # across `_build_child_env`, `maybe_run_mir_eval_manifest`,
            # `run_anneal_diff`, and `run_anneal_fuzz`.
            for bad_home, home_pat in (
                (str(sym_home), "symlink"),
                ("../outside-home", "parent traversal"),
            ):
                with (
                    mock.patch.dict(
                        os.environ,
                        {
                            "PATH": str(clean_bin),
                            "CARGO_HOME": str(ext_ch),
                            "HOME": bad_home,
                        },
                        clear=False,
                    ),
                    _patch_subprocess_exec() as no_exec,
                ):
                    os.environ.pop("CARGO", None)
                    os.environ.pop("RUSTC", None)
                    os.environ.pop("CARGO_TARGET_DIR", None)
                    with self.assertRaisesRegex(ValueError, home_pat):
                        cmd._build_child_env(root)
                    with self.assertRaisesRegex(ValueError, home_pat):
                        cmd.maybe_run_mir_eval_manifest(mir_manifest)
                    with self.assertRaisesRegex(ValueError, home_pat):
                        cmd.run_anneal_diff(
                            anneal_root=anneal_dir,
                            manifest=None,
                            capture_bin=None,
                            mir_eval_bin=None,
                            cache_root=None,
                            self_check_oracle=False,
                        )
                    with self.assertRaisesRegex(ValueError, home_pat):
                        cmd.run_anneal_fuzz(
                            anneal_root=anneal_dir,
                            capture_bin=None,
                            mir_eval_bin=None,
                            cache_root=None,
                            seed=20261124,
                            cases=8,
                            max_stmts=6,
                            ub_ratio=0.2,
                            min_admission_rate=0.9,
                        )
                    no_exec.assert_not_called()

            # Valid `[source]`-only vendor config works and strips
            # `CARGO_TARGET_*_RUNNER`, and `_build_child_env` anchors relative
            # `HOME` to `caller_cwd` so `work_dir`/child cwds cannot pick up
            # unvalidated `rel-home/.cargo` or `rel-home/.rustup`.
            rel_home_caller = root / "rel-home"
            rel_home_caller.mkdir()
            poison_workdir_cargo = anneal_dir / "rel-home" / ".cargo"
            poison_workdir_cargo.mkdir(parents=True)
            (poison_workdir_cargo / "config.toml").write_text(
                '[build]\nrustc-wrapper = "/bin/false"\n',
                encoding="utf-8",
            )
            (ext_ch / "config.toml").write_text(
                '[source.crates-io]\nreplace-with = "anneal-vendor"\n'
                f'[source.anneal-vendor]\ndirectory = "{vendor_dir}"\n',
                encoding="utf-8",
            )
            diff_json = json.dumps(_sample_diff_report())
            seen_runner_envs: list[dict[str, str]] = []

            def _mock_clean_cargo(
                args: list[str], **kwargs: Any
            ) -> mock.Mock:
                seen_runner_envs.append(dict(kwargs.get("env") or {}))
                return mock.Mock(returncode=0, stdout=diff_json, stderr="")

            prev_cwd = Path.cwd()
            os.chdir(root)
            try:
                with (
                    mock.patch.dict(
                        os.environ,
                        {
                            "PATH": str(clean_bin),
                            "HOME": "rel-home",
                            "CARGO_NET_OFFLINE": "true",
                            "CARGO_BUILD_JOBS": "4",
                            "CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUNNER": "/bin/false",
                            "RUSTFLAGS": "-C linker=/bin/false",
                        },
                        clear=False,
                    ),
                    _patch_subprocess_exec(side_effect=_mock_clean_cargo),
                ):
                    os.environ.pop("CARGO_HOME", None)
                    os.environ.pop("CARGO", None)
                    os.environ.pop("RUSTC", None)
                    os.environ.pop("CARGO_TARGET_DIR", None)
                    rc_unset_ch, _ = cmd.run_anneal_diff(
                        anneal_root=anneal_dir,
                        manifest=None,
                        capture_bin=None,
                        mir_eval_bin=None,
                        cache_root=None,
                        self_check_oracle=False,
                    )
                with (
                    mock.patch.dict(
                        os.environ,
                        {
                            "PATH": str(clean_bin),
                            "CARGO_HOME": str(ext_ch),
                            "HOME": "rel-home",
                            "CARGO_NET_OFFLINE": "true",
                            "CARGO_BUILD_JOBS": "4",
                            "CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUNNER": "/bin/false",
                            "RUSTFLAGS": "-C linker=/bin/false",
                        },
                        clear=False,
                    ),
                    _patch_subprocess_exec(side_effect=_mock_clean_cargo),
                ):
                    os.environ.pop("CARGO", None)
                    os.environ.pop("RUSTC", None)
                    os.environ.pop("CARGO_TARGET_DIR", None)
                    rc_clean, _ = cmd.run_anneal_diff(
                        anneal_root=anneal_dir,
                        manifest=None,
                        capture_bin=None,
                        mir_eval_bin=None,
                        cache_root=None,
                        self_check_oracle=False,
                    )
            finally:
                os.chdir(prev_cwd)
            self.assertEqual(rc_unset_ch, 0)
            self.assertEqual(rc_clean, 0)
            self.assertEqual(len(seen_runner_envs), 2)
            for seen_env in seen_runner_envs:
                self.assertEqual(seen_env.get("HOME"), str(rel_home_caller))
                self.assertNotIn(
                    "CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUNNER",
                    seen_env,
                )
                self.assertNotIn("RUSTFLAGS", seen_env)
                self.assertEqual(seen_env.get("CARGO_NET_OFFLINE"), "true")
                self.assertEqual(seen_env.get("CARGO_BUILD_JOBS"), "4")

            # 3. Failing fuzz reproducers preserve `source`, `fn_name`, `args`,
            #    `program_sha256`, `fuel`, and inconclusive `shrink_trace` when
            #    `shrink_verification` is `None`.
            unshrunk_rep = _sample_fuzz_report(unsound=1)
            fail_case = next(
                c
                for c in unshrunk_rep["cases"]
                if c["evaluation"]["agreement"] == "unsound_accept_critical"
            )
            fail_fn = fail_case["fn_name"]
            fail_idx = fail_case["case_index"]
            captured_srcs: list[str] = []
            orig_render = cmd._render_gen_program_standalone

            def _spy_render(**kw: Any) -> str:
                rendered = orig_render(**kw)
                if kw.get("fn_name") == fail_fn:
                    captured_srcs.append(rendered)
                return rendered

            with mock.patch.object(
                cmd, "_render_gen_program_standalone", side_effect=_spy_render
            ):
                cmd._expected_fuzz_case_details(
                    unshrunk_rep["seed"],
                    fail_idx,
                    unshrunk_rep["max_stmts"],
                    unshrunk_rep["ub_ratio"],
                    default_fuel=unshrunk_rep["fuel"],
                )
            self.assertEqual(len(captured_srcs), 1)
            fail_case["source"] = captured_srcs[0]
            fail_case["shrink_trace"] = None
            fail_case["shrink_verification"] = None

            no_shrink_detail = cmd.build_semantic_detail_report(
                diff_report=_sample_diff_report(),
                mir_eval_status={"executed": False, "passed": None},
                repo="google/zerocopy",
                branch="main",
                commit_sha="a" * 40,
                commit_unix_ts=1_780_000_000,
                environment_profile={"os": "linux"},
                fuzz_report=unshrunk_rep,
            )
            f0 = no_shrink_detail["evidence_blocks"]["differential_fuzz"][
                "failing_cases"
            ][0]
            self.assertEqual(f0["fn_name"], fail_fn)
            self.assertEqual(f0["args"], fail_case["args"])
            self.assertEqual(f0["program_sha256"], fail_case["program_sha256"])
            self.assertEqual(f0["fuel"], fail_case["fuel"])
            self.assertEqual(f0["source"], fail_case["source"])
            self.assertIsNone(f0["shrink_trace"])
            self.assertFalse(cmd.report_passes(no_shrink_detail, require_fuzz=True))

            inconclusive_rep = json.loads(json.dumps(unshrunk_rep))
            inc_fc = inconclusive_rep["cases"][fail_idx]
            inc_fc["shrink_trace"] = {
                "original_nodes": 6,
                "shrunk_nodes": 6,
                "steps_evaluated": 2,
                "oracle_runs": 2,
                "cache_hits": 0,
                "converged_1_minimal": False,
                "minimized_source": inc_fc["source"],
                "minimized_args": inc_fc["args"],
            }
            inc_detail = cmd.build_semantic_detail_report(
                diff_report=_sample_diff_report(),
                mir_eval_status={"executed": False, "passed": None},
                repo="google/zerocopy",
                branch="main",
                commit_sha="a" * 40,
                commit_unix_ts=1_780_000_000,
                environment_profile={"os": "linux"},
                fuzz_report=inconclusive_rep,
            )
            inc_f0 = inc_detail["evidence_blocks"]["differential_fuzz"][
                "failing_cases"
            ][0]
            self.assertEqual(inc_f0["source"], fail_case["source"])
            self.assertEqual(inc_f0["shrink_trace"], inc_fc["shrink_trace"])
            self.assertNotIn("shrink_verification", inc_f0)

    def test_ub_bucket_and_assign_place_read_parity(self) -> None:
        self.assertEqual(
            cmd._classify_ub_bucket(
                "error: Undefined Behavior: arithmetic overflow in `unchecked_sub`"
            ),
            "arithmetic_overflow",
        )
        self.assertEqual(
            cmd._classify_ub_bucket("arithmetic overflow"),
            "arithmetic_overflow",
        )
        self.assertEqual(
            cmd._classify_ub_bucket("overflow in signed division"),
            "signed_div_overflow",
        )
        self.assertEqual(
            cmd._classify_ub_bucket("overflowing add"),
            "arithmetic_overflow",
        )

        ap_case = {
            "case_id": "ap_read",
            "fn_name": "ap_fn",
            "args": [{"kind": "bool", "value": False}],
            "lean": {"kind": "returned", "value": {"kind": "bool", "value": False}},
            "exercised_move_reinit": True,
            "move_reinit_evidence": {
                "body_id": 0,
                "fn_identity": "rust-path-v1::ap_fn",
                "local_slot": 2,
                "arg_count": 1,
                "local_tys": [
                    {"kind": "bool"},
                    {"kind": "bool"},
                    {
                        "kind": "enum",
                        "tag_repr": {"kind": "scalar", "size": 1},
                    },
                ],
                "blocks": [
                    {
                        "statements": [
                            {
                                "kind": "assign",
                                "local": 2,
                                "value": {"kind": "use"},
                            },
                            {
                                "kind": "assign",
                                "local": 3,
                                "value": {
                                    "kind": "use",
                                    "operand": {"kind": "move", "local": 2},
                                },
                            },
                            {
                                "kind": "assign",
                                "local": 2,
                                "value": {"kind": "use"},
                            },
                            {
                                "kind": "assign_place",
                                "place": {"local": 0, "projection": []},
                                "value": {
                                    "kind": "discriminant",
                                    "place": {"local": 2, "projection": []},
                                },
                            },
                        ],
                        "terminator": {"kind": "ret"},
                    }
                ],
                "total_steps": 5,
                "init_step": {"step": 0, "block": 0, "stmt": 0},
                "move_step": {"step": 1, "block": 0, "stmt": 1},
                "reinit_step": {"step": 2, "block": 0, "stmt": 2},
                "read_step": {"step": 3, "block": 0, "stmt": 3},
                "lean_probe_line": (
                    "ANNEAL_LEAN_CASE:ap_read:BODY|0|rust-path-v1::ap_fn|MR1|2|5|"
                    "0,0,0|1,0,1|2,0,2|3,0,3:RETURNED:BOOL:false"
                ),
            },
        }
        ap_case["move_reinit_evidence"]["capture_body_sha256"] = (
            cmd._canonical_capture_body_sha256(
                "rust-path-v1::ap_fn",
                1,
                ap_case["move_reinit_evidence"]["local_tys"],
                ap_case["move_reinit_evidence"]["blocks"],
            )
        )
        witness = cmd._verify_move_reinit_evidence(ap_case, 0)
        self.assertEqual(witness["local_slot"], 2)

    def test_binds_min_admission_rate_and_isolates_or_rejects_hardlinked_capture(
        self,
    ) -> None:
        # 1. Requested `fuzz_min_admission_rate` binds `min_admission_rate` in
        #    `validate_fuzz_report`, `build_semantic_detail_report`,
        #    `report_passes`, and `main`.
        diff = _sample_diff_report()
        for bad_reported in (0.50, 0.95):
            fuzz_bad = _sample_fuzz_report(
                admission_rate=1.0, reported_min_rate=bad_reported
            )
            with self.assertRaisesRegex(ValueError, "min_admission_rate"):
                cmd.validate_fuzz_report(
                    fuzz_bad, expected_min_admission_rate=0.90
                )
            with self.assertRaisesRegex(ValueError, "min_admission_rate"):
                cmd.build_semantic_detail_report(
                    diff_report=diff,
                    fuzz_report=fuzz_bad,
                    mir_eval_status={"executed": False, "passed": None},
                    repo="google/zerocopy",
                    branch="main",
                    commit_sha="a" * 40,
                    commit_unix_ts=1_780_000_000,
                    environment_profile={"os": "linux", "arch": "x86_64"},
                    fuzz_min_admission_rate=0.90,
                )
            detail_unpaired = cmd.build_semantic_detail_report(
                diff_report=diff,
                fuzz_report=fuzz_bad,
                mir_eval_status={"executed": False, "passed": None},
                repo="google/zerocopy",
                branch="main",
                commit_sha="a" * 40,
                commit_unix_ts=1_780_000_000,
                environment_profile={"os": "linux", "arch": "x86_64"},
            )
            self.assertFalse(
                cmd.report_passes(
                    detail_unpaired,
                    require_fuzz=True,
                    fuzz_min_admission_rate=0.90,
                )
            )

        # 2. Rogue hardlinked capture binaries (`nlink > 1` outside Cargo
        #    `deps/`) fail closed in Python, while legitimate Cargo `deps/`
        #    `nlink == 2` capture binaries materialize into `nlink == 1`.
        with tempfile.TemporaryDirectory() as tmpd:
            root = Path(tmpd).resolve()
            anneal_dir = root / "anneal"
            (anneal_dir / "target" / "debug" / "deps").mkdir(parents=True)
            real_cap = root / "real-cap"
            real_cap.write_bytes(b"capture-bytes")
            rogue_cap = root / "rogue-cap-hardlink"
            os.link(real_cap, rogue_cap)

            with (
                mock.patch.dict(
                    os.environ,
                    {"ANNEAL_CAPTURE": str(rogue_cap)},
                    clear=False,
                ),
                _patch_subprocess_exec() as no_exec,
            ):
                os.environ.pop("CARGO", None)
                os.environ.pop("RUSTC", None)
                os.environ.pop("CARGO_TARGET_DIR", None)
                with self.assertRaisesRegex(ValueError, "hard"):
                    cmd._build_child_env(root)
                with self.assertRaisesRegex(ValueError, "hard"):
                    cmd.run_anneal_diff(
                        anneal_root=anneal_dir,
                        manifest=None,
                        capture_bin=None,
                        mir_eval_bin=None,
                        cache_root=None,
                        self_check_oracle=False,
                    )
                with self.assertRaisesRegex(ValueError, "hard"):
                    cmd.run_anneal_fuzz(
                        anneal_root=anneal_dir,
                        capture_bin=None,
                        mir_eval_bin=None,
                        cache_root=None,
                        seed=20261124,
                        cases=8,
                        max_stmts=6,
                        ub_ratio=0.2,
                        min_admission_rate=0.9,
                    )
                no_exec.assert_not_called()

            with _patch_subprocess_exec() as no_exec:
                with self.assertRaisesRegex(ValueError, "hard"):
                    cmd.run_anneal_diff(
                        anneal_root=anneal_dir,
                        manifest=None,
                        capture_bin=rogue_cap,
                        mir_eval_bin=None,
                        cache_root=None,
                        self_check_oracle=False,
                    )
                no_exec.assert_not_called()

            cargo_dep = (
                anneal_dir / "target" / "debug" / "deps" / "anneal_rustc_capture-abc"
            )
            cargo_dep.write_bytes(b"cargo-capture-bytes")
            cargo_cap = (
                anneal_dir / "target" / "debug" / "anneal-rustc-capture"
            )
            os.link(cargo_dep, cargo_cap)
            with (
                ExitStack() as cap_stack,
                mock.patch.dict(
                    os.environ,
                    {"ANNEAL_CAPTURE": str(cargo_cap), "TMPDIR": str(root)},
                    clear=False,
                ),
            ):
                os.environ.pop("CARGO", None)
                os.environ.pop("RUSTC", None)
                os.environ.pop("CARGO_TARGET_DIR", None)
                iso_env = cmd._build_child_env(root, exit_stack=cap_stack)
                iso_cap = Path(iso_env["ANNEAL_CAPTURE"])
                self.assertEqual(os.lstat(iso_cap).st_nlink, 1)
                self.assertIn(".anneal-isolated-bins", str(iso_cap))
                self.assertEqual(stat.S_IMODE(os.lstat(iso_cap).st_mode), 0o555)
                self.assertFalse(
                    (anneal_dir / "target" / ".anneal-isolated-bins").exists()
                )
            self.assertFalse(iso_cap.exists())

            # Rogue hardlinks and symlinks supplied via `--anneal-diff-bin` must
            # fail closed in both `main()` and `_run_anneal_diff_subcommand`,
            # while Cargo `nlink == 2` binaries under `<profile>/deps/` isolate
            # safely into `.anneal-isolated-bins/anneal-diff`.
            rogue_diff = root / "rogue-anneal-diff-hardlink"
            os.link(real_cap, rogue_diff)
            sym_diff = root / "sym-anneal-diff"
            sym_diff.symlink_to(real_cap)
            trav_diff = Path("sub") / ".." / "anneal-diff-trav"
            with _patch_subprocess_exec() as no_exec:
                for trav_args in (
                    ["--anneal-diff-bin", str(trav_diff)],
                    ["--cache-root", "dir/../cache"],
                    ["--mir-eval-manifest", "dir/../Cargo.toml"],
                ):
                    with self.assertRaisesRegex(ValueError, "parent traversal"):
                        cmd.main(trav_args)
                for bad_diff, err_pat in (
                    (rogue_diff, "hardlink"),
                    (sym_diff, "symlink"),
                ):
                    with self.assertRaisesRegex(ValueError, err_pat):
                        cmd.run_anneal_diff(
                            anneal_root=anneal_dir,
                            manifest=None,
                            capture_bin=None,
                            mir_eval_bin=None,
                            cache_root=None,
                            self_check_oracle=False,
                            anneal_diff_bin=bad_diff,
                        )
                    with self.assertRaisesRegex(ValueError, err_pat):
                        cmd.run_anneal_fuzz(
                            anneal_root=anneal_dir,
                            capture_bin=None,
                            mir_eval_bin=None,
                            cache_root=None,
                            seed=20261124,
                            cases=8,
                            max_stmts=6,
                            ub_ratio=0.2,
                            min_admission_rate=0.9,
                            anneal_diff_bin=bad_diff,
                        )
                    with self.assertRaisesRegex(ValueError, err_pat):
                        cmd.main(["--anneal-diff-bin", str(bad_diff)])
                no_exec.assert_not_called()

            cargo_diff_dep = (
                anneal_dir / "target" / "debug" / "deps" / "anneal_diff-abc"
            )
            cargo_diff_dep.write_text(
                "#!/bin/sh\necho '{}'\n", encoding="utf-8"
            )
            cargo_diff_dep.chmod(0o755)
            cargo_diff_bin = anneal_dir / "target" / "debug" / "anneal-diff"
            os.link(cargo_diff_dep, cargo_diff_bin)
            observed_cmds: list[tuple[list[str], int, int, int]] = []
            diff_json_bytes = json.dumps(_sample_diff_report())
            fuzz_json_bytes = json.dumps(_sample_fuzz_report())

            def _fake_diff_proc(command, **_kwargs):
                exe = Path(command[0])
                observed_cmds.append(
                    (
                        list(command),
                        stat.S_IMODE(os.lstat(exe).st_mode),
                        stat.S_IMODE(os.lstat(exe.parent).st_mode),
                        os.lstat(exe).st_nlink,
                    )
                )
                subcmd = command[1]
                payload = diff_json_bytes if subcmd == "run" else fuzz_json_bytes
                return subprocess.CompletedProcess(
                    command, 0, stdout=payload, stderr=""
                )

            with (
                mock.patch.object(
                    cmd, "_run_subcommand_process_group", side_effect=_fake_diff_proc
                ),
                mock.patch.object(
                    cmd,
                    "_git_metadata",
                    return_value=("main", "a" * 40, 1_780_000_000),
                ),
                mock.patch.object(
                    cmd,
                    "_collect_environment",
                    return_value={
                        "os": "linux",
                        "arch": "x86_64",
                        "rustc_version": "rustc 1",
                        "lean_version": "lean 1",
                        "anneal_root": "anneal",
                    },
                ),
            ):
                rc_iso = cmd.main(
                    [
                        "--anneal-root",
                        str(anneal_dir),
                        "--anneal-diff-bin",
                        str(cargo_diff_bin),
                        "--fuzz-cases",
                        "32",
                        "--fuzz-seed",
                        "20261124",
                    ]
                )
            self.assertEqual(rc_iso, 0)
            self.assertEqual(len(observed_cmds), 2)
            for ran_cmd, mode, dir_mode, nlink in observed_cmds:
                invoked_bin = Path(ran_cmd[0])
                self.assertIn(".anneal-isolated-bins", str(invoked_bin))
                self.assertEqual(nlink, 1)
                self.assertEqual(mode, 0o555)
                self.assertEqual(dir_mode, 0o555)
                self.assertFalse(invoked_bin.exists())

            # Fuzz reports must not include compiled `rustc` execution outputs
            # on Miri-established UB cases when `rustc_compiled` is active.
            executed_ub_rustc = _sample_fuzz_report()
            ub_idx_rep = next(
                i
                for i, c in enumerate(executed_ub_rustc["cases"])
                if c["miri"]["kind"] == "undefined_behavior"
            )
            executed_ub_rustc["cases"][ub_idx_rep]["rustc"] = {
                "kind": "returned",
                "value": {"kind": "int", "int_kind": "u32", "bits": "0"},
            }
            with self.assertRaisesRegex(
                ValueError, "must not execute compiled `rustc`"
            ):
                cmd.validate_fuzz_report(executed_ub_rustc)

    def test_fuzz_subcommand_timeout_emits_failed_semantic_report(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as tmpd:
            root = Path(tmpd).resolve()
            anneal_dir = root / "anneal"
            anneal_dir.mkdir()
            diff_json = json.dumps(_sample_diff_report())
            sample_json_file = root / "sample-run.json"
            sample_json_file.write_text(diff_json, encoding="utf-8")
            stalled_bin = root / "stalled-anneal-diff.sh"
            stalled_bin.write_text(
                f"#!/bin/sh\n"
                f'if [ "$1" = "fuzz" ]; then\n'
                f"  sleep 2\n"
                f"  exit 0\n"
                f"fi\n"
                f'cat "{sample_json_file}"\n',
                encoding="utf-8",
            )
            stalled_bin.chmod(0o755)
            out_detail = root / "detail.json"
            rc = cmd.main(
                [
                    "--anneal-root",
                    str(anneal_dir),
                    "--anneal-diff-bin",
                    str(stalled_bin),
                    "--fuzz-timeout-secs",
                    "0.05",
                    "--expect-capture-source",
                    "env_anneal_capture",
                    "--allow-unknown-git",
                    "--output",
                    str(out_detail),
                ]
            )
            self.assertEqual(rc, 1)
            self.assertTrue(out_detail.is_file())
            detail = json.loads(out_detail.read_text(encoding="utf-8"))
            fuzz_ev = detail["evidence_blocks"]["differential_fuzz"]
            self.assertTrue(fuzz_ev["timed_out"])
            self.assertFalse(fuzz_ev["passed"])
            self.assertIn("timed out", fuzz_ev["error"])
            self.assertFalse(cmd.report_passes(detail, require_fuzz=True))

            fake_proc = mock.Mock()
            fake_proc.pid = 424242
            fake_proc.returncode = None
            fake_proc.communicate.side_effect = [
                subprocess.TimeoutExpired(["anneal-diff"], 0.05),
                ("", ""),
            ]
            with (
                mock.patch("subprocess.Popen", return_value=fake_proc) as popen_mock,
                mock.patch.object(cmd.os, "killpg") as killpg_mock,
            ):
                rc_slow_run_fn = None
                with self.assertRaisesRegex(RuntimeError, "timed out"):
                    rc_slow_run_fn = cmd.run_anneal_diff(
                        anneal_root=anneal_dir,
                        manifest=None,
                        capture_bin=None,
                        mir_eval_bin=None,
                        cache_root=None,
                        self_check_oracle=False,
                        anneal_diff_bin=stalled_bin,
                        timeout_secs=0.05,
                    )
                self.assertIsNone(rc_slow_run_fn)
                if os.name == "posix":
                    self.assertTrue(popen_mock.call_args.kwargs.get("start_new_session"))
                    killpg_mock.assert_called_once_with(424242, signal.SIGKILL)

            slow_run_bin = root / "stalled-run.sh"
            slow_run_bin.write_text("#!/bin/sh\nsleep 2\n", encoding="utf-8")
            slow_run_bin.chmod(0o755)
            with self.assertRaisesRegex(RuntimeError, "timed out"):
                cmd._run_anneal_diff_subcommand(
                    subcmd="run",
                    anneal_root=anneal_dir,
                    capture_bin=None,
                    mir_eval_bin=None,
                    cache_root=None,
                    anneal_diff_bin=slow_run_bin,
                    extra_args=[],
                    timeout_secs=0.05,
                )

            if os.name == "posix":
                tree_pid_file = root / "grandchild.pid"
                parent_pid_file = root / "parent.pid"
                tree_bin = root / "tree-stalled.sh"
                tree_bin.write_text(
                    "#!/bin/sh\n"
                    f'echo "$$" > "{parent_pid_file}"\n'
                    "python3 -c 'import time; time.sleep(30)' &\n"
                    f'echo "$!" > "{tree_pid_file}"\n'
                    "wait\n",
                    encoding="utf-8",
                )
                tree_bin.chmod(0o755)
                with self.assertRaisesRegex(RuntimeError, "timed out"):
                    cmd._run_anneal_diff_subcommand(
                        subcmd="run",
                        anneal_root=anneal_dir,
                        capture_bin=None,
                        mir_eval_bin=None,
                        cache_root=None,
                        anneal_diff_bin=tree_bin,
                        extra_args=[],
                        timeout_secs=0.35,
                    )
                self.assertTrue(parent_pid_file.is_file())
                self.assertTrue(tree_pid_file.is_file())
                def _pid_is_terminated(pid: int) -> bool:
                    try:
                        os.kill(pid, 0)
                    except ProcessLookupError:
                        return True
                    except OSError:
                        return False
                    proc_stat = Path(f"/proc/{pid}/stat")
                    if proc_stat.is_file():
                        try:
                            raw = proc_stat.read_text(
                                encoding="utf-8", errors="replace"
                            )
                        except FileNotFoundError:
                            return True
                        except OSError:
                            return False
                        rparen = raw.rfind(")")
                        if rparen != -1:
                            rest = raw[rparen + 1 :].lstrip()
                            if rest and rest[0] in ("Z", "X", "x"):
                                return True
                        return False
                    if sys.platform != "linux":
                        ps = subprocess.run(
                            ["ps", "-o", "stat=", "-p", str(pid)],
                            capture_output=True,
                            text=True,
                            check=False,
                        )
                        if ps.returncode != 0:
                            return True
                        state = ps.stdout.strip()
                        return (not state) or state.startswith(("Z", "X"))
                    return False

                parent_pid = int(parent_pid_file.read_text(encoding="utf-8").strip())
                grandchild_pid = int(tree_pid_file.read_text(encoding="utf-8").strip())
                deadline = time.monotonic() + 2.0
                while time.monotonic() < deadline:
                    if _pid_is_terminated(parent_pid) and _pid_is_terminated(
                        grandchild_pid
                    ):
                        break
                    time.sleep(0.05)
                self.assertTrue(_pid_is_terminated(parent_pid))
                self.assertTrue(_pid_is_terminated(grandchild_pid))

                if sys.platform == "linux":
                    # Unreaped container grandchildren stay zombie (`Z`) after
                    # `SIGKILL`; verify `_pid_is_terminated` accepts zombies.
                    zproc = subprocess.Popen([sys.executable, "-c", "pass"])
                    try:
                        z_stat = Path(f"/proc/{zproc.pid}/stat")
                        z_deadline = time.monotonic() + 2.0
                        saw_zombie = False
                        while time.monotonic() < z_deadline:
                            if z_stat.is_file():
                                raw = z_stat.read_text(
                                    encoding="utf-8", errors="replace"
                                )
                                rparen = raw.rfind(")")
                                if rparen != -1:
                                    rest = raw[rparen + 1 :].lstrip()
                                    if rest.startswith("Z"):
                                        saw_zombie = True
                                        break
                            time.sleep(0.01)
                        self.assertTrue(saw_zombie)
                        os.kill(zproc.pid, 0)
                        self.assertTrue(_pid_is_terminated(zproc.pid))
                    finally:
                        zproc.wait()

    def test_rejects_untrusted_timed_out_fields_and_enforces_run_provenance(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as tmpd:
            root = Path(tmpd).resolve()
            anneal_dir = root / "anneal"
            anneal_dir.mkdir()

            # 1. Subprocess stdout JSON must never be permitted to inject
            # `timed_out`.
            for subcmd, payload_fn in (
                ("run", _sample_diff_report),
                ("fuzz", _sample_fuzz_report),
            ):
                for bad_val in (True, 1, "yes", False):
                    payload = payload_fn()
                    payload["timed_out"] = bad_val
                    bin_path = root / f"spoof-{subcmd}.sh"
                    json_file = root / f"spoof-{subcmd}.json"
                    json_file.write_text(json.dumps(payload), encoding="utf-8")
                    bin_path.write_text(
                        f'#!/bin/sh\ncat "{json_file}"\n', encoding="utf-8"
                    )
                    bin_path.chmod(0o755)
                    with self.assertRaisesRegex(
                        ValueError, "untrusted 'timed_out' field"
                    ):
                        cmd._run_anneal_diff_subcommand(
                            subcmd=subcmd,
                            anneal_root=anneal_dir,
                            capture_bin=None,
                            mir_eval_bin=None,
                            cache_root=None,
                            anneal_diff_bin=bin_path,
                            extra_args=[],
                        )

            # 2. Direct Python callers reject any `timed_out` on `diff_report`
            # and reject non-bool / extra-key `timed_out` on `fuzz_report`.
            bad_diff = _sample_diff_report()
            bad_diff["timed_out"] = True
            with self.assertRaisesRegex(ValueError, "diff_report.*timed_out"):
                cmd.build_perf_metrics_snippet(bad_diff)
            with self.assertRaisesRegex(ValueError, "diff_report.*timed_out"):
                cmd.build_semantic_detail_report(
                    diff_report=bad_diff,
                    mir_eval_status={"executed": False, "passed": True},
                    repo="google/zerocopy",
                    branch="main",
                    commit_sha="a" * 40,
                    commit_unix_ts=1780000000,
                    environment_profile={
                        "os": "linux",
                        "arch": "x86_64",
                        "rustc_version": "rustc 1",
                        "lean_version": "lean 4",
                        "anneal_root": "anneal",
                    },
                )

            for bad_val in (1, "yes", False):
                bad_fuzz = _sample_fuzz_report()
                bad_fuzz["timed_out"] = bad_val
                with self.assertRaisesRegex(ValueError, "timed_out"):
                    cmd.validate_fuzz_report(bad_fuzz)
                with self.assertRaisesRegex(ValueError, "timed_out"):
                    cmd.build_perf_metrics_snippet(
                        _sample_diff_report(), fuzz_report=bad_fuzz
                    )
                with self.assertRaisesRegex(ValueError, "timed_out"):
                    cmd.build_semantic_detail_report(
                        diff_report=_sample_diff_report(),
                        mir_eval_status={"executed": False, "passed": True},
                        repo="google/zerocopy",
                        branch="main",
                        commit_sha="a" * 40,
                        commit_unix_ts=1780000000,
                        environment_profile={
                            "os": "linux",
                            "arch": "x86_64",
                            "rustc_version": "rustc 1",
                            "lean_version": "lean 4",
                            "anneal_root": "anneal",
                        },
                        fuzz_report=bad_fuzz,
                    )

            extra_fuzz = _sample_fuzz_report()
            extra_fuzz["timed_out"] = True
            with self.assertRaisesRegex(ValueError, "unexpected keys"):
                cmd.build_perf_metrics_snippet(
                    _sample_diff_report(), fuzz_report=extra_fuzz
                )
            with self.assertRaisesRegex(ValueError, "timed_out"):
                cmd.validate_fuzz_report(extra_fuzz)

            # 3. `report_passes` rejects `diff_ev` missing capture provenance
            # or marked `timed_out`, and `main()` enforces
            # `--expect-capture-source` on `run` even when `fuzz` times out.
            detail_bad_sha = cmd.build_semantic_detail_report(
                diff_report={
                    **_sample_diff_report(),
                    "capture_bin_source": "spoofed",
                    "capture_bin_sha256": "",
                },
                mir_eval_status={"executed": False, "passed": True},
                repo="google/zerocopy",
                branch="main",
                commit_sha="a" * 40,
                commit_unix_ts=1780000000,
                environment_profile={
                    "os": "linux",
                    "arch": "x86_64",
                    "rustc_version": "rustc 1",
                    "lean_version": "lean 4",
                    "anneal_root": "anneal",
                },
            )
            self.assertFalse(cmd.report_passes(detail_bad_sha, require_fuzz=False))

            stalled_bin = root / "stalled-fuzz-bad-run.sh"
            bad_run_json = root / "bad-run.json"
            bad_run_json.write_text(
                json.dumps(
                    {
                        **_sample_diff_report(),
                        "capture_bin_source": "spoofed",
                        "capture_bin_sha256": "",
                    }
                ),
                encoding="utf-8",
            )
            stalled_bin.write_text(
                f'#!/bin/sh\nif [ "$1" = "fuzz" ]; then sleep 2; exit 0; fi\n'
                f'cat "{bad_run_json}"\n',
                encoding="utf-8",
            )
            stalled_bin.chmod(0o755)
            out_detail = root / "bad-prov-detail.json"
            stderr_buf = io.StringIO()
            with redirect_stderr(stderr_buf):
                rc = cmd.main(
                    [
                        "--anneal-root",
                        str(anneal_dir),
                        "--anneal-diff-bin",
                        str(stalled_bin),
                        "--fuzz-timeout-secs",
                        "0.05",
                        "--expect-capture-source",
                        "env_anneal_capture",
                        "--allow-unknown-git",
                        "--output",
                        str(out_detail),
                    ]
                )
            self.assertEqual(rc, 1)
            self.assertIn(
                "capture provenance mismatch (run)", stderr_buf.getvalue()
            )
            self.assertFalse(out_detail.exists())

    def test_nix_store_wrapper_symlinks_on_path_and_explicit_overrides(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as tmpd:
            root = Path(tmpd).resolve()
            store = root / "nix" / "store"
            pkg_rust = store / "1111-rust-toolchain"
            pkg_join = store / "2222-join-toolchain"
            (pkg_rust / "bin").mkdir(parents=True)
            (pkg_join / "bin").mkdir(parents=True)
            real_cargo = pkg_rust / "bin" / "cargo"
            real_rustc = pkg_rust / "bin" / "rustc"
            real_lean = pkg_rust / "bin" / "lean"
            for exe in (real_cargo, real_rustc, real_lean):
                exe.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
                exe.chmod(0o755)
            os.symlink(real_cargo, pkg_join / "bin" / "cargo")

            opt_dir = root / "opt" / "anneal-nix"
            opt_dir.mkdir(parents=True)
            opt_rust = opt_dir / "rust-toolchain"
            os.symlink(pkg_rust, opt_rust)
            build_rustc = opt_dir / "build-rustc"
            build_rustc.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            build_rustc.chmod(0o755)

            outside_dir = root / "outside"
            outside_dir.mkdir()
            outside_bin = outside_dir / "cargo"
            outside_bin.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            outside_wrap = root / "opt" / "bad-toolchain"
            os.symlink(outside_dir, outside_wrap)
            store_escape = store / "3333-escape"
            (store_escape / "bin").mkdir(parents=True)
            os.symlink(outside_bin, store_escape / "bin" / "cargo")
            store_hard = store / "4444-hard"
            (store_hard / "bin").mkdir(parents=True)
            os.link(outside_bin, store_hard / "bin" / "rustc")

            with mock.patch.dict(
                os.environ,
                {"PATH": f"{opt_rust / 'bin'}{os.pathsep}{pkg_join / 'bin'}"},
                clear=False,
            ):
                resolved_cargo = cmd._resolve_command_from_path(
                    "cargo",
                    root,
                    allow_rustup_proxy=True,
                    store_prefix=store,
                )
                resolved_join_rustc = cmd._resolve_executable_cli_path(
                    opt_rust / "bin" / "rustc",
                    "RUSTC",
                    base_dir=root,
                    store_prefix=store,
                )
            self.assertEqual(resolved_cargo, str(real_cargo))
            self.assertEqual(resolved_join_rustc, real_rustc)
            self.assertEqual(
                cmd._resolve_executable_cli_path(
                    pkg_join / "bin" / "cargo",
                    "CARGO",
                    base_dir=root,
                    store_prefix=store,
                ),
                real_cargo,
            )

            with mock.patch.dict(
                os.environ, {"PATH": str(outside_wrap)}, clear=False
            ):
                with self.assertRaisesRegex(ValueError, "symlink"):
                    cmd._resolve_command_from_path(
                        "cargo",
                        root,
                        allow_rustup_proxy=True,
                        store_prefix=store,
                    )

            with mock.patch.dict(
                os.environ, {"PATH": str(store_escape / "bin")}, clear=False
            ):
                with self.assertRaisesRegex(ValueError, "escaped store"):
                    cmd._resolve_command_from_path(
                        "cargo",
                        root,
                        allow_rustup_proxy=True,
                        store_prefix=store,
                    )

            with mock.patch.dict(
                os.environ, {"PATH": str(store_hard / "bin")}, clear=False
            ):
                with self.assertRaisesRegex(ValueError, "hardlink"):
                    cmd._resolve_command_from_path(
                        "rustc",
                        root,
                        allow_rustup_proxy=True,
                        store_prefix=store,
                    )

            real_miri = root / "real-miri"
            real_miri.mkdir()
            sym_miri_leaf = root / "sym-miri-leaf"
            os.symlink(real_miri, sym_miri_leaf)
            sym_miri_parent = root / "sym-miri-parent"
            os.symlink(real_miri, sym_miri_parent)
            (real_miri / "nested").mkdir()
            for bad_miri, pat in (
                (str(sym_miri_leaf), "symlink"),
                (str(sym_miri_parent / "nested"), "symlink"),
                ("real-miri/../real-miri", "parent traversal"),
            ):
                with _patch_clean_tool_env(
                    {
                        "PATH": str(outside_dir),
                        "ANNEAL_MIRI_SYSROOT": bad_miri,
                    }
                ):
                    with self.assertRaisesRegex(ValueError, pat):
                        cmd._build_child_env(root)

            # Store-contained `/nix/store` `symlinkJoin` and wrapper symlinks
            # into `/nix/store` are allowed and canonicalized for
            # `ANNEAL_MIRI_SYSROOT` (`miri_runner.rs` parity), while escapes
            # fail.
            store_miri_src = store / "miri-src"
            (store_miri_src / "lib" / "rustlib").mkdir(parents=True)
            (store_miri_src / ".anneal-miri-ready").write_text("ok\n", encoding="utf-8")
            store_miri_join = store / "miri-join"
            store_miri_join.mkdir()
            os.symlink(store_miri_src / "lib", store_miri_join / "lib")
            wrap_miri = root / "wrap-miri"
            os.symlink(store_miri_src, wrap_miri)
            store_miri_escape = store / "miri-escape"
            os.symlink(real_miri, store_miri_escape)
            with mock.patch.object(cmd, "_STORE_PREFIX", store):
                for ok_miri, expected in (
                    (store_miri_join, store_miri_join.resolve(strict=True)),
                    (wrap_miri, store_miri_src.resolve(strict=True)),
                ):
                    with _patch_clean_tool_env(
                        {
                            "PATH": str(outside_dir),
                            "ANNEAL_MIRI_SYSROOT": str(ok_miri),
                        }
                    ):
                        built = cmd._build_child_env(root)
                        self.assertEqual(built["ANNEAL_MIRI_SYSROOT"], str(expected))
                with _patch_clean_tool_env(
                    {
                        "PATH": str(outside_dir),
                        "ANNEAL_MIRI_SYSROOT": str(store_miri_escape),
                    }
                ):
                    with self.assertRaisesRegex(ValueError, "escaped store"):
                        cmd._build_child_env(root)
                with _patch_clean_tool_env(
                    {
                        "PATH": str(outside_dir),
                        "ANNEAL_MIRI_SYSROOT": str(sym_miri_leaf),
                    }
                ):
                    with self.assertRaisesRegex(ValueError, "symlink"):
                        cmd._build_child_env(root)

    def test_lean_probe_aborted_and_unwound_outcomes(self) -> None:
        aborted_out = {
            "kind": "abnormal_abort",
            "detail": "Trusted.MirModel.TerminalOut.aborted",
        }
        unwound_out = {
            "kind": "unwound",
            "detail": "Trusted.MirModel.TerminalOut.unwound",
        }
        self.assertTrue(cmd._verify_lean_probe_payload("ABORTED", aborted_out))
        self.assertFalse(
            cmd._verify_lean_probe_payload(
                "ABORTED", {"kind": "abnormal_abort", "detail": "wrong"}
            )
        )
        self.assertFalse(
            cmd._verify_lean_probe_payload(
                "ABORTED", {"kind": "panic", "detail": "panicked"}
            )
        )

        cap_body = {"body_id": 0, "fn_identity": "fn_a"}
        self.assertTrue(
            cmd._lean_probe_line_matches_outcome(
                "ANNEAL_LEAN_CASE:c1:BODY|0|fn_a|MR0:ABORTED",
                "c1",
                aborted_out,
                capture_body=cap_body,
            )
        )
        self.assertFalse(
            cmd._lean_probe_line_matches_outcome(
                "ANNEAL_LEAN_CASE:c1:BODY|0|fn_a|MR0:ABORTED",
                "c1",
                {"kind": "abnormal_abort", "detail": "wrong"},
                capture_body=cap_body,
            )
        )
        self.assertTrue(
            cmd._lean_probe_line_matches_outcome(
                "ANNEAL_LEAN_CASE:c1:BODY|0|fn_a|MR0:UNWOUND",
                "c1",
                unwound_out,
                capture_body=cap_body,
            )
        )
        self.assertFalse(
            cmd._lean_probe_line_matches_outcome(
                "ANNEAL_LEAN_CASE:c1:BODY|0|fn_a|MR0:UNWOUND",
                "c1",
                {"kind": "unwound", "detail": "wrong"},
                capture_body=cap_body,
            )
        )

        abort_report = _sample_fuzz_report()
        c0 = abort_report["cases"][0]
        c0["rustc"] = dict(aborted_out)
        c0["miri"] = dict(aborted_out)
        c0["lean"] = dict(aborted_out)
        c0["evaluation"]["agreement"] = "bi_fault_equiv_agreement"
        c0["evaluation"]["rustc_status"] = {"status": "agreed"}
        if c0.get("exercised_move_reinit"):
            c0["exercised_move_reinit"] = False
            c0.pop("move_reinit_evidence", None)
            abort_report["metrics"]["move_reinit_exercised_count"] -= 1
        abort_report["metrics"]["admitted_cases"] -= 1
        abort_report["metrics"]["admission_rate"] = (
            abort_report["metrics"]["admitted_cases"]
            / abort_report["metrics"]["admission_eligible_cases"]
        )
        c0["leg_evidence"] = _sample_leg_evidence(
            c0["case_id"],
            c0["fn_name"],
            miri=aborted_out,
            lean=aborted_out,
            rustc=aborted_out,
            capture_body=c0["capture_body"],
        )
        cmd.validate_fuzz_report(abort_report)
        tampered = json.loads(json.dumps(abort_report))
        tampered["cases"][0]["lean"]["detail"] = "spoofed"
        with self.assertRaisesRegex(ValueError, "lean_probe_line"):
            cmd.validate_fuzz_report(tampered)

    def test_main_capture_bin_rejects_bad_paths_and_allows_cargo_deps_hardlink(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as tmpd:
            root = Path(tmpd).resolve()
            anneal_dir = root / "anneal"
            deps_dir = anneal_dir / "target" / "debug" / "deps"
            deps_dir.mkdir(parents=True)
            real_cap = root / "real-cap"
            real_cap.write_bytes(b"cap-bytes")
            rogue_cap = root / "rogue-cap-hardlink"
            os.link(real_cap, rogue_cap)
            sym_cap = root / "sym-cap"
            sym_cap.symlink_to(real_cap)
            mir_eval_manifest = root / "mir_eval_manifest.json"
            mir_eval_manifest.write_text("{}", encoding="utf-8")

            with (
                _patch_subprocess_exec() as no_exec,
                mock.patch.object(cmd, "maybe_run_mir_eval_manifest") as m_eval,
                mock.patch.object(cmd, "run_anneal_diff") as m_diff,
            ):
                with self.assertRaisesRegex(ValueError, "hard"):
                    cmd.main(
                        [
                            "--anneal-root",
                            str(anneal_dir),
                            "--capture-bin",
                            str(rogue_cap),
                            "--mir-eval-manifest",
                            str(mir_eval_manifest),
                        ]
                    )
                with self.assertRaisesRegex(ValueError, "symlink"):
                    cmd.main(
                        [
                            "--anneal-root",
                            str(anneal_dir),
                            "--capture-bin",
                            str(sym_cap),
                            "--mir-eval-manifest",
                            str(mir_eval_manifest),
                        ]
                    )
                m_eval.assert_not_called()
                m_diff.assert_not_called()
                no_exec.assert_not_called()

            cargo_dep = deps_dir / "anneal_rustc_capture-abc"
            cargo_dep.write_bytes(b"cargo-cap-bytes")
            cargo_cap = anneal_dir / "target" / "debug" / "anneal-rustc-capture"
            os.link(cargo_dep, cargo_cap)
            diff_ok = _sample_diff_report()
            fuzz_ok = _sample_fuzz_report()
            observed_caps: list[tuple[Path, int, int, bytes]] = []

            def _capture_diff_spy(**kwargs: Any) -> tuple[int, dict[str, Any]]:
                cb = kwargs["capture_bin"]
                st = os.lstat(cb)
                observed_caps.append(
                    (cb, st.st_nlink, stat.S_IMODE(st.st_mode), cb.read_bytes())
                )
                return (0, diff_ok)

            with (
                _patch_clean_tool_env({"TMPDIR": str(root)}),
                mock.patch.object(
                    cmd,
                    "maybe_run_mir_eval_manifest",
                    return_value=({"executed": False, "passed": None}, None),
                ),
                mock.patch.object(
                    cmd, "run_anneal_diff", side_effect=_capture_diff_spy
                ) as m_diff,
                mock.patch.object(
                    cmd, "run_anneal_fuzz", return_value=(0, fuzz_ok)
                ) as m_fuzz,
                mock.patch.object(
                    cmd,
                    "_git_metadata",
                    return_value=("main", "a" * 40, 1_780_000_000),
                ),
                mock.patch.object(
                    cmd,
                    "_collect_environment",
                    return_value={"os": "linux", "arch": "x86_64"},
                ),
                redirect_stdout(io.StringIO()),
            ):
                rc = cmd.main(
                    [
                        "--anneal-root",
                        str(anneal_dir),
                        "--capture-bin",
                        str(cargo_cap),
                        "--allow-unknown-git",
                    ]
                )
            self.assertEqual(rc, 0)
            iso_cap = m_diff.call_args.kwargs["capture_bin"]
            self.assertEqual(m_fuzz.call_args.kwargs["capture_bin"], iso_cap)
            self.assertEqual(len(observed_caps), 1)
            obs_path, obs_nlink, obs_mode, obs_bytes = observed_caps[0]
            self.assertEqual(obs_path, iso_cap)
            self.assertIn(".anneal-isolated-bins", str(obs_path))
            self.assertEqual(obs_nlink, 1)
            self.assertEqual(obs_mode, 0o555)
            self.assertEqual(obs_bytes, b"cargo-cap-bytes")
            self.assertFalse(iso_cap.exists())
            self.assertFalse(
                (anneal_dir / "target" / ".anneal-isolated-bins").exists()
            )

    def test_cargo_run_pins_validated_linker_and_minimal_path(self) -> None:
        with tempfile.TemporaryDirectory() as tmpd:
            root = Path(tmpd).resolve()
            anneal_dir = root / "anneal"
            anneal_dir.mkdir(parents=True)
            (anneal_dir / "Cargo.toml").write_text(
                '[workspace]\nmembers = ["tests/differential"]\n',
                encoding="utf-8",
            )
            clean_bin = root / "clean-bin"
            clean_bin.mkdir()
            real_cargo = clean_bin / "cargo"
            real_rustc = clean_bin / "rustc"
            for exe in (real_cargo, real_rustc):
                exe.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
                exe.chmod(0o755)

            poisoned_dir = root / "poisoned-ambient-bin"
            poisoned_dir.mkdir()
            poisoned_cc = poisoned_dir / "cc"
            poisoned_cc.write_text("#!/bin/sh\nexit 1\n", encoding="utf-8")
            poisoned_cc.chmod(0o755)

            seen_cargo_runs: list[tuple[list[str], dict[str, str]]] = []
            diff_json = json.dumps(_sample_diff_report())

            def _mock_cargo_run(args: list[str], **kwargs: Any) -> mock.Mock:
                seen_cargo_runs.append(
                    (list(args), dict(kwargs.get("env") or {}))
                )
                return mock.Mock(returncode=0, stdout=diff_json, stderr="")

            with (
                _patch_clean_tool_env(
                    {"PATH": f"{poisoned_dir}{os.pathsep}{clean_bin}"}
                ),
                _patch_subprocess_exec(side_effect=_mock_cargo_run),
            ):
                rc, _ = cmd.run_anneal_diff(
                    anneal_root=anneal_dir,
                    manifest=None,
                    capture_bin=None,
                    mir_eval_bin=None,
                    cache_root=None,
                    self_check_oracle=False,
                )
            self.assertEqual(rc, 0)
            self.assertEqual(len(seen_cargo_runs), 1)
            run_args, run_env = seen_cargo_runs[0]
            dash_idx = run_args.index("--")
            cfg_indices = [
                i for i, tok in enumerate(run_args) if tok == "--config"
            ]
            linker_cfgs = [
                run_args[i + 1]
                for i in cfg_indices
                if i + 1 < dash_idx
                and run_args[i + 1].startswith('target."cfg(all())".linker=')
            ]
            self.assertEqual(len(linker_cfgs), 1, run_args)
            pinned_linker = json.loads(linker_cfgs[0].split("=", 1)[1])
            self.assertNotIn("poisoned-ambient-bin", pinned_linker)
            self.assertNotEqual(run_env["CARGO"], str(real_cargo))
            self.assertNotEqual(run_env["RUSTC"], str(real_rustc))
            self.assertIn(".anneal-isolated-bins", run_env["CARGO"])
            self.assertIn(".anneal-isolated-bins", run_env["RUSTC"])
            self.assertEqual(Path(run_env["CARGO"]).name, "cargo")
            self.assertEqual(Path(run_env["RUSTC"]).name, "rustc")
            path_entries = run_env["PATH"].split(os.pathsep)
            self.assertNotIn(str(poisoned_dir), path_entries)
            self.assertNotIn(str(clean_bin), path_entries)
            self.assertIn(str(Path(run_env["CARGO"]).parent), path_entries)
            self.assertIn(str(Path(run_env["RUSTC"]).parent), path_entries)
            self.assertIn(str(Path(pinned_linker).parent), path_entries)

            # Store-contained linker resolution prefers `/nix/store` linker for
            # store-contained `rustc` and rejects store-escaping symlinks.
            store = root / "nix" / "store"
            store_gcc = store / "5555-gcc-wrapper" / "bin" / "cc"
            store_gcc.parent.mkdir(parents=True)
            store_gcc.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            store_gcc.chmod(0o755)
            store_rustc = store / "6666-rust" / "bin" / "rustc"
            store_rustc.parent.mkdir(parents=True)
            store_rustc.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            store_rustc.chmod(0o755)
            trusted_dir = root / "trusted-usr-bin"
            trusted_dir.mkdir()
            trusted_cc = trusted_dir / cmd._LINKER_BIN_NAME
            trusted_cc.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            trusted_cc.chmod(0o755)
            resolved_store_cc = cmd._resolve_validated_linker(
                store_rustc,
                root,
                f"{poisoned_dir}{os.pathsep}{store_gcc.parent}",
                store_prefix=store,
                trusted_dirs=(trusted_dir,),
                symlink_dirs=(),
            )
            self.assertEqual(resolved_store_cc, store_gcc)

            esc_cc_dir = store / "7777-esc" / "bin"
            esc_cc_dir.mkdir(parents=True)
            os.symlink(poisoned_cc, esc_cc_dir / cmd._LINKER_BIN_NAME)
            with self.assertRaisesRegex(ValueError, "escaped store"):
                cmd._resolve_validated_linker(
                    store_rustc,
                    root,
                    str(esc_cc_dir),
                    store_prefix=store,
                    trusted_dirs=(trusted_dir,),
                    symlink_dirs=(),
                )

            # `rustup` symlink proxies in `_run_anneal_diff_subcommand` unwrap
            # CARGO/RUSTC to the pinned toolchain AND preserve validated
            # `rustup` proxy dir AFTER the pinned toolchain bin dir on PATH
            # so `anneal-diff`'s sysroot lookup (`rustup`) succeeds when
            # `ANNEAL_SYSROOT` is unset.
            proxy_bin = root / "rustup-cargo-bin"
            proxy_bin.mkdir()
            tc_bin = root / "rustup-tc" / "bin"
            tc_bin.mkdir(parents=True)
            tc_cargo = tc_bin / "cargo"
            tc_rustc = tc_bin / "rustc"
            for exe in (tc_cargo, tc_rustc):
                exe.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
                exe.chmod(0o755)
            rustup_exe = proxy_bin / "rustup"
            rustup_exe.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            rustup_exe.chmod(0o755)
            os.symlink("rustup", proxy_bin / "cargo")
            os.symlink("rustup", proxy_bin / "rustc")

            proxy_runs: list[tuple[list[str], dict[str, str]]] = []
            proxy_which_cmds: list[str] = []

            def _mock_proxy_cargo_run(
                args: list[str], **kwargs: Any
            ) -> mock.Mock:
                if len(args) >= 3 and args[1] == "which":
                    proxy_which_cmds.append(args[0])
                    out = str(tc_cargo if args[2] == "cargo" else tc_rustc)
                    return mock.Mock(returncode=0, stdout=out + "\n", stderr="")
                proxy_runs.append((list(args), dict(kwargs.get("env") or {})))
                return mock.Mock(returncode=0, stdout=diff_json, stderr="")

            with (
                _patch_clean_tool_env(
                    {
                        "HOME": str(root),
                        "PATH": f"{poisoned_dir}{os.pathsep}{proxy_bin}",
                    }
                ),
                _patch_subprocess_exec(side_effect=_mock_proxy_cargo_run),
            ):
                rc_p, _ = cmd.run_anneal_diff(
                    anneal_root=anneal_dir,
                    manifest=None,
                    capture_bin=None,
                    mir_eval_bin=None,
                    cache_root=None,
                    self_check_oracle=False,
                )
            self.assertEqual(rc_p, 0)
            self.assertEqual(len(proxy_which_cmds), 2)
            for w_exe in proxy_which_cmds:
                self.assertNotEqual(w_exe, str(rustup_exe))
                self.assertIn(".anneal-isolated-bins", w_exe)
                self.assertEqual(Path(w_exe).name, "rustup")
            self.assertEqual(len(proxy_runs), 1)
            _, proxy_run_env = proxy_runs[0]
            self.assertNotEqual(proxy_run_env["CARGO"], str(tc_cargo))
            self.assertNotEqual(proxy_run_env["RUSTC"], str(tc_rustc))
            self.assertIn(".anneal-isolated-bins", proxy_run_env["CARGO"])
            self.assertIn(".anneal-isolated-bins", proxy_run_env["RUSTC"])
            p_entries = proxy_run_env["PATH"].split(os.pathsep)
            self.assertNotIn(str(poisoned_dir), p_entries)
            self.assertNotIn(str(tc_bin), p_entries)
            self.assertIn(str(Path(proxy_run_env["CARGO"]).parent), p_entries)
            self.assertIn(str(Path(proxy_run_env["RUSTC"]).parent), p_entries)
            self.assertIn(str(proxy_bin), p_entries)
            self.assertLess(
                p_entries.index(str(Path(proxy_run_env["RUSTC"]).parent)),
                p_entries.index(str(proxy_bin)),
                p_entries,
            )

            # Direct pinned CARGO/RUSTC paths also keep a validated ambient
            # `rustup` directory after staged toolchain bin dirs when running
            # `anneal-diff`.
            direct_runs: list[dict[str, str]] = []

            def _mock_direct_cargo_run(
                _args: list[str], **kwargs: Any
            ) -> mock.Mock:
                direct_runs.append(dict(kwargs.get("env") or {}))
                return mock.Mock(returncode=0, stdout=diff_json, stderr="")

            with (
                _patch_clean_tool_env(
                    {
                        "HOME": str(root),
                        "CARGO": str(tc_cargo),
                        "RUSTC": str(tc_rustc),
                        "PATH": f"{poisoned_dir}{os.pathsep}{proxy_bin}",
                    }
                ),
                _patch_subprocess_exec(side_effect=_mock_direct_cargo_run),
            ):
                rc_d, _ = cmd.run_anneal_diff(
                    anneal_root=anneal_dir,
                    manifest=None,
                    capture_bin=None,
                    mir_eval_bin=None,
                    cache_root=None,
                    self_check_oracle=False,
                )
            self.assertEqual(rc_d, 0)
            d_entries = direct_runs[0]["PATH"].split(os.pathsep)
            self.assertNotIn(str(poisoned_dir), d_entries)
            self.assertNotIn(str(tc_bin), d_entries)
            self.assertLess(
                d_entries.index(str(Path(direct_runs[0]["RUSTC"]).parent)),
                d_entries.index(str(proxy_bin)),
                d_entries,
            )

            # Non-store `<prefix>/lib` trees recursively reject symlinked and
            # hardlinked descendants before exporting `LD_LIBRARY_PATH`; Nix
            # store `lib/` trees permit store-contained symlinks while
            # rejecting escaping symlinks and hardlinks.
            evil_so = root / "evil-outside.so"
            evil_so.write_bytes(b"evil-shared-lib")
            tc_nested_lib = root / "rustup-tc" / "lib" / "rustlib" / "host" / "lib"
            tc_nested_lib.mkdir(parents=True)
            sym_so = tc_nested_lib / "libstd-bad.so"
            os.symlink(evil_so, sym_so)
            with (
                _patch_clean_tool_env(
                    {
                        "HOME": str(root),
                        "CARGO": str(tc_cargo),
                        "RUSTC": str(tc_rustc),
                        "PATH": str(tc_bin),
                    }
                ),
                _patch_subprocess_exec() as no_exec,
            ):
                with self.assertRaisesRegex(ValueError, "symlink"):
                    cmd.run_anneal_diff(
                        anneal_root=anneal_dir,
                        manifest=None,
                        capture_bin=None,
                        mir_eval_bin=None,
                        cache_root=None,
                        self_check_oracle=False,
                    )
                no_exec.assert_not_called()
            sym_so.unlink()

            hard_so = tc_nested_lib / "libstd-hard.so"
            os.link(evil_so, hard_so)
            with (
                _patch_clean_tool_env(
                    {
                        "HOME": str(root),
                        "CARGO": str(tc_cargo),
                        "RUSTC": str(tc_rustc),
                        "PATH": str(tc_bin),
                    }
                ),
                _patch_subprocess_exec() as no_exec,
            ):
                with self.assertRaisesRegex(ValueError, "hardlink"):
                    cmd.run_anneal_diff(
                        anneal_root=anneal_dir,
                        manifest=None,
                        capture_bin=None,
                        mir_eval_bin=None,
                        cache_root=None,
                        self_check_oracle=False,
                    )
                no_exec.assert_not_called()
            hard_so.unlink()

            reg_so = tc_nested_lib / "libstd-ok.so"
            reg_so.write_bytes(b"clean-shared-lib")
            # Confined intra-`lib/` relative deduplication symlinks matching
            # `pack_omnibus_archive.sh` (`../../../libLLVM-test.so`) succeed
            # and non-store `lib/` trees (with or without confined links) are
            # materialized into a private read-only symlink-free directory so
            # post-validation symlink retargets or file edits cannot affect it.
            llvm_top = root / "rustup-tc" / "lib" / "libLLVM-test.so"
            llvm_top.write_bytes(b"llvm-so")
            top_link = root / "rustup-tc" / "lib" / "libtop-dedup.so"
            os.symlink("rustlib/host/lib/libstd-ok.so", top_link)
            dedup_so = tc_nested_lib / "libLLVM-test.so"
            os.symlink("../../../libLLVM-test.so", dedup_so)
            with ExitStack() as lib_stack:
                ok_lib = cmd._validate_rustc_sysroot_lib_dir(
                    tc_rustc,
                    base_dir=root,
                    exit_stack=lib_stack,
                    store_prefix=store,
                )
                assert ok_lib is not None
                self.assertNotEqual(
                    ok_lib, (root / "rustup-tc" / "lib").resolve()
                )
                self.assertEqual(stat.S_IMODE(os.lstat(ok_lib).st_mode), 0o555)
                staged_llvm = ok_lib / "libLLVM-test.so"
                staged_top = ok_lib / "libtop-dedup.so"
                self.assertFalse(staged_llvm.is_symlink())
                self.assertFalse(staged_top.is_symlink())
                self.assertEqual(os.lstat(staged_top).st_nlink, 1)
                self.assertEqual(stat.S_IMODE(os.lstat(staged_top).st_mode), 0o444)
                # Retargeting the original symlink or overwriting the original
                # library after staging cannot alter the staged copy.
                top_link.unlink()
                os.symlink(evil_so, top_link)
                llvm_top.write_bytes(b"tampered-llvm-so")
                self.assertEqual(staged_llvm.read_bytes(), b"llvm-so")
                self.assertEqual(staged_top.read_bytes(), b"clean-shared-lib")

            top_link.unlink()

            rel_esc_so = tc_nested_lib / "libesc-rel.so"
            os.symlink("../../../../evil-outside.so", rel_esc_so)
            with ExitStack() as lib_stack:
                with self.assertRaisesRegex(ValueError, "escaped"):
                    cmd._validate_rustc_sysroot_lib_dir(
                        tc_rustc,
                        base_dir=root,
                        exit_stack=lib_stack,
                        store_prefix=store,
                    )
            rel_esc_so.unlink()

            dir_sym = root / "rustup-tc" / "lib" / "rustlib" / "dirsym"
            os.symlink("host", dir_sym)
            with ExitStack() as lib_stack:
                with self.assertRaisesRegex(ValueError, "regular file"):
                    cmd._validate_rustc_sysroot_lib_dir(
                        tc_rustc,
                        base_dir=root,
                        exit_stack=lib_stack,
                        store_prefix=store,
                    )
            dir_sym.unlink()
            dedup_so.unlink()
            # Writable non-store `lib/` WITHOUT symlinks also materializes
            # into a private immutable staging dir.
            with ExitStack() as lib_stack:
                plain_lib = cmd._validate_rustc_sysroot_lib_dir(
                    tc_rustc,
                    base_dir=root,
                    exit_stack=lib_stack,
                    store_prefix=store,
                )
                assert plain_lib is not None
                self.assertNotEqual(
                    plain_lib, (root / "rustup-tc" / "lib").resolve()
                )
                self.assertEqual(
                    stat.S_IMODE(os.lstat(plain_lib).st_mode), 0o555
                )
            llvm_top.unlink()

            store_tc_real = store / "8888-rust-libs" / "lib" / "rustlib" / "lib"
            store_tc_real.mkdir(parents=True)
            (store_tc_real / "libstd-store.so").write_bytes(b"store-so")
            store_join_lib = store / "6666-rust" / "lib" / "rustlib" / "lib"
            store_join_lib.mkdir(parents=True)
            os.symlink(
                store_tc_real / "libstd-store.so",
                store_join_lib / "libstd-store.so",
            )
            with ExitStack() as lib_stack:
                ok_store_lib = cmd._validate_rustc_sysroot_lib_dir(
                    store_rustc,
                    base_dir=root,
                    exit_stack=lib_stack,
                    store_prefix=store,
                )
                self.assertEqual(
                    ok_store_lib, (store / "6666-rust" / "lib").resolve()
                )

            store_esc_so = store_join_lib / "libesc.so"
            os.symlink(evil_so, store_esc_so)
            with ExitStack() as lib_stack:
                with self.assertRaisesRegex(ValueError, "escaped store"):
                    cmd._validate_rustc_sysroot_lib_dir(
                        store_rustc,
                        base_dir=root,
                        exit_stack=lib_stack,
                        store_prefix=store,
                    )
            store_esc_so.unlink()

            store_hard_so = store_join_lib / "libhard.so"
            os.link(evil_so, store_hard_so)
            with ExitStack() as lib_stack:
                with self.assertRaisesRegex(ValueError, "hardlink"):
                    cmd._validate_rustc_sysroot_lib_dir(
                        store_rustc,
                        base_dir=root,
                        exit_stack=lib_stack,
                        store_prefix=store,
                    )
            store_hard_so.unlink()

            # Unsafe symlinked `TMPDIR` fails closed before building.
            sym_tmp = root / "sym-tmp"
            os.symlink(root / "outside-dir", sym_tmp)
            with (
                _patch_clean_tool_env(
                    {
                        "HOME": str(root),
                        "TMPDIR": str(sym_tmp),
                        "PATH": str(tc_bin),
                    }
                ),
                _patch_subprocess_exec() as no_exec,
            ):
                with self.assertRaisesRegex(ValueError, "symlink"):
                    cmd.run_anneal_diff(
                        anneal_root=anneal_dir,
                        manifest=None,
                        capture_bin=None,
                        mir_eval_bin=None,
                        cache_root=None,
                        self_check_oracle=False,
                    )
                no_exec.assert_not_called()

    def test_single_link_anneal_diff_bin_staged_0o555_against_tamper_and_store_zero_copy(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as tmpd:
            root = Path(tmpd).resolve()
            anneal_dir = root / "anneal"
            anneal_dir.mkdir()
            diff_json = root / "diff.json"
            fuzz_json = root / "fuzz.json"
            diff_json.write_text(
                json.dumps(_sample_diff_report()), encoding="utf-8"
            )
            fuzz_json.write_text(
                json.dumps(_sample_fuzz_report()), encoding="utf-8"
            )
            diff_bin = root / "writable-anneal-diff.sh"
            # On `run`, overwrite `writable-anneal-diff.sh` before `fuzz` starts
            # to verify `main()` freezes and reuses the private `0o555` stage.
            diff_bin.write_text(
                "#!/bin/sh\nset -eu\n"
                'if [ "${1:-}" = "run" ]; then\n'
                f'  printf \'#!/bin/sh\\necho TAMPERED >&2\\nexit 99\\n\' > "{diff_bin}"\n'
                f'  cat "{diff_json}"\n'
                "  exit 0\n"
                "fi\n"
                f'cat "{fuzz_json}"\n',
                encoding="utf-8",
            )
            diff_bin.chmod(0o755)
            with (
                _patch_clean_tool_env({"TMPDIR": str(root)}),
                mock.patch.object(
                    cmd,
                    "_git_metadata",
                    return_value=("main", "a" * 40, 1_780_000_000),
                ),
                mock.patch.object(
                    cmd,
                    "_collect_environment",
                    return_value={"os": "linux", "arch": "x86_64"},
                ),
                redirect_stdout(io.StringIO()),
            ):
                rc = cmd.main(
                    [
                        "--anneal-root",
                        str(anneal_dir),
                        "--anneal-diff-bin",
                        str(diff_bin),
                    ]
                )
            self.assertEqual(rc, 0)
            self.assertIn("TAMPERED", diff_bin.read_text(encoding="utf-8"))

            # Direct `run_anneal_diff` on a single-link binary also stages
            # `0o555` and cleans up its private staging dir on return.
            direct_bin = root / "direct-anneal-diff.sh"
            direct_bin.write_text(
                f'#!/bin/sh\ncat "{diff_json}"\n', encoding="utf-8"
            )
            direct_bin.chmod(0o755)
            observed: list[tuple[Path, int, int, int]] = []
            orig_proc = cmd._run_anneal_diff_proc

            def _spy_proc(argv: list[str], **kwargs: Any) -> tuple[int, dict[str, Any]]:
                exe = Path(argv[0])
                observed.append(
                    (
                        exe,
                        stat.S_IMODE(os.lstat(exe).st_mode),
                        stat.S_IMODE(os.lstat(exe.parent).st_mode),
                        os.lstat(exe).st_nlink,
                    )
                )
                return orig_proc(argv, **kwargs)

            with (
                _patch_clean_tool_env({"TMPDIR": str(root)}),
                mock.patch.object(
                    cmd, "_run_anneal_diff_proc", side_effect=_spy_proc
                ),
            ):
                rc_direct, _ = cmd.run_anneal_diff(
                    anneal_root=anneal_dir,
                    manifest=None,
                    capture_bin=None,
                    mir_eval_bin=None,
                    cache_root=None,
                    self_check_oracle=False,
                    anneal_diff_bin=direct_bin,
                )
            self.assertEqual(rc_direct, 0)
            self.assertEqual(len(observed), 1)
            exe_path, exe_mode, dir_mode, exe_nlink = observed[0]
            self.assertNotEqual(exe_path, direct_bin)
            self.assertIn(".anneal-isolated-bins", str(exe_path))
            self.assertEqual(exe_mode, 0o555)
            self.assertEqual(dir_mode, 0o555)
            self.assertEqual(exe_nlink, 1)
            self.assertFalse(exe_path.exists())

            # Verified Nix-store executables remain zero-copy without staging,
            # and both `main()` and pre-staged `run_anneal_{diff,fuzz}` accept
            # them on Linux alongside `/proc/self/fd/<fd>`-staged executables.
            fake_store = root / "nix" / "store"
            store_pkg = fake_store / "9999-anneal-diff"
            (store_pkg / "bin").mkdir(parents=True)
            store_diff = store_pkg / "bin" / "anneal-diff"
            store_diff.write_text(
                "#!/bin/sh\nset -eu\n"
                'if [ "${1:-}" = "run" ]; then\n'
                f'  cat "{diff_json}"\n'
                "  exit 0\n"
                "fi\n"
                f'cat "{fuzz_json}"\n',
                encoding="utf-8",
            )
            store_diff.chmod(0o555)
            with ExitStack() as st:
                staged_store = cmd._stage_verified_executable(
                    store_diff,
                    "anneal-diff",
                    allow_cargo_deps_hardlink=True,
                    exit_stack=st,
                    base_dir=root,
                    store_prefix=fake_store,
                )
                self.assertEqual(staged_store, store_diff.resolve(strict=True))
            observed.clear()
            with (
                _patch_clean_tool_env({"TMPDIR": str(root)}),
                mock.patch.object(cmd, "_STORE_PREFIX", fake_store),
                mock.patch.object(
                    cmd, "_run_anneal_diff_proc", side_effect=_spy_proc
                ),
                mock.patch.object(
                    cmd,
                    "_git_metadata",
                    return_value=("main", "a" * 40, 1_780_000_000),
                ),
                mock.patch.object(
                    cmd,
                    "_collect_environment",
                    return_value={"os": "linux", "arch": "x86_64"},
                ),
                redirect_stdout(io.StringIO()),
            ):
                rc_store_main = cmd.main(
                    [
                        "--anneal-root",
                        str(anneal_dir),
                        "--anneal-diff-bin",
                        str(store_diff),
                    ]
                )
                rc_store_diff, _ = cmd.run_anneal_diff(
                    anneal_root=anneal_dir,
                    manifest=None,
                    capture_bin=None,
                    mir_eval_bin=None,
                    cache_root=None,
                    self_check_oracle=False,
                    anneal_diff_bin=staged_store,
                    _anneal_diff_pre_staged=True,
                )
                rc_store_fuzz, _ = cmd.run_anneal_fuzz(
                    anneal_root=anneal_dir,
                    capture_bin=None,
                    mir_eval_bin=None,
                    cache_root=None,
                    seed=0,
                    cases=8,
                    max_stmts=6,
                    ub_ratio=0.1,
                    min_admission_rate=0.5,
                    fuel=200,
                    anneal_diff_bin=staged_store,
                    _anneal_diff_pre_staged=True,
                )
                if sys.platform.startswith("linux"):
                    with self.assertRaisesRegex(
                        ValueError, "missing live fd handle"
                    ):
                        cmd.run_anneal_diff(
                            anneal_root=anneal_dir,
                            manifest=None,
                            capture_bin=None,
                            mir_eval_bin=None,
                            cache_root=None,
                            self_check_oracle=False,
                            anneal_diff_bin=direct_bin,
                            _anneal_diff_pre_staged=True,
                        )
            self.assertEqual((rc_store_main, rc_store_diff, rc_store_fuzz), (0, 0, 0))
            self.assertEqual(len(observed), 4)
            self.assertTrue(
                all(o[0] == store_diff.resolve(strict=True) for o in observed)
            )

    def test_pin_cargo_rustc_and_rustup_stage_against_post_validation_tamper(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as tmpd:
            root = Path(tmpd).resolve()
            caller_cwd = root / "caller"
            caller_cwd.mkdir()
            proxy_dir = root / "rustup-proxy-bin"
            tc_bin = root / "writable-tc" / "bin"
            tc_nested_lib = root / "writable-tc" / "lib" / "rustlib" / "host" / "lib"
            clean_home = root / "clean-home"
            trusted_cc_dir = root / "trusted-cc"
            for d in (
                proxy_dir,
                tc_bin,
                tc_nested_lib,
                clean_home / ".rustup",
                trusted_cc_dir,
            ):
                d.mkdir(parents=True)
            top_so = root / "writable-tc" / "lib" / "libLLVM-test.so"
            top_so.write_bytes(b"llvm-orig")
            nested_rlib = tc_nested_lib / "libstd.rlib"
            nested_rlib.write_bytes(b"std-orig")
            os.symlink("../../../libLLVM-test.so", tc_nested_lib / "libLLVM-test.so")
            (clean_home / ".rustup" / "settings.toml").write_text(
                'version = "12"\n', encoding="utf-8"
            )
            linker = trusted_cc_dir / cmd._LINKER_BIN_NAME
            linker.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            linker.chmod(0o755)

            tc_cargo = tc_bin / "cargo"
            tc_rustc = tc_bin / "rustc"
            tc_cargo.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            tc_rustc.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            tc_cargo.chmod(0o755)
            tc_rustc.chmod(0o755)

            rustup_bin = proxy_dir / "rustup"
            rustup_ran_paths: list[str] = []
            # Self-overwrite writable `rustup` on `which rustc` AND tamper
            # pre-exec via a callback below to prove `rustup` is staged first.
            rustup_bin.write_text(
                "#!/bin/sh\nset -eu\n"
                'printf \'%s\\n\' "$0" >> "' + str(root / "rustup-0.log") + '"\n'
                'if [ "${1:-}" = "which" ] && [ "${2:-}" = "cargo" ]; then\n'
                f'  printf \'%s\\n\' "{tc_cargo}"\n'
                "  exit 0\n"
                "fi\n"
                'if [ "${1:-}" = "which" ] && [ "${2:-}" = "rustc" ]; then\n'
                f'  printf \'#!/bin/sh\\necho TAMPERED_RUSTUP >&2\\nexit 99\\n\' > "{rustup_bin}"\n'
                f'  printf \'%s\\n\' "{tc_rustc}"\n'
                "  exit 0\n"
                "fi\n"
                "exit 1\n",
                encoding="utf-8",
            )
            rustup_bin.chmod(0o755)
            os.symlink("rustup", proxy_dir / "cargo")
            os.symlink("rustup", proxy_dir / "rustc")

            with (
                ExitStack() as st,
                _patch_clean_tool_env(
                    {
                        "HOME": str(clean_home),
                        "PATH": str(proxy_dir),
                        "TMPDIR": str(root),
                    }
                ),
            ):
                child_env = cmd._build_child_env(caller_cwd)
                cargo_str, _ = cmd._pin_cargo_rustc_env(
                    child_env,
                    caller_cwd,
                    str(proxy_dir / "cargo"),
                    exit_stack=st,
                    work_dir=root,
                    trusted_linker_dirs=(trusted_cc_dir,),
                    trusted_linker_symlink_dirs=(),
                    trusted_child_dirs=(),
                )
                staged_cargo = Path(child_env["CARGO"])
                staged_rustc = Path(child_env["RUSTC"])
                self.assertEqual(cargo_str, str(staged_cargo))
                self.assertIn(".anneal-isolated-bins", str(staged_cargo))
                self.assertIn(".anneal-isolated-bins", str(staged_rustc))
                self.assertEqual(staged_cargo.name, "cargo")
                self.assertEqual(staged_rustc.name, "rustc")
                self.assertEqual(stat.S_IMODE(os.lstat(staged_cargo).st_mode), 0o555)
                self.assertEqual(stat.S_IMODE(os.lstat(staged_rustc).st_mode), 0o555)
                self.assertEqual(os.lstat(staged_cargo).st_nlink, 1)
                self.assertEqual(os.lstat(staged_rustc).st_nlink, 1)
                # Overwriting writable `tc_cargo`, `tc_rustc`, and `lib/rustlib`
                # after staging leaves frozen `0o555`/`0o444` staged copies
                # untouched (ensuring `rustc --print sysroot` finds `rustlib`).
                tc_cargo.write_text("#!/bin/sh\nexit 99\n", encoding="utf-8")
                tc_rustc.write_text("#!/bin/sh\nexit 99\n", encoding="utf-8")
                nested_rlib.write_bytes(b"std-tampered")
                top_so.write_bytes(b"llvm-tampered")
                self.assertEqual(staged_cargo.read_text(encoding="utf-8"), "#!/bin/sh\nexit 0\n")
                self.assertEqual(staged_rustc.read_text(encoding="utf-8"), "#!/bin/sh\nexit 0\n")
                staged_lib = Path(child_env["LD_LIBRARY_PATH"])
                # Non-store `rustc` and `lib/` (including `lib/rustlib/`)
                # co-locate under a single immutable sysroot parent directory.
                self.assertEqual(staged_rustc.parent.parent, staged_lib.parent)
                self.assertEqual(
                    stat.S_IMODE(os.lstat(staged_rustc.parent).st_mode), 0o555
                )
                staged_rlib = staged_lib / "rustlib" / "host" / "lib" / "libstd.rlib"
                staged_dedup = staged_lib / "rustlib" / "host" / "lib" / "libLLVM-test.so"
                self.assertEqual(staged_rlib.read_bytes(), b"std-orig")
                self.assertEqual(staged_dedup.read_bytes(), b"llvm-orig")
                self.assertFalse(staged_dedup.is_symlink())
                self.assertEqual(stat.S_IMODE(os.lstat(staged_rlib).st_mode), 0o444)

            rustup_ran_paths = (root / "rustup-0.log").read_text(encoding="utf-8").splitlines()
            self.assertEqual(len(rustup_ran_paths), 2)
            for rp in rustup_ran_paths:
                self.assertNotEqual(rp, str(rustup_bin))
                self.assertIn(".anneal-isolated-bins", rp)
                self.assertEqual(Path(rp).name, "rustup")
            self.assertFalse(staged_cargo.exists())
            self.assertFalse(staged_rustc.exists())

    def test_non_default_rustup_home_read_only_target_and_empty_home_fallback(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as tmpd:
            root = Path(tmpd).resolve()
            caller_cwd = root / "caller"
            caller_cwd.mkdir()
            anneal_dir = root / "anneal"
            anneal_dir.mkdir()
            proxy_dir = root / "rustup-proxy"
            custom_rh = root / "custom-rustup"
            empty_home = root / "empty-home"
            tc_bin = root / "custom-tc" / "bin"
            trusted_cc = root / "trusted-cc"
            for d in (proxy_dir, custom_rh, empty_home, tc_bin, trusted_cc):
                d.mkdir(parents=True)
            (custom_rh / "settings.toml").write_text('version = "12"\n', encoding="utf-8")
            (trusted_cc / cmd._LINKER_BIN_NAME).write_text(
                "#!/bin/sh\nexit 0\n", encoding="utf-8"
            )
            (trusted_cc / cmd._LINKER_BIN_NAME).chmod(0o755)

            tc_cargo = tc_bin / "cargo"
            tc_rustc = tc_bin / "rustc"
            tc_cargo.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            tc_rustc.write_text(
                "#!/bin/sh\necho 'rustc 1.99.0-custom'\n", encoding="utf-8"
            )
            tc_cargo.chmod(0o755)
            tc_rustc.chmod(0o755)

            rustup_bin = proxy_dir / "rustup"
            rustup_bin.write_text(
                "#!/bin/sh\nset -eu\n"
                f'if [ "${{RUSTUP_HOME:-}}" != "{custom_rh}" ] || '
                '[ "${RUSTUP_TOOLCHAIN:-}" != "nightly-custom" ]; then\n'
                "  echo 'no default toolchain' >&2\n"
                "  exit 1\n"
                "fi\n"
                'if [ "${1:-}" = "which" ] && [ "${2:-}" = "cargo" ]; then\n'
                f'  printf \'%s\\n\' "{tc_cargo}"\n'
                "  exit 0\n"
                "fi\n"
                'if [ "${1:-}" = "which" ] && [ "${2:-}" = "rustc" ]; then\n'
                f'  printf \'%s\\n\' "{tc_rustc}"\n'
                "  exit 0\n"
                "fi\n"
                "exit 1\n",
                encoding="utf-8",
            )
            rustup_bin.chmod(0o755)
            os.symlink("rustup", proxy_dir / "cargo")
            os.symlink("rustup", proxy_dir / "rustc")

            # Explicit RUSTUP_HOME + RUSTUP_TOOLCHAIN succeed even when
            # $HOME is empty and has no `.rustup` directory.
            with (
                ExitStack() as st,
                _patch_clean_tool_env(
                    {
                        "HOME": str(empty_home),
                        "RUSTUP_HOME": str(custom_rh),
                        "RUSTUP_TOOLCHAIN": "nightly-custom",
                        "PATH": str(proxy_dir),
                        "TMPDIR": str(root),
                    }
                ),
            ):
                env = cmd._build_child_env(caller_cwd, exit_stack=st)
                self.assertEqual(env["RUSTUP_HOME"], str(custom_rh))
                self.assertEqual(env["RUSTUP_TOOLCHAIN"], "nightly-custom")
                cargo_str, _ = cmd._pin_cargo_rustc_env(
                    env,
                    caller_cwd,
                    str(proxy_dir / "cargo"),
                    exit_stack=st,
                    work_dir=root,
                    trusted_linker_dirs=(trusted_cc,),
                    trusted_linker_symlink_dirs=(),
                    trusted_child_dirs=(),
                )
                self.assertIn(".anneal-isolated-bins", cargo_str)
                env_info = cmd._collect_environment(anneal_dir, caller_cwd=caller_cwd)
                self.assertEqual(env_info["rustc_version"], "rustc 1.99.0-custom")

            # Poisoned RUSTUP_HOME or RUSTUP_TOOLCHAIN still fails closed.
            sym_rh = root / "sym-rustup-home"
            os.symlink(custom_rh, sym_rh)
            with _patch_clean_tool_env({"RUSTUP_HOME": str(sym_rh), "PATH": str(proxy_dir)}):
                with self.assertRaisesRegex(ValueError, "symlink"):
                    cmd._build_child_env(caller_cwd)
            with _patch_clean_tool_env(
                {"RUSTUP_HOME": str(custom_rh), "RUSTUP_TOOLCHAIN": "../evil", "PATH": str(proxy_dir)}
            ):
                with self.assertRaisesRegex(ValueError, "RUSTUP_TOOLCHAIN"):
                    cmd._build_child_env(caller_cwd)

            # Read-only target/ with nlink == 2 Cargo binaries stages into
            # private 0o555 TMPDIR cleanly (never writing target/) and
            # supports concurrent callers without os.replace races.
            ro_target_dbg = anneal_dir / "ro_target" / "debug"
            (ro_target_dbg / "deps").mkdir(parents=True)
            diff_dep = ro_target_dbg / "deps" / "anneal_diff-123"
            cap_dep = ro_target_dbg / "deps" / "anneal_rustc_capture-456"
            diff_bin = ro_target_dbg / "anneal-diff"
            cap_bin = ro_target_dbg / "anneal-rustc-capture"
            diff_payload = json.dumps(_sample_diff_report())
            fuzz_payload = json.dumps(_sample_fuzz_report())
            diff_script = (
                "#!/bin/sh\n"
                'if [ "${1:-}" = "fuzz" ]; then\n'
                f"  printf '%s\\n' '{fuzz_payload}'\n"
                "  exit 0\n"
                "fi\n"
                f"printf '%s\\n' '{diff_payload}'\n"
            )
            diff_dep.write_text(diff_script, encoding="utf-8")
            diff_dep.chmod(0o755)
            cap_dep.write_bytes(b"ro-capture-bytes")
            cap_dep.chmod(0o755)
            os.link(diff_dep, diff_bin)
            os.link(cap_dep, cap_bin)
            os.chmod(ro_target_dbg / "deps", 0o555)
            os.chmod(ro_target_dbg, 0o555)
            os.chmod(anneal_dir / "ro_target", 0o555)
            try:
                # Concurrent resolution and staging of the same nlink == 2
                # binary must not race.
                from concurrent.futures import ThreadPoolExecutor

                with ExitStack() as conc_st:
                    def _stage_one(_i: int) -> Path:
                        v = cmd._resolve_cargo_executable_cli_path(
                            diff_bin, "anneal_diff_bin", base_dir=root
                        )
                        return cmd._stage_verified_executable(
                            v,
                            "anneal-diff",
                            allow_cargo_deps_hardlink=True,
                            exit_stack=conc_st,
                            base_dir=root,
                            tmp_parent=str(root),
                        )

                    with ThreadPoolExecutor(max_workers=4) as pool:
                        staged_paths = list(pool.map(_stage_one, range(4)))
                    self.assertEqual(len({str(p) for p in staged_paths}), 4)

                # Empty HOME without RUSTUP_HOME causes `rustup which rustc` to
                # exit 1 inside `_collect_environment`; `main()` completes
                # cleanly with `rustc_version == "unknown"` and read-only
                # `target/`.
                out_buf = io.StringIO()
                with (
                    _patch_clean_tool_env(
                        {
                            "HOME": str(empty_home),
                            "PATH": str(proxy_dir),
                            "TMPDIR": str(root),
                        }
                    ),
                    mock.patch.object(
                        cmd,
                        "_git_metadata",
                        return_value=("main", "a" * 40, 1_780_000_000),
                    ),
                    redirect_stdout(out_buf),
                ):
                    rc = cmd.main(
                        [
                            "--anneal-root",
                            str(anneal_dir),
                            "--anneal-diff-bin",
                            str(diff_bin),
                            "--capture-bin",
                            str(cap_bin),
                            "--allow-unknown-git",
                        ]
                    )
                self.assertEqual(rc, 0)
                parsed_out = json.loads(out_buf.getvalue())
                self.assertEqual(
                    parsed_out["environment_profile"]["rustc_version"],
                    "unknown",
                )
            finally:
                os.chmod(anneal_dir / "ro_target", 0o755)
                os.chmod(ro_target_dbg, 0o755)
                os.chmod(ro_target_dbg / "deps", 0o755)

    def test_staging_resists_parent_dir_rename_and_multi_hop_lib_symlinks(
        self,
    ) -> None:
        if os.name != "posix" or not sys.platform.startswith("linux"):
            self.skipTest("Linux /proc/self/fd staging test")
        with tempfile.TemporaryDirectory() as tmpd:
            root = Path(tmpd).resolve()
            caller_cwd = root / "caller"
            anneal_dir = root / "anneal"
            rename_parent = root / "rename-parent"
            active_tmp = rename_parent / "active"
            moved_tmp = rename_parent / "moved"
            tc_dir = root / "tc"
            tc_bin = tc_dir / "bin"
            tc_lib = tc_dir / "lib"
            outside_dir = root / "outside"
            trusted_cc = root / "trusted-cc"
            clean_home = root / "home"
            for d in (
                caller_cwd,
                anneal_dir,
                active_tmp,
                tc_bin,
                tc_lib,
                outside_dir,
                trusted_cc,
                clean_home,
            ):
                d.mkdir(parents=True)

            (trusted_cc / cmd._LINKER_BIN_NAME).write_text(
                "#!/bin/sh\nexit 0\n", encoding="utf-8"
            )
            (trusted_cc / cmd._LINKER_BIN_NAME).chmod(0o755)

            # 1. Confined 2-hop relative symlink inside lib/ materializes
            #    cleanly, while 2-hop symlink escape fails closed.
            (tc_lib / "libc++abi.so.1.0").write_bytes(b"real-cxxabi")
            os.symlink("libc++abi.so.1.0", tc_lib / "libc++abi.so.1")
            os.symlink("libc++abi.so.1", tc_lib / "libc++abi.so")
            with ExitStack() as lib_st:
                staged_lib = cmd._materialize_immutable_top_level_lib(
                    tc_lib,
                    "test sysroot lib",
                    base_dir=root,
                    exit_stack=lib_st,
                    tmp_parent=str(active_tmp),
                )
                self.assertTrue(str(staged_lib).startswith("/proc/self/fd/"))
                self.assertEqual(
                    (staged_lib / "libc++abi.so").read_bytes(), b"real-cxxabi"
                )

            (outside_dir / "evil.so").write_bytes(b"evil")
            os.symlink("../../outside/evil.so", tc_lib / "hop2.so")
            os.symlink("hop2.so", tc_lib / "hop1.so")
            with ExitStack() as esc_st:
                with self.assertRaisesRegex(ValueError, "escaped"):
                    cmd._materialize_immutable_top_level_lib(
                        tc_lib,
                        "test sysroot lib",
                        base_dir=root,
                        exit_stack=esc_st,
                        tmp_parent=str(active_tmp),
                    )
            (tc_lib / "hop1.so").unlink()
            (tc_lib / "hop2.so").unlink()

            # 2. Parent-directory rename + path hijack under active_tmp cannot
            #    subvert pinned `/proc/self/fd/<fd>` staging handles passed to
            #    subprocesses (`_run_subcommand_process_group`, `_tool_version`,
            #    and `main()`).
            tc_cargo = tc_bin / "cargo"
            tc_rustc = tc_bin / "rustc"
            tc_cargo.write_text("#!/bin/sh\necho 'cargo-genuine'\n", encoding="utf-8")
            tc_rustc.write_text("#!/bin/sh\necho 'rustc 1.99.0-pinned'\n", encoding="utf-8")
            tc_cargo.chmod(0o755)
            tc_rustc.chmod(0o755)

            diff_json = root / "diff.json"
            fuzz_json = root / "fuzz.json"
            diff_json.write_text(json.dumps(_sample_diff_report()), encoding="utf-8")
            fuzz_json.write_text(json.dumps(_sample_fuzz_report()), encoding="utf-8")
            diff_bin = root / "anneal-diff"
            # On first call (`run`), move active_tmp aside and plant a TROJAN
            # binary at the vacated disk path inside the newly created
            # active_tmp so the subsequent `fuzz` call proves `/proc/self/fd`
            # stays bound to the genuine staged inode!
            diff_bin.write_text(
                "#!/bin/sh\nset -eu\n"
                'if [ "${1:-}" = "run" ]; then\n'
                '  real_dir=$(cd "$(dirname "$0")/.." && pwd -P)\n'
                '  stage_name=$(basename "$real_dir")\n'
                f'  mv "{active_tmp}" "{moved_tmp}"\n'
                f'  mkdir -p "{active_tmp}/$stage_name/.anneal-isolated-bins"\n'
                f'  printf \'#!/bin/sh\\necho TROJAN >&2\\nexit 99\\n\' > "{active_tmp}/$stage_name/.anneal-isolated-bins/anneal-diff"\n'
                f'  chmod +x "{active_tmp}/$stage_name/.anneal-isolated-bins/anneal-diff"\n'
                f'  cat "{diff_json}"\n'
                "  exit 0\n"
                "fi\n"
                f'cat "{fuzz_json}"\n',
                encoding="utf-8",
            )
            diff_bin.chmod(0o755)

            with (
                ExitStack() as st,
                _patch_clean_tool_env(
                    {
                        "HOME": str(clean_home),
                        "CARGO": str(tc_cargo),
                        "RUSTC": str(tc_rustc),
                        "TMPDIR": str(active_tmp),
                    }
                ),
            ):
                child_env = cmd._build_child_env(caller_cwd, exit_stack=st)
                pinned_cargo, _ = cmd._pin_cargo_rustc_env(
                    child_env,
                    caller_cwd,
                    str(tc_cargo),
                    exit_stack=st,
                    work_dir=root,
                    trusted_linker_dirs=(trusted_cc,),
                    trusted_linker_symlink_dirs=(),
                    trusted_child_dirs=(),
                )
                pinned_rustc = Path(child_env["RUSTC"])
                self.assertTrue(pinned_cargo.startswith("/proc/self/fd/"))
                self.assertTrue(str(pinned_rustc).startswith("/proc/self/fd/"))
                rustc_disk_root = Path(os.path.realpath(str(pinned_rustc))).parent.parent
                self.assertTrue(rustc_disk_root.is_relative_to(active_tmp))
                os.rename(active_tmp, moved_tmp)
                try:
                    hijacked_rustc = rustc_disk_root / ".anneal-isolated-bins" / "rustc"
                    hijacked_rustc.parent.mkdir(parents=True)
                    hijacked_rustc.write_text(
                        "#!/bin/sh\necho TROJAN_RUSTC >&2\nexit 99\n",
                        encoding="utf-8",
                    )
                    hijacked_rustc.chmod(0o755)
                    self.assertEqual(
                        cmd._tool_version(
                            [str(pinned_rustc), "--version"],
                            extra_lib_dir=Path(child_env["LD_LIBRARY_PATH"]),
                        ),
                        "rustc 1.99.0-pinned",
                    )
                    sub_res = cmd._run_subcommand_process_group(
                        [pinned_cargo],
                        cwd=root,
                        env=child_env,
                        timeout_secs=10.0,
                    )
                    self.assertEqual(sub_res.returncode, 0)
                    self.assertEqual(sub_res.stdout.strip(), "cargo-genuine")
                finally:
                    shutil.rmtree(active_tmp, ignore_errors=True)
                    os.rename(moved_tmp, active_tmp)

            # End-to-end `main()` check across `run` -> rename -> `fuzz`.
            out_buf = io.StringIO()
            try:
                with (
                    _patch_clean_tool_env({"HOME": str(clean_home), "TMPDIR": str(active_tmp)}),
                    mock.patch.object(
                        cmd,
                        "_git_metadata",
                        return_value=("main", "a" * 40, 1_780_000_000),
                    ),
                    mock.patch.object(
                        cmd,
                        "_collect_environment",
                        return_value={"os": "linux", "arch": "x86_64"},
                    ),
                    redirect_stdout(out_buf),
                ):
                    rc = cmd.main(
                        [
                            "--anneal-root",
                            str(anneal_dir),
                            "--anneal-diff-bin",
                            str(diff_bin),
                        ]
                    )
            finally:
                if moved_tmp.exists():
                    shutil.rmtree(active_tmp, ignore_errors=True)
                    os.rename(moved_tmp, active_tmp)
            self.assertEqual(rc, 0)
            parsed = json.loads(out_buf.getvalue())
            self.assertEqual(parsed["schema"], "anneal-semantic-detail/v1")
            self.assertEqual(
                parsed["evidence_blocks"]["differential_oracle"]["compared_count"],
                3,
            )
            self.assertEqual(
                parsed["evidence_blocks"]["differential_fuzz"]["admitted_cases"],
                23,
            )

    def test_dirfd_open_pins_executables_and_rustup_settings_across_mutations(
        self,
    ) -> None:
        if os.name != "posix":
            self.skipTest("POSIX dirfd handle pinning test")
        with tempfile.TemporaryDirectory() as tmpd:
            root = Path(tmpd).resolve()
            src_dir = root / "src"
            moved_dir = root / "src-moved"
            src_dir.mkdir()
            tool_bin = src_dir / "tool"
            tool_bin.write_text("#!/bin/sh\necho GENUINE\n", encoding="utf-8")
            tool_bin.chmod(0o755)
            # Retained dirfd + file descriptor keeps staging bound to original
            # bytes even if parent directory is renamed and replaced.
            with ExitStack() as st:
                opened = cmd._open_verified_executable_via_dirfd(
                    tool_bin,
                    root,
                    reject_hardlinks=True,
                    label="test tool",
                    exit_stack=st,
                )
                os.rename(src_dir, moved_dir)
                src_dir.mkdir()
                tool_bin.write_text("#!/bin/sh\necho TROJAN\n", encoding="utf-8")
                tool_bin.chmod(0o755)
                staged = cmd._stage_verified_executable(
                    opened.path,
                    "tool",
                    allow_cargo_deps_hardlink=False,
                    exit_stack=st,
                    base_dir=root,
                    tmp_parent=str(root),
                    preserve_bin_name=True,
                    preopened=opened,
                )
                self.assertIn("GENUINE", staged.read_text(encoding="utf-8"))
                self.assertNotIn("TROJAN", staged.read_text(encoding="utf-8"))

            # `_pin_rustup_settings` snapshots `settings.toml` once via dirfd
            # to derive `RUSTUP_TOOLCHAIN` from `[overrides]` or
            # `default_toolchain`, and freezes `RUSTUP_HOME` when unconfigured.
            ws_dir = root / "ws"
            ws_dir.mkdir()
            rh = root / "rustup-home"
            rh.mkdir()
            settings = rh / "settings.toml"
            settings.write_text(
                'default_toolchain = "stable"\n'
                "[overrides]\n"
                f'"{ws_dir}" = "nightly-2026-05-31"\n',
                encoding="utf-8",
            )
            with ExitStack() as st:
                probe_env = {"RUSTUP_HOME": str(rh), "TMPDIR": str(root)}
                cmd._pin_rustup_settings(probe_env, root, ws_dir, st)
                self.assertEqual(probe_env["RUSTUP_TOOLCHAIN"], "nightly-2026-05-31")

            # Removing `[overrides]` falls back to `default_toolchain`.
            settings.write_text('default_toolchain = "nightly-default"\n', encoding="utf-8")
            with ExitStack() as st:
                probe_env = {"RUSTUP_HOME": str(rh), "TMPDIR": str(root)}
                cmd._pin_rustup_settings(probe_env, root, ws_dir, st)
                self.assertEqual(probe_env["RUSTUP_TOOLCHAIN"], "nightly-default")

            # Unconfigured `settings.toml` stages a private `0o555`/`0o444`
            # `RUSTUP_HOME` insulated from post-snapshotting mutations.
            settings.write_text('version = "12"\n', encoding="utf-8")
            with ExitStack() as st:
                probe_env = {"RUSTUP_HOME": str(rh), "TMPDIR": str(root)}
                cmd._pin_rustup_settings(probe_env, root, ws_dir, st)
                self.assertNotIn("RUSTUP_TOOLCHAIN", probe_env)
                frozen_rh = Path(probe_env["RUSTUP_HOME"])
                self.assertNotEqual(frozen_rh, rh)
                settings.write_text('default_toolchain = "evil"\n', encoding="utf-8")
                self.assertEqual(
                    (frozen_rh / "settings.toml").read_text(encoding="utf-8"),
                    'version = "12"\n',
                )
                self.assertEqual(stat.S_IMODE(os.lstat(frozen_rh / "settings.toml").st_mode), 0o444)

    def test_leg3_source_graph_materialized_immutable_and_rejects_links_and_ambient_cfg(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as tmpd:
            root = Path(tmpd).resolve()
            ws = root / "ws"
            pkg = ws / "tools" / "anneal-mir-eval"
            pkg_src = pkg / "src"
            dep_src = ws / "crates" / "helper" / "src"
            outside = root / "outside"
            clean_bin = root / "bin"
            for d in (pkg_src, dep_src, outside, clean_bin, ws / ".git", ws / "target", pkg / "target"):
                d.mkdir(parents=True)
            (clean_bin / "cargo").write_text("#!/bin/sh\n", encoding="utf-8")
            (clean_bin / "rustc").write_text("#!/bin/sh\n", encoding="utf-8")
            (outside / "secret.txt").write_text("secret\n", encoding="utf-8")
            (ws / ".git" / "HEAD").write_text("ref: refs/heads/main\n", encoding="utf-8")
            (ws / "Cargo.toml").write_text(
                '[workspace]\nmembers = ["tools/anneal-mir-eval"]\n',
                encoding="utf-8",
            )
            (ws / "Cargo.lock").write_text("# lock v1\n", encoding="utf-8")
            (ws / "crates" / "helper" / "Cargo.toml").write_text(
                '[package]\nname = "helper"\nversion = "0.1.0"\n',
                encoding="utf-8",
            )
            (dep_src / "lib.rs").write_text("pub fn helper() -> u32 { 1 }\n", encoding="utf-8")
            mir_manifest = pkg / "Cargo.toml"
            mir_manifest.write_text(
                '[package]\nname = "anneal-mir-eval"\nversion = "0.1.0"\n'
                'build = "build.rs"\n'
                '[dependencies]\nhelper = { path = "../../crates/helper" }\n',
                encoding="utf-8",
            )
            (pkg / "build.rs").write_text("fn main() {}\n", encoding="utf-8")
            (pkg_src / "main.rs").write_text("fn main() {}\n", encoding="utf-8")

            observed: list[tuple[Path, str, str, str, bool]] = []

            def _mock_cargo(args: list[str], **kwargs: Any) -> mock.Mock:
                cwd = Path(kwargs["cwd"])
                mp = Path(args[args.index("--manifest-path") + 1])
                if args[1] == "test":
                    observed.append(
                        (
                            cwd,
                            mp.read_text(encoding="utf-8"),
                            (cwd / "build.rs").read_text(encoding="utf-8"),
                            (cwd.parent.parent / "crates" / "helper" / "src" / "lib.rs").read_text(encoding="utf-8"),
                            (cwd.parent.parent / ".git").exists(),
                        )
                    )
                    # Mutating original workspace files after staging cannot
                    # alter what Cargo sees during `test` or `build`.
                    (pkg / "build.rs").write_text("fn main() { panic!() }\n", encoding="utf-8")
                    (dep_src / "lib.rs").write_text("pub fn helper() -> u32 { 99 }\n", encoding="utf-8")
                    return mock.Mock(returncode=0, stdout="", stderr="")
                priv_td = Path(args[args.index("--target-dir") + 1])
                built_exe = priv_td / "debug" / "anneal-mir-eval"
                built_exe.parent.mkdir(parents=True, exist_ok=True)
                built_exe.write_bytes(b"mir-eval-staged-src")
                art = json.dumps(
                    {
                        "reason": "compiler-artifact",
                        "manifest_path": str(mp),
                        "target": {"name": "anneal-mir-eval", "kind": ["bin"]},
                        "executable": str(built_exe),
                    }
                )
                return mock.Mock(returncode=0, stdout=art + "\n", stderr="")

            with (
                _patch_clean_tool_env({"PATH": str(clean_bin), "TMPDIR": str(root)}),
                _patch_subprocess_exec(side_effect=_mock_cargo),
            ):
                status, staged_exe = cmd.maybe_run_mir_eval_manifest(mir_manifest)
            self.assertTrue(status["passed"], status)
            assert staged_exe is not None
            self.assertEqual(len(observed), 1)
            staged_cwd, m_txt, build_txt, dep_txt, has_git = observed[0]
            self.assertNotEqual(staged_cwd, pkg)
            self.assertIn("helper", m_txt)
            self.assertEqual(build_txt, "fn main() {}\n")
            self.assertEqual(dep_txt, "pub fn helper() -> u32 { 1 }\n")
            self.assertFalse(has_git)

            # Symlinks and hardlinks inside `build.rs` or `path` dependencies
            # fail closed pre-Cargo before any subprocess executes.
            (dep_src / "lib.rs").unlink()
            os.link(outside / "secret.txt", dep_src / "lib.rs")
            with (
                _patch_clean_tool_env({"PATH": str(clean_bin), "TMPDIR": str(root)}),
                _patch_subprocess_exec() as no_exec,
            ):
                with self.assertRaisesRegex(ValueError, "hardlink"):
                    cmd.maybe_run_mir_eval_manifest(mir_manifest)
                no_exec.assert_not_called()

            (dep_src / "lib.rs").unlink()
            (dep_src / "lib.rs").write_text("pub fn helper() -> u32 { 1 }\n", encoding="utf-8")
            (pkg / "build.rs").unlink()
            os.symlink(outside / "secret.txt", pkg / "build.rs")
            with (
                _patch_clean_tool_env({"PATH": str(clean_bin), "TMPDIR": str(root)}),
                _patch_subprocess_exec() as no_exec,
            ):
                with self.assertRaisesRegex(ValueError, "symlink"):
                    cmd.maybe_run_mir_eval_manifest(mir_manifest)
                no_exec.assert_not_called()

            # `[replace]` dependency paths in Cargo.toml fail closed on unsafe
            # non-store absolute paths and symlinks/hardlinks pre-Cargo, and
            # stage relative `[replace]` dependencies into `/proc/self/fd`.
            rep_src = ws / "crates" / "rep_dep" / "src"
            rep_src.mkdir(parents=True)
            (ws / "crates" / "rep_dep" / "Cargo.toml").write_text(
                '[package]\nname = "rep_dep"\nversion = "0.1.0"\n',
                encoding="utf-8",
            )
            (rep_src / "lib.rs").write_text("pub fn rep() {}\n", encoding="utf-8")
            (ws / "Cargo.toml").write_text(
                '[workspace]\nmembers = ["tools/anneal-mir-eval"]\n'
                f'[replace]\n"rep_dep:0.1.0" = {{ path = "{outside / "rep"}" }}\n',
                encoding="utf-8",
            )
            (pkg / "build.rs").unlink()
            (pkg / "build.rs").write_text("fn main() {}\n", encoding="utf-8")
            with (
                _patch_clean_tool_env({"PATH": str(clean_bin), "TMPDIR": str(root)}),
                _patch_subprocess_exec() as no_exec,
            ):
                with self.assertRaisesRegex(ValueError, "outside staged source tree"):
                    cmd.maybe_run_mir_eval_manifest(mir_manifest)
                no_exec.assert_not_called()

            (ws / "Cargo.toml").write_text(
                '[workspace]\nmembers = ["tools/anneal-mir-eval"]\n'
                '[replace]\n"rep_dep:0.1.0" = { path = "crates/rep_dep" }\n',
                encoding="utf-8",
            )
            rep_seen: list[str] = []

            def _mock_rep_cargo(args: list[str], **kwargs: Any) -> mock.Mock:
                cwd = Path(kwargs["cwd"])
                mp = Path(args[args.index("--manifest-path") + 1])
                if args[1] == "test":
                    rep_seen.append(
                        (cwd.parent.parent / "crates" / "rep_dep" / "src" / "lib.rs").read_text(encoding="utf-8")
                    )
                    return mock.Mock(returncode=0, stdout="", stderr="")
                priv_td = Path(args[args.index("--target-dir") + 1])
                built_exe = priv_td / "debug" / "anneal-mir-eval"
                built_exe.parent.mkdir(parents=True, exist_ok=True)
                built_exe.write_bytes(b"rep-staged")
                art = json.dumps(
                    {
                        "reason": "compiler-artifact",
                        "manifest_path": str(mp),
                        "target": {"name": "anneal-mir-eval", "kind": ["bin"]},
                        "executable": str(built_exe),
                    }
                )
                return mock.Mock(returncode=0, stdout=art + "\n", stderr="")

            with (
                _patch_clean_tool_env({"PATH": str(clean_bin), "TMPDIR": str(root)}),
                _patch_subprocess_exec(side_effect=_mock_rep_cargo),
            ):
                rep_status, _ = cmd.maybe_run_mir_eval_manifest(mir_manifest)
            self.assertTrue(rep_status["passed"], rep_status)
            self.assertEqual(rep_seen, ["pub fn rep() {}\n"])

            os.symlink(outside / "secret.txt", rep_src / "evil.rs")
            with (
                _patch_clean_tool_env({"PATH": str(clean_bin), "TMPDIR": str(root)}),
                _patch_subprocess_exec() as no_exec,
            ):
                with self.assertRaisesRegex(ValueError, "symlink"):
                    cmd.maybe_run_mir_eval_manifest(mir_manifest)
                no_exec.assert_not_called()

    def test_explicit_mir_eval_bin_pinned_once_across_run_and_fuzz(self) -> None:
        with tempfile.TemporaryDirectory() as tmpd:
            root = Path(tmpd).resolve()
            anneal_dir = root / "anneal"
            anneal_dir.mkdir()
            diff_json = root / "diff.json"
            fuzz_json = root / "fuzz.json"
            diff_json.write_text(
                json.dumps(_with_mir_eval_leg(_sample_diff_report())),
                encoding="utf-8",
            )
            fuzz_json.write_text(
                json.dumps(_with_mir_eval_leg(_sample_fuzz_report())),
                encoding="utf-8",
            )
            mir_eval_bin = root / "mutable-anneal-mir-eval"
            mir_eval_bin.write_bytes(b"genuine-mir-eval-v1")
            mir_eval_bin.chmod(0o755)
            observed_me: list[tuple[str, bytes, int, int, int]] = []

            def _tampering_exec(args: list[str], **_kwargs: Any) -> mock.Mock:
                me_path = Path(args[args.index("--mir-eval-bin") + 1])
                me_st = os.lstat(me_path)
                observed_me.append(
                    (
                        str(me_path),
                        me_path.read_bytes(),
                        stat.S_IMODE(me_st.st_mode),
                        stat.S_IMODE(os.lstat(me_path.parent).st_mode),
                        me_st.st_nlink,
                    )
                )
                if "run" in args:
                    # Overwrite original `--mir-eval-bin` before `fuzz` runs;
                    # `main()` must feed the identical immutable staged copy.
                    mir_eval_bin.write_bytes(b"TAMPERED-MIR-EVAL")
                    return mock.Mock(
                        returncode=0,
                        stdout=diff_json.read_text(encoding="utf-8"),
                        stderr="",
                    )
                return mock.Mock(
                    returncode=0,
                    stdout=fuzz_json.read_text(encoding="utf-8"),
                    stderr="",
                )

            out_buf = io.StringIO()
            with (
                _patch_clean_tool_env({"TMPDIR": str(root)}),
                mock.patch.object(
                    cmd,
                    "_git_metadata",
                    return_value=("main", "a" * 40, 1_780_000_000),
                ),
                mock.patch.object(
                    cmd,
                    "_collect_environment",
                    return_value={"os": "linux", "arch": "x86_64"},
                ),
                mock.patch("builtins.print"),
                _patch_subprocess_exec(side_effect=_tampering_exec),
            ):
                rc = cmd.main(
                    [
                        "--anneal-root",
                        str(anneal_dir),
                        "--anneal-diff-bin",
                        str(diff_json),
                        "--mir-eval-bin",
                        str(mir_eval_bin),
                        "--allow-unknown-git",
                    ]
                )
            self.assertEqual(rc, 0)
            self.assertEqual(len(observed_me), 2)
            self.assertEqual(observed_me[0][0], observed_me[1][0])
            self.assertIn(".anneal-isolated-bins", observed_me[0][0])
            if os.name == "posix" and sys.platform.startswith("linux"):
                self.assertTrue(observed_me[0][0].startswith("/proc/self/fd/"))
            for p_str, data, mode, dir_mode, nlink in observed_me:
                self.assertEqual(data, b"genuine-mir-eval-v1")
                self.assertEqual(mode, 0o555)
                self.assertEqual(dir_mode, 0o555)
                self.assertEqual(nlink, 1)
                self.assertFalse(Path(p_str).exists())

    def test_mir_eval_manifest_pins_staged_evaluator_against_tmpdir_rename(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as tmpd:
            root = Path(tmpd).resolve()
            anneal_dir = root / "anneal"
            eval_dir = root / "eval"
            eval_src = eval_dir / "src"
            clean_bin = root / "clean-bin"
            trusted_cc = root / "trusted-cc"
            tmpdir_root = root / "shared-tmp"
            for d in (
                anneal_dir,
                eval_src,
                clean_bin,
                trusted_cc,
                tmpdir_root,
            ):
                d.mkdir(parents=True)

            manifest = eval_dir / "Cargo.toml"
            manifest.write_text(
                '[package]\nname = "anneal-mir-eval"\nversion = "0.1.0"\n',
                encoding="utf-8",
            )
            (eval_src / "main.rs").write_text("fn main() {}\n", encoding="utf-8")

            cargo_bin = clean_bin / "cargo"
            rustc_bin = clean_bin / "rustc"
            linker_bin = trusted_cc / cmd._LINKER_BIN_NAME
            for tool, body in (
                (cargo_bin, "#!/bin/sh\nexit 0\n"),
                (rustc_bin, "#!/bin/sh\nexit 0\n"),
                (linker_bin, "#!/bin/sh\nexit 0\n"),
            ):
                tool.write_text(body, encoding="utf-8")
                tool.chmod(0o755)

            fake_diff_bin = root / "anneal-diff"
            fake_diff_bin.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            fake_diff_bin.chmod(0o755)
            diff_payload = json.dumps(_with_mir_eval_leg(_sample_diff_report()))
            fuzz_payload = json.dumps(_with_mir_eval_leg(_sample_fuzz_report()))

            observed_me: list[tuple[str, bytes, int, int, int]] = []
            renamed_backing: list[Path] = []

            def _mock_exec(args: list[str], **_kwargs: Any) -> mock.Mock:
                prog = Path(args[0]).name
                if prog == "cargo":
                    if "test" in args:
                        return mock.Mock(returncode=0, stdout="", stderr="")
                    priv_td = Path(args[args.index("--target-dir") + 1])
                    built_exe = priv_td / "debug" / "anneal-mir-eval"
                    built_exe.parent.mkdir(parents=True, exist_ok=True)
                    built_exe.write_bytes(b"genuine-built-mir-eval-v1")
                    built_exe.chmod(0o755)
                    mp = args[args.index("--manifest-path") + 1]
                    art = json.dumps(
                        {
                            "reason": "compiler-artifact",
                            "manifest_path": mp,
                            "target": {"name": "anneal-mir-eval", "kind": ["bin"]},
                            "profile": {"test": False},
                            "executable": str(built_exe),
                        }
                    )
                    return mock.Mock(returncode=0, stdout=art + "\n", stderr="")

                me_path = Path(args[args.index("--mir-eval-bin") + 1])
                me_st = os.lstat(me_path)
                observed_me.append(
                    (
                        str(me_path),
                        me_path.read_bytes(),
                        stat.S_IMODE(me_st.st_mode),
                        stat.S_IMODE(os.lstat(me_path.parent).st_mode),
                        me_st.st_nlink,
                    )
                )
                if "run" in args:
                    # Simulate a shared-TMPDIR attacker renaming every stage
                    # directory on disk and replacing the path with tampered
                    # bytes between `anneal-diff run` and `anneal-diff fuzz`.
                    for entry in list(tmpdir_root.iterdir()):
                        if entry.name.startswith("anneal-stage-anneal-mir-eval-"):
                            moved = tmpdir_root / f"moved-{entry.name}"
                            os.rename(entry, moved)
                            renamed_backing.append(moved)
                            attacker_iso = entry / ".anneal-isolated-bins"
                            attacker_iso.mkdir(parents=True)
                            (attacker_iso / me_path.name).write_bytes(
                                b"ATTACKER-SWAPPED-EVAL"
                            )
                    return mock.Mock(
                        returncode=0, stdout=diff_payload, stderr=""
                    )
                return mock.Mock(returncode=0, stdout=fuzz_payload, stderr="")

            with (
                _patch_clean_tool_env(
                    {
                        "PATH": f"{clean_bin}{os.pathsep}{trusted_cc}",
                        "TMPDIR": str(tmpdir_root),
                    }
                ),
                mock.patch.object(
                    cmd,
                    "_git_metadata",
                    return_value=("main", "b" * 40, 1_780_000_000),
                ),
                mock.patch.object(
                    cmd,
                    "_collect_environment",
                    return_value={"os": "linux", "arch": "x86_64"},
                ),
                mock.patch("builtins.print"),
                _patch_subprocess_exec(side_effect=_mock_exec),
            ):
                rc = cmd.main(
                    [
                        "--anneal-root",
                        str(anneal_dir),
                        "--anneal-diff-bin",
                        str(fake_diff_bin),
                        "--mir-eval-manifest",
                        str(manifest),
                        "--allow-unknown-git",
                    ]
                )
            for moved in renamed_backing:
                cmd._restore_dir_write_perms_top_down(moved)
            self.assertEqual(rc, 0)
            self.assertEqual(len(observed_me), 2)
            self.assertEqual(observed_me[0][0], observed_me[1][0])
            if os.name == "posix" and sys.platform.startswith("linux"):
                self.assertEqual(len(renamed_backing), 1)
                self.assertTrue(observed_me[0][0].startswith("/proc/self/fd/"))
            for p_str, data, mode, dir_mode, nlink in observed_me:
                self.assertEqual(data, b"genuine-built-mir-eval-v1")
                self.assertEqual(mode, 0o555)
                self.assertEqual(dir_mode, 0o555)
                self.assertEqual(nlink, 1)
                self.assertFalse(Path(p_str).exists())

            unpinned = root / "unpinned-eval"
            unpinned.write_bytes(b"unpinned")
            unpinned.chmod(0o755)
            if sys.platform.startswith("linux"):
                with self.assertRaisesRegex(
                    ValueError, "missing live fd handle"
                ):
                    cmd.run_anneal_diff(
                        anneal_root=anneal_dir,
                        manifest=None,
                        capture_bin=None,
                        mir_eval_bin=unpinned,
                        cache_root=None,
                        self_check_oracle=False,
                        anneal_diff_bin=fake_diff_bin,
                        _mir_eval_pre_staged=True,
                    )
            with self.assertRaisesRegex(ValueError, "staging_exit_stack"):
                cmd.maybe_run_mir_eval_manifest(
                    manifest, staging_dir=tmpdir_root
                )

    def test_capture_bin_and_env_staged_immutable_against_races(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as tmpd:
            root = Path(tmpd).resolve()
            anneal_dir = root / "anneal"
            eval_dir = root / "eval"
            eval_src = eval_dir / "src"
            clean_bin = root / "clean-bin"
            trusted_cc = root / "trusted-cc"
            tmpdir_root = root / "shared-tmp"
            deps_dir = root / "target" / "debug" / "deps"
            for d in (
                anneal_dir,
                eval_src,
                clean_bin,
                trusted_cc,
                tmpdir_root,
                deps_dir,
            ):
                d.mkdir(parents=True)

            manifest = eval_dir / "Cargo.toml"
            manifest.write_text(
                '[package]\nname = "anneal-mir-eval"\nversion = "0.1.0"\n',
                encoding="utf-8",
            )
            (eval_src / "main.rs").write_text("fn main() {}\n", encoding="utf-8")
            for tool, body in (
                (clean_bin / "cargo", "#!/bin/sh\nexit 0\n"),
                (clean_bin / "rustc", "#!/bin/sh\nexit 0\n"),
                (trusted_cc / cmd._LINKER_BIN_NAME, "#!/bin/sh\nexit 0\n"),
            ):
                tool.write_text(body, encoding="utf-8")
                tool.chmod(0o755)

            cap_cli = root / "mutable-cap-cli"
            cap_cli.write_bytes(b"GENUINE-CAPTURE-CLI-V1")
            cap_cli.chmod(0o755)
            cap_env = root / "mutable-cap-env"
            cap_env.write_bytes(b"GENUINE-CAPTURE-ENV-V1")
            cap_env.chmod(0o755)

            fake_diff_bin = root / "anneal-diff"
            fake_diff_bin.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            fake_diff_bin.chmod(0o755)
            diff_payload = json.dumps(_with_mir_eval_leg(_sample_diff_report()))
            fuzz_payload = json.dumps(_with_mir_eval_leg(_sample_fuzz_report()))

            observed: list[tuple[str, bytes, str, bytes, int, int]] = []
            renamed_backing: list[Path] = []

            def _mock_exec(args: list[str], **kwargs: Any) -> mock.Mock:
                prog = Path(args[0]).name
                if prog == "cargo":
                    # Overwrite writable host binaries during manifest build:
                    # pre-staged copies must already be isolated and frozen.
                    cap_cli.write_bytes(b"TAMPERED-CLI-DURING-BUILD")
                    cap_env.write_bytes(b"TAMPERED-ENV-DURING-BUILD")
                    if "test" in args:
                        return mock.Mock(returncode=0, stdout="", stderr="")
                    priv_td = Path(args[args.index("--target-dir") + 1])
                    built_exe = priv_td / "debug" / "anneal-mir-eval"
                    built_exe.parent.mkdir(parents=True, exist_ok=True)
                    built_exe.write_bytes(b"genuine-eval")
                    built_exe.chmod(0o755)
                    mp = args[args.index("--manifest-path") + 1]
                    art = json.dumps(
                        {
                            "reason": "compiler-artifact",
                            "manifest_path": mp,
                            "target": {"name": "anneal-mir-eval", "kind": ["bin"]},
                            "profile": {"test": False},
                            "executable": str(built_exe),
                        }
                    )
                    return mock.Mock(returncode=0, stdout=art + "\n", stderr="")

                cli_p = Path(args[args.index("--capture-bin") + 1])
                env_p = Path(kwargs["env"]["ANNEAL_CAPTURE"])
                cli_st = os.lstat(cli_p)
                observed.append(
                    (
                        str(cli_p),
                        cli_p.read_bytes(),
                        str(env_p),
                        env_p.read_bytes(),
                        stat.S_IMODE(cli_st.st_mode),
                        cli_st.st_nlink,
                    )
                )
                if "run" in args:
                    for entry in list(tmpdir_root.iterdir()):
                        if entry.name.startswith(
                            "anneal-stage-anneal-rustc-capture-"
                        ):
                            moved = tmpdir_root / f"moved-{entry.name}"
                            os.rename(entry, moved)
                            renamed_backing.append(moved)
                            attacker_iso = entry / ".anneal-isolated-bins"
                            attacker_iso.mkdir(parents=True)
                            for tgt in (cli_p.name, env_p.name):
                                (attacker_iso / tgt).write_bytes(
                                    b"ATTACKER-SWAPPED-CAPTURE"
                                )
                    return mock.Mock(
                        returncode=0, stdout=diff_payload, stderr=""
                    )
                return mock.Mock(returncode=0, stdout=fuzz_payload, stderr="")

            with (
                _patch_clean_tool_env(
                    {
                        "PATH": f"{clean_bin}{os.pathsep}{trusted_cc}",
                        "TMPDIR": str(tmpdir_root),
                        "ANNEAL_CAPTURE": str(cap_env),
                    }
                ),
                mock.patch.object(
                    cmd,
                    "_git_metadata",
                    return_value=("main", "c" * 40, 1_780_000_000),
                ),
                mock.patch.object(
                    cmd,
                    "_collect_environment",
                    return_value={"os": "linux", "arch": "x86_64"},
                ),
                mock.patch("builtins.print"),
                _patch_subprocess_exec(side_effect=_mock_exec),
            ):
                rc = cmd.main(
                    [
                        "--anneal-root",
                        str(anneal_dir),
                        "--anneal-diff-bin",
                        str(fake_diff_bin),
                        "--capture-bin",
                        str(cap_cli),
                        "--mir-eval-manifest",
                        str(manifest),
                        "--allow-unknown-git",
                    ]
                )
            for moved in renamed_backing:
                cmd._restore_dir_write_perms_top_down(moved)
            self.assertEqual(rc, 0)
            self.assertEqual(len(observed), 2)
            self.assertEqual(observed[0][0], observed[1][0])
            self.assertEqual(observed[0][2], observed[1][2])
            if os.name == "posix" and sys.platform.startswith("linux"):
                self.assertEqual(len(renamed_backing), 2)
                self.assertTrue(observed[0][0].startswith("/proc/self/fd/"))
                self.assertTrue(observed[0][2].startswith("/proc/self/fd/"))
            for cli_s, cli_b, env_s, env_b, mode, nlink in observed:
                self.assertIn(".anneal-isolated-bins", cli_s)
                self.assertIn(".anneal-isolated-bins", env_s)
                self.assertEqual(cli_b, b"GENUINE-CAPTURE-CLI-V1")
                self.assertEqual(env_b, b"GENUINE-CAPTURE-ENV-V1")
                self.assertEqual(mode, 0o555)
                self.assertEqual(nlink, 1)
                self.assertFalse(Path(cli_s).exists())
                self.assertFalse(Path(env_s).exists())

            dep_cap = deps_dir / "anneal_rustc_capture-999"
            dep_cap.write_bytes(b"CARGO-HARDLINK-CAP")
            dep_cap.chmod(0o755)
            cargo_cap = root / "target" / "debug" / "anneal-rustc-capture"
            os.link(dep_cap, cargo_cap)
            with ExitStack() as st:
                pinned_cap = cmd._maybe_stage_cargo_hardlink_executable(
                    cargo_cap,
                    "anneal-rustc-capture",
                    exit_stack=st,
                    base_dir=root,
                    tmp_parent=str(tmpdir_root),
                )
                if os.name == "posix" and sys.platform.startswith("linux"):
                    self.assertTrue(str(pinned_cap).startswith("/proc/self/fd/"))
                self.assertEqual(pinned_cap.read_bytes(), b"CARGO-HARDLINK-CAP")
            if sys.platform.startswith("linux"):
                with self.assertRaisesRegex(
                    ValueError, "missing live fd handle"
                ):
                    cmd.run_anneal_diff(
                        anneal_root=anneal_dir,
                        manifest=None,
                        capture_bin=cap_cli,
                        mir_eval_bin=None,
                        cache_root=None,
                        self_check_oracle=False,
                        anneal_diff_bin=fake_diff_bin,
                        _capture_pre_staged=True,
                    )

            with _patch_subprocess_exec(
                side_effect=subprocess.TimeoutExpired(cmd=["rustc"], timeout=10)
            ):
                self.assertEqual(cmd._tool_version(["rustc", "--version"]), "unknown")

    def test_workspace_glob_matching_matches_cargo_root_anchored_semantics(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as tmpd:
            root = Path(tmpd).resolve()
            ws = root / "ws"
            outside = root / "outside"
            clean_bin = root / "clean-bin"
            trusted_cc = root / "trusted-cc"
            for d in (
                ws / "crates" / "scratch_ok" / "src",
                ws / "nested" / "crates" / "bar" / "src",
                ws / "a" / "c" / "src",
                ws / "a" / "b" / "c" / "src",
                ws / "tools" / "eval" / "src",
                outside,
                clean_bin,
                trusted_cc,
            ):
                d.mkdir(parents=True)
            (outside / "secret.txt").write_text("SECRET", encoding="utf-8")
            (ws / "Cargo.toml").write_text(
                '[workspace]\nmembers = ["crates/*", "a/**/c", "tools/eval"]\n'
                'exclude = ["scratch*", " excluded_sym ", "crates/nested_sym/"]\n',
                encoding="utf-8",
            )
            os.symlink(outside, ws / "excluded_sym")
            os.symlink(outside, ws / "crates" / "nested_sym")
            self.assertTrue(
                cmd._workspace_pattern_matches_dir_py(
                    ws, " excluded_sym ", ws / "excluded_sym"
                )
            )
            self.assertTrue(
                cmd._workspace_pattern_matches_dir_py(
                    ws, "crates/nested_sym/", ws / "crates" / "nested_sym"
                )
            )
            self.assertFalse(
                cmd._workspace_pattern_matches_dir_py(ws, "/etc", Path("/etc"))
            )
            eval_manifest = ws / "tools" / "eval" / "Cargo.toml"
            eval_manifest.write_text(
                '[package]\nname = "anneal-mir-eval"\nversion = "0.1.0"\n',
                encoding="utf-8",
            )
            (ws / "tools" / "eval" / "src" / "main.rs").write_text(
                "fn main() {}\n", encoding="utf-8"
            )
            for pkg_dir in (
                ws / "crates" / "scratch_ok",
                ws / "nested" / "crates" / "bar",
                ws / "a" / "c",
                ws / "a" / "b" / "c",
            ):
                (pkg_dir / "Cargo.toml").write_text(
                    f'[package]\nname = "{pkg_dir.name}"\nversion = "0.1.0"\n',
                    encoding="utf-8",
                )
                (pkg_dir / "src" / "lib.rs").write_text(
                    "pub fn f() {}\n", encoding="utf-8"
                )

            self.assertFalse(
                cmd._workspace_pattern_matches_dir_py(
                    ws, "scratch*", ws / "crates" / "scratch_ok"
                )
            )
            self.assertFalse(
                cmd._workspace_pattern_matches_dir_py(
                    ws, "crates/*", ws / "nested" / "crates" / "bar"
                )
            )
            self.assertTrue(
                cmd._workspace_pattern_matches_dir_py(
                    ws, "a/**/c", ws / "a" / "c"
                )
            )
            self.assertTrue(
                cmd._workspace_pattern_matches_dir_py(
                    ws, "a/**/c", ws / "a" / "b" / "c"
                )
            )

            # A symlink at `crates/scratch_link` must NOT be suppressed by
            # top-level `exclude = ["scratch*"]`.
            scratch_link = ws / "crates" / "scratch_link"
            os.symlink(outside, scratch_link)
            for tool, body in (
                (clean_bin / "cargo", "#!/bin/sh\nexit 0\n"),
                (clean_bin / "rustc", "#!/bin/sh\nexit 0\n"),
                (trusted_cc / cmd._LINKER_BIN_NAME, "#!/bin/sh\nexit 0\n"),
            ):
                tool.write_text(body, encoding="utf-8")
                tool.chmod(0o755)
            with (
                _patch_clean_tool_env(
                    {
                        "PATH": f"{clean_bin}{os.pathsep}{trusted_cc}",
                        "TMPDIR": str(root),
                    }
                ),
                _patch_subprocess_exec() as no_exec,
            ):
                with self.assertRaisesRegex(ValueError, "symlink"):
                    cmd.maybe_run_mir_eval_manifest(eval_manifest)
                no_exec.assert_not_called()

            scratch_link.unlink()
            seen_ws_dirs: list[tuple[bool, bool, bool, bool]] = []

            def _mock_glob_cargo(args: list[str], **kwargs: Any) -> mock.Mock:
                cwd = Path(kwargs["cwd"])
                ws_root = cwd.parent.parent
                if "test" in args:
                    seen_ws_dirs.append(
                        (
                            (ws_root / "crates" / "scratch_ok" / "src" / "lib.rs").is_file(),
                            (ws_root / "a" / "c" / "src" / "lib.rs").is_file(),
                            (ws_root / "a" / "b" / "c" / "src" / "lib.rs").is_file(),
                            (ws_root / "nested").exists(),
                        )
                    )
                    return mock.Mock(returncode=0, stdout="", stderr="")
                priv_td = Path(args[args.index("--target-dir") + 1])
                built_exe = priv_td / "debug" / "anneal-mir-eval"
                built_exe.parent.mkdir(parents=True, exist_ok=True)
                built_exe.write_bytes(b"glob-eval")
                mp = args[args.index("--manifest-path") + 1]
                art = json.dumps(
                    {
                        "reason": "compiler-artifact",
                        "manifest_path": mp,
                        "target": {"name": "anneal-mir-eval", "kind": ["bin"]},
                        "executable": str(built_exe),
                    }
                )
                return mock.Mock(returncode=0, stdout=art + "\n", stderr="")

            with (
                _patch_clean_tool_env(
                    {
                        "PATH": f"{clean_bin}{os.pathsep}{trusted_cc}",
                        "TMPDIR": str(root),
                    }
                ),
                _patch_subprocess_exec(side_effect=_mock_glob_cargo),
            ):
                st_glob, _ = cmd.maybe_run_mir_eval_manifest(eval_manifest)
            self.assertTrue(st_glob["passed"], st_glob)
            self.assertEqual(seen_ws_dirs, [(True, True, True, False)])

    def test_cargo_home_config_and_source_directory_materialized_immutable_against_races(
        self,
    ) -> None:
        import tomllib

        with tempfile.TemporaryDirectory() as tmpd:
            root = Path(tmpd).resolve()
            anneal_dir = root / "anneal"
            eval_dir = root / "eval"
            ext_ch = root / "ext-cargo-home"
            vendor_dir = root / "vendor"
            vend_crate = vendor_dir / "vendored_dep"
            outside = root / "outside"
            clean_bin = root / "clean-bin"
            trusted_cc = root / "trusted-cc"
            for d in (
                anneal_dir,
                eval_dir / "src",
                ext_ch,
                vend_crate / "src",
                outside,
                clean_bin,
                trusted_cc,
            ):
                d.mkdir(parents=True)

            (anneal_dir / "Cargo.toml").write_text(
                '[package]\nname = "anneal"\nversion = "0.1.0"\n',
                encoding="utf-8",
            )
            mir_manifest = eval_dir / "Cargo.toml"
            mir_manifest.write_text(
                '[package]\nname = "anneal-mir-eval"\nversion = "0.1.0"\n',
                encoding="utf-8",
            )
            (eval_dir / "src" / "main.rs").write_text(
                "fn main() {}\n", encoding="utf-8"
            )
            (vend_crate / "Cargo.toml").write_text(
                '[package]\nname = "vendored_dep"\nversion = "0.1.0"\n',
                encoding="utf-8",
            )
            (vend_crate / "build.rs").write_text(
                "fn main() { /* GENUINE_VENDOR */ }\n", encoding="utf-8"
            )
            (vend_crate / "src" / "lib.rs").write_text(
                "pub fn safe() {}\n", encoding="utf-8"
            )
            (outside / "secret.rs").write_text(
                "pub fn evil() {}\n", encoding="utf-8"
            )

            fake_cargo = clean_bin / "cargo"
            fake_rustc = clean_bin / "rustc"
            fake_cargo.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            fake_rustc.write_text(
                "#!/bin/sh\necho 'rustc 1.99.0'\n", encoding="utf-8"
            )
            fake_cargo.chmod(0o755)
            fake_rustc.chmod(0o755)

            # 1. Disallowed key inside `[source.*]`, symlink descendant, and
            #    hardlink descendant fail closed pre-Cargo across both flows.
            cfg_file = ext_ch / "config.toml"
            cfg_file.write_text(
                f'[source.evil]\nlocal-registry = "{vendor_dir}"\n',
                encoding="utf-8",
            )
            with (
                _patch_clean_tool_env(
                    {"PATH": str(clean_bin), "CARGO_HOME": str(ext_ch)}
                ),
                _patch_subprocess_exec() as no_exec,
            ):
                with self.assertRaisesRegex(ValueError, "disallowed key"):
                    cmd.maybe_run_mir_eval_manifest(mir_manifest)
                with self.assertRaisesRegex(ValueError, "disallowed key"):
                    cmd.run_anneal_diff(
                        anneal_root=anneal_dir,
                        manifest=None,
                        capture_bin=None,
                        mir_eval_bin=None,
                        cache_root=None,
                        self_check_oracle=False,
                    )
                no_exec.assert_not_called()

            cfg_file.write_text(
                '[source.crates-io]\nreplace-with = "anneal-vendor"\n'
                f'[source.anneal-vendor]\ndirectory = "{vendor_dir}"\n',
                encoding="utf-8",
            )
            os.symlink(outside / "secret.rs", vend_crate / "src" / "evil.rs")
            with (
                _patch_clean_tool_env(
                    {"PATH": str(clean_bin), "CARGO_HOME": str(ext_ch)}
                ),
                _patch_subprocess_exec() as no_exec,
            ):
                with self.assertRaisesRegex(ValueError, "symlink"):
                    cmd.maybe_run_mir_eval_manifest(mir_manifest)
                with self.assertRaisesRegex(ValueError, "symlink"):
                    cmd.run_anneal_diff(
                        anneal_root=anneal_dir,
                        manifest=None,
                        capture_bin=None,
                        mir_eval_bin=None,
                        cache_root=None,
                        self_check_oracle=False,
                    )
                no_exec.assert_not_called()
            (vend_crate / "src" / "evil.rs").unlink()

            hard_src = outside / "hard-build.rs"
            hard_src.write_text("fn main() {}\n", encoding="utf-8")
            (vend_crate / "build.rs").unlink()
            os.link(hard_src, vend_crate / "build.rs")
            with (
                _patch_clean_tool_env(
                    {"PATH": str(clean_bin), "CARGO_HOME": str(ext_ch)}
                ),
                _patch_subprocess_exec() as no_exec,
            ):
                with self.assertRaisesRegex(ValueError, "hardlink"):
                    cmd.maybe_run_mir_eval_manifest(mir_manifest)
                with self.assertRaisesRegex(ValueError, "hardlink"):
                    cmd.run_anneal_diff(
                        anneal_root=anneal_dir,
                        manifest=None,
                        capture_bin=None,
                        mir_eval_bin=None,
                        cache_root=None,
                        self_check_oracle=False,
                    )
                no_exec.assert_not_called()
            (vend_crate / "build.rs").unlink()
            (vend_crate / "build.rs").write_text(
                "fn main() { /* GENUINE_VENDOR */ }\n", encoding="utf-8"
            )

            # 2. Valid `[source]` materializes immutable `0o555`/`0o444` Cargo
            #    home and vendor tree; mutating originals between `cargo test`
            #    and `cargo build` (and during `run_anneal_diff`) cannot inject
            #    disallowed config or altered vendor crate code.
            observed: list[tuple[str, str, str, str, int, int]] = []
            diff_json = json.dumps(_sample_diff_report())

            def _capture_and_race(
                args: list[str],
                *,
                env: dict[str, str] | None = None,
                **_kwargs: Any,
            ) -> mock.Mock:
                assert env is not None
                ch_path = Path(env["CARGO_HOME"])
                cfg_p = ch_path / "config.toml"
                cfg_text = cfg_p.read_text(encoding="utf-8")
                parsed_cfg = tomllib.loads(cfg_text)
                v_path = Path(
                    parsed_cfg["source"]["anneal-vendor"]["directory"]
                )
                build_text = (v_path / "vendored_dep" / "build.rs").read_text(
                    encoding="utf-8"
                )
                ch_st = os.lstat(Path(os.path.realpath(ch_path)))
                cfg_st = os.lstat(cfg_p)
                observed.append(
                    (
                        str(ch_path),
                        cfg_text,
                        str(v_path),
                        build_text,
                        stat.S_IMODE(ch_st.st_mode),
                        stat.S_IMODE(cfg_st.st_mode),
                    )
                )
                self.assertEqual(cfg_st.st_nlink, 1)
                self.assertEqual(
                    stat.S_IMODE(
                        os.lstat(v_path / "vendored_dep" / "build.rs").st_mode
                    ),
                    0o444,
                )
                self.assertEqual(
                    stat.S_IMODE(os.lstat(v_path / "vendored_dep").st_mode),
                    0o555,
                )
                if len(args) >= 2 and args[1] == "test":
                    cfg_file.write_text(
                        '[build]\nrustc-wrapper = "/bin/false"\n',
                        encoding="utf-8",
                    )
                    (vend_crate / "build.rs").write_text(
                        "fn main() { /* TAMPERED_VENDOR */ }\n",
                        encoding="utf-8",
                    )
                elif len(args) >= 2 and args[1] == "build":
                    priv_td = Path(args[args.index("--target-dir") + 1])
                    built_exe = priv_td / "debug" / "anneal-mir-eval"
                    built_exe.parent.mkdir(parents=True, exist_ok=True)
                    built_exe.write_bytes(b"pinned-vendor-bin")
                    return mock.Mock(
                        returncode=0,
                        stdout=json.dumps(
                            {
                                "reason": "compiler-artifact",
                                "manifest_path": args[
                                    args.index("--manifest-path") + 1
                                ],
                                "target": {
                                    "kind": ["bin"],
                                    "name": "anneal-mir-eval",
                                },
                                "profile": {"test": False},
                                "executable": str(built_exe),
                            }
                        )
                        + "\n",
                        stderr="",
                    )
                return mock.Mock(returncode=0, stdout=diff_json, stderr="")

            with (
                _patch_clean_tool_env(
                    {
                        "PATH": str(clean_bin),
                        "CARGO_HOME": str(ext_ch),
                        "TMPDIR": str(root),
                    }
                ),
                _patch_subprocess_exec(side_effect=_capture_and_race),
            ):
                st_me, built_me = cmd.maybe_run_mir_eval_manifest(mir_manifest)
                self.assertTrue(st_me["passed"], st_me)
                self.assertIsNotNone(built_me)

                cfg_file.write_text(
                    '[source.crates-io]\nreplace-with = "anneal-vendor"\n'
                    f'[source.anneal-vendor]\ndirectory = "{vendor_dir}"\n',
                    encoding="utf-8",
                )
                (vend_crate / "build.rs").write_text(
                    "fn main() { /* GENUINE_VENDOR */ }\n", encoding="utf-8"
                )
                rc_diff, _ = cmd.run_anneal_diff(
                    anneal_root=anneal_dir,
                    manifest=None,
                    capture_bin=None,
                    mir_eval_bin=None,
                    cache_root=None,
                    self_check_oracle=False,
                )
                self.assertEqual(rc_diff, 0)

            self.assertEqual(len(observed), 3)
            for ch_s, cfg_t, v_s, b_t, ch_m, cfg_m in observed:
                self.assertNotEqual(Path(ch_s), ext_ch)
                self.assertNotEqual(Path(v_s), vendor_dir)
                if os.name == "posix" and sys.platform.startswith("linux"):
                    self.assertTrue(ch_s.startswith("/proc/self/fd/"), ch_s)
                    self.assertTrue(v_s.startswith("/proc/self/fd/"), v_s)
                self.assertIn("/sources/src-0", v_s)
                self.assertIn("GENUINE_VENDOR", b_t)
                self.assertNotIn("TAMPERED_VENDOR", b_t)
                self.assertNotIn("rustc-wrapper", cfg_t)
                self.assertEqual(ch_m, 0o555)
                self.assertEqual(cfg_m, 0o444)

    @unittest.skipUnless(
        os.name == "posix" and sys.platform.startswith("linux"),
        "Linux /proc/self/fd pre-populate pinning only",
    )
    def test_pinned_staging_dir_resists_parent_rename_during_populate_and_freeze(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as tmpd:
            root = Path(tmpd).resolve()
            stage_parent = root / "stage-parent"
            moved_parent = root / "moved-parent"
            stage_parent.mkdir(parents=True)

            def _raced_populate(priv_root: Path, pinned_root: Path) -> None:
                self.assertTrue(str(pinned_root).startswith("/proc/self/fd/"))
                os.rename(stage_parent, moved_parent)
                priv_root.mkdir(parents=True, exist_ok=True)
                os.symlink(root / "nonexistent", priv_root / "evil-sym")
                dst = pinned_root / "payload.txt"
                fd = os.open(dst, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
                try:
                    os.write(fd, b"genuine-pinned-bytes")
                    os.fchmod(fd, 0o444)
                finally:
                    os.close(fd)

            try:
                with ExitStack() as st:
                    pinned_root = cmd._build_pinned_staging_dir(
                        st,
                        prefix="anneal-race-",
                        base_dir=root,
                        tmp_parent=str(stage_parent),
                        label="raced staging",
                        populate=_raced_populate,
                    )
                    self.assertEqual(
                        (pinned_root / "payload.txt").read_bytes(),
                        b"genuine-pinned-bytes",
                    )
                    self.assertFalse((pinned_root / "evil-sym").exists())
                    self.assertEqual(
                        stat.S_IMODE(os.stat(pinned_root).st_mode), 0o555
                    )
            finally:
                if moved_parent.exists():
                    cmd._restore_dir_write_perms_top_down(moved_parent)
                    shutil.rmtree(moved_parent, ignore_errors=True)

    @unittest.skipUnless(
        os.name == "posix" and sys.platform.startswith("linux"),
        "Linux /proc/self/fd CARGO_HOME pinning only",
    )
    def test_cargo_home_staging_resists_parent_rename_and_traps(self) -> None:
        import tomllib

        with tempfile.TemporaryDirectory() as tmpd:
            root = Path(tmpd).resolve()
            store_prefix = root / "nix" / "store"
            vendor_dir = root / "vendor"
            vend_pkg = vendor_dir / "vdep"
            ch_src = root / "ch-source"
            ch_reg = root / "ch-registry"
            outside = root / "outside"
            stage_parent = root / "stage-parent"
            moved_parent = root / "moved-parent"
            for d in (
                store_prefix,
                vend_pkg / "src",
                ch_src,
                ch_reg / "registry" / "index" / "idx-0",
                ch_reg / "registry" / "cache" / "idx-0",
                outside,
                stage_parent,
            ):
                d.mkdir(parents=True)

            (vend_pkg / "Cargo.toml").write_text(
                '[package]\nname = "vdep"\nversion = "0.1.0"\n',
                encoding="utf-8",
            )
            (vend_pkg / "src" / "lib.rs").write_text(
                "pub fn safe_src() -> u32 { 7 }\n", encoding="utf-8"
            )
            (ch_src / "config.toml").write_text(
                '[source.crates-io]\nreplace-with = "anneal-vendor"\n'
                f'[source.anneal-vendor]\ndirectory = "{vendor_dir}"\n',
                encoding="utf-8",
            )
            crate_bytes = b"locked-crate-payload"
            crate_sha = hashlib.sha256(crate_bytes).hexdigest()
            (
                ch_reg / "registry" / "cache" / "idx-0" / "demo-1.0.0.crate"
            ).write_bytes(crate_bytes)
            (ch_reg / "registry" / "index" / "idx-0" / "config.json").write_text(
                '{"dl": "offline"}\n', encoding="utf-8"
            )

            def _run_raced_cargo_home(
                ch_dir: Path,
                parent_src: Path,
                parent_moved: Path,
                locked: tuple[tuple[str, str, str | None], ...],
            ) -> tuple[ExitStack, Path, Path]:
                st = ExitStack()
                decoy_seen: list[Path] = []

                def _pop(priv_root: Path, pinned_root: Path) -> Path | None:
                    self.assertTrue(str(pinned_root).startswith("/proc/self/fd/"))
                    os.rename(parent_src, parent_moved)
                    priv_root.mkdir(parents=True, exist_ok=True)
                    decoy_seen.append(priv_root)
                    os.symlink(outside, priv_root / "sources")
                    os.symlink(outside, priv_root / "registry")
                    _, writable_rel = cmd._inspect_and_stage_cargo_home_py(
                        ch_dir,
                        base_dir=root,
                        explicit_override=True,
                        store_prefix=store_prefix,
                        stage_ctx=(priv_root, pinned_root),
                        locked_crates=locked,
                    )
                    return writable_rel

                pinned = cmd._build_pinned_staging_dir(
                    st,
                    prefix="anneal-ch-race-",
                    base_dir=root,
                    tmp_parent=str(parent_src),
                    label="raced CARGO_HOME",
                    populate=_pop,
                )
                self.assertEqual(len(decoy_seen), 1)
                return st, pinned, decoy_seen[0]

            try:
                st_src, pinned_src, decoy_src = _run_raced_cargo_home(
                    ch_src, stage_parent, moved_parent, ()
                )
                with st_src:
                    cfg_p = pinned_src / "config.toml"
                    cfg_text = cfg_p.read_text(encoding="utf-8")
                    parsed = tomllib.loads(cfg_text)
                    vdir = Path(parsed["source"]["anneal-vendor"]["directory"])
                    self.assertTrue(str(vdir).startswith("/proc/self/fd/"))
                    self.assertEqual(
                        (vdir / "vdep" / "src" / "lib.rs").read_text(
                            encoding="utf-8"
                        ),
                        "pub fn safe_src() -> u32 { 7 }\n",
                    )
                    self.assertEqual(
                        stat.S_IMODE(os.lstat(cfg_p).st_mode), 0o444
                    )
                    self.assertEqual(
                        stat.S_IMODE(os.stat(pinned_src).st_mode), 0o555
                    )
                    self.assertFalse((decoy_src / "config.toml").exists())

                reg_parent = root / "reg-stage-parent"
                reg_moved = root / "reg-moved-parent"
                reg_parent.mkdir(parents=True)
                try:
                    st_reg, pinned_reg, decoy_reg = _run_raced_cargo_home(
                        ch_reg,
                        reg_parent,
                        reg_moved,
                        (("demo", "1.0.0", crate_sha),),
                    )
                    with st_reg:
                        staged_crate = (
                            pinned_reg
                            / "registry"
                            / "cache"
                            / "idx-0"
                            / "demo-1.0.0.crate"
                        )
                        self.assertEqual(staged_crate.read_bytes(), crate_bytes)
                        self.assertEqual(
                            stat.S_IMODE(os.stat(pinned_reg).st_mode), 0o555
                        )
                        self.assertEqual(
                            stat.S_IMODE(
                                os.stat(pinned_reg / "registry" / "src").st_mode
                            ),
                            0o700,
                        )
                        self.assertTrue(
                            os.path.islink(decoy_reg / "registry")
                        )
                finally:
                    if reg_moved.exists():
                        cmd._restore_dir_write_perms_top_down(reg_moved)
                        shutil.rmtree(reg_moved, ignore_errors=True)
            finally:
                if moved_parent.exists():
                    cmd._restore_dir_write_perms_top_down(moved_parent)
                    shutil.rmtree(moved_parent, ignore_errors=True)

    @unittest.skipUnless(
        os.name == "posix" and sys.platform.startswith("linux"),
        "Linux /proc/self/fd workspace extraction & explicit staging only",
    )
    def test_mir_eval_workspace_extract_and_explicit_staging_resist_parent_rename(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as tmpd:
            root = Path(tmpd).resolve()
            ws = root / "ws"
            eval_dir = ws / "tools" / "anneal-mir-eval"
            excl_dir = ws / "tools" / "excluded"
            clean_bin = root / "clean-bin"
            trusted_cc = root / "trusted-cc"
            src_tmp = root / "src-tmp"
            moved_src_tmp = root / "moved-src-tmp"
            stage_parent = root / "explicit-stage-parent"
            moved_stage_parent = root / "moved-explicit-stage-parent"
            explicit_stage_dir = stage_parent / "stage-out"
            decoy_dir = root / "decoy-target"
            for d in (
                eval_dir / "src",
                excl_dir / "src",
                clean_bin,
                trusted_cc,
                src_tmp,
                explicit_stage_dir,
                decoy_dir,
            ):
                d.mkdir(parents=True)

            ws_manifest = ws / "Cargo.toml"
            ws_manifest.write_text(
                '[workspace]\nresolver = "2"\nmembers = ["tools/*"]\n'
                'exclude = ["tools/excluded"]\n',
                encoding="utf-8",
            )
            (eval_dir / "Cargo.toml").write_text(
                '[package]\nname = "anneal-mir-eval"\nversion = "0.1.0"\n',
                encoding="utf-8",
            )
            (eval_dir / "src" / "main.rs").write_text(
                "fn main() {}\n", encoding="utf-8"
            )
            (excl_dir / "Cargo.toml").write_text(
                '[package]\nname = "anneal-mir-eval"\nversion = "0.1.0"\n',
                encoding="utf-8",
            )
            (excl_dir / "src" / "main.rs").write_text(
                "fn main() {}\n", encoding="utf-8"
            )
            (decoy_dir / "Cargo.toml").write_text(
                '[package]\nname = "evil"\n', encoding="utf-8"
            )
            for tool, body in (
                (clean_bin / "cargo", "#!/bin/sh\nexit 0\n"),
                (clean_bin / "rustc", "#!/bin/sh\nexit 0\n"),
                (trusted_cc / cmd._LINKER_BIN_NAME, "#!/bin/sh\nexit 0\n"),
            ):
                tool.write_text(body, encoding="utf-8")
                tool.chmod(0o755)

            raced_once = False
            observed_mp: list[str] = []

            def _mock_raced_cargo(args: list[str], **_kwargs: Any) -> mock.Mock:
                nonlocal raced_once
                if "build" not in args:
                    return mock.Mock(returncode=0, stdout="", stderr="")
                mp = args[args.index("--manifest-path") + 1]
                observed_mp.append(mp)
                self.assertTrue(mp.startswith("/proc/self/fd/"), mp)
                priv_td = Path(args[args.index("--target-dir") + 1])
                built_exe = priv_td / "debug" / "anneal-mir-eval"
                built_exe.parent.mkdir(parents=True, exist_ok=True)
                built_exe.write_bytes(b"#!/bin/sh\nexit 0\n")
                built_exe.chmod(0o755)
                if not raced_once:
                    raced_once = True
                    os.rename(stage_parent, moved_stage_parent)
                    stage_parent.mkdir(parents=True, exist_ok=True)
                    os.symlink(decoy_dir, explicit_stage_dir)

                lines = [
                    # Excluded workspace member must be ignored.
                    json.dumps(
                        {
                            "reason": "compiler-artifact",
                            "manifest_path": mp.replace(
                                "/Cargo.toml", "/tools/excluded/Cargo.toml"
                            ),
                            "target": {
                                "name": "anneal-mir-eval",
                                "kind": ["bin"],
                            },
                            "profile": {"test": False},
                            "executable": str(root / "evil-excluded-bin"),
                        }
                    ),
                    # Non-list `target.kind` must be ignored.
                    json.dumps(
                        {
                            "reason": "compiler-artifact",
                            "manifest_path": mp.replace(
                                "/Cargo.toml",
                                "/tools/anneal-mir-eval/Cargo.toml",
                            ),
                            "target": {
                                "name": "anneal-mir-eval",
                                "kind": "bin",
                            },
                            "profile": {"test": False},
                            "executable": str(root / "evil-scalar-kind-bin"),
                        }
                    ),
                    # Genuine FD-pinned workspace member artifact.
                    json.dumps(
                        {
                            "reason": "compiler-artifact",
                            "manifest_path": mp.replace(
                                "/Cargo.toml",
                                "/tools/anneal-mir-eval/Cargo.toml",
                            ),
                            "target": {
                                "name": "anneal-mir-eval",
                                "kind": ["bin"],
                            },
                            "profile": {"test": False},
                            "executable": str(built_exe),
                        }
                    ),
                ]
                return mock.Mock(
                    returncode=0, stdout="\n".join(lines) + "\n", stderr=""
                )

            try:
                with ExitStack() as stage_stack:
                    with (
                        _patch_clean_tool_env(
                            {
                                "PATH": f"{clean_bin}{os.pathsep}{trusted_cc}",
                                "TMPDIR": str(src_tmp),
                            }
                        ),
                        _patch_subprocess_exec(side_effect=_mock_raced_cargo),
                    ):
                        st_res, iso_bin = cmd.maybe_run_mir_eval_manifest(
                            ws_manifest,
                            staging_dir=explicit_stage_dir,
                            staging_exit_stack=stage_stack,
                        )
                    self.assertTrue(st_res["passed"], st_res)
                    assert iso_bin is not None
                    self.assertTrue(
                        str(iso_bin).startswith("/proc/self/fd/"), iso_bin
                    )
                    self.assertIn(".anneal-isolated-bins", str(iso_bin))
                    cmd._verify_pinned_proc_fd_executable(
                        iso_bin, "raced explicit staged anneal-mir-eval"
                    )
                    self.assertEqual(
                        iso_bin.read_bytes(), b"#!/bin/sh\nexit 0\n"
                    )
                    self.assertEqual(
                        stat.S_IMODE(os.stat(iso_bin.parent).st_mode), 0o555
                    )
                    self.assertEqual(
                        stat.S_IMODE(os.stat(iso_bin.parent.parent).st_mode),
                        0o555,
                    )

                # After staging_exit_stack unwinds, moved explicit staging
                # root has write bits restored via fd even with symlink decoy.
                moved_stage = moved_stage_parent / "stage-out"
                self.assertEqual(stat.S_IMODE(os.stat(moved_stage).st_mode), 0o700)
                self.assertTrue(os.path.islink(explicit_stage_dir))

                # Also verify direct `_extract_built_executable` stays immune
                # when `src_tmp` is renamed and replaced by a decoy, while
                # rejecting scalar `kind`, excluded members, and disk paths.
                with ExitStack() as st2:
                    prep = cmd._stage_mir_eval_source_graph(
                        ws_manifest, root, tmp_parent=str(src_tmp), exit_stack=st2
                    )
                    assert prep.staging_root is not None
                    assert prep.pinned_root_prefix is not None
                    orig_disk_root = prep.staging_root
                    os.rename(src_tmp, moved_src_tmp)
                    orig_disk_root.parent.mkdir(parents=True, exist_ok=True)
                    orig_disk_root.mkdir(parents=True, exist_ok=True)
                    os.symlink(
                        decoy_dir / "Cargo.toml", orig_disk_root / "Cargo.toml"
                    )
                    member_fd_mp = (
                        f"{prep.pinned_root_prefix}/tools/anneal-mir-eval/Cargo.toml"
                    )
                    member_disk_mp = str(
                        orig_disk_root / "tools/anneal-mir-eval/Cargo.toml"
                    )
                    excl_fd_mp = (
                        f"{prep.pinned_root_prefix}/tools/excluded/Cargo.toml"
                    )
                    for bad_line in (
                        json.dumps(
                            {
                                "reason": "compiler-artifact",
                                "manifest_path": member_disk_mp,
                                "target": {
                                    "name": "anneal-mir-eval",
                                    "kind": ["bin"],
                                },
                                "executable": str(root / "bad-disk"),
                            }
                        ),
                        json.dumps(
                            {
                                "reason": "compiler-artifact",
                                "manifest_path": excl_fd_mp,
                                "target": {
                                    "name": "anneal-mir-eval",
                                    "kind": ["bin"],
                                },
                                "executable": str(root / "bad-excl"),
                            }
                        ),
                        json.dumps(
                            {
                                "reason": "compiler-artifact",
                                "manifest_path": member_fd_mp,
                                "target": {
                                    "name": "anneal-mir-eval",
                                    "kind": "bin",
                                },
                                "executable": str(root / "bad-kind"),
                            }
                        ),
                    ):
                        self.assertIsNone(
                            cmd._extract_built_executable(
                                bad_line,
                                "anneal-mir-eval",
                                ws_manifest,
                                staged_manifest=prep.staged_manifest,
                                pinned_root_prefix=prep.pinned_root_prefix,
                                staging_root=orig_disk_root,
                            )
                        )
                    good_line = json.dumps(
                        {
                            "reason": "compiler-artifact",
                            "manifest_path": member_fd_mp,
                            "target": {
                                "name": "anneal-mir-eval",
                                "kind": ["bin"],
                            },
                            "executable": str(root / "ok-bin"),
                        }
                    )
                    self.assertEqual(
                        cmd._extract_built_executable(
                            good_line,
                            "anneal-mir-eval",
                            ws_manifest,
                            staged_manifest=prep.staged_manifest,
                            pinned_root_prefix=prep.pinned_root_prefix,
                            staging_root=prep.staging_root,
                        ),
                        root / "ok-bin",
                    )
            finally:
                for p in (moved_src_tmp, moved_stage_parent):
                    if p.exists():
                        cmd._restore_dir_write_perms_top_down(p)
                        shutil.rmtree(p, ignore_errors=True)


if __name__ == "__main__":
    unittest.main()
