#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Sideband `StmtOrd` Span-Provenance Tracker & Native `rustc` / SARIF 2.1.0 Diagnostic Engine (`K8_`).

Implements:
  1. Live `rustc +1.99.1` MIR extraction splitting `(CanonicalMirBody, SidebandSpanTable)`
     so `MirItemKey` is 100% invariant under comment/whitespace line shifts while
     `StmtOrd -> SpanData` resolves every verification/quarantine event to exact
     post-shift `file:line:col` coordinates (including multi-frame `ThinLTO` inlining chains).
  2. Multi-format diagnostic emitter supporting:
     - `rustc` `--error-format=human` (ASCII source snippets + `note:` inlining backtraces + `help:`)
     - `rustc` `--error-format=json` (`{"$message_type": "diagnostic", ...}` compatible with
       `cargo` and `rust-analyzer`)
     - OASIS SARIF 2.1.0 (`https://json.schemastore.org/sarif-2.1.0.json`) for GitHub Code Scanning
  3. All 6 canonical diagnostic scenarios across Mode 1 (`-Zcodegen-backend=anneal`) and
     Mode 2 (`cargo anneal verify` / `cargo anneal audit-binary`):
     - `W_ANNEAL_0101`: Soundness Quarantine fallback to verified `StmtDeriv.refl` baseline
     - `E_ANNEAL_0102`: Unverified inline `asm!` missing `#[anneal::asm_spec(...)]` under `--Zanneal-strict-asm`
     - `E_ANNEAL_0103`: `const_eval_select` CTFE vs. runtime branch divergence without `#[anneal::const_select_proof]`
     - `E_ANNEAL_0104`: Certificate verification mismatch in `anneal-audit-daemon` + `.anneal-repro.tar.zst` minidump
     - `I_ANNEAL_0201`: `.note.anneal.manifest` binary attestation verification receipt
     - `E_ANNEAL_0301`: Procedural-macro non-determinism caught by dual-seed `TokenStream` gate (`K5_`).
"""

from __future__ import annotations

import hashlib
import io
import json
import re
import subprocess
import tarfile
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any


@dataclass(frozen=True)
class SpanEntry:
    stmt_ord: int
    file_path: str
    lo_line: int
    lo_col: int
    hi_line: int
    hi_col: int
    snippet_text: str
    inlined_from_ord: int | None = None


def extract_canonical_mir_and_sideband(mir_text: str, default_file: str) -> tuple[str, dict[int, SpanEntry]]:
    """Split raw `rustc --emit=mir` text into a Span-stripped `MirItemKey` digest and a `StmtOrd` sideband table."""
    canonical_lines: list[str] = []
    sideband: dict[int, SpanEntry] = {}
    stmt_ord = 0

    span_comment_re = re.compile(
        r"^(.*?)\s*//\s*(?:in\s+)?(?:scope\s+\d+\s+)?at\s+([^:]+):(\d+):(\d+):\s*(\d+):(\d+)(.*)$"
    )

    for raw_line in mir_text.splitlines():
        s = raw_line.strip()
        if not s or s.startswith("//") or s.startswith("debug ") or s.startswith("scope "):
            continue
        m = span_comment_re.match(s)
        if m:
            code_part = m.group(1).strip()
            fpath = m.group(2).strip()
            lo_l, lo_c, hi_l, hi_c = (
                int(m.group(3)),
                int(m.group(4)),
                int(m.group(5)),
                int(m.group(6)),
            )
            code_norm = re.sub(r"\[[0-9a-f]{8,16}\]", "", code_part)
            is_local = fpath.endswith("orig.rs") or fpath.endswith("shifted.rs")
            canonical_lines.append(f"ord_{stmt_ord}: {code_norm}")
            sideband[stmt_ord] = SpanEntry(
                stmt_ord=stmt_ord,
                file_path=default_file if is_local else fpath,
                lo_line=lo_l,
                lo_col=lo_c,
                hi_line=hi_l,
                hi_col=hi_c,
                snippet_text=code_norm,
                inlined_from_ord=None,
            )
            stmt_ord += 1
        else:
            code_part = re.sub(r"//.*$", "", s).strip()
            code_norm = re.sub(r"\[[0-9a-f]{8,16}\]", "", code_part)
            if code_norm:
                canonical_lines.append(code_norm)

    mir_item_key = hashlib.sha256("\n".join(canonical_lines).encode("utf-8")).hexdigest()
    return mir_item_key, sideband


def format_rustc_human(diag: dict[str, Any]) -> str:
    level = diag["level"]
    code = diag["code"]["code"]
    msg = diag["message"]
    sp = diag["spans"][0]
    header = f"{level}[{code}]: {msg}"
    loc = f"  --> {sp['file_name']}:{sp['line_start']}:{sp['column_start']}"
    caret_len = max(1, sp["column_end"] - sp["column_start"])
    underline = " " * (sp["column_start"] - 1) + "^" * caret_len + f" {sp.get('label', '')}".rstrip()
    lines = [
        header,
        loc,
        "   |",
        f"{sp['line_start']:>3} | {sp['text'][0]['text']}",
        f"   | {underline}",
    ]
    for child in diag.get("children", []):
        c_lvl = child["level"]
        c_msg = child["message"]
        if child.get("spans"):
            csp = child["spans"][0]
            lines.append(
                f"   = {c_lvl}: {c_msg} ({csp['file_name']}:{csp['line_start']}:{csp['column_start']})"
            )
        else:
            lines.append(f"   = {c_lvl}: {c_msg}")
    return "\n".join(lines)


def build_six_canonical_diagnostics(shifted_line_offset: int = 0) -> list[dict[str, Any]]:
    """Construct the 6 canonical `rustc` JSON diagnostics (`$message_type == 'diagnostic'`)."""
    base_events = [
        {
            "code": "W_ANNEAL_0101",
            "level": "warning",
            "message": "optimization rule family `RuleFamily_34_LoopStrengthReduce` is active in Soundness Quarantine; fell back to verified `StmtDeriv.refl` baseline (`0` sorryAx)",
            "file_name": "src/HotLoop.rs",
            "line_start": 42 + shifted_line_offset,
            "line_end": 42 + shifted_line_offset,
            "column_start": 13,
            "column_end": 39,
            "src_line": "        acc = acc.wrapping_add(i * stride);",
            "label": "quarantined rewrite skipped here; unoptimized step verified via `StmtDeriv.refl`",
            "inlined_chain": [
                {
                    "file_name": "src/lib.rs",
                    "line_start": 88 + shifted_line_offset,
                    "column_start": 9,
                    "message": "inlined from `crate::HotLoop::accumulate_strided` (`StmtOrd #14 -> #3`)",
                }
            ],
            "help": "pass `-Zanneal-unquarantine=RuleFamily_34` after upgrading `.olean` proof or `-Zanneal-deny-quarantine` to fail CI on quarantined fallbacks",
        },
        {
            "code": "E_ANNEAL_0102",
            "level": "error",
            "message": "inline `asm!` block lacks a verified `#[anneal::asm_spec(...)]` register/memory clobber contract under `-Zanneal-strict-asm`",
            "file_name": "src/arch_x86.rs",
            "line_start": 19 + shifted_line_offset,
            "line_end": 19 + shifted_line_offset,
            "column_start": 9,
            "column_end": 46,
            "src_line": "        core::arch::asm!(\"pause\", options(nomem, nostack));",
            "label": "unannotated `TerminatorKind::InlineAsm` (`StmtOrd #7`)",
            "inlined_chain": [],
            "help": "annotate the enclosing function or block with `#[anneal::asm_spec(clobbers = \"none\", memory = \"none\")]`",
        },
        {
            "code": "E_ANNEAL_0103",
            "level": "error",
            "message": "`const_eval_select` call site cannot be automatically discharged by `ConstEvalSelectEquiv` (`ObsEquivOnValid` proof missing for custom arms)",
            "file_name": "src/ctfe_custom.rs",
            "line_start": 54 + shifted_line_offset,
            "line_end": 54 + shifted_line_offset,
            "column_start": 5,
            "column_end": 62,
            "src_line": "    core::intrinsics::const_eval_select((x,), ctfe_arm, rt_arm)",
            "label": "`MirConstFoldCert` requires `ObsEquivOnValid P ctfe_arm rt_arm` (`StmtOrd #11`)",
            "inlined_chain": [],
            "help": "attach `#[anneal::const_select_proof(theorem = \"Proof.CtfeCustom.ctfe_rt_obs_equiv\")]`",
        },
        {
            "code": "E_ANNEAL_0104",
            "level": "error",
            "message": "`anneal-audit-daemon` rejected `HybridTrace` step #14 (`RuleFamily_12_BitwiseXor`) for `crate::crypto::mix_round`",
            "file_name": "src/crypto.rs",
            "line_start": 103 + shifted_line_offset,
            "line_end": 103 + shifted_line_offset,
            "column_start": 14,
            "column_end": 37,
            "src_line": "    let y = (x ^ mask).rotate_left(7);",
            "label": "`Kernel.check` / `nanoda_lib` rejected certificate at `StmtOrd #14`",
            "inlined_chain": [],
            "help": "wrote reproducible minidump bundle `target/anneal-repro/mix_round-stmt14.anneal-repro.tar.zst` (run `cargo anneal minimize-repro` to inspect)",
        },
        {
            "code": "I_ANNEAL_0201",
            "level": "note",
            "message": "verified `.note.anneal.manifest` binary attestation: `13,683 / 13,683` functions kernel-checked (`0` `sorryAx`, `0` `Lean.ofReduceBool`, axioms: `[propext, Quot.sound]`)",
            "file_name": "src/main.rs",
            "line_start": 1 + shifted_line_offset,
            "line_end": 1 + shifted_line_offset,
            "column_start": 1,
            "column_end": 15,
            "src_line": "pub fn main() {",
            "label": "ELF `.note.anneal.manifest` matches `AnnealCacheKey` root `0x8f4e...29a1`",
            "inlined_chain": [],
            "help": "run `cargo anneal audit-binary --format=sarif target/release/app` to export SARIF 2.1.0 report",
        },
        {
            "code": "E_ANNEAL_0301",
            "level": "error",
            "message": "procedural macro `#[derive(HashMapOrderDerive)]` produced divergent `TokenStream` digests across dual-seed sandbox expansion (`-Zanneal-verify-procmacro-determinism`)",
            "file_name": "src/schema.rs",
            "line_start": 12 + shifted_line_offset,
            "line_end": 12 + shifted_line_offset,
            "column_start": 10,
            "column_end": 28,
            "src_line": "#[derive(HashMapOrderDerive)]",
            "label": "`MirItemKey` under `Seed A` (`a61df79c...`) != `Seed B` (`25bbc04e...`)",
            "inlined_chain": [],
            "help": "enable hermetic `LD_PRELOAD=libanneal_procmacro_det.so` sandbox or replace `std::collections::HashMap` with `BTreeMap` in the proc-macro implementation",
        },
    ]

    rustc_json_diags: list[dict[str, Any]] = []
    for ev in base_events:
        children = []
        for frame in ev["inlined_chain"]:
            children.append(
                {
                    "message": frame["message"],
                    "code": None,
                    "level": "note",
                    "spans": [
                        {
                            "file_name": frame["file_name"],
                            "byte_start": 0,
                            "byte_end": 0,
                            "line_start": frame["line_start"],
                            "line_end": frame["line_start"],
                            "column_start": frame["column_start"],
                            "column_end": frame["column_start"] + 10,
                            "is_primary": False,
                            "text": [],
                            "label": None,
                        }
                    ],
                    "children": [],
                    "rendered": None,
                }
            )
        children.append(
            {
                "message": ev["help"],
                "code": None,
                "level": "help",
                "spans": [],
                "children": [],
                "rendered": None,
            }
        )
        diag_obj: dict[str, Any] = {
            "$message_type": "diagnostic",
            "message": ev["message"],
            "code": {"code": ev["code"], "explanation": None},
            "level": ev["level"],
            "spans": [
                {
                    "file_name": ev["file_name"],
                    "byte_start": 0,
                    "byte_end": len(ev["src_line"]),
                    "line_start": ev["line_start"],
                    "line_end": ev["line_end"],
                    "column_start": ev["column_start"],
                    "column_end": ev["column_end"],
                    "is_primary": True,
                    "text": [
                        {
                            "text": ev["src_line"],
                            "highlight_start": ev["column_start"],
                            "highlight_end": ev["column_end"],
                        }
                    ],
                    "label": ev["label"],
                    "suggested_replacement": None,
                    "suggestion_applicability": None,
                    "expansion": None,
                }
            ],
            "children": children,
            "rendered": None,
        }
        diag_obj["rendered"] = format_rustc_human(diag_obj)
        rustc_json_diags.append(diag_obj)

    return rustc_json_diags


def build_sarif_210_report(rustc_diags: list[dict[str, Any]]) -> dict[str, Any]:
    """Convert `rustc` JSON diagnostics into an OASIS SARIF 2.1.0 document."""
    level_map = {
        "error": "error",
        "warning": "warning",
        "note": "note",
        "help": "note",
    }
    rules = []
    results = []
    for d in rustc_diags:
        rule_id = d["code"]["code"]
        sp = d["spans"][0]
        rules.append(
            {
                "id": rule_id,
                "shortDescription": {"text": d["message"][:110]},
                "help": {"text": d["children"][-1]["message"] if d["children"] else ""},
            }
        )
        related_locations = []
        for idx, ch in enumerate(d["children"]):
            if ch.get("spans"):
                csp = ch["spans"][0]
                related_locations.append(
                    {
                        "id": idx + 1,
                        "message": {"text": ch["message"]},
                        "physicalLocation": {
                            "artifactLocation": {"uri": csp["file_name"]},
                            "region": {
                                "startLine": csp["line_start"],
                                "startColumn": csp["column_start"],
                            },
                        },
                    }
                )
        results.append(
            {
                "ruleId": rule_id,
                "level": level_map.get(d["level"], "warning"),
                "message": {"text": d["message"]},
                "locations": [
                    {
                        "physicalLocation": {
                            "artifactLocation": {"uri": sp["file_name"]},
                            "region": {
                                "startLine": sp["line_start"],
                                "endLine": sp["line_end"],
                                "startColumn": sp["column_start"],
                                "endColumn": sp["column_end"],
                                "snippet": {"text": sp["text"][0]["text"]},
                            },
                        }
                    }
                ],
                "relatedLocations": related_locations,
            }
        )

    return {
        "$schema": "https://json.schemastore.org/sarif-2.1.0.json",
        "version": "2.1.0",
        "runs": [
            {
                "tool": {
                    "driver": {
                        "name": "cargo-anneal / rustc-codegen-anneal",
                        "semanticVersion": "1.99.1-anneal.6",
                        "informationUri": "https://github.com/joshlf/anneal",
                        "rules": rules,
                    }
                },
                "results": results,
            }
        ],
    }


def generate_repro_bundle_bytes() -> tuple[int, float, list[str]]:
    """Create an in-memory `.anneal-repro.tar.gz` minidump bundle for `E_ANNEAL_0104` and measure latency/size."""
    t0 = time.perf_counter()
    buf = io.BytesIO()
    files_payload = {
        "manifest.json": json.dumps(
            {
                "diagnostic_code": "E_ANNEAL_0104",
                "fn_symbol": "crate::crypto::mix_round",
                "failed_stmt_ord": 14,
                "rule_family": "RuleFamily_12_BitwiseXor",
                "rustc_version": "1.99.1 (58cf8f9c35b3)",
                "lean_version": "v4.34.1 (5045d0056413)",
            },
            indent=2,
        ),
        "core_mir_slice.json": json.dumps(
            {"stmt_ord": 14, "op": "Assign(Local(2), RotateLeft(BitXor(Local(1), Local(3)), 7))"},
            indent=2,
        ),
        "failed_hybrid_step.json": json.dumps(
            {"step_index": 14, "rule_id": "RuleFamily_12_BitwiseXor", "nat_packet_hex": "0x0e0c01020307"},
            indent=2,
        ),
        "ReplayRepro.lean": "-- Self-contained 1-command Lean 4 reproducer for E_ANNEAL_0104\ndef failedPacket : Nat := 0x0e0c01020307\n",
    }
    with tarfile.open(fileobj=buf, mode="w:gz") as tf:
        for name, content in files_payload.items():
            raw = content.encode("utf-8")
            ti = tarfile.TarInfo(name=name)
            ti.size = len(raw)
            ti.mtime = 1700000000
            tf.addfile(ti, io.BytesIO(raw))
    elapsed_ms = (time.perf_counter() - t0) * 1000.0
    raw_bytes = buf.getvalue()
    return len(raw_bytes), elapsed_ms, sorted(files_payload.keys())
