#!/usr/bin/env python3
"""Deterministic generator for the V5 diagnostic-prequalification design.

This file does not contain package/target identities, atom manifests, or seeds.
Those are integration inputs. Running ``draft``/``verify-draft`` or
``self-test`` is safe; ``generate`` emits only explicitly unverified draft
documents. The reviewed static integration and freeze entrypoint is
``integrate.py``.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path
from typing import Any


RUN = Path(__file__).resolve().parent
MODES = ("E", "V", "F", "P", "B", "L", "R", "Q")
CONDITIONS = ("v5", "v4", "no_skill")
REPLICATES = tuple(range(1, 6))
SCORERS = ("s1", "s2")
CONSISTENCY_REVIEWERS = ("c1", "c2")
PROMPT_REGIMES = {
    "E": "controlled",
    "V": "controlled",
    "F": "controlled",
    "P": "controlled",
    "B": "naturalistic",
    "L": "naturalistic",
    "R": "naturalistic",
    "Q": "controlled",
}
REPORT_PROMPTS = {
    "controlled": RUN / "prompts" / "report-controlled.md",
    "naturalistic": RUN / "prompts" / "report-naturalistic.md",
}
OPERATIONAL_BLOCK = """Operational constraints: use one agent context for this request; do not create
helpers or sub-agents. Do not build, run, test, or edit the target. Inspect only
the declared input paths and provided Rust documentation. Write only the declared output
path."""
REPORTS_PER_MODE = len(CONDITIONS) * len(REPLICATES)
TOTAL_REPORTS = len(MODES) * REPORTS_PER_MODE
SEED_NAMES = (
    "condition",
    "schedule",
    "blind",
    "presentation",
    "scorer",
    "consistency",
)
HEX64 = re.compile(r"^[0-9a-f]{64}$")
INPUT_ALIAS = "input"
OUTPUT_ALIAS = "output"
BYTE_TREE_ALGORITHM = "BYTE_TREE_V1"
PORTABLE_PATH_COMPONENT = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._+@%=:,-]*$")


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def portable_relative_path(value: str, field: str) -> bytes:
    """Return the canonical UTF-8 bytes for the V5 portable path domain.

    BYTE_TREE_V1's historical record encoding is intentionally unchanged.  New
    V5 material rejects paths outside a strict portable ASCII subset before it
    uses that encoding, so embedded delimiters, control bytes, undecodable
    filesystem names, and platform-dependent spellings cannot collide.
    """

    if not isinstance(value, str) or not value or value != value.strip():
        raise ValueError(f"{field} must be a nonblank relative path")
    try:
        encoded = value.encode("utf-8", errors="strict")
    except UnicodeEncodeError as error:
        raise ValueError(f"{field} is not strict UTF-8") from error
    path = Path(value)
    if (
        path.is_absolute()
        or ".." in path.parts
        or value == "."
        or path.as_posix() != value
        or any(not PORTABLE_PATH_COMPONENT.fullmatch(part) for part in path.parts)
    ):
        raise ValueError(
            f"{field} must be a normalized relative POSIX path in "
            "PORTABLE_ASCII_RELATIVE_PATH_V1"
        )
    return encoded


def byte_tree_v1(root: Path) -> str:
    """Return the historical BYTE_TREE_V1 identity used by frozen packages.

    The identity includes every directory record and, for files, the path,
    byte length, and SHA-256 of the bytes. Symlinks and special entries are
    rejected rather than followed.
    """
    if root.is_symlink() or not root.is_dir():
        raise ValueError(f"BYTE_TREE_V1 root is not a real directory: {root}")
    records: list[bytes] = []
    for item in sorted(root.rglob("*"), key=lambda path: path.relative_to(root).as_posix()):
        relative = item.relative_to(root).as_posix()
        portable_relative_path(relative, "BYTE_TREE_V1 entry")
        if item.is_symlink() or not (item.is_dir() or item.is_file()):
            raise ValueError(f"unsupported BYTE_TREE_V1 entry: {item}")
        if item.is_dir():
            records.append(f"d\0{relative}\n".encode())
        else:
            data = item.read_bytes()
            records.append(f"f\0{relative}\0{len(data)}\0{sha256(data)}\n".encode())
    return sha256(b"".join(records))


def json_dump(value: Any) -> str:
    return (
        json.dumps(
            value,
            indent=2,
            sort_keys=True,
            ensure_ascii=False,
            allow_nan=False,
        )
        + "\n"
    )


def keyed(tag: str, seed: str, value: str) -> str:
    return sha256(tag.encode() + b"\0" + bytes.fromhex(seed) + b"\0" + value.encode())


def opaque_labels(count: int) -> tuple[str, ...]:
    if count < 1 or count > 26:
        raise ValueError("DRAFT opaque labels support 1 through 26 values")
    return tuple(chr(ord("A") + index) for index in range(count))


def _reject_nonfinite_json(value: str) -> Any:
    raise ValueError(f"non-finite JSON number is forbidden: {value}")


def _unique_json_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON object key is forbidden: {key!r}")
        result[key] = value
    return result


def parse_json_bytes(data: bytes, label: str) -> Any:
    try:
        text = data.decode("utf-8", errors="strict")
        return json.loads(
            text,
            object_pairs_hook=_unique_json_object,
            parse_constant=_reject_nonfinite_json,
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ValueError(f"cannot parse strict JSON {label}: {error}") from error


def read_json(path: Path) -> Any:
    try:
        return parse_json_bytes(path.read_bytes(), str(path))
    except OSError as error:
        raise ValueError(f"cannot read JSON {path}: {error}") from error


def require_relative_path(value: Any, field: str) -> str:
    if not isinstance(value, str):
        raise ValueError(f"{field} must be a path string")
    portable_relative_path(value, field)
    return value


def render_report_prompt(
    regime: str,
    *,
    invocation_block: str,
    input_root: str = INPUT_ALIAS,
    output_root: str = OUTPUT_ALIAS,
    target_path: str,
    authority_path: str,
    task_mode: str,
    output_path: str,
    word_cap: int,
) -> bytes:
    if regime not in REPORT_PROMPTS:
        raise ValueError(f"unknown report prompt regime: {regime}")
    if not isinstance(invocation_block, str):
        raise ValueError("invocation block must be text; use the empty string for no-skill")
    values = {
        "{{INVOCATION_BLOCK}}": invocation_block,
        "{{INPUT_ROOT}}": require_agent_visible_alias(input_root, "input root"),
        "{{OUTPUT_ROOT}}": require_agent_visible_alias(output_root, "output root"),
        "{{TARGET_PATH}}": require_relative_path(target_path, "target path"),
        "{{AUTHORITY_PATH}}": require_relative_path(authority_path, "authority path"),
        "{{TASK_MODE}}": task_mode,
        "{{OUTPUT_PATH}}": require_relative_path(output_path, "output path"),
        "{{WORD_CAP}}": str(word_cap),
    }
    if not isinstance(task_mode, str) or not re.fullmatch(r"[a-z][a-z0-9_-]*", task_mode):
        raise ValueError("task mode must be a stable lowercase identifier")
    if type(word_cap) is not int or word_cap < 1:
        raise ValueError("word cap must be a positive integer")
    template = REPORT_PROMPTS[regime].read_text(encoding="utf-8")
    for marker in values:
        if template.count(marker) != 1:
            raise ValueError(f"report template marker count is not one: {marker}")
        template = template.replace(marker, values[marker])
    if "{{" in template or "}}" in template:
        raise ValueError("unresolved marker in rendered report prompt")
    return template.encode("utf-8")


def require_agent_visible_alias(value: Any, field: str) -> str:
    expected = INPUT_ALIAS if field == "input root" else OUTPUT_ALIAS
    if value != expected:
        raise ValueError(f"{field} must be the fixed relative alias {expected!r}")
    return value


def validate_digest(value: Any, field: str) -> str:
    if not isinstance(value, str) or not HEX64.fullmatch(value):
        raise ValueError(f"{field} must be a lowercase SHA-256 digest")
    return value


def validate_seeds(value: Any) -> dict[str, str]:
    if not isinstance(value, dict) or set(value) != set(SEED_NAMES):
        raise ValueError(f"seed keys must be exactly {SEED_NAMES}")
    seeds: dict[str, str] = {}
    for name in SEED_NAMES:
        seed = validate_digest(value[name], f"seed {name}")
        if seed == "0" * 64:
            raise ValueError(f"seed {name} must not be zero")
        seeds[name] = seed
    if len(set(seeds.values())) != len(seeds):
        raise ValueError("randomization seeds must be distinct")
    return seeds


def validate_packages(value: Any) -> dict[str, dict[str, str] | None]:
    """Validate a declaration's shape only; this DRAFT cannot authenticate bytes."""
    if (
        not isinstance(value, dict)
        or value.get("schema_version") != 1
        or value.get("status") != "READY"
        or set(value) != {"schema_version", "status", "packages"}
        or not isinstance(value.get("packages"), dict)
    ):
        raise ValueError("packages.json must be a READY schema-v1 envelope")
    packages = value["packages"]
    if set(packages) != set(CONDITIONS) or packages.get("no_skill") is not None:
        raise ValueError("packages must contain v5/v4 and literal no_skill: null")
    result: dict[str, dict[str, str] | None] = {"no_skill": None}
    for role in ("v5", "v4"):
        package = packages[role]
        if not isinstance(package, dict) or set(package) != {
            "source_path",
            "byte_tree_sha256",
            "skill_sha256",
        }:
            raise ValueError(f"invalid package record for {role}")
        result[role] = {
            "source_path": require_relative_path(package["source_path"], f"{role}.source_path"),
            "byte_tree_sha256": validate_digest(
                package["byte_tree_sha256"], f"{role}.byte_tree_sha256"
            ),
            "skill_sha256": validate_digest(package["skill_sha256"], f"{role}.skill_sha256"),
        }
    return result


def validate_targets(value: Any) -> dict[str, dict[str, Any]]:
    """Validate a declaration's shape only; source-tree recomputation is a blocking hook."""
    if (
        not isinstance(value, dict)
        or value.get("schema_version") != 1
        or value.get("status") != "READY"
        or set(value) != {"schema_version", "status", "targets"}
        or not isinstance(value.get("targets"), list)
    ):
        raise ValueError("targets.json must be a READY schema-v1 envelope")
    targets: dict[str, dict[str, Any]] = {}
    required = {
        "mode",
        "fixture_id",
        "task_mode",
        "prompt_regime",
        "source_path",
        "byte_tree_sha256",
        "authority_packet_path",
        "authority_packet_sha256",
        "authority_packet_visibility",
        "word_cap",
    }
    for target in value["targets"]:
        if not isinstance(target, dict) or set(target) != required:
            raise ValueError("target records have unexpected fields")
        mode = target.get("mode")
        if mode not in MODES or mode in targets:
            raise ValueError(f"missing, duplicate, or unknown target mode: {mode!r}")
        if target.get("prompt_regime") != PROMPT_REGIMES[mode]:
            raise ValueError(f"prompt regime mismatch for mode {mode}")
        if target.get("authority_packet_visibility") != "AGENT_VISIBLE_NEUTRAL":
            raise ValueError(f"authority packet visibility mismatch for mode {mode}")
        if target.get("authority_packet_path") != "docs/rust-documentation.json":
            raise ValueError(f"authority packet path mismatch for mode {mode}")
        if not isinstance(target.get("fixture_id"), str) or not re.fullmatch(
            r"[a-z][a-z0-9_-]*", target["fixture_id"]
        ):
            raise ValueError(f"invalid fixture ID for mode {mode}")
        if not isinstance(target.get("task_mode"), str) or not re.fullmatch(
            r"[a-z][a-z0-9_-]*", target["task_mode"]
        ):
            raise ValueError(f"invalid task mode for mode {mode}")
        if type(target.get("word_cap")) is not int or target["word_cap"] < 1:
            raise ValueError(f"invalid word cap for mode {mode}")
        targets[mode] = {
            **target,
            "source_path": require_relative_path(target["source_path"], f"{mode}.source_path"),
            "authority_packet_path": require_relative_path(
                target["authority_packet_path"], f"{mode}.authority_packet_path"
            ),
            "byte_tree_sha256": validate_digest(
                target["byte_tree_sha256"], f"{mode}.byte_tree_sha256"
            ),
            "authority_packet_sha256": validate_digest(
                target["authority_packet_sha256"], f"{mode}.authority_packet_sha256"
            ),
        }
    if set(targets) != set(MODES):
        raise ValueError(f"target modes must be exactly {MODES}")
    if len({target["authority_packet_sha256"] for target in targets.values()}) != 1:
        raise ValueError("every mode must bind the same byte-identical neutral authority packet")
    return targets


def integration_inputs(root: Path) -> tuple[dict[str, Any], dict[str, Any], dict[str, str]]:
    packages = validate_packages(read_json(root / "packages.json"))
    targets = validate_targets(read_json(root / "targets.json"))
    seeds = validate_seeds(read_json(root / "seeds.json"))
    for mode in MODES:
        for path in (
            root / "atoms" / f"{mode}.json",
            root / "oracle" / f"{mode}.md",
            root / "allowlists" / f"{mode}.txt",
        ):
            if not path.is_file() or not path.read_bytes().strip():
                raise ValueError(f"missing or empty integration input: {path}")
    return packages, targets, seeds


def generated_documents(
    packages: dict[str, Any],
    targets: dict[str, dict[str, Any]],
    seeds: dict[str, str],
    *,
    status: str = "DRAFT-GENERATED-UNVERIFIED",
) -> dict[str, Any]:
    if status not in ("DRAFT-GENERATED-UNVERIFIED", "READY"):
        raise ValueError("generated document status must be DRAFT-GENERATED-UNVERIFIED or READY")
    condition_order = sorted(
        CONDITIONS,
        key=lambda role: (keyed("condition-v5-diagnostic-v1", seeds["condition"], role), role),
    )
    condition_labels = {role: f"c{index}" for index, role in enumerate(condition_order)}
    condition_map = {
        "schema_version": 1,
        "status": status,
        "conditions": [
            {
                "condition_label": condition_labels[role],
                "role": role,
                "package": packages[role],
            }
            for role in condition_order
        ],
    }

    mode_order = sorted(
        MODES,
        key=lambda mode: (keyed("mode-v5-diagnostic-v1", seeds["schedule"], mode), mode),
    )
    mode_labels = {mode: f"m{index}" for index, mode in enumerate(mode_order)}
    target_map = {
        "schema_version": 1,
        "status": status,
        "targets": [
            {"target_label": mode_labels[mode], **targets[mode]} for mode in mode_order
        ],
    }

    wave_order = sorted(
        REPLICATES,
        key=lambda rep: (keyed("wave-v5-diagnostic-v1", seeds["schedule"], str(rep)), rep),
    )
    schedule: list[dict[str, Any]] = []
    run_number = 1
    for wave, replicate in enumerate(wave_order, start=1):
        cells = [(mode, role) for mode in MODES for role in CONDITIONS]
        cells.sort(
            key=lambda cell: (
                keyed(
                    "schedule-v5-diagnostic-v1",
                    seeds["schedule"],
                    f"{cell[0]}|{cell[1]}|{replicate}",
                ),
                cell,
            )
        )
        for mode, role in cells:
            canonical = f"{mode}|{role}|{replicate}"
            schedule.append(
                {
                    "run_id": f"r{run_number:03d}",
                    "cell_id": keyed(
                        "cell-v5-diagnostic-v1", seeds["schedule"], canonical
                    )[:32],
                    "wave": wave,
                    "replicate": replicate,
                    "target_label": mode_labels[mode],
                    "condition_label": condition_labels[role],
                    "prompt_regime": PROMPT_REGIMES[mode],
                }
            )
            run_number += 1
    if len(schedule) != TOTAL_REPORTS or len({row["cell_id"] for row in schedule}) != TOTAL_REPORTS:
        raise AssertionError("generated schedule is incomplete or has duplicate cells")

    labels = opaque_labels(REPORTS_PER_MODE)
    blind_modes: dict[str, list[dict[str, str]]] = {}
    for mode in MODES:
        target_label = mode_labels[mode]
        run_ids = [row["run_id"] for row in schedule if row["target_label"] == target_label]
        run_ids.sort(
            key=lambda run_id: (
                keyed("blind-v5-diagnostic-v1", seeds["blind"], f"{mode}|{run_id}"),
                run_id,
            )
        )
        blind_modes[mode] = [
            {"label": label, "run_id": run_id} for label, run_id in zip(labels, run_ids)
        ]

    presentations: list[dict[str, Any]] = []
    for mode in MODES:
        for scorer in SCORERS:
            ordered = sorted(
                labels,
                key=lambda label: (
                    keyed(
                        "presentation-v5-diagnostic-v1",
                        seeds["presentation"],
                        f"{mode}|{scorer}|{label}",
                    ),
                    label,
                ),
            )
            presentations.append(
                {"claim": f"{mode}-{scorer}", "labels_in_order": ordered}
            )

    scorer_claims = [f"{mode}-{scorer}" for mode in MODES for scorer in SCORERS]
    scorer_claims.sort(
        key=lambda claim: (
            keyed("scorer-v5-diagnostic-v1", seeds["scorer"], claim),
            claim,
        )
    )
    consistency_claims = sorted(
        (f"{mode}-{reviewer}" for mode in MODES for reviewer in CONSISTENCY_REVIEWERS),
        key=lambda claim: (
            keyed("consistency-v5-diagnostic-v1", seeds["consistency"], claim),
            claim,
        ),
    )
    commitments = {
        name: sha256(
            f"{name}-v5-diagnostic-v1".encode() + b"\0" + bytes.fromhex(seed)
        )
        for name, seed in sorted(seeds.items())
    }
    return {
        "condition-map.json": condition_map,
        "target-map.json": target_map,
        "launch-schedule.json": {
            "schema_version": 1,
            "status": status,
            "slots": schedule,
        },
        "blind-map.json": {
            "schema_version": 1,
            "status": status,
            "modes": blind_modes,
        },
        "presentation-orders.json": {
            "schema_version": 1,
            "status": status,
            "presentations": presentations,
        },
        "scoring-schedule.json": {
            "schema_version": 1,
            "status": status,
            "claims": scorer_claims,
        },
        "consistency-schedule.json": {
            "schema_version": 1,
            "status": status,
            "claims": consistency_claims,
        },
        "randomization-commitments.json": {
            "schema_version": 1,
            "status": status,
            "ordering_algorithm": "sha256(tag_utf8 || NUL || seed_bytes || NUL || value_utf8)",
            "commitment_algorithm": "sha256((seed_name + '-v5-diagnostic-v1')_utf8 || NUL || seed_bytes)",
            "commitments": commitments,
        },
    }


def verify_generated(
    documents: dict[str, Any],
    seeds: dict[str, str],
    *,
    expected_status: str = "DRAFT-GENERATED-UNVERIFIED",
) -> None:
    if any(
        document.get("status") != expected_status
        for document in documents.values()
    ):
        raise AssertionError(f"generated documents are not marked {expected_status}")
    conditions = documents["condition-map.json"]["conditions"]
    if len(conditions) != 3 or {row["role"] for row in conditions} != set(CONDITIONS):
        raise AssertionError("condition map is not a three-way comparison")
    no_skill = next(row for row in conditions if row["role"] == "no_skill")
    if no_skill["package"] is not None:
        raise AssertionError("no-skill condition acquired a package")
    targets = documents["target-map.json"]["targets"]
    if len(targets) != len(MODES) or {row["mode"] for row in targets} != set(MODES):
        raise AssertionError("target map mode set mismatch")
    slots = documents["launch-schedule.json"]["slots"]
    if len(slots) != TOTAL_REPORTS:
        raise AssertionError("schedule report count mismatch")
    expected_run_ids = {f"r{index:03d}" for index in range(1, TOTAL_REPORTS + 1)}
    if (
        {row["run_id"] for row in slots} != expected_run_ids
        or len({row["cell_id"] for row in slots}) != TOTAL_REPORTS
    ):
        raise AssertionError("schedule run/cell IDs are not exact unique bijections")
    condition_by_label = {
        row["condition_label"]: row["role"] for row in conditions
    }
    mode_by_label = {row["target_label"]: row["mode"] for row in targets}
    if len(condition_by_label) != len(CONDITIONS) or len(mode_by_label) != len(MODES):
        raise AssertionError("condition/target labels are not unique")
    try:
        coverage = {
            (
                mode_by_label[row["target_label"]],
                condition_by_label[row["condition_label"]],
                row["replicate"],
            )
            for row in slots
        }
    except KeyError as error:
        raise AssertionError("schedule references an unknown target/condition label") from error
    expected_coverage = {
        (mode, condition, replicate)
        for mode in MODES
        for condition in CONDITIONS
        for replicate in REPLICATES
    }
    if coverage != expected_coverage or len(coverage) != TOTAL_REPORTS:
        raise AssertionError("schedule is not an exact 8x3x5 cell bijection")
    for wave in REPLICATES:
        wave_rows = [row for row in slots if row["wave"] == wave]
        if len(wave_rows) != len(MODES) * len(CONDITIONS):
            raise AssertionError(f"wave {wave} is not 24-cell balanced")
        wave_cells = {
            (
                mode_by_label[row["target_label"]],
                condition_by_label[row["condition_label"]],
            )
            for row in wave_rows
        }
        if wave_cells != {(mode, condition) for mode in MODES for condition in CONDITIONS}:
            raise AssertionError(f"wave {wave} lacks exact mode/condition balance")
        if len({row["replicate"] for row in wave_rows}) != 1:
            raise AssertionError(f"wave {wave} mixes replicate identities")
    by_target: dict[str, int] = {}
    for slot in slots:
        by_target[slot["target_label"]] = by_target.get(slot["target_label"], 0) + 1
    if set(by_target.values()) != {REPORTS_PER_MODE}:
        raise AssertionError("mode report counts are not dynamically 15")
    for mode, rows in documents["blind-map.json"]["modes"].items():
        if mode not in MODES or len(rows) != REPORTS_PER_MODE:
            raise AssertionError("blind map count mismatch")
        if {row["label"] for row in rows} != set(opaque_labels(REPORTS_PER_MODE)):
            raise AssertionError("blind labels are incomplete")
    blind_run_ids = [
        row["run_id"]
        for rows in documents["blind-map.json"]["modes"].values()
        for row in rows
    ]
    if len(blind_run_ids) != TOTAL_REPORTS or set(blind_run_ids) != expected_run_ids:
        raise AssertionError("blind map is not a run-ID bijection")
    presentations = documents["presentation-orders.json"]["presentations"]
    expected_claims = {f"{mode}-{scorer}" for mode in MODES for scorer in SCORERS}
    if (
        len(presentations) != len(expected_claims)
        or {row["claim"] for row in presentations} != expected_claims
        or any(
            len(row["labels_in_order"]) != REPORTS_PER_MODE
            or set(row["labels_in_order"]) != set(opaque_labels(REPORTS_PER_MODE))
            for row in presentations
        )
    ):
        raise AssertionError("presentation topology is not 16 mode-level A-O scorer packets")
    scoring_claims = documents["scoring-schedule.json"]["claims"]
    if len(scoring_claims) != 16 or set(scoring_claims) != expected_claims:
        raise AssertionError("scoring topology must contain exactly 16 mode-level scorers")
    consistency_claims = documents["consistency-schedule.json"]["claims"]
    expected_consistency = {
        f"{mode}-{reviewer}" for mode in MODES for reviewer in CONSISTENCY_REVIEWERS
    }
    if len(consistency_claims) != 16 or set(consistency_claims) != expected_consistency:
        raise AssertionError("consistency topology must contain two independent reviewers per mode")
    expected_commitments = {
        name: sha256(
            f"{name}-v5-diagnostic-v1".encode() + b"\0" + bytes.fromhex(seed)
        )
        for name, seed in sorted(seeds.items())
    }
    if documents["randomization-commitments.json"]["commitments"] != expected_commitments:
        raise AssertionError("randomization commitments fail recomputation")
    declared_packages = {row["role"]: row["package"] for row in conditions}
    declared_targets = {
        row["mode"]: {key: item for key, item in row.items() if key != "target_label"}
        for row in targets
    }
    regenerated = generated_documents(
        declared_packages, declared_targets, seeds, status=expected_status
    )
    if json_dump(documents) != json_dump(regenerated):
        raise AssertionError(
            "generated maps/schedules are not byte-identical to exact deterministic regeneration"
        )


def verify_draft() -> None:
    if tuple(PROMPT_REGIMES) != MODES:
        raise AssertionError("prompt-regime inventory is not ordered with modes")
    if REPORTS_PER_MODE != 15 or TOTAL_REPORTS != 120:
        raise AssertionError("DRAFT design must have 15 reports/mode and 120 total")
    plan = (RUN / "plan.md").read_text(encoding="utf-8")
    if "**Status: DRAFT / UNSEALED.**" not in plan:
        raise AssertionError("plan is not conspicuously DRAFT / UNSEALED")
    for regime, path in REPORT_PROMPTS.items():
        template = path.read_text(encoding="utf-8")
        expected_markers = {
            "{{INVOCATION_BLOCK}}",
            "{{INPUT_ROOT}}",
            "{{OUTPUT_ROOT}}",
            "{{TARGET_PATH}}",
            "{{AUTHORITY_PATH}}",
            "{{TASK_MODE}}",
            "{{OUTPUT_PATH}}",
            "{{WORD_CAP}}",
        }
        for marker in expected_markers:
            if template.count(marker) != 1:
                raise AssertionError(
                    f"{regime} report template must have exactly one {marker} marker"
                )
        found_markers = set(re.findall(r"\{\{[A-Z0-9_]+\}\}", template))
        if found_markers != expected_markers:
            raise AssertionError(f"{regime} report template marker set drifted")
        visible = template.replace("{{INVOCATION_BLOCK}}", "").lower()
        contaminated = [
            term
            for term in (
                "no_skill",
                "no-skill",
                "v4",
                "v5",
                "blind",
                "sibling",
                "evaluation",
                "evaluator",
                "experiment",
                "experimental",
                "treatment",
                "instruction package",
                "package identity",
                "skill",
                "mount",
                "report-agent",
                "condition-bearing",
            )
            if term in visible
        ]
        if contaminated:
            raise AssertionError(
                f"{regime} report template leaks evaluator/treatment design: {contaminated}"
            )
        if template.count(OPERATIONAL_BLOCK) != 1:
            raise AssertionError(
                f"{regime} report template does not contain the identical operational block"
            )
    forbidden = (
        "STATIC-LOCK.json",
        "STATIC-MANIFEST.sha256",
        "LOCK.json",
        "file-manifest.sha256",
        "events.jsonl",
        "unblinding.json",
        "collection",
        "scoring",
        "results",
        "sealed",
    )
    present = [name for name in forbidden if (RUN / name).exists()]
    if present:
        raise AssertionError(f"DRAFT contains forbidden frozen/evidence artifacts: {present}")
    print("DRAFT preparation design validation passed")


def self_test() -> None:
    verify_draft()
    for bad in (b'{"x":1,"x":2}', b'{"x":NaN}', b'\xff'):
        try:
            parse_json_bytes(bad, "synthetic-invalid")
        except ValueError:
            pass
        else:
            raise AssertionError("strict JSON parser accepted invalid input")
    for bad_path in ("../escape", "line\nbreak", "nonascii-µ", ".hidden", "a//b"):
        try:
            portable_relative_path(bad_path, "synthetic invalid path")
        except ValueError:
            pass
        else:
            raise AssertionError(
                f"portable path domain accepted an invalid path: {bad_path!r}"
            )
    packages = {
        "v5": {
            "source_path": "synthetic/v5",
            "byte_tree_sha256": "1" * 64,
            "skill_sha256": "2" * 64,
        },
        "v4": {
            "source_path": "synthetic/v4",
            "byte_tree_sha256": "3" * 64,
            "skill_sha256": "4" * 64,
        },
        "no_skill": None,
    }
    targets = {
        mode: {
            "mode": mode,
            "fixture_id": f"synthetic_{mode.lower()}",
            "task_mode": "synthetic_test_only",
            "prompt_regime": PROMPT_REGIMES[mode],
            "source_path": f"synthetic/{mode.lower()}",
            "byte_tree_sha256": sha256(f"synthetic-{mode}".encode()),
            "authority_packet_path": "docs/rust-documentation.json",
            "authority_packet_sha256": sha256(b"synthetic-common-authority"),
            "authority_packet_visibility": "AGENT_VISIBLE_NEUTRAL",
            "word_cap": 1000,
        }
        for mode in MODES
    }
    seeds = {
        name: sha256(f"synthetic-test-only-{name}".encode()) for name in SEED_NAMES
    }
    documents = generated_documents(packages, targets, seeds)
    verify_generated(documents, seeds)
    commitment_document = documents["randomization-commitments.json"]
    if commitment_document["ordering_algorithm"] != (
        "sha256(tag_utf8 || NUL || seed_bytes || NUL || value_utf8)"
    ) or commitment_document["commitment_algorithm"] != (
        "sha256((seed_name + '-v5-diagnostic-v1')_utf8 || NUL || seed_bytes)"
    ):
        raise AssertionError("published randomization algorithm descriptions drifted")
    expected_commitments = {
        name: sha256(
            f"{name}-v5-diagnostic-v1".encode() + b"\0" + bytes.fromhex(seed)
        )
        for name, seed in sorted(seeds.items())
    }
    if commitment_document["commitments"] != expected_commitments:
        raise AssertionError("seed commitments do not match the declared formula")
    for regime in REPORT_PROMPTS:
        baseline = render_report_prompt(
            regime,
            invocation_block="",
            input_root=INPUT_ALIAS,
            output_root=OUTPUT_ALIAS,
            target_path="target/REQUEST.md",
            authority_path="docs/rust-documentation.json",
            task_mode="synthetic_test_only",
            output_path="report.md",
            word_cap=1000,
        )
        invocation = "Follow the package-specific audit instructions."
        treatment = render_report_prompt(
            regime,
            invocation_block=invocation,
            input_root=INPUT_ALIAS,
            output_root=OUTPUT_ALIAS,
            target_path="target/REQUEST.md",
            authority_path="docs/rust-documentation.json",
            task_mode="synthetic_test_only",
            output_path="report.md",
            word_cap=1000,
        )
        if treatment.replace(invocation.encode("utf-8"), b"", 1) != baseline:
            raise AssertionError("treatment rendering changes bytes outside invocation block")
        baseline_lower = baseline.lower()
        if any(term in baseline_lower for term in (b"no_skill", b"no-skill", b"v4", b"v5")):
            raise AssertionError("ordinary no-skill rendering leaks treatment/evaluator language")
    again = generated_documents(packages, targets, seeds)
    if json_dump(documents) != json_dump(again):
        raise AssertionError("generation is not deterministic")
    try:
        write_generated({}, RUN / "forbidden-generated-output")
    except ValueError:
        pass
    else:
        raise AssertionError("generator accepted an output path inside the DRAFT run tree")
    print("DRAFT preparation self-test passed")


def write_generated(documents: dict[str, Any], output: Path) -> None:
    resolved_output = output.resolve()
    if resolved_output == RUN or RUN in resolved_output.parents:
        raise ValueError("generated maps must be written outside the DRAFT run tree")
    if output.exists() and any(output.iterdir()):
        raise FileExistsError(f"generated output directory is not empty: {output}")
    output.mkdir(parents=True, exist_ok=True)
    for name, value in documents.items():
        path = output / name
        with path.open("x", encoding="utf-8", newline="") as file:
            file.write(json_dump(value))


def main() -> None:
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("draft")
    sub.add_parser("verify-draft")
    sub.add_parser("self-test")
    generate = sub.add_parser("generate")
    generate.add_argument("--integration-root", type=Path, required=True)
    generate.add_argument("--output", type=Path, required=True)
    generate.add_argument(
        "--acknowledge-blocking-integrity-hooks",
        action="store_true",
        required=True,
        help="acknowledge that output is DRAFT/UNVERIFIED and cannot launch agents",
    )
    args = parser.parse_args()
    if args.command in ("draft", "verify-draft"):
        verify_draft()
    elif args.command == "self-test":
        self_test()
    else:
        packages, targets, seeds = integration_inputs(args.integration_root)
        documents = generated_documents(packages, targets, seeds)
        verify_generated(documents, seeds)
        write_generated(documents, args.output)
        print(f"wrote {len(documents)} generated DRAFT integration documents")


if __name__ == "__main__":
    main()
