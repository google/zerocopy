#!/usr/bin/env python3
"""Executable DRAFT protocol for V5 diagnostic prequalification.

The protocol deliberately does not turn this shared-filesystem collaboration
environment into an admissible evaluator.  It does provide the strongest
coordinator-side mechanics available here: one exclusive started-attempt
lease, complete envelope capture, and a first-terminal content-addressed
canonical pointer.  The executable gate manifest independently fixes the
isolation and output-finalization roots to FAIL.

All mutable attempt state must be placed under an explicit directory outside
this DRAFT run tree.  Static validation and synthetic self-tests do not create
run artifacts.
"""

from __future__ import annotations

import argparse
import base64
import contextlib
import copy
import fcntl
import hashlib
import json
import os
import re
import runpy
import secrets
import stat
import tempfile
import unicodedata
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path, PurePosixPath
from typing import Any, Iterator


RUN = Path(__file__).resolve().parent
RUNTIME_ROOT = RUN / "runtime"
MODES = ("E", "V", "F", "P", "B", "L", "R", "Q")
LABELS = tuple(chr(ord("A") + index) for index in range(15))
SCORERS = ("s1", "s2")
CONSISTENCY_REVIEWERS = ("c1", "c2")
MATERIALITY_REVIEWERS = ("m1", "m2")
MATERIALITY_SCOPES = (
    "V5_CANDIDATE_REPORTS",
    "CANDIDATE_PACKAGE",
    "HARNESS_PROTOCOL",
    "ADVERSARIAL_AND_COHERENCE_REVIEWS",
)
MATERIALITY_RULE = (
    "BLOCKING_IF_A_SUPPORTED_FINDING_COULD_CHANGE_CANDIDATE_ACCEPTABILITY_"
    "OR_INVALIDATE_HARNESS_INTERPRETATION"
)
NOVEL_CATEGORIES = (
    "VALID_NEW_FINDING",
    "VALID_PROOF_DOCUMENTATION_GAP",
    "DUPLICATE_OR_BROADER_ORACLE_ATOM",
    "UNSUPPORTED_REASONABLE_QUESTION",
    "INVALID_ASSERTION",
    "REQUIRES_UPSTREAM_OR_RUST_DOC_CLARIFICATION",
)
REPORT_SECRET_CATEGORIES = (
    "TREATMENT_INSTRUCTION_OR_PACKAGE_IDENTITY",
    "EVALUATION_CONDITION_IDENTITY",
    "REPORT_AGENT_IDENTITY",
    "CONDITION_BEARING_RUNTIME_IDENTIFIER",
    "EVALUATOR_ONLY_ORACLE_SIBLING_SCORE_METADATA",
)
REPORT_SECRET_MATCH_KINDS = (
    "EXACT_ABSOLUTE_PATH",
    "EXACT_HEX_DIGEST",
    "EXACT_UUID_OR_RUNTIME_ID",
    "EXACT_MULTIWORD_TREATMENT_PHRASE",
)
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
SAFE_ID = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]{0,127}$")
ATOM_ID = re.compile(r"^[EVFPBLRQ][1-9][0-9]*$")
HEX64 = re.compile(r"^[0-9a-f]{64}$")

REQUIRED_ROOT_IDS = {
    "G-ISOLATION",
    "G-OUTPUT-FINALIZATION",
    "D-STATIC-INTEGRITY",
    "D-ORACLE-COVERAGE",
    "D-COLLECTION-COMPLETE",
    "D-OUTPUT-VALID",
    "D-FOCUSED-RECALL",
    "D-PROOF-QUALITY",
    "D-CONTROLS",
    "D-NO-HARD-ERROR",
    "D-NO-GLOBAL-DEFECT",
    "D-NO-MATERIAL-FINDING",
    "D-COMPARISON",
    "D-COHERENCE",
    "D-DIAGNOSTIC-COMPLETION",
}
EXPECTED_INTEGRATION_HOOK_IDS = (
    "H-RECOMPUTE-PACKAGE-TREES",
    "H-VERIFY-SKILL-BYTES",
    "H-RECOMPUTE-TARGET-TREES",
    "H-MATERIALIZE-OPAQUE-TARGETS-AND-SCAN-LEAKAGE",
    "H-VALIDATE-READY-STATUS",
    "H-VALIDATE-CROSS-REFERENCE-CLOSURE",
    "H-VALIDATE-HIDDEN-FIXTURE-MANIFESTS",
    "H-VALIDATE-ORACLE-COVERAGE",
    "H-VALIDATE-INDEPENDENT-SIGNOFFS",
    "H-BUILD-VALIDATE-REPORT-AUTHORITY-PROJECTIONS",
    "H-VALIDATE-PROMPT-RENDERINGS",
    "H-FREEZE-VALIDATE-ENVELOPE-SPECS",
    "H-FREEZE-EXECUTION-ENVIRONMENT-MANIFESTS",
    "H-ENFORCE-WORD-COUNTER",
    "H-BUILD-VALIDATE-SCORER-REPORT-PROJECTIONS",
    "H-GENERATE-VERIFY-RANDOMIZATION",
    "H-VALIDATE-SCHEDULE-LEASE-ATTEMPT-LEDGER",
    "H-SEMANTICALLY-REVALIDATE-ENVELOPES",
    "H-VALIDATE-EVALUATOR-INDEPENDENCE-QUALIFICATION",
    "H-RUN-VALIDATE-MATERIALITY-REVIEWS",
    "H-BUILD-WHOLE-FILE-MANIFEST",
    "H-CREATE-LOCK-LAST",
    "H-DERIVE-AGGREGATE-CONTEXT",
    "H-VALIDATE-AGGREGATION-RULE-INVENTORY",
    "H-BIND-CONTEXT-INPUT-DIGESTS",
)


class ProtocolError(RuntimeError):
    """Base class for fail-closed protocol errors."""


class LeaseAlreadyExists(ProtocolError):
    """A slot already has a started-attempt lease; retry is forbidden."""


class CanonicalAlreadySealed(ProtocolError):
    """A first-terminal canonical envelope already exists for the slot."""


class TerminalAlreadyClaimed(ProtocolError):
    """A seal operation already claimed the attempt's one terminal transition."""


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical_json_bytes(value: Any) -> bytes:
    return (
        json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
        + "\n"
    ).encode("utf-8")


def pretty_json(value: Any) -> str:
    return json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n"


def read_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def require_exact_keys(value: Any, keys: set[str], label: str) -> dict[str, Any]:
    if not isinstance(value, dict) or set(value) != keys:
        actual = sorted(value) if isinstance(value, dict) else type(value).__name__
        raise ProtocolError(f"{label} keys mismatch: {actual!r}")
    return value


def require_safe_id(value: Any, label: str) -> str:
    if not isinstance(value, str) or not SAFE_ID.fullmatch(value):
        raise ProtocolError(f"invalid {label}: {value!r}")
    return value


def require_relative_file(value: Any, label: str) -> str:
    if not isinstance(value, str) or not value or value != value.strip():
        raise ProtocolError(f"{label} must be a nonblank relative POSIX path")
    path = PurePosixPath(value)
    if (
        path.is_absolute()
        or value.endswith("/")
        or any(ord(character) < 32 for character in value)
        or any(part in ("", ".", "..") for part in path.parts)
    ):
        raise ProtocolError(f"invalid {label}: {value!r}")
    return value


def is_within(path: Path, parent: Path) -> bool:
    path = path.resolve()
    parent = parent.resolve()
    return path == parent or parent in path.parents


def require_external_path(path: Path, label: str) -> Path:
    resolved = path.resolve()
    if is_within(resolved, RUN):
        raise ProtocolError(f"DRAFT {label} must be outside the entire run tree: {resolved}")
    return resolved


def fsync_directory(path: Path) -> None:
    fd = os.open(path, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0))
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def fsync_tree(root: Path) -> None:
    directories: list[Path] = []
    for directory, directory_names, file_names in os.walk(root, followlinks=False):
        directory_names.sort()
        file_names.sort()
        directory_path = Path(directory)
        directories.append(directory_path)
        for name in file_names:
            path = directory_path / name
            info = path.lstat()
            if not stat.S_ISREG(info.st_mode):
                raise ProtocolError(f"cannot fsync non-regular envelope entry: {path}")
            fd = os.open(path, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0))
            try:
                os.fsync(fd)
            finally:
                os.close(fd)
    for directory in reversed(directories):
        fsync_directory(directory)


def harden_tree_read_only(root: Path) -> None:
    directories: list[Path] = []
    for directory, directory_names, file_names in os.walk(root, followlinks=False):
        directory_names.sort()
        file_names.sort()
        directory_path = Path(directory)
        directories.append(directory_path)
        for name in file_names:
            path = directory_path / name
            if path.is_symlink() or not path.is_file():
                raise ProtocolError(f"cannot harden unsupported envelope entry: {path}")
            os.chmod(path, 0o400)
    for directory in reversed(directories):
        os.chmod(directory, 0o500)
    fsync_tree(root)


def exclusive_write(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_NOFOLLOW", 0)
    fd = os.open(path, flags, 0o600)
    try:
        view = memoryview(data)
        while view:
            written = os.write(fd, view)
            if written < 1:
                raise OSError("short write")
            view = view[written:]
        os.fsync(fd)
    finally:
        os.close(fd)
    fsync_directory(path.parent)


def write_stage_file(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    exclusive_write(path, data)


@contextlib.contextmanager
def operation_lock(state_root: Path) -> Iterator[None]:
    state_root.mkdir(parents=True, exist_ok=True)
    lock_path = state_root / ".protocol.lock"
    flags = os.O_RDWR | os.O_CREAT | getattr(os, "O_NOFOLLOW", 0)
    fd = os.open(lock_path, flags, 0o600)
    try:
        fcntl.flock(fd, fcntl.LOCK_EX)
        yield
    finally:
        fcntl.flock(fd, fcntl.LOCK_UN)
        os.close(fd)


def byte_tree_digest(root: Path) -> str:
    """Hash every regular file with unambiguous path/length framing."""

    hasher = hashlib.sha256()
    files: list[Path] = []
    for directory, directory_names, file_names in os.walk(root, followlinks=False):
        directory_names.sort()
        file_names.sort()
        directory_path = Path(directory)
        for name in directory_names:
            path = directory_path / name
            if path.is_symlink():
                raise ProtocolError(f"symlink in immutable envelope: {path}")
        for name in file_names:
            path = directory_path / name
            info = path.lstat()
            if not stat.S_ISREG(info.st_mode):
                raise ProtocolError(f"non-regular file in immutable envelope: {path}")
            files.append(path)
    for path in sorted(files, key=lambda item: item.relative_to(root).as_posix()):
        relative = path.relative_to(root).as_posix().encode("utf-8")
        data = path.read_bytes()
        hasher.update(b"file\0")
        hasher.update(len(relative).to_bytes(8, "big"))
        hasher.update(relative)
        hasher.update(len(data).to_bytes(8, "big"))
        hasher.update(data)
    return hasher.hexdigest()


def topological_order(nodes: list[str], prerequisites: dict[str, list[str]], label: str) -> list[str]:
    node_set = set(nodes)
    if len(node_set) != len(nodes):
        raise ProtocolError(f"duplicate {label} ID")
    for node in nodes:
        dependencies = prerequisites[node]
        if len(set(dependencies)) != len(dependencies):
            raise ProtocolError(f"duplicate prerequisite for {label} {node}")
        unknown = set(dependencies) - node_set
        if unknown:
            raise ProtocolError(f"unknown prerequisite(s) for {label} {node}: {sorted(unknown)}")
        if node in dependencies:
            raise ProtocolError(f"self-cycle for {label} {node}")
    state: dict[str, int] = {}
    order: list[str] = []

    def visit(node: str) -> None:
        marker = state.get(node, 0)
        if marker == 1:
            raise ProtocolError(f"cycle in {label} DAG at {node}")
        if marker == 2:
            return
        state[node] = 1
        for dependency in prerequisites[node]:
            visit(dependency)
        state[node] = 2
        order.append(node)

    for node in nodes:
        visit(node)
    return order


def validate_atom_manifest(value: Any, expected_mode: str | None = None) -> dict[str, Any]:
    manifest = require_exact_keys(
        value, {"schema_version", "status", "mode", "atoms"}, "atom manifest"
    )
    if manifest["schema_version"] != 1 or manifest["status"] not in ("DRAFT", "READY"):
        raise ProtocolError("atom manifest must be schema-v1 DRAFT or READY")
    mode = manifest["mode"]
    if mode not in MODES or (expected_mode is not None and mode != expected_mode):
        raise ProtocolError(f"atom manifest mode mismatch: {mode!r}")
    if not isinstance(manifest["atoms"], list) or not manifest["atoms"]:
        raise ProtocolError(f"mode {mode} atom manifest must be nonempty")
    atoms: list[dict[str, Any]] = []
    for index, raw in enumerate(manifest["atoms"]):
        atom = require_exact_keys(
            raw,
            {
                "id",
                "direct_criterion",
                "prerequisites",
                "authority_dependencies",
                "applicability",
            },
            f"atom {index}",
        )
        atom_id = atom["id"]
        if not isinstance(atom_id, str) or not ATOM_ID.fullmatch(atom_id) or not atom_id.startswith(mode):
            raise ProtocolError(f"invalid atom ID for mode {mode}: {atom_id!r}")
        if (
            not isinstance(atom["direct_criterion"], str)
            or not atom["direct_criterion"].strip()
            or atom["direct_criterion"] != atom["direct_criterion"].strip()
        ):
            raise ProtocolError(f"atom {atom_id} has invalid direct criterion")
        if atom["applicability"] != "REQUIRED":
            raise ProtocolError(f"atom {atom_id} must have REQUIRED applicability")
        for field in ("prerequisites", "authority_dependencies"):
            if not isinstance(atom[field], list) or any(
                not isinstance(item, str) or not item for item in atom[field]
            ):
                raise ProtocolError(f"atom {atom_id} has invalid {field}")
            if len(set(atom[field])) != len(atom[field]):
                raise ProtocolError(f"atom {atom_id} has duplicate {field}")
        atoms.append(atom)
    ids = [atom["id"] for atom in atoms]
    prerequisites = {atom["id"]: atom["prerequisites"] for atom in atoms}
    topological_order(ids, prerequisites, f"mode {mode} atom")
    return manifest


def compute_atom_certificates(manifest: dict[str, Any], direct: dict[str, str]) -> dict[str, Any]:
    manifest = validate_atom_manifest(manifest)
    atoms = manifest["atoms"]
    ids = [atom["id"] for atom in atoms]
    if not isinstance(direct, dict) or set(direct) != set(ids):
        raise ProtocolError("direct atom decision set must exactly equal the manifest atom set")
    if any(outcome not in ("PASS", "FAIL") for outcome in direct.values()):
        raise ProtocolError("direct atom decisions must be PASS or FAIL")
    prerequisites = {atom["id"]: atom["prerequisites"] for atom in atoms}
    order = topological_order(ids, prerequisites, "atom")
    results: dict[str, dict[str, Any]] = {}
    for atom_id in order:
        blocked = [
            dependency
            for dependency in prerequisites[atom_id]
            if results[dependency]["certificate_decision"] != "PASS"
        ]
        roots: set[str] = set()
        if direct[atom_id] == "FAIL":
            roots.add(atom_id)
        for dependency in blocked:
            roots.update(results[dependency]["root_failures"])
        results[atom_id] = {
            "id": atom_id,
            "direct_decision": direct[atom_id],
            "blocked_by": blocked,
            "certificate_decision": (
                "PASS" if direct[atom_id] == "PASS" and not blocked else "FAIL"
            ),
            "root_failures": sorted(roots),
        }
    return {
        "schema_version": 1,
        "status": "DRAFT-COMPUTED",
        "mode": manifest["mode"],
        "atoms": [results[atom_id] for atom_id in ids],
    }


def validate_rule_records(
    records: Any, pattern: re.Pattern[str], label: str, mode: str | None = None
) -> list[dict[str, str]]:
    if not isinstance(records, list):
        raise ProtocolError(f"{label} must be a list")
    validated: list[dict[str, str]] = []
    for index, raw in enumerate(records):
        record = require_exact_keys(raw, {"id", "criterion"}, f"{label} {index}")
        rule_id = record["id"]
        if not isinstance(rule_id, str) or not pattern.fullmatch(rule_id):
            raise ProtocolError(f"invalid {label} ID: {rule_id!r}")
        if mode is not None and not rule_id.startswith(f"{mode}H"):
            raise ProtocolError(f"{label} ID has wrong mode prefix: {rule_id}")
        if not isinstance(record["criterion"], str) or not record["criterion"].strip():
            raise ProtocolError(f"blank criterion for {label} {rule_id}")
        validated.append(record)
    ids = [record["id"] for record in validated]
    if len(ids) != len(set(ids)):
        raise ProtocolError(f"duplicate IDs in {label}")
    return validated


def validate_defect_rules(value: Any) -> dict[str, Any]:
    rules = require_exact_keys(
        value,
        {
            "schema_version",
            "status",
            "common_hard_errors",
            "global_defects",
            "modes",
            "novel_findings",
        },
        "defect-rule inventory",
    )
    if rules["schema_version"] != 1 or rules["status"] not in ("DRAFT", "READY"):
        raise ProtocolError("defect-rule inventory must be schema-v1 DRAFT or READY")
    common = validate_rule_records(
        rules["common_hard_errors"], re.compile(r"^GH[1-9][0-9]*$"), "common hard error"
    )
    global_defects = validate_rule_records(
        rules["global_defects"], re.compile(r"^GD[1-9][0-9]*$"), "global defect"
    )
    if not common or not global_defects:
        raise ProtocolError("common hard-error and global-defect inventories must be nonempty")
    if not isinstance(rules["modes"], dict) or set(rules["modes"]) != set(MODES):
        raise ProtocolError("defect-rule mode set mismatch")
    all_ids = [record["id"] for record in common + global_defects]
    for mode in MODES:
        envelope = require_exact_keys(
            rules["modes"][mode], {"hard_errors"}, f"mode {mode} defect rules"
        )
        records = validate_rule_records(
            envelope["hard_errors"],
            re.compile(r"^[EVFPBLRQ]H[1-9][0-9]*$"),
            f"mode {mode} hard error",
            mode,
        )
        if not records:
            raise ProtocolError(f"mode {mode} hard-error inventory must be nonempty")
        all_ids.extend(record["id"] for record in records)
    if len(all_ids) != len(set(all_ids)):
        raise ProtocolError("defect-rule IDs are not globally unique")
    novel = require_exact_keys(
        rules["novel_findings"], {"id_pattern", "routing"}, "novel-finding rule"
    )
    if (
        novel["id_pattern"] != r"^s[12]-N[1-9][0-9]*$"
        or novel["routing"] != "MANDATORY_ADJUDICATION"
    ):
        raise ProtocolError("novel findings must use stable scoped IDs and mandatory adjudication")
    return rules


def hard_error_ids(rules: dict[str, Any], mode: str) -> list[str]:
    rules = validate_defect_rules(rules)
    return [record["id"] for record in rules["common_hard_errors"]] + [
        record["id"] for record in rules["modes"][mode]["hard_errors"]
    ]


def global_defect_ids(rules: dict[str, Any]) -> list[str]:
    rules = validate_defect_rules(rules)
    return [record["id"] for record in rules["global_defects"]]


def require_labels(value: Any, label: str) -> list[str]:
    if not isinstance(value, list) or len(value) != len(LABELS) or set(value) != set(LABELS):
        raise ProtocolError(f"{label} must contain every opaque label A-O exactly once")
    if len(set(value)) != len(value):
        raise ProtocolError(f"{label} contains duplicate labels")
    return value


def validate_evidence(value: Any, label: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise ProtocolError(f"{label} evidence must be nonblank")
    return value


def expected_report_projection_contract() -> dict[str, Any]:
    return {
        "schema_version": 1,
        "status": "DRAFT",
        "algorithm_id": "finite-secret-byte-projection-v1",
        "secret_categories": list(REPORT_SECRET_CATEGORIES),
        "matching": "PROVENANCE_TYPED_EXACT_TOKENS_LONGEST_FIRST_LEFT_TO_RIGHT",
        "allowed_match_kinds": list(REPORT_SECRET_MATCH_KINDS),
        "minimum_token_bytes": 12,
        "forbidden_generic_tokens": ["v5", "v4", "no_skill", "condition"],
        "placeholder_format": "[REDACTED:NOMINAL]",
        "scorer_receipt_fields": [
            "projected_report_sha256",
            "redaction_present",
            "replacement_count",
        ],
        "evaluator_audit_receipt_fields": [
            "raw_report_sha256",
            "projected_report_sha256",
            "category",
            "offset",
            "length",
            "secret_sha256",
            "placeholder",
        ],
        "raw_report_policy": "SEALED_EVALUATOR_RESTRICTED",
        "scorer_visible_policy": "PROJECTED_REPORT_PLUS_VALUE_FREE_RECEIPT",
        "gh12_policy": "FORCE_PRESENT_IFF_RECEIPT_REDACTION_PRESENT",
        "broad_regex_redaction_forbidden": True,
        "ordinary_target_paths_and_source_names_preserved": True,
        "generic_technical_condition_word_preserved": True,
        "protected_target_values_must_not_match": True,
        "style_inference_limitation_gate": "G-ISOLATION",
    }


def validate_report_projection_contract(value: Any) -> dict[str, Any]:
    if value != expected_report_projection_contract():
        raise ProtocolError("report projection contract is not the exact frozen DRAFT contract")
    return value


def project_report_for_scorer(
    label: str, raw_report: bytes, secrets_inventory: dict[str, Any]
) -> tuple[bytes, dict[str, Any], dict[str, Any]]:
    if label not in LABELS or not isinstance(raw_report, bytes):
        raise ProtocolError("report projection label/raw bytes are invalid")
    inventory = require_exact_keys(
        secrets_inventory,
        {"schema_version", "status", "tokens", "protected_target_values"},
        "report projection secret inventory",
    )
    if inventory["schema_version"] != 1 or inventory["status"] != "READY":
        raise ProtocolError("report projection secret inventory must be schema-v1 READY")
    if not isinstance(inventory["tokens"], list) or not isinstance(
        inventory["protected_target_values"], list
    ):
        raise ProtocolError("report projection token/protected sets must be lists")
    protected_values = inventory["protected_target_values"]
    if (
        any(not isinstance(value, str) or not value for value in protected_values)
        or len(protected_values) != len(set(protected_values))
    ):
        raise ProtocolError("protected target values must be unique nonempty strings")
    protected_bytes = [value.encode("utf-8") for value in protected_values]
    secrets_by_bytes: dict[bytes, str] = {}
    for raw in inventory["tokens"]:
        secret = require_exact_keys(
            raw,
            {"category", "value", "provenance", "match_kind"},
            "report projection secret",
        )
        if secret["category"] not in REPORT_SECRET_CATEGORIES:
            raise ProtocolError("report projection secret category is not frozen")
        if secret["match_kind"] not in REPORT_SECRET_MATCH_KINDS:
            raise ProtocolError("report projection secret match kind is not frozen")
        if not isinstance(secret["provenance"], str) or not secret["provenance"].strip():
            raise ProtocolError("report projection secret lacks provenance")
        if not isinstance(secret["value"], str):
            raise ProtocolError("report projection secret value must be UTF-8")
        encoded = secret["value"].encode("utf-8")
        if len(encoded) < 12 or secret["value"].casefold() in {
            "v5",
            "v4",
            "no_skill",
            "condition",
        }:
            raise ProtocolError("report projection rejects short/generic nominal tokens")
        kind = secret["match_kind"]
        if kind == "EXACT_ABSOLUTE_PATH" and not Path(secret["value"]).is_absolute():
            raise ProtocolError("absolute-path projection token is not absolute")
        if kind == "EXACT_HEX_DIGEST" and re.fullmatch(r"[0-9a-f]{64}", secret["value"]) is None:
            raise ProtocolError("digest projection token is not lowercase SHA-256")
        if kind == "EXACT_UUID_OR_RUNTIME_ID" and re.fullmatch(
            r"(?=.*[-_:])(?=.*[0-9])[A-Za-z0-9._:-]{16,}", secret["value"]
        ) is None:
            raise ProtocolError("runtime-ID projection token lacks a long typed shape")
        if kind == "EXACT_MULTIWORD_TREATMENT_PHRASE" and (
            len(encoded) < 16 or not any(character.isspace() for character in secret["value"])
        ):
            raise ProtocolError("treatment-phrase token must be a long multiword phrase")
        if any(encoded in protected or protected in encoded for protected in protected_bytes):
            raise ProtocolError("secret token collides with a protected target/source value")
        prior = secrets_by_bytes.get(encoded)
        if prior is not None and prior != secret["category"]:
            raise ProtocolError("one exact secret token has conflicting categories")
        secrets_by_bytes[encoded] = secret["category"]
    ordered = sorted(
        secrets_by_bytes.items(), key=lambda item: (-len(item[0]), item[0], item[1])
    )
    projected = bytearray()
    replacements: list[dict[str, Any]] = []
    offset = 0
    while offset < len(raw_report):
        match = next(
            (
                (secret_bytes, category)
                for secret_bytes, category in ordered
                if raw_report.startswith(secret_bytes, offset)
            ),
            None,
        )
        if match is None:
            projected.append(raw_report[offset])
            offset += 1
            continue
        secret_bytes, category = match
        placeholder = "[REDACTED:NOMINAL]"
        projected.extend(placeholder.encode("utf-8"))
        replacements.append(
            {
                "category": category,
                "offset": offset,
                "length": len(secret_bytes),
                "secret_sha256": sha256(secret_bytes),
                "placeholder": placeholder,
            }
        )
        offset += len(secret_bytes)
    projected_bytes = bytes(projected)
    if any(secret_bytes in projected_bytes for secret_bytes in secrets_by_bytes):
        raise ProtocolError("a frozen exact secret token survives or collides with a placeholder")
    scorer_receipt = {
        "schema_version": 1,
        "status": "PROJECTED",
        "label": label,
        "projected_report_sha256": sha256(projected_bytes),
        "redaction_present": bool(replacements),
        "replacement_count": len(replacements),
    }
    evaluator_audit_receipt = {
        "schema_version": 1,
        "status": "EVALUATOR-ONLY-AUDIT",
        "label": label,
        "raw_report_sha256": sha256(raw_report),
        "projected_report_sha256": sha256(projected_bytes),
        "replacements": replacements,
    }
    return projected_bytes, scorer_receipt, evaluator_audit_receipt


def validate_score_input_packet(value: Any, expected_mode: str, expected_scorer: str) -> dict[str, Any]:
    packet = require_exact_keys(
        value,
        {
            "schema_version",
            "status",
            "mode",
            "scorer_id",
            "input_digests",
            "labels_in_order",
            "reports",
        },
        "score input packet",
    )
    if (
        packet["schema_version"] != 1
        or packet["status"] != "SCORER-INPUT-PACKET"
        or packet["mode"] != expected_mode
        or packet["scorer_id"] != expected_scorer
    ):
        raise ProtocolError("score input packet identity/status mismatch")
    digests = require_exact_keys(
        packet["input_digests"],
        {
            "projection_bundle_sha256",
            "atom_manifest_sha256",
            "defect_rules_sha256",
            "oracle_sha256",
            "allowlist_sha256",
            "evaluator_authority_sha256",
            "presentation_order_sha256",
        },
        "score input packet digests",
    )
    if any(not isinstance(item, str) or not HEX64.fullmatch(item) for item in digests.values()):
        raise ProtocolError("score input packet digest is invalid")
    labels = require_labels(packet["labels_in_order"], "score input presentation order")
    if not isinstance(packet["reports"], list):
        raise ProtocolError("score input packet reports must be a list")
    report_labels: list[str] = []
    for raw in packet["reports"]:
        report = require_exact_keys(
            raw,
            {
                "label",
                "projected_report_sha256",
                "leakage_receipt_sha256",
                "gh12_forced_present",
            },
            "score input projected report",
        )
        if report["label"] not in LABELS or type(report["gh12_forced_present"]) is not bool:
            raise ProtocolError("score input projected report identity/flag is invalid")
        for field in ("projected_report_sha256", "leakage_receipt_sha256"):
            if not isinstance(report[field], str) or not HEX64.fullmatch(report[field]):
                raise ProtocolError("score input projected report digest is invalid")
        report_labels.append(report["label"])
    if report_labels != labels:
        raise ProtocolError("score input reports must exactly follow the frozen presentation order")
    return packet


def validate_direct_score(
    value: Any,
    atom_manifest: dict[str, Any],
    defect_rules: dict[str, Any],
    expected_scorer: str | None = None,
    input_packet: dict[str, Any] | None = None,
) -> dict[str, Any]:
    manifest = validate_atom_manifest(atom_manifest)
    rules = validate_defect_rules(defect_rules)
    score = require_exact_keys(
        value,
        {
            "schema_version",
            "status",
            "mode",
            "scorer_id",
            "claim",
            "input_packet_sha256",
            "reports",
        },
        "direct score",
    )
    mode = manifest["mode"]
    scorer = score["scorer_id"]
    if input_packet is None:
        raise ProtocolError("direct score validation requires the exact launch-bound input packet")
    input_packet = validate_score_input_packet(input_packet, mode, scorer)
    input_packet_digest = sha256(canonical_json_bytes(input_packet))
    if (
        input_packet["input_digests"]["atom_manifest_sha256"]
        != sha256(canonical_json_bytes(manifest))
        or input_packet["input_digests"]["defect_rules_sha256"]
        != sha256(canonical_json_bytes(rules))
    ):
        raise ProtocolError("score input packet atom/rule digests do not match actual inputs")
    if (
        score["schema_version"] != 1
        or score["status"] != "DIRECT-SCORE"
        or score["mode"] != mode
        or scorer not in SCORERS
        or (expected_scorer is not None and scorer != expected_scorer)
        or score["claim"] != f"{mode}-{scorer}"
        or score["input_packet_sha256"] != input_packet_digest
    ):
        raise ProtocolError("direct-score identity/status mismatch")
    if not isinstance(score["reports"], list):
        raise ProtocolError("direct-score reports must be a list")
    labels = [report.get("label") for report in score["reports"] if isinstance(report, dict)]
    if labels != input_packet["labels_in_order"]:
        raise ProtocolError("direct-score report order does not match its bound scorer packet")
    atom_ids = [atom["id"] for atom in manifest["atoms"]]
    expected_hard = hard_error_ids(rules, mode)
    expected_global = global_defect_ids(rules)
    novel_ids: list[str] = []
    packet_reports = {item["label"]: item for item in input_packet["reports"]}
    for report in score["reports"]:
        report = require_exact_keys(
            report,
            {"label", "atoms", "hard_errors", "global_defects", "novel_findings"},
            f"score report {report.get('label') if isinstance(report, dict) else '?'}",
        )
        if not isinstance(report["atoms"], list):
            raise ProtocolError("score atom decisions must be a list")
        seen_atoms: list[str] = []
        for raw in report["atoms"]:
            decision = require_exact_keys(raw, {"id", "direct_decision", "evidence"}, "direct atom score")
            if decision["direct_decision"] not in ("PASS", "FAIL"):
                raise ProtocolError("direct atom decision must be PASS or FAIL")
            validate_evidence(decision["evidence"], f"atom {decision['id']}")
            seen_atoms.append(decision["id"])
        if seen_atoms != atom_ids:
            raise ProtocolError(
                f"score {mode}/{report['label']} must list every atom exactly once in manifest order"
            )
        for field, expected in (("hard_errors", expected_hard), ("global_defects", expected_global)):
            records = report[field]
            if not isinstance(records, list):
                raise ProtocolError(f"{field} decisions must be a list")
            seen: list[str] = []
            for raw in records:
                decision = require_exact_keys(raw, {"id", "present", "evidence"}, field)
                if type(decision["present"]) is not bool:
                    raise ProtocolError(f"{field} present must be boolean")
                validate_evidence(decision["evidence"], f"{field} {decision['id']}")
                seen.append(decision["id"])
            if seen != expected:
                raise ProtocolError(
                    f"score {mode}/{report['label']} {field} IDs/order must exactly equal frozen rules"
                )
        if "GH12" in expected_hard:
            gh12 = next(item for item in report["hard_errors"] if item["id"] == "GH12")
            if gh12["present"] is not packet_reports[report["label"]]["gh12_forced_present"]:
                raise ProtocolError("GH12 decision must be mechanically forced by the neutral leak receipt")
        if not isinstance(report["novel_findings"], list):
            raise ProtocolError("novel_findings must be a list")
        for raw in report["novel_findings"]:
            novel = require_exact_keys(raw, {"id", "description", "evidence"}, "novel finding")
            if not isinstance(novel["id"], str) or not re.fullmatch(
                rf"{re.escape(scorer)}-N[1-9][0-9]*", novel["id"]
            ):
                raise ProtocolError("novel finding ID is not stably scoped to its scorer")
            validate_evidence(novel["description"], f"novel {novel['id']} description")
            validate_evidence(novel["evidence"], f"novel {novel['id']}")
            novel_ids.append(novel["id"])
    if len(novel_ids) != len(set(novel_ids)):
        raise ProtocolError("novel finding IDs must be unique across the mode score")
    return score


def atom_and_defect_fields(
    atom_manifest: dict[str, Any], defect_rules: dict[str, Any]
) -> tuple[list[str], list[str]]:
    manifest = validate_atom_manifest(atom_manifest)
    rules = validate_defect_rules(defect_rules)
    mode = manifest["mode"]
    atoms = [f"atom:{atom['id']}" for atom in manifest["atoms"]]
    defects = [f"hard_error:{rule_id}" for rule_id in hard_error_ids(rules, mode)] + [
        f"global_defect:{rule_id}" for rule_id in global_defect_ids(rules)
    ]
    return atoms, defects


def validate_consistency(
    value: Any,
    atom_manifest: dict[str, Any],
    defect_rules: dict[str, Any],
    input_packet: dict[str, Any],
    expected_reviewer: str | None = None,
) -> dict[str, Any]:
    manifest = validate_atom_manifest(atom_manifest)
    input_packet = validate_consistency_packet(input_packet)
    consistency = require_exact_keys(
        value,
        {
            "schema_version",
            "status",
            "mode",
            "reviewer_id",
            "claim",
            "input_packet_sha256",
            "labels_reviewed",
            "atom_family_attestations",
            "defect_family_attestations",
            "challenges",
            "novel_classifications",
        },
        "consistency review",
    )
    if (
        consistency["schema_version"] != 1
        or consistency["status"] != "CONSISTENCY-REVIEW"
        or consistency["mode"] != manifest["mode"]
        or input_packet["mode"] != manifest["mode"]
        or consistency["reviewer_id"] not in CONSISTENCY_REVIEWERS
        or (
            expected_reviewer is not None
            and consistency["reviewer_id"] != expected_reviewer
        )
        or consistency["claim"]
        != f"{manifest['mode']}-{consistency['reviewer_id']}"
        or not isinstance(consistency["input_packet_sha256"], str)
        or consistency["input_packet_sha256"]
        != sha256(canonical_json_bytes(input_packet))
    ):
        raise ProtocolError("consistency identity/status mismatch")
    require_labels(consistency["labels_reviewed"], "consistency labels_reviewed")
    atom_fields, defect_fields = atom_and_defect_fields(manifest, defect_rules)
    for key, expected in (
        ("atom_family_attestations", atom_fields),
        ("defect_family_attestations", defect_fields),
    ):
        records = consistency[key]
        if not isinstance(records, list):
            raise ProtocolError(f"{key} must be a list")
        seen: list[str] = []
        for raw in records:
            attestation = require_exact_keys(
                raw, {"field", "labels_reviewed", "evidence"}, key
            )
            require_labels(attestation["labels_reviewed"], f"{key} {attestation['field']}")
            validate_evidence(attestation["evidence"], f"{key} {attestation['field']}")
            seen.append(attestation["field"])
        if seen != expected:
            raise ProtocolError(f"{key} must attest every frozen family exactly once in order")
    allowed_fields = set(atom_fields + defect_fields)
    challenges = consistency["challenges"]
    if not isinstance(challenges, list):
        raise ProtocolError("consistency challenges must be a list")
    challenge_keys: list[tuple[str, str]] = []
    for raw in challenges:
        challenge = require_exact_keys(
            raw, {"label", "field", "proposed_decision", "evidence"}, "consistency challenge"
        )
        if challenge["label"] not in LABELS or challenge["field"] not in allowed_fields:
            raise ProtocolError("consistency challenge has unknown label or field")
        allowed_decisions = ("PASS", "FAIL") if challenge["field"].startswith("atom:") else (
            "PRESENT",
            "ABSENT",
        )
        if challenge["proposed_decision"] not in allowed_decisions:
            raise ProtocolError("consistency challenge decision type mismatch")
        validate_evidence(challenge["evidence"], "consistency challenge")
        challenge_keys.append((challenge["label"], challenge["field"]))
    if len(challenge_keys) != len(set(challenge_keys)):
        raise ProtocolError("duplicate consistency challenge cell")
    classifications = consistency["novel_classifications"]
    if not isinstance(classifications, list):
        raise ProtocolError("novel classifications must be a list")
    expected_novel_ids = [item["id"] for item in input_packet["novel_assertions"]]
    seen_novel_ids: list[str] = []
    for raw in classifications:
        classification = require_exact_keys(
            raw, {"normalized_id", "category", "evidence"}, "novel classification"
        )
        if classification["normalized_id"] not in expected_novel_ids:
            raise ProtocolError("novel classification references an unknown normalized assertion")
        if classification["category"] not in NOVEL_CATEGORIES:
            raise ProtocolError("novel classification category is not in the frozen six-way set")
        validate_evidence(classification["evidence"], "novel classification")
        seen_novel_ids.append(classification["normalized_id"])
    if seen_novel_ids != expected_novel_ids:
        raise ProtocolError(
            "consistency reviewer must classify every normalized novel assertion exactly once in order"
        )
    return consistency


def report_index(score: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {report["label"]: report for report in score["reports"]}


def normalize_novel_description(value: str) -> str:
    validate_evidence(value, "novel description")
    return " ".join(unicodedata.normalize("NFKC", value).split()).casefold()


def build_consistency_packet(
    first: dict[str, Any],
    second: dict[str, Any],
    first_input_packet: dict[str, Any],
    second_input_packet: dict[str, Any],
    atom_manifest: dict[str, Any],
    defect_rules: dict[str, Any],
    evidence_packet_sha256: str,
) -> dict[str, Any]:
    manifest = validate_atom_manifest(atom_manifest)
    first = validate_direct_score(first, manifest, defect_rules, "s1", first_input_packet)
    second = validate_direct_score(second, manifest, defect_rules, "s2", second_input_packet)
    if not isinstance(evidence_packet_sha256, str) or not HEX64.fullmatch(
        evidence_packet_sha256
    ):
        raise ProtocolError("consistency evidence-packet digest is invalid")
    input_digests = {
        "score_s1_sha256": sha256(canonical_json_bytes(first)),
        "score_s2_sha256": sha256(canonical_json_bytes(second)),
        "atom_manifest_sha256": sha256(canonical_json_bytes(manifest)),
        "defect_rules_sha256": sha256(canonical_json_bytes(validate_defect_rules(defect_rules))),
        "evidence_packet_sha256": evidence_packet_sha256,
    }
    grouped: dict[tuple[str, str], list[dict[str, str]]] = {}
    for score in (first, second):
        for report in score["reports"]:
            for novel in report["novel_findings"]:
                normalized = normalize_novel_description(novel["description"])
                grouped.setdefault((report["label"], normalized), []).append(
                    {
                        "scorer_id": score["scorer_id"],
                        "source_id": novel["id"],
                        "description": novel["description"],
                        "evidence": novel["evidence"],
                    }
                )
    assertions: list[dict[str, Any]] = []
    seen_ids: set[str] = set()
    for (label, normalized), sources in sorted(grouped.items()):
        normalized_id = "N-" + sha256(
            f"v5-diagnostic-novel-v1\0{manifest['mode']}\0{label}\0{normalized}".encode(
                "utf-8"
            )
        )[:24]
        if normalized_id in seen_ids:
            raise ProtocolError("normalized novel assertion ID collision")
        seen_ids.add(normalized_id)
        assertions.append(
            {
                "id": normalized_id,
                "label": label,
                "normalized_description": normalized,
                "sources": sorted(
                    sources, key=lambda item: (item["scorer_id"], item["source_id"])
                ),
            }
        )
    return {
        "schema_version": 1,
        "status": "CONSISTENCY-INPUT-PACKET",
        "mode": manifest["mode"],
        "input_digests": input_digests,
        "binding_sha256": sha256(canonical_json_bytes(input_digests)),
        "novel_assertions": assertions,
    }


def validate_consistency_packet(value: Any) -> dict[str, Any]:
    packet = require_exact_keys(
        value,
        {
            "schema_version",
            "status",
            "mode",
            "input_digests",
            "binding_sha256",
            "novel_assertions",
        },
        "consistency input packet",
    )
    if (
        packet["schema_version"] != 1
        or packet["status"] != "CONSISTENCY-INPUT-PACKET"
        or packet["mode"] not in MODES
    ):
        raise ProtocolError("consistency packet identity/status mismatch")
    digests = require_exact_keys(
        packet["input_digests"],
        {
            "score_s1_sha256",
            "score_s2_sha256",
            "atom_manifest_sha256",
            "defect_rules_sha256",
            "evidence_packet_sha256",
        },
        "consistency packet input digests",
    )
    if any(not isinstance(value, str) or not HEX64.fullmatch(value) for value in digests.values()):
        raise ProtocolError("consistency packet contains an invalid input digest")
    if packet["binding_sha256"] != sha256(canonical_json_bytes(digests)):
        raise ProtocolError("consistency packet binding digest mismatch")
    if not isinstance(packet["novel_assertions"], list):
        raise ProtocolError("consistency packet novel assertions must be a list")
    ids: list[str] = []
    sort_keys: list[tuple[str, str]] = []
    for raw in packet["novel_assertions"]:
        assertion = require_exact_keys(
            raw, {"id", "label", "normalized_description", "sources"}, "novel assertion"
        )
        if not isinstance(assertion["id"], str) or not re.fullmatch(
            r"N-[0-9a-f]{24}", assertion["id"]
        ):
            raise ProtocolError("invalid normalized novel assertion ID")
        if assertion["label"] not in LABELS:
            raise ProtocolError("novel assertion has an invalid label")
        normalized = assertion["normalized_description"]
        if not isinstance(normalized, str) or not normalized or normalized != normalize_novel_description(
            normalized
        ):
            raise ProtocolError("novel assertion description is not normalized")
        if not isinstance(assertion["sources"], list) or not assertion["sources"]:
            raise ProtocolError("novel assertion must preserve at least one source")
        source_keys: list[tuple[str, str]] = []
        for source_raw in assertion["sources"]:
            source = require_exact_keys(
                source_raw,
                {"scorer_id", "source_id", "description", "evidence"},
                "novel assertion source",
            )
            if source["scorer_id"] not in SCORERS or not isinstance(
                source["source_id"], str
            ) or not re.fullmatch(r"s[12]-N[1-9][0-9]*", source["source_id"]):
                raise ProtocolError("invalid novel assertion source identity")
            if not source["source_id"].startswith(source["scorer_id"] + "-"):
                raise ProtocolError("novel source/scorer identity mismatch")
            if normalize_novel_description(source["description"]) != normalized:
                raise ProtocolError("novel source does not match its normalized assertion")
            validate_evidence(source["evidence"], "novel assertion source")
            source_keys.append((source["scorer_id"], source["source_id"]))
        if source_keys != sorted(source_keys) or len(source_keys) != len(set(source_keys)):
            raise ProtocolError("novel assertion sources are not unique and sorted")
        ids.append(assertion["id"])
        sort_keys.append((assertion["label"], normalized))
    if len(ids) != len(set(ids)) or sort_keys != sorted(sort_keys):
        raise ProtocolError("novel assertions are not uniquely and deterministically ordered")
    return packet


def add_adjudication_reason(
    cells: dict[tuple[str, str], set[str]], label: str, field: str, reason: str
) -> None:
    cells.setdefault((label, field), set()).add(reason)


def build_adjudication_packet(
    first: dict[str, Any],
    second: dict[str, Any],
    first_input_packet: dict[str, Any],
    second_input_packet: dict[str, Any],
    consistency_first: dict[str, Any],
    consistency_second: dict[str, Any],
    atom_manifest: dict[str, Any],
    defect_rules: dict[str, Any],
    evidence_packet_sha256: str,
) -> dict[str, Any]:
    manifest = validate_atom_manifest(atom_manifest)
    first = validate_direct_score(first, manifest, defect_rules, "s1", first_input_packet)
    second = validate_direct_score(second, manifest, defect_rules, "s2", second_input_packet)
    consistency_packet = build_consistency_packet(
        first,
        second,
        first_input_packet,
        second_input_packet,
        manifest,
        defect_rules,
        evidence_packet_sha256,
    )
    consistency_first = validate_consistency(
        consistency_first, manifest, defect_rules, consistency_packet, "c1"
    )
    consistency_second = validate_consistency(
        consistency_second, manifest, defect_rules, consistency_packet, "c2"
    )
    mode = manifest["mode"]
    first_reports = report_index(first)
    second_reports = report_index(second)
    cells: dict[tuple[str, str], set[str]] = {}
    for label in LABELS:
        left = first_reports[label]
        right = second_reports[label]
        for left_atom, right_atom in zip(left["atoms"], right["atoms"]):
            field = f"atom:{left_atom['id']}"
            if left_atom["direct_decision"] != right_atom["direct_decision"]:
                add_adjudication_reason(cells, label, field, "SCORER_DISAGREEMENT")
        for key, prefix in (("hard_errors", "hard_error"), ("global_defects", "global_defect")):
            for left_rule, right_rule in zip(left[key], right[key]):
                field = f"{prefix}:{left_rule['id']}"
                if left_rule["present"] != right_rule["present"]:
                    add_adjudication_reason(cells, label, field, "SCORER_DISAGREEMENT")
                elif left_rule["present"]:
                    add_adjudication_reason(cells, label, field, "AGREED_POSITIVE_DEFECT")
    challenges_by_cell: dict[tuple[str, str], dict[str, str]] = {}
    for consistency in (consistency_first, consistency_second):
        for challenge in consistency["challenges"]:
            key = (challenge["label"], challenge["field"])
            challenges_by_cell.setdefault(key, {})[consistency["reviewer_id"]] = challenge[
                "proposed_decision"
            ]
            add_adjudication_reason(cells, *key, "CONSISTENCY_CHALLENGE")
    for (label, field), decisions in challenges_by_cell.items():
        if len(set(decisions.values())) > 1:
            add_adjudication_reason(
                cells, label, field, "CONSISTENCY_REVIEWER_DISAGREEMENT"
            )
    novel_first = {
        item["normalized_id"]: item["category"]
        for item in consistency_first["novel_classifications"]
    }
    novel_second = {
        item["normalized_id"]: item["category"]
        for item in consistency_second["novel_classifications"]
    }
    novel_by_id = {item["id"]: item for item in consistency_packet["novel_assertions"]}
    for novel_id in sorted(novel_by_id):
        assertion = novel_by_id[novel_id]
        add_adjudication_reason(
            cells,
            assertion["label"],
            f"novel:{novel_id}",
            "NOVEL_MANDATORY_ADJUDICATION",
        )
        if novel_first[novel_id] != novel_second[novel_id]:
            add_adjudication_reason(
                cells,
                assertion["label"],
                f"novel:{novel_id}",
                "NOVEL_CLASSIFICATION_DISAGREEMENT",
            )
    input_digests = {
        "score_s1_sha256": sha256(canonical_json_bytes(first)),
        "score_s2_sha256": sha256(canonical_json_bytes(second)),
        "consistency_c1_sha256": sha256(canonical_json_bytes(consistency_first)),
        "consistency_c2_sha256": sha256(canonical_json_bytes(consistency_second)),
        "consistency_packet_sha256": sha256(canonical_json_bytes(consistency_packet)),
        "atom_manifest_sha256": sha256(canonical_json_bytes(manifest)),
        "defect_rules_sha256": sha256(canonical_json_bytes(validate_defect_rules(defect_rules))),
        "evidence_packet_sha256": evidence_packet_sha256,
    }
    binding_sha256 = sha256(canonical_json_bytes(input_digests))
    records = []
    for (label, field), reasons in sorted(cells.items()):
        cell_id = sha256(
            f"v5-diagnostic-cell-v2\0{binding_sha256}\0{mode}\0{label}\0{field}".encode("utf-8")
        )[:24]
        records.append(
            {"cell_id": cell_id, "label": label, "field": field, "reasons": sorted(reasons)}
        )
    return {
        "schema_version": 1,
        "status": "ADJUDICATION-PACKET",
        "mode": mode,
        "input_digests": input_digests,
        "binding_sha256": binding_sha256,
        "cells": records,
    }


def validate_adjudication(value: Any, packet: dict[str, Any]) -> dict[str, Any]:
    adjudication = require_exact_keys(
        value,
        {"schema_version", "status", "mode", "packet_sha256", "resolutions"},
        "adjudication",
    )
    packet_digest = sha256(canonical_json_bytes(packet))
    if (
        adjudication["schema_version"] != 1
        or adjudication["status"] != "ADJUDICATED"
        or adjudication["mode"] != packet["mode"]
        or adjudication["packet_sha256"] != packet_digest
    ):
        raise ProtocolError("adjudication identity/packet digest mismatch")
    if not isinstance(adjudication["resolutions"], list):
        raise ProtocolError("adjudication resolutions must be a list")
    by_cell = {cell["cell_id"]: cell for cell in packet["cells"]}
    seen: list[str] = []
    for raw in adjudication["resolutions"]:
        resolution = require_exact_keys(raw, {"cell_id", "decision", "evidence"}, "resolution")
        cell = by_cell.get(resolution["cell_id"])
        if cell is None:
            raise ProtocolError("adjudication contains an unknown cell")
        field = cell["field"]
        if field.startswith("atom:"):
            allowed = ("PASS", "FAIL")
        elif field.startswith("novel:"):
            allowed = NOVEL_CATEGORIES
        else:
            allowed = ("PRESENT", "ABSENT")
        if resolution["decision"] not in allowed:
            raise ProtocolError("adjudication resolution decision type mismatch")
        validate_evidence(resolution["evidence"], "adjudication resolution")
        seen.append(resolution["cell_id"])
    if set(seen) != set(by_cell) or len(seen) != len(by_cell):
        raise ProtocolError("adjudication must resolve every packet cell exactly once")
    return adjudication


def merge_final_scores(
    first: dict[str, Any],
    second: dict[str, Any],
    first_input_packet: dict[str, Any],
    second_input_packet: dict[str, Any],
    consistency_first: dict[str, Any],
    consistency_second: dict[str, Any],
    atom_manifest: dict[str, Any],
    defect_rules: dict[str, Any],
    evidence_packet_sha256: str,
    adjudication: dict[str, Any] | None,
) -> dict[str, Any]:
    manifest = validate_atom_manifest(atom_manifest)
    first = validate_direct_score(first, manifest, defect_rules, "s1", first_input_packet)
    second = validate_direct_score(second, manifest, defect_rules, "s2", second_input_packet)
    consistency_packet = build_consistency_packet(
        first,
        second,
        first_input_packet,
        second_input_packet,
        manifest,
        defect_rules,
        evidence_packet_sha256,
    )
    consistency_first = validate_consistency(
        consistency_first, manifest, defect_rules, consistency_packet, "c1"
    )
    consistency_second = validate_consistency(
        consistency_second, manifest, defect_rules, consistency_packet, "c2"
    )
    packet = build_adjudication_packet(
        first,
        second,
        first_input_packet,
        second_input_packet,
        consistency_first,
        consistency_second,
        manifest,
        defect_rules,
        evidence_packet_sha256,
    )
    if packet["cells"]:
        if adjudication is None:
            raise ProtocolError("nonempty adjudication packet requires one mode adjudication")
        adjudication = validate_adjudication(adjudication, packet)
        resolutions = {item["cell_id"]: item["decision"] for item in adjudication["resolutions"]}
    else:
        if adjudication is not None:
            raise ProtocolError("empty adjudication packet forbids an adjudicator output")
        resolutions = {}
    cell_for = {(cell["label"], cell["field"]): cell for cell in packet["cells"]}
    first_reports = report_index(first)
    second_reports = report_index(second)
    novel_c1 = {
        item["normalized_id"]: item["category"]
        for item in consistency_first["novel_classifications"]
    }
    novel_c2 = {
        item["normalized_id"]: item["category"]
        for item in consistency_second["novel_classifications"]
    }
    final_reports: list[dict[str, Any]] = []
    for label in LABELS:
        left = first_reports[label]
        right = second_reports[label]

        def resolved(field: str, left_value: str, right_value: str) -> str:
            cell = cell_for.get((label, field))
            if cell is not None:
                return resolutions[cell["cell_id"]]
            if left_value != right_value:
                raise ProtocolError(f"unrouted scorer disagreement: {label}/{field}")
            return left_value

        direct: dict[str, str] = {}
        for left_atom, right_atom in zip(left["atoms"], right["atoms"]):
            atom_id = left_atom["id"]
            direct[atom_id] = resolved(
                f"atom:{atom_id}",
                left_atom["direct_decision"],
                right_atom["direct_decision"],
            )
        certificates = compute_atom_certificates(manifest, direct)["atoms"]
        final_hard: list[str] = []
        final_global: list[str] = []
        for key, prefix, destination in (
            ("hard_errors", "hard_error", final_hard),
            ("global_defects", "global_defect", final_global),
        ):
            for left_rule, right_rule in zip(left[key], right[key]):
                decision = resolved(
                    f"{prefix}:{left_rule['id']}",
                    "PRESENT" if left_rule["present"] else "ABSENT",
                    "PRESENT" if right_rule["present"] else "ABSENT",
                )
                if decision == "PRESENT":
                    destination.append(left_rule["id"])
        novel_findings: list[dict[str, Any]] = []
        for assertion in consistency_packet["novel_assertions"]:
            if assertion["label"] != label:
                continue
            novel_id = assertion["id"]
            cell = cell_for.get((label, f"novel:{novel_id}"))
            if cell is None:
                if novel_c1[novel_id] != novel_c2[novel_id]:
                    raise ProtocolError("unrouted novel classification disagreement")
                classification = novel_c1[novel_id]
            else:
                classification = resolutions[cell["cell_id"]]
            novel_findings.append(
                {
                    "id": novel_id,
                    "classification": classification,
                    "sources": [
                        {
                            "scorer_id": source["scorer_id"],
                            "source_id": source["source_id"],
                        }
                        for source in assertion["sources"]
                    ],
                }
            )
        final_reports.append(
            {
                "label": label,
                "atoms": certificates,
                "hard_errors": final_hard,
                "global_defects": final_global,
                "novel_findings": novel_findings,
            }
        )
    return {
        "schema_version": 1,
        "status": "FINAL-SCORE",
        "mode": manifest["mode"],
        "input_binding_sha256": packet["binding_sha256"],
        "reports": final_reports,
    }


def validate_integration_hooks(value: Any) -> dict[str, Any]:
    hooks = require_exact_keys(
        value,
        {"schema_version", "status", "blocking", "failure_gate", "hooks"},
        "integration hooks",
    )
    if (
        hooks["schema_version"] != 1
        or hooks["status"] != "DRAFT"
        or hooks["blocking"] is not True
        or hooks["failure_gate"] != "D-STATIC-INTEGRITY"
        or not isinstance(hooks["hooks"], list)
    ):
        raise ProtocolError("integration hooks must be a blocking schema-v1 DRAFT")
    seen: list[str] = []
    for index, raw in enumerate(hooks["hooks"]):
        hook = require_exact_keys(
            raw,
            {"id", "required", "implementation_status", "consumes", "produces"},
            f"integration hook {index}",
        )
        if (
            hook["required"] is not True
            or hook["implementation_status"] != "UNIMPLEMENTED"
            or not isinstance(hook["consumes"], list)
            or not hook["consumes"]
            or not isinstance(hook["produces"], list)
            or not hook["produces"]
            or any(not isinstance(item, str) or not item.strip() for item in hook["consumes"] + hook["produces"])
        ):
            raise ProtocolError(f"integration hook {hook.get('id')!r} is not explicitly blocking")
        seen.append(hook["id"])
    if tuple(seen) != EXPECTED_INTEGRATION_HOOK_IDS:
        raise ProtocolError("integration hook inventory/order is incomplete or unexpected")
    return hooks


def validate_control_manifest(value: Any) -> dict[str, Any]:
    manifest = require_exact_keys(
        value, {"schema_version", "status", "controls"}, "control manifest"
    )
    if manifest["schema_version"] != 1 or manifest["status"] != "DRAFT":
        raise ProtocolError("control manifest must be schema-v1 DRAFT")
    if not isinstance(manifest["controls"], list) or not manifest["controls"]:
        raise ProtocolError("control manifest must be nonempty")
    fixtures = {
        "E": "e_semantics",
        "V": "v_valid_use",
        "F": "f_fanout",
        "P": "p_predicates",
        "B": "b_build",
        "L": "l_proof",
        "R": "r_redesign",
        "Q": "q_metamorphic",
    }
    atom_modes = {
        atom["id"]: mode
        for mode in MODES
        for atom in validate_atom_manifest(
            read_json(RUN / "freeze" / "atoms" / f"{mode}.json"), mode
        )["atoms"]
    }
    expected_relation = {
        "kind": "ALL_LISTED_ATOM_CERTIFICATES_EQUAL",
        "certificate_field": "certificate_decision",
        "expected_decision": "PASS",
    }
    seen_ids: set[str] = set()
    seen_signatures: set[tuple[str, str, tuple[str, ...]]] = set()
    family_modes: set[tuple[str, str]] = set()
    covered_atoms: set[str] = set()
    for raw in manifest["controls"]:
        control = require_exact_keys(
            raw,
            {
                "id",
                "family",
                "mode",
                "fixture_id",
                "atom_ids",
                "applicability",
                "expected_relation",
                "rationale",
            },
            "control",
        )
        mode = control["mode"]
        family = control["family"]
        prefix = {"PROOF_QUALITY": "PQ", "CLASSIFICATION_CONTROL": "CC"}.get(family)
        if (
            mode not in MODES
            or prefix is None
            or not isinstance(control["id"], str)
            or re.fullmatch(rf"{prefix}-{mode}-[A-Z0-9-]+", control["id"]) is None
            or control["id"] in seen_ids
            or control["fixture_id"] != fixtures[mode]
            or control["applicability"] != "V5_REPORTS_ONLY"
            or control["expected_relation"] != expected_relation
            or not isinstance(control["rationale"], str)
            or not control["rationale"].strip()
        ):
            raise ProtocolError(f"invalid control identity/contract: {control.get('id')!r}")
        atom_ids = control["atom_ids"]
        if (
            not isinstance(atom_ids, list)
            or not atom_ids
            or len(atom_ids) != len(set(atom_ids))
            or any(atom_modes.get(atom_id) != mode for atom_id in atom_ids)
        ):
            raise ProtocolError(f"invalid atom closure for control {control['id']}")
        signature = (mode, family, tuple(atom_ids))
        if signature in seen_signatures:
            raise ProtocolError(f"duplicate control signature: {control['id']}")
        seen_ids.add(control["id"])
        seen_signatures.add(signature)
        family_modes.add((mode, family))
        covered_atoms.update(atom_ids)
    expected_family_modes = {
        (mode, family)
        for mode in MODES
        for family in ("PROOF_QUALITY", "CLASSIFICATION_CONTROL")
    }
    if family_modes != expected_family_modes or covered_atoms != set(atom_modes):
        raise ProtocolError("control manifest does not exactly cover every mode/family and atom")
    return manifest


def validate_materiality_contract(value: Any) -> dict[str, Any]:
    expected = {
        "schema_version": 1,
        "status": "DRAFT",
        "reviewer_ids": ["m1", "m2"],
        "independence": "DISTINCT_AGENTS_NO_OTHER_REVIEW_OUTPUT",
        "scope": [
            "V5_CANDIDATE_REPORTS",
            "CANDIDATE_PACKAGE",
            "HARNESS_PROTOCOL",
            "ADVERSARIAL_AND_COHERENCE_REVIEWS",
        ],
        "inclusive_materiality_rule": "BLOCKING_IF_A_SUPPORTED_FINDING_COULD_CHANGE_CANDIDATE_ACCEPTABILITY_OR_INVALIDATE_HARNESS_INTERPRETATION",
        "finding_id_pattern": r"^m[12]-F[1-9][0-9]*$",
        "empty_review_requirement": "COMPLETE_SCOPE_ATTESTATION_REQUIRED",
        "disagreement_policy": "MANDATORY_INDEPENDENT_ADJUDICATION",
        "novel_classification_is_not_materiality": True,
        "ledger_completion": "BOTH_REVIEWS_COMPLETE_AND_EVERY_UNION_FINDING_RESOLVED",
    }
    if value != expected:
        raise ProtocolError("materiality-review contract is not the exact frozen DRAFT contract")
    return value


def validate_aggregation_rules(value: Any, gate_manifest: dict[str, Any]) -> dict[str, Any]:
    rules = require_exact_keys(
        value,
        {
            "schema_version",
            "status",
            "rules_version",
            "population_contract",
            "input_digest_contract",
            "default_dispositions",
            "rules",
        },
        "aggregation rules",
    )
    if (
        rules["schema_version"] != 1
        or rules["status"] != "DRAFT"
        or rules["rules_version"] != "v5-diagnostic-aggregate-v1"
        or rules["default_dispositions"]
        != {"missing": "ERROR", "malformed": "ERROR", "error": "ERROR"}
    ):
        raise ProtocolError("aggregation rule identity/dispositions mismatch")
    expected_digest_keys = [
        "schedule_slots_sha256",
        "envelopes_sha256",
        "word_counts_sha256",
        "atom_manifests_sha256",
        "oracle_receipts_sha256",
        "blind_join_sha256",
        "joined_reports_sha256",
        "projection_audit_manifest_sha256",
        "scoring_bundle_manifest_sha256",
        "control_manifest_sha256",
        "control_results_sha256",
        "materiality_ledger_sha256",
        "comparison_predicate_sha256",
        "coherence_review_sha256",
    ]
    if rules["input_digest_contract"] != {
        "algorithm": "sha256",
        "canonicalization": "UTF8_SORTED_KEYS_COMPACT_JSON_LF_V1",
        "exact_key_set": expected_digest_keys,
        "binds_exact_artifact_set": True,
    }:
        raise ProtocolError("aggregation input-digest contract is not exact")
    expected_population = {
        "candidate_condition": "v5",
        "candidate_only_paths": [
            "scores.focused_recall_pass",
            "scores.proof_quality_pass",
            "scores.controls_pass",
            "scores.hard_error_count",
            "scores.global_defect_count",
        ],
        "all_condition_paths": [
            "collection.complete",
            "collection.invalid_output_count",
            "comparison.predicate_pass",
        ],
        "separate_review_paths": [
            "oracle.coverage_pass",
            "scores.material_finding_count",
            "review.coherence_pass",
        ],
        "novel_classifications_are_not_material_findings": True,
    }
    if rules["population_contract"] != expected_population:
        raise ProtocolError("aggregation population contract drifted")
    context_inputs = {
        item["source"]["path"]: item["type"]
        for gate in gate_manifest["gates"]
        for item in gate["inputs"]
    }
    if not isinstance(rules["rules"], list):
        raise ProtocolError("aggregation rules must be a list")
    observed: dict[str, dict[str, Any]] = {}
    for raw in rules["rules"]:
        rule = require_exact_keys(raw, {"context_path", "output_type", "formula"}, "aggregate rule")
        path = rule["context_path"]
        if path in observed or rule["output_type"] != context_inputs.get(path) or not isinstance(
            rule["formula"], dict
        ):
            raise ProtocolError(f"invalid or duplicate aggregate rule: {path!r}")
        observed[path] = rule
    if set(observed) != set(context_inputs):
        raise ProtocolError("aggregate rules do not cover every context-backed gate one-to-one")
    expected_formulas = {
        "oracle.coverage_pass": {
            "kind": "oracle_exact_coverage_v1",
            "population": "EVERY_MODE",
            "required_decision": "PASS",
            "set_relation": "covered_atom_ids == atom_manifest_ids",
        },
        "collection.complete": {
            "kind": "collection_exact_slots_v1",
            "population": "ALL_120_REPORT_SLOTS",
            "set_relation": "schedule_slot_ids == envelope_slot_ids == word_count_slot_ids",
            "required_terminal_status": "SEALED",
        },
        "collection.invalid_output_count": {
            "kind": "invalid_output_count_v1",
            "population": "ALL_120_REPORT_SLOTS",
            "invalid_if_any": [
                "terminal_status != SEALED",
                "semantic_valid != true",
                "format_valid != true",
                "word_count_valid != true",
            ],
        },
        "scores.focused_recall_pass": {
            "kind": "candidate_atom_recall_v1",
            "population": "V5_REPORTS_ONLY",
            "quantifier": "EVERY_MODE_ATOM_REPLICATE",
            "field": "certificate_decision",
            "required_value": "PASS",
        },
        "scores.proof_quality_pass": {
            "kind": "candidate_control_family_v1",
            "population": "V5_REPORTS_ONLY",
            "control_family": "PROOF_QUALITY",
            "set_relation": "observed_control_ids == expected_control_ids",
            "decision_relation": "decision == expected_decision",
        },
        "scores.controls_pass": {
            "kind": "candidate_control_family_v1",
            "population": "V5_REPORTS_ONLY",
            "control_family": "CLASSIFICATION_CONTROL",
            "set_relation": "observed_control_ids == expected_control_ids",
            "decision_relation": "decision == expected_decision",
        },
        "scores.hard_error_count": {
            "kind": "candidate_present_rule_count_v1",
            "population": "V5_REPORTS_ONLY",
            "field": "hard_errors",
            "deduplication_key": ["slot_id", "rule_id"],
        },
        "scores.global_defect_count": {
            "kind": "candidate_present_rule_count_v1",
            "population": "V5_REPORTS_ONLY",
            "field": "global_defects",
            "deduplication_key": ["slot_id", "rule_id"],
        },
        "scores.material_finding_count": {
            "kind": "blocking_materiality_count_v1",
            "population": "CANDIDATE_HARNESS_ADVERSARIAL_REVIEW_LEDGER",
            "required_ledger_status": "COMPLETE",
            "required_reviewer_ids": ["m1", "m2"],
            "required_scope_complete": True,
            "field": "blocking",
            "required_value": True,
            "novel_review_source_forbidden": True,
            "empty_allowed_iff": "BOTH_REVIEWS_COMPLETE_AND_ATTEST_NO_FINDINGS",
            "deduplication_key": ["finding_id"],
        },
        "comparison.predicate_pass": {
            "kind": "exact_comparison_predicate_v1",
            "population": "ALL_THREE_CONDITIONS",
            "predicate_id": "v5-diagnostic-absolute-and-not-trailing-v1",
        },
        "review.coherence_pass": {
            "kind": "coherence_decision_v1",
            "population": "CANDIDATE_PACKAGE_AND_HARNESS",
            "required_decision": "PASS",
        },
    }
    for path, expected_formula in expected_formulas.items():
        if observed[path]["formula"] != expected_formula:
            raise ProtocolError(f"aggregate formula is not exact for {path}")
    return rules


def expected_comparison_predicate() -> dict[str, Any]:
    return {
        "schema_version": 1,
        "status": "DRAFT",
        "predicate_id": "v5-diagnostic-absolute-and-not-trailing-v1",
        "claim_kind": "EXACT_DESCRIPTIVE",
        "modes": list(MODES),
        "conditions": ["v5", "v4", "no_skill"],
        "replicates_per_cell": 5,
        "unit": "MODE_ATOM_CERTIFICATE",
        "absolute_v5": {
            "quantifier": "FOR_EVERY_MODE_ATOM_REPLICATE",
            "field": "certificate_decision",
            "required_value": "PASS",
        },
        "not_trailing": {
            "quantifier": "FOR_EVERY_MODE_ATOM",
            "metric": "PASS_COUNT_ACROSS_FIVE_REPLICATES",
            "comparisons": ["v5 >= v4", "v5 >= no_skill"],
        },
        "on_missing": "ERROR",
        "on_malformed": "ERROR",
        "permits_inferential_claim": False,
        "permits_release_claim": False,
    }


def validate_comparison_predicate(value: Any) -> dict[str, Any]:
    if value != expected_comparison_predicate():
        raise ProtocolError("comparison predicate does not exactly match the frozen DRAFT formula")
    return value


def validate_root_inventory(value: Any) -> dict[str, Any]:
    inventory = require_exact_keys(
        value,
        {
            "schema_version",
            "status",
            "inventory_kind",
            "inventory_version",
            "scope",
            "release_eligibility",
            "required_gate_ids",
            "requirements",
        },
        "root inventory",
    )
    if (
        inventory["schema_version"] != 1
        or inventory["status"] != "DRAFT"
        or inventory["inventory_kind"] != "DIAGNOSTIC"
    ):
        raise ProtocolError("root inventory must be schema-v1 DRAFT DIAGNOSTIC")
    eligibility = require_exact_keys(
        inventory["release_eligibility"],
        {"eligible", "decision", "blocking_gate_ids", "reason"},
        "release eligibility",
    )
    if (
        eligibility["eligible"] is not False
        or eligibility["decision"] != "INELIGIBLE"
        or eligibility["blocking_gate_ids"] != ["G-ISOLATION", "G-OUTPUT-FINALIZATION"]
        or not isinstance(eligibility["reason"], str)
        or not eligibility["reason"].strip()
    ):
        raise ProtocolError("diagnostic inventory must fix release eligibility to INELIGIBLE on both G-* blockers")
    roots = inventory["required_gate_ids"]
    if not isinstance(roots, list) or len(roots) != len(set(roots)) or set(roots) != REQUIRED_ROOT_IDS:
        raise ProtocolError("root inventory ID set is not the exact required V5 diagnostic root set")
    requirements = inventory["requirements"]
    if not isinstance(requirements, list) or len(requirements) != len(roots):
        raise ProtocolError("root inventory requirements are incomplete")
    requirement_ids: list[str] = []
    for index, raw in enumerate(requirements):
        requirement = require_exact_keys(raw, {"gate_id", "source", "summary"}, f"gate requirement {index}")
        if any(not isinstance(requirement[field], str) or not requirement[field].strip() for field in ("gate_id", "source", "summary")):
            raise ProtocolError(f"invalid root requirement {index}")
        requirement_ids.append(requirement["gate_id"])
    if set(requirement_ids) != set(roots) or len(set(requirement_ids)) != len(roots):
        raise ProtocolError("root requirement mapping does not exactly cover root IDs")
    return inventory


def validate_gate_manifest(value: Any, inventory: dict[str, Any]) -> dict[str, Any]:
    inventory = validate_root_inventory(inventory)
    manifest = require_exact_keys(
        value, {"schema_version", "status", "manifest_version", "gates"}, "gate manifest"
    )
    if manifest["schema_version"] != 1 or manifest["status"] != "DRAFT":
        raise ProtocolError("gate manifest must be schema-v1 DRAFT")
    if not isinstance(manifest["gates"], list):
        raise ProtocolError("gate manifest gates must be a list")
    gates: list[dict[str, Any]] = []
    for index, raw in enumerate(manifest["gates"]):
        gate = require_exact_keys(
            raw,
            {
                "id",
                "version",
                "mandatory_root",
                "description",
                "prerequisites",
                "inputs",
                "predicate",
                "on_missing",
                "on_error",
            },
            f"gate {index}",
        )
        gate_id = gate["id"]
        if not isinstance(gate_id, str) or not re.fullmatch(r"[DG]-[A-Z][A-Z0-9-]*", gate_id):
            raise ProtocolError(f"invalid gate ID: {gate_id!r}")
        if gate["version"] != 1 or gate["mandatory_root"] is not True:
            raise ProtocolError(f"gate {gate_id} must be version 1 and mandatory_root true")
        if not isinstance(gate["description"], str) or not gate["description"].strip():
            raise ProtocolError(f"gate {gate_id} description is blank")
        if not isinstance(gate["prerequisites"], list) or any(
            not isinstance(item, str) for item in gate["prerequisites"]
        ):
            raise ProtocolError(f"gate {gate_id} prerequisites are invalid")
        if gate["on_missing"] != "ERROR" or gate["on_error"] != "ERROR":
            raise ProtocolError(f"gate {gate_id} must fail closed to ERROR")
        if not isinstance(gate["inputs"], list):
            raise ProtocolError(f"gate {gate_id} inputs must be a list")
        inputs: dict[str, dict[str, Any]] = {}
        for raw_input in gate["inputs"]:
            item = require_exact_keys(raw_input, {"id", "type", "source"}, f"gate {gate_id} input")
            input_id = require_safe_id(item["id"], f"gate {gate_id} input ID")
            if input_id in inputs or item["type"] not in ("boolean", "integer", "string"):
                raise ProtocolError(f"invalid or duplicate gate input {gate_id}.{input_id}")
            source = require_exact_keys(item["source"], {"kind", "path"}, f"gate {gate_id} source")
            if source["kind"] != "context" or not isinstance(source["path"], str) or not re.fullmatch(
                r"[a-z][a-z0-9_]*(\.[a-z][a-z0-9_]*)*", source["path"]
            ):
                raise ProtocolError(f"invalid context source for gate {gate_id}.{input_id}")
            inputs[input_id] = item
        predicate = gate["predicate"]
        if not isinstance(predicate, dict):
            raise ProtocolError(f"gate {gate_id} predicate must be an object")
        kind = predicate.get("kind")
        if kind == "constant":
            require_exact_keys(predicate, {"kind", "outcome"}, f"gate {gate_id} predicate")
            if predicate["outcome"] not in ("PASS", "FAIL") or inputs:
                raise ProtocolError(f"invalid constant predicate for gate {gate_id}")
        elif kind == "boolean_true":
            require_exact_keys(predicate, {"kind", "input"}, f"gate {gate_id} predicate")
            if predicate["input"] not in inputs or inputs[predicate["input"]]["type"] != "boolean":
                raise ProtocolError(f"boolean predicate/input mismatch for gate {gate_id}")
        elif kind == "integer_equals":
            require_exact_keys(predicate, {"kind", "input", "value"}, f"gate {gate_id} predicate")
            if (
                predicate["input"] not in inputs
                or inputs[predicate["input"]]["type"] != "integer"
                or type(predicate["value"]) is not int
            ):
                raise ProtocolError(f"integer predicate/input mismatch for gate {gate_id}")
        else:
            raise ProtocolError(f"unsupported predicate kind for gate {gate_id}: {kind!r}")
        gates.append(gate)
    ids = [gate["id"] for gate in gates]
    roots = inventory["required_gate_ids"]
    if set(ids) != set(roots) or len(ids) != len(roots):
        raise ProtocolError("gate IDs and root inventory IDs must be exactly equal")
    prerequisites = {gate["id"]: gate["prerequisites"] for gate in gates}
    topological_order(ids, prerequisites, "gate")
    expected_completion = {gate_id for gate_id in ids if gate_id.startswith("D-")} - {
        "D-DIAGNOSTIC-COMPLETION"
    }
    if set(prerequisites["D-DIAGNOSTIC-COMPLETION"]) != expected_completion:
        raise ProtocolError(
            "D-DIAGNOSTIC-COMPLETION must depend on every other D-* gate exactly once"
        )
    constants = {gate["id"]: gate["predicate"] for gate in gates}
    for gate_id in ("G-ISOLATION", "G-OUTPUT-FINALIZATION", "D-STATIC-INTEGRITY"):
        if constants[gate_id] != {"kind": "constant", "outcome": "FAIL"}:
            raise ProtocolError(f"{gate_id} must remain a direct constant FAIL")
    return manifest


def context_lookup(context: dict[str, Any], path: str) -> Any:
    value: Any = context
    for part in path.split("."):
        if not isinstance(value, dict) or part not in value:
            raise KeyError(path)
        value = value[part]
    return value


def evaluate_gates(manifest: dict[str, Any], inventory: dict[str, Any], context: dict[str, Any]) -> dict[str, Any]:
    manifest = validate_gate_manifest(manifest, inventory)
    if not isinstance(context, dict):
        raise ProtocolError("gate context must be an object")
    gates = manifest["gates"]
    by_id = {gate["id"]: gate for gate in gates}
    prerequisites = {gate["id"]: gate["prerequisites"] for gate in gates}
    order = topological_order(list(by_id), prerequisites, "gate")
    results: dict[str, dict[str, Any]] = {}
    for gate_id in order:
        gate = by_id[gate_id]
        resolved: dict[str, Any] = {}
        errors: list[str] = []
        for item in gate["inputs"]:
            try:
                value = context_lookup(context, item["source"]["path"])
            except KeyError:
                errors.append(f"missing:{item['source']['path']}")
                continue
            expected = item["type"]
            valid = (
                (expected == "boolean" and type(value) is bool)
                or (expected == "integer" and type(value) is int)
                or (expected == "string" and type(value) is str)
            )
            if not valid:
                errors.append(f"type:{item['source']['path']}:{expected}")
            else:
                resolved[item["id"]] = value
        predicate = gate["predicate"]
        if errors:
            direct = "ERROR"
        elif predicate["kind"] == "constant":
            direct = predicate["outcome"]
        elif predicate["kind"] == "boolean_true":
            direct = "PASS" if resolved[predicate["input"]] else "FAIL"
        elif predicate["kind"] == "integer_equals":
            direct = "PASS" if resolved[predicate["input"]] == predicate["value"] else "FAIL"
        else:  # protected by validation
            direct = "ERROR"
            errors.append("unsupported-predicate")
        blocked = [
            dependency
            for dependency in prerequisites[gate_id]
            if results[dependency]["certificate_decision"] != "PASS"
        ]
        roots: set[str] = set()
        if direct != "PASS":
            roots.add(gate_id)
        for dependency in blocked:
            roots.update(results[dependency]["root_failures"])
        if direct == "PASS" and not blocked:
            certificate = "PASS"
        elif direct == "ERROR" or any(
            results[dependency]["certificate_decision"] == "ERROR" for dependency in blocked
        ):
            certificate = "ERROR"
        else:
            certificate = "FAIL"
        results[gate_id] = {
            "id": gate_id,
            "direct_decision": direct,
            "blocked_by": blocked,
            "certificate_decision": certificate,
            "root_failures": sorted(roots),
            "errors": errors,
        }
    return {
        "schema_version": 1,
        "status": "DRAFT-COMPUTED",
        "manifest_version": manifest["manifest_version"],
        "context_trust": "UNBOUND_DRAFT_INPUT",
        "release_eligibility": copy.deepcopy(inventory["release_eligibility"]),
        "gates": [results[gate["id"]] for gate in gates],
    }


def validate_launch_record(value: Any) -> dict[str, Any]:
    record = require_exact_keys(
        value,
        {
            "schema_version",
            "status",
            "role",
            "assignment_id",
            "slot_id",
            "run_id",
            "cell_id",
            "mode",
            "fixture_id",
            "task_mode",
            "prompt_regime",
            "condition_role",
            "condition_label",
            "target_label",
            "replicate",
            "workspace_root",
            "input_root",
            "output_root",
            "target_path",
            "output_path",
            "schema_paths",
            "schedule_sha256",
            "prompt_sha256",
            "package_byte_tree_sha256",
            "target_byte_tree_sha256",
            "authority_packet_path",
            "authority_packet_sha256",
            "authority_packet_visibility",
            "execution_manifest_sha256",
            "input_packet_sha256",
            "envelope_spec_sha256",
        },
        "launch record",
    )
    if record["schema_version"] != 1 or record["status"] != "READY":
        raise ProtocolError("launch record must be schema-v1 READY")
    role = record["role"]
    if role not in ("report", "scorer", "consistency", "adjudicator"):
        raise ProtocolError("invalid launch semantic-agent role")
    require_safe_id(record["assignment_id"], "launch assignment ID")
    require_safe_id(record["slot_id"], "launch slot ID")
    if not isinstance(record["cell_id"], str) or not re.fullmatch(r"[0-9a-f]{32}", record["cell_id"]):
        raise ProtocolError("launch cell_id must be 128-bit lowercase hex")
    mode = record["mode"]
    if mode not in MODES:
        raise ProtocolError("launch mode is invalid")
    if role == "report":
        if not isinstance(record["run_id"], str) or not re.fullmatch(
            r"r[1-9][0-9]*", record["run_id"]
        ):
            raise ProtocolError("report launch run_id must be a stable rN identifier")
        if record["prompt_regime"] != PROMPT_REGIMES[mode]:
            raise ProtocolError("launch mode/prompt-regime mismatch")
        for field in ("fixture_id", "task_mode"):
            if not isinstance(record[field], str) or not re.fullmatch(r"[a-z][a-z0-9_-]*", record[field]):
                raise ProtocolError(f"invalid launch {field}")
        if record["condition_role"] not in ("v5", "v4", "no_skill"):
            raise ProtocolError("invalid launch condition role")
        require_safe_id(record["condition_label"], "condition label")
        require_safe_id(record["target_label"], "target label")
        if type(record["replicate"]) is not int or record["replicate"] not in range(1, 6):
            raise ProtocolError("launch replicate must be 1 through 5")
        workspace_root = record["workspace_root"]
        if (
            not isinstance(workspace_root, str)
            or not Path(workspace_root).is_absolute()
            or str(Path(workspace_root).resolve()) != workspace_root
        ):
            raise ProtocolError("report launch must bind a normalized absolute workspace root")
        if record["input_root"] != workspace_root:
            raise ProtocolError("report launch input/workspace roots must be identical")
        target_path = require_relative_file(record["target_path"], "launch target path")
        authority_path = require_relative_file(
            record["authority_packet_path"], "launch authority packet path"
        )
        require_relative_file(record["output_path"], "launch output path")
        workspace = Path(workspace_root)
        for relative, label in ((target_path, "target"), (authority_path, "authority")):
            resolved = (workspace / Path(*PurePosixPath(relative).parts)).resolve()
            if not is_within(resolved, workspace):
                raise ProtocolError(f"launch {label} path escapes the exact workspace root")
        if (
            record["authority_packet_path"] != "docs/rust-documentation.json"
            or record["authority_packet_visibility"] != "AGENT_VISIBLE_NEUTRAL"
            or not isinstance(record["authority_packet_sha256"], str)
            or not HEX64.fullmatch(record["authority_packet_sha256"])
        ):
            raise ProtocolError("report launch must bind the common neutral authority packet")
    else:
        nullable = (
            "run_id",
            "fixture_id",
            "task_mode",
            "prompt_regime",
            "condition_role",
            "condition_label",
            "target_label",
            "replicate",
            "workspace_root",
            "target_path",
            "package_byte_tree_sha256",
            "target_byte_tree_sha256",
            "authority_packet_path",
            "authority_packet_sha256",
            "authority_packet_visibility",
        )
        if any(record[field] is not None for field in nullable):
            raise ProtocolError("evaluator launch must null all report-cell-only fields")
        assignment = record["assignment_id"]
        expected_assignment = {
            "scorer": rf"{mode}-s[12]",
            "consistency": rf"{mode}-c[12]",
            "adjudicator": rf"{mode}-a1",
        }[role]
        if re.fullmatch(expected_assignment, assignment) is None:
            raise ProtocolError("evaluator launch role/assignment mismatch")
    for field in ("input_root", "output_root"):
        path_value = record[field]
        if (
            not isinstance(path_value, str)
            or not Path(path_value).is_absolute()
            or str(Path(path_value).resolve()) != path_value
        ):
            raise ProtocolError(f"launch {field} must be a normalized absolute path")
    output_path = require_relative_file(record["output_path"], "launch output path")
    input_root = Path(record["input_root"])
    output_root = Path(record["output_root"])
    if not is_within(
        (output_root / Path(*PurePosixPath(output_path).parts)).resolve(), output_root
    ):
        raise ProtocolError("launch output path escapes the exact output root")
    if not isinstance(record["schema_paths"], list) or not record["schema_paths"]:
        raise ProtocolError("launch must bind at least one schema path")
    schema_paths = [
        require_relative_file(path, "launch schema path") for path in record["schema_paths"]
    ]
    if schema_paths != sorted(schema_paths) or len(schema_paths) != len(set(schema_paths)):
        raise ProtocolError("launch schema paths must be unique and sorted")
    for schema_path in schema_paths:
        resolved = (input_root / Path(*PurePosixPath(schema_path).parts)).resolve()
        if not is_within(resolved, input_root):
            raise ProtocolError("launch schema path escapes the exact input root")
    for field in (
        "schedule_sha256",
        "prompt_sha256",
        "execution_manifest_sha256",
        "input_packet_sha256",
        "envelope_spec_sha256",
    ):
        if not isinstance(record[field], str) or not HEX64.fullmatch(record[field]):
            raise ProtocolError(f"invalid launch digest: {field}")
    if role == "report":
        if not isinstance(record["target_byte_tree_sha256"], str) or not HEX64.fullmatch(
            record["target_byte_tree_sha256"]
        ):
            raise ProtocolError("report launch must bind a target tree digest")
        package = record["package_byte_tree_sha256"]
        if record["condition_role"] == "no_skill":
            if package is not None:
                raise ProtocolError("no-skill launch must bind literal null package digest")
        elif not isinstance(package, str) or not HEX64.fullmatch(package):
            raise ProtocolError("V5/V4 launch must bind a package tree digest")
    return record


def validate_envelope_spec(value: Any, require_ready: bool = True) -> dict[str, Any]:
    spec = require_exact_keys(
        value,
        {
            "schema_version",
            "status",
            "files",
            "final_response",
            "max_total_output_bytes",
            "allowed_process_dispositions",
        },
        "envelope spec",
    )
    if spec["schema_version"] != 1 or spec["status"] not in ("DRAFT", "READY"):
        raise ProtocolError("envelope spec must be schema-v1 DRAFT or READY")
    if require_ready and spec["status"] != "READY":
        raise ProtocolError("attempt leasing requires a READY envelope spec")
    if type(spec["max_total_output_bytes"]) is not int or spec["max_total_output_bytes"] < 1:
        raise ProtocolError("max_total_output_bytes must be a positive integer")
    if not isinstance(spec["files"], list) or not spec["files"]:
        raise ProtocolError("envelope spec files must be a nonempty list")
    paths: list[str] = []
    for index, raw in enumerate(spec["files"]):
        item = require_exact_keys(raw, {"path", "required", "max_bytes", "utf8"}, f"envelope file {index}")
        paths.append(require_relative_file(item["path"], f"envelope file {index} path"))
        if type(item["required"]) is not bool or type(item["utf8"]) is not bool:
            raise ProtocolError(f"envelope file {index} flags must be booleans")
        if type(item["max_bytes"]) is not int or item["max_bytes"] < 0:
            raise ProtocolError(f"envelope file {index} max_bytes must be nonnegative")
    if len(set(paths)) != len(paths):
        raise ProtocolError("envelope spec contains duplicate file paths")
    final = require_exact_keys(
        spec["final_response"],
        {"required", "max_bytes", "utf8", "utf8_fullmatch_regex"},
        "final response spec",
    )
    if type(final["required"]) is not bool or type(final["utf8"]) is not bool:
        raise ProtocolError("final response flags must be booleans")
    if type(final["max_bytes"]) is not int or final["max_bytes"] < 0:
        raise ProtocolError("final response max_bytes must be nonnegative")
    if final["utf8"] is not True or not isinstance(final["utf8_fullmatch_regex"], str) or not final[
        "utf8_fullmatch_regex"
    ]:
        raise ProtocolError("final response must freeze a nonblank UTF-8 fullmatch regex")
    try:
        re.compile(final["utf8_fullmatch_regex"])
    except re.error as error:
        raise ProtocolError("final response UTF-8 fullmatch regex is invalid") from error
    dispositions = spec["allowed_process_dispositions"]
    if (
        not isinstance(dispositions, list)
        or not dispositions
        or len(set(dispositions)) != len(dispositions)
        or any(not isinstance(item, str) or not SAFE_ID.fullmatch(item) for item in dispositions)
    ):
        raise ProtocolError("allowed process dispositions must be unique safe identifiers")
    return spec


def load_bound_spec(lease: dict[str, Any]) -> dict[str, Any]:
    try:
        data = base64.b64decode(lease["envelope_spec_bytes_base64"], validate=True)
    except Exception as error:
        raise ProtocolError("lease envelope spec encoding is invalid") from error
    if sha256(data) != lease.get("envelope_spec_sha256"):
        raise ProtocolError("lease envelope spec digest mismatch")
    try:
        value = json.loads(data.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ProtocolError("lease envelope spec bytes are not valid JSON/UTF-8") from error
    return validate_envelope_spec(value, require_ready=True)


def load_bound_launch(lease: dict[str, Any]) -> dict[str, Any]:
    try:
        data = base64.b64decode(lease["launch_record_bytes_base64"], validate=True)
    except Exception as error:
        raise ProtocolError("lease launch-record encoding is invalid") from error
    if sha256(data) != lease.get("launch_record_sha256"):
        raise ProtocolError("lease launch-record digest mismatch")
    try:
        value = json.loads(data.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ProtocolError("lease launch-record bytes are not valid JSON/UTF-8") from error
    launch = validate_launch_record(value)
    if launch["slot_id"] != lease.get("slot_id"):
        raise ProtocolError("lease/launch slot mismatch")
    return launch


def validate_lease(value: Any) -> dict[str, Any]:
    lease = require_exact_keys(
        value,
        {
            "schema_version",
            "status",
            "slot_id",
            "attempt_id",
            "agent_id",
            "lease_token",
            "launch_record_sha256",
            "launch_record_bytes_base64",
            "attempt_root",
            "attempt_root_claim_sha256",
            "envelope_spec_sha256",
            "envelope_spec_bytes_base64",
        },
        "lease",
    )
    if lease["schema_version"] != 1 or lease["status"] != "STARTED":
        raise ProtocolError("lease must be schema-v1 STARTED")
    for field in ("slot_id", "attempt_id", "agent_id"):
        require_safe_id(lease[field], f"lease {field}")
    if not isinstance(lease["lease_token"], str) or not re.fullmatch(r"[0-9a-f]{64}", lease["lease_token"]):
        raise ProtocolError("invalid lease token")
    for field in (
        "launch_record_sha256",
        "attempt_root_claim_sha256",
        "envelope_spec_sha256",
    ):
        if not isinstance(lease[field], str) or not HEX64.fullmatch(lease[field]):
            raise ProtocolError(f"invalid lease digest: {field}")
    if not isinstance(lease["attempt_root"], str):
        raise ProtocolError("lease attempt_root must be a path string")
    bound_root = Path(lease["attempt_root"]).resolve()
    if sha256(str(bound_root).encode("utf-8")) != lease["attempt_root_claim_sha256"]:
        raise ProtocolError("lease attempt-root claim digest mismatch")
    launch = load_bound_launch(lease)
    load_bound_spec(lease)
    if (
        launch["output_root"] != str(bound_root)
        or launch["envelope_spec_sha256"] != lease["envelope_spec_sha256"]
    ):
        raise ProtocolError("lease launch/output/spec cross-binding mismatch")
    return lease


def acquire_lease(
    state_root: Path,
    launch_path: Path,
    agent_id: str,
    spec_path: Path,
    attempt_root: Path,
) -> dict[str, Any]:
    state_root = require_external_path(state_root, "state root")
    agent_id = require_safe_id(agent_id, "agent ID")
    launch_bytes = launch_path.read_bytes()
    try:
        launch = json.loads(launch_bytes.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ProtocolError("launch record is not valid JSON/UTF-8") from error
    launch = validate_launch_record(launch)
    slot_id = launch["slot_id"]
    spec_bytes = spec_path.read_bytes()
    try:
        spec = json.loads(spec_bytes.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ProtocolError("envelope spec is not valid JSON/UTF-8") from error
    validate_envelope_spec(spec, require_ready=True)
    if sha256(spec_bytes) != launch["envelope_spec_sha256"]:
        raise ProtocolError("launch record/envelope-spec digest mismatch")
    if launch["output_path"] not in {
        item["path"] for item in spec["files"]
    }:
        raise ProtocolError("launch output path is not declared by its envelope spec")
    attempt_root = require_external_path(attempt_root, "fresh attempt root")
    if str(attempt_root) != launch["output_root"]:
        raise ProtocolError("fresh attempt root does not equal launch-bound output root")
    if is_within(attempt_root, state_root) or is_within(state_root, attempt_root):
        raise ProtocolError("attempt root and protocol state root must be disjoint")
    input_root = Path(launch["input_root"]).resolve()
    for left, right, label in (
        (input_root, state_root, "input/state"),
        (input_root, attempt_root, "input/attempt"),
    ):
        if is_within(left, right) or is_within(right, left):
            raise ProtocolError(f"launch roots are not pairwise disjoint: {label}")
    if not attempt_root.parent.is_dir():
        raise ProtocolError("fresh attempt root parent must already exist")
    root_claim_id = sha256(str(attempt_root).encode("utf-8"))
    lease = {
        "schema_version": 1,
        "status": "STARTED",
        "slot_id": slot_id,
        "attempt_id": f"{slot_id}-{secrets.token_hex(12)}",
        "agent_id": agent_id,
        "lease_token": secrets.token_hex(32),
        "launch_record_sha256": sha256(launch_bytes),
        "launch_record_bytes_base64": base64.b64encode(launch_bytes).decode("ascii"),
        "attempt_root": str(attempt_root),
        "attempt_root_claim_sha256": root_claim_id,
        "envelope_spec_sha256": sha256(spec_bytes),
        "envelope_spec_bytes_base64": base64.b64encode(spec_bytes).decode("ascii"),
    }
    lease_path = state_root / "slots" / slot_id / "lease.json"
    agent_claim_path = state_root / "agents" / agent_id / "claim.json"
    root_claim_path = state_root / "attempt-roots" / f"{root_claim_id}.json"
    with operation_lock(state_root):
        if lease_path.exists():
            raise LeaseAlreadyExists(f"slot {slot_id} already has a started lease; retry is forbidden")
        if agent_claim_path.exists():
            raise LeaseAlreadyExists(f"agent {agent_id} already has an attempt; freshness is required")
        if root_claim_path.exists() or attempt_root.exists():
            raise LeaseAlreadyExists("attempt root is not fresh or was previously claimed")
        os.mkdir(attempt_root, mode=0o700)
        claim = {
            "schema_version": 1,
            "slot_id": slot_id,
            "agent_id": agent_id,
            "attempt_root": str(attempt_root),
            "launch_record_sha256": lease["launch_record_sha256"],
        }
        try:
            exclusive_write(agent_claim_path, canonical_json_bytes(claim))
            exclusive_write(root_claim_path, canonical_json_bytes(claim))
            exclusive_write(lease_path, canonical_json_bytes(lease))
        except FileExistsError as error:
            raise LeaseAlreadyExists("slot, agent, or attempt root was concurrently claimed") from error
        os.chmod(agent_claim_path, 0o400)
        os.chmod(root_claim_path, 0o400)
        os.chmod(lease_path, 0o400)
        fsync_directory(lease_path.parent)
    return lease


def scan_output(root: Path) -> list[dict[str, Any]]:
    if not root.exists():
        return []
    entries: list[dict[str, Any]] = []

    def identity(info: os.stat_result) -> tuple[int, int, int, int, int, int]:
        return (
            info.st_dev,
            info.st_ino,
            info.st_mode,
            info.st_size,
            info.st_mtime_ns,
            info.st_ctime_ns,
        )

    def stable_file_bytes(directory_fd: int, name: str, listed: os.stat_result) -> bytes:
        flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0)
        fd = os.open(name, flags, dir_fd=directory_fd)
        try:
            opened = os.fstat(fd)
            if identity(listed) != identity(opened) or not stat.S_ISREG(opened.st_mode):
                raise ProtocolError(f"output entry changed during stable open: {name}")
            chunks: list[bytes] = []
            while True:
                chunk = os.read(fd, 1024 * 1024)
                if not chunk:
                    break
                chunks.append(chunk)
            after = os.fstat(fd)
            data = b"".join(chunks)
            if identity(opened) != identity(after) or len(data) != after.st_size:
                raise ProtocolError(f"output file changed during capture: {name}")
            return data
        finally:
            os.close(fd)

    directory_flags = (
        os.O_RDONLY
        | getattr(os, "O_DIRECTORY", 0)
        | getattr(os, "O_NOFOLLOW", 0)
    )

    def visit(directory_fd: int, prefix: PurePosixPath) -> None:
        before = os.fstat(directory_fd)
        if not stat.S_ISDIR(before.st_mode):
            raise ProtocolError("output traversal descriptor is not a directory")
        with os.scandir(directory_fd) as iterator:
            current = sorted(iterator, key=lambda item: item.name)
        for entry in current:
            relative = (prefix / entry.name).as_posix()
            listed = os.stat(entry.name, dir_fd=directory_fd, follow_symlinks=False)
            if stat.S_ISLNK(listed.st_mode):
                entries.append({"path": relative, "kind": "symlink"})
            elif stat.S_ISDIR(listed.st_mode):
                entries.append({"path": relative, "kind": "directory"})
                child_fd = os.open(entry.name, directory_flags, dir_fd=directory_fd)
                try:
                    if identity(listed) != identity(os.fstat(child_fd)):
                        raise ProtocolError(f"output directory changed during stable open: {relative}")
                    visit(child_fd, prefix / entry.name)
                finally:
                    os.close(child_fd)
                after = os.stat(entry.name, dir_fd=directory_fd, follow_symlinks=False)
                if identity(listed) != identity(after):
                    raise ProtocolError(f"output directory changed during capture: {relative}")
            elif stat.S_ISREG(listed.st_mode):
                data = stable_file_bytes(directory_fd, entry.name, listed)
                entries.append({"path": relative, "kind": "file", "data": data})
            else:
                entries.append({"path": relative, "kind": "special"})
        after = os.fstat(directory_fd)
        if identity(before) != identity(after):
            raise ProtocolError(f"output directory changed during traversal: {prefix.as_posix()}")

    try:
        root_fd = os.open(root, directory_flags)
    except (NotADirectoryError, OSError) as error:
        raise ProtocolError("attempt output root is not a stable non-symlink directory") from error
    try:
        root_identity = identity(os.fstat(root_fd))
        visit(root_fd, PurePosixPath())
        if identity(os.stat(root, follow_symlinks=False)) != root_identity:
            raise ProtocolError("attempt output root path changed during traversal")
    finally:
        os.close(root_fd)
    return entries


def capture_envelope(
    stage: Path,
    lease: dict[str, Any],
    spec: dict[str, Any],
    attempt_root: Path,
    final_response: bytes | None,
    process_disposition: str,
    process_exit_code: int | None,
    metadata: dict[str, Any],
) -> dict[str, Any]:
    violations: list[str] = []
    scanned = scan_output(attempt_root)
    declared = {item["path"]: item for item in spec["files"]}
    scanned_by_path = {item["path"]: item for item in scanned}
    records: list[dict[str, Any]] = []
    total_bytes = 0
    declared_parent_directories = {
        PurePosixPath(*PurePosixPath(path).parts[:index]).as_posix()
        for path in declared
        for index in range(1, len(PurePosixPath(path).parts))
    }
    for entry in scanned:
        path = entry["path"]
        kind = entry["kind"]
        record: dict[str, Any] = {
            "path": path,
            "kind": kind,
            "declared": path in declared or (kind == "directory" and path in declared_parent_directories),
        }
        if kind == "file":
            data = entry["data"]
            total_bytes += len(data)
            record.update({"size": len(data), "sha256": sha256(data)})
            write_stage_file(stage / "payload" / "output" / Path(*PurePosixPath(path).parts), data)
            if path in declared:
                requirement = declared[path]
                if len(data) > requirement["max_bytes"]:
                    violations.append(f"oversize:{path}:{len(data)}:{requirement['max_bytes']}")
                if requirement["utf8"]:
                    try:
                        data.decode("utf-8")
                    except UnicodeDecodeError:
                        violations.append(f"non-utf8:{path}")
            else:
                violations.append(f"unexpected:{path}")
        elif kind == "directory" and path not in declared_parent_directories:
            violations.append(f"unexpected-directory:{path}")
        elif kind in ("symlink", "special", "not-directory"):
            violations.append(f"{kind}:{path}")
        records.append(record)
    for path, requirement in declared.items():
        entry = scanned_by_path.get(path)
        if entry is None:
            if requirement["required"]:
                violations.append(f"missing:{path}")
        elif entry["kind"] != "file":
            violations.append(f"not-regular:{path}:{entry['kind']}")
    if total_bytes > spec["max_total_output_bytes"]:
        violations.append(f"total-output-oversize:{total_bytes}:{spec['max_total_output_bytes']}")

    final_spec = spec["final_response"]
    if final_response is None:
        final_record: dict[str, Any] = {"present": False}
        if final_spec["required"]:
            violations.append("missing:final-response")
    else:
        final_record = {
            "present": True,
            "size": len(final_response),
            "sha256": sha256(final_response),
        }
        write_stage_file(stage / "payload" / "final-response.bin", final_response)
        if len(final_response) > final_spec["max_bytes"]:
            violations.append(f"oversize:final-response:{len(final_response)}:{final_spec['max_bytes']}")
        try:
            final_text = final_response.decode("utf-8")
        except UnicodeDecodeError:
            violations.append("non-utf8:final-response")
        else:
            if re.fullmatch(final_spec["utf8_fullmatch_regex"], final_text) is None:
                violations.append("format:final-response")
    if process_disposition not in spec["allowed_process_dispositions"]:
        violations.append(f"invalid-process-disposition:{process_disposition}")
    if process_exit_code is not None and type(process_exit_code) is not int:
        violations.append("invalid-process-exit-code")
    manifest = {
        "schema_version": 1,
        "identity": {
            "slot_id": lease["slot_id"],
            "attempt_id": lease["attempt_id"],
            "agent_id": lease["agent_id"],
            "lease_sha256": sha256(canonical_json_bytes(lease)),
        },
        "envelope_spec_sha256": lease["envelope_spec_sha256"],
        "output_entries": sorted(records, key=lambda record: record["path"]),
        "total_output_bytes": total_bytes,
        "final_response": final_record,
        "process": {"disposition": process_disposition, "exit_code": process_exit_code},
        "coordinator_metadata": metadata,
        "violations": sorted(set(violations)),
        "format_valid": not violations,
    }
    write_stage_file(stage / "envelope.json", canonical_json_bytes(manifest))
    return manifest


def semantic_verify_envelope(
    object_path: Path,
    lease: dict[str, Any],
    pointer: dict[str, Any],
    terminal_claim: dict[str, Any],
) -> dict[str, Any]:
    """Recompute every envelope semantic from immutable payload bytes and bound inputs."""

    lease = validate_lease(lease)
    spec = load_bound_spec(lease)
    launch = load_bound_launch(lease)
    pointer = require_exact_keys(
        pointer,
        {
            "schema_version",
            "slot_id",
            "attempt_id",
            "agent_id",
            "lease_sha256",
            "launch_record_sha256",
            "terminal_claim_sha256",
            "envelope_sha256",
            "format_valid",
        },
        "canonical pointer",
    )
    terminal_claim = require_exact_keys(
        terminal_claim,
        {
            "schema_version",
            "status",
            "slot_id",
            "attempt_id",
            "agent_id",
            "lease_sha256",
            "attempt_root",
            "final_response_sha256",
            "process_disposition",
            "process_exit_code",
            "metadata_sha256",
        },
        "terminal claim",
    )
    lease_digest = sha256(canonical_json_bytes(lease))
    if (
        pointer["schema_version"] != 1
        or pointer["slot_id"] != lease["slot_id"]
        or pointer["attempt_id"] != lease["attempt_id"]
        or pointer["agent_id"] != lease["agent_id"]
        or pointer["lease_sha256"] != lease_digest
        or pointer["launch_record_sha256"] != lease["launch_record_sha256"]
        or pointer["terminal_claim_sha256"]
        != sha256(canonical_json_bytes(terminal_claim))
        or not isinstance(pointer["envelope_sha256"], str)
        or not HEX64.fullmatch(pointer["envelope_sha256"])
        or type(pointer["format_valid"]) is not bool
    ):
        raise ProtocolError("canonical pointer is not exactly bound to its lease/terminal claim")
    if (
        terminal_claim["schema_version"] != 1
        or terminal_claim["status"] != "TERMINAL-CLAIMED"
        or terminal_claim["slot_id"] != lease["slot_id"]
        or terminal_claim["attempt_id"] != lease["attempt_id"]
        or terminal_claim["agent_id"] != lease["agent_id"]
        or terminal_claim["lease_sha256"] != lease_digest
        or terminal_claim["attempt_root"] != lease["attempt_root"]
        or (
            terminal_claim["final_response_sha256"] is not None
            and (
                not isinstance(terminal_claim["final_response_sha256"], str)
                or not HEX64.fullmatch(terminal_claim["final_response_sha256"])
            )
        )
        or not isinstance(terminal_claim["metadata_sha256"], str)
        or not HEX64.fullmatch(terminal_claim["metadata_sha256"])
    ):
        raise ProtocolError("terminal claim identity/content binding is invalid")
    if not object_path.is_dir() or object_path.name != pointer["envelope_sha256"]:
        raise ProtocolError("canonical object path/digest mismatch")
    if byte_tree_digest(object_path) != pointer["envelope_sha256"]:
        raise ProtocolError("canonical object byte-tree digest mismatch")
    envelope = require_exact_keys(
        read_json(object_path / "envelope.json"),
        {
            "schema_version",
            "identity",
            "envelope_spec_sha256",
            "output_entries",
            "total_output_bytes",
            "final_response",
            "process",
            "coordinator_metadata",
            "violations",
            "format_valid",
        },
        "attempt envelope",
    )
    identity_record = require_exact_keys(
        envelope["identity"], {"slot_id", "attempt_id", "agent_id", "lease_sha256"}, "envelope identity"
    )
    if envelope["schema_version"] != 1 or identity_record != {
        "slot_id": lease["slot_id"],
        "attempt_id": lease["attempt_id"],
        "agent_id": lease["agent_id"],
        "lease_sha256": lease_digest,
    } or envelope["envelope_spec_sha256"] != lease["envelope_spec_sha256"]:
        raise ProtocolError("envelope identity/spec binding mismatch")
    if not isinstance(envelope["coordinator_metadata"], dict) or sha256(
        canonical_json_bytes(envelope["coordinator_metadata"])
    ) != terminal_claim["metadata_sha256"]:
        raise ProtocolError("envelope coordinator metadata does not match terminal claim")

    declared = {item["path"]: item for item in spec["files"]}
    declared_parent_directories = {
        PurePosixPath(*PurePosixPath(path).parts[:index]).as_posix()
        for path in declared
        for index in range(1, len(PurePosixPath(path).parts))
    }
    records = envelope["output_entries"]
    if not isinstance(records, list):
        raise ProtocolError("envelope output entries must be a list")
    seen_paths: list[str] = []
    total_bytes = 0
    violations: list[str] = []
    file_records: dict[str, dict[str, Any]] = {}
    for raw in records:
        if not isinstance(raw, dict):
            raise ProtocolError("envelope output record is not an object")
        kind = raw.get("kind")
        expected_keys = {"path", "kind", "declared", "size", "sha256"} if kind == "file" else {
            "path",
            "kind",
            "declared",
        }
        record = require_exact_keys(raw, expected_keys, "envelope output record")
        path = require_relative_file(record["path"], "envelope output path")
        if kind not in ("file", "directory", "symlink", "special", "not-directory"):
            raise ProtocolError("envelope output record kind is invalid")
        expected_declared = path in declared or (
            kind == "directory" and path in declared_parent_directories
        )
        if type(record["declared"]) is not bool or record["declared"] is not expected_declared:
            raise ProtocolError("envelope declared flag is not recomputable")
        seen_paths.append(path)
        if kind == "file":
            if (
                type(record["size"]) is not int
                or record["size"] < 0
                or not isinstance(record["sha256"], str)
                or not HEX64.fullmatch(record["sha256"])
            ):
                raise ProtocolError("envelope file record size/digest is invalid")
            payload_path = object_path / "payload" / "output" / Path(
                *PurePosixPath(path).parts
            )
            if not payload_path.is_file() or payload_path.is_symlink():
                raise ProtocolError(f"envelope payload file is missing or non-regular: {path}")
            data = payload_path.read_bytes()
            if len(data) != record["size"] or sha256(data) != record["sha256"]:
                raise ProtocolError(f"envelope payload bytes disagree with record: {path}")
            total_bytes += len(data)
            file_records[path] = record
            requirement = declared.get(path)
            if requirement is None:
                violations.append(f"unexpected:{path}")
            else:
                if len(data) > requirement["max_bytes"]:
                    violations.append(
                        f"oversize:{path}:{len(data)}:{requirement['max_bytes']}"
                    )
                if requirement["utf8"]:
                    try:
                        data.decode("utf-8")
                    except UnicodeDecodeError:
                        violations.append(f"non-utf8:{path}")
        elif kind == "directory" and path not in declared_parent_directories:
            violations.append(f"unexpected-directory:{path}")
        elif kind in ("symlink", "special", "not-directory"):
            violations.append(f"{kind}:{path}")
    if seen_paths != sorted(seen_paths) or len(seen_paths) != len(set(seen_paths)):
        raise ProtocolError("envelope output records are not unique and sorted")
    payload_output = object_path / "payload" / "output"
    actual_payload_files: set[str] = set()
    if payload_output.exists():
        for path in payload_output.rglob("*"):
            if path.is_symlink() or (not path.is_file() and not path.is_dir()):
                raise ProtocolError("canonical payload contains a non-regular entry")
            if path.is_file():
                actual_payload_files.add(path.relative_to(payload_output).as_posix())
    if actual_payload_files != set(file_records):
        raise ProtocolError("canonical payload file set does not equal envelope file records")
    for path, requirement in declared.items():
        record = next((item for item in records if item["path"] == path), None)
        if record is None:
            if requirement["required"]:
                violations.append(f"missing:{path}")
        elif record["kind"] != "file":
            violations.append(f"not-regular:{path}:{record['kind']}")
    if total_bytes > spec["max_total_output_bytes"]:
        violations.append(
            f"total-output-oversize:{total_bytes}:{spec['max_total_output_bytes']}"
        )
    if envelope["total_output_bytes"] != total_bytes:
        raise ProtocolError("envelope total output byte count mismatch")

    final_record = envelope["final_response"]
    if not isinstance(final_record, dict) or type(final_record.get("present")) is not bool:
        raise ProtocolError("envelope final-response record is invalid")
    final_path = object_path / "payload" / "final-response.bin"
    if final_record["present"]:
        require_exact_keys(final_record, {"present", "size", "sha256"}, "final response")
        if not final_path.is_file() or final_path.is_symlink():
            raise ProtocolError("present final response lacks regular payload bytes")
        final_bytes = final_path.read_bytes()
        if (
            type(final_record["size"]) is not int
            or final_record["size"] != len(final_bytes)
            or final_record["sha256"] != sha256(final_bytes)
            or terminal_claim["final_response_sha256"] != sha256(final_bytes)
        ):
            raise ProtocolError("final response payload/digest/terminal claim mismatch")
        if len(final_bytes) > spec["final_response"]["max_bytes"]:
            violations.append(
                f"oversize:final-response:{len(final_bytes)}:{spec['final_response']['max_bytes']}"
            )
        try:
            final_text = final_bytes.decode("utf-8")
        except UnicodeDecodeError:
            violations.append("non-utf8:final-response")
        else:
            if re.fullmatch(spec["final_response"]["utf8_fullmatch_regex"], final_text) is None:
                violations.append("format:final-response")
    else:
        require_exact_keys(final_record, {"present"}, "absent final response")
        if final_path.exists() or terminal_claim["final_response_sha256"] is not None:
            raise ProtocolError("absent final response has payload bytes or terminal digest")
        if spec["final_response"]["required"]:
            violations.append("missing:final-response")

    process = require_exact_keys(envelope["process"], {"disposition", "exit_code"}, "process")
    if (
        process["disposition"] != terminal_claim["process_disposition"]
        or process["exit_code"] != terminal_claim["process_exit_code"]
    ):
        raise ProtocolError("process result does not match terminal claim")
    if process["disposition"] not in spec["allowed_process_dispositions"]:
        violations.append(f"invalid-process-disposition:{process['disposition']}")
    if process["exit_code"] is not None and type(process["exit_code"]) is not int:
        violations.append("invalid-process-exit-code")
    expected_violations = sorted(set(violations))
    if envelope["violations"] != expected_violations:
        raise ProtocolError("envelope violations do not equal semantic recomputation")
    expected_valid = not expected_violations
    if type(envelope["format_valid"]) is not bool or envelope["format_valid"] is not expected_valid:
        raise ProtocolError("envelope format_valid disagrees with semantic recomputation")
    if pointer["format_valid"] is not expected_valid:
        raise ProtocolError("canonical pointer format_valid disagrees with envelope")
    if launch["role"] == "report" and launch["output_path"] not in declared:
        raise ProtocolError("bound report output is absent from envelope declaration")
    return envelope


def seal_attempt(
    state_root: Path,
    slot_id: str,
    lease_token: str,
    agent_id: str,
    attempt_root: Path,
    final_response: bytes | None,
    process_disposition: str,
    process_exit_code: int | None,
    metadata: dict[str, Any],
) -> dict[str, Any]:
    state_root = require_external_path(state_root, "state root")
    attempt_root = require_external_path(attempt_root, "attempt output root")
    slot_id = require_safe_id(slot_id, "slot ID")
    agent_id = require_safe_id(agent_id, "agent ID")
    if not isinstance(lease_token, str) or not re.fullmatch(r"[0-9a-f]{64}", lease_token):
        raise ProtocolError("invalid lease token")
    if not isinstance(metadata, dict):
        raise ProtocolError("coordinator metadata must be an object")
    lease_path = state_root / "slots" / slot_id / "lease.json"
    canonical_path = state_root / "slots" / slot_id / "canonical.json"
    terminal_claim_path = state_root / "slots" / slot_id / "terminal-claim.json"
    seal_failure_path = state_root / "slots" / slot_id / "seal-failure.json"
    with operation_lock(state_root):
        if canonical_path.exists():
            raise CanonicalAlreadySealed(f"slot {slot_id} already has a canonical first-terminal envelope")
        if terminal_claim_path.exists():
            raise TerminalAlreadyClaimed(
                f"slot {slot_id} already consumed its one terminal seal transition"
            )
        if not lease_path.is_file():
            raise ProtocolError(f"slot {slot_id} has no started lease")
        lease = validate_lease(read_json(lease_path))
        if (
            lease.get("slot_id") != slot_id
            or lease.get("agent_id") != agent_id
            or lease.get("lease_token") != lease_token
        ):
            raise ProtocolError("lease identity/token mismatch")
        if attempt_root != Path(lease["attempt_root"]).resolve():
            raise ProtocolError("seal attempt root does not equal the fresh root bound by the lease")
        launch = load_bound_launch(lease)
        spec = load_bound_spec(lease)
        if launch["envelope_spec_sha256"] != lease["envelope_spec_sha256"]:
            raise ProtocolError("launch/lease envelope-spec binding mismatch")
        terminal_claim = {
            "schema_version": 1,
            "status": "TERMINAL-CLAIMED",
            "slot_id": slot_id,
            "attempt_id": lease["attempt_id"],
            "agent_id": agent_id,
            "lease_sha256": sha256(canonical_json_bytes(lease)),
            "attempt_root": lease["attempt_root"],
            "final_response_sha256": sha256(final_response) if final_response is not None else None,
            "process_disposition": process_disposition,
            "process_exit_code": process_exit_code,
            "metadata_sha256": sha256(canonical_json_bytes(metadata)),
        }
        exclusive_write(terminal_claim_path, canonical_json_bytes(terminal_claim))
        os.chmod(terminal_claim_path, 0o400)
        fsync_directory(terminal_claim_path.parent)
        objects = state_root / "objects" / "sha256"
        try:
            objects.mkdir(parents=True, exist_ok=True)
            stage = objects / f".stage-{slot_id}-{secrets.token_hex(16)}"
            stage.mkdir(mode=0o700)
            manifest = capture_envelope(
                stage,
                lease,
                spec,
                attempt_root,
                final_response,
                process_disposition,
                process_exit_code,
                metadata,
            )
            fsync_tree(stage)
            digest = byte_tree_digest(stage)
            harden_tree_read_only(stage)
            object_path = objects / digest
            if object_path.exists():
                raise ProtocolError(f"unexpected pre-existing envelope object: {digest}")
            os.rename(stage, object_path)
            fsync_directory(objects)
            pointer = {
                "schema_version": 1,
                "slot_id": slot_id,
                "attempt_id": lease["attempt_id"],
                "agent_id": agent_id,
                "lease_sha256": sha256(canonical_json_bytes(lease)),
                "launch_record_sha256": lease["launch_record_sha256"],
                "terminal_claim_sha256": sha256(canonical_json_bytes(terminal_claim)),
                "envelope_sha256": digest,
                "format_valid": manifest["format_valid"],
            }
            try:
                exclusive_write(canonical_path, canonical_json_bytes(pointer))
            except FileExistsError as error:
                raise CanonicalAlreadySealed(f"slot {slot_id} lost the first-terminal CAS") from error
        except BaseException as error:
            failure = {
                "schema_version": 1,
                "status": "SEAL-FAILED",
                "slot_id": slot_id,
                "attempt_id": lease["attempt_id"],
                "terminal_claim_sha256": sha256(canonical_json_bytes(terminal_claim)),
                "error_type": type(error).__name__,
            }
            try:
                exclusive_write(seal_failure_path, canonical_json_bytes(failure))
                os.chmod(seal_failure_path, 0o400)
                fsync_directory(seal_failure_path.parent)
            except BaseException:
                pass
            raise
        os.chmod(canonical_path, 0o400)
        os.chmod(canonical_path.parent, 0o500)
        fsync_directory(canonical_path.parent)
        fsync_directory(canonical_path.parent.parent)
    return pointer


def verify_state(state_root: Path) -> dict[str, Any]:
    state_root = require_external_path(state_root, "state root")
    slots_root = state_root / "slots"
    results: list[dict[str, Any]] = []
    if not slots_root.exists():
        return {"schema_version": 1, "slots": []}
    for slot_path in sorted((path for path in slots_root.iterdir() if path.is_dir()), key=lambda path: path.name):
        slot_id = require_safe_id(slot_path.name, "slot directory")
        allowed_names = {"lease.json", "terminal-claim.json", "canonical.json", "seal-failure.json"}
        unexpected = {path.name for path in slot_path.iterdir()} - allowed_names
        if unexpected:
            raise ProtocolError(f"unexpected slot ledger entries for {slot_id}: {sorted(unexpected)}")
        lease_path = slot_path / "lease.json"
        if not lease_path.is_file() or lease_path.is_symlink():
            raise ProtocolError(f"slot {slot_id} lacks a regular lease ledger")
        lease = validate_lease(read_json(lease_path))
        if lease_path.lstat().st_mode & 0o222:
            raise ProtocolError(f"started lease is writable for slot {slot_id}")
        if lease["slot_id"] != slot_id:
            raise ProtocolError(f"invalid lease identity/status for slot {slot_id}")
        expected_claim = {
            "schema_version": 1,
            "slot_id": slot_id,
            "agent_id": lease["agent_id"],
            "attempt_root": lease["attempt_root"],
            "launch_record_sha256": lease["launch_record_sha256"],
        }
        root_claim_id = lease["attempt_root_claim_sha256"]
        for claim_path, label in (
            (state_root / "agents" / lease["agent_id"] / "claim.json", "agent"),
            (state_root / "attempt-roots" / f"{root_claim_id}.json", "attempt-root"),
        ):
            if (
                not claim_path.is_file()
                or claim_path.is_symlink()
                or read_json(claim_path) != expected_claim
                or claim_path.lstat().st_mode & 0o222
            ):
                raise ProtocolError(f"slot {slot_id} has an invalid {label} uniqueness claim")
        canonical_path = slot_path / "canonical.json"
        terminal_path = slot_path / "terminal-claim.json"
        failure_path = slot_path / "seal-failure.json"
        if not terminal_path.exists():
            if canonical_path.exists() or failure_path.exists():
                raise ProtocolError(f"slot {slot_id} has terminal artifacts without a claim")
            results.append({"slot_id": slot_id, "status": "STARTED"})
            continue
        if not terminal_path.is_file() or terminal_path.is_symlink() or terminal_path.lstat().st_mode & 0o222:
            raise ProtocolError(f"slot {slot_id} terminal claim is not immutable/regular")
        terminal_claim = read_json(terminal_path)
        terminal_claim_digest = sha256(canonical_json_bytes(terminal_claim))
        if not canonical_path.exists():
            if failure_path.exists():
                failure = require_exact_keys(
                    read_json(failure_path),
                    {
                        "schema_version",
                        "status",
                        "slot_id",
                        "attempt_id",
                        "terminal_claim_sha256",
                        "error_type",
                    },
                    "seal failure",
                )
                if (
                    failure["schema_version"] != 1
                    or failure["status"] != "SEAL-FAILED"
                    or failure["slot_id"] != slot_id
                    or failure["attempt_id"] != lease["attempt_id"]
                    or failure["terminal_claim_sha256"] != terminal_claim_digest
                    or not isinstance(failure["error_type"], str)
                    or not failure["error_type"]
                    or failure_path.lstat().st_mode & 0o222
                ):
                    raise ProtocolError(f"invalid failed-seal ledger for slot {slot_id}")
                results.append(
                    {
                        "slot_id": slot_id,
                        "status": "SEAL_FAILED",
                        "format_valid": False,
                    }
                )
            else:
                results.append(
                    {
                        "slot_id": slot_id,
                        "status": "TERMINAL_CLAIMED_INCOMPLETE",
                        "format_valid": False,
                    }
                )
            continue
        if failure_path.exists():
            raise ProtocolError(f"slot {slot_id} has both canonical and failed-seal ledgers")
        pointer = read_json(canonical_path)
        if slot_path.lstat().st_mode & 0o222:
            raise ProtocolError(f"sealed slot directory is writable for slot {slot_id}")
        if canonical_path.lstat().st_mode & 0o222:
            raise ProtocolError(f"canonical pointer is writable for slot {slot_id}")
        digest = pointer.get("envelope_sha256")
        if not isinstance(digest, str) or not HEX64.fullmatch(digest):
            raise ProtocolError(f"invalid envelope digest for slot {slot_id}")
        object_path = state_root / "objects" / "sha256" / digest
        for path in (object_path, *object_path.rglob("*")):
            if path.lstat().st_mode & 0o222:
                raise ProtocolError(f"published envelope object is not read-only: {path}")
        envelope = semantic_verify_envelope(
            object_path, lease, pointer, terminal_claim
        )
        results.append({"slot_id": slot_id, "status": "SEALED", "envelope_sha256": digest, "format_valid": envelope["format_valid"]})
    return {"schema_version": 1, "slots": results}


def verify_draft() -> None:
    from prepare import verify_draft as verify_preparation

    verify_preparation()
    inventory = validate_root_inventory(read_json(RUN / "root-inventory.json"))
    gate_manifest = validate_gate_manifest(read_json(RUN / "gate-manifest.json"), inventory)
    required_files = {
        "plan.md",
        "prepare.py",
        "protocol.py",
        "root-inventory.json",
        "gate-manifest.json",
        "integration-hooks.json",
        "comparison-predicate.json",
        "aggregation-rules.json",
        "runtime-policy.json",
        "report-projection-contract.json",
        "materiality-review-contract.json",
        "word_count.py",
        "prompts/report-controlled.md",
        "prompts/report-naturalistic.md",
        "prompts/scorer.md",
        "prompts/consistency.md",
        "prompts/adjudicator.md",
        "prompts/materiality-reviewer.md",
        "prompts/materiality-adjudicator.md",
        "policies/isolation.md",
        "policies/attempts-and-finalization.md",
        "policies/tools.md",
        "policies/word-count.md",
        "policies/scoring.md",
        "randomization/spec.md",
        "schemas/atom-manifest.schema.json",
        "schemas/score.schema.json",
        "schemas/final-score.schema.json",
        "schemas/consistency.schema.json",
        "schemas/adjudication-packet.schema.json",
        "schemas/adjudication.schema.json",
        "schemas/defect-rules.schema.json",
        "schemas/envelope-spec.schema.json",
        "schemas/attempt-envelope.schema.json",
        "schemas/root-inventory.schema.json",
        "schemas/gate-manifest.schema.json",
        "schemas/gate-results.schema.json",
        "schemas/integration-hooks.schema.json",
        "schemas/comparison-predicate.schema.json",
        "schemas/agent-authority-packet.schema.json",
        "schemas/aggregate-context.schema.json",
        "schemas/aggregation-rules.schema.json",
        "schemas/consistency-input-packet.schema.json",
        "schemas/control-manifest.schema.json",
        "schemas/fixture-manifest.schema.json",
        "schemas/launch-record.schema.json",
        "schemas/materiality-adjudication.schema.json",
        "schemas/materiality-ledger.schema.json",
        "schemas/materiality-review.schema.json",
        "schemas/report-projection-audit-receipt.schema.json",
        "schemas/report-projection-contract.schema.json",
        "schemas/report-projection-receipt.schema.json",
        "schemas/report-secret-inventory.schema.json",
        "schemas/runtime-policy.schema.json",
        "schemas/score-input-packet.schema.json",
        "schemas/scoring-bundle-manifest.schema.json",
        "schemas/word-count-receipt.schema.json",
        "freeze/controls.json",
        "freeze/controls-completeness.md",
        "freeze/validate_controls.py",
        "freeze/validate_oracle_materials.py",
        "freeze/rules/defect-rules.json",
        "freeze/authority/propositions.json",
        "freeze/authority/quotation-locators.json",
        "freeze/authority/verification.json",
        "freeze/authority/validate_agent_visible.py",
        "freeze/authority/agent-visible/common.json",
        *(f"freeze/atoms/{mode}.json" for mode in MODES),
        *(f"freeze/oracle/{mode}.md" for mode in MODES),
        *(f"freeze/allowlists/{mode}.txt" for mode in MODES),
    }
    missing = sorted(name for name in required_files if not (RUN / name).is_file())
    if missing:
        raise ProtocolError(f"missing DRAFT harness files: {missing}")
    validate_integration_hooks(read_json(RUN / "integration-hooks.json"))
    validate_comparison_predicate(read_json(RUN / "comparison-predicate.json"))
    validate_aggregation_rules(read_json(RUN / "aggregation-rules.json"), gate_manifest)
    validate_report_projection_contract(read_json(RUN / "report-projection-contract.json"))
    validate_materiality_contract(read_json(RUN / "materiality-review-contract.json"))
    atom_directory = RUN / "freeze" / "atoms"
    if atom_directory.exists():
        atom_paths = sorted(path.name for path in atom_directory.glob("*.json"))
        expected_atom_paths = sorted(f"{mode}.json" for mode in MODES)
        if atom_paths != expected_atom_paths:
            raise ProtocolError("DRAFT atom directory must contain exactly one manifest per mode")
        for mode in MODES:
            validate_atom_manifest(read_json(atom_directory / f"{mode}.json"), mode)
    defect_path = RUN / "freeze" / "rules" / "defect-rules.json"
    if defect_path.exists():
        validate_defect_rules(read_json(defect_path))
    validate_control_manifest(read_json(RUN / "freeze" / "controls.json"))
    runpy.run_path(str(RUN / "freeze" / "validate_controls.py"), run_name="v5_controls")[
        "main"
    ]()
    runpy.run_path(
        str(RUN / "freeze" / "validate_oracle_materials.py"), run_name="v5_oracles"
    )["main"]()
    projection_digest = runpy.run_path(
        str(RUN / "freeze" / "authority" / "validate_agent_visible.py"),
        run_name="v5_authority_projection",
    )["validate"]()
    if projection_digest != sha256(
        (RUN / "freeze" / "authority" / "agent-visible" / "common.json").read_bytes()
    ):
        raise ProtocolError("agent-visible authority projection digest mismatch")
    evaluator_prompt_markers = {
        "prompts/scorer.md": {
            "{{MODE}}",
            "{{SCORER_ID}}",
            "{{INPUT_ROOT}}",
            "{{INPUT_PACKET_PATH}}",
            "{{SCORE_SCHEMA_PATH}}",
            "{{OUTPUT_ROOT}}",
            "{{OUTPUT_PATH}}",
        },
        "prompts/consistency.md": {
            "{{REVIEWER_ID}}",
            "{{INPUT_ROOT}}",
            "{{INPUT_PACKET_PATH}}",
            "{{CONSISTENCY_SCHEMA_PATH}}",
            "{{OUTPUT_ROOT}}",
            "{{OUTPUT_PATH}}",
        },
        "prompts/adjudicator.md": {
            "{{INPUT_ROOT}}",
            "{{INPUT_PACKET_PATH}}",
            "{{ADJUDICATION_SCHEMA_PATH}}",
            "{{OUTPUT_ROOT}}",
            "{{OUTPUT_PATH}}",
        },
        "prompts/materiality-reviewer.md": {
            "{{REVIEWER_ID}}",
            "{{INPUT_ROOT}}",
            "{{INPUT_PACKET_PATH}}",
            "{{REVIEW_SCHEMA_PATH}}",
            "{{OUTPUT_ROOT}}",
            "{{OUTPUT_PATH}}",
        },
        "prompts/materiality-adjudicator.md": {
            "{{INPUT_ROOT}}",
            "{{INPUT_PACKET_PATH}}",
            "{{ADJUDICATION_SCHEMA_PATH}}",
            "{{OUTPUT_ROOT}}",
            "{{OUTPUT_PATH}}",
        },
    }
    for relative, expected_markers in evaluator_prompt_markers.items():
        template = (RUN / relative).read_text(encoding="utf-8")
        observed_markers = set(re.findall(r"\{\{[A-Z0-9_]+\}\}", template))
        if observed_markers != expected_markers or any(
            template.count(marker) != 1 for marker in expected_markers
        ):
            raise ProtocolError(f"evaluator prompt marker contract drifted: {relative}")
    forbidden_names = {
        "LOCK.json",
        "file-manifest.sha256",
        "seeds.json",
        "events.jsonl",
        "condition-map.json",
        "target-map.json",
        "launch-schedule.json",
        "blind-map.json",
        "presentation-orders.json",
        "scoring-schedule.json",
        "consistency-schedule.json",
        "randomization-commitments.json",
    }
    present = sorted(path.relative_to(RUN).as_posix() for path in RUN.rglob("*") if path.name in forbidden_names)
    if present:
        raise ProtocolError(f"DRAFT contains forbidden integration/evidence files: {present}")
    forbidden_artifacts = sorted(
        path.relative_to(RUN).as_posix()
        for path in RUN.rglob("*")
        if path.name == "__pycache__"
        or path.suffix == ".pyc"
        or path == RUNTIME_ROOT
        or path.name.startswith(".stage-")
    )
    if forbidden_artifacts:
        raise ProtocolError(f"DRAFT contains interpreter/runtime/stage artifacts: {forbidden_artifacts}")
    for schema_path in sorted((RUN / "schemas").glob("*.json")):
        schema = read_json(schema_path)
        if schema.get("$schema") != "https://json-schema.org/draft/2020-12/schema" or "DRAFT" not in schema.get("$comment", ""):
            raise ProtocolError(f"schema lacks DRAFT marker: {schema_path.name}")
    print("DRAFT protocol/static design validation passed")


def self_test() -> None:
    validate_report_projection_contract(read_json(RUN / "report-projection-contract.json"))
    projection_inventory = {
        "schema_version": 1,
        "status": "READY",
        "tokens": [
            {
                "category": "TREATMENT_INSTRUCTION_OR_PACKAGE_IDENTITY",
                "value": "/coordinator/private/package-candidate-7f3a",
                "provenance": "synthetic launch package path",
                "match_kind": "EXACT_ABSOLUTE_PATH",
            }
        ],
        "protected_target_values": ["src/rev5x.rs", "technical condition"],
    }
    raw_projection_test = (
        b"Inspect src/rev5x.rs under the technical condition; nominal path "
        b"/coordinator/private/package-candidate-7f3a must not appear."
    )
    projected, scorer_receipt, audit_receipt = project_report_for_scorer(
        "A", raw_projection_test, projection_inventory
    )
    expected_projected = raw_projection_test.replace(
        b"/coordinator/private/package-candidate-7f3a", b"[REDACTED:NOMINAL]"
    )
    assert projected == expected_projected
    assert b"src/rev5x.rs" in projected and b"technical condition" in projected
    assert set(scorer_receipt) == {
        "schema_version",
        "status",
        "label",
        "projected_report_sha256",
        "redaction_present",
        "replacement_count",
    }
    assert scorer_receipt["redaction_present"] is True
    assert audit_receipt["raw_report_sha256"] == sha256(raw_projection_test)
    bad_projection_inventory = copy.deepcopy(projection_inventory)
    bad_projection_inventory["tokens"][0]["value"] = "v5"
    try:
        project_report_for_scorer("A", raw_projection_test, bad_projection_inventory)
    except ProtocolError:
        pass
    else:
        raise AssertionError("short generic projection token was accepted")

    synthetic_atoms = {
        "schema_version": 1,
        "status": "DRAFT",
        "mode": "E",
        "atoms": [
            {"id": "E1", "direct_criterion": "Synthetic root criterion.", "prerequisites": [], "authority_dependencies": [], "applicability": "REQUIRED"},
            {"id": "E2", "direct_criterion": "Synthetic dependent criterion.", "prerequisites": ["E1"], "authority_dependencies": ["SYNTHETIC"], "applicability": "REQUIRED"},
            {"id": "E3", "direct_criterion": "Synthetic joint criterion.", "prerequisites": ["E1", "E2"], "authority_dependencies": [], "applicability": "REQUIRED"},
        ],
    }
    validate_atom_manifest(synthetic_atoms, "E")
    certificates = compute_atom_certificates(synthetic_atoms, {"E1": "FAIL", "E2": "PASS", "E3": "FAIL"})
    by_atom = {row["id"]: row for row in certificates["atoms"]}
    assert by_atom["E2"]["blocked_by"] == ["E1"]
    assert by_atom["E2"]["root_failures"] == ["E1"]
    assert by_atom["E3"]["direct_decision"] == "FAIL"
    assert by_atom["E3"]["blocked_by"] == ["E1", "E2"]
    assert by_atom["E3"]["root_failures"] == ["E1", "E3"]
    for bad_direct in ({"E1": "PASS"}, {"E1": "PASS", "E2": "PASS", "E3": "ERROR"}):
        try:
            compute_atom_certificates(synthetic_atoms, bad_direct)
        except ProtocolError:
            pass
        else:
            raise AssertionError("invalid direct atom decisions were accepted")
    bad_atoms = copy.deepcopy(synthetic_atoms)
    bad_atoms["atoms"][0]["prerequisites"] = ["E3"]
    try:
        validate_atom_manifest(bad_atoms)
    except ProtocolError:
        pass
    else:
        raise AssertionError("atom cycle was accepted")

    synthetic_rules = {
        "schema_version": 1,
        "status": "DRAFT",
        "common_hard_errors": [
            {"id": "GH1", "criterion": "Synthetic common false-affirmative rule."}
        ],
        "global_defects": [
            {"id": "GD1", "criterion": "Synthetic cross-mode defect rule."}
        ],
        "modes": {
            mode: {
                "hard_errors": [
                    {
                        "id": f"{mode}H1",
                        "criterion": f"Synthetic mode {mode} false-affirmative rule.",
                    }
                ]
            }
            for mode in MODES
        },
        "novel_findings": {
            "id_pattern": r"^s[12]-N[1-9][0-9]*$",
            "routing": "MANDATORY_ADJUDICATION",
        },
    }
    validate_defect_rules(synthetic_rules)

    def synthetic_score_packet(scorer: str) -> dict[str, Any]:
        return {
            "schema_version": 1,
            "status": "SCORER-INPUT-PACKET",
            "mode": "E",
            "scorer_id": scorer,
            "input_digests": {
                "projection_bundle_sha256": "1" * 64,
                "atom_manifest_sha256": sha256(canonical_json_bytes(synthetic_atoms)),
                "defect_rules_sha256": sha256(canonical_json_bytes(synthetic_rules)),
                "oracle_sha256": "4" * 64,
                "allowlist_sha256": "5" * 64,
                "evaluator_authority_sha256": "6" * 64,
                "presentation_order_sha256": ("7" if scorer == "s1" else "8") * 64,
            },
            "labels_in_order": list(LABELS),
            "reports": [
                {
                    "label": label,
                    "projected_report_sha256": sha256(f"projected-{label}".encode()),
                    "leakage_receipt_sha256": sha256(f"receipt-{label}".encode()),
                    "gh12_forced_present": False,
                }
                for label in LABELS
            ],
        }

    def synthetic_score(scorer: str, input_packet: dict[str, Any]) -> dict[str, Any]:
        return {
            "schema_version": 1,
            "status": "DIRECT-SCORE",
            "mode": "E",
            "scorer_id": scorer,
            "claim": f"E-{scorer}",
            "input_packet_sha256": sha256(canonical_json_bytes(input_packet)),
            "reports": [
                {
                    "label": label,
                    "atoms": [
                        {
                            "id": atom["id"],
                            "direct_decision": "PASS",
                            "evidence": "Synthetic direct evidence.",
                        }
                        for atom in synthetic_atoms["atoms"]
                    ],
                    "hard_errors": [
                        {"id": "GH1", "present": False, "evidence": "Synthetic absence."},
                        {"id": "EH1", "present": False, "evidence": "Synthetic absence."},
                    ],
                    "global_defects": [
                        {"id": "GD1", "present": False, "evidence": "Synthetic absence."}
                    ],
                    "novel_findings": [],
                }
                for label in LABELS
            ],
        }

    atom_fields, defect_fields = atom_and_defect_fields(synthetic_atoms, synthetic_rules)

    def synthetic_consistency(
        reviewer: str,
        input_packet: dict[str, Any],
        category: str = "VALID_NEW_FINDING",
    ) -> dict[str, Any]:
        return {
            "schema_version": 1,
            "status": "CONSISTENCY-REVIEW",
            "mode": "E",
            "reviewer_id": reviewer,
            "claim": f"E-{reviewer}",
            "input_packet_sha256": sha256(canonical_json_bytes(input_packet)),
            "labels_reviewed": list(LABELS),
            "atom_family_attestations": [
                {
                    "field": field,
                    "labels_reviewed": list(LABELS),
                    "evidence": "Compared this atom family across A-O.",
                }
                for field in atom_fields
            ],
            "defect_family_attestations": [
                {
                    "field": field,
                    "labels_reviewed": list(LABELS),
                    "evidence": "Compared this defect family across A-O.",
                }
                for field in defect_fields
            ],
            "challenges": [],
            "novel_classifications": [
                {
                    "normalized_id": assertion["id"],
                    "category": category,
                    "evidence": "Synthetic six-way classification evidence.",
                }
                for assertion in input_packet["novel_assertions"]
            ],
        }

    score_input_first = synthetic_score_packet("s1")
    score_input_second = synthetic_score_packet("s2")
    clean_first = synthetic_score("s1", score_input_first)
    clean_second = synthetic_score("s2", score_input_second)
    evidence_digest = "e" * 64
    clean_consistency_packet = build_consistency_packet(
        clean_first,
        clean_second,
        score_input_first,
        score_input_second,
        synthetic_atoms,
        synthetic_rules,
        evidence_digest,
    )
    clean_consistency_first = synthetic_consistency("c1", clean_consistency_packet)
    clean_consistency_second = synthetic_consistency("c2", clean_consistency_packet)
    validate_direct_score(
        clean_first, synthetic_atoms, synthetic_rules, "s1", score_input_first
    )
    validate_consistency(
        clean_consistency_first,
        synthetic_atoms,
        synthetic_rules,
        clean_consistency_packet,
        "c1",
    )
    empty_packet = build_adjudication_packet(
        clean_first,
        clean_second,
        score_input_first,
        score_input_second,
        clean_consistency_first,
        clean_consistency_second,
        synthetic_atoms,
        synthetic_rules,
        evidence_digest,
    )
    assert empty_packet["cells"] == []
    clean_final = merge_final_scores(
        clean_first,
        clean_second,
        score_input_first,
        score_input_second,
        clean_consistency_first,
        clean_consistency_second,
        synthetic_atoms,
        synthetic_rules,
        evidence_digest,
        None,
    )
    assert len(clean_final["reports"]) == 15

    first = copy.deepcopy(clean_first)
    second = copy.deepcopy(clean_second)
    report_a_second = report_index(second)["A"]
    report_a_second["atoms"][0]["direct_decision"] = "FAIL"
    for score in (first, second):
        next(item for item in report_index(score)["B"]["hard_errors"] if item["id"] == "GH1")[
            "present"
        ] = True
    next(item for item in report_index(first)["C"]["global_defects"] if item["id"] == "GD1")[
        "present"
    ] = True
    report_index(first)["D"]["novel_findings"].append(
        {
            "id": "s1-N1",
            "description": "Synthetic potentially material finding.",
            "evidence": "Synthetic novel evidence.",
        }
    )
    consistency_packet = build_consistency_packet(
        first,
        second,
        score_input_first,
        score_input_second,
        synthetic_atoms,
        synthetic_rules,
        evidence_digest,
    )
    consistency_first = synthetic_consistency("c1", consistency_packet)
    consistency_second = synthetic_consistency(
        "c2", consistency_packet, "INVALID_ASSERTION"
    )
    consistency_first["challenges"].append(
        {
            "label": "E",
            "field": "atom:E2",
            "proposed_decision": "FAIL",
            "evidence": "Synthetic consistency challenge.",
        }
    )
    packet = build_adjudication_packet(
        first,
        second,
        score_input_first,
        score_input_second,
        consistency_first,
        consistency_second,
        synthetic_atoms,
        synthetic_rules,
        evidence_digest,
    )
    assert len(packet["cells"]) == 5
    decisions: list[dict[str, str]] = []
    for cell in packet["cells"]:
        if cell["field"].startswith("atom:"):
            decision = "PASS"
        elif cell["field"].startswith("hard_error:"):
            decision = "PRESENT"
        elif cell["field"].startswith("global_defect:"):
            decision = "ABSENT"
        elif cell["field"].startswith("novel:"):
            decision = "VALID_NEW_FINDING"
        else:
            raise AssertionError(f"unexpected synthetic adjudication cell: {cell}")
        decisions.append(
            {"cell_id": cell["cell_id"], "decision": decision, "evidence": "Synthetic resolution."}
        )
    adjudication = {
        "schema_version": 1,
        "status": "ADJUDICATED",
        "mode": "E",
        "packet_sha256": sha256(canonical_json_bytes(packet)),
        "resolutions": decisions,
    }
    final_score = merge_final_scores(
        first,
        second,
        score_input_first,
        score_input_second,
        consistency_first,
        consistency_second,
        synthetic_atoms,
        synthetic_rules,
        evidence_digest,
        adjudication,
    )
    final_by_label = {report["label"]: report for report in final_score["reports"]}
    assert final_by_label["B"]["hard_errors"] == ["GH1"]
    assert final_by_label["C"]["global_defects"] == []
    assert len(final_by_label["D"]["novel_findings"]) == 1
    assert final_by_label["D"]["novel_findings"][0]["classification"] == "VALID_NEW_FINDING"
    stale_packet = build_adjudication_packet(
        first,
        second,
        score_input_first,
        score_input_second,
        synthetic_consistency(
            "c1",
            build_consistency_packet(
                first,
                second,
                score_input_first,
                score_input_second,
                synthetic_atoms,
                synthetic_rules,
                "f" * 64,
            ),
        ),
        synthetic_consistency(
            "c2",
            build_consistency_packet(
                first,
                second,
                score_input_first,
                score_input_second,
                synthetic_atoms,
                synthetic_rules,
                "f" * 64,
            ),
            "INVALID_ASSERTION",
        ),
        synthetic_atoms,
        synthetic_rules,
        "f" * 64,
    )
    try:
        validate_adjudication(adjudication, stale_packet)
    except ProtocolError:
        pass
    else:
        raise AssertionError("stale adjudication survived an evidence-packet digest change")
    unknown_rule_score = copy.deepcopy(clean_first)
    unknown_rule_score["reports"][0]["hard_errors"][0]["id"] = "GH999"
    try:
        validate_direct_score(
            unknown_rule_score,
            synthetic_atoms,
            synthetic_rules,
            input_packet=score_input_first,
        )
    except ProtocolError:
        pass
    else:
        raise AssertionError("unknown hard-error rule ID was accepted")
    incomplete_consistency = copy.deepcopy(clean_consistency_first)
    incomplete_consistency["defect_family_attestations"].pop()
    try:
        validate_consistency(
            incomplete_consistency,
            synthetic_atoms,
            synthetic_rules,
            clean_consistency_packet,
        )
    except ProtocolError:
        pass
    else:
        raise AssertionError("incomplete defect-family consistency review was accepted")

    hooks = read_json(RUN / "integration-hooks.json")
    validate_integration_hooks(hooks)
    incomplete_hooks = copy.deepcopy(hooks)
    incomplete_hooks["hooks"].pop()
    try:
        validate_integration_hooks(incomplete_hooks)
    except ProtocolError:
        pass
    else:
        raise AssertionError("incomplete blocking integration-hook inventory was accepted")
    comparison_predicate = read_json(RUN / "comparison-predicate.json")
    validate_comparison_predicate(comparison_predicate)
    weakened_comparison = copy.deepcopy(comparison_predicate)
    weakened_comparison["absolute_v5"]["quantifier"] = "FOR_SOME_MODE"
    try:
        validate_comparison_predicate(weakened_comparison)
    except ProtocolError:
        pass
    else:
        raise AssertionError("weakened comparison predicate was accepted")

    inventory = read_json(RUN / "root-inventory.json")
    gates = read_json(RUN / "gate-manifest.json")
    context = {
        "oracle": {"coverage_pass": True},
        "collection": {"complete": True, "invalid_output_count": 0},
        "scores": {
            "focused_recall_pass": True,
            "proof_quality_pass": True,
            "controls_pass": True,
            "hard_error_count": 0,
            "global_defect_count": 0,
            "material_finding_count": 0,
        },
        "comparison": {"predicate_pass": True},
        "review": {"coherence_pass": True},
    }
    gate_results = evaluate_gates(gates, inventory, context)
    assert gate_results["context_trust"] == "UNBOUND_DRAFT_INPUT"
    by_gate = {row["id"]: row for row in gate_results["gates"]}
    assert by_gate["G-ISOLATION"]["direct_decision"] == "FAIL"
    assert by_gate["G-OUTPUT-FINALIZATION"]["direct_decision"] == "FAIL"
    assert by_gate["D-DIAGNOSTIC-COMPLETION"]["direct_decision"] == "PASS"
    assert by_gate["D-STATIC-INTEGRITY"]["direct_decision"] == "FAIL"
    assert by_gate["D-DIAGNOSTIC-COMPLETION"]["certificate_decision"] == "FAIL"
    assert "D-STATIC-INTEGRITY" in by_gate["D-DIAGNOSTIC-COMPLETION"]["root_failures"]
    assert inventory["release_eligibility"]["eligible"] is False
    missing_context = copy.deepcopy(context)
    del missing_context["oracle"]
    missing_results = evaluate_gates(gates, inventory, missing_context)
    missing_by_gate = {row["id"]: row for row in missing_results["gates"]}
    assert missing_by_gate["D-ORACLE-COVERAGE"]["direct_decision"] == "ERROR"
    bad_inventory = copy.deepcopy(inventory)
    bad_inventory["required_gate_ids"].remove("D-COHERENCE")
    try:
        validate_gate_manifest(gates, bad_inventory)
    except ProtocolError:
        pass
    else:
        raise AssertionError("root-set mismatch was accepted")
    cyclic_gates = copy.deepcopy(gates)
    next(gate for gate in cyclic_gates["gates"] if gate["id"] == "D-STATIC-INTEGRITY")["prerequisites"] = ["D-DIAGNOSTIC-COMPLETION"]
    try:
        validate_gate_manifest(cyclic_gates, inventory)
    except ProtocolError:
        pass
    else:
        raise AssertionError("gate cycle was accepted")

    with tempfile.TemporaryDirectory(prefix="v5-diagnostic-protocol-", dir="/tmp") as temporary:
        temporary_root = Path(temporary)
        state = temporary_root / "state"
        spec_path = temporary_root / "spec.json"
        spec = {
            "schema_version": 1,
            "status": "READY",
            "files": [{"path": "report.md", "required": True, "max_bytes": 1024, "utf8": True}],
            "final_response": {
                "required": True,
                "max_bytes": 1024,
                "utf8": True,
                "utf8_fullmatch_regex": "^report\\.md\\n?$",
            },
            "max_total_output_bytes": 2048,
            "allowed_process_dispositions": ["returned", "exception", "timeout"],
        }
        spec_path.write_bytes(canonical_json_bytes(spec))
        input_root = temporary_root / "input"
        input_root.mkdir()

        def synthetic_lease(slot_id: str, agent_id: str, attempt_root: Path) -> dict[str, Any]:
            launch = {
                "schema_version": 1,
                "status": "READY",
                "role": "report",
                "assignment_id": slot_id,
                "slot_id": slot_id,
                "run_id": "r1",
                "cell_id": sha256(slot_id.encode("utf-8"))[:32],
                "mode": "E",
                "fixture_id": "synthetic_fixture",
                "task_mode": "synthetic_test",
                "prompt_regime": "controlled",
                "condition_role": "v5",
                "condition_label": "c0",
                "target_label": "m0",
                "replicate": 1,
                "workspace_root": str(input_root),
                "input_root": str(input_root),
                "output_root": str(attempt_root),
                "target_path": "target/REQUEST.md",
                "output_path": "report.md",
                "schema_paths": ["schemas/report.schema.json"],
                "schedule_sha256": "1" * 64,
                "prompt_sha256": "2" * 64,
                "package_byte_tree_sha256": "3" * 64,
                "target_byte_tree_sha256": "4" * 64,
                "authority_packet_path": "docs/rust-documentation.json",
                "authority_packet_sha256": "5" * 64,
                "authority_packet_visibility": "AGENT_VISIBLE_NEUTRAL",
                "execution_manifest_sha256": "6" * 64,
                "input_packet_sha256": "7" * 64,
                "envelope_spec_sha256": sha256(spec_path.read_bytes()),
            }
            launch_path = temporary_root / f"{slot_id}-{agent_id}.launch.json"
            launch_path.write_bytes(canonical_json_bytes(launch))
            return acquire_lease(state, launch_path, agent_id, spec_path, attempt_root)

        output = temporary_root / "output-one"
        lease = synthetic_lease("slot-one", "agent-one", output)
        try:
            synthetic_lease(
                "slot-one", "agent-two", temporary_root / "output-one-duplicate"
            )
        except LeaseAlreadyExists:
            pass
        else:
            raise AssertionError("second started-attempt lease was accepted")
        (output / "report.md").write_text("synthetic report\n", encoding="utf-8")
        pointer = seal_attempt(
            state,
            "slot-one",
            lease["lease_token"],
            "agent-one",
            output,
            b"report.md\n",
            "returned",
            0,
            {"synthetic": True},
        )
        assert pointer["format_valid"] is True
        try:
            seal_attempt(state, "slot-one", lease["lease_token"], "agent-one", output, b"replacement", "returned", 0, {})
        except CanonicalAlreadySealed:
            pass
        else:
            raise AssertionError("canonical envelope was replaced")

        invalid_output = temporary_root / "output-invalid"
        invalid_lease = synthetic_lease("slot-invalid", "agent-invalid", invalid_output)
        (invalid_output / "extra-empty-directory").mkdir()
        invalid_pointer = seal_attempt(
            state,
            "slot-invalid",
            invalid_lease["lease_token"],
            "agent-invalid",
            invalid_output,
            None,
            "not-allowed",
            None,
            {"synthetic": True},
        )
        assert invalid_pointer["format_valid"] is False
        invalid_envelope = read_json(
            state
            / "objects"
            / "sha256"
            / invalid_pointer["envelope_sha256"]
            / "envelope.json"
        )
        assert "unexpected-directory:extra-empty-directory" in invalid_envelope["violations"]

        format_output = temporary_root / "output-format"
        format_lease = synthetic_lease("slot-format", "agent-format", format_output)
        (format_output / "report.md").write_text("format report\n", encoding="utf-8")
        format_pointer = seal_attempt(
            state,
            "slot-format",
            format_lease["lease_token"],
            "agent-format",
            format_output,
            b"wrong-path.md\n",
            "returned",
            0,
            {"synthetic": True},
        )
        assert format_pointer["format_valid"] is False
        format_envelope = read_json(
            state
            / "objects"
            / "sha256"
            / format_pointer["envelope_sha256"]
            / "envelope.json"
        )
        assert "format:final-response" in format_envelope["violations"]

        race_output = temporary_root / "output-race"
        race_lease = synthetic_lease("slot-race", "agent-race", race_output)
        (race_output / "report.md").write_text("race report\n", encoding="utf-8")

        def race_seal(marker: str) -> str:
            try:
                seal_attempt(
                    state,
                    "slot-race",
                    race_lease["lease_token"],
                    "agent-race",
                    race_output,
                    b"report.md\n",
                    "returned",
                    0,
                    {"marker": marker},
                )
                return "won"
            except CanonicalAlreadySealed:
                return "lost"

        with ThreadPoolExecutor(max_workers=2) as pool:
            race_results = sorted(pool.map(race_seal, ("one", "two")))
        assert race_results == ["lost", "won"]

        failed_output = temporary_root / "output-failed"
        failed_lease = synthetic_lease("slot-failed", "agent-failed", failed_output)
        unreadable = failed_output / "report.md"
        unreadable.write_text("unreadable synthetic report\n", encoding="utf-8")
        os.chmod(unreadable, 0)
        try:
            seal_attempt(
                state,
                "slot-failed",
                failed_lease["lease_token"],
                "agent-failed",
                failed_output,
                b"report.md\n",
                "returned",
                0,
                {"synthetic": True},
            )
        except OSError:
            pass
        else:
            raise AssertionError("synthetic failed seal unexpectedly succeeded")
        finally:
            os.chmod(unreadable, 0o600)
        try:
            seal_attempt(
                state,
                "slot-failed",
                failed_lease["lease_token"],
                "agent-failed",
                failed_output,
                b"report.md\n",
                "returned",
                0,
                {},
            )
        except TerminalAlreadyClaimed:
            pass
        else:
            raise AssertionError("failed terminal claim was retried")
        verified = verify_state(state)
        assert len(verified["slots"]) == 5
        assert sum(row["status"] == "SEALED" for row in verified["slots"]) == 4
        assert sum(row["status"] == "SEAL_FAILED" for row in verified["slots"]) == 1
    print(
        "DRAFT protocol self-test passed "
        "(atoms, closed rules, A-O scoring, adjudication union/merge, DAGs, gates, lease, envelope, CAS)"
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    subcommands = parser.add_subparsers(dest="command", required=True)
    subcommands.add_parser("verify-draft")
    subcommands.add_parser("self-test")
    subcommands.add_parser("validate-integration-spec")
    atoms = subcommands.add_parser("validate-atoms")
    atoms.add_argument("manifest", type=Path)
    rules = subcommands.add_parser("validate-rules")
    rules.add_argument("inventory", type=Path)
    score = subcommands.add_parser("validate-score")
    score.add_argument("--score", type=Path, required=True)
    score.add_argument("--atoms", type=Path, required=True)
    score.add_argument("--rules", type=Path, required=True)
    score.add_argument("--scorer", choices=SCORERS)
    consistency = subcommands.add_parser("validate-consistency")
    consistency.add_argument("--consistency", type=Path, required=True)
    consistency.add_argument("--atoms", type=Path, required=True)
    consistency.add_argument("--rules", type=Path, required=True)
    packet = subcommands.add_parser("build-adjudication")
    packet.add_argument("--score-s1", type=Path, required=True)
    packet.add_argument("--score-s2", type=Path, required=True)
    packet.add_argument("--consistency", type=Path, required=True)
    packet.add_argument("--atoms", type=Path, required=True)
    packet.add_argument("--rules", type=Path, required=True)
    merge = subcommands.add_parser("merge-scores")
    merge.add_argument("--score-s1", type=Path, required=True)
    merge.add_argument("--score-s2", type=Path, required=True)
    merge.add_argument("--consistency", type=Path, required=True)
    merge.add_argument("--atoms", type=Path, required=True)
    merge.add_argument("--rules", type=Path, required=True)
    merge.add_argument("--adjudication", type=Path)
    gates = subcommands.add_parser("evaluate-gates")
    gates.add_argument("context", type=Path)
    lease = subcommands.add_parser("lease")
    lease.add_argument("--state-root", type=Path, required=True)
    lease.add_argument("--slot", required=True)
    lease.add_argument("--agent", required=True)
    lease.add_argument("--envelope-spec", type=Path, required=True)
    seal = subcommands.add_parser("seal-attempt")
    seal.add_argument("--state-root", type=Path, required=True)
    seal.add_argument("--slot", required=True)
    seal.add_argument("--agent", required=True)
    seal.add_argument("--lease-token", required=True)
    seal.add_argument("--attempt-root", type=Path, required=True)
    seal.add_argument("--final-response", type=Path)
    seal.add_argument("--process-disposition", required=True)
    seal.add_argument("--process-exit-code", type=int)
    seal.add_argument("--metadata", type=Path, required=True)
    verify = subcommands.add_parser("verify-state")
    verify.add_argument("--state-root", type=Path, required=True)
    args = parser.parse_args()
    if args.command == "verify-draft":
        verify_draft()
    elif args.command == "self-test":
        verify_draft()
        self_test()
    elif args.command == "validate-atoms":
        print(pretty_json(validate_atom_manifest(read_json(args.manifest))), end="")
    elif args.command == "validate-integration-spec":
        print(
            pretty_json(
                {
                    "schema_version": 1,
                    "status": "BLOCKING-DRAFT-VALIDATED",
                    "integration_hooks": validate_integration_hooks(
                        read_json(RUN / "integration-hooks.json")
                    ),
                    "comparison_predicate": validate_comparison_predicate(
                        read_json(RUN / "comparison-predicate.json")
                    ),
                }
            ),
            end="",
        )
    elif args.command == "validate-rules":
        print(pretty_json(validate_defect_rules(read_json(args.inventory))), end="")
    elif args.command == "validate-score":
        print(
            pretty_json(
                validate_direct_score(
                    read_json(args.score),
                    read_json(args.atoms),
                    read_json(args.rules),
                    args.scorer,
                )
            ),
            end="",
        )
    elif args.command == "validate-consistency":
        print(
            pretty_json(
                validate_consistency(
                    read_json(args.consistency),
                    read_json(args.atoms),
                    read_json(args.rules),
                )
            ),
            end="",
        )
    elif args.command == "build-adjudication":
        print(
            pretty_json(
                build_adjudication_packet(
                    read_json(args.score_s1),
                    read_json(args.score_s2),
                    read_json(args.consistency),
                    read_json(args.atoms),
                    read_json(args.rules),
                )
            ),
            end="",
        )
    elif args.command == "merge-scores":
        print(
            pretty_json(
                merge_final_scores(
                    read_json(args.score_s1),
                    read_json(args.score_s2),
                    read_json(args.consistency),
                    read_json(args.atoms),
                    read_json(args.rules),
                    read_json(args.adjudication) if args.adjudication is not None else None,
                )
            ),
            end="",
        )
    elif args.command == "evaluate-gates":
        print(
            pretty_json(
                evaluate_gates(
                    read_json(RUN / "gate-manifest.json"),
                    read_json(RUN / "root-inventory.json"),
                    read_json(args.context),
                )
            ),
            end="",
        )
    elif args.command == "lease":
        print(pretty_json(acquire_lease(args.state_root, args.slot, args.agent, args.envelope_spec)), end="")
    elif args.command == "seal-attempt":
        response = args.final_response.read_bytes() if args.final_response is not None else None
        print(
            pretty_json(
                seal_attempt(
                    args.state_root,
                    args.slot,
                    args.lease_token,
                    args.agent,
                    args.attempt_root,
                    response,
                    args.process_disposition,
                    args.process_exit_code,
                    read_json(args.metadata),
                )
            ),
            end="",
        )
    else:
        print(pretty_json(verify_state(args.state_root)), end="")


if __name__ == "__main__":
    main()
